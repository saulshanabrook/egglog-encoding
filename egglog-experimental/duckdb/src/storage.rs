use std::collections::BTreeMap;
use std::sync::Mutex;

use anyhow::{Context, Result, anyhow, bail};
use duckdb::types::Value as DuckValue;
use duckdb::{Connection, Row, params_from_iter};
use egglog_backend_trait::{BaseValues, ColumnTy, FunctionId, ScanEntry, Value};
use egglog_core_relations::Boxed;
use egglog_numeric_id::NumericId;
use ordered_float::OrderedFloat;

const COUNTERS_TABLE: &str = "egglog_backend_counters";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ScalarSqlType {
    Id,
    Unit,
    Bool,
    I64,
    F64,
    String,
}

/// Merge policies whose native input semantics are implemented in this first
/// storage slice. This is deliberately not a catch-all representation of
/// `MergeFn`: table registration fails closed before unsupported metadata can
/// reach storage.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum InputMerge {
    KeepOld,
}

impl ScalarSqlType {
    fn from_column(base_values: &BaseValues, ty: ColumnTy) -> Result<Self> {
        let ColumnTy::Base(base) = ty else {
            return Ok(Self::Id);
        };

        // EGraph::with_backend registers these built-in scalar types before it
        // can declare a function table. Unknown extension types fail closed;
        // they are never silently stored as opaque Value handles.
        let scalar = if base == base_values.get_ty::<()>() {
            Self::Unit
        } else if base == base_values.get_ty::<bool>() {
            Self::Bool
        } else if base == base_values.get_ty::<i64>() {
            Self::I64
        } else if base == base_values.get_ty::<Boxed<OrderedFloat<f64>>>() {
            Self::F64
        } else if base == base_values.get_ty::<Boxed<String>>() {
            Self::String
        } else {
            bail!(
                "DuckDB checkpoint 0.5 has no safe native scalar codec for base type {}",
                base.rep()
            );
        };
        Ok(scalar)
    }

    fn sql(self) -> &'static str {
        match self {
            Self::Id => "UBIGINT",
            Self::Unit | Self::Bool => "BOOLEAN",
            Self::I64 => "BIGINT",
            Self::F64 => "DOUBLE",
            Self::String => "VARCHAR",
        }
    }

    /// Render one typed egglog value as a closed SQL expression.
    ///
    /// Every user-controlled byte passes through this single encoder. Numeric
    /// spellings contain only formatter-produced digits/signs, while strings
    /// are UTF-8 hex and therefore cannot terminate or extend the SQL literal.
    fn sql_literal(self, base_values: &BaseValues, value: Value) -> String {
        match self {
            Self::Id => format!("CAST('{}' AS UBIGINT)", value.rep()),
            Self::Unit => {
                base_values.unwrap::<()>(value);
                "CAST(TRUE AS BOOLEAN)".to_string()
            }
            Self::Bool => format!(
                "CAST({} AS BOOLEAN)",
                if base_values.unwrap::<bool>(value) {
                    "TRUE"
                } else {
                    "FALSE"
                }
            ),
            Self::I64 => format!("CAST('{}' AS BIGINT)", base_values.unwrap::<i64>(value)),
            Self::F64 => {
                let value = base_values
                    .unwrap::<Boxed<OrderedFloat<f64>>>(value)
                    .0
                    .into_inner();
                let spelling = if value.is_nan() {
                    "NaN".to_string()
                } else if value == f64::INFINITY {
                    "Infinity".to_string()
                } else if value == f64::NEG_INFINITY {
                    "-Infinity".to_string()
                } else if value == 0.0 && value.is_sign_negative() {
                    "-0.0".to_string()
                } else {
                    format!("{value:?}")
                };
                format!("CAST('{spelling}' AS DOUBLE)")
            }
            Self::String => {
                let value = base_values.unwrap::<Boxed<String>>(value).into_inner();
                format!(
                    "CAST(decode(from_hex('{}')) AS VARCHAR)",
                    encode_hex(value.as_bytes())
                )
            }
        }
    }

    /// Bind a typed value for read-only point lookups. Production ingestion is
    /// deliberately routed through `sql_literal`, never this parameter path.
    fn bind_value(self, base_values: &BaseValues, value: Value) -> DuckValue {
        match self {
            Self::Id => DuckValue::UBigInt(u64::from(value.rep())),
            Self::Unit => {
                base_values.unwrap::<()>(value);
                DuckValue::Boolean(true)
            }
            Self::Bool => DuckValue::Boolean(base_values.unwrap::<bool>(value)),
            Self::I64 => DuckValue::BigInt(base_values.unwrap::<i64>(value)),
            Self::F64 => DuckValue::Double(
                base_values
                    .unwrap::<Boxed<OrderedFloat<f64>>>(value)
                    .0
                    .into_inner(),
            ),
            Self::String => {
                DuckValue::Text(base_values.unwrap::<Boxed<String>>(value).into_inner())
            }
        }
    }

    fn decode(self, base_values: &BaseValues, row: &Row<'_>, column: usize) -> Result<Value> {
        Ok(match self {
            Self::Id => {
                let value = row.get::<_, u64>(column)?;
                Value::new(u32::try_from(value).context("DuckDB id is outside egglog's u32 range")?)
            }
            Self::Unit => {
                let marker = row.get::<_, bool>(column)?;
                if !marker {
                    bail!("DuckDB unit marker must be TRUE");
                }
                base_values.get(())
            }
            Self::Bool => base_values.get(row.get::<_, bool>(column)?),
            Self::I64 => base_values.get(row.get::<_, i64>(column)?),
            Self::F64 => base_values.get(Boxed::new(OrderedFloat(row.get::<_, f64>(column)?))),
            Self::String => base_values.get(Boxed::new(row.get::<_, String>(column)?)),
        })
    }
}

fn encode_hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(bytes.len() * 2);
    for &byte in bytes {
        encoded.push(char::from(DIGITS[usize::from(byte >> 4)]));
        encoded.push(char::from(DIGITS[usize::from(byte & 0x0f)]));
    }
    encoded
}

#[derive(Clone, Debug)]
struct TableInfo {
    name: String,
    columns: Vec<ScalarSqlType>,
    n_keys: usize,
    can_subsume: bool,
    input_merge: InputMerge,
}

impl TableInfo {
    fn arity(&self) -> usize {
        self.columns.len()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct StoredRow {
    pub(crate) values: Vec<Value>,
    pub(crate) generation: u64,
    pub(crate) subsumed: bool,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct InsertStats {
    pub(crate) rows: usize,
    pub(crate) inserted_rows: usize,
    /// A typed vertical table is one SQL DML target. One backend-neutral
    /// add_values batch can name several such targets, so this is the exact
    /// boundary the checkpoint probes rather than hiding behind a host effect
    /// dispatcher.
    pub(crate) target_statements: usize,
}

struct State {
    connection: Connection,
    tables: Vec<TableInfo>,
    #[cfg(test)]
    latest_input_sql: Vec<String>,
}

/// Authoritative DuckDB storage. Rust retains schemas and catalog ids, but no
/// persistent copy of any function row.
pub(crate) struct Storage {
    state: Mutex<State>,
}

impl Storage {
    pub(crate) fn new() -> Result<Self> {
        let connection = Connection::open_in_memory()?;
        // This catalog is backend metadata, not an ordinary function table.
        // Ordinary function DDL below deliberately has no key constraint or
        // index; the counter may use a primary key for its single named row.
        connection.execute_batch(&format!(
            "SET threads = 1;
             SET preserve_insertion_order = false;
             CREATE TABLE {COUNTERS_TABLE} (
                 name VARCHAR PRIMARY KEY,
                 value UBIGINT NOT NULL
             );
             INSERT INTO {COUNTERS_TABLE} VALUES ('generation', 1);"
        ))?;
        Ok(Self {
            state: Mutex::new(State {
                connection,
                tables: Vec::new(),
                #[cfg(test)]
                latest_input_sql: Vec::new(),
            }),
        })
    }

    pub(crate) fn runtime_version(&self) -> Result<String> {
        let state = self.state.lock().expect("DuckDB storage mutex poisoned");
        state
            .connection
            .query_row("SELECT version()", [], |row| row.get(0))
            .map_err(Into::into)
    }

    pub(crate) fn next_table_id(&self) -> FunctionId {
        let state = self.state.lock().expect("DuckDB storage mutex poisoned");
        FunctionId::new(state.tables.len() as u32)
    }

    pub(crate) fn register_table(
        &self,
        base_values: &BaseValues,
        name: String,
        schema: &[ColumnTy],
        n_vals: usize,
        can_subsume: bool,
        input_merge: InputMerge,
    ) -> Result<FunctionId> {
        if !(1..=schema.len()).contains(&n_vals) {
            bail!(
                "function `{name}` declares {n_vals} value columns but has {} columns",
                schema.len()
            );
        }
        let columns = schema
            .iter()
            .copied()
            .map(|column| ScalarSqlType::from_column(base_values, column))
            .collect::<Result<Vec<_>>>()?;
        let n_keys = schema.len() - n_vals;

        let mut state = self.state.lock().expect("DuckDB storage mutex poisoned");
        let id = FunctionId::new(state.tables.len() as u32);
        create_table(
            &state.connection,
            id,
            &TableInfo {
                name: name.clone(),
                columns: columns.clone(),
                n_keys,
                can_subsume,
                input_merge,
            },
        )?;
        state.tables.push(TableInfo {
            name,
            columns,
            n_keys,
            can_subsume,
            input_merge,
        });
        Ok(id)
    }

    pub(crate) fn insert_batch(
        &self,
        base_values: &BaseValues,
        values: Vec<(FunctionId, Vec<Value>)>,
    ) -> Result<InsertStats> {
        if values.is_empty() {
            return Ok(InsertStats::default());
        }

        let mut state = self.state.lock().expect("DuckDB storage mutex poisoned");
        let mut grouped = BTreeMap::<u32, Vec<Vec<String>>>::new();
        for (function, row) in values {
            let info = table_info(&state, function)?;
            if row.len() != info.arity() {
                bail!(
                    "table `{}` expects {} columns, got {}",
                    info.name,
                    info.arity(),
                    row.len()
                );
            }
            let encoded = info
                .columns
                .iter()
                .zip(row)
                .map(|(&ty, value)| ty.sql_literal(base_values, value))
                .collect();
            grouped.entry(function.rep()).or_default().push(encoded);
        }

        let row_count = grouped.values().map(Vec::len).sum();
        let target_statements = grouped.len();
        let grouped = grouped
            .into_iter()
            .map(|(function, rows)| {
                let info = state
                    .tables
                    .get(function as usize)
                    .expect("validated table disappeared")
                    .clone();
                (FunctionId::new(function), info, rows)
            })
            .collect::<Vec<_>>();
        let transaction = state.connection.transaction()?;
        let mut inserted_rows = 0;
        #[cfg(test)]
        let mut executed_sql = Vec::with_capacity(target_statements);
        let write = (|| -> Result<()> {
            let generation = transaction.query_row(
                &format!("SELECT value FROM {COUNTERS_TABLE} WHERE name = 'generation'"),
                [],
                |row| row.get::<_, u64>(0),
            )?;

            for (function, info, rows) in grouped {
                let sql = input_insert_sql(function, &info, &rows, generation);
                inserted_rows += transaction.execute(&sql, [])?;
                #[cfg(test)]
                executed_sql.push(sql);
            }

            if inserted_rows != 0 {
                transaction.execute(
                    &format!(
                        "UPDATE {COUNTERS_TABLE} SET value = value + 1 WHERE name = 'generation'"
                    ),
                    [],
                )?;
            }
            Ok(())
        })();
        if let Err(error) = write {
            if let Err(rollback) = transaction.rollback() {
                return Err(anyhow!(
                    "DuckDB input transaction failed: {error:#}; rollback also failed: {rollback}"
                ));
            }
            return Err(error);
        }
        transaction.commit()?;
        #[cfg(test)]
        {
            state.latest_input_sql = executed_sql;
        }
        Ok(InsertStats {
            rows: row_count,
            inserted_rows,
            target_statements,
        })
    }

    pub(crate) fn table_size(&self, id: FunctionId) -> Result<usize> {
        let state = self.state.lock().expect("DuckDB storage mutex poisoned");
        table_info(&state, id)?;
        let count = state.connection.query_row(
            &format!("SELECT count(*) FROM {}", sql_table(id)),
            [],
            |row| row.get::<_, u64>(0),
        )?;
        usize::try_from(count).context("DuckDB row count exceeds usize")
    }

    pub(crate) fn clear(&self, id: FunctionId) -> Result<()> {
        let state = self.state.lock().expect("DuckDB storage mutex poisoned");
        table_info(&state, id)?;
        state
            .connection
            .execute(&format!("DELETE FROM {}", sql_table(id)), [])?;
        Ok(())
    }

    pub(crate) fn scan(&self, base_values: &BaseValues, id: FunctionId) -> Result<Vec<StoredRow>> {
        let state = self.state.lock().expect("DuckDB storage mutex poisoned");
        let info = table_info(&state, id)?;
        let sql = format!(
            "SELECT {}, __generation, __subsumed FROM {} ORDER BY __generation, {}",
            visible_columns(info.arity()),
            sql_table(id),
            visible_columns(info.arity())
        );
        let mut statement = state.connection.prepare(&sql)?;
        let mut rows = statement.query([])?;
        let mut stored = Vec::new();
        while let Some(row) = rows.next()? {
            stored.push(decode_row(base_values, info, row)?);
        }
        Ok(stored)
    }

    pub(crate) fn lookup(
        &self,
        base_values: &BaseValues,
        id: FunctionId,
        key: &[Value],
    ) -> Result<Option<StoredRow>> {
        let state = self.state.lock().expect("DuckDB storage mutex poisoned");
        let info = table_info(&state, id)?;
        if key.len() != info.n_keys {
            bail!(
                "table `{}` expects {} key columns, got {}",
                info.name,
                info.n_keys,
                key.len()
            );
        }
        let predicate = if key.is_empty() {
            "TRUE".to_string()
        } else {
            (0..key.len())
                .map(|column| format!("c{column} = ?"))
                .collect::<Vec<_>>()
                .join(" AND ")
        };
        let params = info.columns[..info.n_keys]
            .iter()
            .zip(key)
            .map(|(&ty, &value)| ty.bind_value(base_values, value))
            .collect::<Vec<_>>();
        let sql = format!(
            "SELECT {}, __generation, __subsumed FROM {} WHERE {predicate} LIMIT 1",
            visible_columns(info.arity()),
            sql_table(id)
        );
        let mut statement = state.connection.prepare(&sql)?;
        let mut rows = statement.query(params_from_iter(params.iter()))?;
        rows.next()?
            .map(|row| decode_row(base_values, info, row))
            .transpose()
    }

    #[cfg(test)]
    fn generation(&self) -> Result<u64> {
        let state = self.state.lock().expect("DuckDB storage mutex poisoned");
        state
            .connection
            .query_row(
                &format!("SELECT value FROM {COUNTERS_TABLE} WHERE name = 'generation'"),
                [],
                |row| row.get(0),
            )
            .map_err(Into::into)
    }

    #[cfg(test)]
    fn with_connection<R>(&self, f: impl FnOnce(&Connection) -> Result<R>) -> Result<R> {
        let state = self.state.lock().expect("DuckDB storage mutex poisoned");
        f(&state.connection)
    }

    #[cfg(test)]
    fn latest_input_sql(&self) -> Vec<String> {
        self.state
            .lock()
            .expect("DuckDB storage mutex poisoned")
            .latest_input_sql
            .clone()
    }
}

fn create_table(connection: &Connection, id: FunctionId, info: &TableInfo) -> Result<()> {
    let mut columns = info
        .columns
        .iter()
        .enumerate()
        .map(|(index, ty)| format!("c{index} {} NOT NULL", ty.sql()))
        .collect::<Vec<_>>();
    columns.push("__generation UBIGINT NOT NULL".to_string());
    columns.push("__subsumed BOOLEAN NOT NULL".to_string());
    connection.execute(
        &format!("CREATE TABLE {} ({})", sql_table(id), columns.join(", ")),
        [],
    )?;
    Ok(())
}

fn input_insert_sql(
    function: FunctionId,
    info: &TableInfo,
    rows: &[Vec<String>],
    generation: u64,
) -> String {
    debug_assert!(!rows.is_empty());
    debug_assert!(rows.iter().all(|row| row.len() == info.arity()));

    let row_sql = rows
        .iter()
        .enumerate()
        .map(|(ordinal, row)| {
            format!(
                "({}, CAST('{generation}' AS UBIGINT), FALSE, CAST('{ordinal}' AS UBIGINT))",
                row.join(", ")
            )
        })
        .collect::<Vec<_>>()
        .join(", ");
    let window = if info.n_keys == 0 {
        "ORDER BY incoming.__ordinal".to_string()
    } else {
        format!(
            "PARTITION BY {} ORDER BY incoming.__ordinal",
            qualified_columns("incoming", info.n_keys)
        )
    };
    let existing_row = match info.input_merge {
        InputMerge::KeepOld if info.n_keys == 0 => {
            format!("NOT EXISTS (SELECT 1 FROM {})", sql_table(function))
        }
        InputMerge::KeepOld => {
            let equality = (0..info.n_keys)
                .map(|column| format!("existing.c{column} IS NOT DISTINCT FROM ranked.c{column}"))
                .collect::<Vec<_>>()
                .join(" AND ");
            format!(
                "NOT EXISTS (
                     SELECT 1 FROM {} AS existing WHERE {equality}
                 )",
                sql_table(function)
            )
        }
    };

    format!(
        "INSERT INTO {} ({}, __generation, __subsumed)
         SELECT {}, ranked.__generation, ranked.__subsumed
         FROM (
             SELECT incoming.*, row_number() OVER ({window}) AS __rank
             FROM (VALUES {row_sql}) AS incoming(
                 {}, __generation, __subsumed, __ordinal
             )
         ) AS ranked
         WHERE ranked.__rank = 1 AND {existing_row}",
        sql_table(function),
        visible_columns(info.arity()),
        qualified_columns("ranked", info.arity()),
        visible_columns(info.arity()),
    )
}

fn decode_row(base_values: &BaseValues, info: &TableInfo, row: &Row<'_>) -> Result<StoredRow> {
    let values = info
        .columns
        .iter()
        .enumerate()
        .map(|(column, &ty)| ty.decode(base_values, row, column))
        .collect::<Result<Vec<_>>>()?;
    let generation = row.get::<_, u64>(info.arity())?;
    let subsumed = row.get::<_, bool>(info.arity() + 1)?;
    if subsumed && !info.can_subsume {
        bail!("table `{}` contains an illegal subsumed row", info.name);
    }
    Ok(StoredRow {
        values,
        generation,
        subsumed,
    })
}

fn table_info(state: &State, id: FunctionId) -> Result<&TableInfo> {
    state
        .tables
        .get(id.rep() as usize)
        .ok_or_else(|| anyhow!("unregistered DuckDB function {}", id.rep()))
}

fn sql_table(id: FunctionId) -> String {
    format!("egglog_function_{}", id.rep())
}

fn visible_columns(arity: usize) -> String {
    (0..arity)
        .map(|column| format!("c{column}"))
        .collect::<Vec<_>>()
        .join(", ")
}

fn qualified_columns(alias: &str, arity: usize) -> String {
    (0..arity)
        .map(|column| format!("{alias}.c{column}"))
        .collect::<Vec<_>>()
        .join(", ")
}

pub(crate) fn for_each_scan_entry(
    rows: &[StoredRow],
    f: &mut dyn for<'r> FnMut(ScanEntry<'r>) -> bool,
) {
    for row in rows {
        if !f(ScanEntry {
            vals: &row.values,
            subsumed: row.subsumed,
        }) {
            break;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use duckdb::types::Value as DuckValue;
    use egglog_backend_trait::ColumnTy;

    fn scalar_base_values() -> BaseValues {
        let mut values = BaseValues::default();
        values.register_type::<()>();
        values.register_type::<Boxed<String>>();
        values.register_type::<bool>();
        values.register_type::<i64>();
        values.register_type::<Boxed<OrderedFloat<f64>>>();
        values
    }

    fn ordinary_function_index_count(connection: &Connection) -> Result<u64> {
        connection
            .query_row(
                "SELECT count(*)
                 FROM duckdb_indexes()
                 WHERE table_name LIKE 'egglog_function_%'",
                [],
                |row| row.get(0),
            )
            .map_err(Into::into)
    }

    fn ordinary_function_key_constraint_count(connection: &Connection) -> Result<u64> {
        connection
            .query_row(
                "SELECT count(*)
                 FROM duckdb_constraints()
                 WHERE table_name LIKE 'egglog_function_%'
                   AND constraint_type IN ('PRIMARY KEY', 'UNIQUE')",
                [],
                |row| row.get(0),
            )
            .map_err(Into::into)
    }

    #[test]
    fn runtime_is_pinned_duckdb_1_5_4() -> Result<()> {
        let storage = Storage::new()?;
        assert_eq!(storage.runtime_version()?, "v1.5.4");
        Ok(())
    }

    #[test]
    fn typed_values_round_trip_without_opaque_base_handles_or_indexes() -> Result<()> {
        let values = scalar_base_values();
        let storage = Storage::new()?;
        let id = storage.register_table(
            &values,
            "typed".to_string(),
            &[
                ColumnTy::Id,
                ColumnTy::Base(values.get_ty::<bool>()),
                ColumnTy::Base(values.get_ty::<i64>()),
                ColumnTy::Base(values.get_ty::<Boxed<OrderedFloat<f64>>>()),
                ColumnTy::Base(values.get_ty::<Boxed<String>>()),
                ColumnTy::Base(values.get_ty::<()>()),
            ],
            1,
            false,
            InputMerge::KeepOld,
        )?;
        let row = vec![
            Value::new(17),
            values.get(true),
            values.get(-42_i64),
            values.get(Boxed::new(OrderedFloat(3.5))),
            values.get(Boxed::new("quoted ' text".to_string())),
            values.get(()),
        ];
        let stats = storage.insert_batch(&values, vec![(id, row.clone())])?;
        assert_eq!(
            stats,
            InsertStats {
                rows: 1,
                inserted_rows: 1,
                target_statements: 1
            }
        );
        assert_eq!(storage.scan(&values, id)?[0].values, row);
        assert!(
            storage
                .latest_input_sql()
                .iter()
                .all(|sql| !sql.contains('?'))
        );
        storage.with_connection(|connection| {
            let types = connection
                .prepare(&format!("DESCRIBE {}", sql_table(id)))?
                .query_map([], |row| {
                    Ok((row.get::<_, String>(0)?, row.get::<_, String>(1)?))
                })?
                .collect::<duckdb::Result<Vec<_>>>()?;
            assert_eq!(
                &types[..6],
                &[
                    ("c0".to_string(), "UBIGINT".to_string()),
                    ("c1".to_string(), "BOOLEAN".to_string()),
                    ("c2".to_string(), "BIGINT".to_string()),
                    ("c3".to_string(), "DOUBLE".to_string()),
                    ("c4".to_string(), "VARCHAR".to_string()),
                    ("c5".to_string(), "BOOLEAN".to_string()),
                ]
            );
            assert_eq!(types.len(), 8, "no hidden singleton column is allowed");
            assert_eq!(ordinary_function_index_count(connection)?, 0);
            assert_eq!(ordinary_function_key_constraint_count(connection)?, 0);
            Ok(())
        })?;
        Ok(())
    }

    #[test]
    fn adversarial_sql_literals_round_trip_and_cannot_escape_values() -> Result<()> {
        let values = scalar_base_values();
        let storage = Storage::new()?;
        let string_table = storage.register_table(
            &values,
            "strings".to_string(),
            &[
                ColumnTy::Id,
                ColumnTy::Base(values.get_ty::<Boxed<String>>()),
            ],
            1,
            false,
            InputMerge::KeepOld,
        )?;
        let integer_table = storage.register_table(
            &values,
            "integers".to_string(),
            &[ColumnTy::Id, ColumnTy::Base(values.get_ty::<i64>())],
            1,
            false,
            InputMerge::KeepOld,
        )?;
        let float_table = storage.register_table(
            &values,
            "floats".to_string(),
            &[
                ColumnTy::Id,
                ColumnTy::Base(values.get_ty::<Boxed<OrderedFloat<f64>>>()),
            ],
            1,
            false,
            InputMerge::KeepOld,
        )?;

        let strings = [
            "quotes: ' and ''".to_string(),
            "'); DROP TABLE egglog_function_0; --".to_string(),
            "embedded\0nul".to_string(),
            "Unicode: 雪 🦆 café".to_string(),
        ];
        let integers = [i64::MIN, i64::MAX];
        let floats = [
            1.234_567_890_123_456_7,
            -0.0,
            f64::NAN,
            f64::INFINITY,
            f64::NEG_INFINITY,
        ];
        let mut batch = Vec::new();
        for (index, string) in strings.iter().enumerate() {
            batch.push((
                string_table,
                vec![
                    Value::from_usize(index),
                    values.get(Boxed::new(string.clone())),
                ],
            ));
        }
        for (index, integer) in integers.into_iter().enumerate() {
            batch.push((
                integer_table,
                vec![Value::from_usize(index), values.get(integer)],
            ));
        }
        for (index, float) in floats.into_iter().enumerate() {
            batch.push((
                float_table,
                vec![
                    Value::from_usize(index),
                    values.get(Boxed::new(OrderedFloat(float))),
                ],
            ));
        }

        let stats = storage.insert_batch(&values, batch)?;
        assert_eq!(stats.rows, strings.len() + integers.len() + floats.len());
        assert_eq!(stats.inserted_rows, stats.rows);
        assert_eq!(stats.target_statements, 3);
        let generated = storage.latest_input_sql();
        assert_eq!(generated.len(), 3);
        assert!(generated.iter().all(|sql| !sql.contains('?')));
        assert!(generated.iter().all(|sql| !sql.contains("DROP TABLE")));

        let stored_strings = storage.scan(&values, string_table)?;
        for (row, expected) in stored_strings.iter().zip(&strings) {
            assert_eq!(
                values.unwrap::<Boxed<String>>(row.values[1]).into_inner(),
                expected.as_str()
            );
        }
        let stored_integers = storage.scan(&values, integer_table)?;
        assert_eq!(values.unwrap::<i64>(stored_integers[0].values[1]), i64::MIN);
        assert_eq!(values.unwrap::<i64>(stored_integers[1].values[1]), i64::MAX);
        let stored_floats = storage.scan(&values, float_table)?;
        let decoded = stored_floats
            .iter()
            .map(|row| {
                values
                    .unwrap::<Boxed<OrderedFloat<f64>>>(row.values[1])
                    .0
                    .into_inner()
            })
            .collect::<Vec<_>>();
        assert_eq!(decoded[0].to_bits(), floats[0].to_bits());
        assert_eq!(decoded[1].to_bits(), (-0.0_f64).to_bits());
        assert!(decoded[2].is_nan());
        assert_eq!(decoded[3], f64::INFINITY);
        assert_eq!(decoded[4], f64::NEG_INFINITY);

        assert_eq!(storage.table_size(string_table)?, strings.len());
        assert_eq!(storage.table_size(integer_table)?, integers.len());
        assert_eq!(storage.table_size(float_table)?, floats.len());
        storage.with_connection(|connection| {
            assert_eq!(ordinary_function_index_count(connection)?, 0);
            assert_eq!(ordinary_function_key_constraint_count(connection)?, 0);
            Ok(())
        })?;
        Ok(())
    }

    #[test]
    fn keep_old_conflicts_and_invalid_target_rollback_are_transactional() -> Result<()> {
        let values = scalar_base_values();
        let storage = Storage::new()?;
        let schema = [ColumnTy::Id, ColumnTy::Base(values.get_ty::<i64>())];
        let first = storage.register_table(
            &values,
            "first".to_string(),
            &schema,
            1,
            false,
            InputMerge::KeepOld,
        )?;
        let second = storage.register_table(
            &values,
            "second".to_string(),
            &schema,
            1,
            false,
            InputMerge::KeepOld,
        )?;
        // Recreate the ordinary target with a test-only CHECK fault injector.
        // DuckDB 1.5.4 cannot add CHECK constraints with ALTER TABLE; this DDL
        // remains index-free and preserves the registered physical schema.
        storage.with_connection(|connection| {
            connection.execute(&format!("DROP TABLE {}", sql_table(second)), [])?;
            connection.execute(
                &format!(
                    "CREATE TABLE {} (
                         c0 UBIGINT NOT NULL,
                         c1 BIGINT NOT NULL CHECK (c1 >= 0),
                         __generation UBIGINT NOT NULL,
                         __subsumed BOOLEAN NOT NULL
                     )",
                    sql_table(second)
                ),
                [],
            )?;
            assert_eq!(ordinary_function_index_count(connection)?, 0);
            assert_eq!(ordinary_function_key_constraint_count(connection)?, 0);
            Ok(())
        })?;
        storage.insert_batch(
            &values,
            vec![(second, vec![Value::new(1), values.get(10_i64)])],
        )?;
        assert_eq!(storage.generation()?, 2);

        // A conflicting value is a legal KeepOld merge, not a constraint
        // error. DuckDB applies it without advancing the row generation.
        let ignored = storage.insert_batch(
            &values,
            vec![(second, vec![Value::new(1), values.get(99_i64)])],
        )?;
        assert_eq!(ignored.rows, 1);
        assert_eq!(ignored.inserted_rows, 0);
        assert_eq!(
            storage.scan(&values, second)?[0].values[1],
            values.get(10_i64)
        );
        assert_eq!(storage.generation()?, 2);

        // Target one executes before target two violates its independent CHECK.
        let error = storage
            .insert_batch(
                &values,
                vec![
                    (first, vec![Value::new(2), values.get(20_i64)]),
                    (second, vec![Value::new(3), values.get(-1_i64)]),
                ],
            )
            .unwrap_err();
        assert!(
            error
                .to_string()
                .to_lowercase()
                .contains("check constraint")
        );
        assert_eq!(storage.table_size(first)?, 0);
        assert_eq!(storage.table_size(second)?, 1);
        assert_eq!(storage.generation()?, 2);
        storage.with_connection(|connection| {
            assert_eq!(ordinary_function_index_count(connection)?, 0);
            assert_eq!(ordinary_function_key_constraint_count(connection)?, 0);
            Ok(())
        })?;

        let stats = storage.insert_batch(
            &values,
            vec![
                (first, vec![Value::new(2), values.get(20_i64)]),
                (second, vec![Value::new(1), values.get(30_i64)]),
            ],
        )?;
        assert_eq!(stats.target_statements, 2);
        assert_eq!(stats.rows, 2);
        assert_eq!(stats.inserted_rows, 1);
        assert_eq!(storage.scan(&values, first)?[0].generation, 2);
        assert_eq!(storage.scan(&values, second)?[0].generation, 1);
        assert_eq!(
            storage.scan(&values, second)?[0].values[1],
            values.get(10_i64)
        );
        Ok(())
    }

    #[test]
    fn nullary_keep_old_is_index_free_and_keeps_first_incoming() -> Result<()> {
        let values = scalar_base_values();
        let storage = Storage::new()?;
        let table = storage.register_table(
            &values,
            "nullary".to_string(),
            &[ColumnTy::Base(values.get_ty::<i64>())],
            1,
            false,
            InputMerge::KeepOld,
        )?;
        let first = storage.insert_batch(
            &values,
            vec![
                (table, vec![values.get(10_i64)]),
                (table, vec![values.get(20_i64)]),
            ],
        )?;
        assert_eq!(first.rows, 2);
        assert_eq!(first.inserted_rows, 1);
        let ignored = storage.insert_batch(&values, vec![(table, vec![values.get(30_i64)])])?;
        assert_eq!(ignored.inserted_rows, 0);
        assert_eq!(storage.scan(&values, table)?.len(), 1);
        assert_eq!(
            storage.lookup(&values, table, &[])?.unwrap().values[0],
            values.get(10_i64)
        );
        storage.with_connection(|connection| {
            let columns = connection
                .prepare(&format!("DESCRIBE {}", sql_table(table)))?
                .query_map([], |row| row.get::<_, String>(0))?
                .collect::<duckdb::Result<Vec<_>>>()?;
            assert_eq!(columns, ["c0", "__generation", "__subsumed"]);
            assert_eq!(ordinary_function_index_count(connection)?, 0);
            assert_eq!(ordinary_function_key_constraint_count(connection)?, 0);
            Ok(())
        })?;
        Ok(())
    }

    #[test]
    fn safe_api_projects_nested_list_and_struct_results() -> Result<()> {
        let storage = Storage::new()?;
        let (nested, projected_ids, projected_tag) = storage.with_connection(|connection| {
            let nested = connection.query_row(
                "SELECT struct_pack(
                     ids := [CAST(? AS UBIGINT), CAST(? AS UBIGINT)],
                     tag := CAST(? AS VARCHAR)
                 )",
                duckdb::params![1_u64, 2_u64, "typed"],
                |row| row.get::<_, DuckValue>(0),
            )?;
            let projected = connection.query_row(
                "SELECT nested.ids, nested.tag
                 FROM (SELECT struct_pack(
                     ids := [CAST(? AS UBIGINT), CAST(? AS UBIGINT)],
                     tag := CAST(? AS VARCHAR)
                 ) AS nested)",
                duckdb::params![1_u64, 2_u64, "typed"],
                |row| Ok((row.get::<_, DuckValue>(0)?, row.get::<_, String>(1)?)),
            )?;
            Ok((nested, projected.0, projected.1))
        })?;
        let DuckValue::Struct(fields) = nested else {
            panic!("expected a nested STRUCT result, got {nested:?}");
        };
        assert_eq!(
            fields.get(&"ids".to_string()),
            Some(&DuckValue::List(vec![
                DuckValue::UBigInt(1),
                DuckValue::UBigInt(2)
            ]))
        );
        assert_eq!(
            fields.get(&"tag".to_string()),
            Some(&DuckValue::Text("typed".to_string()))
        );
        assert_eq!(
            projected_ids,
            DuckValue::List(vec![DuckValue::UBigInt(1), DuckValue::UBigInt(2)])
        );
        assert_eq!(projected_tag, "typed");
        Ok(())
    }

    #[test]
    fn source_pinned_selective_and_broad_sql_feasibility_probes() -> Result<()> {
        const POINTER: &str = include_str!("../../../benchmarks/pointer-analysis-small.egg");
        const MATH: &str = include_str!("../../../egglog/tests/math-microbenchmark.egg");
        assert!(POINTER.contains(
            "(function_name f)\n    (function_param f idx x)\n    (call_instruction_fn_target instr f)\n    (call_instruction_arg instr idx v)\n    (= (expr_points_to v) a)"
        ));
        assert!(POINTER.contains("(union (expr_points_to x) a)"));
        assert!(MATH.contains("(rewrite (Add a b) (Add b a))"));

        let storage = Storage::new()?;
        storage.with_connection(|connection| {
            connection.execute_batch(
                "CREATE TABLE function_name (function_id UBIGINT);
                 CREATE TABLE function_param (
                     function_id UBIGINT, parameter_index BIGINT, parameter UBIGINT
                 );
                 CREATE TABLE call_instruction_fn_target (
                     instruction UBIGINT, function_id UBIGINT
                 );
                 CREATE TABLE call_instruction_arg (
                     instruction UBIGINT, argument_index BIGINT, argument UBIGINT
                 );
                 CREATE TABLE expr_points_to (expression UBIGINT, allocation UBIGINT);
                 INSERT INTO function_name VALUES (1), (2), (99);
                 INSERT INTO function_param VALUES
                     (1, 0, 100), (1, 1, 101), (2, 0, 200), (99, 0, 9900);
                 INSERT INTO call_instruction_fn_target VALUES (10, 1), (20, 2);
                 INSERT INTO call_instruction_arg VALUES
                     (10, 0, 300), (10, 1, 301), (10, 2, 999), (20, 0, 400);
                 INSERT INTO expr_points_to VALUES
                     (300, 700), (301, 701), (400, 800), (999, 799), (1234, 9999);

                 CREATE TABLE math_add (lhs UBIGINT, rhs UBIGINT, term UBIGINT);
                 INSERT INTO math_add VALUES (1, 2, 100), (2, 3, 101), (4, 5, 102);",
            )?;

            let selective = connection
                .prepare(
                    "SELECT parameter.parameter, points.allocation
                     FROM function_name AS named
                     JOIN function_param AS parameter
                       ON parameter.function_id = named.function_id
                     JOIN call_instruction_fn_target AS call
                       ON call.function_id = named.function_id
                     JOIN call_instruction_arg AS argument
                       ON argument.instruction = call.instruction
                      AND argument.argument_index = parameter.parameter_index
                     JOIN expr_points_to AS points
                       ON points.expression = argument.argument
                     ORDER BY parameter.parameter",
                )?
                .query_map([], |row| Ok((row.get::<_, u64>(0)?, row.get::<_, u64>(1)?)))?
                .collect::<duckdb::Result<Vec<_>>>()?;
            assert_eq!(selective, vec![(100, 700), (101, 701), (200, 800)]);

            let broad = connection
                .prepare(
                    "SELECT term, rhs, lhs
                     FROM math_add
                     ORDER BY term",
                )?
                .query_map([], |row| {
                    Ok((
                        row.get::<_, u64>(0)?,
                        row.get::<_, u64>(1)?,
                        row.get::<_, u64>(2)?,
                    ))
                })?
                .collect::<duckdb::Result<Vec<_>>>()?;
            assert_eq!(broad, vec![(100, 2, 1), (101, 3, 2), (102, 5, 4)]);
            Ok(())
        })?;
        Ok(())
    }
}
