use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

use anyhow::{Context, Result, anyhow, bail};
use duckdb::{Connection, Row};
use egglog_backend_trait::{
    BaseValueId, BaseValues, ColumnTy, DefaultVal, FunctionConfig, FunctionId, MergeAction,
    MergeFn, NativeInputValue, ScanEntry, Value,
};
use egglog_core_relations::{BaseValue, Boxed};
use egglog_numeric_id::NumericId;
use num::{BigInt, BigRational, ToPrimitive, Zero, rational::Rational64};
use ordered_float::OrderedFloat;

use crate::path_compress::PathCompressionPlan;
use crate::rebuild::{OrderedUnionOrientation, OrderedUnionPlan, StandardRebuildKind};
use crate::rule_sql::{CompiledRule, RuleExecutionStats};

const COUNTERS_TABLE: &str = "egglog_backend_counters";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ScalarSqlType {
    Id,
    Unit,
    Bool,
    I64,
    F64,
    String,
    BigInt,
    BigRat,
    Rational,
}

/// Whether a registered table may currently be merge-written by native input
/// or a direct Set. Key deletion and complete-row subsumption do not invoke a
/// table's merge plan and therefore admit deferred capabilities independently.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum WriteCapability {
    KeepOld,
    AssertEq,
    Deferred,
}

impl WriteCapability {
    fn preflight(self, table: &TableInfo) -> Result<()> {
        if self == Self::Deferred {
            bail!(
                "write to table `{}` requires a merge capability that is registered but deferred",
                table.name
            );
        }
        Ok(())
    }
}

impl ScalarSqlType {
    pub(crate) fn from_column(base_values: &BaseValues, ty: ColumnTy) -> Result<Self> {
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
        } else if registered_base_type_is::<Boxed<BigInt>>(base_values, base) {
            Self::BigInt
        } else if registered_base_type_is::<Boxed<BigRational>>(base_values, base) {
            Self::BigRat
        } else if registered_base_type_is::<Boxed<Rational64>>(base_values, base) {
            Self::Rational
        } else {
            bail!(
                "DuckDB has no safe native scalar codec for base type {}",
                base.rep()
            );
        };
        Ok(scalar)
    }

    pub(crate) fn sql(self) -> &'static str {
        match self {
            Self::Id => "UBIGINT",
            Self::Unit | Self::Bool => "BOOLEAN",
            Self::I64 => "BIGINT",
            Self::F64 => "DOUBLE",
            Self::String => "VARCHAR",
            Self::BigInt => "BIGNUM",
            Self::BigRat => "STRUCT(numer BIGNUM, denom BIGNUM)",
            Self::Rational => "STRUCT(numer BIGINT, denom BIGINT)",
        }
    }

    /// Render one typed egglog value as a closed SQL expression.
    ///
    /// Every user-controlled byte passes through this single encoder. Numeric
    /// spellings contain only formatter-produced digits/signs, while strings
    /// are UTF-8 hex and therefore cannot terminate or extend the SQL literal.
    pub(crate) fn sql_literal(self, base_values: &BaseValues, value: Value) -> Result<String> {
        Ok(match self {
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
            Self::BigInt => {
                let value = base_values.unwrap::<Boxed<BigInt>>(value).into_inner();
                format!("CAST('{}' AS BIGNUM)", value)
            }
            Self::BigRat => {
                let value =
                    canonical_bigrat(base_values.unwrap::<Boxed<BigRational>>(value).into_inner())?;
                format!(
                    "CAST(struct_pack(numer := CAST('{}' AS BIGNUM), denom := CAST('{}' AS BIGNUM)) AS STRUCT(numer BIGNUM, denom BIGNUM))",
                    value.numer(),
                    value.denom()
                )
            }
            Self::Rational => {
                let value = canonical_rational64(
                    base_values.unwrap::<Boxed<Rational64>>(value).into_inner(),
                )?;
                format!(
                    "CAST(struct_pack(numer := CAST('{}' AS BIGINT), denom := CAST('{}' AS BIGINT)) AS STRUCT(numer BIGINT, denom BIGINT))",
                    value.numer(),
                    value.denom()
                )
            }
        })
    }

    fn read_expression(self, column: &str) -> String {
        match self {
            Self::BigInt => format!("CAST({column} AS VARCHAR)"),
            Self::BigRat | Self::Rational => format!(
                "concat(CAST(struct_extract({column}, 'numer') AS VARCHAR), '/', CAST(struct_extract({column}, 'denom') AS VARCHAR))"
            ),
            _ => column.to_string(),
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
            Self::BigInt => {
                let value = parse_canonical_bigint(&row.get::<_, String>(column)?)?;
                base_values.get(Boxed::new(value))
            }
            Self::BigRat => {
                let (numer, denom) = parse_exact_pair(&row.get::<_, String>(column)?)?;
                let value = canonical_bigrat(BigRational::new(numer.clone(), denom.clone()))?;
                if value.numer() != &numer || value.denom() != &denom {
                    bail!("DuckDB BigRat row is not canonically reduced");
                }
                base_values.get(Boxed::new(value))
            }
            Self::Rational => {
                let (numer, denom) = parse_exact_pair(&row.get::<_, String>(column)?)?;
                let stored_numer = numer
                    .to_i64()
                    .context("DuckDB Rational numerator is outside i64")?;
                let stored_denom = denom
                    .to_i64()
                    .context("DuckDB Rational denominator is outside i64")?;
                let value = canonical_rational64(Rational64::new_raw(stored_numer, stored_denom))?;
                if *value.numer() != stored_numer || *value.denom() != stored_denom {
                    bail!("DuckDB Rational row is not canonically reduced");
                }
                base_values.get(Boxed::new(value))
            }
        })
    }
}

/// `BaseValues` intentionally exposes no fallible type-id lookup. Registering
/// on a clone tells us whether a concrete Rust type was already present
/// without mutating the live registry or relying on registration order.
fn registered_base_type_is<P: BaseValue>(base_values: &BaseValues, id: BaseValueId) -> bool {
    let mut probe = base_values.clone();
    probe.register_type::<P>() == id
}

fn canonical_bigrat(value: BigRational) -> Result<BigRational> {
    if value.denom().is_zero() {
        bail!("BigRat denominator must not be zero");
    }
    Ok(BigRational::new(
        value.numer().clone(),
        value.denom().clone(),
    ))
}

fn canonical_rational64(value: Rational64) -> Result<Rational64> {
    if value.denom().is_zero() {
        bail!("Rational denominator must not be zero");
    }
    // Normalize through arbitrary precision so hostile raw i64 pairs cannot
    // overflow while flipping a denominator sign or reducing a gcd.
    let normalized = BigRational::new(BigInt::from(*value.numer()), BigInt::from(*value.denom()));
    let numer = normalized
        .numer()
        .to_i64()
        .context("canonical Rational numerator is outside i64")?;
    let denom = normalized
        .denom()
        .to_i64()
        .context("canonical Rational denominator is outside i64")?;
    Ok(Rational64::new_raw(numer, denom))
}

fn parse_canonical_bigint(text: &str) -> Result<BigInt> {
    let value = text
        .parse::<BigInt>()
        .with_context(|| format!("invalid canonical integer projection `{text}`"))?;
    if value.to_string() != text {
        bail!("non-canonical integer projection `{text}`");
    }
    Ok(value)
}

fn parse_exact_pair(text: &str) -> Result<(BigInt, BigInt)> {
    let (numer, denom) = text
        .split_once('/')
        .ok_or_else(|| anyhow!("invalid exact-number projection `{text}`"))?;
    if denom.contains('/') {
        bail!("invalid exact-number projection `{text}`");
    }
    let numer = parse_canonical_bigint(numer)?;
    let denom = parse_canonical_bigint(denom)?;
    if denom <= BigInt::ZERO {
        bail!("exact-number denominator must be positive");
    }
    Ok((numer, denom))
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

#[derive(Clone)]
pub(crate) struct TableInfo {
    pub(crate) name: String,
    pub(crate) schema: Vec<ColumnTy>,
    pub(crate) columns: Vec<ScalarSqlType>,
    pub(crate) n_keys: usize,
    pub(crate) n_vals: usize,
    // Retained for action-stream lookup and identity-guard lowering in later
    // checkpoints even though this slice only executes direct Set writes.
    #[allow(dead_code)]
    pub(crate) n_identity_vals: Option<usize>,
    #[allow(dead_code)]
    pub(crate) default: DefaultVal,
    #[allow(dead_code)]
    pub(crate) merge: Arc<MergeFn>,
    pub(crate) can_subsume: bool,
    pub(crate) write_capability: WriteCapability,
}

impl TableInfo {
    pub(crate) fn arity(&self) -> usize {
        self.columns.len()
    }

    pub(crate) fn preflight_write(&self) -> Result<()> {
        self.write_capability.preflight(self)
    }
}

fn validate_function_config(
    tables: &[TableInfo],
    predicted_id: FunctionId,
    config: &FunctionConfig,
) -> Result<WriteCapability> {
    if !(1..=config.schema.len()).contains(&config.n_vals) {
        bail!(
            "function `{}` declares {} value columns but has {} columns",
            config.name,
            config.n_vals,
            config.schema.len()
        );
    }
    if let Some(identity_vals) = config.n_identity_vals
        && !(1..=config.n_vals).contains(&identity_vals)
    {
        bail!(
            "function `{}` declares {identity_vals} identity columns but has {} value columns",
            config.name,
            config.n_vals
        );
    }

    let (actions, result) = match &config.merge {
        MergeFn::Block { actions, result } => (actions.as_slice(), result.as_ref()),
        result => (&[][..], result),
    };
    let mut available_slots = 0;
    for action in actions {
        validate_merge_action(action, tables, predicted_id, config, available_slots)?;
        if let MergeAction::Let { slot, .. } = action {
            if *slot != available_slots {
                bail!(
                    "merge for `{}` declares let slot {slot}, expected {available_slots}",
                    config.name
                );
            }
            available_slots += 1;
        }
    }

    let results = match result {
        MergeFn::Columns(columns) => columns.as_slice(),
        result => std::slice::from_ref(result),
    };
    if results.len() != config.n_vals {
        bail!(
            "merge for `{}` must produce {} value column(s), got {}",
            config.name,
            config.n_vals,
            results.len()
        );
    }
    for result in results {
        validate_merge_expression(result, tables, predicted_id, config, available_slots)?;
    }

    Ok(match (&config.merge, config.n_vals) {
        (MergeFn::Old, 1) => WriteCapability::KeepOld,
        (MergeFn::AssertEq, 1) => WriteCapability::AssertEq,
        _ => WriteCapability::Deferred,
    })
}

fn validate_merge_action(
    action: &MergeAction,
    tables: &[TableInfo],
    predicted_id: FunctionId,
    config: &FunctionConfig,
    available_slots: usize,
) -> Result<()> {
    match action {
        MergeAction::Set(target, arguments) => {
            let target_arity = if *target == predicted_id {
                config.schema.len()
            } else {
                tables
                    .get(target.rep() as usize)
                    .ok_or_else(|| {
                        anyhow!(
                            "merge for `{}` writes future or unknown function {}",
                            config.name,
                            target.rep()
                        )
                    })?
                    .arity()
            };
            if arguments.len() != target_arity {
                bail!(
                    "merge for `{}` writes {} columns to function {}, expected {target_arity}",
                    config.name,
                    arguments.len(),
                    target.rep()
                );
            }
            for argument in arguments {
                validate_merge_expression(argument, tables, predicted_id, config, available_slots)?;
            }
        }
        MergeAction::Let { value, .. } => {
            validate_merge_expression(value, tables, predicted_id, config, available_slots)?
        }
        MergeAction::Union(lhs, rhs) => {
            validate_merge_expression(lhs, tables, predicted_id, config, available_slots)?;
            validate_merge_expression(rhs, tables, predicted_id, config, available_slots)?;
        }
    }
    Ok(())
}

fn validate_merge_expression(
    merge: &MergeFn,
    tables: &[TableInfo],
    predicted_id: FunctionId,
    config: &FunctionConfig,
    available_slots: usize,
) -> Result<()> {
    match merge {
        MergeFn::OldCol(index) | MergeFn::NewCol(index) => {
            if *index >= config.n_vals {
                bail!(
                    "merge for `{}` references value column {index}, but has only {} value columns",
                    config.name,
                    config.n_vals
                );
            }
        }
        MergeFn::LetVar(slot) => {
            if *slot >= available_slots {
                bail!(
                    "merge for `{}` references let slot {slot} before it is bound",
                    config.name
                );
            }
        }
        MergeFn::Primitive {
            input,
            args: arguments,
            ..
        } => {
            if input.len() != arguments.len() {
                bail!(
                    "merge for `{}` calls a primitive with {} arguments but records {} input types",
                    config.name,
                    arguments.len(),
                    input.len()
                );
            }
            for argument in arguments {
                validate_merge_expression(argument, tables, predicted_id, config, available_slots)?;
            }
        }
        MergeFn::Function(function, arguments) => {
            if *function == predicted_id {
                bail!(
                    "self-referential merge for `{}` may write to itself but may not read itself",
                    config.name
                );
            }
            let target = tables.get(function.rep() as usize).ok_or_else(|| {
                anyhow!(
                    "merge for `{}` reads future or unknown function {}",
                    config.name,
                    function.rep()
                )
            })?;
            let expected = target.arity() - 1;
            if arguments.len() != expected {
                bail!(
                    "merge for `{}` calls function {} with {} arguments, expected {expected}",
                    config.name,
                    function.rep(),
                    arguments.len()
                );
            }
            for argument in arguments {
                validate_merge_expression(argument, tables, predicted_id, config, available_slots)?;
            }
        }
        MergeFn::Lookup(function, arguments) => {
            if *function == predicted_id {
                bail!(
                    "self-referential merge for `{}` may write to itself but may not read itself",
                    config.name
                );
            }
            let target = tables.get(function.rep() as usize).ok_or_else(|| {
                anyhow!(
                    "merge for `{}` reads future or unknown function {}",
                    config.name,
                    function.rep()
                )
            })?;
            if arguments.len() != target.n_keys {
                bail!(
                    "merge for `{}` looks up {} keys from function {}, expected {}",
                    config.name,
                    arguments.len(),
                    function.rep(),
                    target.n_keys
                );
            }
            for argument in arguments {
                validate_merge_expression(argument, tables, predicted_id, config, available_slots)?;
            }
        }
        MergeFn::Columns(_) => {
            bail!(
                "nested MergeFn::Columns is not supported for `{}`",
                config.name
            )
        }
        MergeFn::Block { .. } => {
            bail!(
                "nested MergeFn::Block is not supported for `{}`",
                config.name
            )
        }
        MergeFn::AssertEq
        | MergeFn::UnionId
        | MergeFn::Old
        | MergeFn::New
        | MergeFn::Const { .. } => {}
    }
    Ok(())
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
    next_rule_run: u64,
    #[cfg(test)]
    latest_input_sql: Vec<String>,
    #[cfg(test)]
    latest_rule_sql: Vec<String>,
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
             INSERT INTO {COUNTERS_TABLE} VALUES ('generation', 1), ('fresh_id', 0);"
        ))?;
        Ok(Self {
            state: Mutex::new(State {
                connection,
                tables: Vec::new(),
                next_rule_run: 0,
                #[cfg(test)]
                latest_input_sql: Vec::new(),
                #[cfg(test)]
                latest_rule_sql: Vec::new(),
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

    pub(crate) fn fresh_id(&self) -> Result<Value> {
        let mut state = self.state.lock().expect("DuckDB storage mutex poisoned");
        let transaction = state.connection.transaction()?;
        let value = transaction.query_row(
            &format!("SELECT value FROM {COUNTERS_TABLE} WHERE name = 'fresh_id'"),
            [],
            |row| row.get::<_, u64>(0),
        )?;
        if value >= u32::MAX as u64 {
            transaction.rollback()?;
            bail!("DuckDB fresh-id counter exceeds the usable Value domain");
        }
        transaction.execute(
            &format!(
                "UPDATE {COUNTERS_TABLE} SET value = CAST('{}' AS UBIGINT) WHERE name = 'fresh_id'",
                value + 1
            ),
            [],
        )?;
        transaction.commit()?;
        Ok(Value::new(value as u32))
    }

    pub(crate) fn next_table_id(&self) -> FunctionId {
        let state = self.state.lock().expect("DuckDB storage mutex poisoned");
        FunctionId::new(state.tables.len() as u32)
    }

    pub(crate) fn register_table(
        &self,
        base_values: &BaseValues,
        config: FunctionConfig,
    ) -> Result<FunctionId> {
        let mut state = self.state.lock().expect("DuckDB storage mutex poisoned");
        let id = FunctionId::new(state.tables.len() as u32);
        let write_capability = validate_function_config(&state.tables, id, &config)?;
        let columns = config
            .schema
            .iter()
            .copied()
            .map(|column| ScalarSqlType::from_column(base_values, column))
            .collect::<Result<Vec<_>>>()?;
        let FunctionConfig {
            schema,
            n_vals,
            n_identity_vals,
            default,
            merge,
            name,
            can_subsume,
        } = config;
        let info = TableInfo {
            name,
            n_keys: schema.len() - n_vals,
            n_vals,
            n_identity_vals,
            default,
            merge: Arc::new(merge),
            schema,
            columns,
            can_subsume,
            write_capability,
        };
        create_table(&state.connection, id, &info)?;
        state.tables.push(info);
        Ok(id)
    }

    pub(crate) fn insert_batch(
        &self,
        base_values: &BaseValues,
        values: Vec<(FunctionId, Vec<Value>)>,
    ) -> Result<InsertStats> {
        self.insert_batch_with_fresh(
            base_values,
            values
                .into_iter()
                .map(|(function, row)| {
                    (
                        function,
                        row.into_iter().map(NativeInputValue::Existing).collect(),
                    )
                })
                .collect(),
        )
    }

    pub(crate) fn insert_batch_with_fresh(
        &self,
        base_values: &BaseValues,
        values: Vec<(FunctionId, Vec<NativeInputValue>)>,
    ) -> Result<InsertStats> {
        if values.is_empty() {
            return Ok(InsertStats::default());
        }

        let mut state = self.state.lock().expect("DuckDB storage mutex poisoned");
        let mut grouped = BTreeMap::<u32, Vec<Vec<NativeInputValue>>>::new();
        let mut slots = std::collections::BTreeSet::new();
        for (function, row) in values {
            let info = table_info(&state, function)?;
            info.preflight_write()?;
            if row.len() != info.arity() {
                bail!(
                    "table `{}` expects {} columns, got {}",
                    info.name,
                    info.arity(),
                    row.len()
                );
            }
            for (&value, &ty) in row.iter().zip(&info.schema) {
                match value {
                    NativeInputValue::Existing(value) => {
                        if value.rep() == u32::MAX {
                            bail!(
                                "native input contains the reserved stale Value sentinel in `{}`",
                                info.name
                            );
                        }
                    }
                    NativeInputValue::FreshSlot(slot) => {
                        if ty != ColumnTy::Id {
                            bail!(
                                "native input fresh slot {slot} targets a non-id column in `{}`",
                                info.name
                            );
                        }
                        slots.insert(slot);
                    }
                }
            }
            grouped.entry(function.rep()).or_default().push(row);
        }
        for (expected, actual) in slots.iter().copied().enumerate() {
            if usize::try_from(actual).ok() != Some(expected) {
                bail!(
                    "native input fresh slots must be dense from zero; expected {expected}, found {actual}"
                );
            }
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
            let first_fresh = transaction.query_row(
                &format!("SELECT value FROM {COUNTERS_TABLE} WHERE name = 'fresh_id'"),
                [],
                |row| row.get::<_, u64>(0),
            )?;
            let next_fresh = first_fresh
                .checked_add(slots.len() as u64)
                .filter(|&end| end <= u32::MAX as u64)
                .context("native input fresh-id allocation exceeds the usable Value domain")?;
            if !slots.is_empty() {
                transaction.execute(
                    &format!(
                        "UPDATE {COUNTERS_TABLE} SET value = CAST('{next_fresh}' AS UBIGINT) WHERE name = 'fresh_id'"
                    ),
                    [],
                )?;
            }

            let generation = transaction.query_row(
                &format!("SELECT value FROM {COUNTERS_TABLE} WHERE name = 'generation'"),
                [],
                |row| row.get::<_, u64>(0),
            )?;

            for (function, info, rows) in grouped {
                let rows = rows
                    .into_iter()
                    .map(|row| {
                        info.columns
                            .iter()
                            .zip(row)
                            .map(|(&ty, value)| {
                                let value = match value {
                                    NativeInputValue::Existing(value) => value,
                                    NativeInputValue::FreshSlot(slot) => {
                                        let value = first_fresh + u64::from(slot);
                                        Value::new(u32::try_from(value).expect(
                                            "fresh-id range was checked before row encoding",
                                        ))
                                    }
                                };
                                ty.sql_literal(base_values, value)
                            })
                            .collect::<Result<Vec<_>>>()
                    })
                    .collect::<Result<Vec<_>>>()?;
                if info.write_capability == WriteCapability::AssertEq {
                    let conflict_sql = input_assert_eq_conflict_sql(function, &info, &rows);
                    let conflict = transaction.query_row(&conflict_sql, [], |row| row.get(0))?;
                    #[cfg(test)]
                    executed_sql.push(conflict_sql);
                    if conflict {
                        bail!(
                            "illegal MergeFn::AssertEq conflict for table `{}`",
                            info.name
                        );
                    }
                }
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

    pub(crate) fn table_info(&self, id: FunctionId) -> Result<TableInfo> {
        let state = self.state.lock().expect("DuckDB storage mutex poisoned");
        table_info(&state, id).cloned()
    }

    pub(crate) fn execute_rules(
        &self,
        scheduled: &[(&CompiledRule, u64)],
    ) -> Result<RuleExecutionStats> {
        if scheduled.is_empty() {
            return Ok(RuleExecutionStats::default());
        }

        let path_rules = scheduled
            .iter()
            .filter(|(rule, _)| rule.path_compression().is_some())
            .count();
        let rebuild_rules = scheduled
            .iter()
            .filter(|(rule, _)| rule.standard_rebuild().is_some())
            .count();
        let marker_rules = scheduled
            .iter()
            .filter(|(rule, _)| rule.marker_rekey().is_some())
            .count();
        let rebuilding_rules = rebuild_rules + marker_rules;
        if rebuilding_rules != 0 {
            if rebuilding_rules != scheduled.len() {
                bail!(
                    "DuckDB cannot mix direct/path-compression plans with rebuilding plans in one bounded ruleset"
                );
            }
            return self.execute_rebuilding_rules(scheduled);
        }
        if path_rules != 0 {
            if path_rules != scheduled.len() {
                bail!(
                    "DuckDB cannot yet mix direct-Set and staged path-compression plans in one bounded ruleset"
                );
            }
            return self.execute_path_compression_rules(scheduled);
        }

        let mut state = self.state.lock().expect("DuckDB storage mutex poisoned");
        let run = state.next_rule_run;
        let next_rule_run = state
            .next_rule_run
            .checked_add(1)
            .context("DuckDB rule-stage identifier overflow")?;
        let transaction = state.connection.transaction()?;
        #[cfg(test)]
        let mut sql_log = Vec::new();
        let mut stage_names = Vec::with_capacity(scheduled.len());
        let mut matched_rows = Vec::with_capacity(scheduled.len());
        let mut inserted_rows = vec![0; scheduled.len()];
        let mut statement_count = 0;

        let execute = (|| -> Result<(u64, bool)> {
            let generation = transaction.query_row(
                &format!("SELECT value FROM {COUNTERS_TABLE} WHERE name = 'generation'"),
                [],
                |row| row.get::<_, u64>(0),
            )?;
            statement_count += 1;

            // Materialize every match relation before applying any target
            // effect. These session-local tables are dropped before commit;
            // their contents are never mirrored or enumerated in Rust.
            for (schedule_index, (rule, watermark)) in scheduled.iter().enumerate() {
                let stage = format!("egglog_rule_stage_{run}_{schedule_index}");
                stage_names.push(stage.clone());
                let create = rule.materialize_sql(&stage, *watermark);
                transaction.execute(&create, [])?;
                #[cfg(test)]
                sql_log.push(create);
                statement_count += 1;

                let count_sql = format!("SELECT count(*) FROM {stage}");
                let count = transaction.query_row(&count_sql, [], |row| row.get::<_, u64>(0))?;
                matched_rows
                    .push(usize::try_from(count).context("DuckDB rule match count exceeds usize")?);
                #[cfg(test)]
                sql_log.push(count_sql);
                statement_count += 1;
            }

            // Reference applies every scheduled Delete before any Set/merge,
            // independent of rule schedule order. A real Delete advances the
            // physical freshness generation but deliberately does not set the
            // Reference-compatible public `changed` report.
            let mut physical_changed = false;
            let mut report_changed = false;
            for ((rule, _), stage) in scheduled.iter().zip(&stage_names) {
                for delete in rule.delete_sql(stage) {
                    let deleted = transaction.execute(&delete, [])?;
                    physical_changed |= deleted != 0;
                    #[cfg(test)]
                    sql_log.push(delete);
                    statement_count += 1;
                }
            }

            // Set/conflict effects retain schedule order so a later AssertEq
            // observes an earlier scheduled insert atomically.
            for (schedule_index, ((rule, _), stage)) in
                scheduled.iter().zip(&stage_names).enumerate()
            {
                if let Some(conflict_sql) = rule.conflict_sql(stage) {
                    let conflict = transaction.query_row(&conflict_sql, [], |row| row.get(0))?;
                    #[cfg(test)]
                    sql_log.push(conflict_sql);
                    statement_count += 1;
                    if conflict {
                        bail!("illegal MergeFn::AssertEq conflict in scheduled rule");
                    }
                }
                if let Some(insert) = rule.insert_sql(stage, generation) {
                    let inserted = transaction.execute(&insert, [])?;
                    physical_changed |= inserted != 0;
                    report_changed |= inserted != 0;
                    inserted_rows[schedule_index] = inserted;
                    #[cfg(test)]
                    sql_log.push(insert);
                    statement_count += 1;
                }
            }

            // Subsume last. UPDATE preserves any same-wave Set value; INSERT
            // restores the staged pre-wave row after a same-wave Delete.
            for ((rule, _), stage) in scheduled.iter().zip(&stage_names) {
                for subsume in rule.subsume_sql(stage, generation) {
                    let transitioned = transaction.execute(&subsume, [])?;
                    physical_changed |= transitioned != 0;
                    report_changed |= transitioned != 0;
                    #[cfg(test)]
                    sql_log.push(subsume);
                    statement_count += 1;
                }
            }

            if physical_changed {
                let update = format!(
                    "UPDATE {COUNTERS_TABLE} SET value = value + 1 WHERE name = 'generation'"
                );
                transaction.execute(&update, [])?;
                #[cfg(test)]
                sql_log.push(update);
                statement_count += 1;
            }

            for stage in &stage_names {
                let drop = format!("DROP TABLE {stage}");
                transaction.execute(&drop, [])?;
                #[cfg(test)]
                sql_log.push(drop);
                statement_count += 1;
            }
            Ok((generation, report_changed))
        })();

        let (watermark, changed) = match execute {
            Ok(result) => result,
            Err(error) => {
                let rollback_error = transaction.rollback().err();
                let cleanup_error = cleanup_scratch(&state.connection, &stage_names).err();
                if rollback_error.is_some() || cleanup_error.is_some() {
                    return Err(anyhow!(
                        "DuckDB rule transaction failed: {error:#}; rollback: {rollback_error:?}; scratch cleanup: {cleanup_error:?}"
                    ));
                }
                return Err(error);
            }
        };
        transaction.commit()?;
        state.next_rule_run = next_rule_run;
        #[cfg(test)]
        {
            state.latest_rule_sql = sql_log;
        }
        Ok(RuleExecutionStats {
            changed,
            watermark,
            matched_rows,
            inserted_rows,
            statement_count,
        })
    }

    fn execute_path_compression_rules(
        &self,
        scheduled: &[(&CompiledRule, u64)],
    ) -> Result<RuleExecutionStats> {
        #[derive(Clone)]
        struct QueueGroup {
            plan: PathCompressionPlan,
            queue: String,
        }

        let mut state = self.state.lock().expect("DuckDB storage mutex poisoned");
        let run = state.next_rule_run;
        let next_rule_run = state
            .next_rule_run
            .checked_add(1)
            .context("DuckDB rule-stage identifier overflow")?;
        let transaction = state.connection.transaction()?;
        #[cfg(test)]
        let mut sql_log = Vec::new();
        let mut scratch_names = Vec::<String>::new();
        let mut matched_rows = Vec::with_capacity(scheduled.len());
        let mut inserted_rows = vec![0; scheduled.len()];
        let mut statement_count = 0;

        let execute = (|| -> Result<(u64, bool)> {
            let generation = transaction.query_row(
                &format!("SELECT value FROM {COUNTERS_TABLE} WHERE name = 'generation'"),
                [],
                |row| row.get::<_, u64>(0),
            )?;
            statement_count += 1;
            let first_head_id = transaction.query_row(
                &format!("SELECT value FROM {COUNTERS_TABLE} WHERE name = 'fresh_id'"),
                [],
                |row| row.get::<_, u64>(0),
            )?;
            statement_count += 1;

            // The stable pre-wave contract applies to every scheduled rule,
            // including different union-find targets.  No effect statement is
            // issued until every match relation exists.
            let mut stages = Vec::with_capacity(scheduled.len());
            for (schedule_index, (rule, watermark)) in scheduled.iter().enumerate() {
                let stage = format!("egglog_path_stage_{run}_{schedule_index}");
                scratch_names.push(stage.clone());
                let create = rule.materialize_sql(&stage, *watermark);
                transaction.execute(&create, [])?;
                #[cfg(test)]
                sql_log.push(create);
                statement_count += 1;
                let count_sql = format!("SELECT count(*) FROM {stage}");
                let count = transaction.query_row(&count_sql, [], |row| row.get::<_, u64>(0))?;
                #[cfg(test)]
                sql_log.push(count_sql);
                statement_count += 1;
                matched_rows
                    .push(usize::try_from(count).context("DuckDB path match count exceeds usize")?);
                stages.push(stage);
            }

            let head_count = matched_rows.iter().try_fold(0_u64, |total, &count| {
                total
                    .checked_add(u64::try_from(count).context("path match count exceeds u64")?)
                    .context("path head fresh-id count overflow")
            })?;
            let after_heads = checked_fresh_end(first_head_id, head_count, "path rule heads")?;
            if head_count != 0 {
                let update = format!(
                    "UPDATE {COUNTERS_TABLE} SET value = CAST('{after_heads}' AS UBIGINT) WHERE name = 'fresh_id'"
                );
                transaction.execute(&update, [])?;
                #[cfg(test)]
                sql_log.push(update);
                statement_count += 1;
            }

            let mut groups = Vec::<QueueGroup>::new();
            let mut group_indices = BTreeMap::<(u32, u32, u32), usize>::new();
            for (rule, _) in scheduled {
                let plan = rule
                    .path_compression()
                    .expect("caller checked every scheduled plan");
                if group_indices.contains_key(&plan.group_key()) {
                    continue;
                }
                let index = groups.len();
                let queue = format!("egglog_path_queue_{run}_{index}");
                scratch_names.push(queue.clone());
                let create = format!(
                    "CREATE TEMP TABLE {queue} (
                         __wave UBIGINT NOT NULL,
                         __event_ordinal UBIGINT NOT NULL,
                         c0 UBIGINT NOT NULL,
                         c1 UBIGINT NOT NULL,
                         c2 UBIGINT NOT NULL
                     )"
                );
                transaction.execute(&create, [])?;
                #[cfg(test)]
                sql_log.push(create);
                statement_count += 1;
                group_indices.insert(plan.group_key(), index);
                groups.push(QueueGroup {
                    plan: plan.clone(),
                    queue,
                });
            }

            // Reserve and assign all rule-head ids before any collision can
            // reserve a Sym/Trans pair.  IDs and event ordinals follow schedule
            // order, then the canonical match ordinal inside each stage.
            let mut head_offset = 0_u64;
            let mut event_offset = 0_u64;
            let mut changed = false;
            for (schedule_index, ((rule, _), stage)) in scheduled.iter().zip(&stages).enumerate() {
                let plan = rule
                    .path_compression()
                    .expect("caller checked every scheduled plan");
                let count = u64::try_from(matched_rows[schedule_index])?;
                let head_base = first_head_id
                    .checked_add(head_offset)
                    .context("path head fresh-id offset overflow")?;
                let proof_stage = format!("egglog_path_head_proof_{run}_{schedule_index}");
                scratch_names.push(proof_stage.clone());
                let create = format!(
                    "CREATE TEMP TABLE {proof_stage} AS
                     SELECT c2 AS c0,
                            c4 AS c1,
                            CAST('{head_base}' AS UBIGINT) + __match_ordinal - 1 AS c2,
                            CAST(TRUE AS BOOLEAN) AS c3,
                            __match_ordinal AS __ordinal
                     FROM {stage}"
                );
                transaction.execute(&create, [])?;
                #[cfg(test)]
                sql_log.push(create);
                statement_count += 1;
                let conflict_sql =
                    check_assert_eq_conflict(&transaction, plan.trans, 3, &proof_stage)?;
                #[cfg(test)]
                sql_log.push(conflict_sql);
                #[cfg(not(test))]
                drop(conflict_sql);
                statement_count += 1;
                let insert = stage_insert_sql(plan.trans, 4, 3, &proof_stage, generation);
                let inserted = transaction.execute(&insert, [])?;
                inserted_rows[schedule_index] = inserted;
                changed |= inserted != 0;
                #[cfg(test)]
                sql_log.push(insert);
                statement_count += 1;

                let group = &groups[group_indices[&plan.group_key()]];
                let enqueue = format!(
                    "INSERT INTO {} (__wave, __event_ordinal, c0, c1, c2)
                     SELECT CAST('0' AS UBIGINT),
                            CAST('{event_offset}' AS UBIGINT) + __match_ordinal,
                            c0,
                            c3,
                            CAST('{head_base}' AS UBIGINT) + __match_ordinal - 1
                     FROM {stage}
                     ORDER BY __match_ordinal",
                    group.queue
                );
                let enqueued = transaction.execute(&enqueue, [])?;
                ensure_count(enqueued, count, "path head candidate enqueue")?;
                #[cfg(test)]
                sql_log.push(enqueue);
                statement_count += 1;
                head_offset = head_offset
                    .checked_add(count)
                    .context("path head offset overflow")?;
                event_offset = event_offset
                    .checked_add(count)
                    .context("path event ordinal overflow")?;
            }

            // Corrupt duplicate owners would make a set-wise fold ambiguous.
            // Reject before the first candidate mutation rather than choosing
            // an incidental physical row.
            for group in &groups {
                let uf = sql_table(group.plan.union_find);
                let check = format!(
                    "SELECT EXISTS (
                         SELECT 1 FROM {uf} GROUP BY c0 HAVING count(*) > 1
                     ) OR EXISTS (
                         SELECT 1 FROM {uf} WHERE __subsumed
                     )"
                );
                let invalid = transaction.query_row(&check, [], |row| row.get::<_, bool>(0))?;
                #[cfg(test)]
                sql_log.push(check);
                statement_count += 1;
                if invalid {
                    bail!("DuckDB path executor found duplicate or subsumed union-find owners");
                }
            }

            let mut wave = 0_u64;
            let mut next_event = event_offset;
            let mut pass = 0_u64;
            loop {
                // Globally drain wave w for every independent UF target before
                // any generated w+1 candidate becomes eligible.
                for group in &groups {
                    loop {
                        let count_sql = format!(
                            "SELECT count(*) FROM {} WHERE __wave = CAST('{wave}' AS UBIGINT)",
                            group.queue
                        );
                        let pending =
                            transaction.query_row(&count_sql, [], |row| row.get::<_, u64>(0))?;
                        #[cfg(test)]
                        sql_log.push(count_sql);
                        statement_count += 1;
                        if pending == 0 {
                            break;
                        }

                        let outcome = format!("egglog_path_outcome_{run}_{pass}");
                        let collision = format!("egglog_path_collision_{run}_{pass}");
                        let sym_stage = format!("egglog_path_sym_{run}_{pass}");
                        let trans_stage = format!("egglog_path_trans_{run}_{pass}");
                        scratch_names.extend([
                            outcome.clone(),
                            collision.clone(),
                            sym_stage.clone(),
                            trans_stage.clone(),
                        ]);
                        let uf = sql_table(group.plan.union_find);
                        let create_outcome = format!(
                            "CREATE TEMP TABLE {outcome} AS
                             WITH selected AS (
                                 SELECT __wave, __event_ordinal, c0, c1, c2
                                 FROM (
                                     SELECT queued.*,
                                            row_number() OVER (
                                                PARTITION BY c0
                                                ORDER BY __event_ordinal, c1, c2
                                            ) AS __key_rank
                                     FROM {} AS queued
                                     WHERE __wave = CAST('{wave}' AS UBIGINT)
                                 )
                                 WHERE __key_rank = 1
                             )
                             SELECT selected.__wave,
                                    selected.__event_ordinal,
                                    selected.c0 AS candidate_key,
                                    selected.c1 AS new_parent,
                                    selected.c2 AS new_proof,
                                    existing.c1 AS old_parent,
                                    existing.c2 AS old_proof,
                                    existing.__generation AS old_generation,
                                    existing.__subsumed AS old_subsumed
                             FROM selected
                             LEFT JOIN {uf} AS existing
                               ON existing.c0 IS NOT DISTINCT FROM selected.c0",
                            group.queue
                        );
                        transaction.execute(&create_outcome, [])?;
                        #[cfg(test)]
                        sql_log.push(create_outcome);
                        statement_count += 1;

                        let delete = format!(
                            "DELETE FROM {} AS queued
                             USING {outcome} AS selected
                             WHERE queued.__wave = selected.__wave
                               AND queued.__event_ordinal = selected.__event_ordinal",
                            group.queue
                        );
                        transaction.execute(&delete, [])?;
                        #[cfg(test)]
                        sql_log.push(delete);
                        statement_count += 1;

                        let insert_missing = format!(
                            "INSERT INTO {uf} (c0, c1, c2, __generation, __subsumed)
                             SELECT candidate_key,
                                    new_parent,
                                    new_proof,
                                    CAST('{generation}' AS UBIGINT),
                                    FALSE
                             FROM {outcome}
                             WHERE old_parent IS NULL
                             ORDER BY __event_ordinal"
                        );
                        let inserted = transaction.execute(&insert_missing, [])?;
                        changed |= inserted != 0;
                        #[cfg(test)]
                        sql_log.push(insert_missing);
                        statement_count += 1;

                        let create_collision = format!(
                            "CREATE TEMP TABLE {collision} AS
                             SELECT outcome.*,
                                    CASE WHEN old_parent < new_parent
                                         THEN old_parent ELSE new_parent END AS min_parent,
                                    CASE WHEN old_parent > new_parent
                                         THEN old_parent ELSE new_parent END AS max_parent,
                                    CASE WHEN old_parent < new_parent
                                         THEN old_proof ELSE new_proof END AS lo_proof,
                                    CASE WHEN old_parent > new_parent
                                         THEN old_proof ELSE new_proof END AS hi_proof,
                                    row_number() OVER (
                                        ORDER BY __event_ordinal, candidate_key,
                                                 new_parent, new_proof
                                    ) AS __collision_ordinal
                             FROM {outcome} AS outcome
                             WHERE old_parent IS NOT NULL
                               AND old_parent IS DISTINCT FROM new_parent"
                        );
                        transaction.execute(&create_collision, [])?;
                        #[cfg(test)]
                        sql_log.push(create_collision);
                        statement_count += 1;
                        let collision_count_sql = format!("SELECT count(*) FROM {collision}");
                        let collision_count =
                            transaction
                                .query_row(&collision_count_sql, [], |row| row.get::<_, u64>(0))?;
                        #[cfg(test)]
                        sql_log.push(collision_count_sql);
                        statement_count += 1;

                        if collision_count != 0 {
                            let first_collision_id = transaction.query_row(
                                &format!(
                                    "SELECT value FROM {COUNTERS_TABLE} WHERE name = 'fresh_id'"
                                ),
                                [],
                                |row| row.get::<_, u64>(0),
                            )?;
                            statement_count += 1;
                            let collision_ids = collision_count
                                .checked_mul(2)
                                .context("path collision fresh-id count overflow")?;
                            let after_collisions = checked_fresh_end(
                                first_collision_id,
                                collision_ids,
                                "path merge collisions",
                            )?;
                            let reserve = format!(
                                "UPDATE {COUNTERS_TABLE} SET value = CAST('{after_collisions}' AS UBIGINT) WHERE name = 'fresh_id'"
                            );
                            transaction.execute(&reserve, [])?;
                            #[cfg(test)]
                            sql_log.push(reserve);
                            statement_count += 1;

                            let create_sym = format!(
                                "CREATE TEMP TABLE {sym_stage} AS
                                 SELECT hi_proof AS c0,
                                        CAST('{first_collision_id}' AS UBIGINT)
                                            + 2 * (__collision_ordinal - 1) AS c1,
                                        CAST(TRUE AS BOOLEAN) AS c2,
                                        __collision_ordinal AS __ordinal
                                 FROM {collision}"
                            );
                            transaction.execute(&create_sym, [])?;
                            #[cfg(test)]
                            sql_log.push(create_sym);
                            statement_count += 1;
                            let conflict_sql = check_assert_eq_conflict(
                                &transaction,
                                group.plan.sym,
                                2,
                                &sym_stage,
                            )?;
                            #[cfg(test)]
                            sql_log.push(conflict_sql);
                            #[cfg(not(test))]
                            drop(conflict_sql);
                            statement_count += 1;
                            let insert_sym =
                                stage_insert_sql(group.plan.sym, 3, 2, &sym_stage, generation);
                            let sym_inserted = transaction.execute(&insert_sym, [])?;
                            changed |= sym_inserted != 0;
                            #[cfg(test)]
                            sql_log.push(insert_sym);
                            statement_count += 1;

                            let create_trans = format!(
                                "CREATE TEMP TABLE {trans_stage} AS
                                 SELECT CAST('{first_collision_id}' AS UBIGINT)
                                            + 2 * (__collision_ordinal - 1) AS c0,
                                        lo_proof AS c1,
                                        CAST('{first_collision_id}' AS UBIGINT)
                                            + 2 * (__collision_ordinal - 1) + 1 AS c2,
                                        CAST(TRUE AS BOOLEAN) AS c3,
                                        __collision_ordinal AS __ordinal
                                 FROM {collision}"
                            );
                            transaction.execute(&create_trans, [])?;
                            #[cfg(test)]
                            sql_log.push(create_trans);
                            statement_count += 1;
                            let conflict_sql = check_assert_eq_conflict(
                                &transaction,
                                group.plan.trans,
                                3,
                                &trans_stage,
                            )?;
                            #[cfg(test)]
                            sql_log.push(conflict_sql);
                            #[cfg(not(test))]
                            drop(conflict_sql);
                            statement_count += 1;
                            let insert_trans =
                                stage_insert_sql(group.plan.trans, 4, 3, &trans_stage, generation);
                            let trans_inserted = transaction.execute(&insert_trans, [])?;
                            changed |= trans_inserted != 0;
                            #[cfg(test)]
                            sql_log.push(insert_trans);
                            statement_count += 1;

                            let update_owner = format!(
                                "UPDATE {uf} AS existing
                                 SET c1 = collision.min_parent,
                                     c2 = collision.lo_proof,
                                     __generation = CAST('{generation}' AS UBIGINT)
                                 FROM {collision} AS collision
                                 WHERE existing.c0 IS NOT DISTINCT FROM collision.candidate_key
                                   AND (existing.c1 IS DISTINCT FROM collision.min_parent
                                        OR existing.c2 IS DISTINCT FROM collision.lo_proof)"
                            );
                            let updated = transaction.execute(&update_owner, [])?;
                            changed |= updated != 0;
                            #[cfg(test)]
                            sql_log.push(update_owner);
                            statement_count += 1;

                            let next_wave =
                                wave.checked_add(1).context("path logical wave overflow")?;
                            let enqueue_generated = format!(
                                "INSERT INTO {} (__wave, __event_ordinal, c0, c1, c2)
                                 SELECT CAST('{next_wave}' AS UBIGINT),
                                        CAST('{next_event}' AS UBIGINT) + __collision_ordinal,
                                        max_parent,
                                        min_parent,
                                        CAST('{first_collision_id}' AS UBIGINT)
                                            + 2 * (__collision_ordinal - 1) + 1
                                 FROM {collision}
                                 ORDER BY __collision_ordinal",
                                group.queue
                            );
                            let generated = transaction.execute(&enqueue_generated, [])?;
                            ensure_count(
                                generated,
                                collision_count,
                                "path generated candidate enqueue",
                            )?;
                            #[cfg(test)]
                            sql_log.push(enqueue_generated);
                            statement_count += 1;
                            next_event = next_event
                                .checked_add(collision_count)
                                .context("path generated event ordinal overflow")?;
                        }

                        for scratch in [&sym_stage, &trans_stage, &collision, &outcome] {
                            let drop = format!("DROP TABLE IF EXISTS {scratch}");
                            transaction.execute(&drop, [])?;
                            #[cfg(test)]
                            sql_log.push(drop);
                            statement_count += 1;
                        }
                        pass = pass
                            .checked_add(1)
                            .context("path fold-pass identifier overflow")?;
                    }
                }

                let mut remaining = 0_u64;
                for group in &groups {
                    let count_sql = format!("SELECT count(*) FROM {}", group.queue);
                    let count =
                        transaction.query_row(&count_sql, [], |row| row.get::<_, u64>(0))?;
                    #[cfg(test)]
                    sql_log.push(count_sql);
                    statement_count += 1;
                    remaining = remaining
                        .checked_add(count)
                        .context("path queue row count overflow")?;
                }
                if remaining == 0 {
                    break;
                }
                wave = wave.checked_add(1).context("path logical wave overflow")?;
            }

            if changed {
                let update = format!(
                    "UPDATE {COUNTERS_TABLE} SET value = value + 1 WHERE name = 'generation'"
                );
                transaction.execute(&update, [])?;
                #[cfg(test)]
                sql_log.push(update);
                statement_count += 1;
            }

            for scratch in scratch_names.iter().rev() {
                let drop = format!("DROP TABLE IF EXISTS {scratch}");
                transaction.execute(&drop, [])?;
                #[cfg(test)]
                sql_log.push(drop);
                statement_count += 1;
            }
            Ok((generation, changed))
        })();

        let (watermark, changed) = match execute {
            Ok(result) => result,
            Err(error) => {
                let rollback_error = transaction.rollback().err();
                let cleanup_error = cleanup_scratch(&state.connection, &scratch_names).err();
                if rollback_error.is_some() || cleanup_error.is_some() {
                    return Err(anyhow!(
                        "DuckDB path transaction failed: {error:#}; rollback: {rollback_error:?}; scratch cleanup: {cleanup_error:?}"
                    ));
                }
                return Err(error);
            }
        };
        transaction.commit()?;
        state.next_rule_run = next_rule_run;
        #[cfg(test)]
        {
            state.latest_rule_sql = sql_log;
        }
        Ok(RuleExecutionStats {
            changed,
            watermark,
            matched_rows,
            inserted_rows,
            statement_count,
        })
    }

    fn execute_rebuilding_rules(
        &self,
        scheduled: &[(&CompiledRule, u64)],
    ) -> Result<RuleExecutionStats> {
        #[derive(Clone)]
        struct QueueGroup {
            plan: OrderedUnionPlan,
            queue: String,
        }

        #[derive(Clone, Copy)]
        struct OwnerCheck {
            n_keys: usize,
            reject_subsumed: bool,
        }

        // Resolve the complete target graph before opening the transaction.
        // FunctionId order is the deterministic target order of every wave.
        let mut target_plans = BTreeMap::<u32, OrderedUnionPlan>::new();
        let mut owner_checks = BTreeMap::<u32, OwnerCheck>::new();
        for (rule, _) in scheduled {
            if let Some(plan) = rule.standard_rebuild() {
                for target in [&plan.view, &plan.union_find, &plan.displaced_union_find] {
                    if let Some(existing) = target_plans.get(&target.target.rep()) {
                        if existing != target {
                            bail!(
                                "DuckDB rebuilding target {} has inconsistent ordered-union plans",
                                target.target.rep()
                            );
                        }
                    } else {
                        target_plans.insert(target.target.rep(), target.clone());
                    }
                    let check = OwnerCheck {
                        n_keys: target.n_keys,
                        reject_subsumed: target.orientation == OrderedUnionOrientation::KeyToParent,
                    };
                    if let Some(existing) = owner_checks.get(&target.target.rep()) {
                        if existing.n_keys != check.n_keys
                            || existing.reject_subsumed != check.reject_subsumed
                        {
                            bail!(
                                "DuckDB rebuilding target {} has inconsistent owner checks",
                                target.target.rep()
                            );
                        }
                    } else {
                        owner_checks.insert(target.target.rep(), check);
                    }
                }
            } else if let Some(plan) = rule.marker_rekey() {
                for (target, check) in [
                    (
                        plan.marker,
                        OwnerCheck {
                            n_keys: plan.n_keys,
                            reject_subsumed: false,
                        },
                    ),
                    (
                        plan.union_find.target,
                        OwnerCheck {
                            n_keys: plan.union_find.n_keys,
                            reject_subsumed: true,
                        },
                    ),
                ] {
                    if let Some(existing) = owner_checks.get(&target.rep()) {
                        if existing.n_keys != check.n_keys
                            || existing.reject_subsumed != check.reject_subsumed
                        {
                            bail!(
                                "DuckDB rebuilding target {} has inconsistent owner checks",
                                target.rep()
                            );
                        }
                    } else {
                        owner_checks.insert(target.rep(), check);
                    }
                }
            } else {
                unreachable!("caller checked every scheduled rebuilding plan");
            }
        }

        let mut state = self.state.lock().expect("DuckDB storage mutex poisoned");
        let run = state.next_rule_run;
        let next_rule_run = state
            .next_rule_run
            .checked_add(1)
            .context("DuckDB rule-stage identifier overflow")?;
        let transaction = state.connection.transaction()?;
        #[cfg(test)]
        let mut sql_log = Vec::new();
        let mut scratch_names = Vec::<String>::new();
        let mut matched_rows = Vec::with_capacity(scheduled.len());
        let mut inserted_rows = vec![0; scheduled.len()];
        let mut statement_count = 0;

        let execute = (|| -> Result<(u64, bool)> {
            // These are the only reads of the durable generation/fresh
            // counters. Later collision reservations advance `next_fresh` in
            // scalar Rust state and update the same transactional counter.
            let generation = transaction.query_row(
                &format!("SELECT value FROM {COUNTERS_TABLE} WHERE name = 'generation'"),
                [],
                |row| row.get::<_, u64>(0),
            )?;
            statement_count += 1;
            let first_head_id = transaction.query_row(
                &format!("SELECT value FROM {COUNTERS_TABLE} WHERE name = 'fresh_id'"),
                [],
                |row| row.get::<_, u64>(0),
            )?;
            statement_count += 1;

            // Stable pre-wave: no durable effect is issued until every match
            // relation has been materialized and counted.
            let mut stages = Vec::with_capacity(scheduled.len());
            for (schedule_index, (rule, watermark)) in scheduled.iter().enumerate() {
                let stage = format!("egglog_rebuild_stage_{run}_{schedule_index}");
                scratch_names.push(stage.clone());
                let create = rule.materialize_sql(&stage, *watermark);
                transaction.execute(&create, [])?;
                #[cfg(test)]
                sql_log.push(create);
                statement_count += 1;
                let count_sql = format!("SELECT count(*) FROM {stage}");
                let count = transaction.query_row(&count_sql, [], |row| row.get::<_, u64>(0))?;
                #[cfg(test)]
                sql_log.push(count_sql);
                statement_count += 1;
                matched_rows.push(
                    usize::try_from(count)
                        .context("DuckDB rebuilding match count exceeds usize")?,
                );
                stages.push(stage);
            }

            let mut groups = Vec::<QueueGroup>::with_capacity(target_plans.len());
            let mut group_indices = BTreeMap::<u32, usize>::new();
            for plan in target_plans.values() {
                let index = groups.len();
                let queue = format!("egglog_rebuild_queue_{run}_{index}");
                scratch_names.push(queue.clone());
                let mut columns = vec![
                    "__wave UBIGINT NOT NULL".to_string(),
                    "__event_ordinal UBIGINT NOT NULL".to_string(),
                ];
                columns.extend(
                    plan.columns
                        .iter()
                        .enumerate()
                        .map(|(column, ty)| format!("c{column} {} NOT NULL", ty.sql())),
                );
                let create = format!("CREATE TEMP TABLE {queue} ({})", columns.join(", "));
                transaction.execute(&create, [])?;
                #[cfg(test)]
                sql_log.push(create);
                statement_count += 1;
                group_indices.insert(plan.target.rep(), index);
                groups.push(QueueGroup {
                    plan: plan.clone(),
                    queue,
                });
            }

            // Corrupt physical owners make a key fold/rekey ambiguous. Check
            // every Standard View/UF plus every Marker/UF target before the
            // first durable row/counter mutation.
            for (&target_id, check) in &owner_checks {
                let target_id = FunctionId::new(target_id);
                let target = sql_table(target_id);
                let duplicate = duplicate_owner_sql(&target, check.n_keys);
                let has_duplicate =
                    transaction.query_row(&duplicate, [], |row| row.get::<_, bool>(0))?;
                #[cfg(test)]
                sql_log.push(duplicate);
                statement_count += 1;
                if has_duplicate {
                    bail!(
                        "DuckDB rebuilding executor found duplicate owners for function {}",
                        target_id.rep()
                    );
                }
                if check.reject_subsumed {
                    let subsumed =
                        format!("SELECT EXISTS (SELECT 1 FROM {target} WHERE __subsumed)");
                    let has_subsumed =
                        transaction.query_row(&subsumed, [], |row| row.get::<_, bool>(0))?;
                    #[cfg(test)]
                    sql_log.push(subsumed);
                    statement_count += 1;
                    if has_subsumed {
                        bail!(
                            "DuckDB rebuilding executor found a subsumed UF owner for function {}",
                            target_id.rep()
                        );
                    }
                }
            }

            let head_count = scheduled.iter().zip(&matched_rows).try_fold(
                0_u64,
                |total, ((rule, _), &count)| {
                    let slots = rule
                        .standard_rebuild()
                        .map_or(0, |plan| plan.kind.head_fresh_slots());
                    let count =
                        u64::try_from(count).context("standard rebuild match count exceeds u64")?;
                    total
                        .checked_add(
                            count
                                .checked_mul(slots)
                                .context("standard rebuild head fresh-id count overflow")?,
                        )
                        .context("standard rebuild head fresh-id count overflow")
                },
            )?;
            let after_heads =
                checked_fresh_end(first_head_id, head_count, "standard rebuild rule heads")?;
            if head_count != 0 {
                let reserve = format!(
                    "UPDATE {COUNTERS_TABLE} SET value = CAST('{after_heads}' AS UBIGINT) WHERE name = 'fresh_id'"
                );
                transaction.execute(&reserve, [])?;
                #[cfg(test)]
                sql_log.push(reserve);
                statement_count += 1;
            }
            let mut next_fresh = after_heads;

            let mut physical_changed = false;
            let mut report_changed = false;

            // All Standard key-rekey and Marker stale-key Deletes precede
            // every independent head Set.
            for ((rule, _), stage) in scheduled.iter().zip(&stages) {
                if let Some(plan) = rule.standard_rebuild()
                    && matches!(plan.kind, StandardRebuildKind::EqKey { .. })
                {
                    let equality = key_equality("existing", "staged", plan.view.n_keys);
                    let delete = format!(
                        "DELETE FROM {} AS existing
                         WHERE EXISTS (SELECT 1 FROM {stage} AS staged WHERE {equality})",
                        sql_table(plan.view.target)
                    );
                    let deleted = transaction.execute(&delete, [])?;
                    physical_changed |= deleted != 0;
                    #[cfg(test)]
                    sql_log.push(delete);
                    statement_count += 1;
                } else if let Some(plan) = rule.marker_rekey() {
                    let delete = plan.delete_sql(stage);
                    let deleted = transaction.execute(&delete, [])?;
                    physical_changed |= deleted != 0;
                    #[cfg(test)]
                    sql_log.push(delete);
                    statement_count += 1;
                }
            }

            // Independent proof constructor heads retain schedule, match, and
            // action-slot order. They are the only per-rule inserted telemetry.
            let mut head_offset = 0_u64;
            let mut head_bases = Vec::with_capacity(scheduled.len());
            for (schedule_index, ((rule, _), stage)) in scheduled.iter().zip(&stages).enumerate() {
                let head_base = first_head_id
                    .checked_add(head_offset)
                    .context("standard rebuild head fresh-id offset overflow")?;
                head_bases.push(head_base);
                if let Some(marker) = rule.marker_rekey() {
                    let head_stage = format!("egglog_rebuild_marker_head_{run}_{schedule_index}");
                    scratch_names.push(head_stage.clone());
                    let create = marker.create_head_stage_sql(stage, &head_stage);
                    transaction.execute(&create, [])?;
                    #[cfg(test)]
                    sql_log.push(create);
                    statement_count += 1;
                    let conflict = check_assert_eq_conflict(
                        &transaction,
                        marker.marker,
                        marker.n_keys,
                        &head_stage,
                    )?;
                    #[cfg(test)]
                    sql_log.push(conflict);
                    #[cfg(not(test))]
                    drop(conflict);
                    statement_count += 1;
                    let insert = stage_insert_sql(
                        marker.marker,
                        marker.arity(),
                        marker.n_keys,
                        &head_stage,
                        generation,
                    );
                    let inserted = transaction.execute(&insert, [])?;
                    inserted_rows[schedule_index] = inserted;
                    physical_changed |= inserted != 0;
                    report_changed |= inserted != 0;
                    #[cfg(test)]
                    sql_log.push(insert);
                    statement_count += 1;
                    continue;
                }

                let plan = rule
                    .standard_rebuild()
                    .expect("caller checked every scheduled rebuilding plan");
                let count = u64::try_from(matched_rows[schedule_index])?;
                let view_arity = plan.view.arity();
                let view_payload = plan.view.n_keys + 1;
                let edge_payload = view_arity + 1;
                match &plan.kind {
                    StandardRebuildKind::EqKey {
                        child_index_sql,
                        congr,
                        ..
                    } => {
                        let proof_stage =
                            format!("egglog_rebuild_head_congr_{run}_{schedule_index}");
                        scratch_names.push(proof_stage.clone());
                        let create = format!(
                            "CREATE TEMP TABLE {proof_stage} AS
                             SELECT c{view_payload} AS c0,
                                    {child_index_sql} AS c1,
                                    c{edge_payload} AS c2,
                                    CAST('{head_base}' AS UBIGINT) + __match_ordinal - 1 AS c3,
                                    CAST(TRUE AS BOOLEAN) AS c4,
                                    __match_ordinal AS __ordinal
                             FROM {stage}"
                        );
                        transaction.execute(&create, [])?;
                        #[cfg(test)]
                        sql_log.push(create);
                        statement_count += 1;
                        let conflict =
                            check_assert_eq_conflict(&transaction, *congr, 4, &proof_stage)?;
                        #[cfg(test)]
                        sql_log.push(conflict);
                        #[cfg(not(test))]
                        drop(conflict);
                        statement_count += 1;
                        let insert = stage_insert_sql(*congr, 5, 4, &proof_stage, generation);
                        let inserted = transaction.execute(&insert, [])?;
                        inserted_rows[schedule_index] = inserted;
                        physical_changed |= inserted != 0;
                        report_changed |= inserted != 0;
                        #[cfg(test)]
                        sql_log.push(insert);
                        statement_count += 1;
                    }
                    StandardRebuildKind::EclassOutput { sym, trans } => {
                        let sym_stage = format!("egglog_rebuild_head_sym_{run}_{schedule_index}");
                        let trans_stage =
                            format!("egglog_rebuild_head_trans_{run}_{schedule_index}");
                        scratch_names.extend([sym_stage.clone(), trans_stage.clone()]);
                        let create_sym = format!(
                            "CREATE TEMP TABLE {sym_stage} AS
                             SELECT c{edge_payload} AS c0,
                                    CAST('{head_base}' AS UBIGINT)
                                        + 2 * (__match_ordinal - 1) AS c1,
                                    CAST(TRUE AS BOOLEAN) AS c2,
                                    __match_ordinal AS __ordinal
                             FROM {stage}"
                        );
                        transaction.execute(&create_sym, [])?;
                        #[cfg(test)]
                        sql_log.push(create_sym);
                        statement_count += 1;
                        let conflict = check_assert_eq_conflict(&transaction, *sym, 2, &sym_stage)?;
                        #[cfg(test)]
                        sql_log.push(conflict);
                        #[cfg(not(test))]
                        drop(conflict);
                        statement_count += 1;
                        let insert_sym = stage_insert_sql(*sym, 3, 2, &sym_stage, generation);
                        let sym_inserted = transaction.execute(&insert_sym, [])?;
                        #[cfg(test)]
                        sql_log.push(insert_sym);
                        statement_count += 1;

                        let create_trans = format!(
                            "CREATE TEMP TABLE {trans_stage} AS
                             SELECT CAST('{head_base}' AS UBIGINT)
                                        + 2 * (__match_ordinal - 1) AS c0,
                                    c{view_payload} AS c1,
                                    CAST('{head_base}' AS UBIGINT)
                                        + 2 * (__match_ordinal - 1) + 1 AS c2,
                                    CAST(TRUE AS BOOLEAN) AS c3,
                                    __match_ordinal AS __ordinal
                             FROM {stage}"
                        );
                        transaction.execute(&create_trans, [])?;
                        #[cfg(test)]
                        sql_log.push(create_trans);
                        statement_count += 1;
                        let conflict =
                            check_assert_eq_conflict(&transaction, *trans, 3, &trans_stage)?;
                        #[cfg(test)]
                        sql_log.push(conflict);
                        #[cfg(not(test))]
                        drop(conflict);
                        statement_count += 1;
                        let insert_trans = stage_insert_sql(*trans, 4, 3, &trans_stage, generation);
                        let trans_inserted = transaction.execute(&insert_trans, [])?;
                        #[cfg(test)]
                        sql_log.push(insert_trans);
                        statement_count += 1;

                        let head_inserted = sym_inserted
                            .checked_add(trans_inserted)
                            .context("standard rebuild head insert telemetry overflow")?;
                        inserted_rows[schedule_index] = head_inserted;
                        physical_changed |= head_inserted != 0;
                        report_changed |= head_inserted != 0;
                    }
                }
                let slots = plan.kind.head_fresh_slots();
                head_offset = head_offset
                    .checked_add(
                        count
                            .checked_mul(slots)
                            .context("standard rebuild head offset overflow")?,
                    )
                    .context("standard rebuild head offset overflow")?;
            }

            // Enqueue all canonical View candidates only after every Delete
            // and independent proof Set has completed.
            let mut event_offset = 0_u64;
            for (schedule_index, ((rule, _), stage)) in scheduled.iter().zip(&stages).enumerate() {
                let Some(plan) = rule.standard_rebuild() else {
                    debug_assert!(rule.marker_rekey().is_some());
                    continue;
                };
                let count = u64::try_from(matched_rows[schedule_index])?;
                let head_slots = plan.kind.head_fresh_slots();
                let head_base = head_bases[schedule_index];
                let canonical_column = plan.view.arity();
                let mut candidate = Vec::with_capacity(plan.view.arity());
                match plan.kind {
                    StandardRebuildKind::EqKey { key_index, .. } => {
                        for column in 0..plan.view.n_keys {
                            candidate.push(if column == key_index {
                                format!("c{canonical_column}")
                            } else {
                                format!("c{column}")
                            });
                        }
                        candidate.push(format!("c{}", plan.view.n_keys));
                        candidate.push(format!(
                            "CAST('{head_base}' AS UBIGINT) + __match_ordinal - 1"
                        ));
                    }
                    StandardRebuildKind::EclassOutput { .. } => {
                        candidate.extend((0..plan.view.n_keys).map(|column| format!("c{column}")));
                        candidate.push(format!("c{canonical_column}"));
                        candidate.push(format!(
                            "CAST('{head_base}' AS UBIGINT) + {head_slots} * (__match_ordinal - 1) + 1"
                        ));
                    }
                }
                let group = &groups[group_indices[&plan.view.target.rep()]];
                let enqueue = format!(
                    "INSERT INTO {} (__wave, __event_ordinal, {})
                     SELECT CAST('0' AS UBIGINT),
                            CAST('{event_offset}' AS UBIGINT) + __match_ordinal,
                            {}
                     FROM {stage}
                     ORDER BY __match_ordinal",
                    group.queue,
                    visible_columns(plan.view.arity()),
                    candidate.join(", ")
                );
                let enqueued = transaction.execute(&enqueue, [])?;
                ensure_count(enqueued, count, "standard rebuild View candidate enqueue")?;
                #[cfg(test)]
                sql_log.push(enqueue);
                statement_count += 1;
                event_offset = event_offset
                    .checked_add(count)
                    .context("standard rebuild event ordinal overflow")?;
            }

            let mut wave = 0_u64;
            let mut next_event = event_offset;
            let mut pass = 0_u64;
            loop {
                for group_index in 0..groups.len() {
                    let group = groups[group_index].clone();
                    loop {
                        let count_sql = format!(
                            "SELECT count(*) FROM {} WHERE __wave = CAST('{wave}' AS UBIGINT)",
                            group.queue
                        );
                        let pending =
                            transaction.query_row(&count_sql, [], |row| row.get::<_, u64>(0))?;
                        #[cfg(test)]
                        sql_log.push(count_sql);
                        statement_count += 1;
                        if pending == 0 {
                            break;
                        }

                        let outcome = format!("egglog_rebuild_outcome_{run}_{pass}");
                        let collision = format!("egglog_rebuild_collision_{run}_{pass}");
                        let sym_stage = format!("egglog_rebuild_sym_{run}_{pass}");
                        let trans_stage = format!("egglog_rebuild_trans_{run}_{pass}");
                        scratch_names.extend([
                            outcome.clone(),
                            collision.clone(),
                            sym_stage.clone(),
                            trans_stage.clone(),
                        ]);
                        let target = sql_table(group.plan.target);
                        let key_partition = if group.plan.n_keys == 0 {
                            String::new()
                        } else {
                            format!(
                                "PARTITION BY {} ",
                                (0..group.plan.n_keys)
                                    .map(|column| format!("c{column}"))
                                    .collect::<Vec<_>>()
                                    .join(", ")
                            )
                        };
                        let selected_columns = (0..group.plan.arity())
                            .map(|column| format!("selected.c{column} AS new_c{column}"))
                            .collect::<Vec<_>>()
                            .join(", ");
                        let old_columns = (0..group.plan.arity())
                            .map(|column| format!("existing.c{column} AS old_c{column}"))
                            .collect::<Vec<_>>()
                            .join(", ");
                        let join = key_equality("existing", "selected", group.plan.n_keys);
                        let create_outcome = format!(
                            "CREATE TEMP TABLE {outcome} AS
                             WITH selected AS (
                                 SELECT __wave, __event_ordinal, {}
                                 FROM (
                                     SELECT queued.*,
                                            row_number() OVER (
                                                {key_partition}ORDER BY __event_ordinal
                                            ) AS __key_rank
                                     FROM {} AS queued
                                     WHERE __wave = CAST('{wave}' AS UBIGINT)
                                 )
                                 WHERE __key_rank = 1
                             )
                             SELECT selected.__wave,
                                    selected.__event_ordinal,
                                    {selected_columns},
                                    {old_columns},
                                    existing.__generation AS old_generation,
                                    existing.__subsumed AS old_subsumed
                             FROM selected
                             LEFT JOIN {target} AS existing ON {join}",
                            visible_columns(group.plan.arity()),
                            group.queue
                        );
                        transaction.execute(&create_outcome, [])?;
                        #[cfg(test)]
                        sql_log.push(create_outcome);
                        statement_count += 1;

                        let remove = format!(
                            "DELETE FROM {} AS queued
                             USING {outcome} AS selected
                             WHERE queued.__wave = selected.__wave
                               AND queued.__event_ordinal = selected.__event_ordinal",
                            group.queue
                        );
                        transaction.execute(&remove, [])?;
                        #[cfg(test)]
                        sql_log.push(remove);
                        statement_count += 1;

                        let new_columns = (0..group.plan.arity())
                            .map(|column| format!("new_c{column}"))
                            .collect::<Vec<_>>()
                            .join(", ");
                        let insert_missing = format!(
                            "INSERT INTO {target} ({}, __generation, __subsumed)
                             SELECT {new_columns}, CAST('{generation}' AS UBIGINT), FALSE
                             FROM {outcome}
                             WHERE old_generation IS NULL
                             ORDER BY __event_ordinal",
                            visible_columns(group.plan.arity())
                        );
                        let missing_inserted = transaction.execute(&insert_missing, [])?;
                        physical_changed |= missing_inserted != 0;
                        report_changed |= missing_inserted != 0;
                        #[cfg(test)]
                        sql_log.push(insert_missing);
                        statement_count += 1;

                        let identity = group.plan.n_keys;
                        let payload = identity + 1;
                        let create_collision = format!(
                            "CREATE TEMP TABLE {collision} AS
                             SELECT outcome.*,
                                    CASE WHEN old_c{identity} < new_c{identity}
                                         THEN old_c{identity} ELSE new_c{identity} END AS min_identity,
                                    CASE WHEN old_c{identity} > new_c{identity}
                                         THEN old_c{identity} ELSE new_c{identity} END AS max_identity,
                                    CASE WHEN old_c{identity} < new_c{identity}
                                         THEN old_c{payload} ELSE new_c{payload} END AS lo_payload,
                                    CASE WHEN old_c{identity} > new_c{identity}
                                         THEN old_c{payload} ELSE new_c{payload} END AS hi_payload,
                                    row_number() OVER (ORDER BY __event_ordinal)
                                        AS __collision_ordinal
                             FROM {outcome} AS outcome
                             WHERE old_generation IS NOT NULL
                               AND old_c{identity} IS DISTINCT FROM new_c{identity}"
                        );
                        transaction.execute(&create_collision, [])?;
                        #[cfg(test)]
                        sql_log.push(create_collision);
                        statement_count += 1;
                        let collision_count_sql = format!("SELECT count(*) FROM {collision}");
                        let collision_count =
                            transaction
                                .query_row(&collision_count_sql, [], |row| row.get::<_, u64>(0))?;
                        #[cfg(test)]
                        sql_log.push(collision_count_sql);
                        statement_count += 1;

                        if collision_count != 0 {
                            let first_collision_id = next_fresh;
                            let collision_ids = collision_count
                                .checked_mul(2)
                                .context("standard rebuild collision fresh-id count overflow")?;
                            next_fresh = checked_fresh_end(
                                first_collision_id,
                                collision_ids,
                                "standard rebuild merge collisions",
                            )?;
                            let reserve = format!(
                                "UPDATE {COUNTERS_TABLE} SET value = CAST('{next_fresh}' AS UBIGINT) WHERE name = 'fresh_id'"
                            );
                            transaction.execute(&reserve, [])?;
                            #[cfg(test)]
                            sql_log.push(reserve);
                            statement_count += 1;

                            let sym_input = match group.plan.orientation {
                                OrderedUnionOrientation::KeyToParent => "hi_payload",
                                OrderedUnionOrientation::EclassToTerm => "lo_payload",
                            };
                            let create_sym = format!(
                                "CREATE TEMP TABLE {sym_stage} AS
                                 SELECT {sym_input} AS c0,
                                        CAST('{first_collision_id}' AS UBIGINT)
                                            + 2 * (__collision_ordinal - 1) AS c1,
                                        CAST(TRUE AS BOOLEAN) AS c2,
                                        __collision_ordinal AS __ordinal
                                 FROM {collision}"
                            );
                            transaction.execute(&create_sym, [])?;
                            #[cfg(test)]
                            sql_log.push(create_sym);
                            statement_count += 1;
                            let conflict = check_assert_eq_conflict(
                                &transaction,
                                group.plan.sym,
                                2,
                                &sym_stage,
                            )?;
                            #[cfg(test)]
                            sql_log.push(conflict);
                            #[cfg(not(test))]
                            drop(conflict);
                            statement_count += 1;
                            let insert_sym =
                                stage_insert_sql(group.plan.sym, 3, 2, &sym_stage, generation);
                            let sym_inserted = transaction.execute(&insert_sym, [])?;
                            physical_changed |= sym_inserted != 0;
                            report_changed |= sym_inserted != 0;
                            #[cfg(test)]
                            sql_log.push(insert_sym);
                            statement_count += 1;

                            let (trans_first, trans_second) = match group.plan.orientation {
                                OrderedUnionOrientation::KeyToParent => (
                                    format!(
                                        "CAST('{first_collision_id}' AS UBIGINT) + 2 * (__collision_ordinal - 1)"
                                    ),
                                    "lo_payload".to_string(),
                                ),
                                OrderedUnionOrientation::EclassToTerm => (
                                    "hi_payload".to_string(),
                                    format!(
                                        "CAST('{first_collision_id}' AS UBIGINT) + 2 * (__collision_ordinal - 1)"
                                    ),
                                ),
                            };
                            let create_trans = format!(
                                "CREATE TEMP TABLE {trans_stage} AS
                                 SELECT {trans_first} AS c0,
                                        {trans_second} AS c1,
                                        CAST('{first_collision_id}' AS UBIGINT)
                                            + 2 * (__collision_ordinal - 1) + 1 AS c2,
                                        CAST(TRUE AS BOOLEAN) AS c3,
                                        __collision_ordinal AS __ordinal
                                 FROM {collision}"
                            );
                            transaction.execute(&create_trans, [])?;
                            #[cfg(test)]
                            sql_log.push(create_trans);
                            statement_count += 1;
                            let conflict = check_assert_eq_conflict(
                                &transaction,
                                group.plan.trans,
                                3,
                                &trans_stage,
                            )?;
                            #[cfg(test)]
                            sql_log.push(conflict);
                            #[cfg(not(test))]
                            drop(conflict);
                            statement_count += 1;
                            let insert_trans =
                                stage_insert_sql(group.plan.trans, 4, 3, &trans_stage, generation);
                            let trans_inserted = transaction.execute(&insert_trans, [])?;
                            physical_changed |= trans_inserted != 0;
                            report_changed |= trans_inserted != 0;
                            #[cfg(test)]
                            sql_log.push(insert_trans);
                            statement_count += 1;

                            let owner_join = (0..group.plan.n_keys)
                                .map(|column| {
                                    format!(
                                        "existing.c{column} IS NOT DISTINCT FROM collision.new_c{column}"
                                    )
                                })
                                .collect::<Vec<_>>()
                                .join(" AND ");
                            let owner_join = if owner_join.is_empty() {
                                "TRUE".to_string()
                            } else {
                                owner_join
                            };
                            let update_owner = format!(
                                "UPDATE {target} AS existing
                                 SET c{identity} = collision.min_identity,
                                     c{payload} = collision.lo_payload,
                                     __generation = CAST('{generation}' AS UBIGINT)
                                 FROM {collision} AS collision
                                 WHERE {owner_join}
                                   AND (existing.c{identity} IS DISTINCT FROM collision.min_identity
                                        OR existing.c{payload} IS DISTINCT FROM collision.lo_payload)"
                            );
                            let updated = transaction.execute(&update_owner, [])?;
                            physical_changed |= updated != 0;
                            report_changed |= updated != 0;
                            #[cfg(test)]
                            sql_log.push(update_owner);
                            statement_count += 1;

                            let displaced_index = group_indices
                                .get(&group.plan.displaced_target.rep())
                                .copied()
                                .ok_or_else(|| {
                                    anyhow!(
                                        "standard rebuild target {} has no displaced UF queue",
                                        group.plan.displaced_target.rep()
                                    )
                                })?;
                            let displaced_queue = &groups[displaced_index].queue;
                            let next_wave = wave
                                .checked_add(1)
                                .context("standard rebuild logical wave overflow")?;
                            let enqueue_generated = format!(
                                "INSERT INTO {displaced_queue} (__wave, __event_ordinal, c0, c1, c2)
                                 SELECT CAST('{next_wave}' AS UBIGINT),
                                        CAST('{next_event}' AS UBIGINT) + __collision_ordinal,
                                        max_identity,
                                        min_identity,
                                        CAST('{first_collision_id}' AS UBIGINT)
                                            + 2 * (__collision_ordinal - 1) + 1
                                 FROM {collision}
                                 ORDER BY __collision_ordinal"
                            );
                            let generated = transaction.execute(&enqueue_generated, [])?;
                            ensure_count(
                                generated,
                                collision_count,
                                "standard rebuild generated UF candidate enqueue",
                            )?;
                            #[cfg(test)]
                            sql_log.push(enqueue_generated);
                            statement_count += 1;
                            next_event = next_event
                                .checked_add(collision_count)
                                .context("standard rebuild generated event ordinal overflow")?;
                        }

                        for scratch in [&trans_stage, &sym_stage, &collision, &outcome] {
                            let drop = format!("DROP TABLE IF EXISTS {scratch}");
                            transaction.execute(&drop, [])?;
                            #[cfg(test)]
                            sql_log.push(drop);
                            statement_count += 1;
                        }
                        pass = pass
                            .checked_add(1)
                            .context("standard rebuild fold-pass identifier overflow")?;
                    }
                }

                let mut remaining = 0_u64;
                for group in &groups {
                    let count_sql = format!("SELECT count(*) FROM {}", group.queue);
                    let count =
                        transaction.query_row(&count_sql, [], |row| row.get::<_, u64>(0))?;
                    #[cfg(test)]
                    sql_log.push(count_sql);
                    statement_count += 1;
                    remaining = remaining
                        .checked_add(count)
                        .context("standard rebuild queue row count overflow")?;
                }
                if remaining == 0 {
                    break;
                }
                wave = wave
                    .checked_add(1)
                    .context("standard rebuild logical wave overflow")?;
            }

            if physical_changed {
                let update = format!(
                    "UPDATE {COUNTERS_TABLE} SET value = value + 1 WHERE name = 'generation'"
                );
                transaction.execute(&update, [])?;
                #[cfg(test)]
                sql_log.push(update);
                statement_count += 1;
            }

            for scratch in scratch_names.iter().rev() {
                let drop = format!("DROP TABLE IF EXISTS {scratch}");
                transaction.execute(&drop, [])?;
                #[cfg(test)]
                sql_log.push(drop);
                statement_count += 1;
            }
            Ok((generation, report_changed))
        })();

        let (watermark, changed) = match execute {
            Ok(result) => result,
            Err(error) => {
                let rollback_error = transaction.rollback().err();
                let cleanup_error = cleanup_scratch(&state.connection, &scratch_names).err();
                if rollback_error.is_some() || cleanup_error.is_some() {
                    return Err(anyhow!(
                        "DuckDB rebuilding transaction failed: {error:#}; rollback: {rollback_error:?}; scratch cleanup: {cleanup_error:?}"
                    ));
                }
                return Err(error);
            }
        };
        transaction.commit()?;
        state.next_rule_run = next_rule_run;
        #[cfg(test)]
        {
            state.latest_rule_sql = sql_log;
        }
        Ok(RuleExecutionStats {
            changed,
            watermark,
            matched_rows,
            inserted_rows,
            statement_count,
        })
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
            read_columns(info),
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
            info.columns[..info.n_keys]
                .iter()
                .zip(key)
                .enumerate()
                .map(|(column, (&ty, &value))| {
                    Ok(format!(
                        "c{column} IS NOT DISTINCT FROM {}",
                        ty.sql_literal(base_values, value)?
                    ))
                })
                .collect::<Result<Vec<_>>>()?
                .join(" AND ")
        };
        let sql = format!(
            "SELECT {}, __generation, __subsumed FROM {} WHERE {predicate} LIMIT 1",
            read_columns(info),
            sql_table(id)
        );
        let mut statement = state.connection.prepare(&sql)?;
        let mut rows = statement.query([])?;
        rows.next()?
            .map(|row| decode_row(base_values, info, row))
            .transpose()
    }

    #[cfg(test)]
    pub(crate) fn generation(&self) -> Result<u64> {
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
    pub(crate) fn next_fresh_id(&self) -> Result<u64> {
        let state = self.state.lock().expect("DuckDB storage mutex poisoned");
        state
            .connection
            .query_row(
                &format!("SELECT value FROM {COUNTERS_TABLE} WHERE name = 'fresh_id'"),
                [],
                |row| row.get(0),
            )
            .map_err(Into::into)
    }

    #[cfg(test)]
    pub(crate) fn set_next_fresh_id(&self, value: u64) -> Result<()> {
        let state = self.state.lock().expect("DuckDB storage mutex poisoned");
        state.connection.execute(
            &format!(
                "UPDATE {COUNTERS_TABLE} SET value = CAST('{value}' AS UBIGINT) WHERE name = 'fresh_id'"
            ),
            [],
        )?;
        Ok(())
    }

    #[cfg(test)]
    pub(crate) fn with_connection<R>(&self, f: impl FnOnce(&Connection) -> Result<R>) -> Result<R> {
        let state = self.state.lock().expect("DuckDB storage mutex poisoned");
        f(&state.connection)
    }

    #[cfg(test)]
    pub(crate) fn latest_input_sql(&self) -> Vec<String> {
        self.state
            .lock()
            .expect("DuckDB storage mutex poisoned")
            .latest_input_sql
            .clone()
    }

    #[cfg(test)]
    pub(crate) fn latest_rule_sql(&self) -> Vec<String> {
        self.state
            .lock()
            .expect("DuckDB storage mutex poisoned")
            .latest_rule_sql
            .clone()
    }
}

fn checked_fresh_end(first: u64, count: u64, context: &str) -> Result<u64> {
    first
        .checked_add(count)
        .filter(|&end| end <= u32::MAX as u64)
        .with_context(|| format!("{context} exceed the usable Value domain"))
}

fn ensure_count(actual: usize, expected: u64, context: &str) -> Result<()> {
    if u64::try_from(actual)? != expected {
        bail!("{context} changed {actual} rows, expected {expected}");
    }
    Ok(())
}

fn check_assert_eq_conflict(
    transaction: &duckdb::Transaction<'_>,
    target: FunctionId,
    n_keys: usize,
    stage: &str,
) -> Result<String> {
    let sql = assert_eq_conflict_sql(target, n_keys, stage);
    let conflict = transaction.query_row(&sql, [], |row| row.get::<_, bool>(0))?;
    if conflict {
        bail!(
            "illegal MergeFn::AssertEq conflict in staged path effect for function {}",
            target.rep()
        );
    }
    Ok(sql)
}

fn stage_insert_sql(
    target: FunctionId,
    arity: usize,
    n_keys: usize,
    stage: &str,
    generation: u64,
) -> String {
    debug_assert!(
        stage
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
    );
    let partition = if n_keys == 0 {
        "ORDER BY staged.__ordinal".to_string()
    } else {
        format!(
            "PARTITION BY {} ORDER BY staged.__ordinal",
            qualified_columns("staged", n_keys)
        )
    };
    let no_existing = if n_keys == 0 {
        format!("NOT EXISTS (SELECT 1 FROM {})", sql_table(target))
    } else {
        let equality = key_equality("existing", "ranked", n_keys);
        format!(
            "NOT EXISTS (SELECT 1 FROM {} AS existing WHERE {equality})",
            sql_table(target)
        )
    };
    format!(
        "INSERT INTO {} ({}, __generation, __subsumed)
         SELECT {}, CAST('{generation}' AS UBIGINT), FALSE
         FROM (
             SELECT staged.*,
                    row_number() OVER ({partition}) AS __key_rank
             FROM {stage} AS staged
         ) AS ranked
         WHERE ranked.__key_rank = 1 AND {no_existing}",
        sql_table(target),
        visible_columns(arity),
        qualified_columns("ranked", arity),
    )
}

fn cleanup_scratch(connection: &Connection, scratch_names: &[String]) -> Result<()> {
    for scratch in scratch_names.iter().rev() {
        debug_assert!(
            scratch
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
        );
        connection.execute(&format!("DROP TABLE IF EXISTS {scratch}"), [])?;
    }
    Ok(())
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
    let existing_row = if info.n_keys == 0 {
        format!("NOT EXISTS (SELECT 1 FROM {})", sql_table(function))
    } else {
        let equality = key_equality("existing", "ranked", info.n_keys);
        format!(
            "NOT EXISTS (
                 SELECT 1 FROM {} AS existing WHERE {equality}
             )",
            sql_table(function)
        )
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

fn input_assert_eq_conflict_sql(
    function: FunctionId,
    info: &TableInfo,
    rows: &[Vec<String>],
) -> String {
    debug_assert_eq!(info.write_capability, WriteCapability::AssertEq);
    debug_assert_eq!(info.n_vals, 1);
    let values = rows
        .iter()
        .map(|row| format!("({})", row.join(", ")))
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "WITH incoming({}) AS (VALUES {values}) {}",
        visible_columns(info.arity()),
        assert_eq_conflict_sql(function, info.n_keys, "incoming")
    )
}

pub(crate) fn assert_eq_conflict_sql(
    function: FunctionId,
    n_keys: usize,
    incoming: &str,
) -> String {
    debug_assert!(
        incoming
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
    );
    let output = n_keys;
    let intra_batch = if n_keys == 0 {
        format!("SELECT 1 FROM {incoming} HAVING count(DISTINCT c{output}) > 1")
    } else {
        format!(
            "SELECT 1 FROM {incoming} GROUP BY {} HAVING count(DISTINCT c{output}) > 1",
            visible_columns(n_keys)
        )
    };
    let key_join = if n_keys == 0 {
        "TRUE".to_string()
    } else {
        key_equality("existing", "candidate", n_keys)
    };
    format!(
        "SELECT EXISTS ({intra_batch}) OR EXISTS (
             SELECT 1
             FROM {incoming} AS candidate
             JOIN {} AS existing ON {key_join}
             WHERE candidate.c{output} IS DISTINCT FROM existing.c{output}
         )",
        sql_table(function)
    )
}

fn key_equality(left: &str, right: &str, n_keys: usize) -> String {
    if n_keys == 0 {
        return "TRUE".to_string();
    }
    (0..n_keys)
        .map(|column| format!("{left}.c{column} IS NOT DISTINCT FROM {right}.c{column}"))
        .collect::<Vec<_>>()
        .join(" AND ")
}

fn duplicate_owner_sql(table: &str, n_keys: usize) -> String {
    debug_assert!(
        table
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
    );
    if n_keys == 0 {
        return format!("SELECT count(*) > 1 FROM {table}");
    }
    format!(
        "SELECT EXISTS (
             SELECT 1 FROM {table}
             GROUP BY {}
             HAVING count(*) > 1
         )",
        visible_columns(n_keys)
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

pub(crate) fn sql_table(id: FunctionId) -> String {
    format!("egglog_function_{}", id.rep())
}

pub(crate) fn visible_columns(arity: usize) -> String {
    (0..arity)
        .map(|column| format!("c{column}"))
        .collect::<Vec<_>>()
        .join(", ")
}

fn read_columns(info: &TableInfo) -> String {
    info.columns
        .iter()
        .enumerate()
        .map(|(column, ty)| ty.read_expression(&format!("c{column}")))
        .collect::<Vec<_>>()
        .join(", ")
}

pub(crate) fn qualified_columns(alias: &str, arity: usize) -> String {
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
    use num::{BigInt, BigRational, rational::Rational64};

    fn scalar_base_values() -> BaseValues {
        let mut values = BaseValues::default();
        values.register_type::<()>();
        values.register_type::<Boxed<String>>();
        values.register_type::<bool>();
        values.register_type::<i64>();
        values.register_type::<Boxed<OrderedFloat<f64>>>();
        values
    }

    fn register_keep_old(
        storage: &Storage,
        values: &BaseValues,
        name: &str,
        schema: Vec<ColumnTy>,
        n_vals: usize,
        can_subsume: bool,
    ) -> Result<FunctionId> {
        storage.register_table(
            values,
            FunctionConfig {
                schema,
                n_vals,
                n_identity_vals: None,
                default: DefaultVal::Fail,
                merge: MergeFn::Old,
                name: name.to_string(),
                can_subsume,
            },
        )
    }

    fn register_assert_eq(
        storage: &Storage,
        values: &BaseValues,
        name: &str,
        schema: Vec<ColumnTy>,
        can_subsume: bool,
    ) -> Result<FunctionId> {
        storage.register_table(
            values,
            FunctionConfig {
                schema,
                n_vals: 1,
                n_identity_vals: Some(1),
                default: DefaultVal::Fail,
                merge: MergeFn::AssertEq,
                name: name.to_string(),
                can_subsume,
            },
        )
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
    fn exact_numeric_values_round_trip_through_typed_columns() -> Result<()> {
        let mut values = scalar_base_values();
        let bigint_ty = values.register_type::<Boxed<BigInt>>();
        let bigrat_ty = values.register_type::<Boxed<BigRational>>();
        let rational_ty = values.register_type::<Boxed<Rational64>>();
        let storage = Storage::new()?;
        let table = register_keep_old(
            &storage,
            &values,
            "exact-numbers",
            vec![
                ColumnTy::Id,
                ColumnTy::Base(bigint_ty),
                ColumnTy::Base(bigrat_ty),
                ColumnTy::Base(rational_ty),
            ],
            1,
            false,
        )?;
        let huge = "1234567890".repeat(40).parse::<BigInt>()?;
        let ratio_denom = "98765432109876543210987654321".parse::<BigInt>()?;
        let raw_ratio = BigRational::new_raw(huge.clone(), -ratio_denom.clone());
        let canonical_ratio = BigRational::new(-huge.clone(), ratio_denom);
        let fixed = Rational64::new_raw(-6, -8);
        let row = vec![
            Value::new(1),
            values.get(Boxed::new(huge.clone())),
            values.get(Boxed::new(raw_ratio.clone())),
            values.get(Boxed::new(fixed)),
        ];

        storage.insert_batch(&values, vec![(table, row)])?;
        let stored = &storage.scan(&values, table)?[0].values;
        assert_eq!(values.unwrap::<Boxed<BigInt>>(stored[1]).into_inner(), huge);
        assert_eq!(
            values.unwrap::<Boxed<BigRational>>(stored[2]).into_inner(),
            canonical_ratio
        );
        assert_eq!(
            values.unwrap::<Boxed<Rational64>>(stored[3]).into_inner(),
            Rational64::new(3, 4)
        );
        assert!(
            storage
                .lookup(
                    &values,
                    table,
                    &[
                        Value::new(1),
                        values.get(Boxed::new(huge)),
                        values.get(Boxed::new(raw_ratio)),
                    ],
                )?
                .is_some()
        );
        assert!(
            storage
                .latest_input_sql()
                .iter()
                .all(|statement| !statement.contains('?'))
        );
        storage.with_connection(|connection| {
            let types = connection
                .prepare(&format!("DESCRIBE {}", sql_table(table)))?
                .query_map([], |row| row.get::<_, String>(1))?
                .collect::<duckdb::Result<Vec<_>>>()?;
            assert_eq!(types[1], "BIGNUM");
            assert_eq!(types[2], "STRUCT(numer BIGNUM, denom BIGNUM)");
            assert_eq!(types[3], "STRUCT(numer BIGINT, denom BIGINT)");
            Ok(())
        })?;
        Ok(())
    }

    #[test]
    fn hostile_noncanonical_exact_values_fail_before_transaction_without_panicking() -> Result<()> {
        let mut values = scalar_base_values();
        let bigrat_ty = values.register_type::<Boxed<BigRational>>();
        let rational_ty = values.register_type::<Boxed<Rational64>>();
        let storage = Storage::new()?;
        let first = register_keep_old(
            &storage,
            &values,
            "first-before-hostile",
            vec![ColumnTy::Id, ColumnTy::Id],
            1,
            false,
        )?;
        let bigrat = register_keep_old(
            &storage,
            &values,
            "hostile-bigrat",
            vec![ColumnTy::Id, ColumnTy::Base(bigrat_ty)],
            1,
            false,
        )?;
        let rational = register_keep_old(
            &storage,
            &values,
            "hostile-rational",
            vec![ColumnTy::Id, ColumnTy::Base(rational_ty)],
            1,
            false,
        )?;
        assert!(
            canonical_rational64(Rational64::new_raw(i64::MIN, -1))
                .unwrap_err()
                .to_string()
                .contains("outside i64")
        );
        let generation_before = storage.generation()?;
        let hostile_bigrat = values.get(Boxed::new(BigRational::new_raw(1.into(), 0.into())));
        let error = storage
            .insert_batch(
                &values,
                vec![
                    (first, vec![Value::new(1), Value::new(2)]),
                    (bigrat, vec![Value::new(3), hostile_bigrat]),
                ],
            )
            .unwrap_err();
        assert!(error.to_string().contains("denominator must not be zero"));
        assert_eq!(storage.table_size(first)?, 0);
        assert_eq!(storage.table_size(bigrat)?, 0);
        assert_eq!(storage.generation()?, generation_before);

        let hostile_rational = values.get(Boxed::new(Rational64::new_raw(1, 0)));
        let error = storage
            .insert_batch(
                &values,
                vec![
                    (first, vec![Value::new(1), Value::new(2)]),
                    (rational, vec![Value::new(3), hostile_rational]),
                ],
            )
            .unwrap_err();
        assert!(error.to_string().contains("denominator must not be zero"));
        assert_eq!(storage.table_size(first)?, 0);
        assert_eq!(storage.table_size(rational)?, 0);
        assert_eq!(storage.generation()?, generation_before);
        Ok(())
    }

    #[test]
    fn assert_eq_compares_typed_bigrat_structs_setwise() -> Result<()> {
        let mut values = scalar_base_values();
        let bigrat_ty = values.register_type::<Boxed<BigRational>>();
        let storage = Storage::new()?;
        let table = register_assert_eq(
            &storage,
            &values,
            "bigrat-assert",
            vec![ColumnTy::Id, ColumnTy::Base(bigrat_ty)],
            false,
        )?;
        let one_third = values.get(Boxed::new(BigRational::new(1.into(), 3.into())));
        let two_fifths = values.get(Boxed::new(BigRational::new(2.into(), 5.into())));
        storage.insert_batch(
            &values,
            vec![
                (table, vec![Value::new(1), one_third]),
                (table, vec![Value::new(1), one_third]),
            ],
        )?;
        assert_eq!(storage.table_size(table)?, 1);
        let generation = storage.generation()?;
        assert!(
            storage
                .insert_batch(
                    &values,
                    vec![
                        (table, vec![Value::new(2), one_third]),
                        (table, vec![Value::new(2), two_fifths]),
                    ],
                )
                .unwrap_err()
                .to_string()
                .contains("AssertEq")
        );
        assert!(
            storage
                .insert_batch(&values, vec![(table, vec![Value::new(1), two_fifths])],)
                .unwrap_err()
                .to_string()
                .contains("AssertEq")
        );
        assert_eq!(storage.table_size(table)?, 1);
        assert_eq!(storage.generation()?, generation);
        Ok(())
    }

    #[test]
    fn typed_values_round_trip_without_opaque_base_handles_or_indexes() -> Result<()> {
        let values = scalar_base_values();
        let storage = Storage::new()?;
        let id = register_keep_old(
            &storage,
            &values,
            "typed",
            vec![
                ColumnTy::Id,
                ColumnTy::Base(values.get_ty::<bool>()),
                ColumnTy::Base(values.get_ty::<i64>()),
                ColumnTy::Base(values.get_ty::<Boxed<OrderedFloat<f64>>>()),
                ColumnTy::Base(values.get_ty::<Boxed<String>>()),
                ColumnTy::Base(values.get_ty::<()>()),
            ],
            1,
            false,
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
        let string_table = register_keep_old(
            &storage,
            &values,
            "strings",
            vec![
                ColumnTy::Id,
                ColumnTy::Base(values.get_ty::<Boxed<String>>()),
            ],
            1,
            false,
        )?;
        let integer_table = register_keep_old(
            &storage,
            &values,
            "integers",
            vec![ColumnTy::Id, ColumnTy::Base(values.get_ty::<i64>())],
            1,
            false,
        )?;
        let float_table = register_keep_old(
            &storage,
            &values,
            "floats",
            vec![
                ColumnTy::Id,
                ColumnTy::Base(values.get_ty::<Boxed<OrderedFloat<f64>>>()),
            ],
            1,
            false,
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
        let schema = vec![ColumnTy::Id, ColumnTy::Base(values.get_ty::<i64>())];
        let first = register_keep_old(&storage, &values, "first", schema.clone(), 1, false)?;
        let second = register_keep_old(&storage, &values, "second", schema, 1, false)?;
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
        let table = register_keep_old(
            &storage,
            &values,
            "nullary",
            vec![ColumnTy::Base(values.get_ty::<i64>())],
            1,
            false,
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
