//! Backend-neutral parsing for `(input FUNCTION "FILE")` commands.
//!
//! This module deliberately owns every value it returns. In particular, it does
//! not retain `ArcSort`, backend function IDs, backend values, or source spans.
//! A compile-only frontend can therefore retain a [`TypedInputFile`] after the
//! typechecker and e-graph have gone away.
//!
//! The parser preserves the current frontend's TSV rules:
//!
//! - fields are separated only by tabs and each field is trimmed with
//!   [`str::trim`];
//! - a `Unit` column emits [`InputLiteral::Unit`] without consuming a field;
//! - constructor rows contain only the constructor inputs, whereas custom
//!   function rows contain the inputs followed by every output;
//! - row order and duplicate rows are retained;
//! - [`str::lines`] defines physical lines, so a terminal newline does not add a
//!   row and an empty file has no rows.
//!
//! Two edge cases follow from those rules and are intentionally not papered
//! over. An effective zero-column constructor schema ignores every physical
//! line, matching the existing `row.is_empty()` behavior. Conversely, a
//! nonempty all-`Unit` schema cannot encode a row in TSV: even a blank physical
//! line contains one empty field, and no `Unit` column consumes it, so parsing
//! reports [`TypedInputParseError::ExtraField`].

use std::error::Error;
use std::fmt::{self, Display, Formatter};
use std::io;
use std::path::{Path, PathBuf};
use std::str::Utf8Error;

/// The declaration form that controls which columns occur in the input file.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum InputFunctionSubtype {
    /// Constructor outputs are minted by execution and are not TSV columns.
    Constructor,
    /// Custom functions read their declared inputs followed by every output.
    Custom,
}

/// An owned diagnostic sort name retained exactly as declared by the frontend.
///
/// This name is never semantic authority. Supported scalar identity is carried
/// separately by [`InputSortAuthority`].
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct InputSortName(String);

impl InputSortName {
    pub fn new(name: impl Into<String>) -> Self {
        Self(name.into())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }

    pub fn into_string(self) -> String {
        self.0
    }
}

impl From<&str> for InputSortName {
    fn from(name: &str) -> Self {
        Self::new(name)
    }
}

impl From<String> for InputSortName {
    fn from(name: String) -> Self {
        Self::new(name)
    }
}

impl Display for InputSortName {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        self.0.fmt(formatter)
    }
}

/// The four scalar representations understood by the current input loader.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InputScalarKind {
    Unit,
    I64,
    F64,
    String,
}

impl Display for InputScalarKind {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Unit => "Unit",
            Self::I64 => "i64",
            Self::F64 => "f64",
            Self::String => "String",
        })
    }
}

/// Exact frontend authority for one declared sort.
///
/// This is deliberately separate from [`InputSortName`]. A diagnostic name
/// such as `"i64"` does not make a user-defined sort an integer sort, and an
/// actual integer sort remains an integer even if its diagnostic spelling is
/// changed before this backend-neutral snapshot is rendered.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InputSortAuthority {
    Unit,
    I64,
    F64,
    String,
    /// Any exact sort identity not supported by the TSV loader.
    Unsupported,
}

impl Display for InputSortAuthority {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Unit => "Unit",
            Self::I64 => "i64",
            Self::F64 => "f64",
            Self::String => "String",
            Self::Unsupported => "unsupported",
        })
    }
}

/// One declared sort with exact semantics and independent diagnostic spelling.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DeclaredInputSort {
    pub diagnostic_name: InputSortName,
    pub authority: InputSortAuthority,
}

impl DeclaredInputSort {
    pub fn new(diagnostic_name: impl Into<InputSortName>, authority: InputSortAuthority) -> Self {
        Self {
            diagnostic_name: diagnostic_name.into(),
            authority,
        }
    }

    pub fn unsupported(diagnostic_name: impl Into<InputSortName>) -> Self {
        Self::new(diagnostic_name, InputSortAuthority::Unsupported)
    }
}

/// Whether a declared column is a function input or output.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InputColumnRole {
    Input,
    Output,
}

impl Display for InputColumnRole {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Input => "input",
            Self::Output => "output",
        })
    }
}

/// Graph-neutral declaration metadata captured from the typed frontend.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct DeclaredInputSchema {
    pub subtype: InputFunctionSubtype,
    pub inputs: Vec<DeclaredInputSort>,
    pub outputs: Vec<DeclaredInputSort>,
}

impl DeclaredInputSchema {
    pub fn new(
        subtype: InputFunctionSubtype,
        inputs: impl IntoIterator<Item = DeclaredInputSort>,
        outputs: impl IntoIterator<Item = DeclaredInputSort>,
    ) -> Self {
        Self {
            subtype,
            inputs: inputs.into_iter().collect(),
            outputs: outputs.into_iter().collect(),
        }
    }
}

/// Admitted input schema, retaining both declaration and effective row shape.
///
/// For constructors, `effective_outputs` is empty even though
/// `declared_outputs` retains the constructor result sort. For custom
/// functions, every declared output is present in `effective_outputs`.
/// This owned parse DTO is not a certificate of frontend provenance.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TypedInputSchema {
    pub subtype: InputFunctionSubtype,
    pub declared_inputs: Vec<DeclaredInputSort>,
    pub declared_outputs: Vec<DeclaredInputSort>,
    pub effective_inputs: Vec<InputScalarKind>,
    pub effective_outputs: Vec<InputScalarKind>,
}

impl TypedInputSchema {
    pub fn row_arity(&self) -> usize {
        self.effective_inputs.len() + self.effective_outputs.len()
    }

    fn effective_columns(
        &self,
    ) -> impl Iterator<Item = (InputColumnRole, usize, InputScalarKind)> + '_ {
        self.effective_inputs
            .iter()
            .copied()
            .enumerate()
            .map(|(ordinal, kind)| (InputColumnRole::Input, ordinal, kind))
            .chain(
                self.effective_outputs
                    .iter()
                    .copied()
                    .enumerate()
                    .map(|(ordinal, kind)| (InputColumnRole::Output, ordinal, kind)),
            )
    }
}

/// A scalar parsed from a TSV row.
///
/// Floating-point values are retained as their exact IEEE-754 bit pattern. This
/// preserves `-0.0` and parsed NaN payloads without depending on a graph-owned
/// float wrapper.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum InputLiteral {
    Unit,
    I64(i64),
    F64Bits(u64),
    String(String),
}

impl InputLiteral {
    pub fn from_f64(value: f64) -> Self {
        Self::F64Bits(value.to_bits())
    }

    pub fn as_f64(&self) -> Option<f64> {
        match self {
            Self::F64Bits(bits) => Some(f64::from_bits(*bits)),
            _ => None,
        }
    }
}

/// One retained source row.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TypedInputRow {
    /// Zero-based ordinal among retained rows, including duplicates.
    pub source_row_ordinal: u64,
    /// One-based physical line number in the decoded source file.
    pub physical_line: u64,
    pub values: Vec<InputLiteral>,
}

/// Pure parsing result for one input command.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TypedInput {
    pub schema: TypedInputSchema,
    pub rows: Vec<TypedInputRow>,
}

/// The declared path, optional fact-directory base, and exact path that was read.
///
/// Resolution intentionally performs no canonicalization or filesystem access.
/// It uses `PathBuf::push`, matching the existing loader: an absolute declared
/// path replaces the fact-directory base.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct InputPathMetadata {
    pub declared: PathBuf,
    pub fact_directory: Option<PathBuf>,
    pub effective: PathBuf,
}

/// A file-backed input snapshot.
///
/// `bytes` are the exact bytes returned by the single file read, before UTF-8
/// decoding or TSV parsing, so the caller can hash them without reopening the
/// file.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TypedInputFile {
    pub path: InputPathMetadata,
    pub bytes: Vec<u8>,
    pub input: TypedInput,
}

/// A schema or row-format failure from pure TSV parsing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypedInputParseError {
    InvalidOutputArity {
        subtype: InputFunctionSubtype,
        outputs: usize,
    },
    UnsupportedSort {
        role: InputColumnRole,
        column_ordinal: usize,
        sort: InputSortName,
    },
    ResolvedSchemaMismatch {
        role: InputColumnRole,
        column_ordinal: usize,
        expected: Option<InputScalarKind>,
        actual: Option<InputScalarKind>,
    },
    MalformedField {
        physical_line: u64,
        field_ordinal: usize,
        role: InputColumnRole,
        column_ordinal: usize,
        expected: InputScalarKind,
        value: String,
    },
    MissingField {
        physical_line: u64,
        field_ordinal: usize,
        role: InputColumnRole,
        column_ordinal: usize,
        expected: InputScalarKind,
    },
    ExtraField {
        physical_line: u64,
        field_ordinal: usize,
        value: String,
    },
    SourcePositionOverflow,
}

impl Display for TypedInputParseError {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidOutputArity { subtype, outputs } => match subtype {
                InputFunctionSubtype::Constructor => write!(
                    formatter,
                    "constructor input target must declare exactly one output, got {outputs}"
                ),
                InputFunctionSubtype::Custom => write!(
                    formatter,
                    "custom-function input target must declare at least one output, got {outputs}"
                ),
            },
            Self::UnsupportedSort {
                role,
                column_ordinal,
                sort,
            } => write!(
                formatter,
                "unsupported {role} sort {:?} at zero-based column {column_ordinal}",
                sort.as_str()
            ),
            Self::ResolvedSchemaMismatch {
                role,
                column_ordinal,
                expected,
                actual,
            } => write!(
                formatter,
                "resolved {role} schema mismatch at zero-based column {column_ordinal}: expected {expected:?}, got {actual:?}"
            ),
            Self::MalformedField {
                physical_line,
                field_ordinal,
                role,
                column_ordinal,
                expected,
                value,
            } => write!(
                formatter,
                "malformed {expected} field {field_ordinal} ({role} column {column_ordinal}) on line {physical_line}: {value:?}"
            ),
            Self::MissingField {
                physical_line,
                field_ordinal,
                role,
                column_ordinal,
                expected,
            } => write!(
                formatter,
                "missing {expected} field {field_ordinal} ({role} column {column_ordinal}) on line {physical_line}"
            ),
            Self::ExtraField {
                physical_line,
                field_ordinal,
                value,
            } => write!(
                formatter,
                "extra field {field_ordinal} on line {physical_line}: {value:?}"
            ),
            Self::SourcePositionOverflow => {
                formatter.write_str("input source position exceeds the u64 snapshot domain")
            }
        }
    }
}

impl Error for TypedInputParseError {}

/// File access, decoding, or parse failure from [`read_tsv_file`].
#[derive(Debug)]
pub enum TypedInputReadError {
    Read {
        path: PathBuf,
        source: io::Error,
    },
    InvalidUtf8 {
        path: PathBuf,
        source: Utf8Error,
    },
    Parse {
        path: PathBuf,
        source: TypedInputParseError,
    },
}

impl Display for TypedInputReadError {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Read { path, source } => {
                write!(formatter, "failed to read input file {path:?}: {source}")
            }
            Self::InvalidUtf8 { path, source } => {
                write!(formatter, "input file {path:?} is not UTF-8: {source}")
            }
            Self::Parse { path, source } => {
                write!(formatter, "invalid input file {path:?}: {source}")
            }
        }
    }
}

impl Error for TypedInputReadError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Read { source, .. } => Some(source),
            Self::InvalidUtf8 { source, .. } => Some(source),
            Self::Parse { source, .. } => Some(source),
        }
    }
}

/// Resolve an input command's file path without touching the filesystem.
pub fn resolve_input_path(
    fact_directory: Option<&Path>,
    declared_path: impl AsRef<Path>,
) -> InputPathMetadata {
    let declared = declared_path.as_ref().to_path_buf();
    let fact_directory = fact_directory.map(Path::to_path_buf);
    let mut effective = fact_directory.clone().unwrap_or_default();
    effective.push(&declared);
    InputPathMetadata {
        declared,
        fact_directory,
        effective,
    }
}

/// Admit a declared schema and compute its effective TSV row shape.
///
/// This preserves the current loader's role-specific support. Inputs admit
/// `i64`, `f64`, and `String`; custom outputs admit `i64`, `String`, and `Unit`.
/// A constructor's one output sort is retained as declaration metadata but is
/// not sort-validated or represented as a file column because execution mints
/// it.
pub fn resolve_input_schema(
    declared: &DeclaredInputSchema,
) -> Result<TypedInputSchema, TypedInputParseError> {
    let valid_output_arity = match declared.subtype {
        InputFunctionSubtype::Constructor => declared.outputs.len() == 1,
        InputFunctionSubtype::Custom => !declared.outputs.is_empty(),
    };
    if !valid_output_arity {
        return Err(TypedInputParseError::InvalidOutputArity {
            subtype: declared.subtype,
            outputs: declared.outputs.len(),
        });
    }
    let effective_inputs = declared
        .inputs
        .iter()
        .enumerate()
        .map(|(column_ordinal, sort)| resolve_sort(InputColumnRole::Input, column_ordinal, sort))
        .collect::<Result<Vec<_>, _>>()?;
    let effective_outputs = match declared.subtype {
        InputFunctionSubtype::Constructor => Vec::new(),
        InputFunctionSubtype::Custom => declared
            .outputs
            .iter()
            .enumerate()
            .map(|(column_ordinal, sort)| {
                resolve_sort(InputColumnRole::Output, column_ordinal, sort)
            })
            .collect::<Result<Vec<_>, _>>()?,
    };

    Ok(TypedInputSchema {
        subtype: declared.subtype,
        declared_inputs: declared.inputs.clone(),
        declared_outputs: declared.outputs.clone(),
        effective_inputs,
        effective_outputs,
    })
}

fn resolve_sort(
    role: InputColumnRole,
    column_ordinal: usize,
    sort: &DeclaredInputSort,
) -> Result<InputScalarKind, TypedInputParseError> {
    let kind = match (role, sort.authority) {
        (InputColumnRole::Input, InputSortAuthority::I64)
        | (InputColumnRole::Output, InputSortAuthority::I64) => InputScalarKind::I64,
        (InputColumnRole::Input, InputSortAuthority::F64) => InputScalarKind::F64,
        (InputColumnRole::Input, InputSortAuthority::String)
        | (InputColumnRole::Output, InputSortAuthority::String) => InputScalarKind::String,
        (InputColumnRole::Output, InputSortAuthority::Unit) => InputScalarKind::Unit,
        _ => {
            return Err(TypedInputParseError::UnsupportedSort {
                role,
                column_ordinal,
                sort: sort.diagnostic_name.clone(),
            });
        }
    };
    Ok(kind)
}

/// Parse UTF-8 TSV text into owned typed rows without filesystem or backend use.
pub fn parse_tsv(
    contents: &str,
    declared_schema: &DeclaredInputSchema,
) -> Result<TypedInput, TypedInputParseError> {
    let schema = resolve_input_schema(declared_schema)?;
    parse_tsv_with_resolved_schema(contents, &schema)
}

/// Parse UTF-8 TSV text using an already-resolved exact schema.
///
/// The effective scalar kinds are checked against the declaration's exact sort
/// authority before parsing. Diagnostic names are retained in the returned
/// snapshot but never participate in admission or field interpretation.
///
/// This checks schema self-consistency, not frontend provenance. The caller
/// must authenticate the carried authority against its exact function/catalog
/// identity before treating the resulting rows as a program input.
pub fn parse_tsv_with_resolved_schema(
    contents: &str,
    schema: &TypedInputSchema,
) -> Result<TypedInput, TypedInputParseError> {
    validate_resolved_schema(schema)?;
    let mut rows = Vec::with_capacity(contents.lines().count());
    for (zero_based_line, line) in contents.lines().enumerate() {
        let physical_line = u64::try_from(zero_based_line)
            .ok()
            .and_then(|line| line.checked_add(1))
            .ok_or(TypedInputParseError::SourcePositionOverflow)?;
        let mut fields = line.split('\t').map(str::trim).enumerate();
        let mut values = Vec::with_capacity(schema.row_arity());

        for (role, column_ordinal, kind) in schema.effective_columns() {
            if kind == InputScalarKind::Unit {
                values.push(InputLiteral::Unit);
                continue;
            }
            let Some((field_ordinal, raw)) = fields.next() else {
                return Err(TypedInputParseError::MissingField {
                    physical_line,
                    field_ordinal: values
                        .iter()
                        .filter(|value| !matches!(value, InputLiteral::Unit))
                        .count(),
                    role,
                    column_ordinal,
                    expected: kind,
                });
            };
            let value = parse_field(
                physical_line,
                field_ordinal,
                role,
                column_ordinal,
                kind,
                raw,
            )?;
            values.push(value);
        }

        // This is the existing loader's behavior for a nullary constructor: it
        // ignores the physical line before checking for unconsumed fields.
        if values.is_empty() {
            continue;
        }
        if let Some((field_ordinal, raw)) = fields.next() {
            return Err(TypedInputParseError::ExtraField {
                physical_line,
                field_ordinal,
                value: raw.to_owned(),
            });
        }

        let source_row_ordinal =
            u64::try_from(rows.len()).map_err(|_| TypedInputParseError::SourcePositionOverflow)?;
        rows.push(TypedInputRow {
            source_row_ordinal,
            physical_line,
            values,
        });
    }

    Ok(TypedInput {
        schema: schema.clone(),
        rows,
    })
}

fn validate_resolved_schema(schema: &TypedInputSchema) -> Result<(), TypedInputParseError> {
    let expected = resolve_input_schema(&DeclaredInputSchema {
        subtype: schema.subtype,
        inputs: schema.declared_inputs.clone(),
        outputs: schema.declared_outputs.clone(),
    })?;
    validate_effective_kinds(
        InputColumnRole::Input,
        &expected.effective_inputs,
        &schema.effective_inputs,
    )?;
    validate_effective_kinds(
        InputColumnRole::Output,
        &expected.effective_outputs,
        &schema.effective_outputs,
    )
}

fn validate_effective_kinds(
    role: InputColumnRole,
    expected: &[InputScalarKind],
    actual: &[InputScalarKind],
) -> Result<(), TypedInputParseError> {
    let compared_len = expected.len().max(actual.len());
    for column_ordinal in 0..compared_len {
        let expected_kind = expected.get(column_ordinal).copied();
        let actual_kind = actual.get(column_ordinal).copied();
        if expected_kind != actual_kind {
            return Err(TypedInputParseError::ResolvedSchemaMismatch {
                role,
                column_ordinal,
                expected: expected_kind,
                actual: actual_kind,
            });
        }
    }
    Ok(())
}

fn parse_field(
    physical_line: u64,
    field_ordinal: usize,
    role: InputColumnRole,
    column_ordinal: usize,
    expected: InputScalarKind,
    raw: &str,
) -> Result<InputLiteral, TypedInputParseError> {
    let malformed = || TypedInputParseError::MalformedField {
        physical_line,
        field_ordinal,
        role,
        column_ordinal,
        expected,
        value: raw.to_owned(),
    };
    match expected {
        InputScalarKind::Unit => Ok(InputLiteral::Unit),
        InputScalarKind::I64 => raw
            .parse::<i64>()
            .map(InputLiteral::I64)
            .map_err(|_| malformed()),
        InputScalarKind::F64 => raw
            .parse::<f64>()
            .map(InputLiteral::from_f64)
            .map_err(|_| malformed()),
        InputScalarKind::String => Ok(InputLiteral::String(raw.to_owned())),
    }
}

/// Resolve, read once, decode, and parse an input file.
///
/// The exact byte buffer used for decoding is returned in the successful
/// result. This function performs no separate metadata preflight,
/// canonicalization, or second logical file read.
pub fn read_tsv_file(
    fact_directory: Option<&Path>,
    declared_path: impl AsRef<Path>,
    schema: &DeclaredInputSchema,
) -> Result<TypedInputFile, TypedInputReadError> {
    let path = resolve_input_path(fact_directory, declared_path);
    // Match the current frontend's admission order: reject an unsupported
    // schema before opening the file. Valid schemas still perform one read.
    let schema = resolve_input_schema(schema).map_err(|source| TypedInputReadError::Parse {
        path: path.effective.clone(),
        source,
    })?;
    let bytes = std::fs::read(&path.effective).map_err(|source| TypedInputReadError::Read {
        path: path.effective.clone(),
        source,
    })?;
    let contents =
        std::str::from_utf8(&bytes).map_err(|source| TypedInputReadError::InvalidUtf8 {
            path: path.effective.clone(),
            source,
        })?;
    let input = parse_tsv_with_resolved_schema(contents, &schema).map_err(|source| {
        TypedInputReadError::Parse {
            path: path.effective.clone(),
            source,
        }
    })?;
    Ok(TypedInputFile { path, bytes, input })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::sync::atomic::{AtomicU64, Ordering};

    static NEXT_TEMP_DIRECTORY: AtomicU64 = AtomicU64::new(0);

    fn schema(
        subtype: InputFunctionSubtype,
        inputs: &[(&str, InputSortAuthority)],
        outputs: &[(&str, InputSortAuthority)],
    ) -> DeclaredInputSchema {
        DeclaredInputSchema::new(
            subtype,
            inputs
                .iter()
                .map(|(name, authority)| DeclaredInputSort::new(*name, *authority)),
            outputs
                .iter()
                .map(|(name, authority)| DeclaredInputSort::new(*name, *authority)),
        )
    }

    fn one_row(input: TypedInput) -> TypedInputRow {
        assert_eq!(input.rows.len(), 1);
        input.rows.into_iter().next().unwrap()
    }

    fn temp_directory() -> PathBuf {
        let ordinal = NEXT_TEMP_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        std::env::temp_dir().join(format!(
            "egglog_typed_input_{}_{}",
            std::process::id(),
            ordinal
        ))
    }

    #[test]
    fn constructor_shape_reads_only_inputs_and_retains_declared_output() {
        let declared = schema(
            InputFunctionSubtype::Constructor,
            &[
                ("i64", InputSortAuthority::I64),
                ("String", InputSortAuthority::String),
            ],
            &[("AnEqSort", InputSortAuthority::Unsupported)],
        );
        let input = parse_tsv("1\t value \n", &declared).unwrap();

        assert_eq!(
            input.schema.declared_outputs,
            [DeclaredInputSort::unsupported("AnEqSort")]
        );
        assert_eq!(
            input.schema.effective_inputs,
            [InputScalarKind::I64, InputScalarKind::String]
        );
        assert!(input.schema.effective_outputs.is_empty());
        assert_eq!(
            input.rows[0].values,
            [InputLiteral::I64(1), InputLiteral::String("value".into())]
        );
    }

    #[test]
    fn custom_shape_reads_inputs_and_every_output_with_unit_consuming_no_field() {
        let declared = schema(
            InputFunctionSubtype::Custom,
            &[("i64", InputSortAuthority::I64)],
            &[
                ("String", InputSortAuthority::String),
                ("Unit", InputSortAuthority::Unit),
                ("i64", InputSortAuthority::I64),
            ],
        );
        let input = parse_tsv("1\t result \t2\n", &declared).unwrap();

        assert_eq!(input.schema.effective_inputs, [InputScalarKind::I64]);
        assert_eq!(
            input.schema.effective_outputs,
            [
                InputScalarKind::String,
                InputScalarKind::Unit,
                InputScalarKind::I64
            ]
        );
        assert_eq!(
            input.rows[0].values,
            [
                InputLiteral::I64(1),
                InputLiteral::String("result".into()),
                InputLiteral::Unit,
                InputLiteral::I64(2),
            ]
        );
    }

    #[test]
    fn trims_each_field_and_preserves_f64_bits_across_crlf() {
        let declared = schema(
            InputFunctionSubtype::Constructor,
            &[
                ("i64", InputSortAuthority::I64),
                ("f64", InputSortAuthority::F64),
                ("String", InputSortAuthority::String),
            ],
            &[("Ignored", InputSortAuthority::Unsupported)],
        );
        let row = one_row(parse_tsv(" 1 \t -0.0 \t hello world \r\n", &declared).unwrap());

        assert_eq!(row.physical_line, 1);
        assert_eq!(row.source_row_ordinal, 0);
        assert_eq!(
            row.values,
            [
                InputLiteral::I64(1),
                InputLiteral::F64Bits((-0.0_f64).to_bits()),
                InputLiteral::String("hello world".into()),
            ]
        );
        assert_eq!(
            row.values[1].as_f64().unwrap().to_bits(),
            (-0.0_f64).to_bits()
        );
    }

    #[test]
    fn malformed_numeric_field_is_structured() {
        let declared = schema(
            InputFunctionSubtype::Constructor,
            &[("i64", InputSortAuthority::I64)],
            &[("Ignored", InputSortAuthority::Unsupported)],
        );
        let error = parse_tsv("not-an-int\n", &declared).unwrap_err();
        assert_eq!(
            error,
            TypedInputParseError::MalformedField {
                physical_line: 1,
                field_ordinal: 0,
                role: InputColumnRole::Input,
                column_ordinal: 0,
                expected: InputScalarKind::I64,
                value: "not-an-int".into(),
            }
        );
    }

    #[test]
    fn missing_and_extra_fields_are_distinct() {
        let declared = schema(
            InputFunctionSubtype::Constructor,
            &[
                ("i64", InputSortAuthority::I64),
                ("String", InputSortAuthority::String),
            ],
            &[("Ignored", InputSortAuthority::Unsupported)],
        );
        assert_eq!(
            parse_tsv("1\n", &declared).unwrap_err(),
            TypedInputParseError::MissingField {
                physical_line: 1,
                field_ordinal: 1,
                role: InputColumnRole::Input,
                column_ordinal: 1,
                expected: InputScalarKind::String,
            }
        );

        let declared = schema(
            InputFunctionSubtype::Constructor,
            &[("i64", InputSortAuthority::I64)],
            &[("Ignored", InputSortAuthority::Unsupported)],
        );
        assert_eq!(
            parse_tsv("1\textra\n", &declared).unwrap_err(),
            TypedInputParseError::ExtraField {
                physical_line: 1,
                field_ordinal: 1,
                value: "extra".into(),
            }
        );
    }

    #[test]
    fn unsupported_sorts_are_role_specific_structured_errors() {
        let declared = schema(
            InputFunctionSubtype::Constructor,
            &[("Unit", InputSortAuthority::Unit)],
            &[("Ignored", InputSortAuthority::Unsupported)],
        );
        assert_eq!(
            parse_tsv("\n", &declared).unwrap_err(),
            TypedInputParseError::UnsupportedSort {
                role: InputColumnRole::Input,
                column_ordinal: 0,
                sort: InputSortName::new("Unit"),
            }
        );

        let declared = schema(
            InputFunctionSubtype::Custom,
            &[("i64", InputSortAuthority::I64)],
            &[("f64", InputSortAuthority::F64)],
        );
        assert_eq!(
            parse_tsv("1\t2.0\n", &declared).unwrap_err(),
            TypedInputParseError::UnsupportedSort {
                role: InputColumnRole::Output,
                column_ordinal: 0,
                sort: InputSortName::new("f64"),
            }
        );

        let declared = schema(
            InputFunctionSubtype::Custom,
            &[("Map", InputSortAuthority::Unsupported)],
            &[("Unit", InputSortAuthority::Unit)],
        );
        assert!(matches!(
            parse_tsv("anything\n", &declared),
            Err(TypedInputParseError::UnsupportedSort {
                role: InputColumnRole::Input,
                column_ordinal: 0,
                ..
            })
        ));
    }

    #[test]
    fn primitive_looking_diagnostic_name_does_not_grant_scalar_authority() {
        let declared = schema(
            InputFunctionSubtype::Constructor,
            &[("i64", InputSortAuthority::Unsupported)],
            &[("Ignored", InputSortAuthority::Unsupported)],
        );

        assert_eq!(
            parse_tsv("7\n", &declared).unwrap_err(),
            TypedInputParseError::UnsupportedSort {
                role: InputColumnRole::Input,
                column_ordinal: 0,
                sort: InputSortName::new("i64"),
            }
        );
    }

    #[test]
    fn exact_scalar_authority_ignores_arbitrary_diagnostic_spelling() {
        let declared = schema(
            InputFunctionSubtype::Constructor,
            &[
                ("not-an-integer-name", InputSortAuthority::I64),
                ("also-not-a-float-name", InputSortAuthority::F64),
                ("i64", InputSortAuthority::String),
            ],
            &[("i64", InputSortAuthority::Unsupported)],
        );
        let input = parse_tsv("7\t-0.0\ttext\n", &declared).unwrap();

        assert_eq!(
            input.rows[0].values,
            [
                InputLiteral::I64(7),
                InputLiteral::F64Bits((-0.0_f64).to_bits()),
                InputLiteral::String("text".into()),
            ]
        );

        let custom = schema(
            InputFunctionSubtype::Custom,
            &[("Unit", InputSortAuthority::String)],
            &[
                ("f64", InputSortAuthority::I64),
                ("not-unit", InputSortAuthority::Unit),
            ],
        );
        let custom = parse_tsv("key\t8\n", &custom).unwrap();
        assert_eq!(
            custom.rows[0].values,
            [
                InputLiteral::String("key".into()),
                InputLiteral::I64(8),
                InputLiteral::Unit,
            ]
        );
    }

    #[test]
    fn resolved_schema_parser_revalidates_exact_authority_and_effective_kinds() {
        let declared = schema(
            InputFunctionSubtype::Constructor,
            &[("String", InputSortAuthority::I64)],
            &[("output", InputSortAuthority::Unsupported)],
        );
        let schema = resolve_input_schema(&declared).unwrap();
        let parsed = parse_tsv_with_resolved_schema("9\n", &schema).unwrap();
        assert_eq!(parsed.rows[0].values, [InputLiteral::I64(9)]);

        let mut forged = schema;
        forged.effective_inputs[0] = InputScalarKind::String;
        assert_eq!(
            parse_tsv_with_resolved_schema("9\n", &forged).unwrap_err(),
            TypedInputParseError::ResolvedSchemaMismatch {
                role: InputColumnRole::Input,
                column_ordinal: 0,
                expected: Some(InputScalarKind::I64),
                actual: Some(InputScalarKind::String),
            }
        );

        let authority_forged = TypedInputSchema {
            subtype: InputFunctionSubtype::Constructor,
            declared_inputs: vec![DeclaredInputSort::unsupported("i64")],
            declared_outputs: vec![DeclaredInputSort::unsupported("output")],
            effective_inputs: vec![InputScalarKind::I64],
            effective_outputs: Vec::new(),
        };
        assert_eq!(
            parse_tsv_with_resolved_schema("9\n", &authority_forged).unwrap_err(),
            TypedInputParseError::UnsupportedSort {
                role: InputColumnRole::Input,
                column_ordinal: 0,
                sort: InputSortName::new("i64"),
            }
        );
    }

    #[test]
    fn malformed_output_arities_fail_schema_preflight() {
        for declared in [
            schema(
                InputFunctionSubtype::Constructor,
                &[("i64", InputSortAuthority::I64)],
                &[],
            ),
            schema(
                InputFunctionSubtype::Constructor,
                &[("i64", InputSortAuthority::I64)],
                &[
                    ("First", InputSortAuthority::Unsupported),
                    ("Second", InputSortAuthority::Unsupported),
                ],
            ),
            schema(
                InputFunctionSubtype::Custom,
                &[("i64", InputSortAuthority::I64)],
                &[],
            ),
        ] {
            assert!(matches!(
                resolve_input_schema(&declared),
                Err(TypedInputParseError::InvalidOutputArity { .. })
            ));
        }
    }

    #[test]
    fn duplicates_blank_string_rows_and_physical_lines_are_retained() {
        let declared = schema(
            InputFunctionSubtype::Constructor,
            &[("String", InputSortAuthority::String)],
            &[("Ignored", InputSortAuthority::Unsupported)],
        );
        let input = parse_tsv("a\n\n a \n", &declared).unwrap();

        assert_eq!(
            input
                .rows
                .iter()
                .map(|row| (row.source_row_ordinal, row.physical_line, &row.values[0]))
                .collect::<Vec<_>>(),
            [
                (0, 1, &InputLiteral::String("a".into())),
                (1, 2, &InputLiteral::String(String::new())),
                (2, 3, &InputLiteral::String("a".into())),
            ]
        );
    }

    #[test]
    fn empty_and_all_unit_files_have_explicit_legacy_behavior() {
        let all_unit = schema(
            InputFunctionSubtype::Custom,
            &[],
            &[
                ("Unit", InputSortAuthority::Unit),
                ("Unit", InputSortAuthority::Unit),
            ],
        );
        assert!(parse_tsv("", &all_unit).unwrap().rows.is_empty());
        assert_eq!(
            parse_tsv("\n", &all_unit).unwrap_err(),
            TypedInputParseError::ExtraField {
                physical_line: 1,
                field_ordinal: 0,
                value: String::new(),
            }
        );

        let zero_column = schema(
            InputFunctionSubtype::Constructor,
            &[],
            &[("Ignored", InputSortAuthority::Unsupported)],
        );
        assert!(
            parse_tsv("ignored\n\n", &zero_column)
                .unwrap()
                .rows
                .is_empty()
        );
    }

    #[test]
    fn path_resolution_matches_pathbuf_push_for_relative_and_absolute_paths() {
        let base = std::env::temp_dir().join("egglog-facts-base");
        let relative = resolve_input_path(Some(&base), Path::new("nested/rows.tsv"));
        assert_eq!(relative.declared, Path::new("nested/rows.tsv"));
        assert_eq!(relative.fact_directory.as_deref(), Some(base.as_path()));
        assert_eq!(relative.effective, base.join("nested/rows.tsv"));

        let absolute_path = std::env::temp_dir().join("egglog-absolute-rows.tsv");
        assert!(absolute_path.is_absolute());
        let absolute = resolve_input_path(Some(&base), &absolute_path);
        assert_eq!(absolute.declared, absolute_path);
        assert_eq!(absolute.effective, absolute.declared);
    }

    #[test]
    fn file_wrapper_returns_exact_bytes_path_metadata_and_owned_rows() {
        let directory = temp_directory();
        fs::create_dir_all(&directory).unwrap();
        let bytes = b" 7 \t name \r\n";
        fs::write(directory.join("rows.tsv"), bytes).unwrap();
        let declared = schema(
            InputFunctionSubtype::Constructor,
            &[
                ("i64", InputSortAuthority::I64),
                ("String", InputSortAuthority::String),
            ],
            &[("Ignored", InputSortAuthority::Unsupported)],
        );

        let file = read_tsv_file(Some(&directory), "rows.tsv", &declared).unwrap();
        assert_eq!(file.bytes, bytes);
        assert_eq!(file.path.declared, Path::new("rows.tsv"));
        assert_eq!(
            file.path.fact_directory.as_deref(),
            Some(directory.as_path())
        );
        assert_eq!(file.path.effective, directory.join("rows.tsv"));
        assert_eq!(
            file.input.rows[0].values,
            [InputLiteral::I64(7), InputLiteral::String("name".into())]
        );

        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn file_wrapper_reports_utf8_and_io_errors_without_panicking() {
        let directory = temp_directory();
        fs::create_dir_all(&directory).unwrap();
        fs::write(directory.join("invalid.tsv"), [0xff]).unwrap();
        let declared = schema(
            InputFunctionSubtype::Constructor,
            &[("String", InputSortAuthority::String)],
            &[("Ignored", InputSortAuthority::Unsupported)],
        );

        assert!(matches!(
            read_tsv_file(Some(&directory), "invalid.tsv", &declared),
            Err(TypedInputReadError::InvalidUtf8 { .. })
        ));
        assert!(matches!(
            read_tsv_file(Some(&directory), "missing.tsv", &declared),
            Err(TypedInputReadError::Read { .. })
        ));

        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn file_wrapper_rejects_unsupported_schema_before_a_missing_path() {
        let directory = temp_directory();
        let declared = schema(
            InputFunctionSubtype::Constructor,
            &[("Vec", InputSortAuthority::Unsupported)],
            &[("Ignored", InputSortAuthority::Unsupported)],
        );

        assert!(matches!(
            read_tsv_file(Some(&directory), "missing.tsv", &declared),
            Err(TypedInputReadError::Parse {
                source: TypedInputParseError::UnsupportedSort { .. },
                ..
            })
        ));
    }
}
