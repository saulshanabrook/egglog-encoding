//! Closed authenticated scalar-expression lowering.
//!
//! Call-site names never enter this module. A rule is admitted only through an
//! exact backend-minted token/descriptor pair and an exact concrete signature.

use std::collections::BTreeMap;

use anyhow::{Result, bail, ensure};
use egglog_backend_trait::{
    BaseValues, ColumnTy, ExternalFunctionId, NativePrimitive, NativeScalarPrimitive,
};
use egglog_numeric_id::NumericId;

use crate::storage::ScalarSqlType;

const I64_MIN: &str = "-9223372036854775808";
const I64_MAX: &str = "9223372036854775807";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ScalarAuthority {
    Native(NativePrimitive),
    Typed(NativeScalarPrimitive),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ScalarOperation {
    I64Add,
    I64Sub,
    I64Mul,
    I64Div,
    I64Rem,
    I64BitAnd,
    I64Min,
    I64Max,
    I64Ge,
    I64Gt,
    I64Le,
    I64Lt,
    I64BoolLt,
    F64Gt,
    F64Lt,
    ValueNeq(ScalarSqlType),
    OrderingMin,
    OrderingMax,
    SelectMinPayload,
    SelectMaxPayload,
    SelectEqPayload(ScalarSqlType),
}

/// An authenticated, exactly typed binary scalar operation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ScalarExpression {
    token: ExternalFunctionId,
    authority: ScalarAuthority,
    operation: ScalarOperation,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct RenderedScalarExpression {
    pub(crate) value: String,
    pub(crate) defined: String,
}

impl RenderedScalarExpression {
    pub(crate) fn is_total(&self) -> bool {
        self.defined == "TRUE"
    }
}

impl ScalarExpression {
    pub(crate) fn authenticate(
        base_values: &BaseValues,
        native_primitives: &BTreeMap<ExternalFunctionId, NativePrimitive>,
        native_scalar_primitives: &BTreeMap<ExternalFunctionId, NativeScalarPrimitive>,
        token: ExternalFunctionId,
        inputs: &[ColumnTy],
        output: ColumnTy,
    ) -> Result<Self> {
        ensure!(
            !(native_primitives.contains_key(&token)
                && native_scalar_primitives.contains_key(&token)),
            "DuckDB scalar token {} has ambiguous native authority",
            token.rep()
        );

        let (authority, operation) = if let Some(&primitive) = native_scalar_primitives.get(&token)
        {
            let operation = authenticate_typed(base_values, primitive, inputs, output)?;
            (ScalarAuthority::Typed(primitive), operation)
        } else if let Some(&primitive) = native_primitives.get(&token) {
            let operation = authenticate_raw(base_values, primitive, inputs, output)?;
            (ScalarAuthority::Native(primitive), operation)
        } else {
            bail!(
                "DuckDB scalar expression uses unauthenticated or callback primitive token {}",
                token.rep()
            );
        };

        Ok(Self {
            token,
            authority,
            operation,
        })
    }

    pub(crate) fn token(&self) -> ExternalFunctionId {
        self.token
    }

    pub(crate) fn authority(&self) -> ScalarAuthority {
        self.authority
    }

    pub(crate) fn render(&self, inputs: &[String]) -> RenderedScalarExpression {
        match self.operation {
            ScalarOperation::SelectMinPayload | ScalarOperation::SelectMaxPayload => {
                let [left, left_payload, right, right_payload] = inputs else {
                    unreachable!("authenticated payload selectors have four inputs")
                };
                let operator = if self.operation == ScalarOperation::SelectMinPayload {
                    "<"
                } else {
                    ">"
                };
                return RenderedScalarExpression {
                    value: format!(
                        "CASE WHEN ({left}) {operator} ({right}) THEN ({left_payload}) ELSE ({right_payload}) END"
                    ),
                    defined: "TRUE".to_string(),
                };
            }
            ScalarOperation::SelectEqPayload(comparison_type) => {
                let [test, candidate, if_equal, otherwise] = inputs else {
                    unreachable!("authenticated equality selector has four inputs")
                };
                let equal = raw_equal(comparison_type, test, candidate);
                return RenderedScalarExpression {
                    value: format!("CASE WHEN {equal} THEN ({if_equal}) ELSE ({otherwise}) END"),
                    defined: "TRUE".to_string(),
                };
            }
            _ => {}
        }
        let [left, right] = inputs else {
            unreachable!("authenticated scalar expressions are binary")
        };
        let left = format!("({left})");
        let right = format!("({right})");
        match self.operation {
            ScalarOperation::I64Add => checked_wide(&left, "+", &right),
            ScalarOperation::I64Sub => checked_wide(&left, "-", &right),
            ScalarOperation::I64Mul => checked_wide(&left, "*", &right),
            ScalarOperation::I64Div => checked_div_rem(&left, "//", &right),
            ScalarOperation::I64Rem => checked_div_rem(&left, "%", &right),
            ScalarOperation::I64BitAnd => RenderedScalarExpression {
                value: format!("(CAST({left} AS BIGINT) & CAST({right} AS BIGINT))"),
                defined: "TRUE".to_string(),
            },
            ScalarOperation::I64Min => total_choice(&left, "<", &right),
            ScalarOperation::I64Max => total_choice(&left, ">", &right),
            ScalarOperation::I64Ge => unit_predicate(format!("({left} >= {right})")),
            ScalarOperation::I64Gt => unit_predicate(format!("({left} > {right})")),
            ScalarOperation::I64Le => unit_predicate(format!("({left} <= {right})")),
            ScalarOperation::I64Lt => unit_predicate(format!("({left} < {right})")),
            ScalarOperation::I64BoolLt => RenderedScalarExpression {
                value: format!("({left} < {right})"),
                defined: "TRUE".to_string(),
            },
            ScalarOperation::F64Gt => unit_predicate(format!(
                "((isnan({left}) AND NOT isnan({right})) OR (NOT isnan({left}) AND NOT isnan({right}) AND {left} > {right}))"
            )),
            ScalarOperation::F64Lt => unit_predicate(format!(
                "(NOT isnan({left}) AND (isnan({right}) OR {left} < {right}))"
            )),
            ScalarOperation::ValueNeq(ScalarSqlType::F64) => {
                let equal = format!(
                    "((isnan({left}) AND isnan({right})) OR (NOT isnan({left}) AND NOT isnan({right}) AND {left} = {right}))"
                );
                unit_predicate(format!("NOT ({equal})"))
            }
            ScalarOperation::ValueNeq(
                ScalarSqlType::Id | ScalarSqlType::I64 | ScalarSqlType::String,
            ) => unit_predicate(format!("NOT ({left} = {right})")),
            ScalarOperation::ValueNeq(_) => {
                unreachable!("signature authentication restricts ValueNeq types")
            }
            ScalarOperation::OrderingMin => total_choice(&left, "<", &right),
            ScalarOperation::OrderingMax => total_choice(&left, ">", &right),
            ScalarOperation::SelectMinPayload
            | ScalarOperation::SelectMaxPayload
            | ScalarOperation::SelectEqPayload(_) => unreachable!(),
        }
    }
}

fn authenticate_typed(
    base_values: &BaseValues,
    primitive: NativeScalarPrimitive,
    inputs: &[ColumnTy],
    output: ColumnTy,
) -> Result<ScalarOperation> {
    let [left, right] = inputs else {
        bail!("DuckDB typed scalar {primitive:?} requires exactly two inputs");
    };
    let left = ScalarSqlType::from_column(base_values, *left)?;
    let right = ScalarSqlType::from_column(base_values, *right)?;
    let output = ScalarSqlType::from_column(base_values, output)?;

    let (expected_input, expected_output, operation) = match primitive {
        NativeScalarPrimitive::I64Add => (
            ScalarSqlType::I64,
            ScalarSqlType::I64,
            ScalarOperation::I64Add,
        ),
        NativeScalarPrimitive::I64Sub => (
            ScalarSqlType::I64,
            ScalarSqlType::I64,
            ScalarOperation::I64Sub,
        ),
        NativeScalarPrimitive::I64Mul => (
            ScalarSqlType::I64,
            ScalarSqlType::I64,
            ScalarOperation::I64Mul,
        ),
        NativeScalarPrimitive::I64Div => (
            ScalarSqlType::I64,
            ScalarSqlType::I64,
            ScalarOperation::I64Div,
        ),
        NativeScalarPrimitive::I64Rem => (
            ScalarSqlType::I64,
            ScalarSqlType::I64,
            ScalarOperation::I64Rem,
        ),
        NativeScalarPrimitive::I64BitAnd => (
            ScalarSqlType::I64,
            ScalarSqlType::I64,
            ScalarOperation::I64BitAnd,
        ),
        NativeScalarPrimitive::I64Min => (
            ScalarSqlType::I64,
            ScalarSqlType::I64,
            ScalarOperation::I64Min,
        ),
        NativeScalarPrimitive::I64Max => (
            ScalarSqlType::I64,
            ScalarSqlType::I64,
            ScalarOperation::I64Max,
        ),
        NativeScalarPrimitive::I64Ge => (
            ScalarSqlType::I64,
            ScalarSqlType::Unit,
            ScalarOperation::I64Ge,
        ),
        NativeScalarPrimitive::I64Gt => (
            ScalarSqlType::I64,
            ScalarSqlType::Unit,
            ScalarOperation::I64Gt,
        ),
        NativeScalarPrimitive::I64Le => (
            ScalarSqlType::I64,
            ScalarSqlType::Unit,
            ScalarOperation::I64Le,
        ),
        NativeScalarPrimitive::I64Lt => (
            ScalarSqlType::I64,
            ScalarSqlType::Unit,
            ScalarOperation::I64Lt,
        ),
        NativeScalarPrimitive::I64BoolLt => (
            ScalarSqlType::I64,
            ScalarSqlType::Bool,
            ScalarOperation::I64BoolLt,
        ),
        NativeScalarPrimitive::F64Gt => (
            ScalarSqlType::F64,
            ScalarSqlType::Unit,
            ScalarOperation::F64Gt,
        ),
        NativeScalarPrimitive::F64Lt => (
            ScalarSqlType::F64,
            ScalarSqlType::Unit,
            ScalarOperation::F64Lt,
        ),
        _ => bail!("DuckDB typed scalar {primitive:?} is not a supported descriptor"),
    };
    ensure!(
        left == expected_input && right == expected_input && output == expected_output,
        "DuckDB typed scalar {primitive:?} has signature ({left:?}, {right:?}) -> {output:?}; expected ({expected_input:?}, {expected_input:?}) -> {expected_output:?}"
    );
    Ok(operation)
}

fn authenticate_raw(
    base_values: &BaseValues,
    primitive: NativePrimitive,
    inputs: &[ColumnTy],
    output: ColumnTy,
) -> Result<ScalarOperation> {
    if primitive == NativePrimitive::SelectEqPayload {
        let [test, candidate, if_equal, otherwise] = inputs else {
            bail!("DuckDB raw scalar {primitive:?} requires exactly four inputs")
        };
        ensure!(
            test == candidate && if_equal == otherwise && *if_equal == output,
            "DuckDB raw {primitive:?} requires (T, T, P, P) -> P"
        );
        let comparison_type = ScalarSqlType::from_column(base_values, *test)?;
        ScalarSqlType::from_column(base_values, *if_equal)?;
        return Ok(ScalarOperation::SelectEqPayload(comparison_type));
    }
    if matches!(
        primitive,
        NativePrimitive::SelectMinPayload | NativePrimitive::SelectMaxPayload
    ) {
        let [left, left_payload, right, right_payload] = inputs else {
            bail!("DuckDB raw scalar {primitive:?} requires exactly four inputs")
        };
        ensure!(
            *left == ColumnTy::Id
                && *right == ColumnTy::Id
                && left_payload == right_payload
                && *left_payload == output,
            "DuckDB raw {primitive:?} requires (Id, T, Id, T) -> T"
        );
        ScalarSqlType::from_column(base_values, *left_payload)?;
        return Ok(if primitive == NativePrimitive::SelectMinPayload {
            ScalarOperation::SelectMinPayload
        } else {
            ScalarOperation::SelectMaxPayload
        });
    }
    let [left, right] = inputs else {
        bail!("DuckDB raw scalar {primitive:?} requires exactly two inputs");
    };
    let left_scalar = ScalarSqlType::from_column(base_values, *left)?;
    let right_scalar = ScalarSqlType::from_column(base_values, *right)?;
    let output_scalar = ScalarSqlType::from_column(base_values, output)?;
    match primitive {
        NativePrimitive::ValueNeq => {
            ensure!(
                left == right
                    && left_scalar == right_scalar
                    && matches!(
                        left_scalar,
                        ScalarSqlType::Id
                            | ScalarSqlType::I64
                            | ScalarSqlType::F64
                            | ScalarSqlType::String
                    )
                    && output_scalar == ScalarSqlType::Unit,
                "DuckDB ValueNeq requires matching Id/i64/f64/String inputs and Unit output"
            );
            Ok(ScalarOperation::ValueNeq(left_scalar))
        }
        NativePrimitive::OrderingMin | NativePrimitive::OrderingMax => {
            ensure!(
                *left == ColumnTy::Id && *right == ColumnTy::Id && output == ColumnTy::Id,
                "DuckDB raw {primitive:?} scalar lowering requires (Id, Id) -> Id"
            );
            Ok(if primitive == NativePrimitive::OrderingMin {
                ScalarOperation::OrderingMin
            } else {
                ScalarOperation::OrderingMax
            })
        }
        NativePrimitive::SelectMinPayload
        | NativePrimitive::SelectMaxPayload
        | NativePrimitive::SelectEqPayload => unreachable!(),
        _ => bail!("DuckDB raw primitive {primitive:?} is not a public scalar expression"),
    }
}

fn raw_equal(ty: ScalarSqlType, left: &str, right: &str) -> String {
    match ty {
        ScalarSqlType::F64 => format!(
            "((isnan({left}) AND isnan({right})) OR (NOT isnan({left}) AND NOT isnan({right}) AND ({left}) = ({right})))"
        ),
        ScalarSqlType::Unit => "TRUE".to_string(),
        _ => format!("(({left}) = ({right}))"),
    }
}

fn checked_wide(left: &str, operator: &str, right: &str) -> RenderedScalarExpression {
    let wide = format!("(CAST({left} AS HUGEINT) {operator} CAST({right} AS HUGEINT))");
    let defined = format!(
        "({wide} >= CAST('{I64_MIN}' AS HUGEINT) AND {wide} <= CAST('{I64_MAX}' AS HUGEINT))"
    );
    RenderedScalarExpression {
        value: format!(
            "CAST((CASE WHEN {defined} THEN {wide} ELSE CAST('0' AS HUGEINT) END) AS BIGINT)"
        ),
        defined,
    }
}

fn checked_div_rem(left: &str, operator: &str, right: &str) -> RenderedScalarExpression {
    let defined = format!(
        "({right} <> CAST('0' AS BIGINT) AND NOT ({left} = CAST('{I64_MIN}' AS BIGINT) AND {right} = CAST('-1' AS BIGINT)))"
    );
    let divisor = format!(
        "(CASE WHEN {defined} THEN CAST({right} AS HUGEINT) ELSE CAST('1' AS HUGEINT) END)"
    );
    RenderedScalarExpression {
        value: format!("CAST((CAST({left} AS HUGEINT) {operator} {divisor}) AS BIGINT)"),
        defined,
    }
}

fn total_choice(left: &str, comparison: &str, right: &str) -> RenderedScalarExpression {
    RenderedScalarExpression {
        value: format!("(CASE WHEN {left} {comparison} {right} THEN {left} ELSE {right} END)"),
        defined: "TRUE".to_string(),
    }
}

fn unit_predicate(predicate: String) -> RenderedScalarExpression {
    RenderedScalarExpression {
        value: "CAST(TRUE AS BOOLEAN)".to_string(),
        defined: predicate,
    }
}
