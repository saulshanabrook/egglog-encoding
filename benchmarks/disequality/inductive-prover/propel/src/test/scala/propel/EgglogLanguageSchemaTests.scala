package propel

import org.scalatest.funsuite.AnyFunSuite
import propel.evaluator.egraph.Language

class EgglogLanguageSchemaTests extends AnyFunSuite:
  test("schema contains reachable Propel operators without unused adapter declarations"):
    val schema = Language.PropelLanguage.egglogSchema(builtInBenchmarks("nat_add1_comm"))
    val operators = schema.operators.map(spec => (spec.sourceName, spec.arity)).toSet

    assert(operators.contains(("@λ", 2)))
    assert(operators.contains(("@apply", 2)))
    assert(operators.contains(("@case", 2)))
    assert(operators.contains(("@match", 3)))
    assert(operators.contains(("S", 1)))
    assert(operators.contains(("Z", 0)))
    assert(operators.contains(("Unit", 0)))
    assert(operators.contains(("≟", 2)))
    assert(operators.contains(("≛", 1)))
    assert(!operators.exists(_._1 == "@:"))
    assert(!operators.exists(_._1 == "@new"))

  test("type lambdas encode their dynamic binder as a term"):
    val schema = Language.PropelLanguage.egglogSchema(builtInBenchmarks("tip_list_append_assoc"))
    val operators = schema.operators.map(spec => (spec.sourceName, spec.arity)).toSet

    assert(operators.contains(("@Λ", 2)))
    assert(!operators.exists((name, arity) => name.startsWith("@Λ") && arity == 1))
