package propel.evaluator

import org.scalatest.funsuite.AnyFunSuite
import propel.evaluator.egraph.{EClass, ENode, Operator}
import scala.collection.mutable

class EgglogEqualityGraphTests extends AnyFunSuite:
  private val lhs = EClass(ENode(Operator("lhs")))
  private val rhs = EClass(ENode(Operator("rhs")))

  private class StubRuntime(
      var equalResult: EgglogCommandResult = EgglogCommandResult.CheckFailed,
      var disequalResult: EgglogCommandResult = EgglogCommandResult.ExpectFailFailed,
      var consistencyResult: EgglogCommandResult = EgglogCommandResult.ExpectFailFailed,
  ) extends EgglogRuntime:
    var disequalityChecks = 0

    override def copyRuntime(): EgglogRuntime = this
    override def add(operator: String, children: Array[Long]): Long = 0
    override def union(lhs: Long, rhs: Long): Unit = ()
    override def disequal(lhs: Long, rhs: Long): Unit = ()
    override def rebuild(): EgglogCommandResult = EgglogCommandResult.Success
    override def checkEqual(lhs: Long, rhs: Long): EgglogCommandResult = equalResult
    override def checkKnownDisequal(lhs: Long, rhs: Long): EgglogCommandResult =
      disequalityChecks += 1
      disequalResult
    override def checkConsistency(): EgglogCommandResult = consistencyResult
    override def numNodes: Int = 2
    override def numClasses: Int = 2
    override def source: String = ""
    override def desugaredSource: String = ""

  private def graph(runtime: EgglogRuntime): EgglogEqualityGraph =
    EgglogEqualityGraph(runtime, mutable.Map(lhs.id -> 0L, rhs.id -> 1L))

  test("equality succeeds without querying disequality"):
    val runtime = StubRuntime(equalResult = EgglogCommandResult.Success)
    assert(graph(runtime).compare(lhs, rhs) == GraphComparison.Equal)
    assert(runtime.disequalityChecks == 0)

  test("failed equality then successful disequality reports unequal"):
    val runtime = StubRuntime(disequalResult = EgglogCommandResult.Success)
    assert(graph(runtime).compare(lhs, rhs) == GraphComparison.Unequal)
    assert(runtime.disequalityChecks == 1)

  test("two expected query failures report indeterminate"):
    assert(graph(StubRuntime()).compare(lhs, rhs) == GraphComparison.Indeterminate)

  test("consistency query distinguishes contradiction from no contradiction"):
    assert(graph(StubRuntime(consistencyResult = EgglogCommandResult.Success)).hasContradiction)
    assert(!graph(StubRuntime()).hasContradiction)

  test("backend errors and unexpected statuses are not reclassified"):
    val backendError = intercept[RuntimeException]:
      graph(StubRuntime(equalResult = EgglogCommandResult.Error("backend failed"))).compare(lhs, rhs)
    assert(backendError.getMessage == "backend failed")

    intercept[IllegalStateException]:
      graph(StubRuntime(equalResult = EgglogCommandResult.ExpectFailFailed)).compare(lhs, rhs)
