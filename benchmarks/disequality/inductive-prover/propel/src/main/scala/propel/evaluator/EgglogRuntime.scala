package propel.evaluator

enum EgglogEncoding(val abiValue: Int):
  case EqualityEmbedding extends EgglogEncoding(0)
  case OptimizedEqualityEmbedding extends EgglogEncoding(1)
  case NegatedEqualityEmbedding extends EgglogEncoding(2)
  case DisequalityEdges extends EgglogEncoding(3)

enum EgglogTermLanguage(val abiValue: Int):
  case Vec extends EgglogTermLanguage(0)
  case Direct extends EgglogTermLanguage(1)

case class EgglogOperatorSpec(
    sourceName: String,
    preferredName: Option[String],
    arity: Int,
)

case class EgglogLanguageSchema(
    sortName: String,
    operators: Vector[EgglogOperatorSpec],
)

enum EgglogCommandOutputKind:
  case PrintFunctionSize
  case PrintAllFunctionsSize
  case ExtractBest
  case ExtractVariants
  case ProveExists
  case OverallStatistics
  case PrintFunction
  case RunSchedule
  case UserDefined

case class EgglogCommandOutput(kind: EgglogCommandOutputKind, text: String)

/** Structured outcome of one `EGraph.run_program` call in the Rust backend. */
enum EgglogCommandResult:
  case Success(outputs: Vector[EgglogCommandOutput])
  case CheckFailed(outputs: Vector[EgglogCommandOutput])
  case ExpectFailFailed(outputs: Vector[EgglogCommandOutput])
  case Error(message: String)

trait EgglogRuntimeTemplate extends AutoCloseable:
  def newRuntime(recordInteractions: Boolean): EgglogRuntime

trait EgglogRuntime:
  def copyRuntime(): EgglogRuntime
  def add(operator: String, children: Array[Long]): Long
  def union(lhs: Long, rhs: Long): Unit
  def disequal(lhs: Long, rhs: Long): Unit
  def flush(): EgglogCommandResult
  def rebuild(): EgglogCommandResult
  def checkEqual(lhs: Long, rhs: Long): EgglogCommandResult
  def checkKnownDisequal(lhs: Long, rhs: Long): EgglogCommandResult
  def checkConsistency(): EgglogCommandResult
  def numNodes: Int
  def numClasses: Int
  def source: String
  def desugaredSource: String
