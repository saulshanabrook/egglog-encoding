package propel.evaluator

enum EgglogEncoding(val abiValue: Int):
  case EqualityEmbedding extends EgglogEncoding(0)
  case OptimizedEqualityEmbedding extends EgglogEncoding(1)
  case NegatedEqualityEmbedding extends EgglogEncoding(2)
  case DisequalityEdges extends EgglogEncoding(3)

trait EgglogRuntime:
  def copyRuntime(): EgglogRuntime
  def add(operator: String, children: Array[Long]): Long
  def union(lhs: Long, rhs: Long): Unit
  def disequal(lhs: Long, rhs: Long): Unit
  def rebuild(): Unit
  def compare(lhs: Long, rhs: Long): Int
  def isConsistent: Boolean
  def numNodes: Int
  def numClasses: Int
  def writeSnapshot(sourcePath: String, desugaredPath: String): Unit
