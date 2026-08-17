package propel.evaluator

import propel.evaluator.egraph.{EClass, ENode}
import propel.evaluator.egraph.mutable.{EGraph, EGraphOps}
import scala.collection.mutable

enum GraphComparison:
  case Equal
  case Unequal
  case Indeterminate

case class EqualityGraphStats(classes: Int, nodes: Int)

trait EqualityGraph:
  def copyGraph(): EqualityGraph
  def add(node: ENode): EClass
  def union(lhs: EClass, rhs: EClass): Unit
  def disequal(lhs: EClass, rhs: EClass): Unit
  def compare(lhs: EClass, rhs: EClass): GraphComparison
  def rebuild(): Unit
  def hasContradiction: Boolean
  def stats: EqualityGraphStats
  def writeSnapshot(sourcePath: String, desugaredPath: String): Unit

trait EqualityGraphBackend:
  def name: String
  def isEgglog: Boolean
  def empty: EqualityGraph
  def withEgglogLanguage(
      termLanguage: EgglogTermLanguage,
      schema: EgglogLanguageSchema,
      cacheTemplate: Boolean,
  ): EqualityGraphBackend = this

object EqualityGraphBackend:
  val DisequalityEdges: EqualityGraphBackend = NativeBackend(
    "de",
    EGraph.DisequalityEdges.EGraphsOps,
  )
  val EqualityEmbedding: EqualityGraphBackend = NativeBackend(
    "ee",
    EGraph.EqualityEmbedding.EGraphsOps,
  )
  val DisequalityEmbedding: EqualityGraphBackend = NativeBackend(
    "nee",
    EGraph.DisequalityEmbedding.EGraphsOps,
  )
  val EgglogEqualityEmbedding: EqualityGraphBackend = EgglogBackend(
    "egglog-ee",
    EgglogEncoding.EqualityEmbedding,
  )
  val EgglogOptimizedEqualityEmbedding: EqualityGraphBackend = EgglogBackend(
    "egglog-oee",
    EgglogEncoding.OptimizedEqualityEmbedding,
  )
  val EgglogNegatedEqualityEmbedding: EqualityGraphBackend = EgglogBackend(
    "egglog-nee",
    EgglogEncoding.NegatedEqualityEmbedding,
  )
  val EgglogDisequalityEdges: EqualityGraphBackend = EgglogBackend(
    "egglog-de",
    EgglogEncoding.DisequalityEdges,
  )

  private case class NativeBackend(
      name: String,
      operations: EGraphOps[EGraph.EGraph],
  ) extends EqualityGraphBackend:
    override val isEgglog: Boolean = false
    override def empty: EqualityGraph = NativeEqualityGraph(EGraph.empty, operations)

  private case class EgglogBackend(
      name: String,
      encoding: EgglogEncoding,
      termLanguage: EgglogTermLanguage = EgglogTermLanguage.Vec,
      schema: EgglogLanguageSchema = EgglogLanguageSchema("BenchmarkTerm", Vector.empty),
      cacheTemplate: Boolean = false,
  ) extends EqualityGraphBackend:
    override val isEgglog: Boolean = true
    private lazy val template = EgglogRuntimePlatform.createTemplate(encoding, termLanguage, schema)
    override def withEgglogLanguage(
        termLanguage: EgglogTermLanguage,
        schema: EgglogLanguageSchema,
        cacheTemplate: Boolean,
    ): EqualityGraphBackend = copy(
      termLanguage = termLanguage,
      schema = schema,
      cacheTemplate = cacheTemplate,
    )
    override def empty: EqualityGraph = EgglogEqualityGraph(
      if termLanguage == EgglogTermLanguage.Vec && !cacheTemplate then
        EgglogRuntimePlatform.create(encoding)
      else if cacheTemplate then template.newRuntime()
      else
        val uncachedTemplate = EgglogRuntimePlatform.createTemplate(encoding, termLanguage, schema)
        try uncachedTemplate.newRuntime()
        finally uncachedTemplate.close(),
      mutable.Map.empty,
    )

private case class NativeEqualityGraph(
    underlying: EGraph.EGraph,
    operations: EGraphOps[EGraph.EGraph],
) extends EqualityGraph:
  private given EGraphOps[EGraph.EGraph] = operations

  override def copyGraph(): EqualityGraph =
    NativeEqualityGraph(EGraph.clone(underlying), operations)
  override def add(node: ENode): EClass = underlying.add(node)
  override def union(lhs: EClass, rhs: EClass): Unit =
    underlying.union(lhs, rhs)
    ()
  override def disequal(lhs: EClass, rhs: EClass): Unit = underlying.disunion(lhs, rhs)
  override def compare(lhs: EClass, rhs: EClass): GraphComparison =
    if underlying.equal(lhs, rhs) then GraphComparison.Equal
    else if underlying.unequal(lhs, rhs) then GraphComparison.Unequal
    else GraphComparison.Indeterminate
  override def rebuild(): Unit = underlying.rebuild()
  override def hasContradiction: Boolean = underlying.hasContradiction
  override def stats: EqualityGraphStats =
    val classes = underlying.eclasses
    EqualityGraphStats(classes.size, classes.valuesIterator.map(_.size).sum)
  override def writeSnapshot(sourcePath: String, desugaredPath: String): Unit =
    throw UnsupportedOperationException("native Propel e-graphs cannot emit egglog source")

private case class EgglogEqualityGraph(
    runtime: EgglogRuntime,
    terms: mutable.Map[EClass.Id, Long],
) extends EqualityGraph:
  override def copyGraph(): EqualityGraph = EgglogEqualityGraph(runtime.copyRuntime(), terms.clone())

  override def add(node: ENode): EClass =
    val eclass = EClass(node)
    terms.getOrElseUpdate(
      eclass.id,
      runtime.add(node.op.id.name, node.refs.map(ref => terms(ref.id)).toArray),
    )
    eclass

  override def union(lhs: EClass, rhs: EClass): Unit = runtime.union(terms(lhs.id), terms(rhs.id))
  override def disequal(lhs: EClass, rhs: EClass): Unit = runtime.disequal(terms(lhs.id), terms(rhs.id))
  override def compare(lhs: EClass, rhs: EClass): GraphComparison =
    runtime.compare(terms(lhs.id), terms(rhs.id)) match
      case 0 => GraphComparison.Equal
      case 1 => GraphComparison.Unequal
      case 2 => GraphComparison.Indeterminate
      case result => throw IllegalStateException(s"unknown egglog comparison result: $result")
  override def rebuild(): Unit = runtime.rebuild()
  override def hasContradiction: Boolean = !runtime.isConsistent
  override def stats: EqualityGraphStats = EqualityGraphStats(runtime.numClasses, runtime.numNodes)
  override def writeSnapshot(sourcePath: String, desugaredPath: String): Unit =
    runtime.writeSnapshot(sourcePath, desugaredPath)
