package propel.evaluator

import java.lang.ref.WeakReference
import scala.collection.mutable.ArrayBuffer
import scala.scalanative.unsafe.*
import scala.scalanative.unsigned.*

@extern
@link("egglog_disequality_backend")
private object EgglogApi:
  def egglog_disequality_graph_new(encoding: CUnsignedInt, recordInteractions: CInt): Ptr[Byte] = extern
  def egglog_disequality_template_new(
      encoding: CUnsignedInt,
      termLanguage: CUnsignedInt,
      sortName: CString,
  ): Ptr[Byte] = extern
  def egglog_disequality_template_register_operator(
      template: Ptr[Byte],
      sourceName: CString,
      preferredName: CString,
      arity: CSize,
  ): CUnsignedInt = extern
  def egglog_disequality_template_finish(template: Ptr[Byte]): CInt = extern
  def egglog_disequality_graph_new_from_template(
      template: Ptr[Byte],
      recordInteractions: CInt,
  ): Ptr[Byte] = extern
  def egglog_disequality_template_free(template: Ptr[Byte]): Unit = extern
  def egglog_disequality_template_last_error(template: Ptr[Byte]): CString = extern
  def egglog_disequality_graph_clone(graph: Ptr[Byte]): Ptr[Byte] = extern
  def egglog_disequality_graph_free(graph: Ptr[Byte]): Unit = extern
  def egglog_disequality_add(
      graph: Ptr[Byte],
      operatorName: CString,
      children: Ptr[CUnsignedLongLong],
      childCount: CSize,
  ): CUnsignedLongLong = extern
  def egglog_disequality_add_atom(
      graph: Ptr[Byte],
      atomName: CString,
  ): CUnsignedLongLong = extern
  def egglog_disequality_add_registered(
      graph: Ptr[Byte],
      operatorId: CUnsignedInt,
      children: Ptr[CUnsignedLongLong],
      childCount: CSize,
  ): CUnsignedLongLong = extern
  def egglog_disequality_union(graph: Ptr[Byte], lhs: CUnsignedLongLong, rhs: CUnsignedLongLong): CInt = extern
  def egglog_disequality_disunion(graph: Ptr[Byte], lhs: CUnsignedLongLong, rhs: CUnsignedLongLong): CInt = extern
  def egglog_disequality_rebuild(graph: Ptr[Byte]): CInt = extern
  def egglog_disequality_compare(graph: Ptr[Byte], lhs: CUnsignedLongLong, rhs: CUnsignedLongLong): CInt = extern
  def egglog_disequality_is_consistent(graph: Ptr[Byte]): CInt = extern
  def egglog_disequality_num_nodes(graph: Ptr[Byte]): CUnsignedLongLong = extern
  def egglog_disequality_num_classes(graph: Ptr[Byte]): CUnsignedLongLong = extern
  def egglog_disequality_write_snapshot(
      graph: Ptr[Byte],
      sourcePath: CString,
      desugaredPath: CString,
  ): CInt = extern
  def egglog_disequality_last_error(graph: Ptr[Byte]): CString = extern

object EgglogRuntimePlatform:
  def create(encoding: EgglogEncoding, recordInteractions: Boolean): EgglogRuntime =
    NativeEgglogRuntime.checkedPointer(
      EgglogApi.egglog_disequality_graph_new(
        encoding.abiValue.toUInt,
        (if recordInteractions then 1 else 0),
      ),
      EgglogTermLanguage.Vec,
      Map.empty,
      "create egglog graph",
    )

  def createTemplate(
      encoding: EgglogEncoding,
      termLanguage: EgglogTermLanguage,
      schema: EgglogLanguageSchema,
  ): EgglogRuntimeTemplate = Zone {
    val template = NativeEgglogTemplate.checkedPointer(
      EgglogApi.egglog_disequality_template_new(
        encoding.abiValue.toUInt,
        termLanguage.abiValue.toUInt,
        toCString(schema.sortName),
      ),
      "create egglog graph template",
    )
    try
      val operatorIds = termLanguage match
        case EgglogTermLanguage.Vec => Map.empty
        case EgglogTermLanguage.Direct => schema.operators.map(spec =>
          val preferredName = spec.preferredName match
            case Some(name) => toCString(name)
            case None => 0L.toPtr[Byte]
          val result = EgglogApi.egglog_disequality_template_register_operator(
            template.pointer,
            toCString(spec.sourceName),
            preferredName,
            spec.arity.toUSize,
          )
          if result == UInt.MaxValue then template.fail(s"register ${spec.sourceName}/${spec.arity}")
          (spec.sourceName, spec.arity) -> result.toInt
        ).toMap
      template.finish(termLanguage, operatorIds)
    catch
      case error: Throwable =>
        template.close()
        throw error
  }

private object NativeEgglogTemplate:
  def checkedPointer(template: Ptr[Byte], operation: String): NativeEgglogTemplate =
    if template.toLong == 0 then throw RuntimeException(s"failed to $operation")
    new NativeEgglogTemplate(template)

private final class NativeEgglogTemplate private (
    val pointer: Ptr[Byte],
):
  private var closed = false

  def fail(operation: String): Nothing =
    val message = EgglogApi.egglog_disequality_template_last_error(pointer)
    val detail =
      if message.toLong == 0 then "unknown Rust backend error"
      else fromCString(message)
    throw RuntimeException(s"failed to $operation: $detail")

  def finish(
      termLanguage: EgglogTermLanguage,
      operatorIds: Map[(String, Int), Int],
  ): EgglogRuntimeTemplate =
    if EgglogApi.egglog_disequality_template_finish(pointer) != 0 then fail("finish egglog graph template")
    NativeEgglogRuntimeTemplate(this, termLanguage, operatorIds)

  def close(): Unit =
    if !closed then
      EgglogApi.egglog_disequality_template_free(pointer)
      closed = true

  def isClosed: Boolean = closed

private final class NativeEgglogRuntimeTemplate(
    owner: NativeEgglogTemplate,
    termLanguage: EgglogTermLanguage,
    operatorIds: Map[(String, Int), Int],
) extends EgglogRuntimeTemplate:
  override def newRuntime(recordInteractions: Boolean): EgglogRuntime =
    if owner.isClosed then throw IllegalStateException("egglog graph template is closed")
    val graph = EgglogApi.egglog_disequality_graph_new_from_template(
      owner.pointer,
      (if recordInteractions then 1 else 0),
    )
    if graph.toLong == 0 then owner.fail("create egglog graph from template")
    NativeEgglogRuntime.checkedPointer(
      graph,
      termLanguage,
      operatorIds,
      "create egglog graph from template",
    )

  override def close(): Unit = owner.close()

private object NativeEgglogRuntime:
  private case class Tracked(
      owner: WeakReference[NativeEgglogRuntime],
      graph: Ptr[Byte],
  )
  private val tracked = ArrayBuffer.empty[Tracked]

  private def collectDeadGraphs(): Unit = synchronized {
    var index = tracked.length - 1
    while index >= 0 do
      if tracked(index).owner.get() == null then
        EgglogApi.egglog_disequality_graph_free(tracked(index).graph)
        tracked.remove(index)
      index -= 1
  }

  def checkedPointer(
      graph: Ptr[Byte],
      termLanguage: EgglogTermLanguage,
      operatorIds: Map[(String, Int), Int],
      operation: String,
  ): NativeEgglogRuntime =
    if graph.toLong == 0 then throw RuntimeException(s"failed to $operation")
    collectDeadGraphs()
    val runtime = NativeEgglogRuntime(graph, termLanguage, operatorIds)
    synchronized {
      tracked += Tracked(WeakReference(runtime), graph)
    }
    runtime

private final class NativeEgglogRuntime private (
    private val graph: Ptr[Byte],
    private val termLanguage: EgglogTermLanguage,
    private val operatorIds: Map[(String, Int), Int],
) extends EgglogRuntime:
  private def fail(operation: String): Nothing =
    val message = EgglogApi.egglog_disequality_last_error(graph)
    val detail =
      if message.toLong == 0 then "unknown Rust backend error"
      else fromCString(message)
    throw RuntimeException(s"failed to $operation: $detail")

  private def check(result: CInt, operation: String): Unit =
    if result != 0 then fail(operation)

  private def count(result: CUnsignedLongLong, operation: String): Int =
    val value = result.toLong
    if value < 0 || value > Int.MaxValue then fail(operation)
    value.toInt

  override def copyRuntime(): EgglogRuntime =
    NativeEgglogRuntime.checkedPointer(
      EgglogApi.egglog_disequality_graph_clone(graph),
      termLanguage,
      operatorIds,
      "clone egglog graph",
    )

  override def add(operator: String, children: Array[Long]): Long = Zone {
    val childPointer =
      if children.isEmpty then 0L.toPtr[CUnsignedLongLong]
      else
        val pointer = alloc[CUnsignedLongLong](children.length)
        children.indices.foreach(index => !(pointer + index) = children(index).toULong)
        pointer
    val result = termLanguage match
      case EgglogTermLanguage.Vec =>
        EgglogApi.egglog_disequality_add(
          graph,
          toCString(operator),
          childPointer,
          children.length.toUSize,
        ).toLong
      case EgglogTermLanguage.Direct =>
        operatorIds.get((operator, children.length)) match
          case Some(operatorId) =>
            EgglogApi.egglog_disequality_add_registered(
              graph,
              operatorId.toUInt,
              childPointer,
              children.length.toUSize,
            ).toLong
          case None if children.isEmpty =>
            EgglogApi.egglog_disequality_add_atom(graph, toCString(operator)).toLong
          case None if operator.startsWith("@Λ") && children.length == 1 =>
            val binder = EgglogApi
              .egglog_disequality_add_atom(graph, toCString(operator.stripPrefix("@Λ")))
              .toLong
            if binder < 0 then fail("add a type-lambda binder")
            val typeLambda = operatorIds.getOrElse(
              ("@Λ", 2),
              throw IllegalStateException("Propel type-lambda constructor was absent from the egglog schema"),
            )
            val expandedChildren = alloc[CUnsignedLongLong](2)
            !expandedChildren = binder.toULong
            !(expandedChildren + 1) = children(0).toULong
            EgglogApi.egglog_disequality_add_registered(
              graph,
              typeLambda.toUInt,
              expandedChildren,
              2.toUSize,
            ).toLong
          case None =>
            throw IllegalStateException(
              s"Propel constructor $operator/${children.length} was absent from the egglog schema",
            )
    if result < 0 then fail("add an e-node")
    result
  }

  override def union(lhs: Long, rhs: Long): Unit =
    check(EgglogApi.egglog_disequality_union(graph, lhs.toULong, rhs.toULong), "union e-classes")

  override def disequal(lhs: Long, rhs: Long): Unit =
    check(EgglogApi.egglog_disequality_disunion(graph, lhs.toULong, rhs.toULong), "add a disequality")

  override def rebuild(): Unit =
    check(EgglogApi.egglog_disequality_rebuild(graph), "rebuild the e-graph")

  override def compare(lhs: Long, rhs: Long): Int =
    val result = EgglogApi.egglog_disequality_compare(graph, lhs.toULong, rhs.toULong)
    if result < 0 then fail("compare e-classes")
    result

  override def isConsistent: Boolean =
    val result = EgglogApi.egglog_disequality_is_consistent(graph)
    if result < 0 then fail("check graph consistency")
    result != 0

  override def numNodes: Int = count(EgglogApi.egglog_disequality_num_nodes(graph), "count e-nodes")
  override def numClasses: Int = count(EgglogApi.egglog_disequality_num_classes(graph), "count e-classes")

  override def writeSnapshot(sourcePath: String, desugaredPath: String): Unit = Zone {
    check(
      EgglogApi.egglog_disequality_write_snapshot(
        graph,
        toCString(sourcePath),
        toCString(desugaredPath),
      ),
      "write an egglog snapshot",
    )
  }
