package propel.evaluator

import java.lang.ref.WeakReference
import scala.collection.mutable.ArrayBuffer
import scala.scalanative.unsafe.*
import scala.scalanative.unsigned.*

@extern
@link("egglog_disequality_backend")
private object EgglogApi:
  def egglog_disequality_graph_new(encoding: CUnsignedInt): Ptr[Byte] = extern
  def egglog_disequality_graph_clone(graph: Ptr[Byte]): Ptr[Byte] = extern
  def egglog_disequality_graph_free(graph: Ptr[Byte]): Unit = extern
  def egglog_disequality_add(
      graph: Ptr[Byte],
      operatorName: CString,
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
  def create(encoding: EgglogEncoding): EgglogRuntime =
    NativeEgglogRuntime.checkedPointer(
      EgglogApi.egglog_disequality_graph_new(encoding.abiValue.toUInt),
      "create egglog graph",
    )

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

  def checkedPointer(graph: Ptr[Byte], operation: String): NativeEgglogRuntime =
    if graph.toLong == 0 then throw RuntimeException(s"failed to $operation")
    collectDeadGraphs()
    val runtime = NativeEgglogRuntime(graph)
    synchronized {
      tracked += Tracked(WeakReference(runtime), graph)
    }
    runtime

private final class NativeEgglogRuntime private (private val graph: Ptr[Byte]) extends EgglogRuntime:
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
      "clone egglog graph",
    )

  override def add(operator: String, children: Array[Long]): Long = Zone {
    val childPointer =
      if children.isEmpty then 0L.toPtr[CUnsignedLongLong]
      else
        val pointer = alloc[CUnsignedLongLong](children.length)
        children.indices.foreach(index => !(pointer + index) = children(index).toULong)
        pointer
    val result = EgglogApi.egglog_disequality_add(
      graph,
      toCString(operator),
      childPointer,
      children.length.toUSize,
    ).toLong
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
