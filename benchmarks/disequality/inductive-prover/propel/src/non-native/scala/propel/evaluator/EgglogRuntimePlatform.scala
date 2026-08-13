package propel.evaluator

object EgglogRuntimePlatform:
  def create(encoding: EgglogEncoding): EgglogRuntime =
    throw UnsupportedOperationException(
      s"${encoding.toString} requires the Scala Native Propel executable",
    )
