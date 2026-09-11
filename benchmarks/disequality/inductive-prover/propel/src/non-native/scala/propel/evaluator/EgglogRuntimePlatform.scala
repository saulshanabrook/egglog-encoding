package propel.evaluator

object EgglogRuntimePlatform:
  def create(encoding: EgglogEncoding, recordInteractions: Boolean): EgglogRuntime =
    throw UnsupportedOperationException(
      s"${encoding.toString} requires the Scala Native Propel executable",
    )

  def createTemplate(
      encoding: EgglogEncoding,
      termLanguage: EgglogTermLanguage,
      schema: EgglogLanguageSchema,
  ): EgglogRuntimeTemplate =
    throw UnsupportedOperationException(
      s"${encoding.toString} requires the Scala Native Propel executable",
    )
