package propel.evaluator

object EgglogRuntimePlatform:
  def createTemplate(
      encoding: EgglogEncoding,
      termLanguage: EgglogTermLanguage,
      schema: EgglogLanguageSchema,
  ): EgglogRuntimeTemplate =
    throw UnsupportedOperationException(
      s"${encoding.toString} requires the Scala Native Propel executable",
    )
