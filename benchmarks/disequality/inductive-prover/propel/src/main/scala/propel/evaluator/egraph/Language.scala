package propel.evaluator.egraph

import propel.ast.Pattern.{Bind, Match}
import propel.ast.Term.{Abs, App, Cases, Data, TypeAbs, TypeApp, Var}
import propel.ast.{Pattern, Term, Type}
import propel.evaluator.{EgglogLanguageSchema, EgglogOperatorSpec}
import scala.collection.mutable

/**
 * A language for writing terms interpretable by e-graphs.
 * @tparam T the possible terms in the language.
 * @note a language depends on a [[EClassGenerator]] to generate [[EClass]]es and
 *       [[ENode]] from terms. Most of the time, this dependency is actually the
 *       e-graph to which the language is being adapted. Maybe there is a better
 *       way to specify this dependency.
 */
trait Language[T]:
  /** An implicit [[Conversion]] from terms to [[ENode]]s. */
  given termAsEnode(using EClassGenerator): Conversion[T, ENode] = this.parse
  /** An implicit [[Conversion]] from terms to [[EClass]]es. */
  given termAsEClass(using EClassGenerator): Conversion[T, EClass] = this.parseClass

  /**
   * @param term the specified term.
   * @param generator a function generating [[EClass]]es from [[ENode]]s.
   * @return the [[ENode]] corresponding to the specified term.
   */
  def parse(term: T)(using generator: EClassGenerator): ENode
  /**
   * @param term the specified term.
   * @param generator a function generating [[EClass]]es from [[ENode]]s.
   * @return the [[EClass]] corresponding to the specified term.
   */
  def parseClass(term: T)(using generator: EClassGenerator): EClass = generator(this.parse(term))
    
/** Companion object of [[Language]]. */
object Language:
  /** An adapter from the language of propel to the language of e-graphs. */
  object PropelLanguage:
    /** The set of [[Operator]]s in propel. */
    object Operators:
      def Type: Operator = op(":")
      def Lambda: Operator = op("λ")
      def TypeLambda(domain: Symbol): Operator = op(s"Λ${domain.name}")
      def Application: Operator = op("apply")
      def TypeApplication: Operator = op("applyType")
      def Constructor: Operator = op("new")
      def Match: Operator = op("match")
      def Case: Operator = op("case")
      private inline def op(name: String): Operator = Operator(s"@$name")

    def egglogSchema(term: Term): EgglogLanguageSchema =
      val operators = mutable.Map.empty[(String, Int), Option[String]]

      def add(name: String, arity: Int, preferredName: Option[String] = None): Unit =
        operators.get((name, arity)) match
          case Some(Some(existing)) if preferredName.exists(_ != existing) =>
            throw IllegalArgumentException(
              s"operator $name/$arity has conflicting egglog names $existing and ${preferredName.get}",
            )
          case Some(existing) => operators((name, arity)) = existing.orElse(preferredName)
          case None => operators((name, arity)) = preferredName

      def addSourceOperator(name: String, arity: Int): Unit =
        val preferredName = name match
          case "⊤" => Some("Top")
          case "⊥" => Some("Bot")
          case _ => None
        add(name, arity, preferredName)

      def collectType(tpe: Type): Unit = tpe match
        case Type.Function(arg, result) =>
          collectType(arg)
          collectType(result)
        case Type.Universal(_, result) => collectType(result)
        case Type.Recursive(_, result) => collectType(result)
        case Type.TypeVar(_) => ()
        case Type.Sum(sum) =>
          sum.foreach((constructor, arguments) =>
            addSourceOperator(constructor.ident.name, arguments.size)
            arguments.foreach(collectType)
          )

      def collectPattern(pattern: Pattern): Unit = pattern match
        case Pattern.Match(constructor, arguments) =>
          addSourceOperator(constructor.ident.name, arguments.size)
          arguments.foreach(collectPattern)
        case Pattern.Bind(_) => ()

      def collectTerm(current: Term): Unit = current match
        case Term.Abs(_, _, tpe, expression) =>
          add("@λ", 2, Some("Lambda"))
          collectType(tpe)
          collectTerm(expression)
        case Term.TypeAbs(domain, expression) =>
          add("@Λ", 2, Some("TypeLambda"))
          collectTerm(expression)
        case Term.App(_, expression, argument) =>
          add("@apply", 2, Some("Apply"))
          collectTerm(expression)
          collectTerm(argument)
        case Term.TypeApp(expression, tpe) =>
          add("@applyType", 2, Some("ApplyType"))
          collectTerm(expression)
          collectType(tpe)
        case Term.Data(constructor, arguments) =>
          addSourceOperator(constructor.ident.name, arguments.size)
          arguments.foreach(collectTerm)
        case Term.Var(_) => ()
        case Term.Cases(scrutinee, cases) =>
          add("@match", cases.size + 1, Some("Match"))
          add("@case", 2, Some("Case"))
          collectTerm(scrutinee)
          cases.foreach((pattern, expression) =>
            collectPattern(pattern)
            collectTerm(expression)
          )

      add("≟", 2)
      add("≛", 1)
      collectTerm(term)

      EgglogLanguageSchema(
        "PropelTerm",
        operators.toVector
          .sortBy((signature, _) => signature)
          .map((signature, preferredName) =>
            EgglogOperatorSpec(signature._1, preferredName, signature._2),
          ),
      )

  trait PropelLanguage extends Language[propel.ast.Term]:
    override def parse(term: Term)(using generator: EClassGenerator): ENode = term match
      case Abs(properties, ident, tpe, expr) =>
        ENode(PropelLanguage.Operators.Lambda, Seq(
          this.parseClass(ident),
          this.parseClass(expr)
        ))
      case TypeAbs(ident, expr) =>
        ENode(PropelLanguage.Operators.TypeLambda(ident), Seq(
          this.parseClass(expr)
        ))
      case App(properties, expr, arg) =>
        ENode(PropelLanguage.Operators.Application, Seq(
          this.parseClass(expr),
          this.parseClass(arg)
        ))
      case TypeApp(expr, tpe) =>
        ENode(PropelLanguage.Operators.TypeApplication, Seq(
          this.parseClass(expr),
          this.parseClass(tpe)
        ))
      case Data(ctor, args) =>
        ENode(Operator(ctor.ident.name), args.map(this.parseClass))
      case Var(ident) =>
        ENode(Operator(ident.name))
      case Cases(scrutinee, cases) =>
        ENode(PropelLanguage.Operators.Match,
          this.parseClass(scrutinee) +:
          cases.map((pattern, term) => generator(
            ENode(PropelLanguage.Operators.Case, Seq(
              this.parseClass(pattern),
              this.parseClass(term)
            ))
          ))
        )

    private def parseClass(id: Symbol)(using generator: EClassGenerator): EClass =
      generator(ENode(Operator(id.name)))
      
    private def parseClass(tpe: Type)(using generator: EClassGenerator): EClass =
      this.parseClass(Symbol(tpe.toString))
      
    private def parseClass(pattern: Pattern)(using generator: EClassGenerator): EClass = pattern match
      case Match(ctor, args) =>
        generator(ENode(Operator(ctor.ident.name), args.map(this.parseClass)))
      case Bind(ident) =>
        this.parseClass(Symbol(s"?${ident.name}"))
