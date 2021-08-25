import scala.util.Success
import scala.util.parsing.combinator.*
import scala.util.parsing.combinator.lexical.StdLexical
import famlang._

/*
Family A (extends B)? {
    type R (+)?= {(f: T = v)*}                  % extensible records w/ defaults
    type R (+)?= \overline{C {(f: T)*}}         % extensible ADTs
    val m : (T -> T') = (lam (x : T). body)     % functions w/ inputs
}
 */

class FamParser extends StdLexical with RegexParsers with PackratParsers {

  // NAMES
  def var_name: Parser[String] = """[a-z]""".r ^^ { _.toString }
  def family_name: Parser[String] = """[A-Z][a-z]*""".r ^^ { _.toString }
  def type_name: Parser[String] = """[A-Z][a-z]*""".r ^^ { _.toString }
  def function_name: Parser[String] = """[a-z]+""".r ^^ { _.toString }
  def field_name: Parser[String] = """([a-z0-9])+""".r ^^ { _.toString }
  def constructor_name: Parser[String] = """[A-Z][a-z]*""".r ^^ { _.toString }

  // FAMILY PATHS
  lazy val fampath : PackratParser[FamilyPath] =
    family_name ^^ {s => AbsoluteFamily(Family(s))}
    | "self(" ~> family_name <~ ")" ^^ {s => SelfFamily(Family(s))}

  // TYPES
  lazy val funtype: PackratParser[FunType] = typ ~ "->" ~ typ ^^ { case inp~_~out => FunType(inp, out)}
  lazy val recfield: PackratParser[(String, Type)] = field_name ~ ":" ~ typ ^^ {case k~_~v => k -> v}
  lazy val rectype: PackratParser[RecType] = "{"~> repsep(recfield, ",") <~"}" ^^ {case lst => RecType(lst.toMap)}
  lazy val famtype: PackratParser[FamType] = fampath ~ "." ~ type_name ^^ { case p~_~t => FamType(p, t)}
  lazy val ntype: PackratParser[Type] = "N" ^^ (_ => N)
  lazy val btype: PackratParser[Type] = "B" ^^ (_ => B)

  lazy val typ: PackratParser[Type] = funtype | rectype | famtype | ntype | btype | "(" ~> typ <~ ")"

  // ADTS
  lazy val adt_constructor: PackratParser[(String, RecType)] = constructor_name ~ rectype ^^ {case k ~ v => k -> v}
  lazy val adt: PackratParser[ADT] = repsep(adt_constructor, "|") ^^ {case lst => ADT(lst.toMap)}

  // EXPRESSIONS
  lazy val exp_bool_true: PackratParser[Bexp] = "true" ^^ {_ => Bexp(true)}
  lazy val exp_bool_false: PackratParser[Bexp] = "false" ^^ {_ => Bexp(false)}
  lazy val exp_nat: PackratParser[Nexp] = """(0|[1-9]\d*)""".r ^^ { n => Nexp(n.toInt) }
  lazy val exp_var: PackratParser[Var] = var_name ^^ {id => Var(id)}
  lazy val lam_input: PackratParser[(Var, Type)] = "(" ~> exp_var ~ ":" ~ typ <~ ")" ^^ {case v~_~t => v -> t}
  lazy val exp_lam: PackratParser[Lam] =
    "lam" ~> lam_input ~ "." ~ exp ^^ {case inp~_~body => Lam(inp._1, inp._2, body)}

  lazy val exp_famfun: PackratParser[FamFun] = fampath ~ "." ~ function_name ^^ {case p~_~n => FamFun(p, n)}
  lazy val exp_app: PackratParser[App] = exp ~ exp ^^ {case e~g => App(e, g)}
  lazy val exp_proj: PackratParser[Proj] = exp ~ "." ~ field_name ^^ {case e~_~n => Proj(e, n)}
  lazy val field_val: PackratParser[(String, Expression)] = field_name ~ "=" ~ exp ^^ {case k~_~v => k -> v}
  lazy val exp_rec: PackratParser[Rec] = "{"~> repsep(field_val, ",") <~"}" ^^ {case lst => Rec(lst.toMap)}
  lazy val exp_inst: PackratParser[Inst] = famtype ~ "(" ~ exp_rec <~ ")" ^^ {case t~_~r => Inst(t, r)}
  lazy val exp_inst_adt: PackratParser[InstADT] =
    famtype ~ "(" ~ constructor_name ~ exp_rec <~ ")" ^^ {case t~_~c~r => InstADT(t, c, r)}

  lazy val match_case: PackratParser[(String, Lam)] = constructor_name ~ "=>" ~ exp_lam ^^ {case k~_~v => k -> v}
  lazy val exp_match: PackratParser[Match] =
    "match" ~> exp ~ "with" ~ repsep(match_case, "|") ^^ {case e~_~lst => Match(e, lst.toMap)}

  lazy val exp: PackratParser[Expression] =
  exp_match | exp_app | exp_proj | exp_famfun
  | exp_lam | exp_bool_true | exp_bool_false | exp_nat
  | exp_inst_adt | exp_inst | exp_rec
  | exp_var
  | "(" ~> exp <~ ")"

  // MARKERS
  lazy val marker: PackratParser[Marker] =
    "=" ^^ {_ => Eq} | "+=" ^^ {_ => PlusEq}

  // DEFINITIONS
  lazy val typedef: PackratParser[(String, (Marker, RecType))] =
    "type" ~> type_name ~ marker ~ rectype ^^ {case n~m~rt => (n -> (m -> rt))}
  lazy val adtdef: PackratParser[(String, (Marker, ADT))] =
    "type" ~> type_name ~ marker ~ adt ^^ {case n~m~a => (n -> (m -> a))}
  lazy val fundef: PackratParser[(String, (FunType, Lam))] =
    "val" ~> function_name ~ ":" ~ funtype ~ "=" ~ exp_lam ^^ {case m~_~t~_~b => m -> (t -> b)}

  lazy val famdef: PackratParser[Linkage] =
    "Family" ~> family_name ~ "extends" ~ family_name ~ "{" ~ rep(typedef) ~ rep(adtdef) ~ rep(fundef) <~ "}" ^^
    {case a~_~b~_~typs~adts~funs =>
      Linkage(SelfFamily(Family(a)), SelfFamily(Family(b)), typs.toMap, adts.toMap, funs.toMap)}

}

object TestFamParser extends FamParser {
  def main(args: Array[String]) = {
    parse(phrase(exp), "lam (x : B). x") match {
      case Success(matched,tail) => println(matched)
      case Failure(msg,tail) => println(s"FAILURE: $msg")
      case Error(msg,_) => println(s"ERROR: $msg")
    }
  }

  def parse0[T](p: PackratParser[T], inp: String) = parseAll(phrase(p), inp)
  def canParse[T](p: PackratParser[T], inp: String) = parse0(p, inp).successful
  def parseSuccess[T](p: PackratParser[T], inp: String) = parse0(p, inp).get
}
