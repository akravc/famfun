import scala.util.parsing.combinator.*
import famlang._

/*
Family A (extends B)? {
    type R (+)?= {(f: T = v)*}                  % extensible records w/ defaults
    type R (+)?= \overline{C {(f: T)*}}         % extensible ADTs
    val m : (T -> T') = (lam (x : T). body)     % functions w/ inputs
}
 */

class FamParser extends RegexParsers with PackratParsers {
  // KEYWORDS
  val kwMatch = "match\\b".r
  val kwWith = "with\\b".r
  val kwTrue = "true\\b".r
  val kwFalse = "false\\b".r
  val kwLam = "lam\\b".r
  val kwType = "type\\b".r
  val kwVal = "val\\b".r
  val kwFamily = "Family\\b".r
  val kwExtends = "extends\\b".r
  val kwN = "N\\b".r
  val kwB = "B\\b".r
  val kwSelf = "self\\b".r

  val reserved: Parser[String] = ( kwMatch | kwWith | kwTrue | kwFalse | kwLam  | kwType | kwVal | kwFamily
    | kwExtends | kwN | kwB | kwSelf )

  // NAMES
  def var_name: Parser[String] = not(reserved) ~> """[a-z]""".r ^^ { _.toString }
  def family_name: Parser[String] = not(reserved) ~> """[A-Z][a-z]*""".r ^^ { _.toString }
  def type_name: Parser[String] = not(reserved) ~> """[A-Z][a-z]*""".r ^^ { _.toString }
  def function_name: Parser[String] = not(reserved) ~> """[a-z]+""".r ^^ { _.toString }
  def field_name: Parser[String] = not(reserved) ~> """([a-z0-9])+""".r ^^ { _.toString }
  def constructor_name: Parser[String] = not(reserved) ~> """[A-Z][a-z]*""".r ^^ { _.toString }

  // FAMILY PATHS
  lazy val fampath : PackratParser[FamilyPath] =
    family_name ^^ {s => AbsoluteFamily(Family(s))}
    | kwSelf ~> "(" ~ family_name <~ ")" ^^ {case _~s => SelfFamily(Family(s))}

  // TYPES
  lazy val funtype: PackratParser[FunType] = typ ~ "->" ~ typ ^^ { case inp~_~out => FunType(inp, out)}
  lazy val recfield: PackratParser[(String, Type)] = field_name ~ ":" ~ typ ^^ {case k~_~v => k -> v}
  lazy val rectype: PackratParser[RecType] = "{"~> repsep(recfield, ",") <~"}" ^^ {case lst => RecType(lst.toMap)}
  lazy val famtype: PackratParser[FamType] = fampath ~ "." ~ type_name ^^ { case p~_~t => FamType(p, t)}
  lazy val ntype: PackratParser[Type] = kwN ^^ (_ => N)
  lazy val btype: PackratParser[Type] = kwB ^^ (_ => B)

  lazy val typ: PackratParser[Type] = funtype | rectype | famtype | ntype | btype | "(" ~> typ <~ ")"

  // ADTS
  lazy val adt_constructor: PackratParser[(String, RecType)] = constructor_name ~ rectype ^^ {case k ~ v => k -> v}
  lazy val adt: PackratParser[ADT] = repsep(adt_constructor, "|") ^^ {case lst => ADT(lst.toMap)}

  // EXPRESSIONS
  lazy val exp_bool_true: PackratParser[Bexp] = kwTrue ^^ {_ => Bexp(true)}
  lazy val exp_bool_false: PackratParser[Bexp] = kwFalse ^^ {_ => Bexp(false)}
  lazy val exp_nat: PackratParser[Nexp] = """(0|[1-9]\d*)""".r ^^ { n => Nexp(n.toInt) }
  lazy val exp_var: PackratParser[Var] = var_name ^^ {id => Var(id)}
  lazy val lam_input: PackratParser[(Var, Type)] = "(" ~> exp_var ~ ":" ~ typ <~ ")" ^^ {case v~_~t => v -> t}
  lazy val exp_lam: PackratParser[Lam] =
    kwLam ~> lam_input ~ "." ~ exp ^^ {case inp~_~body => Lam(inp._1, inp._2, body)}

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
    kwMatch ~> exp ~ kwWith ~ repsep(match_case, "|") ^^ {case e~_~lst => Match(e, lst.toMap)}

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
    kwType ~> type_name ~ marker ~ rectype ^^ {case n~m~rt => (n -> (m -> rt))}
  lazy val adtdef: PackratParser[(String, (Marker, ADT))] =
    kwType ~> type_name ~ marker ~ adt ^^ {case n~m~a => (n -> (m -> a))}

  lazy val fundef: PackratParser[(String, (FunType, Lam))] =
    kwVal ~> function_name ~ ":" ~ "(" ~ funtype ~ ")" ~ "=" ~ exp_lam ^^ {case m~_~_~t~_~_~b => m -> (t -> b)}
    | kwVal ~> function_name ~ ":" ~ funtype ~ "=" ~ exp_lam ^^ {case m~_~t~_~b => m -> (t -> b)}

  // A family can extend another family. If it does not, the parent is null.
  lazy val famdef: PackratParser[Linkage] =
    // family extends another
    kwFamily ~> family_name ~ kwExtends ~ family_name ~ "{" ~ rep(typedef) ~ rep(adtdef) ~ rep(fundef) <~ "}" ^^
      {case a~_~b~_~typs~adts~funs =>
        Linkage(SelfFamily(Family(a)), SelfFamily(Family(b)), typs.toMap, adts.toMap, funs.toMap)} |
    // family does not extend another
    kwFamily ~> family_name ~ "{" ~ rep(typedef) ~ rep(adtdef) ~ rep(fundef) <~ "}" ^^
      {case a~_~typs~adts~funs =>
        Linkage(SelfFamily(Family(a)), null, typs.toMap, adts.toMap, funs.toMap)}

}

object TestFamParser extends FamParser {
  def parse0[T](p: PackratParser[T], inp: String) = parseAll(phrase(p), inp)
  def canParse[T](p: PackratParser[T], inp: String) = parse0(p, inp).successful
  def parseSuccess[T](p: PackratParser[T], inp: String) = parse0(p, inp).get
}
