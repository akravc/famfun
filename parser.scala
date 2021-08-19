import scala.util.Success
import scala.util.parsing.combinator.*
import famlang._


/*
Family A (extends B)? {
    type R (+)?= {(f: T = v)*}                  % extensible records w/ defaults
    type R (+)?= \overline{C {(f: T)*}}         % extensible ADTs
    val m : (T -> T') = (lam (x : T). body)     % functions w/ inputs
}

FamilyDef has a family, a super, type defs, ADT defs, fundefs
 */


sealed class Definition
case class FunDef(name: String, t: FunType, df: Lam)
case class TypeDef(name: String, t: RecType)
case class ADTDef(name: String, adt: ADT)


class FamParser extends RegexParsers with PackratParsers {

  // optional punctuation
  def oparen: Parser[String] = """\(?""".r ^^ { _.toString }
  def cparen: Parser[String] = """\)?""".r ^^ { _.toString }
  def comma: Parser[String] = """,?""".r ^^ { _.toString }

  // NAMES
  def var_name: Parser[String] = """[a-z]""".r ^^ { _.toString }
  def family_name: Parser[String] = """[A-Z][a-z]*""".r ^^ { _.toString }
  def type_name: Parser[String] = """[A-Z][a-z]*""".r ^^ { _.toString }
  def function_name: Parser[String] = """[a-z]+""".r ^^ { _.toString }
  def field_name: Parser[String] = """([a-z0-9])+""".r ^^ { _.toString }
  def constructor_name: Parser[String] = """[A-Z][a-z]*""".r ^^ { _.toString }

  // FAMILY PATHS
  def fampath : Parser[FamilyPath] =
    family_name ^^ {s => AbsoluteFamily(Family(s))}
    | "self(" ~> family_name <~ ")" ^^ {s => SelfFamily(Family(s))}

  // TYPES
  def funtype: Parser[FunType] = "(" ~> typ ~ "->" ~ typ <~ ")" ^^ { case inp~_~out => FunType(inp, out)}
  def recfield: Parser[(String, Type)] = field_name ~ ":" ~ typ ^^ {case k~":"~v => k -> v}
  def rectype: Parser[RecType] = "{"~> repsep(recfield, ",") <~"}" ^^ {case lst => RecType(lst.toMap)}
  def famtype: Parser[FamType] = fampath ~ "." ~ type_name ^^ { case p~_~t => FamType(p, t)}
  def ntype: Parser[Type] = "N" ^^ (_ => N)
  def btype: Parser[Type] = "B" ^^ (_ => B)

  def typ: Parser[Type] = funtype | rectype | famtype | ntype | btype

  // ADTS
  def adt_constructor: Parser[(String, RecType)] = constructor_name ~ rectype ^^ {case k ~ v => k -> v}
  def adt_def: Parser[ADT] = repsep(adt_constructor, "|") ^^ {case lst => ADT(lst.toMap)}

  // EXPRESSIONS
  def exp_bool_true: Parser[Bexp] = "true" ^^ {_ => Bexp(true)}
  def exp_bool_false: Parser[Bexp] = "false" ^^ {_ => Bexp(false)}
  def exp_nat: Parser[Nexp] = """(0|[1-9]\d*)""".r ^^ { n => Nexp(n.toInt) }
  def exp_var: Parser[Var] = var_name ^^ {id => Var(id)}
  def lam_input: Parser[(Var, Type)] = "(" ~> exp_var ~ ":" ~ typ <~ ")" ^^ {case v~":"~t => v -> t}
  def exp_lam: Parser[Lam] =
    "lam" ~> lam_input ~ "." ~ exp ^^ {case inp~_~body => Lam(inp._1, inp._2, body)}

  def exp_famfun: Parser[FamFun] = fampath ~ "." ~ function_name ^^ {case p~"."~n => FamFun(p, n)}
  def exp_app: Parser[App] = exp ~ exp ^^ {case e~g => App(e, g)}
  def exp_proj: Parser[Proj] = exp ~ field_name ^^ {case e~n => Proj(e, n)}
  def field_val: Parser[(String, Expression)] = field_name ~ "=" ~ exp ^^ {case k~":"~v => k -> v}
  def exp_rec: Parser[Rec] = "{"~> repsep(field_val, ",") <~"}" ^^ {case lst => Rec(lst.toMap)}
  def exp_inst: Parser[Inst] = famtype ~ "(" ~ exp_rec <~ ")" ^^ {case t~"("~r => Inst(t, r)}
  def exp_inst_adt: Parser[InstADT] =
    famtype ~ "(" ~ constructor_name ~ exp_rec <~ ")" ^^ {case t~"("~c~r => InstADT(t, c, r)}

  def match_case: Parser[(String, Lam)] = constructor_name ~ "=>" ~ exp_lam ^^ {case k~"=>"~v => k -> v}
  def exp_match: Parser[Match] =
    "match" ~> exp ~ "with" ~ repsep(match_case, "|") <~ "." ^^ {case e~_~lst => Match(e, lst.toMap)}

  def exp: Parser[Expression] = exp_match | exp_inst_adt | exp_inst | exp_rec | exp_lam | exp_app
    | exp_famfun | exp_proj | exp_bool_true | exp_bool_false | exp_nat | exp_var
}

object TestFamParser extends FamParser {
  def main(args: Array[String]) = {
    parse(exp, "lam (x : B). x") match {
      case Success(matched,tail) => println(matched)
      case Failure(msg,tail) => println(s"FAILURE: $msg")
      case Error(msg,_) => println(s"ERROR: $msg")
    }
  }
}
