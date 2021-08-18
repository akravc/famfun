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


class FamParser extends RegexParsers {

  def fampath : Parser[FamilyPath] =
    family_name ^^ {s => AbsoluteFamily(Family(s))}
    | "self(" ~ family_name ~ ")" ^^ {case _~s~_ => SelfFamily(Family(s))}

  def typ : Parser[Type] =
    "N" ^^ (_ => N)
    | "B" ^^ (_ => B)
    | typ ~ "->" ~ typ ^^ { case inp~_~out => FunType(inp, out)}
    | fampath ~ "." ~ type_name ^^ { case p~_~t => FamType(p, t)}


  //def recfield: Parser[(String, Type)] = field_name ~ ":" ~ typ ^^ (case k~":"~v => k -> v)
  //def rec : Parser[RecType] = "{"~> repsep(recfield, ",") <~"}" ^^ (case ??? )


  // NAMES
  def var_name: Parser[String] = """[a-z]""".r ^^ { _.toString }
  def family_name: Parser[String] = """[A-Z][a-z]*""".r ^^ { _.toString }
  def type_name: Parser[String] = """[A-Z][a-z]*""".r ^^ { _.toString }
  def function_name: Parser[String] = """[a-z]+""".r ^^ { _.toString }
  def field_name: Parser[String] = """([a-z0-9])+""".r ^^ { _.toString }
  def constructor_name: Parser[String] = """[A-Z][a-z]*""".r ^^ { _.toString }


}

object TestFamParser extends FamParser {
  def main(args: Array[String]) = {
    parse(typ, "N -> B") match {
      case Success(matched,tail) => println(matched)
      case Failure(msg,tail) => println(s"FAILURE: $msg"); println(tail.source)
      case Error(msg,_) => println(s"ERROR: $msg")
    }
  }
}
