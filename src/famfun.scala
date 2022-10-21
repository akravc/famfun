import scala.annotation.tailrec

object famfun {
  /* ======================== FAMILIES & PATHS ======================== */

  // Path a := sp | a.A
  sealed trait Path 
  case class Sp(sp: SelfPath) extends Path // sp 
  case class AbsoluteFamily(pref: Path, fam: String) extends Path // a.A

  // RelPath sp := prog | self(sp.A)
  sealed trait SelfPath
  case object Prog extends SelfPath // <prog>
  case class SelfFamily(pref: SelfPath, fam: String) extends SelfPath // self(sp.A)
  
  // returns the last family name in the path (suffix)
  def pathName(p: Path): String = p match {
    case Sp(Prog) => throw new Exception("Should not try to get path name of <>")
    case Sp(SelfFamily(_, f)) => f
    case AbsoluteFamily(_, f) => f
  }

  // Transforms all self paths into absolute paths (except Prog)
  def concretizePath(p: Path): Path = p match {
    case Sp(Prog) => p
    case Sp(SelfFamily(pref, fam)) => AbsoluteFamily(concretizePath(Sp(pref)), fam)
    case AbsoluteFamily(pref, fam) => AbsoluteFamily(concretizePath(pref), fam)
  }

  // Transforms all absolute paths into self paths
  def relativizePath(p: Path): SelfPath = p match {
    case Sp(sp) => sp
    case AbsoluteFamily(pref, fam) => SelfFamily(relativizePath(pref), fam)
  }

  // transform path to list of family names
  @tailrec
  def pathToFamList(p: Path, acc: List[String] = Nil): List[String] = p match {
    case Sp(sp) => selfPathToFamList(sp, acc)
    case AbsoluteFamily(pref, fam) => pathToFamList(pref, fam :: acc)
  }
  
  // transform self path to list of family names
  @tailrec
  def selfPathToFamList(sp: SelfPath, acc: List[String] = Nil): List[String] = sp match {
    case Prog => acc
    case SelfFamily(pref, fam) => selfPathToFamList(pref, fam :: acc)
  }

  /* ======================== TYPES ======================== */
  
  sealed trait Type
  case object NType extends Type // N
  case object BType extends Type // B
  case object StringType extends Type // String
  case class FamType(var path: Option[Path], name: String) extends Type // a.R
  case class FunType(input: Type, output: Type) extends Type // T -> T'
  case class RecType(fields: Map[String, Type]) extends Type // {(f: T)*}

  // Generic traversal to change the paths
  def recType(f: Path => Path)(t: Type): Type = t match {
    case FamType(path, name) => FamType(path.map(f), name)
    case FunType(input, output) => FunType(recType(f)(input), recType(f)(output))
    case RecType(fields) => RecType(fields.view.mapValues(recType(f)).toMap)
    case _ => t
  }

  // Transforms self paths in types into absolute paths (except Prog)
  def concretizeType(t: Type): Type = recType(concretizePath)(t)

  // Replaces all self paths `sp` in `t` with the prefix path of `p` (as a self path) of the same length as `sp`
  def subSelfInTypeAccordingTo(p: Path)(t: Type): Type = {
    val pFamList: List[String] = pathToFamList(p)
    recType(path => path match {
      case Sp(sp) => Sp(
        pFamList.take(selfPathToFamList(sp).length).foldLeft(Prog)(SelfFamily.apply)
      )
      case other => other
    })(t)
  }

  /* ======================== EXPRESSIONS  ======================== */

  sealed trait Expression {
    var exprType: Option[Type] = None
  }
  case class Var(id: String) extends Expression // x
  case class Lam(v: Var, t: Type, body: Expression) extends Expression // lam (x: T). body
  case class FamFun(var path: Option[Path], name: String) extends Expression // a.m
  case class FamCases(var path: Option[Path], name: String) extends Expression // a.r
  case class App(e1: Expression, e2: Expression) extends Expression // e g
  case class Rec(fields: Map[String, Expression]) extends Expression // {(f = e)*}
  case class Proj(e: Expression, name: String) extends Expression // e.f
  case class Inst(t: FamType, rec: Rec) extends Expression // a.R({(f = e)*})
  case class InstADT(t: FamType, cname: String, rec: Rec) extends Expression // a.R(C {(f = e)*})
  //TODO: FIX MATCH STATEMENT
  case class Match(e: Expression, g: Expression) extends Expression // match e with g
  case class IfThenElse(condExpr: Expression, ifExpr: Expression, elseExpr: Expression) extends Expression

  // arithmetic expressions; how to parse?
  sealed trait AExp extends Expression 
  case class NConst(n: Int) extends AExp
  case class ABinExp(a1: Expression, op: AOp, a2: Expression) extends AExp
  sealed trait AOp
  case object AAdd extends AOp
  case object ASub extends AOp
  case object AMul extends AOp
  case object ADiv extends AOp
  def showAOp(op: AOp): String = op match {
    case AAdd => "+"
    case ASub => "-"
    case AMul => "*"
    case ADiv => "/"
  }

  // Boolean expressions
  sealed trait BExp extends Expression
  case class BConst(b: Boolean) extends BExp
  case class BBinExp(e1: Expression, op: BOp, e2: Expression) extends BExp
  case class BNot(e: Expression) extends BExp
  sealed trait BOp
  case object BAnd extends BOp
  case object BOr extends BOp
  case object BEq extends BOp
  case object BNeq extends BOp
  case object BLt extends BOp
  case object BGt extends BOp
  case object BLeq extends BOp
  case object BGeq extends BOp
  def showBOp(op: BOp): String = op match {
    case BAnd => "&&"
    case BOr => "||"
    case BEq => "=="
    case BNeq => "!="
    case BLt => "<"
    case BGt => ">"
    case BLeq => "<="
    case BGeq => ">="
  }

  // String expressions
  sealed trait StringExp extends Expression
  case class StringLiteral(literal: String) extends StringExp
  case class StringInterpolated(interpolated: List[StringInterpolationComponent]) extends StringExp
  sealed trait StringInterpolationComponent
  case class StringComponent(str: String) extends StringInterpolationComponent
  case class InterpolatedComponent(exp: Expression) extends StringInterpolationComponent

  /* ======================== DEFINITIONS ======================== */

  sealed trait Marker // either += or =
  case object PlusEq extends Marker // type extension marker
  case object Eq extends Marker // type definition marker

  // Things that could be defined or extended / further bound
  case class DefnBody[B](defn: Option[B], extendsFrom: Option[Path], furtherBindsFrom: Option[Path])

  // types
  case class TypeDefn(name: String, marker: Marker, typeBody: DefnBody[RecType])
  
  // defaults
  case class DefaultDefn(name: String, marker: Marker, defaultBody: DefnBody[Rec])

  // ADTs
  case class AdtDefn(name: String, marker: Marker, adtBody: DefnBody[Map[String, RecType]])

  // Functions
  case class FunDefn(name: String, t: FunType, funBody: DefnBody[Expression])

  // Cases
  case class CasesDefn(name: String, matchType: FamType, t: Type, marker: Marker, casesBody: DefnBody[Expression])

  /* ======================== LINKAGES ======================== */

  case class Linkage(path: Path,
                     self: SelfPath, // self
                     sup: Option[Path], // super
                     types: Map[String, TypeDefn],
                     defaults: Map[String, DefaultDefn],
                     adts: Map[String, AdtDefn],
                     funs: Map[String, FunDefn],
                     depot: Map[String, CasesDefn],
                     nested: Map[String, Linkage]
                    )

  /*====================================== VALUES ======================================*/

  // Values
  def is_value(e: Expression): Boolean = e match {
    case Lam(v, t, body) => true
    case Inst(t, rec) => rec.fields.forall { case (_, exp) => is_value(exp) }
    case InstADT(t, cname, rec) => rec.fields.forall { case (_, exp) => is_value(exp) }
    case Rec(fields) => fields.forall { case (_, exp) => is_value(exp) }
    case NConst(_) => true
    case ABinExp(a1, _, a2) => is_value(a1) && is_value(a2)
    case BConst(_) => true
    case BBinExp(e1, _, e2) => is_value(e1) && is_value(e2)
    case BNot(inner) => is_value(inner)
    case StringLiteral(_) => true
    case StringInterpolated(components) => components.forall {
      case StringComponent(_) => true
      case InterpolatedComponent(exp) => is_value(exp)
    }
    case IfThenElse(condExpr, ifExpr, elseExpr) => is_value(condExpr) && is_value(ifExpr) && is_value(elseExpr)
    case _ => false
  }
}
