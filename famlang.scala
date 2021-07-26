object famlang {
  // Families & Paths
  case class Family(name: String) 
  sealed class FamilyPath
  case class AbsoluteFamily(fam: Family) extends FamilyPath 
  case class SelfFamily(fam: Family) extends FamilyPath 

  // Types
  sealed class Type
  case object N extends Type
  case object B extends Type
  case class FamType(path: FamilyPath, name: String) extends Type
  case class FunType(input: Type, output: Type) extends Type
  case class RecType(fields: Map[String,Type]) extends Type
  
  //ADTs
  case class ADT(cs: Map[String, RecType])
  
  // Expressions
  sealed class Expression
  case class Var(id: String) extends Expression
  case class Lam(v: Var, t: Type, body: Expression) extends Expression
  case class FamFun(path: FamilyPath, name: String) extends Expression
  case class App(e1: Expression, e2: Expression) extends Expression
  case class Rec(fields: Map[String, Expression]) extends Expression
  case class Proj(e: Expression, name: String) extends Expression
  case class Inst(t: FamType, fields: Rec) extends Expression
  case class InstADT(t: FamType, cname: String, fields: Rec) extends Expression
  case class Match(e: Expression, cases: Map[String, Lam]) extends Expression
  case class Nexp(n: Int) extends Expression
  case class Bexp(b: Boolean) extends Expression
  
  // Linkages
    /* [ SELF = self(A)                                                               ]    
        | SUPER = self(B)                                                           | 
        | TYPES = \overline{ R (+)?= {(f: T)*} }                            | % types   
        | ADTS = \overline{ R (+)?= \overline{C {(f: T)*}} }           | % ADTs
        [ FUNS = \overline{ m : (T -> T') = (lam (x : T). body) }   ] % function defs  
    */
  sealed class Marker // either = or +=
  case object PlusEq extends Marker // type being extended
  case object Eq extends Marker // type definition
  case class Linkage(self: SelfFamily, sup: SelfFamily, types: Map[String, (Marker, RecType)], 
                                    adts: Map[String, (Marker, ADT)], funs: Map[String, (FunType, Lam)])
  
  
  // Values
  def is_value(e: Expression): Boolean = e match {
      case Lam(v, t, body) => true
      case Inst(t, rec) => rec.fields.filter{case (_, exp) => !is_value(exp)}.isEmpty
      case InstADT(t, cname, rec) => rec.fields.filter{case (_, exp) => !is_value(exp)}.isEmpty
      case Rec(fields) => fields.filter{case (_, exp) => !is_value(exp)}.isEmpty
      case Nexp(n) => true
      case Bexp(b) => true
      case _ => false
    }

  // Well-Formedness Rules
  // K is the linkage context
  def wf(t: Type, K: Map[FamilyPath, Linkage]): Boolean = t match {
    case N => true
    case B => true
    case FamType(path, name) => 
        K.get(path) match { 
        case None => false
        case Some(lkg) => lkg.types.contains(name)
        }
    case FunType(t1,t2) => wf(t1, K) && wf(t2, K)
    case RecType(m) => m.filter{case (_,t) => !wf(t, K)}.isEmpty
    case _ => false
  }

// Typing Rules
// G is the typing context, K is the linkage context

/**  FAILED TRY:
def typ(exp: Expression, t: Type, G: Map[String, Type], K: Map[FamilyPath, Linkage]): Boolean = (exp, t) match {
    case (Nexp(n), N) => true
    case (Bexp(b), B) => true
    case (Var(x), t) => G.get(x) == Some(t)
    case (Lam(Var(x), xtype, body), FunType(it, ot)) => (xtype == it) && wf(it, K) && typ(body, ot, (G + (x -> it)), K)
    case (App(e1, e2), t) => typ(e1, FunType(it, ot), 
    FAIL: NEED TO "compute" a type here....
    */
    
  def typ(exp: Expression, G: Map[String, Type], K: Map[FamilyPath, Linkage]): Option[Type] = exp match {
    case Nexp(n) => Some(N)
    case Bexp(b) => Some(B)
    case Var(x) => G.get(x)
    case Lam(Var(x), xtype, body) => {
      if wf(xtype, K) then {
        typ(body, G + (x -> xtype), K) match {
          case Some(otype) => Some(FunType(xtype, otype))
          case _ => None
        }
      } else None
    }
    case App(e1, e2) => (typ(e1, G, K), typ(e2, G, K)) match {
        case (Some(FunType(itype, otype)), Some(expt)) if (itype == expt) =>  Some(otype)
        case _ => None
    }
    case Rec(fields) => None // need to return a new map here of fields to types
    case _ => None
  }














    

    
    
  
}
