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
  case class Inst(t: FamType, rec: Rec) extends Expression
  case class InstADT(t: FamType, cname: String, rec: Rec) extends Expression
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

    case App(e1, e2) =>
      (typ(e1, G, K), typ(e2, G, K)) match {
        case (Some(FunType(itype, otype)), Some(expt)) if (itype == expt) =>  Some(otype)
        case _ => None
    }

    case Rec(fields) =>
      val mp = fields.map{case (fname, fex) =>  (fname, typ(fex, G, K))};
      if mp.exists{case (_,t) => t == None} then { None }  // checks for fields with None types
      else { Some(RecType(mp.map{case (f, Some(t)) => (f, t)})) }

    case Proj(e, f) =>
      typ(e, G, K) match {
        case Some(RecType(mp)) => mp.get(f)
        case _ => None
      }

    case FamFun(path, name) =>
      K.get(path) match {
        case Some(lkg) =>
          lkg.funs.get(name) match {
            case Some(funtype, body) if wf(funtype, K) => Some(funtype)
            case _ => None
          }
        case _ => None
      }

    case Inst(ftype, rec) =>
      K.get(ftype.path) match {
        case Some(lkg) =>
          lkg.types.get(ftype.name) match {
            case Some(_, rt) => // assuming marker is = at this point, complete linkages
              if rt.fields.map{case(f, t) => (f, Some(t))} == rec.fields.map{case(f, e) => (f, typ(e, G, K))}
              then Some(ftype) else None
            case _ => None
          }
        case _ => None
      }

    case InstADT(ftype, cname, rec) =>
      K.get(ftype.path) match {
        case Some(lkg) =>
          lkg.adts.get(ftype.name) match {
            case Some(_, adt) => adt.cs.get(cname) match {
              case Some(RecType(fields)) =>
                if fields.map{case(f, t) => (f, Some(t))} == rec.fields.map{case(f, e) => (f, typ(e, G, K))}
                then Some(ftype) else None
              case _ => None
            }
            case _ => None
          }
        case _ => None
      }
      
    case Match(e, cases) =>
      typ(e, G, K) match {
        case Some(FamType(path, name)) =>
          K.get(path) match {
            case Some(lkg) =>
              lkg.adts.get(name) match {
                case Some(_, adt) =>
                  val funtypes = cases.map{case (c, lam) => (c, typ(lam, G, K))};
                  if funtypes.exists{case (_,t) => t != Some(FunType(_,_))} then { None } // check for ill-formed functions g_i
                  else {
                    // TODO: finish checking that each g_i has a proper input and output type that matches ADT definition
                    None
                  }
                case _ => None
              }
            case _ => None
          }
        case _ => None
      }
    case _ => None
  }
  
  } // eof