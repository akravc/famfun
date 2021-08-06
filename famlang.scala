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

  case class RecType(fields: Map[String, Type]) extends Type

  // ADTs
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
  /*

  [ SELF = self(A)                                                            ]
  | SUPER = self(B)                                                           |
  | TYPES = \overline{ R (+)?= {(f: T)*} }                                    | % types
  | ADTS = \overline{ R (+)?= \overline{C {(f: T)*}} }                        | % ADTs
  [ FUNS = \overline{ m : (T -> T') = (lam (x : T). body) }                   ] % function defs

  */

  sealed class Marker // either += or =

  case object PlusEq extends Marker // type extension

  case object Eq extends Marker // type definition

  case class Linkage(self: SelfFamily, sup: SelfFamily, types: Map[String, (Marker, RecType)],
                     adts: Map[String, (Marker, ADT)], funs: Map[String, (FunType, Lam)])


  // Values
  def is_value(e: Expression): Boolean = e match {
    case Lam(v, t, body) => true
    case Inst(t, rec) => rec.fields.filter { case (_, exp) => !is_value(exp) }.isEmpty
    case InstADT(t, cname, rec) => rec.fields.filter { case (_, exp) => !is_value(exp) }.isEmpty
    case Rec(fields) => fields.filter { case (_, exp) => !is_value(exp) }.isEmpty
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
        case Some(lkg) => lkg.types.contains(name)
        case None => false
      }
    case FunType(t1, t2) => wf(t1, K) && wf(t2, K)
    case RecType(m) => m.filter { case (_, t) => !wf(t, K) }.isEmpty
    case _ => false
  }


  // Type Inference
  // G is the typing context, K is the linkage context
  def typInf(exp: Expression, G: Map[String, Type], K: Map[FamilyPath, Linkage]): Option[Type] = exp match {

    // _________________ T_Num
    //  G |- n : N
    case Nexp(n) => Some(N)

    // _________________ T_Bool
    //  G |- b : B
    case Bexp(b) => Some(B)

    //  x: T \in G
    // ______________ T_Var
    //  G |- x : T
    case Var(x) => G.get(x)

    //  WF(T)
    //  x : T, G |- body : T'
    // _____________________________________ T_Lam
    //  G |- lam (x : T). body : T -> T'
    case Lam(Var(x), xtype, body) =>
      if wf(xtype, K) then {
        typInf(body, G + (x -> xtype), K).map { otype => FunType(xtype, otype) }
      } else None

    //  G |- e : T
    //  G |- g : T -> T'
    //___________________ T_App
    //  G |- g e : T'
    case App(e1, e2) =>
      (typInf(e1, G, K), typInf(e2, G, K)) match { // type e1 and e2
        case (Some(FunType(itype, otype)), Some(expt)) if (itype == expt) => Some(otype)
        case _ => None
      }

    //  forall i, G |- e_i : T_i
    //_____________________________________ T_Rec
    //  G |- {(f_i = e_i)*} : {(f_i: T_i)*}
    case Rec(fields) =>
      val ftypes = fields.map { case (fname, fex) => (fname, typInf(fex, G, K)) }; // type all expressions
      if ftypes.exists { case (_, t) => t == None } then None // check for fields with None types
      else {
        Some(RecType(ftypes.map { case (f, Some(t)) => (f, t) }))
      } // extract types from options

    //  G |- e : {(f': T')*}
    //  (f: T) in \overline{f': T'}
    //_______________________________ T_RecField
    //  G |- e.f : T
    case Proj(e, f) =>
      typInf(e, G, K).flatMap { case RecType(ftypes) => ftypes.get(f) case _ => None }

    //  WF(T -> T')
    //  m : (T -> T') = (lam (x : T). body) in [[a]]
    //_______________________________________________ T_FamFun
    //  G |- a.m : T -> T'
    case FamFun(path, name) =>
      K.get(path).flatMap {
        lkg =>
          lkg.funs.get(name).map {
            // funtype should be well-formed, check with assertion
            (funtype, body) => assert(wf(funtype, K)); funtype
          }
      }

    //  R = {(f_i: T_i)*} in [[a]]
    //  forall i, G |- e_i : T_i
    //______________________________________ T_Constructor
    //  G |- a.R({(f_i = e_i)*}) : a.R
    case Inst(ftype, rec) =>
      K.get(ftype.path).flatMap {
        lkg =>
          lkg.types.get(ftype.name).flatMap {
            (marker, rt) =>
              assert(marker == Eq); // should be Eq in a complete linkage, check with assertion
              assert(wf(rt, K)); // should be well-formed in linkage, check
              if rec.fields.filter { (f, e) => // typeCheck all fields wrt linkage definition
                rt.fields.get(f) match {
                  case Some(typedef) => !typCheck(e, typedef, G, K)
                  case _ => false
                }
              }.isEmpty then Some(ftype) else None
          }
      }

    //  R = \overline{C' {(f': T')*}} in [[a]]
    //  C {(f_i: T_i)*} in \overline{C' {(f': T')*}}
    //  forall i, G |- e_i : T_i
    //_________________________________________________ T_ADT
    //  G |- a.R(C {(f_i = e_i)*}) : a.R
    case InstADT(ftype, cname, rec) =>
      K.get(ftype.path).flatMap {
        lkg =>
          lkg.adts.get(ftype.name).flatMap {
            (marker, adt) =>
              assert(marker == Eq); // should be Eq in a complete linkage, check with assertion
              adt.cs.get(cname).flatMap {
                case RecType(fields) =>
                  if fields.map { case (f, t) => (f, Some(t)) } == rec.fields.map { case (f, e) => (f, typInf(e, G, K)) }
                  then Some(ftype) else None
              }
          }
      }

    //  G |- e : a.R
    //  R = \overline{C_i {(f_i: T_i)*}} in [[a]]
    //  forall i, G |- g_i : {(f_i: T_i)*} -> T'
    //____________________________________________ T_Match
    //  G |- match e with (C_i => g_i)* : T'
    case Match(e, cases) =>
      typInf(e, G, K).flatMap {
        case FamType(path, name) =>
          K.get(path).flatMap {
            lkg =>
              lkg.adts.get(name).flatMap {
                (marker, adt) =>
                  assert(marker == Eq); // should be Eq in a complete linkage, check with assertion
                  val funtypes = cases.map { case (c, lam) => (c, typInf(lam, G, K)) }; // infer types of g_i's
                  if funtypes.exists {
                    case (c, Some (FunType(infrt, otype))) =>
                      adt.cs.get(c) match {
                        // all output types are not the same OR inferred input type doesn't match definition
                        case Some(defrt) => funtypes.head._2 != Some(otype) || infrt != defrt
                        case _ => true
                      }
                    case _ => true // if not, or if something doesn't have a function type
                  } then None else funtypes.head._2 // first function output type since all are the same
              }
          }
      }

    // All other cases
    case _ => None
  } // end fun


  // Type Checking
  // G is the typing context, K is the linkage context
  // t is the expected type
  def typCheck(exp: Expression, t: Type, G: Map[String, Type], K: Map[FamilyPath, Linkage]): Boolean =
    val inftype = typInf(exp, G, K);
    if inftype == Some(t) then true else {
      (inftype, t) match {
        //  forall i, (f_i: T_i) \in (f_j: T_j)*
        //______________________________________ T_SubRec
        //  {(f_j: T_j)*} <: {(f_i: T_i)*}
        case (Some(RecType(fdsinf)), RecType(fdst)) =>
          !fdst.exists{case (f, ft) =>
            fdsinf.get(f) match {
              case Some(v) => (v == ft)
              case None => false
            }
          }

        //  R = T in [[a]]
        //__________________ T_Expansion
        //  a.R <: T
        case (Some(FamType(path, name)), t) =>
          K.get{path} match {
            case Some(lkg) =>
              lkg.types.get(name) match {
                case Some((marker, typedef)) =>
                  assert(marker == Eq); // should be Eq, check
                  assert(wf(typedef, K)); // should be well formed in linkage, check
                  (typedef == t)
                case None => false
              }
            case None => false
          }

        case _ => false
      }
    }







} // eof