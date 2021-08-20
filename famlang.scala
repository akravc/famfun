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


  /*====================================== VALUES ======================================*/

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

  /*====================================== TYPE WELL-FORMEDNESS ======================================*/

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

  /*====================================== TYPING ======================================*/


  // Type Inference
  // G is the typing context, K is the linkage context
  // Infer the type of expression exp
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
      typInf(e1, G, K) match { // type e1
        case Some(FunType(itype, otype)) if typCheck(e2, itype, G, K) => Some(otype)
        case _ => None
      }

    //  forall i, G |- e_i : T_i
    //_____________________________________ T_Rec
    //  G |- {(f_i = e_i)*} : {(f_i: T_i)*}
    case Rec(fields) =>
      val ftypes = fields.map { case (fname, fex) => (fname, typInf(fex, G, K)) }; // type all expressions
      if ftypes.exists { (_, t) => t == None } then None // check for fields with None types
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
              if rec.fields.exists { (f, e) => // typeCheck all fields wrt linkage definition
                rt.fields.get(f) match {
                  case Some(typedef) => !typCheck(e, typedef, G, K) // if any exp in record does not typecheck
                  case _ => true // or field does not exist in the type
                }
              } then None else Some(ftype)
          }
      }

    //  R = \overline{C' {(f': T')*}} in [[a]]
    //  C {(f_i: T_i)*} in \overline{C' {(f': T')*}}
    //  forall i, G |- e_i : T_i
    //_________________________________________________ T_ADT
    //  G |- a.R(C {(f_i = e_i)*}) : a.R
    case InstADT(ftype, cname, rec) =>
      val inferredtypes = rec.fields.map { case (f, e) => (f, typInf(e, G, K)) };
      K.get(ftype.path).flatMap {
        lkg =>
          lkg.adts.get(ftype.name).flatMap {
            (marker, adt) =>
              assert(marker == Eq); // should be Eq in a complete linkage, check with assertion
              adt.cs.get(cname).flatMap {
                case RecType(fields) =>
                  val linkagetypes = fields.map { case (f, t) => (f, Some(t)) };
                  if  inferredtypes.equals(linkagetypes) // we do not allow subtyping within ADT records right now
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
                    case (c, Some(FunType(infrt, otype))) =>
                      adt.cs.get(c) match {
                        // all output types are not the same OR inferred input type doesn't match definition
                        case Some(defrt) => funtypes.head._2 != Some(otype) || infrt != defrt
                        case _ => true
                      }
                    case _ => true // if not, or if something doesn't have a function type
                  } then None else funtypes.head._2 // first function output type since all are the same
              }
          }
        case _ => None
      }

    // All other cases
    case _ => None
  } // end fun


  // Type Checking
  // G is the typing context, K is the linkage context
  // does expression exp have the expected type t?
  def typCheck(exp: Expression, t: Type, G: Map[String, Type], K: Map[FamilyPath, Linkage]): Boolean =
    typInf(exp, G, K) match {
      case Some(inft) => subtype(inft, t, K)
      case _ => false
    }

  /*====================================== SUBTYPING ======================================*/

  // Subtyping
  // K is the linkage context
  // is T1 a subtype of T2? (or equal to T2)
  def subtype(t1: Type, t2: Type, K: Map[FamilyPath, Linkage]): Boolean =
    (t1, t2) match {
      // a.R <: t2 means we pull out the definition of R from linkage
      // and check if subtype of t2
      case (FamType(path, name), t2) =>
        K.get(path).flatMap{
          lkg => lkg.types.get(name).flatMap{
            (marker, rectype) =>
              assert(marker == Eq); // should be Eq in a complete linkage, check
              Some(subtype(rectype, t2, K))
          }
        } match {case Some(b) => b case _ => false} // pull out boolean from option

      // conventional arrow type subtyping
      case (FunType(it1, ot1), FunType(it2, ot2)) =>
        subtype(it2, it1, K) && subtype(ot1, ot2, K)

      // {(fi : Ti)*} <: {(fj : Tj)*}
      case (RecType(fds1), RecType(fds2)) =>
        // width subtyping: all fields in T2 appear in T1
        fds2.forall { case (fj, tj) =>
          fds1.get(fj) match {
            case Some(ti) => subtype(ti, tj, K) // depth subtyping
            case _ => false
          }
        }

      case (_, _) => (t1 == t2) // defer to equality
    }


  /*====================================== LINKAGE WELL-FORMEDNESS  ======================================*/

//  case class Linkage(self: SelfFamily, sup: SelfFamily, types: Map[String, (Marker, RecType)],
//                     adts: Map[String, (Marker, ADT)], funs: Map[String, (FunType, Lam)])

  // G is the typing context
  // K is the linkage context
  def linkage_ok (lkg: Linkage, G: Map[String, Type], K: Map[FamilyPath, Linkage]): Boolean = {
    // forall (R = {(f: T)*}) in TYPES, WF({(f: T)*})
    (lkg.types.filter{case (s, (m, rt)) => !wf(rt, K)}.isEmpty &&

    // forall (R = \overline{C {(f: T)*}}) in ADTS, WF({(f: T)*})
    lkg.adts.filter{ case (s, (m, adt)) =>
        adt.cs.exists{ case (s, rt) => !wf(rt, K)} // exists an ADT that's not well-formed
    }.isEmpty &&

    // forall (m : (T -> T') = (lam (x : T). body)),
    //    G |- lam (x : T). body : T -> T'
    lkg.funs.filter{ case (s, (ft, lam)) => !typCheck(lam, ft, G, K)}.isEmpty)
  }

  /*====================================== LINKAGE CONCATENATION  ======================================*/

  // the assumption is that all linkages in K are incomplete
  def complete_linkage(fam: FamilyPath, K: Map[FamilyPath, Linkage]): Linkage = {
    fam match {
      // K |- self(A) ~> [[self(A)]]
      // ____________________________ L-Qual
      // K |- A ~> [[A]]
      case AbsoluteFamily(f) => complete_linkage(SelfFamily(f), K)

      // A ~> [self(A)] in K
      // K |- super(A) ~> [[self(P)]]
      // [[self(P)]] + [self(A)] = [[self(A)]]
      // _______________________________________ L-Self
      // K |- self(A) ~> [[self(A)]]
      case _ => K.get(fam) match { // do we have a linkage for this family?
        case Some(lkg) => // have an incomplete? let's build a complete one
          if (lkg.sup == null) then { // no parent? no problem
            concat(null, lkg) // concat with empty complete linkage and return
          } else {
            val parent = lkg.sup;
            val complete_super = complete_linkage(parent, K)
            concat(complete_super, lkg)
          }
        case _ => null // none? tough luck :c
      }
    }
  }

  // concatenates two linkages
  // lkg1 is complete
  // lkg2 is incomplete
  def concat(lkg1: Linkage, lkg2: Linkage): Linkage = {

    // TODO: Syntactic Transformation
    // In linkage for Family A, replace self(A) with self(B).

    Linkage(lkg2.self, lkg1.self, concat_types(lkg1.types, lkg2.types),
      concat_adts(lkg1.adts, lkg2.adts), concat_funs(lkg1.funs, lkg2.funs))
  }

  def concat_types(types1: Map[String, (Marker, RecType)], types2: Map[String, (Marker, RecType)]) : Map[String, (Marker, RecType)] = {
    // not extended in the child
    val unchanged_parent_types = types1.filter{case (k,(m,v)) => !types2.contains(k)}
    // types that are being extended in the child
    val types_to_extend = types2.filter{case (k, (m,v)) => types1.contains(k)}
    // types that are completely new in child
    val new_types = types2.filter{case (k, (m,v)) => !types1.contains(k)}

    // actually extending the types
    val extended_types = types_to_extend.map{
      case (k, (m,rt)) =>
        types1.get(k) match {
          case Some((_, rtype)) => (k, (Eq, RecType((rt.fields).++(rtype.fields)))) // this can be done w/o overriding
          case _ => assert(false) // unreachable by definition
        }
    }
    // the actual result is all of these combined
    (unchanged_parent_types.++(extended_types)).++(new_types)
  }

  def concat_adts(adts1: Map[String, (Marker, ADT)], adts2: Map[String, (Marker, ADT)]) : Map[String, (Marker, ADT)] = {
    // not extended in the child
    val unchanged_parent_adts = adts1.filter{case (k,(m,a)) => !adts2.contains(k)}
    // adts that are being extended in the child
    val adts_to_extend = adts2.filter{case (k, (m,a)) => adts1.contains(k)}
    // adts that are completely new in child
    val new_adts = adts2.filter{case (k, (m,a)) => !adts1.contains(k)}

    // actually extending the adts
    val extended_adts = adts_to_extend.map{
      case (k, (m, a)) =>
        adts1.get(k) match {
          case Some((_, adt)) => (k, (Eq, ADT((a.cs).++(adt.cs)))) // this can be done w/o overriding
          case _ => assert(false) // unreachable by definition
        }
    }
    // the actual result is all of these combined
    (unchanged_parent_adts.++(extended_adts)).++(new_adts)
  }

  def concat_funs(funs1: Map[String, (FunType, Lam)], funs2: Map[String, (FunType, Lam)]) : Map[String, (FunType, Lam)] = {
    // functions from parent, not overridden in child
    val unchanged_parent_funs = funs1.filter{case (k,(ft,lam)) => !funs2.contains(k)}
    // functions that child overrides
    val funs_to_override = funs2.filter{case (k, (ft, lam)) => funs1.contains(k)}
    // new functions in child
    val new_funs = funs2.filter{case (k, (ft, lam)) => !funs1.contains(k)}

    val overridden_funs = funs_to_override.map{
      case (k, (ft, lam)) =>
        funs1.get(k) match {
          case Some((ftype, fdef)) =>
            if (ft != ftype) then {
              throw new Exception("Attempting to override function with conflicting type.")
            } else (k, (ft, fdef)) // otherwise, just use new definition from child (fdef)
          case _ => assert(false) // unreachable by definition
        }
    }

    // the actual result is all of these combined
    (unchanged_parent_funs.++(overridden_funs)).++(new_funs)
  }



} // eof