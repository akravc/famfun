object famlang {
  // Families & Paths
  case class Family(name: String)
  sealed class FamilyPath // a
  case class AbsoluteFamily(fam: Family) extends FamilyPath // A
  case class SelfFamily(fam: Family) extends FamilyPath // self(A)

  // Types
  sealed class Type
  case object N extends Type
  case object B extends Type
  case class FamType(path: FamilyPath, name: String) extends Type // a.R
  case class FunType(input: Type, output: Type) extends Type // T -> T'
  case class RecType(fields: Map[String, Type]) extends Type // {(f: T)*}

  // ADTs
  case class ADT(cs: Map[String, RecType])

  // Expressions
  sealed class Expression
  case class Var(id: String) extends Expression // x
  case class Lam(v: Var, t: Type, body: Expression) extends Expression // lam (x: T). body
  case class FamFun(path: FamilyPath, name: String) extends Expression // a.m
  case class FamCases(path: FamilyPath, name: String) extends Expression // a.r
  case class App(e1: Expression, e2: Expression) extends Expression // e g
  case class Rec(fields: Map[String, Expression]) extends Expression // {(f = e)*}
  case class Proj(e: Expression, name: String) extends Expression // e.f
  case class Inst(t: FamType, rec: Rec) extends Expression // a.R({(f = e)*})
  case class InstADT(t: FamType, cname: String, rec: Rec) extends Expression // a.R(C {(f = e)*})
  case class Match(e: Expression, g: Expression) extends Expression // match e with g
  case class Nexp(n: Int) extends Expression
  case class Bexp(b: Boolean) extends Expression

  // Linkages
  sealed class Marker // either += or =
  case object PlusEq extends Marker // type extension marker
  case object Eq extends Marker // type definition marker

  case class Linkage(self: SelfFamily, // self
                     sup: SelfFamily,  // super
                     types: Map[String, (Marker, RecType)],
                     defaults: Map[String, (Marker, Rec)],
                     adts: Map[String, (Marker, ADT)],
                     funs: Map[String, (FunType, Lam)],
                     depot: Map[String, (Marker, FunType, Lam)])


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
  // ASSUMPTION: Linkages in K are complete and well-formed
  def wf(t: Type, K: Map[FamilyPath, Linkage]): Boolean = t match {
    case N => true
    case B => true
    case FamType(path, name) =>
      K.get(path) match {
        case Some(lkg) => lkg.types.contains(name) || lkg.adts.contains(name)
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
  // ASSUMPTION: Linkages are complete and well-formed
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
        typInf(body, G.+(x -> xtype), K).map { otype => FunType(xtype, otype) }
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
        Some(RecType(ftypes.map { case (f, Some(t)) => (f, t) case (f, None) => (f, N) })) // the 2nd case is bogus
      } // extract types from options

    //  G |- e : {(f': T')*}
    //  (f: T) in \overline{f': T'}
    //_______________________________ T_RecField
    //  G |- e.f : T
    case Proj(e, f) =>
      typInf(e, G, K).flatMap {
        case RecType(ftypes) => ftypes.get(f)
        // if we have an instance of a type, the inferred type will be a famtype
        case FamType(p, n) =>
          K.get(p).flatMap {
            lkg =>
              lkg.types.get(n) match {
                case Some(_, RecType(fields)) => fields.get(f)
                case _ => None
              }
          }
        case _ => None }

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


    //  r : {(f_i:T_i)*} -> {(C_j':T_j'->T_j'')*} =
    //      lam (x: {(f_i:T_i)*}). body) in [[a]]
    // ___________________________________________________ T_Cases
    // G |- a.r : {(f_i:T_i)*} -> {(C_j':T_j'->T_j'')*}
    case FamCases(path, name) =>
      K.get(path).flatMap {
        lkg =>
          lkg.depot.get(name).map {
            // funtype should be well-formed, check with assertion
            (marker, funtype, lam) =>
              assert(marker == Eq);
              assert(wf(funtype, K));
              funtype
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
    //  G |- g: {(C_i: {(f_i: T_i)*} -> T')*}
    //  ___________________________________________ T_Match
    //    G |- match e with g : T'
    case Match(e, g) =>
      typInf(e, G, K).flatMap {
        case FamType(path, name) =>
          K.get(path).flatMap {
            lkg =>
              // look up the name of the ADT type in the linkage
              lkg.adts.get(name).flatMap {
                (marker, adt) =>
                  assert(marker == Eq); // should be Eq in a complete linkage, check with assertion
                  g match {
                    case Rec(fields) => // the fields are constructor names, same as the keys of the adt
                      if (fields.keySet != adt.cs.keySet) then { // all constructor names must appear in match
                        throw new Exception("Pattern match is not exhaustive.")
                      } else {
                        val funtypes = fields.map { case (c, lam) => (c, typInf(lam, G, K)) }; // infer types of the functions
                        // output type of the first funtype for equality comparison later
                        val head_out = funtypes.head._2 match {
                          case Some(FunType(i, o)) => o // should be the same output type for each case lambda
                          case _ => return None // abandon ship if the first inferred type is not even a function type
                        }
                        if fields.forall {
                          case (c, lam) =>
                            adt.cs.get(c) match {
                              case Some(constr_rectype) => typCheck(lam, FunType(constr_rectype, head_out), G, K)
                              case _ => false
                            }
                        } then Some(head_out) else None
                      }
                    case _ => None // if the expression g is not a a record
                  }
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
    if (t1 == t2) then true else
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

      case (_, _) => false
    }

  /*====================================== LINKAGE CONCATENATION  ======================================*/

  // Given a context of incomplete, well-formed linkages, produce a complete linkage for some family path fpath
  // ASSUMPTION: linkages in K are incomplete, but are well-formed

  def complete_linkage(fpath: FamilyPath, K: Map[FamilyPath, Linkage]): Linkage = {
    fpath match {
      // K |- self(A) ~> [[self(A)]]
      // ____________________________ L-Qual
      // K |- A ~> [[A]]
      case AbsoluteFamily(f) => complete_linkage(SelfFamily(f), K)

      // A ~> [self(A)] in K
      // K |- super(A) ~> [[self(P)]]
      // [[self(P)]] + [self(A)] = [[self(A)]]
      // _______________________________________ L-Self
      // K |- self(A) ~> [[self(A)]]
      case SelfFamily(Family(fname)) => K.get(fpath) match { // do we have a linkage for this family?
        case Some(lkg) => // have an incomplete? let's build a complete one
          if (lkg.sup == null) then { // no parent? no problem
            concat(null, lkg) // concat with empty complete linkage and return
          } else {
            // A ~> [self(A)] in K
            // K |- [self(A)].super ~> [[self(P)]]
            // _____________________________________ L-Super
            // K |- super(A) ~> [[self(P)]]
            val parent = lkg.sup;
            val complete_super = complete_linkage(parent, K)
            concat(complete_super, lkg)
          }
        case _ => throw new Exception("No incomplete linkage exists for family " + fname) // none? tough luck :c
      }
      case _ => assert(false) // path is neither self nor absolute
    }
  }

  // HELPERS for concatenating linkages: replace self(A) with self(B) in types and expressions

  // replace self-paths p1 with self-paths p2 in a type
  def update_self_in_type(t: Type, p1: SelfFamily, p2: SelfFamily): Type = {
    t match {
      case FamType(path, name) =>
        if (path == p1) then FamType(p2, name) else FamType(path, name)
      case FunType(t1, t2) => FunType(update_self_in_type(t1, p1, p2), update_self_in_type(t2, p1, p2))
      case RecType(m) => RecType(m.map{case (s, ft) => (s, update_self_in_type(ft, p1, p2))})
      case _ => t
    }
  }

  // replace self-paths p1 with self-paths p2 in an expression
  def update_self_in_exp(e: Expression, p1: SelfFamily, p2: SelfFamily): Expression = {
    e match {
      case Lam(v, t, body) => Lam(v, update_self_in_type(t, p1, p2), update_self_in_exp(body, p1, p2))
      case FamFun(path, name) => if (path == p1) then FamFun(p2, name) else e
      case FamCases(path, name) => if (path == p1) then FamCases(p2, name) else e
      case App(e1, e2) => App(update_self_in_exp(e1, p1, p2), update_self_in_exp(e2, p1, p2))
      case Rec(m) => Rec(m.map{case (s, fex) => (s, update_self_in_exp(fex, p1, p2))})
      case Proj(exp, name) => Proj(update_self_in_exp(exp, p1, p2), name)
      case Inst(t, rec) =>
        Inst(update_self_in_type(t, p1, p2).asInstanceOf[FamType], update_self_in_exp(rec, p1, p2).asInstanceOf[Rec])
      case InstADT(t, cname, rec) =>
        InstADT(update_self_in_type(t, p1, p2).asInstanceOf[FamType], cname, update_self_in_exp(rec, p1, p2).asInstanceOf[Rec])
      case Match(exp, g) => Match(update_self_in_exp(exp, p1, p2), update_self_in_exp(g, p1, p2))
      case _ => e
    }
  }

  // concatenates two linkages
  // ASSUMPTION: lkgA is complete, lkgB is incomplete
  def concat(lkgA: Linkage, lkgB: Linkage): Linkage = {
    if lkgA==null then lkgB else {

    // Syntactic Transformation
    // In linkage for Family A, replace self(A) with self(B).
    val p1 = lkgA.self
    val p2 = lkgB.self
    val updated_types =
      lkgA.types.map{case (s, (m, rt)) => (s, (m, update_self_in_type(rt, p1, p2).asInstanceOf[RecType]))}
    val updated_defaults =
      lkgA.defaults.map{case (s, (m, r)) => (s, (m, update_self_in_exp(r, p1, p2).asInstanceOf[Rec]))}
    val updated_adts =
      lkgA.adts.map{case (s, (m, adt)) =>
        (s, (m, ADT(adt.cs.map{case(s, rt) => (s, update_self_in_type(rt, p1, p2).asInstanceOf[RecType])})))}
    val updated_funs =
      lkgA.funs.map{case (s, (ft, lm)) =>
        (s, (update_self_in_type(ft, p1, p2).asInstanceOf[FunType], update_self_in_exp(lm, p1, p2).asInstanceOf[Lam]))}
    val updated_depot =
      lkgA.depot.map{ case (s, (m, ft, lm)) =>
        (s, (m, update_self_in_type(ft, p1, p2).asInstanceOf[FunType], update_self_in_exp(lm, p1, p2).asInstanceOf[Lam]))}

    // Concat and create new, complete linkage
    Linkage(lkgB.self, lkgA.self, concat_types(updated_types, lkgB.types),
      concat_defaults(updated_defaults, lkgB.defaults), concat_adts(updated_adts, lkgB.adts),
      concat_funs(updated_funs, lkgB.funs), concat_depots(updated_depot, lkgB.depot))
    }
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
          case Some((_, rtype)) =>
            // make sure we're not repeating any fields
            val combined = (rt.fields).++(rtype.fields)
            if (combined.size != rt.fields.size + rtype.fields.size)
            then throw new Exception("Concatenation resulted in duplicate fields in a record type.")
            else (k, (Eq, RecType(combined)))
          case _ => assert(false) // unreachable by definition
        }
    }
    // the actual result is all of these combined
    (unchanged_parent_types.++(extended_types)).++(new_types)
  }

  def concat_defaults(defaults1: Map[String, (Marker, Rec)], defaults2: Map[String, (Marker, Rec)]) : Map[String, (Marker, Rec)] = {
    // not extended in the child
    val unchanged_parent_defaults = defaults1.filter{case (k,(m,v)) => !defaults2.contains(k)}
    // defaults for types that are being extended in the child
    val defaults_to_extend = defaults2.filter{case (k, (m,v)) => defaults1.contains(k)}
    // defaults for types that are completely new in child
    val new_defaults = defaults2.filter{case (k, (m,v)) => !defaults1.contains(k)}

    // actually extending the defaults for extended types
    val extended_defaults = defaults_to_extend.map{
      case (k, (m,r)) =>
        defaults1.get(k) match {
          case Some((_, rcrd)) =>
            // make sure we're not repeating any fields
            val combined = (r.fields).++(rcrd.fields)
            if (combined.size != r.fields.size + rcrd.fields.size)
            then throw new Exception("Concatenation resulted in duplicate fields in a record of defaults.")
            else (k, (Eq, Rec(combined)))
          case _ => assert(false) // unreachable by definition
        }
    }
    // the actual result is all of these combined
    (unchanged_parent_defaults.++(extended_defaults)).++(new_defaults)
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
          case Some((_, adt)) =>
            // make sure we're not repeating any constructors
            val combined = (a.cs).++(adt.cs)
            if (combined.size != a.cs.size + adt.cs.size)
            then throw new Exception("Concatenation resulted in duplicate constructors in an ADT.")
            else (k, (Eq, ADT(combined)))
          case _ => assert(false) // unreachable by definition
        }
    }
    // the actual result is all of these combined
    (unchanged_parent_adts.++(extended_adts)).++(new_adts)
  }


  def concat_funs(funs1: Map[String, (FunType, Lam)],
                  funs2: Map[String, (FunType, Lam)]) : Map[String, (FunType, Lam)] = {
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

  def concat_depots(dep1: Map[String, (Marker, FunType, Lam)],
                    dep2: Map[String, (Marker, FunType, Lam)]) : Map[String, (Marker, FunType, Lam)] = {
    // cases from parent, not overridden in child
    val unchanged_parent_cases = dep1.filter{case (k,(m, ft,lam)) => !dep2.contains(k)}
    // cases that child extends
    val cases_to_extend = dep2.filter{case (k, (m, ft, lam)) => dep1.contains(k)}
    // new cases in child
    val new_cases = dep2.filter{case (k, (m, ft, lam)) => !dep1.contains(k)}

    val extended_cases = cases_to_extend.map {
      case (k, (m2, ft2, lam2)) =>
        assert(m2 == PlusEq); // the marker on the child cases should be +=
        dep1.get(k) match {
          case Some((m1, ft1, lam1)) =>
            (ft1, ft2) match {
              case (FunType(in1, out1), FunType(in2, out2)) =>
                // TODO: here, we should really check that in2 is a subtype of in1, since child cases may take more args
                assert(out1.isInstanceOf[RecType]);
                assert(out2.isInstanceOf[RecType]);
                val out1map = out1.asInstanceOf[RecType].fields
                val out2map = out2.asInstanceOf[RecType].fields
                val combined_out = (out1map).++(out2map)
                if (combined_out.size != out1map.size + out2map.size) then
                  throw new Exception("Concatenation resulted in duplicate fields in the type of a cases construct.")
                else {
                  assert(lam1.isInstanceOf[Lam]); assert(lam2.isInstanceOf[Lam]);
                  val caserec1 = lam1.body
                  val caserec2 = lam2.body
                  assert(caserec1.isInstanceOf[Rec]); assert(caserec2.isInstanceOf[Rec]); // bodies have to be records
                  val casemap1 = caserec1.asInstanceOf[Rec].fields
                  val casemap2 = caserec2.asInstanceOf[Rec].fields
                  val comb_cases = (casemap1).++(casemap2)
                  if (comb_cases.size != casemap1.size + casemap2.size) then
                    throw new Exception("Concatenation of cases resulted in duplicate constructors.")
                  else {
                    // TODO: need to check that the variable of lam1 and lam2 is the same
                    // TODO: need to check that the type lam2.t is appropriate
                    (k, (Eq, FunType(in2, RecType(combined_out)), Lam(lam2.v, lam2.t, Rec(comb_cases))))
                  }
                }
              case (_, _) => throw new Exception("Some cases constructs have non-arrow types.")
            }
          case _ => assert(false) // unreachable by definition
        }
    }

    // the actual result is all of these combined
    (unchanged_parent_cases.++(extended_cases)).++(new_cases)
  }

  /*====================================== LINKAGE WELL-FORMEDNESS  ======================================*/

  // G is the typing context
  // K is the linkage context (incomplete linkages, before concatenation)
  // ASSUMPTION: all linkages are complete
  def linkage_ok (lkg: Linkage, G: Map[String, Type], K: Map[FamilyPath, Linkage]): Boolean = {
    // forall (R = {(f: T)*}) in TYPES, WF({(f: T)*})
    val types_ok = lkg.types.filter{case (s, (m, rt)) => !wf(rt, K)}.isEmpty
    // check that for every default record there is a type corresponding to it and the defaults typecheck
    val defaults_ok = lkg.defaults.filter{
      case (s, (m, r)) => !is_value(r) || // if the default is not a value or...
        (lkg.types.get(s) match {
          case Some(m, rt) => (rt != typInf(r, G, K).asInstanceOf[RecType]) // ...or the default has the wrong type
          case _ => assert(false)
        })}.isEmpty
    // forall (R = \overline{C {(f: T)*}}) in ADTS, WF({(f: T)*})
    val adts_ok = lkg.adts.filter{ case (s, (m, adt)) =>
      adt.cs.exists{ case (s, rt) => !wf(rt, K)} // exists an ADT that's not well-formed
    }.isEmpty

    // forall (m : (T -> T') = (lam (x : T). body)),
    //    G |- lam (x : T). body : T -> T'
    val funs_ok = lkg.funs.filter{
      case (s, (ft, lam)) =>
        if !typCheck(lam, ft, G, K) then
          print("Function " + s + " in linkage " + lkg.self + " does not typecheck\n");
          true // mark it
        else false
    }.isEmpty
    val cases_ok = lkg.depot.filter{ case (s, (m, ft, lam)) => !typCheck(lam, ft, G, K)}.isEmpty

    if !types_ok then throw new Exception("Types in linkage " + lkg.self + " are not well-formed.")
    else if !defaults_ok then throw new Exception("Defaults in linkage " + lkg.self + " don't typecheck.")
    else if !adts_ok then throw new Exception("ADTs in linkage " + lkg.self + " don't typecheck.")
    else if !funs_ok then throw new Exception("Functions in linkage " + lkg.self + " don't typecheck.")
    else if !cases_ok then throw new Exception("Cases in linkage " + lkg.self + " don't typecheck.")
    else true
  }

  /*====================================== LINKAGE SYNTACTIC TRANSFORMATION  ======================================*/

  def fill_paths_in_type (t: Type, p: FamilyPath) : Type = {
    if (p == null) then {
      throw new Exception("Attempting to update a relative type with a null path.")
    }
    t match {
      case FamType(path, name) => if (path == null) then FamType(p, name) else t
      case FunType(it, ot) => FunType(fill_paths_in_type(it, p), fill_paths_in_type(ot, p))
      case RecType(fields) => RecType(fields.map{(str, t) => (str, fill_paths_in_type(t, p))})
      case _ => t
    }
  }

  def fill_paths_in_exp (exp: Expression, p: FamilyPath) : Expression = {
    if (p == null) then {
      throw new Exception("Attempting to update a relative expression with a null path.")
    }
    exp match {
      case Lam(v, t, body) => Lam(v, fill_paths_in_type(t, p), fill_paths_in_exp(body, p))
      case FamFun(path, name) => if (path == null) then FamFun(p, name) else exp
      case FamCases(path, name) => if (path == null) then FamCases(p, name) else exp
      case App(e1, e2) => App(fill_paths_in_exp(e1, p), fill_paths_in_exp(e2, p))
      case Rec(fields) => Rec(fields.map{(s, e) => (s, fill_paths_in_exp(e, p))})
      case Proj(e, name) => Proj(fill_paths_in_exp(e, p), name)
      case Inst(t, rec) =>
        Inst(fill_paths_in_type(t, p).asInstanceOf[FamType], fill_paths_in_exp(rec, p).asInstanceOf[Rec])
      case InstADT(t, cname, rec) =>
        InstADT(fill_paths_in_type(t, p).asInstanceOf[FamType], cname, fill_paths_in_exp(rec, p).asInstanceOf[Rec])
      case Match(e, g) =>
        Match(fill_paths_in_exp(e, p), fill_paths_in_exp(g, p))
      case _ => exp
    }
  }

  def fill_paths (lkg: Linkage) : Linkage = {
    var p = lkg.self
    var newtypes =
      lkg.types.map{case (s, (m, rt)) => (s, (m, fill_paths_in_type(rt, p).asInstanceOf[RecType]))}
    var newdefaults =
      lkg.defaults.map{case (s, (m, rec)) => (s, (m, fill_paths_in_exp(rec, p).asInstanceOf[Rec]))}
    var newadts =
      lkg.adts.map{case (s, (m, adt)) => (s, (m, ADT(adt.cs.map{(s, rt) => (s, fill_paths_in_type(rt, p).asInstanceOf[RecType])})))}
    var newfuns = lkg.funs.map{case (s, (ft, lam)) =>
        (s, (fill_paths_in_type(ft, p).asInstanceOf[FunType], fill_paths_in_exp(lam, p).asInstanceOf[Lam]))}
    var newdepot = lkg.depot.map{case (s, (m, ft, lam)) =>
      (s, (m, fill_paths_in_type(ft, p).asInstanceOf[FunType], fill_paths_in_exp(lam, p).asInstanceOf[Lam]))}

    Linkage(p, lkg.sup, newtypes, newdefaults, newadts, newfuns, newdepot)
  }

} // eof