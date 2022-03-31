object famfun {
  // Families & Paths
  sealed trait Path
  case class Sp(sp: SelfPath) extends Path
  case class AbsoluteFamily(pref: Path, fam: String) extends Path // a.A

  sealed trait SelfPath
  case object Prog extends SelfPath // <prog>
  case class SelfFamily(pref: SelfPath, fam: String) extends SelfPath // self(sp.A)
  
  def pathName(p: Path): String = p match {
    case Sp(Prog) => throw new Exception("Should not try to get path name of <>")
    case Sp(SelfFamily(_, f)) => f
    case AbsoluteFamily(_, f) => f
  }

  // Types
  sealed trait Type
  case object N extends Type
  case object B extends Type
  case class FamType(path: Option[Path], name: String) extends Type // a.R
  case class FunType(input: Type, output: Type) extends Type // T -> T'
  case class RecType(fields: Map[String, Type]) extends Type // {(f: T)*}

  sealed trait Marker // either += or =
  case object PlusEq extends Marker // type extension marker
  case object Eq extends Marker // type definition marker

  // ADTs
  case class ADT(name: String, marker: Marker, cs: Map[String, RecType])

  // Expressions
  sealed trait Expression
  case class Var(id: String) extends Expression // x
  case class Lam(v: Var, t: Type, body: Expression) extends Expression // lam (x: T). body
  case class FamFun(path: Option[Path], name: String) extends Expression // a.m
  case class FamCases(path: Option[Path], name: String) extends Expression // a.r
  case class App(e1: Expression, e2: Expression) extends Expression // e g
  case class Rec(fields: Map[String, Expression]) extends Expression // {(f = e)*}
  case class Proj(e: Expression, name: String) extends Expression // e.f
  case class Inst(t: FamType, rec: Rec) extends Expression // a.R({(f = e)*})
  case class InstADT(t: FamType, cname: String, rec: Rec) extends Expression // a.R(C {(f = e)*})
  case class Match(e: Expression, g: Expression) extends Expression // match e with g
  case class Nexp(n: Int) extends Expression
  case class Bexp(b: Boolean) extends Expression

  sealed trait DefnBody
  case class BodyDeclared(defined: Expression) extends DefnBody
  case class BodyInherited(from: Path) extends DefnBody

  // Functions
  case class FunDefn(name: String, t: FunType, body: DefnBody)

  // Cases
  case class CasesDefn(name: String, matchType: FamType, t: Type, marker: Marker, body: DefnBody)

  // TODO: should we add a `furtherBinds: Option[Path]` field,
  //       or should things that can be extended (Marker = PlusEq)
  //       have field for what definitions they extend?
  // Linkages
  case class Linkage(path: Path,
                     self: SelfPath, // self
                     sup: Option[Path], // super
                     types: Map[String, (Marker, RecType)],
                     defaults: Map[String, (Marker, Rec)], // TODO: should this be combined with `types`?
                     adts: Map[String, ADT],
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
    case Nexp(n) => true
    case Bexp(b) => true
    case _ => false
  }

  /* TODO: uncomment
  /*====================================== TYPE WELL-FORMEDNESS ======================================*/

  // helper that returns the self version or the qualified version of the linkage
  def get_lkg(p: Path, K: Map[Path, Linkage]): Option[Linkage] = {
    p match {
      // if our path is a self path, just get the linkage
      case SelfFamily(Family(f)) => K.get(p)
      // if we have an absolute path, return the qualified version of the linkage
      case AbsoluteFamily(Family(f)) =>
        K.get(SelfFamily(Family(f))) match {
          case Some(lkg) => Some(update_paths(lkg, SelfFamily(Family(f)), p))
          case None => None
        }
      case _ => None
    }
  }

  // Well-Formedness Rules
  // K is the linkage context
  // ASSUMPTION: Linkages in K are complete and well-formed
  def wf(t: Type, K: Map[Path, Linkage]): Boolean = t match {
    case N => true
    case B => true
    case FamType(path, name) =>
      get_lkg(path, K) match {
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
  def typInf(exp: Expression, G: Map[String, Type], K: Map[Path, Linkage]): Option[Type] = exp match {

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
          get_lkg(p, K).flatMap {
            lkg =>
              lkg.types.get(n) match {
                case Some(_, RecType(fields)) => fields.get(f)
                case _ => None
              }
          }
        case _ => None }

    //  m : (T -> T') = (lam (x : T). body) in {{a}}
    //_______________________________________________ T_FamFun
    //  G |- a.m : T -> T'
    case FamFun(path, name) =>
      get_lkg(path, K).flatMap {
        lkg =>
          lkg.funs.get(name).map {
            // funtype should be well-formed, check with assertion
            (funtype, body) => assert(wf(funtype, K)); funtype
          }
      }


    //  r : {(f_i:T_i)*} -> {(C_j':T_j'->T_j'')*} =
    //      lam (x: {(f_i:T_i)*}). body) in {{a}}
    // ___________________________________________________ T_Cases
    // G |- a.r : {(f_i:T_i)*} -> {(C_j':T_j'->T_j'')*}
    case FamCases(path, name) =>
      get_lkg(path, K).flatMap {
        lkg =>
          lkg.depot.get(name).map {
            // types should be well-formed, check with assertion
            (matchtype, marker, funtype, lam) =>
              assert(marker == Eq);
              assert(wf(funtype, K));
              assert(wf(matchtype, K));
              funtype
          }
      }

    //  R = {(f_i: T_i)*} in {{a}}
    //  forall i, G |- e_i : T_i
    //______________________________________ T_Constructor
    //  G |- a.R({(f_i = e_i)*}) : a.R
    case Inst(ftype, rec) =>
      get_lkg(ftype.path, K).flatMap {
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

    //  R = \overline{C' {(f': T')*}} in {{a}}
    //  C {(f_i: T_i)*} in \overline{C' {(f': T')*}}
    //  forall i, G |- e_i : T_i
    //_________________________________________________ T_ADT
    //  G |- a.R(C {(f_i = e_i)*}) : a.R
    case InstADT(ftype, cname, rec) =>
      val inferredtypes = rec.fields.map { case (f, e) => (f, typInf(e, G, K)) };
      get_lkg(ftype.path, K).flatMap {
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
    //  R = \overline{C_i {(f_i: T_i)*}} in {{a}}
    //  G |- g: {(C_i: {(f_i: T_i)*} -> T')*}
    //  ___________________________________________ T_Match
    //    G |- match e with g : T'
    case Match(e, g) =>
      typInf(e, G, K).flatMap {
        case FamType(path, name) =>
          get_lkg(path, K).flatMap {
            lkg =>
              // look up the name of the ADT type in the linkage
              lkg.adts.get(name).flatMap {
                (marker, adt) =>
                  assert(marker == Eq); // should be Eq in a complete linkage, check with assertion
                  // check that g has proper application shape, cases to args: a.r {(f=e)*}
                  assert(g.isInstanceOf[App]);
                  assert(g.asInstanceOf[App].e1.isInstanceOf[FamCases]);
                  assert(g.asInstanceOf[App].e2.isInstanceOf[Rec]);
                  typInf(g, G, K).flatMap{
                    case RecType(fields) => // the fields are constructor names, same as the keys of the adt
                      if (fields.keySet != adt.cs.keySet) then { // all constructor names must appear in match
                        print("Pattern match is not exhaustive.");
                        return None;
                      } else {
                        // all of these function types must have inputs that correspond to the proper ADT constructor
                        // and the same output type
                        val head_out = fields.head._2 match {
                          case FunType(i, o) => o // should be the same output type for each case lambda
                          case _ => return None // abandon ship if the first inferred type is not even a function type
                        }
                        if fields.forall {
                          case (c, FunType(i, o)) =>
                            adt.cs.get(c) match {
                              case Some(constr_rectype) => (i == constr_rectype) && (o == head_out)
                              case _ => false
                            }
                          case _ => false
                        } then Some(head_out) else None
                      }
                    case _ => None // expression g does not have a record type
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
  def typCheck(exp: Expression, t: Type, G: Map[String, Type], K: Map[Path, Linkage]): Boolean =
    typInf(exp, G, K) match {
      case Some(inft) => subtype(inft, t, K)
      case _ => false
    }

  /*====================================== SUBTYPING ======================================*/

  // Subtyping
  // K is the linkage context
  // is T1 a subtype of T2? (or equal to T2)
  def subtype(t1: Type, t2: Type, K: Map[Path, Linkage]): Boolean =
    if (t1 == t2) then true else
    (t1, t2) match {
      // a.R <: t2 means we pull out the definition of R from linkage
      // and check if subtype of t2
      case (FamType(path, name), t2) =>
        get_lkg(path, K).flatMap{
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
  // ASSUMPTION: linkages in K are incomplete
  // we return the updated map of complete linkages for memoization purposes

  def complete_linkage(fpath: Path, K: Map[Path, Linkage], M: Map[Path, Linkage]): (Linkage, Map[Path, Linkage])  = {
    fpath match {
      // K |- self(A) ~> {{self(A)}}
      // ____________________________ L-Qual
      // K |- A ~> {{A}}
      case AbsoluteFamily(f) =>
        // do we have a complete linkage already?
        get_lkg(SelfFamily(f), M) match {
          case Some(lkg) => (lkg, M)
          case None => complete_linkage(SelfFamily(f), K, M)
        }

      // self(A) ~> {self(A)} in K
      // K |- super(A) ~> {{self(P)}}
      // {{self(P)}} + {self(A)} = {{self(A)}}
      // _______________________________________ L-Self
      // K |- self(A) ~> {{self(A)}}
      case SelfFamily(Family(fname)) =>
        get_lkg(fpath, M) match {
          case Some(lkg) => (lkg, M)
          case None => // don't have a complete linkage calculated yet
            get_lkg(fpath, K) match { // do we have an incomplete linkage for this family?
              case Some(lkg) => // have an incomplete? let's build a complete one
                if (lkg.sup == null) then { // no parent? no problem
                  val cat = concat(null, lkg) // concat with empty complete linkage and return
                  val updatedM = M.+(fpath->cat)
                  (cat, updatedM)
                } else {
                  // self(A) ~> {self(A)} in K
                  // K |- {self(A)}.super ~> {{self(P)}}
                  // _____________________________________ L-Super
                  // K |- super(A) ~> {{self(P)}}
                  val parent = lkg.sup;
                  val (complete_super, superM) = complete_linkage(parent, K, M)
                  val cat = concat(complete_super, lkg)
                  val updatedM = superM.+(fpath->cat)
                  (cat, updatedM)
                }
              case _ => throw new Exception("No incomplete linkage exists for family " + fname) // none? tough luck :c
            }
        }
      case _ => assert(false) // path is neither self nor absolute
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
      lkgA.types.map{case (s, (m, rt)) => (s, (m, update_type_paths(rt, p1, p2).asInstanceOf[RecType]))}
    val updated_defaults =
      lkgA.defaults.map{case (s, (m, r)) => (s, (m, update_exp_paths(r, p1, p2).asInstanceOf[Rec]))}
    val updated_adts =
      lkgA.adts.map{case (s, (m, adt)) =>
        (s, (m, ADT(adt.cs.map{case(s, rt) => (s, update_type_paths(rt, p1, p2).asInstanceOf[RecType])})))}
    val updated_funs =
      lkgA.funs.map{case (s, (ft, lm)) =>
        (s, (update_type_paths(ft, p1, p2).asInstanceOf[FunType], update_exp_paths(lm, p1, p2).asInstanceOf[Lam]))}
    val updated_depot =
      lkgA.depot.map{ case (s, (mt, m, ft, lm)) =>
        (s, (update_type_paths(mt, p1, p2).asInstanceOf[FamType], m,
          update_type_paths(ft, p1, p2).asInstanceOf[FunType], update_exp_paths(lm, p1, p2).asInstanceOf[Lam]))}

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
              // NOTE: currently we do not allow functions in child with the same names as in parent, but different type
              // this is due to several things: maps can't store multiple values for the same key, and also
              // selection of function from a family would require knowing the full type of the function
              throw new Exception("Attempting to override function with conflicting type.")
            } else (k, (ft, fdef)) // otherwise, just use new definition from child (fdef)
          case _ => assert(false) // unreachable by definition
        }
    }

    // the actual result is all of these combined
    (unchanged_parent_funs.++(overridden_funs)).++(new_funs)
  }

  // helper to get all bound vars in an expression
  def bound_vars (exp: Expression) : List[Var] = {
    exp match {
      case Lam(v, t, body) => v :: bound_vars(body)
      case App(e1, e2) => bound_vars(e1).++(bound_vars(e2))
      case Rec(fields) => fields.map{case (s, e) => bound_vars(e)}.flatten.toList
      case Proj(e, f) => bound_vars(e)
      case Inst(_, r) => bound_vars(r)
      case InstADT(_, _, r) => bound_vars(r)
      case Match(e, g) => bound_vars(e).++(bound_vars(g))
      case _ => List.empty[Var]
    }
  }

  // select a fresh variable name that's not contained in the list
  def pick_fresh (lst: List[Var]) : Var = {
    var x = "x"
    while (lst.contains(Var(x))) {
      x = Random.alphanumeric.filter(_.isLetter).head.toString
    }
    return Var(x)
  }

  // expression e is the body of a new lambda with bound var v2
  // we replace necessary instances of v1 with v2
  // ASSUMPTION: v1 is fresh in e
  def var_replace(exp: Expression, v1: Var, v2: Var) : Expression = {
    // if we're trying to replace an _ variable, nothing in the expression changes because
    // underscores are not used in the *bodies* of functions,
    // only in lam definitions as a placeholder
    if v1 == Var("_") then return exp;

    exp match {
      case Var(x) => if (v1 == Var(x)) then v2 else Var(x)
      case Lam(v, t, body) =>
        if (v1 == v) then {
          throw new Exception("Uh oh! The variable you're trying to replace is bound!")
        } else Lam(v, t, var_replace(body, v1, v2))
      case App(e1, e2) => App(var_replace(e1, v1, v2), var_replace(e2, v1, v2))
      case Rec(fields) => Rec(fields.map{case (s, e) => (s, var_replace(e, v1, v2))})
      case Proj(e, f) => Proj(var_replace(e, v1, v2), f)
      case Inst(t, r) => Inst(t, var_replace(r, v1, v2).asInstanceOf[Rec])
      case InstADT(t, c, r) => InstADT(t, c, var_replace(r, v1, v2).asInstanceOf[Rec])
      case Match(e, g) => Match(var_replace(e, v1, v2), var_replace(g, v1, v2))
      case _ => exp
    }
  }

  def concat_depots(dep1: Map[String, (FamType, Marker, FunType, Lam)],
                    dep2: Map[String, (FamType, Marker, FunType, Lam)]) : Map[String, (FamType, Marker, FunType, Lam)] = {
    // cases from parent, not overridden in child
    val unchanged_parent_cases = dep1.filter{case (k,_) => !dep2.contains(k)}
    // cases that child extends
    val cases_to_extend = dep2.filter{case (k,_) => dep1.contains(k)}
    // new cases in child
    val new_cases = dep2.filter{case (k, _) => !dep1.contains(k)}

    val extended_cases = cases_to_extend.map {
      case (k, (mt2, m2, ft2, lam2)) =>
        assert(m2 == PlusEq); // the marker on the child cases should be +=
        // get stuff from parent depot
        dep1.get(k) match {
          case Some((mt1, m1, ft1, lam1)) =>
            // handle the overriding case: if the name, match type, and the case type are the same,
            // and the marker is =, we override the definition.
            if (mt1 == mt2 && ft1 == ft2 && m2 == Eq) then (k, (mt2, m2, ft2, lam2));

            // if the signature does not match exactly, we attempt to extend. typechecker will figure out the rest
            (ft1, ft2) match {
              case (FunType(in1, out1), FunType(in2, out2)) =>
                // In the future, we might check that in2 is a subtype of in1, since child cases could take more args
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
                    // make sure that the new lambda variable is fresh
                    var caserec = Rec(comb_cases)
                    val bound = lam1.v :: (lam2.v :: bound_vars(caserec))
                    val freshv = pick_fresh(bound)
                    caserec = var_replace(caserec, lam1.v, freshv).asInstanceOf[Rec]
                    caserec = var_replace(caserec, lam2.v, freshv).asInstanceOf[Rec]
                    (k, (mt2, Eq, FunType(in2, RecType(combined_out)), Lam(freshv, lam2.t, caserec)))
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

  // for each instance of a type, check that all type fields are instantiated
  // if not, supplement with fields & values from default.
  def handle_defaults(exp: Expression, K: Map[Path, Linkage]) : Expression = {
    exp match {
      case Lam(v, t, body) => Lam(v, t, handle_defaults(body, K))
      case App(e1, e2) => App(handle_defaults(e1, K), handle_defaults(e2, K))
      case Rec(fields) => Rec(fields.map{case (s, e) => (s, handle_defaults(e, K))})
      case Proj(e, name) => Proj(handle_defaults(e, K), name)
      case Inst(t, rec) =>
        get_lkg(t.path, K) match {
          case Some(lkg) =>
            lkg.types.get(t.name) match {
              case Some((marker, rectype)) =>
                // rectype is all the fields that should be in this instance
                if (rectype.fields.keySet != rec.fields.keySet) then {
                  // look up the default record
                  lkg.defaults.get(t.name) match {
                    case Some((_, default_rec)) =>
                      var final_rec_fields = rec.fields
                      // need to add missing fields and values to rec
                      for (fd <- rectype.fields.keySet) {
                        if (!rec.fields.contains(fd)) then {
                          default_rec.fields.get(fd) match {
                            case Some(e) =>
                              // add a new binding for this missing field with the default value
                              final_rec_fields = final_rec_fields.+(fd -> e)
                            case _ => throw new Exception("No default for field " + fd)
                          }
                        }
                      }
                      // now after we've added all missing bindings, we can recurse
                      Inst(t, handle_defaults(Rec(final_rec_fields), K).asInstanceOf[Rec])
                    case _ => throw new Exception("No default record for type " + t.name)
                  }
                } else {
                  // simply propagate by recursion
                  Inst(t, handle_defaults(rec, K).asInstanceOf[Rec])
                }
              case _ => throw new Exception("No type by the name " + t.name + " found in the linkage.")
            }
          case None => throw new Exception("No linkage corresponding to family " + t.path)
        }
      case InstADT(t, c, rec) => InstADT(t, c, handle_defaults(rec, K).asInstanceOf[Rec])
      case Match(e, g) => Match(handle_defaults(e, K), handle_defaults(g, K))
      case _ => exp
    }
  }

  def fill_defaults_lkg (lkg: Linkage, K: Map[Path, Linkage]) : Linkage = {
    // need to update instances in every expression: defaults, funs, & cases
    val newdefaults = lkg.defaults.map{ case (s, (m, r)) => (s, (m, handle_defaults(r, K).asInstanceOf[Rec]))}
    val newfuns = lkg.funs.map{ case (s, (ft, lam)) => (s, (ft, handle_defaults(lam, K).asInstanceOf[Lam]))}
    val newdepot = lkg.depot.map{ case (s, (mt, m, ft, lam)) =>
      (s, (mt, m, ft, handle_defaults(lam, K).asInstanceOf[Lam]))}

    Linkage(lkg.self, lkg.sup, lkg.types, newdefaults, lkg.adts, newfuns, newdepot)
  }


  /*====================================== LINKAGE WELL-FORMEDNESS  ======================================*/

  // G is the typing context
  // ASSUMPTION: all linkages are complete
  def linkage_ok (lkg: Linkage, G: Map[String, Type], K: Map[Path, Linkage]): Boolean = {
    // forall (R = {(f: T)*}) in TYPES, WF({(f: T)*})
    val types_ok = lkg.types.filter{case (s, (m, rt)) => !wf(rt, K)}.isEmpty
    // check that for every default record there is a type corresponding to it and the defaults typecheck
    val defaults_ok = lkg.defaults.filter{
      case (s, (m, r)) => !is_value(r) || // if the default is not a value or...
        (lkg.types.get(s) match {
          case Some(m, rt) =>
            // the inferred type of the default can have fewer fields than the actual type (if not all fields have default values)
            // therefore the real type should be a subtype of the inferred default type
            typInf(r, G, K) match {
              case Some(inferred_deftype) =>
                !subtype(rt, inferred_deftype, K)
              case None => true
            }
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
    val cases_ok = lkg.depot.filter{ case (s, (mt, m, ft, lam)) => !typCheck(lam, ft, G, K)}.isEmpty

    if !types_ok then { print("Types in linkage " + lkg.self + " are not well-formed."); return false }
    else if !defaults_ok then { print("Defaults in linkage " + lkg.self + " don't typecheck."); return false }
    else if !adts_ok then { print("ADTs in linkage " + lkg.self + " don't typecheck."); return false }
    else if !funs_ok then { print("Functions in linkage " + lkg.self + " don't typecheck."); return false }
    else if !cases_ok then { print("Cases in linkage " + lkg.self + " don't typecheck."); return false }
    else true
  }

  /*====================================== LINKAGE TRANSFORMATIONS  ======================================*/

  // replaces paths p1 in type t with paths p2
  def update_type_paths (t: Type, p1: Path, p2: Path) : Type = {
    if (p2 == null) then {
      throw new Exception("Attempting to update a type with a null path.")
    }
    t match {
      case FamType(path, name) => if (path == p1) then FamType(p2, name) else t
      case FunType(it, ot) => FunType(update_type_paths(it, p1, p2), update_type_paths(ot, p1, p2))
      case RecType(fields) => RecType(fields.map{(str, t) => (str, update_type_paths(t, p1, p2))})
      case _ => t
    }
  }

  // replaces paths p1 in expression exp with paths p2
  def update_exp_paths (exp: Expression, p1: Path, p2: Path) : Expression = {
    if (p2 == null) then {
      throw new Exception("Attempting to update an expression with a null path.")
    }
    exp match {
      case Lam(v, t, body) => Lam(v, update_type_paths(t, p1, p2), update_exp_paths(body, p1, p2))
      case FamFun(path, name) => if (path == p1) then FamFun(p2, name) else exp
      case FamCases(path, name) => if (path == p1) then FamCases(p2, name) else exp
      case App(e1, e2) => App(update_exp_paths(e1, p1, p2), update_exp_paths(e2, p1, p2))
      case Rec(fields) => Rec(fields.map{(s, e) => (s, update_exp_paths(e, p1, p2))})
      case Proj(e, name) => Proj(update_exp_paths(e, p1, p2), name)
      case Inst(t, rec) =>
        Inst(update_type_paths(t, p1, p2).asInstanceOf[FamType], update_exp_paths(rec, p1, p2).asInstanceOf[Rec])
      case InstADT(t, cname, rec) =>
        InstADT(update_type_paths(t, p1, p2).asInstanceOf[FamType], cname, update_exp_paths(rec, p1, p2).asInstanceOf[Rec])
      case Match(e, g) =>
        Match(update_exp_paths(e, p1, p2), update_exp_paths(g, p1, p2))
      case _ => exp
    }
  }

  // replace paths with other paths
  def update_paths (lkg: Linkage, p1: Path, p2: Path) : Linkage = {
    var newself = if (lkg.self == p1) then p2 else lkg.self
    // NOTE: currently, super serves only for concatenation purposes. it is always a self() path.
    // we do not need to replace super when updating paths.
    // sometimes we need to replace self(A) with the qualified version (A), but this does not apply for super.
    // this may change when we have nested families.
    var newtypes =
      lkg.types.map{case (s, (m, rt)) => (s, (m, update_type_paths(rt, p1, p2).asInstanceOf[RecType]))}
    var newdefaults =
      lkg.defaults.map{case (s, (m, rec)) => (s, (m, update_exp_paths(rec, p1, p2).asInstanceOf[Rec]))}
    var newadts =
      lkg.adts.map{case (s, (m, adt)) => (s, (m, ADT(adt.cs.map{(s, rt) => (s, update_type_paths(rt, p1, p2).asInstanceOf[RecType])})))}
    var newfuns = lkg.funs.map{case (s, (ft, lam)) =>
        (s, (update_type_paths(ft, p1, p2).asInstanceOf[FunType], update_exp_paths(lam, p1, p2).asInstanceOf[Lam]))}
    var newdepot = lkg.depot.map{case (s, (mt, m, ft, lam)) =>
      (s, (update_type_paths(mt, p1, p2).asInstanceOf[FamType], m,
        update_type_paths(ft, p1, p2).asInstanceOf[FunType], update_exp_paths(lam, p1, p2).asInstanceOf[Lam]))}

    Linkage(newself, lkg.sup, newtypes, newdefaults, newadts, newfuns, newdepot)
  }


  // unfold wildcards in cases
  // ASSUMPTION: incomplete linkages, K is the context of incomplete linkages
  def unfold_wildcards (lkg: Linkage, K: Map[Path, Linkage]) : Linkage = {
    val newdepot = lkg.depot.map{ case (k, (mt, m, ft, lam)) =>
      assert(lam.body.isInstanceOf[Rec]);
      assert(ft.output.isInstanceOf[RecType]);
      // a map of case ids in this definition
      var case_ids = lam.body.asInstanceOf[Rec].fields
      // output type of cases is a record type map
      var cases_out_type = ft.output.asInstanceOf[RecType].fields
      // the output type of each lambda case should be the same, grab the first one
      val out_type_of_each_lam = cases_out_type.head._2.asInstanceOf[FunType].output
      if !case_ids.contains("_") then (k, (mt, m, ft, lam)) // quit here if no wildcard cases
      else {
        // check mt is a family type, look it up in the linkage for that family
        mt match {
          case FamType(path, name) =>
            get_lkg(path, K) match {
              // this is the linkage in which the match type appears
              case Some(typelkg) =>
                // get the named type from the proper family's linkage
                typelkg.adts.get(name) match {
                  // there's an ADT for our match type, yay!
                  case Some((m, adt)) =>
                    // retrieve the wildcard case from the cases definition
                    case_ids.get("_") match {
                      // case ids are mapped to functions
                      case Some(Lam(v, t, wild_body)) =>
                        for (c <- adt.cs.keySet) {
                          // if some constructor does not appear in the case_ids and the output type,
                          // it is covered by the wildcard
                          if !case_ids.contains(c) && !cases_out_type.contains(c) then {
                            adt.cs.get(c) match {
                              case Some(constr_rt) =>
                                // add an unfolded case with a _ variable (will not be used),
                                // the same input type as the ADT has for this constructor, and
                                // the body from the wildcard case
                                case_ids = case_ids.+((c, Lam(Var("_"), constr_rt, wild_body)))
                                // add to the output type of cases to reflect the new case inserted
                                cases_out_type = cases_out_type.+((c, FunType(constr_rt, out_type_of_each_lam)))
                              case _ => assert(false); //that's just not possible
                            }
                          }
                        };
                        // remove the wildcard case
                        case_ids = case_ids.-("_");
                        cases_out_type = cases_out_type.-("_");
                        // return the updated definition
                        (k, (mt, m, FunType(ft.input, RecType(cases_out_type)), Lam(lam.v, lam.t, Rec(case_ids))))
                      case _ => throw new Exception("Wildcard case does not have a lambda abstraction value.")
                    }
                  case _ => throw new Exception("Match type does not exist in the specified family, " +
                    "or does not have an ADT definition.")
                }
              case _ => throw new Exception("No linkage exists for family of match type.")
            }
          case null => throw new Exception("The match type is null.")
        }
      }
    }
    // return the updated incomplete linkage
    Linkage(lkg.self, lkg.sup, lkg.types, lkg.defaults, lkg.adts, lkg.funs, newdepot)
  }
  */
}
