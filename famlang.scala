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
  case class App(e1: Expression, e2: Expression) extends Expression // e g
  case class Rec(fields: Map[String, Expression]) extends Expression // {(f = e)*}
  case class Proj(e: Expression, name: String) extends Expression // e.f
  case class Inst(t: FamType, rec: Rec) extends Expression // a.R({(f = e)*})
  case class InstADT(t: FamType, cname: String, rec: Rec) extends Expression // a.R(C {(f = e)*})
  case class Match(e: Expression, cases: Map[String, Lam]) extends Expression // match e with (C => g)*
  case class Nexp(n: Int) extends Expression
  case class Bexp(b: Boolean) extends Expression

  /*
  [ SELF = self(A)                                                            ]
  | SUPER = self(B)                                                           |
  | TYPES = \overline{ R (+)?= {(f: T)*} }                                    | % types
  | ADTS = \overline{ R (+)?= \overline{C {(f: T)*}} }                        | % ADTs
  [ FUNS = \overline{ m : (T -> T') = (lam (x : T). body) }                   ] % function defs
  */

  // Linkages
  sealed class Marker // either += or =
  case object PlusEq extends Marker // type extension marker
  case object Eq extends Marker // type definition marker
  case class Linkage(self: SelfFamily, sup: SelfFamily, types: Map[String, (Marker, RecType)],
                     defaults: Map[String, (Marker, Rec)], adts: Map[String, (Marker, ADT)],
                     funs: Map[String, (FunType, Lam)], cases: Map[String, (FunType, Map[String, Lam])])


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

  /*====================================== LINKAGE CONCATENATION  ======================================*/

  // Given a context of incomplete linkages, produce a complete linkage for some family path fpath
  // ASSUMPTION: linkages in K are incomplete
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
      case FamFun(path, name) => if (path == p1) then FamFun(p2, name) else FamFun(path, name)
      case App(e1, e2) => App(update_self_in_exp(e1, p1, p2), update_self_in_exp(e2, p1, p2))
      case Rec(m) => Rec(m.map{case (s, fex) => (s, update_self_in_exp(fex, p1, p2))})
      case Proj(exp, name) => Proj(update_self_in_exp(exp, p1, p2), name)
      case Inst(t, rec) =>
        Inst(update_self_in_type(t, p1, p2).asInstanceOf[FamType], update_self_in_exp(rec, p1, p2).asInstanceOf[Rec])
      case InstADT(t, cname, rec) =>
        InstADT(update_self_in_type(t, p1, p2).asInstanceOf[FamType], cname, update_self_in_exp(rec, p1, p2).asInstanceOf[Rec])
      case Match(exp, cases) =>
        Match(update_self_in_exp(exp, p1, p2),
          cases.map{case (s, l) => (s, update_self_in_exp(l, p1, p2).asInstanceOf[Lam])})
      case _ => e
    }
  }

  // concatenates two linkages
  // ASSUMPTION: lkgA is complete, lkgB is incomplete
  def concat(lkgA: Linkage, lkgB: Linkage): Linkage = {

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

    // Concat and create new, complete linkage
    // in a complete linkage, there's no need for cases  as we have already incorporated them during concatenation
    Linkage(lkgB.self, lkgA.self, concat_types(updated_types, lkgB.types),
      concat_defaults(updated_defaults, lkgB.defaults), concat_adts(updated_adts, lkgB.adts),
      concat_funs(updated_funs, lkgB.funs, lkgB.cases), null)
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

  // helper for updating existing matches with extra cases from child
  def extend_nth_match(body: Expression, pmid: Int, extras: Map[String, Lam], ctr: Int): Expression = {
    body match {
      // match case
      case Match(exp, cases) =>
        if (pmid == ctr) // this is the match we want to extend
        then {
          val new_cases = cases.++(extras)
          if (new_cases.size == cases.size + extras.size) // no duplicates here
          then Match(exp, new_cases)
          else throw new Exception("Attempting to duplicate constructors in extended match.")
        } else
          Match(extend_nth_match(exp, pmid, extras, ctr+1),
            cases.map{ case (s, l) => (s, extend_nth_match(l, pmid, extras, ctr+1).asInstanceOf[Lam])})
      // other cases
      case Lam(v, t, b) => Lam(v, t, extend_nth_match(b, pmid, extras, ctr))
      case App(e1, e2) => App(extend_nth_match(e1, pmid, extras, ctr), extend_nth_match(e2, pmid, extras, ctr))
      case Rec(f) => Rec(f.map{case (s, e) => (s, extend_nth_match(e, pmid, extras, ctr))})
      case Proj(e, n) => Proj(extend_nth_match(e, pmid, extras, ctr), n)
      case Inst(t, rec) => Inst(t, extend_nth_match(rec, pmid, extras, ctr).asInstanceOf[Rec])
      case InstADT(t, cn, rec) => InstADT(t, cn, extend_nth_match(rec, pmid, extras, ctr).asInstanceOf[Rec])
      case _ => body
    }
  }

  def concat_funs(funs1: Map[String, (FunType, Lam)],
                  funs2: Map[String, (FunType, Lam)],
                  cases: Map[String, (FunType, Map[String, Lam])]) : Map[String, (FunType, Lam)] = {
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
    var all_funs = (unchanged_parent_funs.++(overridden_funs)).++(new_funs)

    // Now we need to expand all matches using the cases in the child linkage
    for ((k,v) <- cases)
      var pmid = k.split('_').last // pattern match id isolated as a string
      var fun_name = k.substring(0, k.indexOfSlice(pmid) - 1) // function name isolated
      all_funs.get(fun_name) match { // get the info about this function that we need to extend
        case Some((funtype, Lam(x, t, body))) =>
          var newlam = Lam(x, t, extend_nth_match(body, pmid.toInt, v._2, 1)) // update the body with the extended match
          var updated_funs = all_funs + (fun_name -> (funtype, newlam)) // update the mapping
          all_funs = updated_funs // update original variable for all funs
        case _ => throw new Exception("Encountered cases for extension of non-existing function.")
      }

    all_funs // return this updated version
  }

  /*====================================== LINKAGE WELL-FORMEDNESS  ======================================*/

  // G is the typing context
  // K is the linkage context
  // ASSUMPTION: all linkages are complete
  def linkage_ok (lkg: Linkage, G: Map[String, Type], K: Map[FamilyPath, Linkage]): Boolean = {
    // forall (R = {(f: T)*}) in TYPES, WF({(f: T)*})
    (lkg.types.filter{case (s, (m, rt)) => !wf(rt, K)}.isEmpty &&

      // check that for every default record there is a type corresponding to it and the defaults typecheck
      lkg.defaults.filter{
        case (s, (m, r)) => !is_value(r) || // if the default is not a value or...
          (lkg.types.get(s) match {
            case Some(m, rt) => (rt != typInf(r, G, K).asInstanceOf[RecType]) // ...or the default has the wrong type
            case _ => assert(false)
          })
      }.isEmpty &&

      // forall (R = \overline{C {(f: T)*}}) in ADTS, WF({(f: T)*})
      lkg.adts.filter{ case (s, (m, adt)) =>
        adt.cs.exists{ case (s, rt) => !wf(rt, K)} // exists an ADT that's not well-formed
      }.isEmpty &&

      // forall (m : (T -> T') = (lam (x : T). body)),
      //    G |- lam (x : T). body : T -> T'
      lkg.funs.filter{ case (s, (ft, lam)) => !typCheck(lam, ft, G, K)}.isEmpty)
  }


  /*====================================== PUTTING IT ALL TOGETHER  ======================================*/

  // TODO: function that takes a program, performs the syntactic transformations, parses families into incomplete
  // linkages, then concatenates to complete linkages, then does linkage checking, and returns a context of complete
  // linkages for use with type checking and so on

} // eof