//import TestFamParser._
//import famfun._

object famfun_translate {

  /* TODO: uncomment
  /* ===================== PATHS ===================== */
  def trans_path(p: FamilyPath): String = {
    p match {
      case SelfFamily(f) => f.name
      case AbsoluteFamily(f) => f.name
      case _ => "null"
    }
  }

  /* ===================== TYPES ===================== */
  def trans_type(t: Type): String = {
    t match {
      case N => "N"
      case B => "B"
      case FamType(a, r) => trans_path(a) + "." + r
      case FunType(i, o) => "(" + trans_type(i) + " -> " + trans_type(o) + ")"
      case RecType(fields) =>
        val printmap = fields.map{case (f, t) =>
          if ((f, t) == fields.last) then f + ": " + trans_type(t)
          else f + ": " + trans_type(t) + ", "}
        "{" + printmap.mkString + "}"
      case _ => "null"
    }
  }

  /* ===================== EXPRESSIONS ===================== */
  def trans_exp(exp: Expression, K: Map[FamilyPath, Linkage]): String = {
    exp match {
      case Var(x) => x
      case Nexp(n) => n.toString()
      case Bexp(b) => b.toString()
      case Lam(x, t, body) => "lam (" + trans_exp(x, K) + ": " + trans_type(t) + "). " + trans_exp(body, K)
      case FamFun(a, m) => trans_path(a) + "." + m
      case App(e, g) => "(" + trans_exp(e, K) + " " + trans_exp(g, K) + ")"
      case Rec(fields) =>
        val printmap = fields.map{case (f, e) =>
          if ((f, e) == fields.last) then f + " = " + trans_exp(e, K)
          else f + " = " + trans_exp(e, K) + ", "}
        "{" + printmap.mkString + "}"
      case Proj(e, f) => trans_exp(e, K) + "." + f
      case Inst(t, r) => trans_type(t) + "(" + trans_exp(r, K) + ")"
      case InstADT(t, c, r) => trans_type(t) + "(" + c + " " + trans_exp(r, K) + ")"
      case Match(e, g) =>
        g match {
          // has to be an application of cases to a record of arguments
          case App(FamCases(a, r), Rec(fields)) =>
            "(match " + trans_exp(e, K) + " with \n" + trans_cases_def(a, r, K) + ") " + trans_exp(Rec(fields), K)
          case _ => throw new Exception("Improper match structure.")
        }
      case _ => "null"
    }
  }

  /* ===================== CASES DEFINITION ===================== */
  def trans_cases_def(a: FamilyPath, r: String, K: Map[FamilyPath, Linkage]): String = {
    K.get(a) match {
      case Some(lkg) =>
        lkg.depot.get(r) match {
          case Some(_, _, _, Lam(x, argtype, rec)) =>
            // needs to have proper structure here
            assert(rec.isInstanceOf[Rec]);
            var cases = ""
            val fields = rec.asInstanceOf[Rec].fields
            for (C <- fields.keySet) {
              fields.get(C) match {
                case Some(exp) =>
                  val handler = exp.asInstanceOf[Lam]
                  if (C == fields.head._1) then
                    cases = cases + C + " => " +
                    trans_exp(Lam(handler.v, handler.t, Lam(x, argtype, handler.body)), K) + "\n"
                  else
                    cases = cases + "| " + C + " => " +
                    trans_exp(Lam(handler.v, handler.t, Lam(x, argtype, handler.body)), K) + "\n"
                case _ => assert(false)
              }
            }
            return cases;
          case _ => assert(false)
        }
      case _ => assert(false)
    }
  }

  /* ===================== TYPE DEFINITION ===================== */

  def combine(rt: RecType, rec: Rec, K: Map[FamilyPath, Linkage]): String = {
    val printmap = rt.fields.map { case (f, t) =>
      rec.fields.get(f) match {
        case Some(default) =>
          if ((f, t) == rt.fields.last) then f + ": " + trans_type(t) + " = " + trans_exp(default, K)
          else f + ": " + trans_type(t) + " = " + trans_exp(default, K) + ", "
        case _ =>
          if ((f, t) == rt.fields.last) then f + ": " + trans_type(t)
          else f + ": " + trans_type(t) + ", "
      }
    }
    return "{" + printmap.mkString + "}"
  }

  def trans_typedef(typename: String, lkg: Linkage, K: Map[FamilyPath, Linkage]): String = {
    lkg.types.get(typename) match {
      case Some(_, rt) =>
        lkg.defaults.get(typename) match {
          case Some(_, rec) =>
            return "type " + typename + " = " + combine(rt, rec, K)
          case _ => return "type " + typename + " = " + trans_type(rt)
        }
      case _ => assert(false)
    }
  }

  /* ===================== ADT DEFINITION ===================== */


  def trans_adt(adt: ADT): String = {
    val printmap = adt.cs.map { case (c, rt) =>
      if ((c, rt) == adt.cs.last) then c + " " + trans_type(rt)
      else c + " " + trans_type(rt) + " | "
    }
    return printmap.mkString
  }

  def trans_adtdef(typename: String, lkg: Linkage): String = {
    lkg.adts.get(typename) match {
      case Some(_, adt) =>
        return "type " + typename + " = " + trans_adt(adt)
      case _ => assert(false)
    }
  }


  /* ===================== FUNCTION DEFINITION ===================== */
  def trans_fundef(funname: String, lkg: Linkage, K: Map[FamilyPath, Linkage]): String = {
    lkg.funs.get(funname) match {
      case Some(ftype, lam) =>
        "val " + funname + " " + trans_type(ftype) + " = " + trans_exp(lam, K)
      case _ => assert(false)
    }
  }


  /* ===================== TYPE, ADT, FUNCTION LISTS ===================== */
  def trans_list_type(lkg: Linkage, K: Map[FamilyPath, Linkage]): String = {
    var alltypes = ""
    for (typename <- lkg.types.keySet) {
      alltypes = alltypes + trans_typedef(typename, lkg, K) + "\n"
    }
    return alltypes
  }

  def trans_list_adt(lkg: Linkage): String = {
    var alladts = ""
    for (typename <- lkg.adts.keySet) {
      alladts = alladts + trans_adtdef(typename, lkg) + "\n"
    }
    return alladts
  }

  def trans_list_fun(lkg: Linkage, K: Map[FamilyPath, Linkage]): String = {
    var allfuns = ""
    for (funname <- lkg.funs.keySet) {
      allfuns = allfuns + trans_fundef(funname, lkg, K) + "\n"
    }
    return allfuns
  }

  def trans_fam (lkg: Linkage, K: Map[FamilyPath, Linkage]): String = {
    val fpath = lkg.self;
    "module " + trans_path(fpath) + " {" + "\n" +
      trans_list_type(lkg, K) +
      trans_list_adt(lkg) +
      trans_list_fun(lkg, K) +
      "}" + "\n"
  }

    def translate (usercode: String): String = {

      /* ================== PARSE PROGRAM, CREATE INCOMPLETE LINKAGES ================== */
      if (!canParse(program, usercode)) then {
        throw new Exception("Cannot parse the program.")
      }
      // context of incomplete linkages, fresh from the parser
      var map_inc: Map[FamilyPath, Linkage] = parseSuccess(program, usercode);

      /* ================== TRANSFORM INCOMPLETE LINKAGES (MISSING PATHS, UNFOLD WILDCARDS) ================== */
      // update all null paths with self paths (.T is parsed as a family type T with null family)
      map_inc = map_inc.map{case(p, lkg)=> (p, update_paths(lkg, null, lkg.self))};
      map_inc = map_inc.map{case(p, lkg)=> (p, unfold_wildcards(lkg, map_inc))};

      /* ================== BUILD COMPLETE LINKAGES BY CONCATENATION ================== */
      // for each linkage in the map, build a complete linkage
      var M = Map[FamilyPath, Linkage]()
      // for each incomplete linkage, build a complete one using memoization to remember previously computed stuff
      for (p <- map_inc.keySet) {
        map_inc.get(p) match {
          case Some(lkg) =>
            val (complete_lkg, updatedM) = complete_linkage(p, map_inc, M);
            M = updatedM;
          case _ => assert(false);
        }
      }

      // fill in the missing defaults
      M = M.map{case (p, lkg) => (p, fill_defaults_lkg(lkg, M))}

      val printmap = M.map { case (p, lkg) => trans_fam(lkg, M)}
      printmap.mkString
    }
  */
}