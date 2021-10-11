import famlang._

object PrettyPrint {

  def print_path(p: FamilyPath) : String = {
    p match {
      case SelfFamily(Family(f)) => "self(" + f + ")"
      case AbsoluteFamily(Family(f)) => f
      case _ => "None"
    }
  }

  def print_type(t: Type): String = {
    t match {
      case N => "N"
      case B => "B"
      case FunType(a, b) => "(" + print_type(a) + " -> " + print_type(b) + ")"
      case FamType(path, n) => print_path(path) + "." + n
      case RecType(fields) =>
        val printmap = fields.map{case (f, t) =>
          if ((f, t) == fields.last) then f + ": " + print_type(t)
          else f + ": " + print_type(t) + ", "}
        "{" + printmap.mkString + "}"
      case _ => "None"
    }
  }

  def print_marker(m: Marker): String = {
    m match {
      case Eq => " = "
      case PlusEq => " += "
      case _ => "None"
    }
  }

  def print_exp(e: Expression) : String = {
    e match {
      case Var(id) => id
      case Lam(v, t, body) => "lam (" + print_exp(v) + ": " + print_type(t) + "). " + print_exp(body)
      case FamFun(p, n) => print_path(p) + "." + n
      case FamCases(p, n) => "<" + print_path(p) + "." + n + ">"
      case App(e, g) => "(" + print_exp(e) + " " + print_exp(g) + ")"
      case Rec(fields) =>
        val printmap = fields.map{case (f, e) =>
          if ((f, e) == fields.last) then f + " = " + print_exp(e)
          else f + " = " + print_exp(e) + ", "}
        "{"+ printmap.mkString + "}"
      case Proj(e, n) => print_exp(e) + "." + n
      case Inst(t, r) => print_type(t) + " (" + print_exp(r) + ")"
      case InstADT(t, c, r) => print_type(t) + " (" + c + " " + print_exp(r) + ")"
      case Match(e, g) => "match " + print_exp(e) + " with " + print_exp(g)
      case Nexp(n) => n.toString()
      case Bexp(b) => b.toString()
      case _ => "None"
    }
  }

  def print_adt(a: ADT) : String = {
    val amap = a.cs.map{case (c, r) =>
      if ((c, r) == a.cs.last) then c + " " + print_type(r)
      else c + " " + print_type(r) + " | "}
    amap.mkString
  }

  def print_lkg(lkg: Linkage) = {
    print("LINKAGE DEFINITION: \n\n")

    print("SELF: " + print_path(lkg.self) + "\n\n")

    print("SUPER: " + print_path(lkg.sup) + "\n\n")

    print("TYPES: ")
    val typemap = lkg.types.map{
      case (s, (m, t)) => "type " + s + print_marker(m) +  print_type(t) + "\n"
    }
    print(typemap.mkString)
    print("\n\n")

    print("DEFAULTS: ")
    val defmap = lkg.defaults.map{
      case (s, (m, r)) => "type " + s + print_marker(m) +  print_exp(r) + "\n"
    }
    print(defmap.mkString)
    print("\n\n")

    print("ADTs: ")
    val adtmap = lkg.adts.map{
      case (s, (m, adt)) => "type " + s + print_marker(m) +  print_adt(adt) + "\n"
    }
    print(adtmap.mkString)
    print("\n\n")

    print("FUNS: ")
    val funmap = lkg.funs.map{
      case (s, (ft, lam)) => "val " + s + ": " + print_type(ft) + " = " + print_exp(lam) + "\n"
    }
    print(funmap.mkString)
    print("\n\n")

    print("CASES: ")
    val casemap = lkg.depot.map{
      case (s, (mt, m, ft, lam)) => "cases " + s + "<" + print_type(mt) + ">" + ": " +
        print_type(ft) + print_marker(m) + print_exp(lam) + "\n"
    }
    print(casemap.mkString)
    print("\n\n")
  }
}