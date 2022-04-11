import famfun._

object PrettyPrint {

  def print_selfPath(sp: SelfPath): String = sp match {
    case Prog => "<>"
    case SelfFamily(p, f) => "self(" + print_selfPath(p) + "." + f + ")"
  }
  def print_path(p: Path) : String = {
    p match {
      case Sp(sp) => print_selfPath(sp)
      case AbsoluteFamily(p, f) => print_path(p) + "." + f
    }
  }

  def print_type(t: Type): String = {
    t match {
      case N => "N"
      case B => "B"
      case FunType(a, b) => "(" + print_type(a) + " -> " + print_type(b) + ")"
      case FamType(path, n) => path.map(print_path).getOrElse("None") + "." + n
      case RecType(fields) =>
        val printmap = fields.map{case (f, t) =>
          if fields.last == (f, t) then f + ": " + print_type(t)
          else f + ": " + print_type(t) + ", "}
        "{" + printmap.mkString + "}"
    }
  }

  def print_marker(m: Marker): String = {
    m match {
      case Eq => " = "
      case PlusEq => " += "
    }
  }

  def print_exp(e: Expression) : String = {
    e match {
      case Var(id) => id
      case Lam(v, t, body) => "lam (" + print_exp(v) + ": " + print_type(t) + "). " + print_exp(body)
      case FamFun(p, n) => p.map(print_path).getOrElse("None") + "." + n
      case FamCases(p, n) => "<" + p.map(print_path).getOrElse("None") + "." + n + ">"
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
    }
  }

  def print_adt(a: AdtDefn) : String = a match {
    case AdtDefn(name, marker, adtBody) =>
      "type " + name + print_marker(marker) +
        print_body(adtBody)(_.map {
          (c, r) => c + " " + print_type(r)
        }.mkString(" | ")) +
        "\n"
  }

  def print_body[B](body: DefnBody[B])(printB: B => String): String = {
    val DefnBody(defn, extendsFrom, furtherBindsFrom) = body
    val bPretty = defn.map(printB)
    s"[$bPretty, extends from: ${extendsFrom.map(print_path)}, further binds from: ${furtherBindsFrom.map(print_path)}]"
  }

  def print_lkg(lkg: Linkage) = {
    print("LINKAGE DEFINITION: \n\n")

    print("PATH: " + print_path(lkg.path) + "\n\n")

    print("SELF: " + print_selfPath(lkg.self) + "\n\n")

    print("SUPER: " + lkg.sup.map(print_path).getOrElse("None") + "\n\n")

    print("TYPES:\n")
    val typemap = lkg.types.view.mapValues{
      case TypeDefn(name, marker, typeBody) => "type " + name + print_marker(marker) +  print_body(typeBody)(print_type) + "\n"
    }
    print(typemap.mkString)
    print("\n\n")

    print("DEFAULTS:\n")
    val defmap = lkg.defaults.view.mapValues {
      case DefaultDefn(s, m, defaultBody) => "type " + s + print_marker(m) +  print_body(defaultBody)(print_exp) + "\n"
    }
    print(defmap.mkString)
    print("\n\n")

    print("ADTs:\n")
    val adtmap = lkg.adts.map{
      case (s, adt) => print_adt(adt) + "\n"
    }
    print(adtmap.mkString)
    print("\n\n")

    print("FUNS:\n")
    val funmap = lkg.funs.map{
      case (_, FunDefn(s, ft, body)) =>
        "val " + s + ": " + print_type(ft) + " = " + print_body(body)(print_exp) + "\n"
    }
    print(funmap.mkString)
    print("\n\n")

    print("CASES:\n")
    val casemap = lkg.depot.values.map {
      case CasesDefn(s, mt, ft, m, body) =>
        "cases " + s + "<" + print_type(mt) + ">" + ": " + print_type(ft) + print_marker(m) + print_body(body)(print_exp) + "\n"
    }
    print(casemap.mkString)
    print("\n\n")
  }
}