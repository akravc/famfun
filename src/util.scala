import famfun._

object PrettyPrint {
  def print_selfPath(sp: SelfPath): String = sp match {
    case Prog => "<>"
    case SelfFamily(Sp(p), f) => "self(" + print_selfPath(p) + "." + f + ")"
  }
  def print_path(p: Path) : String = {
    p match {
      case Sp(sp) => print_selfPath(sp)
      case AbsoluteFamily(p, f) => print_path(p) + "." + f
    }
  }

  def print_type(t: Type): String = {
    t match {
      case NType => "N"
      case BType => "B"
      case StringType => "String"
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
      case NConst(n) => n.toString
      case ABinExp(a1, op, a2) => s"(${print_exp(a1)} ${showAOp(op)} ${print_exp(a2)})"
      case BConst(b) => b.toString
      case BBinExp(e1, op, e2) => s"(${print_exp(e1)} ${showBOp(op)} ${print_exp(e2)})"
      case BNot(e) => s"!${print_exp(e)}"
      case IfThenElse(condExpr, ifExpr, elseExpr) =>
        s"if ${print_exp(condExpr)} then ${print_exp(ifExpr)} else ${print_exp(elseExpr)}"
      case StringLiteral(s) => s"\"$s\""
      case StringInterpolated(interpolated) =>
        val inner: String = interpolated.map {
          case StringComponent(str) => str
          case InterpolatedComponent(exp) => s"$${${print_exp(exp)}}"
        }.mkString
        s"s\"$inner\""
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

object MapOps {
  def traverseWithKeyMap[K, V, E, W](m: Map[K, V])(f: (K, V) => Either[E, W]): Either[E, Map[K, W]] = {
    val kvpList: List[(K, V)] = m.toList
    kvpList.foldLeft(Right(List.empty[(K, W)]).withLeft[E]) {
      case (a, (curKey, curVal)) => for {
        accList <- a
        curValApplied <- f(curKey, curVal)
      } yield (curKey, curValApplied) :: accList
    }.map(_.toMap)
  }
  def traverseMap[K, V, E, W](m: Map[K, V])(f: V => Either[E, W]): Either[E, Map[K, W]] = {
    traverseWithKeyMap(m)((_: K, v: V) => f(v))
  }
  
  def unionWithM[K, V, E](m1: Map[K, V], m2: Map[K, V])(f: (V, V) => Either[E, V])(implicit ordK: Ordering[K]): Either[E, Map[K, V]] = {
    m2.toList.foldLeft(Right(m1).withLeft[E]) {
      case (eAccMap, (curK, curV)) => for {
        accMap <- eAccMap
        result <- (accMap.get(curK) match {
          case None => Right(curV)
          case Some(existingV) => f(existingV, curV)
        }).map(resultV => accMap + (curK -> resultV))
      } yield result
    }
  }
}

object OptionOps {
  def firstSome[T](opt1: Option[T], opt2: => Option[T]): Option[T] = opt1 match {
    case None => opt2
    case Some(_) => opt1
  }
  def lastSome[T](opt1: => Option[T], opt2: Option[T]): Option[T] = opt2 match {
    case None => opt1
    case Some(_) => opt2
  }
}
