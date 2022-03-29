import scala.util.parsing.combinator.*
import famfun._

/*
Family A (extends P)? {
    type R (+)?= {(f: T = e)*}                  % extensible records w/ defaults
    type R (+)?= \overline{C {(f: T)*}}         % extensible ADTs
    val m : (T -> T') = (lam (x : T). body)     % functions w/ inputs
    cases r <a.R> : {(f:T)*} -> {(C': T'->T'')*} =
        lam (x:{(f:T)*}). {(C' = lam (x: T'). body)*}
    Family C (extends P')? { ... }               % nested families
}
 */

class FamParser extends RegexParsers with PackratParsers {

  def hasDuplicateName[K, V](kvList: List[(K, V)]): Boolean = kvList.size != kvList.distinctBy(_._1).size

  def unSnoc[T](list: List[T]): (List[T], T) = list match {
    case Nil => throw new Exception("Cannot unSnoc an empty list")
    case List(x) => (List(), x)
    case x :: xs =>
      val (us, u) = unSnoc(xs)
      (x::us, u)
  }

  def between[T, A, B](l: Parser[A], r: Parser[B], mid: Parser[T]): Parser[T] = l ~> mid <~ r
  def optBetween[T, A, B](l: Parser[A], r: Parser[B], mid: Parser[T]): Parser[T] = between(l, r, mid) | mid

  // KEYWORDS
  val kwMatch: Parser[String] = "match\\b".r
  val kwWith: Parser[String] = "with\\b".r
  val kwTrue: Parser[String] = "true\\b".r
  val kwFalse: Parser[String] = "false\\b".r
  val kwLam: Parser[String] = "lam\\b".r
  val kwType: Parser[String] = "type\\b".r
  val kwVal: Parser[String] = "val\\b".r
  val kwFamily: Parser[String] = "Family\\b".r
  val kwExtends: Parser[String] = "extends\\b".r
  val kwN: Parser[String] = "N\\b".r
  val kwB: Parser[String] = "B\\b".r
  val kwSelf: Parser[String] = "self\\b".r
  val kwCases: Parser[String] = "cases\\b".r

  val reserved: Parser[String] = kwMatch | kwWith | kwTrue | kwFalse | kwLam  | kwType | kwVal | kwFamily
    | kwExtends | kwN | kwB | kwSelf | kwCases

  // NAMES
  lazy val pVarName: Parser[String] = not(reserved) ~> """[a-z_]+""".r
  lazy val pFamilyName: Parser[String] = not(reserved) ~> """([A-Z][a-z]*)+""".r
  lazy val pTypeName: Parser[String] = not(reserved) ~> """([A-Z][a-z]*)+""".r
  lazy val pFunctionName: Parser[String] = not(reserved) ~> """[a-z][a-zA-Z_0-9]*""".r
  // field names can also be constructor names or underscores because of cases
  // is this a problem to allow this for all records?
  lazy val pFieldName: Parser[String] = not(reserved) ~> """(([a-z0-9])+)|(([A-Z][a-z0-9]*)+)|_""".r
  lazy val pConstructorName: Parser[String] = not(reserved) ~> """([A-Z][a-z0-9]*)+""".r

  // FAMILY PATHS
  lazy val pPath: PackratParser[Path] =
    pPath ~ ("." ~> pFamilyName) ^^ { case p~f => AbsoluteFamily(p, f) }
    | pFamilyName ^^ { f => AbsoluteFamily(Sp(Prog), f) }
    | pSelfPath ^^ { Sp.apply }

  lazy val pSelfPath: PackratParser[SelfPath] =
    kwSelf ~> between("(", ")",
      pSelfPath ~ ("." ~> pFamilyName) ^^ { case p~f => SelfFamily(p, f) }
      | pFamilyName ^^ { f => SelfFamily(Prog, f) }
    )

  // This is needed for things of the form `path.(family/type)name`,
  // since when `path` is absolute, we get something like `[self(A).]C.D.T`
  // and `pPath` itself cannot tell when to stop (will consume `T`)
  lazy val pPathExtra: PackratParser[(Path, String)] =
    // Absolute path prefix (note that this can start with a single self(...))
    (pSelfPath <~ ".").? ~ pFamilyName ~ ("." ~> rep1sep(pFamilyName, ".")) ^^ {
      case _~_~Nil => throw new Exception("Should be impossible")
      case optSelfHead~n~ns =>
        // n :: ns has length at least 2
        val (namesInit, namesLast) = unSnoc(n::ns)
        val inner: Path = Sp(optSelfHead.getOrElse(Prog))
        (namesInit.foldLeft(inner) { AbsoluteFamily.apply }, namesLast)
    }
    // Self path prefix
    | pSelfPath ~ ("." ~> pFamilyName) ^^ {
      case sp~n => (Sp(sp), n)
    }

  // TYPES
  lazy val pFunType: PackratParser[FunType] = pType ~ ("->" ~> pType) ^^ { case inp~out => FunType(inp, out) }
  lazy val pRecField: PackratParser[(String, Type)] = pFieldName ~ (":" ~> pType) ^^ { case f~t => f->t }
  lazy val pRecType: PackratParser[RecType] = between("{", "}", repsep(pRecField, ",") ^^ {
    lst =>
      if hasDuplicateName(lst) // disallow records with duplicate fields
      then throw new Exception("Parsing a record type with duplicate fields.")
      else RecType(lst.toMap)
  })
  lazy val pFamType: PackratParser[FamType] =
    pPathExtra ^^ { case (p,t) => FamType(Some(p), t) }
    | pTypeName ^^ { t => FamType(None, t) }

  lazy val pNType: PackratParser[Type] = kwN ^^^ N
  lazy val pBType: PackratParser[Type] = kwB ^^^ B

  // separate parser for record field definition with defaults
  lazy val pDefaultRecField: PackratParser[(String, (Type, Option[Expression]))] =
    pFieldName ~ (":" ~> pType) ~ ("=" ~> pExp).? ^^ { case f~t~oe => f->(t->oe) }
  // separate parser for record type definition with defaults
  lazy val pDefaultRecType: PackratParser[(RecType, Rec)] = "{"~> repsep(pDefaultRecField, ",") <~"}" ^^ {
    lst =>
      if hasDuplicateName(lst) // disallow records with duplicate fields
      then throw new Exception("Parsing a record type with duplicate fields.")
      else {
        val type_fields = lst.collect{case (s, (t, _)) => (s, t)}.toMap;
        val defaults = lst.collect{case (s, (t, Some(e))) => (s, e)}.toMap;
        RecType(type_fields) -> Rec(defaults)
      }
  }

  lazy val pType: PackratParser[Type] = pFunType | pRecType | pFamType | pNType | pBType | between("(", ")", pType)

  // ADTS
  lazy val pAdtConstructor: PackratParser[(String, RecType)] = pConstructorName ~ pRecType ^^ { case k ~ v => k -> v }
  lazy val pAdt: PackratParser[ADT] =
    (kwType ~> pTypeName) ~ pMarker ~ repsep(pAdtConstructor, "|") ^^ {
      case n~m~cs =>
        if hasDuplicateName(cs) // disallow ADTs with duplicate constructors
        then throw new Exception("Parsing an ADT with duplicate constructors.")
        else ADT(n, m, cs.toMap)
    }

  // EXPRESSIONS
  lazy val pExpBool: PackratParser[Bexp] = kwTrue ^^^ Bexp(true) | kwFalse ^^^ Bexp(false)
  lazy val pExpNat: PackratParser[Nexp] = """(0|[1-9]\d*)""".r ^^ { n => Nexp(n.toInt) }
  lazy val pExpVar: PackratParser[Var] = pVarName ^^ { id => Var(id)}
  lazy val pExpLam: PackratParser[Lam] =
    kwLam ~> between("(", ")", pExpVar ~ (":" ~> pType)) ~ ("." ~> pExp) ^^ { case v~t~body => Lam(v, t, body) }

  // Implicit self path functions are parsed as Vars first, then resolved later.
  lazy val pExpFamFun: PackratParser[FamFun] =
    pPath ~ ("." ~> pFunctionName) ^^ { case p~n => FamFun(Some(p), n) }

  lazy val pExpFamCases: PackratParser[FamCases] =
    between("<", ">", (pPath <~ ".").? ~ pFunctionName) ^^ { case p~n => FamCases(p, n) }

  lazy val pExpApp: PackratParser[App] = pExp ~ pExp ^^ { case e~g => App(e, g) }
  lazy val pExpProj: PackratParser[Proj] = pExp ~ "." ~ pFieldName ^^ {case e~_~n => Proj(e, n)}
  lazy val pFieldVal: PackratParser[(String, Expression)] = pFieldName ~ "=" ~ pExp ^^ {case k~_~v => k -> v}
  lazy val pExpRec: PackratParser[Rec] = "{"~> repsep(pFieldVal, ",") <~"}" ^^ {
    lst =>
      if hasDuplicateName(lst) // disallow records with duplicate fields
      then throw new Exception("Parsing a record with duplicate fields.")
      else Rec(lst.toMap)
  }

  lazy val pExpInst: PackratParser[Inst] =
    pFamType ~ between("(", ")", pExpRec) ^^ { case t~r => Inst(t, r) }
  lazy val pExpInstAdt: PackratParser[InstADT] =
    pFamType ~ between("(", ")", pConstructorName ~ pExpRec) ^^ { case t~(c~r) => InstADT(t, c, r) }

  lazy val pExpMatch: PackratParser[Match] =
    kwMatch ~> pExp ~ (kwWith ~> pExp) ^^ { case e~g => Match(e, g) }

  lazy val pExp: PackratParser[Expression] =
    pExpMatch | pExpProj | pExpInstAdt | pExpInst | pExpApp | pExpRec
    | pExpFamFun | pExpFamCases
    | pExpLam | pExpBool | pExpNat
    | pExpVar
    | between("(", ")", pExp)

  // MARKERS
  lazy val pMarker: PackratParser[Marker] =
    "=" ^^ {_ => Eq} | "+=" ^^ {_ => PlusEq}

  // DEFINITIONS
  lazy val pTypeDef: PackratParser[(String, (Marker, (RecType, Rec)))] =
    kwType ~> pTypeName ~ pMarker ~ pDefaultRecType ^^ { case n~m~rt => n -> (m -> rt) }
  lazy val pAdtDef: PackratParser[(String, ADT)] =
    pAdt ^^ { a => a.name -> a }

  lazy val pFunDef: PackratParser[(String, FunDefn)] =
    kwVal ~> pFunctionName ~ (":" ~> optBetween("(", ")", pFunType)) ~ ("=" ~> pExp) ^^ {
      case n~t~b => n -> FunDefn(n, t, BodyDeclared(b))
    }

  lazy val pMatchType: PackratParser[FamType] = between("<", ">", pFamType)
  // mt = match type, m = marker, ft = funtype, lam = body
  lazy val pCasesDef: PackratParser[(String, CasesDefn)] =
    kwCases ~> pFunctionName ~ pMatchType ~ (":" ~> optBetween("(", ")", pFunType)) ~ pMarker ~ pExp ^^ {
      case n~mt~ft~m~b => n -> CasesDefn(n, mt, ft, m, BodyDeclared(b))
    }

  // A family can extend another family. If it does not, the parent is None.
  def pFamDef(selfPrefix: SelfPath): PackratParser[(String, Linkage)] = {
    for {
      fam <- kwFamily ~> pFamilyName
      curSelfPath = SelfFamily(selfPrefix, fam)
      supFam <- (kwExtends ~> pPath).?
      typs~adts~funs~cases~nested <- between("{", "}",
        rep(pTypeDef) ~ rep(pAdtDef) ~ rep(pFunDef) ~ rep(pCasesDef) ~ rep(pFamDef(curSelfPath))
      )
    } yield {
      if hasDuplicateName(typs) then throw new Exception("Parsing duplicate type names.")
      else if hasDuplicateName(adts) then throw new Exception("Parsing duplicate ADT names.")
      else if hasDuplicateName(funs) then throw new Exception("Parsing duplicate function names.")
      else if hasDuplicateName(cases) then throw new Exception("Parsing duplicate cases names.")
      else if hasDuplicateName(nested) then throw new Exception("Parsing duplicate family names.")
      else {
        supFam match {
          case Some(b) =>
            /* TODO: Do this in the extend cycle check in later phase.
            if (a == b) then
              throw new Exception("Parsing a family that extends itself.")
            else
             */
            // family extends another
            if typs.exists{case (s, (m, (rt, r))) => (m == PlusEq) && (rt.fields.keySet != r.fields.keySet)} then
              throw new Exception("In a type extension, not all fields have defaults.");
            else ()
          // family does not extend another
          case None => ()
        }
        val typedefs = typs.collect{case (s, (m, (rt, r))) => (s, (m, rt))}.toMap
        val defaults = typs.collect{case (s, (m, (rt, r))) => (s, (m, r))}.toMap

        fam -> Linkage(
          Sp(curSelfPath),
          curSelfPath,
          supFam,
          typedefs,
          defaults,
          adts.toMap,
          funs.toMap,
          cases.toMap,
          nested.toMap
        )
      }
    }
  }

  // TODO: should we call the resolution functions directly here?
  lazy val pProgram: PackratParser[Map[Path, Linkage]] =
    rep(pFamDef(Prog)) ^^ {
      fams => Map(
        Sp(Prog) -> Linkage(
          Sp(Prog), Prog, None, Map(), Map(), Map(), Map(), Map(),
          fams.toMap
        )
      )
    }

  // A pass to resolve whether things parsed as variables are actually variables or function names.
  // Also resolves implicit self paths for functions.
  // TODO: resolve implicit self paths for everything here?
  def resolveParsedVars(l: Linkage): Linkage = l.copy(
    defaults =
      l.defaults.view
        .mapValues { case (m, r) => m -> resolveParsedVarsRec(l.self)(Set.empty)(r) }
        .toMap,
    funs =
      l.funs.view
        .mapValues { f => resolveParsedVarsFunDefn(l.self)(Set.empty)(f) }
        .toMap,
    depot =
      l.depot.view
        .mapValues { c => resolveParsedVarsCasesDefn(l.self)(Set.empty)(c) }
        .toMap,
    nested =
      l.nested.view
        .mapValues { nl => resolveParsedVars(nl) }
        .toMap
  )
  def resolveParsedVarsRec(curSelf: SelfPath)(boundVars: Set[String])(r: Rec): Rec = r.copy(
    fields =
      r.fields.view
        .mapValues(resolveParsedVarsExpression(curSelf)(boundVars))
        .toMap
  )
  def resolveParsedVarsFunDefn(curSelf: SelfPath)(boundVars: Set[String])(f: FunDefn): FunDefn = f.copy(
    body = resolveParsedVarsDefnBody(curSelf)(boundVars)(f.body)
  )
  def resolveParsedVarsCasesDefn(curSelf: SelfPath)(boundVars: Set[String])(c: CasesDefn): CasesDefn = c.copy(
    body = resolveParsedVarsDefnBody(curSelf)(boundVars)(c.body)
  )
  def resolveParsedVarsDefnBody(curSelf: SelfPath)(boundVars: Set[String])(b: DefnBody): DefnBody = b match {
    case BodyDeclared(defined) => BodyDeclared(resolveParsedVarsExpression(curSelf)(boundVars)(defined))
    case BodyInherited(_) => b
  }
  def resolveParsedVarsExpression(curSelf: SelfPath)(boundVars: Set[String])(e: Expression): Expression = e match {
    case Var(id) if !boundVars.contains(id) => FamFun(Some(Sp(curSelf)), id)
    case Lam(v, t, body) => Lam(v, t, resolveParsedVarsExpression(curSelf)(boundVars + v.id)(body))
    case App(e1, e2) => App(
      resolveParsedVarsExpression(curSelf)(boundVars)(e1),
      resolveParsedVarsExpression(curSelf)(boundVars)(e2)
    )
    case r@Rec(_) => resolveParsedVarsRec(curSelf)(boundVars)(r)
    case Proj(e, name) => Proj(resolveParsedVarsExpression(curSelf)(boundVars)(e), name)
    case Inst(t, rec) => Inst(t, resolveParsedVarsRec(curSelf)(boundVars)(rec))
    case InstADT(t, cname, rec) => InstADT(t, cname, resolveParsedVarsRec(curSelf)(boundVars)(rec))
    case Match(e, g) => Match(
      resolveParsedVarsExpression(curSelf)(boundVars)(e),
      resolveParsedVarsExpression(curSelf)(boundVars)(g)
    )
    case _ => e
  }
}

object TestFamParser extends FamParser {
  def parse0[T](p: PackratParser[T], inp: String): ParseResult[T] = parseAll(phrase(p), inp)
  def canParse[T](p: PackratParser[T], inp: String): Boolean = parse0(p, inp).successful
  def parseSuccess[T](p: PackratParser[T], inp: String): T = parse0(p, inp).get
}
