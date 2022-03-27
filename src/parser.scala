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
  lazy val pFunctionName: Parser[String] = not(reserved) ~> """[a-zA-Z_0-9]+""".r
  // field names can also be constructor names or underscores because of cases
  // is this a problem to allow this for all records?
  lazy val pFieldName: Parser[String] = not(reserved) ~> """(([a-z0-9])+)|(([A-Z][a-z0-9]*)+)|_""".r
  lazy val pConstructorName: Parser[String] = not(reserved) ~> """([A-Z][a-z0-9]*)+""".r

  // FAMILY PATHS
  lazy val pPath: PackratParser[Path] =
    pPath ~ pFamilyName ^^ { case p~f => AbsoluteFamily(p, Family(f)) }
    | pFamilyName ^^ { f => AbsoluteFamily(Sp(Prog), Family(f)) }
    | pSelfPath ^^ { Sp.apply }

  lazy val pSelfPath: PackratParser[SelfPath] =
    kwSelf ~> between("(", ")",
      pSelfPath ~ ("." ~> pFamilyName) ^^ { case p~f => SelfFamily(p, Family(f)) }
      | pFamilyName ^^ { f => SelfFamily(Prog, Family(f)) }
    )

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
    pPath ~ ("." ~> pTypeName) ^^ { case p~t => FamType(Some(p), t)} |
    "." ~> pTypeName ^^ { t => FamType(None, t)} | // TODO: do we still want this?
    pTypeName ^^ { t => FamType(None, t)}

  lazy val pNType: PackratParser[Type] = kwN ^^^ N
  lazy val pBType: PackratParser[Type] = kwB ^^^ B

  // separate parser for record field definition with defaults
  lazy val pDefaultRecField: PackratParser[(String, (Type, Option[Expression]))] =
    pFieldName ~ (":" ~> pType) ~ ("=" ~> exp).? ^^ { case f~t~oe => f->(t->oe) }
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
    kwLam ~> between("(", ")", pExpVar ~ (":" ~> pType)) ~ ("." ~> exp) ^^ { case v~t~body => Lam(v, t, body) }

  lazy val pExpFamFun: PackratParser[FamFun] =
    pPath ~ ("." ~> pFunctionName) ^^ { case p~n => FamFun(Some(p), n) }
    | "." ~> pFunctionName ^^ { n => FamFun(None, n) }

  lazy val pExpFamCases: PackratParser[FamCases] =
    between("<", ">", pPath ~ ("." ~> pFunctionName)) ^^ { case p~n => FamCases(Some(p), n) }
    | between("<", ">", "." ~> pFunctionName) ^^ { n => FamCases(None, n) } // TODO: do we still want this?

  lazy val pExpApp: PackratParser[App] = exp ~ exp ^^ { case e~g => App(e, g) }
  lazy val pExpProj: PackratParser[Proj] = exp ~ "." ~ pFieldName ^^ {case e~_~n => Proj(e, n)}
  lazy val pFieldVal: PackratParser[(String, Expression)] = pFieldName ~ "=" ~ exp ^^ {case k~_~v => k -> v}
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

  // the second expression will be an application of exp_famcases to a record of arguments
  lazy val pExpMatch: PackratParser[Match] =
    kwMatch ~> exp ~ (kwWith ~> pExpApp) ^^ { case e~g => Match(e, g) }

  lazy val exp: PackratParser[Expression] =
    pExpMatch | pExpProj | pExpInstAdt | pExpInst | pExpApp | pExpRec
    | pExpFamFun | pExpFamCases
    | pExpLam | pExpBool | pExpNat
    | pExpVar
    | between("(", ")", exp)

  // MARKERS
  lazy val pMarker: PackratParser[Marker] =
    "=" ^^ {_ => Eq} | "+=" ^^ {_ => PlusEq}

  // DEFINITIONS
  lazy val pTypeDef: PackratParser[(String, (Marker, (RecType, Rec)))] =
    kwType ~> pTypeName ~ pMarker ~ pDefaultRecType ^^ { case n~m~rt => n -> (m -> rt) }
  lazy val pAdtDef: PackratParser[(String, ADT)] =
    pAdt ^^ { a => a.name -> a }

  lazy val pFunDef: PackratParser[(String, Fun)] =
    kwVal ~> pFunctionName ~ (":" ~> optBetween("(", ")", pFunType)) ~ ("=" ~> pExpLam) ^^ {
      case n~t~b => n -> FunDeclared(n, t, b)
    }

  lazy val pMatchType: PackratParser[FamType] = between("<", ">", pFamType)
  // mt = match type, m = marker, ft = funtype, lam = body
  lazy val pCasesDef: PackratParser[(String, Cases)] =
    kwCases ~> pFunctionName ~ pMatchType ~ (":" ~> optBetween("(", ")", pFunType)) ~ pMarker ~ pExpLam ^^ {
      case n~mt~ft~m~b => n -> CasesDeclared(n, mt, ft, m, b)
    }

  // A family can extend another family. If it does not, the parent is None.
  lazy val pFamDef: PackratParser[Linkage] =
    (kwFamily ~> pFamilyName) ~ (kwExtends ~> pPath).? ~ between("{", "}",
      rep(pTypeDef) ~ rep(pAdtDef) ~ rep(pFunDef) ~ rep(pCasesDef) ~ rep(pFamDef)
    ) ^^ {
      case a~supFam~(typs~adts~funs~cases~nestedLkgs) =>
        val nestedList = nestedLkgs.map{lkg => (lkg.path, lkg)}
        if hasDuplicateName(typs) then throw new Exception("Parsing duplicate type names.")
        else if hasDuplicateName(adts) then throw new Exception("Parsing duplicate ADT names.")
        else if hasDuplicateName(funs) then throw new Exception("Parsing duplicate function names.")
        else if hasDuplicateName(cases) then throw new Exception("Parsing duplicate cases names.")
        else if hasDuplicateName(nestedList) then throw new Exception("Parsing duplicate family names.")
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
          val selfPath = SelfFamily(Prog, Family(a))
          val typedefs = typs.collect{case (s, (m, (rt, r))) => (s, (m, rt))}.toMap
          val defaults = typs.collect{case (s, (m, (rt, r))) => (s, (m, r))}.toMap
          Linkage(
            Sp(selfPath),
            selfPath,
            supFam,
            typedefs,
            defaults,
            adts.toMap,
            funs.toMap,
            cases.toMap,
            nestedList.toMap
          )
        }
      }

  lazy val pProgram: PackratParser[Map[Path, Linkage]] =
    rep(pFamDef) ^^ {
      lst => Map(
        Sp(Prog) -> Linkage(
          Sp(Prog), Prog, None, Map(), Map(), Map(), Map(), Map(),
          lst.map{lkg => (lkg.path, lkg)}.toMap
        )
      )
    }
}

object TestFamParser extends FamParser {
  def parse0[T](p: PackratParser[T], inp: String): ParseResult[T] = parseAll(phrase(p), inp)
  def canParse[T](p: PackratParser[T], inp: String): Boolean = parse0(p, inp).successful
  def parseSuccess[T](p: PackratParser[T], inp: String): T = parse0(p, inp).get
}
