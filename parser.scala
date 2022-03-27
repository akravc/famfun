import scala.util.parsing.combinator.*
import famfun._

/*
Family A (extends B)? {
    type R (+)?= {(f: T = e)*}                  % extensible records w/ defaults
    type R (+)?= \overline{C {(f: T)*}}         % extensible ADTs
    val m : (T -> T') = (lam (x : T). body)     % functions w/ inputs
    cases r <a.R> : {(f:T)*} -> {(C': T'->T'')*} =
        lam (x:{(f:T)*}). {(C' = lam (x: T'). body)*}
    Family C (extends D)? { ... }               % nested families
}
 */

class FamParser extends RegexParsers with PackratParsers {
  // KEYWORDS
  val kwMatch = "match\\b".r
  val kwWith = "with\\b".r
  val kwTrue = "true\\b".r
  val kwFalse = "false\\b".r
  val kwLam = "lam\\b".r
  val kwType = "type\\b".r
  val kwVal = "val\\b".r
  val kwFamily = "Family\\b".r
  val kwExtends = "extends\\b".r
  val kwN = "N\\b".r
  val kwB = "B\\b".r
  val kwSelf = "self\\b".r
  val kwCases = "cases\\b".r

  val reserved: Parser[String] = (kwMatch | kwWith | kwTrue | kwFalse | kwLam  | kwType | kwVal | kwFamily
    | kwExtends | kwN | kwB | kwSelf | kwCases)

  // NAMES
  def var_name: Parser[String] = not(reserved) ~> """[a-z_]+""".r ^^ { _.toString }
  def family_name: Parser[String] = not(reserved) ~> """([A-Z][a-z]*)+""".r ^^ { _.toString }
  def type_name: Parser[String] = not(reserved) ~> """([A-Z][a-z]*)+""".r ^^ { _.toString }
  def function_name: Parser[String] = not(reserved) ~> """[a-zA-Z_0-9]+""".r ^^ { _.toString }
  // field names can also be constructor names or underscores because of cases
  // is this a problem to allow this for all records?
  def field_name: Parser[String] = not(reserved) ~> """(([a-z0-9])+)|(([A-Z][a-z0-9]*)+)|_""".r ^^ { _.toString }
  def constructor_name: Parser[String] = not(reserved) ~> """([A-Z][a-z0-9]*)+""".r ^^ { _.toString }

  // FAMILY PATHS
  lazy val fampath: PackratParser[Path] =
    fampath ~ family_name ^^ { case p~f => AbsoluteFamily(p, Family(f)) }
    | family_name ^^ { case f => AbsoluteFamily(Sp(Prog), Family(f)) }
    | selfpath ^^ { Sp(_) }

  lazy val selfpath: PackratParser[SelfPath] =
    kwSelf ~> "(" ~> (
      selfpath ~ ("." ~> family_name) ^^ { case p~f => SelfFamily(p, Family(f)) }
      | family_name ^^ { case f => SelfFamily(Prog, Family(f)) }
    ) <~ ")"

  // TYPES
  lazy val funtype: PackratParser[FunType] = typ ~ "->" ~ typ ^^ { case inp~_~out => FunType(inp, out)}
  lazy val recfield: PackratParser[(String, Type)] =
    field_name ~ ":" ~ typ ^^ {case f~_~t => f->t}
  lazy val rectype: PackratParser[RecType] = "{"~> repsep(recfield, ",") <~"}" ^^
    {case lst =>
      if (lst.size == lst.unzip._1.distinct.size) // disallow records with duplicate fields
      then RecType(lst.toMap)
      else throw new Exception("Parsing a record type with duplicate fields.")}
  lazy val famtype: PackratParser[FamType] =
    fampath ~ "." ~ type_name ^^ { case p~_~t => FamType(p, t)} |
    "." ~> type_name ^^ { case t => FamType(null, t)} |
    type_name ^^ { case t => FamType(null, t)}

  lazy val ntype: PackratParser[Type] = kwN ^^ (_ => N)
  lazy val btype: PackratParser[Type] = kwB ^^ (_ => B)

  // separate parser for record field definition with defaults
  lazy val default_recfield: PackratParser[(String, (Type, Option[Expression]))] =
    field_name ~ ":" ~ typ ~ ("=".?) ~ (exp.?) ^^ {case f~_~t~_~oe => f->(t->oe)}
  // separate parser for record type definition with defaults
  lazy val default_rectype: PackratParser[(RecType, Rec)] = "{"~> repsep(default_recfield, ",") <~"}" ^^
    {case lst =>
      if (lst.size != lst.unzip._1.distinct.size) // disallow records with duplicate fields
      then throw new Exception("Parsing a record type with duplicate fields.")
      else {
        val type_fields = lst.collect{case (s, (t, _)) => (s, t)}.toMap;
        val defaults = lst.collect{case (s, (t, Some(e))) => (s, e)}.toMap;
        RecType(type_fields) -> Rec(defaults)
      }}

  lazy val typ: PackratParser[Type] = funtype | rectype | famtype | ntype | btype | "(" ~> typ <~ ")"

  // ADTS
  lazy val adt_constructor: PackratParser[(String, RecType)] = constructor_name ~ rectype ^^ {case k ~ v => k -> v}
  lazy val adt: PackratParser[ADT] =
    (kwType ~> type_name) ~ marker ~ repsep(adt_constructor, "|") ^^ {
      case n~m~cs =>
        if (cs.size == cs.distinctBy(_._1).size) // disallow ADTs with duplicate constructors
        then ADT(n, m, cs.toMap)
        else throw new Exception("Parsing an ADT with duplicate constructors.")}

  // EXPRESSIONS
  lazy val exp_bool_true: PackratParser[Bexp] = kwTrue ^^ {_ => Bexp(true)}
  lazy val exp_bool_false: PackratParser[Bexp] = kwFalse ^^ {_ => Bexp(false)}
  lazy val exp_nat: PackratParser[Nexp] = """(0|[1-9]\d*)""".r ^^ { n => Nexp(n.toInt) }
  lazy val exp_var: PackratParser[Var] = var_name ^^ {id => Var(id)}
  lazy val lam_input: PackratParser[(Var, Type)] = "(" ~> exp_var ~ ":" ~ typ <~ ")" ^^ {case v~_~t => v -> t}
  lazy val exp_lam: PackratParser[Lam] =
    kwLam ~> lam_input ~ "." ~ exp ^^ {case inp~_~body => Lam(inp._1, inp._2, body)}

  lazy val exp_famfun: PackratParser[FamFun] =
    fampath ~ "." ~ function_name ^^ {case p~_~n => FamFun(p, n)} |
    "." ~> function_name ^^ {case n => FamFun(null, n)}

  lazy val exp_famcases: PackratParser[FamCases] =
    "<" ~> fampath ~ "." ~ function_name <~ ">" ^^ {case p~_~n => FamCases(p, n)} |
    "<" ~> "." ~ function_name <~ ">" ^^ {case _~n => FamCases(null, n)}

  lazy val exp_app: PackratParser[App] = exp ~ exp ^^ {case e~g => App(e, g)}
  lazy val exp_proj: PackratParser[Proj] = exp ~ "." ~ field_name ^^ {case e~_~n => Proj(e, n)}
  lazy val field_val: PackratParser[(String, Expression)] = field_name ~ "=" ~ exp ^^ {case k~_~v => k -> v}
  lazy val exp_rec: PackratParser[Rec] = "{"~> repsep(field_val, ",") <~"}" ^^
    {case lst =>
      if (lst.size == lst.unzip._1.distinct.size) // disallow records with duplicate fields
      then Rec(lst.toMap)
      else throw new Exception("Parsing a record with duplicate fields.")}

  lazy val exp_inst: PackratParser[Inst] =
    famtype ~ "(" ~ exp_rec <~ ")" ^^ {case t~_~r => Inst(t, r)}
  lazy val exp_inst_adt: PackratParser[InstADT] =
    famtype ~ "(" ~ constructor_name ~ exp_rec <~ ")" ^^ {case t~_~c~r => InstADT(t, c, r)}

  // the second expression will be an application of exp_famcases to a record of arguments
  lazy val exp_match: PackratParser[Match] =
    kwMatch ~> exp ~ kwWith ~ exp_app ^^ {case e~_~g => Match(e, g)}

  lazy val exp: PackratParser[Expression] =
    exp_match | exp_proj | exp_inst_adt | exp_inst | exp_app | exp_rec
    | exp_famfun | exp_famcases
    | exp_lam | exp_bool_true | exp_bool_false | exp_nat
    | exp_var
    | "(" ~> exp <~ ")"

  // MARKERS
  lazy val marker: PackratParser[Marker] =
    "=" ^^ {_ => Eq} | "+=" ^^ {_ => PlusEq}

  // DEFINITIONS
  lazy val typedef: PackratParser[(String, (Marker, (RecType, Rec)))] =
    kwType ~> type_name ~ marker ~ default_rectype ^^ { case n~m~rt => (n -> (m -> rt)) }
  lazy val adtdef: PackratParser[(String, ADT)] =
    adt ^^ {case a => (a.name -> a)}

  lazy val fundef: PackratParser[(String, Fun)] =
    kwVal ~> function_name ~ (":" ~> "(" ~> funtype) ~ (")" ~> "=" ~> exp_lam) ^^ {
      case n~t~b => n -> FunDeclared(n, t, b)
    }
    // TODO: why are these both needed?
    | kwVal ~> function_name ~ (":" ~> funtype) ~ ("=" ~> exp_lam) ^^ {
      case n~t~b => n -> FunDeclared(n, t, b)
    }

  lazy val match_type: PackratParser[FamType] = "<" ~> famtype <~ ">"
  // mt = match type, m = marker, ft = funtype, lam = body
  lazy val cases_def: PackratParser[(String, Cases)] =
    kwCases ~> function_name ~ match_type ~ (":" ~> funtype) ~ marker ~ exp_lam ^^ {
      case n~mt~ft~m~b => (n -> CasesDeclared(n, mt, ft, m, b))
    }
    // TODO: why are these both needed?
    | kwCases ~> function_name ~ match_type ~ (":" ~> "(" ~> funtype) ~ (")" ~> marker) ~ exp_lam ^^ {
      case n~mt~ft~m~b => (n -> CasesDeclared(n, mt, ft, m, b))
    }


  def hasDuplicateName[K, V](kvList: List[(K, V)]): Boolean = kvList.size != kvList.distinctBy(_._1).size

  // A family can extend another family. If it does not, the parent is null.
  lazy val famdef: PackratParser[Linkage] =
    (kwFamily ~> family_name) ~ (kwExtends ~> family_name).? ~
      ("{" ~> rep(typedef)) ~ rep(adtdef) ~ rep(fundef) ~ rep(cases_def) ~ rep(famdef) <~ "}" ^^ {
      case a~optB~typs~adts~funs~cases~nestedLkgs =>
        val nestedList = nestedLkgs.map{lkg => (lkg.path, lkg)}
        if (hasDuplicateName(typs)) then throw new Exception("Parsing duplicate type names.")
        else if (hasDuplicateName(adts)) then throw new Exception("Parsing duplicate ADT names.")
        else if (hasDuplicateName(funs)) then throw new Exception("Parsing duplicate function names.")
        else if (hasDuplicateName(cases)) then throw new Exception("Parsing duplicate cases names.")
        else if (hasDuplicateName(nestedList)) then throw new Exception("Parsing duplicate family names.")
        else {
          val supFam = optB match {
            case Some(b) =>
              // family extends another
              if (a == b) then
                throw new Exception("Parsing a family that extends itself.")
              else if (typs.exists{case (s, (m, (rt, r))) => (m == PlusEq) && (rt.fields.keySet != r.fields.keySet)}) then
                throw new Exception("In a type extension, not all fields have defaults.");
              else Sp(SelfFamily(Prog, Family(b)))
            // family does not extend another
            case None => null
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

  lazy val program: PackratParser[Map[Path, Linkage]] =
    rep(famdef) ^^ {
      case lst => Map(
        Sp(Prog) -> Linkage(
          Sp(Prog), Prog, null, Map(), Map(), Map(), Map(), Map(),
          lst.map{lkg => (lkg.path, lkg)}.toMap
        )
      )
    }
}

object TestFamParser extends FamParser {
  def parse0[T](p: PackratParser[T], inp: String) = parseAll(phrase(p), inp)
  def canParse[T](p: PackratParser[T], inp: String) = parse0(p, inp).successful
  def parseSuccess[T](p: PackratParser[T], inp: String) = parse0(p, inp).get
}
