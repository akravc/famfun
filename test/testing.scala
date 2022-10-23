import org.scalatest.funsuite.AnyFunSuite
import famfun._
import name_resolution._
import type_checking._
import TestFamParser._
import famfun_main._
import scala.language.postfixOps

class FamFunParserTesting extends AnyFunSuite {
  /* ==================================== PARSER TESTING ==================================== */

  // Parsing Paths
  test("paths: absolute path") {
    val inp = "A.C.D"
    assert(canParse(pPath, inp))
    assertResult(
      AbsoluteFamily(AbsoluteFamily(AbsoluteFamily(Sp(Prog), "A"), "C"),"D")
    ){parseSuccess(pPath, inp)}
  }

  test("paths: self head absolute path") {
    val inp = "self(self(A).C).D"
    assert(canParse(pPath, inp))
    assertResult(
      AbsoluteFamily(Sp(SelfFamily(SelfFamily(Prog, "A"), "C")), "D")
    ){parseSuccess(pPath, inp)}
  }

  test("paths: self path") {
    val inp = "self(self(self(A).C).D)"
    assert(canParse(pPath, inp))
    assertResult(
      Sp(SelfFamily(SelfFamily(SelfFamily(Prog, "A"), "C"), "D"))
    ){parseSuccess(pPath, inp)}
  }

  // Parsing Types
  test("types: nat") {
    assert(canParse(pType, "N"))
    assertResult(NType){parseSuccess(pType, "N")}
  }

  test("types: bool") {
    assert(canParse(pType, "B"))
    assertResult(BType){parseSuccess(pType, "B")}
  }

  test("types: arrow") {
    assert(canParse(pType, "B -> N"))
    assertResult(FunType(BType, NType)){parseSuccess(pType, "B -> N")}
  }

  test("types: absolute famtype") {
    assert(canParse(pType, "A.R"))
    assertResult(FamType(Some(AbsoluteFamily(Sp(Prog), "A")), "R")){parseSuccess(pType, "A.R")}
  }

  test("types: absolute path famtype") {
    val inp = "A.C.D.R"
    assert(canParse(pType, inp))
    assertResult(
      FamType(Some(AbsoluteFamily(AbsoluteFamily(AbsoluteFamily(Sp(Prog), "A"), "C"), "D")), "R")
    ){parseSuccess(pType, inp)}
  }

  test("types: absolute path self head famtype") {
    val inp = "self(self(A).C).D.R"
    assert(canParse(pType, inp))
    assertResult(
      FamType(Some(AbsoluteFamily(Sp(SelfFamily(SelfFamily(Prog, "A"), "C")), "D")), "R")
    ) {parseSuccess(pType, inp)}
  }

  test("types: self famtype") {
    assert(canParse(pType, "self(A).R"))
    assertResult(FamType(Some(Sp(SelfFamily(Prog, "A"))), "R")){parseSuccess(pType, "self(A).R")}
  }

  test("types: self path famtype") {
    val inp = "self(self(self(A).C).D).R"
    assert(canParse(pType, inp))
    assertResult(
      FamType(Some(Sp(SelfFamily(SelfFamily(SelfFamily(Prog, "A"), "C"), "D"))), "R")
    ){parseSuccess(pType, inp)}
  }

  test("types: record type") {
    assert(canParse(pType, "{ a: N, b: B, c: A.R }"))
    assertResult(
      RecType(Map("a"->NType, "b"->BType, "c"->FamType(Some(AbsoluteFamily(Sp(Prog), "A")), "R")))
    ){parseSuccess(pType, "{ a: N, b: B, c: A.R }")}
  }

  test("types: paren form") {
    assert(canParse(pType, "(B->{})"))
    assertResult(FunType(BType, RecType(Map()))){parseSuccess(pType, "(B->{})")}
  }

  // Parsing Expressions
  test("exp: true") {
    assert(canParse(pExp, "true"))
    assertResult(BConst(true)){parseSuccess(pExp, "true")}
  }

  test("exp: false") {
    assert(canParse(pExp, "false"))
    assertResult(BConst(false)){parseSuccess(pExp, "false")}
  }

  test("exp: nat") {
    assert(canParse(pExp, "5"))
    assertResult(NConst(5)){parseSuccess(pExp, "5")}
  }

  test("exp: var") {
    assert(canParse(pExp, "x"))
    assertResult(Var("x")){parseSuccess(pExp, "x")}
  }

  test("exp: lam") {
    assert(canParse(pExp, "lam (x: B). x"))
    assertResult(Lam(Var("x"), BType, Var("x"))){parseSuccess(pExp, "lam (x: B). x")}
  }

  test("exp: select function from family") {
    assert(canParse(pExp, "self(A).calculate"))
    assertResult(FamFun(Some(Sp(SelfFamily(Prog, "A"))), "calculate")){parseSuccess(pExp, "self(A).calculate")}
  }

  test("exp: app") {
    assert(canParse(pExp, "(lam (x: B). x) true"))
    assertResult(App(Lam(Var("x"), BType, Var("x")), BConst(true))){parseSuccess(pExp, "(lam (x: B). x) true")}
  }

  test("exp: record") {
    assert(canParse(pExp, "{ a = 5 , b = true }"))
    assertResult(Rec(Map("a"-> NConst(5), "b" -> BConst(true)))){parseSuccess(pExp, "{ a = 5, b = true }")}
  }

  test("exp: projection") {
    assert(canParse(pExp, "{ a = 5 , b = true }.b"))
    assertResult(Proj(Rec(Map("a"-> NConst(5), "b" -> BConst(true))), "b")){parseSuccess(pExp, "{ a = 5 , b = true }.b")}
  }

  test("exp: instance") {
    assert(canParse(pExp, "A.R({a = 4})"))
    assertResult(
      Inst(FamType(Some(AbsoluteFamily(Sp(Prog), "A")), "R"), Rec(Map("a"->NConst(4))))
    ){parseSuccess(pExp, "A.R({a = 4})")}
  }

  test("exp: ADT instance") {
    assert(canParse(pExp, "A.R(C {})"))
    assertResult(
      InstADT(FamType(Some(AbsoluteFamily(Sp(Prog), "A")), "R"), "C", Rec(Map()))
    ){parseSuccess(pExp, "A.R(C {})")}
  }

  test("parser: cases with underscores") {
    val prog = "Family A {" +
      "type T = C1 {n: N} | C2 {b: B}" +
      "cases tcase <T> : {} -> {C1: {n: N} -> N, C2: {b: B} -> N, _: {} -> N} = " +
      "lam (x: {}). {C1 = lam (y: {n: N}). 1, C2 = lam (z: {b: B}). 1, _ = lam (w: {}). 0}" +
      "}"
    assert(canParse(pFamDef(Prog), prog))
  }

  // Parsing Families
  test("famdef one type") {
    assert(canParse(
      pFamDef(Prog), "Family A { type T = {f: B = true, n: N = 3}}"
    ))
    assertResult(
      "A" -> Linkage(
        AbsoluteFamily(Sp(Prog), "A"),
        SelfFamily(Prog, "A"),
        None,
        Map("T" -> TypeDefn("T", Eq, DefnBody(Some(RecType(Map("f"->BType, "n"->NType))), None, None))),
        Map("T" -> DefaultDefn("T", Eq, DefnBody(Some(Rec(Map("f"->BConst(true), "n"->NConst(3)))), None, None))),
        Map(), Map(), Map(), Map()
      )
    ){parseSuccess(pFamDef(Prog), "Family A { type T = {f: B = true, n: N = 3}}")}
  }

  test("famdef extends") {
    assert(canParse(
      pFamDef(Prog), "Family A extends C { type T = {f: B = true, n: N = 3}}"
    ))
    assertResult(
      "A" -> Linkage(
        AbsoluteFamily(Sp(Prog), "A"),
        SelfFamily(Prog, "A"),
        Some(AbsoluteFamily(Sp(Prog), "C")),
        Map("T" -> TypeDefn("T", Eq, DefnBody(Some(RecType(Map("f"->BType, "n"->NType))), None, None))),
        Map("T" -> DefaultDefn("T", Eq, DefnBody(Some(Rec(Map("f"->BConst(true), "n"->NConst(3)))), None, None))),
        Map(), Map(), Map(), Map()
      )
    ){parseSuccess(pFamDef(Prog), "Family A extends C { type T = {f: B = true, n: N = 3}}")}
  }

  test("famdef extends and plusEquals, missing defaults") {
    assertThrows[Exception](canParse(
      pFamDef(Prog), "Family A extends C { type T += {f: B, n: N = 3}}"
    ))
  }

  test("famdef extends and plusEquals") {
    assert(canParse(
      pFamDef(Prog), "Family A extends C {type T += {f: B = true, n: N = 3}}"
    ))
    assertResult(
      "A" -> Linkage(
        AbsoluteFamily(Sp(Prog), "A"),
        SelfFamily(Prog, "A"),
        Some(AbsoluteFamily(Sp(Prog), "C")),
        Map("T" -> TypeDefn("T", PlusEq, DefnBody(Some(RecType(Map("f"->BType, "n"->NType))), None, None))),
        Map("T" -> DefaultDefn("T", PlusEq, DefnBody(Some(Rec(Map("f"->BConst(true), "n"->NConst(3)))), None, None))),
        Map(), Map(), Map(), Map()
      )
    ){parseSuccess(pFamDef(Prog), "Family A extends C { type T += {f: B = true, n: N = 3}}")}
  }

  test("famdef multiple types") {
    assert(canParse(pFamDef(Prog),
      "Family A { " +
        "type T = {f: B = true, n: N = 3} " +
        "type R = {s: self(A).T = {}}" +
        "}"
    ))
    assertResult(
      "A" -> Linkage(
        AbsoluteFamily(Sp(Prog), "A"),
        SelfFamily(Prog, "A"),
        None,
        Map(
          "T" -> TypeDefn("T", Eq, DefnBody(Some(RecType(Map("f"->BType, "n"->NType))), None, None)),
          "R" -> TypeDefn("R", Eq, DefnBody(Some(RecType(Map("s"->FamType(Some(Sp(SelfFamily(Prog, "A"))), "T")))), None, None))
        ),
        Map(
          "T" -> DefaultDefn("T", Eq, DefnBody(Some(Rec(Map("f"->BConst(true), "n"->NConst(3)))), None, None)),
          "R" -> DefaultDefn("R", Eq, DefnBody(Some(Rec(Map("s"->Rec(Map())))), None, None))
        ),
        Map(), Map(), Map(), Map()
      )
    ){parseSuccess(pFamDef(Prog),
      "Family A { " +
        "type T = {f: B = true, n: N = 3} " +
        "type R = {s: self(A).T = {}}" +
        "}")}
  }

  test("famdef types + ADTs") {
    assert(canParse(pFamDef(Prog),
      "Family A { " +
        "type T = {f: B = true, n: N = 3} " +
        "type R = {s: self(A).T = {}}" +
        "type List = Nil {} | Cons {x: N, tail: self(A).List}" +
        "}"
    ))
    assertResult(
      "A" -> Linkage(
        AbsoluteFamily(Sp(Prog), "A"),
        SelfFamily(Prog, "A"),
        None,
        // types
        Map(
          "T" -> TypeDefn("T", Eq, DefnBody(Some(RecType(Map("f"->BType, "n"->NType))), None, None)),
          "R" -> TypeDefn("R", Eq, DefnBody(Some(RecType(Map("s"->FamType(Some(Sp(SelfFamily(Prog, "A"))), "T")))), None, None))
        ),
        // defaults
        Map(
          "T" -> DefaultDefn("T", Eq, DefnBody(Some(Rec(Map("f"->BConst(true), "n"->NConst(3)))), None, None)),
          "R" -> DefaultDefn("R", Eq, DefnBody(Some(Rec(Map("s"->Rec(Map())))), None, None))
        ),
        // adts
        Map(
          "List"-> AdtDefn(
            "List", Eq, DefnBody(
              Some(Map(
                "Nil" -> RecType(Map()),
                "Cons" -> RecType(Map(
                  "x" -> NType,
                  "tail" -> FamType(Some(Sp(SelfFamily(Prog, "A"))), "List")
                ))
              )),
              None, None
            )
          )
        ),
        Map(), Map(), Map()
      )
    ){parseSuccess(pFamDef(Prog),
      "Family A { " +
        "type T = {f: B = true, n: N = 3} " +
        "type R = {s: self(A).T = {}}" +
        "type List = Nil {} | Cons {x: N, tail: self(A).List}" +
        "}")}
  }

  test("famdef can parse multiple types and ADTs") {
    assert(canParse(pFamDef(Prog),
      "Family A { " +
        "type T = {f: B = true, n: N = 3} " +
        "type R = {s: self(A).T = {}}" +
        "type List = Nil {} | Cons {x: N, tail: self(A).List}" +
        "type Weekend = Sat {} | Sun {}" +
        "}"
    ))
  }

  test("famdef can parse types, adts, functions") {
    assert(canParse(pFamDef(Prog),
      "Family A { " +
        "type T = {f: B = true, n: N = 3} " +
        "type R = {s: self(A).T = {}}" +
        "type List = Nil {} | Cons {x: N, tail: self(A).List}" +
        "type Weekend = Sat {} | Sun {}" +
        "val identity: (B -> B) = lam (x: B). x" +
        "}"
    ))
  }

  test("famdef can parse nested families") {
    val prog =
    """
     |Family A {
     |  Family C {
     |    Family D {}
     |  }
     |  Family E {}
     |}
     |""".stripMargin

    assert(canParse(pFamDef(Prog), prog))

    assertResult(
      "A" -> Linkage(
        AbsoluteFamily(Sp(Prog), "A"),
        SelfFamily(Prog, "A"),
        None,
        Map(), Map(), Map(), Map(), Map(),
        Map(
          "C" -> Linkage(
            AbsoluteFamily(AbsoluteFamily(Sp(Prog), "A"), "C"),
            SelfFamily(SelfFamily(Prog, "A"), "C"),
            None,
            Map(), Map(), Map(), Map(), Map(),
            Map(
              "D" -> Linkage(
                AbsoluteFamily(AbsoluteFamily(AbsoluteFamily(Sp(Prog), "A"), "C"), "D"),
                SelfFamily(SelfFamily(SelfFamily(Prog, "A"), "C"), "D"),
                None,
                Map(), Map(), Map(), Map(), Map(), Map()
              )
            )
          ),
          "E" -> Linkage(
            AbsoluteFamily(AbsoluteFamily(Sp(Prog), "A"), "E"),
            SelfFamily(SelfFamily(Prog, "A"), "E"),
            None,
            Map(), Map(), Map(), Map(), Map(), Map()
          )
        )
      )
    ){parseSuccess(pFamDef(Prog), prog)}
  }

  test("famdef can parse nested families with types, adts, functions") {
    """
      |Family A {
      |  type T = {f: B = true, n: N = 3}
      |  type Weekend = Sat {} | Sun {}
      |  val identity: (B -> B) = lam (x: B). x
      |  Family C {
      |      type R = {s: self(A).T = {}}
      |      type List = Nil {} | Cons {x: N, tail: self(A).List}
      |  }
      |  Family D {
      |    val add1: (N -> N) = lam (x: N). x + 1
      |  }
      |}
      |""".stripMargin
  }

  // Testing Exceptions
  test("exception: duplicate fields in record") {
    assertThrows[Exception](parse0(pRecType, "{f: N, f: B}"))
  }

  test("exception: duplicate constructors in ADT") {
    assertThrows[Exception](parse0(pAdt, "type T = A {} | A {}"))
  }

  test("exception: duplicate family names") {
    assertThrows[Exception](parse0(pFamDef(Prog), "Family A { Family C {} Family C {} }"))
  }

  test("can parse record fields that are constructors") {
    assert(canParse(pFieldName, "HelloWorld"))
  }

  test("can parse cases by themselves") {
    assert(canParse(pCasesDef, "cases hello_world <T> : {} -> {A: B -> N, C: B -> N} = " +
      "lam (_: {}). {A = lam (x: B). 3, C = lam (x: B). 4}"))
  }

  test("Var resolution: bound Var stays Var") {
    val inp =
      """
        |Family A {
        |  val f: B -> B = lam (x: B). x
        |}
        |""".stripMargin

    assert(canParse(pFamDef(Prog), inp))

    val resolvedLkg: Linkage = resolveVarsAndValidateSelfPaths(parseSuccess(pFamDef(Prog), inp)._2).getOrElse(throw new Exception("?"))

    assertResult(
      DefnBody(
        Some(Lam(Var("x"), BType, Var("x"))),
        None,
        None
      )
    ){resolvedLkg.funs("f").funBody}
  }

  test("Var resolution: free Var becomes FamFun") {
    val inp =
      """
        |Family A {
        |  val f: B -> B = y
        |}
        |""".stripMargin

    assert(canParse(pFamDef(Prog), inp))

    val resolvedLkg: Linkage =
      resolveVarsAndValidateSelfPaths(parseSuccess(pFamDef(Prog), inp)._2).getOrElse(throw new Exception("?"))

    assertResult(
      DefnBody(
        Some(FamFun(None, "y")),
        None,
        None
      )
    ){resolvedLkg.funs("f").funBody}
  }
}

class FamFunTesting extends AnyFunSuite {
  /* ==================================== TYPECHECKER TESTING ==================================== */

  // TESTING IS_VALUE

  test("isvalue: functions") {
    assert(is_value(Lam(Var("x"), BType, Var("x"))))
  }

  test("isvalue: bools") {
    assert(is_value(BConst(true)))
    assert(is_value(BConst(false)))
  }

  test("isvalue: nats") {
    assert(is_value(NConst(0)))
    assert(is_value(NConst(4)))
  }

  test("isvalue: record") {
    assert(is_value(Rec(Map("f"->NConst(2), "p"->BConst(true)))))
  }

  test("not a value: record") {
    assert(!is_value(Rec(Map("f"->Var("x"), "p"->BConst(true)))))
  }

  // A.T({f=2, p=5})
  test("isvalue: instance of a type") {
    assert(is_value(Inst(FamType(Some(Sp(SelfFamily(Prog, "A"))), "T"), Rec(Map("f"->NConst(2), "p"->NConst(5))))))
  }

  // A.T({f=2, p=x})
  test("not a value: instance of a type") {
    assert(!is_value(Inst(FamType(Some(Sp(SelfFamily(Prog, "A"))), "T"), Rec(Map("f"->NConst(2), "p"->Var("x"))))))
  }

  // A.T(C {f=2, p=5})
  test("isvalue: instance of an ADT") {
    assert(is_value(InstADT(FamType(Some(Sp(SelfFamily(Prog, "A"))), "T"), "C", Rec(Map("f"->NConst(2), "p"->NConst(5))))))
  }

  // A.T(C {f=2, p=x})
  test("not a value: instance of an ADT") {
    assert(!is_value(InstADT(FamType(Some(Sp(SelfFamily(Prog, "A"))), "T"), "C", Rec(Map("f"->NConst(2), "p"->Var("x"))))))
  }

  test("not a value: other") {
    assert(!is_value(App(Var("x"), BConst(true))))
  }

  // TESTING WELL-FORMEDNESS

  test("wf: nat") {
    //assert(wf(NType, Map()))
    assertResult(Right(true))(wf(NType))
  }

  test("wf: bool") {
    //assert(wf(BType, Map()))
    assertResult(Right(true))(wf(BType))
  }

  // T = {f: B, n: N}
  // self(A).T is well formed
  test("wf: family type") {
    val self_a = SelfFamily(Prog, "A") // path self(A)
    init(Linkage(Sp(Prog), Prog, None, Map(), Map(), Map(), Map(), Map(),
      Map("A" -> Linkage(
        AbsoluteFamily(Sp(Prog), "A"), self_a, None,
        Map("T"->(TypeDefn("T", Eq, DefnBody(Some(RecType(Map("f"->BType, "n"->NType))), None, None)))), Map(), Map(), Map(), Map(), Map()))))
    assertResult(Right(true))(wf(FamType(Some(Sp(self_a)), "T")))
  }

  // List = Nil {} | Cons {x: N, tail: self(A).List}
  // self(A).List is well formed
  test("wf: family ADT type") {
    val self_a = SelfFamily(Prog, "A") // path self(A)
    init(Linkage(Sp(Prog), Prog, None, Map(), Map(), Map(), Map(), Map(),
      Map("A" -> Linkage(
        AbsoluteFamily(Sp(Prog), "A"), self_a, None,
        Map(), Map(),
        Map("List"->
          (AdtDefn("List,", Eq, DefnBody(Some(Map(
            "Nil"->RecType(Map()),
            "Cons"->RecType(Map("x"->NType, "tail"->FamType(Some(Sp(SelfFamily(Prog, "A"))), "List"))))), None, None)))), Map(), Map(), Map()))))
    assertResult(Right(true))(wf(FamType(Some(Sp(self_a)), "List")))
  }

  // N -> B
  test("wf: function type") {
    assertResult(Right(true))(wf(FunType(NType, BType)))
  }

  // self(A).T -> N
  test("wf: function type 2") {
    val self_a = SelfFamily(Prog, "A") // path self(A)
    init(Linkage(Sp(Prog), Prog, None, Map(), Map(), Map(), Map(), Map(),
      Map("A" -> Linkage(
        AbsoluteFamily(Sp(Prog), "A"), self_a, None,
        Map("T"->(TypeDefn("T", Eq, DefnBody(Some(RecType(Map("f"->BType, "n"->NType))), None, None)))), Map(), Map(), Map(), Map(), Map()))))
    assertResult(Right(true))(wf(FunType(FamType(Some(Sp(self_a)), "T"), NType)))
  }

  // self(A).T -> N
  test("wf: function type not in linkage") {
    val self_a = SelfFamily(Prog, "A") // path self(A)
    init(Linkage(Sp(Prog), Prog, None, Map(), Map(), Map(), Map(), Map(),
      Map("A" -> Linkage(
        AbsoluteFamily(Sp(Prog), "A"), self_a, None,
        Map("G"->(TypeDefn("G", Eq, DefnBody(Some(RecType(Map("f"->BType, "n"->NType))), None, None)))), Map(), Map(), Map(), Map(), Map()))))
    assertResult(Right(false))(wf(FunType(FamType(Some(Sp(self_a)), "T"), NType)))
  }

  // {f: B, p: N}
  test("wf: record type") {
    assertResult(Right(true))(wf(RecType(Map("f"->BType, "p"->NType))))
  }

  // {f: B, p: self(A).T}
  test("wf: record type 2") {
    val self_a = SelfFamily(Prog, "A") // path self(A)
    init(Linkage(Sp(Prog), Prog, None, Map(), Map(), Map(), Map(), Map(),
      Map("A" -> Linkage(
        AbsoluteFamily(Sp(Prog), "A"), self_a, None,
        Map("T"->(TypeDefn("T", Eq, DefnBody(Some(RecType(Map("f"->BType, "n"->NType))), None, None)))), Map(), Map(), Map(), Map(), Map()))))
    assertResult(Right(true))(wf(RecType(Map("f"->BType, "p"->FamType(Some(Sp(self_a)), "T")))))
  }

  test("wf: record type not in linkage") {
    val self_a = SelfFamily(Prog, "A") // path self(A)
    init(Linkage(Sp(Prog), Prog, None, Map(), Map(), Map(), Map(), Map(),
      Map("A" -> Linkage(
        AbsoluteFamily(Sp(Prog), "A"), self_a, None,
        Map("T"->(TypeDefn("T", Eq, DefnBody(Some(RecType(Map("f"->BType, "n"->NType))), None, None)))), Map(), Map(), Map(), Map(), Map()))))
    assertResult(Right(false))(wf(RecType(Map("f"->BType, "p"->FamType(Some(Sp(self_a)), "G")))))
  }

  test("wf: null type is not") {
    assertResult(Right(false))(wf(null))
  }

  // TESTING SUBTYPING

  test("subtype: the type itself") {
    assertResult(Right(true))(isSubtype(BType, BType))
  }

  test("subtype: the type itself 2") {
    assertResult(Right(true))(isSubtype(NType, NType))
  }

  test("subtype: the type itself 3") {
    val self_a = SelfFamily(Prog, "A") // path self(A)
    assertResult(Right(true))(isSubtype(FamType(Some(Sp(self_a)), "G"), FamType(Some(Sp(self_a)), "G")))
  }

  // {f: B, p: N} <: {f: B}
  test("subtype: rectype width") {
    assertResult(Right(true))(isSubtype(RecType(Map("f"->BType, "p"->NType)), RecType(Map("f"->BType))))
  }

  // {g: {f: B, p: N}} <: {g: {f: B}}
  test("subtype: rectype depth") {
    assertResult(Right(true))(isSubtype(RecType(Map("g"->RecType(Map("f"->BType, "p"->NType)))),
      RecType(Map("g"->RecType(Map("f"->BType))))))
  }

  // {f: B, p: N} <: {f: B, g: N}
  test("subtype: rectype bad") {
    assertResult(Right(false))(isSubtype(RecType(Map("f"->BType, "p"->NType)), RecType(Map("f"->BType, "g"->NType))))
  }

  test("subtype: funtype eq") {
    assertResult(Right(true))(isSubtype(FunType(BType,NType), FunType(BType,NType)))
  }

  // {f: B} <: {}, therefore:
  // {} -> {f: B} <: {f: B} -> {}
  test("subtype: funtype good") {
    assertResult(Right(true))(isSubtype(FunType(RecType(Map()), RecType(Map("f"->BType))),
      FunType(RecType(Map("f"->BType)),RecType(Map()))))
  }

  test("subtype: funtype bad") {
    assertResult(Right(false))(isSubtype(FunType(RecType(Map()), RecType(Map("f"->BType))),
      FunType(RecType(Map("f"->BType)),RecType(Map("g"->BType)))))
  }

  test("subtype: famtype good") {
    val self_a = SelfFamily(Prog, "A")
    init(Linkage(Sp(Prog), Prog, None, Map(), Map(), Map(), Map(), Map(),
      Map("A" -> Linkage(
        AbsoluteFamily(Sp(Prog), "A"), self_a, None,
        Map("T"->(TypeDefn("T", Eq, DefnBody(Some(RecType(Map("f"->BType))), None, None)))), Map(), Map(), Map(), Map(), Map()))))
    assertResult(Right(true))(isSubtype(FamType(Some(Sp(self_a)), "T"), RecType(Map("f"->BType))))
  }

  test("subtype: famtype mismatch in linkage") {
    val self_a = SelfFamily(Prog, "A")
    init(Linkage(Sp(Prog), Prog, None, Map(), Map(), Map(), Map(), Map(),
      Map("A" -> Linkage(
        AbsoluteFamily(Sp(Prog), "A"), self_a, None,
        Map("T"->(TypeDefn("T", Eq, DefnBody(Some(RecType(Map("f"->BType))), None, None)))), Map(), Map(), Map(), Map(), Map()))))
    assertResult(Right(false))(isSubtype(FamType(Some(Sp(self_a)), "T"), RecType(Map("g"->BType))))
  }

  test("subtype: famtype bad") {
    val self_a = SelfFamily(Prog, "A")
    init(Linkage(Sp(Prog), Prog, None, Map(), Map(), Map(), Map(), Map(),
      Map("A" -> Linkage(
        AbsoluteFamily(Sp(Prog), "A"), self_a, None,
        Map("T"->(TypeDefn("T", Eq, DefnBody(Some(RecType(Map("f"->BType))), None, None)))), Map(), Map(), Map(), Map(), Map()))))
    assertResult(Right(false))(isSubtype(FamType(Some(Sp(self_a)), "T"), FunType(BType,NType)))
  }

  test("subtype: two unrelated types") {
    assertResult(Right(false))(isSubtype(BType, FunType(BType,NType)))
  }

  // TESTING TYP_INF

  val emptyLinkage = Linkage(Sp(Prog), Prog, None, Map(), Map(), Map(), Map(), Map(), Map())

  val typInf = typeOfExpression(emptyLinkage, Map())

  test("typinf: nat") {
    assertResult(Right(NType)){typInf(NConst(5))}
  }

  test("typinf: bool") {
    assertResult(Right(BType)){typInf(BConst(true))}
    assertResult(Right(BType)){typInf(BConst(false))}
  }

  test("typinf: var") {
    assertResult(Right(NType)){typeOfExpression(emptyLinkage, Map("x"->NType))(Var("x"))}
  }

  test("typinf: var none") {
    assertResult(Left("Variable x unbound\nIn expression x")){typInf(Var("x"))}
  }

  test("typinf: lam") {
    assertResult(Right(FunType(BType, NType))){
      typInf(Lam(Var("x"), BType, NConst(5)))
    }
  }

  test("typinf: lam identity") {
    assertResult(Right(FunType(BType, BType))){
      typInf(Lam(Var("x"), BType, Var("x")))
    }
  }

  test("typinf: app") {
    assertResult(Right(NType)){
      typInf(App(Lam(Var("x"), BType, NConst(5)), BConst(true)))
    }
  }

  test("typinf: app improper") {
    assertResult(Left("Variable x unbound\nIn expression x\nIn expression (x true)")){
      typInf(App(Var("x"), BConst(true)))
    }
  }

  test("typinf: rec") {
    assertResult(Right(RecType(Map("f"->BType, "p"->NType)))){
      typInf(Rec(Map("f"->BConst(true), "p"->NConst(4))))
    }
  }

  def isLeft[A,B](x: Either[A,B]) = x match {
    case Left(_) => true
    case Right(_) => false
  }

  test("typinf: rec improper") {
    assert(isLeft(
      typInf(Rec(Map("f"->BConst(true), "p"->App(NConst(4), BConst(true)))))))
  }

  test("typinf: rec empty") {
    assertResult(Right(RecType(Map()))){typInf(Rec(Map()))}
  }

  ignore("typinf: null type") {
    assert(isLeft(typInf(null)))
  }

  test("typinf: proj") {
    assertResult(Right(NType)){
      typInf(Proj(Rec(Map("f"->BConst(true), "p"->NConst(4))), "p"))
    }
  }

  test("typinf: proj field absent") {
    assert(isLeft(
      typInf(Proj(Rec(Map("f"->BConst(true), "p"->NConst(4))), "g"))))
  }

  test("typinf: proj from not record") {
    assert(isLeft(
      typInf(Proj(Var("x"), "x"))))
  }

  // self(A).m : (B -> N) = lam (x: B). 5
  test("typinf: fam fun") {
    val self_a = SelfFamily(Prog, "A")
    val k = Linkage(Sp(Prog), Prog, None, Map(), Map(), Map(), Map(), Map(),
      Map("A" -> Linkage(AbsoluteFamily(Sp(Prog), "A"), self_a, None,
        Map(), Map(), Map(),
        Map("m"->(FunDefn("m", FunType(BType, NType), DefnBody(Some(Lam(Var("x"), BType, NConst(5))), None, None)))),
        Map(), Map())))
    init(k)
    assertResult(Right(FunType(BType, NType))){
      typInf(FamFun(Some(Sp(self_a)), "m"))
    }
  }

  // self(A).m does not exist, we have self(A).g instead
  test("typinf: fam fun not in linkage") {
    val self_a = SelfFamily(Prog, "A")
    val k = Linkage(Sp(Prog), Prog, None, Map(), Map(), Map(), Map(), Map(),
      Map("A" -> Linkage(AbsoluteFamily(Sp(Prog), "A"), self_a, None,
        Map(), Map(), Map(),
        Map("g"->(FunDefn("g", FunType(BType, NType), DefnBody(Some(Lam(Var("x"), BType, NConst(5))), None, None)))),
        Map(), Map())))
    init(k)
    assertResult(Left("No such function m\nIn expression self(<>.A).m")){
      typInf(FamFun(Some(Sp(self_a)), "m"))
    }
  }

  test("typinf: fam fun, absent linkage for self_a") {
    val self_a = SelfFamily(Prog, "A")
    assert(isLeft(
      typInf(FamFun(Some(Sp(self_a)), "m"))
    ))
  }

  // self(A).R({f->true, n->5})
  test("typinf: instance of type") {
    val self_a = SelfFamily(Prog, "A")
    val k = Linkage(Sp(Prog), Prog, None, Map(), Map(), Map(), Map(), Map(),
      Map("A" -> Linkage(AbsoluteFamily(Sp(Prog), "A"), self_a, None,
        Map("R"->(TypeDefn("R", Eq, DefnBody(Some(RecType(Map("f"->BType, "n"->NType))), None, None)))), Map(), Map(), Map(), Map(), Map())))
    init(k)
    assertResult(Right(FamType(Some(Sp(self_a)), "R"))){
      typInf(Inst(FamType(Some(Sp(self_a)), "R"), Rec(Map("f"->BConst(true), "n"->NConst(5)))))
    }
  }

  test("typinf: instance of type wrong field name") {
    val self_a = SelfFamily(Prog, "A")
    val k = Linkage(Sp(Prog), Prog, None, Map(), Map(), Map(), Map(), Map(),
      Map("A" -> Linkage(AbsoluteFamily(Sp(Prog), "A"), self_a, None,
        Map("R"->(TypeDefn("R", Eq, DefnBody(Some(RecType(Map("f"->BType, "p"->NType))), None, None)))), Map(), Map(), Map(), Map(), Map())))
    init(k)
    assert(isLeft(
      typInf(Inst(FamType(Some(Sp(self_a)), "R"), Rec(Map("f"->BConst(true), "n"->NConst(5)))))
    ))
  }

  test("typinf: instance of type wrong field type") {
    val self_a = SelfFamily(Prog, "A")
    val k = Linkage(Sp(Prog), Prog, None, Map(), Map(), Map(), Map(), Map(),
      Map("A" -> Linkage(AbsoluteFamily(Sp(Prog), "A"), self_a, None,
        Map("R"->(TypeDefn("R", Eq, DefnBody(Some(RecType(Map("f"->BType, "n"->BType))), None, None)))), Map(), Map(), Map(), Map(), Map())))
    init(k)
    assert(isLeft(
      typInf(Inst(FamType(Some(Sp(self_a)), "R"), Rec(Map("f"->BConst(true), "n"->NConst(5)))))
    ))
  }

  test("typinf: instance of type wrong type name") {
    val self_a = SelfFamily(Prog, "A")
    val k = Linkage(Sp(Prog), Prog, None, Map(), Map(), Map(), Map(), Map(),
      Map("A" -> Linkage(AbsoluteFamily(Sp(Prog), "A"), self_a, None,
        Map("R"->(TypeDefn("R", Eq, DefnBody(Some(RecType(Map("f"->BType, "n"->NType))), None, None)))), Map(), Map(), Map(), Map(), Map())))
    init(k)
    assert(isLeft(
      typInf(Inst(FamType(Some(Sp(self_a)), "K"), Rec(Map("f"->BConst(true), "n"->NConst(5)))))
    ))
  }

  // self(A).R(C {f->true, n->5})
  test("typinf: instance of ADT") {
    val self_a = SelfFamily(Prog, "A")
    val k = Linkage(Sp(Prog), Prog, None, Map(), Map(), Map(), Map(), Map(),
      Map("A" -> Linkage(AbsoluteFamily(Sp(Prog), "A"), self_a, None,
        Map(), Map(),
        Map("R"->(AdtDefn("R", Eq, DefnBody(Some(Map("C"->RecType(Map("f"->BType, "n"->NType)))), None, None)))),
        Map(), Map(), Map())))
    init(k)
    assertResult(Right(FamType(Some(Sp(self_a)), "R"))){
      typInf(InstADT(FamType(Some(Sp(self_a)), "R"), "C", Rec(Map("f"->BConst(true), "n"->NConst(5)))))
    }
  }

  test("typinf: instance of ADT wrong field name") {
    val self_a = SelfFamily(Prog, "A")
    val k = Linkage(Sp(Prog), Prog, None, Map(), Map(), Map(), Map(), Map(),
      Map("A" -> Linkage(AbsoluteFamily(Sp(Prog), "A"), self_a, None,
        Map(), Map(),
        Map("R"->(AdtDefn("R", Eq, DefnBody(Some(Map("C"->RecType(Map("f"->BType, "n"->NType)))), None, None)))),
        Map(), Map(), Map())))
    init(k)
    assert(isLeft(
      typInf(InstADT(FamType(Some(Sp(self_a)), "R"), "C", Rec(Map("f"->BConst(true), "p"->NConst(5)))))
    ))
  }

  test("typinf: instance of ADT wrong field type") {
    val self_a = SelfFamily(Prog, "A")
    val k = Linkage(Sp(Prog), Prog, None, Map(), Map(), Map(), Map(), Map(),
      Map("A" -> Linkage(AbsoluteFamily(Sp(Prog), "A"), self_a, None,
        Map(), Map(),
        Map("R"->(AdtDefn("R", Eq, DefnBody(Some(Map("C"->RecType(Map("f"->BType, "n"->BType)))), None, None)))),
        Map(), Map(), Map())))
    init(k)
    assert(isLeft(
      typInf(InstADT(FamType(Some(Sp(self_a)), "R"), "C", Rec(Map("f"->BConst(true), "n"->NConst(5)))))
    ))
  }

  test("typinf: instance of ADT wrong constructor name") {
    val self_a = SelfFamily(Prog, "A")
    val k = Linkage(Sp(Prog), Prog, None, Map(), Map(), Map(), Map(), Map(),
      Map("A" -> Linkage(AbsoluteFamily(Sp(Prog), "A"), self_a, None,
        Map(), Map(),
        Map("R"->(AdtDefn("R", Eq, DefnBody(Some(Map("C"->RecType(Map("f"->BType, "n"->NType)))), None, None)))),
        Map(), Map(), Map())))
    init(k)
    assert(isLeft(
      typInf(InstADT(FamType(Some(Sp(self_a)), "R"), "K", Rec(Map("f"->BConst(true), "n"->NConst(5)))))
    ))
  }

  test("typinf: instance of ADT wrong type name") {
    val self_a = SelfFamily(Prog, "A")
    val k = Linkage(Sp(Prog), Prog, None, Map(), Map(), Map(), Map(), Map(),
      Map("A" -> Linkage(AbsoluteFamily(Sp(Prog), "A"), self_a, None,
        Map(), Map(),
        Map("R"->(AdtDefn("R", Eq, DefnBody(Some(Map("C"->RecType(Map("f"->BType, "n"->NType)))), None, None)))),
        Map(), Map(), Map())))
    init(k)
    assert(isLeft(
      typInf(InstADT(FamType(Some(Sp(self_a)), "K"), "C", Rec(Map("f"->BConst(true), "n"->NConst(5)))))
    ))
  }

  test("typinf: instance of ADT empty map in linkage") {
    val self_a = SelfFamily(Prog, "A")
    val k = Linkage(Sp(Prog), Prog, None, Map(), Map(), Map(), Map(), Map(),
      Map("A" -> Linkage(AbsoluteFamily(Sp(Prog), "A"), self_a, None,
        Map(), Map(),
        Map(),
        Map(), Map(), Map())))
    init(k)
    assert(isLeft(
      typInf(InstADT(FamType(Some(Sp(self_a)), "R"), "C", Rec(Map("f"->BConst(true), "n"->NConst(5)))))
    ))
  }

  test("typinf: match not on instance of ADT") {
    assert(isLeft(
      typInf(Match(Var("x"), Var("x")))
    ))
  }

  test("typinf: match on instance of type, not ADT") {
    val self_a = SelfFamily(Prog, "A")
    // self(A).R({f->true, n->5})
    val exp = Inst(FamType(Some(Sp(self_a)), "R"), Rec(Map("f"->BConst(true), "n"->NConst(5))))
    assert(isLeft(
      typInf(Match(exp, exp))
    ))
  }

  test("typinf: match on instance of ADT not in linkage") {
    val self_a = SelfFamily(Prog, "A")
    // self(A).R({f->true, n->5})
    val exp = InstADT(FamType(Some(Sp(self_a)), "R"), "C", Rec(Map("f"->BConst(true), "n"->NConst(5))))
    assert(isLeft(
      typInf(Match(exp, exp))
    ))
  }

  test("process: pattern match, wrong function type") {
    val prog = """
Family A {
  type R = C {f: B, n: N}

  val x: {} -> N = lam (_: {}). match R(C {f = true, n = 5}) with <cs> {}

  cases cs <R> : {} -> { C: {f: N, n: N} -> N } =
    lam (_: {}). {C = lam (x: {f: N, n: N}). 1 }
}
    """
    assertResult(Left("Cases cs in <>.A is non-exhaustive."))(typecheckProcess(prog))
  }

  // TODO(now): this seems OK because checked above?
  ignore("typinf: match on instance of ADT, wrong function type in match") {
    val self_a = SelfFamily(Prog, "A")
    // self(A).R({f->true, n->5})
    val exp = InstADT(FamType(Some(Sp(self_a)), "R"), "C", Rec(Map("f"->BConst(true), "n"->NConst(5))))
    val k = Linkage(Sp(Prog), Prog, None, Map(), Map(), Map(), Map(), Map(),
      Map("A" -> Linkage(AbsoluteFamily(Sp(Prog), "A"), self_a, None,
        Map(), Map(),
        Map("R"->(AdtDefn("R", Eq, DefnBody(Some(Map("C"->RecType(Map("f"->BType, "n"->NType)))), None, None)))),
        Map(),
        Map("cs"->(CasesDefn("cs", FamType(Some(Sp(self_a)), "R"), FunType(RecType(Map()), RecType(Map("C"->FunType(RecType(Map("f"->NType, "n"->NType)), NType)))), Eq,
              DefnBody(Some(Lam(Var("x"), RecType(Map()), Rec(Map("C" -> Lam(Var("r"), RecType(Map("f"->NType, "n"->NType)), NConst(1)))))), None, None)))),
        Map())))
    init(k)
    assert(isLeft(
      typInf(Match(exp, App(FamCases(Some(Sp(self_a)), "cs"), Rec(Map()))))
    ))

    /* // original test
     val self_a = SelfFamily(Prog, "A")
    // self(A).R({f->true, n->5})
    val exp = InstADT(FamType(self_a, "R"), "C", Rec(Map("f"->BConst(true), "n"->NConst(5))))
    assertResult(None){
      typInf(Match(exp, App(FamCases(self_a, "cs"), Rec(Map()))), Map(),
        Map(self_a->
          Linkage(self_a, null, Map(), Map(),
          // list of ADTs has R = C {f:B, n:N}
          Map("R"->(Eq, ADT(Map("C"->RecType(Map("f"->BType, "n"->NType)))))), Map(),
          Map("cs"->(FamType(self_a, "R"), Eq, FunType(RecType(Map()), RecType(Map("C"->FunType(RecType(Map("f"->NType, "n"->NType)), NType)))),
            Lam(Var("x"), RecType(Map()), Rec(Map("C" -> Lam(Var("r"), RecType(Map("f"->NType, "n"->NType)), NConst(1))))))))))
     }
     */
  }

  test("process: pattern match") {
    val prog = """
Family A {
  type R = C {f: B, n: N} | K {}

  val x: {} -> N = lam (_: {}). match R(C {f = true, n = 5}) with <cs> {}

  cases cs <R> : {} -> { C: {f: B, n: N} -> N, K: {} -> N } =
    lam (_: {}). {C = lam (x: {f: B, n: N}). 1, K = lam (x: {}). 2}
}
    """
    assertResult(Right(()))(typecheckProcess(prog))
  }

  test("process: pattern match not exhaustive") {
    val prog = """
Family A {
  type R = C {f: B, n: N} | K {}

  val x: {} -> N = lam (_: {}). match R(C {f = true, n = 5}) with <cs> {}

  cases cs <R> : {} -> { C: {f: B, n: N} -> N } =
    lam (_: {}). {C = lam (x: {f: B, n: N}). 1}
}
    """
    assertResult(Left("Cases cs in <>.A is non-exhaustive."))(typecheckProcess(prog))
  }

  // TODO(now): this seems OK because checked above?
  ignore("typinf: pattern match not exhaustive") {
    val self_a = SelfFamily(Prog, "A")
    // self(A).R({f->true, n->5})
    val exp = InstADT(FamType(Some(Sp(self_a)), "R"), "C", Rec(Map("f"->BConst(true), "n"->NConst(5))))
    val k = Linkage(Sp(Prog), Prog, None, Map(), Map(), Map(), Map(), Map(),
      Map("A" -> Linkage(AbsoluteFamily(Sp(Prog), "A"), self_a, None,
        Map(), Map(),
        Map("R"->(AdtDefn("R", Eq, DefnBody(Some(Map("C"->RecType(Map("f"->BType, "n"->NType)), "K"->RecType(Map()))), None, None)))),
        Map(),
        Map("cs"->(CasesDefn("cs", FamType(Some(Sp(self_a)), "R"), FunType(RecType(Map()), RecType(Map("C"->FunType(RecType(Map("f"->BType, "n"->NType)), NType)))), Eq,
              DefnBody(Some(Lam(Var("x"), RecType(Map()), Rec(Map("C" -> Lam(Var("r"), RecType(Map("f"->BType, "n"->NType)), NConst(1)))))), None, None)))),
        Map())))
    init(k)
    assert(isLeft(
      typInf(Match(exp, App(FamCases(Some(Sp(self_a)), "cs"), Rec(Map()))))
    ))

    /* // original test
    assertResult(None){
      typInf(Match(exp, App(FamCases(self_a, "cs"), Rec(Map()))), Map(),
        Map(self_a->
          Linkage(self_a, null, Map(), Map(),
            // list of ADTs has R = C {f:B, n:N}
            Map("R"->(Eq, ADT(Map("C"->RecType(Map("f"->BType, "n"->NType)), "K"->RecType(Map()))))), Map(),
            Map("cs"->(FamType(self_a, "R"), Eq, FunType(RecType(Map()), RecType(Map("C"->FunType(RecType(Map("f"->BType, "n"->NType)), NType)))),
              Lam(Var("x"), RecType(Map()), Rec(Map("C" -> Lam(Var("r"), RecType(Map("f"->BType, "n"->NType)), NConst(1))))))))))
    }
     */
  }

  test("typinf: good match with one constructor") {
    val self_a = SelfFamily(Prog, "A")
    // self(A).R({f->true, n->5})
    val exp = InstADT(FamType(Some(Sp(self_a)), "R"), "C", Rec(Map("f"->BConst(true), "n"->NConst(5))))
    val k = Linkage(Sp(Prog), Prog, None, Map(), Map(), Map(), Map(), Map(),
      Map("A" -> Linkage(AbsoluteFamily(Sp(Prog), "A"), self_a, None,
        Map(), Map(),
        Map("R"->(AdtDefn("R", Eq, DefnBody(Some(Map("C"->RecType(Map("f"->BType, "n"->NType)))), None, None)))),
        Map(),
        Map("cs"->(CasesDefn("cs", FamType(Some(Sp(self_a)), "R"), FunType(RecType(Map()), RecType(Map("C"->FunType(RecType(Map("f"->BType, "n"->NType)), NType)))), Eq,
              DefnBody(Some(Lam(Var("x"), RecType(Map()), Rec(Map("C" -> Lam(Var("r"), RecType(Map("f"->BType, "n"->NType)), NConst(1)))))), None, None)))),
        Map())))
    init(k)
    assertResult(Right(NType)){
      typInf(Match(exp, App(FamCases(Some(Sp(self_a)), "cs"), Rec(Map()))))
    }
  }

  test("typinf: type a cases construct") {
    val self_a = SelfFamily(Prog, "A")
    // self(A).R({f->true, n->5})
    val exp = InstADT(FamType(Some(Sp(self_a)), "R"), "C", Rec(Map("f"->BConst(true), "n"->NConst(5))))
    val k = Linkage(Sp(Prog), Prog, None, Map(), Map(), Map(), Map(), Map(),
      Map("A" -> Linkage(AbsoluteFamily(Sp(Prog), "A"), self_a, None,
        Map(), Map(),
        Map("R"->(AdtDefn("R", Eq, DefnBody(Some(Map("C"->RecType(Map("f"->BType, "n"->NType)))), None, None)))),
        Map(),
        Map("cs"->(CasesDefn("cs", FamType(Some(Sp(self_a)), "R"), FunType(RecType(Map()), RecType(Map("C"->FunType(RecType(Map("f"->BType, "n"->NType)), NType)))), Eq,
              DefnBody(Some(Lam(Var("x"), RecType(Map()), Rec(Map("C" -> Lam(Var("r"), RecType(Map("f"->BType, "n"->NType)), NConst(1)))))), None, None)))),
        Map())))
    init(k)
    assertResult(Right(FunType(RecType(Map()), RecType(Map("C"->FunType(RecType(Map("f"->BType, "n"->NType)), NType)))))){
      typInf(FamCases(Some(Sp(self_a)), "cs"))
    }
  }

  test("typinf: type application of cases to a record") {
    val self_a = SelfFamily(Prog, "A")
    // self(A).R({f->true, n->5})
    val exp = InstADT(FamType(Some(Sp(self_a)), "R"), "C", Rec(Map("f"->BConst(true), "n"->NConst(5))))
    val k = Linkage(Sp(Prog), Prog, None, Map(), Map(), Map(), Map(), Map(),
      Map("A" -> Linkage(AbsoluteFamily(Sp(Prog), "A"), self_a, None,
        Map(), Map(),
        Map("R"->(AdtDefn("R", Eq, DefnBody(Some(Map("C"->RecType(Map("f"->BType, "n"->NType)))), None, None)))),
        Map(),
        Map("cs"->(CasesDefn("cs", FamType(Some(Sp(self_a)), "R"), FunType(RecType(Map()), RecType(Map("C"->FunType(RecType(Map("f"->BType, "n"->NType)), NType)))), Eq,
              DefnBody(Some(Lam(Var("x"), RecType(Map()), Rec(Map("C" -> Lam(Var("r"), RecType(Map("f"->BType, "n"->NType)), NConst(1)))))), None, None)))),
        Map())))
    init(k)
    assertResult(Right(RecType(Map("C"->FunType(RecType(Map("f"->BType, "n"->NType)), NType))))){
      typInf(App(FamCases(Some(Sp(self_a)), "cs"), Rec(Map())))
    }
  }

  /* ==================================== LINKAGE TESTING ==================================== */

  // linkage ( self, parent, types, defaults, adts, funs, cases )

  /* TODO(now)
  // types in A: X = {f: B}, Y = {p: N}
  // types in B: Z = {n: N}, Y += {b: B}
  // concatenated: X = {f: B}, Y = {b: B, p: N}, Z = {n: N}
  test("linkage: concat types") {
    val self_a = SelfFamily(Prog, "A")
    val self_b = SelfFamily(Family("B"))
    assertResult(Linkage(self_b, self_a,
        Map("X"->(Eq, RecType(Map("f"->B))), "Y"->(Eq, RecType(Map("b"->BType, "p"->NType))), "Z"->(Eq, RecType(Map("n"->NType)))),
        Map(), Map(), Map(), Map())){
      concat(
        Linkage(self_a, null,
          Map("X"->(Eq, RecType(Map("f"->B))), "Y"->(Eq, RecType(Map("p"->NType)))), Map(), Map(), Map(), Map()),
        Linkage(self_b, self_a,
          Map("Z"->(Eq, RecType(Map("n"->NType))), "Y"->(PlusEq, RecType(Map("b"->B)))), Map(), Map(), Map(), Map()))
    }
  }

  // types in A: X = C {f: B}, Y = K {p: N}
  // types in B: Z = P {n: N}, Y += J {b: B}
  // concatenated: X = {f: B}, Y = {b: B, p: N}, Z = {n: N}
  test("linkage: concat ADTs") {
    val self_a = SelfFamily(Prog, "A")
    val self_b = SelfFamily(Family("B"))
    assertResult(Linkage(self_b, self_a, Map(), Map(),
      Map("X"->(Eq, ADT(Map("C"->RecType(Map("f"->B))))),
        "Y"->(Eq, ADT(Map("K"->RecType(Map("p"->NType)), "J"->RecType(Map("b"->B))))),
        "Z"->(Eq, ADT(Map("P"->RecType(Map("n"->NType)))))),
      Map(), Map())){
      concat(
        Linkage(self_a, null, Map(), Map(),
          Map("X"->(Eq, ADT(Map("C"->RecType(Map("f"->B))))),
            "Y"->(Eq, ADT(Map("K"->RecType(Map("p"->NType)))))), Map(), Map()),
        Linkage(self_b, self_a, Map(), Map(),
          Map("Z"->(Eq, ADT(Map("P"->RecType(Map("n"->NType))))),
            "Y"->(PlusEq, ADT(Map("J"->RecType(Map("b"->B)))))), Map(), Map()))
    }
  }

  // A has m: (B->N) = lam (x: B). 5
  // B has id: (N->N) = lam (x: N). x
  // concat has both
  test("linkage: concat functions") {
    val self_a = SelfFamily(Prog, "A")
    val self_b = SelfFamily(Family("B"))
    assertResult(Linkage(self_b, self_a, Map(), Map(),Map(),
      Map("m"->(FunType(BType, NType), Lam(Var("x"), BType, NConst(5))),
      "id"->(FunType(N, NType), Lam(Var("x"), N, Var("x")))), Map())){
      concat(
        Linkage(self_a, null, Map(), Map(), Map(),
          Map("m"->(FunType(BType, NType), Lam(Var("x"), BType, NConst(5)))), Map()),
        Linkage(self_b, self_a, Map(), Map(), Map(),
          Map("id"->(FunType(N, NType), Lam(Var("x"), N, Var("x")))), Map()))
    }
  }

  test("linkage: complete linkage function") {
    val self_a = SelfFamily(Prog, "A")
    val self_b = SelfFamily(Prog, "B")
    val self_c = SelfFamily(Prog, "C")
    assertResult(Linkage(self_c, self_b, Map("R"->(Eq, RecType(Map("f"->B)))), Map(), Map(),
      Map("m"->(FunType(BType, NType), Lam(Var("x"), BType, NConst(5))),
        "id"->(FunType(N, NType), Lam(Var("x"), N, Var("x")))), Map())){
      complete_linkage(self_c,
        Map(self_a -> Linkage(self_a, null, Map(), Map(), Map(),
          Map("m"->(FunType(BType, NType), Lam(Var("x"), BType, NConst(5)))), Map()),
        self_b -> Linkage(self_b, self_a, Map(), Map(), Map(),
          Map("id"->(FunType(N, NType), Lam(Var("x"), N, Var("x")))), Map()),
        self_c -> Linkage(self_c, self_b, Map("R"->(Eq, RecType(Map("f"->B)))), Map(), Map(), Map(), Map())), Map())._1
    }
  }

   */

  /* TODO(now)
  // assume .plus is defined and exists in the nat library
  // these are ADTs so they don't need defaults
  test("sums example: can parse base family and triple extension in sums program") {
    assert(canParse(program,
      "Family Base { " +

        "type T = C1 {n: N} | C2 {n1: N, n2: N}" +

        "val sum: (.T -> N) = lam (t: .T). match t with <.sum_cases> {arg = t}" +

        "cases sum_cases <.T>: {arg: .T} -> {C1: {n: N} -> N, C2: {n1: N, n2: N} -> N} =" +
          "lam (r: {arg: .T}). {C1 = lam (x: {n: N}). x.n, C2 = lam (x: {n1: N, n2: N}). (.plus x.n1 x.n2)}" +

      "}" +

      "Family Triple extends A {" +

        "type T += C3 {n1: N, n2: N, n3: N}" +

        "cases sum_cases <.T>: {arg: .T} -> {C3: {n1: N, n2: N, n3: N} -> N} +=" +
          "lam (r: {arg: .T}). {C3 = lam (x: {n1: N, n2: N, n3: N}). ((.plus ((.plus x.n1) x.n2)) x.n3)}" +

        "}"
    ))
  }

  test("sums example: parsing the program produces correct linkages") {
    val prog : String =
      ("Family Base { " +

      "type T = C1 {n: N} | C2 {n1: N, n2: N}" +

      "val plus: (N -> N -> N) = lam (x: N). lam (y: N). 1" +

      "val sum: (.T -> N) = lam (t: .T). match t with <.sum_cases> {arg = t}" +

      "cases sum_cases <.T> : {arg: .T} -> {C1: {n: N} -> N, C2: {n1: N, n2: N} -> N} =" +
        "lam (r: {arg: .T}). {C1 = lam (x: {n: N}). x.n, C2 = lam (x: {n1: N, n2: N}). ((.plus x.n1) x.n2)}" +

      "}" +

      "Family Triple extends Base {" +

      "type T += C3 {n1: N, n2: N, n3: N}" +

      "cases sum_cases <.T> : {arg: .T} -> {C3: {n1: N, n2: N, n3: N} -> N} +=" +
        "lam (r: {arg: .T}). {C3 = lam (x: {n1: N, n2: N, n3: N}). ((.plus ((.plus x.n1) x.n2)) x.n3)}" +

      "}");

    val self_base = SelfFamily(Family("Base"))
    val self_triple = SelfFamily(Family("Triple"))
    val lkg_base = Linkage(self_base, null, Map(), Map(),
      // adts
      Map("T"->(Eq, ADT(Map("C1"->RecType(Map("n"->NType)), "C2"->RecType(Map("n1"->NType, "n2"->NType)))))),
      // functions
      Map("plus"->(FunType(N, FunType(N,NType)), Lam(Var("x"), N, Lam(Var("y"), N, NConst(1)))),
        "sum"->(FunType(FamType(null, "T"), NType), Lam(Var("t"), FamType(null, "T"),
        Match(Var("t"), App(FamCases(null, "sum_cases"), Rec(Map("arg"->Var("t")))))))),
      // cases
      Map("sum_cases"-> (FamType(null, "T"), Eq,
          // the arrow type of cases
          FunType(RecType(Map("arg"->FamType(null, "T"))),
            RecType(Map("C1"->FunType(RecType(Map("n"->NType)), NType),
                        "C2"->FunType(RecType(Map("n1"->NType, "n2"->NType)), NType)))),
          // the function body of cases
          Lam(Var("r"), RecType(Map("arg"->FamType(null, "T"))),
            Rec(Map("C1"->Lam(Var("x"), RecType(Map("n"->NType)), Proj(Var("x"), "n")),
                    "C2"->Lam(Var("x"), RecType(Map("n1"->NType, "n2"->NType)),
                      App(App(FamFun(null, "plus"), Proj(Var("x"), "n1")), Proj(Var("x"), "n2")))))))))
    val lkg_triple = Linkage(self_triple, self_base, Map(), Map(),
      // adts
      Map("T"->(PlusEq, ADT(Map("C3"->RecType(Map("n1"->NType, "n2"->NType, "n3"->NType)))))),
      Map(),
      // cases
      Map("sum_cases"-> (FamType(null, "T"), PlusEq,
        // the arrow type of cases
        FunType(RecType(Map("arg"->FamType(null, "T"))),
          RecType(Map("C3"->FunType(RecType(Map("n1"->NType, "n2"->NType, "n3"->NType)), NType)))),
        // the function body of cases
        Lam(Var("r"), RecType(Map("arg"->FamType(null, "T"))),
          Rec(Map("C3"->Lam(Var("x"), RecType(Map("n1"->NType, "n2"->NType, "n3"->NType)),
              App(App(FamFun(null, "plus"),
                App(App(FamFun(null, "plus"), Proj(Var("x"), "n1")), Proj(Var("x"), "n2"))),
                Proj(Var("x"), "n3")))))))))

    assertResult(Map(self_base->lkg_base, self_triple->lkg_triple)){parseSuccess(program, prog)}
    assert(process(prog))
    // NOTE: must include parens around the first app (.plus x.n1), otherwise it parses apps right to left
  }
   */

  /* ==================================== wildcard unfolding ==================================== */

  // TODO(now): it doesn't look like wildcard unfolding is implemented?
  ignore("wildcard unfolding: parent only") {
    val prog : String =
      ("Family Base {" +
        "type T = C1 {} | C2 {n: N} | C3 {b: B}" +
        "val f: T -> B = lam (x: T). match x with <fcases> {}" +
        "cases fcases <T> : {} -> {C3: {b: B} -> B, _: {} -> B} = " +
          "lam (_: {}). {C3 = lam (r: {b: B}). r.b, _ = lam (_:{}). false}" +
        "}");
    assertResult(Right(()))(typecheckProcess(prog))
  }

  // TODO(now): ditto?
  ignore("wildcard unfolding: parent and child") {
    val prog : String =
      ("Family Base {" +
        "type T = C1 {} | C2 {n: N} | C3 {b: B}" +
        "val f: T -> B = lam (x: T). match x with <fcases> {}" +
        "cases fcases <T> : {} -> {C3: {b: B} -> B, _: {} -> B} = " +
        "lam (_: {}). {C3 = lam (r: {b: B}). r.b, _ = lam (_:{}). false}" +
        "}" +
        "Family Ext extends Base {" +
        "type T += C4 {} | C5 {b: B}" +
        "cases fcases <T> : {} -> {C5: {b: B} -> B, _: {} -> B} = " +
        "lam (_: {}). {C5 = lam (r: {b: B}). r.b, _ = lam (_:{}). false}" +
        "}"
        );
    assertResult(Right(()))(typecheckProcess(prog))
  }

  test("wildcard unfolding: incomplete match") {
    val prog : String =
      ("Family Base {" +
        "type T = C1 {} | C2 {n: N} | C3 {b: B}" +
        "val f: T -> B = lam (x: T). match x with <fcases> {}" +
        "cases fcases <T> : {} -> {C3: {b: B} -> B} = " +
        "lam (_: {}). {C3 = lam (r: {b: B}). r.b}" +
        "}"
        );
    assertResult(Left("Cases fcases in <>.Base is non-exhaustive."))(typecheckProcess(prog))
  }

  /* ==================================== default handling ==================================== */
  test("default handling: good") {
    val prog : String =
      ("Family Base {" +
        "type T = {x: N = 1, b: B = true}" +
        "val f: N -> T  = lam (k: N). T({x=k})"+
        "}"
        );
    assertResult(Right(()))(typecheckProcess(prog))
  }

  // TODO(now)
  ignore("default handling: bad") {
    val prog : String =
      ("Family Base {" +
        "type T = {x: N, b: B}" +
        "val f: N -> T  = lam (k: N). T({x=k})"+
        "}"
        );
    assertResult(Left(""))(typecheckProcess(prog))
  }

  /* ==================================== TYPING EXAMPLE PROGRAMS ==================================== */

  test("sums example: the program typechecks") {
    val prog : String = """
      Family Base {

        type T = C1 {n: N} | C2 {n1: N, n2: N}

        val plus: (N -> N -> N) = lam (x: N). lam (y: N). 1

        val sum: (T -> N) = lam (t: T). match t with <sum_cases> {arg = t}

        cases sum_cases <T> : {arg: T} -> {C1: {n: N} -> N, C2: {n1: N, n2: N} -> N} =
          lam (r: {arg: T}). {C1 = lam (x: {n: N}). x.n, C2 = lam (x: {n1: N, n2: N}). ((plus x.n1) x.n2)}

      }

      Family Triple extends Base {

        type T += C3 {n1: N, n2: N, n3: N}

        cases sum_cases <T> : {arg: T} -> {C3: {n1: N, n2: N, n3: N} -> N} +=
          lam (r: {arg: T}). {C3 = lam (x: {n1: N, n2: N, n3: N}). ((plus ((plus x.n1) x.n2)) x.n3)}

       }""";
    assertResult(Right(()))(typecheckProcess(prog))
    // NOTE: must include parens around the first app (plus x.n1), otherwise it parses apps right to left
  }

  test("sums better example: the program typechecks") {
    val prog : String = """
      Family Base {

        type T = C1 {n: N} | C2 {n1: N, n2: N}

        val plus: (N -> N -> N) = lam (x: N). lam (y: N). 1

        val sum: (T -> N) = lam (t: T). match t with <sum_cases> {arg = t}

        cases sum_cases <T> : {arg: T} -> {C1: {n: N} -> N, C2: {n1: N, n2: N} -> N} =
          lam (r: {arg: T}). {C1 = lam (x: {n: N}). x.n, C2 = lam (x: {n1: N, n2: N}). ((plus x.n1) x.n2)}

      }

      Family Triple extends Base {

        type T += C3 {n1: N, n2: N, n3: N}

        cases sum_cases <T> : {arg: T} -> {C3: {n1: N, n2: N, n3: N} -> N} +=
          lam (r: {arg: T}). {C3 = lam (x: {n1: N, n2: N, n3: N}). ((plus (sum T(C2 {n1 = x.n1, n2 = x.n2}))) x.n3)}

      }""";
    assertResult(Right(()))(typecheckProcess(prog))
    // NOTE: must include parens around the first app (plus x.n1), otherwise it parses apps right to left
  }

  test("wrap/unwrap example: the program typechecks") {
    val prog : String = """
      Family A {
        type T = {n: N = 1}
        type U = {t: T = T({n=1})}
        val wrap: N->U = lam (k: N). U({t= T({n = k})})
        val unwrap: U->N = lam (u: U). (u.t).n
      }"""
    assertResult(Right(()))(typecheckProcess(prog))
  }

  // a program in which defaults are used (also use this to test translation to scala)
  test("wrap example with more defaults: the program typechecks") {
    val prog : String = """
      Family A {
        type T = {n1: N = 1, n2: N, b: B = true}
        val wrap1: N -> T = lam (k: N). T({n2 = k})
        val wrap2: N -> B -> T = lam (k: N). lam (b: B). T({n2 = k, b = b})
      }"""
    assertResult(Right(()))(typecheckProcess(prog))
  }

  test("even / odd: the program typechecks") {
    val prog : String = """
      Family Peano {
        type Nat = O {} | S {n: Nat}
      }

      Family Even {
        val even: Peano.Nat -> B = lam (n: Peano.Nat). match n with <even_cases> {arg=n}
        cases even_cases <Peano.Nat> : {arg: Peano.Nat} -> {O: {} -> B, S: {n: Peano.Nat} -> B} =
          lam (_: {arg: Peano.Nat}). {O = lam (_:{}). true, S = lam (x: {n: Peano.Nat}). Odd.odd x.n}

      }

      Family Odd {
        val odd: Peano.Nat -> B = lam (n: Peano.Nat). match n with <odd_cases> {arg=n}
        cases odd_cases <Peano.Nat>: {arg: Peano.Nat} -> {O: {} -> B, S: {n: Peano.Nat} -> B} =
          lam (_: {arg: Peano.Nat}). {O = lam (_:{}). false, S = lam (x: {n: Peano.Nat}). Even.even x.n}
      }"""
    assertResult(Right(()))(typecheckProcess(prog))
  }

  test("can parse all relative paths without dots") {
    val prog : String = """
      Family A {
        type T = {n: N}
        type U = {t: T}
        val wrap: N->U = lam (k: N). U({t= T({n = k})})
        val unwrap: U->N = lam (u: U). (u.t).n
        val moot: N->N = lam (k: N). k
      }"""
    assertResult(Right(()))(typecheckProcess(prog))
  }
}
