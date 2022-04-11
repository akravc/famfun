import org.scalatest.funsuite.AnyFunSuite
import famfun._
import name_resolution._
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
    assertResult(N){parseSuccess(pType, "N")}
  }

  test("types: bool") {
    assert(canParse(pType, "B"))
    assertResult(B){parseSuccess(pType, "B")}
  }

  test("types: arrow") {
    assert(canParse(pType, "B -> N"))
    assertResult(FunType(B, N)){parseSuccess(pType, "B -> N")}
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
      RecType(Map("a"->N, "b"->B, "c"->FamType(Some(AbsoluteFamily(Sp(Prog), "A")), "R")))
    ){parseSuccess(pType, "{ a: N, b: B, c: A.R }")}
  }

  test("types: paren form") {
    assert(canParse(pType, "(B->{})"))
    assertResult(FunType(B, RecType(Map()))){parseSuccess(pType, "(B->{})")}
  }

  // Parsing Expressions
  test("exp: true") {
    assert(canParse(pExp, "true"))
    assertResult(Bexp(true)){parseSuccess(pExp, "true")}
  }

  test("exp: false") {
    assert(canParse(pExp, "false"))
    assertResult(Bexp(false)){parseSuccess(pExp, "false")}
  }

  test("exp: nat") {
    assert(canParse(pExp, "5"))
    assertResult(Nexp(5)){parseSuccess(pExp, "5")}
  }

  test("exp: var") {
    assert(canParse(pExp, "x"))
    assertResult(Var("x")){parseSuccess(pExp, "x")}
  }

  test("exp: lam") {
    assert(canParse(pExp, "lam (x: B). x"))
    assertResult(Lam(Var("x"), B, Var("x"))){parseSuccess(pExp, "lam (x: B). x")}
  }

  test("exp: select function from family") {
    assert(canParse(pExp, "self(A).calculate"))
    assertResult(FamFun(Some(Sp(SelfFamily(Prog, "A"))), "calculate")){parseSuccess(pExp, "self(A).calculate")}
  }

  test("exp: app") {
    assert(canParse(pExp, "(lam (x: B). x) true"))
    assertResult(App(Lam(Var("x"), B, Var("x")), Bexp(true))){parseSuccess(pExp, "(lam (x: B). x) true")}
  }

  test("exp: record") {
    assert(canParse(pExp, "{ a = 5 , b = true }"))
    assertResult(Rec(Map("a"-> Nexp(5), "b" -> Bexp(true)))){parseSuccess(pExp, "{ a = 5, b = true }")}
  }

  test("exp: projection") {
    assert(canParse(pExp, "{ a = 5 , b = true }.b"))
    assertResult(Proj(Rec(Map("a"-> Nexp(5), "b" -> Bexp(true))), "b")){parseSuccess(pExp, "{ a = 5 , b = true }.b")}
  }

  test("exp: instance") {
    assert(canParse(pExp, "A.R({a = 4})"))
    assertResult(
      Inst(FamType(Some(AbsoluteFamily(Sp(Prog), "A")), "R"), Rec(Map("a"->Nexp(4))))
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
        Map("T" -> TypeDefn("T", Eq, DefnBody(Some(RecType(Map("f"->B, "n"->N))), None, None))),
        Map("T" -> DefaultDefn("T", Eq, DefnBody(Some(Rec(Map("f"->Bexp(true), "n"->Nexp(3)))), None, None))),
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
        Map("T" -> TypeDefn("T", Eq, DefnBody(Some(RecType(Map("f"->B, "n"->N))), None, None))),
        Map("T" -> DefaultDefn("T", Eq, DefnBody(Some(Rec(Map("f"->Bexp(true), "n"->Nexp(3)))), None, None))),
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
        Map("T" -> TypeDefn("T", PlusEq, DefnBody(Some(RecType(Map("f"->B, "n"->N))), None, None))),
        Map("T" -> DefaultDefn("T", PlusEq, DefnBody(Some(Rec(Map("f"->Bexp(true), "n"->Nexp(3)))), None, None))),
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
          "T" -> TypeDefn("T", Eq, DefnBody(Some(RecType(Map("f"->B, "n"->N))), None, None)),
          "R" -> TypeDefn("R", Eq, DefnBody(Some(RecType(Map("s"->FamType(Some(Sp(SelfFamily(Prog, "A"))), "T")))), None, None))
        ),
        Map(
          "T" -> DefaultDefn("T", Eq, DefnBody(Some(Rec(Map("f"->Bexp(true), "n"->Nexp(3)))), None, None)),
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
          "T" -> TypeDefn("T", Eq, DefnBody(Some(RecType(Map("f"->B, "n"->N))), None, None)),
          "R" -> TypeDefn("R", Eq, DefnBody(Some(RecType(Map("s"->FamType(Some(Sp(SelfFamily(Prog, "A"))), "T")))), None, None))
        ),
        // defaults
        Map(
          "T" -> DefaultDefn("T", Eq, DefnBody(Some(Rec(Map("f"->Bexp(true), "n"->Nexp(3)))), None, None)),
          "R" -> DefaultDefn("R", Eq, DefnBody(Some(Rec(Map("s"->Rec(Map())))), None, None))
        ),
        // adts
        Map(
          "List"-> AdtDefn(
            "List", Eq, DefnBody(
              Some(Map(
                "Nil" -> RecType(Map()),
                "Cons" -> RecType(Map(
                  "x" -> N,
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

    val resolvedLkg: Linkage = resolveSelfPaths(parseSuccess(pFamDef(Prog), inp)._2).getOrElse(throw new Exception("?"))

    assertResult(
      DefnBody(
        Some(Lam(Var("x"), B, Var("x"))),
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
      resolveSelfPaths(parseSuccess(pFamDef(Prog), inp)._2).getOrElse(throw new Exception("?"))

    assertResult(
      DefnBody(
        Some(FamFun(Some(Sp(SelfFamily(Prog, "A"))), "y")),
        None,
        None
      )
    ){resolvedLkg.funs("f").funBody}
  }
}

/* TODO: uncomment

class FamFunTesting extends AnyFunSuite {
  /* ==================================== TYPECHECKER TESTING ==================================== */

  // TESTING IS_VALUE

  test("isvalue: functions") {
    assert(is_value(Lam(Var("x"), B, Var("x"))))
  }

  test("isvalue: bools") {
    assert(is_value(Bexp(true)))
    assert(is_value(Bexp(false)))
  }

  test("isvalue: nats") {
    assert(is_value(Nexp(0)))
    assert(is_value(Nexp(4)))
  }

  test("isvalue: record") {
    assert(is_value(Rec(Map("f"->Nexp(2), "p"->Bexp(true)))))
  }

  test("not a value: record") {
    assert(!is_value(Rec(Map("f"->Var("x"), "p"->Bexp(true)))))
  }

  // A.T({f=2, p=5})
  test("isvalue: instance of a type") {
    assert(is_value(Inst(FamType(SelfFamily(Family("A")), "T"), Rec(Map("f"->Nexp(2), "p"->Nexp(5))))))
  }

  // A.T({f=2, p=x})
  test("not a value: instance of a type") {
    assert(!is_value(Inst(FamType(SelfFamily(Family("A")), "T"), Rec(Map("f"->Nexp(2), "p"->Var("x"))))))
  }

  // A.T(C {f=2, p=5})
  test("isvalue: instance of an ADT") {
    assert(is_value(InstADT(FamType(SelfFamily(Family("A")), "T"), "C", Rec(Map("f"->Nexp(2), "p"->Nexp(5))))))
  }

  // A.T(C {f=2, p=x})
  test("not a value: instance of an ADT") {
    assert(!is_value(InstADT(FamType(SelfFamily(Family("A")), "T"), "C", Rec(Map("f"->Nexp(2), "p"->Var("x"))))))
  }

  test("not a value: other") {
    assert(!is_value(App(Var("x"), Bexp(true))))
  }

  // TESTING WELL-FORMEDNESS

  test("wf: nat") {
    assert(wf(N, Map()))
  }

  test("wf: bool") {
    assert(wf(B, Map()))
  }

  // T = {f: B, n: N}
  // self(A).T is well formed
  test("wf: family type") {
    val self_a = SelfFamily(Family("A")) // path self(A)
    assert(wf(FamType(self_a, "T"),
      Map(self_a-> Linkage(self_a, null,
        Map("T"->(Eq, RecType(Map("f"->B, "n"->N)))), Map(), Map(), Map(), Map()))))
  }

  // List = Nil {} | Cons {x: N, tail: self(A).List}
  // self(A).List is well formed
  test("wf: family ADT type") {
    val self_a = SelfFamily(Family("A")) // path self(A)
    assert(wf(FamType(self_a, "List"),
      Map(self_a-> Linkage(self_a, null, Map(), Map(),
        Map("List"->
          (Eq, ADT(Map(
            "Nil"->RecType(Map()),
            "Cons"->RecType(Map("x"->N, "tail"->FamType(SelfFamily(Family("A")), "List"))))))), Map(), Map()))))
  }

  // N -> B
  test("wf: function type") {
    assert(wf(FunType(N, B), Map()))
  }

  // self(A).T -> N
  test("wf: function type 2") {
    val self_a = SelfFamily(Family("A")) // path self(A)
    assert(wf(FunType(FamType(self_a, "T"), N), Map(self_a-> Linkage(self_a, null,
      Map("T"->(Eq, RecType(Map("f"->B, "n"->N)))), Map(), Map(), Map(), Map()))))
  }

  // self(A).T -> N
  test("wf: function type not in linkage") {
    val self_a = SelfFamily(Family("A")) // path self(A)
    assert(!wf(FunType(FamType(self_a, "T"), N), Map(self_a-> Linkage(self_a, null,
      Map("G"->(Eq, RecType(Map("f"->B, "n"->N)))), Map(), Map(), Map(), Map()))))
  }

  // {f: B, p: N}
  test("wf: record type") {
    assert(wf(RecType(Map("f"->B, "p"->N)), Map()))
  }

  // {f: B, p: self(A).T}
  test("wf: record type 2") {
    val self_a = SelfFamily(Family("A")) // path self(A)
    assert(wf(RecType(Map("f"->B, "p"->FamType(self_a, "T"))),
      Map(self_a-> Linkage(self_a, null,
        Map("T"->(Eq, RecType(Map("f"->B, "n"->N)))), Map(), Map(), Map(), Map()))))
  }

  test("wf: record type not in linkage") {
    val self_a = SelfFamily(Family("A")) // path self(A)
    assert(!wf(RecType(Map("f"->B, "p"->FamType(self_a, "G"))),
      Map(self_a-> Linkage(self_a, null,
        Map("T"->(Eq, RecType(Map("f"->B, "n"->N)))), Map(), Map(), Map(), Map()))))
  }

  test("wf: null type is not") {
    assert(!wf(null, Map()))
  }

  // TESTING SUBTYPING

  test("subtype: the type itself") {
    assert(subtype(B, B, Map()))
  }

  test("subtype: the type itself 2") {
    assert(subtype(N, N, Map()))
  }

  test("subtype: the type itself 3") {
    val self_a = SelfFamily(Family("A")) // path self(A)
    assert(subtype(FamType(self_a, "G"), FamType(self_a, "G"), Map()))
  }

  // {f: B, p: N} <: {f: B}
  test("subtype: rectype width") {
    assert(subtype(RecType(Map("f"->B, "p"->N)), RecType(Map("f"->B)), Map()))
  }

  // {g: {f: B, p: N}} <: {g: {f: B}}
  test("subtype: rectype depth") {
    assert(subtype(RecType(Map("g"->RecType(Map("f"->B, "p"->N)))),
      RecType(Map("g"->RecType(Map("f"->B)))), Map()))
  }

  // {f: B, p: N} <: {f: B, g: N}
  test("subtype: rectype bad") {
    assert(!subtype(RecType(Map("f"->B, "p"->N)), RecType(Map("f"->B, "g"->N)), Map()))
  }

  test("subtype: funtype eq") {
    assert(subtype(FunType(B,N), FunType(B,N), Map()))
  }

  // {f: B} <: {}, therefore:
  // {} -> {f: B} <: {f: B} -> {}
  test("subtype: funtype good") {
    assert(subtype(FunType(RecType(Map()), RecType(Map("f"->B))),
      FunType(RecType(Map("f"->B)),RecType(Map())), Map()))
  }

  test("subtype: funtype bad") {
    assert(!subtype(FunType(RecType(Map()), RecType(Map("f"->B))),
      FunType(RecType(Map("f"->B)),RecType(Map("g"->B))), Map()))
  }

  test("subtype: famtype good") {
    val self_a = SelfFamily(Family("A"))
    assert(subtype(FamType(self_a, "T"), RecType(Map("f"->B)),
      Map(self_a-> Linkage(self_a, null,
        Map("T"->(Eq, RecType(Map("f"->B)))), Map(), Map(), Map(), Map()))))
  }

  test("subtype: famtype mismatch in linkage") {
    val self_a = SelfFamily(Family("A"))
    assert(!subtype(FamType(self_a, "T"), RecType(Map("g"->B)),
      Map(self_a-> Linkage(self_a, null,
        Map("T"->(Eq, RecType(Map("f"->B)))), Map(), Map(), Map(), Map()))))
  }

  test("subtype: famtype bad") {
    val self_a = SelfFamily(Family("A"))
    assert(!subtype(FamType(self_a, "T"), FunType(B,N),
      Map(self_a-> Linkage(self_a, null,
        Map("T"->(Eq, RecType(Map("f"->B)))), Map(), Map(), Map(), Map()))))
  }

  test("subtype: two unrelated types") {
    assert(!subtype(B, FunType(B,N), Map()))
  }

  // TESTING TYP_INF

  test("typinf: nat") {
    assertResult(Some(N)){typInf(Nexp(5), Map(), Map())}
  }

  test("typinf: bool") {
    assertResult(Some(B)){typInf(Bexp(true), Map(), Map())}
    assertResult(Some(B)){typInf(Bexp(false), Map(), Map())}
  }

  test("typinf: var") {
    assertResult(Some(N)){typInf(Var("x"), Map("x"->N), Map())}
  }

  test("typinf: var none") {
    assertResult(None){typInf(Var("x"), Map(), Map())}
  }

  test("typinf: lam") {
    assertResult(Some(FunType(B, N))){
      typInf(Lam(Var("x"), B, Nexp(5)), Map(), Map())
    }
  }

  test("typinf: lam identity") {
    assertResult(Some(FunType(B, B))){
      typInf(Lam(Var("x"), B, Var("x")), Map(), Map())
    }
  }

  test("typinf: app") {
    assertResult(Some(N)){
      typInf(App(Lam(Var("x"), B, Nexp(5)), Bexp(true)), Map(), Map())
    }
  }

  test("typinf: app improper") {
    assertResult(None){
      typInf(App(Var("x"), Bexp(true)), Map(), Map())
    }
  }

  test("typinf: rec") {
    assertResult(Some(RecType(Map("f"->B, "p"->N)))){
      typInf(Rec(Map("f"->Bexp(true), "p"->Nexp(4))), Map(), Map())
    }
  }

  test("typinf: rec improper") {
    assertResult(None){
      typInf(Rec(Map("f"->Bexp(true), "p"->App(Nexp(4), Bexp(true)))), Map(), Map())
    }
  }

  test("typinf: rec empty") {
    assertResult(Some(RecType(Map()))){typInf(Rec(Map()), Map(), Map())}
  }

  test("typinf: null type") {
    assertResult(None){typInf(null, Map(), Map())}
  }

  test("typinf: proj") {
    assertResult(Some(N)){
      typInf(Proj(Rec(Map("f"->Bexp(true), "p"->Nexp(4))), "p"), Map(), Map())
    }
  }

  test("typinf: proj field absent") {
    assertResult(None){
      typInf(Proj(Rec(Map("f"->Bexp(true), "p"->Nexp(4))), "g"), Map(), Map())
    }
  }

  test("typinf: proj from not record") {
    assertResult(None){
      typInf(Proj(Var("x"), "x"), Map(), Map())
    }
  }

  // self(A).m : (B -> N) = lam (x: B). 5
  test("typinf: fam fun") {
    val self_a = SelfFamily(Family("A"))
    assertResult(Some(FunType(B, N))){
      typInf(FamFun(self_a, "m"), Map(),
        Map(self_a-> Linkage(self_a, null,
          Map(), Map(), Map(),
          Map("m"->(FunType(B, N),Lam(Var("x"), B, Nexp(5)))),
          Map())))
    }
  }

  // self(A).m does not exist, we have self(A).g instead
  test("typinf: fam fun not in linkage") {
    val self_a = SelfFamily(Family("A"))
    assertResult(None){
      typInf(FamFun(self_a, "m"), Map(),
        Map(self_a-> Linkage(self_a, null,
          Map(), Map(), Map(),
          Map("g"->(FunType(B, N),Lam(Var("x"), B, Nexp(5)))),
          Map())))
    }
  }

  test("typinf: fam fun, absent linkage for self_a") {
    val self_a = SelfFamily(Family("A"))
    assertResult(None){
      typInf(FamFun(self_a, "m"), Map(), Map())
    }
  }

  // self(A).R({f->true, n->5})
  test("typinf: instance of type") {
    val self_a = SelfFamily(Family("A"))
    assertResult(Some(FamType(self_a, "R"))){
      typInf(Inst(FamType(self_a, "R"), Rec(Map("f"->Bexp(true), "n"->Nexp(5)))), Map(),
        Map(self_a-> Linkage(self_a, null,
          Map("R"->(Eq, RecType(Map("f"->B, "n"->N)))), Map(), Map(), Map(), Map())))
    }
  }

  test("typinf: instance of type wrong field name") {
    val self_a = SelfFamily(Family("A"))
    assertResult(None){
      typInf(Inst(FamType(self_a, "R"), Rec(Map("f"->Bexp(true), "n"->Nexp(5)))), Map(),
        Map(self_a-> Linkage(self_a, null,
          Map("R"->(Eq, RecType(Map("f"->B, "p"->N)))), Map(), Map(), Map(), Map())))
    }
  }

  test("typinf: instance of type wrong field type") {
    val self_a = SelfFamily(Family("A"))
    assertResult(None){
      typInf(Inst(FamType(self_a, "R"), Rec(Map("f"->Bexp(true), "n"->Nexp(5)))), Map(),
        Map(self_a-> Linkage(self_a, null,
          Map("R"->(Eq, RecType(Map("f"->B, "n"->B)))), Map(), Map(), Map(), Map())))
    }
  }

  test("typinf: instance of type wrong type name") {
    val self_a = SelfFamily(Family("A"))
    assertResult(None){
      typInf(Inst(FamType(self_a, "K"), Rec(Map("f"->Bexp(true), "n"->Nexp(5)))), Map(),
        Map(self_a-> Linkage(self_a, null,
          Map("R"->(Eq, RecType(Map("f"->B, "n"->N)))), Map(), Map(), Map(), Map())))
    }
  }

  // self(A).R(C {f->true, n->5})
  test("typinf: instance of ADT") {
    val self_a = SelfFamily(Family("A"))
    assertResult(Some(FamType(self_a, "R"))){
      typInf(InstADT(FamType(self_a, "R"), "C", Rec(Map("f"->Bexp(true), "n"->Nexp(5)))), Map(),
        Map(self_a-> Linkage(self_a, null, Map(), Map(),
          Map("R"->(Eq, ADT(Map("C"->RecType(Map("f"->B, "n"->N)))))), Map(), Map())))
    }
  }

  test("typinf: instance of ADT wrong field name") {
    val self_a = SelfFamily(Family("A"))
    assertResult(None){
      typInf(InstADT(FamType(self_a, "R"), "C", Rec(Map("f"->Bexp(true), "n"->Nexp(5)))), Map(),
        Map(self_a-> Linkage(self_a, null, Map(), Map(),
          Map("R"->(Eq, ADT(Map("C"->RecType(Map("f"->B, "p"->N)))))), Map(), Map())))
    }
  }

  test("typinf: instance of ADT wrong field type") {
    val self_a = SelfFamily(Family("A"))
    assertResult(None){
      typInf(InstADT(FamType(self_a, "R"), "C", Rec(Map("f"->Bexp(true), "n"->Nexp(5)))), Map(),
        Map(self_a-> Linkage(self_a, null, Map(), Map(),
          Map("R"->(Eq, ADT(Map("C"->RecType(Map("f"->B, "n"->B)))))), Map(), Map())))
    }
  }

  test("typinf: instance of ADT wrong constructor name") {
    val self_a = SelfFamily(Family("A"))
    assertResult(None){
      typInf(InstADT(FamType(self_a, "R"), "K", Rec(Map("f"->Bexp(true), "n"->Nexp(5)))), Map(),
        Map(self_a-> Linkage(self_a, null, Map(), Map(),
          Map("R"->(Eq, ADT(Map("C"->RecType(Map("f"->B, "n"->N)))))), Map(), Map())))
    }
  }

  test("typinf: instance of ADT wrong type name") {
    val self_a = SelfFamily(Family("A"))
    assertResult(None){
      typInf(InstADT(FamType(self_a, "K"), "C", Rec(Map("f"->Bexp(true), "n"->Nexp(5)))), Map(),
        Map(self_a-> Linkage(self_a, null, Map(), Map(),
          Map("R"->(Eq, ADT(Map("C"->RecType(Map("f"->B, "n"->N)))))), Map(), Map())))
    }
  }

  test("typinf: instance of ADT empty map in linkage") {
    val self_a = SelfFamily(Family("A"))
    assertResult(None){
      typInf(InstADT(FamType(self_a, "R"), "C", Rec(Map("f"->Bexp(true), "n"->Nexp(5)))), Map(),
        Map(self_a-> Linkage(self_a, null, Map(), Map(),
          Map(), Map(), Map())))
    }
  }

  test("typinf: match not on instance of ADT") {
    assertResult(None){
      typInf(Match(Var("x"), Var("x")), Map(), Map())
    }
  }

  test("typinf: match on instance of type, not ADT") {
    val self_a = SelfFamily(Family("A"))
    // self(A).R({f->true, n->5})
    val exp = Inst(FamType(self_a, "R"), Rec(Map("f"->Bexp(true), "n"->Nexp(5))))
    assertResult(None){
      typInf(Match(exp, exp), Map(), Map())
    }
  }

  test("typinf: match on instance of ADT not in linkage") {
    val self_a = SelfFamily(Family("A"))
    // self(A).R({f->true, n->5})
    val exp = InstADT(FamType(self_a, "R"), "C", Rec(Map("f"->Bexp(true), "n"->Nexp(5))))
    assertResult(None){
      typInf(Match(exp, exp), Map(), Map())
    }
  }

  test("typinf: match on instance of ADT, wrong function type in match") {
    val self_a = SelfFamily(Family("A"))
    // self(A).R({f->true, n->5})
    val exp = InstADT(FamType(self_a, "R"), "C", Rec(Map("f"->Bexp(true), "n"->Nexp(5))))

    assertResult(None){
      typInf(Match(exp, App(FamCases(self_a, "cs"), Rec(Map()))), Map(),
        Map(self_a->
          Linkage(self_a, null, Map(), Map(),
          // list of ADTs has R = C {f:B, n:N}
          Map("R"->(Eq, ADT(Map("C"->RecType(Map("f"->B, "n"->N)))))), Map(),
          Map("cs"->(FamType(self_a, "R"), Eq, FunType(RecType(Map()), RecType(Map("C"->FunType(RecType(Map("f"->N, "n"->N)), N)))),
            Lam(Var("x"), RecType(Map()), Rec(Map("C" -> Lam(Var("r"), RecType(Map("f"->N, "n"->N)), Nexp(1))))))))))
    }
  }

  test("typinf: pattern match not exhaustive") {
    val self_a = SelfFamily(Family("A"))
    // self(A).R({f->true, n->5})
    val exp = InstADT(FamType(self_a, "R"), "C", Rec(Map("f"->Bexp(true), "n"->Nexp(5))))

    assertResult(None){
      typInf(Match(exp, App(FamCases(self_a, "cs"), Rec(Map()))), Map(),
        Map(self_a->
          Linkage(self_a, null, Map(), Map(),
            // list of ADTs has R = C {f:B, n:N}
            Map("R"->(Eq, ADT(Map("C"->RecType(Map("f"->B, "n"->N)), "K"->RecType(Map()))))), Map(),
            Map("cs"->(FamType(self_a, "R"), Eq, FunType(RecType(Map()), RecType(Map("C"->FunType(RecType(Map("f"->B, "n"->N)), N)))),
              Lam(Var("x"), RecType(Map()), Rec(Map("C" -> Lam(Var("r"), RecType(Map("f"->B, "n"->N)), Nexp(1))))))))))
    }
  }

  test("typinf: good match with one constructor") {
    val self_a = SelfFamily(Family("A"))
    // self(A).R({f->true, n->5})
    val exp = InstADT(FamType(self_a, "R"), "C", Rec(Map("f"->Bexp(true), "n"->Nexp(5))))

    assertResult(Some(N)){
      typInf(Match(exp, App(FamCases(self_a, "cs"), Rec(Map()))), Map(),
        Map(self_a->
          Linkage(self_a, null, Map(), Map(),
            // list of ADTs has R = C {f:B, n:N}
            Map("R"->(Eq, ADT(Map("C"->RecType(Map("f"->B, "n"->N)))))), Map(),
            Map("cs"->(FamType(self_a, "R"), Eq, FunType(RecType(Map()), RecType(Map("C"->FunType(RecType(Map("f"->B, "n"->N)), N)))),
              Lam(Var("x"), RecType(Map()), Rec(Map("C" -> Lam(Var("r"), RecType(Map("f"->B, "n"->N)), Nexp(1))))))))))
    }
  }

  test("typinf: type a cases construct") {
    val self_a = SelfFamily(Family("A"))
    // self(A).R({f->true, n->5})
    val exp = InstADT(FamType(self_a, "R"), "C", Rec(Map("f"->Bexp(true), "n"->Nexp(5))))

    assertResult(Some(FunType(RecType(Map()), RecType(Map("C"->FunType(RecType(Map("f"->B, "n"->N)), N)))))){
      typInf(FamCases(self_a, "cs"), Map(),
        Map(self_a->
          Linkage(self_a, null, Map(), Map(),
            // list of ADTs has R = C {f:B, n:N}
            Map("R"->(Eq, ADT(Map("C"->RecType(Map("f"->B, "n"->N)))))), Map(),
            Map("cs"->(FamType(self_a, "R"), Eq, FunType(RecType(Map()), RecType(Map("C"->FunType(RecType(Map("f"->B, "n"->N)), N)))),
              Lam(Var("x"), RecType(Map()), Rec(Map("C" -> Lam(Var("r"), RecType(Map("f"->B, "n"->N)), Nexp(1))))))))))
    }
  }

  test("typinf: type application of cases to a record") {
    val self_a = SelfFamily(Family("A"))
    // self(A).R({f->true, n->5})
    val exp = InstADT(FamType(self_a, "R"), "C", Rec(Map("f"->Bexp(true), "n"->Nexp(5))))

    assertResult(Some(RecType(Map("C"->FunType(RecType(Map("f"->B, "n"->N)), N))))){
      typInf(App(FamCases(self_a, "cs"), Rec(Map())), Map(),
        Map(self_a->
          Linkage(self_a, null, Map(), Map(),
            // list of ADTs has R = C {f:B, n:N}
            Map("R"->(Eq, ADT(Map("C"->RecType(Map("f"->B, "n"->N)))))), Map(),
            Map("cs"->(FamType(self_a, "R"), Eq, FunType(RecType(Map()), RecType(Map("C"->FunType(RecType(Map("f"->B, "n"->N)), N)))),
              Lam(Var("x"), RecType(Map()), Rec(Map("C" -> Lam(Var("r"), RecType(Map("f"->B, "n"->N)), Nexp(1))))))))))
    }
  }


  /* ==================================== LINKAGE TESTING ==================================== */

  // linkage ( self, parent, types, defaults, adts, funs, cases )

  // types in A: X = {f: B}, Y = {p: N}
  // types in B: Z = {n: N}, Y += {b: B}
  // concatenated: X = {f: B}, Y = {b: B, p: N}, Z = {n: N}
  test("linkage: concat types") {
    val self_a = SelfFamily(Family("A"))
    val self_b = SelfFamily(Family("B"))
    assertResult(Linkage(self_b, self_a,
        Map("X"->(Eq, RecType(Map("f"->B))), "Y"->(Eq, RecType(Map("b"->B, "p"->N))), "Z"->(Eq, RecType(Map("n"->N)))),
        Map(), Map(), Map(), Map())){
      concat(
        Linkage(self_a, null,
          Map("X"->(Eq, RecType(Map("f"->B))), "Y"->(Eq, RecType(Map("p"->N)))), Map(), Map(), Map(), Map()),
        Linkage(self_b, self_a,
          Map("Z"->(Eq, RecType(Map("n"->N))), "Y"->(PlusEq, RecType(Map("b"->B)))), Map(), Map(), Map(), Map()))
    }
  }

  // types in A: X = C {f: B}, Y = K {p: N}
  // types in B: Z = P {n: N}, Y += J {b: B}
  // concatenated: X = {f: B}, Y = {b: B, p: N}, Z = {n: N}
  test("linkage: concat ADTs") {
    val self_a = SelfFamily(Family("A"))
    val self_b = SelfFamily(Family("B"))
    assertResult(Linkage(self_b, self_a, Map(), Map(),
      Map("X"->(Eq, ADT(Map("C"->RecType(Map("f"->B))))),
        "Y"->(Eq, ADT(Map("K"->RecType(Map("p"->N)), "J"->RecType(Map("b"->B))))),
        "Z"->(Eq, ADT(Map("P"->RecType(Map("n"->N)))))),
      Map(), Map())){
      concat(
        Linkage(self_a, null, Map(), Map(),
          Map("X"->(Eq, ADT(Map("C"->RecType(Map("f"->B))))),
            "Y"->(Eq, ADT(Map("K"->RecType(Map("p"->N)))))), Map(), Map()),
        Linkage(self_b, self_a, Map(), Map(),
          Map("Z"->(Eq, ADT(Map("P"->RecType(Map("n"->N))))),
            "Y"->(PlusEq, ADT(Map("J"->RecType(Map("b"->B)))))), Map(), Map()))
    }
  }

  // A has m: (B->N) = lam (x: B). 5
  // B has id: (N->N) = lam (x: N). x
  // concat has both
  test("linkage: concat functions") {
    val self_a = SelfFamily(Family("A"))
    val self_b = SelfFamily(Family("B"))
    assertResult(Linkage(self_b, self_a, Map(), Map(),Map(),
      Map("m"->(FunType(B, N), Lam(Var("x"), B, Nexp(5))),
      "id"->(FunType(N, N), Lam(Var("x"), N, Var("x")))), Map())){
      concat(
        Linkage(self_a, null, Map(), Map(), Map(),
          Map("m"->(FunType(B, N), Lam(Var("x"), B, Nexp(5)))), Map()),
        Linkage(self_b, self_a, Map(), Map(), Map(),
          Map("id"->(FunType(N, N), Lam(Var("x"), N, Var("x")))), Map()))
    }
  }

  test("linkage: complete linkage function") {
    val self_a = SelfFamily(Family("A"))
    val self_b = SelfFamily(Family("B"))
    val self_c = SelfFamily(Family("C"))
    assertResult(Linkage(self_c, self_b, Map("R"->(Eq, RecType(Map("f"->B)))), Map(), Map(),
      Map("m"->(FunType(B, N), Lam(Var("x"), B, Nexp(5))),
        "id"->(FunType(N, N), Lam(Var("x"), N, Var("x")))), Map())){
      complete_linkage(self_c,
        Map(self_a -> Linkage(self_a, null, Map(), Map(), Map(),
          Map("m"->(FunType(B, N), Lam(Var("x"), B, Nexp(5)))), Map()),
        self_b -> Linkage(self_b, self_a, Map(), Map(), Map(),
          Map("id"->(FunType(N, N), Lam(Var("x"), N, Var("x")))), Map()),
        self_c -> Linkage(self_c, self_b, Map("R"->(Eq, RecType(Map("f"->B)))), Map(), Map(), Map(), Map())), Map())._1
    }
  }

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
      Map("T"->(Eq, ADT(Map("C1"->RecType(Map("n"->N)), "C2"->RecType(Map("n1"->N, "n2"->N)))))),
      // functions
      Map("plus"->(FunType(N, FunType(N,N)), Lam(Var("x"), N, Lam(Var("y"), N, Nexp(1)))),
        "sum"->(FunType(FamType(null, "T"), N), Lam(Var("t"), FamType(null, "T"),
        Match(Var("t"), App(FamCases(null, "sum_cases"), Rec(Map("arg"->Var("t")))))))),
      // cases
      Map("sum_cases"-> (FamType(null, "T"), Eq,
          // the arrow type of cases
          FunType(RecType(Map("arg"->FamType(null, "T"))),
            RecType(Map("C1"->FunType(RecType(Map("n"->N)), N),
                        "C2"->FunType(RecType(Map("n1"->N, "n2"->N)), N)))),
          // the function body of cases
          Lam(Var("r"), RecType(Map("arg"->FamType(null, "T"))),
            Rec(Map("C1"->Lam(Var("x"), RecType(Map("n"->N)), Proj(Var("x"), "n")),
                    "C2"->Lam(Var("x"), RecType(Map("n1"->N, "n2"->N)),
                      App(App(FamFun(null, "plus"), Proj(Var("x"), "n1")), Proj(Var("x"), "n2")))))))))
    val lkg_triple = Linkage(self_triple, self_base, Map(), Map(),
      // adts
      Map("T"->(PlusEq, ADT(Map("C3"->RecType(Map("n1"->N, "n2"->N, "n3"->N)))))),
      Map(),
      // cases
      Map("sum_cases"-> (FamType(null, "T"), PlusEq,
        // the arrow type of cases
        FunType(RecType(Map("arg"->FamType(null, "T"))),
          RecType(Map("C3"->FunType(RecType(Map("n1"->N, "n2"->N, "n3"->N)), N)))),
        // the function body of cases
        Lam(Var("r"), RecType(Map("arg"->FamType(null, "T"))),
          Rec(Map("C3"->Lam(Var("x"), RecType(Map("n1"->N, "n2"->N, "n3"->N)),
              App(App(FamFun(null, "plus"),
                App(App(FamFun(null, "plus"), Proj(Var("x"), "n1")), Proj(Var("x"), "n2"))),
                Proj(Var("x"), "n3")))))))))

    assertResult(Map(self_base->lkg_base, self_triple->lkg_triple)){parseSuccess(program, prog)}
    assert(process(prog))
    // NOTE: must include parens around the first app (.plus x.n1), otherwise it parses apps right to left
  }

  /* ==================================== wildcard unfolding ==================================== */

  test("wildcard unfolding: parent only") {
    val prog : String =
      ("Family Base {" +
        "type T = C1 {} | C2 {n: N} | C3 {b: B}" +
        "val f: .T -> B = lam (x: .T). match x with <.fcases> {}" +
        "cases fcases <.T> : {} -> {C3: {b: B} -> B, _: {} -> B} = " +
          "lam (_: {}). {C3 = lam (r: {b: B}). r.b, _ = lam (_:{}). false}" +
        "}");
    assert(process(prog))
  }

  test("wildcard unfolding: parent and child") {
    val prog : String =
      ("Family Base {" +
        "type T = C1 {} | C2 {n: N} | C3 {b: B}" +
        "val f: .T -> B = lam (x: .T). match x with <.fcases> {}" +
        "cases fcases <.T> : {} -> {C3: {b: B} -> B, _: {} -> B} = " +
        "lam (_: {}). {C3 = lam (r: {b: B}). r.b, _ = lam (_:{}). false}" +
        "}" +
        "Family Ext extends Base {" +
        "type T += C4 {} | C5 {b: B}" +
        "cases fcases <.T> : {} -> {C5: {b: B} -> B, _: {} -> B} = " +
        "lam (_: {}). {C5 = lam (r: {b: B}). r.b, _ = lam (_:{}). false}" +
        "}"
        );
    assert(process(prog))
  }

  test("wildcard unfolding: incomplete match") {
    val prog : String =
      ("Family Base {" +
        "type T = C1 {} | C2 {n: N} | C3 {b: B}" +
        "val f: .T -> B = lam (x: .T). match x with <.fcases> {}" +
        "cases fcases <.T> : {} -> {C3: {b: B} -> B} = " +
        "lam (_: {}). {C3 = lam (r: {b: B}). r.b}" +
        "}"
        );
    assert(!process(prog))
  }

  /* ==================================== default handling ==================================== */
  test("default handling: good") {
    val prog : String =
      ("Family Base {" +
        "type T = {x: N = 1, b: B = true}" +
        "val f: N -> .T  = lam (k: N). .T({x=k})"+
        "}"
        );
    assert(process(prog))
  }

  test("default handling: bad") {
    val prog : String =
      ("Family Base {" +
        "type T = {x: N, b: B}" +
        "val f: N -> .T  = lam (k: N). .T({x=k})"+
        "}"
        );
    assertThrows[Exception](process(prog))
  }


  /* ==================================== TYPING EXAMPLE PROGRAMS ==================================== */

  test("sums example: the program typechecks") {
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
    assert(process(prog))
    // NOTE: must include parens around the first app (.plus x.n1), otherwise it parses apps right to left
  }

  test("sums better example: the program typechecks") {
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
        "lam (r: {arg: .T}). {C3 = lam (x: {n1: N, n2: N, n3: N}). ((.plus (.sum T(C2 {n1 = x.n1, n2 = x.n2}))) x.n3)}\n" +

        "}");
    assert(process(prog))
    // NOTE: must include parens around the first app (.plus x.n1), otherwise it parses apps right to left
  }

  test("wrap/unwrap example: the program typechecks") {
    val prog : String =
      ("Family A { " +
        "type T = {n: N = 1}" +
        "type U = {t: .T = .T({n=1})}" +
        "val wrap: N->.U = lam (k: N). .U({t= .T({n = k})})" +
        "val unwrap: .U->N = lam (u: .U). (u.t).n" +
        "}"
        );
    assert(process(prog))
  }

  test("wrap/unwrap example with implied relative paths, typechecks") {
    val prog : String =
      ("Family A { " +
        "type T = {n: N = 1}" +
        "type U = {t: T = T({n=1})}" +
        "val wrap: N->U = lam (k: N). U({t=T({n = k})})" +
        "val unwrap: U->N = lam (u: U). (u.t).n" +
        "}"
        );
    assert(process(prog))
  }

  // a program in which defaults are used (also use this to test translation to scala)
  test("wrap example with more defaults: the program typechecks") {
    val prog : String =
      ("Family A { " +
        "type T = {n1: N = 1, n2: N, b: B = true}" +
        "val wrap1: N -> .T = lam (k: N). .T({n2 = k})" +
        "val wrap2: N -> B -> .T = lam (k: N). lam (b: B). .T({n2 = k, b = b})" +
        "}"
        );
    assert(process(prog))
  }

  test("even / odd: the program typechecks") {
    val prog : String =
      ("Family Peano { "+
        "type Nat = O {} | S {n: .Nat}"+ // should be able to have .Nat / self(Peano).Nat here
        "}" +

      "Family Even {" +
        "val even: Peano.Nat -> B = lam (n: Peano.Nat). match n with <.even_cases> {arg=n}" +
        "cases even_cases <Peano.Nat> : {arg: Peano.Nat} -> {O: {} -> B, S: {n: Peano.Nat} -> B} = " +
          "lam (_: {arg: Peano.Nat}). {O = lam (_:{}). true, S = lam (x: {n: Peano.Nat}). Odd.odd x.n}" +

      "}" +

      "Family Odd {" +
        "val odd: Peano.Nat -> B = lam (n: Peano.Nat). match n with <.odd_cases> {arg=n}" +
        "cases odd_cases <Peano.Nat>: {arg: Peano.Nat} -> {O: {} -> B, S: {n: Peano.Nat} -> B} = " +
        "lam (_: {arg: Peano.Nat}). {O = lam (_:{}). false, S = lam (x: {n: Peano.Nat}). Even.even x.n}" +
        "}"
        );
    assert(process(prog))
  }

  test("can parse all relative paths without dots") {
    val prog : String =
      """
      Family A {
        type T = {n: N}
        type U = {t: T}
        val wrap: N->U = lam (k: N). U({t= T({n = k})})
        val unwrap: U->N = lam (u: U). (u.t).n
        val moot: N->N = lam (k: N). k
      }"""
    assert(process(prog))
  }
}
*/