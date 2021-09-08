import org.scalatest.funsuite.AnyFunSuite
import famlang._
import TestFamParser._

class FamlangTesting extends AnyFunSuite {

  /* ==================================== PARSER TESTING ==================================== */

  // Parsing Types
  test("types: nat") {
    assert(canParse(typ, "N"))
    assertResult(N){parseSuccess(typ, "N")}
  }

  test("types: bool") {
    assert(canParse(typ, "B"))
    assertResult(B){parseSuccess(typ, "B")}
  }

  test("types: arrow") {
    assert(canParse(typ, "B -> N"))
    assertResult(FunType(B, N)){parseSuccess(typ, "B -> N")}
  }

  test("types: absolute famtype") {
    assert(canParse(typ, "A.R"))
    assertResult(FamType(AbsoluteFamily(Family("A")), "R")){parseSuccess(typ, "A.R")}
  }

  test("types: self famtype") {
    assert(canParse(typ, "self(A).R"))
    assertResult(FamType(SelfFamily(Family("A")), "R")){parseSuccess(typ, "self(A).R")}
  }

  test("types: record type") {
    assert(canParse(typ, "{ a: N, b: B, c: A.R }"))
    assertResult(
      RecType(Map("a"->N, "b"->B, "c"->FamType(AbsoluteFamily(Family("A")), "R")))
    ){parseSuccess(typ, "{ a: N, b: B, c: A.R }")}
  }

  test("types: paren form") {
    assert(canParse(typ, "(B->{})"))
    assertResult(FunType(B, RecType(Map()))){parseSuccess(typ, "(B->{})")}
  }

  // Parsing Expressions
  test("exp: true") {
    assert(canParse(exp, "true"))
    assertResult(Bexp(true)){parseSuccess(exp, "true")}
  }

  test("exp: false") {
    assert(canParse(exp, "false"))
    assertResult(Bexp(false)){parseSuccess(exp, "false")}
  }

  test("exp: nat") {
    assert(canParse(exp, "5"))
    assertResult(Nexp(5)){parseSuccess(exp, "5")}
  }

  test("exp: var") {
    assert(canParse(exp, "x"))
    assertResult(Var("x")){parseSuccess(exp, "x")}
  }

  test("exp: lam") {
    assert(canParse(exp, "lam (x: B). x"))
    assertResult(Lam(Var("x"), B, Var("x"))){parseSuccess(exp, "lam (x: B). x")}
  }

  test("exp: select function from family") {
    assert(canParse(exp, "self(A).calculate"))
    assertResult(FamFun(SelfFamily(Family("A")), "calculate")){parseSuccess(exp, "self(A).calculate")}
  }

  test("exp: app") {
    assert(canParse(exp, "(lam (x: B). x) true"))
    assertResult(App(Lam(Var("x"), B, Var("x")), Bexp(true))){parseSuccess(exp, "(lam (x: B). x) true")}
  }

  test("exp: record") {
    assert(canParse(exp, "{ a = 5 , b = true }"))
    assertResult(Rec(Map("a"-> Nexp(5), "b" -> Bexp(true)))){parseSuccess(exp, "{ a = 5, b = true }")}
  }

  test("exp: projection") {
    assert(canParse(exp, "{ a = 5 , b = true }.b"))
    assertResult(Proj(Rec(Map("a"-> Nexp(5), "b" -> Bexp(true))), "b")){parseSuccess(exp, "{ a = 5 , b = true }.b")}
  }

  test("exp: instance") {
    assert(canParse(exp, "A.R({a = 4})"))
    assertResult(
      Inst(FamType(AbsoluteFamily(Family("A")), "R"), Rec(Map("a"->Nexp(4))))
    ){parseSuccess(exp, "A.R({a = 4})")}
  }

  test("exp: ADT instance") {
    assert(canParse(exp, "A.R(C {})"))
    assertResult(
      InstADT(FamType(AbsoluteFamily(Family("A")), "R"), "C", Rec(Map()))
    ){parseSuccess(exp, "A.R(C {})")}
  }

  test("exp: match") {
    assert(canParse(exp, " match x with A => lam (y: B). true | C => lam (z: N). z "))
    assertResult(
      Match(Var("x"), Map("A"->Lam(Var("y"), B, Bexp(true)), "C"->Lam(Var("z"), N, Var("z"))))
    ){parseSuccess(exp, "match x with A => lam (y: B). true | C => lam (z: N). z")}
  }

  // Parsing Families
  test("famdef one type") {
    assert(canParse(
      famdef, "Family A { type T = {f: B = true, n: N = 3}}"
    ))
    assertResult(
      Linkage(SelfFamily(Family("A")), null,
        Map("T"->(Eq, RecType(Map("f"->B, "n"->N)))),
        Map("T"->(Eq, Rec(Map("f"->Bexp(true), "n"->Nexp(3))))),
        Map(), Map(), Map())
    ){parseSuccess(famdef, "Family A { type T = {f: B = true, n: N = 3}}")}
  }

  test("famdef extends") {
    assert(canParse(
      famdef, "Family A extends C { type T = {f: B = true, n: N = 3}}"
    ))
    assertResult(
      Linkage(SelfFamily(Family("A")), SelfFamily(Family("C")),
        Map("T"->(Eq, RecType(Map("f"->B, "n"->N)))),
        Map("T"->(Eq, Rec(Map("f"->Bexp(true), "n"->Nexp(3))))),
        Map(), Map(), Map())
    ){parseSuccess(famdef, "Family A extends C { type T = {f: B = true, n: N = 3}}")}
  }

  test("famdef extends and plusEquals") {
    assert(canParse(
      famdef, "Family A extends C { type T += {f: B = true, n: N = 3}}"
    ))
    assertResult(
      Linkage(SelfFamily(Family("A")), SelfFamily(Family("C")),
        Map("T"->(PlusEq, RecType(Map("f"->B, "n"->N)))),
        Map("T"->(PlusEq, Rec(Map("f"->Bexp(true), "n"->Nexp(3))))),
        Map(), Map(), Map())
    ){parseSuccess(famdef, "Family A extends C { type T += {f: B = true, n: N = 3}}")}
  }

  test("famdef multiple types") {
    assert(canParse(famdef,
      "Family A { " +
        "type T = {f: B = true, n: N = 3} " +
        "type R = {s: self(A).T = {}}" + // TODO: discuss default handling like this
        "}"
    ))
    assertResult(
      Linkage(SelfFamily(Family("A")), null,
        Map("T"->(Eq, RecType(Map("f"->B, "n"->N))),
            "R"->(Eq, RecType(Map("s"->FamType(SelfFamily(Family("A")), "T"))))),
        Map("T"->(Eq, Rec(Map("f"->Bexp(true), "n"->Nexp(3)))),
            "R"-> (Eq, Rec(Map("s"->Rec(Map()))))),
        Map(), Map(), Map())
    ){parseSuccess(famdef,
      "Family A { " +
      "type T = {f: B = true, n: N = 3} " +
      "type R = {s: self(A).T = {}}" +
      "}")}
  }

  test("famdef types + ADTs") {
    assert(canParse(famdef,
      "Family A { " +
        "type T = {f: B = true, n: N = 3} " +
        "type R = {s: self(A).T = {}}" +
        "type List = Nil {} | Cons {x: N, tail: self(A).List}" +
        "}"
    ))
    assertResult(
      Linkage(SelfFamily(Family("A")), null,
        // types
        Map("T"->(Eq, RecType(Map("f"->B, "n"->N))),
          "R"->(Eq, RecType(Map("s"->FamType(SelfFamily(Family("A")), "T"))))),
        // defaults
        Map("T"->(Eq, Rec(Map("f"->Bexp(true), "n"->Nexp(3)))),
          "R"-> (Eq, Rec(Map("s"->Rec(Map()))))),
        // adts
        Map("List"->
          (Eq, ADT(Map(
            "Nil"->RecType(Map()),
            "Cons"->RecType(Map("x"->N, "tail"->FamType(SelfFamily(Family("A")), "List"))))))),
        Map(), Map())
    ){parseSuccess(famdef,
      "Family A { " +
        "type T = {f: B = true, n: N = 3} " +
        "type R = {s: self(A).T = {}}" +
        "type List = Nil {} | Cons {x: N, tail: self(A).List}" +
        "}")}
  }

  test("famdef can parse multiple types and ADTs") {
    assert(canParse(famdef,
      "Family A { " +
        "type T = {f: B = true, n: N = 3} " +
        "type R = {s: self(A).T = {}}" +
        "type List = Nil {} | Cons {x: N, tail: self(A).List}" +
        "type Weekend = Sat {} | Sun {}" +
        "}"
    ))
  }

  test("famdef can parse types, adts, functions") {
    assert(canParse(famdef,
      "Family A { " +
        "type T = {f: B = true, n: N = 3} " +
        "type R = {s: self(A).T = {}}" +
        "type List = Nil {} | Cons {x: N, tail: self(A).List}" +
        "type Weekend = Sat {} | Sun {}" +
        "val identity: (B -> B) = lam (x: B). x" +
        "}"
    ))
  }

  // Testing Exceptions
  test("exception: duplicate fields in record") {
    assertThrows[Exception](parse(exp, "{f: N, f: B}"))
  }

  test("exception: duplicate constructors in ADT") {
    assertThrows[Exception](parse(adt, "A {} | A {}"))
  }

  // Testing helper function duplicate_headers
  test("helper: duplicate headers absent") {
    assert(
      !duplicate_headers(List(("foo", (FunType(B, N), null)), ("foo", (FunType(N, N), Lam(Var("x"), N, Bexp(true))))))
    )
  }

  test("helper: duplicate headers present") {
    assert(
      duplicate_headers(List(("foo", (FunType(B, N), null)), ("foo", (FunType(B, N), Lam(Var("x"), B, Bexp(true))))))
    )
  }


  test("can parse case ids") {
    assert(canParse(case_id, "hello_world_1"))
  }

  test("can parse cases by themselves") {
    assert(canParse(cases_def, "cases hello_world_1: B -> N = A => lam (x: B). 3 | C => lam (x: B). 4"))
  }

  // TODO: more tests involving parsing cases into linkages?

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














































  /* ==================================== LINKAGE TESTING ==================================== */

}

