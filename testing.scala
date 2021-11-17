import org.scalatest.funsuite.AnyFunSuite
import famlang._
import TestFamParser._
import famlang_main._
import scala.language.postfixOps
import PrettyPrint._
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

  test("parser: cases with underscores") {
    val prog = "Family A {" +
      "type T = C1 {n: N} | C2 {b: B}" +
      "cases tcase <.T> : {} -> {C1: {n: N} -> N, C2: {b: B} -> N, _: {} -> N} = " +
        "lam (x: {}). {C1 = lam (y: {n: N}). 1, C2 = lam (z: {b: B}). 1, _ = lam (w: {}). 0}" +
      "}"
    assert(canParse(famdef, prog))
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

  test("famdef extends and plusEquals, missing defaults") {
    assertThrows[Exception](canParse(
      famdef, "Family A extends C { type T += {f: B, n: N = 3}}"
    ))
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

  test("can parse record fields that are constructors") {
    assert(canParse(field_name, "HelloWorld"))
  }

  test("can parse cases by themselves") {
    assert(canParse(cases_def, "cases hello_world <.T> : {} -> {A: B -> N, C: B -> N} = " +
      "lam (_: {}). {A = lam (x: B). 3, C = lam (x: B). 4}"))
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

//  test("linkage: complete linkage function") {
//    val self_a = SelfFamily(Family("A"))
//    val self_b = SelfFamily(Family("B"))
//    val self_c = SelfFamily(Family("C"))
//    assertResult(Linkage(self_c, self_b, Map("R"->(Eq, RecType(Map("f"->B)))), Map(), Map(),
//      Map("m"->(FunType(B, N), Lam(Var("x"), B, Nexp(5))),
//        "id"->(FunType(N, N), Lam(Var("x"), N, Var("x")))), Map())){
//      complete_linkage(self_c,
//        Map(self_a -> Linkage(self_a, null, Map(), Map(), Map(),
//          Map("m"->(FunType(B, N), Lam(Var("x"), B, Nexp(5)))), Map()),
//        self_b -> Linkage(self_b, self_a, Map(), Map(), Map(),
//          Map("id"->(FunType(N, N), Lam(Var("x"), N, Var("x")))), Map()),
//        self_c -> Linkage(self_c, self_b, Map("R"->(Eq, RecType(Map("f"->B)))), Map(), Map(), Map(), Map())))
//    }
//  }

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

  //TODO: make defaults optional for this test to pass
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

