import org.scalatest.funsuite.AnyFunSuite
import famlang._
import TestFamParser._

class ParserTesting extends AnyFunSuite {
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
        Map(), Map())
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
        Map(), Map())
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
        Map(), Map())
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
        Map(), Map())
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
        Map())
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
    assertResult(false) {
      duplicate_headers(List(("foo", (FunType(B, N), null)), ("foo", (FunType(N, N), Lam(Var("x"), N, Bexp(true))))))
    }
  }

  test("helper: duplicate headers present") {
    assertResult(true){
      duplicate_headers(List(("foo", (FunType(B, N), null)), ("foo", (FunType(B, N), Lam(Var("x"), B, Bexp(true))))))
    }
  }





























































}
