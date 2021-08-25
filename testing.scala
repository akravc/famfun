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

  test("exp: kw testing") {
    assert(canParse(kw_match, "match"))
    assertResult(Keyword("match")){parseSuccess(kw_match, "match")}
  }

  test("exp: kw testing 2") {
    assert(canParse(kw_with, "with"))
    assertResult(Keyword("with")){parseSuccess(kw_with, "with")}
  }

  test("exp: match") {
    assert(canParse(exp, " match x with A => lam (y: B). true | B => lam (z: N). z "))
    print(parseSuccess(exp, "match x with A => lam (y: B). true | B => lam (z: N). z"))
  }











































}
