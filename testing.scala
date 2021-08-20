import org.scalatest.funsuite.AnyFunSuite
import scala.util.Success
import scala.util.parsing.combinator.*
import TestFamParser._

class Testing extends AnyFunSuite with RegexParsers {

  test("types: nat") {
    assert(parse(typ, "N") = Success(N, _))
  }
}