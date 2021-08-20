import org.scalatest.funsuite.AnyFunSuite
import scala.util.Success
import famlang._
import TestFamParser._

class Testing extends AnyFunSuite {
  test("types: nat") {
    assert(canParse(typ, "N"))
    assert(parse1(typ, "N", N))
  }
}
