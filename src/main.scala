import famfun._
import TestFamParser._
import PrettyPrint._
import type_checking._

import scala.io.Source

object famfun_main {
  def main(args: Array[String]): Unit = {
    // Testing code for now
    val buf = Source.fromFile("res/example")
    val inp = buf.getLines.mkString("\n")
    val progLkg = parse0(pProgram, inp).get

    initK(progLkg)
    print(getCompleteLinkage(Sp(SelfFamily(SelfFamily(Prog, "Y"), "D"))))
  }
  /* TODO: uncomment
  /*====================================== PUTTING IT ALL TOGETHER  ======================================*/

  // function that takes a program, parses out the families and produces incomplete linkages, fixes null family paths
  // (relative paths .R and .m become self(A).R and self(A).m), then concatenates to yield complete linkages, and performs
  // linkage checking on complete linkages, typechecks everything in the program.

  def process(usercode: String): Boolean = {

    /* ================== PARSE PROGRAM, CREATE INCOMPLETE LINKAGES ================== */
    if (!canParse(program, usercode)) then {
      throw new Exception("Cannot parse the program.")
    }
    // context of incomplete linkages, fresh from the parser
    var map_inc: Map[FamilyPath, Linkage] = parseSuccess(program, usercode);

    /* ================== TRANSFORM INCOMPLETE LINKAGES (MISSING PATHS, UNFOLD WILDCARDS) ================== */
    // update all null paths with self paths (.T is parsed as a family type T with null family)
    map_inc = map_inc.map{case(p, lkg)=> (p, update_paths(lkg, null, lkg.self))};
    map_inc = map_inc.map{case(p, lkg)=> (p, unfold_wildcards(lkg, map_inc))};

    /* ================== BUILD COMPLETE LINKAGES BY CONCATENATION ================== */
    // for each linkage in the map, build a complete linkage
    var M = Map[FamilyPath, Linkage]()
    // for each incomplete linkage, build a complete one using memoization to remember previously computed stuff
    for (p <- map_inc.keySet) {
      map_inc.get(p) match {
        case Some(lkg) =>
          val (complete_lkg, updatedM) = complete_linkage(p, map_inc, M);
          M = updatedM;
        case _ => assert(false);
      }
    }

    // fill in the missing defaults
    M = M.map{case (p, lkg) => (p, fill_defaults_lkg(lkg, M))}

    // TESTING
    //complete_map.map{case (p, lkg) => print_lkg(lkg)}

    /* ================== TYPECHECK ALL LINKAGES ================== */
    // typecheck everything and return true if linkage typechecks
    return !M.exists{ case(p, lkg) => !linkage_ok(lkg, Map(), M)}
  }
*/
}