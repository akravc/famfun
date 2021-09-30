//import famlang._
//import TestFamParser._
//
//object famlang_main {
//  /*====================================== PUTTING IT ALL TOGETHER  ======================================*/
//
//  // function that takes a program, parses out the families and produces incomplete linkages, fixes null family paths
//  // (relative paths .R and .m become self(A).R and self(A).m), then concatenates to yield complete linkages, and performs
//  // linkage checking on complete linkages. Returns a context of complete linkages for use with type cheking, etc.
//
//  def process(usercode: String): Map[FamilyPath, Linkage] = {
//    if (!canParse(program, usercode)) then {
//      throw new Exception("Cannot parse the program.")
//    }
//    // context of incomplete linkages, fresh from the parser
//    var map_inc: Map[FamilyPath, Linkage] = parseSuccess(program, usercode);
//
//
//
//
//
//    return map_inc
//  }
//}