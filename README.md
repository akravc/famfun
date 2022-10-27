# famfun

We include the following files:
- `build.sbt`, with our SBT settings
- `src/famfun.scala`, with the representation of our system
- `src/type_checking.scala`, with our typechecker and linkage creation/concatenation engine
- `src/parser.scala`, with the parser for FamFun
- `src/util.scala`, with the pretty-printing capabilities for linkages
- `src/main.scala`, which brings together the parts of our system
- `test/testing.scala`, our testing suite
- `src/translate.scala`, an old defunct translation to non-extensible modules
- `src/code_generation.scala`, a translation to Scala code

The directory `res` contains some sample programs.

## Running

To run the tests, `sbt test`

To generate code, first create `mkdir -p test/gen` once.
Then do `sbt "run EXAMPLE_FILE"`.
For example, `sbt "run res/pretty_example"`.
The generated code will be in `test/gen` and can be compiled with `sbt test`.
The files `res/*scala` contains example main runs for the test. They can be copied to `test/gen` and ran with `test:run`.
