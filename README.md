# famfun

We include the following files:
- `build.sbt`, with our SBT settings
- `src/famfun.scala`, with the representation of our system
- `src/type_checking.scala`, with our typechecker and linkage creation/concatenation engine
- `src/code_generation.scala`, our translator to Scala code
- `src/parser.scala`, with our parser
- `src/name_resolution.scala`, with our name resolver
- `src/util.scala`, with the pretty-printing capabilities for linkages
- `src/main.scala`, with end to end running
- `test/testing.scala`, our testing suite
- `res/*`, with some sample programs

## Running

To run the tests, `sbt test`

To generate code, first create `mkdir -p test/gen` once.
Then do `sbt "run EXAMPLE_FILE"`.
For example, `sbt "run res/pretty_example"`.
The generated code will be in `test/gen` and can be compiled with `sbt test`.
The files `res/*scala` contains example main runs for the test. They can be copied to `test/gen` and ran with `test:run`.
