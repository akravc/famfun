# TODOs

- Well-formed family definitions does not seem to be implemented?
  It checks that default values have the declared type, etc.
  Checking for duplicates is omitted for all the rules -- it's implicit.
  This relation is not definitions, not linkages. So how will we do it?
  The reason it's on the definitions, and not the linkage, is to avoid double checking.
  
- [ ] Uncomment old tests? Search for `TODO(now)` in testing file.

- TODO: think about not having a mutable K but passing it around like it used to be, in particular for `wf`.

- [x] TODO: Even/odd example shows a subtle bug with self path substitution: `Peano` becomes `Odd`!
  It sounds like we're mixing the self of the type being matched against, which might be absolute in the current class.
  Run like this: `sbt:famfun> testOnly *FamFunTesting -- -z even`

- It sounds like we could have some helper functions for all those substitution styles.
- [x] Did recType. Could do for other sorts.

- ignore("typinf: match on instance of ADT, wrong function type in match")
- ignore("typinf: pattern match not exhaustive")

- [x] The generated code for even_odd does not compile with Scala :(

- [ ] The generated code for mixins does not compile with Scala

- Also, we need to specify the self, e.g. `self(IfExt).Base` instead of it being inferred.

- [ ] Should be able to run a "Main" with the code.

- [x] Why is `subSelfInTypeAccordingTo` taking a prefix? Causes trouble for test5. But prefix is necessary for pretty_example.

- [ ] Eliminate dead code.

- [x] Get rid of `throwLeft`.

- [ ] Fix `???/*TODO*/` in transport code generation.
