# TODOs

- Well-formed family definitions does not seem to be implemented?
  It checks that default values have the declared type, etc.
  Checking for duplicates is omitted for all the rules -- it's implicit.
  This relation is not definitions, not linkages. So how will we do it?
  The reason it's on the definitions, and not the linkage, is to avoid double checking.
  
- Uncomment old tests? Search for `TODO(now)` in testing file.

- TODO: think about not having a mutable K but passing it around like it used to be, in particular for `wf`.

- TODO: Even/odd example shows a subtle bug with self path substitution: `Peano` becomes `Odd`!

