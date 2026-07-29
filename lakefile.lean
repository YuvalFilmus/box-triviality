import Lake

open Lake DSL

package BoxTrivialityProject

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "9de45fe2ae74dd4266ede24a28f9198e0023590a"

@[default_target]
lean_lib BoxTriviality
