import Lake

open Lake DSL

package BoxTrivialityProject

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "f6633228a768aaa39d18c5d7101d6b09cd673d18"

@[default_target]
lean_lib BoxTriviality
