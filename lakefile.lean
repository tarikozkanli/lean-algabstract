
import Lake
open Lake DSL

package algabstract

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_lib Algabstract
