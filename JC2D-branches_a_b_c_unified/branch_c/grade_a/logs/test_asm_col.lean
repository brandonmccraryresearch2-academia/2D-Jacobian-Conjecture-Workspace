import Mathlib
import RCCommon
import A1Data
import A1DispatchBase
import A1Dispatch0
import A1Dispatch1
import A1Dispatch2
import A1Dispatch3
import A1Dispatch4
import A1Dispatch5
import A1Dispatch6
import A1Dispatch7

set_option exponentiation.threshold 200000
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A1Test

open BranchC.A1Data
open BranchC.A1Inst

/-- colThm assembly with the chunk-7 bound passed as a `(by omega)` term
argument instead of a `have` inside the `first` alternative. -/
theorem colThmTest : ∀ j : Fin 3199,
    BranchC.RankCheck.colOK j.val (XSumNat j.val) = true := by
  intro j
  have hj : j.val < 3199 := j.isLt
  set cc := j.val / 400 with hc_def
  have hc : cc < 8 := by have hj := j.isLt; omega
  have hr : j.val % 400 < 400 := Nat.mod_lt _ (by decide)
  have hd : 400 * cc + j.val % 400 = j.val := by rw [hc_def]; exact Nat.div_add_mod _ _
  interval_cases cc <;> rw [← hd] <;> first | exact colThm0 _ hr | exact colThm1 _ hr | exact colThm2 _ hr | exact colThm3 _ hr | exact colThm4 _ hr | exact colThm5 _ hr | exact colThm6 _ hr | exact colThm7 _ (by omega)

end BranchC.A1Test
