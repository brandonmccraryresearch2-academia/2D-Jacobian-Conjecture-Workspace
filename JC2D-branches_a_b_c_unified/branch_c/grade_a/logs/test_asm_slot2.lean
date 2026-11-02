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

/-- slotThm assembly with the chunk-7 bound as a `(by omega)` term
argument (same shape as the passing colThm test). Tests whether the
whnf timeout is the have-in-first issue or something slot-specific. -/
theorem slotThmTest2 : ∀ i : Fin 3199,
    BranchC.RankCheck.slotOK (CpkFunNat i.val) = true := by
  intro i
  have hi : i.val < 3199 := i.isLt
  set cc := i.val / 400 with hc_def
  have hc : cc < 8 := by have hi := i.isLt; omega
  have hr : i.val % 400 < 400 := Nat.mod_lt _ (by decide)
  have hd : 400 * cc + i.val % 400 = i.val := by rw [hc_def]; exact Nat.div_add_mod _ _
  interval_cases cc <;> rw [← hd] <;> first | exact slotThm0 _ hr | exact slotThm1 _ hr | exact slotThm2 _ hr | exact slotThm3 _ hr | exact slotThm4 _ hr | exact slotThm5 _ hr | exact slotThm6 _ hr | exact slotThm7 _ (by omega)

end BranchC.A1Test
