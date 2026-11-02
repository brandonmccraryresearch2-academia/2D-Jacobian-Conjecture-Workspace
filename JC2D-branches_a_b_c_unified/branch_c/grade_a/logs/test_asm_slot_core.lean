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

/-- Single-branch slotThm (k = 3): tests rw + exact on slotOK/CpkFunNat
content with no case-split machinery at all. -/
theorem slotBranch3 : ∀ i : Fin 3199, i.val / 400 = 3 →
    BranchC.RankCheck.slotOK (CpkFunNat i.val) = true := by
  intro i h3
  have hr : i.val % 400 < 400 := Nat.mod_lt _ (by decide)
  have hd : 400 * (i.val / 400) + i.val % 400 = i.val := Nat.div_add_mod _ _
  rw [← hd, h3]
  exact slotThm3 _ hr

/-- Full slotThm assembly, core-only: nested by_cases on i.val / 400,
no interval_cases, no Mathlib. -/
theorem slotThmCore : ∀ i : Fin 3199,
    BranchC.RankCheck.slotOK (CpkFunNat i.val) = true := by
  intro i
  have hi : i.val < 3199 := i.isLt
  have hr : i.val % 400 < 400 := Nat.mod_lt _ (by decide)
  have hd : 400 * (i.val / 400) + i.val % 400 = i.val := Nat.div_add_mod _ _
  by_cases h0 : i.val / 400 = 0
  · rw [← hd, h0]; exact slotThm0 _ hr
  · by_cases h1 : i.val / 400 = 1
    · rw [← hd, h1]; exact slotThm1 _ hr
    · by_cases h2 : i.val / 400 = 2
      · rw [← hd, h2]; exact slotThm2 _ hr
      · by_cases h3 : i.val / 400 = 3
        · rw [← hd, h3]; exact slotThm3 _ hr
        · by_cases h4 : i.val / 400 = 4
          · rw [← hd, h4]; exact slotThm4 _ hr
          · by_cases h5 : i.val / 400 = 5
            · rw [← hd, h5]; exact slotThm5 _ hr
            · by_cases h6 : i.val / 400 = 6
              · rw [← hd, h6]; exact slotThm6 _ hr
              · have h7 : i.val / 400 = 7 := by omega
                rw [← hd, h7]; exact slotThm7 _ (by omega)

end BranchC.A1Test
