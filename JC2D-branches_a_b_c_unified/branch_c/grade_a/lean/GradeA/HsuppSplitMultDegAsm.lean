/- MultDeg assembler: multDegRange from the imported slice files
   (Low 0-15, Q1 16-23, E1 24-27, E2 28-31). No decides here. -/
import GradeA.A2Entry
import GradeA.A2Data
import GradeA.A2RowsNodup
import GradeA.HsuppSplitCommon
import GradeA.HsuppSplitMultDegLow
import GradeA.HsuppSplitMultDegQ1
import GradeA.HsuppSplitMultDegE1
import GradeA.HsuppSplitMultDegE2

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.HsuppSplit

open BranchC.A2Data


theorem multDegRange : ∀ i ∈ List.range 3199,
    wdeg (multList.getD i (0, 0, 0, 0, 0)) ≤
      (if genList.getD i 0 = 0 then 19 else if genList.getD i 0 = 1 then 18
        else if genList.getD i 0 = 2 then 18 else 17) := by
  intro i hi
  rw [List.mem_range] at hi
  have hk : i / 100 < 32 := by omega
  have hr : i % 100 < 100 := Nat.mod_lt _ (by norm_num)
  have hEq : 100 * (i / 100) + i % 100 = i := Nat.div_add_mod i 100
  have hslice : ∀ k : Fin 32, ∀ r ∈ List.range 100,
      wdeg (multList.getD (100 * k.val + r) (0, 0, 0, 0, 0)) ≤
        (if genList.getD (100 * k.val + r) 0 = 0 then 19
          else if genList.getD (100 * k.val + r) 0 = 1 then 18
          else if genList.getD (100 * k.val + r) 0 = 2 then 18 else 17) := by
    intro k; fin_cases k <;> first | exact sliceMultDeg0 | exact sliceMultDeg1 | exact sliceMultDeg2 | exact sliceMultDeg3 | exact sliceMultDeg4 | exact sliceMultDeg5 | exact sliceMultDeg6 | exact sliceMultDeg7 | exact sliceMultDeg8 | exact sliceMultDeg9 | exact sliceMultDeg10 | exact sliceMultDeg11 | exact sliceMultDeg12 | exact sliceMultDeg13 | exact sliceMultDeg14 | exact sliceMultDeg15 | exact sliceMultDeg16 | exact sliceMultDeg17 | exact sliceMultDeg18 | exact sliceMultDeg19 | exact sliceMultDeg20 | exact sliceMultDeg21 | exact sliceMultDeg22 | exact sliceMultDeg23 | exact sliceMultDeg24 | exact sliceMultDeg25 | exact sliceMultDeg26 | exact sliceMultDeg27 | exact sliceMultDeg28 | exact sliceMultDeg29 | exact sliceMultDeg30 | exact sliceMultDeg31
  have h := hslice ⟨i / 100, hk⟩ (i % 100) (List.mem_range.mpr hr)
  rw [hEq] at h
  exact h

end BranchC.HsuppSplit
