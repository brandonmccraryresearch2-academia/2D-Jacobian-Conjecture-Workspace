/- Split decides for Hsupp (see Hsupp.lean): the three full-size decides
   each died rc=137 alone, so each is proved here in small slices plus a
   combiner. One small decide per command; working memory is freed
   between commands. wdeg/qexp come from HsuppSplitCommon (single
   definition, shared so files can be imported together). -/
import GradeA.A2Entry
import GradeA.A2Data
import GradeA.A2RowsNodup
import GradeA.HsuppSplitCommon

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.HsuppSplit

open BranchC.A2Data


theorem sliceMultDeg0 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 0 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 0 + r) 0 = 0 then 19 else if genList.getD (100 * 0 + r) 0 = 1 then 18 else if genList.getD (100 * 0 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg1 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 1 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 1 + r) 0 = 0 then 19 else if genList.getD (100 * 1 + r) 0 = 1 then 18 else if genList.getD (100 * 1 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg2 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 2 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 2 + r) 0 = 0 then 19 else if genList.getD (100 * 2 + r) 0 = 1 then 18 else if genList.getD (100 * 2 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg3 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 3 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 3 + r) 0 = 0 then 19 else if genList.getD (100 * 3 + r) 0 = 1 then 18 else if genList.getD (100 * 3 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg4 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 4 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 4 + r) 0 = 0 then 19 else if genList.getD (100 * 4 + r) 0 = 1 then 18 else if genList.getD (100 * 4 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg5 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 5 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 5 + r) 0 = 0 then 19 else if genList.getD (100 * 5 + r) 0 = 1 then 18 else if genList.getD (100 * 5 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg6 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 6 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 6 + r) 0 = 0 then 19 else if genList.getD (100 * 6 + r) 0 = 1 then 18 else if genList.getD (100 * 6 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg7 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 7 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 7 + r) 0 = 0 then 19 else if genList.getD (100 * 7 + r) 0 = 1 then 18 else if genList.getD (100 * 7 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg8 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 8 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 8 + r) 0 = 0 then 19 else if genList.getD (100 * 8 + r) 0 = 1 then 18 else if genList.getD (100 * 8 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg9 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 9 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 9 + r) 0 = 0 then 19 else if genList.getD (100 * 9 + r) 0 = 1 then 18 else if genList.getD (100 * 9 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg10 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 10 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 10 + r) 0 = 0 then 19 else if genList.getD (100 * 10 + r) 0 = 1 then 18 else if genList.getD (100 * 10 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg11 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 11 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 11 + r) 0 = 0 then 19 else if genList.getD (100 * 11 + r) 0 = 1 then 18 else if genList.getD (100 * 11 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg12 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 12 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 12 + r) 0 = 0 then 19 else if genList.getD (100 * 12 + r) 0 = 1 then 18 else if genList.getD (100 * 12 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg13 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 13 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 13 + r) 0 = 0 then 19 else if genList.getD (100 * 13 + r) 0 = 1 then 18 else if genList.getD (100 * 13 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg14 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 14 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 14 + r) 0 = 0 then 19 else if genList.getD (100 * 14 + r) 0 = 1 then 18 else if genList.getD (100 * 14 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg15 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 15 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 15 + r) 0 = 0 then 19 else if genList.getD (100 * 15 + r) 0 = 1 then 18 else if genList.getD (100 * 15 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg16 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 16 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 16 + r) 0 = 0 then 19 else if genList.getD (100 * 16 + r) 0 = 1 then 18 else if genList.getD (100 * 16 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg17 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 17 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 17 + r) 0 = 0 then 19 else if genList.getD (100 * 17 + r) 0 = 1 then 18 else if genList.getD (100 * 17 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg18 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 18 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 18 + r) 0 = 0 then 19 else if genList.getD (100 * 18 + r) 0 = 1 then 18 else if genList.getD (100 * 18 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg19 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 19 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 19 + r) 0 = 0 then 19 else if genList.getD (100 * 19 + r) 0 = 1 then 18 else if genList.getD (100 * 19 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg20 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 20 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 20 + r) 0 = 0 then 19 else if genList.getD (100 * 20 + r) 0 = 1 then 18 else if genList.getD (100 * 20 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg21 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 21 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 21 + r) 0 = 0 then 19 else if genList.getD (100 * 21 + r) 0 = 1 then 18 else if genList.getD (100 * 21 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg22 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 22 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 22 + r) 0 = 0 then 19 else if genList.getD (100 * 22 + r) 0 = 1 then 18 else if genList.getD (100 * 22 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg23 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 23 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 23 + r) 0 = 0 then 19 else if genList.getD (100 * 23 + r) 0 = 1 then 18 else if genList.getD (100 * 23 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg24 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 24 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 24 + r) 0 = 0 then 19 else if genList.getD (100 * 24 + r) 0 = 1 then 18 else if genList.getD (100 * 24 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg25 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 25 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 25 + r) 0 = 0 then 19 else if genList.getD (100 * 25 + r) 0 = 1 then 18 else if genList.getD (100 * 25 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg26 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 26 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 26 + r) 0 = 0 then 19 else if genList.getD (100 * 26 + r) 0 = 1 then 18 else if genList.getD (100 * 26 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg27 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 27 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 27 + r) 0 = 0 then 19 else if genList.getD (100 * 27 + r) 0 = 1 then 18 else if genList.getD (100 * 27 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg28 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 28 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 28 + r) 0 = 0 then 19 else if genList.getD (100 * 28 + r) 0 = 1 then 18 else if genList.getD (100 * 28 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg29 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 29 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 29 + r) 0 = 0 then 19 else if genList.getD (100 * 29 + r) 0 = 1 then 18 else if genList.getD (100 * 29 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg30 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 30 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 30 + r) 0 = 0 then 19 else if genList.getD (100 * 30 + r) 0 = 1 then 18 else if genList.getD (100 * 30 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg31 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 31 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 31 + r) 0 = 0 then 19 else if genList.getD (100 * 31 + r) 0 = 1 then 18 else if genList.getD (100 * 31 + r) 0 = 2 then 18 else 17) := by decide

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
