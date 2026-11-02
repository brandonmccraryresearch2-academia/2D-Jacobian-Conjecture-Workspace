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


theorem sliceMultQ0 : ∀ r ∈ List.range 100,
    qexp (multList.getD (100 * 0 + r) (0, 0, 0, 0, 0)) ≤ 4 := by decide

theorem sliceMultQ1 : ∀ r ∈ List.range 100,
    qexp (multList.getD (100 * 1 + r) (0, 0, 0, 0, 0)) ≤ 4 := by decide

theorem sliceMultQ2 : ∀ r ∈ List.range 100,
    qexp (multList.getD (100 * 2 + r) (0, 0, 0, 0, 0)) ≤ 4 := by decide

theorem sliceMultQ3 : ∀ r ∈ List.range 100,
    qexp (multList.getD (100 * 3 + r) (0, 0, 0, 0, 0)) ≤ 4 := by decide

theorem sliceMultQ4 : ∀ r ∈ List.range 100,
    qexp (multList.getD (100 * 4 + r) (0, 0, 0, 0, 0)) ≤ 4 := by decide

theorem sliceMultQ5 : ∀ r ∈ List.range 100,
    qexp (multList.getD (100 * 5 + r) (0, 0, 0, 0, 0)) ≤ 4 := by decide

theorem sliceMultQ6 : ∀ r ∈ List.range 100,
    qexp (multList.getD (100 * 6 + r) (0, 0, 0, 0, 0)) ≤ 4 := by decide

theorem sliceMultQ7 : ∀ r ∈ List.range 100,
    qexp (multList.getD (100 * 7 + r) (0, 0, 0, 0, 0)) ≤ 4 := by decide

theorem sliceMultQ8 : ∀ r ∈ List.range 100,
    qexp (multList.getD (100 * 8 + r) (0, 0, 0, 0, 0)) ≤ 4 := by decide

theorem sliceMultQ9 : ∀ r ∈ List.range 100,
    qexp (multList.getD (100 * 9 + r) (0, 0, 0, 0, 0)) ≤ 4 := by decide

theorem sliceMultQ10 : ∀ r ∈ List.range 100,
    qexp (multList.getD (100 * 10 + r) (0, 0, 0, 0, 0)) ≤ 4 := by decide

theorem sliceMultQ11 : ∀ r ∈ List.range 100,
    qexp (multList.getD (100 * 11 + r) (0, 0, 0, 0, 0)) ≤ 4 := by decide

theorem sliceMultQ12 : ∀ r ∈ List.range 100,
    qexp (multList.getD (100 * 12 + r) (0, 0, 0, 0, 0)) ≤ 4 := by decide

theorem sliceMultQ13 : ∀ r ∈ List.range 100,
    qexp (multList.getD (100 * 13 + r) (0, 0, 0, 0, 0)) ≤ 4 := by decide

theorem sliceMultQ14 : ∀ r ∈ List.range 100,
    qexp (multList.getD (100 * 14 + r) (0, 0, 0, 0, 0)) ≤ 4 := by decide

theorem sliceMultQ15 : ∀ r ∈ List.range 100,
    qexp (multList.getD (100 * 15 + r) (0, 0, 0, 0, 0)) ≤ 4 := by decide

theorem sliceMultQ16 : ∀ r ∈ List.range 100,
    qexp (multList.getD (100 * 16 + r) (0, 0, 0, 0, 0)) ≤ 4 := by decide

theorem sliceMultQ17 : ∀ r ∈ List.range 100,
    qexp (multList.getD (100 * 17 + r) (0, 0, 0, 0, 0)) ≤ 4 := by decide

theorem sliceMultQ18 : ∀ r ∈ List.range 100,
    qexp (multList.getD (100 * 18 + r) (0, 0, 0, 0, 0)) ≤ 4 := by decide

theorem sliceMultQ19 : ∀ r ∈ List.range 100,
    qexp (multList.getD (100 * 19 + r) (0, 0, 0, 0, 0)) ≤ 4 := by decide

theorem sliceMultQ20 : ∀ r ∈ List.range 100,
    qexp (multList.getD (100 * 20 + r) (0, 0, 0, 0, 0)) ≤ 4 := by decide

theorem sliceMultQ21 : ∀ r ∈ List.range 100,
    qexp (multList.getD (100 * 21 + r) (0, 0, 0, 0, 0)) ≤ 4 := by decide

theorem sliceMultQ22 : ∀ r ∈ List.range 100,
    qexp (multList.getD (100 * 22 + r) (0, 0, 0, 0, 0)) ≤ 4 := by decide

theorem sliceMultQ23 : ∀ r ∈ List.range 100,
    qexp (multList.getD (100 * 23 + r) (0, 0, 0, 0, 0)) ≤ 4 := by decide

theorem sliceMultQ24 : ∀ r ∈ List.range 100,
    qexp (multList.getD (100 * 24 + r) (0, 0, 0, 0, 0)) ≤ 4 := by decide

theorem sliceMultQ25 : ∀ r ∈ List.range 100,
    qexp (multList.getD (100 * 25 + r) (0, 0, 0, 0, 0)) ≤ 4 := by decide

theorem sliceMultQ26 : ∀ r ∈ List.range 100,
    qexp (multList.getD (100 * 26 + r) (0, 0, 0, 0, 0)) ≤ 4 := by decide

theorem sliceMultQ27 : ∀ r ∈ List.range 100,
    qexp (multList.getD (100 * 27 + r) (0, 0, 0, 0, 0)) ≤ 4 := by decide

theorem sliceMultQ28 : ∀ r ∈ List.range 100,
    qexp (multList.getD (100 * 28 + r) (0, 0, 0, 0, 0)) ≤ 4 := by decide

theorem sliceMultQ29 : ∀ r ∈ List.range 100,
    qexp (multList.getD (100 * 29 + r) (0, 0, 0, 0, 0)) ≤ 4 := by decide

theorem sliceMultQ30 : ∀ r ∈ List.range 100,
    qexp (multList.getD (100 * 30 + r) (0, 0, 0, 0, 0)) ≤ 4 := by decide

theorem sliceMultQ31 : ∀ r ∈ List.range 100,
    qexp (multList.getD (100 * 31 + r) (0, 0, 0, 0, 0)) ≤ 4 := by decide

theorem multQRange : ∀ i ∈ List.range 3199,
    qexp (multList.getD i (0, 0, 0, 0, 0)) ≤ 4 := by
  intro i hi
  rw [List.mem_range] at hi
  have hk : i / 100 < 32 := by omega
  have hr : i % 100 < 100 := Nat.mod_lt _ (by norm_num)
  have hEq : 100 * (i / 100) + i % 100 = i := Nat.div_add_mod i 100
  have hslice : ∀ k : Fin 32, ∀ r ∈ List.range 100,
      qexp (multList.getD (100 * k.val + r) (0, 0, 0, 0, 0)) ≤ 4 := by
    intro k; fin_cases k <;> first | exact sliceMultQ0 | exact sliceMultQ1 | exact sliceMultQ2 | exact sliceMultQ3 | exact sliceMultQ4 | exact sliceMultQ5 | exact sliceMultQ6 | exact sliceMultQ7 | exact sliceMultQ8 | exact sliceMultQ9 | exact sliceMultQ10 | exact sliceMultQ11 | exact sliceMultQ12 | exact sliceMultQ13 | exact sliceMultQ14 | exact sliceMultQ15 | exact sliceMultQ16 | exact sliceMultQ17 | exact sliceMultQ18 | exact sliceMultQ19 | exact sliceMultQ20 | exact sliceMultQ21 | exact sliceMultQ22 | exact sliceMultQ23 | exact sliceMultQ24 | exact sliceMultQ25 | exact sliceMultQ26 | exact sliceMultQ27 | exact sliceMultQ28 | exact sliceMultQ29 | exact sliceMultQ30 | exact sliceMultQ31
  have h := hslice ⟨i / 100, hk⟩ (i % 100) (List.mem_range.mpr hr)
  rw [hEq] at h
  exact h

end BranchC.HsuppSplit
