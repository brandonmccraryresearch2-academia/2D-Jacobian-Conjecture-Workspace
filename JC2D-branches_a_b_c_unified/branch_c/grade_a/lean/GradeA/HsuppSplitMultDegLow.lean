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

end BranchC.HsuppSplit
