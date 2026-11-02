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


theorem sliceMultDeg50_0 : ∀ r ∈ List.range 50,
    wdeg (multList.getD (2800 + r) (0, 0, 0, 0, 0)) ≤
      (if genList.getD (2800 + r) 0 = 0 then 19 else if genList.getD (2800 + r) 0 = 1 then 18
        else if genList.getD (2800 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg50_1 : ∀ r ∈ List.range 50,
    wdeg (multList.getD (2850 + r) (0, 0, 0, 0, 0)) ≤
      (if genList.getD (2850 + r) 0 = 0 then 19 else if genList.getD (2850 + r) 0 = 1 then 18
        else if genList.getD (2850 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg50_2 : ∀ r ∈ List.range 50,
    wdeg (multList.getD (2900 + r) (0, 0, 0, 0, 0)) ≤
      (if genList.getD (2900 + r) 0 = 0 then 19 else if genList.getD (2900 + r) 0 = 1 then 18
        else if genList.getD (2900 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg50_3 : ∀ r ∈ List.range 50,
    wdeg (multList.getD (2950 + r) (0, 0, 0, 0, 0)) ≤
      (if genList.getD (2950 + r) 0 = 0 then 19 else if genList.getD (2950 + r) 0 = 1 then 18
        else if genList.getD (2950 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg50_4 : ∀ r ∈ List.range 50,
    wdeg (multList.getD (3000 + r) (0, 0, 0, 0, 0)) ≤
      (if genList.getD (3000 + r) 0 = 0 then 19 else if genList.getD (3000 + r) 0 = 1 then 18
        else if genList.getD (3000 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg50_5 : ∀ r ∈ List.range 50,
    wdeg (multList.getD (3050 + r) (0, 0, 0, 0, 0)) ≤
      (if genList.getD (3050 + r) 0 = 0 then 19 else if genList.getD (3050 + r) 0 = 1 then 18
        else if genList.getD (3050 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg50_6 : ∀ r ∈ List.range 50,
    wdeg (multList.getD (3100 + r) (0, 0, 0, 0, 0)) ≤
      (if genList.getD (3100 + r) 0 = 0 then 19 else if genList.getD (3100 + r) 0 = 1 then 18
        else if genList.getD (3100 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg50_7 : ∀ r ∈ List.range 50,
    wdeg (multList.getD (3150 + r) (0, 0, 0, 0, 0)) ≤
      (if genList.getD (3150 + r) 0 = 0 then 19 else if genList.getD (3150 + r) 0 = 1 then 18
        else if genList.getD (3150 + r) 0 = 2 then 18 else 17) := by decide

end BranchC.HsuppSplit
