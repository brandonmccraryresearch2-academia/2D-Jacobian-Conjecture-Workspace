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


theorem sliceMultDeg24 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 24 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 24 + r) 0 = 0 then 19 else if genList.getD (100 * 24 + r) 0 = 1 then 18 else if genList.getD (100 * 24 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg25 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 25 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 25 + r) 0 = 0 then 19 else if genList.getD (100 * 25 + r) 0 = 1 then 18 else if genList.getD (100 * 25 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg26 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 26 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 26 + r) 0 = 0 then 19 else if genList.getD (100 * 26 + r) 0 = 1 then 18 else if genList.getD (100 * 26 + r) 0 = 2 then 18 else 17) := by decide

theorem sliceMultDeg27 : ∀ r ∈ List.range 100,
    wdeg (multList.getD (100 * 27 + r) (0, 0, 0, 0, 0)) ≤ (if genList.getD (100 * 27 + r) 0 = 0 then 19 else if genList.getD (100 * 27 + r) 0 = 1 then 18 else if genList.getD (100 * 27 + r) 0 = 2 then 18 else 17) := by decide

end BranchC.HsuppSplit
