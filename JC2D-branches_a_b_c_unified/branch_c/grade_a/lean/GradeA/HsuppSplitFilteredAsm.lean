/- Filtered assembler: filteredLength from the imported half files, via
   an append chain (boxAll = concat of the 25 slice boxes, by rfl on the
   spine) instead of the map-sum show, which is suspect in the full
   file's rc=137 death. No decides here. -/
import GradeA.A2Entry
import GradeA.A2Data
import GradeA.A2RowsNodup
import GradeA.HsuppSplitCommon
import GradeA.HsuppSplitFilteredLow
import GradeA.HsuppSplitFilteredHigh

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.HsuppSplit

open BranchC.A2Data


def boxAll : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 25).flatMap (fun t =>
      (List.range 13).flatMap (fun s =>
        (List.range 9).flatMap (fun r =>
          (List.range 9).flatMap (fun u =>
            (List.range 7).map (fun q => (t, s, r, u, q))))))

theorem filteredLength :
    (boxAll.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length = 3199 := by
  have hbox : boxAll = boxSlice0 ++ boxSlice1 ++ boxSlice2 ++ boxSlice3 ++ boxSlice4 ++ boxSlice5 ++ boxSlice6 ++ boxSlice7 ++ boxSlice8 ++ boxSlice9 ++ boxSlice10 ++ boxSlice11 ++ boxSlice12 ++ boxSlice13 ++ boxSlice14 ++ boxSlice15 ++ boxSlice16 ++ boxSlice17 ++ boxSlice18 ++ boxSlice19 ++ boxSlice20 ++ boxSlice21 ++ boxSlice22 ++ boxSlice23 ++ boxSlice24 := rfl
  rw [hbox]
  simp only [List.filter_append, List.length_append]
  rw [sliceFiltered0]
  rw [sliceFiltered1]
  rw [sliceFiltered2]
  rw [sliceFiltered3]
  rw [sliceFiltered4]
  rw [sliceFiltered5]
  rw [sliceFiltered6]
  rw [sliceFiltered7]
  rw [sliceFiltered8]
  rw [sliceFiltered9]
  rw [sliceFiltered10]
  rw [sliceFiltered11]
  rw [sliceFiltered12]
  rw [sliceFiltered13]
  rw [sliceFiltered14]
  rw [sliceFiltered15]
  rw [sliceFiltered16]
  rw [sliceFiltered17]
  rw [sliceFiltered18]
  rw [sliceFiltered19]
  rw [sliceFiltered20]
  rw [sliceFiltered21]
  rw [sliceFiltered22]
  rw [sliceFiltered23]
  rw [sliceFiltered24]
  norm_num

end BranchC.HsuppSplit
