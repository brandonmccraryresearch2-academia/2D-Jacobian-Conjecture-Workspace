/- Probe A: the sliceAll fin_cases chain alone (imports the half files).
   If this passes, the 25-case chain is innocent and the killer is in the
   induction part of the Ind file. -/
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

def innerFn (t : Nat) : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 13).flatMap (fun s =>
    (List.range 9).flatMap (fun r =>
      (List.range 9).flatMap (fun u =>
        (List.range 7).map (fun q => (t, s, r, u, q)))))

def countList : List Nat :=
  [491, 427, 373, 323, 277, 237, 203, 169, 143, 119, 97, 79, 65, 50, 40, 31, 23, 17, 13, 8, 6, 4, 2, 1, 1]

theorem sliceAll : ∀ t : Fin 25,
    ((innerFn t.val).filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length =
      countList.getD t.val 0 := by
  intro t
  fin_cases t <;> first | exact sliceFiltered0 | exact sliceFiltered1 | exact sliceFiltered2 | exact sliceFiltered3 | exact sliceFiltered4 | exact sliceFiltered5 | exact sliceFiltered6 | exact sliceFiltered7 | exact sliceFiltered8 | exact sliceFiltered9 | exact sliceFiltered10 | exact sliceFiltered11 | exact sliceFiltered12 | exact sliceFiltered13 | exact sliceFiltered14 | exact sliceFiltered15 | exact sliceFiltered16 | exact sliceFiltered17 | exact sliceFiltered18 | exact sliceFiltered19 | exact sliceFiltered20 | exact sliceFiltered21 | exact sliceFiltered22 | exact sliceFiltered23 | exact sliceFiltered24

end BranchC.HsuppSplit
