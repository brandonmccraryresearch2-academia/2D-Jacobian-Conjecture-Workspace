/- Validation: one slice of each killer decide, at 1/32 (MultDeg/MultQ)
   and 1/25 (Filtered) scale. If these pass fast, the split design is sound. -/
import GradeA.A2Entry
import GradeA.A2Data
import GradeA.A2RowsNodup

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.HsuppSplit

open BranchC.A2Data

def wdeg (t : Nat × Nat × Nat × Nat × Nat) : Nat :=
  t.1 + 2 * t.2.1 + 3 * t.2.2.1 + 3 * t.2.2.2.1 + 4 * t.2.2.2.2

def qexp (t : Nat × Nat × Nat × Nat × Nat) : Nat := t.2.2.2.2

theorem sliceMultDeg0 : ∀ i ∈ List.range 100,
    wdeg (multList.getD i (0, 0, 0, 0, 0)) ≤
      (if genList.getD i 0 = 0 then 19 else if genList.getD i 0 = 1 then 18
        else if genList.getD i 0 = 2 then 18 else 17) := by decide

theorem sliceMultQ0 : ∀ i ∈ List.range 100,
    qexp (multList.getD i (0, 0, 0, 0, 0)) ≤ 4 := by decide

def boxSlice0 : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 13).flatMap (fun s =>
    (List.range 9).flatMap (fun r =>
      (List.range 9).flatMap (fun u =>
        (List.range 7).map (fun q => (0, s, r, u, q)))))

theorem sliceFiltered0 :
    (boxSlice0.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))).length = 491 := by decide

end BranchC.HsuppSplit
