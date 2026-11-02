/- Probe: the filtered box length decide, isolated (same imports as Hsupp). -/
import GradeA.A2Entry
import GradeA.A2Data
import GradeA.A2RowsNodup

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.HsuppProbe

def wdeg (t : Nat × Nat × Nat × Nat × Nat) : Nat :=
  t.1 + 2 * t.2.1 + 3 * t.2.2.1 + 3 * t.2.2.2.1 + 4 * t.2.2.2.2

def qexp (t : Nat × Nat × Nat × Nat × Nat) : Nat := t.2.2.2.2

def boxList : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 25).flatMap (fun t =>
    (List.range 13).flatMap (fun s =>
      (List.range 9).flatMap (fun r =>
        (List.range 9).flatMap (fun u =>
          (List.range 7).map (fun q => (t, s, r, u, q))))))

def filteredList : List (Nat × Nat × Nat × Nat × Nat) :=
  boxList.filter (fun u => decide (wdeg u ≤ 24 ∧ qexp u ≠ 6))

theorem probeFiltered : filteredList.length = 3199 := by decide

end BranchC.HsuppProbe
