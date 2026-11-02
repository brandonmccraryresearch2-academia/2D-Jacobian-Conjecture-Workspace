/- Probe: the multDeg range decide, isolated (same imports as Hsupp). -/
import GradeA.A2Entry
import GradeA.A2Data
import GradeA.A2RowsNodup

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.HsuppProbe

open BranchC.A2Data

def wdeg (t : Nat × Nat × Nat × Nat × Nat) : Nat :=
  t.1 + 2 * t.2.1 + 3 * t.2.2.1 + 3 * t.2.2.2.1 + 4 * t.2.2.2.2

theorem probeMultDeg : ∀ i ∈ List.range 3199,
    wdeg (multList.getD i (0, 0, 0, 0, 0)) ≤
      (if genList.getD i 0 = 0 then 19 else if genList.getD i 0 = 1 then 18
        else if genList.getD i 0 = 2 then 18 else 17) := by decide

end BranchC.HsuppProbe
