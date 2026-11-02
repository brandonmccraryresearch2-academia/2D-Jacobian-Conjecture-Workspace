/- Probe: the multQ range decide, isolated (same imports as Hsupp). -/
import GradeA.A2Entry
import GradeA.A2Data
import GradeA.A2RowsNodup

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.HsuppProbe

open BranchC.A2Data

def qexp (t : Nat × Nat × Nat × Nat × Nat) : Nat := t.2.2.2.2

theorem probeMultQ : ∀ i ∈ List.range 3199,
    qexp (multList.getD i (0, 0, 0, 0, 0)) ≤ 4 := by decide

end BranchC.HsuppProbe
