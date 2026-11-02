/- Probe: A2 chunk 0 in Nat-bounded form (A1's form), columns 0-99. -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem probeNat100 : ∀ j : Nat, j < 100 →
    (unionTuples ⟨j, by omega⟩).all (checkFun ⟨j, by omega⟩) = true ∧
    linkFun ⟨j, by omega⟩ = true := by
  decide +kernel

end BranchC.A2Check
