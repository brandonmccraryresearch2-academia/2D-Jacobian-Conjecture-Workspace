/- Probe: single A2 chunk theorem at bound 25 (columns 0-24) alone. -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem probe25 : ∀ c : Fin 3199, 0 ≤ c.val → c.val < 25 →
    (unionTuples c).all (checkFun c) = true ∧ linkFun c = true := by
  decide +kernel

end BranchC.A2Check
