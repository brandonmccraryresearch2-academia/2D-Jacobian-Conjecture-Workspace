/- Probe: linkFun half only, columns 0-24, Fin form. -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem probeLink25 : ∀ c : Fin 3199, 0 ≤ c.val → c.val < 25 →
    linkFun c = true := by
  decide +kernel

end BranchC.A2Check
