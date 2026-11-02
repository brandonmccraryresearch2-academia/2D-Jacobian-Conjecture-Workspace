import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem probeTheta2561 : ∀ c : Fin 3199, 2561 ≤ c.val → c.val < 2562 →
    (unionTuples c).all (checkFun c) = true ∧ linkFun c = true := by
  decide +kernel

end BranchC.A2Check
