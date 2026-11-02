import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem probeB10 : ∀ c : Fin 3199, 0 ≤ c.val → c.val < 10 →
    (unionTuples c).all (checkFun c) = true ∧ linkFun c = true := by
  decide +kernel

end BranchC.A2Check
