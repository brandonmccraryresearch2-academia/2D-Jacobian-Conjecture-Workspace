/- Probe: single A2 chunk theorem (columns 0-99) alone, to size the chunk work. -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem probeChunk0 : ∀ c : Fin 3199, 0 ≤ c.val → c.val < 100 →
    (unionTuples c).all (checkFun c) = true ∧ linkFun c = true := by
  decide +kernel

end BranchC.A2Check
