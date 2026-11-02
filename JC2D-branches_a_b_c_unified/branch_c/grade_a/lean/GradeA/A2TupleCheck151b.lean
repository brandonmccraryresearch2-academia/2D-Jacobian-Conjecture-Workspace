/- A2 tuple-check chunk 151b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk151b : (1515 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk151b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1515 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1515) boundChunk151b⟩)).all (checkFun ⟨1515 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1515) boundChunk151b⟩) = true ∧ linkFun ⟨1515 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1515) boundChunk151b⟩ = true := by
  decide +kernel

end BranchC.A2Check
