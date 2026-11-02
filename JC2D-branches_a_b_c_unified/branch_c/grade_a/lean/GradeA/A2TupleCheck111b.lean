/- A2 tuple-check chunk 111b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk111b : (1115 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk111b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1115 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1115) boundChunk111b⟩)).all (checkFun ⟨1115 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1115) boundChunk111b⟩) = true ∧ linkFun ⟨1115 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1115) boundChunk111b⟩ = true := by
  decide +kernel

end BranchC.A2Check
