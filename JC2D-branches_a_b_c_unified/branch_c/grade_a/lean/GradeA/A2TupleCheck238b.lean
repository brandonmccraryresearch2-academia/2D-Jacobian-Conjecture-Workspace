/- A2 tuple-check chunk 238b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk238b : (2385 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk238b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2385 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2385) boundChunk238b⟩)).all (checkFun ⟨2385 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2385) boundChunk238b⟩) = true ∧ linkFun ⟨2385 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2385) boundChunk238b⟩ = true := by
  decide +kernel

end BranchC.A2Check
