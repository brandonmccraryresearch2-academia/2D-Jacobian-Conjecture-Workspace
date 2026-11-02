/- A2 tuple-check chunk 154b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk154b : (1545 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk154b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1545 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1545) boundChunk154b⟩)).all (checkFun ⟨1545 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1545) boundChunk154b⟩) = true ∧ linkFun ⟨1545 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1545) boundChunk154b⟩ = true := by
  decide +kernel

end BranchC.A2Check
