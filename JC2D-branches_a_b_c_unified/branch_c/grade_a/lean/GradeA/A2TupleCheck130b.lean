/- A2 tuple-check chunk 130b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk130b : (1305 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk130b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1305 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1305) boundChunk130b⟩)).all (checkFun ⟨1305 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1305) boundChunk130b⟩) = true ∧ linkFun ⟨1305 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1305) boundChunk130b⟩ = true := by
  decide +kernel

end BranchC.A2Check
