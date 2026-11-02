/- A2 tuple-check chunk 259b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk259b : (2595 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk259b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2595 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2595) boundChunk259b⟩)).all (checkFun ⟨2595 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2595) boundChunk259b⟩) = true ∧ linkFun ⟨2595 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2595) boundChunk259b⟩ = true := by
  decide +kernel

end BranchC.A2Check
