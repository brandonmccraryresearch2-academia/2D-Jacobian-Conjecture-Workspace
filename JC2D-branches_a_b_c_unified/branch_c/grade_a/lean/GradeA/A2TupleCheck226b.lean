/- A2 tuple-check chunk 226b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk226b : (2265 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk226b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2265 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2265) boundChunk226b⟩)).all (checkFun ⟨2265 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2265) boundChunk226b⟩) = true ∧ linkFun ⟨2265 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2265) boundChunk226b⟩ = true := by
  decide +kernel

end BranchC.A2Check
