/- A2 tuple-check chunk 231b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk231b : (2315 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk231b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2315 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2315) boundChunk231b⟩)).all (checkFun ⟨2315 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2315) boundChunk231b⟩) = true ∧ linkFun ⟨2315 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2315) boundChunk231b⟩ = true := by
  decide +kernel

end BranchC.A2Check
