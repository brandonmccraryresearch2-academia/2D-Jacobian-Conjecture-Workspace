/- A2 tuple-check chunk 293b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk293b : (2935 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk293b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2935 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2935) boundChunk293b⟩)).all (checkFun ⟨2935 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2935) boundChunk293b⟩) = true ∧ linkFun ⟨2935 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2935) boundChunk293b⟩ = true := by
  decide +kernel

end BranchC.A2Check
