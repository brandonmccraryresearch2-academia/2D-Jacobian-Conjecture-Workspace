/- A2 tuple-check chunk 235b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk235b : (2355 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk235b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2355 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2355) boundChunk235b⟩)).all (checkFun ⟨2355 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2355) boundChunk235b⟩) = true ∧ linkFun ⟨2355 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2355) boundChunk235b⟩ = true := by
  decide +kernel

end BranchC.A2Check
