/- A2 tuple-check chunk 222b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk222b : (2225 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk222b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2225 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2225) boundChunk222b⟩)).all (checkFun ⟨2225 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2225) boundChunk222b⟩) = true ∧ linkFun ⟨2225 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2225) boundChunk222b⟩ = true := by
  decide +kernel

end BranchC.A2Check
