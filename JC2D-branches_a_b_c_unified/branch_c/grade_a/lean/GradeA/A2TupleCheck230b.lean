/- A2 tuple-check chunk 230b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk230b : (2305 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk230b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2305 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2305) boundChunk230b⟩)).all (checkFun ⟨2305 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2305) boundChunk230b⟩) = true ∧ linkFun ⟨2305 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2305) boundChunk230b⟩ = true := by
  decide +kernel

end BranchC.A2Check
