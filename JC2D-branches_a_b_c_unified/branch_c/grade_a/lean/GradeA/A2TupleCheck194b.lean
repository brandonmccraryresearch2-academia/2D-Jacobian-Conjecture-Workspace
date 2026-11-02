/- A2 tuple-check chunk 194b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk194b : (1945 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk194b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1945 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1945) boundChunk194b⟩)).all (checkFun ⟨1945 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1945) boundChunk194b⟩) = true ∧ linkFun ⟨1945 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1945) boundChunk194b⟩ = true := by
  decide +kernel

end BranchC.A2Check
