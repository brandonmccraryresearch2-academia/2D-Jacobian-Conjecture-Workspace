/- A2 tuple-check chunk 113b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk113b : (1135 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk113b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1135 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1135) boundChunk113b⟩)).all (checkFun ⟨1135 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1135) boundChunk113b⟩) = true ∧ linkFun ⟨1135 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1135) boundChunk113b⟩ = true := by
  decide +kernel

end BranchC.A2Check
