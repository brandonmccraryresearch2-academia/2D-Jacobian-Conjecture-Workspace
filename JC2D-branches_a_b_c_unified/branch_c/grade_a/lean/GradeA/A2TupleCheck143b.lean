/- A2 tuple-check chunk 143b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk143b : (1435 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk143b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1435 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1435) boundChunk143b⟩)).all (checkFun ⟨1435 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1435) boundChunk143b⟩) = true ∧ linkFun ⟨1435 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1435) boundChunk143b⟩ = true := by
  decide +kernel

end BranchC.A2Check
