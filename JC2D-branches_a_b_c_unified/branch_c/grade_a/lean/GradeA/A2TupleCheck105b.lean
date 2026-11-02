/- A2 tuple-check chunk 105b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk105b : (1055 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk105b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1055 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1055) boundChunk105b⟩)).all (checkFun ⟨1055 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1055) boundChunk105b⟩) = true ∧ linkFun ⟨1055 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1055) boundChunk105b⟩ = true := by
  decide +kernel

end BranchC.A2Check
