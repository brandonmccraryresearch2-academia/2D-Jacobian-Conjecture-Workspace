/- A2 tuple-check chunk 138b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk138b : (1385 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk138b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1385 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1385) boundChunk138b⟩)).all (checkFun ⟨1385 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1385) boundChunk138b⟩) = true ∧ linkFun ⟨1385 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1385) boundChunk138b⟩ = true := by
  decide +kernel

end BranchC.A2Check
