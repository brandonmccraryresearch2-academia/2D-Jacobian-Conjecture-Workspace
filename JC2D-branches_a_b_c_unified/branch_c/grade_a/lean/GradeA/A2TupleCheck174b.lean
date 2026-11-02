/- A2 tuple-check chunk 174b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk174b : (1745 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk174b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1745 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1745) boundChunk174b⟩)).all (checkFun ⟨1745 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1745) boundChunk174b⟩) = true ∧ linkFun ⟨1745 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1745) boundChunk174b⟩ = true := by
  decide +kernel

end BranchC.A2Check
