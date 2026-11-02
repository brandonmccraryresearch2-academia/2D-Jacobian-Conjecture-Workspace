/- A2 tuple-check chunk 294b1 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk294b1 : (2945 + 2 : Nat) < 3199 := by decide
theorem colCheckChunk294b1 : ∀ (j : Nat) (hj : j < 2),
    (dedup5 (unionTuples ⟨2945 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2945) boundChunk294b1⟩)).all (checkFun ⟨2945 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2945) boundChunk294b1⟩) = true ∧ linkFun ⟨2945 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2945) boundChunk294b1⟩ = true := by
  decide +kernel

end BranchC.A2Check
