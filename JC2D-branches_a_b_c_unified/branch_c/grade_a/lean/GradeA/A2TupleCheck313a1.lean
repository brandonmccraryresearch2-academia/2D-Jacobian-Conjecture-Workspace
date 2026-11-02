/- A2 tuple-check chunk 313a1 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk313a1 : (3130 + 2 : Nat) < 3199 := by decide
theorem colCheckChunk313a1 : ∀ (j : Nat) (hj : j < 2),
    (dedup5 (unionTuples ⟨3130 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3130) boundChunk313a1⟩)).all (checkFun ⟨3130 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3130) boundChunk313a1⟩) = true ∧ linkFun ⟨3130 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3130) boundChunk313a1⟩ = true := by
  decide +kernel

end BranchC.A2Check
