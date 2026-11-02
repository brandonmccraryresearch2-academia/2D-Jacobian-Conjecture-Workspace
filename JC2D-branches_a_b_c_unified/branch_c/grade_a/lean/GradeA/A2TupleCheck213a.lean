/- A2 tuple-check chunk 213a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk213a : (2130 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk213a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2130 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2130) boundChunk213a⟩)).all (checkFun ⟨2130 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2130) boundChunk213a⟩) = true ∧ linkFun ⟨2130 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2130) boundChunk213a⟩ = true := by
  decide +kernel

end BranchC.A2Check
