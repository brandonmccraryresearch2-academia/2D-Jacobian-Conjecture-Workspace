/- A2 tuple-check chunk 113a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk113a : (1130 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk113a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1130 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1130) boundChunk113a⟩)).all (checkFun ⟨1130 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1130) boundChunk113a⟩) = true ∧ linkFun ⟨1130 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1130) boundChunk113a⟩ = true := by
  decide +kernel

end BranchC.A2Check
