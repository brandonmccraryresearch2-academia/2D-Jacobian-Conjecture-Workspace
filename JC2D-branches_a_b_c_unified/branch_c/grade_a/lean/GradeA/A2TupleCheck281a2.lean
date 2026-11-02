/- A2 tuple-check chunk 281a2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk281a2 : (2812 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk281a2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨2812 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2812) boundChunk281a2⟩)).all (checkFun ⟨2812 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2812) boundChunk281a2⟩) = true ∧ linkFun ⟨2812 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2812) boundChunk281a2⟩ = true := by
  decide +kernel

end BranchC.A2Check
