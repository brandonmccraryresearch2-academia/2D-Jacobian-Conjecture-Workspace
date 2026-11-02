/- A2 tuple-check chunk 297b2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk297b2 : (2977 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk297b2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨2977 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2977) boundChunk297b2⟩)).all (checkFun ⟨2977 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2977) boundChunk297b2⟩) = true ∧ linkFun ⟨2977 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2977) boundChunk297b2⟩ = true := by
  decide +kernel

end BranchC.A2Check
