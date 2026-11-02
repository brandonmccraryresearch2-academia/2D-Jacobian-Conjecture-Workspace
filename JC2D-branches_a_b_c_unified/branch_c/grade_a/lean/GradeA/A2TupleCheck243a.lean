/- A2 tuple-check chunk 243a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk243a : (2430 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk243a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2430 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2430) boundChunk243a⟩)).all (checkFun ⟨2430 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2430) boundChunk243a⟩) = true ∧ linkFun ⟨2430 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2430) boundChunk243a⟩ = true := by
  decide +kernel

end BranchC.A2Check
