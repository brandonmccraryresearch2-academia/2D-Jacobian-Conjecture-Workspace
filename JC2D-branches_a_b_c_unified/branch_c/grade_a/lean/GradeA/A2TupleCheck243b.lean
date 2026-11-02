/- A2 tuple-check chunk 243b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk243b : (2435 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk243b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2435 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2435) boundChunk243b⟩)).all (checkFun ⟨2435 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2435) boundChunk243b⟩) = true ∧ linkFun ⟨2435 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2435) boundChunk243b⟩ = true := by
  decide +kernel

end BranchC.A2Check
