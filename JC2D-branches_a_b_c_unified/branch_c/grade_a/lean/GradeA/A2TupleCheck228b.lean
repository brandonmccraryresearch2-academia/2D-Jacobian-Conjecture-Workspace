/- A2 tuple-check chunk 228b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk228b : (2285 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk228b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2285 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2285) boundChunk228b⟩)).all (checkFun ⟨2285 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2285) boundChunk228b⟩) = true ∧ linkFun ⟨2285 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2285) boundChunk228b⟩ = true := by
  decide +kernel

end BranchC.A2Check
