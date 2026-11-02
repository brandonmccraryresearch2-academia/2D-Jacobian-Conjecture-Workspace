/- A2 tuple-check chunk 165a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk165a : (1650 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk165a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1650 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1650) boundChunk165a⟩)).all (checkFun ⟨1650 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1650) boundChunk165a⟩) = true ∧ linkFun ⟨1650 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1650) boundChunk165a⟩ = true := by
  decide +kernel

end BranchC.A2Check
