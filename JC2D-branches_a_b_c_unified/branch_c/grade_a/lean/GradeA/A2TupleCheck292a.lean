/- A2 tuple-check chunk 292a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk292a : (2920 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk292a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2920 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2920) boundChunk292a⟩)).all (checkFun ⟨2920 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2920) boundChunk292a⟩) = true ∧ linkFun ⟨2920 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2920) boundChunk292a⟩ = true := by
  decide +kernel

end BranchC.A2Check
