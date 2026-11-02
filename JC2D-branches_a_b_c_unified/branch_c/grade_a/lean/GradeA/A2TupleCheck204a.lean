/- A2 tuple-check chunk 204a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk204a : (2040 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk204a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2040 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2040) boundChunk204a⟩)).all (checkFun ⟨2040 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2040) boundChunk204a⟩) = true ∧ linkFun ⟨2040 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2040) boundChunk204a⟩ = true := by
  decide +kernel

end BranchC.A2Check
