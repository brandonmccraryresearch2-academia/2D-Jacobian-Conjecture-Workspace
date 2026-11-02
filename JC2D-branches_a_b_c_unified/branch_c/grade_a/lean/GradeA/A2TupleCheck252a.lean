/- A2 tuple-check chunk 252a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk252a : (2520 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk252a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2520 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2520) boundChunk252a⟩)).all (checkFun ⟨2520 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2520) boundChunk252a⟩) = true ∧ linkFun ⟨2520 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2520) boundChunk252a⟩ = true := by
  decide +kernel

end BranchC.A2Check
