/- A2 tuple-check chunk 205a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk205a : (2050 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk205a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2050 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2050) boundChunk205a⟩)).all (checkFun ⟨2050 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2050) boundChunk205a⟩) = true ∧ linkFun ⟨2050 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2050) boundChunk205a⟩ = true := by
  decide +kernel

end BranchC.A2Check
