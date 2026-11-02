/- A2 tuple-check chunk 254a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk254a : (2540 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk254a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2540 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2540) boundChunk254a⟩)).all (checkFun ⟨2540 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2540) boundChunk254a⟩) = true ∧ linkFun ⟨2540 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2540) boundChunk254a⟩ = true := by
  decide +kernel

end BranchC.A2Check
