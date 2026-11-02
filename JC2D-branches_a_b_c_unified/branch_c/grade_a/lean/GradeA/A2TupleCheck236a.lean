/- A2 tuple-check chunk 236a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk236a : (2360 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk236a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2360 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2360) boundChunk236a⟩)).all (checkFun ⟨2360 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2360) boundChunk236a⟩) = true ∧ linkFun ⟨2360 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2360) boundChunk236a⟩ = true := by
  decide +kernel

end BranchC.A2Check
