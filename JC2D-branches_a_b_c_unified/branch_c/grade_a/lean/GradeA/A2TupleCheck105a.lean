/- A2 tuple-check chunk 105a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk105a : (1050 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk105a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1050 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1050) boundChunk105a⟩)).all (checkFun ⟨1050 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1050) boundChunk105a⟩) = true ∧ linkFun ⟨1050 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1050) boundChunk105a⟩ = true := by
  decide +kernel

end BranchC.A2Check
