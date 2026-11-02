/- A2 tuple-check chunk 146a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk146a : (1460 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk146a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1460 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1460) boundChunk146a⟩)).all (checkFun ⟨1460 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1460) boundChunk146a⟩) = true ∧ linkFun ⟨1460 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1460) boundChunk146a⟩ = true := by
  decide +kernel

end BranchC.A2Check
