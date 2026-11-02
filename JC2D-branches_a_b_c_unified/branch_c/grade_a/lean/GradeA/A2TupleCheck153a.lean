/- A2 tuple-check chunk 153a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk153a : (1530 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk153a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1530 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1530) boundChunk153a⟩)).all (checkFun ⟨1530 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1530) boundChunk153a⟩) = true ∧ linkFun ⟨1530 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1530) boundChunk153a⟩ = true := by
  decide +kernel

end BranchC.A2Check
