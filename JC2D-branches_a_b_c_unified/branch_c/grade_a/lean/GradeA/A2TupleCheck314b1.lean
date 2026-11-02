/- A2 tuple-check chunk 314b1 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk314b1 : (3145 + 2 : Nat) < 3199 := by decide
theorem colCheckChunk314b1 : ∀ (j : Nat) (hj : j < 2),
    (dedup5 (unionTuples ⟨3145 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3145) boundChunk314b1⟩)).all (checkFun ⟨3145 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3145) boundChunk314b1⟩) = true ∧ linkFun ⟨3145 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3145) boundChunk314b1⟩ = true := by
  decide +kernel

end BranchC.A2Check
