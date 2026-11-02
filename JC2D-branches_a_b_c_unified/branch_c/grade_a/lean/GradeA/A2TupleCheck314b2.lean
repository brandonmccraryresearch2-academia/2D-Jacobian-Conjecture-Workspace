/- A2 tuple-check chunk 314b2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk314b2 : (3147 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk314b2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨3147 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3147) boundChunk314b2⟩)).all (checkFun ⟨3147 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3147) boundChunk314b2⟩) = true ∧ linkFun ⟨3147 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3147) boundChunk314b2⟩ = true := by
  decide +kernel

end BranchC.A2Check
