/- A2 tuple-check chunk 38 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk38 : (380 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk38 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨380 + j, Nat.lt_trans (Nat.add_lt_add_left hj 380) boundChunk38⟩)).all (checkFun ⟨380 + j, Nat.lt_trans (Nat.add_lt_add_left hj 380) boundChunk38⟩) = true ∧ linkFun ⟨380 + j, Nat.lt_trans (Nat.add_lt_add_left hj 380) boundChunk38⟩ = true := by
  decide +kernel

end BranchC.A2Check
