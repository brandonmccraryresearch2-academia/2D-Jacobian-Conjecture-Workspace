/- A2 tuple-check chunk 45 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk45 : (450 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk45 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨450 + j, Nat.lt_trans (Nat.add_lt_add_left hj 450) boundChunk45⟩)).all (checkFun ⟨450 + j, Nat.lt_trans (Nat.add_lt_add_left hj 450) boundChunk45⟩) = true ∧ linkFun ⟨450 + j, Nat.lt_trans (Nat.add_lt_add_left hj 450) boundChunk45⟩ = true := by
  decide +kernel

end BranchC.A2Check
