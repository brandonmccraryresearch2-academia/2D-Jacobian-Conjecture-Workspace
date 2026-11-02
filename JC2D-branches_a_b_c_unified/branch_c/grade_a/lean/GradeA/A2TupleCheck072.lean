/- A2 tuple-check chunk 72 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk72 : (720 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk72 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨720 + j, Nat.lt_trans (Nat.add_lt_add_left hj 720) boundChunk72⟩)).all (checkFun ⟨720 + j, Nat.lt_trans (Nat.add_lt_add_left hj 720) boundChunk72⟩) = true ∧ linkFun ⟨720 + j, Nat.lt_trans (Nat.add_lt_add_left hj 720) boundChunk72⟩ = true := by
  decide +kernel

end BranchC.A2Check
