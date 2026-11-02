/- A2 tuple-check chunk 79 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk79 : (790 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk79 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨790 + j, Nat.lt_trans (Nat.add_lt_add_left hj 790) boundChunk79⟩)).all (checkFun ⟨790 + j, Nat.lt_trans (Nat.add_lt_add_left hj 790) boundChunk79⟩) = true ∧ linkFun ⟨790 + j, Nat.lt_trans (Nat.add_lt_add_left hj 790) boundChunk79⟩ = true := by
  decide +kernel

end BranchC.A2Check
