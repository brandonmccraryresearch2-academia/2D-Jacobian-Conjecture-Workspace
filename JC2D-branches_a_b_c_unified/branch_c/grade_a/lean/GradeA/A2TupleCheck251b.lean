/- A2 tuple-check chunk 251b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk251b : (2515 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk251b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2515 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2515) boundChunk251b⟩)).all (checkFun ⟨2515 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2515) boundChunk251b⟩) = true ∧ linkFun ⟨2515 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2515) boundChunk251b⟩ = true := by
  decide +kernel

end BranchC.A2Check
