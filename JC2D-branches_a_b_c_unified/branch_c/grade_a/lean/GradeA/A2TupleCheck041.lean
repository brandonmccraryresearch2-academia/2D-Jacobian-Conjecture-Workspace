/- A2 tuple-check chunk 41 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk41 : (410 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk41 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨410 + j, Nat.lt_trans (Nat.add_lt_add_left hj 410) boundChunk41⟩)).all (checkFun ⟨410 + j, Nat.lt_trans (Nat.add_lt_add_left hj 410) boundChunk41⟩) = true ∧ linkFun ⟨410 + j, Nat.lt_trans (Nat.add_lt_add_left hj 410) boundChunk41⟩ = true := by
  decide +kernel

end BranchC.A2Check
