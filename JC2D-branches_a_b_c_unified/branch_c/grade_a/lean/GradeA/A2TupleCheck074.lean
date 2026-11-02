/- A2 tuple-check chunk 74 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk74 : (740 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk74 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨740 + j, Nat.lt_trans (Nat.add_lt_add_left hj 740) boundChunk74⟩)).all (checkFun ⟨740 + j, Nat.lt_trans (Nat.add_lt_add_left hj 740) boundChunk74⟩) = true ∧ linkFun ⟨740 + j, Nat.lt_trans (Nat.add_lt_add_left hj 740) boundChunk74⟩ = true := by
  decide +kernel

end BranchC.A2Check
