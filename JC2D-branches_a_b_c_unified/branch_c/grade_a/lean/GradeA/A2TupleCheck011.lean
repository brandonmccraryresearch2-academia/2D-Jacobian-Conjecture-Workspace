/- A2 tuple-check chunk 11 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk11 : (110 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk11 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨110 + j, Nat.lt_trans (Nat.add_lt_add_left hj 110) boundChunk11⟩)).all (checkFun ⟨110 + j, Nat.lt_trans (Nat.add_lt_add_left hj 110) boundChunk11⟩) = true ∧ linkFun ⟨110 + j, Nat.lt_trans (Nat.add_lt_add_left hj 110) boundChunk11⟩ = true := by
  decide +kernel

end BranchC.A2Check
