/- A2 tuple-check chunk 313b2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk313b2 : (3137 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk313b2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨3137 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3137) boundChunk313b2⟩)).all (checkFun ⟨3137 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3137) boundChunk313b2⟩) = true ∧ linkFun ⟨3137 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3137) boundChunk313b2⟩ = true := by
  decide +kernel

end BranchC.A2Check
