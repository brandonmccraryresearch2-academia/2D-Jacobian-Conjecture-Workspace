/- A2 tuple-check chunk 21 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk21 : (210 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk21 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨210 + j, Nat.lt_trans (Nat.add_lt_add_left hj 210) boundChunk21⟩)).all (checkFun ⟨210 + j, Nat.lt_trans (Nat.add_lt_add_left hj 210) boundChunk21⟩) = true ∧ linkFun ⟨210 + j, Nat.lt_trans (Nat.add_lt_add_left hj 210) boundChunk21⟩ = true := by
  decide +kernel

end BranchC.A2Check
