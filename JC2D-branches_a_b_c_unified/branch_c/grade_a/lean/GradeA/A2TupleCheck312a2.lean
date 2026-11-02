/- A2 tuple-check chunk 312a2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk312a2 : (3122 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk312a2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨3122 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3122) boundChunk312a2⟩)).all (checkFun ⟨3122 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3122) boundChunk312a2⟩) = true ∧ linkFun ⟨3122 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3122) boundChunk312a2⟩ = true := by
  decide +kernel

end BranchC.A2Check
