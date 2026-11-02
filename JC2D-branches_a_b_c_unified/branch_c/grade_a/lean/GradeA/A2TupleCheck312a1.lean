/- A2 tuple-check chunk 312a1 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk312a1 : (3120 + 2 : Nat) < 3199 := by decide
theorem colCheckChunk312a1 : ∀ (j : Nat) (hj : j < 2),
    (dedup5 (unionTuples ⟨3120 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3120) boundChunk312a1⟩)).all (checkFun ⟨3120 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3120) boundChunk312a1⟩) = true ∧ linkFun ⟨3120 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3120) boundChunk312a1⟩ = true := by
  decide +kernel

end BranchC.A2Check
