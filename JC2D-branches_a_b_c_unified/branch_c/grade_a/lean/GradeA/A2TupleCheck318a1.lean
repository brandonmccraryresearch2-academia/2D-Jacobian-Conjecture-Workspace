/- A2 tuple-check chunk 318a1 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk318a1 : (3180 + 2 : Nat) < 3199 := by decide
theorem colCheckChunk318a1 : ∀ (j : Nat) (hj : j < 2),
    (dedup5 (unionTuples ⟨3180 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3180) boundChunk318a1⟩)).all (checkFun ⟨3180 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3180) boundChunk318a1⟩) = true ∧ linkFun ⟨3180 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3180) boundChunk318a1⟩ = true := by
  decide +kernel

end BranchC.A2Check
