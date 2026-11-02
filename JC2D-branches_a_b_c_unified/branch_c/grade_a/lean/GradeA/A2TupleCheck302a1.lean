/- A2 tuple-check chunk 302a1 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk302a1 : (3020 + 2 : Nat) < 3199 := by decide
theorem colCheckChunk302a1 : ∀ (j : Nat) (hj : j < 2),
    (dedup5 (unionTuples ⟨3020 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3020) boundChunk302a1⟩)).all (checkFun ⟨3020 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3020) boundChunk302a1⟩) = true ∧ linkFun ⟨3020 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3020) boundChunk302a1⟩ = true := by
  decide +kernel

end BranchC.A2Check
