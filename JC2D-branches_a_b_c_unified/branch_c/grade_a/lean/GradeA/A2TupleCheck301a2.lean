/- A2 tuple-check chunk 301a2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk301a2 : (3012 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk301a2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨3012 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3012) boundChunk301a2⟩)).all (checkFun ⟨3012 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3012) boundChunk301a2⟩) = true ∧ linkFun ⟨3012 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3012) boundChunk301a2⟩ = true := by
  decide +kernel

end BranchC.A2Check
