/- A2 tuple-check chunk 52 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk52 : (520 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk52 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨520 + j, Nat.lt_trans (Nat.add_lt_add_left hj 520) boundChunk52⟩)).all (checkFun ⟨520 + j, Nat.lt_trans (Nat.add_lt_add_left hj 520) boundChunk52⟩) = true ∧ linkFun ⟨520 + j, Nat.lt_trans (Nat.add_lt_add_left hj 520) boundChunk52⟩ = true := by
  decide +kernel

end BranchC.A2Check
