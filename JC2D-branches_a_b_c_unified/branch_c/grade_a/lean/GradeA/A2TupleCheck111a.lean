/- A2 tuple-check chunk 111a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk111a : (1110 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk111a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1110 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1110) boundChunk111a⟩)).all (checkFun ⟨1110 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1110) boundChunk111a⟩) = true ∧ linkFun ⟨1110 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1110) boundChunk111a⟩ = true := by
  decide +kernel

end BranchC.A2Check
