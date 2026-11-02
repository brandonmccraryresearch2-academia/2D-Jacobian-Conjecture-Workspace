/- A2 tuple-check chunk 94 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk94 : (940 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk94 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨940 + j, Nat.lt_trans (Nat.add_lt_add_left hj 940) boundChunk94⟩)).all (checkFun ⟨940 + j, Nat.lt_trans (Nat.add_lt_add_left hj 940) boundChunk94⟩) = true ∧ linkFun ⟨940 + j, Nat.lt_trans (Nat.add_lt_add_left hj 940) boundChunk94⟩ = true := by
  decide +kernel

end BranchC.A2Check
