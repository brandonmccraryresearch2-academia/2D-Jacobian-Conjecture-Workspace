/- A2 tuple-check chunk 308a2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk308a2 : (3082 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk308a2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨3082 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3082) boundChunk308a2⟩)).all (checkFun ⟨3082 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3082) boundChunk308a2⟩) = true ∧ linkFun ⟨3082 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3082) boundChunk308a2⟩ = true := by
  decide +kernel

end BranchC.A2Check
