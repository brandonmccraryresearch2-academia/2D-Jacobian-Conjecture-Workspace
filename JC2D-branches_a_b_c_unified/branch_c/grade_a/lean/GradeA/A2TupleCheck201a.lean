/- A2 tuple-check chunk 201a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk201a : (2010 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk201a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2010 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2010) boundChunk201a⟩)).all (checkFun ⟨2010 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2010) boundChunk201a⟩) = true ∧ linkFun ⟨2010 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2010) boundChunk201a⟩ = true := by
  decide +kernel

end BranchC.A2Check
