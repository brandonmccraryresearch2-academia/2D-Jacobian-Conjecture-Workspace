/- A2 tuple-check chunk 201b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk201b : (2015 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk201b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2015 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2015) boundChunk201b⟩)).all (checkFun ⟨2015 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2015) boundChunk201b⟩) = true ∧ linkFun ⟨2015 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2015) boundChunk201b⟩ = true := by
  decide +kernel

end BranchC.A2Check
