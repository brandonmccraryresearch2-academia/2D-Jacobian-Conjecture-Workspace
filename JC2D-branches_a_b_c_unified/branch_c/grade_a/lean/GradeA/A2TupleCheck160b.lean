/- A2 tuple-check chunk 160b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk160b : (1605 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk160b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1605 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1605) boundChunk160b⟩)).all (checkFun ⟨1605 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1605) boundChunk160b⟩) = true ∧ linkFun ⟨1605 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1605) boundChunk160b⟩ = true := by
  decide +kernel

end BranchC.A2Check
