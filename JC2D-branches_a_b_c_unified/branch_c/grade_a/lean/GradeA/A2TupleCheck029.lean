/- A2 tuple-check chunk 29 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk29 : (290 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk29 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨290 + j, Nat.lt_trans (Nat.add_lt_add_left hj 290) boundChunk29⟩)).all (checkFun ⟨290 + j, Nat.lt_trans (Nat.add_lt_add_left hj 290) boundChunk29⟩) = true ∧ linkFun ⟨290 + j, Nat.lt_trans (Nat.add_lt_add_left hj 290) boundChunk29⟩ = true := by
  decide +kernel

end BranchC.A2Check
