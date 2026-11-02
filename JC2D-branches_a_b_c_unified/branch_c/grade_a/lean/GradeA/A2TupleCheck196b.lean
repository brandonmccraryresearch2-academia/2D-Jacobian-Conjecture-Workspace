/- A2 tuple-check chunk 196b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk196b : (1965 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk196b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1965 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1965) boundChunk196b⟩)).all (checkFun ⟨1965 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1965) boundChunk196b⟩) = true ∧ linkFun ⟨1965 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1965) boundChunk196b⟩ = true := by
  decide +kernel

end BranchC.A2Check
