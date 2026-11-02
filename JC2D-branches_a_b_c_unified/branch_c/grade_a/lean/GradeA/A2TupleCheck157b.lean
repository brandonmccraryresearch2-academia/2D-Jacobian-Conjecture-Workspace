/- A2 tuple-check chunk 157b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk157b : (1575 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk157b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1575 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1575) boundChunk157b⟩)).all (checkFun ⟨1575 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1575) boundChunk157b⟩) = true ∧ linkFun ⟨1575 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1575) boundChunk157b⟩ = true := by
  decide +kernel

end BranchC.A2Check
