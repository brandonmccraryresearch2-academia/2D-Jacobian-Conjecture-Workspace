/- A2 tuple-check chunk 120b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk120b : (1205 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk120b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1205 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1205) boundChunk120b⟩)).all (checkFun ⟨1205 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1205) boundChunk120b⟩) = true ∧ linkFun ⟨1205 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1205) boundChunk120b⟩ = true := by
  decide +kernel

end BranchC.A2Check
