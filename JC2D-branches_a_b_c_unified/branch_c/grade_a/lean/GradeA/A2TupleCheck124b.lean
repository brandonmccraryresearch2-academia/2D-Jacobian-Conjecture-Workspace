/- A2 tuple-check chunk 124b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk124b : (1245 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk124b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1245 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1245) boundChunk124b⟩)).all (checkFun ⟨1245 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1245) boundChunk124b⟩) = true ∧ linkFun ⟨1245 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1245) boundChunk124b⟩ = true := by
  decide +kernel

end BranchC.A2Check
