/- A2 tuple-check chunk 146b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk146b : (1465 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk146b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1465 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1465) boundChunk146b⟩)).all (checkFun ⟨1465 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1465) boundChunk146b⟩) = true ∧ linkFun ⟨1465 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1465) boundChunk146b⟩ = true := by
  decide +kernel

end BranchC.A2Check
