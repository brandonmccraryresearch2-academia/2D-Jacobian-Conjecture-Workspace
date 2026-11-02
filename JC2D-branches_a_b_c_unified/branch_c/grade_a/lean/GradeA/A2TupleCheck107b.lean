/- A2 tuple-check chunk 107b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk107b : (1075 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk107b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1075 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1075) boundChunk107b⟩)).all (checkFun ⟨1075 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1075) boundChunk107b⟩) = true ∧ linkFun ⟨1075 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1075) boundChunk107b⟩ = true := by
  decide +kernel

end BranchC.A2Check
