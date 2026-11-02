/- A2 tuple-check chunk 107a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk107a : (1070 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk107a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1070 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1070) boundChunk107a⟩)).all (checkFun ⟨1070 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1070) boundChunk107a⟩) = true ∧ linkFun ⟨1070 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1070) boundChunk107a⟩ = true := by
  decide +kernel

end BranchC.A2Check
