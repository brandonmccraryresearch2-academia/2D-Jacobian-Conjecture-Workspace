/- A2 tuple-check chunk 155a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk155a : (1550 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk155a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1550 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1550) boundChunk155a⟩)).all (checkFun ⟨1550 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1550) boundChunk155a⟩) = true ∧ linkFun ⟨1550 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1550) boundChunk155a⟩ = true := by
  decide +kernel

end BranchC.A2Check
