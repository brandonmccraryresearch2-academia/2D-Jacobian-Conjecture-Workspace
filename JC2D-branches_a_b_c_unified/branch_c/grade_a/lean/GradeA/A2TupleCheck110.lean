/- A2 tuple-check chunk 110 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk110 : (1100 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk110 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨1100 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1100) boundChunk110⟩)).all (checkFun ⟨1100 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1100) boundChunk110⟩) = true ∧ linkFun ⟨1100 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1100) boundChunk110⟩ = true := by
  decide +kernel

end BranchC.A2Check
