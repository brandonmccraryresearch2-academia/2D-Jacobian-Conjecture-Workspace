/- A2 tuple-check chunk 174a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk174a : (1740 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk174a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1740 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1740) boundChunk174a⟩)).all (checkFun ⟨1740 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1740) boundChunk174a⟩) = true ∧ linkFun ⟨1740 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1740) boundChunk174a⟩ = true := by
  decide +kernel

end BranchC.A2Check
