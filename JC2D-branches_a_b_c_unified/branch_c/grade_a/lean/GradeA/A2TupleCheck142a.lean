/- A2 tuple-check chunk 142a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk142a : (1420 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk142a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1420 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1420) boundChunk142a⟩)).all (checkFun ⟨1420 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1420) boundChunk142a⟩) = true ∧ linkFun ⟨1420 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1420) boundChunk142a⟩ = true := by
  decide +kernel

end BranchC.A2Check
