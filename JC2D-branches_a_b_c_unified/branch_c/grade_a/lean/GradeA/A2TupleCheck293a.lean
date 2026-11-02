/- A2 tuple-check chunk 293a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk293a : (2930 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk293a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2930 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2930) boundChunk293a⟩)).all (checkFun ⟨2930 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2930) boundChunk293a⟩) = true ∧ linkFun ⟨2930 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2930) boundChunk293a⟩ = true := by
  decide +kernel

end BranchC.A2Check
