/- A2 tuple-check chunk 173a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk173a : (1730 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk173a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1730 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1730) boundChunk173a⟩)).all (checkFun ⟨1730 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1730) boundChunk173a⟩) = true ∧ linkFun ⟨1730 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1730) boundChunk173a⟩ = true := by
  decide +kernel

end BranchC.A2Check
