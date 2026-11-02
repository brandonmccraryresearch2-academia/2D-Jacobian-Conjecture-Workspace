/- A2 tuple-check chunk 286b1 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk286b1 : (2865 + 2 : Nat) < 3199 := by decide
theorem colCheckChunk286b1 : ∀ (j : Nat) (hj : j < 2),
    (dedup5 (unionTuples ⟨2865 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2865) boundChunk286b1⟩)).all (checkFun ⟨2865 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2865) boundChunk286b1⟩) = true ∧ linkFun ⟨2865 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2865) boundChunk286b1⟩ = true := by
  decide +kernel

end BranchC.A2Check
