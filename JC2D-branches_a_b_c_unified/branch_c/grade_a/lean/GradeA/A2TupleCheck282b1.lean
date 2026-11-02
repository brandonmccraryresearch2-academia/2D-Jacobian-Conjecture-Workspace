/- A2 tuple-check chunk 282b1 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk282b1 : (2825 + 2 : Nat) < 3199 := by decide
theorem colCheckChunk282b1 : ∀ (j : Nat) (hj : j < 2),
    (dedup5 (unionTuples ⟨2825 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2825) boundChunk282b1⟩)).all (checkFun ⟨2825 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2825) boundChunk282b1⟩) = true ∧ linkFun ⟨2825 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2825) boundChunk282b1⟩ = true := by
  decide +kernel

end BranchC.A2Check
