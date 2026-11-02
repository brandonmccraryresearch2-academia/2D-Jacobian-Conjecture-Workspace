/- A2 tuple-check chunk 284b2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk284b2 : (2847 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk284b2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨2847 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2847) boundChunk284b2⟩)).all (checkFun ⟨2847 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2847) boundChunk284b2⟩) = true ∧ linkFun ⟨2847 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2847) boundChunk284b2⟩ = true := by
  decide +kernel

end BranchC.A2Check
