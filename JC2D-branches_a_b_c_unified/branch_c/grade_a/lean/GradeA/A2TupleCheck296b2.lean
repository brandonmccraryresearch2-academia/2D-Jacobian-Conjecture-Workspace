/- A2 tuple-check chunk 296b2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk296b2 : (2967 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk296b2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨2967 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2967) boundChunk296b2⟩)).all (checkFun ⟨2967 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2967) boundChunk296b2⟩) = true ∧ linkFun ⟨2967 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2967) boundChunk296b2⟩ = true := by
  decide +kernel

end BranchC.A2Check
