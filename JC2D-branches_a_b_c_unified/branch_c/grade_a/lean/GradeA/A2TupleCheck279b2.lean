/- A2 tuple-check chunk 279b2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk279b2 : (2797 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk279b2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨2797 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2797) boundChunk279b2⟩)).all (checkFun ⟨2797 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2797) boundChunk279b2⟩) = true ∧ linkFun ⟨2797 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2797) boundChunk279b2⟩ = true := by
  decide +kernel

end BranchC.A2Check
