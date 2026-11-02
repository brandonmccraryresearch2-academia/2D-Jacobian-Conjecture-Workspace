/- A2 tuple-check chunk 251a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk251a : (2510 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk251a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2510 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2510) boundChunk251a⟩)).all (checkFun ⟨2510 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2510) boundChunk251a⟩) = true ∧ linkFun ⟨2510 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2510) boundChunk251a⟩ = true := by
  decide +kernel

end BranchC.A2Check
