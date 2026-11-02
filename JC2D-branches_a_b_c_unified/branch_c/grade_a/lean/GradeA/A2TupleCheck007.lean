/- A2 tuple-check chunk 7 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk7 : (70 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk7 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨70 + j, Nat.lt_trans (Nat.add_lt_add_left hj 70) boundChunk7⟩)).all (checkFun ⟨70 + j, Nat.lt_trans (Nat.add_lt_add_left hj 70) boundChunk7⟩) = true ∧ linkFun ⟨70 + j, Nat.lt_trans (Nat.add_lt_add_left hj 70) boundChunk7⟩ = true := by
  decide +kernel

end BranchC.A2Check
