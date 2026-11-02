/- A2 tuple-check chunk 22 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk22 : (220 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk22 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨220 + j, Nat.lt_trans (Nat.add_lt_add_left hj 220) boundChunk22⟩)).all (checkFun ⟨220 + j, Nat.lt_trans (Nat.add_lt_add_left hj 220) boundChunk22⟩) = true ∧ linkFun ⟨220 + j, Nat.lt_trans (Nat.add_lt_add_left hj 220) boundChunk22⟩ = true := by
  decide +kernel

end BranchC.A2Check
