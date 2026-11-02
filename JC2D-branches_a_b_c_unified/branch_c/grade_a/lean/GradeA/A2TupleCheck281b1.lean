/- A2 tuple-check chunk 281b1 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk281b1 : (2815 + 2 : Nat) < 3199 := by decide
theorem colCheckChunk281b1 : ∀ (j : Nat) (hj : j < 2),
    (dedup5 (unionTuples ⟨2815 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2815) boundChunk281b1⟩)).all (checkFun ⟨2815 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2815) boundChunk281b1⟩) = true ∧ linkFun ⟨2815 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2815) boundChunk281b1⟩ = true := by
  decide +kernel

end BranchC.A2Check
