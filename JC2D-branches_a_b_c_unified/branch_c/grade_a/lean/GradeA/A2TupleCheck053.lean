/- A2 tuple-check chunk 53 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk53 : (530 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk53 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨530 + j, Nat.lt_trans (Nat.add_lt_add_left hj 530) boundChunk53⟩)).all (checkFun ⟨530 + j, Nat.lt_trans (Nat.add_lt_add_left hj 530) boundChunk53⟩) = true ∧ linkFun ⟨530 + j, Nat.lt_trans (Nat.add_lt_add_left hj 530) boundChunk53⟩ = true := by
  decide +kernel

end BranchC.A2Check
