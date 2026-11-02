/- A2 tuple-check chunk 59 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk59 : (590 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk59 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨590 + j, Nat.lt_trans (Nat.add_lt_add_left hj 590) boundChunk59⟩)).all (checkFun ⟨590 + j, Nat.lt_trans (Nat.add_lt_add_left hj 590) boundChunk59⟩) = true ∧ linkFun ⟨590 + j, Nat.lt_trans (Nat.add_lt_add_left hj 590) boundChunk59⟩ = true := by
  decide +kernel

end BranchC.A2Check
