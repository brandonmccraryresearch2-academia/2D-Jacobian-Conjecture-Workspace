/- A2 tuple-check chunk 58 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk58 : (580 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk58 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨580 + j, Nat.lt_trans (Nat.add_lt_add_left hj 580) boundChunk58⟩)).all (checkFun ⟨580 + j, Nat.lt_trans (Nat.add_lt_add_left hj 580) boundChunk58⟩) = true ∧ linkFun ⟨580 + j, Nat.lt_trans (Nat.add_lt_add_left hj 580) boundChunk58⟩ = true := by
  decide +kernel

end BranchC.A2Check
