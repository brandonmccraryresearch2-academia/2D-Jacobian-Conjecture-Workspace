/- A2 tuple-check chunk 315b1 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk315b1 : (3155 + 2 : Nat) < 3199 := by decide
theorem colCheckChunk315b1 : ∀ (j : Nat) (hj : j < 2),
    (dedup5 (unionTuples ⟨3155 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3155) boundChunk315b1⟩)).all (checkFun ⟨3155 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3155) boundChunk315b1⟩) = true ∧ linkFun ⟨3155 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3155) boundChunk315b1⟩ = true := by
  decide +kernel

end BranchC.A2Check
