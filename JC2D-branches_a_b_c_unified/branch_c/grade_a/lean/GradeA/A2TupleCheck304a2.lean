/- A2 tuple-check chunk 304a2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk304a2 : (3042 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk304a2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨3042 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3042) boundChunk304a2⟩)).all (checkFun ⟨3042 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3042) boundChunk304a2⟩) = true ∧ linkFun ⟨3042 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3042) boundChunk304a2⟩ = true := by
  decide +kernel

end BranchC.A2Check
