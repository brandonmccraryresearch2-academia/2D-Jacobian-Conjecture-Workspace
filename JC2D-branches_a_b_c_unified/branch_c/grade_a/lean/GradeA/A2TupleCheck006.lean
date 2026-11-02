/- A2 tuple-check chunk 6 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk6 : (60 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk6 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨60 + j, Nat.lt_trans (Nat.add_lt_add_left hj 60) boundChunk6⟩)).all (checkFun ⟨60 + j, Nat.lt_trans (Nat.add_lt_add_left hj 60) boundChunk6⟩) = true ∧ linkFun ⟨60 + j, Nat.lt_trans (Nat.add_lt_add_left hj 60) boundChunk6⟩ = true := by
  decide +kernel

end BranchC.A2Check
