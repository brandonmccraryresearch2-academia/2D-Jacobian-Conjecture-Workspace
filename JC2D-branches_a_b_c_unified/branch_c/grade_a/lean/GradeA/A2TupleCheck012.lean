/- A2 tuple-check chunk 12 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk12 : (120 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk12 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨120 + j, Nat.lt_trans (Nat.add_lt_add_left hj 120) boundChunk12⟩)).all (checkFun ⟨120 + j, Nat.lt_trans (Nat.add_lt_add_left hj 120) boundChunk12⟩) = true ∧ linkFun ⟨120 + j, Nat.lt_trans (Nat.add_lt_add_left hj 120) boundChunk12⟩ = true := by
  decide +kernel

end BranchC.A2Check
