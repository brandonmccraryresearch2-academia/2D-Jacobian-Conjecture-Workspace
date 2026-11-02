/- A2 tuple-check chunk 307b2 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk307b2 : (3077 + 3 : Nat) < 3199 := by decide
theorem colCheckChunk307b2 : ∀ (j : Nat) (hj : j < 3),
    (dedup5 (unionTuples ⟨3077 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3077) boundChunk307b2⟩)).all (checkFun ⟨3077 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3077) boundChunk307b2⟩) = true ∧ linkFun ⟨3077 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3077) boundChunk307b2⟩ = true := by
  decide +kernel

end BranchC.A2Check
