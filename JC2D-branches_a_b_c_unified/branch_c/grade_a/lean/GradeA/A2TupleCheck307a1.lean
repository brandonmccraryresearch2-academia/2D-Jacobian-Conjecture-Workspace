/- A2 tuple-check chunk 307a1 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk307a1 : (3070 + 2 : Nat) < 3199 := by decide
theorem colCheckChunk307a1 : ∀ (j : Nat) (hj : j < 2),
    (dedup5 (unionTuples ⟨3070 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3070) boundChunk307a1⟩)).all (checkFun ⟨3070 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3070) boundChunk307a1⟩) = true ∧ linkFun ⟨3070 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3070) boundChunk307a1⟩ = true := by
  decide +kernel

end BranchC.A2Check
