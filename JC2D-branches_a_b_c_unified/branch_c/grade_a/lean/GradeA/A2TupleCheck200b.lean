/- A2 tuple-check chunk 200b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk200b : (2005 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk200b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2005 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2005) boundChunk200b⟩)).all (checkFun ⟨2005 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2005) boundChunk200b⟩) = true ∧ linkFun ⟨2005 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2005) boundChunk200b⟩ = true := by
  decide +kernel

end BranchC.A2Check
