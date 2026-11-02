/- A2 tuple-check chunk 229b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk229b : (2295 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk229b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2295 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2295) boundChunk229b⟩)).all (checkFun ⟨2295 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2295) boundChunk229b⟩) = true ∧ linkFun ⟨2295 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2295) boundChunk229b⟩ = true := by
  decide +kernel

end BranchC.A2Check
