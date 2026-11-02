/- A2 tuple-check chunk 233b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk233b : (2335 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk233b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2335 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2335) boundChunk233b⟩)).all (checkFun ⟨2335 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2335) boundChunk233b⟩) = true ∧ linkFun ⟨2335 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2335) boundChunk233b⟩ = true := by
  decide +kernel

end BranchC.A2Check
