/- A2 tuple-check chunk 289b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk289b : (2895 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk289b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2895 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2895) boundChunk289b⟩)).all (checkFun ⟨2895 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2895) boundChunk289b⟩) = true ∧ linkFun ⟨2895 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2895) boundChunk289b⟩ = true := by
  decide +kernel

end BranchC.A2Check
