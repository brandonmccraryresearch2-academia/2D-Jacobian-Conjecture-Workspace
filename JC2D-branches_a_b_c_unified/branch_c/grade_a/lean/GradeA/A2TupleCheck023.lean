/- A2 tuple-check chunk 23 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk23 : (230 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk23 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨230 + j, Nat.lt_trans (Nat.add_lt_add_left hj 230) boundChunk23⟩)).all (checkFun ⟨230 + j, Nat.lt_trans (Nat.add_lt_add_left hj 230) boundChunk23⟩) = true ∧ linkFun ⟨230 + j, Nat.lt_trans (Nat.add_lt_add_left hj 230) boundChunk23⟩ = true := by
  decide +kernel

end BranchC.A2Check
