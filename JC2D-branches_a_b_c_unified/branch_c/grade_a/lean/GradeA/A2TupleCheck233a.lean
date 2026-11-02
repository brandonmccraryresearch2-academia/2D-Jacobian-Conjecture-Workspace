/- A2 tuple-check chunk 233a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk233a : (2330 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk233a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2330 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2330) boundChunk233a⟩)).all (checkFun ⟨2330 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2330) boundChunk233a⟩) = true ∧ linkFun ⟨2330 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2330) boundChunk233a⟩ = true := by
  decide +kernel

end BranchC.A2Check
