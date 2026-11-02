/- A2 tuple-check chunk 40 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk40 : (400 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk40 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨400 + j, Nat.lt_trans (Nat.add_lt_add_left hj 400) boundChunk40⟩)).all (checkFun ⟨400 + j, Nat.lt_trans (Nat.add_lt_add_left hj 400) boundChunk40⟩) = true ∧ linkFun ⟨400 + j, Nat.lt_trans (Nat.add_lt_add_left hj 400) boundChunk40⟩ = true := by
  decide +kernel

end BranchC.A2Check
