/- A2 tuple-check chunk 46 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk46 : (460 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk46 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨460 + j, Nat.lt_trans (Nat.add_lt_add_left hj 460) boundChunk46⟩)).all (checkFun ⟨460 + j, Nat.lt_trans (Nat.add_lt_add_left hj 460) boundChunk46⟩) = true ∧ linkFun ⟨460 + j, Nat.lt_trans (Nat.add_lt_add_left hj 460) boundChunk46⟩ = true := by
  decide +kernel

end BranchC.A2Check
