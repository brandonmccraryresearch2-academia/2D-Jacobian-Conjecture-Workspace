/- A2 tuple-check chunk 51 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk51 : (510 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk51 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨510 + j, Nat.lt_trans (Nat.add_lt_add_left hj 510) boundChunk51⟩)).all (checkFun ⟨510 + j, Nat.lt_trans (Nat.add_lt_add_left hj 510) boundChunk51⟩) = true ∧ linkFun ⟨510 + j, Nat.lt_trans (Nat.add_lt_add_left hj 510) boundChunk51⟩ = true := by
  decide +kernel

end BranchC.A2Check
