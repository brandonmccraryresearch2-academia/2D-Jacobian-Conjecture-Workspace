/- A2 tuple-check chunk 176a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk176a : (1760 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk176a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1760 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1760) boundChunk176a⟩)).all (checkFun ⟨1760 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1760) boundChunk176a⟩) = true ∧ linkFun ⟨1760 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1760) boundChunk176a⟩ = true := by
  decide +kernel

end BranchC.A2Check
