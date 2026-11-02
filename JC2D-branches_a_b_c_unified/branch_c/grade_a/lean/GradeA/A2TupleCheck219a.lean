/- A2 tuple-check chunk 219a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk219a : (2190 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk219a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2190 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2190) boundChunk219a⟩)).all (checkFun ⟨2190 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2190) boundChunk219a⟩) = true ∧ linkFun ⟨2190 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2190) boundChunk219a⟩ = true := by
  decide +kernel

end BranchC.A2Check
