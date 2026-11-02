/- A2 tuple-check chunk 28 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk28 : (280 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk28 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨280 + j, Nat.lt_trans (Nat.add_lt_add_left hj 280) boundChunk28⟩)).all (checkFun ⟨280 + j, Nat.lt_trans (Nat.add_lt_add_left hj 280) boundChunk28⟩) = true ∧ linkFun ⟨280 + j, Nat.lt_trans (Nat.add_lt_add_left hj 280) boundChunk28⟩ = true := by
  decide +kernel

end BranchC.A2Check
