/- A2 tuple-check chunk 318b1 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk318b1 : (3185 + 2 : Nat) < 3199 := by decide
theorem colCheckChunk318b1 : ∀ (j : Nat) (hj : j < 2),
    (dedup5 (unionTuples ⟨3185 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3185) boundChunk318b1⟩)).all (checkFun ⟨3185 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3185) boundChunk318b1⟩) = true ∧ linkFun ⟨3185 + j, Nat.lt_trans (Nat.add_lt_add_left hj 3185) boundChunk318b1⟩ = true := by
  decide +kernel

end BranchC.A2Check
