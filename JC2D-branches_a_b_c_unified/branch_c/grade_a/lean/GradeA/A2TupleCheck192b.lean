/- A2 tuple-check chunk 192b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk192b : (1925 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk192b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1925 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1925) boundChunk192b⟩)).all (checkFun ⟨1925 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1925) boundChunk192b⟩) = true ∧ linkFun ⟨1925 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1925) boundChunk192b⟩ = true := by
  decide +kernel

end BranchC.A2Check
