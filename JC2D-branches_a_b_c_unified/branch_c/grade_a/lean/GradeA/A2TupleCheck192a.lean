/- A2 tuple-check chunk 192a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk192a : (1920 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk192a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1920 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1920) boundChunk192a⟩)).all (checkFun ⟨1920 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1920) boundChunk192a⟩) = true ∧ linkFun ⟨1920 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1920) boundChunk192a⟩ = true := by
  decide +kernel

end BranchC.A2Check
