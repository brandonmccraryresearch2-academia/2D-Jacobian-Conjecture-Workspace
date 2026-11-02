/- A2 tuple-check chunk 178a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk178a : (1780 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk178a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1780 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1780) boundChunk178a⟩)).all (checkFun ⟨1780 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1780) boundChunk178a⟩) = true ∧ linkFun ⟨1780 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1780) boundChunk178a⟩ = true := by
  decide +kernel

end BranchC.A2Check
