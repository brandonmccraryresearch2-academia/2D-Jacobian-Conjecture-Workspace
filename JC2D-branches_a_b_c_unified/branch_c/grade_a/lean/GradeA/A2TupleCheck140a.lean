/- A2 tuple-check chunk 140a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk140a : (1400 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk140a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1400 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1400) boundChunk140a⟩)).all (checkFun ⟨1400 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1400) boundChunk140a⟩) = true ∧ linkFun ⟨1400 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1400) boundChunk140a⟩ = true := by
  decide +kernel

end BranchC.A2Check
