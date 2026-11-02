/- A2 tuple-check chunk 98 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk98 : (980 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk98 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨980 + j, Nat.lt_trans (Nat.add_lt_add_left hj 980) boundChunk98⟩)).all (checkFun ⟨980 + j, Nat.lt_trans (Nat.add_lt_add_left hj 980) boundChunk98⟩) = true ∧ linkFun ⟨980 + j, Nat.lt_trans (Nat.add_lt_add_left hj 980) boundChunk98⟩ = true := by
  decide +kernel

end BranchC.A2Check
