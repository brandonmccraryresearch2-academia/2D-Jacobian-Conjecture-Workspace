/- A2 tuple-check chunk 148a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk148a : (1480 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk148a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1480 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1480) boundChunk148a⟩)).all (checkFun ⟨1480 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1480) boundChunk148a⟩) = true ∧ linkFun ⟨1480 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1480) boundChunk148a⟩ = true := by
  decide +kernel

end BranchC.A2Check
