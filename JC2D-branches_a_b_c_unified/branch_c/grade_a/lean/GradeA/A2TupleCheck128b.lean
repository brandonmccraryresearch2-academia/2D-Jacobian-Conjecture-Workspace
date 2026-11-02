/- A2 tuple-check chunk 128b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk128b : (1285 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk128b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1285 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1285) boundChunk128b⟩)).all (checkFun ⟨1285 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1285) boundChunk128b⟩) = true ∧ linkFun ⟨1285 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1285) boundChunk128b⟩ = true := by
  decide +kernel

end BranchC.A2Check
