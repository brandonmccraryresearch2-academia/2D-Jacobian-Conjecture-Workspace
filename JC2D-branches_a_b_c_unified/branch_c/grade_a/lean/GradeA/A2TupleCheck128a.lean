/- A2 tuple-check chunk 128a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk128a : (1280 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk128a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1280 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1280) boundChunk128a⟩)).all (checkFun ⟨1280 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1280) boundChunk128a⟩) = true ∧ linkFun ⟨1280 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1280) boundChunk128a⟩ = true := by
  decide +kernel

end BranchC.A2Check
