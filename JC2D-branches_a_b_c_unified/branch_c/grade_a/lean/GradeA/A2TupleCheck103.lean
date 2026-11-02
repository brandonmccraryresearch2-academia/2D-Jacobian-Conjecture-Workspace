/- A2 tuple-check chunk 103 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk103 : (1030 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk103 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨1030 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1030) boundChunk103⟩)).all (checkFun ⟨1030 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1030) boundChunk103⟩) = true ∧ linkFun ⟨1030 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1030) boundChunk103⟩ = true := by
  decide +kernel

end BranchC.A2Check
