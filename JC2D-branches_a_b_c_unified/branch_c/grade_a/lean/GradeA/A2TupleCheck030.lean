/- A2 tuple-check chunk 30 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk30 : (300 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk30 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨300 + j, Nat.lt_trans (Nat.add_lt_add_left hj 300) boundChunk30⟩)).all (checkFun ⟨300 + j, Nat.lt_trans (Nat.add_lt_add_left hj 300) boundChunk30⟩) = true ∧ linkFun ⟨300 + j, Nat.lt_trans (Nat.add_lt_add_left hj 300) boundChunk30⟩ = true := by
  decide +kernel

end BranchC.A2Check
