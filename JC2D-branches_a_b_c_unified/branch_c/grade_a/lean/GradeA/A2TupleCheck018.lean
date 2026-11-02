/- A2 tuple-check chunk 18 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk18 : (180 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk18 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨180 + j, Nat.lt_trans (Nat.add_lt_add_left hj 180) boundChunk18⟩)).all (checkFun ⟨180 + j, Nat.lt_trans (Nat.add_lt_add_left hj 180) boundChunk18⟩) = true ∧ linkFun ⟨180 + j, Nat.lt_trans (Nat.add_lt_add_left hj 180) boundChunk18⟩ = true := by
  decide +kernel

end BranchC.A2Check
