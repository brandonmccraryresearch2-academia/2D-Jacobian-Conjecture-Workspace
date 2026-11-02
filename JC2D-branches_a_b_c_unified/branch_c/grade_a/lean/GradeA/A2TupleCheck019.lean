/- A2 tuple-check chunk 19 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk19 : (190 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk19 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨190 + j, Nat.lt_trans (Nat.add_lt_add_left hj 190) boundChunk19⟩)).all (checkFun ⟨190 + j, Nat.lt_trans (Nat.add_lt_add_left hj 190) boundChunk19⟩) = true ∧ linkFun ⟨190 + j, Nat.lt_trans (Nat.add_lt_add_left hj 190) boundChunk19⟩ = true := by
  decide +kernel

end BranchC.A2Check
