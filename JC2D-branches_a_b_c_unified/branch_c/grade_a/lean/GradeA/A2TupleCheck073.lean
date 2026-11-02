/- A2 tuple-check chunk 73 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk73 : (730 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk73 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨730 + j, Nat.lt_trans (Nat.add_lt_add_left hj 730) boundChunk73⟩)).all (checkFun ⟨730 + j, Nat.lt_trans (Nat.add_lt_add_left hj 730) boundChunk73⟩) = true ∧ linkFun ⟨730 + j, Nat.lt_trans (Nat.add_lt_add_left hj 730) boundChunk73⟩ = true := by
  decide +kernel

end BranchC.A2Check
