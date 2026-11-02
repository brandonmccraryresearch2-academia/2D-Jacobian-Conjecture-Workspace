/- A2 tuple-check chunk 56 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk56 : (560 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk56 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨560 + j, Nat.lt_trans (Nat.add_lt_add_left hj 560) boundChunk56⟩)).all (checkFun ⟨560 + j, Nat.lt_trans (Nat.add_lt_add_left hj 560) boundChunk56⟩) = true ∧ linkFun ⟨560 + j, Nat.lt_trans (Nat.add_lt_add_left hj 560) boundChunk56⟩ = true := by
  decide +kernel

end BranchC.A2Check
