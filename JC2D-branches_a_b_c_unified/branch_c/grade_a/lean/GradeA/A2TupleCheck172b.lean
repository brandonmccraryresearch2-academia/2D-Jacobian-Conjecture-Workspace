/- A2 tuple-check chunk 172b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk172b : (1725 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk172b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1725 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1725) boundChunk172b⟩)).all (checkFun ⟨1725 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1725) boundChunk172b⟩) = true ∧ linkFun ⟨1725 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1725) boundChunk172b⟩ = true := by
  decide +kernel

end BranchC.A2Check
