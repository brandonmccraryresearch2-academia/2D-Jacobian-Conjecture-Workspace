/- A2 tuple-check chunk 86 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk86 : (860 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk86 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨860 + j, Nat.lt_trans (Nat.add_lt_add_left hj 860) boundChunk86⟩)).all (checkFun ⟨860 + j, Nat.lt_trans (Nat.add_lt_add_left hj 860) boundChunk86⟩) = true ∧ linkFun ⟨860 + j, Nat.lt_trans (Nat.add_lt_add_left hj 860) boundChunk86⟩ = true := by
  decide +kernel

end BranchC.A2Check
