/- A2 tuple-check chunk 195b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk195b : (1955 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk195b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1955 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1955) boundChunk195b⟩)).all (checkFun ⟨1955 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1955) boundChunk195b⟩) = true ∧ linkFun ⟨1955 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1955) boundChunk195b⟩ = true := by
  decide +kernel

end BranchC.A2Check
