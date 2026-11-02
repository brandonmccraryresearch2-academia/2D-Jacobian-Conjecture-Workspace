/- A2 tuple-check chunk 197b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk197b : (1975 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk197b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1975 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1975) boundChunk197b⟩)).all (checkFun ⟨1975 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1975) boundChunk197b⟩) = true ∧ linkFun ⟨1975 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1975) boundChunk197b⟩ = true := by
  decide +kernel

end BranchC.A2Check
