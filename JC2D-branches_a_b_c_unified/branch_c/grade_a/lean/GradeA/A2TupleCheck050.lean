/- A2 tuple-check chunk 50 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk50 : (500 + 10 : Nat) < 3199 := by decide
theorem colCheckChunk50 : ∀ (j : Nat) (hj : j < 10),
    (dedup5 (unionTuples ⟨500 + j, Nat.lt_trans (Nat.add_lt_add_left hj 500) boundChunk50⟩)).all (checkFun ⟨500 + j, Nat.lt_trans (Nat.add_lt_add_left hj 500) boundChunk50⟩) = true ∧ linkFun ⟨500 + j, Nat.lt_trans (Nat.add_lt_add_left hj 500) boundChunk50⟩ = true := by
  decide +kernel

end BranchC.A2Check
