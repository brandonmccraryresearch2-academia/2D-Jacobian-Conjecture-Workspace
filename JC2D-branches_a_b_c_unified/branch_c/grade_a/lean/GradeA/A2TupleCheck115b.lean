/- A2 tuple-check chunk 115b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk115b : (1155 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk115b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1155 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1155) boundChunk115b⟩)).all (checkFun ⟨1155 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1155) boundChunk115b⟩) = true ∧ linkFun ⟨1155 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1155) boundChunk115b⟩ = true := by
  decide +kernel

end BranchC.A2Check
