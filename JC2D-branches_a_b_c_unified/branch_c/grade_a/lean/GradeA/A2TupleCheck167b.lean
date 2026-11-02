/- A2 tuple-check chunk 167b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk167b : (1675 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk167b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1675 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1675) boundChunk167b⟩)).all (checkFun ⟨1675 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1675) boundChunk167b⟩) = true ∧ linkFun ⟨1675 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1675) boundChunk167b⟩ = true := by
  decide +kernel

end BranchC.A2Check
