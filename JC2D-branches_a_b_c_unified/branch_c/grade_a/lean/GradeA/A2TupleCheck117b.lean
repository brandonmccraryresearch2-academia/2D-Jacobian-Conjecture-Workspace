/- A2 tuple-check chunk 117b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk117b : (1175 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk117b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1175 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1175) boundChunk117b⟩)).all (checkFun ⟨1175 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1175) boundChunk117b⟩) = true ∧ linkFun ⟨1175 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1175) boundChunk117b⟩ = true := by
  decide +kernel

end BranchC.A2Check
