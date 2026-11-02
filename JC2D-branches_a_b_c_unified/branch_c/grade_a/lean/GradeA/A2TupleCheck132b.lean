/- A2 tuple-check chunk 132b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk132b : (1325 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk132b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1325 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1325) boundChunk132b⟩)).all (checkFun ⟨1325 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1325) boundChunk132b⟩) = true ∧ linkFun ⟨1325 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1325) boundChunk132b⟩ = true := by
  decide +kernel

end BranchC.A2Check
