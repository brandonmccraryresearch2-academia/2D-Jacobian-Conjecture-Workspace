/- A2 tuple-check chunk 149b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk149b : (1495 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk149b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1495 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1495) boundChunk149b⟩)).all (checkFun ⟨1495 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1495) boundChunk149b⟩) = true ∧ linkFun ⟨1495 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1495) boundChunk149b⟩ = true := by
  decide +kernel

end BranchC.A2Check
