/- A2 tuple-check chunk 188b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk188b : (1885 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk188b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1885 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1885) boundChunk188b⟩)).all (checkFun ⟨1885 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1885) boundChunk188b⟩) = true ∧ linkFun ⟨1885 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1885) boundChunk188b⟩ = true := by
  decide +kernel

end BranchC.A2Check
