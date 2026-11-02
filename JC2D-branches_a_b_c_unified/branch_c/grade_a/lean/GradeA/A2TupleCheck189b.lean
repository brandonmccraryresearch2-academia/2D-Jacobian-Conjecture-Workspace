/- A2 tuple-check chunk 189b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk189b : (1895 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk189b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1895 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1895) boundChunk189b⟩)).all (checkFun ⟨1895 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1895) boundChunk189b⟩) = true ∧ linkFun ⟨1895 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1895) boundChunk189b⟩ = true := by
  decide +kernel

end BranchC.A2Check
