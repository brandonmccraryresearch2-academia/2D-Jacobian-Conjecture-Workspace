/- A2 tuple-check chunk 145b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk145b : (1455 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk145b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1455 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1455) boundChunk145b⟩)).all (checkFun ⟨1455 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1455) boundChunk145b⟩) = true ∧ linkFun ⟨1455 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1455) boundChunk145b⟩ = true := by
  decide +kernel

end BranchC.A2Check
