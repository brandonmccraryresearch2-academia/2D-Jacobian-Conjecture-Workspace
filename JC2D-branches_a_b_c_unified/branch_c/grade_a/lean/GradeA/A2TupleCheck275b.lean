/- A2 tuple-check chunk 275b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk275b : (2755 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk275b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2755 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2755) boundChunk275b⟩)).all (checkFun ⟨2755 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2755) boundChunk275b⟩) = true ∧ linkFun ⟨2755 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2755) boundChunk275b⟩ = true := by
  decide +kernel

end BranchC.A2Check
