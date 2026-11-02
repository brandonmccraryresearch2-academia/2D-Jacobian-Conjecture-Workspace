/- A2 tuple-check chunk 144b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk144b : (1445 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk144b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1445 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1445) boundChunk144b⟩)).all (checkFun ⟨1445 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1445) boundChunk144b⟩) = true ∧ linkFun ⟨1445 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1445) boundChunk144b⟩ = true := by
  decide +kernel

end BranchC.A2Check
