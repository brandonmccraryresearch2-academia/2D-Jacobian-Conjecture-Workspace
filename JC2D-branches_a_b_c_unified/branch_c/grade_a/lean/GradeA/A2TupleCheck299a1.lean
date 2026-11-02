/- A2 tuple-check chunk 299a1 (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk299a1 : (2990 + 2 : Nat) < 3199 := by decide
theorem colCheckChunk299a1 : ∀ (j : Nat) (hj : j < 2),
    (dedup5 (unionTuples ⟨2990 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2990) boundChunk299a1⟩)).all (checkFun ⟨2990 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2990) boundChunk299a1⟩) = true ∧ linkFun ⟨2990 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2990) boundChunk299a1⟩ = true := by
  decide +kernel

end BranchC.A2Check
