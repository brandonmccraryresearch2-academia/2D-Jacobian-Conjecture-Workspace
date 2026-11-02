/- A2 tuple-check chunk 203a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk203a : (2030 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk203a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2030 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2030) boundChunk203a⟩)).all (checkFun ⟨2030 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2030) boundChunk203a⟩) = true ∧ linkFun ⟨2030 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2030) boundChunk203a⟩ = true := by
  decide +kernel

end BranchC.A2Check
