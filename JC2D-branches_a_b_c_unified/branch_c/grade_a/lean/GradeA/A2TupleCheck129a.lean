/- A2 tuple-check chunk 129a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk129a : (1290 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk129a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1290 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1290) boundChunk129a⟩)).all (checkFun ⟨1290 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1290) boundChunk129a⟩) = true ∧ linkFun ⟨1290 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1290) boundChunk129a⟩ = true := by
  decide +kernel

end BranchC.A2Check
