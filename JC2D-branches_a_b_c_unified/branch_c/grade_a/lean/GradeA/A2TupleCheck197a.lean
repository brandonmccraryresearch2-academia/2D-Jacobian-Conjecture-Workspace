/- A2 tuple-check chunk 197a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk197a : (1970 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk197a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1970 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1970) boundChunk197a⟩)).all (checkFun ⟨1970 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1970) boundChunk197a⟩) = true ∧ linkFun ⟨1970 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1970) boundChunk197a⟩ = true := by
  decide +kernel

end BranchC.A2Check
