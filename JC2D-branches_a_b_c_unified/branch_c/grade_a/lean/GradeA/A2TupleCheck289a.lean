/- A2 tuple-check chunk 289a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk289a : (2890 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk289a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨2890 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2890) boundChunk289a⟩)).all (checkFun ⟨2890 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2890) boundChunk289a⟩) = true ∧ linkFun ⟨2890 + j, Nat.lt_trans (Nat.add_lt_add_left hj 2890) boundChunk289a⟩ = true := by
  decide +kernel

end BranchC.A2Check
