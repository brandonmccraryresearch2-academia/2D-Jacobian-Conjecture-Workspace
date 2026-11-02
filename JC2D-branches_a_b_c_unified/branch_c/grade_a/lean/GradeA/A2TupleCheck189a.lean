/- A2 tuple-check chunk 189a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk189a : (1890 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk189a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1890 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1890) boundChunk189a⟩)).all (checkFun ⟨1890 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1890) boundChunk189a⟩) = true ∧ linkFun ⟨1890 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1890) boundChunk189a⟩ = true := by
  decide +kernel

end BranchC.A2Check
