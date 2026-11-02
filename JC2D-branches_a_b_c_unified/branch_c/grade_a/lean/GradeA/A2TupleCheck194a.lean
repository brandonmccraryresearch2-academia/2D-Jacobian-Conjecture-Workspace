/- A2 tuple-check chunk 194a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk194a : (1940 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk194a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1940 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1940) boundChunk194a⟩)).all (checkFun ⟨1940 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1940) boundChunk194a⟩) = true ∧ linkFun ⟨1940 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1940) boundChunk194a⟩ = true := by
  decide +kernel

end BranchC.A2Check
