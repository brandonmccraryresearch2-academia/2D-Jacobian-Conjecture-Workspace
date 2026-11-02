/- A2 tuple-check chunk 151a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk151a : (1510 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk151a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1510 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1510) boundChunk151a⟩)).all (checkFun ⟨1510 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1510) boundChunk151a⟩) = true ∧ linkFun ⟨1510 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1510) boundChunk151a⟩ = true := by
  decide +kernel

end BranchC.A2Check
