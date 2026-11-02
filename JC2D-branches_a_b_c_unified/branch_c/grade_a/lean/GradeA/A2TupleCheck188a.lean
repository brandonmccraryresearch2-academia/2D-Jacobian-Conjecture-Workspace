/- A2 tuple-check chunk 188a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk188a : (1880 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk188a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1880 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1880) boundChunk188a⟩)).all (checkFun ⟨1880 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1880) boundChunk188a⟩) = true ∧ linkFun ⟨1880 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1880) boundChunk188a⟩ = true := by
  decide +kernel

end BranchC.A2Check
