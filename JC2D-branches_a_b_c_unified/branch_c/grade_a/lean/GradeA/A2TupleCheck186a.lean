/- A2 tuple-check chunk 186a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk186a : (1860 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk186a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1860 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1860) boundChunk186a⟩)).all (checkFun ⟨1860 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1860) boundChunk186a⟩) = true ∧ linkFun ⟨1860 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1860) boundChunk186a⟩ = true := by
  decide +kernel

end BranchC.A2Check
