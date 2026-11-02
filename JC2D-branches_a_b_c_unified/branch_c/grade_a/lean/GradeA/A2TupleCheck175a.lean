/- A2 tuple-check chunk 175a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk175a : (1750 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk175a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1750 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1750) boundChunk175a⟩)).all (checkFun ⟨1750 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1750) boundChunk175a⟩) = true ∧ linkFun ⟨1750 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1750) boundChunk175a⟩ = true := by
  decide +kernel

end BranchC.A2Check
