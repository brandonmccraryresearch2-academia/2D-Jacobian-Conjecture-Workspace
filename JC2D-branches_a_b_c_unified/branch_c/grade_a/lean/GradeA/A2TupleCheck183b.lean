/- A2 tuple-check chunk 183b (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk183b : (1835 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk183b : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1835 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1835) boundChunk183b⟩)).all (checkFun ⟨1835 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1835) boundChunk183b⟩) = true ∧ linkFun ⟨1835 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1835) boundChunk183b⟩ = true := by
  decide +kernel

end BranchC.A2Check
