/- A2 tuple-check chunk 132a (core-only, Nat-bounded, deduped). -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

theorem boundChunk132a : (1320 + 5 : Nat) < 3199 := by decide
theorem colCheckChunk132a : ∀ (j : Nat) (hj : j < 5),
    (dedup5 (unionTuples ⟨1320 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1320) boundChunk132a⟩)).all (checkFun ⟨1320 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1320) boundChunk132a⟩) = true ∧ linkFun ⟨1320 + j, Nat.lt_trans (Nat.add_lt_add_left hj 1320) boundChunk132a⟩ = true := by
  decide +kernel

end BranchC.A2Check
