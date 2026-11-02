/- Probe: check over hand-rolled dedup of the union, columns 0-99, Fin form. -/
import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace BranchC.A2Check

/-- Dedup for 5-tuples (core has no List.eraseDup). -/
def dedup5 (l : List (Nat × Nat × Nat × Nat × Nat)) :
    List (Nat × Nat × Nat × Nat × Nat) :=
  l.foldr (fun x acc => if acc.any (fun y => decide (x = y)) then acc else x :: acc) []

theorem probeDedup100 : ∀ c : Fin 3199, 0 ≤ c.val → c.val < 100 →
    (dedup5 (unionTuples c)).all (checkFun c) = true ∧ linkFun c = true := by
  decide +kernel

end BranchC.A2Check
