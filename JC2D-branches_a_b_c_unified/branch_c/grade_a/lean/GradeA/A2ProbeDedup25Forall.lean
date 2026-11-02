import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace BranchC.A2Check
def dedup5 (l : List (Nat × Nat × Nat × Nat × Nat)) :
    List (Nat × Nat × Nat × Nat × Nat) :=
  l.foldr (fun x acc => if acc.any (fun y => decide (x = y)) then acc else x :: acc) []
theorem probeDedup25Forall : ∀ c : Fin 3199, 0 ≤ c.val → c.val < 25 →
    (dedup5 (unionTuples c)).all (checkFun c) = true ∧ linkFun c = true := by
  decide +kernel
end BranchC.A2Check
