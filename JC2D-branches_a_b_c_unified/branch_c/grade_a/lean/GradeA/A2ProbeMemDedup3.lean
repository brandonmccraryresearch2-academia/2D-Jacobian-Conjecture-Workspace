import GradeA.A2TupleCheckBase
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace BranchC.A2Check
def dedup5 (l : List (Nat × Nat × Nat × Nat × Nat)) :
    List (Nat × Nat × Nat × Nat × Nat) :=
  l.foldr (fun x acc => if acc.any (fun y => decide (x = y)) then acc else x :: acc) []
theorem mem_dedup5_of_mem : ∀ (x : Nat × Nat × Nat × Nat × Nat)
    (l : List (Nat × Nat × Nat × Nat × Nat)), x ∈ l → x ∈ dedup5 l := by
  intro x l
  induction l with
  | nil => intro h; simp at h
  | cons a as ih =>
      intro h
      have hstep : dedup5 (a :: as) =
          (if (dedup5 as).any (fun y => decide (a = y)) then dedup5 as
           else a :: dedup5 as) := rfl
      rw [hstep]
      by_cases ha : (dedup5 as).any (fun y => decide (a = y)) = true
      · rw [ite_eq_left ha]
        simp only [List.mem_cons] at h
        cases h with
        | inl hx =>
            rw [List.any_eq_true] at ha
            obtain ⟨y, hy, hy2⟩ := ha
            have hay : a = y := of_decide_eq_true hy2
            rw [hx, hay]
            exact hy
        | inr hx => exact ih hx
      · rw [ite_eq_right ha]
        simp only [List.mem_cons] at h ⊢
        cases h with
        | inl hx => exact Or.inl hx
        | inr hx => exact Or.inr (ih hx)
end BranchC.A2Check
