/- A2 tuple-level column check, core-only definitions.

The tuple check: for pivot column `c` and row tuple `rt`,
  tupleSumNatT c rt % 32003 = (msValNatT c rt * scaleFun (genFun c)) % 32003.
`tupleSumNatT` sums `termValNat` over the generator's terms shifted by
`multTuple c`; `msValNatT` sums the emitted `msTuplePairs` entries.
The chunk files decide this over each column's deduped union tuples,
plus the `msTuplePairs` link to `colDataNat` (via `rowTupleOfNat`).
-/
import GradeA.A2Data
import GradeA.A2Terms
import GradeA.A1Data
import GradeA.A2MSPairs

namespace BranchC.A2Check

open BranchC.A2Data BranchC.A2Terms BranchC.A1Data BranchC.A2MSPairs

/-- Term list of the generator of pivot column `c` (A2Term mirror). -/
def colTermsNat (c : Fin 3199) : List A2Term := tlFun (genFun c)

/-- Row tuple by index, with a dummy default (indices < 3199 occur). -/
def rowTupleOfNat (n : Nat) : Nat × Nat × Nat × Nat × Nat :=
  rowsList.getD n (0, 0, 0, 0, 0)

/-- Componentwise addition of 5-tuples (core has no HAdd instance for tuples). -/
def add5 (a b : Nat × Nat × Nat × Nat × Nat) : Nat × Nat × Nat × Nat × Nat :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2.1 + b.2.2.1, a.2.2.2.1 + b.2.2.2.1, a.2.2.2.2 + b.2.2.2.2)

/-- Tuple sum at `(c, rt)`: evaluated-generator side, in Nat. -/
def tupleSumNatT (c : Fin 3199) (rt : Nat × Nat × Nat × Nat × Nat) : Nat :=
  ((colTermsNat c).map (fun t =>
    if add5 (mono5 t) (multTuple c) = rt then termValNat t else 0)).sum

/-- Tuple sum at `(c, rt)`: MS side, from emitted tuple-keyed pairs. -/
def msValNatT (c : Fin 3199) (rt : Nat × Nat × Nat × Nat × Nat) : Nat :=
  ((msTuplePairs c.val).map (fun t =>
    if t.1 = rt then t.2 else 0)).sum

/-- Shifted term tuples of column `c`. -/
def computedTuples (c : Fin 3199) : List (Nat × Nat × Nat × Nat × Nat) :=
  (colTermsNat c).map (fun t => add5 (mono5 t) (multTuple c))

/-- Union of shifted-term tuples and MS tuples of column `c`. -/
def unionTuples (c : Fin 3199) : List (Nat × Nat × Nat × Nat × Nat) :=
  computedTuples c ++ (msTuplePairs c.val).map Prod.fst

/-- Dedup for 5-tuples (core has no List.eraseDup). The chunk checks run
over `dedup5 (unionTuples c)`: the raw union has ~312 entries with
duplicates but only ~52-70 distinct rows, and each duplicate row
re-scans all 110-260 terms, which is what made bound 100 OOM. -/
def dedup5 (l : List (Nat × Nat × Nat × Nat × Nat)) :
    List (Nat × Nat × Nat × Nat × Nat) :=
  l.foldr (fun x acc => if acc.any (fun y => decide (x = y)) then acc else x :: acc) []

/-- Membership in a list implies membership in its dedup. -/
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

/-- The per-tuple check predicate, as a Bool. -/
def checkFun (c : Fin 3199) (rt : Nat × Nat × Nat × Nat × Nat) : Bool :=
  tupleSumNatT c rt % 32003 ==
    (msValNatT c rt * scaleFun (genFun c)) % 32003

/-- The `msTuplePairs` link predicate, as a Bool. -/
def linkFun (c : Fin 3199) : Bool :=
  msTuplePairs c.val ==
    (colDataNat c.val).map (fun t => (rowTupleOfNat t.1, t.2))

/-- A Nat list sum is zero when every element is zero (core has no List.sum_eq_zero). -/
theorem nat_sum_eq_zero : ∀ (l : List Nat), (∀ x ∈ l, x = 0) → l.sum = 0 := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a as ih =>
      intro h
      rw [List.sum_cons, h a (by simp),
        ih (fun x hx => h x (by simp [hx]))]

/-- Outside the computed tuples, the tuple sum is zero. -/
theorem tupleSumNatT_zero (c : Fin 3199) (rt : Nat × Nat × Nat × Nat × Nat)
    (h : rt ∉ computedTuples c) : tupleSumNatT c rt = 0 := by
  unfold tupleSumNatT computedTuples at *
  apply nat_sum_eq_zero
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  show (if add5 (mono5 t) (multTuple c) = rt then termValNat t else 0) = 0
  by_cases hc : add5 (mono5 t) (multTuple c) = rt
  · exfalso
    apply h
    rw [List.mem_map]
    exact ⟨t, ht, hc⟩
  · rw [if_neg hc]

/-- Outside the MS tuples, the MS tuple sum is zero. -/
theorem msValNatT_zero (c : Fin 3199) (rt : Nat × Nat × Nat × Nat × Nat)
    (h : rt ∉ (msTuplePairs c.val).map Prod.fst) :
    msValNatT c rt = 0 := by
  unfold msValNatT
  apply nat_sum_eq_zero
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  show (if t.1 = rt then t.2 else 0) = 0
  by_cases hc : t.1 = rt
  · exfalso
    apply h
    rw [List.mem_map]
    exact ⟨t, ht, hc⟩
  · rw [if_neg hc]

end BranchC.A2Check
