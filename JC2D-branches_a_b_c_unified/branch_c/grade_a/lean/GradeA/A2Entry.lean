/-
# A2, generic entry lemma (branch (c))

The evaluated Macaulay entry at row `r`, pivot column `c` equals the
tuple sum over the generator's term list: the bridge between the
`MvPolynomial` form (`macaulay`, `polyOfTerms`) and the plain-Nat
5-tuple checks of the core-only column-check file.

Imports: `Chart.Gens` (the `tl_*` term lists), `Chart.Poly`
(`polyOfTerms`, `Term.poly/mono/coeffX`), `Macaulay` (`macaulay`),
`A2Data` (rows, pivot generators/multipliers).  No bundle modules beyond
what `Chart.Poly` already needs (`ChartProof.Reflect`, whose olean exists
in `branches_a_b/lean/.lake`).
-/

import GradeA.Chart.Gens
import GradeA.Chart.Poly
import GradeA.Macaulay
import GradeA.A2Data

namespace BranchC.A2Entry

open BranchC.GradeA.Chart BranchC.GradeA BranchC.A2Data Polynomial

/-- The six chart generators as `MvPolynomial (Fin 5) ℤ[X]`, in the
comparator's `Fpoly` order (0=Psi, 1=Phi1, 2=Phi2, 3=Theta1, 4=Theta2,
5=Theta3).  Definitionally the comparator's `Fpoly`. -/
noncomputable def Fpoly2 : Fin 6 → MvPolynomial (Fin 5) ℤ[X]
  | 0 => polyOfTerms tl_Psi
  | 1 => polyOfTerms tl_Phi1
  | 2 => polyOfTerms tl_Phi2
  | 3 => polyOfTerms tl_Theta1
  | 4 => polyOfTerms tl_Theta2
  | 5 => polyOfTerms tl_Theta3

/-- Term lists in `Fpoly` order. -/
noncomputable def tlFun : Fin 6 → List Term
  | 0 => tl_Psi
  | 1 => tl_Phi1
  | 2 => tl_Phi2
  | 3 => tl_Theta1
  | 4 => tl_Theta2
  | 5 => tl_Theta3

/-- `Fpoly2 n` is `polyOfTerms (tlFun n)`, by cases on the generator. -/
theorem Fpoly2_tlFun (n : Fin 6) : Fpoly2 n = polyOfTerms (tlFun n) := by
  fin_cases n <;> simp [Fpoly2, tlFun]

/-- Term list of the generator of pivot column `c`. -/
noncomputable def colTerms (c : Fin 3199) : List Term := tlFun (genFun c)

/-- `Fpoly2 (genFun c)` is `polyOfTerms (colTerms c)`. -/
theorem Fpoly2_colTerms (c : Fin 3199) : Fpoly2 (genFun c) = polyOfTerms (colTerms c) :=
  Fpoly2_tlFun (genFun c)

/-- A 5-tuple as a `Fin 5 →₀ ℕ` monomial, in exactly `Term.mono`'s form. -/
noncomputable def finsuppOfTuple (t : Nat × Nat × Nat × Nat × Nat) : Fin 5 →₀ ℕ :=
  Finsupp.single 0 t.1 + Finsupp.single 1 t.2.1 + Finsupp.single 2 t.2.2.1 +
    Finsupp.single 3 t.2.2.2.1 + Finsupp.single 4 t.2.2.2.2

/-- The row monomial of row `r`, as a `Fin 5 →₀ ℕ`. -/
noncomputable def rowMono (r : Fin 3199) : Fin 5 →₀ ℕ := finsuppOfTuple (rowTuple r)

/-- The multiplier monomial of pivot column `c`, as a `Fin 5 →₀ ℕ`. -/
noncomputable def multMono (c : Fin 3199) : Fin 5 →₀ ℕ := finsuppOfTuple (multTuple c)

/-- A chart term's monomial, as a 5-tuple. -/
def mono5 (t : Term) : Nat × Nat × Nat × Nat × Nat := (t.et, t.es, t.er, t.eu, t.eq)

/-- `Term.mono` is `finsuppOfTuple` of the 5-tuple, by definition. -/
theorem mono_finsuppOfTuple (t : Term) : t.mono = finsuppOfTuple (mono5 t) := rfl

/-- `finsuppOfTuple` preserves tuple addition. -/
theorem finsuppOfTuple_add (a b : Nat × Nat × Nat × Nat × Nat) :
    finsuppOfTuple (a + b) = finsuppOfTuple a + finsuppOfTuple b := by
  apply Finsupp.ext
  intro i
  fin_cases i <;> simp [finsuppOfTuple]

/-- `finsuppOfTuple` is injective. -/
theorem finsuppOfTuple_injective : Function.Injective finsuppOfTuple := by
  intro a b h
  obtain ⟨a1, a2, a3, a4, a5⟩ := a
  obtain ⟨b1, b2, b3, b4, b5⟩ := b
  have h' := Finsupp.ext_iff.mp h
  have e0 := h' 0
  have e1 := h' 1
  have e2 := h' 2
  have e3 := h' 3
  have e4 := h' 4
  simp [finsuppOfTuple] at e0 e1 e2 e3 e4
  exact Prod.ext e0 (Prod.ext e1 (Prod.ext e2 (Prod.ext e3 e4)))

/-- Right summand is below a sum, for `Fin 5 →₀ ℕ`. -/
theorem finsupp_le_add_left (a b : Fin 5 →₀ ℕ) : b ≤ a + b := by
  rw [Finsupp.le_iff]
  intro i _
  rw [Finsupp.add_apply]
  exact Nat.le_add_left _ _

/-- A term's evaluated coefficient at `w0 = 11147` mod `32003`. -/
noncomputable def evalTerm (t : Term) : ZMod 32003 :=
  (t.c : ZMod 32003) * (11147 : ZMod 32003) ^ t.i

/-- Evaluation of a term's `ℤ[X]` coefficient. -/
theorem eval_coeffX (t : Term) :
    (eval₂RingHom (Int.castRingHom (ZMod 32003)) 11147) t.coeffX = evalTerm t := by
  simp [Term.coeffX, evalTerm, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X_pow]

/-- The tuple sum: evaluated Macaulay entry at `(r, c)` in tuple form. -/
noncomputable def tupleSum (c r : Fin 3199) : ZMod 32003 :=
  ((colTerms c).map (fun t =>
    if mono5 t + multTuple c = rowTuple r then evalTerm t else 0)).sum

/-- Coefficient of `polyOfTerms`, as a term sum. -/
theorem polyOfTerms_coeff (l : List Term) (d : Fin 5 →₀ ℕ) :
    (polyOfTerms l).coeff d = (l.map (fun t => t.poly.coeff d)).sum := by
  induction l with
  | nil => simp [polyOfTerms]
  | cons t ts ih =>
    show (t.poly + polyOfTerms ts).coeff d = _
    rw [MvPolynomial.coeff_add, ih]
    simp [List.map_cons, List.sum_cons]

/-- Evaluated coefficient of `polyOfTerms`, as a term sum. -/
theorem eval_polyOfTerms_coeff (l : List Term) (d : Fin 5 →₀ ℕ) :
    (eval₂RingHom (Int.castRingHom (ZMod 32003)) 11147) ((polyOfTerms l).coeff d) =
      (l.map (fun t => if t.mono = d then evalTerm t else 0)).sum := by
  induction l with
  | nil => simp [polyOfTerms]
  | cons t ts ih =>
    show (eval₂RingHom (Int.castRingHom (ZMod 32003)) 11147)
        ((t.poly + polyOfTerms ts).coeff d) = _
    rw [MvPolynomial.coeff_add, map_add, ih]
    rw [Term.poly, MvPolynomial.coeff_monomial]
    by_cases hd : t.mono = d
    · rw [if_pos hd, eval_coeffX]
      simp [List.map_cons, List.sum_cons, hd]
    · rw [if_neg hd]
      simp [List.map_cons, List.sum_cons, hd]

/-- The Finsupp condition and the tuple condition coincide, under
`multMono c ≤ rowMono r`. -/
theorem cond_iff (h : multMono c ≤ rowMono r) (t : Term) :
    (t.mono = rowMono r - multMono c) ↔ (mono5 t + multTuple c = rowTuple r) := by
  constructor
  · intro ht
    apply finsuppOfTuple_injective
    calc finsuppOfTuple (mono5 t + multTuple c)
        = finsuppOfTuple (mono5 t) + finsuppOfTuple (multTuple c) :=
          finsuppOfTuple_add _ _
      _ = t.mono + multMono c := by simp only [← mono_finsuppOfTuple, multMono]
      _ = rowMono r := by rw [ht, tsub_add_cancel_of_le h]
      _ = finsuppOfTuple (rowTuple r) := rfl
  · intro ht
    have h2 : t.mono + multMono c = rowMono r := by
      calc t.mono + multMono c
          = finsuppOfTuple (mono5 t) + finsuppOfTuple (multTuple c) := by
            simp only [mono_finsuppOfTuple, multMono]
        _ = finsuppOfTuple (mono5 t + multTuple c) := (finsuppOfTuple_add _ _).symm
        _ = finsuppOfTuple (rowTuple r) := congrArg finsuppOfTuple ht
        _ = rowMono r := rfl
    rw [← h2, add_tsub_cancel_right]

/-- Sum congruence for mapped lists, by induction (no `List.sum_congr`
in this Mathlib). -/
theorem map_sum_congr {l : List Term} {f g : Term → ZMod 32003}
    (h : ∀ t ∈ l, f t = g t) : (l.map f).sum = (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons t ts ih =>
    have h1 : f t = g t := h t List.mem_cons_self
    have h2 : (ts.map f).sum = (ts.map g).sum :=
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.sum_cons, h1, h2]

/-- **The generic entry lemma.** The evaluated Macaulay entry at
`(r, c)` is the tuple sum. -/
theorem evaluatedEntry (r c : Fin 3199) :
    (eval₂RingHom (Int.castRingHom (ZMod 32003)) 11147).mapMatrix
      (macaulay Fpoly2 rowMono genFun multMono) r c = tupleSum c r := by
  rw [RingHom.mapMatrix_apply]
  show (eval₂RingHom (Int.castRingHom (ZMod 32003)) 11147)
      ((MvPolynomial.monomial (multMono c) 1 * Fpoly2 (genFun c)).coeff (rowMono r)) = _
  rw [MvPolynomial.coeff_monomial_mul', Fpoly2_colTerms]
  by_cases h : multMono c ≤ rowMono r
  · rw [if_pos h, one_mul, eval_polyOfTerms_coeff]
    unfold tupleSum
    apply map_sum_congr
    intro t _
    show (if t.mono = rowMono r - multMono c then evalTerm t else 0) =
      (if mono5 t + multTuple c = rowTuple r then evalTerm t else 0)
    by_cases hc : t.mono = rowMono r - multMono c
    · rw [if_pos hc, if_pos ((cond_iff h t).mp hc)]
    · rw [if_neg hc, if_neg (fun hcon => hc ((cond_iff h t).mpr hcon))]
  · rw [if_neg h, map_zero]
    symm
    unfold tupleSum
    apply List.sum_eq_zero
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    show (if mono5 t + multTuple c = rowTuple r then evalTerm t else 0) = 0
    by_cases hc : mono5 t + multTuple c = rowTuple r
    · exfalso
      apply h
      have h2 : t.mono + multMono c = rowMono r := by
        calc t.mono + multMono c
            = finsuppOfTuple (mono5 t) + finsuppOfTuple (multTuple c) := by
              simp only [mono_finsuppOfTuple, multMono]
          _ = finsuppOfTuple (mono5 t + multTuple c) := (finsuppOfTuple_add _ _).symm
          _ = finsuppOfTuple (rowTuple r) := congrArg finsuppOfTuple hc
          _ = rowMono r := rfl
      rw [← h2]
      exact finsupp_le_add_left _ _
    · rw [if_neg hc]

end BranchC.A2Entry
