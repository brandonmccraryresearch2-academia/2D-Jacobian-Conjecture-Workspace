/-
  BlockRank.lean — Lemma `lem:block-rank` from "No Keller Map Admits Two Dicritical Divisors".

  For distinct `e_1, ..., e_n` and `m ≥ n`, the `2m × n` matrix with entries
  `C(e_k, i) * a^{e_k - i}` (for `i = 0, ..., m-1`, `a ∈ {a_3, a_4}` distinct nonzero)
  has rank `n`.

  Proof strategy (following the paper):
  1. The `n × n` matrix `[C(e_k, i)]` factors as `L * W` where `L` is lower-triangular
     with diagonal `1/i!` (from the falling-factorial polynomial identity) and `W`
     is (transpose of) Vandermonde. Hence `det = (∏ 1/i!) * ∏_{j<k}(e_k - e_j) ≠ 0`.
  2. The `2m × n` block matrix contains an `n × n` submatrix (rows `(i, a_3)`,
     `i < n`) which equals `D₁ * C * D₂` for diagonal `D₁, D₂` with nonzero entries.
     So the submatrix has nonzero determinant, forcing full column rank `n`.
-/
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Order.OrderDual

open Matrix Finset Polynomial

variable {K : Type*} [Field K] [CharZero K]

-- ============================================================================
-- Section 1: The falling-factorial polynomial and the choose identity
-- ============================================================================

section ChoosePoly

/-- The falling-factorial polynomial `∏_{j < i} (X - j)`, monic of degree `i`. -/
noncomputable def choosePoly (i : Nat) : Polynomial K :=
  ∏ j ∈ Finset.range i, (Polynomial.X - Polynomial.C (j : K))

theorem choosePoly_monic (i : Nat) : (choosePoly (i : Nat) : Polynomial K).Monic := by
  unfold choosePoly
  apply monic_prod_of_monic
  intro j _
  exact Polynomial.monic_X_sub_C _

theorem choosePoly_natDegree (i : Nat) : (choosePoly (i : Nat) : Polynomial K).natDegree = i := by
  induction i with
  | zero =>
    simp [choosePoly]
  | succ k ih =>
    have hprod : choosePoly (k + 1 : Nat) = choosePoly (k : Nat) * (Polynomial.X - Polynomial.C (k : K)) := by
      unfold choosePoly
      rw [Finset.prod_range_succ]
    rw [hprod, Polynomial.natDegree_mul (choosePoly_monic k).ne_zero (Polynomial.monic_X_sub_C _).ne_zero,
      ih, Polynomial.natDegree_X_sub_C]

/-- Evaluation of `choosePoly`: `∏_{j < i} (x - j)`. -/
theorem choosePoly_eval (i : Nat) (x : K) :
    (choosePoly (i : Nat) : Polynomial K).eval x = ∏ j ∈ Finset.range i, (x - (j : K)) := by
  unfold choosePoly
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro j _
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

/-- `Nat.choose` as a polynomial evaluation: `C(e,i) = (∏_{j<i} (e-j)) / i!`. -/
theorem choose_eq_choosePoly_eval (e i : Nat) :
    (Nat.choose e i : K) = (choosePoly (i : Nat) : Polynomial K).eval (e : K) / (Nat.factorial i : K) := by
  have hfact : (Nat.factorial i : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  have h1 : (Nat.choose e i : K) * (Nat.factorial i : K) = ((e.descFactorial i : Nat) : K) := by
    have h := Nat.descFactorial_eq_factorial_mul_choose e i
    have hcast : ((e.descFactorial i : Nat) : K) = (Nat.factorial i : K) * (Nat.choose e i : K) := by
      rw [h]; push_cast; ring
    rw [hcast]; ring
  have h2 : ((e.descFactorial i : Nat) : K) = ∏ j ∈ Finset.range i, ((e : K) - (j : K)) := by
    by_cases h : i ≤ e
    · rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
      apply Finset.prod_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      rw [Nat.cast_sub (Nat.le_trans (Nat.le_of_lt hj) h)]
    · push_neg at h
      rw [Nat.descFactorial_eq_zero_iff_lt.mpr h, Nat.cast_zero]
      have h0 : ((e : K) - (e : K)) = 0 := sub_self _
      exact (Finset.prod_eq_zero (Finset.mem_range.mpr h) h0).symm
  rw [choosePoly_eval]
  field_simp
  rw [h1, h2]

end ChoosePoly

-- ============================================================================
-- Section 2: The choose-matrix has nonzero determinant
-- ============================================================================

section ChooseDet

variable {n : Nat} {e : Fin n → Nat} (he : Function.Injective e)

/-- Coefficient matrix `L i j = (choosePoly i).coeff j / i!`: lower-triangular
    with diagonal `1/i!`. -/
noncomputable def chooseCoeffMat' (K : Type*) [Field K] (n : Nat) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => (choosePoly (i.val : Nat) : Polynomial K).coeff j.val / (Nat.factorial i.val : K)

/-- Vandermonde part `W j k = (e k)^j`. -/
noncomputable def chooseVandMat' (K : Type*) [Field K] (n : Nat) (e : Fin n → Nat) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun j k => ((e k : Nat) : K) ^ j.val

/-- Evaluation as a sum over `Fin n` (terms beyond `natDegree` vanish). -/
theorem choosePoly_eval_sum (i k : Fin n) :
    (choosePoly (i.val : Nat) : Polynomial K).eval ((e k : Nat) : K)
      = ∑ j : Fin n, (choosePoly (i.val : Nat) : Polynomial K).coeff j.val
          * (((e k : Nat) : K) ^ j.val) := by
  rw [Polynomial.eval_eq_sum_range, choosePoly_natDegree,
    Fin.sum_univ_eq_sum_range (fun j =>
      (choosePoly (i.val : Nat) : Polynomial K).coeff j * (((e k : Nat) : K) ^ j))]
  have hsub : Finset.range (i.val + 1) ⊆ Finset.range n := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    have hle := Nat.succ_le_of_lt i.isLt
    omega
  apply Finset.sum_subset hsub
  intro j _ hj
  rw [Finset.mem_range] at hj
  have hle : i.val + 1 ≤ j := Nat.le_of_not_lt hj
  have hcoeff : (choosePoly (i.val : Nat) : Polynomial K).coeff j = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by
      rw [choosePoly_natDegree]; omega)
  rw [hcoeff, zero_mul]

/-- The choose matrix factors as `L * W`, entrywise. -/
theorem choose_mat_factor (i k : Fin n) :
    (Nat.choose (e k) i.val : K)
      = ∑ j : Fin n, chooseCoeffMat' K n i j * chooseVandMat' K n e j k := by
  unfold chooseCoeffMat' chooseVandMat'
  simp only [Matrix.of_apply]
  rw [choose_eq_choosePoly_eval (e k) i.val, choosePoly_eval_sum (e := e) i k,
    div_eq_inv_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- `L` is lower-triangular (zeros above the diagonal). -/
theorem chooseCoeffMat_lowerTri :
    (chooseCoeffMat' K n : Matrix (Fin n) (Fin n) K).IsLowerTriangular := by
  intro i j hij
  -- hij : toDual j < toDual i, which is definitionally i < j
  have h : i < j := hij
  have hlt : i.val < j.val := by
    rw [Fin.lt_def] at h
    exact h
  unfold chooseCoeffMat'
  simp only [Matrix.of_apply]
  have hcoeff : (choosePoly (i.val : Nat) : Polynomial K).coeff j.val = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by
      rw [choosePoly_natDegree]; exact hlt)
  rw [hcoeff, zero_div]

/-- Diagonal entries of `L` are nonzero (`1/i!`). -/
theorem chooseCoeffMat_diag_ne_zero (i : Fin n) :
    chooseCoeffMat' K n i i ≠ 0 := by
  unfold chooseCoeffMat'
  simp only [Matrix.of_apply]
  have hcoeff : (choosePoly (i.val : Nat) : Polynomial K).coeff i.val = 1 := by
    have hmonic := choosePoly_monic (K := K) i.val
    have hdeg := choosePoly_natDegree (K := K) i.val
    have h := hmonic.coeff_natDegree
    rw [hdeg] at h
    exact h
  rw [hcoeff]
  exact div_ne_zero one_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i.val))

/-- The Vandermonde part has nonzero determinant (`e` injective). -/
theorem chooseVandMat_det_ne_zero (he : Function.Injective e) :
    Matrix.det (chooseVandMat' K n e) ≠ 0 := by
  unfold chooseVandMat'
  have hW : (Matrix.of fun j k : Fin n => (((e k : Nat) : K)) ^ j.val)
      = (Matrix.vandermonde (fun k : Fin n => ((e k : Nat) : K)))ᵀ := by
    ext j k
    simp [Matrix.vandermonde_apply, Matrix.transpose_apply]
  rw [hW, Matrix.det_transpose, Matrix.det_vandermonde_ne_zero_iff]
  intro a b hab
  simp only at hab
  apply he
  exact Nat.cast_injective hab

/-- **Determinant formula.** The choose-matrix `[C(e_k, i)]` has nonzero determinant
    for distinct `e_k`. -/
theorem choose_det_ne_zero (he : Function.Injective e) :
    (Matrix.det (Matrix.of fun i k : Fin n => (Nat.choose (e k) i.val : K))) ≠ 0 := by
  have hMW : (Matrix.of fun i k : Fin n => (Nat.choose (e k) i.val : K))
      = chooseCoeffMat' K n * chooseVandMat' K n e := by
    ext i k
    simp only [Matrix.of_apply, Matrix.mul_apply]
    exact choose_mat_factor i k
  rw [hMW, Matrix.det_mul]
  apply mul_ne_zero
  · rw [Matrix.det_of_isLowerTriangular _ chooseCoeffMat_lowerTri]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => chooseCoeffMat_diag_ne_zero i)
  · exact chooseVandMat_det_ne_zero he

end ChooseDet

-- ============================================================================
-- Section 3: The full 2m × n block matrix has rank n
-- ============================================================================

section BlockRank

variable {m n : Nat} (hmn : n ≤ m)
variable {e : Fin n → Nat} (he : Function.Injective e)
variable {a b : K} (ha : a ≠ 0)

/-- The two centers as `Fin 2 → K`. -/
noncomputable def centers (a b : K) : Fin 2 → K := ![a, b]

/-- The `2m × n` block matrix. Entry `((i, c), k) = C(e_k, i) * c_a^{e_k} * (c_a^i)⁻¹`.
    For `e_k ≥ i` this equals the paper's `C(e_k,i) * c_a^{e_k - i}`; where `C = 0`
    both vanish. -/
noncomputable def blockMat (a b : K) : Matrix (Fin m × Fin 2) (Fin n) K :=
  Matrix.of fun ri k =>
    (Nat.choose (e k) ri.1.val : K) * (centers a b ri.2) ^ (e k)
      * (((centers a b ri.2) ^ (ri.1.val))⁻¹)

/-- Row embedding for the `n × n` submatrix on rows `(i, a)`, `i < n ≤ m`. -/
def subRow (hmn : n ≤ m) : Fin n → Fin m × Fin 2 :=
  fun i => (⟨i.val, Nat.lt_of_lt_of_le i.isLt hmn⟩, 0)

/-- The `n × n` submatrix. -/
noncomputable def subMat (a b : K) (hmn : n ≤ m) : Matrix (Fin n) (Fin n) K :=
  (blockMat (m := m) (e := e) a b).submatrix (subRow hmn) id

/-- The submatrix has nonzero determinant, via row/column scaling. -/
theorem subMat_det_ne_zero (he : Function.Injective e) (ha : a ≠ 0) :
    Matrix.det (subMat (e := e) a b hmn) ≠ 0 := by
  -- Entry formula
  have hentry : ∀ i k : Fin n, subMat (e := e) a b hmn i k
      = ((a ^ (i.val : Nat))⁻¹ : K) * ((Nat.choose (e k) i.val : K) * (a ^ (e k) : K)) := by
    intro i k
    simp only [subMat, blockMat, subRow, centers, Matrix.submatrix_apply,
      Matrix.of_apply, id, Matrix.cons_val_zero, Fin.isValue]
    ring
  -- Rewrite as scaled matrix
  have hmat : subMat (e := e) a b hmn
      = Matrix.of fun i k : Fin n => ((a ^ (i.val : Nat))⁻¹ : K)
        * ((Nat.choose (e k) i.val : K) * (a ^ (e k) : K)) := by
    apply Matrix.ext
    intro i k
    rw [hentry]
    rfl
  rw [hmat]
  have hdet1 : Matrix.det (Matrix.of fun i k : Fin n => ((a ^ (i.val : Nat))⁻¹ : K)
      * ((Nat.choose (e k) i.val : K) * (a ^ (e k) : K)))
      = (∏ i : Fin n, ((a ^ (i.val : Nat))⁻¹ : K))
        * Matrix.det (Matrix.of fun i k : Fin n => ((Nat.choose (e k) i.val : K) * (a ^ (e k) : K))) := by
    exact Matrix.det_mul_column (fun i : Fin n => ((a ^ (i.val : Nat))⁻¹ : K))
      (Matrix.of fun i k : Fin n => ((Nat.choose (e k) i.val : K) * (a ^ (e k) : K)))
  rw [hdet1]
  apply mul_ne_zero
  · rw [Finset.prod_ne_zero_iff]
    intro i _
    exact inv_ne_zero (pow_ne_zero _ ha)
  · -- Column scaling: C * a^(e_k) = a^(e_k) * C
    have hmat2 : (Matrix.of fun i k : Fin n => ((Nat.choose (e k) i.val : K) * (a ^ (e k) : K)))
        = Matrix.of fun i k : Fin n => (a ^ (e k) : K) * (Nat.choose (e k) i.val : K) := by
      apply Matrix.ext
      intro i k
      simp only [Matrix.of_apply]
      ring
    rw [hmat2]
    have hdet2 : Matrix.det (Matrix.of fun i k : Fin n => (a ^ (e k) : K) * (Nat.choose (e k) i.val : K))
        = (∏ k : Fin n, (a ^ (e k) : K))
          * Matrix.det (Matrix.of fun i k : Fin n => (Nat.choose (e k) i.val : K)) := by
      exact Matrix.det_mul_row (fun k : Fin n => (a ^ (e k) : K))
        (Matrix.of fun i k : Fin n => (Nat.choose (e k) i.val : K))
    rw [hdet2]
    apply mul_ne_zero
    · rw [Finset.prod_ne_zero_iff]
      intro k _
      exact pow_ne_zero _ ha
    · exact choose_det_ne_zero he

/-- Injectivity of `mulVecLin` for a square matrix with nonzero determinant. -/
theorem mulVecLin_injective_of_det_ne_zero {S : Matrix (Fin n) (Fin n) K}
    (hdet : S.det ≠ 0) : Function.Injective S.mulVecLin := by
  have hunit : IsUnit S.det := isUnit_iff_ne_zero.mpr hdet
  rw [← Matrix.isUnit_iff_isUnit_det] at hunit
  -- S is a unit; get the inverse matrix T with T * S = 1
  obtain ⟨u, hu⟩ := hunit
  have hTS : (u.inv : Matrix (Fin n) (Fin n) K) * S = 1 := by
    rw [← hu]
    exact Units.inv_mul u
  intro v w hvw
  simp only [Matrix.mulVecLin_apply] at hvw
  have h1 : (u.inv : Matrix (Fin n) (Fin n) K) *ᵥ (S *ᵥ v)
      = (u.inv : Matrix (Fin n) (Fin n) K) *ᵥ (S *ᵥ w) := by rw [hvw]
  have key : ∀ x, ((u.inv : Matrix (Fin n) (Fin n) K) * S) *ᵥ x
      = (u.inv : Matrix (Fin n) (Fin n) K) *ᵥ (S *ᵥ x) := fun x => by
    rw [Matrix.mulVec_mulVec]
  have h2 : ((u.inv : Matrix (Fin n) (Fin n) K) * S) *ᵥ v
      = ((u.inv : Matrix (Fin n) (Fin n) K) * S) *ᵥ w := by
    rw [key, key]; exact h1
  rw [hTS] at h2
  simpa using h2

/-- **Block rank lemma.** The `2m × n` matrix has rank `n`. -/
theorem block_rank (hmn : n ≤ m) (he : Function.Injective e) (ha : a ≠ 0) :
    (blockMat (m := m) (e := e) a b).rank = n := by
  have hle : (blockMat (m := m) (e := e) a b).rank ≤ n := by
    have h := Matrix.rank_le_card_width (blockMat (m := m) (e := e) a b)
    rwa [Fintype.card_fin] at h
  have hge : n ≤ (blockMat (m := m) (e := e) a b).rank := by
    have hinj : Function.Injective (blockMat (m := m) (e := e) a b).mulVecLin := by
      intro v w hvw
      have hsub : (subMat (e := e) a b hmn).mulVecLin v
          = (subMat (e := e) a b hmn).mulVecLin w := by
        ext i
        have h1 : ((subMat (e := e) a b hmn).mulVecLin v) i
            = ((blockMat (m := m) (e := e) a b).mulVecLin v) (subRow hmn i) := by
          simp only [Matrix.mulVecLin_apply, Matrix.mulVec_apply, subMat]
          apply Finset.sum_congr rfl
          intro k _
          simp [Matrix.submatrix_apply]
        have h2 : ((subMat (e := e) a b hmn).mulVecLin w) i
            = ((blockMat (m := m) (e := e) a b).mulVecLin w) (subRow hmn i) := by
          simp only [Matrix.mulVecLin_apply, Matrix.mulVec_apply, subMat]
          apply Finset.sum_congr rfl
          intro k _
          simp [Matrix.submatrix_apply]
        rw [h1, h2, hvw]
      exact mulVecLin_injective_of_det_ne_zero (subMat_det_ne_zero hmn he ha) hsub
    have hker : LinearMap.ker (blockMat (m := m) (e := e) a b).mulVecLin = ⊥ :=
      LinearMap.ker_eq_bot.mpr hinj
    have hrn := LinearMap.finrank_range_add_finrank_ker
      (blockMat (m := m) (e := e) a b).mulVecLin
    rw [hker, finrank_bot] at hrn
    have hdom : Module.finrank K (Fin n → K) = n := by
      rw [Module.finrank_pi, Fintype.card_fin]
    rw [hdom] at hrn
    -- hrn : finrank range + 0 = n, so finrank range = n
    have hrank_eq : (blockMat (m := m) (e := e) a b).rank = n := by
      unfold Matrix.rank
      omega
    omega
  omega

end BlockRank
