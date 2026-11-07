import Mathlib

/-! # R13 — D1 full theory: en/st as homogeneous parts, Pred/Succ as operators
(Phase 4, Leg E)

**CLAIM:** `dirLt` transitivity on an interval (the gap narrowed in
inventory.md 21:45/22:20) is kernel; set-level consecutiveness and Succ as
an operator are kernel modulo an explicit uniqueness premise.
**STATUS:**
  - KERNEL: `dirLt_trans_halfplane` — the cross-product order is
    transitive for directions in one open half-plane. Proof: the vector
    identity `cross(a,b)·(w·c) + cross(b,c)·(w·a) + cross(c,a)·(w·b) = 0`
    (`cross_dot_identity`, by `ring`), so if `cross(a,b), cross(b,c) >
    0` and `w·a, w·b, w·c > 0` then `cross(c,a) < 0`, i.e.
    `cross(a,c) > 0`. This closes gap (b) of the 21:45 entry ("dirLt
    TRANSITIVITY on an interval") in the half-plane form — which is the
    paper's own form: TeX 1186–1191, "`(ρ,σ) < (ρ',σ') ⟺
    (ρ,σ)×(ρ',σ') > 0`" holds on intervals containing no closed half
    circle. Gap (a) (dirs ↔ isDir bridge) stays a carried hypothesis
    `hdirs` in `succ_set_consecutive`, exactly as the 22:20 entry
    specifies ("carry `hdirs : ∀ δ, δ ∈ dirs ↔ isDir`").
  - KERNEL: `succ_set_consecutive` — from `isSuccFrom` (Part20, line
    140 — already "no element strictly between") + `hdirs`, the
    set-level consecutiveness: no `Dir(P)` element lies strictly
    between a direction and its successor. This closes gap (c) modulo
    `hdirs`.
  - KERNEL (modulo explicit uniqueness): `succOp` — Succ as an operator
    (a function `List (Int×Int) → Int×Int → Option (Int×Int)`), with
    `succOp_spec` (it returns a successor when one exists) and
    `succOp_eq_of_isSuccFrom` (it returns THE successor, given the
    uniqueness premise `huniq`). The paper's circular Succ/Pred
    coincide with `isSuccFrom` only on intervals of span < 180° (see
    the d2combine header caveat on Pred_5/Succ_1); the operator here is
    the interval form, and the caveat is recorded, not hidden.
  - NOT proved here: gap (d) of the 21:45 entry in full generality —
    the `stFace`/`enFace` ↔ CCW `st`/`en` bridge. The bridge's sharp
    form (inventory.md "Starting-vs-end node CLOSED") is the
    `(1,-1)`/`(-1,1)` slice formulas, which Part17 already implements
    on the list side; the remaining step is proving Part17's
    `stFace`/`enFace` satisfy the CCW definition via `cross > 0` +
    endpoints. That step is NOT in this file — it needs the face-list
    machinery (Part17, ~600 lines) copied into the file, which would
    exceed the chunking budget for this leg; it is recorded here as the
    precise remaining D1 gap.
No `sorry` anywhere; no `axiom` anywhere.
-/

/-- Cross product of two integer vectors (Part14, verbatim). -/
def crossProd (a b : Int × Int) : Int := a.1 * b.2 - a.2 * b.1

/-- Dot product of two integer vectors. -/
def dotProd (a b : Int × Int) : Int := a.1 * b.1 + a.2 * b.2

/-- The direction order: `a < b` iff `cross(a,b) > 0` (Part20 `dirLt`). -/
def dirLt (a b : Int × Int) : Prop := 0 < crossProd a b

/-- The vector identity behind transitivity: for any `a, b, c, w`,
`cross(a,b)·(w·c) + cross(b,c)·(w·a) + cross(c,a)·(w·b) = 0`.
(2D vector triple product, dotted with `w`.) -/
theorem cross_dot_identity (a b c w : Int × Int) :
    crossProd a b * dotProd w c + crossProd b c * dotProd w a +
      crossProd c a * dotProd w b = 0 := by
  simp only [crossProd, dotProd]
  ring

/-- `dirLt` is transitive on an open half-plane: if `a < b`, `b < c`,
and `a, b, c` all have positive dot product with `w` (i.e. they lie in
the open half-plane through the origin determined by `w`), then
`a < c`. This is the interval form of transitivity (TeX 1186–1191). -/
theorem dirLt_trans_halfplane {a b c w : Int × Int}
    (hab : dirLt a b) (hbc : dirLt b c)
    (hwa : 0 < dotProd w a) (hwb : 0 < dotProd w b) (hwc : 0 < dotProd w c) :
    dirLt a c := by
  have hid := cross_dot_identity a b c w
  -- `cross(c,a)·(w·b) = -(positive) - (positive) < 0`, and `w·b > 0`,
  -- so `cross(c,a) < 0`, i.e. `cross(a,c) > 0`.
  have hneg : crossProd c a * dotProd w b < 0 := by
    have h1 : 0 < crossProd a b * dotProd w c := mul_pos hab hwc
    have h2 : 0 < crossProd b c * dotProd w a := mul_pos hbc hwa
    omega
  have hca : crossProd c a < 0 := by
    by_contra h
    push_neg at h
    have hnn : 0 ≤ crossProd c a * dotProd w b :=
      mul_nonneg h (le_of_lt hwb)
    omega
  have hanti : crossProd a c = -crossProd c a := by
    simp only [crossProd]; ring
  show 0 < crossProd a c
  rw [hanti]
  omega

/-- Cross product is antisymmetric. -/
theorem crossProd_antisymm (a b : Int × Int) :
    crossProd b a = -crossProd a b := by
  simp only [crossProd]; ring

/-- `dirLt` is irreflexive (Part20, restated for the record). -/
theorem dirLt_irrefl' (a : Int × Int) : ¬ dirLt a a := by
  have h0 : crossProd a a = 0 := by simp only [crossProd]; ring
  show ¬ 0 < crossProd a a
  rw [h0]
  exact lt_irrefl 0

/-- `dirLt` is asymmetric. -/
theorem dirLt_asymm' {a b : Int × Int} (h : dirLt a b) : ¬ dirLt b a := by
  intro hba
  have h' : 0 < crossProd a b := h
  have hba' : 0 < crossProd b a := hba
  rw [crossProd_antisymm] at hba'
  omega

/-- List-level successor (Part20 `isSuccFrom`, line 140): `δ` is the
successor of `src` in `dirs` iff it is in the list, after `src`, and no
list element lies strictly between. -/
def isSuccFrom (src δ : Int × Int) (dirs : List (Int × Int)) : Prop :=
  δ ∈ dirs ∧ dirLt src δ ∧
    ∀ δ' ∈ dirs, dirLt src δ' → dirLt δ' δ → δ' = δ

/-- Set-level consecutiveness (gap (c) of inventory.md 21:45, narrowed
22:20): from `isSuccFrom` + the bridge `hdirs : δ ∈ dirs ↔ isDir δ`,
no `Dir` element lies strictly between `src` and its successor `δ`. -/
theorem succ_set_consecutive {src δ : Int × Int} {dirs : List (Int × Int)}
    {isDir : Int × Int → Prop}
    (hsucc : isSuccFrom src δ dirs)
    (hdirs : ∀ δ, δ ∈ dirs ↔ isDir δ) :
    ∀ δ', isDir δ' → dirLt src δ' → dirLt δ' δ → δ' = δ := by
  intro δ' hdir h1 h2
  exact hsucc.2.2 δ' ((hdirs δ').mpr hdir) h1 h2

open Classical in
/-- Succ as an operator: the successor of `src` in `dirs` if one exists.
Noncomputable (uses choice); the spec below is what matters. -/
noncomputable def succOp (dirs : List (Int × Int)) (src : Int × Int) :
    Option (Int × Int) :=
  if h : ∃ δ, isSuccFrom src δ dirs then some (Classical.choose h) else none

/-- `succOp` returns a successor whenever one exists. -/
theorem succOp_spec {dirs : List (Int × Int)} {src δ : Int × Int}
    (h : isSuccFrom src δ dirs) : succOp dirs src = some δ ∨
      (∃ δ', succOp dirs src = some δ' ∧ isSuccFrom src δ' dirs) := by
  have hex : ∃ δ', isSuccFrom src δ' dirs := ⟨δ, h⟩
  unfold succOp
  rw [dif_pos hex]
  exact Or.inr ⟨Classical.choose hex, rfl, Classical.choose_spec hex⟩

/-- `succOp` returns THE successor, given uniqueness of successors.
Uniqueness itself needs the interval/totality hypotheses (on a
half-plane interval it follows from `dirLt_trans_halfplane` +
trichotomy; it is carried here as an explicit premise, not smuggled). -/
theorem succOp_eq_of_isSuccFrom {dirs : List (Int × Int)} {src δ : Int × Int}
    (h : isSuccFrom src δ dirs)
    (huniq : ∀ δ δ', isSuccFrom src δ dirs → isSuccFrom src δ' dirs →
      δ = δ') :
    succOp dirs src = some δ := by
  have hex : ∃ δ', isSuccFrom src δ' dirs := ⟨δ, h⟩
  unfold succOp
  rw [dif_pos hex]
  congr 1
  exact huniq _ δ (Classical.choose_spec hex) h
