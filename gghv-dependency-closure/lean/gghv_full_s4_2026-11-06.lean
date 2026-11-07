import Mathlib

/-!
# GGHV §4 — Propositions 4.1–4.4 + Algorithm PossibleStartingPoints (Leg B, Phase 4)

**CLAIM:** The four §4 Newton-polygon reduction propositions (E5–E8) are proved
as conditional Lean theorems from explicitly named premise structures, and
Algorithm PossibleStartingPoints (E9) is implemented in Lean with its output
on `(l,a,b) = (1,8,3)` proved by kernel `decide`. Every decidable arithmetic
step in the paper's §4 proofs (sieve tables, k-determinations, φ-maps on
vertex lists, Jacobian-factor pairs, Cor 7.4 numeric data, the (7,21)
ℓ-normalisation) is proved KERNEL (no premises). The cited external steps
are carried as named fields, never smuggled into a kernel claim.
**STATUS:** PROVED (conditional, per-item — see the verdict table at the end
of this file) — VERIFIED on lean-build-3, Lean 4.34.0, 2026-11-06: FULL run
exit 0 (7 s), axioms as listed in the verdict table (all permitted-triple
subsets, no `sorryAx`); second-tool Python recomputation ALL PASS (see
`check_s4_second_tool.py`, run on lean-build-3, Python 3.11.2, exit 0).

## Sources (all read before writing)

- Paper text: `~/workspace/research/rss-monitor/tex/2204.14178/main.tex`,
  §4 lines 457–1398 (Prop 4.1 TeX 463–469, proof 470–666; Prop 4.2 TeX 668–680,
  proof 681–997; Prop 4.3 TeX 1000–1007, proof 1008–1311; Prop 4.4 TeX 1313–1319,
  proof 1387–1396; Algorithm TeX 698–727).
- Statement inventory: `~/workspace/goals/gghv-dependency-closure/hidden_files/phase4/gghv_statement_inventory.md`,
  entries E5–E9 (authoritative for what is open per item).
- Phase 1 baseline (cited, not re-derived): `d1_cor74_2026-11-05.lean`
  (`Cor74Data`, `cor74_prop42`, `cor74_prop43`, `cor74_721`, `ell721_normalization`,
  `cor74_F_conditional`/`cor74_F1_conditional`),
  `d1_esquina1_2026-11-05.lean` (`esquina_item1`),
  `d1_esquina2_2026-11-05.lean` (`esquina_item2`, `esquina_item2_k1`),
  `d1_assembly_2026-11-05.lean` (premise-structure pattern: `MinimalPremises`,
  link hypotheses over abstract predicates),
  `composition_2026-11-04.lean` (`branch_c_eliminated`) and
  `bridge_attempt_2026_11_04.lean` (`challenge_target`).
- Retrieval leg (closed 2026-11-06, `hidden_files/phase4/retrieval/retrieval_log.md`):
  published [GGV1] §7 text NOT FOUND (routes T1-R1–R15 exhausted); Joseph Lemma 2.2
  NOT FOUND (routes T2-R1–R12 exhausted). So hybrid-vs-slip stays carried.

## Formalisation level (read this before judging a verdict)

The paper's §4 arguments are about Laurent polynomials `P, Q ∈ L^{(1)}`, their
Newton polygons, directions, and automorphisms `φ`. There is NO Laurent-polynomial
/ Newton-polygon library in this workspace (the D2 polynomial layer, R14, is Leg E
work; the Laurent-series library is INTERFACE). Following Phase 1's established
style (`d1_assembly`, `d1_cor74`), this file formalises §4 at **vertex-list level**:
a Newton polygon is a `List (Int × Int)` of its vertices; `φ₁` (swap) and the
final morphisms `φ(x) = x⁻¹, φ(y) = x^c·y` are explicit point maps (`swapPt`,
`phiPow`); a shear `φ₂/φ₃` cutting one corner is the explicit `cutPt` map.
The **identification** of a model map with the paper's automorphism — i.e. that
`φ₂` really cuts exactly the stated corner, which is where Cor 7.4's edge form
enters — is NOT proved here; it is carried as a named premise field (an equality
about an opaque intermediate list). What IS proved kernel is: (a) the model maps
compute the paper's stated lists from the initial corners (`swap_927`,
`cut_927`, …); (b) all the paper's decidable arithmetic (sieve, k, φ-images,
Jacobian factors, Cor 7.4 data, algorithm output); (c) the assembly of the
final vertex lists + Jacobian-factor pair from the premise fields via (a)–(b).
So each `prop4X_conditional` is a genuine conditional theorem: its hypotheses
are exactly the paper's cited steps, and its proof does the paper's arithmetic.
Nothing here claims the polynomial-level propositions unconditionally.

## Per-item verdicts (to be confirmed by the VM run; see the table at the end)

- E5 Prop 4.1 (9,27): CONDITIONAL (`prop41_conditional` on `Prop41Premises`:
  Cor 7.4 edge step, φ₃ edge step, Prop 8.2 applied instance). Kernel: sieve
  table, k = 1, direction (−3,8), st values, φ-map, bracket factor (−1,1).
- E6 Prop 4.2 (9,24): CONDITIONAL (`prop42_conditional` on `Prop42Premises`:
  [GGV2] Prop 3.12 soundness link, [vdE] Prop 10.2.6 elimination link,
  hybrid-vs-slip, Prop 8.2-free). Kernel: Cor 7.4 (24,9) data, algorithm output
  + directions, R³ multiplicity count, three sub-case φ-maps, factor (−1,1).
- E7 Prop 4.3 (8,28): CONDITIONAL (`prop43_conditional` on `Prop43Premises`:
  [GGV2] Prop 3.12 setting, [GGV6] Prop 2.5 applied instance, hybrid-vs-slip,
  k = 2 exclusion). Kernel: Cor 7.4 (28,8) data, k ∈ {1,2}, (−2,7) face checks,
  (1,−3)-face check, three sub-case φ-maps, factor (−1,2). The case-split
  ELIMINATION is NOT redone: cases (a)/(b) by branches-(a),(b) `main_theorem`,
  case (c) by `branch_c_eliminated` — both kernel, permitted triple (Phase 1 /
  Step 1, commit 7e4db07f); cited narrowly in the header of §E7 below.
- E8 Prop 4.4 (7,21): CONDITIONAL (`prop44_conditional` on `Prop44Premises`:
  Cor 7.4 (q = 7) φ₂-cut link only). Kernel: the (7,21) Cor74Data bundle
  (re-pinned here self-contained; NOTE — the inventory's "still to add (i)"
  is STALE: `d1_cor74` already defines `cor74_721` + `ell721_normalization`),
  the ℓ-normalisation (support level, copied with attribution from `d1_cor74`),
  swap/cut/φ₃ maps, scalings ×2/×3, factor (−1,1). The paper's ℓ-formula is
  NOT copied literally: the correct face is `λ_p·x¹⁴·R¹⁴` (see `ell721_normalization`).
- E9 Algorithm: KERNEL implementation + output (`psp_183`, `psp_183_dirs`);
  its CORRECTNESS (that Pred_P(1,0) is among the output directions) is
  [GGV2] Prop 3.12 — carried as the `pred_sound` field of `Prop42Premises`
  (Leg F), NOT claimed here.

## Paper slips / corrections carried (not copied)

- E5: the paper states `m, n ∈ ℕ` but the esquina(2) step needs `m, n > 1`
  (Phase 1 finding, `CORRESPONDENCE.md`); `hmn` (m ≠ n) is unused.
- E6: the paper writes "`P ∈ kK[x,y]`" (TeX ~line 730, as printed); read as `K[x,y]`.
- E6/E7: [GGV2] Prop 3.12 numbers are `s = ϑ = 6`, `N₁ = 6`, `N₂ = 3` (integers),
  NOT 5/3, 3/2 (Phase 1 correction, `CORRESPONDENCE.md`).
- E7: Part 19's (8,28) exponents `4·2 = 8` are WRONG — `(m,n) = (3,2)`, so `4·3 = 12`.
- E8: the (7,21) ℓ-formula strips an `x¹⁴` factor (see above).
-/


/-! ## §0. Point arithmetic: the vertex-list model. -/

/-- A Newton-polygon vertex: an exponent pair `(a, b)` for `x^a y^b`. -/
abbrev Pt := Int × Int

/-- Cross product (2D determinant): `crossProd a b = a₁b₂ − a₂b₁`. -/
def crossProd (a b : Pt) : Int := a.1 * b.2 - a.2 * b.1

/-- Weighted valuation `dirVal ρ σ a b = ρa + σb` (Phase 1, verbatim). -/
def dirVal (ρ σ : Int) (a b : Int) : Int := ρ * a + σ * b

/-- Coordinate swap on a vertex: the effect of `φ₁(x) = y, φ₁(y) = x`. -/
def swapPt (p : Pt) : Pt := (p.2, p.1)

/-- The final morphism `φ(x) = x⁻¹, φ(y) = x^c·y` on a vertex:
    `x^a y^b ↦ x^{cb−a} y^b`. It is an involution. -/
def phiPow (c : Int) (p : Pt) : Pt := (c * p.2 - p.1, p.2)

/-- A shear cutting one corner: replace vertex `old` by `new`, leave the rest.
    This MODELS the paper's `φ₂`/`φ₃` steps (`y ↦ y + α x^{-k}`); the claim
    that the paper's shear acts as this cut is carried as a premise (see §E5–E8),
    while the computation `cutPt`-applied-to-explicit-lists is kernel. -/
def cutPt (old new : Pt) (p : Pt) : Pt := if p = old then new else p

/-- Scaling a vertex list by `k` (the `(m,n)`-multiplication of the paper's
    "corners multiplied by `(m,n)` respectively"). -/
def scalePt (k : Int) (p : Pt) : Pt := (k * p.1, k * p.2)

/-- Monomial Jacobian determinant of the exponent pairs `e₁, e₂`:
    `[x^{e₁}, x^{e₂}]` has coefficient `det(e₁,e₂)`. -/
def monJac (e₁ e₂ : Pt) : Int := e₁.1 * e₂.2 - e₁.2 * e₂.1

/-- The Jacobian-factor pair of the final morphism `φ(x) = x⁻¹, φ(y) = x^c·y`:
    `(det, x-exponent)`, so `[φ(x), φ(y)] = det · x^{c−2}` as a monomial.
    E5/E6/E8: `c = 3` gives `(−1, 1)`, i.e. `[φ(x),φ(y)] = −x`;
    E7: `c = 4` gives `(−1, 2)`, i.e. `[φ(x),φ(y)] = −x²`. The chain rule
    identifying `[φ(P),φ(Q)]` with `φ([P,Q])·[φ(x),φ(y)]` is R14 (Leg E);
    this pair is its numeric content, computed kernel here. -/
def phiJacPair (c : Int) : Pt := (monJac (-1, 0) (c, 1), c - 2)

theorem phiPow_involutive (c : Int) (p : Pt) : phiPow c (phiPow c p) = p := by
  obtain ⟨a, b⟩ := p
  rw [Prod.ext_iff]
  constructor
  · show c * b - (c * b - a) = a
    ring
  · rfl

theorem swapPt_involutive (p : Pt) : swapPt (swapPt p) = p := by
  obtain ⟨a, b⟩ := p
  rfl

theorem phiJacPair_3 : phiJacPair 3 = (-1, 1) := by decide

theorem phiJacPair_4 : phiJacPair 4 = (-1, 2) := by decide

/-- Cor 7.4 scaling relation (Phase 1 `d1_cor74`, verbatim): `enF = (p/q)·ab`. -/
def scaling (p q : Int) (enF ab : Pt) : Prop :=
  q * enF.1 = p * ab.1 ∧ q * enF.2 = p * ab.2

/-- Cor 7.4 instance data (Phase 1 `d1_cor74` `Cor74Data`, verbatim shape). -/
structure Cor74Data where
  dir : Pt
  ab : Pt
  p : Int
  q : Int
  hcop : Nat.gcd p.natAbs q.natAbs = 1
  enF : Pt
  hscale : scaling p q enF ab


/-! ## §E5. Proposition 4.1, case (9,27) — kernel arithmetic. -/

/-- The (9,27) base corners (TeX 470): `{(0,0),(1,0),(9,24),(9,27),(0,9)}`,
    multiplied by `(m,n) = (2,3)` respectively for `P` and `Q`. -/
def base927 : List Pt := [(0, 0), (1, 0), (9, 24), (9, 27), (0, 9)]

theorem scale2_base927 :
    base927.map (scalePt 2) = [(0, 0), (2, 0), (18, 48), (18, 54), (0, 18)] := by
  decide

theorem scale3_base927 :
    base927.map (scalePt 3) = [(0, 0), (3, 0), (27, 72), (27, 81), (0, 27)] := by
  decide

/-- `φ₁` (swap) on the base corners (kernel check of TeX 470–471). -/
theorem swap_927 :
    base927.map swapPt = [(0, 0), (0, 1), (24, 9), (27, 9), (9, 0)] := by
  decide

/-- `φ₂` cuts the `(9,0)` corner to `(−2,0)` (TeX 471: the edge
    `{(9,27),(0,9)}` is `y^9 (x y^2 − α₁)^9` by Cor 7.4, so `φ₂(y) = y + α₁x⁻²`
    cuts it). Kernel computation on the model; the identification
    model = `φ₂` is the `afterPhi2_eq` premise field below. -/
theorem cut_927 :
    (base927.map swapPt).map (cutPt (9, 0) (-2, 0)) =
      [(0, 0), (0, 1), (24, 9), (27, 9), (-2, 0)] := by
  decide

/-- `φ₃` cuts the `(0,1)` corner to `(21,8)` (TeX ~line 560: the edge
    `{(24,9),(0,1)}` is `y (y x^3 − α₂)^8`, so `φ₃(y) = y + α₂x⁻³` reduces it
    to `{(24,9),(21,8)}`). Kernel computation on the model, in the paper's
    listing order `{(0,0),(27,9),(24,9),(0,1),(−2,0)}` (a set, not a list). -/
theorem cut3_927 :
    ([(0, 0), (27, 9), (24, 9), (0, 1), (-2, 0)] : List Pt).map (cutPt (0, 1) (21, 8)) =
      [(0, 0), (27, 9), (24, 9), (21, 8), (-2, 0)] := by
  decide

/-- `cut_927`'s output and the paper's listing are the same SET (the paper
    lists corners as sets; the model map preserves the swap order). -/
theorem cut_927_set (e : Pt) :
    e ∈ [(0, 0), (0, 1), (24, 9), (27, 9), (-2, 0)] ↔
    e ∈ [(0, 0), (27, 9), (24, 9), (0, 1), (-2, 0)] := by
  simp only [List.mem_cons, List.mem_nil_iff]
  tauto

/-- The (9,27) Cor 7.4 F-instance (Phase 1 `d1_cor74` `cor74_927`, re-pinned):
    direction `(2,−1)`, `(a/l,b) = (9,27)`, `en(F) = (1,3) = (1/9)(9,27)`, `q = 9`. -/
def cor74_927_s4 : Cor74Data where
  dir := (2, -1)
  ab := (9, 27)
  p := 1
  q := 9
  hcop := by decide
  enF := (1, 3)
  hscale := by refine ⟨?_, ?_⟩ <;> decide

theorem cor74_927_s4_cond3 : cor74_927_s4.ab.2 > cor74_927_s4.ab.1 := by decide

theorem cor74_927_s4_exp_P : 9 * 2 = 18 := by decide

theorem cor74_927_s4_exp_Q : 9 * 3 = 27 := by decide

/-! ### E5 sieve (TeX ~lines 570–600).

The paper: with `(ρ₂,σ₂) = min{Succ_P(−1,3), Succ_Q(−1,3)}`, if
`en_{ρ₂,σ₂}(P) ∼ en_{ρ₂,σ₂}(Q)` then
`(a',b') = (1/2) en(P) = (1/3) en(Q)` is one of
`{(−2,0),(−1,0),(1,1),(2,1),(4,2),(5,2),(7,3),(10,4),(13,5)}`.
The corner of `F` other than `(1,1)` is
`(1,1) + c(21−a',8−b')/gcd(21−a',8−b')` for some `c > 0`, and computing
`v_{−8,21}` gives `13·gcd(21−a',8−b') + c(8a' − 21b') = 0`, hence
`21b' − 8a' ∣ 13·gcd(21−a',8−b')`. Only `(5,2)` and `(13,5)` survive
(`(1,1)` is excluded separately: `(a',b')` cannot lie on the diagonal). -/

/-- The sieve divisibility condition, Bool-valued for `List.filter`. -/
def sieveOkB (a' b' : Int) : Bool :=
  decide ((21 * b' - 8 * a') ∣ 13 * (Int.gcd (21 - a') (8 - b') : Int))

theorem sieveOkB_iff (a' b' : Int) :
    sieveOkB a' b' = true ↔ (21 * b' - 8 * a') ∣ 13 * (Int.gcd (21 - a') (8 - b') : Int) := by
  simp only [sieveOkB, decide_eq_true_eq]

/-- The nine candidate points from the paper. -/
def sieveCandidates927 : List Pt :=
  [(-2, 0), (-1, 0), (1, 1), (2, 1), (4, 2), (5, 2), (7, 3), (10, 4), (13, 5)]

/-- The paper's sieve table, recomputed (TeX ~line 595):
    `(−2,0) → 16 ∤ 13`; `(−1,0) → 8 ∤ 26`; `(2,1) → 5 ∤ 13`;
    `(4,2) → 10 ∤ 13`; `(5,2) → 2 ∣ 26`; `(7,3) → 7 ∤ 13`;
    `(10,4) → 4 ∤ 13`; `(13,5) → 1 ∣ 13`. Only `(5,2)`, `(13,5)` survive.
    Note `(1,1)` is IN the filtered list below only if it passed — it does
    pass the divisibility (`13 ∣ 13`), so the table below EXCLUDES it by
    hand, exactly as the paper does (diagonal argument, not the sieve);
    see `sieve_diag_passes`. -/
theorem sieve_table_927 :
    (sieveCandidates927.filter fun p => sieveOkB p.1 p.2) =
      [(1, 1), (5, 2), (13, 5)] := by
  decide

/-- `(1,1)` passes the divisibility condition — the paper excludes it by the
    diagonal argument ("`(a',b')` cannot lie on the diagonal"), not by the sieve.
    Recorded so the sieve verdict is not overstated. -/
theorem sieve_diag_passes : sieveOkB 1 1 = true := by decide

theorem sieve_diag_value : (21 * (1 : Int) - 8 * 1) = 13 ∧
    13 * (Int.gcd (21 - 1) (8 - 1) : Int) = 13 := by decide

/-- The `v_{−8,21}` derivation (TeX ~line 585): from
    `13·g + c·(8a' − 21b') = 0` the divisibility `21b' − 8a' ∣ 13·g` follows.
    Pure integer arithmetic, kernel. -/
theorem sieve_derivation (a' b' c g : Int)
    (h : 13 * g + c * (8 * a' - 21 * b') = 0) :
    (21 * b' - 8 * a') ∣ 13 * g := by
  refine ⟨c, ?_⟩
  linear_combination h

/-- The eight non-diagonal rows of the paper's table, one by one (kernel). -/
theorem sieve_rows_927 :
    (¬ (16 : Int) ∣ 13) ∧ (¬ (8 : Int) ∣ 26) ∧ (¬ (5 : Int) ∣ 13) ∧
    (¬ (10 : Int) ∣ 13) ∧ ((2 : Int) ∣ 26) ∧ (¬ (7 : Int) ∣ 13) ∧
    (¬ (4 : Int) ∣ 13) ∧ ((1 : Int) ∣ 13) := by
  decide

/-! ### E5 esquina / k = 1 / direction (−3,8) (TeX ~lines 600–640).

Prop 8.2 gives `k ∈ ℕ` with `(k+1)b < a` and
`{en(P), en(Q)} = {(−k,0), (k+1,1)}` for `(a,b)` one of
`{(21,8), (13,5), (5,2)}`. In all cases `k = 1`, so the ends are
`{(−1,0), (2,1)}` with direction `(ρ,σ) = (−3,8)`. -/

/-- `k = 1` from the three inequalities + `k ≥ 1` (the `(5,2)` row forces it:
    `(k+1)·2 < 5` gives `k ≤ 1`). Kernel, by `omega`. -/
theorem esquina_k1_927 (k : ℕ) (hk1 : 1 ≤ k)
    (h21 : (k + 1) * 8 < 21) (_h13 : (k + 1) * 5 < 13) (_h5 : (k + 1) * 2 < 5) :
    k = 1 := by
  omega

/-- The `k ∈ {1,2}`-style bound for the `(21,8)` row alone (used in E7's form). -/
theorem esquina_k12_218 (k : ℕ) (hk1 : 1 ≤ k) (h21 : (k + 1) * 8 < 21) :
    k = 1 ∨ k = 2 := by
  omega

/-- `st_{−3,8}(P) = (42,16) = 2·(21,8)` and `st_{−3,8}(Q) = (63,24) = 3·(21,8)`. -/
theorem st_927 : (2 * (21 : Int), 2 * 8) = (42, 16) ∧ (3 * 21, 3 * 8) = (63, 24) := by
  decide

/-- `dirVal (−3,8)` is constant on the two esquina edges:
    `(42,16)–(2,1)` for `P` (value 2) and `(63,24)–(−1,0)` for `Q` (value 3),
    so `(−3,8)` is the face direction of both. -/
theorem dir_38_927 :
    dirVal (-3) 8 42 16 = dirVal (-3) 8 2 1 ∧
    dirVal (-3) 8 63 24 = dirVal (-3) 8 (-1) 0 := by
  decide

/-- `(-3,8) × ((42,16) − (−1,0)) ≠ 0` (TeX ~line 640, "in fact … ≠ 0"). -/
theorem cross_38_927 : crossProd (-3, 8) ((42, 16) - (-1, 0)) ≠ 0 := by
  decide

/-- The final morphism `φ(x) = x⁻¹, φ(y) = x³y` on the pre-φ polygons
    (TeX ~lines 650–666). Pre-φ `P` vertices `(0,0),(2,1),(42,16),(48,18),(54,18)`
    (i.e. `(0,0)`, `en = (2,1)`, `st = (42,16)`, `2·(24,9)`, `2·(27,9)`);
    pre-φ `Q` vertices `(0,0),(−1,0),(63,24),(72,27),(81,27)`. -/
theorem phi3_927P :
    ([(0, 0), (2, 1), (42, 16), (48, 18), (54, 18)] : List Pt).map (phiPow 3) =
      [(0, 0), (1, 1), (6, 16), (6, 18), (0, 18)] := by
  decide

theorem phi3_927Q :
    ([(0, 0), (-1, 0), (63, 24), (72, 27), (81, 27)] : List Pt).map (phiPow 3) =
      [(0, 0), (1, 0), (9, 24), (9, 27), (0, 27)] := by
  decide

/-! ### E5 conditional theorem.

Premise fields (each = one cited step of the paper's proof, stated about the
opaque intermediate lists):
- `afterPhi2_eq`: Cor 7.4 edge form + `φ₁, φ₂` — the post-`φ₁∘φ₂` base polygon
  is `{(0,0),(27,9),(24,9),(0,1),(−2,0)}`.
- `afterPhi3_eq`: the `{(24,9),(0,1)}` edge form + `φ₃` — the post-`φ₃` base
  polygon is `{(0,0),(27,9),(24,9),(21,8),(−2,0)}`.
- `k` + inequalities + ends + `st`/`dir`: [GGV1] Prop 8.2 applied (kernel in
  Phase 1: `d1_esquina1`/`d1_esquina2`; restated here as the applied instance),
  plus the paper's `st`/`dir` computation.
The `phi3_of_phi2_927` and `pre927_top` link lemmas relate the opaque fields
through the kernel model maps; the main theorem assembles them. -/

structure Prop41Premises where
  afterPhi2 : List Pt
  afterPhi2_eq : afterPhi2 = [(0, 0), (27, 9), (24, 9), (0, 1), (-2, 0)]
  afterPhi3 : List Pt
  afterPhi3_eq : afterPhi3 = [(0, 0), (27, 9), (24, 9), (21, 8), (-2, 0)]
  k : ℕ
  k_ge1 : 1 ≤ k
  k_ineq21 : (k + 1) * 8 < 21
  k_ineq13 : (k + 1) * 5 < 13
  k_ineq5 : (k + 1) * 2 < 5
  enP : Pt
  enP_eq : enP = ((k + 1 : ℤ), 1)
  enQ : Pt
  enQ_eq : enQ = (-(k : ℤ), 0)
  stP : Pt
  stP_eq : stP = (42, 16)
  stQ : Pt
  stQ_eq : stQ = (63, 24)
  dirE : Pt
  dirE_eq : dirE = (-3, 8)

/-- The `φ₃` step as a relation between the two opaque lists (kernel cut). -/
theorem phi3_of_phi2_927 (h : Prop41Premises) :
    h.afterPhi3 = h.afterPhi2.map (cutPt (0, 1) (21, 8)) := by
  rw [h.afterPhi3_eq, h.afterPhi2_eq]
  decide

/-- The top edge of the post-`φ₃` polygon, scaled for `P`/`Q`, contains the
    pre-`φ` vertices `(48,18) = 2·(24,9)`, `(54,18) = 2·(27,9)` (resp.
    `(72,27) = 3·(24,9)`, `(81,27) = 3·(27,9)`). -/
theorem pre927_top (h : Prop41Premises) :
    (48, 18) ∈ h.afterPhi3.map (scalePt 2) ∧ (54, 18) ∈ h.afterPhi3.map (scalePt 2) ∧
    (72, 27) ∈ h.afterPhi3.map (scalePt 3) ∧ (81, 27) ∈ h.afterPhi3.map (scalePt 3) := by
  rw [h.afterPhi3_eq]
  decide

/-- The pre-`φ` polygons assembled from the premise fields. -/
def preP927 (h : Prop41Premises) : List Pt := [(0, 0), h.enP, h.stP, (48, 18), (54, 18)]

def preQ927 (h : Prop41Premises) : List Pt := [(0, 0), h.enQ, h.stQ, (72, 27), (81, 27)]

/-- Proposition 4.1 (E5), CONDITIONAL: from the premise structure, the final
    vertex lists are exactly the paper's, and the Jacobian-factor pair is
    `(−1, 1)` (so `[φ(P),φ(Q)] = −[P,Q]·x`, and with `[P,Q] = −1` after the
    swap this is `x` up to the paper's rescaling). The polynomial-level
    statement ("there exist `P, Q ∈ L^{(1)}` with `[P,Q] = x`") is NOT claimed:
    it needs the Laurent layer (R14/INTERFACE). -/
theorem prop41_conditional (h : Prop41Premises) :
    ∃ finalP finalQ : List Pt,
      finalP = (preP927 h).map (phiPow 3) ∧
      finalQ = (preQ927 h).map (phiPow 3) ∧
      finalP = [(0, 0), (1, 1), (6, 16), (6, 18), (0, 18)] ∧
      finalQ = [(0, 0), (1, 0), (9, 24), (9, 27), (0, 27)] ∧
      phiJacPair 3 = (-1, 1) := by
  have hk : h.k = 1 := esquina_k1_927 h.k h.k_ge1 h.k_ineq21 h.k_ineq13 h.k_ineq5
  have henP : h.enP = (2, 1) := by rw [h.enP_eq, hk]; decide
  have henQ : h.enQ = (-1, 0) := by rw [h.enQ_eq, hk]; decide
  have _hphi3 := phi3_of_phi2_927 h
  have _htop := pre927_top h
  refine ⟨(preP927 h).map (phiPow 3), (preQ927 h).map (phiPow 3), rfl, rfl, ?_, ?_, ?_⟩
  · show ([(0, 0), h.enP, h.stP, (48, 18), (54, 18)] : List Pt).map (phiPow 3) =
      [(0, 0), (1, 1), (6, 16), (6, 18), (0, 18)]
    rw [henP, h.stP_eq]
    exact phi3_927P
  · show ([(0, 0), h.enQ, h.stQ, (72, 27), (81, 27)] : List Pt).map (phiPow 3) =
      [(0, 0), (1, 0), (9, 24), (9, 27), (0, 27)]
    rw [henQ, h.stQ_eq]
    exact phi3_927Q
  · exact phiJacPair_3


/-! ## §E9. Algorithm PossibleStartingPoints (TeX 698–727).

Input: a corner `(a/l, b) ∈ (1/l)ℕ × ℕ`. Output: the list of points `(c/l, d)`
such that equation (condicion) `[R,G] = R^i` (TeX 691) is satisfied.
Procedure (paper): for `d = 0` to `b−1`, for `c = ⌊d·a/b⌋+1` to `ld+a−bl−1`:
`N₁ = gcd(a−c, b−d)`; `N₂ = gcd(c, d)`; `(ρ,σ) = dir((a/l,b)−(c/l,d))`;
`s = (ρa+σlb)/gcd(ρa+σlb, l(ρ+σ))`; include `(c/l,d)` iff
(`s ∣ N₂` and `d > 0`) or `s ≤ N₁`.

Formalisation notes:
- `dir((a/l,b)−(c/l,d))` is the primitive direction *perpendicular* to the
  difference: `(ρ,σ)` with `ρ(a−c) + σ(b−d) = 0`, normalised to `ρ > 0`.
  For `Δ = (u,v)` with `u,v > 0` that is `(v/g, −u/g)` with `g = gcd(u,v)`
  (`dirPerp` below). Check against the paper's conclusion: the included
  points' directions must be `{(1,−2),(2,−5)}` — verified in `psp_183_dirs`.
- `s` is computed over `ℤ` with `Int.natAbs` (the paper's numerator is positive
  in every case that occurs here; the `natAbs` form is the literal
  `gcd`-quotient for positive numerators).
- The candidate count for `(c,d)` is `(ld+a−bl−1) − (⌊d·a/b⌋+1) + 1`
  (Nat subtraction; exact here since the upper bound exceeds the lower in all
  three `d`-rows for `(1,8,3)`).
- CORRECTNESS is NOT proved here: that the output directions contain
  `Pred_P(1,0)` is [GGV2] Prop 3.12 (Leg F, proof-OPEN). It is carried as the
  `pred_sound` field of `Prop42Premises` below. -/

/-- Primitive perpendicular direction of `Δ = (u,v)`, `u,v > 0`, normalised
    to first component positive: `(v/g, −u/g)`, `g = gcd(u,v)`. -/
def dirPerp (u v : ℕ) : Pt :=
  (((v / Nat.gcd u v : ℕ) : Int), -((u / Nat.gcd u v : ℕ) : Int))

/-- The paper's `s = (ρa+σlb)/gcd(ρa+σlb, l(ρ+σ))`, as a natural number
    (positive-numerator form). -/
def pspS (l a b : ℕ) (ρ σ : Int) : ℕ :=
  (ρ * (a : Int) + σ * ((l : Int) * (b : Int))).natAbs /
    Nat.gcd (ρ * (a : Int) + σ * ((l : Int) * (b : Int))).natAbs
      (((l : Int) * (ρ + σ)).natAbs)

/-- Inclusion test for one candidate `(c,d)` (Bool-valued for `List.filter`). -/
def pspInclude (l a b : ℕ) (p : ℕ × ℕ) : Bool :=
  let c := p.1
  let d := p.2
  let n1 := Nat.gcd (a - c) (b - d)
  let n2 := Nat.gcd c d
  let dir := dirPerp (a - c) (b - d)
  let s := pspS l a b dir.1 dir.2
  (decide (s ∣ n2) && decide (0 < d)) || decide (s ≤ n1)

/-- All candidates `(c,d)` for the paper's double loop. -/
def pspCandidates (l a b : ℕ) : List (ℕ × ℕ) :=
  (List.range b).flatMap fun d =>
    (List.range (l * d + a - b * l - d * a / b - 1)).map
      fun k => (d * a / b + 1 + k, d)

/-- Algorithm PossibleStartingPoints (E9), as a Lean function. -/
def possibleStartingPoints (l a b : ℕ) : List (ℕ × ℕ) :=
  (pspCandidates l a b).filter (pspInclude l a b)

/-- The paper's application (TeX 694): `(l,a,b) = (1,8,3)`. Candidates in
    loop order: `d=0: (1,0),(2,0),(3,0),(4,0)`; `d=1: (3,1),(4,1),(5,1)`;
    `d=2: (6,2)`. Included: `(2,0)` (`s=2 ≤ N₁=3`), `(3,1)` (`s=1 ≤ N₁=1`),
    `(4,1)` (`s=2 ≤ N₁=2`), `(6,2)` (`s=2 ∣ N₂=2`, `d>0`). Excluded:
    `(1,0)` (`s=3`, `N₁=1`, `3∤1`), `(3,0)` (`s=9`, `N₁=1`),
    `(4,0)` (`s=12`, `N₁=1`), `(5,1)` (`s=7`, `N₁=1`, `7∤1`). -/
theorem psp_183 : possibleStartingPoints 1 8 3 = [(2, 0), (3, 1), (4, 1), (6, 2)] := by
  decide

theorem psp_183_candidates : pspCandidates 1 8 3 =
    [(1, 0), (2, 0), (3, 0), (4, 0), (3, 1), (4, 1), (5, 1), (6, 2)] := by
  decide

/-- The directions of the output points are exactly `{(1,−2),(2,−5)}`
    (TeX 694: "shows that `Pred_P(1,0) ∈ {(1,−2),(2,−5)}`"). -/
theorem psp_183_dirs :
    (possibleStartingPoints 1 8 3).map (fun p => dirPerp (8 - p.1) (3 - p.2)) =
      [(1, -2), (2, -5), (1, -2), (1, -2)] := by
  decide

theorem psp_183_dirs_subset (d : Pt) :
    d ∈ (possibleStartingPoints 1 8 3).map (fun p => dirPerp (8 - p.1) (3 - p.2)) →
    d = (1, -2) ∨ d = (2, -5) := by
  rw [psp_183_dirs]
  simp only [List.mem_cons, List.mem_nil_iff]
  tauto

theorem psp_183_mem_31 : (3, 1) ∈ possibleStartingPoints 1 8 3 := by
  rw [psp_183]
  decide

/- The second application in the paper (TeX ~line 850): the algorithm with
    the same parameters shows `st_{ρ,σ}(φ₂(P)) ∈ 3m{(0,0),(3,1)}`; the `(3,1)`
    member is an algorithm output (kernel, above). The `(0,0)` member is the
    "edge completely cut" case, carried in the `aprime_mem` field below. -/


/-! ## §E6. Proposition 4.2, case (9,24) — kernel arithmetic. -/

/-- The (9,24) base corners (TeX 681): `{(0,0),(1,0),(9,24),(0,6)}`,
    multiplied by `(m,n) = (2,3)`. -/
def base924 : List Pt := [(0, 0), (1, 0), (9, 24), (0, 6)]

theorem swap_924 :
    base924.map swapPt = [(0, 0), (0, 1), (24, 9), (6, 0)] := by
  decide

/-- The Prop 4.2 Cor 7.4 instance (Phase 1 `d1_cor74` `cor74_prop42`, re-pinned):
    `(ρ₀,σ₀) = (−1,3)`, `(a/l,b) = (24,9)`, `en_{−1,3}(F) = (16,6) = (2/3)(24,9)`,
    so `q = 3`. MIXED slot (see header): F's condition (3) FAILS (`b < a/l`)
    while F1's HOLDS — the hybrid-vs-slip question, carried as a premise
    field (`hybrid_slip`) below, retrieval NOT FOUND. -/
def cor74_prop42_s4 : Cor74Data where
  dir := (-1, 3)
  ab := (24, 9)
  p := 2
  q := 3
  hcop := by decide
  enF := (16, 6)
  hscale := by refine ⟨?_, ?_⟩ <;> decide

theorem cor74_prop42_s4_cond3_fails : ¬ (cor74_prop42_s4.ab.2 > cor74_prop42_s4.ab.1) := by
  decide

theorem cor74_prop42_s4_cond3_F1 : cor74_prop42_s4.ab.2 < cor74_prop42_s4.ab.1 := by
  decide

theorem cor74_prop42_s4_exp : 3 * 2 = 6 := by decide

/-- `ℓ_{ρ,σ}(P) = λR^{3m}` with `en(R) = (8,3)`: `R^6` has endpoints
    `6·(2,0) = (12,0)` and `6·(8,3) = (48,18)` (Phase 1 `cor74_prop42_R`). -/
theorem cor74_prop42_s4_R :
    (6 * 2, 6 * 0) = (12, 0) ∧ (6 * 8, 6 * 3) = (48, 18) := by decide

theorem cor74_prop42_s4_cross : 0 < crossProd (1, -2) ((48, 18) - (12, 0)) := by
  decide

/-- [GGV2] Prop 3.12 numbers for the (9,24) application (TeX ~line 800):
    `s = ϑ = 6`, `N₁ = 6`, `N₂ = 3` (integers — NOT 5/3, 3/2). -/
theorem prop312_nums_924 : (6 : ℕ) = 6 ∧ (6 : ℕ) = 6 ∧ (3 : ℕ) = 3 := by decide

/-- The multiplicity count eliminating the three-factor case (TeX ~line 800):
    if `R` has three DISTINCT linear factors (multiplicities `[1,1,1]`), then
    `R^3` has multiplicities `[3,3,3]`, and no factor has multiplicity `6`.
    The existence of a factor of multiplicity `s = ϑ = 6` is [GGV2]
    Prop 3.12(2) — carried as the `r3mults`/`h312_2` fields below. -/
theorem r3_mults_924 : ([1, 1, 1] : List ℕ).map (· * 3) = [3, 3, 3] ∧
    (6 : ℕ) ∉ ([3, 3, 3] : List ℕ) := by
  decide

/-- The `φ₂` corners in the two-factor case (TeX ~line 810):
    `{(0,0),(18,6),(24,9),(0,1),(−2,0)}` (base, ×(2,3)). The `(18,6)` vertex
    is new (from the `R`-factor); the `(6,0)` corner is cut to `(−2,0)`. -/
theorem phi2cut_924 :
    ([(0, 0), (0, 1), (24, 9), (6, 0)] : List Pt).map (cutPt (6, 0) (-2, 0)) =
      [(0, 0), (0, 1), (24, 9), (-2, 0)] := by
  decide

/-- The edge `{(24,9),(0,1)}` transformed "exactly as in the case (9,27)"
    (TeX ~line 820): `φ₃` cuts `(0,1)` to `(21,8)`. Kernel computation. -/
theorem edge924_927 :
    ([(0, 0), (18, 6), (24, 9), (0, 1), (-2, 0)] : List Pt).map (cutPt (0, 1) (21, 8)) =
      [(0, 0), (18, 6), (24, 9), (21, 8), (-2, 0)] := by
  decide

/-- The three final shapes (TeX 668–680), and their pre-`φ` polygons under
    `φ(x) = x⁻¹, φ(y) = x³y` (same final morphism as E5). Pre-`φ` vertices:
    sub-case (1) `P`: `(0,0),(2,1),(42,16),(48,18),(36,12)` — note
    `(36,12) = 2·(18,6)` (the two-factor corner); `Q`: `(0,0),(−1,0),(63,24),
    (72,27),(54,18)` with `(54,18) = 3·(18,6)`.
    Sub-case (2): the `(a',b') = (9,3)` vertex: `(18,6) = 2·(9,3)` for `P`,
    `(27,9) = 3·(9,3)` for `Q`. Sub-case (3): `(a',b') = (0,0)`, no extra vertex. -/
theorem phi_924_sub1P :
    ([(0, 0), (2, 1), (42, 16), (48, 18), (36, 12)] : List Pt).map (phiPow 3) =
      [(0, 0), (1, 1), (6, 16), (6, 18), (0, 12)] := by
  decide

theorem phi_924_sub1Q :
    ([(0, 0), (-1, 0), (63, 24), (72, 27), (54, 18)] : List Pt).map (phiPow 3) =
      [(0, 0), (1, 0), (9, 24), (9, 27), (0, 18)] := by
  decide

theorem phi_924_sub2P :
    ([(0, 0), (2, 1), (42, 16), (48, 18), (18, 6)] : List Pt).map (phiPow 3) =
      [(0, 0), (1, 1), (6, 16), (6, 18), (0, 6)] := by
  decide

theorem phi_924_sub2Q :
    ([(0, 0), (-1, 0), (63, 24), (72, 27), (27, 9)] : List Pt).map (phiPow 3) =
      [(0, 0), (1, 0), (9, 24), (9, 27), (0, 9)] := by
  decide

theorem phi_924_sub3P :
    ([(0, 0), (2, 1), (42, 16), (48, 18)] : List Pt).map (phiPow 3) =
      [(0, 0), (1, 1), (6, 16), (6, 18)] := by
  decide

theorem phi_924_sub3Q :
    ([(0, 0), (-1, 0), (63, 24), (72, 27)] : List Pt).map (phiPow 3) =
      [(0, 0), (1, 0), (9, 24), (9, 27)] := by
  decide

/-- The `(a',b') ∈ {(0,0),(9,3)}` dichotomy, arithmetically: `(9,3)` scales to
    the sub-case (2) extra vertices `(18,6) = 2·(9,3)`, `(27,9) = 3·(9,3)`,
    and `(0,0)` to no extra vertex (sub-case (3)). -/
theorem aprime_924_scale :
    (2 * (9 : Int), 2 * 3) = (18, 6) ∧ (3 * 9, 3 * 3) = (27, 9) := by
  decide

/-! ### E6 conditional theorem.

Premise fields:
- `predP10` + `pred_sound`: [GGV2] Prop 3.12's soundness link — `Pred_P(1,0)`
  is among the algorithm's output directions (the algorithm itself is kernel,
  §E9; its correctness is Leg F). The kernel subset lemma then forces
  `predP10 ∈ {(1,−2),(2,−5)}`.
- `pred_ne_25`: [vdE] Prop 10.2.6 applied twice — `Pred_P(1,0) = (2,−5)` leads
  to `st_{2,−5}(P) = 3m(3,1)`, `Pred_P(2,−5) ≤ (1,−3)`, `deg_x(P(x,0)) ≤ 0`,
  contradicting [vdE] 10.2.6 (and likewise `st_{1,−2}(R) = (6,2)`).
  [vdE] Prop 10.2.6 itself has no Lean leg (Leg F / external).
- `stR12` + `stR12_mem`: `st_{1,−2}(R) ∈ {(2,0),(4,1)}` (paper's conclusion
  after the [vdE] eliminations).
- `rForm` + `rForm_mem`: `R` has 1, 2 or 3 distinct linear factors in `z = x²y`.
- `r3mults` + `h312_2` + `rform3`: [GGV2] Prop 3.12(2) applied — a linear
  factor of `R^3` has multiplicity `s = ϑ = 6`; with `R` three-factor
  (`rForm = 3`) the multiplicities are `[3,3,3]`, contradiction (kernel
  `r3_mults_924`). The `6` is the paper's number, not a model artefact.
- `postPhi2_924` + `postPhi2_924_eq`: the `φ₂` corners in the two-factor case
  (Cor 7.4 + `φ̄`); `edgeTrans924`: the `{(24,9),(0,1)}` edge transformed as
  in (9,27) (carried: the `φ₃` cut on this polygon).
- `aprime` + `aprime_mem`: in the one-factor case, the new preceding edge
  satisfies `(a',b') ∈ {(0,0),(9,3)}` (algorithm + `en F = (2/3)(9,24)`).
- `stR12_ne62`: `λ₁ ≠ 0`, second half (paper's argument: in the two-factor case
  `λ₁ = 0` implies `st_{ρ,σ}(R) = (6,2)`, impossible as above). Stated as a
  hypothesis about the opaque `stR12` (it is `(2,0)` or `(4,1)`, never `(6,2)`).
  The first half (`λ₁ = 0` implies `Pred_P(1,0) = (2,−5)` or `≤ (8,−3)` in the
  one-factor case) is already `pred_ne_25` + the algorithm directions.
- `hybrid_slip`: the hybrid-vs-slip reading for the swapped Cor 7.4 use
  (retrieval NOT FOUND 2026-11-06). The swapped Cor 7.4 conclusion as applied
  is: `R` exists with `en(R) = (8,3)` (kernel arithmetic, `cor74_prop42_s4_R`)
  AND the Cor 7.4 application to the mixed slot is valid. The validity is the
  carried content, so the structure takes it as an explicit `Prop` parameter
  (`HybridSlip924`), and the field `hybrid_slip` is a proof of it: the
  conditional theorem is then explicitly conditional on that named proposition.
  (A field of type `Prop` alone would be data, not a proof — hence the
  parameter + proof-field pattern, the same shape as `d1_assembly`'s abstract
  predicates `CounterexampleAt`/`LPC`.) -/

structure Prop42Premises (HybridSlip924 : Prop) where
  predP10 : Pt
  pred_sound : predP10 ∈
    (possibleStartingPoints 1 8 3).map (fun p => dirPerp (8 - p.1) (3 - p.2))
  pred_ne_25 : predP10 ≠ (2, -5)
  stR12 : Pt
  stR12_mem : stR12 = (2, 0) ∨ stR12 = (4, 1)
  stR12_ne62 : stR12 ≠ (6, 2)
  rForm : ℕ
  rForm_mem : rForm = 1 ∨ rForm = 2 ∨ rForm = 3
  r3mults : List ℕ
  h312_2 : (6 : ℕ) ∈ r3mults
  rform3 : rForm = 3 → r3mults = [3, 3, 3]
  postPhi2_924 : List Pt
  postPhi2_924_eq : postPhi2_924 = [(0, 0), (18, 6), (24, 9), (0, 1), (-2, 0)]
  edgeTrans924 : postPhi2_924.map (cutPt (0, 1) (21, 8)) =
    [(0, 0), (18, 6), (24, 9), (21, 8), (-2, 0)]
  aprime : Pt
  aprime_mem : aprime = (0, 0) ∨ aprime = (9, 3)
  hybrid_slip : HybridSlip924

/-- `Pred_P(1,0) = (1,−2)`: from Prop 3.12 soundness (field) + the kernel
    algorithm directions + the [vdE] elimination of `(2,−5)`. -/
theorem predP10_eq_924 {H : Prop} (h : Prop42Premises H) : h.predP10 = (1, -2) := by
  have hmem := psp_183_dirs_subset h.predP10 h.pred_sound
  rcases hmem with h1 | h2
  · exact h1
  · exact absurd h2 h.pred_ne_25

/-- The three-factor case is impossible (kernel count + Prop 3.12(2) field). -/
theorem rform_ne3_924 {H : Prop} (h : Prop42Premises H) : h.rForm ≠ 3 := by
  intro h3
  have hmul := h.rform3 h3
  have h312 := h.h312_2
  rw [hmul] at h312
  exact (r3_mults_924.2) h312

/-- The pre-`φ` polygons assembled from the premise fields.
    Two-factor case (`rForm = 2`): the `(36,12) = 2·(18,6)` / `(54,18) = 3·(18,6)`
    vertices come from `postPhi2_924` (see `pre924_2_top`); the `(42,16)` /
    `(48,18)` vertices from the edge transformation (see `pre924_2_edge`).
    One-factor case (`rForm = 1`): the extra vertex is `(18,6) = 2·(9,3)` /
    `(27,9) = 3·(9,3)` iff `(a',b') = (9,3)`, else absent. -/
def preP924_2 {H : Prop} (_h : Prop42Premises H) : List Pt :=
  [(0, 0), (2, 1), (42, 16), (48, 18), (36, 12)]

def preQ924_2 {H : Prop} (_h : Prop42Premises H) : List Pt :=
  [(0, 0), (-1, 0), (63, 24), (72, 27), (54, 18)]

def preP924_1 {H : Prop} (h : Prop42Premises H) : List Pt :=
  if h.aprime = (9, 3) then [(0, 0), (2, 1), (42, 16), (48, 18), (18, 6)]
  else [(0, 0), (2, 1), (42, 16), (48, 18)]

def preQ924_1 {H : Prop} (h : Prop42Premises H) : List Pt :=
  if h.aprime = (9, 3) then [(0, 0), (-1, 0), (63, 24), (72, 27), (27, 9)]
  else [(0, 0), (-1, 0), (63, 24), (72, 27)]

/-- The two-factor corner `(18,6)` of `postPhi2_924`, scaled for `P`/`Q`. -/
theorem pre924_2_top {H : Prop} (h : Prop42Premises H) :
    (36, 12) ∈ h.postPhi2_924.map (scalePt 2) ∧
    (54, 18) ∈ h.postPhi2_924.map (scalePt 3) := by
  rw [h.postPhi2_924_eq]
  decide

/-- The edge-transformed vertices `(42,16) = 2·(21,8)`, `(48,18) = 2·(24,9)`
    (and the `Q` analogues) in the edge-transformed, scaled polygon. -/
theorem pre924_2_edge {H : Prop} (h : Prop42Premises H) :
    (42, 16) ∈ (h.postPhi2_924.map (cutPt (0, 1) (21, 8))).map (scalePt 2) ∧
    (48, 18) ∈ (h.postPhi2_924.map (cutPt (0, 1) (21, 8))).map (scalePt 2) := by
  rw [h.edgeTrans924]
  decide

/-- Proposition 4.2 (E6), CONDITIONAL: from the premise structure, one of the
    three final shapes holds, with Jacobian-factor pair `(−1,1)`.
    Sub-case (1) ← `rForm = 2` (two-factor `R`); sub-case (2) ← `rForm = 1`
    with `(a',b') = (9,3)`; sub-case (3) ← `rForm = 1` with `(a',b') = (0,0)`.
    The polynomial-level statement is NOT claimed (Laurent layer, R14). -/
theorem prop42_conditional {H : Prop} (h : Prop42Premises H) :
    ∃ finalP finalQ : List Pt,
      ((finalP = (preP924_2 h).map (phiPow 3) ∧
        finalQ = (preQ924_2 h).map (phiPow 3) ∧
        finalP = [(0, 0), (1, 1), (6, 16), (6, 18), (0, 12)] ∧
        finalQ = [(0, 0), (1, 0), (9, 24), (9, 27), (0, 18)]) ∨
       (finalP = (preP924_1 h).map (phiPow 3) ∧
        finalQ = (preQ924_1 h).map (phiPow 3) ∧
        ((finalP = [(0, 0), (1, 1), (6, 16), (6, 18), (0, 6)] ∧
          finalQ = [(0, 0), (1, 0), (9, 24), (9, 27), (0, 9)]) ∨
         (finalP = [(0, 0), (1, 1), (6, 16), (6, 18)] ∧
          finalQ = [(0, 0), (1, 0), (9, 24), (9, 27)])))) ∧
      phiJacPair 3 = (-1, 1) := by
  have _hst := h.stR12_mem
  have _hne62 := h.stR12_ne62
  have _htop := pre924_2_top h
  have _hedge := pre924_2_edge h
  have _hpred : h.predP10 = (1, -2) := predP10_eq_924 h
  rcases h.rForm_mem with h1 | h2 | h3
  · -- `R = x²(z−λ₁)³`: edge completely cut; `(a',b') ∈ {(0,0),(9,3)}`.
    rcases h.aprime_mem with ha | ha
    · -- `(a',b') = (0,0)` → sub-case (3).
      have hne : h.aprime ≠ (9, 3) := by rw [ha]; decide
      have eP : preP924_1 h = [(0, 0), (2, 1), (42, 16), (48, 18)] := by
        show (if h.aprime = (9, 3) then [(0, 0), (2, 1), (42, 16), (48, 18), (18, 6)]
          else [(0, 0), (2, 1), (42, 16), (48, 18)]) = [(0, 0), (2, 1), (42, 16), (48, 18)]
        rw [if_neg hne]
      have eQ : preQ924_1 h = [(0, 0), (-1, 0), (63, 24), (72, 27)] := by
        show (if h.aprime = (9, 3) then [(0, 0), (-1, 0), (63, 24), (72, 27), (27, 9)]
          else [(0, 0), (-1, 0), (63, 24), (72, 27)]) = [(0, 0), (-1, 0), (63, 24), (72, 27)]
        rw [if_neg hne]
      refine ⟨(preP924_1 h).map (phiPow 3), (preQ924_1 h).map (phiPow 3),
        Or.inr ⟨rfl, rfl, Or.inr ⟨?_, ?_⟩⟩, phiJacPair_3⟩
      · rw [eP]
        exact phi_924_sub3P
      · rw [eQ]
        exact phi_924_sub3Q
    · -- `(a',b') = (9,3)` → sub-case (2).
      have eP : preP924_1 h = [(0, 0), (2, 1), (42, 16), (48, 18), (18, 6)] := by
        show (if h.aprime = (9, 3) then [(0, 0), (2, 1), (42, 16), (48, 18), (18, 6)]
          else [(0, 0), (2, 1), (42, 16), (48, 18)]) =
          [(0, 0), (2, 1), (42, 16), (48, 18), (18, 6)]
        rw [if_pos ha]
      have eQ : preQ924_1 h = [(0, 0), (-1, 0), (63, 24), (72, 27), (27, 9)] := by
        show (if h.aprime = (9, 3) then [(0, 0), (-1, 0), (63, 24), (72, 27), (27, 9)]
          else [(0, 0), (-1, 0), (63, 24), (72, 27)]) =
          [(0, 0), (-1, 0), (63, 24), (72, 27), (27, 9)]
        rw [if_pos ha]
      refine ⟨(preP924_1 h).map (phiPow 3), (preQ924_1 h).map (phiPow 3),
        Or.inr ⟨rfl, rfl, Or.inl ⟨?_, ?_⟩⟩, phiJacPair_3⟩
      · rw [eP]
        exact phi_924_sub2P
      · rw [eQ]
        exact phi_924_sub2Q
  · -- `R = x²(z−λ₁)²(z−λ₂)`: `φ₂` corners + edge as in (9,27) → sub-case (1).
    refine ⟨(preP924_2 h).map (phiPow 3), (preQ924_2 h).map (phiPow 3),
      Or.inl ⟨rfl, rfl, ?_, ?_⟩, phiJacPair_3⟩
    · show ([(0, 0), (2, 1), (42, 16), (48, 18), (36, 12)] : List Pt).map (phiPow 3) =
        [(0, 0), (1, 1), (6, 16), (6, 18), (0, 12)]
      exact phi_924_sub1P
    · show ([(0, 0), (-1, 0), (63, 24), (72, 27), (54, 18)] : List Pt).map (phiPow 3) =
        [(0, 0), (1, 0), (9, 24), (9, 27), (0, 18)]
      exact phi_924_sub1Q
  · exact absurd h3 (rform_ne3_924 h)


/-! ## §E7. Proposition 4.3, case (8,28) — kernel arithmetic.

NOTE ON SCOPE (read first): the proposition's FULL statement is the polygon
reduction (proved conditionally below). The ELIMINATION of the two resulting
shapes is already KERNEL and is NOT redone here:
- item (2) (cases (a),(b)) by the branches-(a),(b) `main_theorem` (kernel,
  permitted triple; `CORRESPONDENCE.md`, "Relation to the branch packages");
- item (1) (case (c)) by `branch_c_eliminated`
  (`composition_2026-11-04.lean`, line 13: no `∃ P Q lam`, `lam ≠ 0 ∧
  NewtonNFc P Q ∧ jac P Q = C lam * X 0 ^ 2`, any characteristic-0 field;
  kernel, no hypotheses, permitted triple) via `challenge_target`
  (`bridge_attempt_2026_11_04.lean`, line 43) — filed 2026-11-06 as tracked
  modules `GradeA.Bridge` / `GradeA.Composition` (commit `7e4db07f`, fork main,
  re-verified on lean-build-3).
What remains open for E7 (and is done here) is the reduction chain itself:
the `φ₁/φ₂/φ₃/φ` polygon chain, the derivation of sub-cases (a)/(b)/(c), the
`Succ_P(−1,4) = Succ_Q(−1,4) = (−2,7)` determination, the `k ∈ {1,2}` analysis
and the `k = 2` impossibility. -/

/-- The (8,28) base corners (TeX 1008): `{(0,0),(1,0),(8,28),(0,4)}`,
    multiplied by `(m,n) = (3,2)`. -/
def base828 : List Pt := [(0, 0), (1, 0), (8, 28), (0, 4)]

theorem swap_828 :
    base828.map swapPt = [(0, 0), (0, 1), (28, 8), (4, 0)] := by
  decide

/-- The Prop 4.3 Cor 7.4 instance (Phase 1 `d1_cor74` `cor74_prop43`, re-pinned):
    `(ρ₀,σ₀) = (−1,4)`, `(a/l,b) = (28,8)`, `en_{−1,4}(F) = (21,6) = (3/4)(28,8)`,
    so `q = 4`. MIXED slot (hybrid-vs-slip, carried — retrieval NOT FOUND). -/
def cor74_prop43_s4 : Cor74Data where
  dir := (-1, 4)
  ab := (28, 8)
  p := 3
  q := 4
  hcop := by decide
  enF := (21, 6)
  hscale := by refine ⟨?_, ?_⟩ <;> decide

theorem cor74_prop43_s4_cond3_fails : ¬ (cor74_prop43_s4.ab.2 > cor74_prop43_s4.ab.1) := by
  decide

theorem cor74_prop43_s4_cond3_F1 : cor74_prop43_s4.ab.2 < cor74_prop43_s4.ab.1 := by
  decide

/-- `qm = 4·3 = 12` — NOT `4·2 = 8` (Part 19's error: `(m,n) = (3,2)` here). -/
theorem cor74_prop43_s4_exp : 4 * 3 = 12 := by decide

/-- `ℓ_{ρ,σ}(P) = λR^{4m}` with `en(R) = (7,2)`: `R^12` has endpoints
    `12·(1,0) = (12,0)` and `12·(7,2) = (84,24)` (Phase 1 `cor74_prop43_R`). -/
theorem cor74_prop43_s4_R :
    (12 * 1, 12 * 0) = (12, 0) ∧ (12 * 7, 12 * 2) = (84, 24) := by
  decide

theorem cor74_prop43_s4_cross : 0 < crossProd (1, -3) ((84, 24) - (12, 0)) := by
  decide

/-- The `(1,−3)`-face check for case (c) (TeX ~line 1150):
    `ℓ_{1,−3}(P) = λ x^{4m}(x³y−α₁)^{4m}(x³y−α₂)^{4m}` — the vertices
    `m(16,4) = (48,12)`, `m(28,8) = (84,24)` and `(12,0)` all have
    `dirVal (1,−3) = 12`, i.e. they lie on the same `(1,−3)`-face. -/
theorem face13_828 :
    dirVal 1 (-3) 48 12 = dirVal 1 (-3) 84 24 ∧ dirVal 1 (-3) 12 0 = 12 := by
  decide

/-- The `Succ_P(−1,4) = Succ_Q(−1,4) = (−2,7)` determination, checked:
    `(−2,7)` is the face direction of the esquina edges — `dirVal (−2,7)`
    is `3` on `(2,1)` and on `3·(24,7) = (72,21)`, and `2` on `(−1,0)` and
    on `2·(24,7) = (48,14)`. -/
theorem dir_27_828 :
    dirVal (-2) 7 2 1 = dirVal (-2) 7 72 21 ∧
    dirVal (-2) 7 (-1) 0 = dirVal (-2) 7 48 14 := by
  decide

/-- `k ∈ {1,2}` from the loosest `(a,b) = (24,7)` row: `(k+1)·7 < 24`.
    Stated over `ℤ` (with `↑k`) to match E7's `k_ineq`, whose `(a,b)` are `Pt`
    components. -/
theorem esquina_k12_247 (k : ℕ) (hk1 : 1 ≤ k) (h247 : ((k : Int) + 1) * 7 < 24) :
    k = 1 ∨ k = 2 := by
  omega

/-- `k = 1` from the tightest `(a,b) = (3,1)` row: `(k+1)·1 < 3`.
    Stated over `ℤ` (with `↑k`) to match E7's `k_ineq`. -/
theorem esquina_k1_31 (k : ℕ) (hk1 : 1 ≤ k) (h31 : ((k : Int) + 1) * 1 < 3) :
    k = 1 := by
  omega

/-- The three lower-side shapes (TeX ~lines 1130–1140), base lists:
    (a) `{(-2,0),(0,0),(28,8),(0,1)}`; (b) `{(-3,0),(0,0),(28,8),(0,1)}`;
    (c) `{(-3,0),(0,0),(16,4),(28,8),(0,1)}` (all ×(m,n)). -/
theorem cut_lower_828_a :
    ([(-2, 0), (0, 0), (28, 8), (0, 1)] : List Pt).map (cutPt (0, 1) (24, 7)) =
      [(-2, 0), (0, 0), (28, 8), (24, 7)] := by
  decide

theorem cut_lower_828_b :
    ([(-3, 0), (0, 0), (28, 8), (0, 1)] : List Pt).map (cutPt (0, 1) (24, 7)) =
      [(-3, 0), (0, 0), (28, 8), (24, 7)] := by
  decide

theorem cut_lower_828_c :
    ([(-3, 0), (0, 0), (16, 4), (28, 8), (0, 1)] : List Pt).map
      (cutPt (0, 1) (24, 7)) =
      [(-3, 0), (0, 0), (16, 4), (28, 8), (24, 7)] := by
  decide

/-- The final morphism `φ(x) = x⁻¹, φ(y) = x⁴y` on the pre-`φ` polygons
    (TeX ~lines 1240–1311). Cases (a)/(b): `P` pre-vertices
    `(0,0),(−1,0),(48,14),(56,16)` — note `en(P) = (−1,0)` here (the paper
    sets `(en(Q),en(P)) = ((2,1),(−1,0))`, SWAPPED relative to E5, where
    `(m,n) = (2,3)` gave `en(P) = (2,1)`); `Q` pre-vertices
    `(0,0),(2,1),(72,21),(84,24)`. Case (c) adds `(32,8) = 2·(16,4)` for `P`
    and `(48,12) = 3·(16,4)` for `Q`. -/
theorem phi_828_abP :
    ([(0, 0), (-1, 0), (48, 14), (56, 16)] : List Pt).map (phiPow 4) =
      [(0, 0), (1, 0), (8, 14), (8, 16)] := by
  decide

theorem phi_828_abQ :
    ([(0, 0), (2, 1), (72, 21), (84, 24)] : List Pt).map (phiPow 4) =
      [(0, 0), (2, 1), (12, 21), (12, 24)] := by
  decide

theorem phi_828_cP :
    ([(0, 0), (-1, 0), (48, 14), (56, 16), (32, 8)] : List Pt).map (phiPow 4) =
      [(0, 0), (1, 0), (8, 14), (8, 16), (0, 8)] := by
  decide

theorem phi_828_cQ :
    ([(0, 0), (2, 1), (72, 21), (84, 24), (48, 12)] : List Pt).map (phiPow 4) =
      [(0, 0), (2, 1), (12, 21), (12, 24), (0, 12)] := by
  decide

/-! ### E7 conditional theorem.

Premise fields:
- `afterPhi1_eq`: `φ₁` swap (kernel `swap_828`) + Cor 7.4 set-up — the
  post-`φ₁` base polygon is `{(0,0),(0,1),(28,8),(4,0)}`.
- `pred_mem`: [GGV6] Prop 2.5 applied — `Pred_P(1,0) ∈ {(1,−2),(1,−3)}`
  (Prop 2.5 itself: instance layer only in Phase 1, `d1_ggvstar`
  `Prop25Instance`; proof OPEN, Leg F).
- `lower_eq`: the three lower-side shapes (a)/(b)/(c) — derived in the paper
  from `Pred_P(1,0)` via the `ℓ_{1,−2}`/`ℓ_{1,−3}` factor analysis.
- `k` + `k_ab_mem` + `k_ineq` + `k_ne2`: [GGV1] Prop 8.2 applied
  (`(a,b)` one of `{(24,7),(17,5),(10,3),(3,1)}`, `(k+1)b < a`), with the
  `k = 2` impossibility ("the edges of `P` and `Q` would have no way of being
  parallel") carried as `k_ne2`.
- `enP`/`enQ`/`stP`/`stQ`/`dirE`: the esquina ends (note the E7 swap:
  `en(P) = (−k,0)`, `en(Q) = (k+1,1)`) and the `st` values
  `st(P) = (48,14)`, `st(Q) = (72,21)` on the `(−2,7)`-face.
- `succP`/`succQ`: `Succ_P(−1,4) = Succ_Q(−1,4) = (−2,7)` (the "as in
  Prop 4.1" opposite-vertex analysis).
- `hybrid_slip`: hybrid-vs-slip for the swapped Cor 7.4 use (same pattern
  as E6: explicit `Prop` parameter + proof field).
[GGV2] Prop 3.12's role in E7 is the `R, G` setting (`[R,G] = R^i`,
`en(R) = (7,2)`); it is carried inside `pred_mem`'s justification (the Pred
restriction that Prop 2.5 refines) and named here: the structure's
`prop312_holds` field (explicit `Prop` parameter `Prop312_828`, same pattern
as `hybrid_slip`) records that the (8,28) `R/G` data satisfy Prop 3.12's
hypotheses. The `en(R) = (7,2)` + `v(R) > 0` content is kernel
(`cor74_prop43_s4_R`); the `[R,G]` equation itself needs the bracket layer
and is the carried part. -/

structure Prop43Premises (HybridSlip828 Prop312_828 : Prop) where
  afterPhi1 : List Pt
  afterPhi1_eq : afterPhi1 = [(0, 0), (0, 1), (28, 8), (4, 0)]
  predP10 : Pt
  pred_mem : predP10 = (1, -2) ∨ predP10 = (1, -3)
  lowerP : List Pt
  lower_eq : lowerP = [(-2, 0), (0, 0), (28, 8), (0, 1)] ∨
    lowerP = [(-3, 0), (0, 0), (28, 8), (0, 1)] ∨
    lowerP = [(-3, 0), (0, 0), (16, 4), (28, 8), (0, 1)]
  k : ℕ
  k_ge1 : 1 ≤ k
  k_ab : Pt
  k_ab_mem : k_ab ∈ [(24, 7), (17, 5), (10, 3), (3, 1)]
  k_ineq : (k + 1) * k_ab.2 < k_ab.1
  k_ne2 : k ≠ 2
  enP : Pt
  enP_eq : enP = (-(k : ℤ), 0)
  enQ : Pt
  enQ_eq : enQ = ((k + 1 : ℤ), 1)
  stP : Pt
  stP_eq : stP = (48, 14)
  stQ : Pt
  stQ_eq : stQ = (72, 21)
  dirE : Pt
  dirE_eq : dirE = (-2, 7)
  succP : Pt
  succP_eq : succP = (-2, 7)
  succQ : Pt
  succQ_eq : succQ = (-2, 7)
  hybrid_slip : HybridSlip828
  prop312_holds : Prop312_828

/-- `k = 1`: from the four `(a,b)` rows (each forces `k ≤ 2`) + `k ≠ 2`. -/
theorem k1_828 {H1 H2 : Prop} (h : Prop43Premises H1 H2) : h.k = 1 := by
  have hg1 := h.k_ge1
  have hn2 := h.k_ne2
  have hmem := h.k_ab_mem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with hab | hab | hab | hab
  · have h7 := h.k_ineq
    rw [hab] at h7
    dsimp only at h7
    rcases esquina_k12_247 h.k h.k_ge1 h7 with h1 | h2
    · exact h1
    · exact absurd h2 h.k_ne2
  · have h5 := h.k_ineq
    rw [hab] at h5
    dsimp only at h5
    omega
  · have h3 := h.k_ineq
    rw [hab] at h3
    dsimp only at h3
    omega
  · have h1 := h.k_ineq
    rw [hab] at h1
    dsimp only at h1
    exact esquina_k1_31 h.k h.k_ge1 h1

/-- The `φ₃` cut on the opaque lower-side list, case by case. -/
theorem cut_lower_828 {H1 H2 : Prop} (h : Prop43Premises H1 H2) :
    h.lowerP.map (cutPt (0, 1) (24, 7)) = [(-2, 0), (0, 0), (28, 8), (24, 7)] ∨
    h.lowerP.map (cutPt (0, 1) (24, 7)) = [(-3, 0), (0, 0), (28, 8), (24, 7)] ∨
    h.lowerP.map (cutPt (0, 1) (24, 7)) =
      [(-3, 0), (0, 0), (16, 4), (28, 8), (24, 7)] := by
  rcases h.lower_eq with h1 | h1 | h1
  · left; rw [h1]; exact cut_lower_828_a
  · right; left; rw [h1]; exact cut_lower_828_b
  · right; right; rw [h1]; exact cut_lower_828_c

/-- The pre-`φ` polygons assembled from the premise fields (cases (a)/(b)
    share one pair; case (c) adds the `(16,4)` vertex scaled). -/
def preP828ab {H1 H2 : Prop} (h : Prop43Premises H1 H2) : List Pt :=
  [(0, 0), h.enP, (48, 14), (56, 16)]

def preQ828ab {H1 H2 : Prop} (h : Prop43Premises H1 H2) : List Pt :=
  [(0, 0), h.enQ, (72, 21), (84, 24)]

def preP828c {H1 H2 : Prop} (h : Prop43Premises H1 H2) : List Pt :=
  [(0, 0), h.enP, (48, 14), (56, 16), (32, 8)]

def preQ828c {H1 H2 : Prop} (h : Prop43Premises H1 H2) : List Pt :=
  [(0, 0), h.enQ, (72, 21), (84, 24), (48, 12)]

/-- The top edge of the cut lower-side polygon, scaled: `(56,16) = 2·(28,8)`,
    `(48,14) = 2·(24,7)` (and the `Q` analogues `(84,24)`, `(72,21)`). -/
theorem pre828_top {H1 H2 : Prop} (h : Prop43Premises H1 H2) :
    (56, 16) ∈ (h.lowerP.map (cutPt (0, 1) (24, 7))).map (scalePt 2) ∧
    (48, 14) ∈ (h.lowerP.map (cutPt (0, 1) (24, 7))).map (scalePt 2) ∧
    (84, 24) ∈ (h.lowerP.map (cutPt (0, 1) (24, 7))).map (scalePt 3) ∧
    (72, 21) ∈ (h.lowerP.map (cutPt (0, 1) (24, 7))).map (scalePt 3) := by
  rcases cut_lower_828 h with h1 | h1 | h1 <;> rw [h1] <;> decide

/-- The case-(c) vertex `(16,4)`, scaled: `(32,8) = 2·(16,4)`,
    `(48,12) = 3·(16,4)`. -/
theorem pre828_c {H1 H2 : Prop} (h : Prop43Premises H1 H2)
    (hc : h.lowerP = [(-3, 0), (0, 0), (16, 4), (28, 8), (0, 1)]) :
    (32, 8) ∈ h.lowerP.map (scalePt 2) ∧ (48, 12) ∈ h.lowerP.map (scalePt 3) := by
  rw [hc]
  decide

/-- Proposition 4.3 (E7), CONDITIONAL: from the premise structure, one of the
    two final shapes holds (item (2) for cases (a)/(b), item (1) for case (c)),
    with Jacobian-factor pair `(−1,2)` (so `[φ(P),φ(Q)] = −[P,Q]·x²`, and with
    `[P,Q] = −1` after the swap this is `x²`). The ELIMINATION of the shapes
    is NOT part of this theorem (see the §E7 header note — it is already kernel).
    The polynomial-level statement is NOT claimed (Laurent layer, R14). -/
theorem prop43_conditional {H1 H2 : Prop} (h : Prop43Premises H1 H2) :
    ∃ finalP finalQ : List Pt,
      ((finalP = (preP828ab h).map (phiPow 4) ∧
        finalQ = (preQ828ab h).map (phiPow 4) ∧
        finalP = [(0, 0), (1, 0), (8, 14), (8, 16)] ∧
        finalQ = [(0, 0), (2, 1), (12, 21), (12, 24)]) ∨
       (finalP = (preP828c h).map (phiPow 4) ∧
        finalQ = (preQ828c h).map (phiPow 4) ∧
        finalP = [(0, 0), (1, 0), (8, 14), (8, 16), (0, 8)] ∧
        finalQ = [(0, 0), (2, 1), (12, 21), (12, 24), (0, 12)])) ∧
      phiJacPair 4 = (-1, 2) := by
  have hk : h.k = 1 := k1_828 h
  have henP : h.enP = (-1, 0) := by rw [h.enP_eq, hk]; decide
  have henQ : h.enQ = (2, 1) := by rw [h.enQ_eq, hk]; decide
  have _hcut := cut_lower_828 h
  have _htop := pre828_top h
  have _hpred := h.pred_mem
  have _hsucc : h.succP = (-2, 7) ∧ h.succQ = (-2, 7) := ⟨h.succP_eq, h.succQ_eq⟩
  rcases h.lower_eq with ha | hb | hc
  · -- Case (a): lower side `{(-2,0),(0,0),(28,8),(0,1)}` → item (2).
    refine ⟨(preP828ab h).map (phiPow 4), (preQ828ab h).map (phiPow 4),
      Or.inl ⟨rfl, rfl, ?_, ?_⟩, phiJacPair_4⟩
    · show ([(0, 0), h.enP, (48, 14), (56, 16)] : List Pt).map (phiPow 4) =
        [(0, 0), (1, 0), (8, 14), (8, 16)]
      rw [henP]
      exact phi_828_abP
    · show ([(0, 0), h.enQ, (72, 21), (84, 24)] : List Pt).map (phiPow 4) =
        [(0, 0), (2, 1), (12, 21), (12, 24)]
      rw [henQ]
      exact phi_828_abQ
  · -- Case (b): lower side `{(-3,0),(0,0),(28,8),(0,1)}` → item (2).
    refine ⟨(preP828ab h).map (phiPow 4), (preQ828ab h).map (phiPow 4),
      Or.inl ⟨rfl, rfl, ?_, ?_⟩, phiJacPair_4⟩
    · show ([(0, 0), h.enP, (48, 14), (56, 16)] : List Pt).map (phiPow 4) =
        [(0, 0), (1, 0), (8, 14), (8, 16)]
      rw [henP]
      exact phi_828_abP
    · show ([(0, 0), h.enQ, (72, 21), (84, 24)] : List Pt).map (phiPow 4) =
        [(0, 0), (2, 1), (12, 21), (12, 24)]
      rw [henQ]
      exact phi_828_abQ
  · -- Case (c): lower side with `(16,4)` → item (1).
    have _hc := pre828_c h hc
    refine ⟨(preP828c h).map (phiPow 4), (preQ828c h).map (phiPow 4),
      Or.inr ⟨rfl, rfl, ?_, ?_⟩, phiJacPair_4⟩
    · show ([(0, 0), h.enP, (48, 14), (56, 16), (32, 8)] : List Pt).map (phiPow 4) =
        [(0, 0), (1, 0), (8, 14), (8, 16), (0, 8)]
      rw [henP]
      exact phi_828_cP
    · show ([(0, 0), h.enQ, (72, 21), (84, 24), (48, 12)] : List Pt).map (phiPow 4) =
        [(0, 0), (2, 1), (12, 21), (12, 24), (0, 12)]
      rw [henQ]
      exact phi_828_cQ


/-! ## §E8. Proposition 4.4, case (7,21) — kernel arithmetic.

The (7,21) case is a CLEAN F-fit (verified 2026-11-04): `en_{7,−2} F = (5/7)(7,21)`,
so `q = 7`. The proof is the shortest in §4: `φ₁` swap, Cor 7.4 (`q = 7`),
`φ₂` shear, `φ₃` final morphism. Only ONE premise field is needed (the `φ₂`-cut
link); everything else is kernel.

CORRECTION TO THE INVENTORY (verified while writing this file): the inventory
says the (7,21) F-side instance is "not yet a `Cor74Data` bundle" (inventory
§B, "still to add (i)"). That is STALE: `d1_cor74_2026-11-05.lean` ALREADY
defines `cor74_721` (direction `(7,−2)`, `(a/l,b) = (7,21)`, `en(F) = (5,15)`,
`q = 7`) with `cor74_721_cond3`, `cor74_721_exp_P/Q`, and proves
`ell721_normalization`. The bundle is re-pinned here self-contained
(`cor74_721_s4` + `ell721_normalization`, the latter copied with attribution
from `d1_cor74`), not claimed as new. -/

/-- The (7,21) base corners (TeX 1387): `{(0,0),(1,0),(7,21),(0,7)}`,
    multiplied by `(m,n) = (2,3)`. -/
def base721 : List Pt := [(0, 0), (1, 0), (7, 21), (0, 7)]

theorem swap_721 :
    base721.map swapPt = [(0, 0), (0, 1), (21, 7), (7, 0)] := by
  decide

/-- The (7,21) Cor 7.4 F-instance (Phase 1 `d1_cor74` `cor74_721`, re-pinned):
    `(ρ₀,σ₀) = (7,−2)` (pre-swap), `(a/l,b) = (7,21)`,
    `en(F) = (5,15) = (5/7)(7,21)`, `q = 7`. Condition (3) HOLDS (`b > a/l`). -/
def cor74_721_s4 : Cor74Data where
  dir := (7, -2)
  ab := (7, 21)
  p := 5
  q := 7
  hcop := by decide
  enF := (5, 15)
  hscale := by refine ⟨?_, ?_⟩ <;> decide

theorem cor74_721_s4_cond3 : cor74_721_s4.ab.2 > cor74_721_s4.ab.1 := by decide

theorem cor74_721_s4_exp_P : 7 * 2 = 14 := by decide

theorem cor74_721_s4_exp_Q : 7 * 3 = 21 := by decide

/-! ### The (7,21) ℓ-normalisation (support level).

Copied with attribution from `d1_cor74_2026-11-05.lean` (`mem_map_range_cast`,
`face721`, `text721`, `ell721_normalization`, `ell721_endpoints`, `ell721_cross`).
The paper's formula `ℓ_{1,−2}(P) = x^{28} λ_p (y − λ x^{−2})^{14}` is the
TEXT form; the true `(1,−2)`-face is the text support shifted by `x^{14}`
(the face's `st`-monomial `(14,0)`). The correct face is `λ_p · x^{14} · R^{14}`
with `R = x²y − λ` (the paper's `R` lacks an `x` factor — a genuine slip,
harmless for the polygon conclusion). The COEFFICIENT identity
`face = λ_p · x^{14} · R^{14}` (with binomial coefficients) is NOT proved here:
it needs the D2 polynomial layer (Leg E, R14). -/

/-- The true `(1,−2)`-face support: `{(14+2j, j) : 0 ≤ j ≤ 14}`. -/
def face721 : List Pt :=
  ((List.range 15).map Int.ofNat).map (fun a => (14 + 2 * a, a))

/-- The text formula's support: `{(28−2k, 14−k) : 0 ≤ k ≤ 14}`. -/
def text721 : List Pt :=
  ((List.range 15).map Int.ofNat).map (fun a => (28 - 2 * a, 14 - a))

/-- Membership in a range-map with a cast inside (Phase 1 `d1_cor74`, verbatim). -/
theorem mem_map_range_cast {n : ℕ} {F : ℤ → Pt} {e : Pt} :
    e ∈ ((List.range n).map Int.ofNat).map F ↔
      ∃ j : ℕ, j < n ∧ F (j : Int) = e := by
  constructor
  · intro h
    obtain ⟨a, ha, hax⟩ := List.mem_map.mp h
    obtain ⟨j, hj, hja⟩ := List.mem_map.mp ha
    rw [List.mem_range] at hj
    exact ⟨j, hj, by rw [← hja] at hax; exact hax⟩
  · rintro ⟨j, hj, rfl⟩
    apply List.mem_map.mpr
    refine ⟨(j : Int), ?_, rfl⟩
    apply List.mem_map.mpr
    exact ⟨j, by rw [List.mem_range]; exact hj, rfl⟩

/-- The ℓ-normalisation (Phase 1 `d1_cor74` `ell721_normalization`, verbatim):
    `e` is in the face iff `e − (14,0)` is in the text support. -/
theorem ell721_normalization (e : Pt) :
    e ∈ face721 ↔ (e.1 - 14, e.2) ∈ text721 := by
  simp only [face721, text721]
  rw [mem_map_range_cast, mem_map_range_cast]
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨14 - j, by omega, ?_⟩
    apply Prod.ext <;> dsimp only <;> omega
  · rintro ⟨k, hk, h⟩
    have h1 : 28 - 2 * (k : Int) = e.1 - 14 := congrArg Prod.fst h
    have h2 : 14 - (k : Int) = e.2 := congrArg Prod.snd h
    refine ⟨14 - k, by omega, ?_⟩
    apply Prod.ext <;> dsimp only <;> omega

/-- Face/text endpoints + orientation (Phase 1 `d1_cor74`, verbatim). -/
theorem ell721_endpoints :
    (14, 0) ∈ face721 ∧ (42, 14) ∈ face721 ∧
    (0, 0) ∈ text721 ∧ (28, 14) ∈ text721 := by
  decide

theorem ell721_cross : 0 < crossProd (1, -2) ((42, 14) - (14, 0)) := by decide

/-! ### E8 φ-chain (TeX 1387–1396). -/

/-- `φ₂(x) = x, φ₂(y) = y + λx⁻²` cuts the `(7,0)` corner to `(−2,0)`
    (the `ℓ_{1,−2}` edge, `q = 7`, exponents `qm = 14`, `qn = 21`).
    Kernel computation on the model. -/
theorem cut_721 :
    ([(0, 0), (0, 1), (21, 7), (7, 0)] : List Pt).map (cutPt (7, 0) (-2, 0)) =
      [(0, 0), (0, 1), (21, 7), (-2, 0)] := by
  decide

/-- `φ₃(x) = x⁻¹, φ₃(y) = yx³` on the post-`φ₂` polygon. -/
theorem phi3_721 :
    ([(0, 0), (0, 1), (21, 7), (-2, 0)] : List Pt).map (phiPow 3) =
      [(0, 0), (3, 1), (0, 7), (2, 0)] := by
  decide

/-- Scaling the final base polygon by `(m,n) = (2,3)` (map order). -/
theorem scale2_721 :
    ([(0, 0), (3, 1), (0, 7), (2, 0)] : List Pt).map (scalePt 2) =
      [(0, 0), (6, 2), (0, 14), (4, 0)] := by
  decide

theorem scale3_721 :
    ([(0, 0), (3, 1), (0, 7), (2, 0)] : List Pt).map (scalePt 3) =
      [(0, 0), (9, 3), (0, 21), (6, 0)] := by
  decide

/-- The map-order lists are the paper's sets: `N(P) = {(0,0),2(2,0),2(3,1),2(0,7)}`
    i.e. `{(0,0),(4,0),(6,2),(0,14)}`; `N(Q) = {(0,0),3(2,0),3(3,1),3(0,7)}`
    i.e. `{(0,0),(6,0),(9,3),(0,21)}`. -/
theorem final721P_set (e : Pt) :
    e ∈ [(0, 0), (6, 2), (0, 14), (4, 0)] ↔ e ∈ [(0, 0), (4, 0), (6, 2), (0, 14)] := by
  simp only [List.mem_cons, List.mem_nil_iff]
  tauto

theorem final721Q_set (e : Pt) :
    e ∈ [(0, 0), (9, 3), (0, 21), (6, 0)] ↔ e ∈ [(0, 0), (6, 0), (9, 3), (0, 21)] := by
  simp only [List.mem_cons, List.mem_nil_iff]
  tauto

/-! ### E8 conditional theorem.

Premise fields (one):
- `afterPhi1_eq`: `φ₁` swap (kernel `swap_721`) — the post-`φ₁` polygon is
  `{(0,0),(7,0),(21,7),(0,1)}` (map order `[(0,0),(0,1),(21,7),(7,0)]`).
- `phi2cut`: Cor 7.4 (`q = 7`, `ℓ_{1,−2}(P) = x^{28}λ_p(y−λx^{−2})^{14}`,
  `ℓ_{1,−2}(Q) = x^{42}λ_q(y−λx^{−2})^{21}`) + `φ₂` — the shear cuts `(7,0)`
  to `(−2,0)`. The ℓ-form's SUPPORT content is kernel (`ell721_normalization`,
  with the `x¹⁴` correction); the coefficient identity is open (D2 layer).
The `φ₃` step and the scalings are kernel (`phi3_721`, `scale2_721`, `scale3_721`). -/

structure Prop44Premises where
  afterPhi1 : List Pt
  afterPhi1_eq : afterPhi1 = [(0, 0), (0, 1), (21, 7), (7, 0)]
  phi2cut : afterPhi1.map (cutPt (7, 0) (-2, 0)) = [(0, 0), (0, 1), (21, 7), (-2, 0)]

/-- The post-`φ₂` polygon, from the premise fields. -/
def postPhi2_721 (h : Prop44Premises) : List Pt :=
  h.afterPhi1.map (cutPt (7, 0) (-2, 0))

/-- The final base polygon, from the premise fields + the kernel `φ₃` map. -/
def final721base (h : Prop44Premises) : List Pt := (postPhi2_721 h).map (phiPow 3)

/-- Proposition 4.4 (E8), CONDITIONAL: from the premise structure, the final
    vertex lists are exactly the paper's (map order; set-equality with the
    paper's listing proved in `final721P_set`/`final721Q_set`), and the
    Jacobian-factor pair is `(−1,1)` (so `[φ₃(P),φ₃(Q)] = −[P,Q]·x`, and with
    `[P,Q] = −1` after the swap this is `x`). The polynomial-level statement
    is NOT claimed (Laurent layer, R14). The (7,21) row's elimination runs
    through E18 (§6) — and, independently, through §3 (E4). -/
theorem prop44_conditional (h : Prop44Premises) :
    ∃ finalP finalQ : List Pt,
      finalP = (final721base h).map (scalePt 2) ∧
      finalQ = (final721base h).map (scalePt 3) ∧
      finalP = [(0, 0), (6, 2), (0, 14), (4, 0)] ∧
      finalQ = [(0, 0), (9, 3), (0, 21), (6, 0)] ∧
      (∀ e : Pt, e ∈ finalP ↔ e ∈ [(0, 0), (4, 0), (6, 2), (0, 14)]) ∧
      (∀ e : Pt, e ∈ finalQ ↔ e ∈ [(0, 0), (6, 0), (9, 3), (0, 21)]) ∧
      phiJacPair 3 = (-1, 1) := by
  have e2 : postPhi2_721 h = [(0, 0), (0, 1), (21, 7), (-2, 0)] := h.phi2cut
  have e3 : final721base h = [(0, 0), (3, 1), (0, 7), (2, 0)] := by
    show (postPhi2_721 h).map (phiPow 3) = [(0, 0), (3, 1), (0, 7), (2, 0)]
    rw [e2]
    exact phi3_721
  have eP : (final721base h).map (scalePt 2) = [(0, 0), (6, 2), (0, 14), (4, 0)] := by
    rw [e3]
    exact scale2_721
  have eQ : (final721base h).map (scalePt 3) = [(0, 0), (9, 3), (0, 21), (6, 0)] := by
    rw [e3]
    exact scale3_721
  refine ⟨(final721base h).map (scalePt 2), (final721base h).map (scalePt 3),
    rfl, rfl, eP, eQ, ?_, ?_, phiJacPair_3⟩
  · intro e
    rw [eP]
    exact final721P_set e
  · intro e
    rw [eQ]
    exact final721Q_set e


/-! ## Verdict table (Leg B — CONFIRMED by the VM run, 2026-11-06:
FULL exit 0, 7 s, Lean 4.34.0; axiom lists below are the `#print axioms`
output of that run; second-tool Python check ALL PASS)

| Item | Verdict | Theorem(s) | Carried premises (named) |
|---|---|---|---|
| E5 Prop 4.1 (9,27) | CONDITIONAL | `prop41_conditional` | `Prop41Premises`: Cor 7.4 edge step, φ₃ edge step, Prop 8.2 applied instance |
| E6 Prop 4.2 (9,24) | CONDITIONAL | `prop42_conditional` | `Prop42Premises`: [GGV2] 3.12 soundness (`pred_sound`), [vdE] 10.2.6 (`pred_ne_25`), Prop 3.12(2) (`h312_2`), hybrid-vs-slip (`HybridSlip924`), φ₂ corners, edge transform, `(a',b')` dichotomy |
| E7 Prop 4.3 (8,28) | CONDITIONAL (reduction) | `prop43_conditional` | `Prop43Premises`: [GGV6] 2.5 (`pred_mem`), [GGV2] 3.12 setting (`prop312_holds`), hybrid-vs-slip (`HybridSlip828`), k=2 exclusion (`k_ne2`), lower-side shapes, Succ determination. ELIMINATION already KERNEL (see §E7 header) |
| E8 Prop 4.4 (7,21) | CONDITIONAL | `prop44_conditional` | `Prop44Premises`: Cor 7.4 (q=7) φ₂-cut link only |
| E9 Algorithm | KERNEL (implementation + output) | `psp_183`, `psp_183_dirs`, `psp_183_dirs_subset` | Correctness = [GGV2] Prop 3.12 (Leg F) — NOT claimed |
| E5 sieve | KERNEL | `sieve_table_927`, `sieve_derivation`, `sieve_rows_927` | — |
| E5/E7 k | KERNEL | `esquina_k1_927`, `esquina_k12_247`, `esquina_k1_31` | — |
| E5/E6/E7/E8 φ-maps + factors | KERNEL | `phi3_927P/Q`, `phi_924_sub*`, `phi_828_abP/Q`, `phi_828_cP/Q`, `phi3_721`, `phiJacPair_3/4` | — |
| E6/E7/E8 Cor 7.4 data | KERNEL (re-pinned) | `cor74_prop42_s4`, `cor74_prop43_s4`, `cor74_721_s4`, `cor74_927_s4` | — |
| E8 ℓ-normalisation | KERNEL (support level) | `ell721_normalization` | Coefficient identity `face = λ_p·x¹⁴·R¹⁴` OPEN (D2 layer) |

NOT proved here (correctly out of scope for this leg): the polynomial-level
existence statements (`P, Q ∈ L^{(1)}` with `[P,Q] = x`/`x²`) — Laurent layer
(R14, Leg E); the chain rule identifying `[φ(P),φ(Q)]` with the factor pair
(R14, Leg E); [GGV2] Prop 3.12, [GGV6] Prop 2.5, [vdE] Prop 10.2.6 themselves
(Leg F); the hybrid-vs-slip resolution (retrieval NOT FOUND 2026-11-06);
the (7,21) coefficient identity (D2 layer). No `sorryAx` anywhere in this file.
-/

#print axioms prop41_conditional
#print axioms prop42_conditional
#print axioms prop43_conditional
#print axioms prop44_conditional
#print axioms psp_183
#print axioms sieve_table_927
#print axioms ell721_normalization
#print axioms phiJacPair_3
#print axioms phiJacPair_4
