# Branch (a,b), degree pair (72,108): Lean 4 formalization of Theorem 1.1 (unconditional since v17)

Lean 4.34.0 · Mathlib `v4.34.0` = `5ed2965256430c3649e86755f9576b54eca72435` (pinned in `lake-manifest.json`).

The capstone is the paper's Theorem 1.1. The top-layer classification (Proposition 6.1) is **reduced
in Lean**, kernel-checked, to one explicit zero-dimensional polynomial system, `ChartClassification`
(17 equations in 17 unknowns). **Since v17 `ChartClassification` is itself proved in Lean**
(`Jacobian/ChartProof/`, `BranchAb.chartClassification_holds`). The NewtonNF2 form of Theorem 1.1,
`BranchAb.main_theorem`, is therefore an **unconditional** kernel-checked theorem on the standard axioms
(§1a⁰, `CLASSIFICATION_STATUS.md`).

GGHV Proposition 4.3 connects Theorem 1.1 to the Jacobian conjecture and lies outside the formal
statement.

## 1. Main results

### 1a⁰. Capstone (v17): Main Theorem 1.1, NewtonNF2 form, unconditional

`BranchAb.main_theorem` and `BranchAb.chartClassification_holds` (`Jacobian/ChartProof/Final.lean`):

```lean
theorem chartClassification_holds (L : Type*) [Field L] [CharZero L] : ChartClassification L
theorem main_theorem {L : Type*} [Field L] [CharZero L] :
    ¬ ∃ (P Q : MvPolynomial (Fin 2) L) (lam : L), lam ≠ 0 ∧ NewtonNF2 P Q ∧
      jac P Q = MvPolynomial.C lam * MvPolynomial.X 0 ^ 2 :=
  main_theorem_of_chart (chartClassification_holds L)
```

* **Axioms.** `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for both
  (`logs/chartproof_axioms.log`).
* **Coordinates.** The proof passes to the reversed coordinates `y_i = a_{7−i}/a₇`, `y₇ = 1/a₇`. There
  the chart equations are the coefficient recursion of `(1 + y₁v + … + y₇v⁷)^{3/2}`.
* **Orbit relations.** Six weighted-homogeneous orbit relations, of weights 4, 5, 5, 6, 6, 7, lie in
  `(S₁₁, …, S₁₆) : y₇³`.
* **Last steps.** A Sylvester resultant and the torus normalization finish the proof.
* **Kernel checks.** All 111 certificate steps are checked by the kernel (`decide +kernel` over the
  verified `Lean.Grind.CommRing` normalizer). There is no `native_decide`.
* **Details.** See `certgen/chartproof/README_chartproof.md`.

### 1a. Capstone: the paper's Main Theorem 1.1, conditional only on the top-layer classification

`BranchAb.main_theorem_of_classification` (`Jacobian/BranchAbMain.lean`):

```lean
theorem main_theorem_of_classification {L : Type*} [Field L] [CharZero L]
    (hcl : TopLayerClassification L) :
    ¬ ∃ (P Q : MvPolynomial (Fin 2) L) (lam : L), lam ≠ 0 ∧ NewtonNF2 P Q ∧ jac P Q = C lam * X 0 ^ 2
```

* `NewtonNF2 P Q` says that `P` and `Q` have exactly the Newton polygons
  `N(P) = conv{(0,0),(1,0),(8,14),(8,16)}` and `N(Q) = conv{(0,0),(2,1),(12,21),(12,24)}`: the support
  lies in the polygon (given by its half-planes), and all 8 vertex coefficients are nonzero.
  `latticeNP_card` and `latticeNQ_card` check by `decide` that the polygons have 25 and 47 lattice
  points, and `vertices_mem` checks the vertices.
* `TopLayerClassification L` is the paper's Proposition 6.1 (m = 7), stated in Lean
  (`BranchAbClassification.lean`). It is **a hypothesis, not an axiom and not proved**. For `L = ℂ` it
  is exactly what the paper proves with Riemann's existence theorem.
* The P,Q-to-layers bookkeeping is **proved** (`BranchAbNewton.lean`, `layers_of_support`).
* `#print axioms main_theorem_of_classification` gives only `[propext, Classical.choice, Quot.sound]`.

### 1a′. Prop. 6.1 reduced to a finite polynomial system (`Jacobian/BranchAbChart.lean`, generated)

```lean
def ChartClassification (L : Type*) [Field L] : Prop :=
  ∀ a1 … a7 b0 … b9 : L, E₁ = 0 → … → E₁₆ = 0 → a7 ^ 3 * b0 ^ 2 = 1 →
    ∃ w, w ^ 5 - w ^ 4 + 3 * w ^ 3 + 3 * w ^ 2 + 26 = 0 ∧ a1 = P₁(w) ∧ … ∧ b9 = Q₉(w)
theorem topLayerClassification_of_chart [CharZero L] : ChartClassification L → TopLayerClassification L
theorem main_theorem_of_chart [CharZero L] (hc : ChartClassification L) :
    ¬ ∃ P Q lam, lam ≠ 0 ∧ NewtonNF2 P Q ∧ jac P Q = C lam * X 0 ^ 2
theorem chart_point_solves [CharZero L] (w) (hw : R w = 0) : …   -- the K₅ chart point solves the system
```

* `E_n = Σ_{i+k=n} (1 + 2k − 3i) a_i b_k`, with `a₀ = b₁₀ = 1`.
* `P_j, Q_k ∈ ℚ[w]`, of degree ≤ 4, give the K₅ top layer in this chart (`certgen/k5point.py`, exact).
* The chart comes from `κ = x₀³ y₁₀² / (x₇³ y₀²)`, which inverts only the four vertex coefficients, so
  no case split is needed.
* In this normalization there are no degenerate solutions: `λ ≠ 0` and `a₇ ≠ 0` are forced.
* All four theorems are on the standard axioms.

What remained for an unconditional Theorem 1.1 was exactly `ChartClassification`. It is proved in v17
(§1a⁰). The external Singular evidence (`certgen/check_chart_cas.sh`: mod 32003, no solution with
`a₁ = 0`, degree 5 with `a₁ = 1`) agrees, and is kept for reference.

### 1b. The descent at the level of P and Q, unconditionally

`BranchAb.no_completion_K5_PQ`: for `P, Q` supported in `N(P)`, `N(Q)`, with `J(P, Q) = λ x²` and
top-layer coefficients `P.coeff(xⁱ y^{2i−2}) = ρ εⁱ⁻¹ topA w i` and
`Q.coeff(xᵏ y^{2k−3}) = σ εᵏ⁻² topB w k` (any root `w`, any `ρ σ ε ≠ 0`), the coefficient
`Q.coeff(x¹² y²⁴)` must be 0.  `BranchAb.no_completion_K5` is the same statement in layer form.

* All five roots `w` (the Galois conjugates) and every torus normalization are covered, including the
  paper's 35 chart points `a₈,₁₄ = 1`, since `L` may be `ℂ`.
* `BranchAb.top_layer_E5`: the hard-coded top layer really solves E5, `2A₂B₃' − 3A₂'B₃ = x²`.
  `BranchAb.orbit_solves_E5` extends this to the whole torus orbit, with `λ = ρσ`.
* `BranchAb.layers_K5_sharp`: every hypothesis except the vertex condition `(12,24)` is satisfiable,
  by the lower-edge partial solution.  So the statements are not vacuous, and the vertex condition is
  exactly what they refute.

### 1c. Lower-edge rigidity (2026-10-07): Corollary 1.2 and Remark 8.8 of the paper

`Jacobian/A816/` (generated by `certgen/gen_a816.py`):

```lean
theorem lower_edge_rigidity {L : Type*} [Field L] [CharZero L] (P Q : MvPolynomial (Fin 2) L) (lam : L)
    (hP : ∀ m ∈ P.support, inNP m) (hQ : ∀ m ∈ Q.support, inNQ m)
    (v10 : P.coeff (mono 1 0) ≠ 0) (v814 : P.coeff (mono 8 14) ≠ 0)
    (w21 : Q.coeff (mono 2 1) ≠ 0) (w1221 : Q.coeff (mono 12 21) ≠ 0)
    (hJ : jac P Q = MvPolynomial.C lam * MvPolynomial.X 0 ^ 2) :
    (∀ i j, 2 * i ≤ j + 1 → (i, j) ≠ (0, 0) → P.coeff (mono i j) = 0) ∧
      (∀ k l, 2 * k ≤ l + 2 → (k, l) ≠ (0, 0) → Q.coeff (mono k l) = 0)
```

* Every coefficient of `P` off its top edge `j = 2i − 2` and of `Q` off its top edge `l = 2k − 3` vanishes, except
  the constant terms: `P = P₂ + a₀,₀`, `Q = Q₃ + b₀,₀`. `λ ≠ 0` is not needed.
* `a816_eq_zero`: in particular `P.coeff (mono 8 16) = 0` (Corollary 1.2).
* `main_theorem_lower_edge`: the NewtonNF2 form of Theorem 1.1 again, now through the vertex `(8,16)`; the vertex
  condition `b₁₂,₂₄ ≠ 0` is not used.
* The chain: `A816.rigidity_K5` (the 75 bracket equations of weights −3 … 0 at the rescaled K₅ top layer force
  all 51 lower unknowns to 0) → `layers_K5_rigid` (layer form) → `rigid_K5` (torus orbit, from `J = λx²`, with
  `layers_transport_E1`) → `rigid_K5_PQ` → `lower_edge_rigidity` (top layer from `chartClassification_holds`).
* **Route.** `rigidity_K5` reuses the descent lemmas of `Jacobian/Descent` up to `t = 0` (the chain of
  `descent_K5`), so it is not independent of Certificate III; it is independent of the vertex `(12,24)`. Then:
  depth 1 vanishes (E₄ pivot facts); at `t = 0` every depth-2 unknown is a K₅-linear form in
  `s = (b₁₁,₂₁, b₁₂,₂₃)` (E₃ pivot facts), e.g. `a₈,₁₆ = κ b₁₂,₂₃`; the E₁ equations `h1_17_34`, `h1_18_36`,
  `h1_19_38` give `b₁₂,₂₃² = 0` and `b₁₁,₂₁² = 0` with explicit K₅ multipliers; E₂ is triangular in `b_{k,2k}` once
  depth 1 vanishes. Each new step is one `linear_combination` checked by `ring1` (67 identities, each also
  verified exactly by the generator with sympy).
* **Statement check** (`certgen/check_a816_statement.py`, sympy, independent of the generators): the 75 equation
  hypotheses are the coefficients of `J = P_x Q_y − P_y Q_x` over the lattice points of `inNP`, `inNQ`, none
  missing; the top layer is `scripts/a816_full.sing`'s; at the K₅ point the equations are the generators
  `e_1 … e_75` of `scripts/a816_certificate/a816_system.py`; the final statements are the expected texts.
* `#print axioms`: `[propext, Classical.choice, Quot.sound]` for all 9 theorems (`logs/axioms_verify_script_66.log`).
  Controls: `controls_a816.sh`, 9/9 as expected (`logs/controls_a816.log`).
* The explicit certificate `a₈,₁₆² = Σ H_k e_k` of `scripts/a816_certificate/` is a second proof of Corollary 1.2,
  independent of the descent. Its structured route is checked in Lean at the level of reflected expressions by
  route C (§1d); the identity `a₈,₁₆² = Σ H_k e_k` itself is not checked in Lean.

### 1d. Route C (merged 2026-10-08; reviewed and integrated 2026-10-12): the certificate's own route, by reflection

`Jacobian/A816C/` (55 files, generated by `routec_gen.py`, **which is not in the repository**). Not imported by
`Jacobian.lean`; built and checked by `./verify_routeC.sh`.

* `A816C.routeC_a816` (`RouteC.lean`): over every field `L` of characteristic 0, for every context `ctx`, if
  `eR.denote ctx = 0` (R(w) = 0) and the 75 reflected equations `Ek_i_j.denote ctx = 0` hold, then
  `(Expr.var 17).denote ctx = 0`. The proof is the certificate's pivot chain (`Pivot/P01–P47`, `Final.lean`), each
  identity checked by kernel reflection (`ChartProof/Reflect.lean`); 56 of the 75 equations are used.
* `A816C.Bridge.routeC_source` (`Bridge.lean`): the same conclusion from the source equations `G_i_j.denote ctx = 0`.
  The `Ek_i_j` use four rescaled variables (a₈,₁₆, b₁₁,₂₀, b₁₁,₂₁, b₁₂,₂₂ multiplied by an integer Δ); the bridge
  proves `Ek_i_j = σ(G_i_j)` by kernel `decide` and transfers the hypotheses through `divCtx`.
* **Statement check** (`certgen/check_routeC_statement.py`, sympy; added 2026-10-12): with `var 0 = w` and `var k`
  the k-th unknown of `scripts/a816_full.sing`, each `G_i_j` is a nonzero integer multiple (1 to 268736) of the
  coefficient of xⁱyʲ of J = P_x Q_y − P_y Q_x in K₅[unknowns], for P, Q of `a816_full.sing`; the 75 labels are
  exactly the nonzero coefficients of weights 3, 2, 1, 0; `var 17` is a₈,₁₆. Three controls fail as required
  (`logs/routeC_statement_check.log`).
* `C7_transfer_fails_without_divCtx` (`Control/C7.lean`): the substitution identity fails without `divCtx`, so the
  rescaling is needed. This is a property of the bridge, not a perturbation control of the certificate: no
  perturbed copy of a pivot identity has been run against the kernel for route C.
* `#print axioms`: `[propext, Classical.choice, Quot.sound]` for `routeC_a816`, `routeC_source`, `transfer` and the C7
  theorem (`logs/routeC_axioms.log`). Build: about 34 min on 2 cores (`logs/routeC_build.log`).
* **What route C does not prove.** `routeC_source` is a statement about reflected expressions. Its link to
  `jac P Q` for `MvPolynomial`s is the Python statement check above, not a Lean theorem. Route R (§1c) is the Lean
  proof at the level of P and Q, and route C is not needed for any theorem of this project. With the statement
  check, route C gives a second, kernel-checked derivation of a₈,₁₆ = 0 from the 75 scalar equations, along the
  certificate's route and independent of `Jacobian/Descent`.

## 2. Proof architecture

| Stage | Lean | Method |
|---|---|---|
| Layer reduction | `BranchAbLayers.lean`: `layer_bracket`, `coeff_yev`, `layers_eq_zero`, `layers_of_jac`, `coeff_layerTerm` | General proof from the derivation rules of `∂ₓ` and `∂ᵧ`. `y^{a+b+1} J(pₐ, q_b) = y² (a A B' − b A' B)(x y²)`. The layers `yᵏ F_k(x y²)` have disjoint monomial supports, so `J = λx²` forces E5, …, E1. `coeff_layerTerm` gives the scalar equations `Σ (a k − b i) Aᵢ B_k`. |
| Torus transport (Lemma 9.1(v)) | `BranchAbTorus.lean`: `coeff_sc`, `layerTerm_sc`, `layers_transport` | `u ↦ κu` together with constants α, β multiplies every layer term by αβκ, so E4, E3, E2 and the supports are preserved. |
| Exact K₅ descent | `Descent/**` (generated, 83 lemma modules) and `Descent/Main.lean` (`descent_K5`) | Certificate steps over K₅. Each is `linear_combination` with explicit multipliers, closed by `ring_nf` and the reduction `wᵏ ↦` a polynomial of degree ≤ 4. |
| Glue | `BranchAbFinal.lean` (generated): `layers_K5`, `no_completion_K5` | Coefficient `n` of each layer identity, expanded by `coeff_layerTerm`, is exactly the scalar bracket equation used by `descent_K5` (56 equations). |
| Consistency and sharpness | `BranchAbSharp.lean` (generated): `top_layer_E5`, `layers_K5_sharp` | 22 coefficient identities over K₅, and an explicit witness. |
| Newton-polygon bookkeeping | `BranchAbNewton.lean`: `layerPoly`, `layerPiece`, `X1_pow_mul_layerPiece`, `eq_sum_layerPiece`, `coeff_layerPoly`, `layerPoly_support`, `NewtonNF2`; `BranchAbMain.lean`: `layers_of_support` | General proof: the monomials of weight 2i − j = a form `yᵃ·Aₐ(xy²)`; the half-plane description gives weights in [0,2] and [0,3], and the supports of the layers. |
| Classification (Prop. 6.1) | `BranchAbClassification.lean`: `TopLayerClassification` (stated), `orbit_solves_E5`, `belyi_derivative`, `layerTerm_top` | The converse (every torus image of a K₅ point solves E5 with λ = ρσ) and the Belyi identity `φ' α⁴ = β·E5` are proved. |
| Reduction of Prop. 6.1 to a finite system | `BranchAbChart.lean` (generated by `gen_chart.py`): `ChartClassification`, `chart_K5_identities`, `topLayerClassification_of_chart`, `chart_point_solves`, `main_theorem_of_chart` | E5 coefficients → normalization by κ → 16 bilinear equations + `a₇³b₀² = 1`; from `(a,b) = (P(w),Q(w))` back to `A₂, B₃` via 21 K₅ identities. The forward direction of `ChartClassification` is the only open input. |
| Capstone | `BranchAbMain.lean` (generated): `no_completion_K5_PQ`, `main_theorem_of_classification` | Theorem 1.1 from the classification hypothesis. |
| **Proof of Prop. 6.1, m = 7, chart form (v17)** | `ChartProof/Reflect.lean`, then `Defs`, `Stage1`, `Stage2_g4…g7`, `Stage3`, `Stage4`, `Final` (generated by `certgen/chartproof/`): `chartClassification_holds`, `main_theorem` | Reversed coordinates `y_i = a_{7−i}/a₇`: the E-equations are the recursion of `(1+x)^{3/2}`. Six orbit relations, of weights 4–7, satisfy `y₇³ g ∈ (S₁₁..S₁₆)`. Sylvester resultant in the chart `t = y₂/y₁²`, `s = y₃/y₁³`. The torus normalization `S₁₀² = y₇³`, then back to `(a,b)`. 111 kernel-evaluated reflective certificate steps. |
| Earlier theorems | `BranchAbObstruction.lean`, `BranchAbRefereeChecks.lean` | `t_zero_case`, `minor_obstruction`, `only_zero_transport`; `t_zero_case_char`, `t_zero_case_fails_char3`, `minor_vanish`, `no_nonzero_direction`. |

### The descent certificate (`certgen/cert.json`, every identity re-verified exactly in python-flint)

Normalization. The point of `e5_exact_K5.json` (`a₁,₀ = b₂,₁ = a₂,₂ = 1`) is moved along the torus by
`e = (49w⁴ − 51w³ − 389w² + 879w + 2424)/128`. The denominators come from four prime ideals (above 2,
431 and 571063277), with valuation proportional to the torus exponent. K₅ has class number 1, so one
generator cancels them all. The total coefficient size falls from about 936 to 89 digits. The choice is
immaterial, because the theorem quantifies over the whole orbit.

| Step | Matrix | Certificate | Modules | Maximum multiplier size |
|---|---|---|---|---|
| E₄ (weight −3) | 18 × 19, rank 17 | reduced row echelon form: each pivot is a K₅-linear form in t = (b₁₁,₂₀, b₁₂,₂₂) | `E4/z_*` (17) | 126 digits |
| E₃ reduction | — | each equation, after the E₄ substitution, reduced mod R | `E3red/r3_*` (19) | — |
| E₃ (weight −2) | 19 × 20, rank 18 | each pivot is a quadratic form in t plus a linear form in s = (b₁₁,₂₁, b₁₂,₂₃) | `E3/x_*` (18) | 165 digits |
| E₂ reduction | — | each equation, after the E₄ and E₃ substitutions, reduced | `E2red/r2_*` (19) | — |
| E₂ (weight −1) | 19 × 12, rank 12 | 7 left-null combinations give F_i = b_i(t) + s₁M_i(t) + s₂L_i(t) = 0 | `E2/F0..F6` | 71 digits |
| Span | 35 minors, rank 6 | t₁⁵ = Σ G⁰_r F_r and t₂⁵ = Σ G¹_r F_r, with G quadratic in t | `Span/span_t1`, `span_t2` | 529 digits |
| t = 0 | — | b₁₂,₂₄ = Σ v_e E₂,e (a row of the left inverse) | `E2/T0` | 64 digits |

## 3. What is proved, what is stated, what is outside

| Item | Status |
|---|---|
| Layer reduction, torus transport, exact K₅ descent, span certificate, glue, E5 consistency, sharpness | **Proved** |
| P,Q-to-layers bookkeeping (Newton polygons to layers, supports, vertices) | **Proved** (`BranchAbNewton`, `layers_of_support`) |
| Theorem 1.1 given the classification | **Proved** (`main_theorem_of_classification`) |
| Top-layer classification, Prop. 6.1 (m = 7): every E5 solution with the vertex conditions lies in the torus orbit of a K₅ point | **Reduced (proved)** to `ChartClassification` (`topLayerClassification_of_chart`). The converse and the Belyi identity are proved. |
| `ChartClassification`: the explicit 17 × 17 polynomial system has only the five K₅ solutions | **Proved (v17)**, `chartClassification_holds` (`Jacobian/ChartProof/Final.lean`), standard axioms. *Pre-v17 note, kept for the record:* **Not proved in Lean.** The measurements are in `CLASSIFICATION_STATUS.md`. The smallest certificate found for the easier half (no solution with `a₁ = 0`) has about 2 × 10⁶ monomial products with coefficients of 10³ digits. Lean's `ring` times out at 1200 s on a single identity with 1.4 × 10⁴ output terms, and kernel reflection runs out of memory. External evidence is mod p only; the Gröbner computations over ℚ did not finish in this session. The paper's route needs Riemann's existence theorem, which is not in Mathlib. |
| GGHV Proposition 4.3 (a counterexample in case (8,28) gives normal form (1) or (2)) | **Outside the formal statement [of this package].** It connects Theorem 1.1 to the Jacobian conjecture. Its proof rests on the structure theory of Jacobian pairs developed across the GGHV papers, which has since been formalized in full in Lean — CONDITIONAL (`prop43_conditional`, axioms `[propext, Quot.sound]`, on `Prop43Premises`; `gghv-dependency-closure/`, inventory `gghv_full_assembly_inventory.md`). Normal form (1) is not treated by the paper [but was eliminated in Lean on 2026-11-04; see `../branch_c/`]. |

Not needed, and so not formalized: the E₃ consistency condition, exact rank equalities (the row-echelon
certificates give the needed direction), and the irreducibility of 𝒲 (every root is quantified over).

## 4. Verification

### Quick start

```bash
./setup.sh             # elan + Lean 4.34.0 + pinned Mathlib and its prebuilt cache (+ python-flint / PARI check)
./run_all.sh           # setup, then the checks below (WITH_CERTGEN / WITH_CONTROLS / WITH_CAS = 0 to skip)
```

### Individual checks

| Command | What it checks | Time on 4 cores |
|---|---|---|
| `./verify_branch_ab_lean.sh` | `lake build` (fails on any error or ``declaration uses `sorry` ``); a static scan of every `.lean` file under `Jacobian/`, comments stripped, for `sorry`, `admit`, `native_decide` or `axiom`; `#print axioms` on 66 theorems (44 through v19, the 9 `Jacobian/B26` theorems added 2026-10-05, the 2 `Jacobian/B26Count` theorems and the 2 `Jacobian/B26Irred` theorems added 2026-10-06, the 9 `Jacobian/A816` theorems added 2026-10-07), each of which must depend only on standard axioms, a subset of `[propext, Classical.choice, Quot.sound]` (v17: includes `chartClassification_holds`, `main_theorem`, `eq_of_toPolyK`, `lc_zero`; two B26 lemmas use only `propext` and `Quot.sound`; `logs/axioms_verify_script_57.log`) | about 17 min from scratch, plus about 25 min for `ChartProof` built sequentially, about 8 min for `B26`, and about 30 s each for `B26Count` and `B26Irred` |
| `./certgen/check_regeneration.sh` | Regenerates `cert.json` and every generated Lean file in a scratch directory and requires them to be byte-identical; then the independent PARI/GP span check; v17: then `chartproof/regenerate_chartproof.sh` (all ChartProof data and modules byte-identical, 105 identities re-verified in SymPy) | 489 s in total for v17 (about 2 min, then about 6 min for ChartProof; `../logs/regeneration_check_v17.log`) |
| `./controls.sh` | Negative controls: perturbed copies (E₃ value, E₄ top-layer value, E₂ multiplier, span multiplier, chart point) must be rejected, a `sorry` copy must be flagged, and the unmodified copies (E₃ lemma, chart module) must be accepted. v17: plus 6 ChartProof controls (recursion, orbit batch, resultant and chart-point perturbations rejected by `decide`; `sorry` flagged; `Stage3` accepted). A rejection counts only if Lean reports the expected error | about 8 min + 2 min on 4 cores; 1,115 s for all 14 with `CONTROLS_JOBS=1` (v17) |
| `./controls_a816.sh` | Negative controls for `Jacobian/A816` (2026-10-07): perturbed copies (both E₁ multipliers, an E₁ coefficient, a top-layer value, a depth-3 coefficient, a false strengthening of `lower_edge_rigidity`) must be rejected, a `sorry` copy must be flagged, the unmodified `Rigidity.lean` and `Final.lean` must be accepted | about 9 min on 2 cores (`CONTROLS_JOBS=1`) |
| `./verify_routeC.sh` (optional, 2026-10-12) | Route C (§1d): builds `Jacobian.A816C.Bridge` and `Jacobian.A816C.Control.C7` (fails on any error or `sorry`), `#print axioms` on `routeC_a816`, `routeC_source`, `transfer` and the C7 theorem (standard axioms only), and the statement check `certgen/check_routeC_statement.py` | about 34 min on 2 cores, plus about 25 s for the statement check |
| `./certgen/check_chart_cas.sh` (optional, needs Singular) | **External evidence, not a proof.** Mod 32003, the chart system has no solution with `a₁ = 0` (unit ideal) and is zero-dimensional of degree 5 with `a₁ = 1` | about 5 min |

Resources: about 2 GB RAM per build job (peak 7.8 GB with 4 jobs). The generated chart module
`BranchAbChart.lean` alone needs about 8 GB and 2 minutes; it is built last, so it runs alone. There is
about 2.5 GB of `.olean` output.
Proof checking is done by the Lean kernel. `native_decide` is never used in `Jacobian/`, and the verifier
rejects it. It appears only in `experimental/CertCheck.lean`, a prototype certificate checker that is not
imported and not used by any theorem (see `CLASSIFICATION_STATUS.md` §6).

### Recorded results (`logs/`)

* `logs/routeC_build.log`, `logs/routeC_axioms.log`, `logs/routeC_statement_check.log` (2026-10-12): route C (§1d):
  the build of `Jacobian/A816C` (exit 0, 2020 s on 2 cores; the warnings are summarized in the log's header), the
  axioms of its four theorems, and the statement check (PASS, three controls fail as required).
* `logs/axioms_verify_script_66.log`, `logs/controls_a816.log`, `logs/a816_build.log`, `logs/a816_statement_check.log` (2026-10-07): the full `verify_branch_ab_lean.sh` run with `Jacobian/A816` (66/66 theorems on the standard axioms), its controls, the build of the two modules, and the statement check.
* `logs/chartproof_build.log`, `logs/chartproof_axioms.log`, `logs/chartproof_controls.log`, `logs/chartproof_regeneration.log`, `logs/chartproof_saturation.log`, `logs/chartproof_independent_check.log` (v17): sequential build of the 11 generated ChartProof modules (`Reflect.lean` was built before, as a dependency); `verify_branch_ab_lean.sh` (44/44 theorems on the standard axioms) and `AxiomsAudit.lean`; 14/14 controls as expected; byte-identical regeneration; the saturation check over ℚ (context only); the independent re-check of all 111 identities.
* `logs/verify_with_chart.log` (not included in this bundle, nor in v16): the full project with the chart reduction. ALL CHECKS PASSED; 40/40 theorems on the standard axioms.
* `logs/run_all_with_chart.log`: `run_all.sh` end to end, with regeneration, controls and the CAS evidence.
* `logs/chart_cas.log`: the external Singular runs for the chart system, mod p and over ℚ, including the ℚ runs that did not finish.

* `logs/verify_with_classification.log`: the full project with the bookkeeping, classification and capstone modules. ALL CHECKS PASSED; 36/36 theorems on the standard axioms.
* `logs/verify_from_scratch.log`, from a clean extraction of the previous version (the descent, 24 theorems): ALL CHECKS PASSED in 892 s, peak memory
  7.8 GB, 0 warnings, 24/24 theorems on the standard axioms.
* `logs/lake_build_from_scratch.log`: the full build output, with per-module timings.
* `certgen/span_check.out`, the PARI/GP check:
  * F_i = b_i + s₁M_i + s₂L_i for all 7 rows: PASS.
  * Nonzero minors: 35 of 35, rank 6 over K₅.
  * t₁⁵ and t₂⁵ via c₀, c₁ (6 minors) and via G: PASS.
  * Corrupted-multiplier control: rejected.
* Controls run by hand during development:
  * an E₃ pivot value off by one in its last digit: rejected;
  * an E₄ top-layer value off by 1/16: rejected;
  * a planted `sorry`: flagged;
  * the original shipped `h2` line: build error at 45:4.
* `logs/run_all_first_pass.log`: `run_all.sh` end to end on a clean extraction (setup, verify,
  byte-identical regeneration, PARI check, controls). RUN_ALL: EVERYTHING PASSED in 294 s. That pass
  exposed a bug in `controls.sh`: the job list had no trailing newline, so the last control (the
  planted `sorry`) was silently skipped, and 5 of 6 ran.
* `logs/controls.log`: the fixed `controls.sh` (it now also requires every queued control to report).
  6 / 6 passed: the unmodified E₃ lemma is accepted; the perturbed E₃ value, E₄ top-layer value, E₂
  multiplier and span multiplier are rejected; the `sorry` copy is flagged.

## 5. Layout

```
Jacobian.lean                        imports every module below
Jacobian/Basic.lean                  valuative properness (unrelated to branch (a,b); kept for compatibility)
Jacobian/BranchAbObstruction.lean    original 3 theorems (h2 build fix; docstrings corrected)
Jacobian/BranchAbRefereeChecks.lean  characteristic analysis, minor vanishing, §8.4 chain
Jacobian/BranchAbLayers.lean         layer reduction (general)
Jacobian/BranchAbTorus.lean          torus transport (general)
Jacobian/BranchAbFinal.lean          layers_K5, no_completion_K5        [generated]
Jacobian/BranchAbSharp.lean          top_layer_E5, layers_K5_sharp      [generated]
Jacobian/BranchAbNewton.lean         Newton polygons, P,Q-to-layers bookkeeping
Jacobian/BranchAbClassification.lean TopLayerClassification (stated), orbit_solves_E5, belyi_derivative
Jacobian/BranchAbMain.lean           no_completion_K5_PQ, main_theorem_of_classification   [generated]
Jacobian/BranchAbChart.lean          ChartClassification, topLayerClassification_of_chart, main_theorem_of_chart [generated]
Jacobian/ChartProof/Reflect.lean     kernel-evaluable reflective certificate checker (toPolyK, eq_of_toPolyK, lc_zero)
Jacobian/ChartProof/{Defs,Stage1,Stage2_g4..g7,Stage3,Stage4}.lean   proof of ChartClassification [generated]
Jacobian/ChartProof/Final.lean       chartClassification_holds, main_theorem (unconditional)        [generated]
Jacobian/Descent/{E4,E3red,E3,E2red,E2,Span}/*.lean, Main.lean   [generated]
Jacobian/A816/Rigidity.lean, Final.lean   lower-edge rigidity: rigidity_K5, ..., lower_edge_rigidity (2026-10-07) [generated]
Jacobian/A816C/                      route C: routeC_a816, routeC_source (2026-10-08) [generated; generator not included;
                                     NOT imported by Jacobian.lean; see verify_routeC.sh]
certgen/  make_cert.py gen_lean2.py gen_final.py gen_sharp.py gen_main.py export_pari.py opt.gp
          gen_system.py e5_exact_K5.json cert.json span_check.gp span_check.out
          regenerate.sh check_regeneration.sh README_descent.md
          k5point.py chartpoint.json gen_chart.py chart_cas.py check_chart_cas.sh chart_*.sing
          chartproof/  generator of Jacobian/ChartProof (README_chartproof.md, regenerate_chartproof.sh)
          gen_a816.py check_a816_statement.py   generator and statement check of Jacobian/A816 (2026-10-07)
          check_routeC_statement.py   statement check of Jacobian/A816C (2026-10-12)
experimental/CertCheck.lean          native_decide certificate-checker prototype (NOT imported, NOT used)
verify_branch_ab_lean.sh setup.sh run_all.sh controls.sh controls_a816.sh verify_routeC.sh
BranchAbObstruction_CORRESPONDENCE.md  CLASSIFICATION_STATUS.md  CHANGES.diff  MD5SUMS  logs/
```
