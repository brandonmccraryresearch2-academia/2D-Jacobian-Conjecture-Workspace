# Two-Dicritical Lean Scoping — Script Inventory, Proof Obligations, No-Go Zones

Date: 2026-10-14. Branch: `caic/two-dicritical-lean-scoping` (from `origin/main` @ `c617838`).
Build: `branch_two_dicritical/lean/build.sh ~/workspace/jacobian_lean` (Lean 4.34.0, Mathlib v4.34.0).

## 1. The 18 SymPy scripts: what each proves, and its Lean status

### Part I — the m ≥ 2 elimination (constant-leading-form degeneration)

| # | Script | What it proves (inputs → outputs) | Lean status |
|---|--------|-----------------------------------|-------------|
| 1 | `general_constant_form.py` | **The universal mechanism.** For any `E_k` (k≥2) obtained by successive blowups at points with nonzero transverse coordinate `u₀≠0`: the coefficient of the exact pole order `(v')^{-m}` is *independent* of the residual transverse coordinate `u'`, because `(u₀+u'v')^{-J}|_{v'=0} = u₀^{-J}` is constant. Hence `[φ₀:ψ₀]` has degree 0, so no dicritical of order m≥2 exists on any such `E_k`. Symbolic demonstration of the inductive step. | **OPEN — biggest gap.** Nothing formalized. Needs blowup charts + valuations. |
| 2 | `middle_e2.py` | Solitary m=2 dicritical on **middle** E₂ of chain E₁–E₂–E₃ impossible. Finite computation at symbolic nonzero `c`, d=2,3,4, explicit E₂ chart. | Open; subsumed by (1) if formalized. |
| 3 | `leaf_e3.py` | Solitary m=2 on **leaf** E₃ impossible. Finite computation at symbolic `c`, `τ₀≠0`, d=2,3,4. | Open; subsumed by (1). |
| 4 | `leaf_e4.py` | Solitary m=2 on **leaf** E₄ impossible. Finite computation at symbolic `c`, `τ₀≠0`, `x₀≠0`, d=2,3. | Open; subsumed by (1). |
| 5 | `e1_solitary.py` | Solitary m=2 on the **first** exceptional E₁, d=4,5,6, explicit E₁ chart. | **NO-GO (false thm:e1).** Computed in the misread monomial set (J+K≥2). Must be redone in the x-degree formulation. |
| 6 | `e1_global.py` | Global d=4 test: explicit pair in the "open subset". | **NO-GO (false thm:e1).** Same wrong monomial set; moreover `check_e1_index.py` check 6 shows the pair's restriction has degree 1, not 2, when correctly labelled. |
| 7 | `e1_keller_search.py` | Random + structural search for constant-Jacobian deformation on E₁. | **NO-GO (false thm:e1).** Searches the wrong monomial set. The corrected question (x-degree ≤ 2) is partially in Lean via `e1_lead_proportional`. |
| 8 | `at_degree_bound.py` | at-degree bound for the two-branch bridge: finite computation at centers {2,5}, 1≤m₁≤m₂≤5, d=m₂..m₂+3. The `b^{2d-m}` coefficient has at-degree < m. | Open in general; the m=1 case is subsumed by `bridge_collapse`. |
| 9 | `mixed_poles.py` | Two-branch bridge with **unequal** pole orders (m=2 at a₃=2, m=3 at a₄=5). Finite joint linear system; reports nullity and J-vanishing. | **Open.** `bridge_collapse` covers only m=1 at both centers. |
| 10 | `depth5_global.py` | Depth-5 global analysis at explicit centers: m=1 Vandermonde nullity-2 for d≤5; adjacent monomial restriction (generic degree-2 check); non-cancellation `C_P≠0` **assumed, not proved**. | Partially subsumed by `bridge_collapse`; the adjacent case and `C_P≠0` remain open. |
| 11 | `depth6_enum.py` | Depth-6 **combinatorial** enumeration of trees with ≥2 dicritical candidates (m≥3, κ≥7 odd) via κ=3ν−c. Not a geometric realizability proof. | No direct Lean obligation (combinatorics, not geometry). |
| 12 | `routeB_cancellation.py` | Route B residual loophole at d=3, symbolic nonzero `c`: closed-form `w^{-M}`, `w^{-(M-1)}` coefficients; tests dicritical conditions on the cancellation locus `C_P=0`. | Open (finite d=3 computation). |

### Part II — the m = 1 bridge (descending induction on W = 2J+K)

| # | Script | What it proves (inputs → outputs) | Lean status |
|---|--------|-----------------------------------|-------------|
| 13 | `m1_bridge_general.py` | m=1 bridge at **symbolic** centers a₃≠a₄, d=2,3: joint nullspace = span{1,y}, so J vanishes identically. | **FORMALIZED, generalized.** `bridge_collapse` (BridgeCollapse.lean): all d, all W, no sorry. |
| 14 | `m1_induction.py` | m=1 bridge collapse at higher d (numeric, a₃=2,a₄=5, d=4,5,6). | Subsumed by `bridge_collapse`. |
| 15 | `m1_triangular.py` | Weight-by-weight triangularity at d=6 (the induction structure). | Subsumed: this triangularity *is* the proof structure of `bridge_collapse`. |
| 16 | `m1_block_rank.py` | Block-rank certificate: diagonal blocks `[C(e_k,i)a^{e_k-i}]` are full-rank scaled Vandermondes; Vandermonde column test at d=2..6. | **FORMALIZED.** `block_rank` (BlockRank.lean); `block_vanish_two` is the lemma `bridge_collapse` applies. |
| 17 | `e3_adjacent.py` | Adjacent case (E₂,E₃ both dicritical) at d=3. | Open beyond d=3 (RESTATEMENT.md O4). |
| 18 | `at_degree_bound_m5.py` | at-degree bound extended to m≤5 (see #8). | Same as #8. |

### Check scripts (not part of the 18; they audit the claims)

- `lean/check_e1_index.py` — 6 checks: the ν_{E₁}(x^i y^j)=−i formula; the two 12-element monomial sets and their difference; the Keller counterexample P=(x+y²)²+y, Q=P+x+y² ([P,Q]=−1, satisfies the paper's stated E₁ conditions); the x^{2n−1}-coefficient n(AD′−A′D); the restriction formula on 40 random S; the e1_global.py relabelling (degree 1, not 2).
- `lean/check_satellite.py` — 7 checks: the bridge pullback identity; ν(x),ν(y) at free points (−2,−1) vs at a=0 (−3,−2); the (x−a₄y²,y) witness; the (0,5) center computation; ν_{E(a)}(S) for a≠0; the (x+y³,y) satellite pencil; **check 7: a degree-1 restriction does not force ν≥−1** (P=(x−a₄y²)y+1, Q=y²+1: ν=−2, P/Q restricts to at/a₄) — i.e. **(P2) is asserted, not derived**.

## 2. What is formalized on this branch (all zero-sorry, standard axioms)

Build status 2026-10-14 (via `build.sh`; Lean 4.34.0, Mathlib v4.34.0):
- **Verified compiling (exit 0):** `BlockRank` (75 s), `E1Obstruction` (2 s).
- **Blocked by environment, not by file errors:** `BridgeCollapse` and the new `E1Valuation`
  hit a Lean-runtime futex stall (`futex_do_wait`, ~5% CPU) under severe VM overload
  (load avg 7+, 7 concurrent Lean processes from multiple agents, 2 CPUs). `BridgeCollapse`
  compiled clean on 2026-10-13 in the same build.sh; the stall is environmental.
  `E1Valuation` is new and unverified — its proofs are `rfl`/`omega`/`decide`/`norm_num`
  over exponent arithmetic, but it has not completed a compile in this environment.
- The remaining modules (`CenterHypotheses`, `OneCenter`, `E1Keller`, `Axioms`) were not
  reached in this build run (build.sh stops at the first failure).

| File | Theorems | Content |
|------|----------|---------|
| `TwoDicritical/BlockRank.lean` | `choose_det_ne_zero`, `subMat_det_ne_zero`, `block_rank` | Scaled-Vandermonde full rank (script #16). |
| `TwoDicritical/BridgeCollapse.lean` | `bridge_collapse`, `bridge_jacobian_eq_zero` | m=1 bridge: nullspace = span{1,y} for all d, W (scripts #13–16). |
| `TwoDicritical/CenterHypotheses.lean` | 3 witnesses | a₃≠0, a₄≠0, a₃≠a₄ cannot be dropped. |
| `TwoDicritical/E1Keller.lean` | `thm_e1_false`, `e1P_not_noLowTerms`, `eq_C_mul_of_wronskian`, `jac2_coeff_top`, `e1_lead_proportional`, `jac2_eq_zero_of_natDegree_zero` | M3: the paper's thm:e1 is false (Keller counterexample); the corrected algebraic step (Wronskian proportionality). |
| `TwoDicritical/E1Obstruction.lean` | (fidelity-flagged) | **Proves a true theorem about the wrong monomial set** — retained with its fidelity warning; do not cite as the E₁ obstruction. |
| `TwoDicritical/E1Valuation.lean` **(new, unverified — see build status above)** | `e1_order`, `e1_condition_iff`, `e1_true_set_card`, `e1_false_set_card`, `e1_sets_differ_x3`, `e1_sets_differ_y` | **The M3 chart step**: ν_{E₁}(x^i y^j)=−i; ν≥−2 ⟺ x-degree ≤ 2; both d=4 monomial sets have 12 elements (`decide`); explicit witnesses that they differ. Pure exponent arithmetic; the chart substitution is executed in `check_e1_index.py`. |
| `TwoDicritical/OneCenter.lean` | `bridge_one_center`, `zero_center_no_top_degree` | One-center case; the a=0 top-degree vanishing. |
| `TwoDicritical/Axioms.lean` | 21 `#print axioms` lines | Axiom audit: all on {propext, Classical.choice, Quot.sound}. |

## 3. Proof-obligation list for the Lean translation (what remains)

**P-A (largest gap). The m ≥ 2 constant-leading-form mechanism** (script #1).
Formalize: blowup at `(u₀,0)` with `u₀≠0`; chart `u = u₀+u'v'`, `v = v'`; the
`(v')^{-m}` coefficient is `u'`-independent. Requires a formal notion of blowup
chart / valuation — the natural next major target, but the heaviest lift.
Scripts #2–4 are corollaries once this is done.

**P-B. The E₁ degree obstruction, end to end** (scripts #5–7, corrected).
Have: `e1_lead_proportional` (algebraic Wronskian step) + `E1Valuation` (chart
valuation formula). Missing: the assembly — from "P,Q in the true E₁ span
(x-degree ≤ 2), [P,Q] = c ≠ 0" derive a contradiction *using* the Keller
condition globally. The Keller counterexample shows the E₁-local conditions alone
do not suffice; the global argument is open.

**P-C. The bridge's geometric premises as explicit hypotheses.**
`BridgeConditions` (the `ord_b ≥ 2d−1` equations at two centers) is the formal
stand-in for (P1)+(P2). The derivation "two dicriticals at infinity ⟹
`BridgeConditions`" is not in Lean and cannot be completed without (P2) as an
explicit premise (`check_satellite.py` check 7: degree-1 restriction ⇏ ν≥−1).

**P-D. Mixed pole orders** (script #9). `bridge_collapse` is m=1 at both centers;
the (m₁,m₂)≠(1,1) bridge is open.

**P-E. The adjacent case beyond d=3** (scripts #17, #10-part; RESTATEMENT.md O4).

**P-F. Route B cancellation beyond d=3** (script #12).

## 4. No-go zones → explicit hypotheses

### (a) The false thm:e1 — do NOT formalize the paper's monomial translation
- **The trap.** The paper's §3.2 reads the unknowns `p[J,K]` (indexing `x^{d-J-K}y^J`)
  as `x^Jy^K`, turning "ν_{E₁}≥−2" into "total degree ≥ 2". `E1Obstruction.lean`'s
  `noLowTerms` formalizes the misreading (true theorem, wrong statement — fidelity
  failure, retained with warning).
- **The rule.** Any E₁ formalization must use the x-degree formulation:
  `E1Open4` (`m 0 ≤ 2`) in `E1Keller.lean`, `e1_condition_iff` in `E1Valuation.lean`.
  Scripts #5–7 (`e1_solitary.py`, `e1_global.py`, `e1_keller_search.py`) are computed
  in the wrong monomial set and must be redone, not translated.
- **Explicit hypothesis where needed.** `E1Open4 p m d (hP : p 0 ≤ 2) (hQ : m 0 ≤ 2)` —
  the `m 0 ≤ 2` premises *are* the true E₁ condition, stated on the nose.

### (b) The a=0 "center" is a satellite-chart artifact — not a missing argument
- **The fact.** `check_satellite.py` checks 1–2, 5: the bridge pullback
  `S_a(b) = S^h(1,b,b²(a+ãb))` is a chart at a point of E₂; at `a=0` it is the
  satellite point E₂∩L, where ν(x),ν(y) = (−3,−2) not (−2,−1) and the threshold
  `ord_b ≥ 2d−1` weakens with the homogenizing degree. The "a=0 center" of the
  paper's §3.3 is not a free point and carries no dicritical of the required type.
- **The rule.** `bridge_collapse`'s hypotheses `a₃≠0`, `a₄≠0` mark exactly where the
  chart formula applies (`CenterHypotheses.lean` witnesses they cannot be dropped).
  Satellite points are untreated — and need no treatment for the free-point bridge.
- **Explicit hypothesis where needed.** Every bridge application carries
  `ha₃ : a₃ ≠ 0`, `ha₄ : a₄ ≠ 0`, `hne : a₃ ≠ a₄` — these are chart-validity
  conditions, not gaps.

### (c) P1/P2 — premises of the bridge, not conclusions
- **P1** (dicriticals above free points of E₂): encoded in the use of the free-point
  chart `S_a(b)` with `a≠0`; satellite points excluded by (b).
- **P2** (pole order ≤ 1): `BridgeConditions` *states* `ord_b(S_{a_i}) ≥ 2d−1`
  (equivalently ν_{E(a_i)} ≥ −1). `check_satellite.py` check 7 proves this does not
  follow from the restriction having degree 1: P=(x−a₄y²)y+1, Q=y²+1 have ν=−2
  while P/Q restricts to at/a₄. **(P2) is therefore an explicit premise of every
  bridge application, asserted, not derived.**
- **The rule.** The formal theorem is "`BridgeConditions` ⟹ J=0 on the span".
  The geometric step "two dicriticals at infinity ⟹ `BridgeConditions`" is
  P-C above: open, and blocked on (P2) by check 7.

## 5. Deliberately not formalized

- `depth6_enum.py` (#11): finite combinatorics, not geometry; no Lean obligation.
- The full resolution tree / divisor classification: the formalization targets the
  two proof engines (m≥2 degeneration, m=1 bridge), not the algebro-geometric
  scaffolding around them.
- Anything requiring the false thm:e1 or the a=0 satellite center as stated.
