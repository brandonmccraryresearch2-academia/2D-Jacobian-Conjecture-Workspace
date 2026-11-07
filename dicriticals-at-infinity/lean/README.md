# Two-dicritical line: Lean 4 formalization (partial)

Added 2026-10-12. Lean 4.34.0, Mathlib v4.34.0; no `sorry`; 21 theorems on the standard axioms (`logs/build.log`,
about 2 min on 2 cores). `build.sh` compiles the modules in a temporary directory against any Lake project with
Mathlib v4.34.0 (default `../../JC2D-branches_a_b_c_unified/branches_a_b/lean`, after `lake exe cache get` there),
scans for `sorry`/`admit`/`native_decide`/`axiom`, and checks the axioms. If the project has no compiled Mathlib, it
stops with exit status 2 before calling `lake`, which would otherwise start cloning Mathlib (CAIC's review).

The 21 theorems, by kind (`TwoDicritical/Axioms.lean`):
- 8 on the bridge equations;
- 5 witnesses that the center hypotheses cannot be dropped from the formal statement;
- 8 on `E₁`:
  - 2 true, but about a set of monomials that is not the `E₁` condition;
  - 2 for the counterexample to Theorem `thm:e1`;
  - 4 for the corrected step.

**Corrected on 2026-10-13**, after an outside referee's report on PR #19. Every point below was re-derived and
executed here before it was accepted (`check_satellite.py`, `check_e1_index.py`, with their logs):
- the center hypotheses are not a gap of the kind "a center cannot sit at 0" (item 1 below);
- Theorem `thm:e1` is false as stated, and `E1Obstruction.lean` is about a different set of monomials (item 2).

## What is proved

| Module | Theorem | Statement | Paper |
|---|---|---|---|
| `BlockRank` (CAIC, unchanged) | `choose_det_ne_zero`, `block_rank` | det[C(e_k, i)] ≠ 0 for distinct e_k (falling factorials and Vandermonde); the 2m × n block has rank n when m ≥ n | Lemma `lem:block-rank` |
| `BridgeCollapse` | `bridge_collapse` | under the bridge conditions at two distinct nonzero centers, every p(J,K) with J + K ≤ d and 2J + K ≥ 2 vanishes: the solutions are span{1, y} | Theorem `thm:bridge` |
| | `bridge_jacobian_eq_zero` | two polynomials satisfying the bridge conditions have Jacobian 0, so they are not a Keller pair | Corollary `cor:bridge-empty` |
| `OneCenter` (2026-10-13) | `bridge_one_center` | the equations at **one** nonzero center a already kill every coefficient of weight 2J + K ≥ 3 and force p(0,2) = −a·p(1,0): the solutions are span{1, y, x − a·y²}, of degree at most 2 | the scope of Theorem `thm:bridge` |
| | `zero_center_no_top_degree` | at the centers 0 and a₄ ≠ 0 with d ≥ 3, every coefficient of total degree d vanishes: with d read as the exact degree, the witness below does not exist | the same |
| `CenterHypotheses` (2026-10-12) | `bridge_collapse_needs_ne_zero`, `bridge_collapse_needs_ne`, `bridge_jacobian_needs_ne_zero` | none of the center hypotheses can be dropped from the formal theorem: x − c·y² satisfies every bridge equation at the centers 0 and c (d ≥ 3), and at c and c (d ≥ 2); with Q = y it is a Keller pair (`jacobian_auto`: Jacobian 1). Item 1 below explains why the center at 0 is not a geometric bridge | the scope of Theorem `thm:bridge` |
| `E1Obstruction` (CAIC, unchanged) | `e1_degree_obstruction`, `not_keller_of_noLowTerms` | if every monomial of P and Q has total degree ≥ 2, then [P,Q] has no constant term, so (P,Q) is not Keller. True, but **not** the E₁ condition, which is x-degree ≤ 2 (item 2) | none: the label "Theorem `thm:e1`, its algebraic step" was wrong |
| `E1Keller` (2026-10-13) | `thm_e1_false`, `e1P_not_noLowTerms` | P = (x + y²)² + y and Q = P + x + y² lie in the paper's E₁ m = 2 open subset at d = 4 (`E1Open4`) and [P,Q] = −1; P contains y | Theorem `thm:e1` is false as stated |
| | `eq_C_mul_of_wronskian`, `jac2_coeff_top`, `e1_lead_proportional`, `jac2_eq_zero_of_natDegree_zero` | for x-degrees ≤ n ≥ 1 and constant Jacobian, the xⁿ-coefficients A, D ∈ K[y] are proportional (the x^(2n−1)-coefficient of [P,Q] is n(AD′ − A′D), and a vanishing Wronskian forces proportionality in characteristic 0); for x-degree 0 the Jacobian vanishes | the intended conclusion of `thm:e1`, for every m |

### How `BridgeCollapse` differs from the draft `Bridge.lean` of 2026-10-12

That draft (handoff only; sha256 `49cb5c3c…`) derived the theorem from two axioms, `bridge_triangular` and
`block_full_rank`. Lean quantified both over **every** system, not over the paper's, and each is false
(`../../JC2D-branches_a_b_c_unified/reviews/lean/BridgeAxiomsInconsistent.lean`). So its theorems were vacuous.
`BridgeCollapse` has no axioms. It takes the paper's equations as an explicit definition (`bridgeEq`) and proves the
theorem from them.

**The equations.**
- The coefficient of ã^i b^t of the pullback S_a(b) = Σ p_{JK}(a + ã b)^{d−J−K} b^{2d−2J−K} collects exactly the
  monomials of weight W = 2J + K = 2d − t + i.
- So the system is **block-diagonal** in W, and the draft's triangularity axiom is not needed.
- `check_bridgeEq.py` confirms the definition against the expanded pullback for d = 2…6, and finds nullity 2 at the
  centers 2 and 5 (`logs/check_bridgeEq.log`).

**A gap in the paper's proof, closed here.** The block at weight W has n variables and m = W − 1 equations per
center. The paper applies the block-rank lemma, whose hypothesis is m ≥ n. This fails at W = 2, where n = 2 > 1 = m.
`block_vanish_two` closes that case with the two centers: a^{d−2}(p₁₀a + p₀₂) = 0 at a₃ ≠ a₄, both nonzero. For
W ≥ 3, n ≤ m and one center suffices (`block_vanish`).

**A shorter proof, outside Lean.** Over a free point a ≠ 0 of E₂, the valuation of the divisor E(a) is minus the
degree in the coordinates (x − a·y², y). The reason: (x − ay²)^j y^k becomes ã^j b^{−(j+k)}(a + ãb)^{−2j−k} along
E(a), and for fixed j + k the leading terms are distinct powers of ã. So ν ≥ −1 means S ∈ span{1, y, x − a·y²}, and
two distinct centers give span{1, y} with no block-rank lemma. Executed in `check_satellite.py` (240 random S, and the
exact image of each monomial). This proof is the referee's.

## What is not proved (the main theorem stays open)

0. **The statement of the main theorem.**
   - As worded ("the resolution of the pencil λP + μQ contains no two distinct dicritical divisors") it is false for
     **every** Keller map of degree ≥ 2.
   - Such a pencil has a base point at infinity: with equal degrees the top forms are proportional, and with unequal
     degrees Qʰ vanishes on the line at infinity
     (`../../JC2D-branches_a_b_c_unified/reviews/two_dicritical/base_point_at_infinity_check.py`).
   - It also has an affine base point once the target is translated so that 0 is a value. An automorphism needs no
     translation.
   - Every base point carries a dicritical. Read literally, the statement would imply the Jacobian conjecture
     outright, and every non-affine automorphism refutes it (`main_statement_check.py` there:
     (x − y², y) and (x, y + x²)).
   - The intended statement is written down in `../RESTATEMENT.md` (Theorem R: at most one dicritical at
     infinity). It is equivalent to the plane Jacobian conjecture, so items 1–5 cannot be assembled into a proof of
     it without proving the conjecture.
1. **What the bridge theorem assumes, and what it covers.** `bridge_collapse` is a theorem about the equations
   `bridgeEq`.
   - **The chart.** The paper's pullback is Sʰ(1, b, b²(a + ã b)) (`check_satellite.py`), the chart at the point
     w₂ = a of the second exceptional curve E₂ over [1:0:0], with w₂ = x/y². Read through it, the theorem rests on
     two premises:
     - (P1) the two dicriticals are the divisors E(a₃), E(a₄) over two distinct **free** points a₃, a₄ of E₂;
     - (P2) every member S of the pencil has ν_{E(a)}(S) ≥ −1 on them.
   - **(P2) is asserted, not derived.** The paper defines m as the degree of the pencil's restriction, and degree 1
     does not force pole order 1. For P = (x − a·y²)·y + 1 and Q = y² + 1, both have ν = −2 on E(a), and P/Q restricts
     to ã/a (`check_satellite.py`, check 7).
   - **ã is not a premise.** Reading ã as an indeterminate is how ν_{E(a)} is computed.
   - **Both centers nonzero** is not a missing argument either: it is where the formula applies.
     - At a = 0 (where E₂ meets the line at infinity, a satellite point) the factor Zᵈ becomes ãᵈb^{3d} instead of
       b^{2d} times a unit.
     - There the threshold 2d − 1 says ν ≥ −(d + 1), a condition that weakens as d grows.
     - The formal witness (x − a₄y², y) of `CenterHypotheses.lean` has degree 2 and satisfies the equations only for
       d ≥ 3. Over a = 0 its P/Q has a pole, and its only dicritical at infinity lies over the free point a₄, where
       P/Q restricts to ã/a₄. It is a one-center configuration, not a bridge.
     - Read as ν ≥ −1 (ord_b S₀ ≥ 3d − 1), the conditions at the centers 0 and 5 leave only constants, d = 2…6.
   - **Scope.** Under (P1) and (P2), **one** such dicritical already forces degree ≤ 2 (`bridge_one_center`). So for
     d ≥ 3 the bridge's hypothesis cannot be met even with one center, and the bridge says nothing about pencils of
     degree ≥ 3.
   - **What the paper does not treat.** Dicriticals over the satellite points a = 0 and a = ∞ of E₂, and over deeper
     satellite points, are covered neither by the bridge nor by the constant-leading-form sketch, which assumes
     centers with u₀ ≠ 0. The automorphism (x + y³, y) has its dicritical at infinity over a = ∞: every member of its
     pencil passes through w₂ = ∞ (`check_satellite.py`).
2. **E₁: Theorem `thm:e1` is false as stated; its intended conclusion is proved here, except for the chart step.**
   - **The order condition.** E₁ is the blow-up of [1:0:0], and ν_{E₁}(x^i y^j) = −i. So ν_{E₁} ≥ −2 means x-degree
     ≤ 2 (`check_e1_index.py`).
   - **The index mix-up.** `e1_solitary.py` indexes its unknowns p[J,K] by X^{d−J−K}Y^J Z^K, that is, by the affine
     monomial x^{d−J−K}y^J. The paper's proof, `e1_keller_search.py` and `E1Obstruction.lean` read p[J,K] as x^J y^K,
     which turns the condition into "total degree ≥ 2". At d = 4 both sets have 12 monomials, which hid the mix-up.
   - **The counterexample** (`thm_e1_false`).
     - P = (x + y²)² + y and Q = P + x + y² satisfy the paper's definition of the open subset (ν_{E₁} = −2, and each
       restriction C(t₁) = t₁² of exact degree 2), and [P,Q] = −1.
     - E₁ is not dicritical for them (P/Q restricts to 1).
     - So the definition "both restrictions of exact degree 2" does not capture an m = 2 dicritical, and the paper's
       proof argues about the wrong monomials.
   - **The intended conclusion holds, for every m: E₁ is never dicritical for a Keller map.**
     - The algebraic step is proved: `e1_lead_proportional`, and `jac2_eq_zero_of_natDegree_zero` for x-degree 0.
     - The chart step is executed, not formalized: on E₁, P/Q restricts to A(1/t₁)/D(1/t₁) when both x-degrees equal
       n, and to 0 or ∞ otherwise (`check_e1_index.py`, check 5).
     - A linear change of coordinates keeps the Keller condition, so the same holds over every point at infinity.
3. **m ≥ 2 on E_k, k ≥ 2** (Proposition `prop:constant-form`). The paper gives a proof sketch only; nothing is
   formalized. The sketch also assumes centers with u₀ ≠ 0, so it covers free points only.
4. **The adjacent m = 1 case.** The paper computes it at d = 3 only; there is no argument for other degrees.
5. **The assembly into the main theorem.** It needs items 0–4.

See `../README.md` ("Status") and the review of 2026-10-12, §5 and §9.

## Files

| File | Contents |
|---|---|
| `TwoDicritical/BlockRank.lean` | from the handoff of 2026-10-12 (CAIC), unchanged; sha256 `9cae6bea…` |
| `TwoDicritical/E1Obstruction.lean` | from the same handoff, unchanged; sha256 `30e38fe1…`; a true lemma about a set of monomials that is not the E₁ condition |
| `TwoDicritical/BridgeCollapse.lean` | the bridge collapse from the explicit equations |
| `TwoDicritical/CenterHypotheses.lean` | the center hypotheses of `bridge_collapse` cannot be dropped from the formal theorem (witness x − c·y²); its header explains why the center at 0 is not a geometric bridge |
| `TwoDicritical/OneCenter.lean` | one center already forces degree ≤ 2; with d the exact degree, the center at 0 leaves nothing of degree d ≥ 3 |
| `TwoDicritical/E1Keller.lean` | the counterexample to Theorem `thm:e1`, and the corrected E₁ step |
| `TwoDicritical/Axioms.lean` | `#print axioms` for the 21 theorems |
| `build.sh`, `logs/build.log` | build and audit |
| `check_bridgeEq.py`, `logs/check_bridgeEq.log` | the definition `bridgeEq` against the paper's pullback |
| `check_center_nonzero.py`, `logs/check_center_nonzero.log` | the nullspace of the pullback formula's equations with a center at 0, with equal centers, and (control) with distinct nonzero centers, d = 2…6 |
| `check_satellite.py`, `logs/check_satellite.log` | the pullback as a chart at a point of E₂; valuations at free points and at a = 0; the witness; the conditions at 0 read as ν ≥ −1; the valuation identity; a dicritical over a = ∞; restriction degree 1 with pole order 2 |
| `check_e1_index.py`, `logs/check_e1_index.log` | the E₁ order condition; the two monomial sets; the counterexample; the top x-coefficient of the Jacobian; the restriction to E₁ |
