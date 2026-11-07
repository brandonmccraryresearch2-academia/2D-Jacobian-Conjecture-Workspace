# Laurent fragment log — GGHV full-proof programme (Leg: laurent)
## 2026-11-06 ~19:55 CST — start
- Read: paper TeX §5 `calculo de C` (TeX 1416–1526) and §6 `calculo de C para 7` (TeX 1828–1932); Leg C `gghv_full_s5_2026-11-06.lean`; Leg D `gghv_full_s6_2026-11-06.lean`; inventory E11/E19/E20/E23; phase4_map §18.
- Ambient types (verified against TeX, NOT the task's shorthand):
  - §5 E11: C, F ∈ K[y, C₃⁻¹]((x⁻¹)), C₃ = y⁸(y+1). Coefficient ring is the LOCALIZATION at C₃, not K[y,y⁻¹].
  - §6 E19: C, F ∈ K[y,y⁻¹]((x⁻¹)). Coefficient ring is Laurent polynomials in y.
  - Items (1)–(4) in both: (1) P=C², Q=C³+α₂C²+α₁C+α₀+α₋₁C⁻¹+F; (2) ℓ_{1,0}(C)=x³C₃ (§5) / x³y (§6); (3) v_{-1,1}(C)=6 (§5) / v_{2,1}(C)=7 (§6, paper says 6 — slip, correct value 7); (4) v_{3,-1}(C)=1 (§5) / v_{1,-1}(C)=2 (§6).
  - F-construction in both: via [GGV1] Prop 1.13 + Prop 2.1 + [GGV3] §1; v_{1,0}(F)=−4.
- KEY FINDING (preliminary, to be kernel-checked): Leg D's `ValAxioms` (gghv_full_s6, §1) states `mul : ∀ a b, w (a*b) = w a + w b` UNCONDITIONALLY. Taking a=0 gives w b = 0 for all b, so the ONLY instance is w ≡ 0. The `add` axiom is likewise inconsistent with any valuation taking a negative value (a + (−a) = 0 forces w 0 ≤ w a < 0 while `zero` forces w 0 = 0). Hence Leg D's abstract bound-step lemmas (e19_bound_step_21/_1m1, e19_finite_bounds) can NEVER be instantiated with the intended non-trivial valuations v_{2,1}, v_{1,-1}. The fragment must supply a CORRECTED axiom structure (nonzero guards) and re-proved bound steps. This will be proved as a kernel lemma `valAxioms_forces_zero`.

## 2026-11-06 ~20:40 CST — Mathlib API probe (lean-build-3, Lean 4.34.0)
- Mathlib LaurentSeries R = R⟦ℤ⟧ (HahnSeries), variable t = x⁻¹. EXISTS: coeff, coeff_mul (support-restricted antidiagonal), single, C, ext, order/orderTop, order_mul/neg/single/C, addVal, hasseDeriv + hasseDeriv_coeff, ofPowerSeries, coeff_coe_powerSeries, PowerSeries.mk/coeff_mk/coeff_mul/ext, isUnit_iff_constantCoeff, invOfUnit; LaurentPolynomial: T, isUnit_T, degree : WithBot ℤ (= coeff.support.max), degree_T/C/C_mul_T, T_add/T_sub/T_mul, invert (T ↦ T⁻¹ algebra equiv); RatFunc.intDegree + intDegree_mul/add_le/zero/one/X/neg/inv/C; Field (LaurentSeries (RatFunc K)).
- MISSING (verified by #check errors / grep): LaurentPolynomial.degree_mul; LaurentSeries.X; PowerSeries.isUnit_iff (name is isUnit_iff_constantCoeff); RatFunc.derivative; LaurentPolynomial.derivative; Leibniz rule for hasseDeriv/derivative on HahnSeries (Binomial.lean is about binomial series, not Leibniz); any (ρ,σ)-valuation; two-variable Laurent series. `pow_ne_zero` in 4.34 resolves to an IsReduced version — used own induction lemma instead.
- Verification pattern that works: cd overlay_c project; `lake env lean /tmp/<file>.lean` (the task's `--root=/tmp` form does NOT find Mathlib; the legs' real pattern is `LP=$(lake env printenv LEAN_PATH); LEAN_PATH=$LP lean --root=...`).

## 2026-11-06 ~20:55 CST — Part 1 VERIFIED (lean-build-3)
- File: gghv_full_laurent_2026-11-06.lean (§§1–3a). FULL_RC=0, 0 errors, 3 linter warnings only, ~6 s.
- Axioms run AX_RC=0: 17 theorems; all on permitted-triple subsets ([propext, Quot.sound], [propext], triple, or zero axioms); sorryAx count 0.
- §1 KERNEL: ValAxiomsOrig.forces_zero ([propext, Quot.sound]), nonneg, no_nontrivial — Leg D's ValAxioms admits only w ≡ 0.
- §2 KERNEL: ValCore + inv_unit/pow/sum_le/inv/div/zpow + valcore_bound_step_21/_1m1 + valcore_finite_bounds + valcore_b0_21 (all triple or subset).
- §3a KERNEL: valCore_ratFunc_intDegree (RatFunc.intDegree satisfies ValCore), w21Rat_y, w21Rat_two_mul_y.
- Fixes during build: own pow_ne_zero_of_ne (IsReduced issue); `Int.ofNat_eq_natCast` (deprecation); `RatFunc.X ≠ 0` via intDegree (simp failed); dropped `omit` (docstring conflict — accepted linter warnings instead).

## 2026-11-06 ~21:30 CST — §3b VERIFIED (lean-build-3, Lean 4.34.0)
- §3b (LP max/min-degree valuations) FULL_RC=0, 0 errors, 33 linter warnings (deprecations + unused section vars only), ~6 s.
- Axioms run AX_RC=0: 12 theorems (lpMaxDeg_mul, lpMinDeg_mul, lpMaxDeg_add_le, lpMinDeg_add_le, lpMaxDeg_neg, lpMinDeg_neg, valCore_lpMaxDeg, valCore_lpMinDeg, lpMaxDeg_T, lpMinDeg_T, lpMaxDeg_C, lpMinDeg_C) ALL on the permitted triple [propext, Classical.choice, Quot.sound]; sorryAx count 0.
- §3b is KERNEL: Mathlib 4.34.0 has `LaurentPolynomial.degree` (= coeff.support.max, definitionally) but NO `degree_mul`; both degree laws proved from `AddMonoidAlgebra.coeff_mul` (double Finsupp.sum) + `coeff_mul_add_of_uniqueAdd` (unique top/bottom pair). `ValCore (LaurentPolynomial K) lpMaxDeg` and `ValCore ... lpMinDeg` are kernel instances.
- API fixes found: `UniqueAdd` binders are `∀ a' b', a' ∈ s → b' ∈ t → ...` (elements first); `Finsupp.support_single (a) (h : b ≠ 0)` replaces deprecated `support_single_ne_zero`; `f.coeff = 0 → f = 0` bridge via `AddMonoidAlgebra.coeffEquiv.injective` (coeff is NOT defeq to identity at the type level); support rewrites must precede `dif_pos` (dependent-proof motive failure); `C` ambiguous between LaurentPolynomial/HahnSeries/PowerSeries in `map_one C` — qualify; `neg_min` does not exist, `max_neg_neg` does; `single_eq_C_mul_T` is forward (single = C * T).

## 2026-11-06 ~22:05 CST — §4 (chunk 1) VERIFIED (lean-build-3, Lean 4.34.0)
- §4 chunk 1 (rec_step, powser_sq, recSeq/recDiag, exists_sqrt_series, h2y_s6, e19_sqrt_s6) FULL_RC=0, 0 errors, ~6 s.
- Axioms run AX_RC=0: all 11 theorems on the permitted triple [propext, Classical.choice, Quot.sound]; sorryAx count 0.
- §4 is KERNEL for (a): `exists_sqrt_series` gives C with C² = Pser, C.coeff (k-3) = recDiag k, C.coeff (-3) = u0, generic over any CommRing with explicit inv2u0. `e19_sqrt_s6` is the §6 instance (u0 = T 1, inv2u0 = C(1/2)*T(-1)).
- API fixes found: `Function.update_same`/`update_noteq` are now `Function.update_self`/`Function.update_of_ne`; antidiagonal lemma is `Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk` (the non-`_mk` form fails higher-order unification on `?f ij.1 ij.2`); `Nat.le_induction` via `induction n, hmn using Nat.le_induction`; `single_mul_single` is FORWARD (single = C*T was the earlier confusion, here single*single = single(sum)); `calc` with universe-poly K hit an Eq.{1} vs Eq.{u_1+1} elaboration mismatch — replaced by `mul_mul_mul_comm` + rw chains (probe9-verified); `rw [show A = B]` can fail to match a goal LHS that LOOKS identical (hidden instance elaboration differences, esp. around `1/2` in K) — prefer generic-pattern rewrites (`mul_mul_mul_comm`) and in-block `have`s; in `rec_step`, `linear_combination` treats `u 0` and `u0` as different atoms — state the helper with `u0`.

## 2026-11-06 ~22:30 CST — §4 (chunk 2) VERIFIED (lean-build-3, Lean 4.34.0)
- §4 chunk 2 (lp_two_ne_zero, e19_existence_bounds_s6) FULL_RC=0, 0 errors, ~8 s.
- Axioms run AX_RC=0: both on the permitted triple [propext, Classical.choice, Quot.sound]; sorryAx count 0.
- §4 is now fully KERNEL for (a)+(b): `e19_existence_bounds_s6` gives C with C² = P, C.coeff (k-3) = recDiag k, C.coeff (-3) = y, AND the (b_k)/(c_k) bounds lpMaxDeg (C.coeff (n-3)) ≤ 1+2n, lpMinDeg (C.coeff (n-3)) ≤ n-1, from `valcore_finite_bounds` at the two kernel LP valuations with the explicit unit d = (2y)⁻¹. The P-bounds hP21/hP1m1 stay hypotheses (paper Newton-polygon data).
- Fixes found: norm_num does NOT prove (2 : LaurentPolynomial K) ≠ 0 — proved via degree_C/degree_zero (`lp_two_ne_zero`); `exact_mod_cast` fails on un-beta-reduced lambda equalities (use `have` + omega); `set`-introduced `q m` is reducibly defeq to Pcoef (6-↑m), so a trailing rw can close the goal early ("No goals"); shadowing `hC3` broke the refine (renamed to `hCfun3`).

## 2026-11-06 ~23:05 CST — §5 (bracket) VERIFIED (lean-build-3, Lean 4.34.0)
- §5 FULL_RC=0, 0 errors, ~8 s. Axioms run AX_RC=0: all 20 theorems
  (mono_coeff, lpDeriv_zero/add/C_mul_T/T/C, C_mul_T_mul_C_mul_T, C_mul_T_smul,
  derivY_coeff, hasseDeriv_single_one, derivX_mono, derivY_mono, smul_single,
  derivX_add, derivY_add, bracket_add_left/right, bracket_mono, e23_instance,
  e23_series_reduction) on the permitted triple [propext, Classical.choice,
  Quot.sound]; sorryAx count 0.
- §5 verdict: KERNEL for the monomial bracket (`bracket_mono`: [xⁿyʲ, xᶜyᵈ] =
  (nd−jc)xⁿ⁺ᶜ⁻¹yʲ⁺ᵈ⁻¹), the E23 instance (`e23_instance`: [x⁶y², (1/2)y⁻¹x⁻⁴] = x),
  bracket additivity, lpDeriv, derivX/derivY on monomials. CONDITIONAL: the
  series reduction (`e23_series_reduction`) on the bracket-degree bound `hdeg`
  (the bracket of x⁶y² with a series of x-degree ≤ −4 has no x-coefficient above
  degree 1) — needs the Leibniz rule for `LaurentSeries.derivative`, absent from
  Mathlib 4.34.0.
- Lean 4.34.0 / Mathlib API lessons (recorded, all probed on the VM):
  * `-f x` parses as `(-f) x` (negation on the FUNCTION), not `-(f x)`: a negated
    `HahnSeries.single` must be written `-(single a r)` with the application inside
    the parens. This was the cause of the `neg_mul` "pattern not found" failures.
  * `neg_mul`/`mul_neg` are effectively unusable on `LaurentSeries (LP K)`:
    `rw` fails to match, and term-mode `neg_mul _ _` TIMES OUT at whnf
    (200000 heartbeats) on instance unification. Avoided entirely: the sign is
    absorbed into the coefficient via `HahnSeries.single_neg` (derivX_mono now
    states coefficient `(n:K)`, no outer negation).
  * `rw [h]` FAILS ("pattern not found", even though the pattern is visibly present)
    when h's RHS contains h's LHS pattern (e.g. `T j = C 1 * T j`). Use calc +
    congr + simp instead (lpDeriv_T, lpDeriv_C).
  * A statement `lpDeriv 0 = 0` leaves K ambiguous (stuck `Field ?m` typeclass
    error at the `:`); ascribe the type: `lpDeriv (0 : LaurentPolynomial K) = 0`.
  * `HahnSeries.coeff_single`'s `ite` uses `Classical.propDecidable`, while a
    user-written `if` uses `instDecidableEq`: prove `mono_coeff` by by_cases + simp,
    and in derivY_mono rewrite `if_pos`/`if_neg` TWICE (once per ite instance).
  * `Set.IsPWO.mono` takes the IsPWO FIRST, then the subset.
  * `hasseDeriv_single`'s coefficient is a ℤ-smul (`Ring.choose n 1 • c` with
    `Ring.choose` at ℤ); bridge with `← Int.cast_smul_eq_zsmul K`.
  * Names that do NOT exist in 4.34.0: `Finsupp.sum_zero`, `add_left_eq_self`,
    `zsmul_eq_smul_cast`, `HahnSeries.smul_single`, `HahnSeries.coeff_mk`,
    `HahnSeries.hasseDeriv_C`, `LaurentSeries.coeff_single_mul` (it is
    `HahnSeries.coeff_single_mul`).
  * `Int.cast_smul_eq_zsmul (R) (n) (b) : (↑n : R) • b = n • b` exists.

## 2026-11-06 ~23:40 CST — §6 (F-construction) VERIFIED (lean-build-3, Lean 4.34.0)
- §6 FULL_RC=0, 0 errors, ~9 s. Axioms run AX_RC=0: all 9 theorems
  (coeff_ofPowerSeries_neg, exists_sqrt_series, e19_sqrt_s6,
  e19_existence_bounds_s6, v10_zero, valCore_v10, v10_of_coeff, exists_F,
  v10_C_s6) on the permitted triple [propext, Classical.choice, Quot.sound];
  sorryAx count 0. The §4 amendment (negative-coefficient conjunct
  `∀ m < -3, C.coeff m = 0` in exists_sqrt_series / e19_sqrt_s6 /
  e19_existence_bounds_s6) re-verified with it.
- §6 verdict: KERNEL for `v10` (the (1,0)-valuation `-(order)`, generic over any
  CommRing with no zero divisors) satisfying `ValCore` (`valCore_v10`), for
  `v10_of_coeff` (v10 C = 3 from the leading coefficient), and for `v10_C_s6`
  (the §6 series C has v10 C = 3). CONDITIONAL: `exists_F` on the named bundle
  `GGV1Inputs` (cancel + leading at coefficient level = the [GGV3] §1 α-choice
  + [GGV1] Prop 1.13/2.1 content). The bracket step `[C^k, C²] = 0` is a named
  hypothesis `bracket_pow_C` (NOT proved: needs the Leibniz rule for
  `LaurentSeries.derivative`, absent from Mathlib 4.34.0).
- Mathlib API record (probed on the VM):
  * `HahnSeries.order : R⟦Γ⟧ → Γ` is Γ-valued (NOT WithBot); `order 0 = 0`
    (by definition, via `dite`); `order_mul` (needs NoZeroDivisors),
    `order_neg`, `order_one`, `order_C : (C r).order = 0` (no nonzero side
    condition), `order_le_of_coeff_ne_zero`, `coeff_eq_zero_of_lt_order`,
    `coeff_order_eq_zero`, `order_eq_orderTop_of_ne_zero : ↑x.order = x.orderTop`,
    `min_orderTop_le_orderTop_add` (needs only AddMonoid R), `addVal` (full
    `AddValuation`, needs IsDomain R).
  * `WithTop.coe_min : ↑(min a b) = min ↑a ↑b`; `WithTop.coe_le_coe`;
    `max_neg_neg : max (-a) (-b) = -min a b` (use FORWARD, not ←).
  * `rw [h]` fails when h's RHS contains its LHS pattern (again: `T j = C 1 * T j`).
  * `rw [iff]` on a `≠` goal fails (the `Eq` is hidden inside `Ne`): rewrite the
    hypothesis instead (`intro h0; rw [...] at h0`).
  * `α₋₁` (U+208B subscript minus) is NOT a valid Lean identifier character;
    renamed to `αm1`.
  * `HahnSeries.coeff_C` and `RatFunc.coe` do NOT exist; `HahnSeries.map`
    (coefficientwise map via a ZeroHom) exists; `Int.cast_smul_eq_zsmul` exists.
  * `IsDomain (LaurentPolynomial K)` and `Field (LaurentSeries (RatFunc K))`
    instances exist (the probe's `dependsOnNoncomputable` errors were only the
    `example`-as-definition quirk, not missing instances).
  * `ofPowerSeries` goes through `embDomain`; negative coefficients vanish via
    `embDomain_notin_image_support`.

## 2026-11-06 ~23:50 CST — §7 (tilde) + §8 (assembly interface), written

- Probe 21 (`probe21.lean`): `HahnSeries.isUnit_iff : IsUnit x ↔ IsUnit x.leadingCoeff`
  EXISTS (needs IsDomain R); `LaurentSeries.isUnit_iff` does NOT exist.
  `leadingCoeff` is defined via `orderTop.untop`; `WithTop.untop_eq_iff (h : a ≠ ⊤) :
  a.untop h = b ↔ a = ↑b` and `WithTop.untop_coe` exist (probe22, PROBE_RC=0).
  `mul_inv_cancel₀ : a ≠ 0 → a * a⁻¹ = 1` exists.
- §7 `exists_tilde`: generic over `LaurentSeries (RatFunc K)`; applies
  `exists_sqrt_series` to the tilde coefficients, `Ct⁻¹` is the field inverse,
  `Ft` defined as the difference. Sharper claim (Ft v10 = -4, lam' formula) NOT proved.
- §8: `isUnit_of_coeff` (KERNEL, via `HahnSeries.isUnit_iff` + leadingCoeff);
  `laurent_series_discharge_s6` (KERNEL, repackages `e19_existence_bounds_s6` +
  `v10_of_coeff` + a leading-term conjunct `(C - mono 3 1 1).coeff m = 0` for m ≤ -3);
  `tilde_Ptcoef` (KERNEL) + `tilde_discharge` (KERNEL modulo Ptcoef construction);
  `bracket_reduction_discharge` (CONDITIONAL on `hdeg`);
  `f_discharge` (CONDITIONAL on `GGV1Inputs`, Fpoly unfolded);
  `FpolyLp` + `GGV1InputsLp` + `exists_F_lp` (CONDITIONAL on `GGV1InputsLp` + unit u);
  `f_discharge_lp_s6` (CONDITIONAL on `GGV1InputsLp` as a ∀-hypothesis over the
  constructed C and u).

## 2026-11-06 ~23:52 CST — §7+§8 compile, first attempt

- Run: lean-build-3, `.../overlay_c`, `lake env lean /tmp/laurent.lean`.
  FULL_RC=1, 7 errors, ~10 s.
  * `isUnit_of_coeff` hlc: `rw [← order_eq_orderTop_of_ne_zero ...]` fails with
    "motive is not type correct" — `hx : C.orderTop ≠ ⊤` depends on `C.orderTop`,
    so rewriting `C.orderTop` inside `(orderTop C).untop hx` is ill-typed.
    FIX: prove `htop' : C.orderTop = ↑(-3)` (goal has no dependent proof), then
    `htop : C.orderTop.untop hx = -3 := (WithTop.untop_eq_iff hx).mpr htop'`, then
    `rw [← coeff_untop_eq_leadingCoeff hx, htop]`.
  * `tilde_Ptcoef` (2 errors): goal is the un-beta-reduced lambda application
    `(fun n => ...) n = 0`, so `rw [if_neg ...]` finds no `if` pattern.
    FIX: `show Pcoef n + (if n = 0 then ... else 0) = 0` first.
  * `GGV1InputsLp` (3 errors, incl. `exists_F_lp` unknown in `f_discharge_lp_s6`):
    the structure takes `C Q u α₂ α₁ α₀ αm1` (7 parameters) but I wrote
    `GGV1InputsLp C u α₂ ...` (dropped Q) — the elaborator coerced `u` into the
    Q slot and expected `α₂ : ...ˣ`. FIX: `GGV1InputsLp C Q u α₂ α₁ α₀ αm1`
    in both `exists_F_lp` and `f_discharge_lp_s6`.
  * One more fix in the same round: `WithTop.untop_eq_iff.mpr` is an unknown
    constant — `untop_eq_iff` takes the proof `h` explicitly, so it is
    `(WithTop.untop_eq_iff hx).mpr htop'`.

## 2026-11-06 ~23:55 CST — §7+§8 VERIFIED

- Run: lean-build-3, FULL_RC=0, 0 errors, ~10 s (1705 lines).
- Axioms run (§7+§8, 9 theorems): AX_RC=0, all on the permitted triple
  [propext, Classical.choice, Quot.sound], sorryAx count 0:
  `exists_tilde`, `isUnit_of_coeff`, `laurent_series_discharge_s6`,
  `tilde_Ptcoef`, `tilde_discharge`, `bracket_reduction_discharge`,
  `f_discharge`, `exists_F_lp`, `f_discharge_lp_s6`.
- Full-file axioms audit (87 theorems, `#print axioms` appended): first attempt
  AX_FULL_RC=1, 7 errors — only my generated lines: `forces_zero`/`zero`/
  `nonneg`/`no_nontrivial` live in namespace `ValAxiomsOrig` and `inv_unit`/
  `pow`/`sum_le` in namespace `ValCore`. Fixed the names, re-ran:
  AX_FULL_RC=0 (confirmed by a final re-run below), 86 "depends on axioms"
  lines + `pow_ne_zero_of_ne` (no axioms) = 87, sorryAx count 0, ERRORS=0.
  Non-triple lists are all subsets: `ValAxiomsOrig.*` [propext, Quot.sound],
  `ValCore.inv_unit` [propext, Quot.sound], `ValCore.pow` [propext],
  `valcore_b0_21` [propext], `pow_ne_zero_of_ne` [].
- Second-tool check (Python/Fractions, run on lean-build-3):
  `recursion_check.py` — the §4 recursion with q = [1,2,3,5,7,11], u0 = 1
  gives u = [1, 1, 1, 3/2, 3/2, 5/2] (matches hand computation) and the
  convolution identity (u*u)_n = q_n for n = 0..5: PASS.
- Final full-file run after header update: FINAL_FULL_RC=0, 0 errors, 1705 lines.
- Header verdict list updated: §6 (was PENDING) → PARTIAL (KERNEL v10 parts +
  CONDITIONAL exists_F); §7 → KERNEL (modulo Ptcoef data); §8 → KERNEL/CONDITIONAL
  per theorem. File header STATUS now records the full-file verification.
- §7 verdict: KERNEL for `exists_tilde` (modulo the Ptcoef data hypotheses).
- §8 verdicts: KERNEL `isUnit_of_coeff`, `laurent_series_discharge_s6`,
  `tilde_Ptcoef`, `tilde_discharge`; CONDITIONAL `bracket_reduction_discharge`
  (on `hdeg`), `f_discharge` (on `GGV1Inputs`), `exists_F_lp` /
  `f_discharge_lp_s6` (on `GGV1InputsLp` + unit).
- Mathlib API record (probed on the VM):
  * `HahnSeries.isUnit_iff : IsUnit x ↔ IsUnit x.leadingCoeff` (IsDomain R);
    `LaurentSeries.isUnit_iff` does NOT exist.
  * `WithTop.untop_eq_iff (h : a ≠ ⊤) : a.untop h = b ↔ a = ↑b` — the proof
    argument is explicit, so use `(WithTop.untop_eq_iff hx).mpr`, not
    `WithTop.untop_eq_iff.mpr`.
  * `rw` cannot rewrite a term on which a hypothesis in scope depends
    (motive not type correct): prove the dependent equality via an iff whose
    RHS mentions only the bare term.
  * A `refine` goal `(fun n => ...) n = 0` is not beta-reduced for `rw`: use
    `show` (defeq) before rewriting, or `simp` (which beta-reduces).
  * Structure applications: count the parameters — dropping one silently
    coerces the next argument into the wrong slot (here `u` coerced into `Q`).
- VM/lock state: lock RELEASED by `laurent` after the final run; VM lean-build-3
  left RUNNING (stop decision in the final report — assembly may still need it;
  check lock status before stopping).
