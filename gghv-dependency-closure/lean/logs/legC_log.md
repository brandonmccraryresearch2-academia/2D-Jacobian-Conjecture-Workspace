# Leg C (§5 systems, E10–E17) — work log (append mode)
# Programme: GGHV full-proof, Phase 4. Holder: legC. VM: lean-build-3.
# Rules: truth-seeking-frontier v5; sorryAx NOWHERE; axioms recorded exactly.

## 2026-11-06 ~15:32 CST — start
- Read inventory E10–E17 + phase4_map + paper §5 TeX 1399–1813 in full.
- Read existing logs (repo lean/logs/, tooling/logs_gcp_phase3/logs/) and the
  bridge recheck script: invocation = cd <lake project>; LP=$(lake env printenv LEAN_PATH);
  LEAN_PATH="$LP" lean --root="$(dirname "$f")" -o /tmp/out.olean "$f".
  Singular --version < /dev/null (hangs on stdin otherwise).
- VM lock acquired (legC). lean-build-3 was TERMINATED; started.
- VM probe: Singular 4.3.1, SymPy 1.14.0, 62 GB RAM. Lean version check pending.

## 2026-11-06 ~16:30-17:05 CST — Bézout fix, full compile, axioms, phi-shift check
- Bézout (e13_bezout) was the last blocker (2-error full compile: C3_mul_f + bezout).
  C3_mul_f fixed by factored proof via e13_f_factor (moved before it). Bézout fixed
  via probe32: 5 monomial-normalizer helpers (C_mul_X_pow_mul_C, X_pow_mul_C_mul_C,
  C_mul_C_mul_X_pow, C_mul_X_pow, C_mul_X_pow_C; each by `ring` + `<- C_mul`) normalize
  every monomial to X^n * C r; then sub_eq_add_neg + <- mul_neg + <- map_neg, add_assoc +
  <- mul_add/<- mul_sub + <- C_add/<- C_sub, norm_num; `ring_nf` cancels the
  identical-atom opposite-sign pairs (U.f vs V.f' contributions, X^5..X^10); second
  combining pass on the exposed X^1 leftover (HSub form -> <- mul_sub/<- C_sub);
  norm_num; try ring. Key diagnostics (probe33 pp.all, probe35/36 traces): goal is
  HAdd-of-Neg-of-product; `norm_num` pushes negations back out of C and re-commutes
  monomials to C-first, so `<- mul_neg` on C-first terms lands the negation on the
  X-power; `ring_nf` leaves the goal in HSub form. Probe32 rc=0 (15 s); probe34
  (minimal finish) rc=0.
- FULL FILE COMPILE: LEAN_RC=0, 42 s, 0 errors, 0 sorryAx, 90 linter warnings
  (unused simp args only). File: gghv_full_s5_2026-11-06.lean, 836 lines, 39 decls.
  Log: s5_build_5.log. Lean 4.34.0 / Lake 5.0.0 / Mathlib (branches_a_b project).
- AXIOMS RUN: LEAN_RC=0, 42 s, 0 errors, 0 sorryAx. File:
  gghv_full_s5_axioms_2026-11-06.lean (39 `#print axioms` appended). Log: s5_axioms.log.
  Axiom lists (all within permitted triple [propext, Classical.choice, Quot.sound]
  or a subset/zero): triple for most (incl. all E13, e16_principal, e14_d_mem,
  e12_*, e11_*, e10_rescaling, e10_dt_bound, e10_endgame, thm51_conditional);
  [propext, Quot.sound] for e16_cert, e15_arith_neg13, e15_arith_17,
  e15_bound_neg13, e15_bound_17; [propext] for val_pow, e10_clearing;
  NO axioms for pow_ne_zero_of_ne, cor52_conditional. No sorryAx anywhere.
- PHI-SHIFT CHECK (Leg G hypothesis, tool-verified): paper TeX line 1663 defines
  phi(x)=x-D_2 (phi(y)=y); line 1668 asserts shifted D has d_2=0. SymPy 1.14.0
  (lean-build-3, PY_RC=0, ALL_PASS=True), script legG_phi_shift_check.py, log
  legG_phi_shift_check.log: x^2-coeff of D(x-t) = D_2 - 3*t (D monic deg 3, D_3=1,
  TeX 1617); at t=D_2: d_2 = -2*D_2 (NOT 0); at t=D_2/3: d_2 = 0. Paper's own
  phi(x^-1) expansion verified (series + multiply-out). VERDICT: Leg G's hand
  arithmetic CONFIRMED. The paper's line-1663 shift and line-1668 d_2=0 claim are
  mutually inconsistent as written; the consistent shift is t=D_2/3. Same shift +
  assertion recur at TeX 2025/2030 for the (9,27) half. This is a paper slip to
  flag (bears on the OPEN 9-equation derivation, which would need the corrected
  shift); it does NOT touch the kernel E16 elimination (9 eqs => principal eq),
  which does not depend on how d_2 was set to 0.
- VM LOCK: coordinator time-slicing rule received 17:05 CST (lock held since
  22:11:17Z, ~55 min; Legs A/B/G/H timed out waiting). Lock released after the
  phi-shift check run; VM NOT stopped. Per-run acquire/release from here on.
