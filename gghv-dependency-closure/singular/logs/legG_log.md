# Leg G log — Singular recomputation (R21–R23 + E13), Phase 4
**CLAIM:** Scratch log for Leg G. Verdicts are I1 (independent recomputation),
NEVER kernel proof. **STATUS:** started 2026-11-06 ~15:35 CST.

## Scope
- E13 ODE second-tool check (Leg C needs it): f_1 formula, ODE, separability,
  y(y+1)|f, deg f = 6.
- R21: §2 table in Singular (previously Python/flint only) + §3 numerics re-run.
- R22: [GGV5] enumeration generative use (GetmnFamilies) + family-to-row
  attribution; delimit what is not computable in Singular.
- R23: 9-equation derivation — computational steps only; delimit Lean-only parts.
- NO Lean proofs. NO repo commits. VM via vm_lock.sh; do NOT stop VM on release.

## Runs
(appended as they land)

## 2026-11-06 ~17:05 CST — BLOCKED on the VM lock (no runs yet)
- All 7 scripts written and self-reviewed (see below); NONE run yet — every
  verdict below is NOT RUN, not PASS/FAIL.
- VM lock: legC has held it continuously. Acquire attempts by legG:
  (1) vm_lock.sh acquire, 1800 s timeout -> TIMEOUT, holder legC;
  (2) vm_lock.sh acquire, 1800 s timeout -> TIMEOUT, holder legC;
  (3) tight mkdir loop (2 s poll), 1500 s timeout -> TIMEOUT, holder legC;
  (4) one earlier tight loop (~22:36 UTC) was lost in an apparent runtime
  restart (session vanished from process.list; lock still held by legC).
  Total waiting ~85 min. Lock inspected 22:38 UTC: held by legC, same lock
  instance since 22:11:17Z (age 1609 s then) — legC is alive and cycling, not
  stale (age << 3 h); break-stale NOT applicable and NOT attempted.
- Per the task's BLOCKED rule (state precisely why; do not stall), reporting
  back with scripts ready to run. Resume: acquire lock, scp
  ~/workspace/research/tooling/phase4_legG/ to lean-build-3 /tmp/legG, run
  the 7 scripts (Singular < /dev/null; python3 with the conda env), capture
  logs to the same dir, release lock (do NOT stop the VM).
- UNVERIFIED HYPOTHESIS (hand computation only, NOT tool-checked): with
  phi(x) = x - t, the x^2-coefficient of phi(D) is D_2 - 3t, so the paper's
  stated shift t = D_2 gives d_2 = -2 D_2, not 0; t = D_2/3 gives 0. This
  must be confirmed by the R23 script run before being reported as a finding.
  Do NOT cite it as verified.

## Scripts written (NOT RUN)
- gghv_full_singular_e13_ode_2026-11-06.sing (E13 ODE + bracket steps)
- gghv_full_singular_e13_sympy_2026-11-06.py (E13 SymPy cross-check + dsolve)
- gghv_full_singular_table_s5_2026-11-06.sing (R21 §2 table in Singular + §3 re-run)
- gghv_full_singular_ggv5_families_2026-11-06.sing (R22 GetmnFamilies + attribution)
- gghv_full_singular_ggv5_families_py_2026-11-06.py (R22 Python/flint cross-check)
- gghv_full_singular_nine_eq_2026-11-06.sing (R23 scalings + expansions + shift)
- gghv_full_singular_nine_eq_sympy_2026-11-06.py (R23 SymPy cross-check)
- Self-review fixes applied before any run: D_3 = 1 (no negative exponents);
  §6 C_3 = y (CY[15] = yy); 1/E valid only mod u^5 (u^5 coeff dm2 - 2 d0 d1).
- Cross-check for R21: re-run filed d1_singular_table_enum_2026-11-05.py and
  compare with the Singular table output.
- Filed-script cross-references: R23 (D~^2)_{-7} corrected form (+2 dm10) is
  the form already used in d1_singular_groebner_s5 (D2_7 includes 2*dm10).

## 2026-11-07 ~00:11–00:25 UTC (2026-11-06 ~18:11–18:25 CST) — RUNS COMPLETE (legG-runner)
- Lock: acquired as `legG-runner` 2026-11-07 00:11:50 UTC after waiting through
  legC -> legB -> legA -> legE (44 min hold) -> legF rotations. First acquire
  attempt (23:06 UTC, 7200 s) was lost in an apparent runtime restart
  (~23:53 UTC, session vanished from process.list); re-acquired 23:54 UTC.
  Lock held ~14 min for the runs. VM lean-build-3 was already RUNNING
  (us-central1-a); no wake needed. VM NOT stopped on release.
- Tool versions MEASURED on lean-build-3 at run time (logs/versions.log):
  Singular 4.3.1 (Debian 1:4.3.1-p3+ds-2); Python 3.11.2; SymPy 1.14.0;
  python-flint 0.9.0 — all exactly as in the Phase 1 record. NOTE: these came
  from /usr/bin/python3 (system Python); the conda-env path
  $HOME/miniconda3/envs/jacobian-conjecture-2d/bin/python3 does NOT exist on
  the VM (driver fell back to `python3`). The Phase 1 toolchain evidently
  lives in the system Python on lean-build-3.
- Logs: logs/versions.log, logs/e13_singular.log, logs/e13_sympy.log,
  logs/table_s5_singular.log, logs/table_filed_py.log,
  logs/ggv5_families_singular.log, logs/ggv5_families_py.log,
  logs/nine_eq_singular.log, logs/nine_eq_sympy.log. Drivers:
  run_legG_driver.sh (driver 1), run_legG_driver2.sh (corrected Singular
  re-run). NO script file was modified; only invocations changed (see below).

### Driver-1 invocation bug (mine, logged verbatim) — Singular runs VOID, re-run
- Driver 1 invoked the Singular scripts as `Singular < script < /dev/null`.
  In bash the LAST redirection wins, so Singular read empty stdin: all four
  Singular logs were banner-only (397 bytes), rc=0, scripts NEVER executed.
  Driver 2 re-ran all four as `timeout 600 Singular < script` (stdin = the
  script file; each script ends with `quit;`): all rc=0, real output.
  The void banner-only logs were OVERWRITTEN in logs/ by the real runs
  (void versions not preserved — they contained only the banner).

### E13 — I1 PASS on the mathematical content; script rc=1 (SymPy) with defects decomposed
- Singular (rc=0): ODE_DIFF = 0 (both forms), DEG_F1 = 15, DEG_C3 = 9,
  F1_MINUS_C3_F = 0, DEG_F = 6, F_MINUS_Y_YPLUS1_G = 0, DEG_G = 4,
  G_AT_0 = -1/26, G_AT_MINUS1 = -1/2, GCD_F_FP = 1, GCD_G_GP = 1,
  GCD_F1_F1P = y^9+y^8 (f1's multiple roots are exactly the y^9(y+1)^2
  factor, as the script's own comment anticipates),
  BRACKET2_MINUS_2X10C3CUBED = 0, X7C3SQ_MINUS_2BR = 0.
- SymPy (rc=1, 6 FAIL lines of 27 checks; the 21 PASS lines include ODE
  form 1, ODE form 2, deg f1/f/C3/g, f1-C3*f, f-y(y+1)g, g(0)=-1/26,
  g(-1)=-1/2, discriminant(g)=43046721/210999880000 != 0, g 4 distinct
  roots, f 6 distinct roots, [x^6 C3^2, 2 x^5 f1] = 2 x^10 C3^3,
  x^7 C3^2 = 2 [x^3 C3, x^5 f1]):
  (i) 2x gcd FAILs are Poly-domain comparison artifacts: got
  Poly(1, y, domain='QQ'), want Poly(1, y, domain='ZZ') — the gcd VALUE
  is 1 in both; separability content PASSES (confirmed by Singular
  gcd = 1 and by discriminant != 0 + 6 distinct numeric roots).
  (ii) 1x bracket FAIL is a SCRIPT error in BOTH scripts (factor 2):
  the scripts compare [x^3 C3, x^5 f1] directly to
  x^7(6 C3 f1' - 10 C3' f1), but the paper's identity is
  x^7 C3^2 = 2[x^3 C3, x^5 f1] = x^7(6 C3 f1' - 10 C3' f1), i.e. the
  6/10 form is 2x the bracket. The logged difference is exactly -br
  (-x^7*y^18/2 - x^7*y^17 - x^7*y^16/2 = -x^7 y^16 (y+1)^2 / 2), and
  the correct identities x^7 C3^2 = 2 br and [x^6 C3^2, 2 x^5 f1] =
  2 x^10 C3^3 PASS in both tools. The paper is right; the check is
  wrong by a factor of 2. NOT fixed (not a syntax error) — reported
  for Leg G / Leg C to correct in the scripts.
  (iii) 3x dsolve FAILs are a SymPy 1.14.0 limitation: dsolve returns a
  Piecewise/zoo/nan mess with unevaluated integrals, not the clean
  C1*y^(40/3)*(y+1)^(5/3) homogeneous form the script expects. So ODE
  UNIQUENESS among polynomials via dsolve is NOT ESTABLISHED by this
  run (not refuted — the direct ODE substitution checks PASS in both
  tools). The E13 f1 formula, degrees, divisibility and separability
  are I1 PASS; the dsolve-uniqueness sub-claim stays open.

### R21 — I1 PASS
- Singular table (rc=0): BAD_ROWS = 0; all 10 rows' maxima match the
  stated values ([64,112,75,75,84,96,108,120,99,108]); survivors
  (108,72), (66,99), (72,108); ROW7 swapped = ROW10; GCD_72_108 = 36;
  ratio (2,3); §3 numerics re-run all as expected (I_M=4, I_m=5,
  4<5, 4+gcd(8,4)=8, bounds 75/76, G-degree 78).
- Filed re-run d1_singular_table_enum_2026-11-05.py (rc=0): OVERALL ALL
  PASS — degree pairs [(48,64),(80,112),(50,75),(75,50),(56,84),(64,96),
  (108,72),(120,80),(66,99),(72,108)] and maxima identical to the
  Singular table output; survivors [(108,72),(66,99),(72,108)] agree.

### R22 — I1 PASS (generative step + attribution; completeness NOT recomputed)
- Singular GetmnFamilies (rc=0): all 7 family checks = 1; sizes exact
  (F1/F2/F9/F17/F22 = 1 family; F3/F4 and F10/F11 corners = 2 each);
  F4 = ((2,1),(3,16),(2,12)), F11 = ((2,0),(2,5),(1,3)) as tabled.
  All 7 attribution rows give the tabled (m,n), gcd 1 and max degree
  (64, 112, 75, 75, 84, 96, 99); chain rows 108 / 120 / 108.
- Python/flint cross-check (rc=0): OVERALL ALL PASS — family lists
  IDENTICAL to Singular on all 9 families; all attribution rows PASS;
  flint spot checks PASS. Delimitation stands: Main-algorithm chain
  enumeration and completeness are NOT recomputed (need the [GGV5]
  program/database or a Lean proof, R19).

### R23 — I1 PASS on the computational steps (two tools jointly); phi-shift hypothesis CONFIRMED
- SymPy (rc=0): OVERALL ALL PASS — §5 D-scaling all 12 identities = 0
  (D^2 k=1..8, D^3 k=1..4); §6 D-scaling all 12 = 0; (D~^2)_{-k} k=1..8
  and (D~^3)_{-j} j=1..4 all = 0 against the displays EXCEPT k=7, where
  TRUE - DISPLAY = 2*dm10 exactly and TRUE - (DISPLAY + 2 dm10) = 0;
  inverse coefficients (D~^{-1})_{-3}=1, _{-4}=0, _{-1}=_{-2}=0,
  1/E coeffs u^2..u^5 = -d1, -d0, d1^2-dm1, 2 d0 d1 - dm2; phi-shift
  checks all PASS (see below); Laurent bracket [x^6 y^2, (1/2) y^{-1}
  x^{-4}] = x PASS.
- Singular (rc=0): §6 D-scaling all 0 (PASS); (D~^2) k=1..6 = 0,
  (D~^3) j=1..3 = 0 (PASS); inverse coeffs u^0..u^4 = 0, U5 difference
  = 0 (PASS, i.e. u^5 coeff = dm2 - 2 d0 d1 as expected); phi-shift:
  DSH_MINUS_FORMULA = 0, X2_COEFF_GENERAL = 0 (x^2-coeff minus
  (D2-3t)), X2_COEFF_AT_T_EQ_D2 = -2*D2, X2_COEFF_AT_T_EQ_D2_OVER_3 = 0;
  monomial bracket = 0 (PASS).
- Singular §5 D-scaling NONZERO — SCRIPT BUG, not a mathematical
  failure: the script uses TWO symbols for C_3 (c3x in the C-list,
  c3 as the scaling base). E.g. k=1 prints 2*c3^13*cm4 - 2*c3^12*c3x*cm4
  = 2 c3^12 cm4 (c3 - c3x), which vanishes on identifying c3 = c3x.
  The SymPy check (single C3 symbol) gives 0 for all 12 §5 identities,
  deciding the mathematics. NOT fixed — reported for script correction.
- Singular (D~^2)_{-7} / _{-8} and (D~^3)_{-4} outputs are CORRUPTED by
  a second script bug: coeffU's `fact` is a 32-bit Singular `int`;
  13! = 6227020800 overflows to 1932053504 (= 1024 x 1886771) and
  14! overflows to 1278945280 (= 10240 x 124897). The printed
  coefficients match the corrupted values EXACTLY (verified locally to
  full precision, e.g. D2M7 non-dm10 terms 8388608/1886771 =
  2*(13!/1932053504 - 1) = 4.446012791165436; dm10 term 12162150/1886771
  = 6.446012791165436 = that + 2). The +2 excess on dm10 is the REAL
  signal (the missing 2 d_{-10} term); the rest is the overflow
  artifact. The SymPy run (exact Python ints) decides the mathematics:
  (D~^2)_{-7} TRUE - DISPLAY = 2 d_{-10} exactly.
- PHI-SHIFT VERDICT — HYPOTHESIS CONFIRMED by BOTH tools: with
  phi(x) = x - t, the x^2-coefficient of phi(D) is D_2 - 3t; the paper's
  stated shift t = D_2 gives d_2 = -2 D_2 (Singular: X2_COEFF_AT_T_EQ_D2
  = -2*D2; SymPy: [PASS] x^2 coeff at t=D2 == -2 D2), NOT 0; the shift
  that gives d_2 = 0 is t = D_2/3 (both tools: 0). So the paper's stated
  shift formula is a genuine slip confined to the shift formula; the
  displayed 9 equations are the equations for the d_2 = 0 normal form,
  i.e. for the CORRECTED shift t = D_2/3. Flagged for Legs C/D (they need
  the corrected shift). The negative-index coefficients d_{-1} = Dm1,
  d_{-2} = Dm2 + t*Dm1, d_{-3} = t^2*Dm1 + 2 t*Dm2 also PASS (SymPy).
- (D~^2)_{-7} DISPLAY FACTS CONFIRMED: the display omits the 2 d_{-10}
  term (TRUE - DISPLAY = 2 d_{-10} exactly, SymPy; consistent with the
  Singular output once the overflow artifact is removed), and the
  literal "2 d_{-1} 0" term in the printed display is identically zero,
  contributing nothing. The filed Groebner script's corrected form
  (with 2*dm10) is the true expansion.
- Delimitations stand (Lean-only): E11/E14/E19/E21 themselves and the
  "phi(Phat), phi(Qhat) in K[x,y] => negative coefficients vanish"
  implication were NOT checked here.
- Lock released by legG-runner after the runs; VM left RUNNING (not stopped).
