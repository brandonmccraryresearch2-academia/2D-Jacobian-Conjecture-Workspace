# Manifest — GGHV dependency-closure Singular recomputations (`gghv-dependency-closure/singular/`)

Filed 2026-11-05 as tracked modules of this repository, from the Singular leg
of Phase 1 (completed 2026-11-05 ~07:30 CST on lean-build-3). Every file below
was copied byte-identically from `~/workspace/research/tooling/` (verified with
`cmp` at filing time; SHA-256 prefixes below are the first 16 hex digits — run
`sha256sum` in this directory for the full values). No file was edited in
filing.

## What "recomputed" means here (read before citing anything)

- **Status I1: independent recomputation, NOT kernel proof.** Every item below
  was recomputed in Singular (or SymPy / python-flint, as noted) from the
  data in the Lean files and the paper, independently of Lean's `ring` tactic
  and of the original computation. Agreement between the recomputation and
  the Lean/paper record is evidence at independence level I1; it is not a
  Lean kernel proof and must never be described as one.
- **Tools and versions (all on lean-build-3):** Singular 4.3.1, SymPy 1.14.0,
  python-flint 0.9.0. The `.sing` scripts are Singular; `d1_singular_table_enum_2026-11-05.py`
  is Python (exact integers, with a python-flint primary check);
  `extract_cert_2026-11-05.py` is Python.
- **The five items, and their verdicts:** (i) Parts 11–12 D3 certificate
  identities — agree; (ii) §5/§6 principal-equation eliminations — agree by
  three routes; (iii) §3 numerics — agree; (iv) §2 table — agree; (v) [GGV5]
  enumeration first stage — agree. The logs in `logs/` are the run records;
  each log's verdict is quoted per script below.
- **What was NOT recomputed:** the [GGV5] enumeration completeness claim
  (carried as a premise); the PFL generative use; the family-to-row
  attribution; the derivation of the 9 equations from the C/F/D expansions
  (the elimination shows only: *if* the 9 equations hold, *then* the
  principal equation holds).

## Filed scripts

### `extract_cert_2026-11-05.py` — 2,095 bytes, sha256 `82f05cce8f3856c8`

- **Source:** `~/workspace/research/tooling/extract_cert_2026-11-05.py`.
- **What it does:** extracts the Parts 11–12 D3 certificate identities
  verbatim from the Lean files, independently of Lean's `ring` tactic, so
  that the Singular certificate check (scripts `d1_singular_cert_s5/s6`)
  tests the identities as written, not Lean's rendering of them.
- **Verdict:** the extracted identities are the ones checked; see the
  `cert_s5`/`cert_s6` entries.

### `d1_singular_cert_s5_2026-11-05.sing` — 3,281 bytes, sha256 `06593958dea06ecb`

- **Source:** `~/workspace/research/tooling/d1_singular_cert_s5_2026-11-05.sing`.
- **What it recomputes:** the §5 (Part 11) D3 certificate identities.
- **Verdict (log `logs/d1_singular_2026-11-05_cert_s5.log`):**
  `CERT_DIFF = 0`, `CERT_IS_ZERO = 1` — the identities hold exactly.

### `d1_singular_cert_s6_2026-11-05.sing` — 3,038 bytes, sha256 `b783a3d7a986b04a`

- **Source:** `~/workspace/research/tooling/d1_singular_cert_s6_2026-11-05.sing`.
- **What it recomputes:** the §6 (Part 12) D3 certificate identities.
- **Verdict (log `logs/d1_singular_2026-11-05_cert_s6.log`):**
  `CERT_DIFF = 0`, `CERT_IS_ZERO = 1` — the identities hold exactly.

### `d1_singular_elim_s5_2026-11-05.sing` — 2,640 bytes, sha256 `2a755c7b16047eba`

- **Source:** `~/workspace/research/tooling/d1_singular_elim_s5_2026-11-05.sing`.
- **What it recomputes:** the §5 principal-equation elimination, Route A'
  (resultants).
- **Verdict (log `logs/d1_singular_2026-11-05_elim_s5.log`):** the resultant
  is `Res = (−19683/64) · target · dm1³`, where the target is the §5
  principal equation and `dm1` is the first denominator factor; `reduce = 0`
  at `k = 0`. The SymPy re-run agrees (log
  `logs/d1_singular_2026-11-05_sympy_s5_rerun.log`, CHECK PASSED; quotient
  `−27/(64·dm1³)`). The arithmetic in full: `19683 = 3⁹`, so
  `−19683/64 = −(3⁹)/(2⁶)`; the quotient `−27/(64·dm1³)` is `−(3³)/(2⁶·dm1³)`.

### `d1_singular_elim_s6_2026-11-05.sing` — 3,019 bytes, sha256 `dc5ec44e80197219`

- **Source:** `~/workspace/research/tooling/d1_singular_elim_s6_2026-11-05.sing`.
- **What it recomputes:** the §6 principal-equation elimination, Route A'
  (resultants).
- **Verdict (log `logs/d1_singular_2026-11-05_elim_s6.log`):** the resultant
  is `Res = (−19683/64) · target · dm1³`, `reduce = 0` at `k = 0`, exactly as
  in §5. The SymPy re-run agrees (log
  `logs/d1_singular_2026-11-05_sympy_s6_rerun.log`, CHECK PASSED; quotient
  `−27/(64·dm1³)`).

### `d1_singular_groebner_s5_2026-11-05.sing` — 1,540 bytes, sha256 `d85c1e5a09d7f558`

- **Source:** `~/workspace/research/tooling/d1_singular_groebner_s5_2026-11-05.sing`.
- **What it recomputes:** the §5 elimination, Route B — Gröbner `eliminate`
  of the full 9-equation ideal.
- **Verdict (log `logs/d1_singular_2026-11-05_groebner_s5.log`):** the
  eliminated ideal is **principal** with generator **exactly** the target:
  `ELIM_IDEAL_SIZE 1`, `reduce(target, E) = 0`. This is stronger than the
  resultant check: it shows the 9 equations jointly force the principal
  equation, with no extra component.

### `d1_singular_groebner_s6_2026-11-05.sing` — 1,527 bytes, sha256 `b55b6f80c4543cd8`

- **Source:** `~/workspace/research/tooling/d1_singular_groebner_s6_2026-11-05.sing`.
- **What it recomputes:** the §6 elimination, Route B — Gröbner `eliminate`
  of the full 9-equation ideal.
- **Verdict (log `logs/d1_singular_2026-11-05_groebner_s6.log`):**
  `ELIM_IDEAL_SIZE 1`, `reduce(target, E) = 0` — principal, generator
  exactly the target, as in §5.

### `d1_singular_numerics_2026-11-05.sing` — 1,562 bytes, sha256 `e21d4878206d3a6c`

- **Source:** `~/workspace/research/tooling/d1_singular_numerics_2026-11-05.sing`.
- **What it recomputes:** the §3 numerics and the §4 degree/gcd arithmetic.
- **Verdict (log `logs/d1_singular_2026-11-05_numerics.log`), in full:**
  `I_M = 4`, `I_m = 5`; the §3-120 identities hold; `4 + gcd(8, 4) = 8`,
  because `gcd(8, 4) = 4` and `4 + 4 = 8`; the Part 4 bounds are 75, 76,
  78; the degrees are 27 and 27; `gcd(72, 108) = 36`, because
  `72 = 36 × 2` and `108 = 36 × 3` with `gcd(2, 3) = 1`; the reduced ratio
  is `(72/36, 108/36) = (2, 3)`. The python-flint cross-check passes.

### `d1_singular_pllc_2026-11-05.sing` — 1,304 bytes, sha256 `f30cff2806f3da37`

- **Source:** `~/workspace/research/tooling/d1_singular_pllc_2026-11-05.sing`.
- **What it recomputes:** the [GGV5] enumeration first stage (the
  piecewise-linear-candidate filter).
- **Verdict (log `logs/d1_singular_2026-11-05_pllc.log`):**
  `pllcFilter(8, 3) = 1` (the (8, 3) candidate is in),
  `pllcFilter(8, 4) = 0` (the (8, 4) candidate is out); `pllcDir` is
  `(1, −2)` and `(1, −1)`; 18 candidates with `a ≤ 9`; the Python table
  enumeration agrees.

### `d1_singular_pllc_fix_2026-11-05.sing` — 702 bytes, sha256 `1bc3ab2ef90899af`

- **Source:** `~/workspace/research/tooling/d1_singular_pllc_fix_2026-11-05.sing`.
- **What it is:** a fix to the `pllc` script. Singular has no `list == list`
  comparison, so list membership is re-checked component-wise. One script
  fix, recorded here so the fix is not mistaken for a second computation.
- **Verdict (log `logs/d1_singular_2026-11-05_pllc_fix.log`):** the
  component-wise membership check agrees with the Python enumeration.

### `d1_singular_table_enum_2026-11-05.py` — 4,456 bytes, sha256 `05d4b98f4b80372a`

- **Source:** `~/workspace/research/tooling/d1_singular_table_enum_2026-11-05.py`.
- **What it recomputes:** the §2 table — all 10 rows, in Python exact
  integer arithmetic, with a python-flint primary check.
- **Verdict (log `logs/d1_singular_2026-11-05_table_enum.log`):** OVERALL ALL
  PASS. Maximum degrees per row are `[64, 112, 75, 75, 84, 96, 108, 120, 99,
  108]`; there are 5 red rows; the survivors are `[(108, 72), (66, 99),
  (72, 108)]`; (72, 108) arises from two rows. The arithmetic in full for
  the survivor degrees: `gcd(72, 108) = 36` (since `72 = 36 × 2` and
  `108 = 36 × 3`), and the reduced pair is `(2, 3)`.

## Run logs (`singular/logs/`, 12 files)

- `d1_singular_2026-11-05_cert_s5.log` (37 bytes),
  `d1_singular_2026-11-05_cert_s6.log` (37 bytes) — certificate identities.
- `d1_singular_2026-11-05_elim_s5.log` (668 bytes),
  `d1_singular_2026-11-05_elim_s6.log` (800 bytes) — resultant eliminations.
- `d1_singular_2026-11-05_groebner_s5.log` (153 bytes),
  `d1_singular_2026-11-05_groebner_s6.log` (141 bytes) — Gröbner eliminations.
- `d1_singular_2026-11-05_numerics.log` (906 bytes) — §3/§4 numerics.
- `d1_singular_2026-11-05_pllc.log` (1,084 bytes),
  `d1_singular_2026-11-05_pllc_fix.log` (76 bytes) — enumeration filter.
- `d1_singular_2026-11-05_sympy_s5_rerun.log` (1,181 bytes),
  `d1_singular_2026-11-05_sympy_s6_rerun.log` (1,203 bytes) — the SymPy
  second-tool re-runs of the §5/§6 eliminations (SymPy 1.14.0).
- `d1_singular_2026-11-05_table_enum.log` (2,662 bytes) — the §2 table.

## The bundle

The same 23 files (11 scripts + 12 logs) were bundled on 2026-11-05 as
`~/workspace/zips/d1-singular-leg-2026-11-05.zip` (17,280 bytes, sha256
`3bdeaa9ddd5698f32a734eb60568bda030e9d834c67f1d3b0ea60e9a00c54341`). The zip
is **not** copied into this repository — the individual files above are the
tracked copies, and the zip's contents are byte-identical to them (verified
by listing the archive against the filed files at filing time).

## Scope guard

Nothing here is a kernel proof, and nothing here discharges the [GGV5]
enumeration completeness claim, the 9 equations' derivation from the C/F/D
expansions, or the family-to-row attribution. Those remain carried premises
of the dependency-closure programme. The recomputation status is I1 throughout.

---

## Phase 4 — full-GGHV second-tool recomputations (filed 2026-11-07)

Leg G (the Singular/SymPy runner) plus the second-tool files of Legs
C/D/E. All runs on lean-build-3. Toolchain: Singular 4.3.1 (Debian
1:4.3.1-p3+ds-2), Python 3.11.2, SymPy 1.14.0, python-flint 0.9.0
(measured at run time; from `/usr/bin/python3` system Python).
Status throughout is I1 (independent recomputation), **not** kernel
proof. Nothing here discharges the [GGV5] enumeration completeness
claim, the 9 equations' derivation from the C/F/D expansions, or the
family-to-row attribution. The definitive verdict record is
`gghv_full_assembly_inventory.md`; the validation is
`validation_g1/g1_validation_report_2026-11-07.md` (CONDITIONAL GO).
Every file below was copied byte-identically from
`~/workspace/research/tooling/` (verified with `cmp` at filing time).
No file was edited in filing. Sizes + SHA-256 (first 16 hex digits).

### Leg G scripts (`singular/`)

| File | Bytes | sha256 | What it recomputes |
|---|---|---|---|
| `gghv_full_singular_table_s5_2026-11-06.sing` | 3,085 | `8de43bb60aac9f35` | §2 table + §3 numerics (R21) |
| `gghv_full_singular_ggv5_families_2026-11-06.sing` | 7,180 | `8dd19cb93d770811` | [GGV5] generative step + attribution (R22) |
| `gghv_full_singular_ggv5_families_py_2026-11-06.py` | 4,348 | `b7e0aa8a2541449e` | Python/flint cross-check of the above |
| `gghv_full_singular_e13_ode_2026-11-06.sing` | 2,955 | `24414d99164b8fb9` | E13 ODE / separability (R23, E13) |
| `gghv_full_singular_e13_sympy_2026-11-06.py` | 4,048 | `7f053f407426b8bd` | SymPy cross-check of the above |
| `gghv_full_singular_nine_eq_2026-11-06.sing` | 9,491 | `6a99e8de2c4f3a5b` | 9-equation D-scaling / displays (R23) |
| `gghv_full_singular_nine_eq_sympy_2026-11-06.py` | 7,422 | `fac3203b12940d0b` | SymPy cross-check of the above |
| `run_legG_driver.sh` | 1,547 | `f783d0aed2541c2e` | Leg G run driver (1st invocation) |
| `run_legG_driver2.sh` | 1,073 | `1c5301022f356b3c` | Leg G run driver (2nd invocation) |

**Verdicts (R21–R23, from `singular/logs/`):** R21 I1 PASS (BAD_ROWS
= 0; all 10 rows' maxima [64,112,75,75,84,96,108,120,99,108];
survivors (108,72),(66,99),(72,108); GCD_72_108 = 36). R22 I1 PASS
(generative step + attribution; all 7 family checks = 1; Python
cross-check OVERALL: ALL PASS). R23 I1 PASS on the computational
steps (D-scaling identities, displayed (D̃²)/(D̃³) expansions,
inverse coefficients, φ-shift coefficient; Laurent bracket
[x⁶y², (1/2)y⁻¹x⁻⁴] = x, SymPy rc=0 OVERALL ALL PASS).
**Delimitation (R19):** the Main-algorithm chain enumeration and the
completeness claim (listed families/chains are ALL) are NOT computable
in Singular — they rest on the [GGV5] C++ program + SQL database,
which are not available as a Singular computation.
**Logged defects (not hidden):** the runner's driver-1 invocation
bug (`Singular < script < /dev/null` made the second redirect win, so
Singular read empty stdin — all four first Singular runs were
banner-only and VOID; re-ran correctly as `timeout 600 Singular <
script`; the reported verdicts are from the correct re-runs). Two
Singular script bugs REPORTED, not fixed: (a) §5 D-scaling nonzero
because the script uses two symbols for C₃ (`c3x` in the C-list, `c3`
as scaling base) — SymPy (single C₃) gives 0 for all 12, mathematics
decided; (b) (D̃²)_{−7}/_{−8} and (D̃³)_{−4} outputs corrupted by
32-bit `int` overflow of 13!/14! in `coeffU`'s `fact`
(13! = 6227020800 → 1932053504; 14! → 1278945280) — use a
bigint/exact division. (D̃²)_{−7} display facts CONFIRMED: TRUE −
DISPLAY = 2d_{−10} exactly (SymPy); the literal "2 d_{−1} 0" term is
identically zero; the filed Gröbner script's corrected form (with
2·dm10) is the true expansion.

### Leg C / Leg D / Leg E second-tool files (`singular/`)

| File | Bytes | sha256 | What it is |
|---|---|---|---|
| `e13_singular_check.sing` | 969 | `33cbfb80c9bb114e` | Leg C E13 Singular check |
| `e13_sympy_check.py` | 2,330 | `c66bca66d9ebdc4b` | Leg C E13 SymPy check |
| `legG_phi_shift_check.py` | 2,175 | `63632ee4e7158999` | φ-shift check (SymPy): x²-coefficient of φ(D) is D₂−3t; at t=D₂ it is −2D₂ (not 0); at t=D₂/3 it is 0 — the paper's stated shift is a genuine slip confined to the shift formula; the 9 equations are the d₂=0 normal form for the corrected shift |
| `lift_s6_extra.sing` | 1,825 | `92ccdd1d85dbb054` | Leg D §6 extra lift attempt — TIMEOUT 600 s (exit 124), inconclusive; its Q4x2 carried a 6/6 transcription error (fixed to 12/12) |
| `lift_s6_square.sing` | 1,409 | `e1b0300eb10550c4` | Leg D §6 square lift attempt — explicit lift() coefficients still NOT obtained (lift is the slow step) |
| `member_s6_extra.sing` | 1,348 | `eff60cb022166e0c` | Leg D §6 extra membership (0.37 s, GB size 200): both extra identities ARE in the 9-equation ideal |
| `member_s6_square.sing` | 758 | `1c54155f07769e29` | Leg D §6 square membership (0.64 s, GB size 591): reduce(T,GJ) ≠ 0, reduce(y²·al¹⁰·T,GJ) ≠ 0, reduce(y⁹·T,GJ) = 0 — T follows up to the nonzero factor y⁹, but no explicit lift coefficients, so hsq stays a named premise |
| `jacobi_check.sing` | 775 | `790eb0465d70d26d` | Leg E R8/R14 Jacobi check: JACOBI = 0, BRACKET_AB = −x²−1, exit 0 |

### Verification logs filed (`singular/logs/`, 17 files)

| File | Bytes | sha256 |
|---|---|---|
| `versions.log` | 4,606 | `9db4c2a29b3e6cd4` |
| `table_s5_singular.log` | 2,507 | `34ce963d9787e641` |
| `table_filed_py.log` | 2,662 | `486a9c87609ca69c` |
| `ggv5_families_singular.log` | 3,601 | `2c20747353f9e858` |
| `ggv5_families_py.log` | 2,775 | `ad58f3bbd8dcf526` |
| `e13_singular.log` | 1,527 | `5c0f550a48c57f49` |
| `e13_sympy.log` | 25,927 | `3b81fa57a6060862` |
| `nine_eq_singular.log` | 5,920 | `ca430b4c3c331432` |
| `nine_eq_sympy.log` | 3,638 | `defbe6e60be0714c` |
| `legG_log.md` | 12,271 | `aeef4aaf2ccd8bbf` |
| `e13_second_tool_check.log` | 1,660 | `94542439da985ec1` |
| `legG_phi_shift_check.log` | 383 | `ec7692d9ab709ea1` |
| `cert_s6_rerun.log` | 37 | `8af3b094b930aa9f` |
| `elim_s6_rerun.log` | 800 | `2d0951b4529de497` |
| `groebner_s6_rerun.log` | 141 | `5962036555953f00` |
| `member_extra.log` | 65 | `787a7d2c9b2f1117` |
| `member_square.log` | 882 | `39108279584599ca` |

Notes: E13 SymPy tail shows the dsolve Piecewise mess + OVERALL:
FAILURES PRESENT (as reported in the inventory) — the filed SymPy
script exits rc=1 with DECOMPOSED defects (2× gcd Poly-domain
artifacts, value is 1; 1× bracket FAIL is a script error in BOTH
scripts, factor 2 — the paper's identity is x⁷C₃² = 2[x³C₃, x⁵f₁]
and the correct identities PASS in both tools; 3× dsolve FAILs are a
SymPy 1.14.0 limitation). Leg D `cert_s6_rerun.log` (37 bytes):
CERT_DIFF = 0, CERT_IS_ZERO = 1; `elim_s6_rerun.log`: Res =
(−19683/64)·target·dm1³, reduce = 0 at k=0; `groebner_s6_rerun.log`:
Gröbner reduce(dm1·target, E) = 0.

### Scope guard (Phase 4)

Nothing here is a kernel proof, and nothing here discharges the [GGV5]
enumeration completeness claim, the 9 equations' derivation from the
C/F/D expansions, or the family-to-row attribution. Those remain
carried premises of the dependency-closure programme. The recomputation
status is I1 throughout.
