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
