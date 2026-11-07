# Explicit maximal minor — branch (c), Macaulay matrix at W = 24 (Leg H, Step 3)

**CLAIM:** The 3199 × 3199 pivot block M_S of the branch-(c) Macaulay matrix
M₂₄ is named explicitly below (all 3199 row indices with monomial labels,
all 3199 column indices with (generator, multiplier) labels), and its
determinant is nonzero at both filed primes, each value computed by two
independent routes that agree.
**STATUS:** IDENTIFICATION COMPLETE (computation, not a Lean proof).
This leg produces an identification, not a kernel proof. The §6.3(a)
demand is met in its index-and-nonvanishing parts; its K₅-value part is
NOT met as literally worded (see §5) — whether the delivered form
satisfies §6.3(a) is Brandon's judgement call, not this leg's.

**Date:** 2026-11-06 (extraction + determinants run 2026-11-07 ~00:26–00:44 UTC
/ 2026-11-06 18:26–18:44 CST on lean-build-3). **Holder:** legH.
**Grade:** this is a computational identification (HLRE: exact-arithmetic
certificate data, two independent implementations at each prime — I1 on
the shared matrix construction). It does not change any Lean grade.

## 1. The §6.3(a) requirement (quoted exactly)

Phase 3 protocol §1, triage cell 6.3 (record audit §6.3a):

> "exact-arithmetic certificate — explicit nonzero maximal minor, with row
> and column indices, of the branch-(c) Macaulay matrix over K₅, rebuilt by
> someone outside the project"

Record audit §6.3a verdict before this leg: "OPEN — NOT FOUND as demanded.
No filed Lean file, log, script, or paper states an explicit nonzero maximal
minor of the branch-(c) Macaulay matrix over K₅ with row and column indices
(and no determinant value is filed anywhere)."

Rank lemma (combined paper, Lemma `bc:lem:rank`, ll. 1345–1353):

> "Let A = ℤ_(p)[w]/(R), free of rank 5 over ℤ_(p), embedding in K₅. Let
> φ: A → 𝔽_p, w ↦ w₀, with R(w₀) ≡ 0 (mod p). Let M be the weighted
> Macaulay matrix of the chart generators at fixed weight W … If φ(M) has
> full row rank N, then M has full row rank over K₅."
> "Proof. Some N × N minor satisfies det φ(M_S) = φ(det M_S) ≠ 0. Hence
> det M_S ≠ 0 in A ⊂ K₅, and M_S is invertible over the field K₅."

K₅ existential lemma (branch_c/GUIDE.md §5.9, l. 531): "Some N × N minor
has det φ(M_S) = φ(det M_S) ≠ 0." — no minor named. This leg names it.

## 2. The matrix

M = M₂₄, the weighted Macaulay matrix of the six chart generators
(Ψ, Φ₁, Φ₂, Θ₁, Θ₂, Θ₃) at weight W = 24, on the chart T₂ = 1, S₂ = κ,
at a root w₀ of R = w⁵ − w⁴ + 3w³ + 3w² + 26.

- Dimensions: 3199 rows × 6054 columns; 239,154 nonzero entries.
- Columns: (n, m) for n ∈ {Psi, Phi1, Phi2, Theta1, Theta2, Theta3} and
  monomials m in (t, s, r, u, q) with wdeg(m) ≤ 24 − wt(F_n),
  weights (1, 2, 3, 3, 4), wt = (5, 6, 6, 7, 7, 7). Per-generator column
  counts: Psi 1308, Phi1 1071, Phi2 1071, Theta1 868, Theta2 868,
  Theta3 868.
- Rows: the monomials of the K₅-supports of the products m·F_n, plus the
  monomial 1; each row is a 5-tuple of exponents in (t, s, r, u, q).
- Field: entries in K₅ = ℚ[w]/(R); the filed computations reduce at
  φ: w ↦ w₀ mod p, at two primes:
  - p = 32003, w₀ = 11147 (matrix sha16 of (rows, cols, entries)
    `69569983b45a6478`, `logs/build_matrix.log`);
  - p = 1000003, w₀ = 806739 (matrix rebuilt on lean-build-3 in this leg,
    sha16 of (rows, cols, entries) `4ce659455ea3df65`,
    `vm_out/build_p1000003.log`; two generator derivations agree).
- Construction: `branch_c/rank_lemma_check/build_matrix.py` from the v3.1
  bundle chart code (`step3b_rank_lift.py`, `step1/lowerc_chart.py`).
  All in-project checks share this one matrix construction (I1).

## 3. The minor — row set

The minor is maximal: N = 3199 = number of rows, so the row set is ALL
rows, indices 0–3198 in filed order.

- Row i (0-based) is labelled by the monomial 5-tuple `rows[i]`
  (exponents in (t, s, r, u, q)).
- Full list: `vm_out/out/rows.json` (3199 entries, all distinct).
  sha256(repr(rows))[:16] = `80fed24d2a885918` — identical for the
  matrix pkl (`inv_work_M.pkl`, verified on lean-build-3) and the filed
  Lean data (`grade_a/lean/GradeA/A2Data.lean`, `rowsList`, parsed
  locally from the text file).
- First three rows: (0,1,1,0,0), (0,0,1,0,0), (2,0,1,0,0).
  Last three rows: (0,8,0,0,2), (0,10,0,0,1), (0,12,0,0,0).
  Row 19 is (0,0,0,0,0) = the monomial 1.

## 4. The minor — column set

The column set is the 3199 pivot columns selected by FLINT RREF
(`make_inverse.py`, first pivot in each row), filed as `piv` in
`INVERSE.pkl`.

- Source file: `~/workspace/research/2D-Jacobian-Conjecture-Workspace/JC2D-branches_a_b_c_unified/branch_c/rank_lemma_check/INVERSE.pkl`
  — 82,788,865 bytes; file sha256
  `1af9b3c8a4d32a2a611b6b3958c6e3770e282d5d351b423af45ea304a44189fe`
  (verified locally and on lean-build-3; the 79 MB pkl is NOT copied
  into any repo — referenced by path + sha256 only).
- Extraction: restricted unpickler (allowed classes: builtins containers
  + numpy ndarray/dtype reconstruct only; the pickle uses STACK_GLOBAL
  opcodes — 474,540 opcodes total, PROTO … STOP — and loaded cleanly
  under the restriction, so no other code could execute). Script:
  `extract_minor.py`; log `vm_out/extract.log`; exit 0.
- Verification against the filed record (all match):
  - sha256(repr(piv))[:16] = `00e40995b010f30a` — equals the hash printed
    by `make_inverse.py:30–31` and `logs/make_inverse.log:1`.
    (NOTE: this is the hash of the pivot *list*, not of the file. The
    Phase 3 report's "sha256 hash 00e40995b010f30a" is this list hash.)
  - sha256(C.tobytes())[:16] = `6cffa0100555b7b8` — equals the filed C hash.
  - C = M_S⁻¹ mod 32003: 9,151,397 / 10,233,601 nonzero = 89.42%
    (filed: 89.4%); M_S: 105,807 nonzeros, column supports 22–52,
    row supports 1–102 (filed log values reproduced).
- Column ordinals (0-based into the 6054 columns): full list
  `vm_out/out/piv.json` (3199 entries, strictly increasing, distinct).
  piv_min = 0, piv_max = 5307. First ten: 0, 1, 2, 3, 4, 5, 6, 7, 8, 9.
  Last ten: 5298, 5299, 5300, 5301, 5302, 5303, 5304, 5305, 5306, 5307.
  Columns 5308–6053 are never pivots; 2,108 ordinals below 5307 are
  non-pivots.
- Column labels: pivot column jj is (generator, multiplier monomial),
  full list `vm_out/out/pivcols.json` (3199 entries). It was verified on
  lean-build-3 that `pivcols[jj] == cols[piv[jj]]` for every jj, against
  `inv_work_M.pkl` (p = 32003, w₀ = 11147, W = 24, 3199 rows, 6054
  cols; cols sha16 `3e4797dd478be218`), and the same label match was
  verified against the freshly rebuilt p = 1000003 matrix (§6).
  First three: (Psi,(0,0,0,0,0)), (Psi,(0,0,0,0,1)), (Psi,(0,0,0,0,2)).
  Last three: (Theta3,(0,3,0,0,0)), (Theta3,(0,3,0,0,1)),
  (Theta3,(0,3,0,0,2)).
- Counts by generator (pivot columns / total columns):
  Psi 1308/1308 (ALL Psi columns are pivots), Phi1 731/1071,
  Phi2 522/1071, Theta1 306/868, Theta2 210/868, Theta3 122/868.
- Sparse entries of M_S: full list `vm_out/out/colv.json`
  (`colv[jj]` = [(row, value mod 32003), …] for pivot-block column jj;
  105,807 entries). The same data is filed in Lean as
  `grade_a/lean/GradeA/A1Data*.lean` (`colDataNat`), kernel-checked
  there as 6,398 packed identities (C·M_S ≡ I mod 32003, axioms
  `[propext]`).

## 5. The minor — value (nonzero, two routes at each prime)

| Prime | FLINT `nmod_mat.det` | NumPy modular LU (independent code) | det(C) (FLINT) | Agreement |
|---|---|---|---|---|
| p = 32003, w₀ = 11147 | det(M_S) = **29127** (4.6 s) | det(M_S) = **29127** (193.4 s) | 9069; 9069 × 29127 ≡ 1 (mod 32003) | YES |
| p = 1000003, w₀ = 806739 | det(M_S) = **262898** (4.8 s) | det(M_S) = **262898** (201.4 s) | — (C filed only mod 32003) | YES |

- Script: `det_minor.py`; logs `vm_out/det_p32003.log`,
  `vm_out/det_p1000003.log`; JSONs `vm_out/out/det_p32003.json`,
  `vm_out/out/det_p1000003.json`; exit code 0 in both runs
  (the script asserts route agreement and aborts on disagreement).
- Both determinants are nonzero mod p, so M_S is invertible mod p at
  both primes and the 3199 × 6054 matrix has full row rank 3199 at both
  primes. The p = 32003 value is further corroborated by the filed
  Lean-kernel check C·M_S ≡ I (6,398 identities, `[propext]`) and by
  the FLINT C·M_S = I check in `logs/make_inverse.log`.
- Over K₅: det(M_S) ≠ 0 follows by the rank lemma's own proof
  (Lemma `bc:lem:rank`): det φ(M_S) = φ(det M_S) ≠ 0 at p = 32003
  (indeed at both primes), hence det M_S ≠ 0 in A ⊂ K₅ and M_S is
  invertible over K₅.

## 6. §6.3(a) check

| §6.3(a) element | Status after this leg |
|---|---|
| Explicit maximal minor with row indices | DONE — all 3199 rows, §3 + `rows.json`. |
| Explicit maximal minor with column indices | DONE — all 3199 pivot ordinals + labels, §4 + `piv.json` + `pivcols.json`. |
| Nonzero (determinant value) | DONE mod p at two primes — 29127 mod 32003, 262898 mod 1000003, each by two independent routes that agree (§5). Nonvanishing over K₅ follows by the rank-lemma lift. |
| Determinant value as an explicit element of K₅ | NOT DONE — no value in K₅ itself is exhibited. Computing det(M_S) ∈ K₅ exactly (5 rational coefficients of the reduced determinant) has no feasible route here: it would need the 3199 × 3199 determinant over ℚ[w]/(R), i.e. multimodular reconstruction over ~10⁴ primes at ~5 s of FLINT det each plus rational reconstruction of unknown height. This leg does NOT claim it. |
| Rebuilt by someone outside the project | NOT DONE — that is §6.3(b), not this leg; the I3 spec is still awaiting an outside party (GUIDE.md §11). All checks in this leg are I1 (same matrix construction, independent code). |

**Verdict on §6.3(a) as literally worded:** PARTIAL → narrowed. What was
missing as a *named artifact* (row/column indices + determinant values)
now exists as filed text/JSON; what remains missing is the determinant
value *as an element of K₅* and the outside rebuild. Whether the
delivered form — explicit indices + nonzero modular determinants + the
rank-lemma lift to K₅ — satisfies §6.3(a) is **Brandon's judgement call**,
not this leg's. This leg does not decide it.

## 7. What this does NOT establish (scope guards)

- Not a Lean proof: no kernel theorem about a determinant is proved
  here. The minor is an identification from the filed certificate form.
- Not "(72,108) excluded unconditionally" and not JC(2): those still rest
  on GGHV exhaustiveness + the reduction chain.
- Not an outside-project rebuild (§6.3b): the matrix construction is
  shared across all in-project checks (FLINT, NumPy, Lean kernel).
- The K₅ determinant value is not exhibited (see §6).

## 8. Tool versions and verification record

- lean-build-3 (n2-standard-16, us-central1-a): VM status RUNNING
  (gcloud describe, rc 0). Lock legH acquired ~00:19 UTC 2026-11-07,
  released 00:37 UTC after copying results back (single ~25 min
  time-slice; VM left RUNNING, not stopped, per coordinator rule).
- VM Python 3.11.2, python-flint 0.9.0, numpy 2.4.6
  (quoted from the VM: `python 3.11.2 | python-flint 0.9.0 |
  numpy 2.4.6`).
- Extraction: `extract_minor.py`, exit 0, 1.6 s on the VM.
- Determinants: `det_minor.py`, exit 0 both primes; FLINT det ~5 s
  each; NumPy LU 193.4 s (p = 32003), 201.4 s (p = 1000003).
- Matrix rebuild at p = 1000003: `build_matrix.py`, exit 0, 0.7 s;
  two generator derivations agree.
- Local checks (control plane only): file sha256 of INVERSE.pkl
  (`sha256sum`, 1af9b3c8…44189fe) matches on disk and on the VM;
  `piv.json`/`pivcols.json` re-read locally (3199 entries, sorted,
  distinct); `rows.json` parsed from `A2Data.lean` text matches the
  matrix pkl rows sha16 `80fed24d2a885918`.

## 9. Files (scratch, `~/workspace/research/tooling/phase4_legH/`)

- `minor_spec_2026-11-06.md` — this file.
- `extract_minor.py` — restricted-unpickler extraction script.
- `det_minor.py` — two-route determinant script (FLINT + NumPy LU).
- `leg_log_2026-11-06.md` — append-mode leg log (includes the VM-lock
  wait: legC held 22:11–~23:05 UTC, then legB, legE, legF, legG under
  time-slicing; legH acquired ~00:19 UTC 2026-11-07).
- `vm_out/out/piv.json` — 3199 pivot column ordinals.
- `vm_out/out/pivcols.json` — 3199 (generator, multiplier) labels.
- `vm_out/out/rows.json` — 3199 row monomial labels.
- `vm_out/out/colv.json` — sparse entries of M_S mod 32003.
- `vm_out/out/summary.json`, `vm_out/out/det_p32003.json`,
  `vm_out/out/det_p1000003.json`, `vm_out/out/globals.txt` — extraction
  summary, determinant results, pickle opcode scan.
- `vm_out/extract.log`, `vm_out/det_p32003.log`,
  `vm_out/det_p1000003.log`, `vm_out/build_p1000003.log`,
  `vm_out/mcheck.log` — computation logs.
- NOT copied anywhere: the 79 MB `INVERSE.pkl` (referenced by path +
  sha256 only); the extracted `C.npy` (81.8 MB) was deleted after the
  det(C) cross-check was recorded, to avoid duplicating the filed
  content in scratch.
- NO repo commits were made (incorporation waits for the validation gate).

## 10. Open items for the parent / Brandon

1. §6.3(a) judgement call for Brandon: does the delivered form
   (explicit indices + nonzero modular determinants + rank-lemma lift)
   satisfy §6.3(a), or does it require the determinant value as an
   explicit element of K₅? If the latter, the route (multimodular
   reconstruction, ~10⁴ primes) needs to be ordered and resourced
   separately — it is not feasible as a quick follow-on.
2. §6.3(b) outside-project rebuild: still open, untouched by this leg.
3. A Lean formalization of this minor (e.g. `RingHom.map_det` instance
   with the 3199 × 6054 matrix as Lean data) is a separate, un-ordered
   item (combined paper open item (2)).
