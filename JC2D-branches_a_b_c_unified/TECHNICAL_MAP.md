# Technical Map — JC2D Branches (a), (b), (c), Unified

Elimination of the degree-(72,108) candidate of GGHV Proposition 4.3, case (1),
for the two-dimensional Jacobian conjecture, branches (a), (b) and (c).

This document is the exhaustive guide to `JC2D-branches_a_b_c_unified/`: the
mathematics, every component, the symbolic and numerical eliminations branch by
branch, the trust base, and how to reproduce everything.

---

## 1. What this is

GGHV Proposition 4.3 (case (1)) lists the surviving configurations for a
counterexample pair to the planar Jacobian conjecture at degree pair (72,108).
In the repository's formalization they are organized as **branches**:

| Branch | GGHV normal form | Case | Status |
|---|---|---|---|
| (a), (b) | form (2) | degree-(8,28) | **Eliminated** — Lean `main_theorem`, no remaining hypothesis |
| (c) | form (1) | degree-(72,108) | **Eliminated in Lean** — `branch_c_eliminated` (2026-11-04, no hypotheses, standard axioms); the rank computation stands as independent corroboration. The GGHV paper's own proof is now formalized in full in Lean — CONDITIONAL (`gghv-dependency-closure/`) |

Both branches work over

    K₅ = ℚ[w]/(R),   R(w) = w⁵ − w⁴ + 3w³ + 3w² + 26,

R irreducible over ℚ (and mod 109). The Jacobian condition is `[P,Q] = λx²`
with `λ ≠ 0`.

**Scope.** This unified directory is the branch-elimination record for one case
(case (1)) of one proposition (GGHV Prop. 4.3). It is not a proof of the
two-dimensional Jacobian conjecture; it says nothing about the other cases of
Prop. 4.3, and nothing about the reduction from the conjecture to Prop. 4.3
(that reduction is external mathematics). Nothing here has been published,
uploaded, deposited or minted beyond what each branch package already records.

---

## 2. Directory layout

```
JC2D-branches_a_b_c_unified/
├── README.md                      # overview + reading order
├── TECHNICAL_MAP.md               # this file
├── TODO_correspondence_guide.md   # conditional to-do (NOT started)
├── branches_a_b/                  # branch-(a,b) package (v19, revised 2026-10-05; identical copy: /branch_ab_v19/)
│   ├── README.md
│   ├── BUILD_STATUS.md
│   ├── CHECKSUMS.md5 / CHECKSUMS.sha256
│   ├── CHANGES_v18.md / CHANGES_v19.md
│   ├── paper/                     # 34-page paper (33 until 2026-10-06): branch_ab_elimination_v3.tex/.pdf
│   ├── scripts/                   # audit/analysis scripts + README; since 2026-10-05 also
│   │                              #   a816_certificate/, b22_structured/, b26_m5_eliminant/
│   ├── lean/                      # Lean 4 project: proof sources, generators, verify scripts
│   │   ├── Jacobian/ChartProof/   # the 12-module machine-checked proof (111 identities)
│   │   ├── Jacobian/B26/          # m = 3, 5 chart classifications (10 modules, 2026-10-05)
│   │   ├── Jacobian/A816/         # lower-edge rigidity, Corollary 1.2 and Remark 8.8 (2 modules, 2026-10-07)
│   │   └── certgen/chartproof/    # exact generators + independent checks
│   ├── audits/                    # HLRE v5.0 audit + errata
│   ├── correspondence_guide/      # CORRESPONDENCE_GUIDE.md (exists for a,b)
│   ├── figures/                   # paper figures
│   ├── logs/                      # build, axiom, control, regeneration, saturation logs
│   └── verify_v19.sh              # one-command verification
└── branch_c/                      # branch-(c) package in the (a,b) paper format (v3.1)
    ├── README.md                  # format map: (a,b) component -> (c) location
    ├── BUILD_STATUS.md            # build + verification record
    ├── CHECKSUMS.md5 / CHECKSUMS.sha256
    ├── GUIDE.md                   # the comprehensive v3.1 guide (start here for branch c); maintained copy since
    │                              #   2026-10-06 (the frozen v3.1 text is bundle_v3_1/GUIDE.md)
    ├── V3_1_PROVENANCE.md         # provenance of the v3.1 bundle
    ├── rank_lemma_check/          # 2026-10-06: checks of the rank lemma's instance (claim C5): R irreducible,
    │                              #   generators = Lean conditions (exact), an explicit inverse checked by the Lean
    │                              #   kernel, controls; I3_REPLICATION_SPEC.md; feasibility/
    ├── muse_refutation/           # 2026-10-06: Muse char0_cert bundle withdrawn: DEPRECATED_char0_cert.md and a
    │                              #   cleanly building copy of the refutation
    ├── paper/
    │   ├── branch_c_elimination.tex / .pdf   # the 16-page elimination paper (2026-09-30)
    │   ├── README.md                         # paper build + status
    │   └── BRANCH_C_GUIDE.md                 # comprehensive v3.1 reference (paper-equivalent; = GUIDE.md)
    ├── bundle_v3_1/               # the v3.1 bundle, byte-for-byte (manifest-verified)
    │   ├── GUIDE.md / README.txt / PARTS.txt / MANIFEST.sha256
    │   ├── jacobian_lean/         # Lean overlay + generators + certificates
    │   │   ├── Jacobian/BranchC/  # v1/v2 modules, Descent2R (505), T1Zero, Bridge, CondsC
    │   │   ├── certgen_c/         # exact generators (python-flint) + data
    │   │   ├── chart_certificates/# step-1/3/4 scripts + data (rank lift, identities)
    │   │   ├── AxiomsAuditBranchC.lean, BRANCH_C_LEAN_STATUS.md
    │   │   └── verify_branch_c_lean.sh, build_branch_c_lowmem.sh
    │   ├── logs/                  # every build/verify/control log (GUIDE.md §9 index)
    │   ├── diag/                  # procmon.py, guardrun.py, leanprof.sh, t1z_controls.py
    │   ├── profiling/             # Lean profiler findings + test files
    │   ├── muse_refutation/       # the false reduction_lemma axiom proves False
    │   └── v2_carryover/          # v2 audits, controls, checks, unapplied commit proposal
    └── verify_branch_c.sh         # wrapper -> bundle_v3_1/jacobian_lean/verify_branch_c_lean.sh
```

**Why `bundle_v3_1/` is kept intact.** `verify_branch_c_lean.sh` (steps 0–1)
requires `certgen/`, `certgen_c/`, `chart_certificates/` and `Jacobian/` as
siblings under `jacobian_lean/`, with byte-identical regeneration. Reorganizing
the interior would break the verified reproduction chain. The (a,b)-paper *format*
(paper / scripts / lean / audits / logs / checksums / verify) is therefore
provided at the `branch_c/` level — see the format map in `branch_c/README.md` —
while the bundle interior is untouched.

---

## 3. Branches (a) and (b) — elimination

GGHV normal form (2), degree-(8,28) case. Package: `branches_a_b/` (= `branch_ab`, the v19 package, revised
2026-10-05). The identical copy `branch_ab_v19/` at the repository root is the path the Zenodo record cites.

### 3.1 Symbolic elimination (Lean 4)

- `chartClassification_holds`: every solution of the 17-equation normalized chart
  (`ChartClassification L`) is one of the **five K₅-conjugate points** — the m = 7
  case of Proposition 6.1. Kernel-checked, depending only on `propext`,
  `Classical.choice`, `Quot.sound`.
- `BranchAb.main_theorem`: the NewtonNF2 form of Theorem 1.1 **with no remaining
  hypothesis** (v19 concludes `b_{12,24} = 0`; `a_{8,16} = 0` is an independent
  rigidity corollary).
- `lean/Jacobian/A816/` (2026-10-07): `BranchAb.lower_edge_rigidity`, kernel-checked: under the hypotheses of
  Theorem 1.1 every coefficient of P and Q off the top edges vanishes except the constants, so `a_{8,16} = 0`
  (`a816_eq_zero`, Corollary 1.2) and P = P₂ + const, Q = Q₃ + const (Remark 8.8). `main_theorem_lower_edge`
  refutes NewtonNF2 through the vertex (8,16) without using (12,24). The proof reuses the descent up to t = 0
  (Certificate III) and then E₁; it is not independent of the descent.
- `lean/Jacobian/ChartProof/`: the 12-module machine-checked proof — Reflect plus
  11 generated modules, **111 step theorems**.
- `lean/Jacobian/B26/` (2026-10-05): the m = 3 and m = 5 chart classifications over any field of characteristic 0.
  `m3_chart_iff` and `m5_chart_iff` say the system holds iff T(a_{m-1}) = 0 plus explicit back-substitution; the
  squarefree lemmas show T has no repeated root. `lean/Jacobian/B26Count.lean` (2026-10-06) proves the exact counts
  `m3_chart_card` (3) and `m5_chart_card` (10) over any algebraically closed field of characteristic 0.
  `lean/Jacobian/B26Irred.lean` (2026-10-06) proves that both eliminants are irreducible over ℚ
  (`T3poly_irreducible`, `T5poly_irreducible`). The main theorem does not use them.
- `verify_branch_ab_lean.sh`: 66 theorems (44 until 2026-10-05, the 9 B26 theorems, the 2 count theorems, the 2
  irreducibility theorems, the 9 A816 theorems), each using only standard axioms
  (`lean/logs/axioms_verify_script_66.log`).
- Controls: 14/14 as expected (3 unmodified ACCEPT, 9 perturbed REJECT, 2 sorry
  copies flagged); for `Jacobian/A816`, `controls_a816.sh`: 9/9 (2 ACCEPT, 6 REJECT, 1 sorry copy flagged).

### 3.2 Numerical elimination (certificates and computation)

- The 34-page paper is organized around **four certificates**, with the 35-minor
  span argument and the characteristic-zero transfer made explicit (v19).
- `scripts/a816_full.sing`: `a_{8,16} = 0` forced (G[1] = 1 once E1 is included).
- `scripts/a816_certificate/` (2026-10-05): the explicit identity $a_{8,16}^2=\sum_k H_k e_k$ over K₅ (76 cofactors,
  3464 terms), checked exactly by Singular and by python-flint, with negative controls (Corollary 1.2). Since
  2026-10-07 the corollary itself is also kernel-checked (§3.1); the certificate stays a second proof, independent of
  the descent, outside Lean.
- `scripts/b22_structured/` (2026-10-05): the c-recursion form of the chart system, validated exactly at the K₅ point.
- `scripts/belyi_count*.py`: the m = 3 / m = 5 Belyi bounds sharp (vdim 3/10,
  irreducible separable eliminants).
- `logs/k5_minor_certificate.json`: machine-readable 35×6 K₅ minor matrix with
  rank-6 certificate.
- 111/111 identities verified over ℤ (`independent_check.py`, ~2 s); saturation
  over ℚ via Singular.

### 3.3 Paper and verification

- `paper/branch_ab_elimination_v3.pdf` (33 pp, XeLaTeX, TeX Live 2026; revised 2026-10-05).
- `verify_v19.sh`: one command. It checks the checksums, runs the scripts, checks the 111/111 identities, builds the
  paper, and since 2026-10-05 also runs the a₈,₁₆ certificate checks, the B26 regeneration and statement checks, and
  the B2.2 validation.
- `correspondence_guide/CORRESPONDENCE_GUIDE.md`: proof elements mapped to their
  Lean formalization (exists for branches (a,b)).
- Published: Zenodo 10.5281/zenodo.23023490 (v19, preprint).

---

## 4. Branch (c) — elimination

GGHV normal form (1), degree-(72,108) candidate. Newton polygons:

    N(P) = conv{(0,0),(1,0),(8,14),(8,16),(0,8)}
    N(Q) = conv{(0,0),(2,1),(12,21),(12,24),(0,12)}

Package: `branch_c/` (v3.1, 2026-09-29). Comprehensive reference:
`branch_c/GUIDE.md` (§1 verdict, §2 the proof bridge by bridge, §3 the five
steps, §5 the computational structures, §5.9 the rank lemma, §9 the log index).

### 4.1 The five steps (as specified; all done)

| Step | Task | Status | Where |
|---|---|---|---|
| 1 | Certify `lower_c`'s ideal, not the pipeline's | **Done.** Exact over K₅ on the slice t₁ = 0 (FLINT, no Singular, 3 controls); modular on the whole chart (𝔽₁₀₁, 𝔽₁₀₀₀₀₀₃, 𝔽_{109⁵}) | `bundle_v3_1/jacobian_lean/chart_certificates/step1/` |
| 2 | Lean lemmas for the E₀, E₋₁, E₋₂ eliminations | **Done in Lean**, kernel-reflected, whole chain E₄…E₋₂ (`Descent2R`, 505 modules). `Bridge`: `DescentClaimC ⇐ ChartEmptyC` | `bundle_v3_1/jacobian_lean/Jacobian/BranchC/Descent2R/`, `CondsC.lean` |
| 3 | Canonical certificate over K₅ | **Not built (measured).** Hadamard bound 4.39 M digits; estimated heights 2.0–2.7 × 10⁵ digits. Replaced by an existence proof (step 4) | `chart_certificates/STEP3_4_CHART.md` §1 |
| 4 | Exact check with FLINT | **Done.** (a) t₁ = 0 certificate, exactly; (b) whole chart: exact finite-field ranks at two primes (FLINT + independent numpy elimination) proving a certificate exists over K₅ (rank lemma); (c) exact identity of the chart generators | `step1/check_certB_lowerc.py`, `step3b_rank_lift.py`, `step3c_chart_identity.py` |
| 5 | Check in Lean, or label | **Stratum t₁ = 0 kernel-checked** (`T1Zero`). **`ChartEmptyC ⇐ ChartEmptyC_T1ne0` in Lean** (`Combine`). `ChartEmptyC_T1ne0` proved **in Lean** 2026-11-04 (`challenge_target`, `GradeA.Bridge`); step 4b now stands as independent corroboration | `Jacobian/BranchC/T1Zero/` |

### 4.2 Symbolic elimination (Lean 4)

All modules built; `verify_branch_c_lean.sh` passes (exit 0); `#print axioms` shows
only `propext`, `Classical.choice`, `Quot.sound`; no `sorry`/`axiom`/`native_decide`.

| Component | Modules | What it proves |
|---|---|---|
| v1/v2 (`Degree19`, `LayerE2`, `LayersGen`, `Edge19`, `OmegaSquare`, `OmegaEdge`, `DescentClaim`, `Descent/**`, `Rank/**`) | 162 | Layer identities, top layer, t₂ ≠ 0, normalization to the chart b_{12,22} = 1 — `DescentClaimC`'s hypotheses (`main_theorem_c_of_claim`) |
| `Descent2R/Facts`, `Vals_*`, layers L4, L3, L2c, L1, L0, Lm1, Lm2 | 505 | The E₄…E₋₂ eliminations by kernel reflection |
| `CondsC` | 1 | The twelve chart conditions |
| `Descent2R/Main` (`chart_descent_refl`) | 1 | Main descent reflection (1243 jobs, 2,298 s) |
| `Descent2R/Bridge` | 1 | `DescentClaimC ⇐ ChartEmptyC` (built after a bug fix, §13) |
| `T1Zero` (`Defs`, `Sq`, `F_*`, `P_*`, `Final`, `Main`) | 14+1 | `chartEmpty_t1_zero`: no common zero on the stratum b_{11,20} = 0; 5 negative controls fail as required |
| `T1Zero/Combine` | 1 | `ChartEmptyC ⇐ ChartEmptyC_T1ne0` — isolates the chart-emptiness premise, now itself proved in Lean (`challenge_target`, 2026-11-04) |

Net Lean theorem (standard axioms only):

    main_theorem_c_of_chartEmpty_T1ne0 :
      ChartEmptyC_T1ne0 L → ¬∃ P Q λ, λ ≠ 0 ∧ NewtonNFc P Q ∧ jac P Q = C λ * X 0 ^ 2

Since 2026-11-04 the premise is itself proved: `branch_c_eliminated`
(`GradeA.Composition`, no hypotheses, standard axioms) states that no Keller
pair with Newton normal form (c) exists over any field of characteristic 0.

### 4.3 Numerical elimination (certificates and rank computations)

- **Step 1** (`chart_certificates/step1/`): `certB_lowerc.json` — exact certificate
  over K₅ on the slice t₁ = 0 (degree 2, 75 K₅-terms, heights ≤ 9,681 digits),
  produced by `certB_lowerc.py` (pivots from mod-p RREF, exact FLINT solve) and
  checked by an independent script (`check_certB_lowerc.py`); controls: perturbed
  coefficient, Θ₃ dropped, the pipeline's generators — all False as required.
  Whole-chart modular certificates: 𝔽₁₀₁ (3,661 terms), 𝔽₁₀₀₀₀₀₃ (3,688 terms),
  𝔽_{109⁵} (102,097 terms; R irreducible mod 109).
- **Step 4b — the rank lemma** (GUIDE.md §5.9): let A = ℤ_(p)[w]/(R), free of rank
  5, φ: A → 𝔽_p with R(w₀) ≡ 0. If φ(M) has full row rank N, then M has full row
  rank over K₅ — some N×N minor has det φ(M_S) = φ(det M_S) ≠ 0, so M_S is
  invertible over K₅. Full row rank is the nonvanishing of a minor, an *open*
  condition, which is why it lifts (mere *consistency* of the Macaulay system does
  not lift — cf. `muse_refutation/`).
  Instance (`step3b_rank_lift.py`, 6.5 min, 0.5 GB): at W = 24 the Macaulay matrix
  is 3199 × 3199 of full row rank mod p = 1000003 (w₀ = 806739) **and** mod
  p = 32003 (w₀ = 11147); FLINT `nmod_mat.rank` and an independent numpy
  elimination agree; planted-zero control drops rank to 3198. Hence
  `ChartEmptyC`, hence `ChartEmptyC_T1ne0`.
  - **Further checks, 2026-10-06** (`branch_c/rank_lemma_check/`, `run.sh`, about 4.5 min). Since 2026-11-04 the link from this arithmetic to `ChartEmptyC_T1ne0` is in Lean (`challenge_target`, `GradeA.Bridge`), so the grade is A; these checks stand as independent corroboration.
    - **R irreducible over ℚ:** FLINT factorization; irreducible mod 67; degree patterns mod 5 and 23.
    - **The generators are the Lean conditions.** `CondsC.lean`, parsed from its text and expanded exactly over K₅,
      equals λₙ · `conds_c.json`[n] for all 12 conditions, with λₙ a positive integer. On the Lean side,
      Ω = o₁(S₂ − κT₂²)² holds exactly.
    - **An explicit inverse C of the W = 24 pivot block mod 32003, checked by the Lean kernel.** Columns are packed
      into natural numbers with 40-bit slots, giving 6398 `decide +kernel` identities. Axioms: `[propext]`. Five
      controls are rejected. It takes about 7 CPU-minutes, at ≤ 1.8 GB per module.
    - **What the kernel check covers.** It checks the arithmetic only. Its meaning, C·M_S ≡ I, follows from a
      digit argument on paper. The matrix construction is shared with `step3b_rank_lift.py`.
    - **Outside replication.** An I3 specification is in `I3_REPLICATION_SPEC.md`.
- **Generators** (`certgen_c/`): `lower_c.py` writes `conds_c.json` (the twelve
  conditions); every generated identity is first checked in Python by exact
  integer arithmetic, and the generator asserts term-by-term equality with the
  conditions Lean derives.

### 4.4 Grades (HLRE)

| Claim | Grade | Basis |
|---|---|---|
| DescentClaimC's hypotheses (layers, top layer, t₂ ≠ 0, normalization) | **A** | Lean (v1/v2) |
| `DescentClaimC ⇐ ChartEmptyC` | **A** | Lean kernel reflection, built, axioms audited |
| Stratum b_{11,20} = 0 empty | **A** | Lean kernel (`T1Zero`), 5 negative controls |
| `ChartEmptyC ⇐ ChartEmptyC_T1ne0` | **A** | Lean (`Combine`) |
| `ChartEmptyC` (whole chart, all char-0 L) | **A** (since 2026-11-04) | Lean (`challenge_target`, `GradeA.Bridge`); the rank lemma + two-prime, two-implementation ranks + input checks now stand as independent corroboration (I1), as do R irreducible, the generators matched exactly to `CondsC.lean`, and a kernel check of an explicit inverse (`branch_c/rank_lemma_check/`) |
| The 6398 packed identities of that kernel check | **A** (identities); **A** (their meaning C·M_S ≡ I mod 32003, since 2026-11-04) | Lean kernel, axioms `[propext]`; the digit argument now in Lean (A1, `GradeA.Bridge`) |
| Canonical K₅ certificate heights | **C** (estimate) | Hadamard bound + extrapolated height estimate |

---

## 5. How the branches relate

- Branches (a)/(b) are GGHV normal form (2); branch (c) is normal form (1). They
  are disjoint cases of the same Prop. 4.3 case-(1) analysis.
- Both eliminations work over the same field K₅ = ℚ[w]/(R),
  R = w⁵ − w⁴ + 3w³ + 3w² + 26, and both exclude a pair with `[P,Q] = λx²`, λ ≠ 0.
- (a,b): the Lean formalization is complete — `main_theorem` has no remaining
  hypothesis. (c): Lean proves everything, including `ChartEmptyC_T1ne0`
  itself (`challenge_target`, 2026-11-04); the rank computation stands as
  independent corroboration.
- The (a,b) Lean project is the *base* the branch-(c) overlay builds on:
  `verify_branch_c_lean.sh` step 0 fingerprints the branch-(a,b) prerequisites
  (`certgen` inputs, 54 Descent E4/E3red/E3 files) before building branch (c).

---

## 6. Trust base

| Layer | Branches (a,b) | Branch (c) |
|---|---|---|
| Lean kernel + Mathlib v4.34.0; axioms `propext`, `Classical.choice`, `Quot.sound` | 44 theorems audited (`logs/chartproof_axioms.log`); 57 since 2026-10-06, with B26, B26Count and B26Irred (`lean/logs/axioms_verify_script_57.log`) | 53 theorems audited (`bundle_v3_1/jacobian_lean/axioms_branch_c.log`) |
| No `sorry` / `axiom` / `native_decide` | `grep`-checked | `verify_branch_c_lean.sh` step 4 |
| Symbolic elimination | ChartProof (111 identities), `independent_check.py` | Descent2R (505 modules), T1Zero, Bridge, Combine |
| Numerical elimination | Four paper certificates; 35-minor span; char-0 transfer; `a816_full.sing` and the explicit a₈,₁₆ certificate (`scripts/a816_certificate/`, two exact checkers) | Step-1 certificates (exact K₅ slice + 3 modular); rank lemma + two-prime ranks; since 2026-10-06 a kernel check of an explicit inverse, the generators matched exactly to `CondsC.lean`, and R irreducible (`rank_lemma_check/`) |
| Controls | 14/14 (3 ACCEPT, 9 REJECT, 2 sorry-flagged) | T1Zero 5 negative controls; rank planted-zero control; step-1 perturbed/dropped controls; `rank_lemma_check/` 5 kernel controls + 4 script controls |
| External review | HLRE v5.0 audit + errata (`audits/`) | none yet; an I3 replication is specified (`rank_lemma_check/I3_REPLICATION_SPEC.md`); the p-adic argument is closed as not needed; the correspondence guide is deferred |

---

## 7. Reproduction

### Branches (a,b)

```bash
cd branches_a_b
bash verify_v19.sh                      # checksums, scripts, 111/111 identities, 2026-10-05 checks, paper build
cd lean
lake exe cache get
LEAN_NUM_THREADS=1 bash verify_branch_ab_lean.sh   # full build + 66-theorem axiom audit
bash verify_routeC.sh                   # optional (2026-10-12): route C build, axioms, statement check (~34 min)
```

Two replication documents (2026-10-12): `../REPRODUCTION_GUIDE.md` at the repository root re-runs the project's
scripts (reproducibility, I1); `replication/INDEPENDENT_REPLICATION_GUIDE.md` is the blind replication with the
replicator's own code (I3 when done by an outside party).

### Branch (c)

```bash
cd branch_c
bash verify_branch_c.sh                 # -> bundle_v3_1/jacobian_lean/verify_branch_c_lean.sh
bash rank_lemma_check/run.sh            # 2026-10-06: premise checks + kernel check of the inverse (~4.5 min, core Lean)
bash muse_refutation/check_refutation.sh   # 2026-10-06: the refutation, clean copy (needs Mathlib v4.34.0)
```

Requires elan/lake (Lean 4.34.0, Mathlib v4.34.0), python3 with python-flint and
sympy. Single modules peak at ~5.6 GB RSS; allow 12+ GB or set `LOWMEM=1`.
Step 0 fingerprints the branch-(a,b) prerequisites, so the (a,b) Lean tree must
be present underneath `jacobian_lean/` (see GUIDE.md §12 for the overlay procedure).

---

## 8. Provenance and version history

- **Branches (a,b):** v17 (2026-09-28) → v18 (build fixes, wording) → v19
  (independent blind review: no fatal flaw; ten recommendations implemented).
  Published: Zenodo 10.5281/zenodo.23023490. The v17/v18 trees are preserved on
  repo main as `branch_ab_v17/`, `branch_ab_v18/` until 2026-09-30, when both were removed and `branch_ab_v19/` renamed to `branch_ab/`.
  - 2026-10-03: `branch_ab_v19/` was restored at the repository root as a copy of `branches_a_b/`, because the
    Zenodo record cites that path.
  - 2026-10-05: the a₈,₁₆ certificate, the Lean m = 3, 5 classifications (`Jacobian/B26`) and the B2.2 resolution
    were added (PR #3), followed by the check of CAIC's B2.6 data file. `branch_ab_v19/` was synced to stay
    byte-identical with `branches_a_b/`. See `branches_a_b/CHANGES_v19.md` §15.
  - 2026-10-06: the abstract update, the Lean solution counts (`B26Count`) and the irreducibility of the eliminants
    (`B26Irred`); `branch_ab_v19/` synced again. See `branches_a_b/CHANGES_v19.md` §15.
  - 2026-10-07: the Lean proof of Corollary 1.2 and Remark 8.8 (`Jacobian/A816`, G3 by route R) and the paper text
    that reports it (34 pages); `branch_ab_v19/` synced again. See `branches_a_b/CHANGES_v19.md` §16.
  - 2026-10-08 (CAIC): route C (`lean/Jacobian/A816C`, PR #15, added to `branch_ab_v19/` only) and a page-count change
    in `verify_v19.sh` (PR #14, manifests not regenerated). Reviewed and repaired on 2026-10-12: route C copied into
    `branches_a_b/`, built, given a statement check and `verify_routeC.sh`; page count 34 (35 accepted); manifests
    regenerated; the two copies byte-identical again. See `branches_a_b/CHANGES_v19.md` §17.
- **Branch (c):** the `branch_c/` pipeline scripts on repo main (corrected
  2026-09-29: E₁ projection, 6d κ=0, Singular hang guard) → v2 bundle → v3.0
  (bundled mid-build) → **v3.1** (2026-09-29, 23:40 CDT; every module built,
  `verify_branch_c_lean.sh` passed, `Bridge` bug found and fixed).
  - **The v2 corrected-commit proposal.** It was applied to repo main as `2b77cd4` on 2026-09-29; the result is
    byte-identical to `proposed_branch_c/`. Earlier versions of this map said "not applied"; that was corrected on
    2026-10-06.
  - **The top-level `branch_c/`.** It was removed on 2026-10-01 (`d65a007`).
  - **2026-10-06.** Three additions outside the bundle copy, which stays byte-identical:
    - `branch_c/rank_lemma_check/`: premise checks and the kernel check of the rank lemma's arithmetic, plus the I3
      specification;
    - `branch_c/muse_refutation/`: the Muse bundle withdrawn, and a clean refutation copy;
    - the maintained `GUIDE.md` and `paper/BRANCH_C_GUIDE.md`.
    The p-adic argument is closed as not needed.
  - See `branch_c/V3_1_PROVENANCE.md`.
- **This unified directory** (2026-09-30): `branches_a_b/` is `branch_ab` (v19) byte-for-byte; `branch_c/bundle_v3_1/` is the v3.1 bundle byte-for-byte
  (manifest-verified at assembly). New: this map, the READMEs, `BUILD_STATUS.md`,
  checksums, `verify_branch_c.sh`, and the conditional correspondence-guide to-do.

## 9. Deferred and open items

1. **Branch-(c) correspondence guide** — **written 2026-10-07 (CAIC, PR #13)**:
   `branch_c/correspondence_guide/CORRESPONDENCE_GUIDE.md`. Its section mapping was corrected on 2026-10-12, and it
   now records a discrepancy in the paper: the "Formalization seam" paragraph of the paper's §6 says degree-19
   rigidity is not formalized in Lean, but `degree19_rigidity`, `vertex_12_24_forces_t2` and
   `main_theorem_c_of_claim` are kernel-checked. The paper is not yet corrected. (`TODO_correspondence_guide.md` is
   the original to-do.)
2. The p-adic argument for branch (c) — **closed 2026-10-06: not needed** (independent alternative, unreviewed,
   unused). `branch_c/bundle_v3_1/jacobian_lean/chart_certificates/padic_DEFERRED/` stays byte-identical.
   Its `SINGLE_PRIME_ARGUMENT.md` §6 is out of date: it lists the E₀–E₋₂ elimination as a premise outside Lean, but
   that elimination is now kernel-checked (`Descent2R`, `Bridge`). See GUIDE.md §4.4.
3. The branch-(c) `.tex` elimination paper — **done 2026-09-30**:
   `branch_c/paper/branch_c_elimination.tex` / `.pdf` (16 pages in Noto Sans / Noto Sans Math when first built;
   18 pages in Fira since the 2026-10-01 font revision); `BRANCH_C_GUIDE.md` remains the comprehensive reference.
4. `ChartEmptyC_T1ne0` in Lean — **now in Lean (grade A since 2026-11-04)**;
   formalizing the rank lemma's instance in Lean was listed as optional
   (GUIDE.md §11) and is done.
   - **Correction (2026-10-06).** `chart_certificates/STEP3_4_CHART.md` (in the bundle copy, left unchanged)
     estimates kernel `decide` at "hours or more" and offers `native_decide`. That estimate is superseded.
     - **Measured:** the arithmetic core passes the Lean kernel in about 7 CPU-minutes, with axioms `[propext]`
       only and no `native_decide`. The core is an explicit inverse of the W = 24 pivot block mod 32003, packed
       into natural numbers.
     - **Kept as a reproducibility target:** `branch_c/rank_lemma_check/`.
   - **Grade A is now a formalization task, deferred by decision (2026-10-06).** Estimated at 9–15 sessions:
     - A1: the digit argument;
     - A2: the matrix built in Lean from `CondsC.lean`;
     - A3: the determinant transfer through ℤ[X]/(R), with R irreducible, in Lean;
     - A4: the chart reduction S₂ = κ, with a Bézout certificate for o₁(w) ≠ 0;
     - A5: integration.
   - **Completed 2026-10-31–11-04.** A1 compiled 2026-10-31, A2 2026-11-01,
     `hsupp2` 2026-11-02, `challenge_target` + `branch_c_eliminated` proved
     2026-11-04, filed as tracked modules `GradeA.Bridge` /
     `GradeA.Composition` (commit `7e4db07f`, 2026-11-06; status record
     `branch_c/grade_a/BRIDGE_STATUS_2026-11-06.md`). The grade is A; the rank
     computations stand as independent corroboration (I1), and the I3
     replication is still open.
   - **Status 2026-10-12.** CAIC drafted A1–A5 on the unmerged branch `caic/branch-c-cleanup` (19 `sorry`s, 8 axioms
     in the assembly). A review on 2026-10-12 found: A1 (the digit argument) genuine, with 3 `sorry`s, not yet linked
     to the kernel-checked data; A2 stubs (`def … := sorry`); A3's transfer inapplicable as stated (it needs ℤ[X] and
     the minimal polynomial, not ℤ); A4 and A5 stated over ℤ, where R has no root, so they are vacuous (a Lean proof
     of `False` from their hypotheses was given); A5's assembly circular. The branch's "fidelity B+, I3" regrade is not
     supported. The corrected architecture (over a field L of characteristic 0; κ from `T1Zero.s_sq`, `s_X2`; the
     left-kernel argument; the determinant over ℤ[X] evaluated at w₀ mod p; R | D by irreducibility) is in
     `reviews/REVIEW_2026-10-12_handoff.md`.
   - **2026-10-12, `branch_c/grade_a/`:** the generic half is in Lean (no `sorry`, standard axioms). It contains R
     irreducible over ℚ (H3, now grade A), the transfer through ℤ[X], and the assembly theorem
     `no_common_zero_of_certificate`. Later the same day the chart reduction was added (`grade_a/lean/GradeA/Chart/`,
     kernel-checked: a chart point is a common zero of the six generators, with b₁₁,₂₀ free), and the interface
     theorem `chartEmptyC_T1ne0_of_certificate`. It proves `ChartEmptyC_T1ne0` for every field of characteristic 0
     from the Macaulay data (rows, pivot columns, support) and two finite deliverables: A1 (`Cinv * MS = 1` mod
     32003, from the packed kernel check) and A2 (`MS` is the evaluated Macaulay block of the generators, up to one
     nonzero scale per generator). See `branch_c/grade_a/README.md`.
     **Completed 2026-10-31–11-04:** A1, A2, and the rows/pivot columns/support
     were supplied and kernel-verified; `challenge_target` + `branch_c_eliminated`
     proved 2026-11-04. `ChartEmptyC_T1ne0` is grade A.
5. Branch-(c) figures — produced: `branch_c/paper/figures/` (four figures with their scripts).
6. GGHV Prop. 4.3's other cases and the reduction from the Jacobian conjecture —
   outside scope, unchanged.
7. Branches (a,b) (2026-10-05/06): optional Lean extensions, none needed for `main_theorem`:
   - G1: irreducibility of the m = 3, 5 eliminants over ℚ (**done 2026-10-06**, `lean/Jacobian/B26Irred.lean`);
   - G2: the solution counts as cardinality theorems (**done 2026-10-06**, `lean/Jacobian/B26Count.lean`);
   - G3: Corollary 1.2 in Lean — **done 2026-10-07 by route R** (`lean/Jacobian/A816/`, `lower_edge_rigidity`,
     `a816_eq_zero`, `main_theorem_lower_edge`; 66/66 theorems of the verify script on standard axioms; controls
     9/9). Route R reuses the descent up to t = 0 and adds four small steps (depth 1; depth 2 as linear forms in
     s = (b₁₁,₂₁, b₁₂,₂₃); E₁ gives s₂² = s₁² = 0; E₂ triangular in depth 3).
     - **Route C**, the kernel check of the certificate's own route — **done at the reflection level (CAIC,
       2026-10-08; reviewed and integrated 2026-10-12).** `lean/Jacobian/A816C`: `routeC_a816` and `routeC_source`
       (a₈,₁₆ = 0 from the 75 bracket equations, 56 of them used, independent of `Jacobian/Descent`), standard axioms,
       built in 2020 s on 2 cores (against the 10–20 min estimate of 2026-10-06). Limits: the hypotheses are
       reflected expressions, linked to `jac P Q` by the Python statement check `lean/certgen/check_routeC_statement.py`
       (added 2026-10-12), not in Lean; the generator `routec_gen.py` is not in the repository; no perturbation
       control has been run for route C (its C7 theorem shows the bridge's rescaling is needed). See
       `branches_a_b/lean/README.md` §1d.

   Remark 8.8 (all lower coefficients vanish at the K₅ point): since 2026-10-06 its 61 certificates are written out
   and checked by two independent programs (`branches_a_b/scripts/a816_rigidity/`): 47 pivot identities x − φ(x) ∈ I
   and 14 depth-4 monomials m ∈ I. Grade B (exact, outside Lean). Before that it rested on one exact rank computation,
   corroborated mod p. Since 2026-10-07 the zero-set form (the only solution is P = P₂ + const, Q = Q₃ + const) is
   kernel-checked as `lower_edge_rigidity` (grade A); the nilpotency itself stays grade B.
8. The Muse `char0_cert` bundle — **closed 2026-10-06: withdrawn, superseded by v3.**
   - Its axiom `reduction_lemma` proves `False`, so its theorems (`descentClaimC_holds` …) are vacuous.
   - The withdrawal notice is `branch_c/muse_refutation/DEPRECATED_char0_cert.md`. It goes, as `DEPRECATED.md`, into
     every stored copy of the bundle.
   - A cleanly building copy of the refutation is in `branch_c/muse_refutation/`.
   - The bundle itself (not in this repository) is kept unchanged, for provenance. See GUIDE.md §4.5.
9. I3 replication of the branch-(c) rank computation — **open.** The specification was written on 2026-10-06
   (`branch_c/rank_lemma_check/I3_REPLICATION_SPEC.md`). It needs someone outside the project.
   - **2026-10-08/11.** An agent of the project (CAIC) implemented the specification and reproduced its numbers. The
     numbers are right, but the work is not I3: the implementer is internal, and the specification states the
     expected values (§§1, 3, 4, 6). It counts as I1–I2. The branch `caic/branch-c-cleanup` says "I3 complete"; that
     claim is not accepted.
   - **2026-10-12.** A blind guide for an outside replicator, with a separate answer key recomputed in fresh code:
     `replication/INDEPENDENT_REPLICATION_GUIDE.md`. It replaces the specification for blind use.
