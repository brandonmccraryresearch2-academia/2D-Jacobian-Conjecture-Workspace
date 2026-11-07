# Branch (a,b) Elimination — v19

Elimination of GGHV normal form (2) [branch (a,b)] in the degree-(8,28) case of the
two-dimensional Jacobian conjecture, with a Lean 4 machine-checked proof of the
m = 7 top-layer classification (Proposition 6.1).

v19 implements the ten recommendations of the independent final blind review
received 2026-09-28 (no fatal flaw found in the b_{12,24}=0 chain): the main
theorem now concludes only b_{12,24}=0 (a_{8,16}=0 is an independent
rigidity corollary), the proof is organized around four certificates, the
35-minor span argument and the characteristic-zero transfer are explicit,
and the obstruction script emits a machine-readable K5 rank certificate.
See `CHANGES_v19.md` for the full list. The v18 tree is in the git history
(commit 42cbf03); it was kept at the repository root as `branch_ab_v18/` until
2026-09-30.

**Two identical copies.** This package is in the repository twice, with identical
contents:
- `branch_ab_v19/` at the repository root, the path that the Zenodo record
  10.5281/zenodo.23023490 cites;
- `JC2D-branches_a_b_c_unified/branches_a_b/`.

The 2026-10-05 revision adds the a₈,₁₆ certificate, the Lean m = 3, 5
classifications and the B2.2 resolution. See `CHANGES_v19.md` §15.
The 2026-10-07 revision adds the Lean proof of Corollary 1.2 (a₈,₁₆ = 0) and
Remark 8.8 (lower-edge rigidity), `lean/Jacobian/A816/`. See `CHANGES_v19.md` §16.

Elimination of GGHV normal form (2) [branch (a,b)] in the degree-(8,28) case of the
two-dimensional Jacobian conjecture, with a Lean 4 machine-checked proof of the
m = 7 top-layer classification (Proposition 6.1).

## What this is

For polynomials P, Q ∈ L[x,y] over a field L of characteristic 0 in GGHV normal
form (2) with [P,Q] = λx², λ ≠ 0, there is **no solution**. The Lean formalization
proves, independently of GGHV Proposition 4.3:

- `chartClassification_holds`: every solution of the 17-equation normalized chart
  (`ChartClassification L`) is one of the five K₅-conjugate points (m = 7 case of
  Proposition 6.1), kernel-checked, depending only on `propext`,
  `Classical.choice`, `Quot.sound`.
- `main_theorem`: the NewtonNF2 form of Theorem 1.1 with no remaining hypothesis,
  kernel-checked on the standard axioms only.
- `lower_edge_rigidity` (2026-10-07): under the hypotheses of Theorem 1.1, every
  coefficient of P and Q off the top edges vanishes except the constant terms, so
  a₈,₁₆ = 0 (`a816_eq_zero`, Corollary 1.2) and P = P₂ + const, Q = Q₃ + const
  (Remark 8.8); `main_theorem_lower_edge` refutes NewtonNF2 through the vertex
  (8,16) alone. Same three axioms.

Conditional on GGHV Proposition 4.3, this eliminates branch (a,b). Branch (c)
(normal form (1)) is not addressed by this package; it was eliminated in Lean
on 2026-11-04 (`branch_c_eliminated`, no hypotheses, standard axioms) — see
`../branch_c/`. GGHV Proposition 4.3 itself is now proved in full in Lean —
CONDITIONAL (`prop43_conditional`, `gghv-dependency-closure/`). The full
planar Jacobian conjecture remains open.

## Repository layout

| Path | Contents |
|---|---|
| `lean/` | Lean 4 project (Mathlib v4.34.0): proof sources, generators, verification scripts |
| `lean/Jacobian/ChartProof/` | The 12-module machine-checked proof (Reflect + 11 generated modules, 111 identities) |
| `lean/certgen/chartproof/` | Exact generators (Python/SymPy/python-flint) + independent check scripts |
| `lean/Jacobian/B26.lean`, `lean/Jacobian/B26/`, `lean/Jacobian/B26Count.lean`, `lean/Jacobian/B26Irred.lean` | (2026-10-05/06) Kernel-checked $m=3$ and $m=5$ top-layer chart classifications over any field of characteristic 0 (`m3_chart_iff`, `m5_chart_iff`, squarefree eliminants), the exact solution counts 3 and 10 over any algebraically closed field of characteristic 0 (`m3_chart_card`, `m5_chart_card`), and the irreducibility of the eliminants over $\mathbb{Q}$ (`T3poly_irreducible`, `T5poly_irreducible`); standard axioms only |
| `lean/Jacobian/A816/` | (2026-10-07) Kernel-checked lower-edge rigidity: `lower_edge_rigidity`, `a816_eq_zero` (Corollary 1.2), `main_theorem_lower_edge`; generator `lean/certgen/gen_a816.py`, statement check `lean/certgen/check_a816_statement.py`, controls `lean/controls_a816.sh` |
| `paper/` | 34-page paper (XeLaTeX, TeX Live 2026), four certificates, explicit 35-minor and transfer arguments |
| `scripts/` | Audit and analysis scripts |
| `scripts/a816_certificate/` | (2026-10-05) Explicit certificate $a_{8,16}^2=\sum H_k e_k$ over $K_5$ for Corollary 1.2, two independent exact checkers, controls; `./verify_bundle.sh` |
| `scripts/a816_lean_feasibility/` | (2026-10-06) Feasibility estimate for checking that certificate in the Lean kernel: exact sizes, pilots that pass the kernel, a calibration; not part of the Lean build; `bash run_all.sh`. Corollary 1.2 itself was formalized on 2026-10-07 by a shorter route (`lean/Jacobian/A816/`) |
| `scripts/a816_rigidity/` | (2026-10-06) The 61 certificates behind Remark 8.8: all 51 lower unknowns nilpotent modulo the layer ideal. Generated with exact $K_5$ arithmetic and checked by an independent python-flint program; `bash run.sh` (about 8 min) |
| `scripts/b26_m5_eliminant/lean_certificates/` | (2026-10-05) Generator and ideal-equality certificates for `lean/Jacobian/B26*`; `./regen_b26.sh` |
| `scripts/b22_structured/RESOLUTION.md` | (2026-10-05) B2.2 = the Lean chart system; the exact $K_5$ point validated in the $c$-recursion form (`b22_validate.py`) |
| `figures/` | Paper figures |
| `logs/` | Build, axiom, control, regeneration, saturation logs |
| `correspondence_guide/` | Correspondence guide mapping proof elements to their Lean formalization |
| `audits/` | The HLRE v5.0 audit (an external review, filed unchanged) and `HLRE_v5_audit_ERRATA.md`, which corrects its factual errors (the errata is a response, not an independent review) |
| `BUILD_STATUS.md` | Full build and verification record |
| `CHECKSUMS.md5` / `CHECKSUMS.sha256` | Checksums of the shipped bundle files (excludes this README, `.gitignore`, and `audits/`, which were added for publication) |
| `CHANGES_v19.md` | Full v19 change list vs v18 |
| `logs/k5_minor_certificate.json` | Machine-readable 35×6 K5 minor matrix with rank-6 certificate |
| `logs/v19_scripts.log` | Recorded stdout + exit codes of the v19 script runs |
| `verify_v19.sh` | One-command verification: checksums, scripts, 111/111 identities, the 2026-10-05 checks (a₈,₁₆ certificate, B26 regeneration and statement check, B2.2 validation), paper build |

## Reproduction

```bash
cd lean
lake exe cache get                              # fetch Mathlib oleans
LEAN_NUM_THREADS=1 bash verify_branch_ab_lean.sh  # full build + 66-theorem axiom audit
CONTROLS_JOBS=1 bash controls.sh                  # 14/14 as expected: 3 unmodified ACCEPT, 9 perturbed REJECT (expected Lean error), 2 sorry copies flagged
CONTROLS_JOBS=1 bash controls_a816.sh             # 9/9 as expected for Jacobian/A816: 2 ACCEPT, 6 REJECT, 1 sorry copy flagged
bash certgen/check_regeneration.sh                # byte-identical regeneration, plus the Jacobian/A816 statement check
```

Quick checks (no Lean needed):

```bash
python3 lean/certgen/chartproof/independent_check.py   # 111/111 identities over Z (~2 s)
python3 lean/certgen/chartproof/saturation_check.py     # saturation over Q (needs Singular)
```

## Scope and provenance

- The main theorem's Lean proof uses the m = 7 chart classification. The
  m = 3 and m = 5 chart classifications are kernel-checked separately
  (`lean/Jacobian/B26*`, 2026-10-05); the main theorem does not use them.
  The degree-35 eliminant, the explicit a₈,₁₆ certificate of
  `scripts/a816_certificate/` (an independent second proof of Corollary 1.2;
  the corollary itself is kernel-checked since 2026-10-07), and GGHV
  Proposition 4.3 are outside the Lean formalization (see
  `lean/CLASSIFICATION_STATUS.md` and paper §1.3 "Logical status").
- Nothing here claims resolution of the (8,28) case or the Jacobian conjecture.

## Status

Staged release. Not peer-reviewed. See `BUILD_STATUS.md` for the complete
verification record.
