# Branch-(c) elimination paper

**Elimination of the GGHV Branch-(c) Normal Form at Degree Pair (72,108):
A Certified Computational Audit — Descent, Chart Conditions, and the Rank-Lemma Obstruction**

Brandon D. McCrary (independent researcher), 2026-10-01.

## Files

| File | Description | MD5 |
|---|---|---|
| `branch_c_elimination.tex` | LaTeX source (XeLaTeX; Fira Sans / Fira Mono / Fira Math) | `481dfbc948ca6b50133fff9ed684bc5d` |
| `branch_c_elimination.pdf` | Compiled 18-page paper, all fonts embedded | `31d4b56a2ff7e87c9572aa52840754eb` |
| `BRANCH_C_GUIDE.md` | The comprehensive v3.1 bundle guide (paper-equivalent reference document; 13 sections) | `6b88d690bcea34ce25b853f356433ada` |
| `figures/fig1_newton_polygons.pdf` | Figure 1: branch-(c) Newton polygons N(P), N(Q) (vector) | `45287d2f6e2b5404fcd35a2519ebad16` |
| `figures/fig2_bridges.pdf` | Figure 2: B0–B8 bridge architecture flowchart (vector) | `e117806fbc10ab8baff10c0ef10be388` |
| `figures/fig3_omega.pdf` | Figure 3: chart geometry near Ω=0, schematic (vector) | `83d047cb4ac018ddcf4b3365ddb44bc8` |
| `figures/fig4_ranks.pdf` | Figure 4: Macaulay rank profile W=22,23,24 (vector) | `1a36531d8d336dbcb2ececec98cd3af6` |
| `figures/*.py` | Python scripts regenerating the four figures (matplotlib, Fira Sans) | — |

## What the paper is

The branch-(c) elimination worked out **symbolically** (Lean 4: 790 modules, 600
kernel-checked reflective identities, no `sorry`/`axiom`/`native_decide`,
`#print axioms` = propext, Classical.choice, Quot.sound) and **numerically**
(exact K5 certificate on the t1=0 stratum; fixed-degree Macaulay rank lemma at
W=24, two primes, two independent implementations, negative controls).

It follows the format of the branch-(a,b) elimination paper
(`../branches_a_b/paper/branch_ab_elimination_v3.tex`) exactly: same document
class and layout, Fira Sans text with Fira Math symbols and Fira Mono code,
theorem/lemma/definition environments, Lean code listings, four finished
vector figures (regenerable from the checked-in Python scripts), epistemic-grade
claim registry, computational archive appendix, and AI-disclosure section.

## Status

- The Lean-checked part (descent, t1=0 stratum) is grade A.
- The whole-chart rank computation is now proved in Lean (grade A, 2026-11-04:
  `challenge_target`, `GradeA.Bridge`); the rank lemma (§5.9 of the guide, §10
  of the paper) stands as independent corroboration. The false reduction lemma
  is retracted and replaced by the rank lemma.
- The degree-19 rigidity lemma's parity-constrained Davenport–Stothers step is
  supplied by an external certified point (grade B), not formalized in Lean
  (§3.2 of the paper).
- This is **not** a proof of the planar Jacobian conjecture and does not cover
  other GGHV cases (see §12 of the paper, "what is not claimed").

## Build

```bash
export PATH=~/texlive/bin/x86_64-linux:$PATH
xelatex -interaction=nonstopmode branch_c_elimination.tex
xelatex -interaction=nonstopmode branch_c_elimination.tex
xelatex -interaction=nonstopmode branch_c_elimination.tex
```

Requires: Fira Sans, Fira Sans Italic/Bold, Fira Mono, Fira Math (OpenType).
Font discipline (Brandon 2026-10-01): Fira ONLY — Fira Sans (text), Fira Mono
(code), Fira Math (math, with `FakeBold=0.3`). Latin Modern Math is forbidden
everywhere, including inside `tabular` environments. Noto fonts are not used.
The build is verified: exit 0 on all three passes, zero overfull boxes, zero
undefined references/citations, 18 pages, `pdffonts` shows only Fira families.
