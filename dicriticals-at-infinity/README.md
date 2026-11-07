# Two-Dicritical Line Closure

## No Keller Map Admits Two Dicritical Divisors

**Author:** Brandon D. McCrary (ORCID: 0009-0008-2804-7165)
**Date:** October 1, 2026

### Status (review of 2026-10-12, corrected 2026-10-13; paper update 2026-11-04)

**2026-11-04:** the current paper is now `paper/two_dicritical_closure_rewrite.tex`
/ `.pdf` (November 2 rewrite); the October 1 draft (`paper/two_dicritical_closure.tex`
/ `.pdf`) is SUPERSEDED/WITHDRAWN but retained byte-identical — see
`paper/SUPERSEDED_2026-11-04.md` and `BUILD_STATUS.md`. The finalized unified
paper is recorded alongside it as `paper/combined_paper_final_2026-11-04.tex`
/ `.pdf`. The two-dicritical Lean count is unchanged: 21 of 21 theorems on the
standard axioms (VM re-verification, `BUILD_STATUS.md` 2026-11-04 entry).

The theorem below is **claimed. As worded it is false, one of its theorems is false as stated, and its proof is
incomplete** (`../JC2D-branches_a_b_c_unified/reviews/REVIEW_2026-10-12_handoff.md`, §5 and §9; `lean/README.md`):
- **The statement, read literally, is false for every Keller map of degree $\geq 2$.**
  - Such a pencil $\lambda P+\mu Q$ always has a base point at infinity
    (`../JC2D-branches_a_b_c_unified/reviews/two_dicritical/base_point_at_infinity_check.py`).
  - It also has an affine one, once the target is translated so that $0$ is a value; an automorphism needs no
    translation.
  - Every base point carries a dicritical.
  - Worked examples: the automorphisms $(x-y^2,\ y)$ and $(x,\ y+x^2)$
    (`../JC2D-branches_a_b_c_unified/reviews/two_dicritical/main_statement_check.py`; the identity is the control,
    with one base point).
  - Read literally, the statement would imply the Jacobian conjecture outright, and every non-affine automorphism
    refutes it. The paper's computations all take place at infinity.
  - **The intended statement is now written down** (2026-10-13): `RESTATEMENT.md`, Theorem R: the pencil has at most
    one dicritical at infinity. It is equivalent to the plane Jacobian conjecture (Proposition 3.2 there), so a
    complete proof of it would prove the conjecture.
- **Theorem `thm:e1` is false as stated** (corrected 2026-10-13, after an outside referee's report on PR #19).
  - Its proof reads the order condition $\nu_{E_1}\geq -2$ as "total degree $\geq 2$"; it means "$x$-degree
    $\leq 2$". `e1_solitary.py` indexes its unknowns by $X^{d-J-K}Y^JZ^K$, and the proof read them as $x^Jy^K$.
  - $P=(x+y^2)^2+y$, $Q=P+x+y^2$ satisfy the paper's definition of the $E_1$ $m=2$ open subset, and $[P,Q]=-1$
    (`lean/TwoDicritical/E1Keller.lean`, `lean/check_e1_index.py`).
  - The intended conclusion is true, for every $m$: $E_1$ is never dicritical for a Keller map. The algebraic step
    is proved in `lean/` (a vanishing Wronskian); the chart step is executed, not formalized.
- the paper closes the adjacent $m = 1$ case by a computation at $d = 3$ only (`e3_adjacent.py`,
  `routeB_cancellation.py`), while the theorem is stated for every degree;
- the constant-leading-form proposition, which carries the case $m \geq 2$ on $E_k$, $k\geq 2$, has a proof sketch
  only, and the sketch assumes free centers ($u_0\neq 0$);
- **the bridge.** The Lean drafts of 2026-10-12 rested the bridge induction on two axioms that are false as stated.
  - **Since 2026-10-12, `lean/` proves the bridge collapse (Theorem `thm:bridge`) from the paper's explicit
    equations, with no axioms.** That proof also closes a gap in the paper's proof at weight $W = 2$, where the
    block-rank lemma does not apply.
  - The equations are the chart at a free point $a$ of $E_2$ (`lean/check_satellite.py`). Read through it, the theorem
    rests on two premises:
    - the two dicriticals lie over two distinct **free** points of $E_2$;
    - every member of the pencil has pole order at most 1 on them. This is asserted, not derived from $m = 1$.
  - "Both centers nonzero" marks where the formula applies, not a missing argument. At $a = 0$ (a satellite point)
    the same equations mean something else. The formal witness $(x-a_4y^2,\ y)$ of
    `lean/TwoDicritical/CenterHypotheses.lean` is a one-center configuration, not a bridge.
  - Under the two premises, **one** such dicritical already forces degree $\leq 2$
    (`lean/TwoDicritical/OneCenter.lean`), so the bridge says nothing about pencils of higher degree.
  - Dicriticals over the satellite points of $E_2$, and over deeper satellite points, are not treated. The bridge
    takes free points of $E_2$. The constant-leading-form sketch and its scripts (`middle_e2.py`, `leaf_e3.py`,
    `leaf_e4.py`) take centers with nonzero coordinates.
  - See `lean/README.md`, item 1.

The 18 scripts reproduce exactly (`verify_all.sh`, outputs compared byte for byte), but they are computations at
fixed degrees and do not prove the general statements.

### Main theorem (as worded in the paper; false as worded, see Status)

The corrected statement, with what is proved toward it and what is missing, is in `RESTATEMENT.md`.

Let $K$ be a field of characteristic $0$. Let $P,Q\in K[x,y]$ with
$[P,Q]=c\in K^\times$ (a Keller map). Then the resolution of the pencil
$\lambda P+\mu Q$ contains no two distinct dicritical divisors.

### Structure

| Directory | Contents |
|-----------|----------|
| `paper/` | LaTeX source (`two_dicritical_closure.tex`) and compiled PDF |
| `scripts/` | 18 Python/SymPy scripts, each actually executed |
| `outputs/` | Exact stdout + exit codes from every script run |
| `logs/` | Build logs |

### Key results

These are the paper's claims; see Status for what is proved.

1. **No $m\geq 2$ dicritical exists for any Keller map.**
   - All $E_k$ ($k\geq 2$): constant-leading-form theorem (proof sketch only).
   - $E_1$: degree obstruction ($J$ has minimum degree $2$). False as stated; the corrected statement, that $E_1$ is
     never dicritical for a Keller map, has its algebraic step proved in `lean/`.

2. **The $m=1$ bridge is empty for every $d\geq 2$** (at two distinct free centers; proved in `lean/` for the
   paper's equations; one such center already forces degree $\leq 2$).
   - Descending induction on weighted degree $W=2J+K$.
   - Diagonal blocks $[\binom{e_k}{i}a^{e_k-i}]$ reduce to scaled Vandermonde; full rank.
   - Nullspace $=\mathrm{span}\{1,y\}$; $J\equiv 0$.

### Reproducibility

```bash
./verify_all.sh   # re-runs all 18 scripts; checks exit codes and compares each output with outputs/
```

`CORRESPONDENCE.md` maps every script to the exact paper statement it certifies.

### Paper

`paper/two_dicritical_closure.pdf` (6 pages) — compiled with XeLaTeX,
Fira Sans, Fira Mono and Fira Math (since 2026-10-01; `pdffonts` shows only Fira faces), no overfull boxes.
