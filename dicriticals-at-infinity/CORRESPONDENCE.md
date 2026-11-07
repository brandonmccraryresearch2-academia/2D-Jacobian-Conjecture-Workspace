# Script-to-Arithmetic Correspondence

## Two-Dicritical Line Closure (October 1, 2026)

Every script below was actually executed. Outputs are in `outputs/`.
This file maps each script to the exact arithmetic statement in the paper
(`paper/two_dicritical_closure.tex`) that it certifies.

---

### Part I: No dicritical of order m >= 2 (Paper §3)

| Script | Paper locus | Exact arithmetic certified |
|--------|-------------|---------------------------|
| `general_constant_form.py` | Prop. 3.1 | Pullback unit $U(u',v')\|_{v'=0}$ has $u'$-degree $0$ after normalization; verified $(u_0+u'v')^{-2}\|_{v'=0}=u_0^{-2}$ symbolically. |
| `middle_e2.py` | Cor. 3.2 | Middle $E_2$ divisor: $m=2$ leading coefficient computation in the selected chart. |
| `leaf_e3.py` | Cor. 3.2 | Leaf $E_3$: $m=2$ leading coefficient is constant in the chart; no $m\geq 2$ dicritical. |
| `leaf_e4.py` | Cor. 3.2 | Leaf $E_4$: $m=2$ leading coefficient is constant in the chart; no $m\geq 2$ dicritical. |
| `e1_solitary.py` | §3.2 | $E_1$ $m=2$ span: at $d=4,5,6$, nullities $12,14,16$; linear conditions $p_{JK}=0$ for $J+K<d-2$ imposed. |
| `e1_global.py` | §3.2 | Explicit pair $(y^2,y^2+xy)$: $C_P(t_1)=t_1^2$, $C_Q(t_1)=t_1^2+t_1$, exact order $-2$, exact degree $2$. |
| `e1_keller_search.py` | Thm. 3.3 | Every monomial has $J+K\geq 2$ $\Rightarrow$ each partial has min degree $1$ $\Rightarrow$ $[P,Q]$ has min degree $2$, never constant. 20 random trials confirm $J$ never constant. |
| `at_degree_bound.py` | Cor. 3.2 | Finite bridge table $m_1,m_2\leq 4$: stronger center has at-degree $<m_2$ in every row. |
| `at_degree_bound_m5.py` | Cor. 3.2 | Finite bridge table $m_1,m_2\leq 5$: same collapse. |
| `mixed_poles.py` | Cor. 3.2 | Mixed $(2,3)$ bridge at centers $\{2,5\}$: nullity $4$ at $d=2$, $5$ at $d=3..7$; leading at-degrees $<m$. |
| `depth5_global.py` | Cor. 3.2 | 945 depth-5 states; 13 with $\geq 2$ candidates $m\geq 2$; none with two $m\geq 3$. |
| `depth6_enum.py` | Cor. 3.2 | 10,395 depth-6 states; 17 with $\geq 2$ candidates $m\geq 3$; minimal pair type $((7,3),(7,3))$. |

### Part II: The m=1 bridge is empty (Paper §4)

| Script | Paper locus | Exact arithmetic certified |
|--------|-------------|---------------------------|
| `m1_bridge_general.py` | Thm. 4.1 | Symbolic nullspace at general $a_3\neq a_4$: $d=2$ ($6\times 6$, rank 4, nullity 2), $d=3$ ($14\times 10$, rank 8, nullity 2); nullspace $=\mathrm{span}\{1,y\}$. |
| `m1_induction.py` | §4.3 | Numeric nullspace at $a_3=2,a_4=5$: nullity $2$, only $J=0$ survives, for $d=2,\dots,8$. |
| `m1_triangular.py` | §4.2 | Block-triangular structure at $d=6$: for each weight $W$, equations $\geq$ variables (e.g.\ $W=8$: 3 vars, 6 eqs). |
| `m1_block_rank.py` | Lem. 4.2 | Symbolic $\det[C(e_k,i)]_{i=0,1,2}=-(e_1-e_2)(e_1-e_3)(e_2-e_3)/2\neq 0$; general Vandermonde reduction proof. |
| `routeB_cancellation.py` | Thm. 5.1 | Adjacent $m=1$ pair: $d=3$ computation showing $E_2$ dicritical forces $E_3$ constant. |
| `e3_adjacent.py` | Thm. 5.1 | $E_2$--$E_3$ adjacent $m=1$ pair analysis. |


### Note of 2026-10-13 on the E₁ rows (§3.2)

- `e1_solitary.py` multiplies its unknown $p_{JK}$ by $X^{d-J-K}Y^JZ^K$, that is, by the affine monomial
  $x^{d-J-K}y^J$, so its condition (i) is "$x$-degree $\leq 2$". Its printed supports, and the pair of
  `e1_global.py`, label $p_{JK}$ as $x^Jy^K$: those are the chart coordinates $(s,t)=(y/x,1/x)$, not the affine ones.
  In affine terms the pair of `e1_global.py` is $(x^2,\ x^2(1+y))$. Its restrictions $t_1^2$ and $t_1^2+t_1$ share a
  factor, so $P/Q$ has degree 1 on $E_1$, not 2.
- `e1_keller_search.py` reads the same set as "total degree $\geq 2$". The arithmetic it certifies holds for that
  set, which is not the $E_1$ condition. Theorem 3.3 (`thm:e1`) is false as stated: $P=(x+y^2)^2+y$, $Q=P+x+y^2$ lie
  in its open subset and $[P,Q]=-1$.
- See `lean/README.md` (item 2), `lean/check_e1_index.py` and `lean/TwoDicritical/E1Keller.lean`.

---

## Execution record

All 18 scripts were re-executed on October 1, 2026 with
`~/miniconda3/envs/physics/bin/python` (Python 3.12, SymPy).
Every script exited with code 0. Outputs are byte-identical to the
`outputs/` directory contents.

Run `verify_all.sh` to reproduce.
