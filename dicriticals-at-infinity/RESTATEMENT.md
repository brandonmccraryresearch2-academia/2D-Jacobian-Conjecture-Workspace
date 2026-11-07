# The two-dicritical theorem, restated

*2026-10-13. Written at Brandon McCrary's request from the audit of `paper/two_dicritical_closure.tex`. That audit is
the review of 2026-10-12, §9.3–9.4, PR #19, an outside referee's report on #19, and the checks in `lean/`. Nothing
here proves the Jacobian conjecture. Nothing was published or deposited.*

## 0. Summary

1. **The theorem as worded is false** for every Keller map of degree ≥ 2 (Corollary 2.3). It can hold only for
   affine maps.
2. **The intended statement is equivalent to the plane Jacobian conjecture.** That statement is: the pencil
   $\lambda P+\mu Q$ of a Keller map has at most one dicritical divisor **at infinity** (Theorem R, Proposition 3.2).
   - So a complete proof of the paper's theorem, once corrected, would be a proof of the conjecture.
   - That is the bar the paper's arguments must be read against.
3. **Proved toward it** (§4):
   - neither the line at infinity nor any first blow-up at infinity is dicritical for a non-affine Keller map;
   - so every dicritical at infinity lies at depth ≥ 2.
4. **The bridge** is proved for the paper's equations. Read through its chart, it concerns two dicriticals over
   **free** points of one curve $E_2$, with pole order at most 1. One such dicritical already forces degree ≤ 2, so
   the bridge says nothing about pencils of degree ≥ 3 (§4.4).
5. **What is missing** (§5):
   - the paper's case split ("an adjacent pair or a bridge"), which is asserted, not proved;
   - dicriticals over satellite points, over different points at infinity, and at depth ≥ 3 beyond free chains;
   - the adjacent case beyond $d=3$;
   - the premise (P2).
6. **Where a counterexample's dicriticals would sit** (§3.3):
   - $E_\infty$ maps onto the target's line at infinity;
   - $E_S$ maps onto a curve of non-proper values.

   $E_\infty$ always exists, so Theorem R amounts to showing that $E_S$ cannot exist.

## 1. Setting and definitions

$K$ is an algebraically closed field of characteristic 0; statements over any field of characteristic 0 reduce to
its algebraic closure. $F=(P,Q):\mathbb A^2\to\mathbb A^2$ is a **Keller map**: $[P,Q]=P_xQ_y-P_yQ_x\in K^\times$.

**Standard facts used.**
- (F1) $F$ is étale. Its generic degree $e=[K(x,y):K(P,Q)]$ is at least 1.
- (F2) The **non-properness set** $S_F$ is the set of points of the target over which $F$ is not proper. It is
  either empty or a curve whose components are rational (Jelonek 1993, for dominant maps
  $\mathbb A^n\to\mathbb A^n$).
- (F3) $F$ is an automorphism $\iff S_F=\emptyset$.
  - If $S_F=\emptyset$, $F$ is a finite étale cover of the simply connected $\mathbb A^2$, hence an isomorphism.
  - If $F$ is not an automorphism, then $e\ge2$. With $e=1$, $F$ is birational and étale, hence an open immersion by
    Zariski's main theorem; so it is injective, and then bijective (Białynicki-Birula–Rosenlicht).

**Compactification.**
- Source and target are $\mathbb A^2\subset\mathbb P^2$, with lines at infinity $L_\infty$ and $L'_\infty$.
- Let $\sigma:X\to\mathbb P^2$ be a sequence of point blow-ups over $L_\infty$ such that $G=\bar F\circ\sigma:X\to
  \mathbb P^2$ is a morphism.
- The **curves at infinity** of $X$ are the components of $X\setminus\mathbb A^2$: the strict transform of $L_\infty$
  and the exceptional curves.

**The pencil.** For $c\in\mathbb A^2$ (target), $\Lambda_c$ is the pencil whose members are $F^{-1}(\ell)$ for the
lines $\ell\ni c$. Its members are the fibers of $\varphi_c=\pi_c\circ F$, where $\pi_c$ is the projection from $c$.
The paper's pencil $\lambda P+\mu Q$ is $\Lambda_0$.

**Dicriticals** (standard definition; review §9.3).
- A divisor $E$ over the source plane is **dicritical** for $\Lambda_c$ if $\varphi_c$ is not constant on $E$.
- Its **degree** $m(E)$ is the degree of $\varphi_c|_E:E\to\mathbb P^1$.
- $E$ is **at infinity** if its center on $\mathbb P^2$ lies on $L_\infty$; $L_\infty$ itself counts. Otherwise
  $E$ is **affine**.
- **Depth:** $L_\infty$ has depth 0. The exceptional curve of the blow-up at a point $p$ has depth one more than the
  largest depth of the curves through $p$. So $E_1$ over a point of $L_\infty$ has depth 1.
- **Free and satellite points.** A point of an exceptional curve is a satellite point if it lies on another
  component of the total transform of $L_\infty$, and free otherwise.

The paper (line 81) calls dicriticals "exceptional divisors on which the pulled-back pencil has no base points". That
is not the standard notion; this document uses the standard one.

## 2. Counting dicriticals

**Proposition 2.1 (the count).** Let $F$ be a Keller map and $c\in\mathbb A^2\setminus S_F$.
- (a) The affine dicriticals of $\Lambda_c$ are exactly the $e$ exceptional curves $E_q$ of the blow-ups at the
  points $q\in F^{-1}(c)$. Each has degree 1.
- (b) The dicriticals at infinity are the curves at infinity $D$ of $X$ for which $G(D)$ is a curve. Then $G(D)$ is
  $L'_\infty$ or a component of $\bar S_F$, and
  $$m(D)=\deg\big(D\to G(D)\big)\cdot\deg G(D).$$
- (c) $L'_\infty$ and every component of $\bar S_F$ are $G(D)$ for at least one such $D$. So the number $N_\infty(c)$ of
  dicriticals at infinity satisfies
  $$N_\infty(c)\;\ge\;1+\#\{\text{components of }S_F\}.$$

*Proof.*
- **(a)** Since $c\notin S_F$, $F$ is proper over a neighbourhood of $c$. With (F1), $F^{-1}(c)$ has exactly $e$
  points, and $F$ is a local isomorphism at each. Near $q$, $\varphi_c$ is a projection from a point composed with a
  local isomorphism. One blow-up at $q$ resolves it, and the exceptional curve maps isomorphically onto
  $\mathbb P^1$. At every other affine point, $\varphi_c$ is regular, so no other affine divisor is dicritical.
- **(b)** Let $D$ be a curve at infinity. $G(D)$ is not the point $c$: $G$ maps no curve at infinity into
  $\mathbb A^2\setminus S_F$. If $G(D)$ is a point $\neq c$, then $\varphi_c$ is constant on $D$. If $G(D)$ is a curve,
  it is $L'_\infty$ or meets $\mathbb A^2$. In the second case every point of $G(D)\cap\mathbb A^2$ is a limit of $F$
  along a path to infinity, so it lies in $S_F$, and $G(D)$ is a component of $\bar S_F$. Neither $L'_\infty$ nor a
  component of $S_F$ is a line through $c$. So $\pi_c$ restricted to $G(D)$ has degree $\deg G(D)$, and $D$ is
  dicritical with the stated degree.
- **(c)** $G$ is proper and surjective, so $L'_\infty$ is dominated by a curve at infinity. By the description of
  $S_F$ as $G(X\setminus\mathbb A^2)\cap\mathbb A^2$, so is each component of $S_F$. $\square$

This is elementary. Nguyen Van Chau describes the non-proper value set of a map through its "dicritical components" at
infinity (arXiv:0801.4138) and studies the pencil $aP+bQ$ itself (arXiv:0905.3939). The count is presumably known
in some form and is not claimed as new.

**Corollary 2.2 (automorphisms).** If $F$ is an automorphism, $\Lambda_c$ has exactly two dicriticals for every $c$:
- one affine, over $F^{-1}(c)$;
- one at infinity, the unique curve $D$ with $G(D)=L'_\infty$ ($G$ is birational).

Both have degree 1. For non-affine $F$, the one at infinity is exceptional (Lemma 4.1). This confirms the outside
referee's sketch.

**Corollary 2.3 (the theorem as worded fails).** Every Keller map of degree ≥ 2 has at least two exceptional
dicriticals in $\Lambda_0$, after a translation of the target that puts $0$ in $F(\mathbb A^2)\setminus S_F$. An
automorphism needs no translation. So `thm:main` ("no two distinct dicritical divisors") fails for every Keller map of
degree ≥ 2. If only exceptional curves count as divisors of the resolution, it holds exactly for affine maps, whose
dicritical at infinity is $L_\infty$ itself; if $L_\infty$ counts, it fails for them too.

Executed checks:
- `../JC2D-branches_a_b_c_unified/reviews/two_dicritical/main_statement_check.py`: $(x-y^2,y)$ and $(x,y+x^2)$ in
  full;
- `base_point_at_infinity_check.py` there: a base point at infinity on 30 random automorphisms;
- `restatement_checks.py` (here): $(x+y^3,y)$, whose dicritical at infinity has depth 5 and lies over a satellite
  point.

## 3. The corrected statement

**Theorem R (the corrected main theorem; open).** For every Keller map $(P,Q)$, the pencil $\lambda P+\mu Q$ has at
most one dicritical divisor at infinity.

**Proposition 3.1.** Let $F$ be a Keller map and $c\notin S_F$. Then $\Lambda_c$ has at most one dicritical at
infinity if and only if $F$ is an automorphism. In that case it has exactly one, of degree 1.

*Proof.*
- If $F$ is an automorphism, Corollary 2.2 applies.
- Conversely, by Proposition 2.1(c), at most one dicritical at infinity forces $S_F=\emptyset$, and (F3) makes $F$ an
  automorphism. $\square$

**Proposition 3.2. Theorem R is equivalent to the plane Jacobian conjecture.**

*Proof.*
- If the conjecture holds, every Keller map is an automorphism, and Corollary 2.2 gives exactly one dicritical at
  infinity.
- Conversely, let $F$ be a Keller map and pick $c\notin S_F$. Then $F-c$ is a Keller map with $0\notin S_{F-c}$, and
  its pencil is $\Lambda_c(F)$. Theorem R for $F-c$ and Proposition 3.1 make $F$ an automorphism. $\square$

### 3.3 Where a counterexample's dicriticals would sit

Let $F$ be a Keller map that is not an automorphism, and $c\notin S_F$. Then $\Lambda_c$ has:
- $e\ge2$ affine dicriticals, by (F3);
- at least one $E_\infty$ with $G(E_\infty)=L'_\infty$, of degree $\deg(E_\infty\to L'_\infty)$;
- at least one $E_S$ over each component $C$ of $S_F$, of degree $\deg(E_S\to C)\cdot\deg C$.

**The two halves of the paper.**
- The paper's first half claims there is no dicritical of degree $m\ge2$ for any Keller map. Applied to $E_S$, it
  would already exclude every counterexample whose $S_F$ has a component of degree ≥ 2.
- Its second half claims there are no two dicriticals of degree 1. That would handle the rest.

**What either half must cover.** It must apply to $E_\infty$ and $E_S$ wherever they sit in the resolution tree:
- over any point of $L_\infty$, at any depth;
- after free or satellite blow-ups.

## 4. What is proved toward Theorem R

| | Statement | Status | Where |
|---|---|---|---|
| 4.1 | **The line at infinity.** For a non-affine Keller map, $L_\infty$ is not dicritical for any $\Lambda_c$. | proof by hand; the binary-form step executed | `base_point_at_infinity_check.py`, check 1 |
| 4.2 | **First blow-ups at infinity.** For a Keller map, the exceptional curve of the blow-up at any point of $L_\infty$ is not dicritical. | algebraic step in Lean; chart step executed | `lean/TwoDicritical/E1Keller.lean` (`e1_lead_proportional`, `jac2_eq_zero_of_natDegree_zero`), `lean/check_e1_index.py` |
| 4.3 | **Depth ≥ 2.** Every dicritical at infinity of a non-affine Keller map has depth ≥ 2. | from 4.1 and 4.2 | — |
| 4.4 | **The bridge.** Under the paper's equations at two distinct nonzero centers, $S\in\operatorname{span}\{1,y\}$. | Lean for the equations; the geometric reading is executed | `lean/TwoDicritical/BridgeCollapse.lean`, `OneCenter.lean`, `lean/check_satellite.py` |
| 4.5 | **Constant leading form** (no $m\ge2$ on $E_k$, $k\ge2$). | proof sketch; free centers only | paper, Proposition `prop:constant-form` |
| 4.6 | **The adjacent case.** | computation at $d=3$ only | `scripts/e3_adjacent.py`, `routeB_cancellation.py` |

### 4.1 The line at infinity

Let $d=\max(\deg P,\deg Q)\ge2$.
- **Unequal degrees.** If $\deg P\ne\deg Q$, then $\varphi_c|_{L_\infty}$ is the constant $0$ or $\infty$.
- **Equal degrees.** If $\deg P=\deg Q=d$, the degree-$(2d-2)$ part of $[P,Q]$ is $[P_d,Q_d]$, and it vanishes.
  For binary forms $f,g$ of the same degree $\ge1$, $[f,g]=0$ forces $f=rg$:
  - $h=f/g$ has degree 0, so $xh_x+yh_y=0$ (Euler);
  - $[h,g]=[f,g]/g=0$;
  - if $(h_x,h_y)\ne0$, both relations make $(g_x,g_y)$ proportional to $(-y,x)$, so $\deg g\cdot g=xg_x+yg_y=0$.

  Hence $\varphi_c|_{L_\infty}=P_d/Q_d$ is constant.

### 4.2 First blow-ups at infinity

After a linear change of coordinates, which keeps the Keller condition, the point is $[1{:}0{:}0]$. There
$\nu_{E_1}(x^iy^j)=-i$.
- **The restriction to $E_1$.** If $P$ and $Q$ have $x$-degree $n\ge1$ with $x^n$-coefficients $A,D\in K[y]$, then
  $P/Q$ restricts to $A(1/t_1)/D(1/t_1)$ on $E_1$. If the $x$-degrees differ, it restricts to $0$ or $\infty$.
- **The Keller condition.** The $x^{2n-1}$-coefficient of $[P,Q]$ is $n(AD'-A'D)$. A vanishing Wronskian forces
  $A=rD$ in characteristic 0. If both $x$-degrees are 0, then $[P,Q]=0$.

This corrects Theorem `thm:e1`, which is false as stated (`lean/README.md`, item 2). The fix covers every $m$, not
only $m=2$.

### 4.4 The bridge, read through its chart

The paper's pullback is $S^h(1,b,b^2(a+\tilde ab))$, the chart at the point $w_2=a$ of $E_2$ over $[1{:}0{:}0]$, with
$w_2=x/y^2$. Read through it, `bridge_collapse` rests on two premises:
- (P1) the two dicriticals lie over two distinct **free** points of this $E_2$;
- (P2) every member has pole order at most 1 on them.

**(P2) is not derived.** The paper defines $m$ as a degree, and degree 1 does not force pole order 1
(`lean/check_satellite.py`, check 7).

**Scope.** Under (P1) and (P2):
- one such dicritical forces $S\in\operatorname{span}\{1,y,x-ay^2\}$ (`bridge_one_center`);
- so no pencil of degree ≥ 3 has even one of them;
- in degree 2, the automorphism $(x-ay^2,y)$ has exactly one, consistent with Theorem R.

## 5. What a proof of Theorem R still needs

- **O1. The case split.** The paper's proof of `thm:main` says that two $m=1$ dicriticals "form either an adjacent
  pair or a bridge". This is asserted, not proved, and the positions in a resolution tree are more varied:
  - dicriticals over **different points** of $L_\infty$: a pencil can have several base points at infinity in
    general, as the non-Keller $(x,xy)$ shows, and whether a Keller counterexample's pencil can must be settled;
  - over **satellite points**: the point $a=\infty$ of $E_2$ in $(x+y^3,y)$, and deeper ones;
  - at **different depths**.

  A proof must cover every configuration of $E_\infty$ and $E_S$ (§3.3).
- **O2. (P2).** Derive pole order ≤ 1 from the definition of $m$, or restate the bridge with it as a hypothesis and
  supply a separate argument for higher pole order.
- **O3. $m\ge2$ at depth ≥ 2** (Proposition `prop:constant-form`), for every chain of centers, satellite ones
  included. Today there is a sketch for free chains only.
- **O4. The adjacent case** for every degree, not only $d=3$.
- **O5. Two small formalizations:** the chart step of 4.2 and the binary-form step of 4.1 in Lean.
- **O6. The Keller condition must be used globally.** Theorem R is false without it. $(x,xy)$, with Jacobian $x$, has
  two dicriticals at infinity in $\Lambda_{(1,1)}$, over $[1{:}0{:}0]$ and $[0{:}1{:}0]$; the second maps onto the line
  $u=0$ of non-proper values (`restatement_checks.py`, check 2). Arguments that never use $[P,Q]\in K^\times$ cannot
  prove Theorem R.

## 6. Tests any proof must pass

- **T1. Automorphisms have exactly one dicritical at infinity, of degree 1** (Corollary 2.2). Its position varies:
  - over the free point $a$ of $E_2$ for $(x-ay^2,y)$ (`lean/check_satellite.py`: $P/Q=\tilde a/a$ there);
  - over the satellite point $a=\infty$ of $E_2$, at depth 5, for $(x+y^3,y)$ (`restatement_checks.py`).

  A lemma that rules out a dicritical in either position is false.
- **T2. The identity.** Its dicritical at infinity is $L_\infty$ itself; Lemma 4.1 excludes only non-affine maps.
- **T3. Non-Keller maps.** These can have two dicriticals at infinity (O6).
- **T4. Every Keller map of degree ≥ 2** has two exceptional dicriticals in total, so only the count *at infinity*
  can be bounded (Corollary 2.3).

## 7. How the paper could be restated (the author's decision)

- **Option A (the conjecture).**
  - State Theorem R as the target, with Proposition 3.2: it is equivalent to the plane Jacobian conjecture.
  - Present §4 as partial results, and §5 as the open obligations.
  - Possible title: "Dicriticals at infinity of Keller maps: a reformulation of the plane Jacobian conjecture and
    local obstructions".
- **Option B (the lemmas).** Keep only what is proved, with no claim about the conjecture:
  - Lemmas 4.1 and 4.2 (leading-form arguments in the tradition of Magnus and Abhyankar–Moh);
  - the bridge for its equations under (P1) and (P2);
  - the corrected $E_1$ statement.

**Required in either option:**
- replace Theorem `thm:e1`, which is false as stated;
- replace the definition of a dicritical (line 81) by the standard one;
- withdraw the abstract's "We close the two-dicritical line";
- withdraw `rem:status`'s "Theorem 1.1 is unconditional".

## 8. Evidence ledger

Grades follow the review's conventions:
- **A** machine-checked;
- **B** a proof by hand from stated facts, or an exact computation outside Lean;
- **C** a sketch or a computation at fixed degrees.

The independence level is I1 (one team, one pipeline) unless stated.

| Claim | Grade | Evidence |
|---|---|---|
| Proposition 2.1 (the count) | B | the proof above, from (F1)–(F3) |
| Corollary 2.2 (automorphisms: exactly two, of degree 1) | B | the same; consistent with three executed examples; the outside referee's sketch agrees (I1–I2) |
| Corollary 2.3 (the theorem as worded fails) | B in general; exact in the examples | `main_statement_check.py`, `base_point_at_infinity_check.py`, `restatement_checks.py` |
| Proposition 3.2 (Theorem R ⟺ the conjecture) | B | the proof above |
| Lemma 4.1 (the line at infinity) | B | the proof above; check 1 of `base_point_at_infinity_check.py` |
| Lemma 4.2 (first blow-ups) | A for the algebra, B for the chart step | `E1Keller.lean`; `check_e1_index.py` |
| 4.4 (the bridge) | A for the equations; B for the geometric reading | `BridgeCollapse.lean`, `OneCenter.lean`, `check_satellite.py` |
| 4.5, 4.6 | C | the paper's sketch; the $d=3$ computation |

## 9. References

- Z. Jelonek, *The set of points at which a polynomial map is not proper*, Ann. Polon. Math. 58 (1993), no. 3,
  259–266, doi:10.4064/ap-58-3-259-266.
- Nguyen Van Chau, *Plane Jacobian problem for rational polynomials*, arXiv:0801.4138.
- Nguyen Van Chau, *Pencil of irreducible rational curves and plane Jacobian conjecture*, arXiv:0905.3939.
- S. S. Abhyankar and W. J. Heinzer, *Existence of dicritical divisors revisited*, arXiv:1508.06015.
- *Abhyankar's work on dicritical divisors*, arXiv:1707.06733. A survey; it states no equivalence between
  dicriticals and the conjecture.
- A. Białynicki-Birula and M. Rosenlicht, *Injective morphisms of real algebraic varieties*, Proc. Amer. Math. Soc.
  13 (1962), 200–203.
