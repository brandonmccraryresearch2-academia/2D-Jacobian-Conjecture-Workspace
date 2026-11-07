# HLRE v5 §15 Amendment — 2026-11-06

**Amends:** McCrary, B. D., & Muse (2026), *Hyper-Literal Reverse Engineering v5:
A Formal Methodological Alternative to the Traditional Scientific Method*,
24 September 2026 (11 pp., LaTeX with hyperref; filed PDF
`hlre_v5_methodology_4_5onc.pdf`, SHA-256
`38a57b2617fb1aa13b9b1624727b9649e4e2b9043196fb984621e69e645d7061`).

**Status:** APPROVED by Brandon D. McCrary 2026-11-06 ~14:19 CST. Prepared
2026-11-06 ~12:15 CST as `hlre-v5-section15-ALIGNMENT-DRAFT-2026-11-06.md`;
issued here as a versioned amendment. The filed HLRE v5 PDF is untouched —
byte-identical before and after this amendment — and v5 remains citable in its
published form, per the paper's own policy (p. 11): "Amendments beyond v5, if
any, will be versioned; v5 remains citable in its published form."

**Scope of this amendment:** only the closing-result paragraph of §15 (p. 10)
and the reference [9] entry (p. 11). The first half of §15 — the four v4.1
errors caught by the source gate, balance gate, framing audit, and taxonomy —
is left untouched; it was not re-audited here. No other section of HLRE v5 is
amended by this document.

**What this is:** the second half of Phase 3 §6.5 (GGHV dependency-closure
programme). Phase 3's RQ-E audit found Part III retraction/rescoping DONE, the
corrected Jelonek memo NOT DONE (draft delivered 2026-11-06 ~11:18 CST;
approved by Brandon 2026-11-06, memo replaced), and HLRE §15 alignment NOT
DONE. This amendment closes the §15 half.

---

## Correction log — what changes, and why

1. **Closing result, misdescribed as filed.** §15 grades "a Diophantine support
   obstruction eliminating the candidate … verified by exhaustive enumeration over
   the full polygon support". That phrasing describes at most the branches-(a,b)
   side (Davenport–Stothers chart / support enumeration), not the branch-(c)
   elimination as filed. The actual closing result is the Lean certificate
   `challenge_target` (Theorem `bc:thm:unconditional`, Part II of the combined
   paper): the Fpoly = Fpoly2 bridge + A1, A2, hsupp2 + the six data hypotheses,
   proved 2026-11-04 with no hypotheses and axioms exactly the permitted triple
   [propext, Classical.choice, Quot.sound]. The draft replacement says so, and
   keeps the rank computation in its true role — independent corroboration, not
   the load-bearing route.
2. **Companion [9] no longer "forthcoming" — but not deposited either.** The
   mathematical account now exists as the combined paper, *Elimination of the
   GGHV Normal Forms at Degree Pair (72,108), and Closure of the Two-Dicritical
   Line: A Certified Computational Audit in Three Parts* (67 pp., finalized
   2026-11-04; `combined_paper_final_2026-11-04.tex/.pdf`, repo root of the
   fork, main 7da907d). But its title differs from the [9] citation, and no
   Zenodo DOI for it is recorded in the paper — so [9] is neither "forthcoming"
   nor published as cited. The draft entry names the actual paper and flagged the title/deposition question; APPROVED 2026-11-06: [9] is the combined paper as named, title differing from the filed citation; no DOI invented.
3. **Grade A: retained — APPROVED by Brandon 2026-11-06 (was flagged as your grading call).** §12 grade A requires "independently corroborated prediction:
   pre-specified or protocol-frozen, quantitatively successful, independently
   tested, comparatively discriminating". What the record now supports:
   kernel-verified elimination at independence I1 (same data, independent code),
   plus the rank route as independent corroboration (3199×6054 Macaulay matrix,
   full row rank 3199 at p = 1000003 and p = 32003, two independent
   implementations FLINT and NumPy, negative controls). What it does NOT yet
   have: I3 outside-project rebuild (NOT DONE, Phase 3 RQ-C), and the explicit
   maximal minor is only PARTIAL (the filed form is a full inverse of the
   3199×3199 pivot block, not a named minor; pivot columns live only inside the
   79 MB binary INVERSE.pkl). Whether I1 kernel verification + rank
   corroboration meets §12's "independently tested" — and whether a deductive
   Lean certificate is a "prediction" in §12's sense at all — is a methodology
   judgement only you could make; made by your approval 2026-11-06. The approved text keeps grade A, and spells out the B fallback (grade B until I3 lands). Flag resolved by approval; the B fallback stands if the 'independently tested' reading is later rejected or I3 fails.

## Scope guard (unchanged — carried into the draft verbatim in substance)

Not "(72,108) excluded unconditionally" and not JC(2) proved. The application to
the Jacobian conjecture remains conditional on the correctness and exhaustiveness
of GGHV Proposition 4.3 (combined paper, Corollary `bc:cor:gghv`). Branch (c) is
unconditional *in Lean*; branches (a),(b) are kernel-verified (`main_theorem`,
same permitted triple, 2026-11-04); the (72,108) exclusion still rests on the
GGHV reduction chain, ledgered not re-derived.

---

## Filed §15 closing paragraph (verbatim, p. 10)

> The investigation's closing result — a Diophantine support obstruction
> eliminating the candidate — is graded A under the protocol: a deductive
> consequence of cataloged premises, verified by exhaustive enumeration over
> the full polygon support, independent of all fitted quantities. The full
> mathematical account is the companion paper [9].

## Replacement paragraph (APPROVED 2026-11-06)

> The investigation's closing result is the branch-(c) elimination of the
> GGHV (72,108) candidate, proved unconditionally in Lean as
> `challenge_target` (Theorem `bc:thm:unconditional`, Part II of [9]): the
> Fpoly = Fpoly2 bridge with the A1, A2, and hsupp2 certificates and the six
> data hypotheses, kernel-verified with no hypotheses and axioms exactly
> [propext, Classical.choice, Quot.sound]. Branches (a) and (b) are likewise
> kernel-verified (`main_theorem`, same permitted triple). It is graded A
> under the protocol **[APPROVED 2026-11-06 — grade A retained]**: a deductive consequence
> of cataloged premises, kernel-verified at independence I1 with the rank
> computation retained as independent corroboration (full row rank 3199 of
> the 3199×6054 Macaulay matrix at two primes, verified by two independent
> implementations). The grade does not extend past the certificate: the
> application to the Jacobian conjecture remains conditional on the
> correctness and exhaustiveness of GGHV Proposition 4.3, I3 outside-project
> replication is still awaited, and the explicit maximal minor is filed only
> in partial form. The full mathematical account is [9].

## Filed reference [9] (verbatim, p. 11)

> [9] B. D. McCrary and Muse, The Planar Jacobian Conjecture Below Degree 125:
> Closure of the GGHV (72,108) Case, companion paper, Zenodo, 2026
> (forthcoming).

## Replacement reference [9] (APPROVED 2026-11-06)

> [9] B. D. McCrary and Muse, Elimination of the GGHV Normal Forms at Degree
> Pair (72,108), and Closure of the Two-Dicritical Line: A Certified
> Computational Audit in Three Parts, 67 pp., finalized 2026-11-04
> (combined a/b/c paper; repo root, fork main 7da907d). **[APPROVED 2026-11-06 — [9] is this paper as named; the filed [9] title differs and no Zenodo DOI for it is recorded; no DOI invented, no title silently substituted.]**

---

## Honesty ledger — what this amendment does NOT do

- Does not amend the filed HLRE v5 PDF (that file is untouched) and does not
  create an HLRE v5.1 paper file — none exists; only the v5 PDFs and the
  `hlre-v5-1` skill are on file.
- Grade A retained by Brandon's approval 2026-11-06 (I1 kernel verification + rank corroboration accepted as meeting §12's "independently tested"); does not claim
  I3 replication, and does not present the rank route as the load-bearing proof
  (the Lean certificate is; the rank route corroborates).
- Does not touch the first half of §15 (the four v4.1 errors) or any other
  section of HLRE v5.
- Does not upgrade any claim grade anywhere else. Phase 3's verdicts stand:
  [GGV5] enumeration completeness UNVERIFIED, published [GGV1] §7 text NOT
  OBTAINED, Joseph Lemma 2.2 full text NOT FOUND.

## Sources checked for this amendment

- Filed §15 text and [9] entry: `~/workspace/user/files/hlre_v5_methodology_4_5onc.pdf`,
  pp. 10–11, extracted with pdftotext (this run); §12 grade table, p. 7.
  Re-verified 2026-11-07 against the filed PDF: both quoted filed passages
  match the PDF text verbatim. The two copies of the filed PDF on file
  (`hlre_v5_methodology_2_9eo9.pdf`, 2026-10-20, and
  `hlre_v5_methodology_4_5onc.pdf`, 2026-10-25) are byte-identical
  (SHA-256 `38a57b2617fb1aa13b9b1624727b9649e4e2b9043196fb984621e69e645d7061`).
- Phase 3 RQ-E audit (§6.5(3)): `~/workspace/goals/gghv-dependency-closure/hidden_files/phase3/working/leg_record_audit.md`
  lines 119–135, and the Phase 3 report `phase3_systematic_integrative_report_2026-11-06.md`
  §3.4.5 / §4.5 (HLRE §15 NOT DONE).
- Combined paper title, `bc:thm:unconditional`, rank route (two primes, FLINT +
  NumPy, corroboration role), scope guard: `~/workspace/research/2D-Jacobian-Conjecture-Workspace/combined_paper_final_2026-11-04.tex`
  (title block; Part II text; 67 pp., finalized 2026-11-04).
- `challenge_target` / branch-(c) proof status and axioms: MEMORY.md
  (proved 2026-11-04, no hypotheses, permitted triple); branches-(a,b)
  `main_theorem` axioms verified 2026-11-04 on lean-build-2.
- Explicit-minor PARTIAL verdict and I3 rebuild NOT DONE: Phase 3 report RQ-C.

---

## Filing note (2026-11-07 — not part of the approved text)

Recorded at filing preparation so the filed amendment stays honest without
silently editing the approved text above (HLRE's own no-silent-correction rule):

- The honesty ledger line "published [GGV1] §7 text NOT OBTAINED" is superseded
  as of 2026-11-07: the exhaustiveness campaign's leg 6 found the published
  [GGV1] §7 text via the CONICET repository (genuine version of record),
  confirmed the Thm 7.6(5) numbering, and discharged the `h76_5` premise.
  Joseph Lemma 2.2 full text is still NOT FOUND (institutional access the only
  untried route); [GGV5] enumeration completeness remains UNVERIFIED.
- The [9] entry's "fork main 7da907d" is the commit at which the combined paper
  was filed at the repo root; fork main has since advanced (filing commit
  484b5a8, comb commit 70ac1a3, rename commit 4be7471
  `branch_two_dicritical` → `dicriticals-at-infinity`). The citation is to the
  filing commit, not to current main.
- The §15 text above is reproduced verbatim from the approved draft
  (`hlre-v5-section15-ALIGNMENT-DRAFT-2026-11-06.md`, 132 lines); only the
  header, this filing note, and the re-verification line in "Sources checked"
  were added at preparation. No [DECISION] flag remained in the draft — the
  grade-A and [9] flags were resolved by Brandon's approval 2026-11-06, and
  only the issuance format was delegated (this standalone versioned amendment
  document, per the filed paper's own amendment policy).
