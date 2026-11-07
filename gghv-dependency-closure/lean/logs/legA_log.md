# Leg A — GGHV §2/§3 + Theorem 2.1 (E1–E4)
# Append-mode log. All Lean/Singular/Python runs on lean-build-3 via vm_lock.sh.
# Rule: no repo commits; scratch proofs + verdicts only.
# 2026-11-06 ~15:29 CST: leg started. Read inventory E1–E4, phase4_map §§5–9,
#   d1_assembly (593 lines) + d1_ggvstar redrow/prop329/ggv6 sections in full.
#   Retrieval leg CLOSED: published [GGV1] §7 NOT FOUND (15 routes), Joseph 2.2
#   NOT FOUND — carried as premises, no waiting. Legs B/C/F dirs empty at start.
# 2026-11-06 ~15:35 CST: main file drafted (self-contained, import Mathlib only,
#   no sorry): gghv_full_s2s3_2026-11-06.lean. New kernel vs Phase 1: bundled
#   table theorem; survivor-pair uniqueness; v_120 direction + en uniqueness;
#   d0 bound/forced-4; corner exponents; IM(j)=2(j+2) for all j; Im in Q;
#   factor count. Second-tool script check_legA_2026-11-06.py written.
# 2026-11-06 ~16:05 CST: VM lock acquire TIMED OUT after 1800 s; holder legC.
#   No force; local hardening instead: d0_forced_4 rewritten (obtain + omega,
#   dropping interval_cases without bounds); im_84_general rewritten as a
#   calc (ring + h7) so no tactic can close the goal early. Retrying acquire
#   with 3600 s timeout.
# 2026-11-06 ~16:38 CST: 2nd acquire KILLED by runtime SIGTERM after ~36 min
#   (session proc_1ed52824674c); lock never acquired. Lock still held by legC
#   (age 1622 s at check). Legs B/C/D have all drafted main files; none verified
#   yet (C log ends at start entry; B waiting on lock too). Leg A file re-checked
#   statically: 645 lines, grep 'sorry' hits only the comment word 'sorryAx'.
#   Retrying acquire with 1800 s timeout.
# 2026-11-06 ~17:05 CST: coordinator notice received.
#   (1) CORRECTION: the retrieval follow-up addressed to Leg B was sent to Leg A
#   in error — DISREGARDED; original brief stands. Note for the record: the
#   "published [GGV1] §7 NOT FOUND / Joseph 2.2 NOT FOUND" status cited in the
#   Leg A file header was read DIRECTLY from hidden_files/phase4/retrieval/
#   retrieval_log.md (closing verdicts table), not from the misrouted follow-up,
#   and carrying those items as explicit premises is already what the original
#   brief orders. No change to the file.
#   (2) VM LOCK TIME-SLICING (new rule): acquire PER verification run only,
#   release immediately after the run; never hold while writing proofs; max
#   continuous hold ~30 min. Leg A acquire (proc_a71957694dd9, 1800 s) still
#   pending at this writing; when it lands, run FULL + AXIOMS + second-tool,
#   then RELEASE at once.
# 2026-11-06 ~17:10 CST: 3rd acquire TIMED OUT after 1800 s; holder now legB
#   (lock passed legC -> legB during the wait). Retrying acquire (1800 s).
#   Per time-slicing rule, when it lands: FULL + AXIOMS + second-tool, then
#   RELEASE immediately.
# 2026-11-06 ~17:20 CST: VERIFICATION COMPLETE (lock acquired 4th attempt,
#   after legB; total hold ~10 min, released immediately after the runs).
#   VM: lean-build-3 RUNNING, Lean 4.34.0 (commit 293d5d0c0c3f), Singular 4.3.1,
#   Python second-tool check exit 0.
#   Invocation (Phase 1 pattern): cd branches_a_b/lean; LP=$(lake env printenv
#   LEAN_PATH); LEAN_PATH="$LP" lean --root=/tmp -o /tmp/gghv_full_s2s3.olean
#   /tmp/gghv_full_s2s3_2026-11-06.lean
#   FULL_EXIT=0 TIME=6s (log legA_full.log; only output a linter hint about an
#   unused binding _h2 in d0_bound — warning, not an error).
#   AXIOMS_EXIT=0 TIME=6s (log legA_axioms.log; appended #print axioms, 21 theorems):
#     zero axioms: gghv_table_full, discard_84_row, discard_120_row,
#       discard_924_row, discard_927_row, discard_721_via_sec3,
#       section2_survivors, pair_108_72_unique, pair_72_108_unique, thm5_endgame
#     [propext]: theorem21_minimal, theorem21_conditional_minimal,
#       red_rows_eliminated, survivors_exact
#     [propext, Classical.choice, Quot.sound]: discard_120_kernel_data,
#       discard_84_kernel_data, im_84_general, im_minor_84_rat, v_120_en_unique
#     [propext, Quot.sound]: d0_bound, d0_forced_4
#     sorryAx: ABSENT (grep count 0 in both logs).
#   Second tool (Python fractions, on VM): 28 checks, OVERALL ALL PASS, exit 0.
#   Singular 4.3.1 spot check: gcd(8,4)=4, gcd(2,7)=1, gcd(72,108)=36,
#   4+gcd(8,4)=8. (First Singular pipe misdirected stdin to /dev/null and
#   printed nothing; rerun with correct stdin gave the four values above.)
#   LOCK RELEASED by legA immediately after the runs (release rc=0).
#   VM NOT stopped (coordinator stops at checkpoints).
#   FINAL VERDICTS: E2 table KERNEL (bundled + uniqueness); red rows CONDITIONAL
#   (5 named premises); E3 kernel arithmetic + CONDITIONAL discard (prop329 +
#   link_120 carried); E4 kernel arithmetic + CONDITIONAL discard (link_84
#   carried); E1 theorem21_minimal CONDITIONAL on all 11 MinimalPremises fields
#   (none discharged — Legs B/C/F not landed/verified at verification time).
#   NO theorem21_unconditional claimed. NO repo commits.
