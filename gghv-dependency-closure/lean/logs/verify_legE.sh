#!/bin/bash
# Leg E verification runner — run LOCALLY only after holding the VM lock
# (vm_lock.sh acquire legE). Wakes lean-build-3 if needed, scp's each
# Leg E file to /tmp on the VM, compiles it TWICE (FULL + AXIOMS) with the
# exact Phase 1 invocation, and pulls the logs back.
# Usage: bash verify_legE.sh [probe|all]   (default: all, probe first)
set -u
export PATH="$HOME/miniconda3/envs/jacobian-conjecture-2d/bin:$PATH"
VM=lean-build-3
ZONE=us-central1-a
PROJECT=gen-lang-client-0391037020
DIR="$HOME/workspace/research/tooling/phase4_legE"
LOGDIR="$DIR/logs_vm"
mkdir -p "$LOGDIR"

echo "=== VM status ==="
STATUS=$(gcloud compute instances describe "$VM" --zone="$ZONE" --project="$PROJECT" \
  --format='value(status)' 2>&1)
echo "lean-build-3 status: $STATUS"
if [ "$STATUS" != "RUNNING" ]; then
  echo "starting VM..."
  gcloud compute instances start "$VM" --zone="$ZONE" --project="$PROJECT" || exit 1
  echo "waiting 90 s for boot..."
  sleep 90
else
  echo "VM already running; waiting 60 s for ssh readiness..."
  sleep 60
fi

# The exact Phase 1 invocation (phase3_vm.sh strays + bridge_recheck):
#   cd <branches_a_b/lean project>; LP=$(lake env printenv LEAN_PATH);
#   LEAN_PATH="$LP" lean --root=/tmp -o /tmp/x.olean /tmp/x.lean
run_one() { # $1 = local .lean path, $2 = label
  local f="$1" label="$2"
  local base
  base=$(basename "$f" .lean)
  echo "=== scp $label ==="
  gcloud compute scp --zone="$ZONE" --project="$PROJECT" --tunnel-through-iap \
    "$f" "$VM:/tmp/$base.lean" || { echo "SCP FAIL $label"; return 1; }
  echo "=== FULL $label ==="
  local t0
  t0=$(date +%s)
  gcloud compute ssh "$VM" --zone="$ZONE" --project="$PROJECT" --tunnel-through-iap \
    --command="export PATH=\"\$HOME/toolchain/bin:\$PATH\"; cd \$HOME/repo/JC2D-branches_a_b_c_unified/branches_a_b/lean && LP=\$(lake env printenv LEAN_PATH) && LEAN_PATH=\"\$LP\" lean --root=/tmp -o /tmp/$base.olean /tmp/$base.lean" \
    > "$LOGDIR/${base}_full.log" 2>&1
  local rc=$?
  echo "FULL $label: exit $rc, $(( $(date +%s) - t0 )) s"
  grep -E "error|declaration uses .sorry.|sorryAx" "$LOGDIR/${base}_full.log" | head -20 || true
  return $rc
}

run_axioms() { # $1 = local .lean path, $2 = label, $3.. = theorem names
  local f="$1" label="$2"; shift 2
  local base
  base=$(basename "$f" .lean)
  local axf="/tmp/${base}_ax.lean"
  cp "$f" "$axf"
  for th in "$@"; do echo "#print axioms $th" >> "$axf"; done
  echo "=== AXIOMS $label ==="
  gcloud compute scp --zone="$ZONE" --project="$PROJECT" --tunnel-through-iap \
    "$axf" "$VM:/tmp/${base}_ax.lean" || { echo "SCP FAIL ax $label"; return 1; }
  local t0
  t0=$(date +%s)
  gcloud compute ssh "$VM" --zone="$ZONE" --project="$PROJECT" --tunnel-through-iap \
    --command="export PATH=\"\$HOME/toolchain/bin:\$PATH\"; cd \$HOME/repo/JC2D-branches_a_b_c_unified/branches_a_b/lean && LP=\$(lake env printenv LEAN_PATH) && LEAN_PATH=\"\$LP\" lean --root=/tmp -o /tmp/${base}_ax.olean /tmp/${base}_ax.lean" \
    > "$LOGDIR/${base}_axioms.log" 2>&1
  local rc=$?
  echo "AXIOMS $label: exit $rc, $(( $(date +%s) - t0 )) s"
  grep -E "depends on axioms|error|sorryAx" "$LOGDIR/${base}_axioms.log" | head -30 || true
  return $rc
}

MODE="${1:-all}"
if [ "$MODE" = "probe" ] || [ "$MODE" = "all" ]; then
  run_one "$DIR/probe_api_2026-11-06.lean" probe
fi
if [ "$MODE" = "all" ]; then
  run_one "$DIR/gghv_full_esquina3l_2026-11-06.lean" R8
  run_one "$DIR/gghv_full_central_gaps_2026-11-06.lean" R9
  run_one "$DIR/gghv_full_esquina_combined_2026-11-06.lean" R10
  run_one "$DIR/gghv_full_721_coeff_2026-11-06.lean" R11
  run_one "$DIR/gghv_full_remark_facelaws_2026-11-06.lean" R12
  run_one "$DIR/gghv_full_d1_theory_2026-11-06.lean" R13
  run_one "$DIR/gghv_full_d2_poly_2026-11-06.lean" R14
  run_one "$DIR/gghv_full_mn_gt1_2026-11-06.lean" R15
  run_one "$DIR/gghv_full_hybrid_slip_2026-11-06.lean" R16
  run_one "$DIR/gghv_full_mayores_2026-11-06.lean" R17
  run_one "$DIR/gghv_full_ggv1_2026-11-06.lean" INDEX
  # Axioms runs (theorem lists per file)
  run_axioms "$DIR/gghv_full_esquina3l_2026-11-06.lean" R8 \
    esq3_val_8_3 esq3_mn_sum esq3_dir_determination esq3_phi_aligned_impossible \
    esq3_phi_nonaligned_impossible esq3_lform_term_val esq3_lform_from_cube
  run_axioms "$DIR/gghv_full_central_gaps_2026-11-06.lean" R9 \
    central_cancellation central_item5 joseph_counting_contradiction \
    int_interval_card central_eq_central_from_joseph22
  run_axioms "$DIR/gghv_full_esquina_combined_2026-11-06.lean" R10 \
    esquina2_set_iff esquina2_combined esquina2_k1_pair esquina1_bundle_iff
  run_axioms "$DIR/gghv_full_721_coeff_2026-11-06.lean" R11 \
    face721_base_identity face721_coeffs face721_monic face721_natDegree_pow \
    face721_leading_coeff face721_factor_count face721_remainder_degree
  run_axioms "$DIR/gghv_full_remark_facelaws_2026-11-06.lean" R12 \
    alineados_2a_from_2b remark_ratio remark_st_scaling remark_en_scaling \
    tpow_exp_smul
  run_axioms "$DIR/gghv_full_d1_theory_2026-11-06.lean" R13 \
    cross_dot_identity dirLt_trans_halfplane dirLt_irrefl' dirLt_asymm' \
    succ_set_consecutive succOp_eq_of_isSuccFrom
  run_axioms "$DIR/gghv_full_d2_poly_2026-11-06.lean" R14 \
    pderiv_comm pderiv_comm01 \
    pbracket_antisymm pbracket_add_left pbracket_add_right pbracket_smul \
    pbracket_leibniz pbracket_jacobi pbracket_translate \
    joseph_counterexample_bracket
  run_axioms "$DIR/gghv_full_mn_gt1_2026-11-06.lean" R15 \
    mn_gt1_dir_mem mn_eq1_needs_b_gt1 gghv_uses_mn_gt1 gghv_uses_dir_mem
  run_axioms "$DIR/gghv_full_hybrid_slip_2026-11-06.lean" R16 \
    hybrid_arith_249 hybrid_arith_288 hybrid_slot_249 hybrid_slot_288 \
    hybrid_slot_927 hybrid_slot_721
  run_axioms "$DIR/gghv_full_mayores_2026-11-06.lean" R17 \
    dirValQ_rat_smul mayores_termination_descent mayores_chain_terminates \
    mayores_cocientes_ratio mayores_cocientes_conditional \
    mayores_full_conditional
fi
echo "=== DONE. Logs in $LOGDIR ==="
ls -la "$LOGDIR"
