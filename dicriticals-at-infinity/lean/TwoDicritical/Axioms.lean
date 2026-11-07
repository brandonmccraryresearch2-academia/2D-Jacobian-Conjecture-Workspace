import TwoDicritical.BridgeCollapse
import TwoDicritical.CenterHypotheses
import TwoDicritical.E1Obstruction
import TwoDicritical.OneCenter
import TwoDicritical.E1Keller

/-! The axioms of the main results (`build.sh` checks each line). By kind (2026-10-13):
* the bridge equations: `choose_det_ne_zero` … `bridge_jacobian_eq_zero`, `bridge_one_center`,
  `zero_center_no_top_degree` (8);
* witnesses that the center hypotheses cannot be dropped from the formal statement: `bridgeConditions_pAuto` …
  `bridge_jacobian_needs_ne_zero` (5);
* `E₁`: `e1_degree_obstruction` and `not_keller_of_noLowTerms` are true, but about a set of monomials that is not the
  `E₁` condition (2); `thm_e1_false` and `e1P_not_noLowTerms` give the counterexample to Theorem `thm:e1` (2);
  `eq_C_mul_of_wronskian` … `jac2_eq_zero_of_natDegree_zero` give the corrected step (4). -/

#print axioms choose_det_ne_zero
#print axioms block_rank
#print axioms TwoDicritical.block_vanish
#print axioms TwoDicritical.block_vanish_two
#print axioms TwoDicritical.bridge_collapse
#print axioms TwoDicritical.bridge_jacobian_eq_zero
#print axioms TwoDicritical.bridgeConditions_pAuto
#print axioms TwoDicritical.bridge_collapse_needs_ne_zero
#print axioms TwoDicritical.bridge_collapse_needs_ne
#print axioms TwoDicritical.jacobian_auto
#print axioms TwoDicritical.bridge_jacobian_needs_ne_zero
#print axioms e1_degree_obstruction
#print axioms not_keller_of_noLowTerms
#print axioms TwoDicritical.bridge_one_center
#print axioms TwoDicritical.zero_center_no_top_degree
#print axioms TwoDicritical.thm_e1_false
#print axioms TwoDicritical.e1P_not_noLowTerms
#print axioms TwoDicritical.eq_C_mul_of_wronskian
#print axioms TwoDicritical.jac2_coeff_top
#print axioms TwoDicritical.e1_lead_proportional
#print axioms TwoDicritical.jac2_eq_zero_of_natDegree_zero
