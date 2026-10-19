import Comparison.Existence.Commutant
import Comparison.Existence.Covariance
import Comparison.Existence.EvenFour
import Comparison.Existence.Exterior
import Comparison.Existence.Planes
import Comparison.Existence.Idempotent
import Comparison.Existence.JointStep
import Comparison.Existence.Spin
import Comparison.Existence.Turn
import Comparison.JointCells.FirstPairing

/-! Audit of the theorems the two maps cite, group 2 (10 files). -/

#print axioms Comparison.finrank_turnsTen
#print axioms Comparison.finrank_keepL
#print axioms Comparison.pair_turns_finrank
#print axioms Comparison.pair_keepL_finrank
#print axioms Comparison.fock_normal
#print axioms Comparison.finrank_su5
#print axioms Comparison.finrank_plane5
#print axioms Comparison.finrank_lastDirection5
#print axioms Comparison.turns_chain
#print axioms Comparison.ordProd
#print axioms Comparison.ordProd_Jx_vac
#print axioms Comparison.εv_anticomm
#print axioms Comparison.ιv_εv_add
#print axioms Comparison.ιv_anticomm
#print axioms Comparison.Jv_anticomm
#print axioms Comparison.Jv_mul_self
#print axioms Comparison.colStep
#print axioms Comparison.extMap_conj_Jv
#print axioms Comparison.cl
#print axioms Comparison.clWord
#print axioms Comparison.evenToFour_singlet_line
#print axioms Comparison.evenToFour_line_line
#print axioms Comparison.line_eq_i_singlet_line
#print axioms Comparison.evenToFour_surjective
#print axioms Comparison.evenToFour_injective
#print axioms Comparison.evenToFour_bijective
#print axioms Comparison.evenEquivFour_apply
#print axioms Comparison.εx_ιx_add
#print axioms Comparison.εx_εx_add
#print axioms Comparison.ιx_ιx_add
#print axioms Comparison.Jx_mul_self
#print axioms Comparison.Jx_anticomm
#print axioms Comparison.shortest_loop
#print axioms Comparison.Jx_mul_Jx
#print axioms Comparison.Nx_Tx
#print axioms Comparison.Tx_Jx
#print axioms Comparison.volume_sq
#print axioms Comparison.half_anticomm
#print axioms Comparison.half_prod
#print axioms Comparison.plane_step_outside
#print axioms Comparison.petersen_steps
#print axioms Comparison.petersen_srg
#print axioms Comparison.planeLap_eigen
#print axioms Comparison.planeLap_charpoly
#print axioms Comparison.contrast_sum
#print axioms Comparison.projectors
#print axioms Comparison.k_sum
#print axioms Comparison.k_values
#print axioms Comparison.perfect_matchings
#print axioms Comparison.T_formula
#print axioms Comparison.k_second_form
#print axioms Comparison.k_idem
#print axioms Comparison.Jv_mul_extMap
#print axioms Comparison.jointStep_rename
#print axioms Comparison.jointStep_inv
#print axioms Comparison.connStep_rename
#print axioms Comparison.connStep_inv
#print axioms Comparison.Jx_single
#print axioms Comparison.Tx_comm_chain
#print axioms Comparison.Tx_comm_disjoint
#print axioms Comparison.rotor_mul
#print axioms Comparison.rotor_two_pi
#print axioms Comparison.rotor_conj_a
#print axioms Comparison.rotor_conj_b
#print axioms Comparison.half_loop_sq
#print axioms Comparison.loop_counts
#print axioms Comparison.phase_compl
#print axioms Comparison.Tx_eq_sum_degrees
#print axioms Comparison.exp_parallel_turn
#print axioms Comparison.JointCells.whole_sq
#print axioms Comparison.JointCells.moved_clocks_held
