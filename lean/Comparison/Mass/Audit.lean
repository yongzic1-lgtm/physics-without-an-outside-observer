import Comparison.Mass

/-!
# Axiom audit of the road to the masses

Build with `lake build Comparison.Mass.Audit`. Every line must read
`depends on axioms: [propext, Classical.choice, Quot.sound]` or a part of it; an unfinished proof would
add an entry to that list.
-/

-- Basic.lean
#print axioms Comparison.prod_updateCol'
#print axioms Comparison.trace_adjugate_mul_eq
#print axioms Comparison.hasDerivAt_det
#print axioms Comparison.adjugate_rank_one
#print axioms Comparison.trace_smul_vecMulVec_mul
#print axioms Comparison.norm_le_of_pos_eigen
#print axioms Comparison.left_eigen_defect

-- Harmonic.lean
#print axioms Comparison.harmonic_const
#print axioms Comparison.fwd_all
#print axioms Comparison.bwd_all
#print axioms Comparison.mem_fwd
#print axioms Comparison.mem_bwd
#print axioms Comparison.step_connected
#print axioms Comparison.rtg_mono
#print axioms Comparison.stepR_mulVec
#print axioms Comparison.stepR_vecMul
#print axioms Comparison.card_predSet
#print axioms Comparison.card_succSet
#print axioms Comparison.kernel_right
#print axioms Comparison.kernel_left
#print axioms Comparison.bDD_sq
#print axioms Comparison.mulVec_split_real
#print axioms Comparison.vecMul_split_real
#print axioms Comparison.glue_A
#print axioms Comparison.glue_D
#print axioms Comparison.stepR_glue_A
#print axioms Comparison.stepR_glue_D
#print axioms Comparison.glue_vecMul_A
#print axioms Comparison.glue_vecMul_D
#print axioms Comparison.watched_kernel_right
#print axioms Comparison.watched_kernel_left

-- Simple.lean
#print axioms Comparison.stepR_map
#print axioms Comparison.det_law_real
#print axioms Comparison.Dplus_hasDerivAt
#print axioms Comparison.law_deriv_quarter
#print axioms Comparison.hasDerivAt_det_one_sub
#print axioms Comparison.stepR_mulVec_one
#print axioms Comparison.one_vecMul_stepR
#print axioms Comparison.law_quarter_mulVec
#print axioms Comparison.law_quarter_vecMul
#print axioms Comparison.det_law_quarter
#print axioms Comparison.adj_law_quarter_exists
#print axioms Comparison.one_dot_stepR_one
#print axioms Comparison.adj_law_quarter
#print axioms Comparison.kappaLaw_pos
#print axioms Comparison.det_availableTransitionsOp
#print axioms Comparison.availableTransitionsOp_quarter
#print axioms Comparison.availableTransitionsOp_hasDerivAt
#print axioms Comparison.watched_kernel_right'
#print axioms Comparison.watched_kernel_left'
#print axioms Comparison.det_one_sub_watched
#print axioms Comparison.adj_watched_exists
#print axioms Comparison.residue_general
#print axioms Comparison.residue_law
#print axioms Comparison.residue_law_form

-- Perron.lean
#print axioms Comparison.det_real_eigen
#print axioms Comparison.perron_unique
#print axioms Comparison.isPerron_of_pos
#print axioms Comparison.solvable
#print axioms Comparison.isBigO_cube_at_zero
#print axioms Comparison.isBigO_cube_tendsto
#print axioms Comparison.WeightedWalk.nonempty
#print axioms Comparison.WeightedWalk.at_zero
#print axioms Comparison.WeightedWalk.entry_tendsto
#print axioms Comparison.WeightedWalk.continuousAt
#print axioms Comparison.WeightedWalk.adj_rank_one
#print axioms Comparison.WeightedWalk.isPerron_zero
#print axioms Comparison.hasDerivAt_det_sub
#print axioms Comparison.perron_exists
#print axioms Comparison.perronRoot_spec
#print axioms Comparison.perronRoot_zero
#print axioms Comparison.tendsto_isBigO_one
#print axioms Comparison.perron_expansion
#print axioms Comparison.abs_log_one_add_le
#print axioms Comparison.abs_log_one_add_sub_le
#print axioms Comparison.perron_log

-- Velocity.lean
#print axioms Comparison.stepT_mulVec_real
#print axioms Comparison.stepT_vecMul_real
#print axioms Comparison.exp_taylor2
#print axioms Comparison.isBigO_cube_mul_left
#print axioms Comparison.lastDirectionP0_mulVec
#print axioms Comparison.lastDirectionP0_vecMul
#print axioms Comparison.sum_piU
#print axioms Comparison.lastDirectionWalk_weighted
#print axioms Comparison.gLastDirectionZ_pred_sum
#print axioms Comparison.gLastDirectionZ_sum
#print axioms Comparison.alongH_count
#print axioms Comparison.gLastDirection_pred_sum
#print axioms Comparison.lastDirectionP1_mulVec_one
#print axioms Comparison.lastDirectionP2_mulVec_one
#print axioms Comparison.lastDirectionP1_mulVec_g
#print axioms Comparison.sum_alongH
#print axioms Comparison.lastDirection_v
#print axioms Comparison.lastDirection_poisson
#print axioms Comparison.lastDirection_g_centred
#print axioms Comparison.lastDirection_sigma
#print axioms Comparison.lastDirection_velocity
#print axioms Comparison.lastDirection_variance_is_spread
#print axioms Comparison.watchOf_stepR
#print axioms Comparison.watchOf_apply
#print axioms Comparison.watchOf_entry_isBigO
#print axioms Comparison.toBlock_add'
#print axioms Comparison.toBlock_smul'
#print axioms Comparison.watchOf_add
#print axioms Comparison.watchOf_smul
#print axioms Comparison.watchOf_lin
#print axioms Comparison.glue_one
#print axioms Comparison.bAA_one
#print axioms Comparison.bDA_one
#print axioms Comparison.one_bAA
#print axioms Comparison.one_bAD
#print axioms Comparison.watchedR_rows
#print axioms Comparison.watchedR_cols
#print axioms Comparison.card_availableTransitions
#print axioms Comparison.piA_eq
#print axioms Comparison.availableTransitions_witness_all
#print axioms Comparison.availableTransitions_witness
#print axioms Comparison.adj_watched_ne
#print axioms Comparison.transition_taylor_entry
#print axioms Comparison.transition_remainder
#print axioms Comparison.watched_weighted
#print axioms Comparison.transitionX_eq
#print axioms Comparison.sum_availableTransitions
#print axioms Comparison.sum_closed
#print axioms Comparison.count_real
#print axioms Comparison.transitionAA_one
#print axioms Comparison.transitionDA_one
#print axioms Comparison.one_bAD_eq
#print axioms Comparison.one_bAD_bDD_eq
#print axioms Comparison.watchOf_dot
#print axioms Comparison.transition_counts
#print axioms Comparison.watched_transition_sum
#print axioms Comparison.watched_v
#print axioms Comparison.inventory_velocity

-- Return72.lean
#print axioms Comparison.repReturn_hasSum
#print axioms Comparison.I_div_four_sq
#print axioms Comparison.zPow_sq
#print axioms Comparison.zPow_even
#print axioms Comparison.repReturn_real
#print axioms Comparison.repR_one
#print axioms Comparison.repR_two
#print axioms Comparison.repR_three
#print axioms Comparison.repR_four
#print axioms Comparison.repR_five
#print axioms Comparison.repR_six
#print axioms Comparison.repR_bound
#print axioms Comparison.repR_pos
#print axioms Comparison.repR_summable
#print axioms Comparison.N1_hasSum
#print axioms Comparison.N1_bounds

-- Angle.lean
#print axioms Comparison.tilt_weighted
#print axioms Comparison.charF_hasDerivAt_s
#print axioms Comparison.charF_hasDerivAt_l
#print axioms Comparison.tiltC_continuous
#print axioms Comparison.tiltC'_continuous
#print axioms Comparison.charM_continuous
#print axioms Comparison.charFs_continuous
#print axioms Comparison.charFl_continuous
#print axioms Comparison.tiltC_zero
#print axioms Comparison.adj_map_real
#print axioms Comparison.angle_of_zero
#print axioms Comparison.real_weight_real_root
#print axioms Comparison.uniform_phase_zero
#print axioms Comparison.quad_ne_zero_of_small
#print axioms Comparison.D_plus_disc
#print axioms Comparison.lawP_weighted
#print axioms Comparison.lawP_rate
#print axioms Comparison.transition_total
#print axioms Comparison.availableTransitions_angle_rate
#print axioms Comparison.one_transition_angle_rate
#print axioms Comparison.proton_availableTransitions_ratio

-- Taylor.lean
#print axioms Comparison.vR_sum
#print axioms Comparison.line_hasDerivAt
#print axioms Comparison.step_first_order
#print axioms Comparison.line_contDiff
#print axioms Comparison.line_taylor
#print axioms Comparison.taylor_step
#print axioms Comparison.critical_operator
#print axioms Comparison.cos_six
#print axioms Comparison.residual_bound
#print axioms Comparison.dispersion_poly
#print axioms Comparison.inverse_step
#print axioms Comparison.cos_mul_bound
#print axioms Comparison.dispersion_series

-- Shift.lean
#print axioms Comparison.lawSrc_hasDerivAt_J
#print axioms Comparison.lawSrc_hasDerivAt_u
#print axioms Comparison.lawSrc_mat_continuous
#print axioms Comparison.zero_shift_law
#print axioms Comparison.zero_shift_form
