import Comparison.ArticleStatements.CommonClock
import Comparison.ArticleStatements.Geometry
import Comparison.ArticleStatements.MeetingPhase
import Comparison.ArticleStatements.MixedMoment
import Comparison.ArticleStatements.Radar
import Comparison.ArticleStatements.SectorSeries
import Comparison.ArticleStatements.SectorSum
import Comparison.Colour.Arcs
import Comparison.Colour.ClosedAvailableTransitions
import Comparison.Colour.BoundStates
import Comparison.Colour.GramTerm
import Comparison.Colour.Inventory
import Comparison.Colour.Light
import Comparison.Colour.Proton
import Comparison.Colour.Singlets
import Comparison.Colour.Tableaux
import Comparison.Colour.Visits
import Comparison.Elements.Divisions
import Comparison.Elements.Half
import Comparison.Elements.KeepL
import Comparison.Elements.MixedStates
import Comparison.Elements.Observables
import Comparison.Elements.OneModel
import Comparison.Elements.OneModelGeneral
import Comparison.Elements.OneThing
import Comparison.Elements.Overlap
import Comparison.Elements.OwnPast
import Comparison.Elements.Partner
import Comparison.Elements.SixDirections
import Comparison.Elements.Turns
import Comparison.Elements.TwoThings
import Comparison.Existence.Born
import Comparison.Existence.AvailableTransitions
import Comparison.Existence.Closing
import Comparison.Existence.Coin
import Comparison.Existence.CovDiff
import Comparison.Existence.Gauge
import Comparison.Existence.LastDirectionSplit
import Comparison.Existence.Holds
import Comparison.Existence.IharaBass
import Comparison.Existence.Excursion
import Comparison.Existence.LogDet
import Comparison.Existence.Matter
import Comparison.Existence.Moments
import Comparison.Existence.Motion
import Comparison.Existence.Pair
import Comparison.Existence.Plaquette
import Comparison.Existence.PlaquetteData
import Comparison.Existence.Return
import Comparison.Existence.Sign
import Comparison.Existence.Table
import Comparison.Existence.Walk
import Comparison.Existence.Words
import Comparison.Existence.Zero
import Comparison.JointCells.PlaneColour
import Comparison.JointCells.Patterns
import Comparison.JointCells.PairSign
import Comparison.Law.Bass
import Comparison.Law.Carried
import Comparison.Law.Composite
import Comparison.Law.LongZero
import Comparison.Law.Meetings
import Comparison.Law.Rows
import Comparison.Law.Rule
import Comparison.Law.Source
import Comparison.Mass.Angle
import Comparison.Mass.Harmonic
import Comparison.Mass.Perron
import Comparison.Mass.Return72
import Comparison.Mass.Shift
import Comparison.Mass.Simple
import Comparison.Mass.Taylor
import Comparison.Mass.Velocity
import Comparison.RuleAndLaw.Bridges
import Comparison.RuleAndLaw.CriticalGerm
import Comparison.RuleAndLaw.FactorsA
import Comparison.RuleAndLaw.FactorsB
import Comparison.RuleAndLaw.FactorsC
import Comparison.RuleAndLaw.Positivity
import Comparison.RuleAndLaw.RuleReadsLaw
import Comparison.WholePicture.Cells
import Comparison.WholePicture.Circulation
import Comparison.WholePicture.Connection
import Comparison.WholePicture.Curvature
import Comparison.WholePicture.Geometry
import Comparison.WholePicture.Green
import Comparison.WholePicture.Moment
import Comparison.WholePicture.MomentSubspaces
import Comparison.WholePicture.OneArc
import Comparison.WholePicture.Polar
import Comparison.WholePicture.SecondVariation
import Comparison.WholePicture.TheLaw
import Comparison.WholePicture.TraceFive

/-! Audit of the theorems the two maps cite, group 1 (93 files). -/

#print axioms Comparison.ArticleStatements.Clock.loops_close_of_clock
#print axioms Comparison.ArticleStatements.Clock.clock_of_loops_close
#print axioms Comparison.ArticleStatements.Clock.clock_iff_loops
#print axioms Comparison.ArticleStatements.Clock.clock_unique
#print axioms Comparison.ArticleStatements.swap_mul_swap
#print axioms Comparison.ArticleStatements.swap_singlet
#print axioms Comparison.ArticleStatements.Eop_mul_Eop
#print axioms Comparison.ArticleStatements.swap_mul_Eop
#print axioms Comparison.ArticleStatements.Eop_mul_swap
#print axioms Comparison.ArticleStatements.L_proj
#print axioms Comparison.ArticleStatements.trace_proj
#print axioms Comparison.ArticleStatements.det_planeMat
#print axioms Comparison.ArticleStatements.Phase.charpoly_Gplus
#print axioms Comparison.ArticleStatements.kappa_one_against_four
#print axioms Comparison.ArticleStatements.kappa_plane_against_colour
#print axioms Comparison.ArticleStatements.Radar.radar_velocity
#print axioms Comparison.ArticleStatements.Radar.radar_gamma
#print axioms Comparison.ArticleStatements.Radar.radar_echo
#print axioms Comparison.ArticleStatements.Radar.tanh_quarter
#print axioms Comparison.ArticleStatements.Radar.tan_sq_pi_div_eight
#print axioms Comparison.ArticleStatements.Radar.radar_quarter
#print axioms Comparison.ArticleStatements.Series.norm_Ztop_eq_iff
#print axioms Comparison.ArticleStatements.Series.theta_bar_series
#print axioms Comparison.ArticleStatements.lawK_posDef
#print axioms Comparison.ArticleStatements.lawWeight_pos
#print axioms Comparison.ArticleStatements.law_pos
#print axioms Comparison.ArticleStatements.lawWeight_conj_eq
#print axioms Comparison.ArticleStatements.sectorSum_zero
#print axioms Comparison.ArticleStatements.norm_sectorSum_le
#print axioms Comparison.ArticleStatements.norm_sectorSum_eq_iff
#print axioms Comparison.ArticleStatements.SectorSource.prop115
#print axioms Comparison.ArticleStatements.SectorSource.prop115_max_iff
#print axioms Comparison.ArticleStatements.SectorSource.theta_bar_zero
#print axioms Comparison.card_arcs
#print axioms Comparison.arcs_leaving
#print axioms Comparison.arcs_entering
#print axioms Comparison.tau_bounds
#print axioms Comparison.blockDD_sq
#print axioms Comparison.det_closed
#print axioms Comparison.det_availableTransitions
#print axioms Comparison.availableTransitions_counts
#print axioms Comparison.availableTransitions_steps
#print axioms Comparison.watched_rows
#print axioms Comparison.watched_cols
#print axioms Comparison.five_lines
#print axioms Comparison.colour_product_oriented
#print axioms Comparison.eps_lines
#print axioms Comparison.baryon_lands_on_plane
#print axioms Comparison.L_planeRel
#print axioms Comparison.meson_either_end
#print axioms Comparison.meson_lands_on_singlet
#print axioms Comparison.L_singlet
#print axioms Comparison.pairing_gram
#print axioms Comparison.gram_levels
#print axioms Comparison.trace_gram
#print axioms Comparison.det_F0
#print axioms Comparison.gramTerm_forms
#print axioms Comparison.weight_moves_zero
#print axioms Comparison.trace_L_sq
#print axioms Comparison.card_BL
#print axioms Comparison.card_Bhbar
#print axioms Comparison.volume_BL
#print axioms Comparison.volume_Bhbar
#print axioms Comparison.deriv_volume_Bhbar
#print axioms Comparison.b_forms
#print axioms Comparison.transition_weight
#print axioms Comparison.transition_inventory
#print axioms Comparison.inventory_by_lines
#print axioms Comparison.inventory_trace
#print axioms Comparison.inventory_rates
#print axioms Comparison.pole_of_count
#print axioms Comparison.rest_poles
#print axioms Comparison.record_count
#print axioms Comparison.three_readings
#print axioms Comparison.pole_reading_value
#print axioms Comparison.arcs_along
#print axioms Comparison.delta_counts
#print axioms Comparison.log_five_halves
#print axioms Comparison.pole_terms
#print axioms Comparison.protonPole_bounds
#print axioms Comparison.protonPole_pull
#print axioms Comparison.W_eq
#print axioms Comparison.alphaG_eq
#print axioms Comparison.alphaG_bounds
#print axioms Comparison.gravity_pull
#print axioms Comparison.gravity_logs
#print axioms Comparison.planck_from_proton
#print axioms Comparison.planck_mass
#print axioms Comparison.meson_singlet
#print axioms Comparison.levi_kept
#print axioms Comparison.baryon_singlet
#print axioms Comparison.no_singlet
#print axioms Comparison.tableaux_counts
#print axioms Comparison.excursion_system
#print axioms Comparison.excursion_system_unique
#print axioms Comparison.GP_eq
#print axioms Comparison.GP_one
#print axioms Comparison.GP_deriv
#print axioms Comparison.GP_denominator
#print axioms Comparison.xc_gt_one
#print axioms Comparison.xc_root
#print axioms Comparison.regression
#print axioms Comparison.pion_radius
#print axioms Comparison.vector_pole
#print axioms Comparison.divSign
#print axioms Comparison.Kept
#print axioms Comparison.Moved
#print axioms Comparison.kept_iff
#print axioms Comparison.moved_iff
#print axioms Comparison.kept_xor_moved
#print axioms Comparison.card_kept
#print axioms Comparison.card_moved
#print axioms Comparison.card_kept_compl
#print axioms Comparison.four_kinds
#print axioms Comparison.card_kept_ten
#print axioms Comparison.card_moved_ten
#print axioms Comparison.six_divisions
#print axioms Comparison.P3_division_keeps_ten
#print axioms Comparison.signD
#print axioms Comparison.half
#print axioms Comparison.half_mul_self
#print axioms Comparison.half_transpose_mul
#print axioms Comparison.half_conjTranspose_mul
#print axioms Comparison.half_pow_four
#print axioms Comparison.half_mul_half_compl
#print axioms Comparison.halves_iff
#print axioms Comparison.halves_solutions
#print axioms Comparison.half_eq
#print axioms Comparison.no_real_half
#print axioms Comparison.metric
#print axioms Comparison.half_on_sets
#print axioms Comparison.sets_count
#print axioms Comparison.pf_conj
#print axioms Comparison.det_eq_one_of_keeps_J
#print axioms Comparison.keeps_singlet_iff
#print axioms Comparison.kron_swap_comm
#print axioms Comparison.keeps_L_iff
#print axioms Comparison.neg_iff_I_smul
#print axioms Comparison.sum_mixedLine_sq_le
#print axioms Comparison.trace_prod_disagreement
#print axioms Comparison.disagreement_mixed_ge
#print axioms Comparison.disagreement_mixture_ge
#print axioms Comparison.τ
#print axioms Comparison.trace_obs_mul
#print axioms Comparison.span_obs_eq_hermitian
#print axioms Comparison.finrank_hermitian
#print axioms Comparison.obs_mul_J
#print axioms Comparison.eq_sum_coord
#print axioms Comparison.distinction_iff
#print axioms Comparison.coord_sum
#print axioms Comparison.distinction_sq
#print axioms Comparison.P3_holds
#print axioms Comparison.P3_two
#print axioms Comparison.not_P3_zero
#print axioms Comparison.distinctionN_one_eq_zero
#print axioms Comparison.diagWitness_isDistinction
#print axioms Comparison.diagWitness_sq_ne
#print axioms Comparison.one_model
#print axioms Comparison.Partner.isDistinctionH_iff
#print axioms Comparison.Partner.P3H_iff
#print axioms Comparison.Partner.one_model_general
#print axioms Comparison.Four
#print axioms Comparison.J
#print axioms Comparison.Θ
#print axioms Comparison.J_transpose
#print axioms Comparison.J_mul_conjTranspose
#print axioms Comparison.Θ_Θ
#print axioms Comparison.Θ_orth
#print axioms Comparison.Θ_norm
#print axioms Comparison.Θ_smul
#print axioms Comparison.IsDistinction
#print axioms Comparison.commutes_Θ_iff
#print axioms Comparison.γ
#print axioms Comparison.γ_isDistinction
#print axioms Comparison.clifford
#print axioms Comparison.γ_mul_self
#print axioms Comparison.γ_anticomm
#print axioms Comparison.γ_prod
#print axioms Comparison.γv
#print axioms Comparison.side
#print axioms Comparison.γv_mul_self
#print axioms Comparison.anticomm_γv
#print axioms Comparison.side_mul_self
#print axioms Comparison.side_add_side_neg
#print axioms Comparison.side_mul_side_neg
#print axioms Comparison.trace_side
#print axioms Comparison.overlap
#print axioms Comparison.overlap_symm
#print axioms Comparison.partnerOp
#print axioms Comparison.partnerOp_eq_self_iff
#print axioms Comparison.partnerTwo
#print axioms Comparison.partnerTwo_kron
#print axioms Comparison.partnerTwo_swap
#print axioms Comparison.partnerTwo_Eop
#print axioms Comparison.partnerTwo_L
#print axioms Comparison.Partner
#print axioms Comparison.Partner.inner_self_Θ
#print axioms Comparison.Partner.norm_Θ
#print axioms Comparison.Partner.finrank_eq
#print axioms Comparison.Partner.exists_normal_basis
#print axioms Comparison.Partner.coord_Θ
#print axioms Comparison.sixP3
#print axioms Comparison.sixP1
#print axioms Comparison.sixP3_transpose
#print axioms Comparison.sixP1_transpose
#print axioms Comparison.pf
#print axioms Comparison.pf_J
#print axioms Comparison.sign_of_time
#print axioms Comparison.pf_P1_six
#print axioms Comparison.det_eq_pf_sq
#print axioms Comparison.det_cone
#print axioms Comparison.su4
#print axioms Comparison.gen
#print axioms Comparison.su4_eq_span
#print axioms Comparison.finrank_su4
#print axioms Comparison.line_turns_singlet
#print axioms Comparison.plane_keeps_singlet
#print axioms Comparison.sp2
#print axioms Comparison.sp2_eq_span
#print axioms Comparison.finrank_sp2
#print axioms Comparison.fifteen_eq_ten_add_five
#print axioms Comparison.keeps_partner_iff
#print axioms Comparison.plane_bijective
#print axioms Comparison.plane_fst_eq_zero_iff
#print axioms Comparison.gen_acts
#print axioms Comparison.Two
#print axioms Comparison.relOf
#print axioms Comparison.MΩ
#print axioms Comparison.Ω
#print axioms Comparison.Ω_eq_sum
#print axioms Comparison.Ω_basis_free
#print axioms Comparison.Ω_norm
#print axioms Comparison.same_from_either_thing
#print axioms Comparison.swap
#print axioms Comparison.Eop
#print axioms Comparison.L
#print axioms Comparison.L_eq_swap_singlet
#print axioms Comparison.disagreeSet
#print axioms Comparison.agreement
#print axioms Comparison.count
#print axioms Comparison.count_rel
#print axioms Comparison.L_rel
#print axioms Comparison.rel_inner
#print axioms Comparison.finrank_eigenspace_L_six
#print axioms Comparison.finrank_eigenspace_L_two
#print axioms Comparison.finrank_eigenspace_L_neg_two
#print axioms Comparison.eigenspace_L_other
#print axioms Comparison.disagreement
#print axioms Comparison.disagreement_eq_zero_iff
#print axioms Comparison.disagreement_sum_sq
#print axioms Comparison.sum_lineOf_sq
#print axioms Comparison.lineOf_unit
#print axioms Comparison.disagreement_prodRel_ge
#print axioms Comparison.doubled_det
#print axioms Comparison.bornM_trace
#print axioms Comparison.bornM_trace_nonneg
#print axioms Comparison.born_mixed
#print axioms Comparison.log_doubled
#print axioms Comparison.lastDirectionRel
#print axioms Comparison.card_excursionStates
#print axioms Comparison.undo_state_only_from_place
#print axioms Comparison.excursionStates_eq_reach
#print axioms Comparison.watched_inflow
#print axioms Comparison.watched_outflow
#print axioms Comparison.availableTransitions_along
#print axioms Comparison.availableTransitions_total
#print axioms Comparison.availableTransitions_shares
#print axioms Comparison.availableTransitions_up
#print axioms Comparison.schur_det
#print axioms Comparison.schur_inv
#print axioms Comparison.schur_diff
#print axioms Comparison.schurR_diff
#print axioms Comparison.schurL_diff
#print axioms Comparison.residue_simple_zero
#print axioms Comparison.zero_shift
#print axioms Comparison.coin
#print axioms Comparison.coin_apply
#print axioms Comparison.coin_transpose
#print axioms Comparison.coin_mul_self
#print axioms Comparison.coin_orthogonal
#print axioms Comparison.coin_unitary
#print axioms Comparison.coin_column
#print axioms Comparison.coin_mulVec_ones
#print axioms Comparison.involutions_ones
#print axioms Comparison.stepU_eq
#print axioms Comparison.stepU_orthogonal
#print axioms Comparison.covDiff_rename
#print axioms Comparison.covDiff_near_one
#print axioms Comparison.covDiff_half
#print axioms Comparison.frobSq_half
#print axioms Comparison.half_mass
#print axioms Comparison.Connection
#print axioms Comparison.Connection.rename
#print axioms Comparison.hol
#print axioms Comparison.hol_rename
#print axioms Comparison.hol_rename_closed
#print axioms Comparison.trace_hol_isFact
#print axioms Comparison.open_transport_any
#print axioms Comparison.four_cycles
#print axioms Comparison.square
#print axioms Comparison.square_closes
#print axioms Comparison.card_squares
#print axioms Comparison.projD
#print axioms Comparison.thetaD
#print axioms Comparison.massForm
#print axioms Comparison.massForm_self_eq
#print axioms Comparison.massForm_nonneg
#print axioms Comparison.massForm_eq_zero_iff
#print axioms Comparison.massForm_unit_moved
#print axioms Comparison.trace_five
#print axioms Comparison.lastDirection_square
#print axioms Comparison.lastDirection_commutator
#print axioms Comparison.keep_move
#print axioms Comparison.trace_lastDirection_curv
#print axioms Comparison.mm_expand
#print axioms Comparison.lambda_from_ratio
#print axioms Comparison.ten_split
#print axioms Comparison.line_on_six
#print axioms Comparison.plane_on_six
#print axioms Comparison.one_of_each
#print axioms Comparison.commutant_perm
#print axioms Comparison.det_sylvester
#print axioms Comparison.stepOp
#print axioms Comparison.ihara_bass
#print axioms Comparison.adjacency_mul_charTable
#print axioms Comparison.D_plus
#print axioms Comparison.Aminus_sq
#print axioms Comparison.D_minus
#print axioms Comparison.D_plus_opposite
#print axioms Comparison.D_plus_quarter
#print axioms Comparison.D_minus_quarter
#print axioms Comparison.IsExcursion
#print axioms Comparison.excursions
#print axioms Comparison.excursion_scalar
#print axioms Comparison.excursionCount_values
#print axioms Comparison.excursionCount_rec
#print axioms Comparison.signedExcursionCount_even
#print axioms Comparison.signedExcursionCount_odd
#print axioms Comparison.signedExcursionCount_small
#print axioms Comparison.excursion_total
#print axioms Comparison.excursion_mean
#print axioms Comparison.excursion_second
#print axioms Comparison.excursion_variance
#print axioms Comparison.excursion_gf
#print axioms Comparison.signed_gf
#print axioms Comparison.Φ_one
#print axioms Comparison.Φ_I
#print axioms Comparison.a_value
#print axioms Comparison.derivative_det
#print axioms Comparison.logdet_derivative
#print axioms Comparison.logdet_eq_log
#print axioms Comparison.log_unique
#print axioms Comparison.generation_classes
#print axioms Comparison.hyper_values
#print axioms Comparison.no_anomaly
#print axioms Comparison.charge_eq
#print axioms Comparison.charge_values
#print axioms Comparison.lastDirection_line_neutral
#print axioms Comparison.plane_meets
#print axioms Comparison.EP_eq
#print axioms Comparison.EQ_eq
#print axioms Comparison.El_eq
#print axioms Comparison.visit_moments
#print axioms Comparison.vline_sum
#print axioms Comparison.vline_dot
#print axioms Comparison.vline_outer
#print axioms Comparison.coin_vline
#print axioms Comparison.critical_vertex
#print axioms Comparison.critical_expansion
#print axioms Comparison.stepMotion_unitary
#print axioms Comparison.stepMotion_add_adjoint
#print axioms Comparison.stepMotion_rest
#print axioms Comparison.eigen_phase
#print axioms Comparison.chart_square
#print axioms Comparison.dirac_square
#print axioms Comparison.tenLine_clifford
#print axioms Comparison.comparison_as_turn
#print axioms Comparison.swap_rel
#print axioms Comparison.irrep_cases
#print axioms Comparison.irrep_values
#print axioms Comparison.quarter_comparison
#print axioms Comparison.irreps
#print axioms Comparison.irrep_projectors
#print axioms Comparison.lastDirection_weights
#print axioms Comparison.lastDirection_share
#print axioms Comparison.traceless_gram
#print axioms Comparison.hypercharge_turn
#print axioms Comparison.circ_grad
#print axioms Comparison.T4_eq
#print axioms Comparison.Kinv_spec
#print axioms Comparison.S2_eq
#print axioms Comparison.kappa_eq
#print axioms Comparison.kappa_quarter
#print axioms Comparison.sadjZ_symm
#print axioms Comparison.sadjZ_sq
#print axioms Comparison.sadjZ_tri
#print axioms Comparison.links_complete
#print axioms Comparison.squares_complete
#print axioms Comparison.squares_distinct
#print axioms Comparison.B4Z_eq
#print axioms Comparison.cZ_div
#print axioms Comparison.wordSum_rec
#print axioms Comparison.wordSum_gf
#print axioms Comparison.returns_plus
#print axioms Comparison.excursion_from_returns
#print axioms Comparison.returns_minus
#print axioms Comparison.signed_excursion_from_returns
#print axioms Comparison.sign_relations
#print axioms Comparison.centralSign_split
#print axioms Comparison.law_split
#print axioms Comparison.resolvent_split
#print axioms Comparison.law_norm
#print axioms Comparison.D_minus_rel
#print axioms Comparison.kept_entry
#print axioms Comparison.central_entry
#print axioms Comparison.clock_dividedSet
#print axioms Comparison.clock_line_kept
#print axioms Comparison.clock_line_central
#print axioms Comparison.clock_line_moved
#print axioms Comparison.clock_plane_kept
#print axioms Comparison.clock_plane_central
#print axioms Comparison.clock_plane_moved
#print axioms Comparison.quarter_turn
#print axioms Comparison.clock_turns_singlet
#print axioms Comparison.gammaD_J_transpose
#print axioms Comparison.C_sq
#print axioms Comparison.amplitude_symm
#print axioms Comparison.hermForm_hermitian
#print axioms Comparison.coinAt_sq
#print axioms Comparison.dividedSetL
#print axioms Comparison.coinAt_echo
#print axioms Comparison.plane_departures
#print axioms Comparison.transition
#print axioms Comparison.disagreeSet_transition
#print axioms Comparison.transition_transition
#print axioms Comparison.transition_ne
#print axioms Comparison.transition_eq_transition_iff
#print axioms Comparison.line_moves_rel
#print axioms Comparison.Adjacent
#print axioms Comparison.card_neighbours
#print axioms Comparison.common_neighbours
#print axioms Comparison.card_edges
#print axioms Comparison.State
#print axioms Comparison.card_state
#print axioms Comparison.Continues
#print axioms Comparison.card_continuations
#print axioms Comparison.card_predecessors
#print axioms Comparison.undo_returns
#print axioms Comparison.γ_mul_γ_scalar_iff
#print axioms Comparison.words
#print axioms Comparison.Reduced
#print axioms Comparison.card_reduced
#print axioms Comparison.reduce_reduced
#print axioms Comparison.reduce_of_reduced
#print axioms Comparison.reduce_eq_of_cancel
#print axioms Comparison.cancels_to_reduce
#print axioms Comparison.unique_reduced
#print axioms Comparison.relOfWord
#print axioms Comparison.history_rel
#print axioms Comparison.disagreeSet_relOfWord
#print axioms Comparison.relOfWord_append
#print axioms Comparison.relOfWord_surjective
#print axioms Comparison.at_place_iff
#print axioms Comparison.visits_per_state
#print axioms Comparison.availableTransitions_visits
#print axioms Comparison.steps_along_lastDirection
#print axioms Comparison.steps_along_lastDirection_count
#print axioms Comparison.lastDirection_stationary
#print axioms Comparison.lastDirection_cov
#print axioms Comparison.lastDirection_spread
#print axioms Comparison.marks_centred
#print axioms Comparison.flux_count
#print axioms Comparison.y_pow
#print axioms Comparison.p_odd
#print axioms Comparison.p_even
#print axioms Comparison.p_one
#print axioms Comparison.p_two
#print axioms Comparison.JointCells.planeTurn_mul_self
#print axioms Comparison.JointCells.kept_F_iff
#print axioms Comparison.JointCells.own_central_F
#print axioms Comparison.JointCells.planeTurn_mul_gen
#print axioms Comparison.JointCells.Patterns.kept_iff_form
#print axioms Comparison.JointCells.pair_sign_blind
#print axioms Comparison.Law.ihara_bass_weighted
#print axioms Comparison.Law.bass_line_weights
#print axioms Comparison.Law.extPow_smul_one
#print axioms Comparison.Law.minor_carried_self
#print axioms Comparison.Law.minor_coin_self
#print axioms Comparison.Law.carried_whole
#print axioms Comparison.Law.prop192_moves
#print axioms Comparison.Law.prop192_count
#print axioms Comparison.Law.time_division_turns
#print axioms Comparison.Law.relTurn_moved
#print axioms Comparison.Law.count_moved
#print axioms Comparison.Law.count_transitions
#print axioms Comparison.Law.count_moved_availableTransitions
#print axioms Comparison.Law.count_transitions_availableTransitions
#print axioms Comparison.Law.prop195
#print axioms Comparison.Law.prop195_availableTransitions
#print axioms Comparison.Law.meeting_matrix_trace
#print axioms Comparison.Law.det_one_sub_kron_of_eigen
#print axioms Comparison.Law.eigen_sum
#print axioms Comparison.Law.eigen_sq
#print axioms Comparison.Law.eigen_cube
#print axioms Comparison.Law.second_order_composite
#print axioms Comparison.Law.prop189_det
#print axioms Comparison.Law.line_side_det
#print axioms Comparison.Law.meeting_side_det
#print axioms Comparison.Law.composite_ends
#print axioms Comparison.Law.K0_composition
#print axioms Comparison.Law.K0_law_on_direct_sum
#print axioms Comparison.Law.lineWalk_isPerron
#print axioms Comparison.Law.singlet_root_of_secular
#print axioms Comparison.Law.singlet_weighted_factor
#print axioms Comparison.Law.conj_spectrum
#print axioms Comparison.Law.uLevel_root
#print axioms Comparison.Law.level_factor
#print axioms Comparison.Law.level_perron
#print axioms Comparison.Law.level_value
#print axioms Comparison.Law.deltaLevel_eq
#print axioms Comparison.Law.delta_expansion
#print axioms Comparison.Law.one_line_rate
#print axioms Comparison.Law.one_line_angle
#print axioms Comparison.Law.availableTransitions_along_rate
#print axioms Comparison.Law.uniform_null
#print axioms Comparison.Law.lKr_u
#print axioms Comparison.Law.charX80_ones
#print axioms Comparison.Law.lKr_u_meeting
#print axioms Comparison.Law.level_source
#print axioms Comparison.Law.level_shift
#print axioms Comparison.Law.residue_sixteen
#print axioms Comparison.Law.residue_values
#print axioms Comparison.Law.critical_sixteen
#print axioms Comparison.Law.lastDirection_cross_cov
#print axioms Comparison.Law.cross_spread
#print axioms Comparison.Law.cross_values
#print axioms Comparison.Law.two_limits_first_order
#print axioms Comparison.Law.charX_mul_self
#print axioms Comparison.Law.charX_transition_charX
#print axioms Comparison.Law.prop130_B
#print axioms Comparison.Law.euler_completion
#print axioms Comparison.Law.meeting_factor
#print axioms Comparison.Law.pattern_factor
#print axioms Comparison.Law.pattern_factor_cancelled
#print axioms Comparison.Law.singlet_factor
#print axioms Comparison.Law.sum_agree_minus_one
#print axioms Comparison.Law.law_meetings
#print axioms Comparison.Law.law_twins
#print axioms Comparison.Law.law_meetings_closed
#print axioms Comparison.Law.piece_b_here
#print axioms Comparison.Law.piece_38
#print axioms Comparison.Law.piece_nu_hn
#print axioms Comparison.Law.piece_f
#print axioms Comparison.Law.piece_alphas_sq
#print axioms Comparison.Law.piece_e_line
#print axioms Comparison.Law.piece_Psi_plane
#print axioms Comparison.Law.piece_Psi_planeSinglet
#print axioms Comparison.Law.piece_kappa_base
#print axioms Comparison.Law.clockGap_hn
#print axioms Comparison.Law.clock_moments
#print axioms Comparison.Law.piece_h
#print axioms Comparison.Law.address_volume
#print axioms Comparison.Law.address_gramTerm
#print axioms Comparison.Law.piece_LOmega
#print axioms Comparison.Law.row_p
#print axioms Comparison.Law.petersen_spectrum
#print axioms Comparison.Law.heatContrasts_eq
#print axioms Comparison.Law.row_n
#print axioms Comparison.Law.row_Lam
#print axioms Comparison.Law.row_Delta
#print axioms Comparison.Law.blk_square
#print axioms Comparison.Law.row_pi0
#print axioms Comparison.Law.alpha_identity
#print axioms Comparison.Law.piece_Nh
#print axioms Comparison.Law.row_pipm
#print axioms Comparison.Law.row_rho
#print axioms Comparison.Law.row_mu
#print axioms Comparison.Law.row_tau
#print axioms Comparison.Law.row_p_quark
#print axioms Comparison.Law.row_q_quark
#print axioms Comparison.Law.row_quarks
#print axioms Comparison.Law.zS
#print axioms Comparison.Law.signS
#print axioms Comparison.Law.LZ
#print axioms Comparison.Law.zS_sq
#print axioms Comparison.Law.zS_eq_whole
#print axioms Comparison.Law.LS_carried
#print axioms Comparison.Law.LS_odd
#print axioms Comparison.Law.LS_even
#print axioms Comparison.Law.PhiS_eq
#print axioms Comparison.Law.PhiS_values
#print axioms Comparison.Law.powS_eq
#print axioms Comparison.Law.uS_sq
#print axioms Comparison.Law.wS_sq
#print axioms Comparison.Law.PsiS_eq
#print axioms Comparison.Law.PsiS_plane
#print axioms Comparison.Law.norm_wS
#print axioms Comparison.Law.eS_add_tS
#print axioms Comparison.Law.eS_four
#print axioms Comparison.Law.NS_turns
#print axioms Comparison.Law.twin_lines
#print axioms Comparison.Law.twin_sign
#print axioms Comparison.Law.rule_values
#print axioms Comparison.Law.sourceZ_places
#print axioms Comparison.Law.sourceZ_times
#print axioms Comparison.Law.sourceZ_ends
#print axioms Comparison.Law.logSource_first_order
#print axioms Comparison.Law.det_one_add_diagonal_mul
#print axioms Comparison.Law.address_coeff
#print axioms Comparison.Law.sourceZ_directSum
#print axioms Comparison.angle_of_zero
#print axioms Comparison.uniform_phase_zero
#print axioms Comparison.D_plus_disc
#print axioms Comparison.lawP_rate
#print axioms Comparison.transition_total
#print axioms Comparison.availableTransitions_angle_rate
#print axioms Comparison.one_transition_angle_rate
#print axioms Comparison.proton_availableTransitions_ratio
#print axioms Comparison.watched_kernel_right
#print axioms Comparison.watched_kernel_left
#print axioms Comparison.perron_unique
#print axioms Comparison.perron_exists
#print axioms Comparison.perron_expansion
#print axioms Comparison.perron_log
#print axioms Comparison.repReturn_hasSum
#print axioms Comparison.repReturn_real
#print axioms Comparison.repR_one
#print axioms Comparison.repR_two
#print axioms Comparison.repR_bound
#print axioms Comparison.repR_pos
#print axioms Comparison.N1_hasSum
#print axioms Comparison.N1_bounds
#print axioms Comparison.zero_shift_law
#print axioms Comparison.det_law_real
#print axioms Comparison.law_deriv_quarter
#print axioms Comparison.det_availableTransitionsOp
#print axioms Comparison.availableTransitionsOp_quarter
#print axioms Comparison.residue_general
#print axioms Comparison.residue_law
#print axioms Comparison.taylor_step
#print axioms Comparison.critical_operator
#print axioms Comparison.dispersion_series
#print axioms Comparison.lastDirectionWalk_weighted
#print axioms Comparison.lastDirection_velocity
#print axioms Comparison.lastDirection_variance_is_spread
#print axioms Comparison.watched_transition_sum
#print axioms Comparison.inventory_velocity
#print axioms Comparison.RuleAndLaw.own_turn_compressed
#print axioms Comparison.RuleAndLaw.pion_join
#print axioms Comparison.RuleAndLaw.green_identity
#print axioms Comparison.RuleAndLaw.green_symm
#print axioms Comparison.RuleAndLaw.laplacian_spectrum
#print axioms Comparison.RuleAndLaw.det_prime
#print axioms Comparison.RuleAndLaw.resistance_values
#print axioms Comparison.RuleAndLaw.rule_classes
#print axioms Comparison.RuleAndLaw.card_class_even
#print axioms Comparison.RuleAndLaw.card_class_five
#print axioms Comparison.RuleAndLaw.card_class_three
#print axioms Comparison.RuleAndLaw.card_class_one
#print axioms Comparison.RuleAndLaw.rule_values_classes
#print axioms Comparison.RuleAndLaw.card_psi_compact
#print axioms Comparison.RuleAndLaw.card_e_compact
#print axioms Comparison.RuleAndLaw.correction_offdiag
#print axioms Comparison.RuleAndLaw.kC_eq
#print axioms Comparison.RuleAndLaw.kC_lines
#print axioms Comparison.RuleAndLaw.uS_norm
#print axioms Comparison.RuleAndLaw.kC_response
#print axioms Comparison.RuleAndLaw.LOmega_forms
#print axioms Comparison.RuleAndLaw.trL2_lines
#print axioms Comparison.RuleAndLaw.sixes_agree_iff
#print axioms Comparison.RuleAndLaw.one_closed_four
#print axioms Comparison.RuleAndLaw.four_history_sign
#print axioms Comparison.RuleAndLaw.trace_four
#print axioms Comparison.RuleAndLaw.least_count
#print axioms Comparison.RuleAndLaw.every_transition_reading
#print axioms Comparison.RuleAndLaw.delta_three
#print axioms Comparison.RuleAndLaw.gravity_three_excursions
#print axioms Comparison.RuleAndLaw.clockMQ_pos
#print axioms Comparison.RuleAndLaw.tiltLaw_mul
#print axioms Comparison.RuleAndLaw.bhattacharyya
#print axioms Comparison.RuleAndLaw.clock_overlap
#print axioms Comparison.RuleAndLaw.exchange_block
#print axioms Comparison.RuleAndLaw.exchange_series
#print axioms Comparison.RuleAndLaw.pion_ends
#print axioms Comparison.RuleAndLaw.plane_phase
#print axioms Comparison.RuleAndLaw.plane_clock_half_turn
#print axioms Comparison.RuleAndLaw.charge_square
#print axioms Comparison.RuleAndLaw.row_pipm_arg
#print axioms Comparison.RuleAndLaw.uRoot_root
#print axioms Comparison.RuleAndLaw.uRoot_at_d
#print axioms Comparison.RuleAndLaw.transfer_rate
#print axioms Comparison.RuleAndLaw.transfer_five
#print axioms Comparison.RuleAndLaw.rho_rule
#print axioms Comparison.RuleAndLaw.clockMeanGap_eq
#print axioms Comparison.RuleAndLaw.massOpRule_eq
#print axioms Comparison.RuleAndLaw.rowPRule_eq
#print axioms Comparison.RuleAndLaw.rowLam_first_order
#print axioms Comparison.RuleAndLaw.proton_radius_factor
#print axioms Comparison.RuleAndLaw.quad_lower
#print axioms Comparison.RuleAndLaw.law_no_zero_below_quarter
#print axioms Comparison.RuleAndLaw.law_no_zero_in_disc
#print axioms Comparison.RuleAndLaw.four_uS
#print axioms Comparison.RuleAndLaw.rule_reads_signed_return
#print axioms Comparison.RuleAndLaw.rule_reads_resolvent
#print axioms Comparison.WholePicture.cubes_complete
#print axioms Comparison.WholePicture.card_cubeSet
#print axioms Comparison.WholePicture.card_sqSet
#print axioms Comparison.WholePicture.euler_number
#print axioms Comparison.WholePicture.bd_bd
#print axioms Comparison.WholePicture.homology_mod_two
#print axioms Comparison.WholePicture.rank_cReal
#print axioms Comparison.WholePicture.cReal_gram_charpoly
#print axioms Comparison.WholePicture.lamMax_gauge
#print axioms Comparison.WholePicture.lamMax_cyc
#print axioms Comparison.WholePicture.long_range_zero
#print axioms Comparison.WholePicture.connStep_herm
#print axioms Comparison.WholePicture.connStep_sq
#print axioms Comparison.WholePicture.law_quad_unitary
#print axioms Comparison.WholePicture.law_weight_pos_unitary
#print axioms Comparison.WholePicture.law_pos_unitary
#print axioms Comparison.WholePicture.law_no_zero_unitary
#print axioms Comparison.WholePicture.wedge_R_E
#print axioms Comparison.WholePicture.wedge_E_E
#print axioms Comparison.WholePicture.curvature_identity
#print axioms Comparison.WholePicture.lambda_three
#print axioms Comparison.WholePicture.Eop_eq_pairing
#print axioms Comparison.WholePicture.compOp_one
#print axioms Comparison.WholePicture.compOp_line
#print axioms Comparison.WholePicture.compOp_plane
#print axioms Comparison.WholePicture.half_general
#print axioms Comparison.WholePicture.half_general_unitary
#print axioms Comparison.WholePicture.description_sign
#print axioms Comparison.WholePicture.description_carries_product
#print axioms Comparison.WholePicture.hyper_fifth
#print axioms Comparison.WholePicture.three_pairings
#print axioms Comparison.WholePicture.gen12_block
#print axioms Comparison.WholePicture.gen12_orthonormal
#print axioms Comparison.WholePicture.lastDirectionGram_eq
#print axioms Comparison.WholePicture.lastDirectionGram_charpoly
#print axioms Comparison.WholePicture.source_ratios
#print axioms Comparison.WholePicture.greenM_eq
#print axioms Comparison.WholePicture.green_penrose
#print axioms Comparison.WholePicture.green_pinv
#print axioms Comparison.WholePicture.mixed_moment_central
#print axioms Comparison.WholePicture.clock_uniform
#print axioms Comparison.WholePicture.crossing_pair_quarter
#print axioms Comparison.WholePicture.mixed_moment_central_subspaces
#print axioms Comparison.WholePicture.arc_cofactor_const
#print axioms Comparison.WholePicture.trace_adj_B
#print axioms Comparison.WholePicture.det_mark
#print axioms Comparison.WholePicture.one_arc
#print axioms Comparison.WholePicture.one_arc_phase
#print axioms Comparison.WholePicture.stepR_gram
#print axioms Comparison.WholePicture.stepR_gram_charpoly
#print axioms Comparison.WholePicture.absB_charpoly
#print axioms Comparison.WholePicture.absB_polar
#print axioms Comparison.WholePicture.charge_current
#print axioms Comparison.WholePicture.twentyfour_eleven
#print axioms Comparison.WholePicture.hessLaw_eq
#print axioms Comparison.WholePicture.kappa_quarters
#print axioms Comparison.WholePicture.law_grade_factors
#print axioms Comparison.WholePicture.law_over_meetings
#print axioms Comparison.WholePicture.grade_factors_plane_quarter
#print axioms Comparison.WholePicture.quarter_factors
#print axioms Comparison.WholePicture.step_weights_are_grade_factors
#print axioms Comparison.WholePicture.one_crossing_pair
#print axioms Comparison.WholePicture.rule_constants
#print axioms Comparison.WholePicture.alphaS_sq
#print axioms Comparison.WholePicture.gravity_grade_form
#print axioms Comparison.WholePicture.law_transformation
#print axioms Comparison.WholePicture.grade_factor_transformation
#print axioms Comparison.WholePicture.trace_five_volume
