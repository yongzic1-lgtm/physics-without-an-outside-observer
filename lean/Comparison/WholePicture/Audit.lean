import Comparison.WholePicture.Geometry
import Comparison.WholePicture.TheLaw
import Comparison.WholePicture.Spectra
import Comparison.WholePicture.Polar
import Comparison.WholePicture.Cells
import Comparison.WholePicture.OneArc
import Comparison.WholePicture.Moment
import Comparison.WholePicture.Circulation
import Comparison.WholePicture.Curvature
import Comparison.WholePicture.SecondVariation
import Comparison.WholePicture.Green
import Comparison.WholePicture.TraceFive
import Comparison.WholePicture.Connection
import Comparison.WholePicture.MomentSubspaces
import Comparison.Elements.OneThing
import Comparison.Elements.TwoThings
import Comparison.Elements.Divisions
import Comparison.Elements.Half
import Comparison.Colour.GramTerm
import Comparison.Colour.Visits
import Comparison.Colour.Proton
import Comparison.Colour.Arcs
import Comparison.Existence.Matter
import Comparison.Existence.Pair
import Comparison.Existence.IharaBass
import Comparison.Existence.PlaquetteData
import Comparison.Existence.Plaquette
import Comparison.Existence.Gauge
import Comparison.Existence.Walk
import Comparison.Existence.Sign
import Comparison.Existence.Return
import Comparison.Existence.Excursion
import Comparison.Existence.Moments
import Comparison.Existence.AvailableTransitions
import Comparison.Existence.Motion
import Comparison.Existence.LastDirectionSplit
import Comparison.Existence.Zero
import Comparison.Law.Meetings
import Comparison.Law.Cover
import Comparison.Law.Composite
import Comparison.Law.LongZero
import Comparison.Law.Rule
import Comparison.Law.Rows
import Comparison.Mass.Simple
import Comparison.Mass.Taylor
import Comparison.RuleAndLaw.Positivity
import Comparison.RuleAndLaw.CriticalGerm
import Comparison.RuleAndLaw.RuleReadsLaw
import Comparison.RuleAndLaw.FactorsA
import Comparison.RuleAndLaw.FactorsB
import Comparison.ArticleStatements.MixedMoment
import Comparison.ArticleStatements.Geometry
import Comparison.ArticleStatements.Radar
import Comparison.ArticleStatements.SectorSum
import Comparison.Existence.LogDet

/-!
# Axiom audit of the whole picture

Build with `lake build Comparison.WholePicture.Audit`. Every new theorem must read
`depends on axioms: [propext, Classical.choice, Quot.sound]` or a part of it; `sorryAx` would
mean an unfinished proof. The second part prints the standing theorems the map cites.
-/

-- new: Comparison/WholePicture/Geometry.lean (39 theorems)
#print axioms Comparison.WholePicture.Eop_eq_pairing
#print axioms Comparison.WholePicture.relOf_sum
#print axioms Comparison.WholePicture.L_on_operator
#print axioms Comparison.WholePicture.compOp_relOp
#print axioms Comparison.WholePicture.compOp_one
#print axioms Comparison.WholePicture.compOp_line
#print axioms Comparison.WholePicture.compOp_plane
#print axioms Comparison.WholePicture.half_general
#print axioms Comparison.WholePicture.half_general_unitary
#print axioms Comparison.WholePicture.card_inter_eq_sum
#print axioms Comparison.WholePicture.card_inter_add
#print axioms Comparison.WholePicture.description_sign
#print axioms Comparison.WholePicture.description_carries_product
#print axioms Comparison.WholePicture.hyper6_fifth
#print axioms Comparison.WholePicture.hyper_fifth
#print axioms Comparison.WholePicture.three_pairings
#print axioms Comparison.WholePicture.genRe_antisymm
#print axioms Comparison.WholePicture.genIm_symm
#print axioms Comparison.WholePicture.genRe_trace
#print axioms Comparison.WholePicture.genIm_trace
#print axioms Comparison.WholePicture.gen_block
#print axioms Comparison.WholePicture.gen_gram_int
#print axioms Comparison.WholePicture.genNorm_pos
#print axioms Comparison.WholePicture.gen12_apply
#print axioms Comparison.WholePicture.gen12_re
#print axioms Comparison.WholePicture.gen12_im
#print axioms Comparison.WholePicture.gen12_antiHermitian
#print axioms Comparison.WholePicture.gen12_trace
#print axioms Comparison.WholePicture.gen12_block
#print axioms Comparison.WholePicture.sqrt_inv_mul_self
#print axioms Comparison.WholePicture.gen12_orthonormal
#print axioms Comparison.WholePicture.gen12_mulVec_lastDirectionE
#print axioms Comparison.WholePicture.lastDirectionGram_eq
#print axioms Comparison.WholePicture.genW_eq
#print axioms Comparison.WholePicture.lastDirection_column_sum
#print axioms Comparison.WholePicture.lastDirectionImg_mul_transpose
#print axioms Comparison.WholePicture.prod_lastDirectionDiag
#print axioms Comparison.WholePicture.lastDirectionGram_charpoly
#print axioms Comparison.WholePicture.source_ratios

-- new: Comparison/WholePicture/TheLaw.lean (14 theorems)
#print axioms Comparison.WholePicture.law_grade_factors
#print axioms Comparison.WholePicture.disagree_card_cases
#print axioms Comparison.WholePicture.meeting_factor_zpow
#print axioms Comparison.WholePicture.law_over_meetings
#print axioms Comparison.WholePicture.kR_plane_quarter
#print axioms Comparison.WholePicture.grade_factors_plane_quarter
#print axioms Comparison.WholePicture.quarter_factors
#print axioms Comparison.WholePicture.step_weights_are_grade_factors
#print axioms Comparison.WholePicture.one_crossing_pair
#print axioms Comparison.WholePicture.rule_constants
#print axioms Comparison.WholePicture.alphaS_sq
#print axioms Comparison.WholePicture.gravity_grade_form
#print axioms Comparison.WholePicture.law_transformation
#print axioms Comparison.WholePicture.grade_factor_transformation

-- new: Comparison/WholePicture/Spectra.lean (7 theorems)
#print axioms Comparison.WholePicture.eigvec_ne_zero
#print axioms Comparison.WholePicture.eig_root_quadratic
#print axioms Comparison.WholePicture.eig_root_cubic
#print axioms Comparison.WholePicture.charpoly_of_values
#print axioms Comparison.WholePicture.trace_of_values
#print axioms Comparison.WholePicture.card_of_values
#print axioms Comparison.WholePicture.rank_of_values

-- new: Comparison/WholePicture/Polar.lean (20 theorems)
#print axioms Comparison.WholePicture.transition_inj
#print axioms Comparison.WholePicture.sum_transition_transition
#print axioms Comparison.WholePicture.two_avoid_count
#print axioms Comparison.WholePicture.stepR_gram
#print axioms Comparison.WholePicture.stepR_gram_proj
#print axioms Comparison.WholePicture.lastDirectionProj_symm
#print axioms Comparison.WholePicture.lastDirectionProj_idem
#print axioms Comparison.WholePicture.trace_lastDirectionProj
#print axioms Comparison.WholePicture.stepR_gram_symm
#print axioms Comparison.WholePicture.stepR_gram_quadratic
#print axioms Comparison.WholePicture.trace_stepR_gram
#print axioms Comparison.WholePicture.stepR_gram_charpoly
#print axioms Comparison.WholePicture.absB_sq
#print axioms Comparison.WholePicture.absB_symm
#print axioms Comparison.WholePicture.absB_charpoly
#print axioms Comparison.WholePicture.absB_polar
#print axioms Comparison.WholePicture.charge3_additive
#print axioms Comparison.WholePicture.charge_additive
#print axioms Comparison.WholePicture.charge_current
#print axioms Comparison.WholePicture.twentyfour_eleven

-- new: Comparison/WholePicture/Cells.lean (31 theorems)
#print axioms Comparison.WholePicture.rank_eq_of_cert
#print axioms Comparison.WholePicture.homology_finrank_one
#print axioms Comparison.WholePicture.linkLine_spec
#print axioms Comparison.WholePicture.cubes_complete
#print axioms Comparison.WholePicture.cubes_distinct
#print axioms Comparison.WholePicture.cubes_ordered
#print axioms Comparison.WholePicture.card_cubeSet
#print axioms Comparison.WholePicture.card_sqSet
#print axioms Comparison.WholePicture.euler_number
#print axioms Comparison.WholePicture.bd1_bd2
#print axioms Comparison.WholePicture.bd2_bd3
#print axioms Comparison.WholePicture.bd3_bd4
#print axioms Comparison.WholePicture.bd_bd
#print axioms Comparison.WholePicture.bd_columns
#print axioms Comparison.WholePicture.bd1_cert
#print axioms Comparison.WholePicture.bd2_cert
#print axioms Comparison.WholePicture.bd3_cert
#print axioms Comparison.WholePicture.bd4_cert
#print axioms Comparison.WholePicture.rank_bd1
#print axioms Comparison.WholePicture.rank_bd2
#print axioms Comparison.WholePicture.rank_bd3
#print axioms Comparison.WholePicture.rank_bd4
#print axioms Comparison.WholePicture.homology_mod_two
#print axioms Comparison.WholePicture.cMat_cert
#print axioms Comparison.WholePicture.rank_cReal
#print axioms Comparison.WholePicture.gTab_eq
#print axioms Comparison.WholePicture.gMat_cubic
#print axioms Comparison.WholePicture.gMat_trace
#print axioms Comparison.WholePicture.cReal_gram
#print axioms Comparison.WholePicture.cReal_gram_symm
#print axioms Comparison.WholePicture.cReal_gram_charpoly

-- new: Comparison/WholePicture/OneArc.lean (31 theorems)
#print axioms Comparison.WholePicture.Bc_apply
#print axioms Comparison.WholePicture.Bc_eq
#print axioms Comparison.WholePicture.disagreeSet_inj
#print axioms Comparison.WholePicture.disagreeSet_injective
#print axioms Comparison.WholePicture.even_sets_are_relations
#print axioms Comparison.WholePicture.disagreeSet_card_even
#print axioms Comparison.WholePicture.relPerm_exists
#print axioms Comparison.WholePicture.disagreeSet_relPerm
#print axioms Comparison.WholePicture.relPerm_injective
#print axioms Comparison.WholePicture.relPerm_transition
#print axioms Comparison.WholePicture.relPerm_zero
#print axioms Comparison.WholePicture.transition_comm
#print axioms Comparison.WholePicture.transition_inj'
#print axioms Comparison.WholePicture.continues_mv
#print axioms Comparison.WholePicture.continues_pm
#print axioms Comparison.WholePicture.mvState_involutive
#print axioms Comparison.WholePicture.pmState_injective
#print axioms Comparison.WholePicture.adj_invariant
#print axioms Comparison.WholePicture.relation_reach
#print axioms Comparison.WholePicture.perm_pair
#print axioms Comparison.WholePicture.arc_transition
#print axioms Comparison.WholePicture.arc_perm
#print axioms Comparison.WholePicture.arc_cofactor_const
#print axioms Comparison.WholePicture.adj_continues
#print axioms Comparison.WholePicture.trace_adj_B
#print axioms Comparison.WholePicture.lawPoly_eval
#print axioms Comparison.WholePicture.eval_map_one_sub
#print axioms Comparison.WholePicture.lawPoly_deriv
#print axioms Comparison.WholePicture.det_mark
#print axioms Comparison.WholePicture.one_arc
#print axioms Comparison.WholePicture.one_arc_phase

-- new: Comparison/WholePicture/Moment.lean (16 theorems)
#print axioms Comparison.WholePicture.plane_clock_sum
#print axioms Comparison.WholePicture.line_clock_sum
#print axioms Comparison.WholePicture.card_planesOf
#print axioms Comparison.WholePicture.card_lineRelsOf
#print axioms Comparison.WholePicture.fifteen_eq
#print axioms Comparison.WholePicture.planes_lines_disjoint
#print axioms Comparison.WholePicture.sum_fifteen
#print axioms Comparison.WholePicture.sum_planes_cw
#print axioms Comparison.WholePicture.sum_lines_cw
#print axioms Comparison.WholePicture.Zc_eq
#print axioms Comparison.WholePicture.meanGrade_eq
#print axioms Comparison.WholePicture.cast_plane_sum
#print axioms Comparison.WholePicture.cast_line_sum
#print axioms Comparison.WholePicture.mixed_moment_central
#print axioms Comparison.WholePicture.clock_uniform
#print axioms Comparison.WholePicture.crossing_pair_quarter

-- new: Comparison/WholePicture/Circulation.lean (65 theorems)
#print axioms Comparison.WholePicture.adjZ_links
#print axioms Comparison.WholePicture.incZ_gram
#print axioms Comparison.WholePicture.incZ_col
#print axioms Comparison.WholePicture.ends_count
#print axioms Comparison.WholePicture.green_identity_local
#print axioms Comparison.WholePicture.adj_srg
#print axioms Comparison.WholePicture.adj_symm
#print axioms Comparison.WholePicture.gradR_apply
#print axioms Comparison.WholePicture.div_grad
#print axioms Comparison.WholePicture.sum_divR
#print axioms Comparison.WholePicture.laplace_green
#print axioms Comparison.WholePicture.divR_thetaCyc
#print axioms Comparison.WholePicture.theta_sub_cyc
#print axioms Comparison.WholePicture.grad_orth
#print axioms Comparison.WholePicture.sqL_cyc_le
#print axioms Comparison.WholePicture.cyc_unique
#print axioms Comparison.WholePicture.nsq_nonneg
#print axioms Comparison.WholePicture.nsq_pos
#print axioms Comparison.WholePicture.sum_ends
#print axioms Comparison.WholePicture.re_term_le
#print axioms Comparison.WholePicture.magForm_le
#print axioms Comparison.WholePicture.rayleigh_le_five
#print axioms Comparison.WholePicture.rayleigh_bdd
#print axioms Comparison.WholePicture.le_lamMax
#print axioms Comparison.WholePicture.lamMax_le
#print axioms Comparison.WholePicture.lamMax_le_five
#print axioms Comparison.WholePicture.nsq_gauge
#print axioms Comparison.WholePicture.gauge_gauge
#print axioms Comparison.WholePicture.star_exp_real
#print axioms Comparison.WholePicture.magForm_gauge
#print axioms Comparison.WholePicture.lamMax_gauge
#print axioms Comparison.WholePicture.lamMax_cyc
#print axioms Comparison.WholePicture.lamMax_ge
#print axioms Comparison.WholePicture.adjC_conjTranspose
#print axioms Comparison.WholePicture.adjC_sq
#print axioms Comparison.WholePicture.one_sub_adjC_sq
#print axioms Comparison.WholePicture.onesC_mulVec
#print axioms Comparison.WholePicture.re_star_self
#print axioms Comparison.WholePicture.clebsch_le
#print axioms Comparison.WholePicture.link_pair_sum
#print axioms Comparison.WholePicture.magForm_zero_eq
#print axioms Comparison.WholePicture.split_term
#print axioms Comparison.WholePicture.magForm_split
#print axioms Comparison.WholePicture.nsq_split
#print axioms Comparison.WholePicture.sum_ends_c
#print axioms Comparison.WholePicture.sum_link_div
#print axioms Comparison.WholePicture.cross_term_le
#print axioms Comparison.WholePicture.magForm_rest_le
#print axioms Comparison.WholePicture.abs_le_sqrt_sqL
#print axioms Comparison.WholePicture.norm_le_sqrt_nsq
#print axioms Comparison.WholePicture.two_by_two
#print axioms Comparison.WholePicture.magForm_upper
#print axioms Comparison.WholePicture.lamMax_upper
#print axioms Comparison.WholePicture.ucrit_root
#print axioms Comparison.WholePicture.log_root_bound
#print axioms Comparison.WholePicture.long_range_zero
#print axioms Comparison.WholePicture.magAdj_isHermitian
#print axioms Comparison.WholePicture.link_pair_sum_phase
#print axioms Comparison.WholePicture.magForm_eq
#print axioms Comparison.WholePicture.star_self_re
#print axioms Comparison.WholePicture.eigen_le_lamMax
#print axioms Comparison.WholePicture.rayleigh_euclid
#print axioms Comparison.WholePicture.toEuclidNZ_surjective
#print axioms Comparison.WholePicture.lamMax_eq_rayleigh
#print axioms Comparison.WholePicture.lamMax_hasEigenvalue

-- new: Comparison/WholePicture/Curvature.lean (20 theorems)
#print axioms Comparison.WholePicture.eps_frame_Z
#print axioms Comparison.WholePicture.eps_eps_Z
#print axioms Comparison.WholePicture.frame_eps_Z
#print axioms Comparison.WholePicture.eps_eps_left_Z
#print axioms Comparison.WholePicture.frame_diag_Z
#print axioms Comparison.WholePicture.frameZ_antisymm
#print axioms Comparison.WholePicture.sum_pair
#print axioms Comparison.WholePicture.eps_frameP
#print axioms Comparison.WholePicture.eps_epsP
#print axioms Comparison.WholePicture.frame_epsP
#print axioms Comparison.WholePicture.eps_eps_leftP
#print axioms Comparison.WholePicture.contract_frameP
#print axioms Comparison.WholePicture.form_antisymm_diag
#print axioms Comparison.WholePicture.wedge_R_E
#print axioms Comparison.WholePicture.wedge_E_R
#print axioms Comparison.WholePicture.onPairs_frame4
#print axioms Comparison.WholePicture.wedge_E_E
#print axioms Comparison.WholePicture.wedge_expand
#print axioms Comparison.WholePicture.curvature_identity
#print axioms Comparison.WholePicture.lambda_three

-- new: Comparison/WholePicture/SecondVariation.lean (19 theorems)
#print axioms Comparison.WholePicture.linkSign_sq
#print axioms Comparison.WholePicture.sadjZ_VU
#print axioms Comparison.WholePicture.AC_sq
#print axioms Comparison.WholePicture.resolventW_spec
#print axioms Comparison.WholePicture.trace_single_single
#print axioms Comparison.WholePicture.trace_M_single_single
#print axioms Comparison.WholePicture.trace_M_single_M_single
#print axioms Comparison.WholePicture.trace_M_single
#print axioms Comparison.WholePicture.linkX_pair
#print axioms Comparison.WholePicture.linkX_triangle
#print axioms Comparison.WholePicture.trace_linkX_linkX
#print axioms Comparison.WholePicture.trace_AC_linkX_linkX
#print axioms Comparison.WholePicture.trace_linkX_AC_linkX
#print axioms Comparison.WholePicture.trace_AC_linkX_AC_linkX
#print axioms Comparison.WholePicture.trace_single_ne
#print axioms Comparison.WholePicture.trace_d2A
#print axioms Comparison.WholePicture.trace_AC_d2A
#print axioms Comparison.WholePicture.hessLaw_eq
#print axioms Comparison.WholePicture.kappa_quarters

-- new: Comparison/WholePicture/Green.lean (12 theorems)
#print axioms Comparison.WholePicture.penrose_unique
#print axioms Comparison.WholePicture.green_identity_right
#print axioms Comparison.WholePicture.lap_col_sum
#print axioms Comparison.WholePicture.green_col_sum
#print axioms Comparison.WholePicture.greenM_eq
#print axioms Comparison.WholePicture.lap_mul_green
#print axioms Comparison.WholePicture.green_mul_lap
#print axioms Comparison.WholePicture.offConst_mul_lap
#print axioms Comparison.WholePicture.offConst_mul_green
#print axioms Comparison.WholePicture.offConst_transpose
#print axioms Comparison.WholePicture.green_penrose
#print axioms Comparison.WholePicture.green_pinv

-- new: Comparison/WholePicture/TraceFive.lean (1 theorems)
#print axioms Comparison.WholePicture.trace_five_volume

-- new: Comparison/WholePicture/Connection.lean (10 theorems)
#print axioms Comparison.WholePicture.turnMat_back
#print axioms Comparison.WholePicture.turnMat_mul_back
#print axioms Comparison.WholePicture.transition_eq_comm
#print axioms Comparison.WholePicture.connStep_herm
#print axioms Comparison.WholePicture.connStep_sq
#print axioms Comparison.WholePicture.connStep_trivial
#print axioms Comparison.WholePicture.law_quad_unitary
#print axioms Comparison.WholePicture.law_weight_pos_unitary
#print axioms Comparison.WholePicture.law_pos_unitary
#print axioms Comparison.WholePicture.law_no_zero_unitary

-- new: Comparison/WholePicture/MomentSubspaces.lean (13 theorems)
#print axioms Comparison.WholePicture.card_disagreeSet
#print axioms Comparison.WholePicture.sum_relEntry
#print axioms Comparison.WholePicture.sum_grade_relEntry
#print axioms Comparison.WholePicture.relEntry_singlet_clock
#print axioms Comparison.WholePicture.grade_split
#print axioms Comparison.WholePicture.plane_line_sums
#print axioms Comparison.WholePicture.central_sums
#print axioms Comparison.WholePicture.wMean_eq
#print axioms Comparison.WholePicture.wClock_eq
#print axioms Comparison.WholePicture.central_moment_sum
#print axioms Comparison.WholePicture.wMoment_eq
#print axioms Comparison.WholePicture.mixed_moment_central_subspaces
#print axioms Comparison.WholePicture.wMoment_uniform

-- standing theorems cited by the whole picture
-- S1 (Elements/OneThing, TwoThings; Colour/Gram-determinant term; ArticleStatements/Geometry)
#print axioms Comparison.γ_conjTranspose
#print axioms Comparison.clifford
#print axioms Comparison.γ_prod
#print axioms Comparison.J_transpose
#print axioms Comparison.L_eq_swap_singlet
#print axioms Comparison.swap_mul_swap
#print axioms Comparison.Eop_mul_Eop
#print axioms Comparison.ArticleStatements.swap_mul_Eop
#print axioms Comparison.ArticleStatements.Eop_mul_swap
#print axioms Comparison.finrank_eigenspace_L_six
#print axioms Comparison.finrank_eigenspace_L_two
#print axioms Comparison.finrank_eigenspace_L_neg_two
#print axioms Comparison.eigenspace_L_other
#print axioms Comparison.L_rel
#print axioms Comparison.rel_inner

-- S2 (Elements/Divisions, Half)
#print axioms Comparison.four_kinds
#print axioms Comparison.card_kept
#print axioms Comparison.card_moved
#print axioms Comparison.half_mul_self
#print axioms Comparison.half_conjTranspose_mul
#print axioms Comparison.half_on_sets

-- S3 (Existence/Matter)
#print axioms Comparison.hyper_values
#print axioms Comparison.charge_eq
#print axioms Comparison.no_anomaly
#print axioms Comparison.generation_classes
#print axioms Comparison.charge_values

-- S4 (Existence/Pair)
#print axioms Comparison.lastDirection_weights
#print axioms Comparison.traceless_gram

-- S5 (Existence/IharaBass; Law/Meetings)
#print axioms Comparison.D_plus
#print axioms Comparison.Law.law_meetings
#print axioms Comparison.Law.pattern_factor_cancelled
#print axioms Comparison.Law.singlet_factor
#print axioms Comparison.Law.law_meetings_closed

-- S6 (Existence/PlaquetteData, Plaquette, Gauge, Walk)
#print axioms Comparison.links_complete
#print axioms Comparison.links_distinct
#print axioms Comparison.squares_complete
#print axioms Comparison.squares_distinct
#print axioms Comparison.cZ_div
#print axioms Comparison.circ_grad
#print axioms Comparison.card_squares
#print axioms Comparison.card_edges

-- S7 (PlaquetteData; IharaBass; Sign; Return; Law/Cover; RuleAndLaw/RuleReadsLaw)
#print axioms Comparison.sadjZ_symm
#print axioms Comparison.sadjZ_sq
#print axioms Comparison.Aminus_sq
#print axioms Comparison.D_minus
#print axioms Comparison.D_minus_rel
#print axioms Comparison.returns_minus
#print axioms Comparison.signed_excursion_from_returns
#print axioms Comparison.Law.signed_law_cover
#print axioms Comparison.RuleAndLaw.rule_reads_resolvent

-- S8 (RuleAndLaw/Positivity; IharaBass)
#print axioms Comparison.RuleAndLaw.quad_lower
#print axioms Comparison.RuleAndLaw.law_no_zero_below_quarter
#print axioms Comparison.RuleAndLaw.law_no_zero_in_disc
#print axioms Comparison.ihara_bass
#print axioms Comparison.ArticleStatements.lawWeight_pos
#print axioms Comparison.ArticleStatements.law_pos

-- S9 (Existence/Excursion, Return)
#print axioms Comparison.excursion_gf
#print axioms Comparison.signed_gf
#print axioms Comparison.excursion_total
#print axioms Comparison.excursion_mean
#print axioms Comparison.excursion_variance
#print axioms Comparison.Φ_one
#print axioms Comparison.Φ_I
#print axioms Comparison.excursion_from_returns

-- S10 (Existence/Moments, Available transitions; Colour/Visits)
#print axioms Comparison.EP_eq
#print axioms Comparison.EQ_eq
#print axioms Comparison.visit_moments
#print axioms Comparison.GP_eq
#print axioms Comparison.GP_denominator
#print axioms Comparison.xc_gt_one
#print axioms Comparison.card_excursionStates
#print axioms Comparison.availableTransitions_along
#print axioms Comparison.availableTransitions_total
#print axioms Comparison.availableTransitions_up

-- S11 (RuleAndLaw/CriticalGerm; ArticleStatements/Radar; Law/Composite; Colour/Gram-determinant term)
#print axioms Comparison.RuleAndLaw.green_identity
#print axioms Comparison.RuleAndLaw.green_symm
#print axioms Comparison.RuleAndLaw.resistance_values
#print axioms Comparison.RuleAndLaw.resistance_real
#print axioms Comparison.ArticleStatements.Radar.tanh_quarter
#print axioms Comparison.Law.prop195
#print axioms Comparison.trace_L_sq

-- S12 (ArticleStatements/MixedMoment)
#print axioms Comparison.ArticleStatements.mixed_moment_subspaces
#print axioms Comparison.ArticleStatements.kappa_eq
#print axioms Comparison.ArticleStatements.tau_clock_clock
#print axioms Comparison.ArticleStatements.tau_grade_clock_clock

-- S13 (Mass/Angle; Law/LongZero; Mass/Simple)
#print axioms Comparison.Law.one_line_rate
#print axioms Comparison.law_deriv_quarter
#print axioms Comparison.residue_law
#print axioms Comparison.derivative_det_one_sub

-- S14 (RuleAndLaw/FactorsA; Law/Rule; Excursion; ArticleStatements/MixedMoment; Pair)
#print axioms Comparison.RuleAndLaw.rule_classes
#print axioms Comparison.RuleAndLaw.rule_values_classes
#print axioms Comparison.Law.norm_wS
#print axioms Comparison.Law.PhiS_values
#print axioms Comparison.a_value
#print axioms Comparison.ArticleStatements.kappa_one_against_four
#print axioms Comparison.ArticleStatements.kappa_plane_against_colour
#print axioms Comparison.ArticleStatements.interior_factor

-- S15 (Existence/Motion, Plaquette, HandSplit; Mass/Taylor)
#print axioms Comparison.vline_sum
#print axioms Comparison.vline_outer
#print axioms Comparison.critical_expansion
#print axioms Comparison.critical_operator
#print axioms Comparison.taylor_step
#print axioms Comparison.dispersion_series
#print axioms Comparison.stepMotion_add_adjoint
#print axioms Comparison.stepMotion_unitary
#print axioms Comparison.eigen_phase
#print axioms Comparison.chart_square
#print axioms Comparison.dirac_square
#print axioms Comparison.S2_eq
#print axioms Comparison.kappa_eq
#print axioms Comparison.kappa_quarter
#print axioms Comparison.trace_five
#print axioms Comparison.lastDirection_commutator
#print axioms Comparison.mm_expand
#print axioms Comparison.lambda_from_ratio

-- S16 (Colour/Proton; Law/Rows; RuleAndLaw/FactorsB)
#print axioms Comparison.W_eq
#print axioms Comparison.alphaG_eq
#print axioms Comparison.protonPole_bounds
#print axioms Comparison.Law.row_p
#print axioms Comparison.RuleAndLaw.gravity_three_excursions

-- S17 (Existence/Zero; Colour/Arcs)
#print axioms Comparison.flux_count
#print axioms Comparison.edges_count

