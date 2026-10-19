import Comparison.Elements

/-!
# Axiom audit of the Elements of Comparison in Lean

Build with `lake build Comparison.Elements.Audit`. Every line must read
`depends on axioms: [propext, Classical.choice, Quot.sound]`; `sorryAx` would mean a `sorry`.
-/

-- Book I: one system
#print axioms Comparison.Θ_Θ
#print axioms Comparison.Θ_orth
#print axioms Comparison.Θ_norm
#print axioms Comparison.J_transpose
#print axioms Comparison.J_mul_conjTranspose
#print axioms Comparison.commutes_Θ_iff
#print axioms Comparison.γ_isDistinction
#print axioms Comparison.clifford
#print axioms Comparison.γ_prod
#print axioms Comparison.eq_sum_coord
#print axioms Comparison.distinction_iff
#print axioms Comparison.coord_sum
#print axioms Comparison.sq_sum
#print axioms Comparison.distinction_sq
#print axioms Comparison.P3_holds
#print axioms Comparison.trace_obs_mul
#print axioms Comparison.span_obs_eq_hermitian
#print axioms Comparison.finrank_hermitian
#print axioms Comparison.obs_mul_J
#print axioms Comparison.anticomm_γv
#print axioms Comparison.side_mul_self
#print axioms Comparison.side_add_side_neg
#print axioms Comparison.side_mul_side_neg
#print axioms Comparison.trace_side
#print axioms Comparison.overlap
-- One model
#print axioms Comparison.one_model
#print axioms Comparison.distinctionN_one_eq_zero
#print axioms Comparison.diagWitness_isDistinction
#print axioms Comparison.diagWitness_sq_ne
#print axioms Comparison.Partner.inner_self_Θ
#print axioms Comparison.Partner.norm_Θ
#print axioms Comparison.Partner.exists_normal_basis
#print axioms Comparison.Partner.finrank_eq
#print axioms Comparison.Partner.coord_Θ
#print axioms Comparison.Partner.isDistinctionH_iff
#print axioms Comparison.Partner.P3H_iff
#print axioms Comparison.Partner.one_model_general
-- Book II: two systems
#print axioms Comparison.Ω_eq_sum
#print axioms Comparison.Ω_basis_free
#print axioms Comparison.Ω_norm
#print axioms Comparison.same_from_either_thing
#print axioms Comparison.L_eq_swap_singlet
#print axioms Comparison.agreement
#print axioms Comparison.count_rel
#print axioms Comparison.L_rel
#print axioms Comparison.rel_inner
#print axioms Comparison.finrank_eigenspace_L_six
#print axioms Comparison.finrank_eigenspace_L_two
#print axioms Comparison.finrank_eigenspace_L_neg_two
#print axioms Comparison.eigenspace_L_other
#print axioms Comparison.disagreement_eq_zero_iff
#print axioms Comparison.disagreement_sum_sq
#print axioms Comparison.lineOf_unit
#print axioms Comparison.disagreement_prodRel_ge
#print axioms Comparison.sum_mixedLine_sq_le
#print axioms Comparison.trace_prod_disagreement
#print axioms Comparison.disagreement_mixed_ge
#print axioms Comparison.disagreement_mixture_ge
#print axioms Comparison.partnerOp_eq_self_iff
#print axioms Comparison.partnerTwo_kron
#print axioms Comparison.partnerTwo_swap
#print axioms Comparison.partnerTwo_Eop
#print axioms Comparison.partnerTwo_L
-- Book III: the six directions
#print axioms Comparison.sixP3_transpose
#print axioms Comparison.sixP1_transpose
#print axioms Comparison.sign_of_time
#print axioms Comparison.pf_P1_six
#print axioms Comparison.det_eq_pf_sq
#print axioms Comparison.det_cone
#print axioms Comparison.finrank_su4
#print axioms Comparison.finrank_sp2
#print axioms Comparison.sp2_eq_span
#print axioms Comparison.line_turns_singlet
#print axioms Comparison.plane_keeps_singlet
#print axioms Comparison.keeps_partner_iff
#print axioms Comparison.pf_conj
#print axioms Comparison.det_eq_one_of_keeps_J
#print axioms Comparison.keeps_singlet_iff
#print axioms Comparison.keeps_L_iff
#print axioms Comparison.neg_iff_I_smul
#print axioms Comparison.gen_acts
#print axioms Comparison.plane_bijective
#print axioms Comparison.plane_fst_eq_zero_iff
-- Book IV: divisions and the square root of the sign
#print axioms Comparison.gen_acts_matrix
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
