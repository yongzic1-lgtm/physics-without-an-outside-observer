import Comparison.Colour

/-!
# Axiom audit of Books XIII on in Lean

Build with `lake build Comparison.Colour.Audit`. Every line must read
`depends on axioms: [propext, Classical.choice, Quot.sound]` or a part of it; `sorryAx` would mean a
`sorry`.
-/

-- BoundStates.lean
#print axioms Comparison.five_linesZ
#print axioms Comparison.map_one_gauss
#print axioms Comparison.five_lines
#print axioms Comparison.orderSign_model
#print axioms Comparison.γ_mul_γ_mul
#print axioms Comparison.colour_product
#print axioms Comparison.colour_product_oriented
#print axioms Comparison.colour_product_model
#print axioms Comparison.levi3_values
#print axioms Comparison.three_orders
#print axioms Comparison.eps_lines
#print axioms Comparison.baryon_lands_on_plane
#print axioms Comparison.baryon_lands_on_plane_model
#print axioms Comparison.planeRel_eq
#print axioms Comparison.γ_conj_plane
#print axioms Comparison.L_planeRel
#print axioms Comparison.meson_either_end
#print axioms Comparison.card_outside
#print axioms Comparison.meson_lands_on_singlet
#print axioms Comparison.L_singlet

-- LastDirections.lean
#print axioms Comparison.dot2_eq
#print axioms Comparison.swap2_mulVec
#print axioms Comparison.swap2_sq
#print axioms Comparison.dot2_sq
#print axioms Comparison.dot2_agree
#print axioms Comparison.dot2_differ
#print axioms Comparison.dot3_mulVec
#print axioms Comparison.dot3_agree
#print axioms Comparison.dot3_differ
#print axioms Comparison.dot3_example
#print axioms Comparison.dot3_example_agree
#print axioms Comparison.swapSum_twice
#print axioms Comparison.swapSum_smul
#print axioms Comparison.dot3_sq
#print axioms Comparison.lastDirection_cost

-- Kernel.lean
#print axioms Comparison.invSqrt3_mul_self
#print axioms Comparison.star_invSqrt3
#print axioms Comparison.gen3_castSucc
#print axioms Comparison.gen3_last
#print axioms Comparison.sum_gen3
#print axioms Comparison.last_mul
#print axioms Comparison.last_mul_star
#print axioms Comparison.gen3_conjTranspose
#print axioms Comparison.gen3_trace
#print axioms Comparison.gen3_trace_mul
#print axioms Comparison.fierz
#print axioms Comparison.casimir
#print axioms Comparison.star_gen3
#print axioms Comparison.meson_pair
#print axioms Comparison.pair_eq
#print axioms Comparison.swap3_mulVec
#print axioms Comparison.pair_antisymm
#print axioms Comparison.pair_symm
#print axioms Comparison.pair01_eq
#print axioms Comparison.pair02_eq
#print axioms Comparison.baryon_line

-- Singlets.lean
#print axioms Comparison.isSU3_of
#print axioms Comparison.IsSU3.mul_star
#print axioms Comparison.IsSU3.det
#print axioms Comparison.turnA_SU3
#print axioms Comparison.turnB_SU3
#print axioms Comparison.turnCyc_SU3
#print axioms Comparison.turnI1_SU3
#print axioms Comparison.turnI2_SU3
#print axioms Comparison.turnX01_SU3
#print axioms Comparison.turnX12_SU3
#print axioms Comparison.mulEntries
#print axioms Comparison.meson_singlet
#print axioms Comparison.levi_kept
#print axioms Comparison.act3_diag
#print axioms Comparison.turnI1_eq
#print axioms Comparison.turnI2_eq
#print axioms Comparison.zero_of_phase
#print axioms Comparison.baryon_singlet
#print axioms Comparison.ω3_primitive
#print axioms Comparison.centre_SU3
#print axioms Comparison.actN_centre
#print axioms Comparison.no_singlet
#print axioms Comparison.norm_delta
#print axioms Comparison.norm_eps
#print axioms Comparison.hook_values

-- Tableaux.lean
#print axioms Comparison.mem_three
#print axioms Comparison.count_cons_self
#print axioms Comparison.count_cons_ne
#print axioms Comparison.mem_latticeGen
#print axioms Comparison.latticeGen_nodup
#print axioms Comparison.lattice_words
#print axioms Comparison.tableaux_counts

-- ClosedAvailableTransitions.lean
#print axioms Comparison.closed_target_list
#print axioms Comparison.closed_target
#print axioms Comparison.undo_closed
#print axioms Comparison.closed_from_undo_list
#print axioms Comparison.closed_from_undo
#print axioms Comparison.blockDD_row
#print axioms Comparison.blockDD_col
#print axioms Comparison.blockDD_sq
#print axioms Comparison.undoProj_mul
#print axioms Comparison.mul_undoProj
#print axioms Comparison.det_closed
#print axioms Comparison.closed_inverse
#print axioms Comparison.toBlock_one_sub_diag
#print axioms Comparison.toBlock_one_sub_off
#print axioms Comparison.toBlock_one_sub_off'
#print axioms Comparison.det_availableTransitions
#print axioms Comparison.availableTransitions_counts
#print axioms Comparison.availableTransitions_steps
#print axioms Comparison.stepQ_mulVec_one
#print axioms Comparison.stepQ_vecMul_one
#print axioms Comparison.mulVec_split
#print axioms Comparison.vecMul_split
#print axioms Comparison.watched_rows
#print axioms Comparison.watched_cols

-- Inventory.lean
#print axioms Comparison.pair_on_singlet
#print axioms Comparison.singlet_inner_plane
#print axioms Comparison.transition_weight
#print axioms Comparison.transition_inventory
#print axioms Comparison.inventory_by_lines
#print axioms Comparison.availableTransitions_diag
#print axioms Comparison.trace_diag_mul
#print axioms Comparison.inventory_trace
#print axioms Comparison.inventory_rates
#print axioms Comparison.pole_of_count
#print axioms Comparison.rest_poles
#print axioms Comparison.record_count
#print axioms Comparison.three_readings
#print axioms Comparison.pole_reading_value

-- GramTerm.lean
#print axioms Comparison.swap_conjTranspose
#print axioms Comparison.Eop_conjTranspose
#print axioms Comparison.swap_mul_swap
#print axioms Comparison.Eop_mul_Eop
#print axioms Comparison.swap_mulVec_singlet
#print axioms Comparison.trace_one_two
#print axioms Comparison.trace_swap
#print axioms Comparison.sum_norm_singlet
#print axioms Comparison.trace_Eop
#print axioms Comparison.trace_swap_Eop
#print axioms Comparison.trace_Eop_mul_Eop
#print axioms Comparison.pairing_gram
#print axioms Comparison.gram3_eq
#print axioms Comparison.gram_levels
#print axioms Comparison.trace_gram
#print axioms Comparison.det_F0
#print axioms Comparison.gramTerm_forms
#print axioms Comparison.stepT_one_eq
#print axioms Comparison.D_plus_pos
#print axioms Comparison.weight_moves_zero
#print axioms Comparison.L_in_pairings
#print axioms Comparison.trace_L_sq
#print axioms Comparison.card_BL
#print axioms Comparison.card_Bhbar
#print axioms Comparison.Bhbar_planes
#print axioms Comparison.volume_eq
#print axioms Comparison.volume_BL
#print axioms Comparison.volume_Bhbar
#print axioms Comparison.deriv_volume_Bhbar
#print axioms Comparison.opened_volumes
#print axioms Comparison.Bhbar_closed
#print axioms Comparison.card_avoid
#print axioms Comparison.singlet_neighbours
#print axioms Comparison.b_forms

-- Proton.lean
#print axioms Comparison.log_five_fourths_sum
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

-- Visits.lean
#print axioms Comparison.class_steps
#print axioms Comparison.excursion_system
#print axioms Comparison.excursion_system_unique
#print axioms Comparison.GP_eq
#print axioms Comparison.GP_one
#print axioms Comparison.GP_deriv
#print axioms Comparison.GP_denominator
#print axioms Comparison.xc_gt_one
#print axioms Comparison.xc'_neg
#print axioms Comparison.GP_denom_pos
#print axioms Comparison.xc_root
#print axioms Comparison.regression
#print axioms Comparison.pole_condition
#print axioms Comparison.pion_radius
#print axioms Comparison.vector_pole

-- Arcs.lean
#print axioms Comparison.card_arcs
#print axioms Comparison.arcs_leaving
#print axioms Comparison.arcs_entering
#print axioms Comparison.arc_rows
#print axioms Comparison.arc_cols
#print axioms Comparison.passage_equations
#print axioms Comparison.landing_unique_Z
#print axioms Comparison.MΩ_mul_J
#print axioms Comparison.landing_unique
#print axioms Comparison.landing_hidden
#print axioms Comparison.det_six_root
#print axioms Comparison.gramTerm_one_direction
#print axioms Comparison.gramN_levels
#print axioms Comparison.gramN_four
#print axioms Comparison.five_lines_only
#print axioms Comparison.kept_by_lastDirection
#print axioms Comparison.kept_rels
#print axioms Comparison.moved_by_singlet
#print axioms Comparison.kept_iff_plane
#print axioms Comparison.gen_rel
#print axioms Comparison.Bhbar_agree
#print axioms Comparison.excursion_leaves_singlet
#print axioms Comparison.commutant_singlet
#print axioms Comparison.commutant_lastDirection
#print axioms Comparison.BL_from_plane
#print axioms Comparison.Bhbar_charges
#print axioms Comparison.availableTransitions_Bhbar
#print axioms Comparison.untaken
#print axioms Comparison.untaken_lastDirection
#print axioms Comparison.untaken_slope
#print axioms Comparison.flux_counts
#print axioms Comparison.edges_count
#print axioms Comparison.count_and_gramTerm
#print axioms Comparison.tau_bounds

-- Light.lean
#print axioms Comparison.arcs_along
#print axioms Comparison.lastDirections_doubly_stochastic
#print axioms Comparison.delta_counts
#print axioms Comparison.trace_swap2
#print axioms Comparison.trace_dot2
#print axioms Comparison.strange_share
#print axioms Comparison.coleman_glashow

-- Heavy.lean
#print axioms Comparison.rest_pole_counts
#print axioms Comparison.contact_factor
#print axioms Comparison.spin_weights
#print axioms Comparison.partner_split
#print axioms Comparison.annihilation_small
#print axioms Comparison.availableTransitions_free_ratio
#print axioms Comparison.availableTransitions_free_values
#print axioms Comparison.charge_products
#print axioms Comparison.heavy_baryons

