/-
Copyright (c) 2026 Henru Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henru Wang
-/
module

import PionCompleteness

/-!
# Axioms of the results

`lake build Verify` checks that each result below depends only on Lean's standard axioms
(`[propext, Classical.choice, Quot.sound]` or a subset): no `sorryAx`, no custom axiom. Each
`#print axioms` is wrapped in `#guard_msgs` (line breaks in the message ignored), so any other
answer fails the build.
The results are listed module by module. The statements of Theorem Π are
`PionCompleteness.Pi.pi_clause1`, `cl2a`, `pi_clause2` and `pi_minimal_iff` (module `C10`); in the
paper's terms, the main theorem is `every_coordinate_zero_contains_a_family_member`,
`family_members_are_minimal_zeros` and `minimal_coordinate_zeros_are_the_list` (module `Paper`,
namespace `PionCompleteness.Paper.NLSM.Zeros`).
-/

-- TreeRectangleZero: the main statement and its witness.
/-- info: 'PionCompleteness.TreeRectangleZero.amp_eq_zero_of_onRect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.TreeRectangleZero.amp_eq_zero_of_onRect
/-- info: 'PionCompleteness.TreeRectangleZero.onRect_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.TreeRectangleZero.onRect_inhabited
-- TreeRectangleZero: the proof steps.
/-- info: 'PionCompleteness.TreeRectangleZero.amp_eq_F' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.TreeRectangleZero.amp_eq_F
/-- info: 'PionCompleteness.TreeRectangleZero.F_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.TreeRectangleZero.F_eq_sum
/-- info: 'PionCompleteness.TreeRectangleZero.mesh_telescope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.TreeRectangleZero.mesh_telescope
/-- info: 'PionCompleteness.TreeRectangleZero.star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.TreeRectangleZero.star
/-- info: 'PionCompleteness.TreeRectangleZero.F_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.TreeRectangleZero.F_factor
/-- info: 'PionCompleteness.TreeRectangleZero.amp_eq_zero_m1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.TreeRectangleZero.amp_eq_zero_m1
/-- info: 'PionCompleteness.TreeRectangleZero.amp_rot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.TreeRectangleZero.amp_rot
/-- info: 'PionCompleteness.TreeRectangleZero.onRect_rot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.TreeRectangleZero.onRect_rot
/-- info: 'PionCompleteness.TreeRectangleZero.mesh_adjacent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.TreeRectangleZero.mesh_adjacent
-- TreeRectangleZero: sanity checks and negative controls.
/-- info: 'PionCompleteness.TreeRectangleZero.triangulations_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.TreeRectangleZero.triangulations_five
/-- info: 'PionCompleteness.TreeRectangleZero.X5w_onRect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.TreeRectangleZero.X5w_onRect
/-- info: 'PionCompleteness.TreeRectangleZero.X5w_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.TreeRectangleZero.X5w_ne_zero
/-- info: 'PionCompleteness.TreeRectangleZero.negcontrol_minus_tile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.TreeRectangleZero.negcontrol_minus_tile
/-- info: 'PionCompleteness.TreeRectangleZero.amp_five_rect11' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.TreeRectangleZero.amp_five_rect11
/-- info: 'PionCompleteness.TreeRectangleZero.rev_negcontrol_no_hX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.TreeRectangleZero.rev_negcontrol_no_hX
/-- info: 'PionCompleteness.TreeRectangleZero.rev_negcontrol_crossing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.TreeRectangleZero.rev_negcontrol_crossing
/-- info: 'PionCompleteness.TreeRectangleZero.rev_card_triangulations_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.TreeRectangleZero.rev_card_triangulations_six
-- ChainSlice: the main theorem and its corollaries.
/-- info: 'PionCompleteness.ChainSlice.t1E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.ChainSlice.t1E
/-- info: 'PionCompleteness.ChainSlice.t1E_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.ChainSlice.t1E_free
/-- info: 'PionCompleteness.ChainSlice.closure_containsDiamond_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.ChainSlice.closure_containsDiamond_iff
-- ChainSlice: the proof steps.
/-- info: 'PionCompleteness.ChainSlice.mesh_tlab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.ChainSlice.mesh_tlab
/-- info: 'PionCompleteness.ChainSlice.onRect_of_diamond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.ChainSlice.onRect_of_diamond
/-- info: 'PionCompleteness.ChainSlice.amp_zero_of_diamond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.ChainSlice.amp_zero_of_diamond
/-- info: 'PionCompleteness.ChainSlice.amp_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.ChainSlice.amp_pos
/-- info: 'PionCompleteness.ChainSlice.E_subset_diagonals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.ChainSlice.E_subset_diagonals
-- ChainSlice: sanity checks and negative controls.
/-- info: 'PionCompleteness.ChainSlice.E_eq_longAvoid_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.ChainSlice.E_eq_longAvoid_small
/-- info: 'PionCompleteness.ChainSlice.card_Free_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.ChainSlice.card_Free_small
/-- info: 'PionCompleteness.ChainSlice.card_diamonds_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.ChainSlice.card_diamonds_small
/-- info: 'PionCompleteness.ChainSlice.diamond_subset_diagonals_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.ChainSlice.diamond_subset_diagonals_small
/-- info: 'PionCompleteness.ChainSlice.diamond_inter_Free_seven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.ChainSlice.diamond_inter_Free_seven
/-- info: 'PionCompleteness.ChainSlice.sanity_six_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.ChainSlice.sanity_six_pos
/-- info: 'PionCompleteness.ChainSlice.sanity_six_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.ChainSlice.sanity_six_zero
/-- info: 'PionCompleteness.ChainSlice.negctl_offbyone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.ChainSlice.negctl_offbyone
/-- info: 'PionCompleteness.ChainSlice.negctl_no_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.ChainSlice.negctl_no_E
/-- info: 'PionCompleteness.ChainSlice.rev_negctl_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.ChainSlice.rev_negctl_small
-- PionZeros: Theorem A and its witness.
/-- info: 'PionCompleteness.PionZeros.theoremA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionZeros.theoremA
/-- info: 'PionCompleteness.PionZeros.diagram_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionZeros.diagram_eq_zero
/-- info: 'PionCompleteness.PionZeros.Qpi_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionZeros.Qpi_eq_zero
/-- info: 'PionCompleteness.PionZeros.ZT_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionZeros.ZT_inhabited
-- PionZeros: the proof steps.
/-- info: 'PionCompleteness.PionZeros.exists_goodQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionZeros.exists_goodQ
/-- info: 'PionCompleteness.PionZeros.quads_alternating' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionZeros.quads_alternating
/-- info: 'PionCompleteness.PionZeros.vnum_eq_zero_of_goodQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionZeros.vnum_eq_zero_of_goodQ
/-- info: 'PionCompleteness.PionZeros.vnum_eq_vnumX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionZeros.vnum_eq_vnumX
-- PionZeros: the structure and count of quadrangulations (not needed by Theorem A).
/-- info: 'PionCompleteness.PionZeros.card_quads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionZeros.card_quads
/-- info: 'PionCompleteness.PionZeros.leg_side_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionZeros.leg_side_unique
/-- info: 'PionCompleteness.PionZeros.diag_plus_minus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionZeros.diag_plus_minus
/-- info: 'PionCompleteness.PionZeros.p3b_diag_plus_minus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionZeros.p3b_diag_plus_minus
/-- info: 'PionCompleteness.PionZeros.p3b_diag_plus_minus_needs_pi_lt_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionZeros.p3b_diag_plus_minus_needs_pi_lt_two
/-- info: 'PionCompleteness.PionZeros.card_quadrangulations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionZeros.card_quadrangulations
-- PionZeros: sanity checks and negative controls.
/-- info: 'PionCompleteness.PionZeros.card_quadrangulations_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionZeros.card_quadrangulations_small
/-- info: 'PionCompleteness.PionZeros.alternating_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionZeros.alternating_six
/-- info: 'PionCompleteness.PionZeros.goodQ_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionZeros.goodQ_six
/-- info: 'PionCompleteness.PionZeros.theoremA_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionZeros.theoremA_six
/-- info: 'PionCompleteness.PionZeros.Qpi_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionZeros.Qpi_six
/-- info: 'PionCompleteness.PionZeros.ZT_inhabited_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionZeros.ZT_inhabited_six
/-- info: 'PionCompleteness.PionZeros.negctl_minus_tile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionZeros.negctl_minus_tile
/-- info: 'PionCompleteness.PionZeros.negctl_wrong_polarity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionZeros.negctl_wrong_polarity
/-- info: 'PionCompleteness.PionZeros.card_quads_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionZeros.card_quads_small
/-- info: 'PionCompleteness.PionZeros.alternating_eight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionZeros.alternating_eight
/-- info: 'PionCompleteness.PionZeros.goodQ_eight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionZeros.goodQ_eight
/-- info: 'PionCompleteness.PionZeros.theoremA_eight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionZeros.theoremA_eight
/-- info: 'PionCompleteness.PionZeros.Qpi_eight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionZeros.Qpi_eight
/-- info: 'PionCompleteness.PionZeros.negctl_mixed_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionZeros.negctl_mixed_parity
/-- info: 'PionCompleteness.PionZeros.rev_negctl_singleton_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionZeros.rev_negctl_singleton_T
/-- info: 'PionCompleteness.PionZeros.rev_negctl_minus_tile_T135' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionZeros.rev_negctl_minus_tile_T135
/-- info: 'PionCompleteness.PionZeros.rev_negctl_maximal_among_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionZeros.rev_negctl_maximal_among_all
-- PionNLSM: Theorem B and the zeros of the NLSM amplitude on Z_T.
/-- info: 'PionCompleteness.PionNLSM.theoremB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionNLSM.theoremB
/-- info: 'PionCompleteness.PionNLSM.theoremB_poly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionNLSM.theoremB_poly
/-- info: 'PionCompleteness.PionNLSM.theoremB_rat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionNLSM.theoremB_rat
/-- info: 'PionCompleteness.PionNLSM.Qpi_polarity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionNLSM.Qpi_polarity
/-- info: 'PionCompleteness.PionNLSM.nlsm_zero_on_ZT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionNLSM.nlsm_zero_on_ZT
/-- info: 'PionCompleteness.PionNLSM.nlsm_ratZero_ZT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionNLSM.nlsm_ratZero_ZT
-- PionNLSM: the rational-function layer and the definition of NLSM.
/-- info: 'PionCompleteness.PionNLSM.NLSM_eq_ps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionNLSM.NLSM_eq_ps
/-- info: 'PionCompleteness.PionNLSM.shiftCoeff_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionNLSM.shiftCoeff_neg
/-- info: 'PionCompleteness.PionNLSM.gen_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionNLSM.gen_ne_zero
/-- info: 'PionCompleteness.PionNLSM.line_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionNLSM.line_bridge
/-- info: 'PionCompleteness.PionNLSM.QP_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionNLSM.QP_eval
/-- info: 'PionCompleteness.PionNLSM.amp_ratZero_onRect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionNLSM.amp_ratZero_onRect
/-- info: 'PionCompleteness.PionNLSM.theoremA_rat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionNLSM.theoremA_rat
-- PionNLSM: small cases end to end, witnesses and negative controls.
/-- info: 'PionCompleteness.PionNLSM.NLSM_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionNLSM.NLSM_four
/-- info: 'PionCompleteness.PionNLSM.shiftCoeff_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionNLSM.shiftCoeff_four
/-- info: 'PionCompleteness.PionNLSM.Qpi_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionNLSM.Qpi_four
/-- info: 'PionCompleteness.PionNLSM.theoremB_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionNLSM.theoremB_four
/-- info: 'PionCompleteness.PionNLSM.NLSM_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionNLSM.NLSM_six
/-- info: 'PionCompleteness.PionNLSM.shiftCoeff_six_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionNLSM.shiftCoeff_six_three
/-- info: 'PionCompleteness.PionNLSM.theoremB_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionNLSM.theoremB_six
/-- info: 'PionCompleteness.PionNLSM.NLSM_ne_zero_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionNLSM.NLSM_ne_zero_small
/-- info: 'PionCompleteness.PionNLSM.theoremB_hyp_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionNLSM.theoremB_hyp_inhabited
/-- info: 'PionCompleteness.PionNLSM.negctl_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionNLSM.negctl_sign
/-- info: 'PionCompleteness.PionNLSM.negctl_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionNLSM.negctl_order
/-- info: 'PionCompleteness.PionNLSM.negctl_poles_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionNLSM.negctl_poles_six
/-- info: 'PionCompleteness.PionNLSM.negctl_pi_two_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionNLSM.negctl_pi_two_six
/-- info: 'PionCompleteness.PionNLSM.negctl_polarity_diagram_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PionNLSM.negctl_polarity_diagram_six
-- C0: results on the amplitude, the zero predicates and `𝒢_N`.
/-- info: 'PionCompleteness.Pi.calA_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.calA_four
/-- info: 'PionCompleteness.Pi.calA_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.calA_six
/-- info: 'PionCompleteness.Pi.nonDeg_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.nonDeg_mono
/-- info: 'PionCompleteness.Pi.nonDeg_iff_pt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.nonDeg_iff_pt
/-- info: 'PionCompleteness.Pi.ampZeroOn_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.ampZeroOn_mono
/-- info: 'PionCompleteness.Pi.ampZeroOn_iff_ratZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.ampZeroOn_iff_ratZero
/-- info: 'PionCompleteness.Pi.calA_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.calA_eq_zero_iff
/-- info: 'PionCompleteness.Pi.ampZeroOn_iff_nlsmZeroOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.ampZeroOn_iff_nlsmZeroOn
/-- info: 'PionCompleteness.Pi.nonzeroOn_iff_not_nlsmZeroOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.nonzeroOn_iff_not_nlsmZeroOn
/-- info: 'PionCompleteness.Pi.nonzeroOn_iff_not_ampZeroOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.nonzeroOn_iff_not_ampZeroOn
/-- info: 'PionCompleteness.Pi.gFamily_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.gFamily_sub
-- C0: the ZMod N bridge and rotations.
/-- info: 'PionCompleteness.Pi.labZ_legZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.labZ_legZ
/-- info: 'PionCompleteness.Pi.legZ_labZ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.legZ_labZ
/-- info: 'PionCompleteness.Pi.labZ_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.labZ_parity
/-- info: 'PionCompleteness.Pi.legZ_rotLeg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.legZ_rotLeg
/-- info: 'PionCompleteness.Pi.inST_rotLeg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.inST_rotLeg
/-- info: 'PionCompleteness.Pi.sepPairs_rotLeg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.sepPairs_rotLeg
-- C0: the first steps of the proof.
/-- info: 'PionCompleteness.Pi.fpi_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.fpi_iff
/-- info: 'PionCompleteness.Pi.lemma65' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.lemma65
/-- info: 'PionCompleteness.Pi.chord_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.chord_restrict
/-- info: 'PionCompleteness.Pi.lemma14_6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.lemma14_6
-- C1: (Tri), and the sides of an odd chord as cyclic arcs.
/-- info: 'PionCompleteness.Pi.threeSep_consecWit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.threeSep_consecWit
/-- info: 'PionCompleteness.Pi.threeSep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.threeSep
/-- info: 'PionCompleteness.Pi.sides_eq_cycArc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.sides_eq_cycArc
/-- info: 'PionCompleteness.Pi.childSize_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.childSize_bounds
-- C2: an innermost chord exists, and (Even-top′) holds at it.
-- can_exists: changed on purpose, its unused hypothesis `InFpi N S` dropped.
/-- info: 'PionCompleteness.Pi.can_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.can_exists
/-- info: 'PionCompleteness.Pi.evenTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.evenTop
-- C3: the chain's output, children, and the parts of `𝒢_N`.
/-- info: 'PionCompleteness.Pi.bot_of_evenTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.bot_of_evenTop
-- int_of_bot: changed on purpose, its unused hypothesis `InFpi N S` dropped.
/-- info: 'PionCompleteness.Pi.int_of_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.int_of_bot
/-- info: 'PionCompleteness.Pi.chain_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.chain_interval
/-- info: 'PionCompleteness.Pi.childF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.childF
/-- info: 'PionCompleteness.Pi.gFamily_antichain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.gFamily_antichain
/-- info: 'PionCompleteness.Pi.cl2a_nondeg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.cl2a_nondeg
/-- info: 'PionCompleteness.Pi.cl2a_diamond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.cl2a_diamond

-- C4: Π and `cl2a` in their M2 forms (the analytic inputs, or clause 1 and `cl2a`, as hypotheses).
/-- info: 'PionCompleteness.Pi.pi_clause1_M2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.pi_clause1_M2
/-- info: 'PionCompleteness.Pi.cl2a_M2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.cl2a_M2
/-- info: 'PionCompleteness.Pi.prop14_7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.prop14_7
/-- info: 'PionCompleteness.Pi.minimal_iff_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.minimal_iff_of
/-- info: 'PionCompleteness.Pi.pi_clause2_M2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.pi_clause2_M2
/-- info: 'PionCompleteness.Pi.pi_minimal_iff_M2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.pi_minimal_iff_M2

-- C5: the germ input at every even `N ≥ 6`. (C6–C9 hold helpers of the residue input, proved
-- in C10.)
/-- info: 'PionCompleteness.Pi.germ_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.germ_input

-- C10: Theorem Π — clause 1 (completeness), `cl2a`, clause 2 (minimality) and "hence" — and the two
-- analytic inputs proved here, the residue and children input and the S_T zero.
/-- info: 'PionCompleteness.Pi.pi_clause1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.pi_clause1
/-- info: 'PionCompleteness.Pi.cl2a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.cl2a
/-- info: 'PionCompleteness.Pi.pi_clause2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.pi_clause2
/-- info: 'PionCompleteness.Pi.pi_minimal_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.pi_minimal_iff
/-- info: 'PionCompleteness.Pi.resChild_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.resChild_input
/-- info: 'PionCompleteness.Pi.stZero_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.stZero_input

-- C10: instances at N = 6 (three members of 𝒢_6 are zeros, clause 1's hypothesis is satisfiable,
-- clause 2 holds for them) and negative controls (∅, |T| = 1, a mixed triple, degenerate sets, the
-- diamonds are needed, minimality is not automatic).
/-- info: 'PionCompleteness.Pi.zero_ST135' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.zero_ST135
/-- info: 'PionCompleteness.Pi.zero_ST13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.zero_ST13
/-- info: 'PionCompleteness.Pi.zero_D14' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.zero_D14
/-- info: 'PionCompleteness.Pi.clause1_hyp_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.clause1_hyp_inhabited
/-- info: 'PionCompleteness.Pi.clause2_six_instances' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.clause2_six_instances
/-- info: 'PionCompleteness.Pi.control_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.control_empty
/-- info: 'PionCompleteness.Pi.nd_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.nd_empty
/-- info: 'PionCompleteness.Pi.control_T1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.control_T1
/-- info: 'PionCompleteness.Pi.control_mixed124' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.control_mixed124
/-- info: 'PionCompleteness.Pi.degenerate_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.degenerate_full
/-- info: 'PionCompleteness.Pi.control_diamonds_needed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.control_diamonds_needed
/-- info: 'PionCompleteness.Pi.control_not_minimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.control_not_minimal
/-- info: 'PionCompleteness.Pi.control_ndZero_not_minimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.control_ndZero_not_minimal

-- C10: instances at N = 8, 10, 12 ((Tri), `lemma14_6`'s hypotheses, the route objects) and the
-- controls.
/-- info: 'PionCompleteness.Pi.nd8_ST135' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.nd8_ST135
/-- info: 'PionCompleteness.Pi.nd8_D14' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.nd8_D14
/-- info: 'PionCompleteness.Pi.mem8_ST135' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.mem8_ST135
/-- info: 'PionCompleteness.Pi.mem8_D14' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.mem8_D14
/-- info: 'PionCompleteness.Pi.threeSep_setting_ten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.threeSep_setting_ten
/-- info: 'PionCompleteness.Pi.threeSep_witness_ten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.threeSep_witness_ten
/-- info: 'PionCompleteness.Pi.threeSep_nonwitness_ten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.threeSep_nonwitness_ten
/-- info: 'PionCompleteness.Pi.threeSep_setting_reject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.threeSep_setting_reject
/-- info: 'PionCompleteness.Pi.lemma14_6_hyp_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.lemma14_6_hyp_inhabited
/-- info: 'PionCompleteness.Pi.nonzero_empty6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.nonzero_empty6
/-- info: 'PionCompleteness.Pi.control_mixed136' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.control_mixed136
/-- info: 'PionCompleteness.Pi.fpi8_mixed136' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.fpi8_mixed136
/-- info: 'PionCompleteness.Pi.rev_card6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.rev_card6
/-- info: 'PionCompleteness.Pi.rev_card8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.rev_card8
/-- info: 'PionCompleteness.Pi.rev_nonempty8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.rev_nonempty8
/-- info: 'PionCompleteness.Pi.rev_wrap18' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.rev_wrap18
/-- info: 'PionCompleteness.Pi.rev_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.rev_head
/-- info: 'PionCompleteness.Pi.sides8_27' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.sides8_27
/-- info: 'PionCompleteness.Pi.rev_tri12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.rev_tri12
/-- info: 'PionCompleteness.Pi.rev_tri12_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.rev_tri12_w
/-- info: 'PionCompleteness.Pi.rev_tri12_nw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.rev_tri12_nw
/-- info: 'PionCompleteness.Pi.ctl8_route' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.ctl8_route
/-- info: 'PionCompleteness.Pi.ctl8_children' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.ctl8_children
/-- info: 'PionCompleteness.Pi.ctl8_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.ctl8_neg
/-- info: 'PionCompleteness.Pi.ctl10_evenTop_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.ctl10_evenTop_fails

-- Conventions: 𝒜_N against outside closed forms (KNT arXiv:1304.3048 eqs. (33), (34), (200)).
/-- info: 'PionCompleteness.Pi.calA_four_knt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.calA_four_knt
/-- info: 'PionCompleteness.Pi.calA_six_knt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.calA_six_knt
/-- info: 'PionCompleteness.Pi.calA_eight_knt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.calA_eight_knt
/-- info: 'PionCompleteness.Pi.nlsm_four_knt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.nlsm_four_knt
/-- info: 'PionCompleteness.Pi.nlsm_six_knt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.nlsm_six_knt
/-- info: 'PionCompleteness.Pi.nlsm_eight_knt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.nlsm_eight_knt
/-- info: 'PionCompleteness.Pi.oddDiagonals_eight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.oddDiagonals_eight
/-- info: 'PionCompleteness.Pi.negctl_knt_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.negctl_knt_sign
/-- info: 'PionCompleteness.Pi.negctl_knt_dictionary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.negctl_knt_dictionary

-- Conventions, every N: KNT's Feynman rules in the Cayley parametrisation (eq. (62)).
/-- info: 'PionCompleteness.Pi.kntSq_kntS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.kntSq_kntS
/-- info: 'PionCompleteness.Pi.kntV_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.kntV_const
/-- info: 'PionCompleteness.Pi.pkG_sum_kids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.pkG_sum_kids
/-- info: 'PionCompleteness.Pi.pkG_card_Ico_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.pkG_card_Ico_root
/-- info: 'PionCompleteness.Pi.faces_card_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.faces_card_sum
/-- info: 'PionCompleteness.Pi.faces_card_sub_two_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.faces_card_sub_two_sum
/-- info: 'PionCompleteness.Pi.faces_half_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.faces_half_sum
/-- info: 'PionCompleteness.Pi.kntCayleySum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.kntCayleySum_eq
/-- info: 'PionCompleteness.Pi.nlsm_knt_cayley' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.nlsm_knt_cayley
/-- info: 'PionCompleteness.Pi.kntFeynman_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.kntFeynman_four
/-- info: 'PionCompleteness.Pi.kntFeynman_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.kntFeynman_six
/-- info: 'PionCompleteness.Pi.kntCayleySum_four_knt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.kntCayleySum_four_knt
/-- info: 'PionCompleteness.Pi.kntCayleySum_six_knt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.kntCayleySum_six_knt
/-- info: 'PionCompleteness.Pi.kntCayleySum_eight_knt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.kntCayleySum_eight_knt
/-- info: 'PionCompleteness.Pi.negctl_knt_vertex_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.negctl_knt_vertex_constant
/-- info: 'PionCompleteness.Pi.negctl_knt_vertex_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.negctl_knt_vertex_sign
/-- info: 'PionCompleteness.Pi.negctl_knt_propagator_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Pi.negctl_knt_propagator_sign

-- Paper: the paper's statements in its exact form.
/-- info: 'PionCompleteness.Paper.onLocus_sepPairs_of_onZT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.onLocus_sepPairs_of_onZT
/-- info: 'PionCompleteness.Paper.onZT_iff_onLocus_sepPairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.onZT_iff_onLocus_sepPairs
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.Families.t_separated_locus_nondegenerate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.Families.t_separated_locus_nondegenerate
/-- info: 'PionCompleteness.Paper.t_separated_zero_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.t_separated_zero_pointwise
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.Families.t_separated_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.Families.t_separated_zero
/-- info: 'PionCompleteness.Paper.NLSM.FeynmanRules.diagrams_vanish_on_t_separated_locus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.FeynmanRules.diagrams_vanish_on_t_separated_locus
/-- info: 'PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.three_row_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.three_row_zeros
/-- info: 'PionCompleteness.Paper.NLSM.FeynmanRules.pkG_V_eq_faceVertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.FeynmanRules.pkG_V_eq_faceVertex
/-- info: 'PionCompleteness.Paper.NLSM.FeynmanRules.cayley_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.FeynmanRules.cayley_form
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.dissection_face_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.dissection_face_count
/-- info: 'PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.on_shell_dissection_has_vanishing_face' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.on_shell_dissection_has_vanishing_face
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.nonvanishing_without_residue_chords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.nonvanishing_without_residue_chords
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.innermost_chord_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.innermost_chord_exists
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.separators_avoid_linked_side' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.separators_avoid_linked_side
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.innermost_class_has_linked_member' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.innermost_class_has_linked_member
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.both_sides_linked_alone_in_flank_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.both_sides_linked_alone_in_flank_class
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.minimality_from_containment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.minimality_from_containment
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.family_members_are_minimal_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.family_members_are_minimal_zeros

/-- info: 'PionCompleteness.Paper.eval_zeroAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.eval_zeroAt
/-- info: 'PionCompleteness.Paper.zeroAt_zeroAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.zeroAt_zeroAt
/-- info: 'PionCompleteness.Paper.ratZeroOn_hyperplane_iff_zeroAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.ratZeroOn_hyperplane_iff_zeroAt
/-- info: 'PionCompleteness.Paper.ratZeroOn_mul_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.ratZeroOn_mul_left
/-- info: 'PionCompleteness.Paper.ringHom_eq_eval_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.ringHom_eq_eval_map
/-- info: 'PionCompleteness.Paper.shiftCoeff_numerator_hom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.shiftCoeff_numerator_hom
/-- info: 'PionCompleteness.Paper.nlsm_numerator_hom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.nlsm_numerator_hom
/-- info: 'PionCompleteness.Paper.eval_mul_of_isHomogeneous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.eval_mul_of_isHomogeneous
/-- info: 'PionCompleteness.Paper.homogeneous_of_numerator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.homogeneous_of_numerator
/-- info: 'PionCompleteness.Paper.prod_oddDiagonals_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.prod_oddDiagonals_erase
/-- info: 'PionCompleteness.Paper.zeroAt_prod_erase_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.zeroAt_prod_erase_ne_zero
/-- info: 'PionCompleteness.Paper.ratZeroOn_of_sub_zeroAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.ratZeroOn_of_sub_zeroAt
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.analytic_facts_delta_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.analytic_facts_delta_order
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.analytic_facts_factorisation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.analytic_facts_factorisation
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.analytic_facts_symmetry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.analytic_facts_symmetry
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.quadrangulation_has_good_quad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.quadrangulation_has_good_quad
/-- info: 'PionCompleteness.Paper.NLSM.FeynmanRules.good_vertex_factor_vanishes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.FeynmanRules.good_vertex_factor_vanishes
/-- info: 'PionCompleteness.Paper.quartic_residue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.quartic_residue
/-- info: 'PionCompleteness.Paper.NLSM.FeynmanRules.quartic_diagram_sum_structure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.FeynmanRules.quartic_diagram_sum_structure
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.single_leg_locus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.single_leg_locus
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.delta_order_factorisation_single_leg_vanishing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.delta_order_factorisation_single_leg_vanishing
/-- info: 'PionCompleteness.Paper.Algebra.RationalFunctions.pole_free_on_odd_chords_is_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Algebra.RationalFunctions.pole_free_on_odd_chords_is_polynomial
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.Families.candidate_sets_are_transversals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.Families.candidate_sets_are_transversals
/-- info: 'PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.block_sums' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.block_sums
/-- info: 'PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.parity_form_nonvanishing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.parity_form_nonvanishing
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.flank_class_top_and_bottom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.flank_class_top_and_bottom
/-- info: 'PionCompleteness.Paper.mesh_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.mesh_add
/-- info: 'PionCompleteness.Paper.mesh_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.mesh_smul
/-- info: 'PionCompleteness.Paper.card_diagonals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.card_diagonals
/-- info: 'PionCompleteness.Paper.mesh_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.mesh_kernel
/-- info: 'PionCompleteness.Paper.sum_shiftSign_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.sum_shiftSign_mul
/-- info: 'PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.momentum_conservation_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.momentum_conservation_relation
/-- info: 'PionCompleteness.Paper.exists_mesh_combination_of_vanishing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.exists_mesh_combination_of_vanishing
/-- info: 'PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.locus_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.locus_coordinates
/-- info: 'PionCompleteness.Paper.mem_oddSideSplit_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.mem_oddSideSplit_iff
/-- info: 'PionCompleteness.Paper.mem_evenSideSplit_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.mem_evenSideSplit_iff
/-- info: 'PionCompleteness.Paper.mem_minRect_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.mem_minRect_iff
/-- info: 'PionCompleteness.Paper.mem_flank_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.mem_flank_split
/-- info: 'PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.flank_sets_of_odd_chord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.flank_sets_of_odd_chord
/-- info: 'PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.on_shell_iff_flank_sets_share_no_missing_pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.on_shell_iff_flank_sets_share_no_missing_pair
/-- info: 'PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.odd_chord_vanishing_on_same_parity_sublocus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.odd_chord_vanishing_on_same_parity_sublocus
/-- info: 'PionCompleteness.Paper.list_member_two_same_parity_pairs_outside' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.list_member_two_same_parity_pairs_outside
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.Families.members_are_closed_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.Families.members_are_closed_zeros
/-- info: 'PionCompleteness.Paper.pkG_r2_vert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.pkG_r2_vert
/-- info: 'PionCompleteness.Paper.pkG_kid_vert_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.pkG_kid_vert_right
/-- info: 'PionCompleteness.Paper.pkG_verts_Icc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.pkG_verts_Icc
/-- info: 'PionCompleteness.Paper.pkG_inner_vert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.pkG_inner_vert
/-- info: 'PionCompleteness.Paper.pkG_verts_not_separated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.pkG_verts_not_separated
/-- info: 'PionCompleteness.Paper.pkG_verts_maximal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.pkG_verts_maximal
/-- info: 'PionCompleteness.Paper.pkG_verts_isFace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.pkG_verts_isFace
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.isFace_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.isFace_iff
/-- info: 'PionCompleteness.Paper.pkG_verts_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.pkG_verts_injOn
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.faces_eq_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.faces_eq_image
/-- info: 'PionCompleteness.Paper.pkG_verts_sup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.pkG_verts_sup
/-- info: 'PionCompleteness.Paper.pkG_W_eq_oddStartLegs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.pkG_W_eq_oddStartLegs
/-- info: 'PionCompleteness.Paper.chordSides_pkG_verts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.chordSides_pkG_verts
/-- info: 'PionCompleteness.Paper.pkG_deg_eq_card_chordSides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.pkG_deg_eq_card_chordSides
/-- info: 'PionCompleteness.Paper.pkG_verts_alternate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.pkG_verts_alternate
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.dissections' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.dissections
/-- info: 'PionCompleteness.Paper.faceVertex_eq_Q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.faceVertex_eq_Q
/-- info: 'PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.face_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.face_identity
/-- info: 'PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.mesh_independent_of_omits_same_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.mesh_independent_of_omits_same_parity
/-- info: 'PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.rows_one_two_span_meet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.rows_one_two_span_meet
/-- info: 'PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.form_identities' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.form_identities
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.odd_chord_sides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.odd_chord_sides

/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.three_separators_single_parity_arc_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  PionCompleteness.Paper.Combinatorics.Polygons.three_separators_single_parity_arc_witness
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.three_separators_contain_t_separated_set' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.three_separators_contain_t_separated_set
/-- info: 'PionCompleteness.Paper.zoneSet_eq_pkT_zoneSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.zoneSet_eq_pkT_zoneSet
/-- info: 'PionCompleteness.Paper.pkT_ZH_of_not_caseEP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.pkT_ZH_of_not_caseEP
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.parity_block_witness_in_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.parity_block_witness_in_cut
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.separator_meets_every_gap_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.separator_meets_every_gap_interval
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.removed_leg_of_tau_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.removed_leg_of_tau_iff
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.removed_leg_of_sigma_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.removed_leg_of_sigma_iff
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.side_gap_gamma_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.side_gap_gamma_sigma
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.side_gap_gamma_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.side_gap_gamma_tau
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.side_gap_left_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.side_gap_left_sigma
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.side_gap_right_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.side_gap_right_tau
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.zoneSet_keeps_middle_legs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.zoneSet_keeps_middle_legs
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.zoneSet_keeps_common_legs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.zoneSet_keeps_common_legs
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.reach_witness_is_odd_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.reach_witness_is_odd_interval
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.reach_witness_has_two_legs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.reach_witness_has_two_legs
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.reach_witness_pairs_in_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.reach_witness_pairs_in_cut
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.residue_chord_joins_innermost_flank_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  PionCompleteness.Paper.Combinatorics.Polygons.residue_chord_joins_innermost_flank_class
/-- info: 'PionCompleteness.Paper.hasNoPoleAlong_of_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.hasNoPoleAlong_of_eq
/-- info: 'PionCompleteness.Paper.restrictsToZeroAlong_of_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.restrictsToZeroAlong_of_eq
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong.hasNoPoleAlong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong.hasNoPoleAlong
/-- info: 'PionCompleteness.Paper.nlsmAvoiding_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.nlsmAvoiding_empty
/-- info: 'PionCompleteness.Paper.nlsmAvoiding_numerator_hom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.nlsmAvoiding_numerator_hom
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses.eq_hitClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses.eq_hitClass
/-- info: 'PionCompleteness.Paper.odd_chord_outside_class_nonvanishing_on_hyperplane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.odd_chord_outside_class_nonvanishing_on_hyperplane
/-- info: 'PionCompleteness.Paper.flank_class_pole_hypotheses_innermost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.flank_class_pole_hypotheses_innermost
/-- info: 'PionCompleteness.Paper.residueHyperplane_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.residueHyperplane_sub
/-- info: 'PionCompleteness.Paper.nlsmAvoiding_child_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.nlsmAvoiding_child_eq
/-- info: 'PionCompleteness.Paper.child_den_nonvanishing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.child_den_nonvanishing
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses.nested' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses.nested
/-- info: 'PionCompleteness.Paper.avoidingA_restrictsToZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.avoidingA_restrictsToZero
/-- info: 'PionCompleteness.Paper.avoidingB_restrictsToZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.avoidingB_restrictsToZero
/-- info: 'PionCompleteness.Paper.region_diag_not_member' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.region_diag_not_member
/-- info: 'PionCompleteness.Paper.region_member_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.region_member_diag
/-- info: 'PionCompleteness.Paper.region_subP_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.region_subP_odd
/-- info: 'PionCompleteness.Paper.regionAmp_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.regionAmp_eq
/-- info: 'PionCompleteness.Paper.region_den_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.region_den_eval
/-- info: 'PionCompleteness.Paper.stripFactor_hasNoPoleAlong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.stripFactor_hasNoPoleAlong
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.only_extreme_term_survives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.only_extreme_term_survives
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.descent_to_smaller_side' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.descent_to_smaller_side
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.odd_side_nesting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.odd_side_nesting
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.odd_side_nesting_mirror' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.odd_side_nesting_mirror
/-- info: 'PionCompleteness.Paper.exists_eval_mul_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.exists_eval_mul_ne_zero
/-- info: 'PionCompleteness.Paper.ratZeroOn_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.ratZeroOn_add
/-- info: 'PionCompleteness.Paper.ratZeroOn_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.ratZeroOn_sum
/-- info: 'PionCompleteness.Paper.ratZeroOn_mul_of_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.ratZeroOn_mul_of_eq
/-- info: 'PionCompleteness.Paper.ratZeroOn_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.ratZeroOn_mul
/-- info: 'PionCompleteness.Paper.ratZeroOn_rep_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.ratZeroOn_rep_add
/-- info: 'PionCompleteness.Paper.ratZeroOn_rep_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.ratZeroOn_rep_mul
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.HasNoPoleAlong.add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.HasNoPoleAlong.add
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.HasNoPoleAlong.mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.HasNoPoleAlong.mul
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong.add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong.add
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong.mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong.mul
/-- info: 'PionCompleteness.Paper.restrictsToZeroAlong_of_ratZeroOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.restrictsToZeroAlong_of_ratZeroOn
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong.sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong.sum
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong.congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong.congr
/-- info: 'PionCompleteness.Paper.hasNoPoleAlong_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.hasNoPoleAlong_const
/-- info: 'PionCompleteness.Paper.ampAvoiding_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.ampAvoiding_shifted
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.ampAvoiding_coeff_numerator_hom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.ampAvoiding_coeff_numerator_hom
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.stripFactor_sub_const_restrictsToZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.stripFactor_sub_const_restrictsToZero
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.flank_class_members_form_chains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.flank_class_members_form_chains
/-- info: 'PionCompleteness.Paper.rename_oddDen_avoiding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.rename_oddDen_avoiding
/-- info: 'PionCompleteness.Paper.prod_oddDiagonals_avoiding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.prod_oddDiagonals_avoiding
/-- info: 'PionCompleteness.Paper.nlsmAvoiding_child_hom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.nlsmAvoiding_child_hom
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.nlsmAvoiding_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.nlsmAvoiding_step
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.grouping_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.grouping_identity
/-- info: 'PionCompleteness.Paper.nlsmAvoiding_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.nlsmAvoiding_top
/-- info: 'PionCompleteness.Paper.nlsmAvoiding_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.nlsmAvoiding_bot
/-- info: 'PionCompleteness.Paper.nlsmAvoiding_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.nlsmAvoiding_congr
/-- info: 'PionCompleteness.Paper.nlsm_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.nlsm_congr
/-- info: 'PionCompleteness.Paper.relab_eq_subX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.relab_eq_subX
/-- info: 'PionCompleteness.Paper.subX_at_relab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.subX_at_relab
/-- info: 'PionCompleteness.Paper.subX_rot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.subX_rot
/-- info: 'PionCompleteness.Paper.nlsm_subX_rot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.nlsm_subX_rot
/-- info: 'PionCompleteness.Paper.nlsm_omega_relab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.nlsm_omega_relab
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.childAmpA_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.childAmpA_expansion
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.nlsm_collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.nlsm_collapse
/-- info: 'PionCompleteness.Paper.region_den_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.region_den_witness
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.collapse_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.collapse_identity
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.strip_factor_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.strip_factor_value
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.avoidingB_top_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.avoidingB_top_eq
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.avoidingA_bottom_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.avoidingA_bottom_eq
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.simple_pole_along_flank_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.simple_pole_along_flank_class
/-- info: 'PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.strip_pairs_positions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.strip_pairs_positions
/-- info: 'PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.strip_regions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.strip_regions
/-- info: 'PionCompleteness.Paper.planar_adjacent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.planar_adjacent
/-- info: 'PionCompleteness.Paper.vtx_succ_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.vtx_succ_eq_iff
/-- info: 'PionCompleteness.Paper.planarWithSides_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.planarWithSides_eq
/-- info: 'PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.corner_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.corner_identity
/-- info: 'PionCompleteness.Paper.mem_oddSide_iff_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.mem_oddSide_iff_interval
/-- info: 'PionCompleteness.Paper.oddSide_sub_Icc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.oddSide_sub_Icc
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.earLocus_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.earLocus_iff
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.polygon_numerators_vanish_on_ear_locus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.polygon_numerators_vanish_on_ear_locus
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.genericity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.genericity
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.genericity_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.genericity_span
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.genericity_double_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.genericity_double_prime
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.genericity_w_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.genericity_w_independent
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.genericity_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.genericity_closed
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.genericity_w_pairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.genericity_w_pairs
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.markedLocus_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.markedLocus_mono
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.genericity_regions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.genericity_regions
/-- info: 'PionCompleteness.Paper.NLSM.Amplitude.polygon_numerator_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Amplitude.polygon_numerator_value
/-- info: 'PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.gram_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.gram_model
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.child_onLocus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.child_onLocus
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.children_of_odd_chord_locus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.children_of_odd_chord_locus
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.children_of_odd_chord_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.children_of_odd_chord_size
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.children_of_odd_chord_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.children_of_odd_chord_linked
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.children_of_odd_chord_flank_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.children_of_odd_chord_flank_class
/-- info: 'PionCompleteness.Paper.cut_planar_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.cut_planar_child
/-- info: 'PionCompleteness.Paper.cut_planar_child_side' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.cut_planar_child_side
/-- info: 'PionCompleteness.Paper.cut_mesh_inside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.cut_mesh_inside
/-- info: 'PionCompleteness.Paper.cut_mesh_ends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.cut_mesh_ends
/-- info: 'PionCompleteness.Paper.cut_mesh_hat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.cut_mesh_hat
/-- info: 'PionCompleteness.Paper.cut_sum_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.cut_sum_split
/-- info: 'PionCompleteness.Paper.cut_mesh_pull' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.cut_mesh_pull
/-- info: 'PionCompleteness.Paper.parityVal_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.parityVal_eq
/-- info: 'PionCompleteness.Paper.cut_relation1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.cut_relation1
/-- info: 'PionCompleteness.Paper.cut_planar_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.cut_planar_diag
/-- info: 'PionCompleteness.Paper.cut_canonical1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.cut_canonical1
/-- info: 'PionCompleteness.Paper.cutVal_add_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.cutVal_add_smul
/-- info: 'PionCompleteness.Paper.parityVal_add_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.parityVal_add_smul
/-- info: 'PionCompleteness.Paper.cut_lift1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.cut_lift1
/-- info: 'PionCompleteness.Paper.shiftSign_of_parity_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.shiftSign_of_parity_ne
/-- info: 'PionCompleteness.Paper.shiftSign_ne_zero_of_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.shiftSign_ne_zero_of_parity
/-- info: 'PionCompleteness.Paper.cut_parity_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.cut_parity_split
/-- info: 'PionCompleteness.Paper.parityVal_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.parityVal_mesh
/-- info: 'PionCompleteness.Paper.cut_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.cut_correct
/-- info: 'PionCompleteness.Paper.cut_onto1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.cut_onto1
/-- info: 'PionCompleteness.Paper.cut_hyperplane1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.cut_hyperplane1
/-- info: 'PionCompleteness.Paper.relab_mem_diagonals_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.relab_mem_diagonals_iff
/-- info: 'PionCompleteness.Paper.rot_planar_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.rot_planar_lt
/-- info: 'PionCompleteness.Paper.rot_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.rot_planar
/-- info: 'PionCompleteness.Paper.rot_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.rot_mesh
/-- info: 'PionCompleteness.Paper.mesh_relab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.mesh_relab
/-- info: 'PionCompleteness.Paper.rotInv_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.rotInv_mem
/-- info: 'PionCompleteness.Paper.rotInv_rotInv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.rotInv_rotInv
/-- info: 'PionCompleteness.Paper.relab_rotInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.relab_rotInv
/-- info: 'PionCompleteness.Paper.rotSet_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.rotSet_sub
/-- info: 'PionCompleteness.Paper.onLocus_rot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.onLocus_rot
/-- info: 'PionCompleteness.Paper.childSet_rot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.childSet_rot
/-- info: 'PionCompleteness.Paper.relab_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.relab_parity
/-- info: 'PionCompleteness.Paper.shiftSign_relab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.shiftSign_relab
/-- info: 'PionCompleteness.Paper.hasCutAbsorber_rot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.hasCutAbsorber_rot
/-- info: 'PionCompleteness.Paper.cutWeight_rot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.cutWeight_rot
/-- info: 'PionCompleteness.Paper.cutVal_rot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.cutVal_rot
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.cut_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.cut_relation
/-- info: 'PionCompleteness.Paper.rot_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.rot_lift
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.cut_image_onto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.cut_image_onto
/-- info: 'PionCompleteness.Paper.rot_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.rot_point
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.cut_image_hyperplane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.cut_image_hyperplane
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.cut_absorber_of_inner_pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.cut_absorber_of_inner_pair
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.cut_absorber_of_residue_chord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.cut_absorber_of_residue_chord
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.child_zeros_away_from_new_leg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.child_zeros_away_from_new_leg
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.child_zeros_at_new_leg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.child_zeros_at_new_leg
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.unlinked_side_child_vanishes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.unlinked_side_child_vanishes
/-- info: 'PionCompleteness.Paper.isRunOf_through' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.isRunOf_through
/-- info: 'PionCompleteness.Paper.isRunOf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.isRunOf_eq
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.inner_oo_pair_in_one_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.inner_oo_pair_in_one_run
/-- info: 'PionCompleteness.Paper.spread_of_isSpread' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.spread_of_isSpread
/-- info: 'PionCompleteness.Paper.legs_of_mem_admSeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.legs_of_mem_admSeps
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.isSpread_iff_spread' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.isSpread_iff_spread
/-- info: 'PionCompleteness.Paper.isRunOf_lin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.isRunOf_lin
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.occupied_run_chords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.occupied_run_chords
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.separated_pairs_of_sub_arc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.separated_pairs_of_sub_arc
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.innermost_chord_has_no_spread_separator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.innermost_chord_has_no_spread_separator
/-- info: 'PionCompleteness.Paper.sameRun_between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.sameRun_between
/-- info: 'PionCompleteness.Paper.mem_of_adj_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.mem_of_adj_run
/-- info: 'PionCompleteness.Paper.second_leg_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.second_leg_pos
/-- info: 'PionCompleteness.Paper.run_chord_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.run_chord_frame
/-- info: 'PionCompleteness.Paper.shortening_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.shortening_core
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.shortening_spread_separator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.shortening_spread_separator
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.shortening_spread_separator_mirror' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.shortening_spread_separator_mirror
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.unlinked_side_has_smaller_linked_chord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.unlinked_side_has_smaller_linked_chord
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.unlinked_side_has_smaller_linked_chord_mirror' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  PionCompleteness.Paper.Combinatorics.Polygons.unlinked_side_has_smaller_linked_chord_mirror
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.no_odd_singleton_separator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.no_odd_singleton_separator
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.thin_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.thin_runs
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.spread_separator_passes_to_innermost_chord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  PionCompleteness.Paper.Combinatorics.Polygons.spread_separator_passes_to_innermost_chord
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.every_coordinate_zero_contains_a_family_member' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.every_coordinate_zero_contains_a_family_member
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.minimal_coordinate_zeros_are_the_list' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.minimal_coordinate_zeros_are_the_list
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.isRegularSet_iff_nondeg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.isRegularSet_iff_nondeg
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.isCoordinateZero_iff_ampZeroOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.isCoordinateZero_iff_ampZeroOn
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.isCoordinateZero_iff_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.isCoordinateZero_iff_pointwise
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.isRegularCoordinateZero_iff_isNDZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.isRegularCoordinateZero_iff_isNDZero
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.isMinimalCoordinateZero_iff_isMinimalZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.isMinimalCoordinateZero_iff_isMinimalZero
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.Families.isListMember_iff_mem_gFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.Families.isListMember_iff_mem_gFamily
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.isCandidateSet_iff_inFpi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.isCandidateSet_iff_inFpi
/-- info: 'PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.chord_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.chord_formula
/-- info: 'PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.proportional_odd_chords_share_missing_flank_set' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.proportional_odd_chords_share_missing_flank_set
/-- info: 'PionCompleteness.Paper.Combinatorics.SetSystems.separated_pair_family_is_antichain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.SetSystems.separated_pair_family_is_antichain
/-- info: 'PionCompleteness.Paper.NLSM.FeynmanRules.quartic_rules_give_nlsm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.FeynmanRules.quartic_rules_give_nlsm
-- Paper, continued: short arguments of the remarks on the definitions and the main theorem, and the
-- pole-free locus at six legs.
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.isRegularSet_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.isRegularSet_mono
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.isCoordinateZero_of_subset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.isCoordinateZero_of_subset
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.exists_minimal_coordinate_zero_subset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.exists_minimal_coordinate_zero_subset
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.isCoordinateZero_iff_contains_minimal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.isCoordinateZero_iff_contains_minimal
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.nextCut_of_above' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.nextCut_of_above
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.nextCut_of_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.nextCut_of_top
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.nextCut_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.nextCut_pair
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.one_parity_iff_gaps_odd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.one_parity_iff_gaps_odd
/-- info: 'PionCompleteness.Paper.Combinatorics.Polygons.opposite_parity_gaps_even' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Combinatorics.Polygons.opposite_parity_gaps_even
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.Families.subset_pair_of_causal_diamond_subset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.Families.subset_pair_of_causal_diamond_subset
/-- info: 'PionCompleteness.Paper.NLSM.Zeros.Families.no_causal_diamond_in_separated_pairs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.NLSM.Zeros.Families.no_causal_diamond_in_separated_pairs
/-- info: 'PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.separated_pairs_block_tile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.separated_pairs_block_tile
/-- info: 'PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.separated_pairs_eq_blocks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.separated_pairs_eq_blocks
/-- info: 'PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.separated_pairs_of_two_legs_eq_diamond' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.separated_pairs_of_two_legs_eq_diamond
/-- info: 'PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.whole_parity_members' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.whole_parity_members
/-- info: 'PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.parity_form_vanishes_on_member_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.parity_form_vanishes_on_member_iff
/-- info: 'PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.parity_form_vanishes_iff_contains_whole_parity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.parity_form_vanishes_iff_contains_whole_parity
-- PaperTests: every test of Paper (non-vacuity, definitions on given sets, examples, hypotheses).
/-- info: 'PionCompleteness.PaperTests.sepPairs_nonempty_of_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.sepPairs_nonempty_of_admissible
/-- info: 'PionCompleteness.PaperTests.sepPairs_nonempty_of_mixedAnchor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.sepPairs_nonempty_of_mixedAnchor
/-- info: 'PionCompleteness.PaperTests.sepPairs_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.sepPairs_nonempty
/-- info: 'PionCompleteness.PaperTests.empty_notMem_gFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.empty_notMem_gFamily
/-- info: 'PionCompleteness.PaperTests.empty_mem_gFamily_seven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.empty_mem_gFamily_seven
/-- info: 'PionCompleteness.PaperTests.empty_mem_gFamily_of_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.empty_mem_gFamily_of_odd
/-- info: 'PionCompleteness.PaperTests.containsGMember_of_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.containsGMember_of_odd
/-- info: 'PionCompleteness.PaperTests.nonDegPt_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.nonDegPt_empty
/-- info: 'PionCompleteness.PaperTests.not_ampZeroOn_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.not_ampZeroOn_empty
/-- info: 'PionCompleteness.PaperTests.exists_NLSM_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.exists_NLSM_ne_zero
/-- info: 'PionCompleteness.PaperTests.sepPairs_one_three_mem_gFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.sepPairs_one_three_mem_gFamily
/-- info: 'PionCompleteness.PaperTests.isNDZero_sepPairs_one_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.isNDZero_sepPairs_one_three
/-- info: 'PionCompleteness.PaperTests.not_isListMember_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.not_isListMember_empty
/-- info: 'PionCompleteness.PaperTests.not_isCoordinateZero_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.not_isCoordinateZero_empty
/-- info: 'PionCompleteness.PaperTests.isListMember_sepPairs_one_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.isListMember_sepPairs_one_three
/-- info: 'PionCompleteness.PaperTests.isRegularCoordinateZero_sepPairs_one_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.isRegularCoordinateZero_sepPairs_one_three
/-- info: 'PionCompleteness.PaperTests.isMinimalCoordinateZero_six_one_three_five' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.isMinimalCoordinateZero_six_one_three_five
/-- info: 'PionCompleteness.PaperTests.isRegularCoordinateZero_six_one_three_five' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.isRegularCoordinateZero_six_one_three_five
/-- info: 'PionCompleteness.PaperTests.isRegularSet_six_one_three_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.isRegularSet_six_one_three_five
/-- info: 'PionCompleteness.PaperTests.isCoordinateZero_six_one_three_five' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.isCoordinateZero_six_one_three_five
/-- info: 'PionCompleteness.PaperTests.not_isRegularSet_six_all_pairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.not_isRegularSet_six_all_pairs
/-- info: 'PionCompleteness.PaperTests.not_isRegularCoordinateZero_six_all_pairs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.not_isRegularCoordinateZero_six_all_pairs
/-- info: 'PionCompleteness.PaperTests.not_isCoordinateZero_six_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.not_isCoordinateZero_six_empty
/-- info: 'PionCompleteness.PaperTests.not_isMinimalCoordinateZero_six_one_three_five_insert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.not_isMinimalCoordinateZero_six_one_three_five_insert
/-- info: 'PionCompleteness.PaperTests.isCausalDiamond_six_one_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.isCausalDiamond_six_one_four
/-- info: 'PionCompleteness.PaperTests.not_isCausalDiamond_six_one_three_five' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.not_isCausalDiamond_six_one_three_five
/-- info: 'PionCompleteness.PaperTests.list_eight_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.list_eight_card
/-- info: 'PionCompleteness.PaperTests.shiftSign_values' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.shiftSign_values
/-- info: 'PionCompleteness.PaperTests.isTriangulation_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.isTriangulation_five
/-- info: 'PionCompleteness.PaperTests.not_isTriangulation_five_not_maximal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.not_isTriangulation_five_not_maximal
/-- info: 'PionCompleteness.PaperTests.not_isTriangulation_five_crossing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.not_isTriangulation_five_crossing
/-- info: 'PionCompleteness.PaperTests.delta_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.delta_coeff
/-- info: 'PionCompleteness.PaperTests.shifted_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.shifted_coeff
/-- info: 'PionCompleteness.PaperTests.faces_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.faces_empty
/-- info: 'PionCompleteness.PaperTests.cayleySum_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.cayleySum_four
/-- info: 'PionCompleteness.PaperTests.faceVertex_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.faceVertex_four
/-- info: 'PionCompleteness.PaperTests.figure_nine_configuration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.figure_nine_configuration
/-- info: 'PionCompleteness.PaperTests.example_eight_c_spread' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.example_eight_c_spread
/-- info: 'PionCompleteness.PaperTests.example_shortening_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.example_shortening_nonvacuous
/-- info: 'PionCompleteness.PaperTests.ratZeroOn_poly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.ratZeroOn_poly
/-- info: 'PionCompleteness.PaperTests.not_hasNoPoleAlong_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.not_hasNoPoleAlong_inv
/-- info: 'PionCompleteness.PaperTests.not_restrictsToZeroAlong_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.not_restrictsToZeroAlong_one
/-- info: 'PionCompleteness.PaperTests.onLocus_line_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.onLocus_line_closed
/-- info: 'PionCompleteness.PaperTests.restrictsToZeroAlong_numerator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.restrictsToZeroAlong_numerator
/-- info: 'PionCompleteness.PaperTests.hasNoPoleAlong_can_fail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.hasNoPoleAlong_can_fail
/-- info: 'PionCompleteness.PaperTests.example_four_six_residue_regime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.example_four_six_residue_regime
/-- info: 'PionCompleteness.PaperTests.example_no_residue_chord_with_both_sides_linked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.example_no_residue_chord_with_both_sides_linked
/-- info: 'PionCompleteness.PaperTests.residueHyperplane_line_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.residueHyperplane_line_closed
/-- info: 'PionCompleteness.PaperTests.example_four_six_extreme_terms_nonvanishing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.example_four_six_extreme_terms_nonvanishing
/-- info: 'PionCompleteness.PaperTests.stripFactor_eight_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.stripFactor_eight_self
/-- info: 'PionCompleteness.PaperTests.regionAmp_eight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.regionAmp_eight
/-- info: 'PionCompleteness.PaperTests.stripFactor_eight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.stripFactor_eight
/-- info: 'PionCompleteness.PaperTests.marked_locus_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.marked_locus_nonvacuous
/-- info: 'PionCompleteness.PaperTests.isSameParitySet_six_one_three_five' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.isSameParitySet_six_one_three_five
/-- info: 'PionCompleteness.PaperTests.polygon_value_hypotheses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.polygon_value_hypotheses
/-- info: 'PionCompleteness.PaperTests.numerator_hom_at_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.numerator_hom_at_one
/-- info: 'PionCompleteness.PaperTests.example_cut_image_hyperplane_candidates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.example_cut_image_hyperplane_candidates
/-- info: 'PionCompleteness.PaperTests.example_cut_image_hyperplane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.example_cut_image_hyperplane
/-- info: 'PionCompleteness.PaperTests.example_pole_free_locus_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.example_pole_free_locus_six
/-- info: 'PionCompleteness.PaperTests.example_pole_free_locus_six_rational' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PionCompleteness.PaperTests.example_pole_free_locus_six_rational
