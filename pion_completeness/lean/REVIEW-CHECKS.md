# Review tests outside `PaperTests`

Every test of the module `Paper` is in `PionCompleteness/PaperTests.lean`. This file lists the tests that stay
elsewhere: in the library's modules (`C0`–`C10` and the base modules), which stay as they were accepted, and in
`Conventions`, the outside anchors. Each row names the statement of the paper that its test checks, as the PDF prints
it: kind, number and title. A row with an empty first cell checks the statement of the nearest named row above it. A
test here is a theorem about given objects, with no variable, that no general proof uses: a computed table that a proof
uses is a step of that proof, and a test stated for every size is not listed. It states that a definition holds or fails
on an example (or for some value), that an object is in it, its value there or a quantity computed from it, or that the
hypotheses of a theorem hold together. Each states what a definition gives on one case; it says nothing about other
cases. Lean's check of the main theorem uses none of them.

Generated on 2026-11-16 from the Lean code (Lean v4.35.0) by a tool that is not released.

| statement | test | module | states |
|---|---|---|---|
| Definition 2.1 (planar variables and mesh variables) | `PionZeros.negctl_minus_tile` | `Base.PionZeros` | a value of `TreeRectangleZero.mesh` |
|  | `PionZeros.rev_negctl_minus_tile_T135` | `Base.PionZeros` | a value of `TreeRectangleZero.mesh` |
|  | `TreeRectangleZero.negcontrol_minus_tile` | `Base.TreeRectangleZero` | a value of `TreeRectangleZero.mesh` |
| Definition 2.6 (the amplitudes) | `PionNLSM.NLSM_ne_zero_small` | `Base.PionNLSM` | a value of `PionNLSM.NLSM` |
|  | `PionNLSM.negctl_sign` | `Base.PionNLSM` | a quantity computed from `PionNLSM.NLSM` |
|  | `PionNLSM.negctl_order` | `Base.PionNLSM` | a quantity computed from `PionNLSM.shiftCoeff` |
|  | `PionNLSM.negctl_poles_six` | `Base.PionNLSM` | a quantity computed from `PionNLSM.NLSM` |
|  | `PionNLSM.negctl_pi_two_six` | `Base.PionNLSM` | a quantity computed from `PionNLSM.NLSM` |
|  | `TreeRectangleZero.negcontrol_minus_tile` | `Base.TreeRectangleZero` | a value of `TreeRectangleZero.amp` |
|  | `TreeRectangleZero.rev_card_triangulations_six` | `Base.TreeRectangleZero` | a quantity computed from `TreeRectangleZero.triangulations` |
| Definition 2.11 (coordinate loci, regular sets and zeros) | `ChainSlice.X6p_onLocus` | `Base.ChainSlice` | `ChainSlice.OnLocus` holds |
|  | `ChainSlice.X6z_onLocus` | `Base.ChainSlice` | `ChainSlice.OnLocus` holds |
|  | `ChainSlice.sanity_six_zero` | `Base.ChainSlice` | `ChainSlice.OnLocus` holds for some value |
|  | `ChainSlice.X6p_onLocus_S6s` | `Base.ChainSlice` | `ChainSlice.OnLocus` holds |
|  | `ChainSlice.negctl_no_E` | `Base.ChainSlice` | `ChainSlice.Nondeg` fails |
|  | `Pi.zero_ST135` | `C10` | `Pi.AmpZeroOn` holds |
|  | `Pi.min_ST135_24` | `C10` | `Pi.AmpZeroOn` fails |
|  | `Pi.min_ST135_26` | `C10` | `Pi.AmpZeroOn` fails |
|  | `Pi.min_ST135_46` | `C10` | `Pi.AmpZeroOn` fails |
|  | `Pi.zero_ST13` | `C10` | `Pi.AmpZeroOn` holds |
|  | `Pi.min_ST13_24` | `C10` | `Pi.AmpZeroOn` fails |
|  | `Pi.min_ST13_25` | `C10` | `Pi.AmpZeroOn` fails |
|  | `Pi.min_ST13_26` | `C10` | `Pi.AmpZeroOn` fails |
|  | `Pi.zero_D14` | `C10` | `Pi.AmpZeroOn` holds |
|  | `Pi.min_D14_25` | `C10` | `Pi.AmpZeroOn` fails |
|  | `Pi.min_D14_26` | `C10` | `Pi.AmpZeroOn` fails |
|  | `Pi.min_D14_35` | `C10` | `Pi.AmpZeroOn` fails |
|  | `Pi.min_D14_36` | `C10` | `Pi.AmpZeroOn` fails |
|  | `Pi.notZero_mixed124` | `C10` | `Pi.AmpZeroOn` fails |
|  | `Pi.control_mixed124` | `C10` | `Pi.AmpZeroOn` fails |
|  | `Pi.degenerate_full` | `C10` | `ChainSlice.Nondeg` fails; `Pi.AmpZeroOn` holds |
|  | `Pi.clause1_hyp_inhabited` | `C10` | `Pi.IsNDZero` holds |
|  | `Pi.control_diamonds_needed` | `C10` | `Pi.IsNDZero` holds |
|  | `Pi.control_ndZero_not_minimal` | `C10` | `Pi.IsNDZero` holds |
| Definition 2.14 (minimal zero) | `Pi.clause2_six_instances` | `C10` | `Pi.IsMinimalZero` holds |
|  | `Pi.control_not_minimal` | `C10` | `Pi.IsMinimalZero` fails |
|  | `Pi.control_ndZero_not_minimal` | `C10` | `Pi.IsMinimalZero` fails |
| Definition 2.17 (separated pairs) | `Pi.SG6_ST135` | `C10` | a value of `Pi.sepPairs` |
|  | `Pi.SG6_ST135_24` | `C10` | a quantity computed from `Pi.sepPairs` |
|  | `Pi.SG6_ST135_26` | `C10` | a quantity computed from `Pi.sepPairs` |
|  | `Pi.SG6_ST135_46` | `C10` | a quantity computed from `Pi.sepPairs` |
|  | `Pi.SG6_ST13` | `C10` | a value of `Pi.sepPairs` |
|  | `Pi.SG6_ST13_24` | `C10` | a quantity computed from `Pi.sepPairs` |
|  | `Pi.SG6_ST13_25` | `C10` | a quantity computed from `Pi.sepPairs` |
|  | `Pi.SG6_ST13_26` | `C10` | a quantity computed from `Pi.sepPairs` |
|  | `Pi.SG6_D14` | `C10` | a value of `Pi.sepPairs` |
|  | `Pi.SG6_D14_25` | `C10` | a quantity computed from `Pi.sepPairs` |
|  | `Pi.SG6_D14_26` | `C10` | a quantity computed from `Pi.sepPairs` |
|  | `Pi.SG6_D14_35` | `C10` | a quantity computed from `Pi.sepPairs` |
|  | `Pi.SG6_D14_36` | `C10` | a quantity computed from `Pi.sepPairs` |
|  | `Pi.control_T1` | `C10` | a value of `Pi.sepPairs` |
|  | `Pi.SG6_mixed124` | `C10` | a value of `Pi.sepPairs` |
|  | `Pi.SG8_ST135` | `C10` | a value of `Pi.sepPairs` |
|  | `Pi.SG8_D14` | `C10` | a value of `Pi.sepPairs` |
|  | `Pi.sepPairs8_136` | `C10` | a value of `Pi.sepPairs` |
|  | `Pi.rev_wrap18` | `C10` | a value of `Pi.sepPairs` |
| Definition 2.20 (causal diamonds) | `ChainSlice.diamond_inter_Free_seven` | `Base.ChainSlice` | a quantity computed from `ChainSlice.diamond` |
|  | `TreeRectangleZero.X5w_onRect` | `Base.TreeRectangleZero` | `TreeRectangleZero.OnRect` holds |
| Definition 2.21 (T-separated sets and the list) | `PionZeros.negctl_wrong_polarity` | `Base.PionZeros` | `PionZeros.OnZT` holds for some value |
|  | `PionZeros.negctl_mixed_parity` | `Base.PionZeros` | `PionZeros.OnZT` holds for some value |
|  | `PionZeros.rev_negctl_singleton_T` | `Base.PionZeros` | `PionZeros.OnZT` holds for some value |
|  | `Pi.mem_ST135` | `C10` | in `Pi.gFamily` |
|  | `Pi.mem_ST13` | `C10` | in `Pi.gFamily` |
|  | `Pi.mem_D14` | `C10` | in `Pi.gFamily` |
|  | `Pi.mem8_ST135` | `C10` | in `Pi.gFamily` |
|  | `Pi.mem8_D14` | `C10` | in `Pi.gFamily` |
|  | `Pi.rev_card6` | `C10` | a quantity computed from `Pi.gFamily` |
|  | `Pi.rev_card8` | `C10` | a quantity computed from `Pi.gFamily` |
| Definition 4.4 (candidate sets) | `Pi.lemma14_6_hyp_inhabited` | `C10` | `Pi.InFpi` holds |
|  | `Pi.fpi8_mixed136` | `C10` | `Pi.InFpi` holds |
| Definition 4.7 (sides, flank sets and the flank overlap) | `Pi.rev_head` | `C10` | a value of `Pi.evenSide`; a value of `Pi.oddSide` |
|  | `Pi.sides8_27` | `C10` | a value of `Pi.evenSide`; a value of `Pi.oddSide` |
| Theorem 4.10 (the chord formula) | `ChainSlice.X6p_onLocus` | `Base.ChainSlice` | hypotheses hold |
| Definition 4.17 (on-shell and residue chords; the same-parity sublocus) | `Pi.lemma14_6_hyp_inhabited` | `C10` | in `Pi.poleChords` |
|  | `Pi.ctl8_route` | `C10` | a value of `Pi.poleChords` |
|  | `Pi.ctl8_neg` | `C10` | in `Pi.poleChords` |
|  | `Pi.ctl10_evenTop_fails` | `C10` | in `Pi.poleChords` |
| Definition 6.1 (separators, linked sides and flank classes) | `Pi.sides8_27` | `C10` | a value of `Pi.cycArc` |
|  | `Pi.ctl8_route` | `C10` | `Pi.IsInnermostChord` holds; `Pi.NoFreeSep` holds; a value of `Pi.goodTail`; a value of `Pi.hitClass` |
|  | `Pi.ctl8_neg` | `C10` | `Pi.NoFreeSep` fails |
|  | `Pi.ctl10_evenTop_fails` | `C10` | `Pi.IsInnermostChord` fails |
| Definition 6.6 (the children of an odd chord) | `Pi.ctl8_children` | `C10` | a value of `Pi.childSetA` |
|  | `Pi.ctl8_neg` | `C10` | a value of `Pi.childSetA` |
| Definition 7.3 (three cuts of a circle) | `Pi.threeSep_setting_ten` | `C10` | `Pi.ThreeSepSetting` holds |
|  | `Pi.threeSep_setting_reject` | `C10` | `Pi.ThreeSepSetting` fails |
|  | `Pi.rev_tri12` | `C10` | `Pi.ThreeSepSetting` holds |
| Theorem 7.4 (the three-cut theorem) | `Pi.threeSep_witness_ten` | `C10` | `Pi.ConsecWit` holds |
|  | `Pi.rev_tri12_w` | `C10` | `Pi.ConsecWit` holds |
| Definition C.1 (quartic diagrams) | `PionNLSM.negctl_sign` | `Base.PionNLSM` | a value of `PionZeros.Qpi` |
|  | `PionNLSM.negctl_order` | `Base.PionNLSM` | a value of `PionZeros.Qpi` |
|  | `PionNLSM.negctl_poles_six` | `Base.PionNLSM` | a value of `PionZeros.Qpi` |
|  | `PionNLSM.negctl_pi_two_six` | `Base.PionNLSM` | a value of `PionZeros.Qpi` |
|  | `PionNLSM.negctl_polarity_diagram_six` | `Base.PionNLSM` | a value of `PionZeros.Qpi`; a value of `PionZeros.diagram` |
|  | `PionZeros.p3b_diag_plus_minus_needs_pi_lt_two` | `Base.PionZeros` | in `PionZeros.quadrangulations` |
|  | `PionZeros.card_quadrangulations_small` | `Base.PionZeros` | a quantity computed from `PionZeros.quadrangulations` |
|  | `PionZeros.negctl_minus_tile` | `Base.PionZeros` | a value of `PionZeros.Qpi` |
|  | `PionZeros.negctl_wrong_polarity` | `Base.PionZeros` | a value of `PionZeros.Qpi`; a value of `PionZeros.diagram` |
|  | `PionZeros.negctl_mixed_parity` | `Base.PionZeros` | a value of `PionZeros.Qpi`; in `PionZeros.quadrangulations` |
|  | `PionZeros.rev_negctl_singleton_T` | `Base.PionZeros` | a value of `PionZeros.Qpi` |
|  | `PionZeros.rev_negctl_minus_tile_T135` | `Base.PionZeros` | a value of `PionZeros.Qpi` |
| Lemma C.3 (a good quad exists) | `PionZeros.negctl_mixed_parity` | `Base.PionZeros` | hypotheses hold |
| Lemma C.4 (the good vertex factor vanishes) | `PionZeros.p3b_diag_plus_minus_needs_pi_lt_two` | `Base.PionZeros` | hypotheses hold |
| Definition D.7 (the Feynman sum of the Cayley parametrization) | `Pi.negctl_knt_vertex_constant` | `Conventions` | a value of `Pi.kntFeynman` |
|  | `Pi.negctl_knt_vertex_sign` | `Conventions` | a value of `Pi.kntFeynman` |
|  | `Pi.negctl_knt_propagator_sign` | `Conventions` | a value of `Pi.kntFeynman` |
| Lemma E.3 (containment) | `Pi.ctl8_route` | `C10` | hypotheses hold |
| Lemma E.6 (the cut image) | `Pi.ctl10_evenTop_fails` | `C10` | hypotheses hold |
| Definition F.10 (chords over a marked leg, the marked locus, numerators) | `Pi.pkG_thmI_six` | `C5` | a value of `PionNLSM.NP` |
