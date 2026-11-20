/-
Copyright (c) 2026 Henru Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henru Wang
-/
module

public import PionCompleteness.C10

/-!
# The paper's statements

Statements in the exact form in which the paper of Theorem Π states them, most of them short
consequences of the general results of `C0`–`C10` and the library files. The general results stay
general (they serve proving and reuse); a statement here has the paper's hypotheses and
conclusion, so a reader can compare it with the paper side by side, with no argued step between
the two.

The main theorem is stated in the paper's terms, with definitions shaped like the paper's: regular
sets (`IsRegularSet`), zeros (`IsCoordinateZero`: the restriction of `NLSM_N` to `L_S` is the zero
rational function, `RatZeroOn`), regular coordinate zeros and minimal ones
(`IsRegularCoordinateZero`, `IsMinimalCoordinateZero`), causal diamonds and the list
(`IsCausalDiamond`, `IsListMember`); and candidate sets (`IsCandidateSet`), the sets clause 1 is
proved for. Each but `IsCausalDiamond` is proved equal, under the statements' hypotheses (even `N`,
a regular set of pairs where a zero is concerned), to the library's form that the statements of
`C10` and the general results use: the pointwise `Nondeg`, `AmpZeroOn` (for `(−1)^{N/2−1} NLSM_N`),
`IsNDZero`, `IsMinimalZero`, `gFamily`, the paper's second form of the list, which covers the causal
diamonds, and `InFpi` (`isRegularSet_iff_nondeg`, `isCoordinateZero_iff_ampZeroOn`,
`isRegularCoordinateZero_iff_isNDZero`, `isMinimalCoordinateZero_iff_isMinimalZero`,
`isListMember_iff_mem_gFamily`, `isCandidateSet_iff_inFpi`). So the three statements of the main
theorem here are proved from those of `C10`, and every statement of this module is stated with these
definitions; only the equalities name the library's forms.

Where the paper speaks of a residue, `Res_{X_C=0} F := (X_C F)|_{X_C=0}`, a statement
`Res_C F = G` is `RatZeroOn {x | x C = 0} (X_C · F − G)`; the bridge
`ratZeroOn_hyperplane_iff_zeroAt` reduces it to the library's numerator form (`zeroAt`), so the
rational statements here are proved, not argued. "Homogeneous of degree 1" is stated over every
field at every point where no odd chord vanishes (at the generic point of a function field this is
the identity of rational functions).

Definitions state notions of the paper that the library had only in another form: the faces of a
dissection (`IsFace`, `faces`: maximal sets of vertices no two of which a chord separates; the
library indexes faces by root sides, and `isFace_iff`, `faces_eq_image` prove the two agree), the
legs of the sides of a face that start at an odd vertex (`sideStart`, `oddStartLegs`: `U_f`), its
chord sides (`chordSides`), the vertex of a face (`faceVertex`, equal to the library's `pkGV` by
`pkG_V_eq_faceVertex`), the Cayley sum built from it, over any field (`cayleySum`), `meshMap`,
the mesh map `𝐜 : X ↦ (c_t(X))_t` as a linear map (for its rank), and the three-cut proof's
case (EP) (`CaseEP`, `HasWideGap`) and zone set `G′` (`zoneSet`, with `PX`, `PY`, `RemovedTau`,
`RemovedSigma`; equal to the library's `pkTZoneSet` for legs `≥ 1`, as in the setting, by
`zoneSet_eq_pkT_zoneSet`), and the runs of an even separator (`IsRunOf`, `IsOccupiedRun`,
`IsSpread`, equal to the library's `Spread` for a set of legs by `isSpread_iff_spread`, and the
piece `R_τ`, `reachPiece`). Two lemmas relate the two descriptions of the `T`-separated locus
(`onLocus_sepPairs_of_onZT`, `onZT_iff_onLocus_sepPairs`).

The class residue is stated in the paper's language of rational functions restricted to `L_S`:
"the restriction of `f` to `V` has no pole along `H`" is `HasNoPoleAlong V H f` (on `V`, `f = P / D`
with `D` not identically zero on `H`) and "`f|_H = 0`" is `RestrictsToZeroAlong V H f` (the same
with `P` vanishing on `H`, for any such representation by
`PaperTests.restrictsToZeroAlong_numerator`); `PaperTests.hasNoPoleAlong_can_fail` shows that the
first is a condition (`1 / x` fails it). The amplitude avoiding a set of chords `K` (`ampAvoiding`,
`nlsmAvoiding`: `A^{¬K}`, `N^{¬K}`) is defined directly and related to the library's numerator by
`nlsmAvoiding_numerator_hom`; the hypotheses of the residue theorem are the structure
`FlankClassPoleHypotheses` (with `residueHyperplane` for `H`, `stripHalfLength` for `d`, `childAmpB`
and `childAmpA` for `a_t`, `b_b`), the parts `a_Q`, `b_Q` are `avoidingB`, `avoidingA`, and the
strip factor `φ(Q, Q′)` is `stripFactor` (with `regionAmp` for `N_{Ω(Q,Q′)}`). An example of the
paper (`N = 8`) satisfies the hypotheses with a class of two members
(`PaperTests.example_four_six_residue_regime`), and there the extreme terms `b_b`, `a_t` do not
vanish on `H` (`PaperTests.example_four_six_extreme_terms_nonvanishing`). Identities on `L_S` are
stated as `RatZeroOn` of the difference, and "`f|_H = g|_H`" as `RestrictsToZeroAlong` of `f − g`;
both predicates are closed under sums and products (`ratZeroOn_add`, `HasNoPoleAlong.add`,
`RestrictsToZeroAlong.mul`, …). A polygon with side values is `planarWithSides`, `meshWithSides`
(the corner identity), and the ear lemma's locus is `earLocus` (equal to the library's `pkRBZ5`,
`earLocus_iff`).

## Main results

* the analytic facts: `analytic_facts_delta_order`, `analytic_facts_factorisation`,
  `analytic_facts_symmetry` (rotations), with the bridge `ratZeroOn_hyperplane_iff_zeroAt`;
* the `T`-separated zeros: `t_separated_zero`, `t_separated_zero_pointwise`, with
  `t_separated_locus_nondegenerate`, `quadrangulation_has_good_quad`,
  `good_vertex_factor_vanishes` and `diagrams_vanish_on_t_separated_locus`;
* the diagram sum and the NLSM side: `quartic_diagram_sum_structure`, `single_leg_locus`,
  `delta_order_factorisation_single_leg_vanishing`, `pole_free_on_odd_chords_is_polynomial`;
* candidate sets and the mesh: `candidate_sets_are_transversals`, `block_sums`,
  `parity_form_nonvanishing`;
* the linear algebra of the mesh: `momentum_conservation_relation` (kernel `ℚ v₀`, the relations,
  the rank and the image) and `locus_coordinates` (coordinates on a locus; a linear form vanishes
  on `L_S` iff it is in `span{c_t : t ∈ S}`);
* odd chords and flank sets: `odd_chord_sides`, `flank_sets_of_odd_chord`,
  `on_shell_iff_flank_sets_share_no_missing_pair`, and `odd_chord_vanishing_on_same_parity_sublocus`
  (`X_P` on the same-parity sublocus);
* `form_identities`: the identities of the forms, with
  `mesh_independent_of_omits_same_parity` and `rows_one_two_span_meet`;
* `three_row_zeros`: three skinny rectangles kill a linear form;
* `dissections`: the claims of the definition of dissections (face count, even, alternating);
* `cayley_form`: `NLSM_N = −Cay_N` as rational functions;
* `face_identity`, `dissection_face_count`, `on_shell_dissection_has_vanishing_face` and
  `nonvanishing_without_residue_chords`: the face identity, the order count, a vanishing
  face, and the non-vanishing of `NLSM_N` on `L_S` when `𝒫₁ = ∅`;
* the three-cut theorem: `three_separators_single_parity_arc_witness` and its corollary, three
  cuts, one parity (`three_separators_contain_t_separated_set`), and the lemmas of its proof:
  `parity_block_witness_in_cut`, `separator_meets_every_gap_interval` (the gap lemma's part (a);
  parts (b)–(d): `removed_leg_of_tau_iff`, `removed_leg_of_sigma_iff`, `side_gap_gamma_sigma`,
  `side_gap_gamma_tau`, `side_gap_left_sigma`, `side_gap_right_tau`, `zoneSet_keeps_middle_legs`,
  `zoneSet_keeps_common_legs`), `reach_witness_is_odd_interval`, `reach_witness_has_two_legs`,
  `reach_witness_pairs_in_cut`, with `PaperTests.figure_nine_configuration` (the zone-case
  hypotheses can hold together);
* `innermost_chord_exists`, `flank_class_top_and_bottom`, `separators_avoid_linked_side`,
  `residue_chord_joins_innermost_flank_class`, `innermost_class_has_linked_member`: steps of
  the residue argument, with `both_sides_linked_alone_in_flank_class` (a residue chord with both
  sides linked is alone in its class);
* the translation to combinatorics: `inner_oo_pair_in_one_run` (runs),
  `occupied_run_chords` (run chords), `separated_pairs_of_sub_arc` (sub-arcs),
  `shortening_spread_separator` and its mirror (shortening),
  `innermost_chord_has_no_spread_separator` (no spread),
  `unlinked_side_has_smaller_linked_chord` and its mirror (the side lemma),
  `no_odd_singleton_separator` (no odd singleton), `thin_runs` and
  `spread_separator_passes_to_innermost_chord` (the lift), with the instances
  `PaperTests.example_eight_c_spread` and `PaperTests.example_shortening_nonvacuous` (the hypotheses
  of the shortening lemma hold together);
* the main theorem in the paper's terms: `every_coordinate_zero_contains_a_family_member` (clause
1), `family_members_are_minimal_zeros` (clause 2) and `minimal_coordinate_zeros_are_the_list` (the
"Hence"), with the definitions above, the zeros read pointwise (`isCoordinateZero_iff_pointwise`)
and the list at eight legs (`PaperTests.list_eight_card`);
* statements restated here so that every claim has a pinned declaration in this module:
  `chord_formula`, `proportional_odd_chords_share_missing_flank_set`,
  `separated_pair_family_is_antichain` and `quartic_rules_give_nlsm`;
* short arguments of the remarks: zeros upward (`isCoordinateZero_iff_contains_minimal`), the gaps
  of a set of legs (`nextCut`, `one_parity_iff_gaps_odd`, `opposite_parity_gaps_even`,
  `subset_pair_of_causal_diamond_subset`), `S_G` as blocks of tiles (`separated_pairs_eq_blocks`,
  `separated_pairs_of_two_legs_eq_diamond`), where the parity form vanishes
  (`whole_parity_members`, `parity_form_vanishes_iff_contains_whole_parity`,
  `parity_form_vanishes_on_member_iff`), and `PaperTests.example_pole_free_locus_six`, with
  `PaperTests.example_pole_free_locus_six_rational`;
* descent and containment: `descent_to_smaller_side` and `odd_side_nesting`,
  `odd_side_nesting_mirror`;
* the class residue: its hypotheses (`FlankClassPoleHypotheses`) with
  `FlankClassPoleHypotheses.eq_hitClass` (`K` is the flank class of its top),
  `odd_chord_outside_class_nonvanishing_on_hyperplane` and
  `flank_class_pole_hypotheses_innermost` (the remarks after the definition), `grouping_identity`
  (with the one-chord step `nlsmAvoiding_step`), `flank_class_members_form_chains`,
  `collapse_identity`, `only_extreme_term_survives`, `strip_factor_value` and
  `simple_pole_along_flank_class`, with the
  non-vacuity facts `PaperTests.not_hasNoPoleAlong_inv`, `PaperTests.not_restrictsToZeroAlong_one`,
  `PaperTests.hasNoPoleAlong_can_fail`, `PaperTests.example_four_six_residue_regime` and
  `PaperTests.example_four_six_extreme_terms_nonvanishing`, and the same example's residue chords,
  none with both sides linked (`PaperTests.example_no_residue_chord_with_both_sides_linked`);
* strip regions, corners and the ear lemma: `strip_regions`, `corner_identity`,
  `polygon_numerators_vanish_on_ear_locus`;
* the marked locus: `gram_model`, `genericity` and its companions and `polygon_numerator_value`,
  with the instance `PaperTests.marked_locus_nonvacuous`;
* the children of an odd chord: `children_of_odd_chord_locus`,
  `children_of_odd_chord_size`, `children_of_odd_chord_linked`,
  `children_of_odd_chord_flank_class`, and the members of a child's list inside the child set:
  `child_zeros_away_from_new_leg`, `child_zeros_at_new_leg`, `unlinked_side_child_vanishes`;
* the image of the cut at an odd chord: `cut_relation`, `cut_image_onto`, `cut_image_hyperplane`,
  `cut_absorber_of_inner_pair`, `cut_absorber_of_residue_chord`, with the example
  `PaperTests.example_cut_image_hyperplane`;
* `minimality_from_containment`: clause 2 of the main theorem from clause 1;
* `members_are_closed_zeros`: the members of the list are regular, zeros and linearly closed.
-/

@[expose] public section

namespace PionCompleteness.Paper

open Finset PionCompleteness.Pi PionCompleteness.PionNLSM PionCompleteness.PionZeros
  PionCompleteness.ChainSlice PionCompleteness.TreeRectangleZero

-- A declaration that a claim of the paper names (it carries the claim's registry key, or a snippet
-- names it in `\lean` before the registry does) is named `<subject path>.<name>`, after the claim's
-- subject; lemmas in the namespace of such a definition
-- move with it (`<subject path>.<Def>.<lemma>`), so that dot notation finds them. The other
-- declarations stay at the top level. `open` needs an existing namespace, hence the empty blocks
-- below; opening them lets the statements and proofs use the short names. Inside this namespace,
-- `open Algebra` would open the subject namespace `Algebra` below, not Mathlib's.
namespace Algebra.RationalFunctions
end Algebra.RationalFunctions
namespace Amplitudes.Kinematics.Mesh
end Amplitudes.Kinematics.Mesh
namespace Combinatorics.Polygons
end Combinatorics.Polygons
namespace Combinatorics.SetSystems
end Combinatorics.SetSystems
namespace NLSM.Amplitude
end NLSM.Amplitude
namespace NLSM.FeynmanRules
end NLSM.FeynmanRules
namespace NLSM.Zeros
end NLSM.Zeros
namespace NLSM.Zeros.Families
end NLSM.Zeros.Families
open Algebra.RationalFunctions Amplitudes.Kinematics.Mesh Combinatorics.Polygons
  Combinatorics.SetSystems NLSM.Amplitude NLSM.FeynmanRules NLSM.Zeros NLSM.Zeros.Families

/-! ## The definitions of the main theorem

The notions in the statement of the main theorem, as the paper defines them: regular sets, zeros,
regular coordinate zeros and minimal ones (`IsRegularSet`, `IsCoordinateZero`,
`IsRegularCoordinateZero`, `IsMinimalCoordinateZero`), causal diamonds and the list
(`IsCausalDiamond`, `IsListMember`); and candidate sets (`IsCandidateSet`), which the proof of
clause 1 is about. The amplitude is `NLSM` at the generic point `gen`, the
coordinate locus `L_S` is `OnLocus`, and the separated pairs `S_G` are `sepPairs`. A pair `{a, b}`
of legs is the element `(a, b)` of `diagonals N`, with `a < b`.

Each definition but `IsCausalDiamond` is proved equal to the library's form that the general
results use: `isRegularSet_iff_nondeg`; `isCoordinateZero_iff_ampZeroOn`, for a regular set of
pairs and even `N ≥ 4`; `isRegularCoordinateZero_iff_isNDZero` and
`isMinimalCoordinateZero_iff_isMinimalZero`, for even `N ≥ 4`; `isListMember_iff_mem_gFamily`,
the list's two forms, for even `N`, which covers the causal diamonds; and
`isCandidateSet_iff_inFpi`, for even `N`. -/

-- registry: C-3Q69 T-P1FD
/-- A set `S` of pairs is **regular**: no planar variable vanishes identically on the coordinate
locus `L_S`. -/
def NLSM.Zeros.IsRegularSet (N : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  ∀ d ∈ diagonals N, ¬ ∀ x : ℕ × ℕ → ℚ, OnLocus N S x → x d = 0

-- registry: C-3Q69 T-0D9F
/-- `S` is a **zero**: `A_N^NLSM ≡ 0` on `L_S`, as a rational function on the kinematic space. -/
def NLSM.Zeros.IsCoordinateZero (N : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  RatZeroOn {x | OnLocus N S x} (NLSM N gen)

-- registry: C-3Q69 T-0D9F
/-- A **regular coordinate zero**: a regular set of pairs that is a zero. -/
def NLSM.Zeros.IsRegularCoordinateZero (N : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  S ⊆ diagonals N ∧ IsRegularSet N S ∧ IsCoordinateZero N S

-- registry: C-N17V T-TRDD
/-- A **minimal** regular coordinate zero `Z`: for every pair `t ∈ Z`, the set `Z ∖ {t}` is not a
zero. -/
def NLSM.Zeros.IsMinimalCoordinateZero (N : ℕ) (Z : Finset (ℕ × ℕ)) : Prop :=
  IsRegularCoordinateZero N Z ∧ ∀ t ∈ Z, ¬ IsCoordinateZero N (Z.erase t)

-- registry: C-WG9E T-K4X2
/-- A **causal diamond**: `S_{a,b}` for two legs `a < b` whose two arcs are both non-empty (a leg
strictly between them, and a leg outside them). -/
def NLSM.Zeros.Families.IsCausalDiamond (N : ℕ) (Z : Finset (ℕ × ℕ)) : Prop :=
  ∃ a ∈ Icc 1 N, ∃ b ∈ Icc 1 N, a < b ∧ (∃ u, a < u ∧ u < b) ∧ (∃ u ∈ Icc 1 N, u < a ∨ b < u) ∧
    Z = sepPairs N {a, b}

-- registry: C-WG9E T-6RK0
/-- `Z` is a member of **the list** `𝒢_N`: a causal diamond, or `S_T` for a set `T` of at least
three legs of one parity. -/
def NLSM.Zeros.Families.IsListMember (N : ℕ) (Z : Finset (ℕ × ℕ)) : Prop :=
  IsCausalDiamond N Z ∨
    ∃ T ⊆ Icc 1 N, 3 ≤ T.card ∧ (∀ t ∈ T, ∀ u ∈ T, t % 2 = u % 2) ∧ Z = sepPairs N T

-- registry: T-ASJM
/-- A **candidate set**: a regular set of pairs that contains no member of the list. -/
def NLSM.Zeros.IsCandidateSet (N : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  S ⊆ diagonals N ∧ IsRegularSet N S ∧ ¬ ∃ Z, IsListMember N Z ∧ Z ⊆ S

-- registry: C-3Q69
/-- Regular is the library's `Nondeg`. -/
theorem NLSM.Zeros.isRegularSet_iff_nondeg {N : ℕ} {S : Finset (ℕ × ℕ)} :
    IsRegularSet N S ↔ Nondeg N S := by
  unfold IsRegularSet Nondeg
  simp only [not_forall, exists_prop]

-- registry: C-3Q69
/-- For a set of pairs that is regular, in the library's form `Nondeg` (`N ≥ 4` even), a zero is
the library's pointwise `AmpZeroOn`. -/
theorem NLSM.Zeros.isCoordinateZero_iff_ampZeroOn {N : ℕ} (hN : 4 ≤ N) (hE : Even N)
    {S : Finset (ℕ × ℕ)} (hS : S ⊆ diagonals N) (hreg : Nondeg N S) :
    IsCoordinateZero N S ↔ AmpZeroOn N S :=
  (ampZeroOn_iff_ratZero hN hE hS hreg).symm

-- registry: C-M4RC
/-- **Zeros pointwise**: for even `N ≥ 4` and a regular set `S` of pairs, `S` is a zero iff
`A_N^NLSM(x) = 0` at every rational point `x` of `L_S` at which no odd chord vanishes. -/
theorem NLSM.Zeros.isCoordinateZero_iff_pointwise {N : ℕ} (hN : 4 ≤ N) (hE : Even N)
    {S : Finset (ℕ × ℕ)} (hS : S ⊆ diagonals N) (hreg : IsRegularSet N S) :
    IsCoordinateZero N S ↔ ∀ x : ℕ × ℕ → ℚ, OnLocus N S x → (∀ d ∈ oddDiagonals N, x d ≠ 0) →
      NLSM N x = 0 := by
  rw [isCoordinateZero_iff_ampZeroOn hN hE hS (isRegularSet_iff_nondeg.1 hreg),
    ampZeroOn_iff_nlsmZeroOn]
  rfl

-- registry: C-3Q69
/-- A regular coordinate zero is the library's `IsNDZero` (`N ≥ 4` even). -/
theorem NLSM.Zeros.isRegularCoordinateZero_iff_isNDZero {N : ℕ} (hN : 4 ≤ N) (hE : Even N)
    {S : Finset (ℕ × ℕ)} : IsRegularCoordinateZero N S ↔ IsNDZero N S := by
  constructor
  · rintro ⟨hS, hr, hz⟩
    have hnd := isRegularSet_iff_nondeg.1 hr
    exact ⟨hS, hnd, (isCoordinateZero_iff_ampZeroOn hN hE hS hnd).1 hz⟩
  · rintro ⟨hS, hnd, hz⟩
    exact ⟨hS, isRegularSet_iff_nondeg.2 hnd, (isCoordinateZero_iff_ampZeroOn hN hE hS hnd).2 hz⟩

-- registry: C-N17V
/-- A minimal regular coordinate zero is the library's `IsMinimalZero` (`N ≥ 4` even): each
`Z ∖ {t}` is regular, so the two readings of "not a zero" agree. -/
theorem NLSM.Zeros.isMinimalCoordinateZero_iff_isMinimalZero {N : ℕ} (hN : 4 ≤ N) (hE : Even N)
    {Z : Finset (ℕ × ℕ)} : IsMinimalCoordinateZero N Z ↔ IsMinimalZero N Z := by
  constructor
  · rintro ⟨hZ, hmin⟩
    have hnd := (isRegularCoordinateZero_iff_isNDZero hN hE).1 hZ
    refine ⟨hnd, fun t ht h => hmin t ht ?_⟩
    exact (isCoordinateZero_iff_ampZeroOn hN hE ((erase_subset t Z).trans hnd.1)
      (nonDeg_mono (erase_subset t Z) hnd.2.1)).2 h
  · rintro ⟨hnd, hmin⟩
    refine ⟨(isRegularCoordinateZero_iff_isNDZero hN hE).2 hnd, fun t ht h => hmin t ht ?_⟩
    exact (isCoordinateZero_iff_ampZeroOn hN hE ((erase_subset t Z).trans hnd.1)
      (nonDeg_mono (erase_subset t Z) hnd.2.1)).1 h

-- registry: C-WG9E
/-- **The list's two forms agree** (even `N`): the members of the list are the members of the
library's `gFamily`, the `S_T` for `T` of at least two legs of one parity and the causal diamonds
`S_{a,b}` with `a`, `b` of opposite parity. Two distinct legs of one parity are never adjacent, so
their causal diamond is an `S_T` with `|T| = 2`. -/
theorem NLSM.Zeros.Families.isListMember_iff_mem_gFamily {N : ℕ} (hE : Even N)
    {Z : Finset (ℕ × ℕ)} : IsListMember N Z ↔ Z ∈ gFamily N := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  constructor
  · rintro (⟨a, ha, b, hb, hab, ⟨u, hu1, hu2⟩, ⟨v, hv, hv'⟩, rfl⟩ | ⟨T, hT, h3, hpar, rfl⟩)
    · have ha' := mem_Icc.1 ha
      have hb' := mem_Icc.1 hb
      have hv'' := mem_Icc.1 hv
      have hsub : ({a, b} : Finset ℕ) ⊆ Icc 1 N := by
        intro x hx
        rcases mem_insert.1 hx with rfl | hx
        · exact ha
        · rw [mem_singleton.1 hx]; exact hb
      refine mem_image.2 ⟨{a, b}, mem_filter.2 ⟨mem_powerset.2 hsub, ?_⟩, rfl⟩
      by_cases hp : a % 2 = b % 2
      · refine Or.inl ?_
        have hadm : Admissible N (a % 2) {a, b} := by
          refine ⟨hsub, by rw [card_pair (by omega)], ?_⟩
          intro x hx
          rcases mem_insert.1 hx with rfl | hx
          · rfl
          · rw [mem_singleton.1 hx]; exact hp.symm
        rcases Nat.mod_two_eq_zero_or_one a with h | h
        · exact Or.inl (h ▸ hadm)
        · exact Or.inr (h ▸ hadm)
      · exact Or.inr ⟨a, ha, b, hb, rfl, by omega, by omega, hp⟩
    · obtain ⟨t0, ht0⟩ : T.Nonempty := card_pos.1 (by omega)
      refine mem_image.2 ⟨T, mem_filter.2 ⟨mem_powerset.2 hT, Or.inl ?_⟩, rfl⟩
      have hadm : Admissible N (t0 % 2) T := ⟨hT, by omega, fun t ht => hpar t ht t0 ht0⟩
      rcases Nat.mod_two_eq_zero_or_one t0 with h | h
      · exact Or.inl (h ▸ hadm)
      · exact Or.inr (h ▸ hadm)
  · intro hZ
    obtain ⟨G, hG, rfl⟩ := mem_image.1 hZ
    obtain ⟨hGsub, hGset⟩ := mem_filter.1 hG
    have hGI : G ⊆ Icc 1 N := mem_powerset.1 hGsub
    -- a leg outside `{a, b}` for `a < b` with `(a, b) ≠ (1, N)`
    have outside : ∀ a b, 1 ≤ a → b ≤ N → a < b → ¬ (a = 1 ∧ b = N) →
        ∃ u ∈ Icc 1 N, u < a ∨ b < u := by
      intro a b ha hb hab hn
      by_cases h1 : a = 1
      · exact ⟨N, mem_Icc.2 ⟨by omega, le_rfl⟩, Or.inr (by omega)⟩
      · exact ⟨1, mem_Icc.2 ⟨le_rfl, by omega⟩, Or.inl (by omega)⟩
    rcases hGset with hsp | ⟨a, ha, b, hb, rfl, hab, hn, -⟩
    · obtain ⟨r, -, h2, hr⟩ : ∃ r, Admissible N r G := by
        rcases hsp with h | h
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
      by_cases h3 : 3 ≤ G.card
      · exact Or.inr ⟨G, hGI, h3, fun t ht u hu => (hr t ht).trans (hr u hu).symm, rfl⟩
      · obtain ⟨a, b, hab, rfl⟩ := card_eq_two.1 (show G.card = 2 by omega)
        have ha := mem_Icc.1 (hGI (mem_insert_self a {b}))
        have hb := mem_Icc.1 (hGI (mem_insert_of_mem (mem_singleton_self b)))
        have hpa := hr a (mem_insert_self a {b})
        have hpb := hr b (mem_insert_of_mem (mem_singleton_self b))
        refine Or.inl ?_
        rcases Nat.lt_or_gt_of_ne hab with h | h
        · exact ⟨a, mem_Icc.2 ha, b, mem_Icc.2 hb, h, ⟨a + 1, by omega, by omega⟩,
            outside a b ha.1 hb.2 h (by omega), rfl⟩
        · exact ⟨b, mem_Icc.2 hb, a, mem_Icc.2 ha, h, ⟨b + 1, by omega, by omega⟩,
            outside b a hb.1 ha.2 h (by omega), by rw [pair_comm]⟩
    · have ha' := mem_Icc.1 ha
      have hb' := mem_Icc.1 hb
      exact Or.inl ⟨a, ha, b, hb, by omega, ⟨a + 1, by omega, by omega⟩,
        outside a b ha'.1 hb'.2 (by omega) hn, rfl⟩

/-- A candidate set is the library's `InFpi` (even `N`): regular is `Nondeg`, and the list's two
forms agree. -/
theorem NLSM.Zeros.isCandidateSet_iff_inFpi {N : ℕ} (hE : Even N) {S : Finset (ℕ × ℕ)} :
    IsCandidateSet N S ↔ InFpi N S := by
  unfold IsCandidateSet InFpi ContainsGMember
  simp only [isRegularSet_iff_nondeg, isListMember_iff_mem_gFamily hE]

/-! ## Zeros upward, the gaps of a set of legs, and the blocks of `S_G`

Short arguments the paper gives in its remarks on the definitions: a regular set containing a
zero is a zero, so the zeros are known once the minimal ones are; a set of legs has one parity iff
every gap between cyclically consecutive legs is odd; a causal diamond inside `S_G` forces
`G ⊆ {a, b}`; and `S_G` is a union of rectangular blocks of tiles, one for each two of its arcs.
The gap after a leg `g` of `G` is written with `nextCut N G g`, the next leg of `G` numbered past
`N` where the gap wraps around: its legs are `vtx N i` for `g < i < nextCut N G g`. A block is the
image under `tlab` of a product of two ranges of integers, the form of `ChainSlice.diamond`. -/

/-- A subset of a regular set of pairs is regular (its locus is larger). -/
theorem NLSM.Zeros.isRegularSet_mono {N : ℕ} {Z S : Finset (ℕ × ℕ)} (h : Z ⊆ S)
    (hreg : IsRegularSet N S) : IsRegularSet N Z :=
  isRegularSet_iff_nondeg.2 (nonDeg_mono h (isRegularSet_iff_nondeg.1 hreg))

-- registry: C-CPXG
/-- **Adding conditions keeps a zero**: for even `N ≥ 4`, if `Z ⊆ S` is a zero and `S` is regular,
then `S` is a zero (`L_S ⊆ L_Z`, and zeros read pointwise for both). -/
theorem NLSM.Zeros.isCoordinateZero_of_subset {N : ℕ} (hN : 4 ≤ N) (hE : Even N)
    {Z S : Finset (ℕ × ℕ)} (hS : S ⊆ diagonals N) (hreg : IsRegularSet N S) (hZS : Z ⊆ S)
    (hZ : IsCoordinateZero N Z) : IsCoordinateZero N S := by
  rw [isCoordinateZero_iff_pointwise hN hE hS hreg]
  intro x hx hp
  exact (isCoordinateZero_iff_pointwise hN hE (hZS.trans hS) (isRegularSet_mono hZS hreg)).1 hZ x
    (onLocus_mono hZS hx) hp

-- registry: C-CPXG
/-- **Every regular coordinate zero contains a minimal one**: removing pairs one at a time while
the set stays a zero ends at a minimal regular coordinate zero. -/
theorem NLSM.Zeros.exists_minimal_coordinate_zero_subset {N : ℕ} {S : Finset (ℕ × ℕ)}
    (hS : IsRegularCoordinateZero N S) : ∃ Z ⊆ S, IsMinimalCoordinateZero N Z := by
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases h : ∀ t ∈ S, ¬ IsCoordinateZero N (S.erase t)
    · exact ⟨S, Subset.rfl, hS, h⟩
    · push Not at h
      obtain ⟨t, ht, hz⟩ := h
      obtain ⟨Z, hZ, hmin⟩ := ih (S.erase t) (erase_ssubset ht)
        ⟨(erase_subset t S).trans hS.1, isRegularSet_mono (erase_subset t S) hS.2.1, hz⟩
      exact ⟨Z, hZ.trans (erase_subset t S), hmin⟩

-- registry: C-CPXG
/-- **The zeros are known once the minimal ones are**: for even `N ≥ 4`, a regular set `S` of pairs
is a zero iff it contains a minimal regular coordinate zero. -/
theorem NLSM.Zeros.isCoordinateZero_iff_contains_minimal {N : ℕ} (hN : 4 ≤ N) (hE : Even N)
    {S : Finset (ℕ × ℕ)} (hS : S ⊆ diagonals N) (hreg : IsRegularSet N S) :
    IsCoordinateZero N S ↔ ∃ Z ⊆ S, IsMinimalCoordinateZero N Z :=
  ⟨fun hz => exists_minimal_coordinate_zero_subset ⟨hS, hreg, hz⟩,
    fun ⟨_, hZS, hZ⟩ => isCoordinateZero_of_subset hN hE hS hreg hZS hZ.1.2.2⟩

-- registry: C-4Z73 C-71E2 C-HCQK
/-- The leg of `G` after the leg `g`, cyclically, numbered past `N` when the gap wraps around: the
least leg of `G` above `g`, else the least leg of `G` plus `N`. The gap after `g` is the legs
`vtx N i`, `g < i < nextCut N G g`; it holds `nextCut N G g - g - 1` legs. -/
def Combinatorics.Polygons.nextCut (N : ℕ) (G : Finset ℕ) (g : ℕ) : ℕ :=
  if h : (G.filter (g < ·)).Nonempty then (G.filter (g < ·)).min' h
  else if h' : G.Nonempty then G.min' h' + N else g + N

/-- When a leg of `G` lies above `g`, the next cut leg is the least such leg. -/
theorem Combinatorics.Polygons.nextCut_of_above {N : ℕ} {G : Finset ℕ} {g : ℕ}
    (h : ∃ y ∈ G, g < y) :
    nextCut N G g ∈ G ∧ g < nextCut N G g ∧ ∀ y ∈ G, g < y → nextCut N G g ≤ y := by
  have hne : (G.filter (g < ·)).Nonempty := by
    obtain ⟨y, hy, hgy⟩ := h
    exact ⟨y, mem_filter.2 ⟨hy, hgy⟩⟩
  unfold nextCut
  rw [dite_eq_left hne]
  have hm := min'_mem _ hne
  exact ⟨(mem_filter.1 hm).1, (mem_filter.1 hm).2,
    fun y hy hgy => min'_le _ _ (mem_filter.2 ⟨hy, hgy⟩)⟩

/-- When `g` is the top leg of `G`, the gap after it wraps around to the least leg, plus `N`. -/
theorem Combinatorics.Polygons.nextCut_of_top {N : ℕ} {G : Finset ℕ} {g : ℕ} (hg : g ∈ G)
    (h : ∀ y ∈ G, y ≤ g) : nextCut N G g = G.min' ⟨g, hg⟩ + N := by
  have hne : ¬ (G.filter (g < ·)).Nonempty := by
    rintro ⟨y, hy⟩
    have := h y (mem_filter.1 hy).1
    have := (mem_filter.1 hy).2
    omega
  unfold nextCut
  rw [dite_eq_right hne, dite_eq_left ⟨g, hg⟩]

/-- The two gaps of two legs `a < b`: `b` follows `a`, and `a + N` follows `b`. -/
theorem Combinatorics.Polygons.nextCut_pair {N a b : ℕ} (hab : a < b) :
    nextCut N {a, b} a = b ∧ nextCut N {a, b} b = a + N := by
  constructor
  · obtain ⟨hm, hlt, -⟩ := nextCut_of_above (N := N) (G := {a, b}) (g := a) ⟨b, by simp, hab⟩
    rcases mem_insert.1 hm with h | h
    · omega
    · rw [mem_singleton.1 h]
  · rw [nextCut_of_top (by simp) (by simp; omega)]
    congr 1
    exact le_antisymm (min'_le _ _ (by simp)) (le_min' _ _ _ (by simp; omega))

-- registry: C-71E2
/-- **One parity iff every gap is odd**: for even `N` and a set `G` of legs, the legs of `G` have
one parity iff the gap after each leg of `G` (the legs strictly between it and the next leg of `G`,
cyclically) holds an odd number of legs; an empty gap counts as even. So every arc of a set of legs
of one parity has odd size. -/
theorem Combinatorics.Polygons.one_parity_iff_gaps_odd {N : ℕ} (hE : Even N) {G : Finset ℕ}
    (hG : G ⊆ Icc 1 N) :
    (∀ g ∈ G, ∀ g' ∈ G, g % 2 = g' % 2) ↔ ∀ g ∈ G, Odd (nextCut N G g - g - 1) := by
  obtain ⟨n, rfl⟩ := hE
  constructor
  · intro hpar g hg
    have hg1 := mem_Icc.1 (hG hg)
    rw [Nat.odd_iff]
    by_cases htop : ∃ y ∈ G, g < y
    · obtain ⟨hm, hlt, -⟩ := nextCut_of_above (N := n + n) htop
      have := hpar g hg _ hm
      omega
    · push Not at htop
      rw [nextCut_of_top hg htop]
      have hm := min'_mem G ⟨g, hg⟩
      have := hpar g hg _ hm
      have := min'_le G g hg
      have := mem_Icc.1 (hG hm)
      omega
  · intro hodd
    -- consecutive legs have one parity; then follow the legs of `G` upwards
    have key : ∀ d, ∀ g ∈ G, ∀ g' ∈ G, g < g' → g' - g ≤ d → g % 2 = g' % 2 := by
      intro d
      induction d using Nat.strong_induction_on with
      | _ d ih =>
        intro g hg g' hg' hlt hd
        obtain ⟨hm, hlt', hle⟩ := nextCut_of_above (N := n + n) ⟨g', hg', hlt⟩
        have h1 := Nat.odd_iff.1 (hodd g hg)
        rcases (hle g' hg' hlt).lt_or_eq with h | h
        · have := ih (g' - nextCut (n + n) G g) (by omega) _ hm g' hg' h le_rfl
          omega
        · rw [← h]
          omega
    intro g hg g' hg'
    rcases lt_trichotomy g g' with h | rfl | h
    · exact key _ g hg g' hg' h le_rfl
    · rfl
    · exact (key _ g' hg' g hg h le_rfl).symm

-- registry: C-4Z73
/-- **Two legs of opposite parity**: for even `N` and legs `a < b` of opposite parity whose two
arcs are non-empty, both gaps of `{a, b}` hold an even number of legs, and both corners of the
causal diamond, `X_{a,b}` and `X_{a+1,b+1}`, are odd chords. -/
theorem Combinatorics.Polygons.opposite_parity_gaps_even {N : ℕ} (hE : Even N) {a b : ℕ}
    (ha : 1 ≤ a) (hb : b ≤ N) (hab : a + 2 ≤ b) (hout : ¬ (a = 1 ∧ b = N))
    (hp : a % 2 ≠ b % 2) :
    Even (nextCut N {a, b} a - a - 1) ∧ Even (nextCut N {a, b} b - b - 1) ∧
      (a, b) ∈ oddDiagonals N ∧ tlab N (a + 1) (b + 1) ∈ oddDiagonals N := by
  obtain ⟨n, rfl⟩ := hE
  obtain ⟨hna, hnb⟩ := nextCut_pair (N := n + n) (show a < b by omega)
  refine ⟨by rw [hna, Nat.even_iff]; omega, by rw [hnb, Nat.even_iff]; omega, ?_, ?_⟩
  · simp only [oddDiagonals, diagonals, mem_filter, mem_product, mem_Icc]; omega
  · rcases (by omega : b < n + n ∨ b = n + n) with h | rfl
    · rw [pkA_tlab_lo (by omega) (by omega) (by omega)]
      simp only [oddDiagonals, diagonals, mem_filter, mem_product, mem_Icc]; omega
    · have e := pkA_tlab_hi (m := n + n) (i := a + 1) (k := 1) le_rfl (by omega) (by omega)
      rw [show 1 + (n + n) = n + n + 1 by omega] at e
      rw [e]
      simp only [oddDiagonals, diagonals, mem_filter, mem_product, mem_Icc]; omega

-- registry: C-7110
/-- **A causal diamond inside `S_G`**: for a set `G` of legs and two legs `a < b` whose two arcs
are non-empty, if `S_{a,b} ⊆ S_G` then `G ⊆ {a, b}`: every other leg lies in a pair of `S_{a,b}`,
so it is not cut. -/
theorem NLSM.Zeros.Families.subset_pair_of_causal_diamond_subset {N : ℕ} {G : Finset ℕ}
    (hG : G ⊆ Icc 1 N) {a b : ℕ} (ha : a ∈ Icc 1 N) (hb : b ∈ Icc 1 N) (hab : a < b)
    (hin : ∃ u, a < u ∧ u < b) (hout : ∃ u ∈ Icc 1 N, u < a ∨ b < u)
    (h : sepPairs N {a, b} ⊆ sepPairs N G) : G ⊆ {a, b} := by
  have ha' := mem_Icc.1 ha
  have hb' := mem_Icc.1 hb
  -- a pair `(s, t)` of `S_{a,b}` has no leg in `G`
  have mk : ∀ s t, s ∈ Icc 1 N → t ∈ Icc 1 N → s < t →
      (∃ c ∈ ({a, b} : Finset ℕ), s < c ∧ c < t) → (∃ c ∈ ({a, b} : Finset ℕ), c < s ∨ t < c) →
      s ∉ ({a, b} : Finset ℕ) → t ∉ ({a, b} : Finset ℕ) → s ∉ G ∧ t ∉ G := by
    intro s t hs ht hst h1 h2 hs' ht'
    have hs'' := mem_Icc.1 hs
    have ht'' := mem_Icc.1 ht
    have hdiag : (s, t) ∈ diagonals N := by
      obtain ⟨c, hc, hc1, hc2⟩ := h1
      obtain ⟨c', hc', hc'2⟩ := h2
      have hc3 : 1 ≤ c' ∧ c' ≤ N := by
        rcases mem_insert.1 hc' with e | e
        · omega
        · rw [mem_singleton.1 e]; omega
      simp only [diagonals, mem_filter, mem_product, mem_Icc]
      omega
    have hp := h (pkL_mem_sep.2 ⟨hdiag, (pkL_inST_iff hst).2 ⟨hs', ht', h1, h2⟩⟩)
    obtain ⟨h3, h4, -, -⟩ := (pkL_inST_iff hst).1 (pkL_mem_sep.1 hp).2
    exact ⟨h3, h4⟩
  intro x hx
  by_contra hxab
  have hx' := mem_Icc.1 (hG hx)
  have hxa : x ≠ a := fun e => hxab (by rw [e]; simp)
  have hxb : x ≠ b := fun e => hxab (by rw [e]; simp)
  obtain ⟨u, hu1, hu2⟩ := hin
  obtain ⟨w, hw, hw'⟩ := hout
  have hw'' := mem_Icc.1 hw
  have nab : ∀ y, y ≠ a → y ≠ b → y ∉ ({a, b} : Finset ℕ) := by
    intro y h1 h2 hy
    rcases mem_insert.1 hy with e | e
    · exact h1 e
    · exact h2 (mem_singleton.1 e)
  rcases (by omega : (a < x ∧ x < b) ∨ x < a ∨ b < x) with hxin | hxo | hxo
  · rcases hw' with hw' | hw'
    · exact (mk w x hw (hG hx) (by omega) ⟨a, by simp, by omega⟩ ⟨b, by simp, by omega⟩
        (nab w (by omega) (by omega)) hxab).2 hx
    · exact (mk x w (hG hx) hw (by omega) ⟨b, by simp, by omega⟩ ⟨a, by simp, by omega⟩
        hxab (nab w (by omega) (by omega))).1 hx
  · exact (mk x u (hG hx) (mem_Icc.2 ⟨by omega, by omega⟩) (by omega) ⟨a, by simp, by omega⟩
      ⟨b, by simp, by omega⟩ hxab (nab u (by omega) (by omega))).1 hx
  · exact (mk u x (mem_Icc.2 ⟨by omega, by omega⟩) (hG hx) (by omega) ⟨b, by simp, by omega⟩
      ⟨a, by simp, by omega⟩ (nab u (by omega) (by omega)) hxab).2 hx

-- registry: C-7110
/-- **No causal diamond inside `S_T` for `|T| ≥ 3`**: for a set `T` of at least three legs, `S_T`
contains no causal diamond. -/
theorem NLSM.Zeros.Families.no_causal_diamond_in_separated_pairs {N : ℕ} {T : Finset ℕ}
    (hT : T ⊆ Icc 1 N) (h3 : 3 ≤ T.card) : ¬ ∃ Z, IsCausalDiamond N Z ∧ Z ⊆ sepPairs N T := by
  rintro ⟨Z, ⟨a, ha, b, hb, hab, hin, hout, rfl⟩, hZT⟩
  have := card_le_card (subset_pair_of_causal_diamond_subset hT ha hb hab hin hout hZT)
  have := card_le_two (a := a) (b := b)
  omega

-- registry: C-HCQK
/-- A tile of the block of two gaps of `G`: for legs `g < h` of `G`, `i` in the gap after `g` and
`j` in the gap after `h` (numbered past `N` where the gap wraps around), the tile `c_{i,j}` is a
pair of `S_G`, and `i < j < i + N`. -/
theorem Amplitudes.Kinematics.Mesh.separated_pairs_block_tile {N : ℕ} {G : Finset ℕ}
    (hG : G ⊆ Icc 1 N) {g h i j : ℕ} (hg : g ∈ G) (hh : h ∈ G) (hgh : g < h)
    (hi : g < i ∧ i < nextCut N G g) (hj : h < j ∧ j < nextCut N G h) :
    tlab N i j ∈ sepPairs N G ∧ i < j ∧ j < i + N := by
  have hg' := mem_Icc.1 (hG hg)
  have hh' := mem_Icc.1 (hG hh)
  obtain ⟨hng, hgn, hlen⟩ := nextCut_of_above (N := N) ⟨h, hh, hgh⟩
  have hnh := hlen h hh hgh
  have hiG : i ∉ G := fun hiG => by have := hlen i hiG hi.1; omega
  have hmin : ∀ y ∈ G, G.min' ⟨g, hg⟩ ≤ y := fun y hy => min'_le G y hy
  have hming := hmin g hg
  have hmin1 := mem_Icc.1 (hG (min'_mem G ⟨g, hg⟩))
  have diag : ∀ s t, 1 ≤ s → s + 2 ≤ t → t ≤ N → ¬ (s = 1 ∧ t = N) → (s, t) ∈ diagonals N := by
    intro s t h1 h2 h3 h4
    simp only [diagonals, mem_filter, mem_product, mem_Icc]
    omega
  by_cases htop : ∃ y ∈ G, h < y
  · obtain ⟨hnh2, hhn, hlen2⟩ := nextCut_of_above (N := N) htop
    have hnh2' := mem_Icc.1 (hG hnh2)
    have hjG : j ∉ G := fun hjG => by have := hlen2 j hjG hj.1; omega
    rw [pkA_tlab_lo (by omega) (by omega) (by omega)]
    exact ⟨pkL_mem_sep.2 ⟨diag i j (by omega) (by omega) (by omega) (by omega),
      (pkL_inST_iff (by omega)).2 ⟨hiG, hjG, ⟨h, hh, by omega, by omega⟩,
        ⟨g, hg, Or.inl (by omega)⟩⟩⟩, by omega, by omega⟩
  · push Not at htop
    rw [nextCut_of_top hh htop] at hj
    rcases (by omega : j ≤ N ∨ N < j) with hjN | hjN
    · have hjG : j ∉ G := fun hjG => by have := htop j hjG; omega
      rw [pkA_tlab_lo (by omega) (by omega) hjN]
      exact ⟨pkL_mem_sep.2 ⟨diag i j (by omega) (by omega) hjN (by omega),
        (pkL_inST_iff (by omega)).2 ⟨hiG, hjG, ⟨h, hh, by omega, by omega⟩,
          ⟨g, hg, Or.inl (by omega)⟩⟩⟩, by omega, by omega⟩
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + N := ⟨j - N, by omega⟩
      have hkG : k ∉ G := fun hkG => by have := hmin k hkG; omega
      rw [pkA_tlab_hi (by omega) (by omega) (by omega)]
      exact ⟨pkL_mem_sep.2 ⟨diag k i (by omega) (by omega) (by omega) (by omega),
        (pkL_inST_iff (by omega)).2 ⟨hkG, hiG, ⟨g, hg, by omega, by omega⟩,
          ⟨h, hh, Or.inr (by omega)⟩⟩⟩, by omega, by omega⟩

-- registry: C-HCQK
/-- **`S_G` is a union of rectangular blocks, one for each two of its arcs**: for a set `G` of legs,
`S_G` is the union, over legs `g < h` of `G`, of the tiles `c_{i,j}` with `i` in the gap after `g`
and `j` in the gap after `h` (numbered past `N` where a gap wraps around); each block is the image
under `tlab` of a product of two ranges of integers with `i < j < i + N`, the form of
`ChainSlice.diamond`. -/
theorem Amplitudes.Kinematics.Mesh.separated_pairs_eq_blocks {N : ℕ} {G : Finset ℕ}
    (hG : G ⊆ Icc 1 N) :
    sepPairs N G = ((G ×ˢ G).filter (fun q => q.1 < q.2)).biUnion (fun q =>
      (Ioo q.1 (nextCut N G q.1) ×ˢ Ioo q.2 (nextCut N G q.2)).image (fun p => tlab N p.1 p.2)) ∧
    ∀ g ∈ G, ∀ h ∈ G, g < h → ∀ i ∈ Ioo g (nextCut N G g), ∀ j ∈ Ioo h (nextCut N G h),
      i < j ∧ j < i + N := by
  refine ⟨?_, fun g hg h hh hgh i hi j hj =>
    (separated_pairs_block_tile hG hg hh hgh (mem_Ioo.1 hi) (mem_Ioo.1 hj)).2⟩
  apply Subset.antisymm
  · rintro ⟨u, w⟩ hp
    obtain ⟨hd, hst⟩ := pkL_mem_sep.1 hp
    have hd' : 1 ≤ u ∧ u ≤ N ∧ 1 ≤ w ∧ w ≤ N ∧ u + 2 ≤ w := by
      simp only [diagonals, mem_filter, mem_product, mem_Icc] at hd
      omega
    obtain ⟨huG, hwG, ⟨t, ht, hut, htw⟩, ⟨t', ht', ht'o⟩⟩ := (pkL_inST_iff (by omega)).1 hst
    -- the last leg of `G` below a leg `x` not in `G`; the gap after it holds `x`
    have hlast : ∀ x, x ≤ N → x ∉ G → ∀ y ∈ G, y < x → ∃ h ∈ G, h < x ∧
        (∀ z ∈ G, z < x → z ≤ h) ∧ x < nextCut N G h := by
      intro x hxN hxG y hy hyx
      have hne : (G.filter (· < x)).Nonempty := ⟨y, mem_filter.2 ⟨hy, hyx⟩⟩
      have hm := mem_filter.1 (max'_mem _ hne)
      refine ⟨_, hm.1, hm.2, fun z hz hzx => le_max' _ _ (mem_filter.2 ⟨hz, hzx⟩), ?_⟩
      by_cases htop : ∃ z ∈ G, (G.filter (· < x)).max' hne < z
      · obtain ⟨hn, hlt, -⟩ := nextCut_of_above (N := N) htop
        by_contra hc
        rcases (by omega : nextCut N G ((G.filter (· < x)).max' hne) = x ∨
            nextCut N G ((G.filter (· < x)).max' hne) < x) with e | e
        · exact hxG (e ▸ hn)
        · have := le_max' (G.filter (· < x)) _ (mem_filter.2 ⟨hn, by exact e⟩); omega
      · push Not at htop
        rw [nextCut_of_top hm.1 htop]
        have := mem_Icc.1 (hG (min'_mem G ⟨_, hm.1⟩))
        omega
    obtain ⟨h, hh, hhw, hhmax, hwn⟩ := hlast w hd'.2.2.2.1 hwG t ht htw
    have hth := hhmax t ht htw
    rw [mem_biUnion]
    by_cases hbelow : ∃ y ∈ G, y < u
    · obtain ⟨y, hy, hyu⟩ := hbelow
      obtain ⟨g, hg, hgu, -, hun⟩ := hlast u hd'.2.1 huG y hy hyu
      refine ⟨(g, h), mem_filter.2 ⟨mem_product.2 ⟨hg, hh⟩, by dsimp only; omega⟩,
        mem_image.2 ⟨(u, w), mem_product.2 ⟨mem_Ioo.2 ⟨hgu, hun⟩, mem_Ioo.2 ⟨hhw, hwn⟩⟩, ?_⟩⟩
      exact pkA_tlab_lo hd'.1 (by omega) hd'.2.2.2.1
    · push Not at hbelow
      have hwt' : w < t' := by
        rcases ht'o with e | e
        · have := hbelow t' ht'; omega
        · exact e
      have hne : G.Nonempty := ⟨t, ht⟩
      have hmax := le_max' G t' ht'
      have hmaxG := mem_Icc.1 (hG (max'_mem G hne))
      have hmin : u < G.min' hne := by
        rcases (hbelow _ (min'_mem G hne)).lt_or_eq with e | e
        · exact e
        · exact absurd (e ▸ min'_mem G hne) huG
      have hnt : nextCut N G (G.max' hne) = G.min' hne + N :=
        nextCut_of_top (max'_mem G hne) (fun y hy => le_max' G y hy)
      refine ⟨(h, G.max' hne), mem_filter.2 ⟨mem_product.2 ⟨hh, max'_mem G hne⟩, by
        dsimp only; omega⟩, mem_image.2 ⟨(w, u + N), mem_product.2 ⟨mem_Ioo.2 ⟨hhw, hwn⟩,
          mem_Ioo.2 ⟨by omega, by rw [hnt]; omega⟩⟩, ?_⟩⟩
      exact pkA_tlab_hi hd'.1 (by omega) hd'.2.2.2.1
  · intro p hp
    obtain ⟨q, hq, hpq⟩ := mem_biUnion.1 hp
    obtain ⟨hq1, hq2⟩ := mem_filter.1 hq
    obtain ⟨⟨i, j⟩, hij, rfl⟩ := mem_image.1 hpq
    obtain ⟨hi, hj⟩ := mem_product.1 hij
    exact (separated_pairs_block_tile hG (mem_product.1 hq1).1 (mem_product.1 hq1).2 hq2
      (mem_Ioo.1 hi) (mem_Ioo.1 hj)).1

-- registry: C-HCQK
/-- **Two cut legs give one block**: for legs `a < b`, `S_{a,b}` is the tile range
`ChainSlice.diamond N (a + 1) (b + 1)`, the tiles `c_{i,j}` with `a < i < b < j < a + N`. -/
theorem Amplitudes.Kinematics.Mesh.separated_pairs_of_two_legs_eq_diamond {N a b : ℕ} (ha : 1 ≤ a)
    (hab : a < b) (hb : b ≤ N) : sepPairs N {a, b} = diamond N (a + 1) (b + 1) := by
  have hG : ({a, b} : Finset ℕ) ⊆ Icc 1 N := by
    intro x hx
    rcases mem_insert.1 hx with e | e
    · rw [e]; exact mem_Icc.2 ⟨ha, by omega⟩
    · rw [mem_singleton.1 e]; exact mem_Icc.2 ⟨by omega, hb⟩
  obtain ⟨hna, hnb⟩ := nextCut_pair (N := N) hab
  have hpairs : (({a, b} : Finset ℕ) ×ˢ {a, b}).filter (fun q => q.1 < q.2) = {(a, b)} := by
    ext ⟨x, y⟩
    simp only [mem_filter, mem_product, mem_insert, mem_singleton, Prod.mk.injEq]
    omega
  rw [(separated_pairs_eq_blocks hG).1, hpairs, singleton_biUnion]
  dsimp only
  rw [hna, hnb, diamond]
  congr 1
  ext ⟨i, j⟩
  simp only [mem_product, mem_Ioo, mem_Icc]
  omega

/-! ## Rational functions: restriction to a hyperplane, numerators and residues

The paper's residue `Res_{X_C=0} F := (X_C F)|_{X_C=0}` and its identities `Res_C F = G` are stated
as `RatZeroOn {x | x C = 0} (X_C · F − G)`: the difference restricts to the zero rational function
on the hyperplane. `ratZeroOn_hyperplane_iff_zeroAt` turns such a statement into one about
numerators (`zeroAt C P = 0`), the form in which the library proves its residues. -/

open MvPolynomial in
/-- Setting the variable `C` to `0` and evaluating at `x` is evaluating at the point `x` with its
`C`-coordinate set to `0`. -/
theorem eval_zeroAt (C : ℕ × ℕ) (x : ℕ × ℕ → ℚ) (P : MvPolynomial (ℕ × ℕ) ℚ) :
    eval x (zeroAt ℚ C P) = eval (fun d => if d = C then 0 else x d) P := by
  have h : (eval x).comp (zeroAt ℚ C : MvPolynomial (ℕ × ℕ) ℚ →+* MvPolynomial (ℕ × ℕ) ℚ) =
      eval (fun d => if d = C then 0 else x d) := by
    refine ringHom_ext (fun r => ?_) (fun d => ?_)
    · simp [zeroAt]
    · simp only [RingHom.coe_comp, Function.comp_apply, zeroAt, AlgHom.coe_toRingHom, aeval_X,
        eval_X]
      split_ifs <;> simp
  exact congrArg (fun φ => φ P) h

open MvPolynomial in
/-- Setting a variable to `0` twice is setting it once. -/
theorem zeroAt_zeroAt (C : ℕ × ℕ) (P : MvPolynomial (ℕ × ℕ) ℚ) :
    zeroAt ℚ C (zeroAt ℚ C P) = zeroAt ℚ C P := by
  have h : (zeroAt ℚ C).comp (zeroAt ℚ C) = zeroAt ℚ C := by
    refine algHom_ext fun d => ?_
    simp only [AlgHom.comp_apply, zeroAt, aeval_X]
    split_ifs with h <;> simp [h]
  exact congrArg (fun φ => φ P) h

open MvPolynomial in
/-- **Restriction to a hyperplane `X_C = 0`, numerator form.** If `F · Q = P` with `Q` not vanishing
identically on `X_C = 0`, then `F` restricts to the zero rational function on `X_C = 0` iff the
numerator `P` with `X_C` set to `0` is the zero polynomial. -/
theorem ratZeroOn_hyperplane_iff_zeroAt {C : ℕ × ℕ} {F : RF} {P Q : MvPolynomial (ℕ × ℕ) ℚ}
    (hF : F * algebraMap _ RF Q = algebraMap _ RF P) (hQ : zeroAt ℚ C Q ≠ 0) :
    RatZeroOn {x | x C = 0} F ↔ zeroAt ℚ C P = 0 := by
  have hinj := IsFractionRing.injective (MvPolynomial (ℕ × ℕ) ℚ) RF
  -- a point of the hyperplane is unchanged by setting its `C`-coordinate to `0`
  have hfix : ∀ x : ℕ × ℕ → ℚ, x C = 0 → (fun d => if d = C then 0 else x d) = x := by
    intro x hx
    funext d
    split_ifs with h
    · rw [h, hx]
    · rfl
  constructor
  · rintro ⟨P', Q', hF', ⟨w, hw, hQw⟩, hP'⟩
    have hw : w C = 0 := hw
    have key : P * Q' = P' * Q := hinj (by
      rw [map_mul, map_mul, ← hF, ← hF']
      ring)
    have hz := congrArg (zeroAt ℚ C) key
    rw [map_mul, map_mul] at hz
    have hP'0 : zeroAt ℚ C P' = 0 := MvPolynomial.funext fun x => by
      rw [eval_zeroAt, map_zero]
      exact hP' _ (by simp)
    have hQ'0 : zeroAt ℚ C Q' ≠ 0 := fun h => hQw (by
      have := congrArg (eval w) h
      rwa [eval_zeroAt, hfix w hw, map_zero] at this)
    rw [hP'0, zero_mul] at hz
    exact (mul_eq_zero.1 hz).resolve_right hQ'0
  · intro hP
    refine ⟨P, Q, hF, ?_, fun x hx => ?_⟩
    · obtain ⟨v, hv⟩ : ∃ v, eval v (zeroAt ℚ C Q) ≠ 0 := by
        by_contra h
        simp only [not_exists, not_not] at h
        exact hQ (MvPolynomial.funext fun v => by rw [h v, map_zero])
      refine ⟨fun d => if d = C then 0 else v d, by simp, ?_⟩
      rwa [eval_zeroAt] at hv
    · have hx : x C = 0 := hx
      rw [← hfix x hx, ← eval_zeroAt, hP, map_zero]

open MvPolynomial in
/-- A rational function vanishing on `V` still vanishes after multiplication by a polynomial. -/
theorem ratZeroOn_mul_left {V : Set (ℕ × ℕ → ℚ)} {F : RF} (h : RatZeroOn V F)
    (u : MvPolynomial (ℕ × ℕ) ℚ) : RatZeroOn V (algebraMap _ RF u * F) := by
  obtain ⟨P, Q, hF, hw, hP⟩ := h
  refine ⟨u * P, Q, by rw [mul_assoc, hF, map_mul], hw, fun x hx => ?_⟩
  rw [map_mul, hP x hx, mul_zero]

open MvPolynomial in
/-- A ring map out of the polynomials is evaluation, at the images of the variables, of the
polynomial with its coefficients mapped. -/
theorem ringHom_eq_eval_map {K : Type*} [CommRing K] (f : MvPolynomial (ℕ × ℕ) ℚ →+* K)
    (p : MvPolynomial (ℕ × ℕ) ℚ) :
    f p = eval (fun d => f (X d)) (map (f.comp C) p) := by
  rw [eval_map]
  have h : f = eval₂Hom (f.comp C) (fun d => f (X d)) :=
    ringHom_ext (fun r => by simp) (fun d => by simp)
  exact congrArg (fun φ => φ p) h

open MvPolynomial in
/-- **Numerator of a δ-coefficient, for every ring map into a field**: `f(AP_m) = a_m(f ∘ X) ·
f(∏_{odd} X_P)` wherever no odd chord maps to `0`. -/
theorem shiftCoeff_numerator_hom {K : Type*} [Field K] (f : MvPolynomial (ℕ × ℕ) ℚ →+* K)
    (N m : ℕ) (hX : ∀ d ∈ oddDiagonals N, f (X d) ≠ 0) :
    f (AP ℚ N m) = shiftCoeff N m (fun d => f (X d)) * f (oddDen ℚ N) := by
  rw [ringHom_eq_eval_map, AP_map, AP_eval N m _ hX, oddDen, map_prod]

open MvPolynomial in
-- registry: C-27FF
/-- **Numerator of `NLSM_N`, for every ring map into a field**: `f(NP) = NLSM_N(f ∘ X) ·
f(∏_{odd} X_P)` wherever no odd chord maps to `0`. -/
theorem nlsm_numerator_hom {K : Type*} [Field K] (f : MvPolynomial (ℕ × ℕ) ℚ →+* K) {N : ℕ}
    (hN : 2 ≤ N) (hX : ∀ d ∈ oddDiagonals N, f (X d) ≠ 0) :
    f (NP ℚ N) = NLSM N (fun d => f (X d)) * f (oddDen ℚ N) := by
  have e : NLSM N (fun d => f (X d)) = shiftCoeff N ((N - 2 : ℕ) : ℤ) (fun d => f (X d)) := by
    rw [show ((N - 2 : ℕ) : ℤ) = (N : ℤ) - 2 by omega]; rfl
  rw [e]
  exact shiftCoeff_numerator_hom f N (N - 2) hX

open MvPolynomial in
/-- A homogeneous polynomial of degree `m` scales by `c ^ m` (over any commutative ring;
`pkR_hom_eval` of `C7` is the same fact over `ℚ`). -/
theorem eval_mul_of_isHomogeneous {R σ : Type*} [CommRing R] {P : MvPolynomial σ R} {m : ℕ}
    (h : P.IsHomogeneous m) (c : R) (x : σ → R) :
    eval (fun i => c * x i) P = c ^ m * eval x P := by
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [h.degree_eq_sum_deg_support hs]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

open MvPolynomial in
/-- **Degree 1 from a numerator.** If `F(X) · ∏_{odd} X_P` is the value of a homogeneous
polynomial of degree `#odd + 1` at every point where no odd chord vanishes, then
`F (c · X) = c · F X` there, for every `c ≠ 0`. -/
theorem homogeneous_of_numerator {K : Type*} [Field K] {N : ℕ} {Num : MvPolynomial (ℕ × ℕ) K}
    (hNum : Num.IsHomogeneous ((oddDiagonals N).card + 1)) {F : (ℕ × ℕ → K) → K}
    (hF : ∀ Y : ℕ × ℕ → K, (∀ d ∈ oddDiagonals N, Y d ≠ 0) →
      eval Y Num = F Y * ∏ d ∈ oddDiagonals N, Y d)
    {c : K} (hc : c ≠ 0) {X : ℕ × ℕ → K} (hX : ∀ d ∈ oddDiagonals N, X d ≠ 0) :
    F (fun d => c * X d) = c * F X := by
  have h1 := hF (fun d => c * X d) fun d hd => mul_ne_zero hc (hX d hd)
  rw [eval_mul_of_isHomogeneous hNum, hF X hX, prod_mul_distrib, prod_const] at h1
  have hp : ∏ d ∈ oddDiagonals N, X d ≠ 0 := prod_ne_zero_iff.2 hX
  apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero (oddDiagonals N).card hc) hp)
  rw [← h1]
  ring

open MvPolynomial in
/-- The odd chords of the `N`-gon other than an odd chord `C = (i, j)`: those of the sub-polygon
`i..j` and of the sub-polygon `j..N,1..i` (relabelled from 1) and those crossing `C`. -/
theorem prod_oddDiagonals_erase {N : ℕ} (hE : Even N) {C : ℕ × ℕ} (hC : C ∈ oddDiagonals N) :
    ∏ d ∈ (oddDiagonals N).erase C, (X d : MvPolynomial (ℕ × ℕ) ℚ) =
      crossProd ℚ N C * rename (relab N C.1) (oddDen ℚ (C.2 - C.1 + 1)) *
        rename (relab N C.2) (oddDen ℚ (N - C.2 + C.1 + 1)) := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  have hd := mem_diagonals.1 (mem_filter.1 hC).1
  have h := pkQ_odd_prod (R := ℚ) (N := N) (i := C.1) (j := C.2) hd.1 hd.2.2.1 hd.2.1 hd.2.2.2 hE'
    (empty_subset _) (empty_subset _)
  have hg : pkSpGlue N C.1 C.2 ∅ ∅ = {C} := by simp [pkSpGlue]
  rw [hg, sdiff_singleton_eq_erase, sdiff_empty, sdiff_empty] at h
  rw [h, oddDen, oddDen]

open MvPolynomial in
/-- The product of the odd chords other than `C` does not involve `X_C`. -/
theorem zeroAt_prod_erase_ne_zero (N : ℕ) (C : ℕ × ℕ) :
    zeroAt ℚ C (∏ d ∈ (oddDiagonals N).erase C, (X d : MvPolynomial (ℕ × ℕ) ℚ)) ≠ 0 := by
  rw [map_prod]
  refine prod_ne_zero_iff.2 fun d hd => ?_
  rw [zeroAt, aeval_X, ite_eq_right (fun h => absurd h (ne_of_mem_erase hd))]
  exact X_ne_zero d

open MvPolynomial in
/-- **A residue identity from its numerator.** Let `C` be an odd chord. If `F · ∏_{odd P ≠ C} X_P`
is `N − N|_{X_C=0}` for a polynomial `N`, then `F` restricts to the zero rational function on
`X_C = 0`. -/
theorem ratZeroOn_of_sub_zeroAt {N : ℕ} {C : ℕ × ℕ} {F : RF} {Num : MvPolynomial (ℕ × ℕ) ℚ}
    (hF : F * algebraMap _ RF (∏ d ∈ (oddDiagonals N).erase C, (X d : MvPolynomial (ℕ × ℕ) ℚ)) =
      algebraMap _ RF (Num - zeroAt ℚ C Num)) :
    RatZeroOn {x | x C = 0} F :=
  (ratZeroOn_hyperplane_iff_zeroAt hF (zeroAt_prod_erase_ne_zero N C)).2
    (by rw [map_sub, zeroAt_zeroAt, sub_self])

/-! ## The analytic facts -/

open MvPolynomial in
-- registry: C-D3DK
/-- Analytic inputs, (δ-order): for even `N ≥ 4`, in `A_N^{φ³}(X + δ v₀) = Σ_j a_j(X) δ^{−j}` every
`a_j` with `j < N − 2` vanishes (as a rational function); `NLSM_N = a_{N−2}` (its definition) is
homogeneous of degree 1 (over every field, at every point where no odd chord vanishes, which at
the generic point of a function field is the rational-function statement); and
`NLSM_N · ∏_{P odd} X_P` is a polynomial. -/
theorem NLSM.Amplitude.analytic_facts_delta_order {N : ℕ} (hN : 4 ≤ N) (hE : Even N) :
    (∀ j : ℤ, j < (N : ℤ) - 2 → shiftCoeff N j gen = 0) ∧
    (∀ (K : Type*) [Field K] (c : K) (X : ℕ × ℕ → K), c ≠ 0 →
      (∀ d ∈ oddDiagonals N, X d ≠ 0) → NLSM N (fun d => c * X d) = c * NLSM N X) ∧
    ∃ P : MvPolynomial (ℕ × ℕ) ℚ,
      NLSM N gen * ∏ d ∈ oddDiagonals N, gen d = algebraMap _ RF P := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  refine ⟨fun j hj => shiftCoeff_eq_zero_of_lt hN hE' gen (fun d _ => gen_ne_zero d) hj,
    fun K _ c X hc hX => ?_, ⟨NP ℚ N, ?_⟩⟩
  · refine homogeneous_of_numerator (Num := NP K N) (pkR_NP_hom hN) (fun Y hY => ?_) hc hX
    have e : NLSM N Y = shiftCoeff N ((N - 2 : ℕ) : ℤ) Y := by
      rw [show ((N - 2 : ℕ) : ℤ) = (N : ℤ) - 2 by omega]; rfl
    rw [e]
    exact AP_eval N (N - 2) Y hY
  · rw [nlsm_numerator_hom (algebraMap _ RF) (by omega) (fun d _ => gen_ne_zero d), oddDen,
      map_prod]
    rfl

open MvPolynomial in
-- registry: C-D3DK
/-- Analytic inputs, (Factorisation): for even `N ≥ 4` and an odd chord `C = (i, j)`,
`Res_{X_C=0} NLSM_N := (X_C · NLSM_N)|_{X_C=0} = NLSM_L · NLSM_R` as rational functions (the
difference restricts to the zero rational function on `X_C = 0`), where `L` (vertices `i..j`) and
`R` (vertices `j..N, 1..i`) are the two sub-polygons cut off by `C`, each relabelled from 1, with
`X_C` read as an edge; the sign is `+1`. -/
theorem NLSM.Amplitude.analytic_facts_factorisation {N : ℕ} (hN : 4 ≤ N) (hE : Even N) {C : ℕ × ℕ}
    (hC : C ∈ oddDiagonals N) :
    RatZeroOn {x | x C = 0} (gen C * NLSM N gen -
      NLSM (C.2 - C.1 + 1) (fun d => gen (relab N C.1 d)) *
        NLSM (N - C.2 + C.1 + 1) (fun d => gen (relab N C.2 d))) := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  -- the child sizes `≥ 4` (used by the `omega` calls below)
  have hc := pkZ_child hE' hC
  refine ratZeroOn_of_sub_zeroAt (N := N) (Num := NP ℚ N) ?_
  -- the parent
  have hP : gen C * NLSM N gen *
      algebraMap _ RF (∏ d ∈ (oddDiagonals N).erase C, (X d : MvPolynomial (ℕ × ℕ) ℚ)) =
      algebraMap _ RF (NP ℚ N) := by
    have h := nlsm_numerator_hom (algebraMap _ RF) (N := N) (by omega)
      (fun d _ => gen_ne_zero d)
    rw [show (fun d => algebraMap _ RF (X d)) = gen from rfl, oddDen, ← mul_prod_erase _ _ hC,
      map_mul] at h
    rw [h, show gen C = algebraMap _ RF (X C) from rfl]
    ring
  -- a child, through the relabelling
  have hch : ∀ (b n : ℕ), 2 ≤ n →
      NLSM n (fun d => gen (relab N b d)) * algebraMap _ RF (rename (relab N b) (oddDen ℚ n)) =
        algebraMap _ RF (rename (relab N b) (NP ℚ n)) := by
    intro b n hn
    have h := nlsm_numerator_hom ((algebraMap _ RF).comp (rename (relab N b)).toRingHom) hn
      (fun d _ => by simp)
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, rename_X] at h
    exact h.symm
  rw [sub_mul, hP, prod_oddDiagonals_erase hE hC, map_sub, NP_residue hN hE' hC]
  congr 1
  rw [map_mul, map_mul, map_mul, map_mul, ← hch C.1 _ (by omega), ← hch C.2 _ (by omega)]
  ring

-- registry: C-D3DK
/-- Analytic inputs, (Symmetry): for even `N ≥ 4`, `NLSM_N` is invariant under the rotations of the
legs (over every field; `rot N` shifts the labels by one). Invariance under a
reflection and under `v₀ ↦ −v₀` is a remark of the paper, not formalised. -/
theorem NLSM.Amplitude.analytic_facts_symmetry {K : Type*} [Field K] {N : ℕ} (hN : 4 ≤ N)
    (hE : Even N) (X : ℕ × ℕ → K) (k : ℕ) : NLSM N (X ∘ (rot N)^[k]) = NLSM N X := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ, ← Function.comp_assoc,
      NLSM_rot hN (Nat.even_iff.1 hE) (X ∘ (rot N)^[k]), ih]

/-! ## The `T`-separated zeros -/

/-- Every point of `Z_T` lies on the `T`-separated locus `L_{S_T}` (converse of `pkS_onZT`). -/
theorem onLocus_sepPairs_of_onZT {N : ℕ} {T : Finset ℕ} {X : ℕ × ℕ → ℚ} (hX : OnZT N T X) :
    OnLocus N (sepPairs N T) X := by
  intro t ht
  obtain ⟨hd, hi⟩ := mem_filter.1 ht
  obtain ⟨h12, -⟩ := mem_filter.1 hd
  rw [mem_product] at h12
  exact hX t.1 h12.1 t.2 h12.2 hi

/-- The two descriptions of the `T`-separated locus agree: for `T ⊆ 1..N`, a rational point lies on
`Z_T` (the mesh variable of every pair separated by `T` vanishes, in either order) iff it lies on
`L_{S_T}`. -/
theorem onZT_iff_onLocus_sepPairs {N : ℕ} {T : Finset ℕ} (hT : T ⊆ Icc 1 N) {X : ℕ × ℕ → ℚ} :
    OnZT N T X ↔ OnLocus N (sepPairs N T) X :=
  ⟨onLocus_sepPairs_of_onZT, pkS_onZT hT⟩

-- registry: C-EFMH
/-- `S_T` is regular: for every even `N ≥ 4` and every set `T` of at least two legs of one parity,
no planar variable vanishes identically on `L_{S_T}` (every chord is non-zero at some point of it).
-/
theorem NLSM.Zeros.Families.t_separated_locus_nondegenerate {N : ℕ} (hN : 4 ≤ N) (hE : Even N)
    {T : Finset ℕ} (hT : IsSameParitySet N T) : IsRegularSet N (sepPairs N T) := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  rw [isRegularSet_iff_nondeg]
  apply nonDeg_of_pt
  rcases hT with h | h <;>
  · obtain ⟨X, hX, hd⟩ := ZT_inhabited hN hE' (by norm_num) h
    exact ⟨X, onLocus_sepPairs_of_onZT hX, hd⟩

/-- The `T`-separated zeros, pointwise: for every even `N ≥ 4` and every set `T` of at least two
legs of one parity, the NLSM amplitude vanishes at every rational point of the `T`-separated
locus `L_{S_T}` where no odd chord vanishes (equivalent to `t_separated_zero` by
`isCoordinateZero_iff_pointwise`). -/
theorem t_separated_zero_pointwise {N : ℕ} (hN : 4 ≤ N) (hE : Even N) {T : Finset ℕ}
    (hT : IsSameParitySet N T) : NLSMZeroOn N (sepPairs N T) := by
  intro X hL hX
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  rcases hT with h | h <;>
  · exact (nlsm_zero_on_ZT hN hE' (by norm_num) h).2 X (pkS_onZT (pkS_sub h) hL) hX

-- registry: C-1WNP
/-- The `T`-separated zeros: for every even `N ≥ 4` and every set `T` of at least two legs of one
parity, `NLSM_N ≡ 0` on the `T`-separated locus `L_{S_T}`, as a rational function (the paper's
"zero"). -/
theorem NLSM.Zeros.Families.t_separated_zero {N : ℕ} (hN : 4 ≤ N) (hE : Even N) {T : Finset ℕ}
    (hT : IsSameParitySet N T) : IsCoordinateZero N (sepPairs N T) :=
  (ampZeroOn_iff_ratZero hN hE (filter_subset _ _)
    (isRegularSet_iff_nondeg.1 (t_separated_locus_nondegenerate hN hE hT))).1
    (ampZeroOn_iff_nlsmZeroOn.2 (t_separated_zero_pointwise hN hE hT))

-- registry: C-6TWS
/-- A good quad exists: for even `N ≥ 4`, a set `T` of at least two legs, all of
parity `r`, and the polarity `π_T = 1 − r` opposite to `T`, every quadrangulation has a good quad
(both `−` sides live, that is, their blocks meet `T`, and neither `+` side live). -/
theorem Combinatorics.Polygons.quadrangulation_has_good_quad {N r : ℕ} (hN : 4 ≤ N) (hE : Even N)
    (hr : r < 2) {T : Finset ℕ} (hT : Admissible N r T) {G : Finset (ℕ × ℕ)}
    (hG : G ∈ quadrangulations N) :
    ∃ q ∈ quads N G, GoodQ N T (1 - r) q :=
  exists_goodQ hN (Nat.even_iff.1 hE) hr hT hG

-- registry: C-70H7
/-- The good vertex factor vanishes: for even `N ≥ 4`, a set `T` of at least two
legs, all of parity `r`, and the polarity `π_T = 1 − r`, let `q` be a good quad of a
quadrangulation, with `+` blocks `B₁`, `B₃`. Every pair `(a, b) ∈ B₁ × B₃` lies in `S_T`; hence
`n_q^{π_T}` vanishes on `K_T = L_{S_T}`. (Labels of a block past `N` are read mod `N`.) -/
theorem NLSM.FeynmanRules.good_vertex_factor_vanishes {N r : ℕ} (hN : 4 ≤ N) (hE : Even N)
    (hr : r < 2) {T : Finset ℕ} (hT : Admissible N r T) {G : Finset (ℕ × ℕ)}
    (hG : G ∈ quadrangulations N) {q : Quad} (hq : q ∈ quads N G) (hg : GoodQ N T (1 - r) q) :
    (∀ a ∈ blk (plusPair N (1 - r) q).1.1 (plusPair N (1 - r) q).1.2,
      ∀ b ∈ blk (plusPair N (1 - r) q).2.1 (plusPair N (1 - r) q).2.2,
        npair N a b ∈ sepPairs N T) ∧
    ∀ X : ℕ × ℕ → ℚ, OnLocus N (sepPairs N T) X → vnum N (1 - r) X q = 0 := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  have hTs := pkS_sub hT
  have hqI := (mem_filter.1 hq).1
  refine ⟨?_, fun X hX => vnum_eq_zero_of_goodQ (by omega) hqI
    (quads_alternating hN hE' hG hq) hg (pkS_onZT hTs hX)⟩
  have hsym : ∀ x y, InST T x y → InST T y x := fun x y h => by
    unfold InST at h ⊢
    rwa [min_comm, max_comm, and_left_comm]
  -- a pair of legs in `1..N` separated by `T` lies in `S_T`
  have hmem : ∀ x y, x ∈ Icc 1 N → y ∈ Icc 1 N → InST T x y → npair N x y ∈ sepPairs N T := by
    intro x y hx hy h
    have vx := vtx_of_mem (mem_Icc.1 hx).1 (mem_Icc.1 hx).2
    have vy := vtx_of_mem (mem_Icc.1 hy).1 (mem_Icc.1 hy).2
    unfold npair
    rw [vx, vy]
    rcases le_total x y with hxy | hxy
    · rw [min_eq_left hxy, max_eq_right hxy]; exact pkS_mem_sep hTs hx hy hxy h
    · rw [min_eq_right hxy, max_eq_left hxy]; exact pkS_mem_sep hTs hy hx hxy (hsym x y h)
  rw [mem_quadIdx] at hqI
  obtain ⟨h1, h2, h3, h4, h5⟩ := hqI
  obtain ⟨p12, p23, p34⟩ := quads_alternating hN hE' hG hq
  have hs : ∀ s ∈ q.sides N, (IsPlus (1 - r) s → ¬ Meets N T s) ∧
      (¬ IsPlus (1 - r) s → Meets N T s) :=
    fun s hs' => ⟨(hg s hs').1, fun hn => by_contra fun hm => hn ((hg s hs').2 hm)⟩
  obtain ⟨m1p, m1m⟩ := hs (q.u1, q.u2) (by simp [Quad.sides])
  obtain ⟨m2p, m2m⟩ := hs (q.u2, q.u3) (by simp [Quad.sides])
  obtain ⟨m3p, m3m⟩ := hs (q.u3, q.u4) (by simp [Quad.sides])
  obtain ⟨m4p, m4m⟩ := hs (q.u4, q.u1 + N) (by simp [Quad.sides])
  simp only [IsPlus, Meets, blk] at m1p m1m m2p m2m m3p m3m m4p m4m
  have vid : ∀ x, 1 ≤ x → x ≤ N → vtx N x = x := fun x a b => vtx_of_mem a b
  unfold plusPair blk
  split_ifs with h
  · dsimp only
    intro a ha b hb
    rw [mem_Icc] at ha hb
    have ha' : a ∉ T := fun hm => m1p h ⟨a, mem_Icc.2 ha,
      by rw [vid a (by omega) (by omega)]; exact hm⟩
    have hb' : b ∉ T := fun hm => m3p (by omega) ⟨b, mem_Icc.2 hb,
      by rw [vid b (by omega) (by omega)]; exact hm⟩
    obtain ⟨x, hx, hxT⟩ := m2m (by omega)
    obtain ⟨y, hy, hyT⟩ := m4m (by omega)
    rw [mem_Icc] at hx hy
    rw [vid x (by omega) (by omega)] at hxT
    refine hmem a b (mem_Icc.2 ⟨by omega, by omega⟩) (mem_Icc.2 ⟨by omega, by omega⟩)
      ⟨ha', hb', ⟨x, hxT, ?_⟩, ?_⟩
    · rw [min_eq_left (by omega), max_eq_right (by omega)]; omega
    · rw [min_eq_left (by omega), max_eq_right (by omega)]
      rcases Nat.lt_or_ge N y with hyN | hyN
      · rw [vtx_of_gt hyN (by omega)] at hyT
        exact ⟨y - N, hyT, Or.inl (by omega)⟩
      · rw [vid y (by omega) hyN] at hyT
        exact ⟨y, hyT, Or.inr (by omega)⟩
  · dsimp only
    intro a ha b hb
    rw [mem_Icc] at ha hb
    have ha' : a ∉ T := fun hm => m2p (by omega) ⟨a, mem_Icc.2 ha,
      by rw [vid a (by omega) (by omega)]; exact hm⟩
    obtain ⟨x, hx, hxT⟩ := m1m h
    obtain ⟨y, hy, hyT⟩ := m3m (by omega)
    rw [mem_Icc] at hx hy
    rw [vid x (by omega) (by omega)] at hxT
    rw [vid y (by omega) (by omega)] at hyT
    rcases Nat.lt_or_ge N b with hbN | hbN
    · have hb' : b - N ∉ T := fun hm =>
        m4p (by omega) ⟨b, mem_Icc.2 hb, by rw [vtx_of_gt hbN (by omega)]; exact hm⟩
      have e : npair N a b = npair N a (b - N) := by
        unfold npair; rw [vtx_of_gt hbN (by omega), vid (b - N) (by omega) (by omega)]
      rw [e]
      refine hmem a (b - N) (mem_Icc.2 ⟨by omega, by omega⟩) (mem_Icc.2 ⟨by omega, by omega⟩)
        ⟨ha', hb', ⟨x, hxT, ?_⟩, ⟨y, hyT, ?_⟩⟩
      · rw [min_eq_right (by omega), max_eq_left (by omega)]; omega
      · rw [max_eq_left (by omega)]; right; omega
    · have hb' : b ∉ T := fun hm =>
        m4p (by omega) ⟨b, mem_Icc.2 hb, by rw [vid b (by omega) hbN]; exact hm⟩
      refine hmem a b (mem_Icc.2 ⟨by omega, by omega⟩) (mem_Icc.2 ⟨by omega, hbN⟩)
        ⟨ha', hb', ⟨y, hyT, ?_⟩, ⟨x, hxT, ?_⟩⟩
      · rw [min_eq_left (by omega), max_eq_right (by omega)]; omega
      · rw [min_eq_left (by omega)]; left; omega

-- registry: C-172Q
/-- Every diagram vanishes: for every even `N ≥ 4` and every set `T` of at least two legs, all of
parity `r`, with the legs of `T` in `−` slots (the polarity `π_T = 1 − r`), every quartic diagram
`∏ n_q / ∏ X_C` of `Q_N^{π_T}`, and their sum `Q_N^{π_T}`, restricts to the zero rational function
on the `T`-separated locus `L_{S_T}`. -/
theorem NLSM.FeynmanRules.diagrams_vanish_on_t_separated_locus {N r : ℕ} (hN : 4 ≤ N) (hE : Even N)
    (hr : r < 2) {T : Finset ℕ} (hT : Admissible N r T) :
    (∀ G ∈ quadrangulations N,
        RatZeroOn {x | OnLocus N (sepPairs N T) x} (diagram N (1 - r) gen G)) ∧
      RatZeroOn {x | OnLocus N (sepPairs N T) x} (Qpi N (1 - r) gen) := by
  have hE : N % 2 = 0 := Nat.even_iff.1 hE
  have hset : {x | OnLocus N (sepPairs N T) x} = {x | OnZT N T x} :=
    Set.ext fun x => (onZT_iff_onLocus_sepPairs (pkS_sub hT)).symm
  rw [hset]
  refine ⟨fun G hG => ?_, theoremA_rat hN hE hr hT⟩
  obtain ⟨w, hwZ, hw0⟩ := ZT_inhabited hN hE hr hT
  have hGs : G ⊆ oddDiagonals N := (mem_filter.1 hG).2.1
  have hGd : ∀ d ∈ G, d ∈ diagonals N := fun d hd => (mem_filter.1 (hGs hd)).1
  -- numerator and denominator of the diagram, as polynomials
  let P : MvPolynomial (ℕ × ℕ) ℚ := ∏ q ∈ quads N G, vnumP ℚ N (1 - r) q
  let Q : MvPolynomial (ℕ × ℕ) ℚ := ∏ d ∈ G, MvPolynomial.X d
  -- `f(P) = diagram(f ∘ X) · f(Q)` for every ring map keeping the propagators non-zero
  have hom : ∀ {K : Type} [Field K] (f : MvPolynomial (ℕ × ℕ) ℚ →+* K),
      (∀ d ∈ G, f (MvPolynomial.X d) ≠ 0) →
      f P = diagram N (1 - r) (fun d => f (MvPolynomial.X d)) G * f Q := by
    intro K _ f hf
    simp only [P, Q, map_prod, diagram]
    have hq : ∀ q ∈ quads N G, f (vnumP ℚ N (1 - r) q) =
        vnum N (1 - r) (fun d => f (MvPolynomial.X d)) q := fun q hq => by
      rw [vnumP_hom, vnum_eq_vnumX (1 - r) _ (mem_filter.1 hq).1]
    rw [prod_congr rfl hq, mul_assoc, ← prod_mul_distrib,
      prod_eq_one fun d hd => inv_mul_cancel₀ (hf d hd), mul_one]
  have hQw : MvPolynomial.eval w Q ≠ 0 := by
    simp only [Q, map_prod, MvPolynomial.eval_X]
    exact prod_ne_zero_iff.2 fun d hd => hw0 d (hGd d hd)
  refine ⟨P, Q, ?_, ⟨w, hwZ, hQw⟩, ?_⟩
  · rw [hom (algebraMap _ RF) (fun d _ => gen_ne_zero d)]; rfl
  · refine line_bridge _ (fun x hx y hy t => by
      simp only [Set.mem_ofPred_eq] at hx hy ⊢; exact onZT_line hx hy t)
      _ _ hwZ hQw fun x hx hQ => ?_
    have hx0 : ∀ d ∈ G, x d ≠ 0 := by
      simp only [Q, map_prod, MvPolynomial.eval_X] at hQ
      exact prod_ne_zero_iff.1 hQ
    rw [hom (MvPolynomial.eval x) (by simpa using hx0)]
    simp only [MvPolynomial.eval_X]
    rw [diagram_eq_zero hN hE hr hT hG hx, zero_mul]

/-! ## The diagram sum and the NLSM side -/

open MvPolynomial in
/-- The residue of `Q_N^π` on an odd chord `C = (i, j)`, as rational functions:
`(X_C · Q_N^π)|_{X_C=0} = Q_L^{π_L} · Q_R^{π_R}`, the children relabelled from 1 with `X_C` an
edge, `π_L = (π + i + 1) mod 2 ≡ π − (i − 1)`, `π_R = (π + j + 1) mod 2 ≡ π − (j − 1)`. -/
theorem quartic_residue {N π : ℕ} (hN : 4 ≤ N) (hE : Even N) (hπ : π < 2) {C : ℕ × ℕ}
    (hC : C ∈ oddDiagonals N) :
    RatZeroOn {x | x C = 0} (gen C * Qpi N π gen -
      Qpi (C.2 - C.1 + 1) ((π + C.1 + 1) % 2) (fun d => gen (relab N C.1 d)) *
        Qpi (N - C.2 + C.1 + 1) ((π + C.2 + 1) % 2) (fun d => gen (relab N C.2 d))) := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  refine ratZeroOn_of_sub_zeroAt (N := N) (Num := QP ℚ N π) ?_
  have hP : gen C * Qpi N π gen *
      algebraMap _ RF (∏ d ∈ (oddDiagonals N).erase C, (X d : MvPolynomial (ℕ × ℕ) ℚ)) =
      algebraMap _ RF (QP ℚ N π) := by
    have h := QP_hom (algebraMap _ RF) N π (fun d _ => gen_ne_zero d)
    rw [show (fun d => algebraMap _ RF (X d)) = gen from rfl, oddDen, ← mul_prod_erase _ _ hC,
      map_mul] at h
    rw [h, show gen C = algebraMap _ RF (X C) from rfl]
    ring
  have hch : ∀ (b n p : ℕ),
      Qpi n p (fun d => gen (relab N b d)) * algebraMap _ RF (rename (relab N b) (oddDen ℚ n)) =
        algebraMap _ RF (rename (relab N b) (QP ℚ n p)) := by
    intro b n p
    have h := QP_hom (R := ℚ) ((algebraMap _ RF).comp (rename (relab N b)).toRingHom) n p
      (fun d _ => by simp)
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, rename_X] at h
    exact h.symm
  rw [sub_mul, hP, prod_oddDiagonals_erase hE hC, map_sub, QP_residue hN hE' hπ hC]
  congr 1
  rw [map_mul, map_mul, map_mul, map_mul, ← hch C.1, ← hch C.2]
  ring

open MvPolynomial in
-- registry: C-92D9
/-- Structure and factorisation of the quartic diagram sum: for even `N ≥ 4` and a
polarity `π`, (i) each diagram has `(N − 2)/2` linear numerators over `(N − 4)/2` distinct odd
chords; (ii) `Q_N^π` is homogeneous of degree 1 (over every field, at every point where no odd
chord vanishes), with simple poles only at odd chords (`Q_N^π · ∏_{C odd} X_C` is a polynomial);
(iii) for an odd chord `C = (i, j)`, `Res_C Q_N^π := (X_C · Q_N^π)|_{X_C=0} = Q_L^{π_L} Q_R^{π_R}`,
with `L` the sub-polygon with vertices `i..j` and `R` the one with vertices `j..N, 1..i`, each
relabelled from 1 in the listed order with `X_C` an edge, and
`π_L = (π + i + 1) mod 2 ≡ π − (i − 1)`, `π_R = (π + j + 1) mod 2 ≡ π − (j − 1)`. -/
theorem NLSM.FeynmanRules.quartic_diagram_sum_structure {N π : ℕ} (hN : 4 ≤ N) (hE : Even N)
    (hπ : π < 2) :
    ((∀ (K : Type*) [Field K] (c : K) (X : ℕ × ℕ → K), c ≠ 0 →
        (∀ d ∈ oddDiagonals N, X d ≠ 0) → Qpi N π (fun d => c * X d) = c * Qpi N π X) ∧
      (∃ P : MvPolynomial (ℕ × ℕ) ℚ,
        Qpi N π gen * ∏ d ∈ oddDiagonals N, gen d = algebraMap _ RF P) ∧
      ∀ G ∈ quadrangulations N, (quads N G).card = (N - 2) / 2 ∧
        (∀ q ∈ quads N G, (vnumP ℚ N π q).IsHomogeneous 1) ∧
        G.card = (N - 4) / 2 ∧ G ⊆ oddDiagonals N) ∧
    ∀ C ∈ oddDiagonals N,
      RatZeroOn {x | x C = 0} (gen C * Qpi N π gen -
        Qpi (C.2 - C.1 + 1) ((π + C.1 + 1) % 2) (fun d => gen (relab N C.1 d)) *
          Qpi (N - C.2 + C.1 + 1) ((π + C.2 + 1) % 2) (fun d => gen (relab N C.2 d))) := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  refine ⟨⟨fun K _ c X hc hX => ?_, ⟨QP ℚ N π, ?_⟩, fun G hG => ?_⟩,
    fun C hC => quartic_residue hN hE hπ hC⟩
  · exact homogeneous_of_numerator (QP_isHomogeneous hN hE' π) (fun Y hY => QP_eval N π Y hY) hc hX
  · rw [QP_hom (algebraMap _ RF) N π (fun d _ => gen_ne_zero d), oddDen, map_prod]
    rfl
  · have hq := card_quads hN hE' hG
    have hq' := pkDg_card_quads hN hE' (mem_filter.1 hG).2
    exact ⟨hq, fun q _ => pkDg_vnumP N π q, by omega, (mem_filter.1 hG).2.1⟩

open MvPolynomial in
-- registry: C-FEV8
/-- Tr(φ³) and NLSM vanish on skinny rectangles: for `n ≥ 4`, the Tr(φ³) amplitude `A_n` vanishes
on the skinny rectangle `{c_{a,b} = 0 for all b}` of every leg `a`;
for even `n`, so does every coefficient of its `δ`-expansion, `NLSM_n` included. All as rational
functions. -/
theorem NLSM.Zeros.single_leg_locus {n a : ℕ} (hn : 4 ≤ n) (ha : a ∈ Icc 1 n) :
    RatZeroOn {x | OnRect n 1 a x} (amp n gen) ∧
    (Even n → (∀ m : ℤ, RatZeroOn {x | OnRect n 1 a x} (shiftCoeff n m gen)) ∧
      RatZeroOn {x | OnRect n 1 a x} (NLSM n gen)) := by
  obtain ⟨ha1, ha2⟩ := mem_Icc.1 ha
  refine ⟨amp_ratZero_onRect le_rfl (by omega) ha1 ha2, fun hE => ?_⟩
  have hE' : n % 2 = 0 := Nat.even_iff.1 hE
  obtain ⟨w, hw0, hwR⟩ := onRect_inhabited (le_refl 1) (by omega) ha1 ha2
  have hwodd : ∀ d ∈ oddDiagonals n, w d ≠ 0 := fun d hd => hw0 d (mem_filter.1 hd).1
  have hcoeff : ∀ m : ℤ, RatZeroOn {x | OnRect n 1 a x} (shiftCoeff n m gen) := by
    intro m
    rcases lt_or_ge m 0 with hm | hm
    · rw [shiftCoeff_neg n gen hm]
      exact ⟨0, 1, by simp, ⟨w, hwR, by simp⟩, fun x _ => by simp⟩
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    refine ⟨AP ℚ n k, oddDen ℚ n, ?_, ⟨w, hwR, pkBr_eval_oddDen_ne hwodd⟩, ?_⟩
    · exact (shiftCoeff_numerator_hom (algebraMap _ RF) n k (fun d _ => gen_ne_zero d)).symm
    · refine line_bridge _ (fun x hx y hy t => by
        simp only [Set.mem_ofPred_eq] at hx hy ⊢; exact onRect_line hx hy t)
        _ _ hwR (pkBr_eval_oddDen_ne hwodd) fun x hx hQ => ?_
      have hxo := pkBr_odd_of_eval hQ
      rw [shiftCoeff_numerator_hom (eval x) n k (by simpa using hxo)]
      simp only [eval_X]
      rw [shiftCoeff_row_zero (by omega) hE' ⟨ha1, ha2⟩ x hxo hx, zero_mul]
  exact ⟨hcoeff, hcoeff _⟩

-- registry: C-87Z8
/-- The NLSM side: for even `N ≥ 4`, writing `A_N^{φ³}(X + δ v₀) = Σ_j a_j δ^{−j}` at large `δ`,
(a) `a_j = 0` for `j < N − 2`; (b) `Res_C NLSM_N = NLSM_L NLSM_R` on every odd chord `C`, with `L`,
`R` the two polygons that `C` cuts off, in the parent's planar variables (`relab`); (c)
`NLSM_N ≡ 0` on the skinny rectangle of every leg `i` (`c_{i,b} = 0` for all `b`); all as rational
functions. -/
theorem NLSM.Amplitude.delta_order_factorisation_single_leg_vanishing {N : ℕ} (hN : 4 ≤ N)
    (hE : Even N) :
    (∀ j : ℤ, j < (N : ℤ) - 2 → shiftCoeff N j gen = 0) ∧
    (∀ C ∈ oddDiagonals N, RatZeroOn {x | x C = 0} (gen C * NLSM N gen -
      NLSM (C.2 - C.1 + 1) (fun d => gen (relab N C.1 d)) *
        NLSM (N - C.2 + C.1 + 1) (fun d => gen (relab N C.2 d)))) ∧
    ∀ i ∈ Icc 1 N, RatZeroOn {x | OnRect N 1 i x} (NLSM N gen) :=
  -- (a) is the analytic input (δ-order); the universe of its homogeneity clause is fixed for the
  -- projection
  ⟨(analytic_facts_delta_order.{0} hN hE).1, fun _ hC => analytic_facts_factorisation hN hE hC,
    fun _ hi => ((single_leg_locus hN hi).2 hE).2⟩

open MvPolynomial in
-- registry: C-YD73
/-- Pole-free on odd chords is a polynomial: if `J` is a rational function with a
square-free denominator dividing `∏_{C odd} X_C` (equivalently, `J · ∏_{C odd} X_C` is a
polynomial) and `(X_C · J)|_{X_C=0} = 0` for every odd chord `C`, then `J` is a polynomial. -/
theorem Algebra.RationalFunctions.pole_free_on_odd_chords_is_polynomial {N : ℕ} {J : RF}
    (hden : ∃ P : MvPolynomial (ℕ × ℕ) ℚ, J * algebraMap _ RF (oddDen ℚ N) = algebraMap _ RF P)
    (hres : ∀ C ∈ oddDiagonals N, RatZeroOn {x | x C = 0} (gen C * J)) :
    ∃ P : MvPolynomial (ℕ × ℕ) ℚ, J = algebraMap _ RF P := by
  obtain ⟨P, hP⟩ := hden
  have hz : ∀ C ∈ oddDiagonals N, zeroAt ℚ C P = 0 := by
    intro C hC
    refine (ratZeroOn_hyperplane_iff_zeroAt ?_ (zeroAt_prod_erase_ne_zero N C)).1 (hres C hC)
    rw [← hP, oddDen, ← mul_prod_erase _ _ hC, map_mul, show gen C = algebraMap _ RF (X C) from rfl]
    ring
  obtain ⟨P', hP'⟩ := prod_X_dvd_of_zeroAt (oddDiagonals N) P hz
  refine ⟨P', ?_⟩
  have hD : algebraMap _ RF (oddDen ℚ N) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (MvPolynomial (ℕ × ℕ) ℚ) RF), oddDen]
    exact prod_ne_zero_iff.2 fun d _ => X_ne_zero d
  apply mul_right_cancel₀ hD
  rw [hP, hP', oddDen, map_mul]
  ring

open MvPolynomial in
-- registry: C-FP65
/-- Three skinny rectangles: for even `N ≥ 6`, a linear form in the planar variables that vanishes
on the skinny rectangles of legs 1, 3, 5 is zero, and so is one that vanishes on those of legs 2, 4,
6. -/
theorem Amplitudes.Kinematics.Mesh.three_row_zeros {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    (α : ℕ × ℕ → ℚ) :
    ((∀ X : ℕ × ℕ → ℚ, (OnRect N 1 1 X ∨ OnRect N 1 3 X ∨ OnRect N 1 5 X) →
        ∑ d ∈ diagonals N, α d * X d = 0) → ∀ d ∈ diagonals N, α d = 0) ∧
    ((∀ X : ℕ × ℕ → ℚ, (OnRect N 1 2 X ∨ OnRect N 1 4 X ∨ OnRect N 1 6 X) →
        ∑ d ∈ diagonals N, α d * X d = 0) → ∀ d ∈ diagonals N, α d = 0) := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  set L : MvPolynomial (ℕ × ℕ) ℚ := ∑ d ∈ diagonals N, C (α d) * X d with hLdef
  have hdeg : L.totalDegree ≤ 1 := by
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun d _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, totalDegree_X]
  have heval : ∀ x : ℕ × ℕ → ℚ, eval x L = ∑ d ∈ diagonals N, α d * x d := by
    intro x; simp [hLdef]
  have hcoeff : ∀ d ∈ diagonals N, L.coeff (Finsupp.single d 1) = α d := by
    intro d hd
    rw [hLdef, coeff_sum, Finset.sum_eq_single d]
    · simp [coeff_C_mul, coeff_X]
    · intro b _ hb
      rw [coeff_C_mul, coeff_X]
      split_ifs with h
      · exact absurd (Finsupp.single_left_injective one_ne_zero h) hb
      · exact mul_zero _
    · intro h; exact absurd hd h
  have key : ∀ a : ℕ, 1 ≤ a ∧ a ≤ 2 →
      (∀ X : ℕ × ℕ → ℚ, (OnRect N 1 a X ∨ OnRect N 1 (a + 2) X ∨ OnRect N 1 (a + 4) X) →
        ∑ d ∈ diagonals N, α d * X d = 0) → ∀ d ∈ diagonals N, α d = 0 := by
    intro a ha h d hd
    have hL0 : L = 0 := three_rows hN hE' ha L hdeg fun x hx => by rw [heval]; exact h x hx
    rw [← hcoeff d hd, hL0]; rfl
  exact ⟨key 1 (by norm_num), key 2 (by norm_num)⟩

/-! ## Candidate sets, block sums and the parity form -/

-- registry: C-Z7RX
/-- Candidate sets are transversals: for even `N ≥ 4`, (i) a set `S` of pairs is a candidate set iff
its missing set `M` meets every member of the list; (ii) a set of pairs that contains no member of
the list is regular; (iii) every subset of a candidate set is a candidate set. -/
theorem NLSM.Zeros.Families.candidate_sets_are_transversals {N : ℕ} (hN : 4 ≤ N) (hE : Even N) :
    (∀ S : Finset (ℕ × ℕ), S ⊆ diagonals N →
      (IsCandidateSet N S ↔ ∀ Z, IsListMember N Z → (Z ∩ missing N S).Nonempty)) ∧
    (∀ S : Finset (ℕ × ℕ), S ⊆ diagonals N → (¬ ∃ Z, IsListMember N Z ∧ Z ⊆ S) →
      IsRegularSet N S) ∧
    ∀ S S' : Finset (ℕ × ℕ), IsCandidateSet N S → S' ⊆ S → IsCandidateSet N S' := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  have hL := fun Z => isListMember_iff_mem_gFamily (Z := Z) hE
  have hnd : ∀ S : Finset (ℕ × ℕ), S ⊆ diagonals N → ¬ ContainsGMember N S → Nondeg N S := by
    intro S hS hG d hd
    refine pkL_nondeg hN hE' hS (fun Z hZ => ?_) hd
    by_contra hne
    refine hG ⟨Z, hZ, fun t ht => ?_⟩
    by_contra htS
    exact hne ⟨t, mem_inter.2 ⟨ht, mem_sdiff.2 ⟨gFamily_sub hZ ht, htS⟩⟩⟩
  have hG : ∀ S : Finset (ℕ × ℕ), (¬ ∃ Z, IsListMember N Z ∧ Z ⊆ S) ↔ ¬ ContainsGMember N S :=
    fun S => by simp only [ContainsGMember, hL]
  refine ⟨fun S hS => ?_, fun S hS h => isRegularSet_iff_nondeg.2 (hnd S hS ((hG S).1 h)),
    fun S S' hF hsub => ?_⟩
  · rw [isCandidateSet_iff_inFpi hE, fpi_iff hN hE hS, Transversal]
    simp only [hL]
  · obtain ⟨hS, -, hF⟩ := hF
    have hF' : ¬ ∃ Z, IsListMember N Z ∧ Z ⊆ S' := fun ⟨Z, hZ, hZS⟩ => hF ⟨Z, hZ, hZS.trans hsub⟩
    exact ⟨hsub.trans hS, isRegularSet_iff_nondeg.2 (hnd S' (hsub.trans hS) ((hG S').1 hF')), hF'⟩

-- registry: C-E7P8
/-- Block sums and an identity for `X_P`: for even `N ≥ 4`, with `s_{a,b} := −c_{a,b}`
(for adjacent legs `−c_{a,a+1} = X_{a,a+2}`, the paper's `s_{a,a+1}`, by the edge convention;
the pair `{N, 1}` enters `pkGQ` as `−c_{1,N}`, equal to `−c_{N,N+1}`: `c` is symmetric, cyclic) and
`Q_U := Σ_{a<b ∈ U} s_{a,b}` (`pkGQ`): (a) `X_{i,j} = Q_{[i,j−1]}` for every chord `(i, j)`;
(b) `Σ_{b ≠ a} s_{a,b} = 0` for every leg `a`; (c) `Q_U = Q_{Uᶜ}` for every `U`, and
`Q_{all legs} = 0`; (d) `E = −Q_evens = −Q_odds`; (e) for every odd chord `P` with sides
`A = A_P`, `B = B_P`, `X_P = Σ_{t ∈ □_P} c_t + (E − Σ^{ee}_B) − Σ^{oo}_A`, where `Σ^{ee}_L`,
`Σ^{oo}_L` are the sums of `c` over the ee and the oo pairs inside `L`. -/
theorem Amplitudes.Kinematics.Mesh.block_sums {N : ℕ} (hN : 4 ≤ N) (hE : Even N) (X : ℕ × ℕ → ℚ) :
    (∀ a ∈ Icc 1 N, -mesh N X a (a + 1) = planar N X a (a + 2)) ∧
    (∀ i j : ℕ, (i, j) ∈ diagonals N → X (i, j) = pkGQ N X (Icc i (j - 1))) ∧
    (∀ a ∈ Icc 1 N, ∑ b ∈ (Icc 1 N).erase a, -mesh N X a b = 0) ∧
    ((∀ U ⊆ Icc 1 N, pkGQ N X U = pkGQ N X (Icc 1 N \ U)) ∧ pkGQ N X (Icc 1 N) = 0) ∧
    (pkGE N X = -pkGQ N X (evens (Icc 1 N)) ∧ pkGE N X = -pkGQ N X (odds (Icc 1 N))) ∧
    ∀ P ∈ oddDiagonals N, X P = ∑ t ∈ minRect N P, mesh N X t.1 t.2 +
      (pkGE N X - pkGSee N X (evenSide N P)) - pkGSoo N X (oddSide N P) := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  have hN2 : 2 ≤ N := by omega
  have hA4 := pkG_A4_all hN2 X
  have hQodd : pkGQ N X (odds (Icc 1 N)) = -pkGE N X := by
    have q := pkG_Q_F hN2 X (odds (Icc 1 N))
    have o := pkG_Soo_F hN2 X (Icc 1 N)
    have oo := pkG_Soo_all hE' X
    have l := pkL_l65 hN hE' X
    have eE : pkGE N X = ∑ t ∈ (diagonals N).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0),
        mesh N X t.1 t.2 := rfl
    linarith
  have hce : Icc 1 N \ evens (Icc 1 N) = odds (Icc 1 N) := by
    ext x; simp only [evens, odds, mem_sdiff, mem_filter, mem_Icc]; omega
  refine ⟨fun a _ => ?_, fun i j h => ?_, fun a ha => ?_, ⟨hA4, ?_⟩, ⟨?_, by rw [hQodd, neg_neg]⟩,
    fun P hP => ?_⟩
  · rw [pkR_mesh_def, pkL_pl_succ hN2, pkL_pl_succ hN2, pkL_pl_self]
    ring
  · rw [pkG_S1 hN2 X h]
    congr 1
    have := (mem_diagonals.1 h).2.2.1
    dsimp only at this
    ext x; simp only [mem_Ico, mem_Icc]; omega
  · rw [sum_erase _ (by rw [pkL_mesh_self hN2, neg_zero]), sum_neg_distrib, pkL_row (by omega),
      neg_zero]
  · have h := hA4 ∅ (empty_subset _)
    rw [sdiff_empty] at h
    rw [← h]
    simp [pkGQ]
  · rw [hA4 (evens (Icc 1 N)) (filter_subset _ _), hce, hQodd, neg_neg]
  · have hU : oddSide N P ⊆ Icc 1 N := by
      unfold oddSide; split_ifs
      · intro x hx; have := (mem_diagonals.1 (mem_filter.1 hP).1); simp only [mem_Icc] at hx ⊢
        omega
      · exact sdiff_subset
    have hXP : X P = pkGQ N X (oddSide N P) := by
      obtain ⟨i, j⟩ := P
      have hd := (mem_filter.1 hP).1
      have hd' := mem_diagonals.1 hd
      dsimp only at hd'
      have hS1 := pkG_S1 hN2 X hd
      have hI : Ico i j = Icc i (j - 1) := by ext x; simp only [mem_Ico, mem_Icc]; omega
      unfold oddSide
      split_ifs with h
      · rw [hS1, hI]
      · rw [hS1, hA4 _ (by rw [hI]; intro x hx; simp only [mem_Icc] at hx ⊢; omega), hI]
    have hcross : ∑ t ∈ minRect N P, mesh N X t.1 t.2 = pkGCross N X (oddSide N P) := by
      unfold minRect pkGCross
      rw [sum_image]
      · rfl
      · rintro ⟨e, o⟩ he ⟨e', o'⟩ he' h
        simp only [mem_coe, mem_product, evens, odds, mem_filter] at he he'
        simp only [Prod.mk.injEq] at h ⊢
        omega
    rw [hXP, pkG_A5_all hN2 X _ hU, hcross, evenSide]
    ring

-- registry: C-TQ19
/-- The parity form: for even `N ≥ 4` and a set `S` of pairs, if `E` vanishes
identically on `L_S`, then `S` contains every ee pair or every oo pair. In particular `E ≢ 0` on
`L_S` for every candidate set `S`. -/
theorem Amplitudes.Kinematics.Mesh.parity_form_nonvanishing {N : ℕ} (hN : 4 ≤ N) (hE : Even N)
    {S : Finset (ℕ × ℕ)} (hS : S ⊆ diagonals N) :
    ((∀ X : ℕ × ℕ → ℚ, OnLocus N S X → pkGE N X = 0) →
      (∀ t ∈ diagonals N, t.1 % 2 = 0 ∧ t.2 % 2 = 0 → t ∈ S) ∨
        ∀ t ∈ diagonals N, t.1 % 2 = 1 ∧ t.2 % 2 = 1 → t ∈ S) ∧
    (IsCandidateSet N S → ∃ X : ℕ × ℕ → ℚ, OnLocus N S X ∧ pkGE N X ≠ 0) := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  have first : (∀ X : ℕ × ℕ → ℚ, OnLocus N S X → pkGE N X = 0) →
      (∀ t ∈ diagonals N, t.1 % 2 = 0 ∧ t.2 % 2 = 0 → t ∈ S) ∨
        ∀ t ∈ diagonals N, t.1 % 2 = 1 ∧ t.2 % 2 = 1 → t ∈ S := by
    intro h0
    by_contra hc
    simp only [not_or, not_forall] at hc
    obtain ⟨⟨⟨e1, e2⟩, he, hee, heS⟩, ⟨⟨o1, o2⟩, ho, hoo, hoS⟩⟩ := hc
    -- the Gram point with `c = −2` on the two missing pairs and `0` on every other pair
    have hm := pkG_gB_mesh hN hE' he ho hee hoo
    have hL : OnLocus N S (p3bXs (pkLSB e1 e2 o1 o2)) := fun t ht => by
      rw [hm t (hS ht), ite_eq_right (fun e : t = (e1, e2) => heS (e ▸ ht)),
        ite_eq_right (fun e : t = (o1, o2) => hoS (e ▸ ht))]
      norm_num
    have hval : pkGE N (p3bXs (pkLSB e1 e2 o1 o2)) = -2 := by
      have eE : pkGE N (p3bXs (pkLSB e1 e2 o1 o2)) =
        ∑ t ∈ (diagonals N).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0),
          mesh N (p3bXs (pkLSB e1 e2 o1 o2)) t.1 t.2 := rfl
      rw [eE, sum_congr rfl (fun t ht => hm t (mem_filter.1 ht).1), sum_add_distrib, sum_ite_eq',
        sum_ite_eq', ite_eq_left (mem_filter.2 ⟨he, hee⟩),
        ite_eq_right (fun h => by have := (mem_filter.1 h).2; dsimp only at this; omega)]
      ring
    have := h0 _ hL
    rw [hval] at this
    norm_num at this
  refine ⟨first, fun hF => ?_⟩
  by_contra hc
  simp only [not_exists, not_and, not_not] at hc
  obtain ⟨-, -, hG⟩ := (isCandidateSet_iff_inFpi hE).1 hF
  rcases first hc with h | h
  · obtain ⟨a, b, hab, habS, ha, hb⟩ := pkG_miss_class hN hG 1 (by omega)
    exact habS (h _ hab ⟨by omega, by omega⟩)
  · obtain ⟨a, b, hab, habS, ha, hb⟩ := pkG_miss_class hN hG 0 (by omega)
    exact habS (h _ hab ⟨by omega, by omega⟩)

/-! ## The linear algebra of the mesh, flank sets, and `X_P` on the same-parity sublocus

The mesh map `𝐜 : X ↦ (c_t(X))_t` (`meshMap`) on the points `X : ℕ × ℕ → ℚ`; a point is read on
the chords only (`pkR_mesh_congrD`), and the pairs are `diagonals N`, as the chords. The
relation vector `ϱ` on the pairs and the δ-shift direction `v₀` on the chords are both
`shiftSign` (`+1` ee, `−1` oo, `0` otherwise). -/

/-- The mesh variables are additive in the point. -/
theorem mesh_add {N : ℕ} (X Y : ℕ × ℕ → ℚ) (a b : ℕ) :
    mesh N (X + Y) a b = mesh N X a b + mesh N Y a b := by
  have h := pkR_mesh_comb N X Y 1 1 a b
  simp only [one_mul] at h
  exact h

/-- The mesh variables are homogeneous in the point. -/
theorem mesh_smul {N : ℕ} (u : ℚ) (X : ℕ × ℕ → ℚ) (a b : ℕ) :
    mesh N (u • X) a b = u * mesh N X a b := by
  have h := pkR_mesh_comb N X X u 0 a b
  simp only [zero_mul, add_zero] at h
  exact h

/-- The mesh map `𝐜 : X ↦ (c_t(X))_t`, a linear map from the points `X` (functions on
pairs of labels; `c` reads them on the chords only, `pkR_mesh_congrD`) to the vectors indexed
by the pairs (`diagonals N`). -/
def meshMap (N : ℕ) : (ℕ × ℕ → ℚ) →ₗ[ℚ] (diagonals N → ℚ) where
  toFun X t := mesh N X t.1.1 t.1.2
  map_add' X Y := funext fun _ => mesh_add X Y _ _
  map_smul' c X := funext fun _ => mesh_smul c X _ _

/-- There are `N(N−3)/2` chords (and as many pairs); for `N ≤ 3` both sides are `0`. -/
theorem card_diagonals (N : ℕ) : (diagonals N).card = N * (N - 3) / 2 := by
  -- `T n`: the pairs `a + 2 ≤ b` of labels in `1..n`, one more than the chords
  have hT : ∀ n : ℕ, ((Icc 1 n ×ˢ Icc 1 n).filter (fun p => p.1 + 2 ≤ p.2)).card * 2 =
      (n - 1) * (n - 2) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      have e : (Icc 1 (n + 1) ×ˢ Icc 1 (n + 1)).filter (fun p => p.1 + 2 ≤ p.2) =
          (Icc 1 n ×ˢ Icc 1 n).filter (fun p => p.1 + 2 ≤ p.2) ∪ (Icc 1 (n - 1) ×ˢ {n + 1}) := by
        ext ⟨a, b⟩
        simp only [mem_filter, mem_product, mem_Icc, mem_union, mem_singleton]
        omega
      have hd : Disjoint ((Icc 1 n ×ˢ Icc 1 n).filter (fun p => p.1 + 2 ≤ p.2))
          (Icc 1 (n - 1) ×ˢ {n + 1}) := by
        rw [disjoint_left]
        rintro ⟨a, b⟩ h1 h2
        simp only [mem_filter, mem_product, mem_Icc, mem_singleton] at h1 h2
        omega
      rw [e, card_union_of_disjoint hd, card_product, Nat.card_Icc, card_singleton, add_mul, ih]
      rcases Nat.lt_or_ge n 2 with h | h
      · interval_cases n <;> rfl
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
        simp only [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega,
          show k + 2 + 1 - 1 = k + 2 by omega, show k + 2 + 1 - 2 = k + 1 by omega]
        ring
  rcases Nat.lt_or_ge N 3 with hN | hN
  · interval_cases N <;> decide
  have e : diagonals N = ((Icc 1 N ×ˢ Icc 1 N).filter (fun p => p.1 + 2 ≤ p.2)).erase (1, N) := by
    ext ⟨a, b⟩
    simp only [mem_diagonals, mem_erase, mem_filter, mem_product, mem_Icc, ne_eq, Prod.mk.injEq]
    omega
  have hmem : (1, N) ∈ (Icc 1 N ×ˢ Icc 1 N).filter (fun p => p.1 + 2 ≤ p.2) := by
    simp only [mem_filter, mem_product, mem_Icc]
    omega
  have h := hT N
  rw [e, card_erase_of_mem hmem]
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 3 := ⟨N - 3, by omega⟩
  have h2 : (k + 3 - 1) * (k + 3 - 2) = k * (k + 3) + 2 := by
    rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega]
    ring
  rw [h2] at h
  rw [show k + 3 - 3 = k by omega, mul_comm (k + 3) k]
  omega

/-- The kernel of the mesh map: if every mesh variable vanishes at `X`, then `X` is a multiple of
`v₀` on the chords. (Proof: the paper's Claims A and B, Claim A from the block sum `pkL_tri`.) -/
theorem mesh_kernel {N : ℕ} (hN : 4 ≤ N) {X : ℕ × ℕ → ℚ}
    (hX : ∀ t ∈ diagonals N, mesh N X t.1 t.2 = 0) :
    ∃ u : ℚ, ∀ d ∈ diagonals N, X d = u * shiftSign d := by
  have hN2 : 2 ≤ N := by omega
  set y : ℕ → ℚ := fun m => planar N X m (m + 2) with hy
  -- Claim A: a planar variable is the sum of the `y_m` along its block
  have claimA : ∀ u v : ℕ, 1 ≤ u → u ≤ v → v ≤ N → ¬ (u = 1 ∧ v = N) →
      planar N X u (v + 1) = ∑ a ∈ Ico u v, y a := by
    intro u v hu huv hv hne
    have ht := pkL_tri hN2 X hu huv hv
    have inner : ∀ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, (if u ≤ a ∧ a < b ∧ b ≤ v then mesh N X a b else 0) =
        if u ≤ a ∧ a + 1 ≤ v then mesh N X a (a + 1) else 0 := by
      intro a ha
      rw [sum_eq_single (a + 1)]
      · by_cases h : u ≤ a ∧ a + 1 ≤ v
        · rw [ite_eq_left (by omega), ite_eq_left h]
        · rw [ite_eq_right (by omega), ite_eq_right h]
      · intro b _ hb
        split_ifs with h
        · exact hX (a, b) (mem_diagonals.2 (by simp only [mem_Icc] at ha; dsimp only; omega))
        · rfl
      · intro h
        rw [ite_eq_right (fun h' => h (mem_Icc.2 ⟨by omega, by omega⟩))]
    rw [sum_congr rfl inner, ← sum_filter] at ht
    have hf : (Icc 1 N).filter (fun a => u ≤ a ∧ a + 1 ≤ v) = Ico u v := by
      ext a; simp only [mem_filter, mem_Icc, mem_Ico]; omega
    rw [hf] at ht
    have hs : ∀ a ∈ Ico u v, mesh N X a (a + 1) = -y a := fun a _ => by
      rw [hy, pkR_mesh_def, pkL_pl_succ hN2, pkL_pl_succ hN2, pkL_pl_self]
      ring
    rw [sum_congr rfl hs, sum_neg_distrib] at ht
    linarith
  -- the chord `(1, a+1)` read from both ends: `Σ_{m < a} y_m = Σ_{a < m < N} y_m`
  have wrap : ∀ a, 1 ≤ a → a ≤ N - 1 → ∑ m ∈ Ico 1 a, y m = ∑ m ∈ Ico (a + 1) N, y m := by
    intro a ha1 ha2
    have h1 := claimA 1 a le_rfl ha1 (by omega) (by omega)
    have h2 := claimA (a + 1) N (by omega) (by omega) le_rfl (by omega)
    rw [← h1, ← h2, ChainSlice.planar_congr X (i := a + 1) (j := N + 1) (i' := a + 1) (j' := 1) rfl
      (pkL_vtx_N1 N), ChainSlice.planar_comm]
  -- Claim B: consecutive `y` cancel
  have claimB : ∀ a, 2 ≤ a → a ≤ N - 1 → y a = -y (a - 1) := by
    intro a ha1 ha2
    have h1 := wrap a (by omega) ha2
    have h2 := wrap (a - 1) (by omega) (by omega)
    rw [show a - 1 + 1 = a by omega] at h2
    rw [show a = a - 1 + 1 by omega, sum_Ico_succ_top (by omega)] at h1
    rw [sum_eq_sum_Ico_succ_bot (show a < N by omega)] at h2
    rw [show a - 1 + 1 = a by omega] at h1
    linarith
  -- so `y_m = ±y_1`, with the sign of the parity of `m`
  have alt : ∀ m, 1 ≤ m → m ≤ N - 1 → y m = (if m % 2 = 1 then 1 else -1) * y 1 := by
    intro m hm1 hm2
    induction m with
    | zero => omega
    | succ m ih =>
      rcases Nat.lt_or_ge m 1 with h | h
      · rw [show m = 0 by omega]; simp
      · rw [claimB (m + 1) (by omega) hm2, show m + 1 - 1 = m by omega, ih h (by omega)]
        split_ifs <;> first | omega | ring
  -- a block sum of alternating terms
  have block : ∀ i k, 1 ≤ i → i ≤ k → k ≤ N - 1 →
      ∑ m ∈ Ico i k, y m = if (k - i) % 2 = 0 then 0 else y i := by
    intro i k hi hik hk
    induction k with
    | zero => omega
    | succ k ih =>
      rcases Nat.lt_or_ge k i with h | h
      · rw [show k + 1 = i by omega, Ico_self, sum_empty, Nat.sub_self]; rfl
      · rw [sum_Ico_succ_top h, ih h (by omega), alt k (by omega) (by omega),
          alt i hi (by omega)]
        split_ifs <;> first | omega | ring
  refine ⟨-y 1, fun d hd => ?_⟩
  obtain ⟨i, j⟩ := d
  have h := mem_diagonals.1 hd
  dsimp only at h
  have hA := claimA i (j - 1) h.1 (by omega) (by omega) (by omega)
  rw [show j - 1 + 1 = j by omega, planar_eq_X X h.1 h.2.2.1 h.2.1 h.2.2.2,
    block i (j - 1) h.1 (by omega) (by omega), alt i h.1 (by omega)] at hA
  rw [hA]
  unfold shiftSign
  dsimp only
  split_ifs <;> first | omega | push_cast; ring

/-- `Σ_t ϱ_t y_t = Σ_ee y − Σ_oo y`, with `ϱ = shiftSign` on the pairs. -/
theorem sum_shiftSign_mul {N : ℕ} (y : ℕ × ℕ → ℚ) :
    ∑ t ∈ diagonals N, (shiftSign t : ℚ) * y t =
      ∑ t ∈ (diagonals N).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0), y t -
        ∑ t ∈ (diagonals N).filter (fun p => p.1 % 2 = 1 ∧ p.2 % 2 = 1), y t := by
  rw [sum_filter, sum_filter, ← sum_sub_distrib]
  refine sum_congr rfl fun t _ => ?_
  unfold shiftSign
  split_ifs <;> first | omega | (push_cast; ring)

-- registry: C-SFR3
/-- Momentum conservation: for even `N ≥ 4` and the mesh map
`𝐜 : X ↦ (c_t(X))_t`, (i) `Σ_ee c_t = Σ_oo c_t` as linear forms; (ii) `ker 𝐜 = ℚ v₀` (on the
chords, `v₀ = shiftSign`); (iii) `rank 𝐜 = N(N−3)/2 − 1`, and every relation `Σ_t λ_t c_t = 0` has
`λ = κϱ`, with `ϱ_t = +1` on ee pairs, `−1` on oo pairs and `0` on opposite-parity pairs
(`ϱ = shiftSign` on the pairs); (iv) `im 𝐜 = {y : Σ_ee y = Σ_oo y}`. -/
theorem Amplitudes.Kinematics.Mesh.momentum_conservation_relation {N : ℕ} (hN : 4 ≤ N)
    (hE : Even N) :
    (∀ X : ℕ × ℕ → ℚ,
      ∑ t ∈ (diagonals N).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0), mesh N X t.1 t.2 =
        ∑ t ∈ (diagonals N).filter (fun p => p.1 % 2 = 1 ∧ p.2 % 2 = 1), mesh N X t.1 t.2) ∧
    (∀ X : ℕ × ℕ → ℚ, (∀ t ∈ diagonals N, mesh N X t.1 t.2 = 0) ↔
      ∃ u : ℚ, ∀ d ∈ diagonals N, X d = u * shiftSign d) ∧
    (Module.finrank ℚ (LinearMap.range (meshMap N)) = N * (N - 3) / 2 - 1 ∧
      ∀ lam : ℕ × ℕ → ℚ, (∀ X : ℕ × ℕ → ℚ, ∑ t ∈ diagonals N, lam t * mesh N X t.1 t.2 = 0) →
        ∃ κ : ℚ, ∀ t ∈ diagonals N, lam t = κ * shiftSign t) ∧
    ∀ y : ℕ × ℕ → ℚ, (∃ X : ℕ × ℕ → ℚ, ∀ t ∈ diagonals N, mesh N X t.1 t.2 = y t) ↔
      ∑ t ∈ (diagonals N).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0), y t =
        ∑ t ∈ (diagonals N).filter (fun p => p.1 % 2 = 1 ∧ p.2 % 2 = 1), y t := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  have hi := lemma65 (K := ℚ) hN hE
  -- (ii)
  have hker : ∀ X : ℕ × ℕ → ℚ, (∀ t ∈ diagonals N, mesh N X t.1 t.2 = 0) ↔
      ∃ u : ℚ, ∀ d ∈ diagonals N, X d = u * shiftSign d := by
    intro X
    refine ⟨mesh_kernel hN, fun ⟨u, hu⟩ t ht => ?_⟩
    have h := mem_diagonals.1 ht
    rw [pkR_mesh_congrD hu]
    refine (mesh_smul u (fun d => (shiftSign d : ℚ)) t.1 t.2).trans ?_
    rw [mesh_shiftSign hN hE' h.1 h.2.2.1 (by omega), mul_zero]
  -- (iii), rank, and (iv): rank–nullity for `𝐜` on the chords, `ker 𝐜 = ℚ v₀`
  let ext : (diagonals N → ℚ) →ₗ[ℚ] (ℕ × ℕ → ℚ) :=
    { toFun := fun v d => if h : d ∈ diagonals N then v ⟨d, h⟩ else 0
      map_add' := fun v w => by
        funext d
        simp only [Pi.add_apply]
        split_ifs <;> simp
      map_smul' := fun c v => by
        funext d
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        split_ifs <;> simp }
  have hext : ∀ v : diagonals N → ℚ, ∀ t : diagonals N, ext v t.1 = v t := fun v t => by
    simp [ext, t.2]
  have hrange : LinearMap.range ((meshMap N).comp ext) = LinearMap.range (meshMap N) := by
    refine le_antisymm (LinearMap.range_comp_le_range _ _) ?_
    rintro _ ⟨X, rfl⟩
    refine ⟨fun t => X t.1, funext fun t => ?_⟩
    exact pkR_mesh_congrD (fun d hd => hext (fun t => X t.1) ⟨d, hd⟩) _ _
  let v0 : diagonals N → ℚ := fun t => shiftSign t.1
  have h24 : ((2, 4) : ℕ × ℕ) ∈ diagonals N := mem_diagonals.2 (by dsimp only; omega)
  have h13 : ((1, 3) : ℕ × ℕ) ∈ diagonals N := mem_diagonals.2 (by dsimp only; omega)
  have hv0 : v0 ≠ 0 := fun h => by
    have := congrFun h ⟨(2, 4), h24⟩
    simp [v0, shiftSign] at this
  have hkerc : LinearMap.ker ((meshMap N).comp ext) = ℚ ∙ v0 := by
    ext v
    rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
    constructor
    · intro hv
      obtain ⟨u, hu⟩ := mesh_kernel hN (X := ext v) (fun t ht => congrFun hv ⟨t, ht⟩)
      refine ⟨u, funext fun t => ?_⟩
      rw [← hext v t, hu t.1 t.2]
      rfl
    · rintro ⟨u, rfl⟩
      funext t
      refine ((hker (ext (u • v0))).2 ⟨u, fun d hd => ?_⟩) t.1 t.2
      rw [hext (u • v0) ⟨d, hd⟩]
      rfl
  have hcard : Module.finrank ℚ (diagonals N → ℚ) = (diagonals N).card := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have hdim : Module.finrank ℚ (LinearMap.range (meshMap N)) = (diagonals N).card - 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker ((meshMap N).comp ext)
    rw [hrange, hkerc, finrank_span_singleton hv0, hcard] at h
    omega
  let φ : (diagonals N → ℚ) →ₗ[ℚ] ℚ :=
    { toFun := fun v => ∑ t, (shiftSign t.1 : ℚ) * v t
      map_add' := fun v w => by simp only [Pi.add_apply, mul_add, sum_add_distrib]
      map_smul' := fun c v => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
        exact sum_congr rfl fun _ _ => by ring }
  have hφ : ∀ y : ℕ × ℕ → ℚ, φ (fun t => y t.1) =
      ∑ t ∈ (diagonals N).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0), y t -
        ∑ t ∈ (diagonals N).filter (fun p => p.1 % 2 = 1 ∧ p.2 % 2 = 1), y t := fun y => by
    rw [← sum_shiftSign_mul]
    exact sum_coe_sort (diagonals N) (fun t => (shiftSign t : ℚ) * y t)
  have hle : LinearMap.range (meshMap N) ≤ LinearMap.ker φ := by
    rintro _ ⟨X, rfl⟩
    rw [LinearMap.mem_ker]
    exact (hφ fun t => mesh N X t.1 t.2).trans (by rw [hi X, sub_self])
  have hne : LinearMap.ker φ ≠ ⊤ := fun h => by
    have h1 : φ (fun t => if t.1 = (2, 4) then 1 else 0) = 0 := by
      rw [← LinearMap.mem_ker, h]
      trivial
    rw [hφ fun t => if t = (2, 4) then 1 else 0, sum_ite_eq', sum_ite_eq',
      ite_eq_left (mem_filter.2 ⟨h24, by norm_num⟩), ite_eq_right (fun h => by
        have := (mem_filter.1 h).2; dsimp only at this; omega)] at h1
    norm_num at h1
  have heq : LinearMap.range (meshMap N) = LinearMap.ker φ := by
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    have := Submodule.finrank_lt hne
    rw [hcard] at this
    omega
  have hiv : ∀ y : ℕ × ℕ → ℚ, (∃ X : ℕ × ℕ → ℚ, ∀ t ∈ diagonals N, mesh N X t.1 t.2 = y t) ↔
      ∑ t ∈ (diagonals N).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0), y t =
        ∑ t ∈ (diagonals N).filter (fun p => p.1 % 2 = 1 ∧ p.2 % 2 = 1), y t := by
    intro y
    constructor
    · rintro ⟨X, hX⟩
      rw [← sum_congr rfl fun t ht => hX t (mem_filter.1 ht).1,
        ← sum_congr rfl fun t ht => hX t (mem_filter.1 ht).1]
      exact hi X
    · intro hy
      have hmem : (fun t : diagonals N => y t.1) ∈ LinearMap.ker φ := by
        rw [LinearMap.mem_ker, hφ, hy, sub_self]
      rw [← heq] at hmem
      obtain ⟨X, hX⟩ := hmem
      exact ⟨X, fun t ht => congrFun hX ⟨t, ht⟩⟩
  refine ⟨hi, hker, ⟨?_, fun lam hlam => ?_⟩, hiv⟩
  · rw [hdim, card_diagonals N]
  -- the relations, tested on vectors of the image
  have test : ∀ y : ℕ × ℕ → ℚ,
      ∑ t ∈ (diagonals N).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0), y t =
        ∑ t ∈ (diagonals N).filter (fun p => p.1 % 2 = 1 ∧ p.2 % 2 = 1), y t →
      ∑ t ∈ diagonals N, lam t * y t = 0 := by
    intro y hy
    obtain ⟨X, hX⟩ := (hiv y).2 hy
    rw [← hlam X]
    exact sum_congr rfl fun t ht => by rw [hX t ht]
  have hmix : ∀ t ∈ diagonals N, ¬ (t.1 % 2 = 0 ∧ t.2 % 2 = 0) → ¬ (t.1 % 2 = 1 ∧ t.2 % 2 = 1) →
      lam t = 0 := by
    intro t ht h1 h2
    have m1 : t ∉ (diagonals N).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0) := fun h =>
      h1 (mem_filter.1 h).2
    have m2 : t ∉ (diagonals N).filter (fun p => p.1 % 2 = 1 ∧ p.2 % 2 = 1) := fun h =>
      h2 (mem_filter.1 h).2
    have h := test (fun s => if s = t then 1 else 0) (by
      rw [sum_ite_eq', sum_ite_eq', ite_eq_right m1, ite_eq_right m2])
    simpa only [mul_ite, mul_one, mul_zero, sum_ite_eq', ite_eq_left ht] using h
  have hpair : ∀ e ∈ diagonals N, ∀ o ∈ diagonals N, (e.1 % 2 = 0 ∧ e.2 % 2 = 0) →
      (o.1 % 2 = 1 ∧ o.2 % 2 = 1) → lam e + lam o = 0 := by
    intro e he o ho hee hoo
    have m1 : e ∈ (diagonals N).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0) :=
      mem_filter.2 ⟨he, hee⟩
    have m2 : o ∉ (diagonals N).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0) := fun h => by
      have := (mem_filter.1 h).2; omega
    have m3 : e ∉ (diagonals N).filter (fun p => p.1 % 2 = 1 ∧ p.2 % 2 = 1) := fun h => by
      have := (mem_filter.1 h).2; omega
    have m4 : o ∈ (diagonals N).filter (fun p => p.1 % 2 = 1 ∧ p.2 % 2 = 1) :=
      mem_filter.2 ⟨ho, hoo⟩
    have h := test (fun s => (if s = e then 1 else 0) + (if s = o then 1 else 0)) (by
      rw [sum_add_distrib, sum_add_distrib, sum_ite_eq', sum_ite_eq', sum_ite_eq', sum_ite_eq',
        ite_eq_left m1, ite_eq_right m2, ite_eq_right m3, ite_eq_left m4, add_comm])
    simpa only [mul_add, mul_ite, mul_one, mul_zero, sum_add_distrib, sum_ite_eq', ite_eq_left he,
      ite_eq_left ho] using h
  refine ⟨lam (2, 4), fun t ht => ?_⟩
  have h2413 := hpair (2, 4) h24 (1, 3) h13 (by norm_num) (by norm_num)
  unfold shiftSign
  split_ifs with h1 h2
  · have := hpair t ht (1, 3) h13 h1 (by norm_num)
    push_cast; linarith
  · have := hpair (2, 4) h24 t ht (by norm_num) h2
    push_cast; linarith
  · rw [hmix t ht h1 h2]
    push_cast; ring

/-- A linear form that vanishes on `L_S` is a combination of the `c_t`, `t ∈ S` (finite-dimensional
duality, Mathlib's `mem_span_of_iInf_ker_le_ker`). -/
theorem exists_mesh_combination_of_vanishing {N : ℕ} {S : Finset (ℕ × ℕ)} (hS : S ⊆ diagonals N)
    (K : (ℕ × ℕ → ℚ) →ₗ[ℚ] ℚ) (hK : ∀ X : ℕ × ℕ → ℚ, OnLocus N S X → K X = 0) :
    ∃ φ : ℕ × ℕ → ℚ, ∀ X : ℕ × ℕ → ℚ, K X = ∑ t ∈ S, φ t * mesh N X t.1 t.2 := by
  let L : S → (ℕ × ℕ → ℚ) →ₗ[ℚ] ℚ := fun t => (LinearMap.proj ⟨t.1, hS t.2⟩).comp (meshMap N)
  have hL : ∀ t X, L t X = mesh N X t.1.1 t.1.2 := fun _ _ => rfl
  have h : ⨅ t, LinearMap.ker (L t) ≤ LinearMap.ker K := by
    intro X hX
    rw [Submodule.mem_iInf] at hX
    rw [LinearMap.mem_ker]
    exact hK X fun t ht => by rw [← hL ⟨t, ht⟩]; exact hX ⟨t, ht⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).1 (mem_span_of_iInf_ker_le_ker h)
  refine ⟨fun t => if h : t ∈ S then c ⟨t, h⟩ else 0, fun X => ?_⟩
  rw [← hc, LinearMap.sum_apply,
    ← sum_coe_sort S (fun t => (if h : t ∈ S then c ⟨t, h⟩ else 0) * mesh N X t.1 t.2)]
  refine sum_congr rfl fun t _ => ?_
  rw [LinearMap.smul_apply, hL, dite_eq_left t.2, smul_eq_mul]

-- registry: C-RDPQ
/-- Coordinates on a locus: for even `N ≥ 4` and every set `S` of pairs, the map
`X ↦ (y_t(X))_{t ∈ M}` (`y_t = c_t|_{L_S}`) sends `L_S` into and onto
`𝕐_S = {y : Σ_{M_e} y = Σ_{M_o} y}`, with kernel `ℚ v₀` (`v₀ = shiftSign` on the chords); a linear
form `f` on the planar variables (a coefficient vector `α` on the chords) vanishes on `L_S` iff
`f ∈ span{c_t : t ∈ S}`; and if `f = Σ_t φ_t c_t`, it vanishes on `L_S` iff `φ − κϱ` is supported
on `S` for some `κ` (`ϱ = shiftSign` on the pairs). -/
theorem Amplitudes.Kinematics.Mesh.locus_coordinates {N : ℕ} (hN : 4 ≤ N) (hE : Even N)
    {S : Finset (ℕ × ℕ)} (hS : S ⊆ diagonals N) :
    (∀ X : ℕ × ℕ → ℚ, OnLocus N S X →
      ∑ t ∈ Mee N S, mesh N X t.1 t.2 = ∑ t ∈ Moo N S, mesh N X t.1 t.2) ∧
    (∀ y : ℕ × ℕ → ℚ, ∑ t ∈ Mee N S, y t = ∑ t ∈ Moo N S, y t →
      ∃ X : ℕ × ℕ → ℚ, OnLocus N S X ∧ ∀ t ∈ missing N S, mesh N X t.1 t.2 = y t) ∧
    (∀ X : ℕ × ℕ → ℚ, (OnLocus N S X ∧ ∀ t ∈ missing N S, mesh N X t.1 t.2 = 0) ↔
      ∃ u : ℚ, ∀ d ∈ diagonals N, X d = u * shiftSign d) ∧
    (∀ α : ℕ × ℕ → ℚ, (∀ X : ℕ × ℕ → ℚ, OnLocus N S X → ∑ d ∈ diagonals N, α d * X d = 0) ↔
      ∃ φ : ℕ × ℕ → ℚ, ∀ X : ℕ × ℕ → ℚ,
        ∑ d ∈ diagonals N, α d * X d = ∑ t ∈ S, φ t * mesh N X t.1 t.2) ∧
    ∀ φ : ℕ × ℕ → ℚ,
      (∀ X : ℕ × ℕ → ℚ, OnLocus N S X → ∑ t ∈ diagonals N, φ t * mesh N X t.1 t.2 = 0) ↔
        ∃ κ : ℚ, ∀ t ∈ diagonals N, t ∉ S → φ t = κ * shiftSign t := by
  obtain ⟨hi, hker, ⟨-, hrel⟩, hiv⟩ := momentum_conservation_relation hN hE
  -- a sum over the pairs of one class reduces to the missing ones when `f` vanishes on `S`
  have split : ∀ (q : ℕ × ℕ → Prop) [DecidablePred q] (f : ℕ × ℕ → ℚ), (∀ t ∈ S, f t = 0) →
      ∑ t ∈ (diagonals N).filter q, f t = ∑ t ∈ (missing N S).filter q, f t := by
    intro q _ f hf
    refine (sum_subset (filter_subset_filter _ sdiff_subset) fun t ht hnt => hf t ?_).symm
    by_contra h
    exact hnt (mem_filter.2 ⟨mem_sdiff.2 ⟨(mem_filter.1 ht).1, h⟩, (mem_filter.1 ht).2⟩)
  have hMee : ∀ f : ℕ × ℕ → ℚ, ∑ t ∈ Mee N S, f t =
      ∑ t ∈ (missing N S).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0), f t := fun _ => rfl
  have hMoo : ∀ f : ℕ × ℕ → ℚ, ∑ t ∈ Moo N S, f t =
      ∑ t ∈ (missing N S).filter (fun p => p.1 % 2 = 1 ∧ p.2 % 2 = 1), f t := fun _ => rfl
  have hform : ∀ φ : ℕ × ℕ → ℚ, ∃ K : (ℕ × ℕ → ℚ) →ₗ[ℚ] ℚ,
      ∀ X, K X = ∑ t ∈ diagonals N, φ t * mesh N X t.1 t.2 := fun φ =>
    ⟨{ toFun := fun X => ∑ t ∈ diagonals N, φ t * mesh N X t.1 t.2
       map_add' := fun X Y => by simp only [mesh_add, mul_add, sum_add_distrib]
       map_smul' := fun c X => by
         simp only [RingHom.id_apply, smul_eq_mul, mul_sum]
         exact sum_congr rfl fun t _ => by
           rw [mesh_smul]
           ring }, fun _ => rfl⟩
  refine ⟨fun X hX => ?_, fun y hy => ?_, fun X => ?_, fun α => ⟨fun h => ?_, ?_⟩,
    fun φ => ⟨?_, ?_⟩⟩
  · -- into `𝕐_S`
    rw [hMee, hMoo, ← split _ _ hX, ← split _ _ hX]
    exact hi X
  · -- onto `𝕐_S`
    set y' : ℕ × ℕ → ℚ := fun t => if t ∈ S then 0 else y t with hy'
    have hy0 : ∀ t ∈ S, y' t = 0 := fun t ht => by simp only [hy', ht, ite_true]
    have hyM : ∀ t ∈ missing N S, y' t = y t := fun t ht => by
      simp only [hy', (mem_sdiff.1 ht).2, ite_false]
    obtain ⟨X, hX⟩ := (hiv y').2 (by
      rw [split _ _ hy0, split _ _ hy0, sum_congr rfl fun t ht => hyM t (mem_filter.1 ht).1,
        sum_congr rfl fun t ht => hyM t (mem_filter.1 ht).1, ← hMee, ← hMoo]
      exact hy)
    exact ⟨X, fun t ht => by rw [hX t (hS ht), hy0 t ht],
      fun t ht => by rw [hX t (mem_sdiff.1 ht).1, hyM t ht]⟩
  · -- the kernel
    rw [← hker]
    refine ⟨fun ⟨hL, hM⟩ t ht => ?_, fun h => ⟨fun t ht => h t (hS ht), fun t ht => h t
      (mem_sdiff.1 ht).1⟩⟩
    by_cases htS : t ∈ S
    · exact hL t htS
    · exact hM t (mem_sdiff.2 ⟨ht, htS⟩)
  · -- a vanishing linear form is in the span
    let K : (ℕ × ℕ → ℚ) →ₗ[ℚ] ℚ :=
      { toFun := fun X => ∑ d ∈ diagonals N, α d * X d
        map_add' := fun X Y => by simp only [Pi.add_apply, mul_add, sum_add_distrib]
        map_smul' := fun c X => by
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
          exact sum_congr rfl fun _ _ => by ring }
    exact exists_mesh_combination_of_vanishing hS K h
  · rintro ⟨φ, hφ⟩ X hX
    rw [hφ X]
    exact sum_eq_zero fun t ht => by rw [hX t ht, mul_zero]
  · -- the representations: `φ − ψ·1_S` is a relation, hence `κϱ`
    intro h
    obtain ⟨K, hK⟩ := hform φ
    obtain ⟨ψ, hψ⟩ := exists_mesh_combination_of_vanishing hS K fun X hX => by rw [hK]; exact h X hX
    obtain ⟨κ, hκ⟩ := hrel (fun t => φ t - if t ∈ S then ψ t else 0) fun X => by
      simp only [sub_mul, ite_mul, zero_mul, sum_sub_distrib]
      rw [sum_ite_mem, inter_eq_right.2 hS, ← hψ, hK, sub_self]
    exact ⟨κ, fun t ht htS => by
      have := hκ t ht
      rwa [ite_eq_right htS, sub_zero] at this⟩
  · rintro ⟨κ, hκ⟩ X hX
    have hrho : ∑ t ∈ diagonals N, (shiftSign t : ℚ) * mesh N X t.1 t.2 = 0 := by
      rw [sum_shiftSign_mul (fun t => mesh N X t.1 t.2), hi X, sub_self]
    have e : ∀ t ∈ diagonals N, φ t * mesh N X t.1 t.2 =
        κ * ((shiftSign t : ℚ) * mesh N X t.1 t.2) := fun t ht => by
      by_cases htS : t ∈ S
      · rw [hX t htS]; ring
      · rw [hκ t ht htS]; ring
    rw [sum_congr rfl e, ← mul_sum, hrho, mul_zero]

-- registry: C-PEQM
/-- Mesh variables omitting a same-parity pair are linearly independent (the identities of the
forms, (iv), first half): for even `N ≥ 4`, a set `T` of pairs and a same-parity pair `t₀ ∉ T`, a
relation `Σ_{t ∈ T} λ_t c_t = 0` has `λ = 0` on `T` (from the relations clause of
`momentum_conservation_relation`: `λ = κϱ`, and `ϱ_{t₀} = ±1`). -/
theorem Amplitudes.Kinematics.Mesh.mesh_independent_of_omits_same_parity {N : ℕ} (hN : 4 ≤ N)
    (hE : Even N) {T : Finset (ℕ × ℕ)} (hT : T ⊆ diagonals N) {t₀ : ℕ × ℕ} (ht₀ : t₀ ∈ diagonals N)
    (ht₀T : t₀ ∉ T) (hpar : t₀.1 % 2 = t₀.2 % 2) (lam : ℕ × ℕ → ℚ)
    (hrel : ∀ X : ℕ × ℕ → ℚ, ∑ t ∈ T, lam t * mesh N X t.1 t.2 = 0) : ∀ t ∈ T, lam t = 0 := by
  classical
  let lam' : ℕ × ℕ → ℚ := fun t => if t ∈ T then lam t else 0
  have h' : ∀ X : ℕ × ℕ → ℚ, ∑ t ∈ diagonals N, lam' t * mesh N X t.1 t.2 = 0 := by
    intro X
    rw [← hrel X, ← sum_subset hT (fun t _ ht => by simp [lam', ht])]
    exact sum_congr rfl fun t ht => by simp [lam', ht]
  obtain ⟨κ, hκ⟩ := (momentum_conservation_relation hN hE).2.2.1.2 lam' h'
  have h0 : κ = 0 := by
    have := hκ t₀ ht₀
    simp only [lam', ht₀T, ↓reduceIte] at this
    have hs : (shiftSign t₀ : ℚ) ≠ 0 := by
      unfold shiftSign
      split_ifs <;> first | omega | norm_num
    exact (mul_eq_zero.1 this.symm).resolve_right hs
  intro t ht
  have := hκ t (hT ht)
  simpa [lam', ht, h0] using this

-- registry: C-PEQM
/-- Rows 1 and 2 (the identities of the forms, (iv), second half): for even `N ≥ 6`, the pairs
`{1, b}` of row 1 and `{2, b}` of row 2 are disjoint and together omit the oo pair `{3, 5}`, so
`span(row 1) ∩ span(row 2) = 0`. -/
theorem Amplitudes.Kinematics.Mesh.rows_one_two_span_meet {N : ℕ} (hN : 6 ≤ N) (hE : Even N) :
    Disjoint ((Icc 3 (N - 1)).image (fun b => ((1 : ℕ), b)))
      ((Icc 4 N).image (fun b => ((2 : ℕ), b))) ∧
    ((3 : ℕ), (5 : ℕ)) ∈ diagonals N ∧
    ((3 : ℕ), (5 : ℕ)) ∉ (Icc 3 (N - 1)).image (fun b => ((1 : ℕ), b)) ∪
      (Icc 4 N).image (fun b => ((2 : ℕ), b)) ∧
    ∀ α β : ℕ → ℚ, (∀ X : ℕ × ℕ → ℚ, ∑ b ∈ Icc 3 (N - 1), α b * mesh N X 1 b =
      ∑ b ∈ Icc 4 N, β b * mesh N X 2 b) →
    ∀ X : ℕ × ℕ → ℚ, ∑ b ∈ Icc 3 (N - 1), α b * mesh N X 1 b = 0 := by
  classical
  let T : Finset (ℕ × ℕ) :=
    (Icc 3 (N - 1)).image (fun b => (1, b)) ∪ (Icc 4 N).image (fun b => (2, b))
  have hT : T ⊆ diagonals N := by
    intro t ht
    simp only [T, mem_union, mem_image, mem_Icc] at ht
    rcases ht with ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩ <;> exact mem_diagonals.2 (by omega)
  have hdisj : Disjoint ((Icc 3 (N - 1)).image (fun b => ((1 : ℕ), b)))
      ((Icc 4 N).image (fun b => ((2 : ℕ), b))) := by
    rw [disjoint_left]; intro t h1 h2
    simp only [mem_image] at h1 h2
    obtain ⟨b, -, rfl⟩ := h1; obtain ⟨b', -, e⟩ := h2
    simp at e
  have h35 : ((3 : ℕ), (5 : ℕ)) ∈ diagonals N := mem_diagonals.2 (by omega)
  have h35T : ((3 : ℕ), (5 : ℕ)) ∉ T := by
    simp only [T, mem_union, mem_image, not_or, not_exists, not_and]
    exact ⟨fun b _ e => by simp at e, fun b _ e => by simp at e⟩
  refine ⟨hdisj, h35, h35T, fun α β h => ?_⟩
  let lam : ℕ × ℕ → ℚ := fun t => if t.1 = 1 then α t.2 else -β t.2
  have hrel : ∀ X : ℕ × ℕ → ℚ, ∑ t ∈ T, lam t * mesh N X t.1 t.2 = 0 := by
    intro X
    rw [sum_union hdisj, sum_image (by intro a _ b _ e; simpa using e),
      sum_image (by intro a _ b _ e; simpa using e)]
    simp only [lam, ↓reduceIte, show ¬ ((2 : ℕ) = 1) from by decide, neg_mul, sum_neg_distrib,
      h X, add_neg_cancel]
  have hz := mesh_independent_of_omits_same_parity (by omega) hE hT h35 h35T (by decide) lam hrel
  intro X
  refine sum_eq_zero fun b hb => ?_
  have := hz (1, b) (mem_union_left _ (mem_image_of_mem _ hb))
  simp only [lam, ↓reduceIte] at this
  rw [this, zero_mul]

-- registry: C-PEQM
/-- The identities of the forms: for even `N ≥ 4`, as linear forms, with
`s_{ab} = −c_{a,b}` (`−c_{a,a+1} = X_{a,a+2}` on adjacent legs) and `Q_U = Σ_{a<b ∈ U} s_{ab}`:
(i) `X_{i,j} = Q_{[i,j−1]}`; (ii) `Σ_{b ≠ a} s_{ab} = 0` for every leg `a`; (iii) `Q_U = Q_{Uᶜ}`
and `Q_all = 0`; (iv) any set of mesh variables that omits at least one same-parity pair is
linearly independent, and for `N ≥ 6` the pairs of row 1 and of row 2 are disjoint, together omit
`{3, 5}`, and `span(row 1) ∩ span(row 2) = 0`. (i)–(iii) are (a)–(c) of `block_sums`. -/
theorem Amplitudes.Kinematics.Mesh.form_identities {N : ℕ} (hN : 4 ≤ N) (hE : Even N) :
    (∀ X : ℕ × ℕ → ℚ, ∀ a ∈ Icc 1 N, -mesh N X a (a + 1) = planar N X a (a + 2)) ∧
    (∀ X : ℕ × ℕ → ℚ, ∀ i j : ℕ, (i, j) ∈ diagonals N → X (i, j) = pkGQ N X (Icc i (j - 1))) ∧
    (∀ X : ℕ × ℕ → ℚ, ∀ a ∈ Icc 1 N, ∑ b ∈ (Icc 1 N).erase a, -mesh N X a b = 0) ∧
    (∀ X : ℕ × ℕ → ℚ, (∀ U ⊆ Icc 1 N, pkGQ N X U = pkGQ N X (Icc 1 N \ U)) ∧
      pkGQ N X (Icc 1 N) = 0) ∧
    (∀ T ⊆ diagonals N, (∃ t₀ ∈ diagonals N, t₀ ∉ T ∧ t₀.1 % 2 = t₀.2 % 2) →
      ∀ lam : ℕ × ℕ → ℚ, (∀ X : ℕ × ℕ → ℚ, ∑ t ∈ T, lam t * mesh N X t.1 t.2 = 0) →
        ∀ t ∈ T, lam t = 0) ∧
    (6 ≤ N →
      Disjoint ((Icc 3 (N - 1)).image (fun b => ((1 : ℕ), b)))
        ((Icc 4 N).image (fun b => ((2 : ℕ), b))) ∧
      ((3 : ℕ), (5 : ℕ)) ∈ diagonals N ∧
      ((3 : ℕ), (5 : ℕ)) ∉ (Icc 3 (N - 1)).image (fun b => ((1 : ℕ), b)) ∪
        (Icc 4 N).image (fun b => ((2 : ℕ), b)) ∧
      ∀ α β : ℕ → ℚ, (∀ X : ℕ × ℕ → ℚ, ∑ b ∈ Icc 3 (N - 1), α b * mesh N X 1 b =
        ∑ b ∈ Icc 4 N, β b * mesh N X 2 b) →
      ∀ X : ℕ × ℕ → ℚ, ∑ b ∈ Icc 3 (N - 1), α b * mesh N X 1 b = 0) :=
  ⟨fun X => (block_sums hN hE X).1, fun X => (block_sums hN hE X).2.1,
    fun X => (block_sums hN hE X).2.2.1, fun X => (block_sums hN hE X).2.2.2.1,
    fun _T hT ⟨_t₀, ht₀, ht₀T, hpar⟩ lam hrel =>
      mesh_independent_of_omits_same_parity hN hE hT ht₀ ht₀T hpar lam hrel,
    fun h6 => rows_one_two_span_meet h6 hE⟩

-- registry: C-EXFS
/-- The sides of an odd chord, the claims of their definition: for even `N`, an odd chord `P`
divides the legs into two arcs of odd size, each with at least three legs (the odd-ended side `A_P`
and the even-ended side `B_P`), and a chord is determined by its odd-ended side. -/
theorem Combinatorics.Polygons.odd_chord_sides {N : ℕ} (hE : Even N) :
    (∀ P ∈ oddDiagonals N,
      (oddSide N P).card % 2 = 1 ∧ 3 ≤ (oddSide N P).card ∧
      (evenSide N P).card % 2 = 1 ∧ 3 ≤ (evenSide N P).card) ∧
    ∀ P ∈ oddDiagonals N, ∀ Q ∈ oddDiagonals N, oddSide N P = oddSide N Q → P = Q := by
  have hE : N % 2 = 0 := Nat.even_iff.1 hE
  refine ⟨fun P hP => ?_, fun P hP Q hQ h => pkR_d2_eq_of_head hP hQ h⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := pkCo_mem_oddDiagonals.1 hP
  have hsub : Icc P.1 (P.2 - 1) ⊆ Icc 1 N := fun x hx => by
    simp only [mem_Icc] at hx ⊢; omega
  have hc : (Icc P.1 (P.2 - 1)).card = P.2 - P.1 := by rw [Nat.card_Icc]; omega
  have hcN : (Icc 1 N).card = N := by rw [Nat.card_Icc]; omega
  have hodd : (oddSide N P).card = if P.1 % 2 = 1 then P.2 - P.1 else N - (P.2 - P.1) := by
    unfold oddSide
    split_ifs
    · exact hc
    · rw [card_sdiff_of_subset hsub, hc, hcN]
  have hosub : oddSide N P ⊆ Icc 1 N := by
    unfold oddSide; split_ifs
    · exact hsub
    · exact sdiff_subset
  have heven : (evenSide N P).card = N - (oddSide N P).card := by
    rw [evenSide, card_sdiff_of_subset hosub, hcN]
  rw [heven, hodd]
  have : ¬ (P.1 = 1 ∧ P.2 = N) := h4
  split_ifs <;> refine ⟨by omega, by omega, by omega, by omega⟩

/-- The flank set `Fl^A = S_{odds(A)}` of an odd chord, pair by pair:
`C(evens A, 2) ∪ (evens A × B)` (the components of the circle minus `odds(A)` are the singletons
of `evens(A)` and the arc `B`). -/
theorem mem_oddSideSplit_iff {N i j a b : ℕ} (hP : (i, j) ∈ oddDiagonals N) :
    (a, b) ∈ oddSideSplit N (i, j) ↔ a < b ∧
      ((a ∈ evens (oddSide N (i, j)) ∧ b ∈ evens (oddSide N (i, j))) ∨
        (a ∈ evens (oddSide N (i, j)) ∧ b ∈ evenSide N (i, j)) ∨
        (a ∈ evenSide N (i, j) ∧ b ∈ evens (oddSide N (i, j)))) := by
  obtain ⟨hi1, hjN, hij, hne, hodd⟩ := pkL_oddD hP
  have hm := fun x =>
    And.intro (pkL_mem_oddSide (x := x) hi1 hjN) (pkL_mem_evenSide (x := x) hi1 hjN)
  have hev : ∀ x, x ∈ evens (oddSide N (i, j)) ↔ x ∈ oddSide N (i, j) ∧ x % 2 = 0 :=
    fun x => mem_filter
  have hod : ∀ x, x ∈ odds (oddSide N (i, j)) ↔ x ∈ oddSide N (i, j) ∧ x % 2 = 1 :=
    fun x => mem_filter
  simp only [hev, (hm _).1, (hm _).2, pkLInA]
  constructor
  · intro h
    have hd := mem_diagonals.1 (pkL_mem_sep.1 h).1
    dsimp only at hd
    obtain ⟨hA, hB, ⟨t1, ht1, h11, h12⟩, ⟨t2, ht2, h2⟩⟩ :=
      (pkL_inST_iff (by omega)).1 (pkL_mem_sep.1 h).2
    simp only [hod, (hm _).1, pkLInA] at hA hB ht1 ht2
    rcases Nat.mod_two_eq_zero_or_one i with hp | hp <;>
      simp only [hp, Nat.zero_ne_one, Nat.one_ne_zero, false_and, true_and, or_false,
        false_or] at hA hB ht1 ht2 ⊢ <;>
      rcases h2 with h2 | h2 <;> omega
  · rintro ⟨hab, h⟩
    -- a pair separated by two odd legs of `A`, one between `a` and `b`, one outside
    have key : ∀ t1 t2 : ℕ, a < t1 → t1 < b → (t2 < a ∨ b < t2) →
        (1 ≤ t1 ∧ t1 ≤ N ∧ t1 % 2 = 1 ∧
          ((i % 2 = 1 ∧ i ≤ t1 ∧ t1 ≤ j - 1) ∨ (i % 2 = 0 ∧ ¬ (i ≤ t1 ∧ t1 ≤ j - 1)))) →
        (1 ≤ t2 ∧ t2 ≤ N ∧ t2 % 2 = 1 ∧
          ((i % 2 = 1 ∧ i ≤ t2 ∧ t2 ≤ j - 1) ∨ (i % 2 = 0 ∧ ¬ (i ≤ t2 ∧ t2 ≤ j - 1)))) →
        (a, b) ∈ oddSideSplit N (i, j) := by
      intro t1 t2 h1 h2 h3 m1 m2
      refine pkL_mem_sep.2 ⟨mem_diagonals.2 (by dsimp only; omega), (pkL_inST_iff hab).2
        ⟨fun h' => ?_, fun h' => ?_, ⟨t1, by simp only [hod, (hm _).1, pkLInA]; omega, h1, h2⟩,
          ⟨t2, by simp only [hod, (hm _).1, pkLInA]; omega, h3⟩⟩⟩ <;>
      simp only [hod, (hm _).1, pkLInA] at h' <;> omega
    rcases Nat.mod_two_eq_zero_or_one i with hp | hp <;>
      simp only [hp, Nat.zero_ne_one, Nat.one_ne_zero, false_and, true_and, or_false,
        false_or] at h <;>
      rcases h with h | h | h
    · by_cases ha : a < i
      · exact key (a + 1) (a - 1) (by omega) (by omega) (by omega) (by omega) (by omega)
      · exact key (a + 1) (i - 1) (by omega) (by omega) (by omega) (by omega) (by omega)
    · exact key (i - 1) j (by omega) (by omega) (by omega) (by omega) (by omega)
    · exact key j (i - 1) (by omega) (by omega) (by omega) (by omega) (by omega)
    · exact key (a + 1) i (by omega) (by omega) (by omega) (by omega) (by omega)
    · exact key (j - 1) i (by omega) (by omega) (by omega) (by omega) (by omega)
    · exact key i (j - 1) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- The flank set `Fl^B = S_{evens(B)}` of an odd chord, pair by pair: `C(odds B, 2) ∪ (odds B × A)`
(the components of the circle minus `evens(B)` are the singletons of `odds(B)` and the arc `A`). -/
theorem mem_evenSideSplit_iff {N i j a b : ℕ} (hE : Even N) (hP : (i, j) ∈ oddDiagonals N) :
    (a, b) ∈ evenSideSplit N (i, j) ↔ a < b ∧
      ((a ∈ odds (evenSide N (i, j)) ∧ b ∈ odds (evenSide N (i, j))) ∨
        (a ∈ odds (evenSide N (i, j)) ∧ b ∈ oddSide N (i, j)) ∨
        (a ∈ oddSide N (i, j) ∧ b ∈ odds (evenSide N (i, j)))) := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  obtain ⟨hi1, hjN, hij, hne, hodd⟩ := pkL_oddD hP
  have hm := fun x =>
    And.intro (pkL_mem_oddSide (x := x) hi1 hjN) (pkL_mem_evenSide (x := x) hi1 hjN)
  have hod : ∀ x, x ∈ odds (evenSide N (i, j)) ↔ x ∈ evenSide N (i, j) ∧ x % 2 = 1 :=
    fun x => mem_filter
  have hev : ∀ x, x ∈ evens (evenSide N (i, j)) ↔ x ∈ evenSide N (i, j) ∧ x % 2 = 0 :=
    fun x => mem_filter
  simp only [hod, (hm _).1, (hm _).2, pkLInA]
  constructor
  · intro h
    have hd := mem_diagonals.1 (pkL_mem_sep.1 h).1
    dsimp only at hd
    obtain ⟨hA, hB, ⟨t1, ht1, h11, h12⟩, ⟨t2, ht2, h2⟩⟩ :=
      (pkL_inST_iff (by omega)).1 (pkL_mem_sep.1 h).2
    simp only [hev, (hm _).2, pkLInA] at hA hB ht1 ht2
    rcases Nat.mod_two_eq_zero_or_one i with hp | hp <;>
      simp only [hp, Nat.zero_ne_one, Nat.one_ne_zero, false_and, true_and, or_false,
        false_or] at hA hB ht1 ht2 ⊢ <;>
      rcases h2 with h2 | h2 <;> omega
  · rintro ⟨hab, h⟩
    -- a pair separated by two even legs of `B`, one between `a` and `b`, one outside
    have key : ∀ t1 t2 : ℕ, a < t1 → t1 < b → (t2 < a ∨ b < t2) →
        (1 ≤ t1 ∧ t1 ≤ N ∧ t1 % 2 = 0 ∧
          ¬ ((i % 2 = 1 ∧ i ≤ t1 ∧ t1 ≤ j - 1) ∨ (i % 2 = 0 ∧ ¬ (i ≤ t1 ∧ t1 ≤ j - 1)))) →
        (1 ≤ t2 ∧ t2 ≤ N ∧ t2 % 2 = 0 ∧
          ¬ ((i % 2 = 1 ∧ i ≤ t2 ∧ t2 ≤ j - 1) ∨ (i % 2 = 0 ∧ ¬ (i ≤ t2 ∧ t2 ≤ j - 1)))) →
        (a, b) ∈ evenSideSplit N (i, j) := by
      intro t1 t2 h1 h2 h3 m1 m2
      refine pkL_mem_sep.2 ⟨mem_diagonals.2 (by dsimp only; omega), (pkL_inST_iff hab).2
        ⟨fun h' => ?_, fun h' => ?_, ⟨t1, by simp only [hev, (hm _).2, pkLInA]; omega, h1, h2⟩,
          ⟨t2, by simp only [hev, (hm _).2, pkLInA]; omega, h3⟩⟩⟩ <;>
      simp only [hev, (hm _).2, pkLInA] at h' <;> omega
    rcases Nat.mod_two_eq_zero_or_one i with hp | hp <;>
      simp only [hp, Nat.zero_ne_one, Nat.one_ne_zero, false_and, true_and, or_false,
        false_or] at h <;>
      rcases h with h | h | h
    · exact key (a + 1) i (by omega) (by omega) (by omega) (by omega) (by omega)
    · exact key (j - 1) i (by omega) (by omega) (by omega) (by omega) (by omega)
    · exact key i (j - 1) (by omega) (by omega) (by omega) (by omega) (by omega)
    · by_cases ha : j ≤ a
      · exact key (a + 1) j (by omega) (by omega) (by omega) (by omega) (by omega)
      · by_cases hb : b < i
        · exact key (a + 1) (i - 1) (by omega) (by omega) (by omega) (by omega) (by omega)
        · exact key (a + 1) (b + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
    · exact key (i - 1) j (by omega) (by omega) (by omega) (by omega) (by omega)
    · exact key j (b + 1) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- Membership in `□_P = evens(A_P) × odds(B_P)` (as sorted pairs). -/
theorem mem_minRect_iff {N : ℕ} {P : ℕ × ℕ} {a b : ℕ} :
    (a, b) ∈ minRect N P ↔ a < b ∧ ((a ∈ evens (oddSide N P) ∧ b ∈ odds (evenSide N P)) ∨
      (a ∈ odds (evenSide N P) ∧ b ∈ evens (oddSide N P))) := by
  rw [pkCh_mem_minRect]
  constructor
  · rintro ⟨e, he, o, ho, h⟩
    have hpe : e % 2 = 0 := (mem_filter.1 he).2
    have hpo : o % 2 = 1 := (mem_filter.1 ho).2
    simp only [Prod.mk.injEq] at h
    rcases Nat.lt_or_ge e o with hlt | hge
    · rw [min_eq_left hlt.le, max_eq_right hlt.le] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hlt, Or.inl ⟨he, ho⟩⟩
    · rw [min_eq_right hge, max_eq_left hge] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by omega, Or.inr ⟨ho, he⟩⟩
  · rintro ⟨hab, ⟨ha, hb⟩ | ⟨ha, hb⟩⟩
    · exact ⟨a, ha, b, hb, by rw [min_eq_left hab.le, max_eq_right hab.le]⟩
    · exact ⟨b, hb, a, ha, by rw [min_eq_right hab.le, max_eq_left hab.le]⟩

/-- The two flank sets of an odd chord, pair by pair: a pair of `Fl^A` is in `□_P` or an ee pair
not inside `B`; a pair of `Fl^B` is in `□_P` or an oo pair not inside `A`. -/
theorem mem_flank_split {N i j a b : ℕ} (hE : Even N) (hP : (i, j) ∈ oddDiagonals N) :
    ((a, b) ∈ oddSideSplit N (i, j) ↔ (a, b) ∈ minRect N (i, j) ∨
      ((a, b) ∈ diagonals N ∧ a % 2 = 0 ∧ b % 2 = 0 ∧
        ¬ (a ∈ evenSide N (i, j) ∧ b ∈ evenSide N (i, j)))) ∧
    ((a, b) ∈ evenSideSplit N (i, j) ↔ (a, b) ∈ minRect N (i, j) ∨
      ((a, b) ∈ diagonals N ∧ a % 2 = 1 ∧ b % 2 = 1 ∧
        ¬ (a ∈ oddSide N (i, j) ∧ b ∈ oddSide N (i, j)))) := by
  -- `B = [1, N] \ A`
  have hB : ∀ x, x ∈ evenSide N (i, j) ↔ x ∈ Icc 1 N ∧ x ∉ oddSide N (i, j) := fun x => mem_sdiff
  have hev : ∀ x, x ∈ evens (oddSide N (i, j)) ↔ x ∈ oddSide N (i, j) ∧ x % 2 = 0 :=
    fun x => mem_filter
  have hod : ∀ x, x ∈ odds (evenSide N (i, j)) ↔ x ∈ evenSide N (i, j) ∧ x % 2 = 1 :=
    fun x => mem_filter
  have hdI : ∀ {p : ℕ × ℕ}, p ∈ diagonals N → p.1 ∈ Icc 1 N ∧ p.2 ∈ Icc 1 N := fun hp => by
    have := mem_diagonals.1 hp
    exact ⟨mem_Icc.2 ⟨this.1, by omega⟩, mem_Icc.2 ⟨by omega, this.2.1⟩⟩
  -- a leg of `[1, N]` not in one side is in the other
  have hAB : ∀ x, x ∈ Icc 1 N → x ∉ evenSide N (i, j) → x ∈ oddSide N (i, j) := fun x hx h => by
    by_contra h'
    exact h ((hB x).2 ⟨hx, h'⟩)
  have hR := fun a b => mem_minRect_iff (N := N) (P := (i, j)) (a := a) (b := b)
  refine ⟨⟨fun h => ?_, ?_⟩, ⟨fun h => ?_, ?_⟩⟩
  · have hd := (pkL_mem_sep.1 h).1
    obtain ⟨hab, h⟩ := (mem_oddSideSplit_iff hP).1 h
    rw [hev, hev] at h
    by_cases hp : a % 2 = 0 ∧ b % 2 = 0
    · refine Or.inr ⟨hd, hp.1, hp.2, fun ⟨ha, hb⟩ => ?_⟩
      rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h2⟩
      · exact ((hB _).1 ha).2 h1.1
      · exact ((hB _).1 ha).2 h1.1
      · exact ((hB _).1 hb).2 h2.1
    · refine Or.inl ((hR a b).2 ⟨hab, ?_⟩)
      rw [hev, hev, hod, hod]
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd ⟨h1.2, h2.2⟩ hp
      · exact Or.inl ⟨h1, h2, by omega⟩
      · exact Or.inr ⟨⟨h1, by omega⟩, h2⟩
  · rintro (h | ⟨hd, ha, hb, hn⟩)
    · obtain ⟨hab, h⟩ := (hR a b).1 h
      rw [hev, hev, hod, hod] at h
      refine (mem_oddSideSplit_iff hP).2 ⟨hab, ?_⟩
      rw [hev, hev]
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr (Or.inl ⟨h1, h2.1⟩)
      · exact Or.inr (Or.inr ⟨h1.1, h2⟩)
    · have hab : a < b := by have := mem_diagonals.1 hd; dsimp only at this; omega
      refine (mem_oddSideSplit_iff hP).2 ⟨hab, ?_⟩
      rw [hev, hev]
      by_cases ha' : a ∈ evenSide N (i, j)
      · exact Or.inr (Or.inr ⟨ha', hAB b (hdI hd).2 fun hb' => hn ⟨ha', hb'⟩, hb⟩)
      · by_cases hb' : b ∈ evenSide N (i, j)
        · exact Or.inr (Or.inl ⟨⟨hAB a (hdI hd).1 ha', ha⟩, hb'⟩)
        · exact Or.inl ⟨⟨hAB a (hdI hd).1 ha', ha⟩, ⟨hAB b (hdI hd).2 hb', hb⟩⟩
  · have hd := (pkL_mem_sep.1 h).1
    obtain ⟨hab, h⟩ := (mem_evenSideSplit_iff hE hP).1 h
    rw [hod, hod] at h
    by_cases hp : a % 2 = 1 ∧ b % 2 = 1
    · refine Or.inr ⟨hd, hp.1, hp.2, fun ⟨ha, hb⟩ => ?_⟩
      rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h2⟩
      · exact ((hB _).1 h1.1).2 ha
      · exact ((hB _).1 h1.1).2 ha
      · exact ((hB _).1 h2.1).2 hb
    · refine Or.inl ((hR a b).2 ⟨hab, ?_⟩)
      rw [hev, hev, hod, hod]
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact absurd ⟨h1.2, h2.2⟩ hp
      · exact Or.inr ⟨h1, h2, by omega⟩
      · exact Or.inl ⟨⟨h1, by omega⟩, h2⟩
  · rintro (h | ⟨hd, ha, hb, hn⟩)
    · obtain ⟨hab, h⟩ := (hR a b).1 h
      rw [hev, hev, hod, hod] at h
      refine (mem_evenSideSplit_iff hE hP).2 ⟨hab, ?_⟩
      rw [hod, hod]
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr (Or.inr ⟨h1.1, h2⟩)
      · exact Or.inr (Or.inl ⟨h1, h2.1⟩)
    · have hab : a < b := by have := mem_diagonals.1 hd; dsimp only at this; omega
      refine (mem_evenSideSplit_iff hE hP).2 ⟨hab, ?_⟩
      rw [hod, hod]
      by_cases ha' : a ∈ oddSide N (i, j)
      · have hb' : b ∈ evenSide N (i, j) := (hB b).2 ⟨(hdI hd).2, fun hb' => hn ⟨ha', hb'⟩⟩
        exact Or.inr (Or.inr ⟨ha', hb', hb⟩)
      · have ha'' : a ∈ evenSide N (i, j) := (hB a).2 ⟨(hdI hd).1, ha'⟩
        by_cases hb' : b ∈ oddSide N (i, j)
        · exact Or.inr (Or.inl ⟨⟨ha'', ha⟩, hb'⟩)
        · exact Or.inl ⟨⟨ha'', ha⟩, ⟨(hB b).2 ⟨(hdI hd).2, hb'⟩, hb⟩⟩

-- registry: C-V6AE
/-- The flank sets of an odd chord and `□_P`: for even `N`, an odd chord `P` with sides
`A = A_P` (odd-ended, `oddSide`) and `B = B_P` (`evenSide`), and any `S`:
(a) `Fl^A = C(evens A, 2) ∪ (evens A × B) = □_P ⊔ {ee pairs not inside B}` and
`Fl^B = C(odds B, 2) ∪ (odds B × A) = □_P ⊔ {oo pairs not inside A}` (a pair `{a, b}` written
`(a, b)` with `a < b`); so `Fl^A ∩ Fl^B = □_P`, `Fl^A` has no oo pair, `Fl^B` no ee pair, and
`Fl^A`, `Fl^B` are members of the list; (b) `P ∈ 𝒫₀ ⇔ M ∩ Fl^A ⊆ M_e ⇔ M ∩ Fl^B ⊆ M_o`; (c)
`e_in(P) = M_e \ h_P` and `o_in(P) = M_o \ h_P`. -/
theorem Amplitudes.Kinematics.Mesh.flank_sets_of_odd_chord {N : ℕ} (hE : Even N)
    {P : ℕ × ℕ} (hP : P ∈ oddDiagonals N) (S : Finset (ℕ × ℕ)) :
    (oddSideSplit N P = ((evens (oddSide N P) ×ˢ evens (oddSide N P)) ∪
        (evens (oddSide N P) ×ˢ evenSide N P) ∪ (evenSide N P ×ˢ evens (oddSide N P))).filter
          (fun t => t.1 < t.2) ∧
      oddSideSplit N P = minRect N P ∪ (diagonals N).filter (fun t => t.1 % 2 = 0 ∧
        t.2 % 2 = 0 ∧ ¬ (t.1 ∈ evenSide N P ∧ t.2 ∈ evenSide N P)) ∧
      Disjoint (minRect N P) ((diagonals N).filter (fun t => t.1 % 2 = 0 ∧ t.2 % 2 = 0 ∧
        ¬ (t.1 ∈ evenSide N P ∧ t.2 ∈ evenSide N P)))) ∧
    (evenSideSplit N P = ((odds (evenSide N P) ×ˢ odds (evenSide N P)) ∪
        (odds (evenSide N P) ×ˢ oddSide N P) ∪ (oddSide N P ×ˢ odds (evenSide N P))).filter
          (fun t => t.1 < t.2) ∧
      evenSideSplit N P = minRect N P ∪ (diagonals N).filter (fun t => t.1 % 2 = 1 ∧
        t.2 % 2 = 1 ∧ ¬ (t.1 ∈ oddSide N P ∧ t.2 ∈ oddSide N P)) ∧
      Disjoint (minRect N P) ((diagonals N).filter (fun t => t.1 % 2 = 1 ∧ t.2 % 2 = 1 ∧
        ¬ (t.1 ∈ oddSide N P ∧ t.2 ∈ oddSide N P)))) ∧
    oddSideSplit N P ∩ evenSideSplit N P = minRect N P ∧
    (∀ t ∈ oddSideSplit N P, ¬ (t.1 % 2 = 1 ∧ t.2 % 2 = 1)) ∧
    (∀ t ∈ evenSideSplit N P, ¬ (t.1 % 2 = 0 ∧ t.2 % 2 = 0)) ∧
    IsListMember N (oddSideSplit N P) ∧ IsListMember N (evenSideSplit N P) ∧
    ((P ∈ cleanChords N S ↔ missing N S ∩ oddSideSplit N P ⊆ Mee N S) ∧
      (P ∈ cleanChords N S ↔ missing N S ∩ evenSideSplit N P ⊆ Moo N S)) ∧
    innerEE N S P = Mee N S \ hitSet N S P ∧ innerOO N S P = Moo N S \ hitSet N S P := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  obtain ⟨i, j⟩ := P
  obtain ⟨hi1, hjN, hij, hne, hodd⟩ := pkL_oddD hP
  have hA := fun a b => mem_oddSideSplit_iff (a := a) (b := b) hP
  have hB := fun a b => mem_evenSideSplit_iff (a := a) (b := b) hE hP
  have FA_split := fun a b => (mem_flank_split (a := a) (b := b) hE hP).1
  have FB_split := fun a b => (mem_flank_split (a := a) (b := b) hE hP).2
  have rect_FA : ∀ a b, (a, b) ∈ minRect N (i, j) → (a, b) ∈ oddSideSplit N (i, j) :=
    fun a b h => (FA_split a b).2 (Or.inl h)
  have rect_FB : ∀ a b, (a, b) ∈ minRect N (i, j) → (a, b) ∈ evenSideSplit N (i, j) :=
    fun a b h => (FB_split a b).2 (Or.inl h)
  have rect_mixed : ∀ a b, (a, b) ∈ minRect N (i, j) → a % 2 ≠ b % 2 := by
    intro a b h
    obtain ⟨-, h⟩ := mem_minRect_iff.1 h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := (mem_filter.1 h1).2; have := (mem_filter.1 h2).2; omega
    · have := (mem_filter.1 h1).2; have := (mem_filter.1 h2).2; omega
  have FA_noOO : ∀ t ∈ oddSideSplit N (i, j), ¬ (t.1 % 2 = 1 ∧ t.2 % 2 = 1) := by
    rintro ⟨a, b⟩ h
    rcases (FA_split a b).1 h with h | ⟨-, ha, hb, -⟩
    · have := rect_mixed a b h; dsimp only; omega
    · dsimp only; omega
  have FB_noEE : ∀ t ∈ evenSideSplit N (i, j), ¬ (t.1 % 2 = 0 ∧ t.2 % 2 = 0) := by
    rintro ⟨a, b⟩ h
    rcases (FB_split a b).1 h with h | ⟨-, ha, hb, -⟩
    · have := rect_mixed a b h; dsimp only; omega
    · dsimp only; omega
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, FA_noOO, FB_noEE,
    (isListMember_iff_mem_gFamily hE).2 (pkL_HA_mem hP),
    (isListMember_iff_mem_gFamily hE).2 (pkL_HB_mem hE' hP),
    ⟨?_, ?_⟩, ?_, ?_⟩
  · ext ⟨a, b⟩
    rw [hA]
    simp only [mem_filter, mem_union, mem_product]
    tauto
  · ext ⟨a, b⟩
    rw [FA_split, mem_union, mem_filter]
  · rw [disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    have := rect_mixed a b h1
    have := (mem_filter.1 h2).2
    dsimp only at this
    omega
  · ext ⟨a, b⟩
    rw [hB]
    simp only [mem_filter, mem_union, mem_product]
    tauto
  · ext ⟨a, b⟩
    rw [FB_split, mem_union, mem_filter]
  · rw [disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    have := rect_mixed a b h1
    have := (mem_filter.1 h2).2
    dsimp only at this
    omega
  · ext ⟨a, b⟩
    rw [mem_inter, FA_split, FB_split]
    constructor
    · rintro ⟨h1 | ⟨-, h1, h2, -⟩, h3 | ⟨-, h3, h4, -⟩⟩
      · exact h1
      · exact h1
      · exact h3
      · omega
    · intro h
      exact ⟨Or.inl h, Or.inl h⟩
  · constructor
    · rintro hc ⟨a, b⟩ h
      obtain ⟨hM, hF⟩ := mem_inter.1 h
      refine mem_filter.2 ⟨hM, ?_⟩
      rcases (FA_split a b).1 hF with hr | ⟨-, ha, hb, -⟩
      · exact absurd hM (disjoint_left.1 (mem_filter.1 hc).2 hr)
      · exact ⟨ha, hb⟩
    · intro hsub
      refine mem_filter.2 ⟨hP, disjoint_left.2 fun ⟨a, b⟩ hr hM => ?_⟩
      have := (mem_filter.1 (hsub (mem_inter.2 ⟨hM, rect_FA a b hr⟩))).2
      have := rect_mixed a b hr
      dsimp only at *
      omega
  · constructor
    · rintro hc ⟨a, b⟩ h
      obtain ⟨hM, hF⟩ := mem_inter.1 h
      refine mem_filter.2 ⟨hM, ?_⟩
      rcases (FB_split a b).1 hF with hr | ⟨-, ha, hb, -⟩
      · exact absurd hM (disjoint_left.1 (mem_filter.1 hc).2 hr)
      · exact ⟨ha, hb⟩
    · intro hsub
      refine mem_filter.2 ⟨hP, disjoint_left.2 fun ⟨a, b⟩ hr hM => ?_⟩
      have := (mem_filter.1 (hsub (mem_inter.2 ⟨hM, rect_FB a b hr⟩))).2
      have := rect_mixed a b hr
      dsimp only at *
      omega
  · ext ⟨a, b⟩
    rw [pkCh_mem_innerEE, mem_sdiff, pkCh_mem_hitSet]
    constructor
    · rintro ⟨hM, h1, h2⟩
      refine ⟨hM, fun ⟨_, hH⟩ => ?_⟩
      have hee := (mem_filter.1 hM).2
      dsimp only at hee h1 h2
      rcases hH with hH | hH
      · rcases (FA_split a b).1 hH with hr | ⟨-, -, -, hn⟩
        · exact rect_mixed a b hr (by omega)
        · exact hn ⟨h1, h2⟩
      · exact FB_noEE _ hH hee
    · rintro ⟨hM, hn⟩
      refine ⟨hM, ?_⟩
      have hee := (mem_filter.1 hM).2
      have hd := (mem_sdiff.1 (mem_filter.1 hM).1).1
      dsimp only at hee ⊢
      by_contra hc
      exact hn ⟨(mem_filter.1 hM).1, Or.inl ((FA_split a b).2 (Or.inr ⟨hd, hee.1, hee.2, hc⟩))⟩
  · ext ⟨a, b⟩
    rw [pkCh_mem_innerOO, mem_sdiff, pkCh_mem_hitSet]
    constructor
    · rintro ⟨hM, h1, h2⟩
      refine ⟨hM, fun ⟨_, hH⟩ => ?_⟩
      have hoo := (mem_filter.1 hM).2
      dsimp only at hoo h1 h2
      rcases hH with hH | hH
      · exact FA_noOO _ hH hoo
      · rcases (FB_split a b).1 hH with hr | ⟨-, -, -, hn⟩
        · exact rect_mixed a b hr (by omega)
        · exact hn ⟨h1, h2⟩
    · rintro ⟨hM, hn⟩
      refine ⟨hM, ?_⟩
      have hoo := (mem_filter.1 hM).2
      have hd := (mem_sdiff.1 (mem_filter.1 hM).1).1
      dsimp only at hoo ⊢
      by_contra hc
      exact hn ⟨(mem_filter.1 hM).1, Or.inr ((FB_split a b).2 (Or.inr ⟨hd, hoo.1, hoo.2, hc⟩))⟩

-- registry: C-J1M2
/-- On-shell chords, the "equivalently" of their definition: an odd chord `P` is on-shell,
`□_P ∩ M = ∅`, iff the two flank sets of `P` share no missing pair. -/
theorem Amplitudes.Kinematics.Mesh.on_shell_iff_flank_sets_share_no_missing_pair {N : ℕ}
    (hE : Even N) {P : ℕ × ℕ} (hP : P ∈ oddDiagonals N) (S : Finset (ℕ × ℕ)) :
    P ∈ cleanChords N S ↔ Disjoint (oddSideSplit N P ∩ evenSideSplit N P) (missing N S) := by
  rw [(flank_sets_of_odd_chord hE hP S).2.2.1]
  exact ⟨fun h => (mem_filter.1 h).2, fun h => mem_filter.2 ⟨hP, h⟩⟩

-- registry: C-GS87
/-- Odd chords on the same-parity sublocus (`X_P` and the mesh sum over `□_P`): for even `N ≥ 4`, a
set `S` of pairs and an odd chord `P`, `X_P − Σ_{□_P} c ∈ span{c_t : t same-parity}`; hence `X_P`
vanishes on the same-parity sublocus `L_S⁰ = L_{S ∪ Same}` iff `□_P ⊆ S`, i.e. `P ∈ 𝒫₀`. -/
theorem Amplitudes.Kinematics.Mesh.odd_chord_vanishing_on_same_parity_sublocus {N : ℕ} (hN : 4 ≤ N)
    (hE : Even N) {S : Finset (ℕ × ℕ)} (hS : S ⊆ diagonals N) {P : ℕ × ℕ}
    (hP : P ∈ oddDiagonals N) :
    (∃ φ : ℕ × ℕ → ℚ, ∀ X : ℕ × ℕ → ℚ,
      X P - ∑ t ∈ minRect N P, mesh N X t.1 t.2 = ∑ t ∈ pkGSame N, φ t * mesh N X t.1 t.2) ∧
    ((∀ X : ℕ × ℕ → ℚ, OnLocus N (S ∪ pkGSame N) X → X P = 0) ↔ minRect N P ⊆ S) ∧
    ((∀ X : ℕ × ℕ → ℚ, OnLocus N (S ∪ pkGSame N) X → X P = 0) ↔ P ∈ cleanChords N S) := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  -- the three same-parity sums of the identity for `X_P` (`block_sums` (e)): all ee pairs, ee pairs
  -- inside `B`, oo pairs inside `A`
  set ee := (diagonals N).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0) with hee
  set eeB := (evenSide N P ×ˢ evenSide N P).filter (fun p => p.1 < p.2 ∧ p.1 % 2 = 0 ∧
    p.2 % 2 = 0) with heeB
  set ooA := (oddSide N P ×ˢ oddSide N P).filter (fun p => p.1 < p.2 ∧ p.1 % 2 = 1 ∧
    p.2 % 2 = 1) with hooA
  have hsides : oddSide N P ⊆ Icc 1 N ∧ evenSide N P ⊆ Icc 1 N := by
    obtain ⟨i, j⟩ := P
    obtain ⟨hi1, hjN, -⟩ := pkL_oddD hP
    refine ⟨fun x hx => ?_, fun x hx => (mem_sdiff.1 hx).1⟩
    have := (pkL_mem_oddSide hi1 hjN).1 hx
    exact mem_Icc.2 ⟨this.1, this.2.1⟩
  have hsub : ∀ (L : Finset ℕ) (r : ℕ), L ⊆ Icc 1 N →
      (L ×ˢ L).filter (fun p => p.1 < p.2 ∧ p.1 % 2 = r ∧ p.2 % 2 = r) ⊆ pkGSame N := by
    intro L r hL p hp
    obtain ⟨hpp, hlt, h1, h2⟩ := mem_filter.1 hp
    obtain ⟨ha, hb⟩ := mem_product.1 hpp
    have ha' := mem_Icc.1 (hL ha)
    have hb' := mem_Icc.1 (hL hb)
    exact pkG_same_diag hE' ha'.1 hlt hb'.2 (by omega)
  have hee_sub : ee ⊆ pkGSame N := fun p hp => by
    obtain ⟨hd, h1, h2⟩ := mem_filter.1 hp
    exact pkG_mem_same.2 ⟨hd, by omega⟩
  have hcomb : ∀ (F : Finset (ℕ × ℕ)), F ⊆ pkGSame N → ∀ X : ℕ × ℕ → ℚ,
      ∑ t ∈ pkGSame N, (if t ∈ F then 1 else 0) * mesh N X t.1 t.2 =
        ∑ t ∈ F, mesh N X t.1 t.2 := by
    intro F hF X
    simp only [ite_mul, one_mul, zero_mul]
    rw [sum_ite_mem, inter_eq_right.2 hF]
  have hclean : P ∈ cleanChords N S ↔ minRect N P ⊆ S := by
    constructor
    · intro h t ht
      by_contra htS
      exact disjoint_left.1 (mem_filter.1 h).2 ht (mem_sdiff.2 ⟨pkG_minRect_diag hP ht, htS⟩)
    · intro h
      exact mem_filter.2 ⟨hP, disjoint_left.2 fun t ht htM => (mem_sdiff.1 htM).2 (h ht)⟩
  -- the span clause: `block_sums` (e) modulo the same-parity mesh variables
  have hspan : ∃ φ : ℕ × ℕ → ℚ, ∀ X : ℕ × ℕ → ℚ,
      X P - ∑ t ∈ minRect N P, mesh N X t.1 t.2 = ∑ t ∈ pkGSame N, φ t * mesh N X t.1 t.2 := by
    refine ⟨fun t => (if t ∈ ee then 1 else 0) - (if t ∈ eeB then 1 else 0) -
        (if t ∈ ooA then 1 else 0), fun X => ?_⟩
    simp only [sub_mul, sum_sub_distrib]
    rw [hcomb ee hee_sub, hcomb eeB (hsub _ 0 hsides.2), hcomb ooA (hsub _ 1 hsides.1),
      (block_sums hN hE X).2.2.2.2.2 P hP]
    have eE : pkGE N X = ∑ t ∈ ee, mesh N X t.1 t.2 := rfl
    have eB : pkGSee N X (evenSide N P) = ∑ t ∈ eeB, mesh N X t.1 t.2 := rfl
    have eA : pkGSoo N X (oddSide N P) = ∑ t ∈ ooA, mesh N X t.1 t.2 := rfl
    rw [eE, eB, eA]
    ring
  -- "if": on `L_S⁰` the mesh variables of `□_P ⊆ S` and of `Same` vanish, so `X_P` does
  have hiff : (∀ X : ℕ × ℕ → ℚ, OnLocus N (S ∪ pkGSame N) X → X P = 0) ↔ P ∈ cleanChords N S := by
    refine ⟨fun h => ?_, fun h X hX => ?_⟩
    · by_contra hc
      obtain ⟨X, hX, h2⟩ := pkG_G1_wit hN hE' hS hP hc
      rw [h X hX] at h2
      norm_num at h2
    · obtain ⟨φ, hφ⟩ := hspan
      have h1 : ∑ t ∈ minRect N P, mesh N X t.1 t.2 = 0 :=
        sum_eq_zero fun t ht => hX t (mem_union_left _ (hclean.1 h ht))
      have h2 : ∑ t ∈ pkGSame N, φ t * mesh N X t.1 t.2 = 0 :=
        sum_eq_zero fun t ht => by rw [hX t (mem_union_right _ ht), mul_zero]
      have := hφ X
      rw [h1, h2] at this
      linarith
  exact ⟨hspan, hiff.trans hclean, hiff⟩

/-! ## Dissections, their faces, and the Cayley form

The definition of dissections in readable form. A dissection is an element of the library's
`pkGDis N` (a set of pairwise non-crossing odd chords; pinned in `Statements.lean`). A face is a
maximal set of polygon vertices no two of which a chord of the dissection separates (`IsFace`); the
library indexes faces by their root side instead (`pkGRoots`, `pkGVerts`), and `isFace_iff` and
`faces_eq_image` prove that the two descriptions give the same faces, one for each root side. The
sides of a face are the pairs of cyclically consecutive vertices; the side `(u, v)` carries the far
arc of legs `[u, v − 1]` (cyclically), so a leg `x` lies on the side that starts at the last vertex
at or before `x` (`sideStart`), and `U_f` is `oddStartLegs`. The chord sides of a face are the
chords of the dissection with both ends on it (`chordSides`). The lemmas named `pkG_…` below are
bridges to the library's encoding (root sides `r`, vertices `pkGVerts D r`, child chords
`pkGKids D r`: the maximal chords of `D` inside `r` other than `r`, which may share an end with it),
not statements of the paper. -/

/-- The chord `P` separates the vertex `u` from the vertex `v`: `u` lies strictly inside `P` and `v`
strictly outside (the ends of `P` are separated from nothing: they lie on both sides). -/
def Separates (P : ℕ × ℕ) (u v : ℕ) : Prop := (P.1 < u ∧ u < P.2) ∧ (v < P.1 ∨ P.2 < v)

-- registry: C-8TJ0
/-- A face of the dissection `D` of the `N`-gon: a set `F` of vertices, no two of which a chord of
`D` separates, that is maximal with that property (every other vertex is separated from some
vertex of `F` by a chord of `D`). -/
def Combinatorics.Polygons.IsFace (N : ℕ) (D : Finset (ℕ × ℕ)) (F : Finset ℕ) : Prop :=
  F ⊆ Icc 1 N ∧ (∀ u ∈ F, ∀ v ∈ F, ∀ P ∈ D, ¬ Separates P u v) ∧
    ∀ w ∈ Icc 1 N, w ∉ F → ∃ u ∈ F, ∃ P ∈ D, Separates P u w ∨ Separates P w u

open Classical in
-- registry: C-8TJ0
/-- The faces of the dissection `D`, as sets of vertices. -/
noncomputable def Combinatorics.Polygons.faces (N : ℕ) (D : Finset (ℕ × ℕ)) : Finset (Finset ℕ) :=
  (Icc 1 N).powerset.filter (IsFace N D)

-- registry: C-8TJ0
/-- The start of the side of the face `F` that carries the leg `x`: the last vertex of `F` at or
before `x`; a leg before the first vertex lies on the closing side, which starts at the last
vertex. (Meaningful for a face; for the empty set it is `0`.) -/
def Combinatorics.Polygons.sideStart (F : Finset ℕ) (x : ℕ) : ℕ :=
  if (F.filter (fun w => w ≤ x)).Nonempty then (F.filter (fun w => w ≤ x)).sup (fun w => w)
  else F.sup (fun w => w)

-- registry: C-8TJ0
/-- `U_f`: the legs of the sides of the face `F` that start at an odd vertex. -/
def Combinatorics.Polygons.oddStartLegs (N : ℕ) (F : Finset ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun x => sideStart F x % 2 = 1)

-- registry: C-8TJ0
/-- The chord sides of the face `F` of `D`: the chords of `D` with both ends on `F`. -/
def Combinatorics.Polygons.chordSides (D : Finset (ℕ × ℕ)) (F : Finset ℕ) : Finset (ℕ × ℕ) :=
  D.filter (fun P => P.1 ∈ F ∧ P.2 ∈ F)

-- registry: C-JNJF
/-- The Cayley vertex `V_f` of a face `F`, over any field: the face sign
`sgn_f = (−1)^{|f|/2 − 1}` times `Q_{U_f} = Σ_{a < b ∈ U_f} s_{ab}` (`s = −c`). -/
def NLSM.FeynmanRules.faceVertex {K : Type*} [Field K] (N : ℕ) (X : ℕ × ℕ → K) (F : Finset ℕ) : K :=
  (-1 : K) ^ (F.card / 2 - 1) *
    ∑ p ∈ (oddStartLegs N F ×ˢ oddStartLegs N F).filter (fun p => p.1 < p.2), -mesh N X p.1 p.2

-- registry: C-JNJF
/-- The Cayley sum `Cay_N` over any field: the sum over all dissections by odd
chords (the empty one included) of the product of the Cayley vertices of the faces and of
`−1/X_P` over the chords. -/
noncomputable def NLSM.FeynmanRules.cayleySum {K : Type*} [Field K] (N : ℕ) (X : ℕ × ℕ → K) : K :=
  ∑ D ∈ pkGDis N, (∏ F ∈ faces N D, faceVertex N X F) * ∏ P ∈ D, -(X P)⁻¹

/-- The end of a root side is a vertex of its face. -/
theorem pkG_r2_vert {D : Finset (ℕ × ℕ)} {r : ℕ × ℕ} (h : r.1 ≤ r.2) : r.2 ∈ pkGVerts D r :=
  pkG_mem_verts.2 ⟨h, le_refl _, fun K hK q => by have := (pkG_kid_in hK).2.2.2; omega⟩

/-- The right end of a child chord (`pkGKids`) is a vertex of the face. -/
theorem pkG_kid_vert_right {N : ℕ} {D : Finset (ℕ × ℕ)} (hD : D ∈ pkGDis N) {r R : ℕ × ℕ}
    (hR : R ∈ pkGKids D r) : R.2 ∈ pkGVerts D r := by
  obtain ⟨hRD, -, a, b⟩ := pkG_kid_in hR
  have cR := pkG_chord hD hRD
  refine pkG_mem_verts.2 ⟨by omega, b, fun R'' hR'' hc => ?_⟩
  by_cases e : R = R''
  · subst e
    omega
  · have := pkG_kids_disj hD hR hR'' e
    omega

/-- The vertices of a face lie in `1..N`. -/
theorem pkG_verts_Icc {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)}
    (hD : D ∈ pkGDis N) {r : ℕ × ℕ} (hr : r ∈ pkGRoots N D) : pkGVerts D r ⊆ Icc 1 N := by
  intro w hw
  have := pkG_root hN hE hD hr
  have := pkG_mem_verts.1 hw
  exact mem_Icc.2 ⟨by omega, by omega⟩

/-- A face has a vertex strictly between the ends of its root side. -/
theorem pkG_inner_vert {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)}
    (hD : D ∈ pkGDis N) {r : ℕ × ℕ} (hr : r ∈ pkGRoots N D) :
    ∃ u ∈ pkGVerts D r, r.1 < u ∧ u < r.2 := by
  have cr := pkG_root hN hE hD hr
  by_cases h : r.1 + 1 ∈ pkGVerts D r
  · exact ⟨_, h, by omega, by omega⟩
  · have hk : ∃ K ∈ pkGKids D r, K.1 < r.1 + 1 ∧ r.1 + 1 < K.2 := by
      by_contra hc
      push Not at hc
      exact h (pkG_mem_verts.2 ⟨by omega, by omega, fun K hK q => by
        have := hc K hK q.1; omega⟩)
    obtain ⟨K, hK, k1, k2⟩ := hk
    obtain ⟨hKD, hKr, a, b⟩ := pkG_kid_in hK
    have : K.1 = r.1 := by omega
    have hne : K.2 ≠ r.2 := fun e => hKr (Prod.ext this e)
    exact ⟨K.2, pkG_kid_vert_right hD hK, by omega, by omega⟩

/-- No chord of `D` separates two vertices of the face with root side `r`. -/
theorem pkG_verts_not_separated {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)}
    (hD : D ∈ pkGDis N) {r : ℕ × ℕ} (hr : r ∈ pkGRoots N D) {u v : ℕ}
    (hu : u ∈ pkGVerts D r) (hv : v ∈ pkGVerts D r) {P : ℕ × ℕ} (hP : P ∈ D) :
    ¬ Separates P u v := by
  rintro ⟨⟨p1, p2⟩, hpv⟩
  have hu' := (pkG_mem_verts' hD).1 hu
  have hv' := (pkG_mem_verts' hD).1 hv
  rcases pkG_lam (pkG_root_nc hN hE hD (mem_insert_of_mem hP) hr) with h | h | h | h
  · by_cases e : P = r
    · subst e; omega
    · exact hu'.2.2 P hP ⟨e, h.1, h.2⟩ ⟨p1, p2⟩
  · omega
  · omega
  · omega

/-- Every vertex off the face with root side `r` is separated from one of its vertices by a chord
of `D`. -/
theorem pkG_verts_maximal {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)}
    (hD : D ∈ pkGDis N) {r : ℕ × ℕ} (hr : r ∈ pkGRoots N D) {w : ℕ} (hw : w ∈ Icc 1 N)
    (hwF : w ∉ pkGVerts D r) :
    ∃ u ∈ pkGVerts D r, ∃ P ∈ D, Separates P u w ∨ Separates P w u := by
  have cr := pkG_root hN hE hD hr
  have hw' := mem_Icc.1 hw
  by_cases hin : r.1 ≤ w ∧ w ≤ r.2
  · have : ∃ R ∈ D, pkGIn R r ∧ R.1 < w ∧ w < R.2 := by
      by_contra hc
      push Not at hc
      exact hwF ((pkG_mem_verts' hD).2 ⟨hin.1, hin.2, fun R hR hRr q => by
        have := hc R hR hRr q.1; omega⟩)
    obtain ⟨R, hRD, ⟨hne, a, b⟩, w1, w2⟩ := this
    by_cases h1 : r.1 < R.1
    · exact ⟨r.1, pkG_r1_vert (by omega), R, hRD, Or.inr ⟨⟨w1, w2⟩, Or.inl h1⟩⟩
    · have h2 : R.2 < r.2 := by
        by_contra h2
        exact hne (Prod.ext (by omega) (by omega))
      exact ⟨r.2, pkG_r2_vert (by omega), R, hRD, Or.inr ⟨⟨w1, w2⟩, Or.inr h2⟩⟩
  · have hrD : r ∈ D := by
      rcases mem_insert.1 hr with e | e
      · exfalso; apply hin; rw [e]; exact ⟨hw'.1, hw'.2⟩
      · exact e
    obtain ⟨u, hu, u1, u2⟩ := pkG_inner_vert hN hE hD hr
    exact ⟨u, hu, r, hrD, Or.inl ⟨⟨u1, u2⟩, by omega⟩⟩

/-- The vertex set of the face with root side `r` is a face. -/
theorem pkG_verts_isFace {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)}
    (hD : D ∈ pkGDis N) {r : ℕ × ℕ} (hr : r ∈ pkGRoots N D) : IsFace N D (pkGVerts D r) :=
  ⟨pkG_verts_Icc hN hE hD hr, fun _ hu _ hv _ hP => pkG_verts_not_separated hN hE hD hr hu hv hP,
    fun _ hw hwF => pkG_verts_maximal hN hE hD hr hw hwF⟩

-- registry: C-8TJ0
/-- The faces are exactly the vertex sets of the root sides: for a dissection `D`, `F` is a face
iff `F = pkGVerts D r` for a root side `r` (a chord of `D` or `(1, N)`). -/
theorem Combinatorics.Polygons.isFace_iff {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)}
    (hD : D ∈ pkGDis N) {F : Finset ℕ} :
    IsFace N D F ↔ ∃ r ∈ pkGRoots N D, pkGVerts D r = F := by
  refine ⟨fun ⟨hFI, hsep, hmax⟩ => ?_, fun ⟨r, hr, e⟩ => e ▸ pkG_verts_isFace hN hE hD hr⟩
  have hmem : (1, N) ∈ (pkGRoots N D).filter (fun r => F ⊆ Icc r.1 r.2) :=
    mem_filter.2 ⟨mem_insert_self _ _, hFI⟩
  obtain ⟨r, hrm, hmin⟩ := exists_min_image _ (fun r : ℕ × ℕ => r.2 - r.1) ⟨_, hmem⟩
  obtain ⟨hr, hFr⟩ := mem_filter.1 hrm
  have cr := pkG_root hN hE hD hr
  have hsub : F ⊆ pkGVerts D r := by
    intro u hu
    have hu' := mem_Icc.1 (hFr hu)
    refine (pkG_mem_verts' hD).2 ⟨hu'.1, hu'.2, fun R hR hRr hRu => ?_⟩
    have hFR : F ⊆ Icc R.1 R.2 := by
      intro v hv
      have := hsep u hu v hv R hR
      simp only [Separates, not_and, not_or, not_lt] at this
      have := this hRu
      exact mem_Icc.2 ⟨this.1, this.2⟩
    have := hmin R (mem_filter.2 ⟨mem_insert_of_mem hR, hFR⟩)
    obtain ⟨hne, a, b⟩ := hRr
    have cR := pkG_chord hD hR
    have : ¬ (R.1 = r.1 ∧ R.2 = r.2) := fun ⟨x, y⟩ => hne (Prod.ext x y)
    omega
  refine ⟨r, hr, le_antisymm (fun w hw => ?_) hsub⟩
  by_contra hwF
  obtain ⟨u, hu, P, hP, h⟩ := hmax w (pkG_verts_Icc hN hE hD hr hw) hwF
  rcases h with h | h
  · exact pkG_verts_not_separated hN hE hD hr (hsub hu) hw hP h
  · exact pkG_verts_not_separated hN hE hD hr hw (hsub hu) hP h

/-- Distinct root sides give distinct faces (a face starts at the start of its root side and ends
at its end). -/
theorem pkG_verts_injOn {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)}
    (hD : D ∈ pkGDis N) : Set.InjOn (pkGVerts D) (pkGRoots N D) := by
  intro r hr r' hr' e
  have c := pkG_root hN hE hD hr
  have c' := pkG_root hN hE hD hr'
  have a := pkG_mem_verts.1 (e ▸ pkG_r1_vert (D := D) (r := r) (by omega) : r.1 ∈ pkGVerts D r')
  have b := pkG_mem_verts.1 (e ▸ pkG_r2_vert (D := D) (r := r) (by omega) : r.2 ∈ pkGVerts D r')
  have a' := pkG_mem_verts.1
    (e.symm ▸ pkG_r1_vert (D := D) (r := r') (by omega) : r'.1 ∈ pkGVerts D r)
  have b' := pkG_mem_verts.1
    (e.symm ▸ pkG_r2_vert (D := D) (r := r') (by omega) : r'.2 ∈ pkGVerts D r)
  exact Prod.ext (by omega) (by omega)

-- registry: C-8TJ0
/-- The faces of `D` are the vertex sets of its root sides, one for each. -/
theorem Combinatorics.Polygons.faces_eq_image {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0)
    {D : Finset (ℕ × ℕ)} (hD : D ∈ pkGDis N) : faces N D = (pkGRoots N D).image (pkGVerts D) := by
  classical
  ext F
  rw [faces, mem_filter, mem_powerset, mem_image]
  constructor
  · rintro ⟨-, h⟩
    obtain ⟨r, hr, e⟩ := (isFace_iff hN hE hD).1 h
    exact ⟨r, hr, e⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨pkG_verts_Icc hN hE hD hr, pkG_verts_isFace hN hE hD hr⟩

/-- The last vertex of a face is the end of its root side. -/
theorem pkG_verts_sup {D : Finset (ℕ × ℕ)} {r : ℕ × ℕ} (h : r.1 ≤ r.2) :
    (pkGVerts D r).sup (fun w => w) = r.2 :=
  le_antisymm (Finset.sup_le fun _ hw => (pkG_mem_verts.1 hw).2.1)
    (le_sup (f := fun w => w) (pkG_r2_vert h))

/-- The library's odd-start class `pkGW` of the face with root side `r` is `U_f`. -/
theorem pkG_W_eq_oddStartLegs {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)}
    (hD : D ∈ pkGDis N) {r : ℕ × ℕ} (hr : r ∈ pkGRoots N D) :
    pkGW N D r = oddStartLegs N (pkGVerts D r) := by
  have cr := pkG_root hN hE hD hr
  have hWI := pkG_W_Icc hN hE hD hr
  ext x
  by_cases hx : x ∈ Icc 1 N
  swap
  · simp only [oddStartLegs, mem_filter, hx, false_and, iff_false]
    exact fun h => hx (hWI h)
  have eW : pkGW N D r = if r.1 % 2 = 1 then pkGU D r else Icc 1 N \ pkGU D r := rfl
  have eO : x ∈ oddStartLegs N (pkGVerts D r) ↔ sideStart (pkGVerts D r) x % 2 = 1 := by
    rw [oddStartLegs, mem_filter]; exact and_iff_right hx
  rw [eO, eW]
  by_cases hin : r.1 ≤ x ∧ x < r.2
  · have hne : ((pkGVerts D r).filter (fun w => w ≤ x)).Nonempty :=
      ⟨r.1, mem_filter.2 ⟨pkG_r1_vert (by omega), hin.1⟩⟩
    have hs : sideStart (pkGVerts D r) x = pkGGov D r x := by
      simp only [sideStart, hne, ↓reduceIte]; rfl
    rw [hs]
    split_ifs with h <;> simp only [mem_sdiff, pkG_mem_U, hx, true_and] <;> omega
  · have hU : x ∉ pkGU D r := fun h => hin ⟨(pkG_mem_U.1 h).1, (pkG_mem_U.1 h).2.1⟩
    have hs : sideStart (pkGVerts D r) x = r.2 := by
      rw [sideStart]
      split_ifs with hne
      · by_cases hlt : x < r.1
        · exfalso
          obtain ⟨w, hw⟩ := hne
          have := (pkG_mem_verts.1 (mem_filter.1 hw).1).1
          have := (mem_filter.1 hw).2
          omega
        · have : (pkGVerts D r).filter (fun w => w ≤ x) = pkGVerts D r :=
            filter_true_of_mem fun w hw => by have := (pkG_mem_verts.1 hw).2.1; omega
          rw [this, pkG_verts_sup (by omega)]
      · exact pkG_verts_sup (by omega)
    rw [hs]
    split_ifs with h <;> simp only [mem_sdiff, hU, hx, true_and, not_false_eq_true, false_iff,
      true_iff] <;> omega

/-- The chord sides of the face with root side `r` are its child chords (`pkGKids`) and, if `r`
is a chord, `r`. -/
theorem chordSides_pkG_verts {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)}
    (hD : D ∈ pkGDis N) {r : ℕ × ℕ} (hr : r ∈ pkGRoots N D) {P : ℕ × ℕ} :
    P ∈ chordSides D (pkGVerts D r) ↔ P ∈ pkGKids D r ∨ (P = r ∧ r ∈ D) := by
  have cr := pkG_root hN hE hD hr
  constructor
  · intro h
    obtain ⟨hPD, h1, h2⟩ := mem_filter.1 h
    have cP := pkG_chord hD hPD
    have v1 := (pkG_mem_verts' hD).1 h1
    have v2 := (pkG_mem_verts' hD).1 h2
    by_cases e : P = r
    · exact Or.inr ⟨e, e ▸ hPD⟩
    · obtain ⟨K, hK, k1, k2⟩ := pkG_desc hD hPD ⟨e, v1.1, v2.2.1⟩
      by_cases eK : K = P
      · exact Or.inl (eK ▸ hK)
      · exfalso
        have hKne : ¬ (K.1 = P.1 ∧ K.2 = P.2) := fun ⟨x, y⟩ => eK (Prod.ext x y)
        have hv1 := (pkG_mem_verts.1 h1).2.2 K hK
        have hv2 := (pkG_mem_verts.1 h2).2.2 K hK
        omega
  · rintro (h | ⟨rfl, hrD⟩)
    · exact mem_filter.2 ⟨(pkG_kid_in h).1, pkG_kid_vert hD h, pkG_kid_vert_right hD h⟩
    · exact mem_filter.2 ⟨hrD, pkG_r1_vert (by omega), pkG_r2_vert (by omega)⟩

/-- The library's count `pkGDeg` of the chord sides of a face that lie outside `C` is the number
of its chord sides outside `C`. -/
theorem pkG_deg_eq_card_chordSides {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)}
    (hD : D ∈ pkGDis N) {r : ℕ × ℕ} (hr : r ∈ pkGRoots N D) (C : Finset (ℕ × ℕ)) :
    pkGDeg (pkGCh D) (D \ C) r = (chordSides D (pkGVerts D r) \ C).card := by
  have hrk : r ∉ pkGKids D r := fun h => (pkG_kid_in h).2.1 rfl
  have e : chordSides D (pkGVerts D r) \ C =
      (D \ C).filter (fun c => c = r) ∪ (D \ C).filter (fun c => c ∈ pkGCh D r) := by
    ext P
    simp only [mem_sdiff, chordSides_pkG_verts hN hE hD hr, mem_union, mem_filter]
    change _ ↔ _ ∨ (_ ∧ P ∈ pkGKids D r)
    constructor
    · rintro ⟨h1 | ⟨rfl, h2⟩, h3⟩
      · exact Or.inr ⟨⟨(pkG_kid_in h1).1, h3⟩, h1⟩
      · exact Or.inl ⟨⟨h2, h3⟩, rfl⟩
    · rintro (⟨⟨h1, h3⟩, rfl⟩ | ⟨⟨h1, h3⟩, h2⟩)
      · exact ⟨Or.inr ⟨rfl, h1⟩, h3⟩
      · exact ⟨Or.inl h2, h3⟩
  have hd : Disjoint ((D \ C).filter (fun c => c = r))
      ((D \ C).filter (fun c => c ∈ pkGCh D r)) := by
    rw [disjoint_left]
    intro P h1 h2
    rw [(mem_filter.1 h1).2] at h2
    exact hrk (mem_filter.1 h2).2
  rw [e, card_union_of_disjoint hd, pkG_deg_eq, filter_eq']
  split_ifs <;> simp

/-- Consecutive vertices of a face have different parity: the side between them is an edge or an
odd chord. -/
theorem pkG_verts_alternate {N : ℕ} {D : Finset (ℕ × ℕ)} (hD : D ∈ pkGDis N) {r : ℕ × ℕ}
    {u v : ℕ} (hu : u ∈ pkGVerts D r) (hv : v ∈ pkGVerts D r) (huv : u < v)
    (hcons : ∀ w ∈ pkGVerts D r, ¬ (u < w ∧ w < v)) : (v - u) % 2 = 1 := by
  by_cases h1 : v = u + 1
  · omega
  have hu' := pkG_mem_verts.1 hu
  have hv' := pkG_mem_verts.1 hv
  have hn : u + 1 ∉ pkGVerts D r := fun h => hcons _ h ⟨by omega, by omega⟩
  have : ∃ K ∈ pkGKids D r, K.1 < u + 1 ∧ u + 1 < K.2 := by
    by_contra hc
    push Not at hc
    exact hn (pkG_mem_verts.2 ⟨by omega, by omega, fun K hK q => by have := hc K hK q.1; omega⟩)
  obtain ⟨K, hK, k1, k2⟩ := this
  have a := hu'.2.2 K hK
  have b := hv'.2.2 K hK
  have hK2 := pkG_kid_vert_right hD hK
  have c : ¬ (u < K.2 ∧ K.2 < v) := hcons _ hK2
  have cK := pkG_chord hD (pkG_kid_in hK).1
  have : K.1 = u := by omega
  have : K.2 = v := by omega
  omega

-- registry: C-8TJ0
/-- Dissections, the claims of their definition: for even `N ≥ 4` and a dissection `D`, the number
of faces is `|D| + 1`; every face is a polygon (at least four vertices) with an even number of
vertices, whose vertex parities alternate: consecutive vertices `u < v` have `v − u` odd, and so do
the last and the first (the closing side). (`Σ_f(|f| − 2) = N − 2` is `faces_card_sub_two_sum`, in
module `Conventions`.) -/
theorem Combinatorics.Polygons.dissections {N : ℕ} (hN : 4 ≤ N) (hE : Even N) {D : Finset (ℕ × ℕ)}
    (hD : D ∈ pkGDis N) :
    (faces N D).card = D.card + 1 ∧
    ∀ F ∈ faces N D, 4 ≤ F.card ∧ Even F.card ∧
      (∀ u ∈ F, ∀ v ∈ F, u < v → (∀ w ∈ F, ¬ (u < w ∧ w < v)) → (v - u) % 2 = 1) ∧
      ∀ u ∈ F, ∀ v ∈ F, (∀ w ∈ F, u ≤ w ∧ w ≤ v) → (v - u) % 2 = 1 := by
  have hE : N % 2 = 0 := Nat.even_iff.1 hE
  rw [faces_eq_image hN hE hD]
  refine ⟨by rw [card_image_of_injOn (pkG_verts_injOn hN hE hD), pkG_card_roots hD], ?_⟩
  rintro F hF
  obtain ⟨r, hr, rfl⟩ := mem_image.1 hF
  have cr := pkG_root hN hE hD hr
  refine ⟨?_, Nat.even_iff.2 (pkG_verts_even hN hE hD hr),
    fun u hu v hv huv hc => pkG_verts_alternate hD hu hv huv hc, fun u hu v hv hb => ?_⟩
  · obtain ⟨w, hw, w1, w2⟩ := pkG_inner_vert hN hE hD hr
    have h3 : ({r.1, w, r.2} : Finset ℕ) ⊆ pkGVerts D r := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact pkG_r1_vert (by omega)
      · exact hw
      · exact pkG_r2_vert (by omega)
    have := card_le_card h3
    rw [card_insert_of_notMem (by simp; omega), card_insert_of_notMem (by simp; omega),
      card_singleton] at this
    have := pkG_verts_even hN hE hD hr
    omega
  · have a := hb _ (pkG_r1_vert (D := D) (r := r) (by omega))
    have b := hb _ (pkG_r2_vert (D := D) (r := r) (by omega))
    have := (pkG_mem_verts.1 hu).1
    have := (pkG_mem_verts.1 hv).2.1
    have : u = r.1 := by omega
    have : v = r.2 := by omega
    omega

-- registry: C-JNJF
/-- Over `ℚ`, the library's Cayley vertex `pkGV` (written with the class `U` of the face) is the
paper's vertex `faceVertex` of the face (written with the class of the sides that start at an odd
vertex, `U` or its complement): `Q_U = Q_{Uᶜ}`. -/
theorem NLSM.FeynmanRules.pkG_V_eq_faceVertex {N : ℕ} (hN : 4 ≤ N) (hE : Even N)
    {D : Finset (ℕ × ℕ)} (hD : D ∈ pkGDis N) {r : ℕ × ℕ} (hr : r ∈ pkGRoots N D) (X : ℕ × ℕ → ℚ) :
    pkGV N X D r = faceVertex N X (pkGVerts D r) := by
  have hE : N % 2 = 0 := Nat.even_iff.1 hE
  have hQ : pkGQ N X (pkGU D r) = pkGQ N X (pkGW N D r) := by
    by_cases h : r.1 % 2 = 1
    · simp only [pkGW, h, ↓reduceIte]
    · simp only [pkGW, h, ↓reduceIte]
      exact pkG_A4_all (by omega) X _ (pkG_U_Icc hN hE hD hr)
  rw [pkGV, hQ, pkG_W_eq_oddStartLegs hN hE hD hr]
  rfl

/-- `V_f = sgn_f · Q_{U_f}` over `ℚ`. -/
theorem faceVertex_eq_Q {N : ℕ} (X : ℕ × ℕ → ℚ) (F : Finset ℕ) :
    faceVertex N X F = (-1) ^ (F.card / 2 - 1) * pkGQ N X (oddStartLegs N F) := rfl

-- registry: C-BE9E
/-- The Cayley form: for every even `N ≥ 4`, `NLSM_N = −Cay_N` as rational functions of
the planar variables. -/
theorem NLSM.FeynmanRules.cayley_form {N : ℕ} (hN : 4 ≤ N) (hE : Even N) :
    NLSM N gen = -cayleySum N gen := by
  have hE : N % 2 = 0 := Nat.even_iff.1 hE
  have hN2 : 2 ≤ N := by omega
  -- the generic point as an evaluation
  have hA : ∀ p : MvPolynomial (ℕ × ℕ) ℚ,
      algebraMap _ RF p = MvPolynomial.eval₂ (algebraMap ℚ RF) gen p := by
    intro p
    have := congrArg (fun φ => φ p)
      (MvPolynomial.aeval_unique (IsScalarTower.toAlgHom ℚ (MvPolynomial (ℕ × ℕ) ℚ) RF))
    simp only [MvPolynomial.aeval_def] at this
    exact this
  -- the numerator of `NLSM_N`
  have hNP : algebraMap _ RF (NP ℚ N) = NLSM N gen * ∏ d ∈ oddDiagonals N, gen d := by
    have e0 : NP ℚ N = AP ℚ N (N - 2) := rfl
    have e3 : ((N : ℤ) - 2) = ((N - 2 : ℕ) : ℤ) := by omega
    have e1 : NLSM N gen = shiftCoeff N ((N - 2 : ℕ) : ℤ) gen := by
      rw [← e3]
      rfl
    rw [hA, e0, ← MvPolynomial.eval_map, AP_map, AP_eval N (N - 2) gen (fun d _ => gen_ne_zero d),
      e1]
  -- the numerator of the Cayley sum
  have hmesh : ∀ i j, algebraMap _ RF (pkGMeshP N i j) = mesh N gen i j := by
    intro i j
    simp only [pkGMeshP, map_sub, map_add, planarP_hom]
    rfl
  -- `Q_U` as a polynomial, and its complement symmetry `Q_U = Q_{Uᶜ}`
  let qP : Finset ℕ → MvPolynomial (ℕ × ℕ) ℚ := fun U =>
    ∑ p ∈ (U ×ˢ U).filter (fun p => p.1 < p.2), -pkGMeshP N p.1 p.2
  have hqP : ∀ U : Finset ℕ, U ⊆ Icc 1 N → qP U = qP (Icc 1 N \ U) := by
    intro U hU
    refine MvPolynomial.funext fun x => ?_
    have e : ∀ V, MvPolynomial.eval x (qP V) = pkGQ N x V := fun V => by
      simp only [qP, map_sum, map_neg, pkG_meshP_eval, pkGQ]
    rw [e, e]
    exact pkG_A4_all hN2 x U hU
  have hV : ∀ D ∈ pkGDis N, ∀ r ∈ pkGRoots N D,
      algebraMap _ RF (pkGVp N D r) = faceVertex N gen (pkGVerts D r) := by
    intro D hD r hr
    have hW : qP (pkGU D r) = qP (pkGW N D r) := by
      by_cases h : r.1 % 2 = 1
      · simp only [pkGW, h, ↓reduceIte]
      · simp only [pkGW, h, ↓reduceIte]
        exact hqP _ (pkG_U_Icc hN hE hD hr)
    have e : pkGVp N D r = MvPolynomial.C (pkGSgn (pkGVerts D r).card) * qP (pkGU D r) := rfl
    rw [e, hW, pkG_W_eq_oddStartLegs hN hE hD hr]
    simp only [qP, faceVertex, pkGSgn, map_mul, map_sum, map_neg, hmesh, map_pow, map_one]
  have hCP : algebraMap _ RF (pkGCP N) = cayleySum N gen * ∏ d ∈ oddDiagonals N, gen d := by
    simp only [pkGCP, cayleySum, map_sum, map_mul, map_pow, map_neg, map_one, map_prod, sum_mul]
    refine sum_congr rfl fun D hD => ?_
    rw [faces_eq_image hN hE hD, prod_image (pkG_verts_injOn hN hE hD), prod_congr rfl (hV D hD)]
    have hsub := (pkG_mem_dis.1 hD).1
    have h1 : (∏ P ∈ D, -(gen P)⁻¹) * ∏ P ∈ D, gen P = (-1 : RF) ^ D.card := by
      rw [← prod_mul_distrib, prod_congr rfl (fun P _ => show -(gen P)⁻¹ * gen P = -1 by
        rw [neg_mul, inv_mul_cancel₀ (gen_ne_zero P)]), prod_const]
    rw [← prod_sdiff hsub, ← h1]
    simp only [gen]
    ring
  have hP := congrArg (algebraMap _ RF) (pkG_thmI_poly N hN hE)
  rw [map_neg, hNP, hCP] at hP
  have hden : ∏ d ∈ oddDiagonals N, gen d ≠ 0 := prod_ne_zero_iff.2 fun d _ => gen_ne_zero d
  have h2 : (NLSM N gen + cayleySum N gen) * ∏ d ∈ oddDiagonals N, gen d = 0 := by
    rw [add_mul, hP]
    ring
  rw [eq_neg_iff_add_eq_zero]
  exact (mul_eq_zero.1 h2).resolve_right hden

/-! ## The first-order term: order count and a vanishing face -/

-- registry: C-WFCW
/-- The face identity: for even `N ≥ 4`, every dissection `D`, face `f` and set `S` of
pairs, with
`U_e := evens(U_f)` and `U^c_o := odds(U_fᶜ)`, as forms on the planar variables,
`Q_{U_f} = Σ_{x ∈ U_e, y ∈ U^c_o} c_{x,y} + E − Σ^{ee}_{U_fᶜ} − Σ^{oo}_{U_f}`; put
`ℓ_f := E − Σ^{ee}_{U_fᶜ} − Σ^{oo}_{U_f}`. If at most one chord side of `f` lies outside `𝒫₀`, then
`V_f` vanishes on the same-parity sublocus `L_S^0` (`L_{S ∪ Same}`) and `V_f ≡ sgn_f ℓ_f` on `L_S`.
For `D = ∅`, `−V_{[1..N]} = ε_N E` with `ε_N = (−1)^{(N−2)/2}`. -/
theorem Amplitudes.Kinematics.Mesh.face_identity {N : ℕ} (hN : 4 ≤ N) (hE : Even N)
    {D : Finset (ℕ × ℕ)} (hD : D ∈ pkGDis N) :
    (∀ F ∈ faces N D,
      (∀ X : ℕ × ℕ → ℚ, pkGQ N X (oddStartLegs N F) =
        ∑ p ∈ evens (oddStartLegs N F) ×ˢ odds (Icc 1 N \ oddStartLegs N F),
          mesh N X (min p.1 p.2) (max p.1 p.2) +
        pkGE N X - pkGSee N X (Icc 1 N \ oddStartLegs N F) - pkGSoo N X (oddStartLegs N F)) ∧
      ∀ S : Finset (ℕ × ℕ), (chordSides D F \ cleanChords N S).card ≤ 1 →
        (∀ X : ℕ × ℕ → ℚ, OnLocus N (S ∪ pkGSame N) X → faceVertex N X F = 0) ∧
        ∀ X : ℕ × ℕ → ℚ, OnLocus N S X → faceVertex N X F = (-1) ^ (F.card / 2 - 1) *
          (pkGE N X - pkGSee N X (Icc 1 N \ oddStartLegs N F) - pkGSoo N X (oddStartLegs N F))) ∧
    ∀ X : ℕ × ℕ → ℚ, -faceVertex N X (Icc 1 N) = (-1) ^ ((N - 2) / 2) * pkGE N X := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  have hN2 : 2 ≤ N := by omega
  refine ⟨fun F hF => ?_, fun X => ?_⟩
  · rw [faces_eq_image hN hE' hD] at hF
    obtain ⟨r, hr, rfl⟩ := mem_image.1 hF
    have hW := pkG_W_eq_oddStartLegs hN hE' hD hr
    have hWI := pkG_W_Icc hN hE' hD hr
    rw [hW] at hWI
    refine ⟨fun X => pkG_A5_all hN2 X _ hWI, fun S hS => ⟨fun X hL => ?_, fun X hL => ?_⟩⟩
    · rw [← pkG_V_eq_faceVertex hN hE hD hr]
      exact pkG_V_base hN hE' hD hr S (by rwa [pkG_deg_eq_card_chordSides hN hE' hD hr]) X
        (pkG_A4_all hN2 X) (pkG_A5_all hN2 X) hL
    · have hc := pkG_cross_zero hN hE' hD hr (cleanChords N S)
        (by rwa [pkG_deg_eq_card_chordSides hN hE' hD hr]) X
        (fun _R _ hR p hp => hL p (pkG_clean_minRect hR hp))
      rw [hW] at hc
      rw [faceVertex_eq_Q, pkG_A5_all hN2 X _ hWI]
      rw [hc]
      ring
  · have hD0 : (∅ : Finset (ℕ × ℕ)) ∈ pkGDis N := pkG_mem_dis.2 ⟨empty_subset _, by simp⟩
    have hr0 : (1, N) ∈ pkGRoots N ∅ := mem_insert_self _ _
    have hv : pkGVerts ∅ (1, N) = Icc 1 N := by
      ext w
      rw [pkG_mem_verts, pkG_kids_empty, mem_Icc]
      simp
    rw [← hv, ← pkG_V_eq_faceVertex hN hE hD0 hr0, pkG_V_empty hN hE' X]
    have : N / 2 + 1 = (N - 2) / 2 + 2 := by omega
    rw [this, pow_add]
    ring

-- registry: C-JTCE
/-- The order count: for even `N ≥ 4` and a dissection `D` with a chord outside `𝒫₀`, the
number `k_D` of faces of `D` with at most one chord side outside `𝒫₀` is at least
`p_D + 2`, `p_D = |D ∩ 𝒫₀|`. -/
theorem Combinatorics.Polygons.dissection_face_count {N : ℕ} (hN : 4 ≤ N) (hE : Even N)
    (S : Finset (ℕ × ℕ)) {D : Finset (ℕ × ℕ)} (hD : D ∈ pkGDis N) (hDP : ¬ D ⊆ cleanChords N S) :
    (D ∩ cleanChords N S).card + 2 ≤
      ((faces N D).filter (fun F => (chordSides D F \ cleanChords N S).card ≤ 1)).card := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  have h := pkG_G3_clean hN hE' hD _ (sdiff_nonempty.2 hDP)
  rw [faces_eq_image hN hE' hD, filter_image, card_image_of_injOn
    ((pkG_verts_injOn hN hE' hD).mono (filter_subset _ _))]
  refine h.trans (le_of_eq (congrArg card (filter_congr fun r hr => ?_)))
  rw [pkG_deg_eq_card_chordSides hN hE' hD hr]

-- registry: C-HN6D
/-- A vanishing face: let `N ≥ 4` be even, `∅ ≠ D ⊆ 𝒫₀` a dissection and
`P ∈ D`. If `o_in(P) = ∅` or `e_in(P) = ∅` (no missing odd–odd pair inside the odd-ended side of
`P`, or no missing even–even pair inside its even-ended side), some face `h` of `D` has `V_h ≡ 0` on
`L_S`. So if `𝒫₁ = ∅`, every non-empty `D ⊆ 𝒫₀` has a face `h` with `V_h ≡ 0` on `L_S`. -/
theorem Amplitudes.Kinematics.Mesh.on_shell_dissection_has_vanishing_face {N : ℕ} (hN : 4 ≤ N)
    (hE : Even N) {S D : Finset (ℕ × ℕ)} (hD : D ∈ pkGDis N) (hsub : D ⊆ cleanChords N S)
    (hne : D.Nonempty) :
    (∀ P ∈ D, innerOO N S P = ∅ ∨ innerEE N S P = ∅ →
      ∃ F ∈ faces N D, ∀ X : ℕ × ℕ → ℚ, OnLocus N S X → faceVertex N X F = 0) ∧
    (poleChords N S = ∅ →
      ∃ F ∈ faces N D, ∀ X : ℕ × ℕ → ℚ, OnLocus N S X → faceVertex N X F = 0) := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  have conv : ∀ r ∈ pkGRoots N D, (∀ X : ℕ × ℕ → ℚ, OnLocus N S X → pkGV N X D r = 0) →
      ∃ F ∈ faces N D, ∀ X : ℕ × ℕ → ℚ, OnLocus N S X → faceVertex N X F = 0 :=
    fun r hr h => ⟨pkGVerts D r, by rw [faces_eq_image hN hE' hD]; exact mem_image_of_mem _ hr,
      fun X hL => pkG_V_eq_faceVertex hN hE hD hr X ▸ h X hL⟩
  have hA4 : ∀ X : ℕ × ℕ → ℚ, pkGA4 N X := fun X => pkG_A4_all (by omega) X
  refine ⟨fun P hP h => ?_, fun hP1 => ?_⟩
  · rcases h with h | h
    · obtain ⟨r, hr, h0⟩ := pkG_G4_o hN hE' hD hP h
      exact conv r hr h0
    · obtain ⟨r, hr, h0⟩ := pkG_G4_e hN hE' hD hP h
      exact conv r hr fun X hL => h0 X (hA4 X) hL
  · obtain ⟨r, hr, h0⟩ := pkG_G4 hN hE' hD hP1 hsub hne
    exact conv r hr fun X hL => h0 X (hA4 X) hL

-- registry: C-6CQF
/-- The first-order regime, non-vanishing without residue chords: for even `N ≥ 4` and a candidate
set `S`, if `𝒫₁ = ∅` then `NLSM_N ≢ 0` on `L_S` (a point of `L_S`, off the
odd poles, where `NLSM_N ≠ 0`). -/
theorem NLSM.Amplitude.nonvanishing_without_residue_chords {N : ℕ} (hN : 4 ≤ N) (hE : Even N)
    {S : Finset (ℕ × ℕ)} (hF : IsCandidateSet N S) (hP1 : poleChords N S = ∅) : NonzeroOn N S := by
  replace hF := (isCandidateSet_iff_inFpi hE).1 hF
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  rcases (by omega : N = 4 ∨ 6 ≤ N) with rfl | h6
  · exact pkM_base4 hF
  · exact germ_input h6 hE S hF hP1

/-! ## The three-cut theorem and its proof

The three-cut setting is the library's `ThreeSepSetting` (pinned with its parts in
`Statements.lean`): `A′ = [1, ω]` odd-ended, `W = [ω + 1, N]` with `|W| ≥ 3`, `Θ` a non-empty set of
even legs of `[2, ω − 1]`, runs `X = [x₀, x₁]` before `Y = [y₀, y₁]` of `A′ ∖ Θ` (`IsRun`) with at
least three legs each, and admissible (`AdmSepCompl`), W-avoiding (`TailAvoiding`) and reaching
separators `τ` of `B_X = C_N ∖ X` and `σ` of `B_Y`. Reaching is `y₀ ∈ τ` or `y₀` and the leg `ω + 2`
of `int W` in different components of `C_N ∖ (X ∪ τ)` (`InST`), and the mirror for `σ` and `x₁`.
`threeSepCut` is `𝒞 = 𝒞_A ∪ 𝒞_X ∪ 𝒞_Y`, with `𝒞_A = sep_{A′}(Θ)` (`runSepA`) and `𝒞_X`, `𝒞_Y` the
pairs separated by `K_X := X ∪ τ`, `K_Y := Y ∪ σ` (`InST`, the predicate of `S_G`).

The three-cut theorem is stated in its single-family form
(`three_separators_single_parity_arc_witness`), and three cuts, one parity is its corollary
(`three_separators_contain_t_separated_set`). The definitions below are its proof's: the case (EP),
and the zone set `G′` with its removal rules (A), (B), (A′), (B′), equal to the library's
`pkTZoneSet` for legs `≥ 1` (as in the setting) by `zoneSet_eq_pkT_zoneSet`. `G′` is not defined as
the walk-defined reach witness `(τ ∖ Z_X) ∪ (σ ∖ Z_Y)` of the earlier, walk-based proof, and no
relation between the two is stated; outside case (Z) they can differ, and inside it their agreement
is only computed, not proved. The names `reach_witness_*` of the convexity, two-legs and zone lemmas
follow the claims' registry slugs; they are about `G′`. `PaperTests.figure_nine_configuration` shows
that the hypotheses of the zone case can hold together. -/

-- registry: C-ZFWK
/-- **The three-cut theorem** (single-family form). In the three-cut setting (`ThreeSepSetting`),
some `G` with `|G| ≥ 2` that equals `U_e ∩ I` or `U_o ∩ I` for one cyclic arc `I` (`ConsecWit`:
`U_e` the even legs of `Θ ∪ τ ∪ σ`, `U_o` the odd legs of `τ ∪ σ`, which are the odd legs of
`Θ ∪ τ ∪ σ` since `Θ` is even) has `S_G ⊆ 𝒞 = 𝒞_A ∪ 𝒞_X ∪ 𝒞_Y` (`threeSepCut`). -/
theorem Combinatorics.Polygons.three_separators_single_parity_arc_witness {N ω x0 x1 y0 y1 : ℕ}
    {Θ τ σ : Finset ℕ} (h : ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ) :
    ∃ G, ConsecWit N Θ τ σ G ∧ sepPairs N G ⊆ threeSepCut N ω x0 x1 y0 y1 Θ τ σ :=
  threeSep_consecWit h

-- registry: C-MQ0K
/-- **Three cuts, one parity**, a corollary of the three-cut theorem: in the three-cut setting, some
`G ∈ 𝒯` (at least two legs, all of one parity) has `S_G ⊆ 𝒞`. -/
theorem Combinatorics.Polygons.three_separators_contain_t_separated_set {N ω x0 x1 y0 y1 : ℕ}
    {Θ τ σ : Finset ℕ} (h : ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ) :
    ∃ G, IsSameParitySet N G ∧ sepPairs N G ⊆ threeSepCut N ω x0 x1 y0 y1 Θ τ σ :=
  threeSep h

/-! ### Case (EP), the zone set `G′`, and the lemmas of the proof -/

-- registry: C-P2TB
/-- `K` has consecutive legs `a < b` (no leg of `K` strictly between them) with at least two legs
of `Θ` strictly between them. -/
def HasWideGap (K Θ : Finset ℕ) : Prop :=
  ∃ a ∈ K, ∃ b ∈ K, a < b ∧ (∀ k ∈ K, ¬ (a < k ∧ k < b)) ∧
    2 ≤ (Θ.filter (fun x => a < x ∧ x < b)).card

-- registry: C-P2TB
/-- Case **(EP)**: `τ` and `σ` are odd, and `K_X = X ∪ τ` or `K_Y = Y ∪ σ`
(`X = [x₀, x₁]`, `Y = [y₀, y₁]`) has consecutive legs with at least two legs of `Θ` between
them. -/
def CaseEP (x0 x1 y0 y1 : ℕ) (Θ τ σ : Finset ℕ) : Prop :=
  (∀ t ∈ τ, t % 2 = 1) ∧ (∀ s ∈ σ, s % 2 = 1) ∧
    (HasWideGap (Icc x0 x1 ∪ τ) Θ ∨ HasWideGap (Icc y0 y1 ∪ σ) Θ)

-- registry: C-P2TB
/-- `P_X`: `σ ∩ [1, x₀] = ∅`. -/
def PX (x0 : ℕ) (σ : Finset ℕ) : Prop := Disjoint σ (Icc 1 x0)

-- registry: C-P2TB
/-- `P_Y`: `τ ∩ [y₁, ω] = ∅`. -/
def PY (ω y1 : ℕ) (τ : Finset ℕ) : Prop := Disjoint τ (Icc y1 ω)

-- registry: C-P2TB
/-- A leg `t` of `τ` is **removed** (the zone case): (A) `t < x₀`,
`σ ∩ [t, x₀] = ∅`, and `P_X` holds or some `θ ∈ Θ` with `θ < t` has `σ ∩ [θ, x₀] = ∅`; or (B)
`t > y₁`, `P_X` holds, and some `θ ∈ Θ ∩ (y₁, t)` has `σ ∩ [θ, ω] = ∅`. -/
def RemovedTau (ω x0 y1 : ℕ) (Θ σ : Finset ℕ) (t : ℕ) : Prop :=
  (t < x0 ∧ Disjoint σ (Icc t x0) ∧ (PX x0 σ ∨ ∃ θ ∈ Θ, θ < t ∧ Disjoint σ (Icc θ x0))) ∨
    (y1 < t ∧ PX x0 σ ∧ ∃ θ ∈ Θ, y1 < θ ∧ θ < t ∧ Disjoint σ (Icc θ ω))

-- registry: C-P2TB
/-- A leg `s` of `σ` is **removed** (the zone case; the mirror): (A′)
`s > y₁`, `τ ∩ [y₁, s] = ∅`, and `P_Y` holds or some `θ ∈ Θ` with `θ > s` has `τ ∩ [y₁, θ] = ∅`;
or (B′) `s < x₀`, `P_Y` holds, and some `θ ∈ Θ ∩ (s, x₀)` has `τ ∩ [1, θ] = ∅`. -/
def RemovedSigma (ω x0 y1 : ℕ) (Θ τ : Finset ℕ) (s : ℕ) : Prop :=
  (y1 < s ∧ Disjoint τ (Icc y1 s) ∧ (PY ω y1 τ ∨ ∃ θ ∈ Θ, s < θ ∧ Disjoint τ (Icc y1 θ))) ∨
    (s < x0 ∧ PY ω y1 τ ∧ ∃ θ ∈ Θ, s < θ ∧ θ < x0 ∧ Disjoint τ (Icc 1 θ))

open Classical in
-- registry: C-P2TB
/-- The **zone set** `G′` (the zone case): the legs of `τ` not removed as
legs of `τ` and the legs of `σ` not removed as legs of `σ`. -/
noncomputable def zoneSet (ω x0 y1 : ℕ) (Θ τ σ : Finset ℕ) : Finset ℕ :=
  τ.filter (fun t => ¬ RemovedTau ω x0 y1 Θ σ t) ∪ σ.filter (fun s => ¬ RemovedSigma ω x0 y1 Θ τ s)

/-- `zoneSet` is the library's `pkTZoneSet` (which states the removal rules inline), for legs
`≥ 1`. -/
theorem zoneSet_eq_pkT_zoneSet {ω x0 y1 : ℕ} {Θ τ σ : Finset ℕ} (hτ : ∀ t ∈ τ, 1 ≤ t)
    (hσ : ∀ s ∈ σ, 1 ≤ s) : zoneSet ω x0 y1 Θ τ σ = pkTZoneSet ω x0 y1 Θ τ σ := by
  have hD : ∀ (D : Finset ℕ) (a b : ℕ), Disjoint D (Icc a b) ↔ ∀ d ∈ D, ¬ (a ≤ d ∧ d ≤ b) := by
    intro D a b
    simp only [disjoint_left, mem_Icc]
  have hPX : PX x0 σ ↔ ∀ s ∈ σ, ¬ s ≤ x0 := by
    rw [PX, hD]
    exact forall₂_congr fun s hs => by have := hσ s hs; omega
  have hPY : PY ω y1 τ ↔ ∀ t ∈ τ, ¬ (y1 ≤ t ∧ t ≤ ω) := by rw [PY, hD]
  have hB' : ∀ θ, Disjoint τ (Icc 1 θ) ↔ ∀ t ∈ τ, ¬ t ≤ θ := fun θ => by
    rw [hD]
    exact forall₂_congr fun t ht => by have := hτ t ht; omega
  ext g
  simp only [zoneSet, pkTZoneSet, mem_union, mem_filter, RemovedTau, RemovedSigma, hPX, hPY, hB']
  simp only [hD]

/-- Case (Z), in the form of the library's bundle `pkTZH`. -/
theorem pkT_ZH_of_not_caseEP {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ}
    (h : ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ) (hτ : ∀ t ∈ τ, t % 2 = 1)
    (hσ : ∀ s ∈ σ, s % 2 = 1) (hEP : ¬ CaseEP x0 x1 y0 y1 Θ τ σ) :
    pkTZH N ω x0 x1 y0 y1 Θ τ σ := by
  have hn : ∀ {K : Finset ℕ}, ¬ HasWideGap K Θ → ∀ a ∈ K, ∀ b ∈ K, a < b →
      (∀ k ∈ K, ¬ (a < k ∧ k < b)) → (Θ.filter (fun x => a < x ∧ x < b)).card ≤ 1 := by
    intro K hK a ha b hb hab hgap
    by_contra hc
    exact hK ⟨a, ha, b, hb, hab, hgap, by omega⟩
  exact pkT_ZH_iff.2 ⟨h, hτ, hσ, hn fun hX => hEP ⟨hτ, hσ, Or.inl hX⟩,
    hn fun hY => hEP ⟨hτ, hσ, Or.inr hY⟩⟩

-- registry: C-BPM0
/-- **Block lemma**. Let `K` be a set of legs and `a, b ∈ K` with no leg of `K` strictly
between them and `b ≤ ω + 1`. Let `G ⊆ [a, b]` agree with `Θ` strictly inside `(a, b)`,
let every leg of `K` outside `G` lie in `A′ ∖ Θ` (`A′ = [1, ω]`), and if an end of `[a, b]` lies in
`G ∖ Θ`, let it be extreme in `K` (`b ∈ G ∖ Θ ⇒ K ⊆ [1, b]`; `a ∈ G ∖ Θ ⇒ K ⊆ [a, N]`). Then every
pair separated by `G` is in `𝒞_A` (`runSepA`) or separated by `K`. (The paper's `a < b` is not
needed, and neither is that `K`'s legs lie in `1..N`, nor the rest of the setting: `N` even, and the
conditions on `Θ` and `ω`; so the statement is stronger.) -/
theorem Combinatorics.Polygons.parity_block_witness_in_cut {N ω : ℕ} {Θ K G : Finset ℕ} {a b : ℕ}
    (ha : a ∈ K) (hb : b ∈ K) (hK : ∀ k ∈ K, ¬ (a < k ∧ k < b)) (hbω : b ≤ ω + 1)
    (hG : G ⊆ Icc a b) (hGΘ : ∀ x, a < x → x < b → (x ∈ G ↔ x ∈ Θ))
    (hKA : ∀ k ∈ K, k ∉ G → k ∈ Icc 1 ω ∧ k ∉ Θ)
    (hbx : b ∈ G → b ∉ Θ → K ⊆ Icc 1 b) (hax : a ∈ G → a ∉ Θ → K ⊆ Icc a N) :
    ∀ p ∈ sepPairs N G, runSepA ω Θ p.1 p.2 ∨ InST K p.1 p.2 := by
  intro p hp
  obtain ⟨hpd, hpG⟩ := pkT_mem_sepPairs.1 hp
  have hlt : p.1 < p.2 := by
    obtain ⟨-, h1⟩ := mem_filter.1 hpd
    omega
  exact pkT_block ha hb (fun g hg => mem_Icc.1 (hG hg)) hGΘ hK hbω
    (fun k hk hkG => by
      obtain ⟨hk1, hk2⟩ := hKA k hk hkG
      exact ⟨(mem_Icc.1 hk1).1, (mem_Icc.1 hk1).2, hk2⟩)
    (fun hbG hbΘ k hk => (mem_Icc.1 (hbx hbG hbΘ hk)).2)
    (fun haG haΘ k hk => (mem_Icc.1 (hax haG haΘ hk)).1) hlt hpG

-- registry: C-SDMT
/-- **Gap lemma**, part (a). In case (Z) (`τ`, `σ` odd and not (EP)), for `K ∈ {K_X, K_Y}`: if
`p < q` are legs of `Θ` and `K` has a leg below `p` and a leg above `q`, then `K` has a leg in
`[p, q]`. (The rest of the setting is not needed.) -/
theorem Combinatorics.Polygons.separator_meets_every_gap_interval {x0 x1 y0 y1 : ℕ}
    {Θ τ σ : Finset ℕ} (hτ : ∀ t ∈ τ, t % 2 = 1) (hσ : ∀ s ∈ σ, s % 2 = 1)
    (hEP : ¬ CaseEP x0 x1 y0 y1 Θ τ σ) {K : Finset ℕ} (hK : K = Icc x0 x1 ∪ τ ∨ K = Icc y0 y1 ∪ σ)
    {p q : ℕ} (hp : p ∈ Θ) (hq : q ∈ Θ) (hpq : p < q) (hlo : ∃ k ∈ K, k < p)
    (hhi : ∃ k ∈ K, q < k) :
    ∃ k ∈ K, p ≤ k ∧ k ≤ q := by
  have hn : ¬ HasWideGap K Θ := by
    rcases hK with rfl | rfl
    · exact fun hX => hEP ⟨hτ, hσ, Or.inl hX⟩
    · exact fun hY => hEP ⟨hτ, hσ, Or.inr hY⟩
  obtain ⟨a0, ha0, h1⟩ := hlo
  obtain ⟨b0, hb0, h2⟩ := hhi
  refine pkT_gap (fun a ha b hb hab hgap => ?_) hp hq hpq ha0 h1 hb0 h2
  by_contra hc
  exact hn ⟨a, ha, b, hb, hab, hgap, by omega⟩

-- registry: C-SDMT
/-- **Gap lemma**, part (b) for `τ`. In case (Z) (`τ`, `σ` odd and not (EP)), a leg `t`
of `τ` is removed if and only if `P_X` holds (`X` is exposed) and either `t < x₀`, or `t > y₁` and
some `θ ∈ Θ` with `y₁ < θ < t` has `σ ∩ [θ, ω] = ∅`. In particular a removed leg of `τ` makes `X`
exposed. (The paper's `t ∈ τ` is not needed: the rules are stated for any `t`. So the statement is
stronger.) -/
theorem Combinatorics.Polygons.removed_leg_of_tau_iff {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ}
    (h : ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ) (hτ : ∀ t ∈ τ, t % 2 = 1)
    (hσ : ∀ s ∈ σ, s % 2 = 1) (hEP : ¬ CaseEP x0 x1 y0 y1 Θ τ σ) {t : ℕ} :
    RemovedTau ω x0 y1 Θ σ t ↔
      PX x0 σ ∧ (t < x0 ∨ (y1 < t ∧ ∃ θ ∈ Θ, y1 < θ ∧ θ < t ∧ Disjoint σ (Icc θ ω))) := by
  have H := pkT_ZH_of_not_caseEP h hτ hσ hEP
  obtain ⟨-, -, -, -, hσf, -, -⟩ := pkT_zf H
  have hD : ∀ (D : Finset ℕ) (a b : ℕ), Disjoint D (Icc a b) ↔ ∀ d ∈ D, ¬ (a ≤ d ∧ d ≤ b) := by
    intro D a b
    simp only [disjoint_left, mem_Icc]
  have hPX : PX x0 σ ↔ ∀ s ∈ σ, ¬ s ≤ x0 := by
    rw [PX, hD]
    exact forall₂_congr fun s hs => by have := (hσf s hs).1; omega
  have hR : RemovedTau ω x0 y1 Θ σ t ↔ pkTRemT ω x0 y1 Θ σ t := by
    simp only [RemovedTau, pkTRemT, hPX, hD]
  rw [hR, hPX]
  constructor
  · intro hr
    refine ⟨pkT_remT_PX H hr, ?_⟩
    rcases hr with ⟨h1, -⟩ | ⟨h1, -, θ, hθ, h2, h3, h4⟩
    · exact Or.inl h1
    · exact Or.inr ⟨h1, θ, hθ, h2, h3, (hD σ θ ω).2 h4⟩
  · rintro ⟨hP, h1 | ⟨h1, θ, hθ, h2, h3, h4⟩⟩
    · exact pkT_remT_of_A h1 hP
    · exact pkT_remT_of_B h1 hP hθ h2 h3 ((hD σ θ ω).1 h4)

-- registry: C-SDMT
/-- **Gap lemma**, part (b) for `σ` (the mirror). In case (Z), a leg `s` of `σ` is removed
if and only if `P_Y` holds (`Y` is exposed) and either `s > y₁`, or `s < x₀` and some `θ ∈ Θ` with
`s < θ < x₀` has `τ ∩ [1, θ] = ∅`. (Here `s ∈ σ` is needed, unlike `t ∈ τ` in the mirror: for
`s > ω`, `P_Y` does not give `τ ∩ [y₁, s] = ∅`.) -/
theorem Combinatorics.Polygons.removed_leg_of_sigma_iff {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ}
    (h : ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ) (hτ : ∀ t ∈ τ, t % 2 = 1)
    (hσ : ∀ s ∈ σ, s % 2 = 1) (hEP : ¬ CaseEP x0 x1 y0 y1 Θ τ σ) {s : ℕ} (hs : s ∈ σ) :
    RemovedSigma ω x0 y1 Θ τ s ↔
      PY ω y1 τ ∧ (y1 < s ∨ (s < x0 ∧ ∃ θ ∈ Θ, s < θ ∧ θ < x0 ∧ Disjoint τ (Icc 1 θ))) := by
  have H := pkT_ZH_of_not_caseEP h hτ hσ hEP
  obtain ⟨-, -, -, hτf, hσf, -, -⟩ := pkT_zf H
  have hD : ∀ (D : Finset ℕ) (a b : ℕ), Disjoint D (Icc a b) ↔ ∀ d ∈ D, ¬ (a ≤ d ∧ d ≤ b) := by
    intro D a b
    simp only [disjoint_left, mem_Icc]
  have hPY : PY ω y1 τ ↔ ∀ t ∈ τ, ¬ (y1 ≤ t ∧ t ≤ ω) := by rw [PY, hD]
  have hB' : ∀ θ, Disjoint τ (Icc 1 θ) ↔ ∀ t ∈ τ, ¬ t ≤ θ := fun θ => by
    rw [hD]
    exact forall₂_congr fun t ht => by have := (hτf t ht).1; omega
  have hR : RemovedSigma ω x0 y1 Θ τ s ↔ pkTRemS ω x0 y1 Θ τ s := by
    simp only [RemovedSigma, pkTRemS, hPY, hB']
    simp only [hD]
  rw [hR, hPY]
  constructor
  · intro hr
    refine ⟨pkT_remS_PY H hr, ?_⟩
    rcases hr with ⟨h1, -⟩ | ⟨h1, -, θ, hθ, h2, h3, h4⟩
    · exact Or.inl h1
    · exact Or.inr ⟨h1, θ, hθ, h2, h3, (hB' θ).2 h4⟩
  · rintro ⟨hP, h1 | ⟨h1, θ, hθ, h2, h3, h4⟩⟩
    · exact pkT_remS_of_A h1 (hσf s hs).2.1 hP
    · exact pkT_remS_of_B h1 hP hθ h2 h3 ((hB' θ).1 h4)

-- registry: C-SDMT
/-- **Gap lemma**, part (c), side gap (Γσ). In case (Z), with `γ = x₁ + 1`: if `q ∈ Θ`
and `γ < q < y₀`, then `σ` has a leg in `(γ, q)`. -/
theorem Combinatorics.Polygons.side_gap_gamma_sigma {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ}
    (h : ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ) (hτ : ∀ t ∈ τ, t % 2 = 1)
    (hσ : ∀ s ∈ σ, s % 2 = 1) (hEP : ¬ CaseEP x0 x1 y0 y1 Θ τ σ) {q : ℕ} (hq : q ∈ Θ)
    (h1 : x1 + 1 < q) (h2 : q < y0) : ∃ k ∈ σ, x1 + 1 < k ∧ k < q :=
  pkT_WgY (pkT_ZH_of_not_caseEP h hτ hσ hEP) hq h1 h2

-- registry: C-SDMT
/-- **Gap lemma**, part (c), side gap (Γτ). In case (Z), with `γ′ = y₀ − 1`: if `p ∈ Θ`
and `x₁ < p < γ′`, then `τ` has a leg in `(p, γ′)`. -/
theorem Combinatorics.Polygons.side_gap_gamma_tau {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ}
    (h : ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ) (hτ : ∀ t ∈ τ, t % 2 = 1)
    (hσ : ∀ s ∈ σ, s % 2 = 1) (hEP : ¬ CaseEP x0 x1 y0 y1 Θ τ σ) {p : ℕ} (hp : p ∈ Θ)
    (h1 : x1 < p) (h2 : p < y0 - 1) : ∃ k ∈ τ, p < k ∧ k < y0 - 1 :=
  pkT_WgX (pkT_ZH_of_not_caseEP h hτ hσ hEP) hp h1 h2

-- registry: C-SDMT
/-- **Gap lemma**, part (c), side gap (Lσ). In case (Z): if `p ∈ Θ`, `p < x₀ − 1`, and
`σ` has a leg below `p`, then `σ` has a leg in `(p, x₀ − 1)`. -/
theorem Combinatorics.Polygons.side_gap_left_sigma {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ}
    (h : ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ) (hτ : ∀ t ∈ τ, t % 2 = 1)
    (hσ : ∀ s ∈ σ, s % 2 = 1) (hEP : ¬ CaseEP x0 x1 y0 y1 Θ τ σ) {p : ℕ} (hp : p ∈ Θ)
    (h1 : p < x0 - 1) (hlo : ∃ s ∈ σ, s < p) : ∃ k ∈ σ, p < k ∧ k < x0 - 1 := by
  obtain ⟨s, hs, hsp⟩ := hlo
  exact pkT_WlY (pkT_ZH_of_not_caseEP h hτ hσ hEP) hp (by omega) hs hsp

-- registry: C-SDMT
/-- **Gap lemma**, part (c), side gap (Rτ). In case (Z): if `q ∈ Θ`, `q > y₁ + 1`, and
`τ` has a leg above `q`, then `τ` has a leg in `(y₁ + 1, q)`. -/
theorem Combinatorics.Polygons.side_gap_right_tau {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ}
    (h : ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ) (hτ : ∀ t ∈ τ, t % 2 = 1)
    (hσ : ∀ s ∈ σ, s % 2 = 1) (hEP : ¬ CaseEP x0 x1 y0 y1 Θ τ σ) {q : ℕ} (hq : q ∈ Θ)
    (h1 : y1 + 1 < q) (hhi : ∃ t ∈ τ, q < t) : ∃ k ∈ τ, y1 + 1 < k ∧ k < q := by
  obtain ⟨t, ht, htq⟩ := hhi
  exact pkT_WrX (pkT_ZH_of_not_caseEP h hτ hσ hEP) hq h1 ht htq

-- registry: C-SDMT
/-- **Gap lemma**, part (d), first half. In case (Z), every leg of `τ ∪ σ` in `[x₀, y₁]`
is kept: it is in `G′`. -/
theorem Combinatorics.Polygons.zoneSet_keeps_middle_legs {N ω x0 x1 y0 y1 : ℕ}
    {Θ τ σ : Finset ℕ} (h : ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ) (hτ : ∀ t ∈ τ, t % 2 = 1)
    (hσ : ∀ s ∈ σ, s % 2 = 1) (hEP : ¬ CaseEP x0 x1 y0 y1 Θ τ σ) {g : ℕ} (hg : g ∈ τ ∪ σ)
    (h1 : x0 ≤ g) (h2 : g ≤ y1) : g ∈ zoneSet ω x0 y1 Θ τ σ := by
  have H := pkT_ZH_of_not_caseEP h hτ hσ hEP
  obtain ⟨-, -, -, hτf, hσf, -, -⟩ := pkT_zf H
  rw [zoneSet_eq_pkT_zoneSet (fun t ht => (hτf t ht).1) (fun s hs => (hσf s hs).1)]
  exact pkT_mid_G (mem_union.1 hg) h1 h2

-- registry: C-SDMT
/-- **Gap lemma**, part (d), second half. In case (Z), every leg of `τ ∩ σ` is kept: it is
in `G′`. -/
theorem Combinatorics.Polygons.zoneSet_keeps_common_legs {N ω x0 x1 y0 y1 : ℕ}
    {Θ τ σ : Finset ℕ} (h : ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ) (hτ : ∀ t ∈ τ, t % 2 = 1)
    (hσ : ∀ s ∈ σ, s % 2 = 1) (hEP : ¬ CaseEP x0 x1 y0 y1 Θ τ σ) {g : ℕ} (hg : g ∈ τ ∩ σ) :
    g ∈ zoneSet ω x0 y1 Θ τ σ := by
  have H := pkT_ZH_of_not_caseEP h hτ hσ hEP
  obtain ⟨-, -, -, hτf, hσf, -, -⟩ := pkT_zf H
  rw [zoneSet_eq_pkT_zoneSet (fun t ht => (hτf t ht).1) (fun s hs => (hσf s hs).1)]
  by_contra hG
  exact pkT_notBoth H (mem_inter.1 hg).1 (mem_inter.1 hg).2 hG

-- registry: C-PPX4
/-- **Convexity**. In case (Z) (`τ`, `σ` odd and not (EP)), `G′` is a linear interval of
odd legs in `[1, ω]`: `G′ ⊆ [1, ω]` and `G′ = U_o ∩ [min G′, max G′]`, `U_o` the odd legs of
`τ ∪ σ`. -/
theorem Combinatorics.Polygons.reach_witness_is_odd_interval {N ω x0 x1 y0 y1 : ℕ}
    {Θ τ σ : Finset ℕ} (h : ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ) (hτ : ∀ t ∈ τ, t % 2 = 1)
    (hσ : ∀ s ∈ σ, s % 2 = 1) (hEP : ¬ CaseEP x0 x1 y0 y1 Θ τ σ) :
    zoneSet ω x0 y1 Θ τ σ ⊆ Icc 1 ω ∧ ∀ hne : (zoneSet ω x0 y1 Θ τ σ).Nonempty,
      zoneSet ω x0 y1 Θ τ σ = odds (τ ∪ σ) ∩
        Icc ((zoneSet ω x0 y1 Θ τ σ).min' hne) ((zoneSet ω x0 y1 Θ τ σ).max' hne) := by
  have H := pkT_ZH_of_not_caseEP h hτ hσ hEP
  obtain ⟨⟨-, -, -, -, -, hωN⟩, -, -, hτf, hσf, -, -⟩ := pkT_zf H
  rw [zoneSet_eq_pkT_zoneSet (fun t ht => (hτf t ht).1) (fun s hs => (hσf s hs).1)]
  obtain ⟨α, β, hα, hαβ, hβ, hG⟩ := pkT_zone_block' H
  have hmem : ∀ x, x ∈ pkTZoneSet ω x0 y1 Θ τ σ ↔ x ∈ odds (τ ∪ σ) ∧ α ≤ x ∧ x ≤ β := by
    intro x
    rw [hG, mem_inter, pkT_mem_cycArc_lin hα (by omega)]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, by omega⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, by omega⟩
  refine ⟨fun x hx => mem_Icc.2 (by have := (hmem x).1 hx; omega), fun hne => ?_⟩
  have hmin := (hmem _).1 ((pkTZoneSet ω x0 y1 Θ τ σ).min'_mem hne)
  have hmax := (hmem _).1 ((pkTZoneSet ω x0 y1 Θ τ σ).max'_mem hne)
  ext x
  rw [mem_inter, mem_Icc]
  constructor
  · intro hx
    exact ⟨((hmem x).1 hx).1, min'_le _ x hx, le_max' _ x hx⟩
  · rintro ⟨hxo, h1, h2⟩
    exact (hmem x).2 ⟨hxo, by omega, by omega⟩

-- registry: C-N4BE
/-- **Two legs**. In case (Z) (`τ`, `σ` odd and not (EP)), `|G′| ≥ 2`. -/
theorem Combinatorics.Polygons.reach_witness_has_two_legs {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ}
    (h : ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ) (hτ : ∀ t ∈ τ, t % 2 = 1)
    (hσ : ∀ s ∈ σ, s % 2 = 1) (hEP : ¬ CaseEP x0 x1 y0 y1 Θ τ σ) :
    2 ≤ (zoneSet ω x0 y1 Θ τ σ).card := by
  have H := pkT_ZH_of_not_caseEP h hτ hσ hEP
  obtain ⟨-, -, -, hτf, hσf, -, -⟩ := pkT_zf H
  rw [zoneSet_eq_pkT_zoneSet (fun t ht => (hτf t ht).1) (fun s hs => (hσf s hs).1)]
  exact pkT_zone_card' H

-- registry: C-60FM
/-- **Zone lemma**. In case (Z) (`τ`, `σ` odd and not (EP)), `S_{G′} ⊆ 𝒞`. -/
theorem Combinatorics.Polygons.reach_witness_pairs_in_cut {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ}
    (h : ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ) (hτ : ∀ t ∈ τ, t % 2 = 1)
    (hσ : ∀ s ∈ σ, s % 2 = 1) (hEP : ¬ CaseEP x0 x1 y0 y1 Θ τ σ) :
    sepPairs N (zoneSet ω x0 y1 Θ τ σ) ⊆ threeSepCut N ω x0 x1 y0 y1 Θ τ σ := by
  have H := pkT_ZH_of_not_caseEP h hτ hσ hEP
  obtain ⟨-, -, -, hτf, hσf, -, -⟩ := pkT_zf H
  rw [zoneSet_eq_pkT_zoneSet (fun t ht => (hτf t ht).1) (fun s hs => (hσf s hs).1)]
  exact pkT_zone_sep' H

/-! ## Innermost chords and the residue argument -/

-- registry: C-CXW0
/-- **Descent to a smaller side**, (B): for even `N ≥ 6`, if `P ∈ 𝒫₁` has its
even-ended side `B_P` not linked, some `Q ∈ 𝒫₁` has `|B_Q| < |B_P|`. No hypothesis on `S`. (The
paper's mirror (A) is a remark, not used and not formalised.) -/
theorem Combinatorics.Polygons.descent_to_smaller_side {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ} (hP : P ∈ poleChords N S)
    (hB : ¬ NoFreeSep N S (tailStart P) (tailLen N P) 1) :
    ∃ Q ∈ poleChords N S, (evenSide N Q).card < (evenSide N P).card := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  obtain ⟨Q, hQ, hlt⟩ := pkCh_Xall_B hN hE' hP hB
  have card : ∀ R ∈ poleChords N S, (evenSide N R).card = tailLen N R := fun R hR => by
    have hRo := (pkCh_mem_pole.1 hR).1
    obtain ⟨hts, -, -, -, htlN, -⟩ := pkCh_sides hE' hRo
    rw [(sides_eq_cycArc (by omega) hE hRo).2, pkCo_card_cycArc hts (by omega)]
  exact ⟨Q, hQ, by rw [card Q hQ, card P hP]; exact hlt⟩

-- registry: C-TM1K
/-- Innermost chords exist: at even `N ≥ 6`, for any set of pairs with `𝒫₁ ≠ ∅`, some chord of
`𝒫₁` has a linked even-ended side (`𝒮_B ≠ ∅`), and an innermost chord exists. -/
theorem Combinatorics.Polygons.innermost_chord_exists {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    {S : Finset (ℕ × ℕ)} (hP : (poleChords N S).Nonempty) :
    (goodTail N S).Nonempty ∧ ∃ P, IsInnermostChord N S P := by
  obtain ⟨P, hPm⟩ := can_exists hN hE hP
  exact ⟨⟨P, (pkCh_minChord_iff.1 hPm).1⟩, P, hPm⟩

-- registry: C-74RW
/-- **Containment**, main form: for even `N ≥ 6`, let `P ∈ 𝒫₁` have its even-ended
side `B_P` linked, and `Q ∈ 𝒫₀` with `e_in(Q) ⊇ e_in(P)` and `A_Q ∩ A_P ≠ ∅`. Then
`A_Q ⊆ A_P`. No hypothesis on `S`. -/
theorem Combinatorics.Polygons.odd_side_nesting {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    {S : Finset (ℕ × ℕ)} {P Q : ℕ × ℕ} (hP : P ∈ poleChords N S)
    (hPB : NoFreeSep N S (tailStart P) (tailLen N P) 1) (hQ : Q ∈ cleanChords N S)
    (hee : innerEE N S P ⊆ innerEE N S Q) (hmeet : (oddSide N Q ∩ oddSide N P).Nonempty) :
    oddSide N Q ⊆ oddSide N P := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  obtain ⟨hPo, -, -, -⟩ := pkCh_mem_pole.1 hP
  have hQo : Q ∈ oddDiagonals N := (mem_filter.1 hQ).1
  have hQr : Disjoint (minRect N Q) (missing N S) := (mem_filter.1 hQ).2
  obtain ⟨hts, hts2, htl1, htl3, htlN, hhs, hhs2, hhl1, hhl3, hhlN⟩ := pkCh_sides hE' hPo
  obtain ⟨qts, qts2, qtl1, qtl3, qtlN, qhs, qhs2, qhl1, qhl3, qhlN⟩ := pkCh_sides hE' hQo
  obtain ⟨mA, mB, mAB, -, -, -, -⟩ := pkCh_arcs (by omega) hE' hPo
  obtain ⟨qA, qB, qAB, -, -, -, -⟩ := pkCh_arcs (by omega) hE' hQo
  obtain ⟨f, hf⟩ := hmeet
  obtain ⟨hfQ, hfP⟩ := mem_inter.1 hf
  have hfI : f ∈ Icc 1 N := pkCo_cycArc_sub (by omega) ((mA f).1 hfP)
  have key := pkCh_lem5 (S :=
      S) hE' hts htl1 htl3 htlN qhs (by omega) qhl1 (by omega) qts (by omega) qAB
    (by rw [show (tailStart P + 1) % 2 = 1 by omega]; exact hPB)
    (fun e he y hy he2 hy2 => fun hm => disjoint_left.1 hQr (pkCh_mem_minRect.2 ⟨e,
      pkCh_mem_evens.2 ⟨(qA e).2 he, by omega⟩, y,
          pkCh_mem_odds.2 ⟨(qB y).2 hy, by omega⟩, rfl⟩) hm)
    (fun u v hm hu hv huL hvL => by
      have hin : (u, v) ∈ innerEE N S Q := hee (pkCh_mem_innerEE.2
        ⟨pkCh_mem_Mee.2 ⟨hm, by omega, by omega⟩, (mB u).2 huL, (mB v).2 hvL⟩)
      obtain ⟨-, hu', hv'⟩ := pkCh_mem_innerEE.1 hin
      exact ⟨(qB u).1 hu', (qB v).1 hv'⟩)
    hfI (fun h => (mAB f hfI).1 ((mA f).1 hfP) h) ((qA f).1 hfQ)
  intro x hx
  have hxI : x ∈ Icc 1 N := pkCo_cycArc_sub (by omega) ((qA x).1 hx)
  exact (mA x).2 ((mAB x hxI).2 (key x ((qA x).1 hx)))

-- registry: C-74RW
/-- **Containment**, mirror form: for even `N ≥ 6`, let `P ∈ 𝒫₁` have its odd-ended
side `A_P` linked, and `Q ∈ 𝒫₀` with `o_in(Q) ⊇ o_in(P)` and `B_Q ∩ B_P ≠ ∅`. Then
`A_P ⊆ A_Q`. No hypothesis on `S`. -/
theorem Combinatorics.Polygons.odd_side_nesting_mirror {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    {S : Finset (ℕ × ℕ)} {P Q : ℕ × ℕ} (hP : P ∈ poleChords N S)
    (hPA : NoFreeSep N S (headStart P) (headLen N P) 0) (hQ : Q ∈ cleanChords N S)
    (hoo : innerOO N S P ⊆ innerOO N S Q) (hmeet : (evenSide N Q ∩ evenSide N P).Nonempty) :
    oddSide N P ⊆ oddSide N Q := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  obtain ⟨hbo, -, -, -⟩ := pkCh_mem_pole.1 hP
  have hQo : Q ∈ oddDiagonals N := (mem_filter.1 hQ).1
  have hQr : Disjoint (minRect N Q) (missing N S) := (mem_filter.1 hQ).2
  obtain ⟨hts, hts2, htl1, htl3, htlN, hhs, hhs2, hhl1, hhl3, hhlN⟩ := pkCh_sides hE' hbo
  obtain ⟨qts, qts2, qtl1, qtl3, qtlN, qhs, qhs2, qhl1, qhl3, qhlN⟩ := pkCh_sides hE' hQo
  obtain ⟨mA, mB, mAB, -, -, -, -⟩ := pkCh_arcs (by omega) hE' hbo
  obtain ⟨qA, qB, qAB, -, -, -, -⟩ := pkCh_arcs (by omega) hE' hQo
  have qBA : ∀ x ∈ Icc 1 N, x ∈ cycArc N (tailStart Q) (tailLen N Q) ↔
      x ∉ cycArc N (headStart Q) (headLen N Q) := fun x hx => by
    rw [qAB x hx]
    exact ⟨fun h h' => h' h, fun h => by by_contra h'; exact h h'⟩
  obtain ⟨g, hg⟩ := hmeet
  obtain ⟨hgQ, hgP⟩ := mem_inter.1 hg
  have hgI : g ∈ Icc 1 N := pkCo_cycArc_sub (by omega) ((mB g).1 hgP)
  have key := pkCh_lem5 (S :=
      S) hE' hhs hhl1 hhl3 hhlN qts (by omega) qtl1 (by omega) qhs (by omega) qBA
    (by rw [show (headStart P + 1) % 2 = 0 by omega]; exact hPA)
    (fun e he y hy he2 hy2 => by
      rw [min_comm, max_comm]
      exact fun hm => disjoint_left.1 hQr (pkCh_mem_minRect.2 ⟨y,
        pkCh_mem_evens.2 ⟨(qA y).2 hy, by omega⟩, e,
            pkCh_mem_odds.2 ⟨(qB e).2 he, by omega⟩, rfl⟩) hm)
    (fun u v hm hu hv huL hvL => by
      have hin : (u, v) ∈ innerOO N S Q := hoo (pkCh_mem_innerOO.2
        ⟨pkCh_mem_Moo.2 ⟨hm, by omega, by omega⟩, (mA u).2 huL, (mA v).2 hvL⟩)
      obtain ⟨-, hu', hv'⟩ := pkCh_mem_innerOO.1 hin
      exact ⟨(qA u).1 hu', (qA v).1 hv'⟩)
    hgI (fun h => (mAB g hgI).1 h ((mB g).1 hgP)) ((qB g).1 hgQ)
  intro z hz
  have hzA := (mA z).1 hz
  have hzI : z ∈ Icc 1 N := pkCo_cycArc_sub (by omega) hzA
  by_contra hzQ
  have hzB : z ∈ cycArc N (tailStart Q) (tailLen N Q) := by
    by_contra h
    exact hzQ ((qA z).2 (by by_contra h'; exact h ((qBA z hzI).2 h')))
  exact key z hzB hzA

-- registry: C-SRY5
/-- Top and bottom: for even `N ≥ 6`, let `P* ∈ 𝒮_B` (a chord of `𝒫₁` whose
even-ended side is linked) and `K*` its flank class. (a) `P*` is the top of `K*`. (b) If `b ∈ K*`
has `A_b` linked, then `b` is the unique bottom of `K*`. Hence (Bot), "`K*` has a member `b` with
`A_b` linked", implies that `K*` has a top and a bottom. No hypothesis on `S`. -/
theorem Combinatorics.Polygons.flank_class_top_and_bottom {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ} (hP : P ∈ goodTail N S) :
    (P ∈ hitClass N S P ∧ ∀ Q ∈ hitClass N S P, oddSide N Q ⊆ oddSide N P) ∧
    (∀ b ∈ hitClass N S P, NoFreeSep N S (headStart b) (headLen N b) 0 →
      (∀ Q ∈ hitClass N S P, oddSide N b ⊆ oddSide N Q) ∧
        ∀ b' ∈ hitClass N S P, (∀ Q ∈ hitClass N S P, oddSide N b' ⊆ oddSide N Q) → b' = b) ∧
    ((∃ b ∈ hitClass N S P, NoFreeSep N S (headStart b) (headLen N b) 0) →
      (∃ t ∈ hitClass N S P, ∀ Q ∈ hitClass N S P, oddSide N Q ⊆ oddSide N t) ∧
        ∃ b ∈ hitClass N S P, ∀ Q ∈ hitClass N S P, oddSide N b ⊆ oddSide N Q) := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  obtain ⟨hPp, hPB⟩ := pkCh_mem_goodTail.1 hP
  have hPK : P ∈ hitClass N S P := pkCh_mem_hitClass.2 ⟨hPp, rfl⟩
  have top : ∀ Q ∈ hitClass N S P, oddSide N Q ⊆ oddSide N P := fun Q hQ => by
    obtain ⟨hQp, hQh⟩ := pkCh_mem_hitClass.1 hQ
    exact pkCh_int_top hN hE' hPp hPB hQp hQh
  have bot : ∀ b ∈ hitClass N S P, NoFreeSep N S (headStart b) (headLen N b) 0 →
      ∀ Q ∈ hitClass N S P, oddSide N b ⊆ oddSide N Q := fun b hb hbA Q hQ => by
    obtain ⟨hbp, hbh⟩ := pkCh_mem_hitClass.1 hb
    obtain ⟨hQp, hQh⟩ := pkCh_mem_hitClass.1 hQ
    exact pkCh_int_bot hN hE' hbp hbA hQp (hQh.trans hbh.symm)
  refine ⟨⟨hPK, top⟩, fun b hb hbA => ⟨bot b hb hbA, fun b' hb' hb'bot => ?_⟩,
    fun ⟨b, hb, hbA⟩ => ⟨⟨P, hPK, top⟩, ⟨b, hb, bot b hb hbA⟩⟩⟩
  -- two bottoms have the same odd-ended side, and a chord is determined by its odd-ended side
  have hb'o := pkM_poleChords_odd (pkCh_mem_hitClass.1 hb').1
  have hbo := pkM_poleChords_odd (pkCh_mem_hitClass.1 hb).1
  exact pkR_d2_eq_of_head hb'o hbo
    (Subset.antisymm (hb'bot b hb) (bot b hb hbA b' hb'))

-- registry: C-2G26
/-- W-avoidance: for even `N`, let `P′` be an odd chord whose even-ended side `B′` is linked, and
`Q` an odd chord with `A_Q ⊆ A′`. Then every free admissible separator `τ` of `B_Q` avoids the
interior of `B′`, and one made of odd legs avoids `B′`. No hypothesis on `S`. -/
theorem Combinatorics.Polygons.separators_avoid_linked_side {N : ℕ} (hE : Even N)
    {S : Finset (ℕ × ℕ)} {P Q : ℕ × ℕ} (hP : P ∈ oddDiagonals N)
    (hlinked : NoFreeSep N S (tailStart P) (tailLen N P) 1) (hQ : Q ∈ oddDiagonals N)
    (hsub : oddSide N Q ⊆ oddSide N P) {τ : Finset ℕ}
    (hτ : τ ∈ admSeps N (tailStart Q) (tailLen N Q) 1)
    (hfree : Disjoint (sepIn N (tailStart Q) (tailLen N Q) τ) (missing N S)) :
    Disjoint τ (intArc N (tailStart P) (tailLen N P)) ∧
      ((∀ t ∈ τ, t % 2 = 1) → Disjoint τ (evenSide N P)) := by
  have hE : N % 2 = 0 := Nat.even_iff.1 hE
  obtain ⟨hts, -, -, htl3, htlN, hs, hs2, hk1, hk3, hkN⟩ := pkCh_sides hE hP
  obtain ⟨htsQ, -, -, -, htlQN, hsQ, -, -, -, -⟩ := pkCh_sides hE hQ
  have hN : 6 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have htl : tailLen N P = N - headLen N P := rfl
  obtain ⟨hcb, -, -, hposQh⟩ := pkCh_subHead hN hE hQ hP hsub
  -- positions along `A′` (from the first leg of `A′`)
  set π := cycPos N (headStart P) with hπ
  set c := π (headStart Q) with hc
  -- a leg of `B′` lies in `B_Q`, and its positions in `B′` and `B_Q` differ by a constant
  have key : ∀ x ∈ Icc 1 N, x ∈ cycArc N (tailStart P) (tailLen N P) →
      headLen N P ≤ π x ∧ x ∈ cycArc N (tailStart Q) (tailLen N Q) ∧
        cycPos N (tailStart P) x = π x - headLen N P ∧
        cycPos N (tailStart Q) x = π x - c - headLen N Q := by
    intro x hx hxB
    obtain ⟨tP1, tP2⟩ := pkCh_tailpos hN hE hP hx
    have h1 : headLen N P ≤ π x := tP1.1 hxB
    have hQx : cycPos N (headStart Q) x = π x - c := hposQh x hx (by omega)
    obtain ⟨tQ1, tQ2⟩ := pkCh_tailpos hN hE hQ hx
    have h2 : headLen N Q ≤ cycPos N (headStart Q) x := by rw [hQx]; omega
    refine ⟨h1, tQ1.2 h2, tP2 h1, ?_⟩
    rw [tQ2 h2, hQx]
  -- the end legs of `B′` are even
  have hend : ∀ x ∈ Icc 1 N, x ∈ cycArc N (tailStart P) (tailLen N P) →
      x ∉ intArc N (tailStart P) (tailLen N P) → x % 2 = 0 := by
    intro x hx hxB hxI
    obtain ⟨h1, -, hpP, -⟩ := key x hx hxB
    have hlt := (pkCo_mem_cycArc_pos hts (by omega)).1 hxB
    have hmod := pkCh_pos_mod hE hs hs2 hx
    have hlt' := pkCo_cycPos_lt hN1 (headStart P) x
    rw [pkCo_mem_intArc hts (by omega)] at hxI
    have : ¬ (1 ≤ cycPos N (tailStart P) x ∧ cycPos N (tailStart P) x + 2 ≤ tailLen N P) :=
      fun h => hxI ⟨hx, h⟩
    rw [hpP] at this hlt
    rw [← hπ] at hmod hlt'
    omega
  obtain ⟨hτsub, hτc⟩ := pkCo_mem_admSeps.1 hτ
  have hτI : ∀ x ∈ τ, x ∈ Icc 1 N := fun x hx =>
    ((pkCo_mem_intArc htsQ (by omega)).1 (hτsub hx)).1
  have part1 : Disjoint τ (intArc N (tailStart P) (tailLen N P)) := by
    rw [disjoint_left]
    intro t htτ htI
    set τ0 := τ.filter (fun x => x ∈ intArc N (tailStart P) (tailLen N P)) with hτ0
    have ht0 : t ∈ τ0 := mem_filter.2 ⟨htτ, htI⟩
    have hτ0adm : τ0 ∈ admSeps N (tailStart P) (tailLen N P) 1 := by
      refine pkCo_mem_admSeps.2 ⟨fun x hx => (mem_filter.1 hx).2, ?_⟩
      have hpos : 1 ≤ τ0.card := card_pos.2 ⟨t, ht0⟩
      rcases hτc with h1 | ⟨-, hodd⟩
      · left
        have := card_le_card (filter_subset (fun x => x ∈ intArc N (tailStart P) (tailLen N P)) τ)
        rw [← hτ0] at this
        omega
      · by_cases h1 : τ0.card = 1
        · exact Or.inl h1
        · exact Or.inr ⟨by omega, fun x hx => hodd x (mem_filter.1 hx).1⟩
    -- a leg of `B′` in `τ` lies in `τ0`
    have hin0 : ∀ x ∈ Icc 1 N, x ∈ cycArc N (tailStart P) (tailLen N P) → x ∈ τ → x ∈ τ0 := by
      intro x hx hxB hxτ
      refine mem_filter.2 ⟨hxτ, ?_⟩
      by_contra hxI
      have he := hend x hx hxB hxI
      rcases hτc with h1 | ⟨-, hodd⟩
      · obtain ⟨y, hy⟩ := card_eq_one.1 h1
        rw [hy, mem_singleton] at hxτ htτ
        exact hxI (hxτ ▸ htτ ▸ htI)
      · have := hodd x hxτ
        omega
    obtain ⟨p, hp, hpm⟩ := not_disjoint_iff.1 (hlinked τ0 hτ0adm)
    rw [pkCo_mem_sepIn] at hp
    obtain ⟨hpd, hp1, hp2, hp1τ, hp2τ, θ, hθ, b1, b2⟩ := hp
    have hp1I := ((pkCo_mem_cycArc_pos hts (by omega)).1 hp1).1
    have hp2I := ((pkCo_mem_cycArc_pos hts (by omega)).1 hp2).1
    have hθτ := (mem_filter.1 hθ).1
    have hθB : θ ∈ cycArc N (tailStart P) (tailLen N P) :=
      (mem_filter.1 ((pkCo_mem_admSeps.1 hτ0adm).1 hθ)).1
    obtain ⟨-, q1, e1, f1⟩ := key p.1 hp1I hp1
    obtain ⟨-, q2, e2, f2⟩ := key p.2 hp2I hp2
    obtain ⟨-, -, eθ, fθ⟩ := key θ (hτI θ hθτ) hθB
    have k1 : headLen N P ≤ π p.1 := (key p.1 hp1I hp1).1
    have k2 : headLen N P ≤ π p.2 := (key p.2 hp2I hp2).1
    have kθ : headLen N P ≤ π θ := (key θ (hτI θ hθτ) hθB).1
    have hpQ : p ∈ sepIn N (tailStart Q) (tailLen N Q) τ := by
      rw [pkCo_mem_sepIn]
      refine ⟨hpd, q1, q2, fun h => hp1τ (hin0 _ hp1I hp1 h),
        fun h => hp2τ (hin0 _ hp2I hp2 h), θ, hθτ, ?_, ?_⟩
      · rw [e1, e2, eθ] at b1
        rw [f1, f2, fθ]
        omega
      · rw [e1, e2, eθ] at b2
        rw [f1, f2, fθ]
        omega
    exact disjoint_left.1 hfree hpQ hpm
  refine ⟨part1, fun hodd => disjoint_left.2 fun x hxτ hxB => ?_⟩
  have hxI := hτI x hxτ
  rw [(sides_eq_cycArc (by omega) (Nat.even_iff.2 hE) hP).2] at hxB
  have := hend x hxI hxB (disjoint_left.1 part1 hxτ)
  have := hodd x hxτ
  omega

/-! ## Runs of an even separator and the translation to combinatorics -/

-- registry: C-SZT3
/-- Runs: `Z` is a run of `L ∖ Θ`, for the arc `L` whose first leg is `s`: a
non-empty set of legs of `L ∖ Θ`, any two of them in the same run (no leg of `Θ` strictly between
them along the arc), and maximal (a leg of `L ∖ Θ` in the same run as a leg of `Z` is in `Z`). -/
def Combinatorics.Polygons.IsRunOf (N s : ℕ) (L Θ Z : Finset ℕ) : Prop :=
  Z.Nonempty ∧ Z ⊆ L \ Θ ∧ (∀ u ∈ Z, ∀ v ∈ Z, SameRun N s Θ u v) ∧
    ∀ u ∈ Z, ∀ v ∈ L \ Θ, SameRun N s Θ u v → v ∈ Z

-- registry: C-SZT3
/-- Occupied runs: for an odd chord `P′` with odd-ended side `A′` and a leg set
`Θ`, an occupied run is a run of `A′ ∖ Θ` that contains a missing oo pair. -/
def Combinatorics.Polygons.IsOccupiedRun (N : ℕ) (S : Finset (ℕ × ℕ)) (P : ℕ × ℕ)
    (Θ Z : Finset ℕ) : Prop :=
  IsRunOf N (headStart P) (oddSide N P) Θ Z ∧ ∃ p ∈ Moo N S, p.1 ∈ Z ∧ p.2 ∈ Z

-- registry: C-SZT3
/-- Spread: `Θ` has at least two occupied runs of `A′ ∖ Θ`. -/
def Combinatorics.Polygons.IsSpread (N : ℕ) (S : Finset (ℕ × ℕ)) (P : ℕ × ℕ)
    (Θ : Finset ℕ) : Prop :=
  ∃ X Y, IsOccupiedRun N S P Θ X ∧ IsOccupiedRun N S P Θ Y ∧ X ≠ Y

-- registry: C-SZT3
/-- The piece `R_τ`: for odd chords `P′`, `Q` and a leg set `τ`, the piece of `B_Q ∖ τ` that
contains the interior of `B′`, read at the leg after the first leg of `B′` (an interior leg of `B′`;
a free admissible separator of `B_Q` avoids the interior of `B′` (W-avoidance), so it lies in
one piece), with `y` adjoined when `τ = {y}` with `y` even. Its complement
`R_τ^c` is `Icc 1 N \ reachPiece N P Q τ`. -/
def Combinatorics.Polygons.reachPiece (N : ℕ) (P Q : ℕ × ℕ) (τ : Finset ℕ) : Finset ℕ :=
  (evenSide N Q).filter (fun x => x ∉ τ ∧ SameRun N (tailStart Q) τ x (vtx N (tailStart P + 1))) ∪
    τ.filter (fun y => τ = {y} ∧ y % 2 = 0)

/-! ### Helpers on runs -/

/-- The run of `L ∖ Θ` through a leg `u` of `L ∖ Θ`, for sets `L`, `Θ` of legs. -/
theorem isRunOf_through {N s : ℕ} {L Θ : Finset ℕ} (hs : s ∈ Icc 1 N) (hL : L ⊆ Icc 1 N)
    (hΘ : Θ ⊆ Icc 1 N) {u : ℕ} (hu : u ∈ L \ Θ) :
    IsRunOf N s L Θ ((L \ Θ).filter (SameRun N s Θ u)) := by
  have huI : u ∈ Icc 1 N := hL (mem_sdiff.1 hu).1
  have huΘ : u ∉ Θ := (mem_sdiff.1 hu).2
  refine ⟨⟨u, mem_filter.2 ⟨hu, pkCo_sameRun_refl _ _ _ u⟩⟩, filter_subset _ _, fun v hv w hw => ?_,
    fun v hv w hw hvw => mem_filter.2 ⟨hw, ?_⟩⟩
  · have huv := (mem_filter.1 hv).2
    have huw := (mem_filter.1 hw).2
    refine pkCo_sameRun_trans hs hΘ huI huΘ ?_ huw
    rintro ⟨θ, hθ, b1, b2⟩
    exact huv ⟨θ, hθ, by omega, by omega⟩
  · obtain ⟨hv', huv⟩ := mem_filter.1 hv
    exact pkCo_sameRun_trans hs hΘ (hL (mem_sdiff.1 hv').1) (mem_sdiff.1 hv').2 huv hvw

/-- Two runs of `L ∖ Θ` that share a leg are equal. -/
theorem isRunOf_eq {N s : ℕ} {L Θ X Y : Finset ℕ} (hX : IsRunOf N s L Θ X)
    (hY : IsRunOf N s L Θ Y) {u : ℕ} (huX : u ∈ X) (huY : u ∈ Y) : X = Y := by
  have key : ∀ X Y, IsRunOf N s L Θ X → IsRunOf N s L Θ Y → u ∈ X → u ∈ Y → X ⊆ Y :=
    fun X Y hX hY huX huY z hz => hY.2.2.2 u huY z (hX.2.1 hz) (hX.2.2.1 u huX z hz)
  exact Subset.antisymm (key X Y hX hY huX huY) (key Y X hY hX huY huX)

/-! ### The fact embedded in the definition of runs -/

-- registry: C-SZT3
/-- Runs, the fact embedded in their definition: every pair of `o_in(P′)` lies inside a single run
of `A′ ∖ Θ`, for a free even separator `Θ` of `A′` (a missing oo pair joining two runs would
lie in `sep_{A′}(Θ)`). -/
theorem Combinatorics.Polygons.inner_oo_pair_in_one_run {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ} (hP : P ∈ oddDiagonals N) {Θ : Finset ℕ}
    (hΘ : Θ ∈ admSeps N (headStart P) (headLen N P) 0) (hΘe : ∀ θ ∈ Θ, θ % 2 = 0)
    (hΘd : Disjoint (sepIn N (headStart P) (headLen N P) Θ) (missing N S)) {p : ℕ × ℕ}
    (hp : p ∈ innerOO N S P) :
    ∃ Z, IsRunOf N (headStart P) (oddSide N P) Θ Z ∧ p.1 ∈ Z ∧ p.2 ∈ Z := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  obtain ⟨-, -, -, -, -, hs, -, -, -, hkN⟩ := pkCh_sides hE' hP
  have eA := (sides_eq_cycArc (by omega) hE hP).1
  have hΘI : Θ ⊆ Icc 1 N := fun θ h =>
    ((pkCo_mem_intArc hs (by omega)).1 ((pkCo_mem_admSeps.1 hΘ).1 h)).1
  have hLI : oddSide N P ⊆ Icc 1 N := by rw [eA]; exact pkCo_cycArc_sub (by omega)
  obtain ⟨hpM, hp1, hp2⟩ := pkCh_mem_innerOO.1 hp
  obtain ⟨hpm, hp1o, hp2o⟩ := pkCh_mem_Moo.1 hpM
  have t1 : p.1 ∉ Θ := fun h => by have := hΘe _ h; omega
  have t2 : p.2 ∉ Θ := fun h => by have := hΘe _ h; omega
  have hsr : SameRun N (headStart P) Θ p.1 p.2 := by
    rintro ⟨θ, hθ, b1, b2⟩
    have a1 : p.1 ∈ cycArc N (headStart P) (headLen N P) := eA ▸ hp1
    have a2 : p.2 ∈ cycArc N (headStart P) (headLen N P) := eA ▸ hp2
    exact disjoint_left.1 hΘd (pkCo_mem_sepIn.2 ⟨(pkCh_mem_missing.1 hpm).1, a1, a2, t1, t2, θ,
      hθ, b1, b2⟩) hpm
  exact ⟨_, isRunOf_through hs hLI hΘI (mem_sdiff.2 ⟨hp1, t1⟩),
    mem_filter.2 ⟨mem_sdiff.2 ⟨hp1, t1⟩, pkCo_sameRun_refl _ _ _ _⟩,
    mem_filter.2 ⟨mem_sdiff.2 ⟨hp2, t2⟩, hsr⟩⟩

/-! ### Spread: the paper's form and the library's form -/

/-- Spread, one direction (any `Θ`): two occupied runs give two missing oo pairs
each in one run, in different runs (`Spread`). -/
theorem spread_of_isSpread {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {S : Finset (ℕ × ℕ)}
    {P : ℕ × ℕ} (hP : P ∈ oddDiagonals N) {Θ : Finset ℕ} (h : IsSpread N S P Θ) :
    Spread N S (headStart P) (headLen N P) Θ := by
  have eA := (sides_eq_cycArc (by omega) hE hP).1
  obtain ⟨X, Y, ⟨hXr, p, hpM, hp1, hp2⟩, ⟨hYr, q, hqM, hq1, hq2⟩, hXY⟩ := h
  have inX : ∀ x ∈ X, x ∈ cycArc N (headStart P) (headLen N P) ∧ x ∉ Θ := fun x hx => by
    have := mem_sdiff.1 (hXr.2.1 hx); rw [eA] at this; exact this
  have inY : ∀ x ∈ Y, x ∈ cycArc N (headStart P) (headLen N P) ∧ x ∉ Θ := fun x hx => by
    have := mem_sdiff.1 (hYr.2.1 hx); rw [eA] at this; exact this
  refine ⟨p, hpM, q, hqM, ⟨(inX _ hp1).1, (inX _ hp2).1, (inX _ hp1).2, (inX _ hp2).2,
    hXr.2.2.1 _ hp1 _ hp2⟩, ⟨(inY _ hq1).1, (inY _ hq2).1, (inY _ hq1).2, (inY _ hq2).2,
    hYr.2.2.1 _ hq1 _ hq2⟩, fun hpq => hXY ?_⟩
  exact isRunOf_eq hXr hYr (hXr.2.2.2 _ hp1 _ (hYr.2.1 hq1) hpq) hq1

/-- An admissible separator of the odd-ended side of an odd chord is a set of legs. -/
theorem legs_of_mem_admSeps {N q : ℕ} (hE : Even N) {P : ℕ × ℕ} (hP : P ∈ oddDiagonals N)
    {Θ : Finset ℕ} (h : Θ ∈ admSeps N (headStart P) (headLen N P) q) : Θ ⊆ Icc 1 N := by
  obtain ⟨-, -, -, -, -, hs, -, -, -, hkN⟩ := pkCh_sides (Nat.even_iff.1 hE) hP
  exact fun x hx => ((pkCo_mem_intArc hs (by omega)).1 ((pkCo_mem_admSeps.1 h).1 hx)).1

-- registry: C-SZT3
/-- Spread, in the library's form, for a set `Θ` of legs (`Θ ⊆ [1, N]`): `Θ` has
two occupied runs iff two missing oo pairs lie each in one run of `A′ ∖ Θ`, in different runs
(`Spread`, the form `EvenTopP`, the no-spread predicate, uses). -/
theorem Combinatorics.Polygons.isSpread_iff_spread {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ} (hP : P ∈ oddDiagonals N) {Θ : Finset ℕ} (hΘ : Θ ⊆ Icc 1 N) :
    IsSpread N S P Θ ↔ Spread N S (headStart P) (headLen N P) Θ := by
  refine ⟨spread_of_isSpread hN hE hP, fun h => ?_⟩
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  obtain ⟨-, -, -, -, -, hs, -, -, -, hkN⟩ := pkCh_sides hE' hP
  have eA := (sides_eq_cycArc (by omega) hE hP).1
  have hLI : oddSide N P ⊆ Icc 1 N := by rw [eA]; exact pkCo_cycArc_sub (by omega)
  obtain ⟨p, hpM, q, hqM, ⟨hp1, hp2, hp1Θ, hp2Θ, hp⟩, ⟨hq1, hq2, hq1Θ, hq2Θ, hq⟩, hpq⟩ := h
  rw [← eA] at hp1 hp2 hq1 hq2
  refine ⟨_, _, ⟨isRunOf_through hs hLI hΘ (mem_sdiff.2 ⟨hp1, hp1Θ⟩), p, hpM,
    mem_filter.2 ⟨mem_sdiff.2 ⟨hp1, hp1Θ⟩, pkCo_sameRun_refl _ _ _ _⟩,
    mem_filter.2 ⟨mem_sdiff.2 ⟨hp2, hp2Θ⟩, hp⟩⟩,
    ⟨isRunOf_through hs hLI hΘ (mem_sdiff.2 ⟨hq1, hq1Θ⟩), q, hqM,
    mem_filter.2 ⟨mem_sdiff.2 ⟨hq1, hq1Θ⟩, pkCo_sameRun_refl _ _ _ _⟩,
    mem_filter.2 ⟨mem_sdiff.2 ⟨hq2, hq2Θ⟩, hq⟩⟩, fun he => hpq ?_⟩
  have hqX : q.1 ∈ (oddSide N P \ Θ).filter (SameRun N (headStart P) Θ p.1) := by
    rw [he]; exact mem_filter.2 ⟨mem_sdiff.2 ⟨hq1, hq1Θ⟩, pkCo_sameRun_refl _ _ _ _⟩
  exact (mem_filter.1 hqX).2

/-! ### Run chords -/

/-- A run `Z` of `A′ ∖ Θ` read in the linear setting of `A′` (labels `cycPos + 1`): if a leg of `Z`
has its label in a run `[a, b]` of the image of `Θ`, then `Z` is the set of legs with label in
`[a, b]`. -/
theorem isRunOf_lin {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {P : ℕ × ℕ} (hP : P ∈ oddDiagonals N)
    {Θ : Finset ℕ} (hΘ : Θ ∈ admSeps N (headStart P) (headLen N P) 0) {Z : Finset ℕ}
    (hZ : IsRunOf N (headStart P) (oddSide N P) Θ Z) {a b : ℕ}
    (hR : IsRun (headLen N P) (Θ.image (rotLeg N (N + 1 - headStart P))) a b) {y : ℕ}
    (hy : y ∈ Z) (hya : a ≤ cycPos N (headStart P) y + 1)
    (hyb : cycPos N (headStart P) y + 1 ≤ b) (x : ℕ) :
    x ∈ Z ↔ x ∈ Icc 1 N ∧ a ≤ cycPos N (headStart P) x + 1 ∧ cycPos N (headStart P) x + 1 ≤ b := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  obtain ⟨-, -, -, -, -, hs, -, -, -, hkN⟩ := pkCh_sides hE' hP
  obtain ⟨-, hab, hbk, haΘ, hbΘ, hRΘ⟩ := pkCh_isRun_iff.1 hR
  obtain ⟨-, hZsub, hZpw, hZmax⟩ := hZ
  have hΘI : Θ ⊆ Icc 1 N := fun θ h =>
    ((pkCo_mem_intArc hs (by omega)).1 ((pkCo_mem_admSeps.1 hΘ).1 h)).1
  have hθl : ∀ θ ∈ Θ, cycPos N (headStart P) θ + 1 ∈ Θ.image (rotLeg N (N + 1 - headStart P)) :=
    fun θ hθ => by rw [← pkCh_phi_eq hs]; exact mem_image_of_mem _ hθ
  have hlθ : ∀ t ∈ Θ.image (rotLeg N (N + 1 - headStart P)), ∃ θ ∈ Θ,
      t = cycPos N (headStart P) θ + 1 := fun t ht => by
    obtain ⟨θ, hθ, rfl⟩ := mem_image.1 ht
    exact ⟨θ, hθ, pkCh_phi_eq hs θ⟩
  have hne : ∀ x ∈ Icc 1 N, x ∉ Θ → ∀ θ ∈ Θ, cycPos N (headStart P) θ ≠ cycPos N (headStart P) x :=
    fun x hx hxΘ θ hθ h => hxΘ (pkCo_cycPos_inj hs (hΘI hθ) hx h ▸ hθ)
  constructor
  · intro hx
    obtain ⟨hxA, hxΘ⟩ := mem_sdiff.1 (hZsub hx)
    obtain ⟨hxI, hxk⟩ := (pkCh_headpos hN hE' hP).1 hxA
    have hyx := hZpw y hy x hx
    refine ⟨hxI, ?_, ?_⟩
    · by_contra hc
      rcases haΘ with h | h
      · omega
      obtain ⟨θ, hθ, e⟩ := hlθ _ h
      have := hne x hxI hxΘ θ hθ
      exact hyx ⟨θ, hθ, by omega, by omega⟩
    · by_contra hc
      rcases hbΘ with h | h
      · omega
      obtain ⟨θ, hθ, e⟩ := hlθ _ h
      have := hne x hxI hxΘ θ hθ
      exact hyx ⟨θ, hθ, by omega, by omega⟩
  · rintro ⟨hxI, h1, h2⟩
    have hxA : x ∈ oddSide N P := (pkCh_headpos hN hE' hP).2 ⟨hxI, by omega⟩
    have hxΘ : x ∉ Θ := fun h => hRΘ _ (mem_Icc.2 ⟨h1, h2⟩) (hθl x h)
    refine hZmax y hy x (mem_sdiff.2 ⟨hxA, hxΘ⟩) ?_
    rintro ⟨θ, hθ, b1, b2⟩
    exact hRΘ _ (mem_Icc.2 ⟨by omega, by omega⟩) (hθl θ hθ)

-- registry: C-ENES
/-- **Run chords**: for even `N ≥ 6`, let `P′ ∈ 𝒫₁` with sides `A′`, `B′`, `Θ` an
free even separator of `A′`, and `Z` an occupied run of `A′ ∖ Θ`. Then the run chord `Q_Z`,
the odd chord with `A_{Q_Z} = Z`, exists and is in `𝒫₁`. No hypothesis on `S`. -/
theorem Combinatorics.Polygons.occupied_run_chords {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ} (hP : P ∈ poleChords N S) {Θ : Finset ℕ}
    (hΘ : Θ ∈ admSeps N (headStart P) (headLen N P) 0) (hΘe : ∀ θ ∈ Θ, θ % 2 = 0)
    (hΘd : Disjoint (sepIn N (headStart P) (headLen N P) Θ) (missing N S)) {Z : Finset ℕ}
    (hZ : IsOccupiedRun N S P Θ Z) :
    ∃ Q ∈ poleChords N S, oddSide N Q = Z := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  obtain ⟨hPo, -, -, -⟩ := pkCh_mem_pole.1 hP
  obtain ⟨-, -, -, -, -, hs, hs2, -, -, hkN⟩ := pkCh_sides hE' hPo
  obtain ⟨hΘl, hΘle, hΘlf⟩ := pkCh_toLin hN hE' hPo hΘ hΘe hΘd
  obtain ⟨hZr, p, hpM, hp1, hp2⟩ := hZ
  obtain ⟨hpm, hp1o, hp2o⟩ := pkCh_mem_Moo.1 hpM
  have hpd := mem_diagonals.1 (pkCh_mem_missing.1 hpm).1
  have hp1' := mem_sdiff.1 (hZr.2.1 hp1)
  obtain ⟨i1, k1⟩ := (pkCh_headpos hN hE' hPo).1 hp1'.1
  obtain ⟨i2, k2⟩ := (pkCh_headpos hN hE' hPo).1 (mem_sdiff.1 (hZr.2.1 hp2)).1
  have hf1Θ : cycPos N (headStart P) p.1 + 1 ∉ Θ.image (rotLeg N (N + 1 - headStart P)) :=
    fun h => by
      have := hΘle _ h
      have := pkCh_pos_mod hE' hs hs2 i1
      omega
  obtain ⟨a, b, hR, hau, hub⟩ := pkCh_runOf hΘl (mem_Icc.2 ⟨by omega, by omega⟩) hf1Θ
  have hlin := isRunOf_lin hN hE hPo hΘ hZr hR hp1 hau hub
  obtain ⟨-, c1, c2⟩ := (hlin p.2).1 hp2
  have hC : ¬ pkChCl N (headStart P) S (cycPos N (headStart P) p.1 + 1)
      (cycPos N (headStart P) p.2 + 1) := by
    have := pkCh_notCl hs i1 i2 hpm
    rw [pkCh_phi_eq hs, pkCh_phi_eq hs] at this
    exact this
  have hne : cycPos N (headStart P) p.1 ≠ cycPos N (headStart P) p.2 := fun h => by
    have := pkCo_cycPos_inj hs i1 i2 h; omega
  have m1 := pkCh_pos_mod hE' hs hs2 i1
  have m2 := pkCh_pos_mod hE' hs hs2 i2
  obtain ⟨Q, hQ, hQodd⟩ := pkCh_L0 hN hE' hP hΘl hΘle hΘlf hR
    ⟨min (cycPos N (headStart P) p.1 + 1) (cycPos N (headStart P) p.2 + 1),
      max (cycPos N (headStart P) p.1 + 1) (cycPos N (headStart P) p.2 + 1),
      by omega, by omega, by omega, by omega, by omega,
      fun h => hC (pkCh_C_minmax pkCh_Cl_symm h)⟩
  exact ⟨Q, hQ, ext fun x => by rw [hQodd x, hlin x]⟩

/-! ### Sub-arcs -/

-- registry: C-PKWQ
/-- **Sub-arcs**: for arcs `L′ ⊆ L ⊊ C_N` and any leg set `Θ`,
`sep_{L′}(Θ ∩ L′) ⊆ sep_L(Θ)`. An arc is given by its first leg and its number of legs. -/
theorem Combinatorics.Polygons.separated_pairs_of_sub_arc {N s k s' k' : ℕ} (hs : s ∈ Icc 1 N)
    (hk : k < N) (hs' : s' ∈ Icc 1 N) (hsub : cycArc N s' k' ⊆ cycArc N s k) (Θ : Finset ℕ) :
    sepIn N s' k' (Θ ∩ cycArc N s' k') ⊆ sepIn N s k Θ := by
  intro p hp
  rw [pkCo_mem_sepIn] at hp ⊢
  obtain ⟨hpd, hp1, hp2, hp1Θ, hp2Θ, θ, hθ, b1, b2⟩ := hp
  obtain ⟨hθΘ, hθL'⟩ := mem_inter.1 hθ
  have hsI := mem_Icc.1 hs
  have hN : 1 ≤ N := by omega
  have hk'1 : 1 ≤ k' := by obtain ⟨j, hj, -⟩ := pkCo_mem_cycArc.1 hp1; omega
  -- the first leg of `L′` is at position `d` of `L`
  have hs'v : vtx N (s' + 0) = s' := by
    rw [add_zero]; exact vtx_of_mem (mem_Icc.1 hs').1 (mem_Icc.1 hs').2
  have hs'L : s' ∈ cycArc N s k := hsub (pkCo_mem_cycArc.2 ⟨0, hk'1, hs'v⟩)
  obtain ⟨d, hd⟩ : ∃ d, d = cycPos N s s' := ⟨_, rfl⟩
  have hdk : d < k := hd ▸ ((pkCo_mem_cycArc_pos hs hk.le).1 hs'L).2
  have he : vtx N (s + d) = s' := hd ▸ pkCo_vtx_cycPos hs hs'
  -- `L′` does not reach the last position `N − 1` of the arc from `s`, as `k < N`
  have hdk' : d + k' ≤ N - 1 := by
    by_contra hc
    have hy : vtx N (s' + (N - 1 - d)) ∈ cycArc N s k :=
      hsub (pkCo_mem_cycArc.2 ⟨N - 1 - d, by omega, rfl⟩)
    rw [← he, pkCo_vtx_vtx_add hN, show s + d + (N - 1 - d) = s + (N - 1) by omega] at hy
    have hpos : cycPos N s (vtx N (s + (N - 1))) = N - 1 := by
      rw [pkCo_vtx_eq hsI.1 hsI.2 (by omega)]
      split_ifs with h <;> rw [pkCo_cycPos_eq hsI.1 hsI.2 (by omega) (by omega)] <;>
        split_ifs <;> omega
    have := ((pkCo_mem_cycArc_pos hs hk.le).1 hy).2
    omega
  have memL' : ∀ x, x ∈ cycArc N s' k' ↔ x ∈ Icc 1 N ∧ d ≤ cycPos N s x ∧
      cycPos N s x < d + k' := fun x => by
    rw [← he]; exact pkCh_mem_sub hs (by omega) hk'1
  have posL' : ∀ x, x ∈ cycArc N s' k' → cycPos N s' x = cycPos N s x - d := fun x hx => by
    obtain ⟨hxI, h1, -⟩ := (memL' x).1 hx
    rw [← he, pkCh_pos_shift hs hxI (by omega), ite_eq_left h1]
  obtain ⟨-, e1, -⟩ := (memL' p.1).1 hp1
  obtain ⟨-, e2, -⟩ := (memL' p.2).1 hp2
  obtain ⟨-, e3, -⟩ := (memL' θ).1 hθL'
  rw [posL' _ hp1, posL' _ hp2, posL' _ hθL'] at b1 b2
  exact ⟨hpd, hsub hp1, hsub hp2, fun h => hp1Θ (mem_inter.2 ⟨h, hp1⟩),
    fun h => hp2Θ (mem_inter.2 ⟨h, hp2⟩), θ, hθΘ, by omega, by omega⟩

/-! ### No spread -/

-- registry: C-B5K0
/-- **No spread**: for a candidate set `S` at even `N ≥ 6` and an innermost chord `P*`, `P*` has
no spread free even separator of `A*`. (Its proof uses the three-cut theorem.) -/
theorem Combinatorics.Polygons.innermost_chord_has_no_spread_separator {N : ℕ} (hN : 6 ≤ N)
    (hE : Even N) {S : Finset (ℕ × ℕ)} (hF : IsCandidateSet N S) {P : ℕ × ℕ}
    (hP : IsInnermostChord N S P) {Θ : Finset ℕ} (hΘ : Θ ∈ admSeps N (headStart P) (headLen N P) 0)
    (hΘe : ∀ θ ∈ Θ, θ % 2 = 0)
    (hΘd : Disjoint (sepIn N (headStart P) (headLen N P) Θ) (missing N S)) :
    ¬ IsSpread N S P Θ := fun h =>
  evenTop hN hE ((isCandidateSet_iff_inFpi hE).1 hF) hP Θ hΘ hΘe hΘd
    (spread_of_isSpread hN hE (pkCh_mem_pole.1 (pkCh_mem_goodTail.1 hP.1).1).1 h)

/-! ### Shortening: `shortening_spread_separator` -/

/-- A leg strictly between two legs of one run of `L ∖ τ` is off `τ` and in that run. -/
theorem sameRun_between {N s : ℕ} {τ : Finset ℕ} {a w b : ℕ} (h : SameRun N s τ a b)
    (hw : cycPos N s a < cycPos N s w ∧ cycPos N s w < cycPos N s b ∨
      cycPos N s b < cycPos N s w ∧ cycPos N s w < cycPos N s a) :
    (∀ t ∈ τ, cycPos N s t ≠ cycPos N s w) ∧ SameRun N s τ w b :=
  ⟨fun t ht he => h ⟨t, ht, by omega⟩, fun ⟨t, ht, h1, h2⟩ => h ⟨t, ht, by omega⟩⟩

/-- A leg of `L ∖ Θ` next to a leg of a run `Z` of `L ∖ Θ` is in `Z` (maximality); so a leg of
`L` next to `Z` and not in `Z` is in `Θ`. -/
theorem mem_of_adj_run {N s : ℕ} {L Θ Z : Finset ℕ} (hZ : IsRunOf N s L Θ Z) {z x : ℕ}
    (hz : z ∈ Z) (hxL : x ∈ L) (hxZ : x ∉ Z)
    (hadj : cycPos N s x + 1 = cycPos N s z ∨ cycPos N s z + 1 = cycPos N s x) : x ∈ Θ := by
  by_contra hx
  exact hxZ (hZ.2.2.2 z hz x (mem_sdiff.2 ⟨hxL, hx⟩) fun ⟨θ, _, h1, h2⟩ => by omega)

/-- The second leg of `B′` sits at position `|A′| + 1` along the arc from the first leg of `A′`. -/
theorem second_leg_pos {N : ℕ} (hE : N % 2 = 0) {P : ℕ × ℕ} (hP : P ∈ oddDiagonals N) :
    vtx N (tailStart P + 1) ∈ Icc 1 N ∧
      cycPos N (headStart P) (vtx N (tailStart P + 1)) = headLen N P + 1 := by
  obtain ⟨-, -, -, -, -, hs, -, -, -, hkN⟩ := pkCh_sides hE hP
  have hN1 : 1 ≤ N := by omega
  refine ⟨mem_Icc.2 (vtx_bounds N _ hN1), ?_⟩
  rw [pkCh_tail_eq hP, pkCo_vtx_vtx_add hN1, add_assoc]
  exact pkCo_cycPos_vtx hs (by omega)

/-- Positions for an odd chord `Q` with `A_Q ⊆ A′`: `A_Q` is the block `[c, c + |A_Q|)` of
positions along `A′`, and positions along `B_Q` are positions along `A′` shifted by `c + |A_Q|`. -/
theorem run_chord_frame {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {P Q : ℕ × ℕ}
    (hP : P ∈ oddDiagonals N) (hQ : Q ∈ oddDiagonals N) (hsub : oddSide N Q ⊆ oddSide N P) :
    ∃ c, c + headLen N Q ≤ headLen N P ∧
      (∀ x ∈ Icc 1 N, x ∈ oddSide N Q ↔ c ≤ cycPos N (headStart P) x ∧
        cycPos N (headStart P) x < c + headLen N Q) ∧
      (∀ x ∈ Icc 1 N, c + headLen N Q ≤ cycPos N (headStart P) x →
        cycPos N (tailStart Q) x = cycPos N (headStart P) x - (c + headLen N Q)) ∧
      (∀ x ∈ Icc 1 N, cycPos N (headStart P) x < c →
        cycPos N (tailStart Q) x = cycPos N (headStart P) x + N - (c + headLen N Q)) := by
  obtain ⟨h1, -, h3, -⟩ := pkCh_subHead hN hE hQ hP hsub
  obtain ⟨-, -, -, -, -, hs, -, -, -, hkN⟩ := pkCh_sides hE hP
  obtain ⟨-, -, -, -, -, hsQ, -⟩ := pkCh_sides hE hQ
  have hN1 : 1 ≤ N := by omega
  have ht : tailStart Q =
      vtx N (headStart P + (cycPos N (headStart P) (headStart Q) + headLen N Q)) := by
    calc tailStart Q = vtx N (headStart Q + headLen N Q) := pkCh_tail_eq hQ
      _ = vtx N (vtx N (headStart P + cycPos N (headStart P) (headStart Q)) + headLen N Q) := by
        rw [pkCo_vtx_cycPos hs hsQ]
      _ = _ := by rw [pkCo_vtx_vtx_add hN1, add_assoc]
  refine ⟨_, h1, h3, fun x hx hc => ?_, fun x hx hc => ?_⟩ <;>
    rw [ht, pkCh_pos_shift hs hx (by omega)]
  · rw [ite_eq_left hc]
  · rw [ite_eq_right (by omega)]

/-- Shortening, common part: for `Q` the run chord of a run `Z` of `A′ ∖ Θ` and `τ` a free
separator of `B_Q`, given a leg `d₀ ∈ Θ` in the `τ`-piece of the second leg of `B′`, strictly
between the occupied runs `X` and `Y`, the set `Θ ∖ R_τ^c` is a free even separator of `A′`,
strictly inside `Θ`, separating `X` from `Y`, and spread. -/
theorem shortening_core {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {S : Finset (ℕ × ℕ)} {P Q : ℕ × ℕ}
    (hP : P ∈ oddDiagonals N) (hlinked : NoFreeSep N S (tailStart P) (tailLen N P) 1)
    {Θ : Finset ℕ} (hΘ : Θ ∈ admSeps N (headStart P) (headLen N P) 0)
    (hΘe : ∀ θ ∈ Θ, θ % 2 = 0)
    (hΘd : Disjoint (sepIn N (headStart P) (headLen N P) Θ) (missing N S)) {X Y Z : Finset ℕ}
    (hX : IsOccupiedRun N S P Θ X) (hY : IsOccupiedRun N S P Θ Y)
    (hZ : IsRunOf N (headStart P) (oddSide N P) Θ Z) (hQ : Q ∈ oddDiagonals N)
    (hQZ : oddSide N Q = Z) {τ : Finset ℕ} (hτ : τ ∈ admSeps N (tailStart Q) (tailLen N Q) 1)
    (hτd : Disjoint (sepIn N (tailStart Q) (tailLen N Q) τ) (missing N S)) {d0 : ℕ}
    (hd0 : d0 ∈ Θ) (hd0r : SameRun N (tailStart Q) τ d0 (vtx N (tailStart P + 1)))
    (hd0X : ∀ x ∈ X, cycPos N (headStart P) x < cycPos N (headStart P) d0)
    (hd0Y : ∀ y ∈ Y, cycPos N (headStart P) d0 < cycPos N (headStart P) y) :
    Θ \ (Icc 1 N \ reachPiece N P Q τ) ∈ admSeps N (headStart P) (headLen N P) 0 ∧
      (∀ θ ∈ Θ \ (Icc 1 N \ reachPiece N P Q τ), θ % 2 = 0) ∧
      Disjoint (sepIn N (headStart P) (headLen N P) (Θ \ (Icc 1 N \ reachPiece N P Q τ)))
        (missing N S) ∧
      Θ \ (Icc 1 N \ reachPiece N P Q τ) ⊂ Θ ∧
      (∀ x ∈ X, ∀ y ∈ Y,
        ¬ SameRun N (headStart P) (Θ \ (Icc 1 N \ reachPiece N P Q τ)) x y) ∧
      IsSpread N S P (Θ \ (Icc 1 N \ reachPiece N P Q τ)) := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  obtain ⟨hts, -, -, -, -, hs, -, -, -, hkN⟩ := pkCh_sides hE' hP
  obtain ⟨qts, -, -, -, -, -, -, -, qk3, -⟩ := pkCh_sides hE' hQ
  have hN1 : 1 ≤ N := by omega
  have htlP : tailLen N P = N - headLen N P := rfl
  have htlQ : tailLen N Q = N - headLen N Q := rfl
  have hZsub := hZ.2.1
  have hsub : oddSide N Q ⊆ oddSide N P := fun x hx =>
    (mem_sdiff.1 (hZsub (by rw [← hQZ]; exact hx))).1
  obtain ⟨c, hck, hZpos, hρR, hρL⟩ := run_chord_frame hN hE' hP hQ hsub
  rw [hQZ] at hZpos
  obtain ⟨hb'I, hb'π⟩ := second_leg_pos hE' hP
  have hb'ρ := hρR _ hb'I (by omega)
  have hBQ : ∀ x, x ∈ cycArc N (tailStart Q) (tailLen N Q) ↔ x ∈ Icc 1 N ∧ x ∉ Z := fun x => by
    rw [← (pkCh_arcs (by omega) hE' hQ).2.1 x, ← hQZ]
    exact mem_sdiff
  have hΘI : ∀ θ ∈ Θ, θ ∈ Icc 1 N ∧ 1 ≤ cycPos N (headStart P) θ ∧
      cycPos N (headStart P) θ + 2 ≤ headLen N P := fun θ hθ =>
    (pkCo_mem_intArc hs (by omega)).1 ((pkCo_mem_admSeps.1 hΘ).1 hθ)
  have hΘZ : ∀ θ ∈ Θ, θ ∉ Z := fun θ hθ hθZ => (mem_sdiff.1 (hZsub hθZ)).2 hθ
  obtain ⟨hτsub, hτc⟩ := pkCo_mem_admSeps.1 hτ
  have hτB : ∀ t ∈ τ, t ∈ Icc 1 N ∧ 1 ≤ cycPos N (tailStart Q) t ∧
      cycPos N (tailStart Q) t + 2 ≤ tailLen N Q := fun t ht =>
    (pkCo_mem_intArc qts (by omega)).1 (hτsub ht)
  have hτI : τ ⊆ Icc 1 N := fun t ht => (hτB t ht).1
  have hτZ : ∀ t ∈ τ, t ∉ Z := fun t ht => ((hBQ t).1 (mem_filter.1 (hτsub ht)).1).2
  have hτev : ∀ t ∈ τ, t % 2 = 0 → τ = {t} := fun t ht ht2 => by
    rcases hτc with h1 | ⟨-, hodd⟩
    · obtain ⟨y, rfl⟩ := card_eq_one.1 h1
      rw [mem_singleton.1 ht]
    · have := hodd t ht
      omega
  -- the legs of `R_τ`
  have hR : ∀ x ∈ reachPiece N P Q τ, x ∈ Icc 1 N ∧ x ∉ Z ∧
      SameRun N (tailStart Q) τ x (vtx N (tailStart P + 1)) := by
    intro x hx
    rcases mem_union.1 hx with h | h
    · obtain ⟨hxB, -, hxr⟩ := mem_filter.1 h
      obtain ⟨h1, h2⟩ := mem_sdiff.1 hxB
      exact ⟨h1, by rw [← hQZ]; exact h2, hxr⟩
    · obtain ⟨hxτ, hτx, -⟩ := mem_filter.1 h
      refine ⟨(hτB x hxτ).1, hτZ x hxτ, ?_⟩
      rintro ⟨t, ht, h1, h2⟩
      rw [hτx, mem_singleton] at ht
      subst ht
      omega
  have hRin : ∀ x ∈ Icc 1 N, x ∉ Z → x ∉ τ →
      SameRun N (tailStart Q) τ x (vtx N (tailStart P + 1)) → x ∈ reachPiece N P Q τ :=
    fun x hx hxZ hxτ hxr => mem_union_left _ (mem_filter.2
      ⟨mem_sdiff.2 ⟨hx, by rw [hQZ]; exact hxZ⟩, hxτ, hxr⟩)
  have hRΘ : ∀ x ∈ Θ, SameRun N (tailStart Q) τ x (vtx N (tailStart P + 1)) →
      x ∈ reachPiece N P Q τ := fun x hx hxr => by
    by_cases hxτ : x ∈ τ
    · exact mem_union_right _ (mem_filter.2 ⟨hxτ, hτev x hxτ (hΘe x hx), hΘe x hx⟩)
    · exact hRin x (hΘI x hx).1 (hΘZ x hx) hxτ hxr
  have hout : ∀ x ∈ Θ, x ∉ reachPiece N P Q τ →
      x ∉ τ ∧ ¬ SameRun N (tailStart Q) τ x (vtx N (tailStart P + 1)) := by
    intro x hx hxR
    have hxτ : x ∉ τ := fun hxτ => hxR (mem_union_right _ (mem_filter.2
      ⟨hxτ, hτev x hxτ (hΘe x hx), hΘe x hx⟩))
    exact ⟨hxτ, fun h => hxR (hRin x (hΘI x hx).1 (hΘZ x hx) hxτ h)⟩
  have hmem : ∀ x, x ∈ Θ \ (Icc 1 N \ reachPiece N P Q τ) ↔ x ∈ Θ ∧ x ∈ reachPiece N P Q τ := by
    intro x
    simp only [mem_sdiff, not_and, not_not]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2 (hΘI x h1).1⟩, fun ⟨h1, h2⟩ => ⟨h1, fun _ => h2⟩⟩
  have hsubΘ : Θ \ (Icc 1 N \ reachPiece N P Q τ) ⊆ Θ := sdiff_subset
  have hd0' : d0 ∈ Θ \ (Icc 1 N \ reachPiece N P Q τ) := (hmem d0).2 ⟨hd0, hRΘ d0 hd0 hd0r⟩
  -- (3) `d₀ ∈ Θ′` separates `X` from `Y`
  have hsep : ∀ x ∈ X, ∀ y ∈ Y,
      ¬ SameRun N (headStart P) (Θ \ (Icc 1 N \ reachPiece N P Q τ)) x y := by
    intro x hx y hy h
    have := hd0X x hx
    have := hd0Y y hy
    exact h ⟨d0, hd0', by omega⟩
  -- `Θ′` is admissible (non-empty, even)
  have hadm : Θ \ (Icc 1 N \ reachPiece N P Q τ) ∈ admSeps N (headStart P) (headLen N P) 0 := by
    refine pkCo_mem_admSeps.2 ⟨hsubΘ.trans (pkCo_mem_admSeps.1 hΘ).1, ?_⟩
    have := card_pos.2 ⟨d0, hd0'⟩
    by_cases h1 : (Θ \ (Icc 1 N \ reachPiece N P Q τ)).card = 1
    · exact Or.inl h1
    · exact Or.inr ⟨by omega, fun θ hθ => hΘe θ (hsubΘ hθ)⟩
  -- (2) `Θ′ ⊊ Θ`: a leg of `Θ` next to `Z` is cut off from `R_τ` by a leg of `τ`
  have hlt : Θ \ (Icc 1 N \ reachPiece N P Q τ) ⊂ Θ := by
    rw [ssubset_iff_of_subset hsubΘ]
    have hcut : ∀ j, j < headLen N P → (j + 1 = c ∨ j = c + headLen N Q) →
        (∃ t ∈ τ, min (cycPos N (tailStart Q) (vtx N (headStart P + j)))
            (cycPos N (tailStart Q) (vtx N (tailStart P + 1))) < cycPos N (tailStart Q) t ∧
          cycPos N (tailStart Q) t < max (cycPos N (tailStart Q) (vtx N (headStart P + j)))
            (cycPos N (tailStart Q) (vtx N (tailStart P + 1)))) →
        ∃ θ ∈ Θ, θ ∉ Θ \ (Icc 1 N \ reachPiece N P Q τ) := by
      intro j hj hjc ht
      have hjI : vtx N (headStart P + j) ∈ Icc 1 N := mem_Icc.2 (vtx_bounds N _ hN1)
      have hjπ : cycPos N (headStart P) (vtx N (headStart P + j)) = j :=
        pkCo_cycPos_vtx hs (by omega)
      obtain ⟨i, hi1, hi2, hi3⟩ : ∃ i, c ≤ i ∧ i < c + headLen N Q ∧ (j + 1 = i ∨ i + 1 = j) := by
        rcases hjc with h | h
        · exact ⟨c, le_rfl, by omega, Or.inl h⟩
        · exact ⟨c + headLen N Q - 1, by omega, by omega, Or.inr (by omega)⟩
      have hiI : vtx N (headStart P + i) ∈ Icc 1 N := mem_Icc.2 (vtx_bounds N _ hN1)
      have hiπ : cycPos N (headStart P) (vtx N (headStart P + i)) = i :=
        pkCo_cycPos_vtx hs (by omega)
      have hiZ : vtx N (headStart P + i) ∈ Z := (hZpos _ hiI).2 ⟨by omega, by omega⟩
      have hjZ : vtx N (headStart P + j) ∉ Z := fun h => by
        have := (hZpos _ hjI).1 h
        omega
      have hjΘ : vtx N (headStart P + j) ∈ Θ :=
        mem_of_adj_run hZ hiZ ((pkCh_headpos hN hE' hP).2 ⟨hjI, by omega⟩) hjZ (by omega)
      refine ⟨_, hjΘ, fun h => ?_⟩
      exact (hR _ ((hmem _).1 h).2).2.2 ht
    obtain ⟨t, ht⟩ : τ.Nonempty := by
      rw [← card_pos]
      rcases hτc with h | ⟨h, -⟩ <;> omega
    obtain ⟨htI, ht1, ht2⟩ := hτB t ht
    have htZ := hτZ t ht
    have htA : ¬ (c ≤ cycPos N (headStart P) t ∧ cycPos N (headStart P) t < c + headLen N Q) :=
      fun h => htZ ((hZpos t htI).2 h)
    -- W-avoidance: `τ` avoids the interior of `B′`
    have h87 := (separators_avoid_linked_side hE hP hlinked hQ hsub hτ hτd).1
    have htB' : ¬ (headLen N P + 1 ≤ cycPos N (headStart P) t ∧
        cycPos N (headStart P) t + 2 ≤ N) := by
      rintro ⟨h1, h2⟩
      have hp := (pkCh_tailpos hN hE' hP htI).2 (by omega)
      refine disjoint_left.1 h87 ht ((pkCo_mem_intArc hts (by omega)).2 ⟨htI, ?_, ?_⟩) <;> omega
    have hlt' := pkCo_cycPos_lt hN1 (headStart P) t
    have hleg : ∀ j < N, vtx N (headStart P + j) ∈ Icc 1 N ∧
        cycPos N (headStart P) (vtx N (headStart P + j)) = j :=
      fun j hj => ⟨mem_Icc.2 (vtx_bounds N _ hN1), pkCo_cycPos_vtx hs hj⟩
    by_cases hc : c + headLen N Q ≤ cycPos N (headStart P) t
    · have hρt := hρR t htI hc
      by_cases hth : cycPos N (headStart P) t ≤ headLen N P
      · obtain ⟨hlI, hlπ⟩ := hleg (c + headLen N Q) (by omega)
        have := hρR _ hlI (by omega)
        exact hcut (c + headLen N Q) (by omega) (Or.inr rfl) ⟨t, ht, by omega, by omega⟩
      · obtain ⟨hlI, hlπ⟩ := hleg (c - 1) (by omega)
        have := hρL _ hlI (by omega)
        exact hcut (c - 1) (by omega) (Or.inl (by omega)) ⟨t, ht, by omega, by omega⟩
    · have hρt := hρL t htI (by omega)
      obtain ⟨hlI, hlπ⟩ := hleg (c - 1) (by omega)
      have := hρL _ hlI (by omega)
      exact hcut (c - 1) (by omega) (Or.inl (by omega)) ⟨t, ht, by omega, by omega⟩
  -- (4) `Θ′` is free
  have hfree : Disjoint (sepIn N (headStart P) (headLen N P)
      (Θ \ (Icc 1 N \ reachPiece N P Q τ))) (missing N S) := by
    rw [disjoint_left]
    intro p hp hpm
    rw [pkCo_mem_sepIn] at hp
    obtain ⟨hpd, hp1, hp2, hp1Θ, hp2Θ, θ, hθ, b1, b2⟩ := hp
    obtain ⟨hθΘ, hθR⟩ := (hmem θ).1 hθ
    obtain ⟨hθI, hθZ, hθr⟩ := hR θ hθR
    have hθA : ¬ (c ≤ cycPos N (headStart P) θ ∧ cycPos N (headStart P) θ < c + headLen N Q) :=
      fun h => hθZ ((hZpos θ hθI).2 h)
    have hθh := (hΘI θ hθΘ).2.2
    -- a pair with a leg `d ∈ Θ ∖ Θ′` is separated by `τ`
    have key : ∀ d v, d ∈ cycArc N (headStart P) (headLen N P) →
        v ∈ cycArc N (headStart P) (headLen N P) → d ∈ Θ →
        d ∉ Θ \ (Icc 1 N \ reachPiece N P Q τ) →
        min (cycPos N (headStart P) d) (cycPos N (headStart P) v) < cycPos N (headStart P) θ →
        cycPos N (headStart P) θ < max (cycPos N (headStart P) d) (cycPos N (headStart P) v) →
        d ∈ cycArc N (tailStart Q) (tailLen N Q) ∧ v ∈ cycArc N (tailStart Q) (tailLen N Q) ∧
          d ∉ τ ∧ v ∉ τ ∧ ∃ t ∈ τ, min (cycPos N (tailStart Q) d) (cycPos N (tailStart Q) v) <
            cycPos N (tailStart Q) t ∧
            cycPos N (tailStart Q) t <
              max (cycPos N (tailStart Q) d) (cycPos N (tailStart Q) v) := by
      intro d v hd hv hdΘ hdΘ' h1 h2
      have hdR : d ∉ reachPiece N P Q τ := fun h => hdΘ' ((hmem d).2 ⟨hdΘ, h⟩)
      obtain ⟨hdτ, hdr⟩ := hout d hdΘ hdR
      have hdZ := hΘZ d hdΘ
      obtain ⟨hdI, hdh⟩ := (pkCo_mem_cycArc_pos hs (by omega)).1 hd
      obtain ⟨hvI, hvh⟩ := (pkCo_mem_cycArc_pos hs (by omega)).1 hv
      -- the other leg `v` lies in `R_τ`, beyond `θ` from `Z`
      obtain ⟨hvZ, hvτ, hvr⟩ : v ∉ Z ∧ (∀ t ∈ τ, cycPos N (tailStart Q) t ≠
          cycPos N (tailStart Q) v) ∧ SameRun N (tailStart Q) τ v (vtx N (tailStart P + 1)) := by
        have hvZ' : ∀ w ∈ Icc 1 N, (cycPos N (headStart P) w < c ∨
            c + headLen N Q ≤ cycPos N (headStart P) w) → w ∉ Z := fun w hw hw' h => by
          have := (hZpos w hw).1 h
          omega
        by_cases hr : c + headLen N Q ≤ cycPos N (headStart P) θ
        · have eθ := hρR θ hθI hr
          have hdv : cycPos N (headStart P) d < cycPos N (headStart P) θ ∧
              cycPos N (headStart P) θ < cycPos N (headStart P) v := by
            by_contra hcon
            have ed := hρR d hdI (by omega)
            exact hdr (sameRun_between hθr (Or.inl ⟨by omega, by omega⟩)).2
          have ev := hρR v hvI (by omega)
          exact ⟨hvZ' v hvI (by omega), sameRun_between hθr (Or.inl ⟨by omega, by omega⟩)⟩
        · have eθ := hρL θ hθI (by omega)
          have hdv : cycPos N (headStart P) v < cycPos N (headStart P) θ ∧
              cycPos N (headStart P) θ < cycPos N (headStart P) d := by
            by_contra hcon
            have ed := hρL d hdI (by omega)
            exact hdr (sameRun_between hθr (Or.inr ⟨by omega, by omega⟩)).2
          have ev := hρL v hvI (by omega)
          exact ⟨hvZ' v hvI (by omega), sameRun_between hθr (Or.inr ⟨by omega, by omega⟩)⟩
      have hvτ' : v ∉ τ := fun h => hvτ v h rfl
      refine ⟨(hBQ d).2 ⟨hdI, hdZ⟩, (hBQ v).2 ⟨hvI, hvZ⟩, hdτ, hvτ', ?_⟩
      by_contra hno
      exact hdr (pkCo_sameRun_trans qts hτI hvI hvτ' hno hvr)
    by_cases h1 : p.1 ∈ Θ
    · obtain ⟨q1, q2, q1τ, q2τ, t, ht, c1, c2⟩ := key p.1 p.2 hp1 hp2 h1 hp1Θ b1 b2
      exact disjoint_left.1 hτd (pkCo_mem_sepIn.2 ⟨hpd, q1, q2, q1τ, q2τ, t, ht, c1, c2⟩) hpm
    by_cases h2 : p.2 ∈ Θ
    · obtain ⟨q2, q1, q2τ, q1τ, t, ht, c1, c2⟩ :=
        key p.2 p.1 hp2 hp1 h2 hp2Θ (by omega) (by omega)
      exact disjoint_left.1 hτd
        (pkCo_mem_sepIn.2 ⟨hpd, q1, q2, q1τ, q2τ, t, ht, by omega, by omega⟩) hpm
    exact disjoint_left.1 hΘd (pkCo_mem_sepIn.2 ⟨hpd, hp1, hp2, h1, h2, θ, hθΘ, b1, b2⟩) hpm
  -- spread: the missing oo pairs of `X` and `Y` lie in runs of `A′ ∖ Θ′`, different ones
  have hrun : ∀ W, IsRunOf N (headStart P) (oddSide N P) Θ W → ∀ r : ℕ × ℕ, r.1 ∈ W →
      r.2 ∈ W → InOneRun N (headStart P) (headLen N P) (Θ \ (Icc 1 N \ reachPiece N P Q τ)) r := by
    intro W hW r h1 h2
    have hA' := (pkCh_arcs (by omega) hE' hP).1
    have m1 := mem_sdiff.1 (hW.2.1 h1)
    have m2 := mem_sdiff.1 (hW.2.1 h2)
    exact ⟨(hA' _).1 m1.1, (hA' _).1 m2.1, fun h => m1.2 (hsubΘ h), fun h => m2.2 (hsubΘ h),
      fun ⟨θ, hθ, hb⟩ => hW.2.2.1 _ h1 _ h2 ⟨θ, hsubΘ hθ, hb⟩⟩
  obtain ⟨hXr, p, hpM, hp1, hp2⟩ := hX
  obtain ⟨hYr, q, hqM, hq1, hq2⟩ := hY
  exact ⟨hadm, fun θ hθ => hΘe θ (hsubΘ hθ), hfree, hlt, hsep,
    (isSpread_iff_spread hN hE hP fun x hx => legs_of_mem_admSeps hE hP hΘ (hsubΘ hx)).2
      ⟨p, hpM, q, hqM, hrun X hXr p hp1 hp2,
      hrun Y hYr q hq1 hq2, hsep _ hp1 _ hq1⟩⟩

-- registry: C-90P5
/-- **Shortening**: for even `N ≥ 6`, let the odd chord `P′` have its even-ended side
`B′` linked, `Θ` a free even separator of `A′`, `X` before `Y` two occupied runs of
`A′ ∖ Θ` (`y₀` the first leg of `Y` along `A′`), `Q_X` the run chord of `X`, and `τ` a free
separator of `B_{Q_X}`. If `τ` is non-reaching (`y₀ ∉ R_τ^c`), then
`Θ′ := Θ ∖ R_τ^c` is a free even separator of `A′` with `Θ′ ⊊ Θ` that separates `X` from
`Y`; so `Θ′` is spread. No hypothesis on `S`. -/
theorem Combinatorics.Polygons.shortening_spread_separator {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    {S : Finset (ℕ × ℕ)} {P QX : ℕ × ℕ} (hP : P ∈ oddDiagonals N)
    (hlinked : NoFreeSep N S (tailStart P) (tailLen N P) 1) {Θ : Finset ℕ}
    (hΘ : Θ ∈ admSeps N (headStart P) (headLen N P) 0) (hΘe : ∀ θ ∈ Θ, θ % 2 = 0)
    (hΘd : Disjoint (sepIn N (headStart P) (headLen N P) Θ) (missing N S)) {X Y : Finset ℕ}
    (hX : IsOccupiedRun N S P Θ X) (hY : IsOccupiedRun N S P Θ Y)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, cycPos N (headStart P) x < cycPos N (headStart P) y) {y0 : ℕ}
    (hy0 : y0 ∈ Y) (hy0f : ∀ y ∈ Y, cycPos N (headStart P) y0 ≤ cycPos N (headStart P) y)
    (hQX : QX ∈ oddDiagonals N) (hQXX : oddSide N QX = X) {τ : Finset ℕ}
    (hτ : τ ∈ admSeps N (tailStart QX) (tailLen N QX) 1)
    (hτd : Disjoint (sepIn N (tailStart QX) (tailLen N QX) τ) (missing N S))
    (hnr : y0 ∉ Icc 1 N \ reachPiece N P QX τ) :
    Θ \ (Icc 1 N \ reachPiece N P QX τ) ∈ admSeps N (headStart P) (headLen N P) 0 ∧
      (∀ θ ∈ Θ \ (Icc 1 N \ reachPiece N P QX τ), θ % 2 = 0) ∧
      Disjoint (sepIn N (headStart P) (headLen N P) (Θ \ (Icc 1 N \ reachPiece N P QX τ)))
        (missing N S) ∧
      Θ \ (Icc 1 N \ reachPiece N P QX τ) ⊂ Θ ∧
      (∀ x ∈ X, ∀ y ∈ Y,
        ¬ SameRun N (headStart P) (Θ \ (Icc 1 N \ reachPiece N P QX τ)) x y) ∧
      IsSpread N S P (Θ \ (Icc 1 N \ reachPiece N P QX τ)) := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  obtain ⟨-, -, -, -, -, hs, hs2, -, -, hkN⟩ := pkCh_sides hE' hP
  obtain ⟨qts, -, -, -, -, -, -, -, qk3, -⟩ := pkCh_sides hE' hQX
  have hN1 : 1 ≤ N := by omega
  have hsub : oddSide N QX ⊆ oddSide N P := fun x hx =>
    (mem_sdiff.1 (hX.1.2.1 (by rw [← hQXX]; exact hx))).1
  obtain ⟨c, hck, hZpos, hρR, -⟩ := run_chord_frame hN hE' hP hQX hsub
  rw [hQXX] at hZpos
  obtain ⟨hb'I, hb'π⟩ := second_leg_pos hE' hP
  have hb'ρ := hρR _ hb'I (by omega)
  have hτI : τ ⊆ Icc 1 N := fun t ht =>
    pkCo_cycArc_sub hN1 (mem_filter.1 ((pkCo_mem_admSeps.1 hτ).1 ht)).1
  -- the last leg of `X` is before `y₀`
  have hxlI : vtx N (headStart P + (c + headLen N QX - 1)) ∈ Icc 1 N :=
    mem_Icc.2 (vtx_bounds N _ hN1)
  have hxlπ : cycPos N (headStart P) (vtx N (headStart P + (c + headLen N QX - 1))) =
      c + headLen N QX - 1 := pkCo_cycPos_vtx hs (by omega)
  have hxl := hXY _ ((hZpos _ hxlI).2 ⟨by omega, by omega⟩) y0 hy0
  obtain ⟨hy0I, hy0h⟩ := (pkCh_headpos hN hE' hP).1 (mem_sdiff.1 (hY.1.2.1 hy0)).1
  -- `d₀`, the leg before `y₀`, is in `Θ`
  have hd0I : vtx N (headStart P + (cycPos N (headStart P) y0 - 1)) ∈ Icc 1 N :=
    mem_Icc.2 (vtx_bounds N _ hN1)
  have hd0π : cycPos N (headStart P) (vtx N (headStart P + (cycPos N (headStart P) y0 - 1))) =
      cycPos N (headStart P) y0 - 1 := pkCo_cycPos_vtx hs (by omega)
  have hd0Θ : vtx N (headStart P + (cycPos N (headStart P) y0 - 1)) ∈ Θ :=
    mem_of_adj_run hY.1 hy0 ((pkCh_headpos hN hE' hP).2 ⟨hd0I, by omega⟩)
      (fun h => by have := hy0f _ h; omega) (Or.inl (by omega))
  have hd0c : c + headLen N QX ≤
      cycPos N (headStart P) (vtx N (headStart P + (cycPos N (headStart P) y0 - 1))) := by
    by_contra h
    exact (mem_sdiff.1 (hX.1.2.1 ((hZpos _ hd0I).2 ⟨by omega, by omega⟩))).2 hd0Θ
  -- `y₀` is odd and lies in `R_τ`, so off `τ`
  have hy0odd : y0 % 2 = 1 := by
    have h1 := pkCh_pos_mod hE' hs hs2 hy0I
    have h2 := pkCh_pos_mod hE' hs hs2 hd0I
    have := hΘe _ hd0Θ
    omega
  have hy0R : y0 ∈ reachPiece N P QX τ := by
    by_contra h
    exact hnr (mem_sdiff.2 ⟨hy0I, h⟩)
  obtain ⟨hy0τ, hy0r⟩ : y0 ∉ τ ∧ SameRun N (tailStart QX) τ y0 (vtx N (tailStart P + 1)) := by
    rcases mem_union.1 hy0R with h | h
    · exact ⟨(mem_filter.1 h).2.1, (mem_filter.1 h).2.2⟩
    · have := (mem_filter.1 h).2.2
      omega
  -- so `d₀` is in the `τ`-piece of the second leg of `B′`
  have ey := hρR y0 hy0I (by omega)
  have ed := hρR _ hd0I hd0c
  have hd0r : SameRun N (tailStart QX) τ (vtx N (headStart P + (cycPos N (headStart P) y0 - 1)))
      (vtx N (tailStart P + 1)) :=
    pkCo_sameRun_trans qts hτI hy0I hy0τ (fun ⟨t, _, h1, h2⟩ => by omega) hy0r
  exact shortening_core hN hE hP hlinked hΘ hΘe hΘd hX hY hX.1 hQX hQXX hτ hτd hd0Θ hd0r
    (fun x hx => by
      have hxI := ((pkCh_headpos hN hE' hP).1 (mem_sdiff.1 (hX.1.2.1 hx)).1).1
      have := (hZpos x hxI).1 hx
      omega)
    (fun y hy => by have := hy0f y hy; omega)

-- registry: C-90P5
/-- **Shortening**, the mirror for `Q_Y`: as `shortening_spread_separator`, with `σ`
a free separator of `B_{Q_Y}` and `x₁` the last leg of `X` along `A′`. If `σ` is non-reaching
(`x₁ ∉ R_σ^c`), then `Θ′ := Θ ∖ R_σ^c` is a free even separator of `A′` with `Θ′ ⊊ Θ` that
separates `X` from `Y`; so `Θ′` is spread. No hypothesis on `S`. -/
theorem Combinatorics.Polygons.shortening_spread_separator_mirror {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    {S : Finset (ℕ × ℕ)} {P QY : ℕ × ℕ}
    (hP : P ∈ oddDiagonals N) (hlinked : NoFreeSep N S (tailStart P) (tailLen N P) 1)
    {Θ : Finset ℕ} (hΘ : Θ ∈ admSeps N (headStart P) (headLen N P) 0)
    (hΘe : ∀ θ ∈ Θ, θ % 2 = 0)
    (hΘd : Disjoint (sepIn N (headStart P) (headLen N P) Θ) (missing N S)) {X Y : Finset ℕ}
    (hX : IsOccupiedRun N S P Θ X) (hY : IsOccupiedRun N S P Θ Y)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, cycPos N (headStart P) x < cycPos N (headStart P) y) {x1 : ℕ}
    (hx1 : x1 ∈ X) (hx1l : ∀ x ∈ X, cycPos N (headStart P) x ≤ cycPos N (headStart P) x1)
    (hQY : QY ∈ oddDiagonals N) (hQYY : oddSide N QY = Y) {σ : Finset ℕ}
    (hσ : σ ∈ admSeps N (tailStart QY) (tailLen N QY) 1)
    (hσd : Disjoint (sepIn N (tailStart QY) (tailLen N QY) σ) (missing N S))
    (hnr : x1 ∉ Icc 1 N \ reachPiece N P QY σ) :
    Θ \ (Icc 1 N \ reachPiece N P QY σ) ∈ admSeps N (headStart P) (headLen N P) 0 ∧
      (∀ θ ∈ Θ \ (Icc 1 N \ reachPiece N P QY σ), θ % 2 = 0) ∧
      Disjoint (sepIn N (headStart P) (headLen N P) (Θ \ (Icc 1 N \ reachPiece N P QY σ)))
        (missing N S) ∧
      Θ \ (Icc 1 N \ reachPiece N P QY σ) ⊂ Θ ∧
      (∀ x ∈ X, ∀ y ∈ Y,
        ¬ SameRun N (headStart P) (Θ \ (Icc 1 N \ reachPiece N P QY σ)) x y) ∧
      IsSpread N S P (Θ \ (Icc 1 N \ reachPiece N P QY σ)) := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  obtain ⟨-, -, -, -, -, hs, hs2, -, -, hkN⟩ := pkCh_sides hE' hP
  obtain ⟨qts, -, -, -, -, -, -, -, qk3, -⟩ := pkCh_sides hE' hQY
  have hN1 : 1 ≤ N := by omega
  have hsub : oddSide N QY ⊆ oddSide N P := fun x hx =>
    (mem_sdiff.1 (hY.1.2.1 (by rw [← hQYY]; exact hx))).1
  obtain ⟨c, hck, hZpos, hρR, hρL⟩ := run_chord_frame hN hE' hP hQY hsub
  rw [hQYY] at hZpos
  obtain ⟨hb'I, hb'π⟩ := second_leg_pos hE' hP
  have hb'ρ := hρR _ hb'I (by omega)
  have hσI : σ ⊆ Icc 1 N := fun t ht =>
    pkCo_cycArc_sub hN1 (mem_filter.1 ((pkCo_mem_admSeps.1 hσ).1 ht)).1
  -- `x₁` is before the first leg of `Y`
  have hyfI : vtx N (headStart P + c) ∈ Icc 1 N := mem_Icc.2 (vtx_bounds N _ hN1)
  have hyfπ : cycPos N (headStart P) (vtx N (headStart P + c)) = c :=
    pkCo_cycPos_vtx hs (by omega)
  have hyf := hXY x1 hx1 _ ((hZpos _ hyfI).2 ⟨by omega, by omega⟩)
  obtain ⟨hx1I, hx1h⟩ := (pkCh_headpos hN hE' hP).1 (mem_sdiff.1 (hX.1.2.1 hx1)).1
  -- `d₀`, the leg after `x₁`, is in `Θ`
  have hd0I : vtx N (headStart P + (cycPos N (headStart P) x1 + 1)) ∈ Icc 1 N :=
    mem_Icc.2 (vtx_bounds N _ hN1)
  have hd0π : cycPos N (headStart P) (vtx N (headStart P + (cycPos N (headStart P) x1 + 1))) =
      cycPos N (headStart P) x1 + 1 := pkCo_cycPos_vtx hs (by omega)
  have hd0Θ : vtx N (headStart P + (cycPos N (headStart P) x1 + 1)) ∈ Θ :=
    mem_of_adj_run hX.1 hx1 ((pkCh_headpos hN hE' hP).2 ⟨hd0I, by omega⟩)
      (fun h => by have := hx1l _ h; omega) (Or.inr (by omega))
  have hd0c : cycPos N (headStart P) (vtx N (headStart P + (cycPos N (headStart P) x1 + 1))) <
      c := by
    by_contra h
    exact (mem_sdiff.1 (hY.1.2.1 ((hZpos _ hd0I).2 ⟨by omega, by omega⟩))).2 hd0Θ
  -- `x₁` is odd and lies in `R_σ`, so off `σ`
  have hx1odd : x1 % 2 = 1 := by
    have h1 := pkCh_pos_mod hE' hs hs2 hx1I
    have h2 := pkCh_pos_mod hE' hs hs2 hd0I
    have := hΘe _ hd0Θ
    omega
  have hx1R : x1 ∈ reachPiece N P QY σ := by
    by_contra h
    exact hnr (mem_sdiff.2 ⟨hx1I, h⟩)
  obtain ⟨hx1σ, hx1r⟩ : x1 ∉ σ ∧ SameRun N (tailStart QY) σ x1 (vtx N (tailStart P + 1)) := by
    rcases mem_union.1 hx1R with h | h
    · exact ⟨(mem_filter.1 h).2.1, (mem_filter.1 h).2.2⟩
    · have := (mem_filter.1 h).2.2
      omega
  -- so `d₀` is in the `σ`-piece of the second leg of `B′`
  have ex := hρL x1 hx1I (by omega)
  have ed := hρL _ hd0I hd0c
  have hd0r : SameRun N (tailStart QY) σ (vtx N (headStart P + (cycPos N (headStart P) x1 + 1)))
      (vtx N (tailStart P + 1)) :=
    pkCo_sameRun_trans qts hσI hx1I hx1σ (fun ⟨t, _, h1, h2⟩ => by omega) hx1r
  exact shortening_core hN hE hP hlinked hΘ hΘe hΘd hX hY hY.1 hQY hQYY hσ hσd hd0Θ hd0r
    (fun x hx => by have := hx1l x hx; omega)
    (fun y hy => by
      have hyI := ((pkCh_headpos hN hE' hP).1 (mem_sdiff.1 (hY.1.2.1 hy)).1).1
      have := (hZpos y hyI).1 hy
      omega)

/-! ### The side lemma and no odd singleton -/

-- registry: C-WGZD
/-- **The side lemma**: for a candidate set `S` at even `N ≥ 6`, let `P′ ∈ 𝒮_B` and
`Q ∈ 𝒫₁` o-clean (`o_in(Q) = o_in(P′)`) with `A_Q ⊆ A′` (`Q = P′` allowed). Suppose `A_Q` is not
linked, witnessed by `{x}` (a free separator of `A_Q`), `x` odd, and the piece of `A_Q` from
`x` to its last leg contains a pair of `o_in(Q)`. Then some `Z ∈ 𝒮_B` has `A_Z ⊆ [x, ω] ⊊ A′`, where
`[x, ω]` is the part of `A′` from `x` to its last leg `ω`. -/
theorem Combinatorics.Polygons.unlinked_side_has_smaller_linked_chord {N : ℕ} (hN : 6 ≤ N)
    (hE : Even N) {S : Finset (ℕ × ℕ)} (hF : IsCandidateSet N S)
    {P Q : ℕ × ℕ} (hP : P ∈ goodTail N S) (hQ : Q ∈ poleChords N S)
    (hsub : oddSide N Q ⊆ oddSide N P) (hoo : innerOO N S Q = innerOO N S P) {x : ℕ}
    (hx : {x} ∈ admSeps N (headStart Q) (headLen N Q) 0) (hx2 : x % 2 = 1)
    (hxd : Disjoint (sepIn N (headStart Q) (headLen N Q) {x}) (missing N S))
    (hpair : ∃ p ∈ innerOO N S Q, cycPos N (headStart Q) x ≤ cycPos N (headStart Q) p.1 ∧
      cycPos N (headStart Q) x ≤ cycPos N (headStart Q) p.2) :
    ∃ Z ∈ goodTail N S,
      oddSide N Z ⊆ (oddSide N P).filter
          (fun z => cycPos N (headStart P) x ≤ cycPos N (headStart P) z) ∧
        (oddSide N P).filter (fun z => cycPos N (headStart P) x ≤ cycPos N (headStart P) z) ⊂
          oddSide N P := by
  replace hF := (isCandidateSet_iff_inFpi hE).1 hF
  have hE : N % 2 = 0 := Nat.even_iff.1 hE
  have hPo := (pkCh_mem_pole.1 (pkCh_mem_goodTail.1 hP).1).1
  have hQo := (pkCh_mem_pole.1 hQ).1
  obtain ⟨-, -, -, -, -, hs, -, hk1, -, -⟩ := pkCh_sides hE hPo
  obtain ⟨-, -, hmemP, hposP⟩ := pkCh_subHead hN hE hQo hPo hsub
  obtain ⟨hxP, hx1, -, -⟩ := pkCh_sideLeg hN hE hPo hQo hsub hx
  have hxI := ((pkCh_headpos hN hE hPo).1 hxP).1
  have hxq := hposP x hxI (by omega)
  -- positions along `A_Q` and along `A′` differ by a constant on `A_Q`
  have hpos : ∀ y ∈ oddSide N Q, cycPos N (headStart Q) x ≤ cycPos N (headStart Q) y →
      cycPos N (headStart P) x ≤ cycPos N (headStart P) y := fun y hy hle => by
    have hyI := ((pkCh_headpos hN hE hQo).1 hy).1
    have hyP := ((hmemP y hyI).1 hy).1
    have := hposP y hyI hyP
    omega
  obtain ⟨⟨f1, f2⟩, hf, h1, h2⟩ := hpair
  obtain ⟨-, hf1, hf2⟩ := pkCh_mem_innerOO.1 hf
  obtain ⟨Z, hZ, hZs⟩ := pkCh_sideR hN hE hF hP hQ hsub hoo hx hx2 hxd
    ⟨f1, f2, hoo ▸ hf, hpos f1 hf1 h1, hpos f2 hf2 h2⟩
  refine ⟨Z, hZ, fun z hz => mem_filter.2 (hZs z hz),
    (ssubset_iff_of_subset (filter_subset _ _)).2 ⟨headStart P,
      (pkCh_headpos hN hE hPo).2 ⟨hs, by rw [pkCo_cycPos_self hs]; omega⟩, fun h => ?_⟩⟩
  have := (mem_filter.1 h).2
  rw [pkCo_cycPos_self hs] at this
  omega

-- registry: C-WGZD
/-- **The side lemma**, the mirror for the piece of `A_Q` from its first leg to `x`:
then some `Z ∈ 𝒮_B` has `A_Z ⊆ [α, x] ⊊ A′`, where `[α, x]` is the part of `A′` from its first
leg `α` to `x`. -/
theorem Combinatorics.Polygons.unlinked_side_has_smaller_linked_chord_mirror {N : ℕ} (hN : 6 ≤ N)
    (hE : Even N) {S : Finset (ℕ × ℕ)}
    (hF : IsCandidateSet N S) {P Q : ℕ × ℕ} (hP : P ∈ goodTail N S) (hQ : Q ∈ poleChords N S)
    (hsub : oddSide N Q ⊆ oddSide N P) (hoo : innerOO N S Q = innerOO N S P) {x : ℕ}
    (hx : {x} ∈ admSeps N (headStart Q) (headLen N Q) 0) (hx2 : x % 2 = 1)
    (hxd : Disjoint (sepIn N (headStart Q) (headLen N Q) {x}) (missing N S))
    (hpair : ∃ p ∈ innerOO N S Q, cycPos N (headStart Q) p.1 ≤ cycPos N (headStart Q) x ∧
      cycPos N (headStart Q) p.2 ≤ cycPos N (headStart Q) x) :
    ∃ Z ∈ goodTail N S,
      oddSide N Z ⊆ (oddSide N P).filter
          (fun z => cycPos N (headStart P) z ≤ cycPos N (headStart P) x) ∧
        (oddSide N P).filter (fun z => cycPos N (headStart P) z ≤ cycPos N (headStart P) x) ⊂
          oddSide N P := by
  replace hF := (isCandidateSet_iff_inFpi hE).1 hF
  have hE : N % 2 = 0 := Nat.even_iff.1 hE
  have hPo := (pkCh_mem_pole.1 (pkCh_mem_goodTail.1 hP).1).1
  have hQo := (pkCh_mem_pole.1 hQ).1
  obtain ⟨-, -, -, -, -, hs, -, hk1, -, hkN⟩ := pkCh_sides hE hPo
  obtain ⟨-, -, hmemP, hposP⟩ := pkCh_subHead hN hE hQo hPo hsub
  obtain ⟨hxP, hx1, hx3, hcb⟩ := pkCh_sideLeg hN hE hPo hQo hsub hx
  have hxI := ((pkCh_headpos hN hE hPo).1 hxP).1
  have hxq := hposP x hxI (by omega)
  -- positions along `A_Q` and along `A′` differ by a constant on `A_Q`
  have hpos : ∀ y ∈ oddSide N Q, cycPos N (headStart Q) y ≤ cycPos N (headStart Q) x →
      cycPos N (headStart P) y ≤ cycPos N (headStart P) x := fun y hy hle => by
    have hyI := ((pkCh_headpos hN hE hQo).1 hy).1
    have hyP := ((hmemP y hyI).1 hy).1
    have := hposP y hyI hyP
    omega
  obtain ⟨⟨f1, f2⟩, hf, h1, h2⟩ := hpair
  obtain ⟨-, hf1, hf2⟩ := pkCh_mem_innerOO.1 hf
  obtain ⟨Z, hZ, hZs⟩ := pkCh_sideL hN hE hF hP hQ hsub hoo hx hx2 hxd
    ⟨f1, f2, hoo ▸ hf, hpos f1 hf1 h1, hpos f2 hf2 h2⟩
  have hωI : headLen N P ∈ Icc 1 N := mem_Icc.2 ⟨by omega, by omega⟩
  have pω := pkCh_psi_pos hs hωI
  refine ⟨Z, hZ, fun z hz => mem_filter.2 (hZs z hz),
    (ssubset_iff_of_subset (filter_subset _ _)).2 ⟨rotLeg N (headStart P - 1) (headLen N P),
      (pkCh_headpos hN hE hPo).2 ⟨pkCh_psi_mem (by omega) _, by rw [pω]; omega⟩, fun h => ?_⟩⟩
  have := (mem_filter.1 h).2
  rw [pω] at this
  omega

-- registry: C-0AZ0
/-- **No odd singleton**: for a candidate set `S` at even `N ≥ 6` and an innermost chord `P*`, no
member `Q` of `K*`, `P*` included, has an odd singleton free separator of `A_Q`. -/
theorem Combinatorics.Polygons.no_odd_singleton_separator {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    {S : Finset (ℕ × ℕ)} (hF : IsCandidateSet N S) {P : ℕ × ℕ} (hP : IsInnermostChord N S P)
    {Q : ℕ × ℕ} (hQ : Q ∈ hitClass N S P) {x : ℕ}
    (hx : {x} ∈ admSeps N (headStart Q) (headLen N Q) 0) (hx2 : x % 2 = 1) :
    ¬ Disjoint (sepIn N (headStart Q) (headLen N Q) {x}) (missing N S) := by
  intro hxd
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  obtain ⟨hPg, hmin⟩ := pkCh_minChord_iff.1 hP
  obtain ⟨hPp, hPB⟩ := pkCh_mem_goodTail.1 hPg
  obtain ⟨hPo, -, -, ⟨⟨f1, f2⟩, hf⟩⟩ := pkCh_mem_pole.1 hPp
  obtain ⟨hQp, hQh⟩ := pkCh_mem_hitClass.1 hQ
  have hQo := (pkCh_mem_pole.1 hQp).1
  -- top and bottom (a), and the flank sets (c): `A_Q ⊆ A*` and `o_in(Q) = o_in(P*) ≠ ∅`
  have hsub := pkCh_int_top hN hE' hPp hPB hQp hQh
  have hoo := pkCh_class_oo hN hE' hPo hQo hQh
  have hfQ : (f1, f2) ∈ innerOO N S Q := hoo ▸ hf
  -- a pair of `o_in(Q)` lies in one of the two pieces of `A_Q ∖ {x}`
  by_cases hRt : cycPos N (headStart Q) x ≤ cycPos N (headStart Q) f1 ∧
      cycPos N (headStart Q) x ≤ cycPos N (headStart Q) f2
  · obtain ⟨Z, hZ, hZs, hss⟩ :=
      unlinked_side_has_smaller_linked_chord hN hE hF hPg hQp hsub hoo hx hx2 hxd
        ⟨(f1, f2), hfQ, hRt⟩
    exact hmin Z hZ (hZs.trans_ssubset hss)
  by_cases hLt : cycPos N (headStart Q) f1 ≤ cycPos N (headStart Q) x ∧
      cycPos N (headStart Q) f2 ≤ cycPos N (headStart Q) x
  · obtain ⟨Z, hZ, hZs, hss⟩ :=
      unlinked_side_has_smaller_linked_chord_mirror hN hE hF hPg hQp hsub hoo hx hx2 hxd
        ⟨(f1, f2), hfQ, hLt⟩
    exact hmin Z hZ (hZs.trans_ssubset hss)
  -- a pair across `x` is in `sep_{A_Q}({x})`, hence not missing
  obtain ⟨hfM, hf1Q, hf2Q⟩ := pkCh_mem_innerOO.1 hfQ
  have hm := (pkCh_mem_Moo.1 hfM).1
  have a1 := ((pkCh_arcs (by omega) hE' hQo).1 f1).1 hf1Q
  have a2 := ((pkCh_arcs (by omega) hE' hQo).1 f2).1 hf2Q
  have n1 : f1 ∉ ({x} : Finset ℕ) := fun h => by rw [mem_singleton] at h; subst h; omega
  have n2 : f2 ∉ ({x} : Finset ℕ) := fun h => by rw [mem_singleton] at h; subst h; omega
  exact disjoint_left.1 hxd (pkCo_mem_sepIn.2 ⟨(pkCh_mem_missing.1 hm).1, a1, a2, n1, n2, x,
    mem_singleton_self _, by dsimp only; omega, by dsimp only; omega⟩) hm

/-! ### Thin runs -/

set_option maxHeartbeats 400000 in
-- one long proof in the linear setting of `P′` (positions along `B_Q`, closed by `omega`): passes at
-- 300,000 and fails at 200,000; `#count_heartbeats` reports about 349,000
-- registry: C-RH2N
/-- **Thin runs**: for a candidate set `S` at even `N ≥ 6`, let `P′ ∈ 𝒮_B` and `Q ∈ 𝒫₀`
o-clean (`o_in(Q) = o_in(P′)`) with `A_Q ⊊ A′`. Then every free separator `τ` of `B_Q` is odd
(all its legs are odd), `B′` lies in one run `R_♮` of `B_Q ∖ τ`, and every other run is a single
even leg. Corollary: if moreover `e_in(Q) ≠ ∅`, the chord `Q⁺` with even-ended side `R_♮` is in
`𝒫₁`, o-clean, with `h_{Q⁺} = h_Q` and `A_Q ⊊ A_{Q⁺} ⊆ A′`. -/
theorem Combinatorics.Polygons.thin_runs {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {S : Finset (ℕ × ℕ)}
    (hF : IsCandidateSet N S) {P Q : ℕ × ℕ} (hP : P ∈ goodTail N S) (hQ : Q ∈ cleanChords N S)
    (hsub : oddSide N Q ⊂ oddSide N P) (hoo : innerOO N S Q = innerOO N S P) {τ : Finset ℕ}
    (hτ : τ ∈ admSeps N (tailStart Q) (tailLen N Q) 1)
    (hτd : Disjoint (sepIn N (tailStart Q) (tailLen N Q) τ) (missing N S)) :
    (∀ t ∈ τ, t % 2 = 1) ∧
      ∃ R, IsRunOf N (tailStart Q) (evenSide N Q) τ R ∧ evenSide N P ⊆ R ∧
        (∀ Z, IsRunOf N (tailStart Q) (evenSide N Q) τ Z → Z ≠ R → ∃ e, e % 2 = 0 ∧ Z = {e}) ∧
        ((innerEE N S Q).Nonempty →
          ∃ Qp ∈ poleChords N S, evenSide N Qp = R ∧ innerOO N S Qp = innerOO N S P ∧
            hitSet N S Qp = hitSet N S Q ∧ oddSide N Q ⊂ oddSide N Qp ∧
            oddSide N Qp ⊆ oddSide N P) := by
  replace hF := (isCandidateSet_iff_inFpi hE).1 hF
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  -- the linear setting of `P′` (labels `cycPos + 1`): `A′ = [1, ω]`, `A_Q = [c + 1, c + k]`
  obtain ⟨hPp, hPB⟩ := pkCh_mem_goodTail.1 hP
  obtain ⟨hPo, -, -, hPoo⟩ := pkCh_mem_pole.1 hPp
  obtain ⟨hQo, hQc⟩ := mem_filter.1 hQ
  obtain ⟨-, -, -, -, -, hs, hs2, hk1, hk3, hkN⟩ := pkCh_sides hE' hPo
  obtain ⟨-, -, -, -, -, hws, hws2, hwk1, hwk3, hwkN⟩ := pkCh_sides hE' hQo
  have hN1 : 1 ≤ N := by omega
  have hsI := mem_Icc.1 hs
  obtain ⟨hcb, hc2, hmemP, -⟩ := pkCh_subHead hN hE' hQo hPo hsub.subset
  obtain ⟨c, hc⟩ : ∃ c, cycPos N (headStart P) (headStart Q) = c := ⟨_, rfl⟩
  rw [hc] at hcb hc2 hmemP
  have hWts : tailStart Q = vtx N (headStart P + (c + headLen N Q)) := by
    rw [pkCh_tail_eq hQo]
    rw [← pkCo_vtx_cycPos hs hws, hc, pkCo_vtx_vtx_add hN1, add_assoc]
  have hWtl : tailLen N Q = N - (c + headLen N Q + 1 - (c + 1)) := by
    rw [show c + headLen N Q + 1 - (c + 1) = headLen N Q by omega]
    rfl
  -- the trace `τ` read linearly
  obtain ⟨τl, hτl⟩ : ∃ τl, τl = τ.image (rotLeg N (N + 1 - headStart P)) := ⟨_, rfl⟩
  have hasc := pkCh_tailAsc hN hE' hPo hQo (a := c + 1) (b := c + headLen N Q)
    (by omega) (by omega) hcb hWts hWtl hτ
  have hτf := pkCh_tailSep hN hE' (S := S) hPo hQo (a := c + 1) (b := c + headLen N Q)
    (by omega) (by omega) hcb hWts hWtl hτ hτd
  rw [← hτl] at hasc hτf
  have hTA := pkCh_b0 hE' hk1 hkN (by omega : c + 1 ≤ c + headLen N Q) hcb (pkCh_HW hN hE'
      hPo hPB) hasc hτf
  have HG := pkCh_HG hN hE' hF hs hs2
  have Hmr : ∀ e o, e ∈ Icc 1 N → o ∈ Icc 1 N → e % 2 = 0 → o % 2 = 1 → c + 1 ≤ e → e ≤
      c + headLen N Q →
      ¬ (c + 1 ≤ o ∧ o ≤ c + headLen N Q) → pkChCl N (headStart P) S e o := by
    intro e o he ho he2 ho2 h1 h2 ho'
    rw [pkCh_Cl_iff]
    rintro ⟨-, -, hm⟩
    have pe := pkCh_psi_pos hs he
    have po := pkCh_psi_pos hs ho
    have eW : rotLeg N (headStart P - 1) e ∈ oddSide N Q :=
      (hmemP _ (pkCh_psi_mem hN1 e)).2 (by rw [pe]; omega)
    have oW : rotLeg N (headStart P - 1) o ∈ evenSide N Q := by
      change rotLeg N (headStart P - 1) o ∈ Icc 1 N \ oddSide N Q
      refine mem_sdiff.2 ⟨pkCh_psi_mem hN1 o, fun h => ?_⟩
      have := (hmemP _ (pkCh_psi_mem hN1 o)).1 h
      rw [po] at this
      omega
    have me := pkCh_psi_mod hN1 hE' hsI.1 hs2 e
    have mo := pkCh_psi_mod hN1 hE' hsI.1 hs2 o
    have hr : (min (rotLeg N (headStart P - 1) e) (rotLeg N (headStart P - 1) o),
        max (rotLeg N (headStart P - 1) e) (rotLeg N (headStart P - 1) o)) ∈ minRect N Q :=
      pkCh_mem_minRect.2 ⟨_, pkCh_mem_evens.2 ⟨eW, by omega⟩, _,
          pkCh_mem_odds.2 ⟨oW, by omega⟩, rfl⟩
    rcases hm with hm | hm
    · have hd := mem_diagonals.1 (pkCh_mem_missing.1 hm).1
      dsimp only at hd
      rw [min_eq_left (by omega), max_eq_right (by omega)] at hr
      exact disjoint_left.1 hQc hr hm
    · have hd := mem_diagonals.1 (pkCh_mem_missing.1 hm).1
      dsimp only at hd
      rw [min_eq_right (by omega), max_eq_left (by omega)] at hr
      exact disjoint_left.1 hQc hr hm
  have Hoc : ∀ u v, u % 2 = 1 → v % 2 = 1 → 1 ≤ u → u ≤ headLen N P → 1 ≤ v → v ≤ headLen N P →
      ¬ (c + 1 ≤ u ∧ u ≤ c + headLen N Q) → pkChCl N (headStart P) S u v := by
    intro u v hu hv u1 u2 v1 v2 hu'
    rw [pkCh_Cl_iff]
    rintro ⟨huI, hvI, hm⟩
    have pu := pkCh_psi_pos hs huI
    have pv := pkCh_psi_pos hs hvI
    have mu := pkCh_psi_mod hN1 hE' hsI.1 hs2 u
    have mv := pkCh_psi_mod hN1 hE' hsI.1 hs2 v
    have uP : rotLeg N (headStart P - 1) u ∈ oddSide N P :=
      (pkCh_headpos hN hE' hPo).2 ⟨pkCh_psi_mem hN1 u, by rw [pu]; omega⟩
    have vP : rotLeg N (headStart P - 1) v ∈ oddSide N P :=
      (pkCh_headpos hN hE' hPo).2 ⟨pkCh_psi_mem hN1 v, by rw [pv]; omega⟩
    have key : ∀ x y, (x, y) ∈ missing N S → x % 2 = 1 → y % 2 = 1 → x ∈ oddSide N P →
        y ∈ oddSide N P →
        x ∈ oddSide N Q ∧ y ∈ oddSide N Q := by
      intro x y hm hx hy hxP hyP
      have hin : (x, y) ∈ innerOO N S P :=
          pkCh_mem_innerOO.2 ⟨pkCh_mem_Moo.2 ⟨hm, hx, hy⟩, hxP, hyP⟩
      rw [← hoo] at hin
      exact ⟨(pkCh_mem_innerOO.1 hin).2.1, (pkCh_mem_innerOO.1 hin).2.2⟩
    have uW : rotLeg N (headStart P - 1) u ∉ oddSide N Q := fun h => by
      have := (hmemP _ (pkCh_psi_mem hN1 u)).1 h
      rw [pu] at this
      omega
    rcases hm with hm | hm
    · exact uW (key _ _ hm (by omega) (by omega) uP vP).1
    · exact uW (key _ _ hm (by omega) (by omega) vP uP).2
  obtain ⟨hodd, lo, hi, hloa, hhib, hhiω, hlo1, hlo2, hhi2, hside, hloT, hhiT, hhi, hlo, T2, T3,
      LL⟩ := pkCh_thinLinRuns pkCh_Cl_symm hE' hkN (by omega) (by omega) (by omega)
        (by omega) hcb hasc hTA hτf HG Hmr Hoc
  -- translation between legs and labels
  obtain ⟨-, hτsub, -⟩ := pkCh_asc_facts hasc
  have hτI : ∀ t ∈ τl, (1 ≤ t ∧ t ≤ N) ∧ ¬ (c + 1 ≤ t ∧ t ≤ c + headLen N Q) := fun t ht =>
    ⟨(pkCh_mem_intCompl.1 (hτsub ht)).1, (pkCh_mem_intCompl.1 (hτsub ht)).2.1⟩
  have hQtsI : tailStart Q ∈ Icc 1 N := (pkCh_sides hE' hQo).1
  have hτ0I : ∀ x ∈ τ, x ∈ Icc 1 N := fun x hx =>
    ((pkCo_mem_intArc hQtsI (by rw [hWtl]; omega)).1 ((pkCo_mem_admSeps.1 hτ).1 hx)).1
  have hmemτ : ∀ x ∈ Icc 1 N, x ∈ τ ↔ cycPos N (headStart P) x + 1 ∈ τl := by
    intro x hx
    constructor
    · intro h
      rw [hτl, ← pkCh_phi_eq hs]
      exact mem_image_of_mem _ h
    · intro h
      rw [hτl] at h
      obtain ⟨y, hy, hyx⟩ := mem_image.1 h
      rw [pkCh_phi_eq hs] at hyx
      rwa [← pkCo_cycPos_inj hs (hτ0I y hy) hx (by omega)]
  have hpar : ∀ x ∈ Icc 1 N, (cycPos N (headStart P) x + 1) % 2 = x % 2 :=
    fun x hx => pkCh_pos_mod hE' hs hs2 hx
  have hposQ : ∀ x ∈ Icc 1 N, cycPos N (tailStart Q) x =
      if c + headLen N Q ≤ cycPos N (headStart P) x then
        cycPos N (headStart P) x - (c + headLen N Q)
      else cycPos N (headStart P) x + N - (c + headLen N Q) := fun x hx => by
    rw [hWts]; exact pkCh_pos_shift hs hx (by omega)
  have hevQ : ∀ x, x ∈ evenSide N Q ↔ x ∈ Icc 1 N ∧ (cycPos N (headStart P) x + 1 < c + 1 ∨
      c + headLen N Q < cycPos N (headStart P) x + 1) := by
    intro x
    rw [pkCh_mem_even (by omega) hE' hQo, hWtl]
    have hlt := pkCo_cycPos_lt hN1 (headStart P) x
    constructor
    · rintro ⟨hx, h⟩
      rw [hposQ x hx] at h
      refine ⟨hx, ?_⟩
      split_ifs at h <;> omega
    · rintro ⟨hx, h⟩
      refine ⟨hx, ?_⟩
      rw [hposQ x hx]
      split_ifs <;> omega
  have hψ : ∀ l, 1 ≤ l → l ≤ N → rotLeg N (headStart P - 1) l ∈ Icc 1 N ∧
      cycPos N (headStart P) (rotLeg N (headStart P - 1) l) + 1 = l := fun l h1 h2 =>
    ⟨pkCh_psi_mem hN1 l, by rw [pkCh_psi_pos hs (mem_Icc.2 ⟨h1, h2⟩)]; omega⟩
  -- a label of `τl` is the label of a leg of `τ`, at its position along `B_Q`
  have hθ : ∀ l ∈ τl, ∃ θ ∈ τ, cycPos N (tailStart Q) θ =
      if c + headLen N Q ≤ l - 1 then l - 1 - (c + headLen N Q)
      else l - 1 + N - (c + headLen N Q) := by
    intro l hl
    obtain ⟨⟨h1, h2⟩, -⟩ := hτI l hl
    obtain ⟨hI, hp⟩ := hψ l h1 h2
    refine ⟨_, (hmemτ _ hI).2 (by rw [hp]; exact hl), ?_⟩
    rw [hposQ _ hI, show cycPos N (headStart P) (rotLeg N (headStart P - 1) l) = l - 1 by omega]
  -- the main run `R`
  obtain ⟨R, hR⟩ : ∃ R, R = (Icc 1 N).filter (fun x => cycPos N (headStart P) x + 1 < lo ∨
      hi < cycPos N (headStart P) x + 1) := ⟨_, rfl⟩
  have hmR : ∀ x, x ∈ R ↔ x ∈ Icc 1 N ∧ (cycPos N (headStart P) x + 1 < lo ∨
      hi < cycPos N (headStart P) x + 1) := fun x => by rw [hR, mem_filter]
  have hRsub : ∀ x ∈ R, x ∈ evenSide N Q ∧ x ∉ τ := by
    intro x hx
    obtain ⟨hxI, h⟩ := (hmR x).1 hx
    refine ⟨(hevQ x).2 ⟨hxI, by omega⟩, fun ht => ?_⟩
    have hl := (hmemτ x hxI).1 ht
    have := hτI _ hl
    have := hhi _ hl
    have := hlo _ hl
    omega
  have hA : ∀ x ∈ R, ∀ z ∈ R, SameRun N (tailStart Q) τ x z := by
    rintro x hx z hz ⟨θ, hθτ, h1, h2⟩
    obtain ⟨hxI, hx'⟩ := (hmR x).1 hx
    obtain ⟨hzI, hz'⟩ := (hmR z).1 hz
    have hθI := hτ0I θ hθτ
    have hl := (hmemτ θ hθI).1 hθτ
    have := hτI _ hl
    have := hhi _ hl
    have := hlo _ hl
    have := pkCo_cycPos_lt hN1 (headStart P) x
    have := pkCo_cycPos_lt hN1 (headStart P) z
    rw [hposQ x hxI, hposQ z hzI, hposQ θ hθI] at h1 h2
    split_ifs at h1 h2 <;> omega
  have hB : ∀ x ∈ R, ∀ z, z ∈ evenSide N Q → z ∉ τ → SameRun N (tailStart Q) τ x z → z ∈ R := by
    intro x hx z hzQ hzτ hsr
    by_contra hzR
    obtain ⟨hxI, hx'⟩ := (hmR x).1 hx
    obtain ⟨hzI, hz'⟩ := (hevQ z).1 hzQ
    have hzR' : ¬ (cycPos N (headStart P) z + 1 < lo ∨ hi < cycPos N (headStart P) z + 1) :=
      fun h => hzR ((hmR z).2 ⟨hzI, h⟩)
    have hzl : cycPos N (headStart P) z + 1 ∉ τl := fun h => hzτ ((hmemτ z hzI).2 h)
    have := pkCo_cycPos_lt hN1 (headStart P) x
    have := pkCo_cycPos_lt hN1 (headStart P) z
    rcases hz' with hz' | hz'
    · have hlo' : lo ∈ τl := by
        rcases hloT with h | h
        · exact h
        · omega
      have hne : lo ≠ cycPos N (headStart P) z + 1 := fun h => hzl (h ▸ hlo')
      obtain ⟨θ, hθτ, hθp⟩ := hθ lo hlo'
      refine hsr ⟨θ, hθτ, ?_⟩
      rw [hposQ x hxI, hposQ z hzI, hθp]
      split_ifs <;> omega
    · have hhi' : hi ∈ τl := by
        rcases hhiT with h | h
        · exact h
        · omega
      have hne : hi ≠ cycPos N (headStart P) z + 1 := fun h => hzl (h ▸ hhi')
      obtain ⟨θ, hθτ, hθp⟩ := hθ hi hhi'
      refine hsr ⟨θ, hθτ, ?_⟩
      rw [hposQ x hxI, hposQ z hzI, hθp]
      split_ifs <;> omega
  -- a leg of `B_Q ∖ τ` outside `R` is a single even leg of its run
  have hC : ∀ x, x ∈ evenSide N Q → x ∉ τ → x ∉ R → x % 2 = 0 ∧ ∀ z, z ∈ evenSide N Q →
      z ∉ τ → SameRun N (tailStart Q) τ x z → z = x := by
    intro x hxQ hxτ hxR
    obtain ⟨hxI, hx'⟩ := (hevQ x).1 hxQ
    have hxR' : ¬ (cycPos N (headStart P) x + 1 < lo ∨ hi < cycPos N (headStart P) x + 1) :=
      fun h => hxR ((hmR x).2 ⟨hxI, h⟩)
    have hxl : cycPos N (headStart P) x + 1 ∉ τl := fun h => hxτ ((hmemτ x hxI).2 h)
    obtain ⟨n0, n1, n2⟩ := LL (cycPos N (headStart P) x + 1) (fun h => by
      rcases mem_union.1 h with h | h
      · rw [mem_Icc] at h; omega
      · exact hxl h) (by omega) (by omega)
    refine ⟨by rw [← hpar x hxI]; exact n2, fun z hzQ hzτ hsr => ?_⟩
    by_contra hne
    obtain ⟨hzI, hz'⟩ := (hevQ z).1 hzQ
    have hzl : cycPos N (headStart P) z + 1 ∉ τl := fun h => hzτ ((hmemτ z hzI).2 h)
    have hne' : cycPos N (headStart P) z ≠ cycPos N (headStart P) x :=
      fun h => hne (pkCo_cycPos_inj hs hzI hxI h)
    have hxK := ((pkCh_mem_even (by omega) hE' hQo).1 hxQ).2
    have hzK := ((pkCh_mem_even (by omega) hE' hQo).1 hzQ).2
    rw [hWtl, hposQ x hxI] at hxK
    rw [hWtl, hposQ z hzI] at hzK
    have := pkCo_cycPos_lt hN1 (headStart P) x
    have := pkCo_cycPos_lt hN1 (headStart P) z
    have key : ∀ l ∈ τl, ¬ (min (cycPos N (tailStart Q) x) (cycPos N (tailStart Q) z) <
        (if c + headLen N Q ≤ l - 1 then l - 1 - (c + headLen N Q)
          else l - 1 + N - (c + headLen N Q)) ∧
        (if c + headLen N Q ≤ l - 1 then l - 1 - (c + headLen N Q)
          else l - 1 + N - (c + headLen N Q)) <
          max (cycPos N (tailStart Q) x) (cycPos N (tailStart Q) z)) := by
      intro l hl h
      obtain ⟨θ, hθτ, hθp⟩ := hθ l hl
      exact hsr ⟨θ, hθτ, by rw [hθp]; exact h⟩
    rw [hposQ x hxI, hposQ z hzI] at key
    rcases mem_union.1 n0 with n0 | n0 <;> rcases mem_union.1 n1 with n1 | n1
    · rw [mem_Icc] at n0 n1; omega
    · rw [mem_Icc] at n0
      have k1 := key _ n1
      have : cycPos N (headStart P) x + 1 + 1 ≠ cycPos N (headStart P) z + 1 :=
        fun h => hzl (h ▸ n1)
      split_ifs at k1 hxK hzK <;> omega
    · rw [mem_Icc] at n1
      have k0 := key _ n0
      have : cycPos N (headStart P) x + 1 - 1 ≠ cycPos N (headStart P) z + 1 :=
        fun h => hzl (h ▸ n0)
      split_ifs at k0 hxK hzK <;> omega
    · have k0 := key _ n0
      have k1 := key _ n1
      have : cycPos N (headStart P) x + 1 + 1 ≠ cycPos N (headStart P) z + 1 :=
        fun h => hzl (h ▸ n1)
      have : cycPos N (headStart P) x + 1 - 1 ≠ cycPos N (headStart P) z + 1 :=
        fun h => hzl (h ▸ n0)
      have := hτI _ n0
      have := hτI _ n1
      split_ifs at k0 k1 hxK hzK <;> omega
  have hRrun : IsRunOf N (tailStart Q) (evenSide N Q) τ R := by
    refine ⟨?_, fun x hx => mem_sdiff.2 (hRsub x hx), hA, fun u hu v hv hsr =>
      hB u hu v (mem_sdiff.1 hv).1 (mem_sdiff.1 hv).2 hsr⟩
    obtain ⟨hI, hp⟩ := hψ (headLen N P + 1) (by omega) (by omega)
    exact ⟨_, (hmR _).2 ⟨hI, by omega⟩⟩
  refine ⟨fun t ht => by rw [← hpar t (hτ0I t ht)]; exact hodd _ ((hmemτ t (hτ0I t ht)).1 ht),
    R, hRrun, fun x hx => ?_, ?_, ?_⟩
  · obtain ⟨hxI, h⟩ := (pkCh_evenpos hN hE' hPo).1 hx
    exact (hmR x).2 ⟨hxI, by omega⟩
  · rintro Z ⟨⟨u, hu⟩, hZsub, hZpair, hZmax⟩ hZR
    obtain ⟨huQ, huτ⟩ := mem_sdiff.1 (hZsub hu)
    by_cases huR : u ∈ R
    · refine absurd (Finset.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩) hZR
      · obtain ⟨hzQ, hzτ⟩ := mem_sdiff.1 (hZsub hz)
        exact hB u huR z hzQ hzτ (hZpair u hu z hz)
      · exact hZmax u hu z (mem_sdiff.2 (hRsub z hz)) (hA u huR z hz)
    · obtain ⟨hu2, hone⟩ := hC u huQ huτ huR
      refine ⟨u, hu2, Finset.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
      · obtain ⟨hzQ, hzτ⟩ := mem_sdiff.1 (hZsub hz)
        exact mem_singleton.2 (hone z hzQ hzτ (hZpair u hu z hz))
      · rw [mem_singleton.1 hz]
        exact hu
  -- Corollary: `Q⁺` is the chord with head `[lo, hi]`
  rintro ⟨⟨g1, g2⟩, hg⟩
  obtain ⟨V, hVo, -, -, hevV, hodV⟩ := pkCh_mkHead hN hE' hPo (a := lo)
      (b := hi) hlo1 (by omega) hhiω hlo2 hhi2
  have hVR : evenSide N V = R := Finset.ext fun x => by rw [hevV, hmR]
  have hodW : ∀ x, x ∈ oddSide N Q ↔ x ∈ Icc 1 N ∧ c + 1 ≤ cycPos N (headStart P) x + 1 ∧
      cycPos N (headStart P) x + 1 ≤ c + headLen N Q := by
    intro x
    constructor
    · intro h
      have hx : x ∈ Icc 1 N := ((pkCh_headpos hN hE' hQo).1 h).1
      have := (hmemP x hx).1 h
      exact ⟨hx, by omega, by omega⟩
    · rintro ⟨hx, h1, h2⟩
      exact (hmemP x hx).2 ⟨by omega, by omega⟩
  have hevW : ∀ x, x ∈ evenSide N Q ↔ x ∈ Icc 1 N ∧ ¬ (c + 1 ≤ cycPos N (headStart P) x + 1 ∧
      cycPos N (headStart P) x + 1 ≤ c + headLen N Q) := by
    intro x
    change x ∈ Icc 1 N \ oddSide N Q ↔ _
    rw [mem_sdiff, hodW]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h => h2 ⟨h1, h⟩⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h => h2 h.2⟩
  have hEE : innerEE N S Q ⊆ innerEE N S V := by
    rintro ⟨x, y⟩ h
    obtain ⟨hM, hx, hy⟩ := pkCh_mem_innerEE.1 h
    obtain ⟨hm, hx2, hy2⟩ := pkCh_mem_Mee.1 hM
    dsimp only at hx hy hx2 hy2
    obtain ⟨hxI, hxW⟩ := (hevW x).1 hx
    obtain ⟨hyI, hyW⟩ := (hevW y).1 hy
    have hd := mem_diagonals.1 (pkCh_mem_missing.1 hm).1
    dsimp only at hd
    have mx := pkCh_pos_mod hE' hs hs2 hxI
    have my := pkCh_pos_mod hE' hs hs2 hyI
    have hne : cycPos N (headStart P) x + 1 ≠ cycPos N (headStart P) y + 1 := fun h => by
      have := pkCo_cycPos_inj hs hxI hyI (by omega)
      omega
    have nC := pkCh_notCl hs hxI hyI hm
    rw [pkCh_phi_eq hs, pkCh_phi_eq hs] at nC
    have lx := pkCo_cycPos_lt hN1 (headStart P) x
    have ly := pkCo_cycPos_lt hN1 (headStart P) y
    have r1 := T3 _ _ (mem_Icc.2 ⟨by omega, by omega⟩) (mem_Icc.2 ⟨by omega, by omega⟩)
        (by omega) (by omega)
      hxW hyW hne nC
    have r2 := T3 _ _ (mem_Icc.2 ⟨by omega, by omega⟩) (mem_Icc.2 ⟨by omega, by omega⟩)
        (by omega) (by omega)
      hyW hxW (Ne.symm hne) (fun h => nC (pkCh_Cl_symm _ _ h))
    exact pkCh_mem_innerEE.2 ⟨hM, (hevV x).2 ⟨hxI, r1⟩, (hevV y).2 ⟨hyI, r2⟩⟩
  have hsubWV : oddSide N Q ⊆ oddSide N V := fun x h => by
    obtain ⟨hx, h1, h2⟩ := (hodW x).1 h
    exact (hodV x).2 ⟨hx, by omega, by omega⟩
  have hsubVP : oddSide N V ⊆ oddSide N P := fun x h => by
    obtain ⟨hx, h1, h2⟩ := (hodV x).1 h
    exact (pkCh_headpos hN hE' hPo).2 ⟨hx, by omega⟩
  have hevVW : evenSide N V ⊆ evenSide N Q := fun x h => by
    obtain ⟨hx, h1⟩ := (hevV x).1 h
    exact (hevW x).2 ⟨hx, by omega⟩
  have hOOV : innerOO N S V = innerOO N S P := by
    apply Finset.Subset.antisymm
    · intro p h
      obtain ⟨hM, h1, h2⟩ := pkCh_mem_innerOO.1 h
      exact pkCh_mem_innerOO.2 ⟨hM, hsubVP h1, hsubVP h2⟩
    · intro p h
      rw [← hoo] at h
      obtain ⟨hM, h1, h2⟩ := pkCh_mem_innerOO.1 h
      exact pkCh_mem_innerOO.2 ⟨hM, hsubWV h1, hsubWV h2⟩
  have hEEeq : innerEE N S V = innerEE N S Q := by
    apply Finset.Subset.antisymm
    · intro p h
      obtain ⟨hM, h1, h2⟩ := pkCh_mem_innerEE.1 h
      exact pkCh_mem_innerEE.2 ⟨hM, hevVW h1, hevVW h2⟩
    · exact hEE
  have hVc : Disjoint (minRect N V) (missing N S) := by
    refine disjoint_left.2 fun p hp hpm => ?_
    obtain ⟨e, he, o, ho, rfl⟩ := pkCh_mem_minRect.1 hp
    obtain ⟨heV, he2⟩ := pkCh_mem_evens.1 he
    obtain ⟨hoV, ho2⟩ := pkCh_mem_odds.1 ho
    obtain ⟨heI, e1, e2⟩ := (hodV e).1 heV
    obtain ⟨hoI, o1⟩ := (hevV o).1 hoV
    have me := pkCh_pos_mod hE' hs hs2 heI
    have mo := pkCh_pos_mod hE' hs hs2 hoI
    have le := pkCo_cycPos_lt hN1 (headStart P) e
    have lo' := pkCo_cycPos_lt hN1 (headStart P) o
    apply pkCh_notCl_mm hs heI hoI hpm
    rw [pkCh_phi_eq hs, pkCh_phi_eq hs]
    by_cases hin : c + 1 ≤ cycPos N (headStart P) e + 1 ∧ cycPos N (headStart P) e + 1 ≤
        c + headLen N Q
    · exact Hmr _ _ (mem_Icc.2 ⟨by omega, by omega⟩) (mem_Icc.2 ⟨by omega, by omega⟩)
        (by omega) (by omega)
        hin.1 hin.2 (by omega)
    · exact T2 _ _ (mem_Icc.2 ⟨by omega, by omega⟩) (mem_Icc.2 ⟨by omega, by omega⟩)
        (by omega) (by omega)
        e1 e2 hin o1
  have hVp : V ∈ poleChords N S := by
    refine pkCh_mem_pole.2 ⟨hVo, hVc, ⟨(g1, g2), hEE hg⟩, ?_⟩
    rw [hOOV]
    exact hPoo
  have hVcl : V ∈ cleanChords N S := mem_filter.2 ⟨hVo, hVc⟩
  refine ⟨V, hVp, hVR, hOOV, pkCh_class_of hN hE' hVcl hQ hEEeq (hOOV.trans hoo.symm),
    (ssubset_iff_of_subset hsubWV).2 ?_, hsubVP⟩
  rcases hside with h | h
  · obtain ⟨hI, hp⟩ := hψ lo hlo1 (by omega)
    exact ⟨_, (hodV _).2 ⟨hI, by omega, by omega⟩, fun h' => by
      have := ((hodW _).1 h').2.1
      omega⟩
  · obtain ⟨hI, hp⟩ := hψ hi (by omega) (by omega)
    exact ⟨_, (hodV _).2 ⟨hI, by omega, by omega⟩, fun h' => by
      have := ((hodW _).1 h').2.2
      omega⟩

/-! ### Absorption -/

-- registry: C-F7S2
/-- **Absorption**: for a candidate set `S` at even `N ≥ 6` and an innermost chord `P*`, every
residue chord `Q` (`Q ∈ 𝒫₁`) with `o_in(Q) = o_in(P*)` and `A_Q ⊆ A*` is in the flank class `K*`. -/
theorem Combinatorics.Polygons.residue_chord_joins_innermost_flank_class {N : ℕ} (hN : 6 ≤ N)
    (hE : Even N) {S : Finset (ℕ × ℕ)} (hF : IsCandidateSet N S) {P : ℕ × ℕ}
    (hP : IsInnermostChord N S P) {Q : ℕ × ℕ} (hQ : Q ∈ poleChords N S)
    (hsub : oddSide N Q ⊆ oddSide N P) (hoo : innerOO N S Q = innerOO N S P) :
    Q ∈ hitClass N S P :=
  pkCh_noB1 hN (Nat.even_iff.1 hE) ((isCandidateSet_iff_inFpi hE).1 hF) hP _ Q hQ rfl hsub hoo

/-! ### The lift -/

-- registry: C-B4RC
/-- **The lift**: for even `N ≥ 6`, a set `S` of pairs, an on-shell chord `P` (`P ∈ 𝒫₀`) and an odd
chord `P′` with `A_P ⊆ A_{P′}` and `o_in(P′) ⊆ o_in(P)`: if `Θ` is a free even separator of
`A_P` that is spread, then `Θ′ := Θ ∪ evens(A_{P′} ∖ A_P)` is a free even separator of `A_{P′}`
that is spread. The paper's general form. The name, kept for the registry key, is that of the
special case of `P′` with a linked even-ended side and `P` in its flank class. Proved from the
library's `pkCh_lift_explicit`, with `Spread` read as `IsSpread` (`isSpread_iff_spread`). -/
theorem Combinatorics.Polygons.spread_separator_passes_to_innermost_chord {N : ℕ} (hN : 6 ≤ N)
    (hE : Even N) {S : Finset (ℕ × ℕ)} {P Ps : ℕ × ℕ} (hP : P ∈ cleanChords N S)
    (hPs : Ps ∈ oddDiagonals N) (hsub : oddSide N P ⊆ oddSide N Ps)
    (hoo : innerOO N S Ps ⊆ innerOO N S P) {Θ : Finset ℕ}
    (hΘ : Θ ∈ admSeps N (headStart P) (headLen N P) 0) (hΘe : ∀ θ ∈ Θ, θ % 2 = 0)
    (hΘd : Disjoint (sepIn N (headStart P) (headLen N P) Θ) (missing N S))
    (hsp : IsSpread N S P Θ) :
    Θ ∪ evens (oddSide N Ps \ oddSide N P) ∈ admSeps N (headStart Ps) (headLen N Ps) 0 ∧
      (∀ θ ∈ Θ ∪ evens (oddSide N Ps \ oddSide N P), θ % 2 = 0) ∧
      Disjoint (sepIn N (headStart Ps) (headLen N Ps) (Θ ∪ evens (oddSide N Ps \ oddSide N P)))
        (missing N S) ∧
      IsSpread N S Ps (Θ ∪ evens (oddSide N Ps \ oddSide N P)) := by
  have hPo : P ∈ oddDiagonals N := (mem_filter.1 hP).1
  obtain ⟨h1, h2, h3, h4⟩ := pkCh_lift_explicit hN (Nat.even_iff.1 hE) hP hPs hsub hoo hΘ hΘe hΘd
    ((isSpread_iff_spread hN hE hPo (legs_of_mem_admSeps hE hPo hΘ)).1 hsp)
  exact ⟨h1, h2, h3, (isSpread_iff_spread hN hE hPs (legs_of_mem_admSeps hE hPs h1)).2 h4⟩

/-! ### (Bot) -/

-- registry: C-QYX9
/-- For a candidate set `S` at even `N ≥ 6` and an innermost chord `P*`, the flank class `K*` of
`P*` has a member `b` whose odd-ended side `A_b` is linked. -/
theorem Combinatorics.Polygons.innermost_class_has_linked_member {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    {S : Finset (ℕ × ℕ)} (hF : IsCandidateSet N S) {P : ℕ × ℕ} (hP : IsInnermostChord N S P) :
    ∃ b ∈ hitClass N S P, NoFreeSep N S (headStart b) (headLen N b) 0 :=
  have hF := (isCandidateSet_iff_inFpi hE).1 hF
  bot_of_evenTop hN hE hF hP (evenTop hN hE hF hP)

-- registry: C-EX2M
/-- **A residue chord with both sides linked**: for even `N ≥ 6` and a set `S` of pairs, (a) a
residue chord `P` whose two sides are linked is the only member of its flank class; (b) for a
candidate set and an innermost chord `P*`, the odd-ended side `A_{P*}` is linked iff the flank class
of `P*` is `{P*}`. -/
theorem Combinatorics.Polygons.both_sides_linked_alone_in_flank_class {N : ℕ} (hN : 6 ≤ N)
    (hE : Even N) {S : Finset (ℕ × ℕ)} :
    (∀ P ∈ poleChords N S, NoFreeSep N S (headStart P) (headLen N P) 0 →
      NoFreeSep N S (tailStart P) (tailLen N P) 1 → hitClass N S P = {P}) ∧
    (IsCandidateSet N S → ∀ P, IsInnermostChord N S P →
      (NoFreeSep N S (headStart P) (headLen N P) 0 ↔ hitClass N S P = {P})) := by
  have one : ∀ P ∈ poleChords N S, NoFreeSep N S (headStart P) (headLen N P) 0 →
      NoFreeSep N S (tailStart P) (tailLen N P) 1 → hitClass N S P = {P} := by
    intro P hP hA hB
    have hPg : P ∈ goodTail N S := pkCh_mem_goodTail.2 ⟨hP, hB⟩
    obtain ⟨⟨hPK, htop⟩, hbot, -⟩ := flank_class_top_and_bottom hN hE hPg
    have hlow := (hbot P hPK hA).1
    have hodd : ∀ Q ∈ hitClass N S P, Q ∈ oddDiagonals N := fun Q hQ =>
      (mem_filter.1 (mem_filter.1 (pkCh_mem_hitClass.1 hQ).1).1).1
    ext Q
    rw [mem_singleton]
    constructor
    · intro hQ
      exact (odd_chord_sides hE).2 Q (hodd Q hQ) P (hodd P hPK)
        (subset_antisymm (htop Q hQ) (hlow Q hQ))
    · rintro rfl
      exact hPK
  refine ⟨one, fun hF P hP => ⟨fun hA => ?_, fun hK => ?_⟩⟩
  · have hPg := (pkCh_minChord_iff.1 hP).1
    exact one P (pkCh_mem_goodTail.1 hPg).1 hA (pkCh_mem_goodTail.1 hPg).2
  · obtain ⟨b, hb, hbl⟩ := innermost_class_has_linked_member hN hE hF hP
    rw [hK, mem_singleton] at hb
    rw [← hb]
    exact hbl

/-! ## The class residue: rational functions on `L_S`, its hypotheses and the extreme term

The class residue is about rational functions restricted to `L_S` and their poles along
`H = L_S ∩ {x = 0}`; the library proves the same results for numerators, pointwise. This
section states them in the paper's language: the predicates `HasNoPoleAlong` and
`RestrictsToZeroAlong` (with the non-vacuity facts `PaperTests.not_hasNoPoleAlong_inv`,
`PaperTests.not_restrictsToZeroAlong_one` and `PaperTests.hasNoPoleAlong_can_fail`, the constructors
`hasNoPoleAlong_of_eq`, `restrictsToZeroAlong_of_eq`, and the well-definedness
`PaperTests.restrictsToZeroAlong_numerator`, and closure lemmas on a linear subspace: `RatZeroOn`
under sums and products, `HasNoPoleAlong` and `RestrictsToZeroAlong` under sums and products,
constants), the amplitude avoiding a set of chords (`ampAvoiding`,
`nlsmAvoiding`, with the numerator lemma `nlsmAvoiding_numerator_hom`), the hypotheses of the
residue theorem (`FlankClassPoleHypotheses`, with an example of the paper as an instance,
`PaperTests.example_four_six_residue_regime`, in which the extreme terms do not vanish on `H`,
`PaperTests.example_four_six_extreme_terms_nonvanishing`), the children's parts `a_Q`, `b_Q`
(`avoidingB`, `avoidingA`), the strip factor `φ` (`stripFactor`), and the extreme term
(`only_extreme_term_survives`). -/

open MvPolynomial in
-- registry: C-DK78
/-- The paper's "the restriction of `f` to `V` has no pole along `H`" (its conventions on
rational functions; meant for `H ⊆ V`, as in every use): on `V`, `f` agrees with
`P / D` for polynomials `P`, `D` with `D` not identically zero on `H`. ("On `V`, `f = P / D`" is
`RatZeroOn V (f D − P)`.) -/
def NLSM.Amplitude.HasNoPoleAlong (V H : Set (ℕ × ℕ → ℚ)) (f : RF) : Prop :=
  ∃ P D : MvPolynomial (ℕ × ℕ) ℚ, RatZeroOn V (f * algebraMap _ RF D - algebraMap _ RF P) ∧
    ∃ w ∈ H, eval w D ≠ 0

open MvPolynomial in
-- registry: C-DK78
/-- The paper's "`f|_H = 0`" for the restriction of `f` to `V`, which has no pole along `H`: as
`HasNoPoleAlong`, with a numerator `P` that vanishes on `H`. -/
def NLSM.Amplitude.RestrictsToZeroAlong (V H : Set (ℕ × ℕ → ℚ)) (f : RF) : Prop :=
  ∃ P D : MvPolynomial (ℕ × ℕ) ℚ, RatZeroOn V (f * algebraMap _ RF D - algebraMap _ RF P) ∧
    (∃ w ∈ H, eval w D ≠ 0) ∧ ∀ x ∈ H, eval x P = 0

open MvPolynomial in
/-- A rational function equal to `P / D` in `RF`, with `D` not identically zero on `H`, has no pole
along `H` (`0 ∈ V`). -/
theorem hasNoPoleAlong_of_eq {V H : Set (ℕ × ℕ → ℚ)} (hV : (fun _ => (0 : ℚ)) ∈ V) {f : RF}
    {P D : MvPolynomial (ℕ × ℕ) ℚ} (hf : f * algebraMap _ RF D = algebraMap _ RF P)
    (hD : ∃ w ∈ H, eval w D ≠ 0) : HasNoPoleAlong V H f :=
  ⟨P, D, ⟨0, 1, by rw [hf, sub_self, zero_mul, map_zero], ⟨_, hV, by simp⟩, by simp⟩, hD⟩

open MvPolynomial in
/-- A rational function equal to `P / D` in `RF`, with `D` not identically zero on `H` and `P`
vanishing on `H`, restricts to zero along `H` (`0 ∈ V`). -/
theorem restrictsToZeroAlong_of_eq {V H : Set (ℕ × ℕ → ℚ)} (hV : (fun _ => (0 : ℚ)) ∈ V) {f : RF}
    {P D : MvPolynomial (ℕ × ℕ) ℚ} (hf : f * algebraMap _ RF D = algebraMap _ RF P)
    (hD : ∃ w ∈ H, eval w D ≠ 0) (hP : ∀ x ∈ H, eval x P = 0) : RestrictsToZeroAlong V H f := by
  refine ⟨P, D, ⟨0, 1, by rw [hf, sub_self, zero_mul, map_zero], ⟨_, hV, by simp⟩, by simp⟩, hD, hP⟩

/-- A function that restricts to zero along `H` has no pole along `H`. -/
theorem NLSM.Amplitude.RestrictsToZeroAlong.hasNoPoleAlong {V H : Set (ℕ × ℕ → ℚ)} {f : RF}
    (h : RestrictsToZeroAlong V H f) : HasNoPoleAlong V H f :=
  let ⟨P, D, h1, h2, _⟩ := h
  ⟨P, D, h1, h2⟩

open MvPolynomial in
/-- Two polynomials each non-zero somewhere on a linear subspace `V` are both non-zero at one
point of `V`. -/
theorem exists_eval_mul_ne_zero {V : Set (ℕ × ℕ → ℚ)} (hV : pkRSub V)
    {D₁ D₂ : MvPolynomial (ℕ × ℕ) ℚ} (h₁ : ∃ w ∈ V, eval w D₁ ≠ 0)
    (h₂ : ∃ w ∈ V, eval w D₂ ≠ 0) : ∃ w ∈ V, eval w (D₁ * D₂) ≠ 0 := by
  obtain ⟨w, hw, hall⟩ := pkR_avoid hV (fun i : Bool => if i then D₁ else D₂) univ
    (fun i _ => by cases i <;> simpa)
  refine ⟨w, hw, ?_⟩
  rw [map_mul]
  exact mul_ne_zero (by simpa using hall true (mem_univ _)) (by simpa using hall false (mem_univ _))

open MvPolynomial in
/-- `RatZeroOn` on a linear subspace is closed under sums. -/
theorem ratZeroOn_add {V : Set (ℕ × ℕ → ℚ)} (hV : pkRSub V) {f g : RF} (hf : RatZeroOn V f)
    (hg : RatZeroOn V g) : RatZeroOn V (f + g) := by
  obtain ⟨A₁, B₁, e₁, w₁, h₁⟩ := hf
  obtain ⟨A₂, B₂, e₂, w₂, h₂⟩ := hg
  refine ⟨A₁ * B₂ + A₂ * B₁, B₁ * B₂, ?_, exists_eval_mul_ne_zero hV w₁ w₂, fun x hx => ?_⟩
  · rw [map_mul, add_mul, map_add, map_mul, map_mul, ← e₁, ← e₂]
    ring
  · rw [map_add, map_mul, map_mul, h₁ x hx, h₂ x hx]
    ring

open MvPolynomial in
/-- `RatZeroOn` on a linear subspace is closed under finite sums. -/
theorem ratZeroOn_sum {ι : Type*} {V : Set (ℕ × ℕ → ℚ)} (hV : pkRSub V) (s : Finset ι)
    {f : ι → RF} (h : ∀ i ∈ s, RatZeroOn V (f i)) : RatZeroOn V (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨0, 1, by simp, ⟨_, hV.1, by simp⟩, fun x _ => by simp⟩
  | insert i s hi ih =>
    rw [sum_insert hi]
    exact ratZeroOn_add hV (h i (mem_insert_self i s))
      (ih fun j hj => h j (mem_insert_of_mem hj))

open MvPolynomial in
/-- A rational function that restricts to zero on `V` still does after multiplication by one of
the form `P / D`, `D` not identically zero on `V` (a linear subspace). -/
theorem ratZeroOn_mul_of_eq {V : Set (ℕ × ℕ → ℚ)} (hV : pkRSub V) {f g : RF}
    (hf : RatZeroOn V f) {P D : MvPolynomial (ℕ × ℕ) ℚ} (hg : g * algebraMap _ RF D =
      algebraMap _ RF P) (hD : ∃ w ∈ V, eval w D ≠ 0) : RatZeroOn V (g * f) := by
  obtain ⟨A, B, e, w, h⟩ := hf
  refine ⟨P * A, D * B, ?_, exists_eval_mul_ne_zero hV hD w, fun x hx => ?_⟩
  · rw [map_mul, map_mul, ← hg, ← e]
    ring
  · rw [map_mul, h x hx, mul_zero]

open MvPolynomial in
/-- `RatZeroOn` on a linear subspace is closed under products. -/
theorem ratZeroOn_mul {V : Set (ℕ × ℕ → ℚ)} (hV : pkRSub V) {f g : RF} (hf : RatZeroOn V f)
    (hg : RatZeroOn V g) : RatZeroOn V (f * g) := by
  obtain ⟨A₁, B₁, e₁, w₁, h₁⟩ := hf
  obtain ⟨A₂, B₂, e₂, w₂, h₂⟩ := hg
  refine ⟨A₁ * A₂, B₁ * B₂, ?_, exists_eval_mul_ne_zero hV w₁ w₂, fun x hx => ?_⟩
  · rw [map_mul, map_mul, ← e₁, ← e₂]
    ring
  · rw [map_mul, h₁ x hx, zero_mul]

open MvPolynomial in
/-- Sum of two representations. -/
theorem ratZeroOn_rep_add {V : Set (ℕ × ℕ → ℚ)} (hV : pkRSub V) {f g : RF}
    {P₁ D₁ P₂ D₂ : MvPolynomial (ℕ × ℕ) ℚ}
    (h₁ : RatZeroOn V (f * algebraMap _ RF D₁ - algebraMap _ RF P₁))
    (h₂ : RatZeroOn V (g * algebraMap _ RF D₂ - algebraMap _ RF P₂)) :
    RatZeroOn V ((f + g) * algebraMap _ RF (D₁ * D₂) - algebraMap _ RF (P₁ * D₂ + P₂ * D₁)) := by
  have e : (f + g) * algebraMap _ RF (D₁ * D₂) - algebraMap _ RF (P₁ * D₂ + P₂ * D₁) =
      algebraMap _ RF D₂ * (f * algebraMap _ RF D₁ - algebraMap _ RF P₁) +
        algebraMap _ RF D₁ * (g * algebraMap _ RF D₂ - algebraMap _ RF P₂) := by
    simp only [map_mul, map_add]
    ring
  rw [e]
  exact ratZeroOn_add hV (ratZeroOn_mul_left h₁ _) (ratZeroOn_mul_left h₂ _)

open MvPolynomial in
/-- Product of two representations. -/
theorem ratZeroOn_rep_mul {V : Set (ℕ × ℕ → ℚ)} (hV : pkRSub V) {f g : RF}
    {P₁ D₁ P₂ D₂ : MvPolynomial (ℕ × ℕ) ℚ}
    (h₁ : RatZeroOn V (f * algebraMap _ RF D₁ - algebraMap _ RF P₁))
    (h₂ : RatZeroOn V (g * algebraMap _ RF D₂ - algebraMap _ RF P₂)) :
    RatZeroOn V ((f * g) * algebraMap _ RF (D₁ * D₂) - algebraMap _ RF (P₁ * P₂)) := by
  have e : (f * g) * algebraMap _ RF (D₁ * D₂) - algebraMap _ RF (P₁ * P₂) =
      (f * algebraMap _ RF D₁ - algebraMap _ RF P₁) *
          (g * algebraMap _ RF D₂ - algebraMap _ RF P₂) +
        algebraMap _ RF P₂ * (f * algebraMap _ RF D₁ - algebraMap _ RF P₁) +
        algebraMap _ RF P₁ * (g * algebraMap _ RF D₂ - algebraMap _ RF P₂) := by
    simp only [map_mul]
    ring
  rw [e]
  exact ratZeroOn_add hV (ratZeroOn_add hV (ratZeroOn_mul hV h₁ h₂) (ratZeroOn_mul_left h₁ _))
    (ratZeroOn_mul_left h₂ _)

/-- Having no pole along `H` is closed under sums (`V`, `H` linear subspaces). -/
theorem NLSM.Amplitude.HasNoPoleAlong.add {V H : Set (ℕ × ℕ → ℚ)} (hV : pkRSub V) (hH : pkRSub H)
    {f g : RF} (hf : HasNoPoleAlong V H f) (hg : HasNoPoleAlong V H g) :
    HasNoPoleAlong V H (f + g) :=
  let ⟨_, _, h₁, w₁⟩ := hf
  let ⟨_, _, h₂, w₂⟩ := hg
  ⟨_, _, ratZeroOn_rep_add hV h₁ h₂, exists_eval_mul_ne_zero hH w₁ w₂⟩

/-- Having no pole along `H` is closed under products (`V`, `H` linear subspaces). -/
theorem NLSM.Amplitude.HasNoPoleAlong.mul {V H : Set (ℕ × ℕ → ℚ)} (hV : pkRSub V) (hH : pkRSub H)
    {f g : RF} (hf : HasNoPoleAlong V H f) (hg : HasNoPoleAlong V H g) :
    HasNoPoleAlong V H (f * g) :=
  let ⟨_, _, h₁, w₁⟩ := hf
  let ⟨_, _, h₂, w₂⟩ := hg
  ⟨_, _, ratZeroOn_rep_mul hV h₁ h₂, exists_eval_mul_ne_zero hH w₁ w₂⟩

open MvPolynomial in
/-- "`f|_H = 0`" is closed under sums. -/
theorem NLSM.Amplitude.RestrictsToZeroAlong.add {V H : Set (ℕ × ℕ → ℚ)} (hV : pkRSub V)
    (hH : pkRSub H) {f g : RF} (hf : RestrictsToZeroAlong V H f) (hg : RestrictsToZeroAlong V H g) :
    RestrictsToZeroAlong V H (f + g) :=
  let ⟨_, _, h₁, w₁, z₁⟩ := hf
  let ⟨_, _, h₂, w₂, z₂⟩ := hg
  ⟨_, _, ratZeroOn_rep_add hV h₁ h₂, exists_eval_mul_ne_zero hH w₁ w₂, fun x hx => by
    rw [map_add, map_mul, map_mul, z₁ x hx, z₂ x hx]
    ring⟩

open MvPolynomial in
/-- "`f|_H = 0`" times a function with no pole along `H` restricts to zero. -/
theorem NLSM.Amplitude.RestrictsToZeroAlong.mul {V H : Set (ℕ × ℕ → ℚ)} (hV : pkRSub V)
    (hH : pkRSub H) {f g : RF} (hf : RestrictsToZeroAlong V H f) (hg : HasNoPoleAlong V H g) :
    RestrictsToZeroAlong V H (f * g) :=
  let ⟨_, _, h₁, w₁, z₁⟩ := hf
  let ⟨_, _, h₂, w₂⟩ := hg
  ⟨_, _, ratZeroOn_rep_mul hV h₁ h₂, exists_eval_mul_ne_zero hH w₁ w₂, fun x hx => by
    rw [map_mul, z₁ x hx, zero_mul]⟩

open MvPolynomial in
/-- A function that restricts to zero on all of `V` restricts to zero along `H` (`H` non-empty). -/
theorem restrictsToZeroAlong_of_ratZeroOn {V H : Set (ℕ × ℕ → ℚ)} (hH : ∃ w, w ∈ H) {f : RF}
    (hf : RatZeroOn V f) : RestrictsToZeroAlong V H f := by
  obtain ⟨w, hw⟩ := hH
  refine ⟨0, 1, ?_, ⟨w, hw, by simp⟩, fun x _ => by simp⟩
  rwa [map_one, mul_one, map_zero, sub_zero]

open MvPolynomial in
/-- "`f|_H = 0`" is closed under finite sums. -/
theorem NLSM.Amplitude.RestrictsToZeroAlong.sum {V H : Set (ℕ × ℕ → ℚ)} (hV : pkRSub V)
    (hH : pkRSub H) {ι : Type*} (s : Finset ι) {f : ι → RF}
    (h : ∀ i ∈ s, RestrictsToZeroAlong V H (f i)) :
    RestrictsToZeroAlong V H (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact restrictsToZeroAlong_of_ratZeroOn ⟨_, hH.1⟩
      ⟨0, 1, by simp, ⟨_, hV.1, by simp⟩, fun _ _ => by simp⟩
  | insert i s hi ih =>
    rw [sum_insert hi]
    exact (h i (mem_insert_self i s)).add hV hH (ih fun j hj => h j (mem_insert_of_mem hj))

open MvPolynomial in
/-- Two functions with the same restriction to `V`: if one restricts to zero along `H`, so does the
other. -/
theorem NLSM.Amplitude.RestrictsToZeroAlong.congr {V H : Set (ℕ × ℕ → ℚ)} (hV : pkRSub V) {f g : RF}
    (hfg : RatZeroOn V (f - g)) (hg : RestrictsToZeroAlong V H g) :
    RestrictsToZeroAlong V H f := by
  obtain ⟨P, D, h, w, z⟩ := hg
  refine ⟨P, D, ?_, w, z⟩
  have e : f * algebraMap _ RF D - algebraMap _ RF P =
      algebraMap _ RF D * (f - g) + (g * algebraMap _ RF D - algebraMap _ RF P) := by ring
  rw [e]
  exact ratZeroOn_add hV (ratZeroOn_mul_left hfg _) h

open MvPolynomial in
/-- A constant has no pole along `H` (`H` non-empty). -/
theorem hasNoPoleAlong_const {V H : Set (ℕ × ℕ → ℚ)} (hV : pkRSub V) (hH : ∃ w, w ∈ H) (c : ℚ) :
    HasNoPoleAlong V H (c : RF) := by
  obtain ⟨w, hw⟩ := hH
  refine ⟨C c, 1, ?_, ⟨w, hw, by simp⟩⟩
  rw [map_one, mul_one, show algebraMap (MvPolynomial (ℕ × ℕ) ℚ) RF (C c) = (c : RF) from
    eq_ratCast ((algebraMap _ RF).comp C) c, sub_self]
  exact ⟨0, 1, by simp, ⟨_, hV.1, by simp⟩, fun _ _ => by simp⟩

/-! ## The amplitude avoiding a set of chords -/

section Avoiding

variable {F : Type*} [Field F]

-- registry: C-XKD2
/-- `A^{¬K}_n`: the sum over the triangulations of the `n`-gon that contain no chord of `K`. -/
noncomputable def ampAvoiding (n : ℕ) (K : Finset (ℕ × ℕ)) (X : ℕ × ℕ → F) : F :=
  ∑ T ∈ (triangulations n).filter (fun T => Disjoint T K), ∏ d ∈ T, (X d)⁻¹

-- registry: C-DK78
/-- `N^{¬K}_n`: the coefficient of `δ^{−(n−2)}` in `A^{¬K}_n(X + δ v₀)`; for `K = ∅` it is
`NLSM_n` (`nlsmAvoiding_empty`). -/
noncomputable def NLSM.Amplitude.nlsmAvoiding (n : ℕ) (K : Finset (ℕ × ℕ)) (X : ℕ × ℕ → F) : F :=
  (ampAvoiding n K (shifted X)).coeff ((n : ℤ) - 2)

theorem nlsmAvoiding_empty (n : ℕ) (X : ℕ × ℕ → F) : nlsmAvoiding n ∅ X = NLSM n X := by
  unfold nlsmAvoiding ampAvoiding NLSM shiftCoeff amp
  simp only [disjoint_empty_right, filter_true_of_mem (fun _ _ => trivial)]

end Avoiding

/-- The coefficients of `A^{¬K}_n(X + δ v₀)` as power-series coefficients of the sum over the
triangulations avoiding `K`. -/
theorem ampAvoiding_shifted {F : Type*} [Field F] (n : ℕ) (K : Finset (ℕ × ℕ)) (x : ℕ × ℕ → F) :
    ampAvoiding n K (shifted x) = HahnSeries.ofPowerSeries ℤ F
      (∑ T ∈ (triangulations n).filter (fun T => Disjoint T K), ∏ d ∈ T, phi x d) := by
  unfold ampAvoiding
  simp only [inv_shifted, ← map_prod, ← map_sum]

-- registry: C-XKD2
/-- **Numerator lemma for every order**: under a ring homomorphism into a field that keeps the
odd diagonals outside `K` non-zero, the library's order-`m` numerator `pkRBAP` maps to the
coefficient of `δ^{−m}` in `A^{¬K}_n(X + δ v₀)` times the product of those diagonals. -/
theorem NLSM.Amplitude.ampAvoiding_coeff_numerator_hom {F : Type*} [Field F]
    (f : MvPolynomial (ℕ × ℕ) ℚ →+* F) (n m : ℕ) (K : Finset (ℕ × ℕ))
    (hX : ∀ d ∈ oddDiagonals n \ K, f (MvPolynomial.X d) ≠ 0) :
    f (pkRBAP ℚ n m K) =
      (ampAvoiding n K (shifted (fun d => f (MvPolynomial.X d)))).coeff (m : ℤ) *
        ∏ d ∈ oddDiagonals n \ K, f (MvPolynomial.X d) := by
  set x : ℕ × ℕ → F := fun d => f (MvPolynomial.X d) with hx
  have hco : (ampAvoiding n K (shifted x)).coeff (m : ℤ) = PowerSeries.coeff m
      (∑ T ∈ (triangulations n).filter (fun T => Disjoint T K), ∏ d ∈ T, phi x d) := by
    rw [ampAvoiding_shifted, HahnSeries.ofPowerSeries_apply_coeff]
  rw [hco, pkRBAP, ← PowerSeries.coeff_map, ← PowerSeries.coeff_mul_C]
  refine congrArg _ ?_
  rw [map_sum, sum_mul]
  refine sum_congr rfl fun T hT => ?_
  obtain ⟨hT, hTK⟩ := mem_filter.1 hT
  have hTs : T ⊆ diagonals n := (mem_triangulations.1 hT).1
  have hsplit : ∏ d ∈ T, phi x d = (∏ d ∈ T.filter (fun d => shiftSign d ≠ 0),
      shiftSeries (shiftSign d) (x d)) *
        PowerSeries.C (∏ d ∈ T.filter (fun d => shiftSign d = 0), (x d)⁻¹) := by
    rw [← prod_filter_mul_prod_filter_not T (fun d => shiftSign d = 0), mul_comm, map_prod]
    congr 1
    · exact prod_congr rfl fun d hd => by
        unfold phi; rw [ite_eq_right_iff.2 fun h => absurd h (mem_filter.1 hd).2]
    · exact prod_congr rfl fun d hd => by
        unfold phi; rw [ite_eq_left_iff.2 fun h => absurd (mem_filter.1 hd).2 h]
  have hodd : T.filter (fun d => shiftSign d = 0) ⊆ oddDiagonals n \ K := fun d hd => by
    obtain ⟨hdT, hd0⟩ := mem_filter.1 hd
    exact mem_sdiff.2 ⟨(pkBr_shiftSign_eq_zero (hTs hdT)).1 hd0,
      fun hK => disjoint_left.1 hTK hdT hK⟩
  have hsc : (∏ d ∈ T.filter (fun d => shiftSign d = 0), (x d)⁻¹) *
      ∏ d ∈ oddDiagonals n \ K, x d = ∏ d ∈ (oddDiagonals n \ T) \ K, x d := by
    rw [← prod_sdiff hodd]
    have he : (oddDiagonals n \ K) \ T.filter (fun d => shiftSign d = 0) =
        (oddDiagonals n \ T) \ K := by
      ext d
      simp only [mem_sdiff, mem_filter]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨h1, fun h => h3 ⟨h, pkZ_i_odd_sign h1⟩⟩, h2⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨h1, h3⟩, fun h => h2 h.1⟩
    rw [he, ← mul_assoc, mul_comm _ (∏ d ∈ (oddDiagonals n \ T) \ K, x d), mul_assoc,
      ← prod_mul_distrib, prod_eq_one fun d hd => inv_mul_cancel₀ (hX d (hodd hd)), mul_one]
  have hsh : ∀ d, PowerSeries.map f (shiftSeriesP ℚ d) = shiftSeries (shiftSign d) (x d) := by
    intro d
    rw [shiftSeriesP, shiftSeries, map_mul, PowerSeries.map_X]
    refine congrArg _ ?_
    ext k
    simp [PowerSeries.coeff_map, hx]
  rw [hsplit, mul_assoc, ← map_mul, hsc, pkRBF, map_mul, PowerSeries.map_C, mul_comm, map_prod f]
  congr 1
  rw [map_prod]
  exact prod_congr rfl fun d _ => hsh d

/-- **Numerator lemma for `N^{¬K}`**: under a ring homomorphism into a field that keeps the odd
diagonals outside `K` non-zero, the library's numerator `pkRBNP` maps to `N^{¬K}_n` times the
product of those diagonals. -/
theorem nlsmAvoiding_numerator_hom {F : Type*} [Field F] (f : MvPolynomial (ℕ × ℕ) ℚ →+* F) {n : ℕ}
    (hn : 2 ≤ n) (K : Finset (ℕ × ℕ)) (hX : ∀ d ∈ oddDiagonals n \ K, f (MvPolynomial.X d) ≠ 0) :
    f (pkRBNP ℚ n K) =
      nlsmAvoiding n K (fun d => f (MvPolynomial.X d)) *
        ∏ d ∈ oddDiagonals n \ K, f (MvPolynomial.X d) := by
  have h := ampAvoiding_coeff_numerator_hom f n (n - 2) K hX
  rwa [show ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 by omega] at h

/-! ## The hypotheses of the residue theorem -/

-- registry: C-S49P
/-- The hypotheses of the residue theorem, for `S`, a set `K` of odd chords,
`x := X_P|_{L_S}` with `P ∈ K`, and chords `t`, `b`: `S` is a candidate set; (H1) no odd chord
vanishes identically on `L_S`; (H2) an odd chord `Q` is in `K` iff `X_Q|_{L_S} ∈ ℚ^× x`, and
`X_Q|_{L_S} = x` for every `Q ∈ K`; (H3) `K ⊆ 𝒫₁` and all members of `K` have the same missing flank
set; (H4) `t` is a top of `K` and `b` a bottom (`A_Q ⊆ A_t` and `A_b ⊆ A_Q` for all `Q ∈ K`). The
fields `odd` and `h1` follow from `h3` and from `candidate` (a candidate set is regular); they are
kept because the paper states them. -/
structure NLSM.Amplitude.FlankClassPoleHypotheses (N : ℕ) (S K : Finset (ℕ × ℕ))
    (P t b : ℕ × ℕ) : Prop where
  candidate : IsCandidateSet N S
  odd : K ⊆ oddDiagonals N
  mem : P ∈ K
  h1 : ∀ Q ∈ oddDiagonals N, ∃ X : ℕ × ℕ → ℚ, OnLocus N S X ∧ X Q ≠ 0
  h2 : ∀ Q ∈ oddDiagonals N,
    Q ∈ K ↔ ∃ c : ℚ, c ≠ 0 ∧ ∀ X : ℕ × ℕ → ℚ, OnLocus N S X → X Q = c * X P
  h2' : ∀ Q ∈ K, ∀ X : ℕ × ℕ → ℚ, OnLocus N S X → X Q = X P
  h3 : K ⊆ poleChords N S
  h3' : ∀ Q ∈ K, ∀ Q' ∈ K, hitSet N S Q = hitSet N S Q'
  top : t ∈ K ∧ ∀ Q ∈ K, oddSide N Q ⊆ oddSide N t
  bottom : b ∈ K ∧ ∀ Q ∈ K, oddSide N b ⊆ oddSide N Q

-- registry: C-S49P
/-- The residue hyperplane `H := L_S ∩ {x = 0}`, `x = X_P|_{L_S}`. -/
def NLSM.Amplitude.residueHyperplane (N : ℕ) (S : Finset (ℕ × ℕ)) (P : ℕ × ℕ) : Set (ℕ × ℕ → ℚ) :=
  {X | OnLocus N S X ∧ X P = 0}

-- registry: C-S49P
/-- The half-length `d := (|A_t| − |A_b|)/2` of the hypotheses of the residue theorem. -/
def NLSM.Amplitude.stripHalfLength (N : ℕ) (t b : ℕ × ℕ) : ℕ := (headLen N t - headLen N b) / 2

-- registry: C-S49P
/-- The hypotheses' `a_t`: `NLSM_{|B_t|+1}` of the sub-polygon bounding `B_t` and closed by the
chord `t` (the B-child of `t`), as a function of the parent planar variables: the child's vertex
`a` is the parent's vertex `a + s − 1` (mod `N`), `s` the first leg of `B_t`. -/
noncomputable def NLSM.Amplitude.childAmpB (N : ℕ) (t : ℕ × ℕ) : RF :=
  NLSM (tailLen N t + 1) (fun d => gen (relab N (tailStart t) d))

-- registry: C-S49P
/-- The hypotheses' `b_b`: `NLSM_{|A_b|+1}` of the sub-polygon bounding `A_b` and closed by the
chord `b` (the A-child of `b`), as a function of the parent planar variables. -/
noncomputable def NLSM.Amplitude.childAmpA (N : ℕ) (b : ℕ × ℕ) : RF :=
  NLSM (headLen N b + 1) (fun d => gen (relab N (headStart b) d))

/-- Under (H1)–(H4), `K` is the flank class `hitClass N S t` of its top (the form in which the
library states its results on the class residue). -/
theorem NLSM.Amplitude.FlankClassPoleHypotheses.eq_hitClass {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    {S K : Finset (ℕ × ℕ)} {P t b : ℕ × ℕ} (h : FlankClassPoleHypotheses N S K P t b) :
    K = hitClass N S t := by
  ext Q
  constructor
  · intro hQ
    exact pkCh_mem_hitClass.2 ⟨h.h3 hQ, h.h3' Q hQ t h.top.1⟩
  · intro hQ
    obtain ⟨hQp, hQh⟩ := pkCh_mem_hitClass.1 hQ
    have hQo : Q ∈ oddDiagonals N := (mem_filter.1 (mem_filter.1 hQp).1).1
    obtain ⟨c, hc, hX⟩ := ((lemma14_6 hN hE ((isCandidateSet_iff_inFpi hE).1 h.candidate)
      (h.h3 h.top.1) hQo).1).2 hQh
    refine (h.h2 Q hQo).2 ⟨c, hc, fun X hL => ?_⟩
    rw [hX X hL, h.h2' t h.top.1 X hL]

-- registry: C-S49P
/-- A remark derived from the hypotheses of the residue theorem: under (H1)–(H4), no odd chord
outside `K` vanishes identically on `H`. -/
theorem odd_chord_outside_class_nonvanishing_on_hyperplane {N : ℕ} {S K : Finset (ℕ × ℕ)}
    {P t b : ℕ × ℕ} (h : FlankClassPoleHypotheses N S K P t b) {Q : ℕ × ℕ}
    (hQ : Q ∈ oddDiagonals N) (hQK : Q ∉ K) : ∃ X ∈ residueHyperplane N S P, X Q ≠ 0 := by
  obtain ⟨X, hX, hXP, hXQ⟩ := pkR_d_offH (isRegularSet_iff_nondeg.1 h.candidate.2.1)
    (mem_filter.1 (h.odd h.mem)).1 (mem_filter.1 hQ).1 (fun hc => hQK ((h.h2 Q hQ).2 hc))
  exact ⟨X, ⟨hX, hXP⟩, hXQ⟩

-- registry: C-S49P
/-- The hypotheses hold for `K*`: for a candidate set `S` at even `N ≥ 6`, an innermost chord
`P*`, its flank class `K*` and a member `b` with `A_b` linked (what (Bot) provides), the hypotheses
(H1)–(H4) hold with `x = X_{P*}`, top `P*` and bottom `b` ((H1) as a candidate set is regular,
(H2) and (H3) by `proportional_odd_chords_share_missing_flank_set`, (H4) by
`flank_class_top_and_bottom`). -/
theorem flank_class_pole_hypotheses_innermost {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    {S : Finset (ℕ × ℕ)} (hF : IsCandidateSet N S) {P b : ℕ × ℕ} (hP : IsInnermostChord N S P)
    (hb : b ∈ hitClass N S P) (hbl : NoFreeSep N S (headStart b) (headLen N b) 0) :
    FlankClassPoleHypotheses N S (hitClass N S P) P P b := by
  have hFi := (isCandidateSet_iff_inFpi hE).1 hF
  have hPg := (pkCh_minChord_iff.1 hP).1
  have hPp := (pkCh_mem_goodTail.1 hPg).1
  obtain ⟨⟨hPK, htop⟩, hbot, -⟩ := flank_class_top_and_bottom hN hE hPg
  have hodd : ∀ Q ∈ hitClass N S P, Q ∈ oddDiagonals N := fun Q hQ =>
    (mem_filter.1 (mem_filter.1 (pkCh_mem_hitClass.1 hQ).1).1).1
  refine ⟨hF, hodd, hPK, fun Q hQ => hFi.2.1 Q (mem_filter.1 hQ).1, fun Q hQ => ?_,
    fun Q hQ X hX => ?_, fun Q hQ => (pkCh_mem_hitClass.1 hQ).1, fun Q hQ Q' hQ' => ?_,
    ⟨hPK, htop⟩, ⟨hb, (hbot b hb hbl).1⟩⟩
  · have hl := lemma14_6 hN hE hFi hPp hQ
    constructor
    · intro hQK
      exact hl.1.2 (pkCh_mem_hitClass.1 hQK).2
    · intro hc
      obtain ⟨c, hc0, hcX⟩ := hc
      exact pkCh_mem_hitClass.2 ⟨(hl.2 c hc0 hcX).2, hl.1.1 ⟨c, hc0, hcX⟩⟩
  · have hl := lemma14_6 hN hE hFi hPp (hodd Q hQ)
    obtain ⟨c, hc0, hcX⟩ := hl.1.2 (pkCh_mem_hitClass.1 hQ).2
    rw [hcX X hX, (hl.2 c hc0 hcX).1, one_mul]
  · rw [(pkCh_mem_hitClass.1 hQ).2, (pkCh_mem_hitClass.1 hQ').2]

/-! ## The parts avoiding `K` of the children -/

-- registry: C-DK78
/-- `b_Q`: `N^{¬K}` of the A-side polygon of `Q` (the sub-polygon bounding `A_Q`, closed by `Q`),
as a function of the parent planar variables; `K_r` read in the child's labels is
`pkRBPull`. -/
noncomputable def NLSM.Amplitude.avoidingA (N : ℕ) (K : Finset (ℕ × ℕ)) (Q : ℕ × ℕ) : RF :=
  nlsmAvoiding (headLen N Q + 1) (pkRBPull N (headStart Q) (headLen N Q + 1) K)
    (fun d => gen (relab N (headStart Q) d))

-- registry: C-DK78
/-- `a_Q`: `N^{¬K}` of the B-side polygon of `Q`, as a function of the parent planar
variables. -/
noncomputable def NLSM.Amplitude.avoidingB (N : ℕ) (K : Finset (ℕ × ℕ)) (Q : ℕ × ℕ) : RF :=
  nlsmAvoiding (tailLen N Q + 1) (pkRBPull N (tailStart Q) (tailLen N Q + 1) K)
    (fun d => gen (relab N (tailStart Q) d))

/-- `H` is a linear subspace. -/
theorem residueHyperplane_sub (N : ℕ) (S : Finset (ℕ × ℕ)) (P : ℕ × ℕ) :
    pkRSub (residueHyperplane N S P) := by
  have h := pkR_d_H_sub N S P
  have e : residueHyperplane N S P = {X : ℕ × ℕ → ℚ | X ∈ {X : ℕ × ℕ → ℚ | OnLocus N S X} ∧
      MvPolynomial.eval X (MvPolynomial.X P : MvPolynomial (ℕ × ℕ) ℚ) = 0} := by
    ext X
    simp [residueHyperplane]
  rw [e]
  exact h

/-- The child part `N^{¬K}` of a sub-polygon written over its denominator: with `s` the start and
`n` the size of the child, `N^{¬K} · ∏ X_{relab d} = rename relab NP^{¬K}` in `RF`. -/
theorem nlsmAvoiding_child_eq (N s n : ℕ) (hn : 2 ≤ n) (K : Finset (ℕ × ℕ)) :
    nlsmAvoiding n (pkRBPull N s n K) (fun d => gen (relab N s d)) *
        algebraMap _ RF (MvPolynomial.rename (relab N s)
          (∏ d ∈ oddDiagonals n \ pkRBPull N s n K,
            (MvPolynomial.X d : MvPolynomial (ℕ × ℕ) ℚ))) =
      algebraMap _ RF (MvPolynomial.rename (relab N s) (pkRBNP ℚ n (pkRBPull N s n K))) := by
  set f : MvPolynomial (ℕ × ℕ) ℚ →+* RF :=
    (algebraMap _ RF).comp (MvPolynomial.rename (relab N s)).toRingHom with hf
  have hX : ∀ d, f (MvPolynomial.X d) = gen (relab N s d) := fun d => by
    simp [hf, gen]
  have h := nlsmAvoiding_numerator_hom f hn (pkRBPull N s n K)
    (fun d _ => by rw [hX]; exact gen_ne_zero _)
  simp only [hX] at h
  rw [show algebraMap _ RF (MvPolynomial.rename (relab N s) (pkRBNP ℚ n (pkRBPull N s n K))) =
    f (pkRBNP ℚ n (pkRBPull N s n K)) from rfl, h, map_prod, map_prod]
  simp [gen]

/-- The denominator of a child part avoiding `K` is not identically zero on `H`: its factors are
odd chords outside `K`. -/
theorem child_den_nonvanishing {N : ℕ} (hE : Even N) {S K : Finset (ℕ × ℕ)} {P t b : ℕ × ℕ}
    (h : FlankClassPoleHypotheses N S K P t b) {s n : ℕ} (hs : 1 ≤ s ∧ s ≤ N) (hn : n ≤ N) :
    ∃ w ∈ residueHyperplane N S P, MvPolynomial.eval w (MvPolynomial.rename (relab N s)
      (∏ d ∈ oddDiagonals n \ pkRBPull N s n K, (MvPolynomial.X d : MvPolynomial (ℕ × ℕ) ℚ))) ≠
        0 := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  obtain ⟨w, hw, hall⟩ := pkR_avoid (residueHyperplane_sub N S P)
    (fun d => (MvPolynomial.X (relab N s d) : MvPolynomial (ℕ × ℕ) ℚ))
    (oddDiagonals n \ pkRBPull N s n K) (fun d hd => by
      obtain ⟨hdo, hdK⟩ := mem_sdiff.1 hd
      have ho := pkR_w_relab_odd hE' hs hn hdo
      have hK : relab N s d ∉ K := fun hK => hdK (mem_filter.2 ⟨(mem_filter.1 hdo).1, hK⟩)
      obtain ⟨X, hX, hXd⟩ := odd_chord_outside_class_nonvanishing_on_hyperplane h ho hK
      exact ⟨X, hX, by rw [MvPolynomial.eval_X]; exact hXd⟩)
  refine ⟨w, hw, ?_⟩
  simp only [map_prod, MvPolynomial.rename_X]
  exact prod_ne_zero_iff.2 fun d hd => hall d hd

/-- Two members of a class with a top and a bottom that do not cross have nested odd-ended sides
(a helper: the direction of `flank_class_members_form_chains` that the library's lemmas take as a
hypothesis). -/
theorem NLSM.Amplitude.FlankClassPoleHypotheses.nested {N : ℕ} {S K : Finset (ℕ × ℕ)}
    {P t b : ℕ × ℕ} (h : FlankClassPoleHypotheses N S K P t b) :
    ∀ Q ∈ K, ∀ Q' ∈ K, ¬ Crosses Q' Q →
      oddSide N Q ⊆ oddSide N Q' ∨ oddSide N Q' ⊆ oddSide N Q := by
  intro Q hQ Q' hQ' hc
  rcases (pkR_b_chain (h.odd h.bottom.1) (h.odd h.top.1) (h.odd hQ') (h.odd hQ)
    (h.bottom.2 Q' hQ') (h.top.2 Q' hQ') (h.bottom.2 Q hQ) (h.top.2 Q hQ)).1 hc with e | e
  · exact Or.inr e
  · exact Or.inl e

/-- The extreme term (i): under (H1)–(H4), `b_Q|_H = 0` for every member `Q ≠ b`. -/
theorem avoidingA_restrictsToZero {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {S K : Finset (ℕ × ℕ)}
    {P t b : ℕ × ℕ} (h : FlankClassPoleHypotheses N S K P t b) {Q : ℕ × ℕ} (hQ : Q ∈ K)
    (hQb : Q ≠ b) :
    RestrictsToZeroAlong {X | OnLocus N S X} (residueHyperplane N S P) (avoidingA N K Q) := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  have hK := h.eq_hitClass hN hE
  have f1 := pkR_b_head_facts hE' (h.odd hQ)
  refine restrictsToZeroAlong_of_eq (P := MvPolynomial.rename (relab N (headStart Q))
      (pkRBNP ℚ (headLen N Q + 1) (pkRBPull N (headStart Q) (headLen N Q + 1) K)))
    (pkR_d_locus_sub N S).1 (nlsmAvoiding_child_eq N _ _ (by omega) K)
    (child_den_nonvanishing hE h ⟨f1.1, f1.2.1⟩ (by omega)) fun X ⟨hX, hXP⟩ => ?_
  have hn := h.nested
  rw [hK] at hQ hn ⊢
  have hb := h.bottom
  rw [hK] at hb
  exact pkR_d2_bvan hN hE' hb.1 hQ (hb.2 Q hQ) hQb hb.2 hn hX
    (by rw [h.h2' Q (hK ▸ hQ) X hX, hXP])

/-- The extreme term (ii): under (H1)–(H4), `a_Q|_H = 0` for every member `Q ≠ t`. -/
theorem avoidingB_restrictsToZero {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {S K : Finset (ℕ × ℕ)}
    {P t b : ℕ × ℕ} (h : FlankClassPoleHypotheses N S K P t b) {Q : ℕ × ℕ} (hQ : Q ∈ K)
    (hQt : Q ≠ t) :
    RestrictsToZeroAlong {X | OnLocus N S X} (residueHyperplane N S P) (avoidingB N K Q) := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  have hK := h.eq_hitClass hN hE
  have hQo := h.odd hQ
  have f1 := pkR_b_head_facts hE' hQo
  have hts1 : 1 ≤ tailStart Q ∧ tailStart Q ≤ N := by
    have hd := mem_diagonals.1 (mem_filter.1 hQo).1
    rcases pkR_b_tail_data hQo with e | e <;> omega
  have htl : tailLen N Q = N - headLen N Q := rfl
  refine restrictsToZeroAlong_of_eq (P := MvPolynomial.rename (relab N (tailStart Q))
      (pkRBNP ℚ (tailLen N Q + 1) (pkRBPull N (tailStart Q) (tailLen N Q + 1) K)))
    (pkR_d_locus_sub N S).1 (nlsmAvoiding_child_eq N _ _ (by omega) K)
    (child_den_nonvanishing hE h hts1 (by omega)) fun X ⟨hX, hXP⟩ => ?_
  have hn := h.nested
  rw [hK] at hQ hn ⊢
  have ht := h.top
  rw [hK] at ht
  exact pkR_d2_avan hN hE' ht.1 hQ hQt ht.2 hn hX (by rw [h.h2' Q (hK ▸ hQ) X hX, hXP])

/-! ## The strip factor -/

-- registry: C-DK78
/-- `N_{Ω(Q,Q′)}`: `NLSM` of the region `Ω(Q, Q′)` of two nested odd chords (`A_{Q′} ⊆ A_Q`), the
sub-polygon with vertices `a, …, c, c′+1, …, a′+1` (`A_Q = [a, a′]`, `A_{Q′} = [c, c′]`), as a
function of the parent planar variables: the library's region point (`pkRSubX`, `C5`) with the
vertex list `pkRBOmL` (`C7`; vertex `k` of the region is the parent vertex `a + k − 1` for
`k ≤ c − a + 1`, else `a + k − 2 + |A_{Q′}|`, mod `N`); `|Ω| = |A_Q| − |A_{Q′}| + 2`. -/
noncomputable def NLSM.Amplitude.regionAmp (N : ℕ) (Q Q' : ℕ × ℕ) : RF :=
  NLSM (pkRBOmM N Q Q')
    (pkRSubX N (pkRBOmL N (headStart Q) (cycPos N (headStart Q) (headStart Q'))
      (headLen N Q')) gen)

-- registry: C-DK78
/-- The strip factor `φ(Q, Q′)`: `1` for `Q = Q′`, `N_{Ω(Q,Q′)} / x` (`x = X_P`) for
`Q ≻ Q′`; used only for `Q ⪰ Q′`. -/
noncomputable def NLSM.Amplitude.stripFactor (N : ℕ) (P Q Q' : ℕ × ℕ) : RF :=
  if Q = Q' then 1 else regionAmp N Q Q' / gen P

/-- An odd diagonal of `Ω(Q, Q′)` that is not the image of a member strictly between `Q′` and `Q`
is, read as a parent chord, not a member of `K` (the library has this for `Ω(t, b)` only,
`pkR_w_notK`). -/
theorem region_diag_not_member {N : ℕ} (hE : Even N) {S K : Finset (ℕ × ℕ)} {P t b : ℕ × ℕ}
    (h : FlankClassPoleHypotheses N S K P t b) {Q Q' : ℕ × ℕ} (hQ : Q ∈ K) (hQ' : Q' ∈ K)
    (hsub : oddSide N Q' ⊆ oddSide N Q) (hne : Q ≠ Q') {d : ℕ × ℕ}
    (hd : d ∈ oddDiagonals (pkRBOmM N Q Q'))
    (hex : d ∉ ((pkRD2Above N (pkRD2Below N K Q) Q').image (pkRBOmI N Q Q')).image
      (pkRMchord (pkRBOmD N Q Q'))) :
    relab N (headStart Q) (pkRWOm (cycPos N (headStart Q) (headStart Q')) (headLen N Q') d) ∉
      K := by
  classical
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  have hQo := h.odd hQ
  have hQ'o := h.odd hQ'
  set K₃ := K.filter (fun c => oddSide N Q' ⊆ oddSide N c ∧ oddSide N c ⊆ oddSide N Q) with hK₃
  have hsame : pkRD2Above N (pkRD2Below N K₃ Q) Q' =
      pkRD2Above N (pkRD2Below N K Q) Q' := by
    ext c
    simp only [pkRD2Above, pkRD2Below, mem_filter, hK₃]
    tauto
  have hn3 := pkR_w_notK hE' hQo hQ'o hsub hne (fun c hc => h.odd (mem_filter.1 hc).1)
    (fun c hc => (mem_filter.1 hc).2) hd (by rw [hsame]; exact hex)
  intro hc
  apply hn3
  refine mem_filter.2 ⟨hc, ?_⟩
  have f1 := pkR_b_head_facts hE' hQo
  have fQ' := pkR_b_head_facts hE' hQ'o
  obtain ⟨p0, p1, p2, -⟩ := pkR_b_nest_pos hE' hQo hQ'o hsub hne
  have hm : pkRBOmM N Q Q' = headLen N Q - headLen N Q' + 2 := rfl
  have hd' := hd
  rw [hm] at hd'
  have hωd := pkR_w_om_mem fQ'.2.2.2.2.1 fQ'.2.2.2.1 p1 hd'
  have hpull : pkRWOm (cycPos N (headStart Q) (headStart Q')) (headLen N Q') d ∈
      pkRBPull N (headStart Q) (headLen N Q + 1) K := mem_filter.2 ⟨(mem_filter.1 hωd.1).1, hc⟩
  rw [pkR_d2_pull_below hE' h.odd h.nested hQ] at hpull
  obtain ⟨e, he, hed⟩ := mem_image.1 hpull
  obtain ⟨c', hc', rfl⟩ := mem_image.1 he
  obtain ⟨hc'K, hc'Q, hc'sub⟩ := mem_filter.1 hc'
  have hc'o := h.odd hc'K
  have fc' := pkR_b_head_facts hE' hc'o
  obtain ⟨q0, q1, -, q3, -⟩ := pkR_d2_npos hE' hQo hc'o hc'sub
  have hrc : relab N (headStart Q) (cycPos N (headStart Q) (headStart c') + 1,
      cycPos N (headStart Q) (headStart c') + headLen N c' + 1) = c' :=
    pkR_b_relab_head hc'o ⟨f1.1, f1.2.1⟩ (by omega) q3
  dsimp only at hed
  rw [← hed, hrc]
  refine ⟨?_, hc'sub⟩
  -- positions: the bottom `b` lies in both `c′` and `Q′`
  have hbK := h.bottom.1
  have hbo := h.odd hbK
  have fb := pkR_b_head_facts hE' hbo
  have hbQ : Q ≠ b := fun e => hne (pkR_d2_eq_of_head hQo hQ'o
    (Subset.antisymm (e ▸ h.bottom.2 Q' hQ') hsub))
  have hbsub : oddSide N b ⊆ oddSide N Q := h.bottom.2 Q hQ
  have hb1 := (pkR_d2_nest_iff hE' hQo hbo hc'o hbsub hc'sub hbQ (Ne.symm hc'Q)).1
    (h.bottom.2 c' hc'K)
  have hb2 := (pkR_d2_nest_iff hE' hQo hbo hQ'o hbsub hsub hbQ hne).1 (h.bottom.2 Q' hQ')
  refine (pkR_d2_nest_iff hE' hQo hQ'o hc'o hsub hc'sub hne (Ne.symm hc'Q)).2 ?_
  obtain ⟨i, j⟩ := d
  have hij := pkR_b_odd_iff.1 hd'
  have e1 := pkR_b_olo_eq (cycPos N (headStart Q) (headStart Q')) (headLen N Q') i
  have e2 := pkR_b_olo_eq (cycPos N (headStart Q) (headStart Q')) (headLen N Q') j
  have w1 := congrArg Prod.fst hed
  have w2 := congrArg Prod.snd hed
  simp only [pkRWOm] at w1 w2
  omega

/-- The member chords of `Ω(Q, Q′)`: for a member `c` strictly between `Q′` and `Q`, its image
`pkRMchord (omD) (omI c)` among the diagonals of `Ω(Q, Q′)` is an odd diagonal and, read as a
parent chord, is `c`. -/
theorem region_member_diag {N : ℕ} (hE : Even N) {S K : Finset (ℕ × ℕ)} {P t b : ℕ × ℕ}
    (h : FlankClassPoleHypotheses N S K P t b) {Q Q' : ℕ × ℕ} (hQ : Q ∈ K) (hQ' : Q' ∈ K)
    (hsub : oddSide N Q' ⊆ oddSide N Q) (hne : Q ≠ Q') {c : ℕ × ℕ}
    (hc : c ∈ pkRD2Above N (pkRD2Below N K Q) Q') :
    pkRMchord (pkRBOmD N Q Q') (pkRBOmI N Q Q' c) ∈ oddDiagonals (pkRBOmM N Q Q') ∧
      pkRWOm (cycPos N (headStart Q) (headStart Q')) (headLen N Q')
          (pkRMchord (pkRBOmD N Q Q') (pkRBOmI N Q Q' c)) ∈ diagonals (headLen N Q + 1) ∧
      relab N (headStart Q) (pkRWOm (cycPos N (headStart Q) (headStart Q')) (headLen N Q')
          (pkRMchord (pkRBOmD N Q Q') (pkRBOmI N Q Q' c))) = c := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  have hQo := h.odd hQ
  have hQ'o := h.odd hQ'
  obtain ⟨hc1, hc2, hc3⟩ := mem_filter.1 hc
  obtain ⟨hcK, hcQ, hcsub⟩ := mem_filter.1 hc1
  have hco := h.odd hcK
  have f1 := pkR_b_head_facts hE' hQo
  have fQ' := pkR_b_head_facts hE' hQ'o
  have fc := pkR_b_head_facts hE' hco
  obtain ⟨p0, p1, p2, -⟩ := pkR_b_nest_pos hE' hQo hQ'o hsub hne
  obtain ⟨c0, c1, c2, -⟩ := pkR_b_nest_pos hE' hQo hco hcsub (Ne.symm hcQ)
  have hn := (pkR_d2_nest_iff hE' hQo hQ'o hco hsub hcsub hne (Ne.symm hcQ)).1 hc3
  obtain ⟨q0, q1, -, q3, -⟩ := pkR_d2_npos hE' hQo hco hcsub
  have hrc : relab N (headStart Q) (cycPos N (headStart Q) (headStart c) + 1,
      cycPos N (headStart Q) (headStart c) + headLen N c + 1) = c :=
    pkR_b_relab_head hco ⟨f1.1, f1.2.1⟩ (by omega) q3
  have hne' : c ≠ Q' := hc2
  have hl : headLen N Q' + 2 ≤ headLen N c :=
    (pkR_b_nest_pos hE' hco hQ'o hc3 hne').2.2.1
  have e1 := pkR_b_olo_eq (cycPos N (headStart Q) (headStart Q')) (headLen N Q')
    (2 * (cycPos N (headStart Q) (headStart c) / 2) + 1)
  have e2 := pkR_b_olo_eq (cycPos N (headStart Q) (headStart Q')) (headLen N Q')
    (2 * (cycPos N (headStart Q) (headStart Q') / 2) + 2 * ((cycPos N (headStart Q) (headStart c) +
      headLen N c - headLen N Q' - cycPos N (headStart Q) (headStart Q')) / 2) + 2)
  have hω : pkRWOm (cycPos N (headStart Q) (headStart Q')) (headLen N Q')
      (pkRMchord (pkRBOmD N Q Q') (pkRBOmI N Q Q' c)) =
      (cycPos N (headStart Q) (headStart c) + 1,
        cycPos N (headStart Q) (headStart c) + headLen N c + 1) := by
    simp only [pkRWOm, pkRMchord, pkRBOmD, pkRBOmI]
    refine Prod.ext ?_ ?_ <;> dsimp only <;> omega
  refine ⟨?_, ?_, by rw [hω, hrc]⟩
  · refine pkR_b_odd_iff.2 ?_
    simp only [pkRBOmD, pkRBOmI, pkRBOmM]
    omega
  · rw [hω]
    refine mem_diagonals.2 ?_
    dsimp only
    omega

/-- At an odd diagonal of `Ω(Q, Q′)`, the region's coordinate polynomial is the parent chord's
variable. -/
theorem region_subP_odd {N : ℕ} (hE : Even N) {Q Q' : ℕ × ℕ} (hQo : Q ∈ oddDiagonals N)
    (hQ'o : Q' ∈ oddDiagonals N) (hsub : oddSide N Q' ⊆ oddSide N Q) (hne : Q ≠ Q') {d : ℕ × ℕ}
    (hd : d ∈ oddDiagonals (pkRBOmM N Q Q')) :
    pkRD2SubP N (pkRBOmL N (headStart Q) (cycPos N (headStart Q) (headStart Q'))
        (headLen N Q')) d =
      MvPolynomial.X (relab N (headStart Q)
        (pkRWOm (cycPos N (headStart Q) (headStart Q')) (headLen N Q') d)) ∧
      relab N (headStart Q) (pkRWOm (cycPos N (headStart Q) (headStart Q')) (headLen N Q') d) ∈
        oddDiagonals N := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  have f1 := pkR_b_head_facts hE' hQo
  have fQ' := pkR_b_head_facts hE' hQ'o
  obtain ⟨p0, p1, p2, -⟩ := pkR_b_nest_pos hE' hQo hQ'o hsub hne
  have hm : pkRBOmM N Q Q' = headLen N Q - headLen N Q' + 2 := rfl
  have hd' := hd
  rw [hm] at hd'
  have hω := pkR_w_om_mem fQ'.2.2.2.2.1 fQ'.2.2.2.1 p1 hd'
  refine ⟨MvPolynomial.funext fun X => ?_, pkR_w_relab_odd hE' ⟨f1.1, f1.2.1⟩ (by omega) hω.1⟩
  rw [pkR_d2_subP_eval, MvPolynomial.eval_X]
  exact pkR_w_omX ⟨f1.1, f1.2.1⟩ (by omega) X (mem_filter.1 hω.1).1

/-- `N_{Ω(Q,Q′)}` over its denominator: `N_Ω · ∏_{d odd} X_d(Ω) = NP_Ω` at the region point, in
`RF`, both sides read as polynomials in the parent planar variables. -/
theorem regionAmp_eq {N : ℕ} (hE : Even N) {Q Q' : ℕ × ℕ} (hQo : Q ∈ oddDiagonals N)
    (hQ'o : Q' ∈ oddDiagonals N) (hsub : oddSide N Q' ⊆ oddSide N Q) (hne : Q ≠ Q') :
    regionAmp N Q Q' * algebraMap _ RF (MvPolynomial.aeval (pkRD2SubP N (pkRBOmL N
        (headStart Q) (cycPos N (headStart Q) (headStart Q')) (headLen N Q')))
        (∏ d ∈ oddDiagonals (pkRBOmM N Q Q'), (MvPolynomial.X d : MvPolynomial (ℕ × ℕ) ℚ))) =
      algebraMap _ RF (MvPolynomial.aeval (pkRD2SubP N (pkRBOmL N (headStart Q)
        (cycPos N (headStart Q) (headStart Q')) (headLen N Q'))) (NP ℚ (pkRBOmM N Q Q'))) := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  set f := pkRBOmL N (headStart Q) (cycPos N (headStart Q) (headStart Q')) (headLen N Q')
  set g : MvPolynomial (ℕ × ℕ) ℚ →+* RF :=
    (algebraMap _ RF).comp (MvPolynomial.aeval (pkRD2SubP N f)).toRingHom with hg
  have hgX : ∀ d, g (MvPolynomial.X d) = pkRSubX N f gen d := fun d => by
    simp only [hg, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, MvPolynomial.aeval_X]
    exact planarP_hom (algebraMap _ RF) N (f d.1) (f d.2)
  have hm2 : 2 ≤ pkRBOmM N Q Q' := by
    have := (pkR_b_nest_pos hE' hQo hQ'o hsub hne).2.2.1
    change 2 ≤ headLen N Q - headLen N Q' + 2
    omega
  have h := nlsm_numerator_hom g hm2 fun d hd => by
    simp only [hg, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, MvPolynomial.aeval_X]
    rw [(region_subP_odd hE hQo hQ'o hsub hne hd).1]
    exact gen_ne_zero _
  simp only [hgX, oddDen] at h
  exact h.symm

/-- On `L_S`, the odd diagonals of `Ω(Q, Q′)` at the region point multiply to `x^{|J|} · D′`
(`J` the members strictly between, `D′` the library's `pkRD2Dp`). -/
theorem region_den_eval {N : ℕ} (hE : Even N) {S K : Finset (ℕ × ℕ)} {P t b : ℕ × ℕ}
    (h : FlankClassPoleHypotheses N S K P t b) {Q Q' : ℕ × ℕ} (hQ : Q ∈ K) (hQ' : Q' ∈ K)
    (hsub : oddSide N Q' ⊆ oddSide N Q) (hne : Q ≠ Q') {X : ℕ × ℕ → ℚ} (hX : OnLocus N S X) :
    MvPolynomial.eval X (MvPolynomial.aeval (pkRD2SubP N (pkRBOmL N
        (headStart Q) (cycPos N (headStart Q) (headStart Q')) (headLen N Q')))
        (∏ d ∈ oddDiagonals (pkRBOmM N Q Q'), (MvPolynomial.X d : MvPolynomial (ℕ × ℕ) ℚ))) =
      X P ^ (pkRD2Above N (pkRD2Below N K Q) Q').card *
        MvPolynomial.eval X (pkRD2Dp N K Q Q') := by
  classical
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  have hQo := h.odd hQ
  have hQ'o := h.odd hQ'
  set f := pkRBOmL N (headStart Q) (cycPos N (headStart Q) (headStart Q')) (headLen N Q')
  set e : ℕ × ℕ → ℕ × ℕ := fun c => pkRMchord (pkRBOmD N Q Q') (pkRBOmI N Q Q' c) with he
  have himg : ((pkRD2Above N (pkRD2Below N K Q) Q').image (pkRBOmI N Q Q')).image
      (pkRMchord (pkRBOmD N Q Q')) = (pkRD2Above N (pkRD2Below N K Q) Q').image e := by
    rw [image_image]
    rfl
  have hinj : Set.InjOn e ↑(pkRD2Above N (pkRD2Below N K Q) Q') := by
    intro c₁ h₁ c₂ h₂ he
    have r₁ := (region_member_diag hE h hQ hQ' hsub hne h₁).2.2
    have r₂ := (region_member_diag hE h hQ hQ' hsub hne h₂).2.2
    rw [← r₁, ← r₂]
    exact congrArg _ (congrArg _ he)
  have hsubJ : (pkRD2Above N (pkRD2Below N K Q) Q').image e ⊆
      oddDiagonals (pkRBOmM N Q Q') := fun d hd => by
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hd
    exact (region_member_diag hE h hQ hQ' hsub hne hc).1
  rw [map_prod, map_prod, pkR_d2_Dp_eval, himg,
    ← prod_filter_mul_prod_filter_not (oddDiagonals (pkRBOmM N Q Q'))
      (fun d => d ∈ (pkRD2Above N (pkRD2Below N K Q) Q').image e)]
  congr 1
  · rw [filter_mem_eq_inter, inter_eq_right.2 hsubJ, prod_image hinj, ← prod_const]
    refine prod_congr rfl fun c hc => ?_
    obtain ⟨-, hω, hrel⟩ := region_member_diag hE h hQ hQ' hsub hne hc
    rw [pkR_eval_aeval, MvPolynomial.eval_X, pkR_d2_subP_eval]
    change pkRBOmX N Q Q' X (e c) = X P
    have hf1 := pkR_b_head_facts hE' hQo
    rw [pkR_w_omX ⟨hf1.1, hf1.2.1⟩ (by omega) X hω, hrel]
    exact h.h2' c (mem_filter.1 (mem_filter.1 hc).1).1 X hX
  · refine prod_congr rfl fun d _ => ?_
    rw [pkR_eval_aeval, MvPolynomial.eval_X, pkR_d2_subP_eval]
    rfl

-- registry: C-ZW0Z
/-- On `L_S`, `φ(Q, Q′)` (members `Q ⪰ Q′`) differs from a non-zero constant `ε` by a function
that restricts to zero on `H`: from the library's Ω formula (`pkR_d2_omegaQ`:
`NP_Ω = x^{|J|}(ε x D′ + x² F)` on `L_S`), `φ = (ε D′ + x F) / D′`; `ε = 1` for `Q = Q′`. -/
theorem NLSM.Amplitude.stripFactor_sub_const_restrictsToZero {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    {S K : Finset (ℕ × ℕ)} {P t b : ℕ × ℕ} (h : FlankClassPoleHypotheses N S K P t b)
    {Q Q' : ℕ × ℕ} (hQ : Q ∈ K)
    (hQ' : Q' ∈ K) (hsub : oddSide N Q' ⊆ oddSide N Q) :
    ∃ ε : ℚ, ε ≠ 0 ∧ RestrictsToZeroAlong {X | OnLocus N S X} (residueHyperplane N S P)
      (stripFactor N P Q Q' - (ε : RF)) := by
  classical
  have hV : (fun _ => (0 : ℚ)) ∈ {X : ℕ × ℕ → ℚ | OnLocus N S X} := (pkR_d_locus_sub N S).1
  by_cases hne : Q = Q'
  · refine ⟨1, one_ne_zero, ?_⟩
    rw [stripFactor, ite_eq_left_of_eq_true _ _ (eq_true hne)]
    exact restrictsToZeroAlong_of_eq (P := 0) (D := 1) hV (by simp)
      ⟨fun _ => 0, ⟨hV, rfl⟩, by simp⟩ fun _ _ => by simp
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  have hK := h.eq_hitClass hN hE
  have hQo := h.odd hQ
  have hQ'o := h.odd hQ'
  obtain ⟨ε, F, hε, hΩ⟩ := pkR_d2_omegaQ hN hE' (hK ▸ hQ) (hK ▸ hQ') hsub hne
  set f := pkRBOmL N (headStart Q) (cycPos N (headStart Q) (headStart Q')) (headLen N Q')
    with hf
  set σ := MvPolynomial.aeval (R := ℚ) (pkRD2SubP N f) with hσ
  set den := ∏ d ∈ oddDiagonals (pkRBOmM N Q Q'), (MvPolynomial.X d : MvPolynomial (ℕ × ℕ) ℚ)
    with hden
  set Dp := pkRD2Dp N K Q Q' with hDp
  set Pn := MvPolynomial.C ε * Dp + MvPolynomial.X P * σ F with hPn
  have hrat := regionAmp_eq hE hQo hQ'o hsub hne
  have hC : algebraMap (MvPolynomial (ℕ × ℕ) ℚ) RF (MvPolynomial.C ε) = (ε : RF) :=
    eq_ratCast ((algebraMap _ RF).comp MvPolynomial.C) ε
  have e : (stripFactor N P Q Q' - (ε : RF)) * algebraMap _ RF Dp -
      algebraMap _ RF (MvPolynomial.X P * σ F) =
      stripFactor N P Q Q' * algebraMap _ RF Dp - algebraMap _ RF Pn := by
    rw [hPn, map_add, map_mul, map_mul, hC]
    ring
  rw [stripFactor, ite_eq_right_of_eq_false _ _ (eq_false hne)] at e
  refine ⟨ε, hε, MvPolynomial.X P * σ F, Dp, ?_, ?_, fun x hx => by
    rw [map_mul, MvPolynomial.eval_X, hx.2, zero_mul]⟩
  · rw [stripFactor, ite_eq_right_of_eq_false _ _ (eq_false hne), e]
    refine ⟨σ (NP ℚ (pkRBOmM N Q Q')) * Dp - Pn * (MvPolynomial.X P * σ den),
      MvPolynomial.X P * σ den, ?_, ?_, ?_⟩
    · -- the identity in `RF`
      have hP0 : (gen P) ≠ 0 := gen_ne_zero P
      have hrat' : regionAmp N Q Q' * algebraMap _ RF (σ den) =
          algebraMap _ RF (σ (NP ℚ (pkRBOmM N Q Q'))) := hrat
      simp only [map_sub, map_mul]
      rw [← hrat', show algebraMap _ RF (MvPolynomial.X P : MvPolynomial (ℕ × ℕ) ℚ) = gen P
        from rfl]
      field_simp
    · -- the denominator is not identically zero on `L_S`
      have hodd := fun d (hd : d ∈ oddDiagonals (pkRBOmM N Q Q')) =>
        region_subP_odd hE hQo hQ'o hsub hne hd
      obtain ⟨w, hw, hall⟩ := pkR_avoid (pkR_d_locus_sub N S)
        (fun o : Option (ℕ × ℕ) => o.elim (MvPolynomial.X P)
          (fun d => MvPolynomial.X (relab N (headStart Q)
            (pkRWOm (cycPos N (headStart Q) (headStart Q')) (headLen N Q') d))))
        (insert none ((oddDiagonals (pkRBOmM N Q Q')).image some)) (by
          intro o ho
          rcases mem_insert.1 ho with e | e
          · subst e
            obtain ⟨X, hX, hXP⟩ := h.h1 P (h.odd h.mem)
            exact ⟨X, hX, by simpa using hXP⟩
          · obtain ⟨d, hd, rfl⟩ := mem_image.1 e
            obtain ⟨X, hX, hXd⟩ := h.h1 _ (hodd d hd).2
            exact ⟨X, hX, by simpa using hXd⟩)
      refine ⟨w, hw, ?_⟩
      rw [map_mul, hσ, hden, map_prod, map_prod]
      refine mul_ne_zero (by simpa using hall none (mem_insert_self _ _))
        (prod_ne_zero_iff.2 fun d hd => ?_)
      rw [MvPolynomial.aeval_X, (hodd d hd).1]
      simpa using hall (some d) (mem_insert_of_mem (mem_image_of_mem _ hd))
    · -- the numerator vanishes on `L_S`
      intro X hX
      have hX' : OnLocus N S X := hX
      have hQP := h.h2' Q hQ X hX'
      have h1 : MvPolynomial.eval X (σ (NP ℚ (pkRBOmM N Q Q'))) = _ :=
        (pkR_d2_eval_sub N f X _).symm.trans (hΩ X hX')
      have h2 := region_den_eval hE h hQ hQ' hsub hne hX'
      have h3 : MvPolynomial.eval X (σ F) = MvPolynomial.eval (pkRBOmX N Q Q' X) F :=
        (pkR_d2_eval_sub N f X F).symm
      have h4 : (∏ Q'' ∈ (oddDiagonals (pkRBOmM N Q Q')).filter (fun Q'' => Q'' ∉
          ((pkRD2Above N (pkRD2Below N (hitClass N S t) Q) Q').image (pkRBOmI N Q Q')).image
            (pkRMchord (pkRBOmD N Q Q'))), pkRBOmX N Q Q' X Q'') =
          MvPolynomial.eval X Dp := by
        rw [hDp, pkR_d2_Dp_eval, hK]
      rw [h4, ← h3, ← hK] at h1
      have h2' : MvPolynomial.eval X (σ den) = _ := h2
      simp only [map_sub, map_mul, map_add, MvPolynomial.eval_C, MvPolynomial.eval_X, hPn]
      rw [h1, h2', hQP]
      ring
  · -- `D′` is not identically zero on `H`
    obtain ⟨w, hw, hall⟩ := pkR_avoid (residueHyperplane_sub N S P)
      (fun d => MvPolynomial.X (relab N (headStart Q)
          (pkRWOm (cycPos N (headStart Q) (headStart Q')) (headLen N Q') d)))
      ((oddDiagonals (pkRBOmM N Q Q')).filter (fun d => d ∉
        ((pkRD2Above N (pkRD2Below N K Q) Q').image (pkRBOmI N Q Q')).image
          (pkRMchord (pkRBOmD N Q Q')))) (by
        intro d hd
        obtain ⟨hdo, hdx⟩ := mem_filter.1 hd
        obtain ⟨X, hX, hXd⟩ := odd_chord_outside_class_nonvanishing_on_hyperplane h
          (region_subP_odd hE hQo hQ'o hsub hne hdo).2
          (region_diag_not_member hE h hQ hQ' hsub hne hdo hdx)
        exact ⟨X, hX, by simpa using hXd⟩)
    refine ⟨w, hw, ?_⟩
    rw [hDp, pkRD2Dp]
    rw [map_prod]
    refine prod_ne_zero_iff.2 fun d hd => ?_
    rw [(region_subP_odd hE hQo hQ'o hsub hne (mem_filter.1 hd).1).1]
    exact hall d hd

/-- Every strip factor has no pole along `H`: under (H1)–(H4), for all members `Q ⪰ Q′`
(`A_{Q′} ⊆ A_Q`), from the value of the strip factor (`stripFactor_sub_const_restrictsToZero`). -/
theorem stripFactor_hasNoPoleAlong {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {S K : Finset (ℕ × ℕ)}
    {P t b : ℕ × ℕ} (h : FlankClassPoleHypotheses N S K P t b) {Q Q' : ℕ × ℕ} (hQ : Q ∈ K)
    (hQ' : Q' ∈ K) (hsub : oddSide N Q' ⊆ oddSide N Q) :
    HasNoPoleAlong {X | OnLocus N S X} (residueHyperplane N S P) (stripFactor N P Q Q') := by
  obtain ⟨ε, -, hφ⟩ := stripFactor_sub_const_restrictsToZero hN hE h hQ hQ' hsub
  have hH : ∃ w, w ∈ residueHyperplane N S P := ⟨_, (residueHyperplane_sub N S P).1⟩
  have := hφ.hasNoPoleAlong.add (pkR_d_locus_sub N S) (residueHyperplane_sub N S P)
    (hasNoPoleAlong_const (pkR_d_locus_sub N S) hH ε)
  rwa [sub_add_cancel] at this

-- registry: C-DK78
/-- **Only the extreme term survives**. Under (H1)–(H4) (`FlankClassPoleHypotheses`; `x = X_P`,
`H = L_S ∩ {x = 0}`), for even `N ≥ 6`: (i) `b_Q|_H = 0` for every member `Q ≠ b`, and (ii)
`a_Q|_H = 0` for every member `Q ≠ t`; the restrictions are those of rational functions to `L_S`.
Here `b_Q` (`avoidingA`) is the paper's `N^{¬K}` of the A-side child of `Q`, and `a_Q`
(`avoidingB`) that of its B-side child. -/
theorem NLSM.Amplitude.only_extreme_term_survives {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    {S K : Finset (ℕ × ℕ)} {P t b : ℕ × ℕ} (h : FlankClassPoleHypotheses N S K P t b) :
    (∀ Q ∈ K, Q ≠ b →
      RestrictsToZeroAlong {X | OnLocus N S X} (residueHyperplane N S P) (avoidingA N K Q)) ∧
    ∀ Q ∈ K, Q ≠ t →
      RestrictsToZeroAlong {X | OnLocus N S X} (residueHyperplane N S P) (avoidingB N K Q) :=
  ⟨fun _ hQ hQb => avoidingA_restrictsToZero hN hE h hQ hQb,
    fun _ hQ hQt => avoidingB_restrictsToZero hN hE h hQ hQt⟩

/-! ## Chains, grouping, collapse and the class residue

Chains (`flank_class_members_form_chains`). The grouping identity (`grouping_identity`); its (b)
for one chord in rational form (`nlsmAvoiding_step`: `N^{¬K} = N^{¬(K ∪ C)} + a · b / X_C`, from the
library's numerator recursion `pkR_b_step` and the split of the odd-chord product at `C`,
`prod_oddDiagonals_avoiding`), its iterations top-down and bottom-up (`nlsmAvoiding_top`,
`nlsmAvoiding_bot`), the A-side expansion inside the A-side polygon of a member
(`childAmpA_expansion`, through the bridges `nlsmAvoiding_congr` and `nlsm_omega_relab`), the
identity at the generic point (`nlsm_collapse`) and the collapse identity on `L_S`
(`collapse_identity`). The value of the strip factor with a non-zero constant
(`strip_factor_value`, from `stripFactor_sub_const_restrictsToZero`), the children's amplitudes as
the full children (`avoidingB_top_eq`, `avoidingA_bottom_eq`) and the class residue
(`simple_pole_along_flank_class`). -/

-- registry: C-DPS3
/-- **Chains**. Let `K` be a set of odd chords with a top `t` and a bottom `b` (H4).
Two distinct members of `K` do not cross if and only if their odd-ended sides are strictly nested;
so the non-crossing subsets of `K` are the chains of `≻` (the subsets totally ordered by
inclusion of odd-ended sides). -/
theorem Combinatorics.Polygons.flank_class_members_form_chains {N : ℕ} {K : Finset (ℕ × ℕ)}
    {t b : ℕ × ℕ} (hK : K ⊆ oddDiagonals N) (htop : t ∈ K ∧ ∀ Q ∈ K, oddSide N Q ⊆ oddSide N t)
    (hbot : b ∈ K ∧ ∀ Q ∈ K, oddSide N b ⊆ oddSide N Q) :
    (∀ Q ∈ K, ∀ Q' ∈ K, Q ≠ Q' →
      (¬ Crosses Q Q' ↔ oddSide N Q ⊂ oddSide N Q' ∨ oddSide N Q' ⊂ oddSide N Q)) ∧
    ∀ D ⊆ K, (∀ Q ∈ D, ∀ Q' ∈ D, ¬ Crosses Q Q') ↔
      ∀ Q ∈ D, ∀ Q' ∈ D, oddSide N Q ⊆ oddSide N Q' ∨ oddSide N Q' ⊆ oddSide N Q := by
  have hch : ∀ Q ∈ K, ∀ Q' ∈ K,
      (¬ Crosses Q Q' ↔ (oddSide N Q ⊆ oddSide N Q' ∨ oddSide N Q' ⊆ oddSide N Q)) :=
    fun Q hQ Q' hQ' => pkR_b_chain (hK hbot.1) (hK htop.1) (hK hQ) (hK hQ') (hbot.2 Q hQ)
      (htop.2 Q hQ) (hbot.2 Q' hQ') (htop.2 Q' hQ')
  refine ⟨fun Q hQ Q' hQ' hne => ?_, fun D hD => ⟨fun h Q hQ Q' hQ' =>
    (hch Q (hD hQ) Q' (hD hQ')).1 (h Q hQ Q' hQ'), fun h Q hQ Q' hQ' =>
      (hch Q (hD hQ) Q' (hD hQ')).2 (h Q hQ Q' hQ')⟩⟩
  rw [hch Q hQ Q' hQ']
  have hsame : oddSide N Q = oddSide N Q' → Q = Q' := pkR_d2_eq_of_head (hK hQ) (hK hQ')
  constructor
  · rintro (h | h)
    · exact Or.inl (ssubset_of_subset_of_ne h fun e => hne (hsame e))
    · exact Or.inr (ssubset_of_subset_of_ne h fun e => hne (hsame e.symm))
  · rintro (h | h)
    · exact Or.inl h.subset
    · exact Or.inr h.subset

open MvPolynomial in
/-- Setting the variables of `K` to `1` in the odd-chord product of a relabelled child leaves the
odd chords of the child that do not pull back into `K`. -/
theorem rename_oddDen_avoiding (N s n : ℕ) (K : Finset (ℕ × ℕ)) :
    pkRBPsi ℚ (fun d => d ∈ K) (rename (relab N s) (oddDen ℚ n)) =
      rename (relab N s) (∏ d ∈ oddDiagonals n \ pkRBPull N s n K,
        (X d : MvPolynomial (ℕ × ℕ) ℚ)) := by
  rw [pkR_b_psi_rename, oddDen, map_prod]
  congr 1
  rw [← prod_filter_mul_prod_filter_not (oddDiagonals n) (fun d => relab N s d ∈ K)]
  have h1 : ∏ d ∈ (oddDiagonals n).filter (fun d => relab N s d ∈ K),
      pkRBPsi ℚ (fun d => relab N s d ∈ K) (X d : MvPolynomial (ℕ × ℕ) ℚ) = 1 :=
    prod_eq_one fun d hd => by rw [pkR_b_psi_X, ite_eq_left (mem_filter.1 hd).2]
  rw [h1, one_mul]
  have he : (oddDiagonals n).filter (fun d => ¬ relab N s d ∈ K) =
      oddDiagonals n \ pkRBPull N s n K := by
    ext d
    simp only [mem_filter, mem_sdiff, pkRBPull, oddDiagonals]
    tauto
  rw [he]
  exact prod_congr rfl fun d hd => by
    rw [pkR_b_psi_X, ite_eq_right fun h =>
      (mem_sdiff.1 hd).2 (mem_filter.2 ⟨(mem_filter.1 (mem_sdiff.1 hd).1).1, h⟩)]

open MvPolynomial in
/-- **The odd chords avoiding `K ∪ {C}`, split at `C`**: for an odd chord `C ∉ K` of the `N`-gon
(`N` even), the odd chords outside `K ∪ {C}` are those of the head child of `C`, those of its
tail child (each outside the pull-back of `K`) and the crossing chords of `C` outside `K`. -/
theorem prod_oddDiagonals_avoiding {N : ℕ} (hE : Even N) {C : ℕ × ℕ} (hC : C ∈ oddDiagonals N)
    (K : Finset (ℕ × ℕ)) :
    ∏ d ∈ oddDiagonals N \ insert C K, (X d : MvPolynomial (ℕ × ℕ) ℚ) =
      rename (relab N (headStart C)) (∏ d ∈ oddDiagonals (headLen N C + 1) \
          pkRBPull N (headStart C) (headLen N C + 1) K, (X d : MvPolynomial (ℕ × ℕ) ℚ)) *
        rename (relab N (tailStart C)) (∏ d ∈ oddDiagonals (tailLen N C + 1) \
          pkRBPull N (tailStart C) (tailLen N C + 1) K, (X d : MvPolynomial (ℕ × ℕ) ℚ)) *
        pkRBCross ℚ N K C := by
  have h := congrArg (pkRBPsi ℚ (fun d => d ∈ K)) (prod_oddDiagonals_erase hE hC)
  rw [pkR_b_psi_prod, map_mul, map_mul, rename_oddDen_avoiding, rename_oddDen_avoiding] at h
  have hl : (oddDiagonals N).erase C \ K = oddDiagonals N \ insert C K := by
    ext d
    simp only [mem_sdiff, mem_erase, mem_insert]
    tauto
  have hc : pkRBPsi ℚ (fun d => d ∈ K) (crossProd ℚ N C) = pkRBCross ℚ N K C :=
    pkR_b_psi_prod K _
  rw [hl, hc] at h
  rw [h]
  rcases pkR_b_head_data hC with ⟨h1, hs, hl⟩ | ⟨h1, hs, hl⟩ <;>
    rcases pkR_b_tail_data hC with ⟨h1', ts, tl⟩ | ⟨h1', ts, tl⟩
  · rw [hs, hl, ts, tl, show N - (C.2 - C.1) + 1 = N - C.2 + C.1 + 1 by
      have := mem_diagonals.1 (mem_filter.1 hC).1; omega]
    ring
  · omega
  · omega
  · rw [hs, hl, ts, tl, show N - (C.2 - C.1) + 1 = N - C.2 + C.1 + 1 by
      have := mem_diagonals.1 (mem_filter.1 hC).1; omega]
    ring

open MvPolynomial in
/-- The numerator lemma for a relabelled child, under a ring map into a field that keeps every
variable non-zero. -/
theorem nlsmAvoiding_child_hom {F : Type*} [Field F] (f : MvPolynomial (ℕ × ℕ) ℚ →+* F)
    (hf : ∀ d, f (X d) ≠ 0) (N s : ℕ) {n : ℕ} (hn : 2 ≤ n) (K : Finset (ℕ × ℕ)) :
    f (rename (relab N s) (pkRBNP ℚ n K)) =
      nlsmAvoiding n K (fun d => f (X (relab N s d))) *
        f (rename (relab N s) (∏ d ∈ oddDiagonals n \ K, (X d : MvPolynomial (ℕ × ℕ) ℚ))) := by
  have h := nlsmAvoiding_numerator_hom (f.comp (rename (relab N s)).toRingHom) hn K
    (fun d _ => by simpa using hf (relab N s d))
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, rename_X] at h
  rw [h, map_prod, map_prod]
  simp

open MvPolynomial in
-- registry: C-XKD2
/-- **One chord of the banned set, rational form** (the grouping identity (b) for one chord): for
even `N ≥ 4`, a set `K` of odd chords and an odd chord `C ∉ K`, at any point where no variable
vanishes (a ring map `f` into a field), `N^{¬K} = N^{¬(K ∪ C)} + a · b / X_C`, where `a` and `b` are
`N^{¬K}` of the head and tail children of `C` (the banned set pulled back). -/
theorem NLSM.Amplitude.nlsmAvoiding_step {F : Type*} [Field F] (f : MvPolynomial (ℕ × ℕ) ℚ →+* F)
    (hf : ∀ d, f (X d) ≠ 0) {N : ℕ} (hN : 4 ≤ N) (hE : Even N) {K : Finset (ℕ × ℕ)}
    {C : ℕ × ℕ} (hK : insert C K ⊆ oddDiagonals N) (hC : C ∉ K) :
    nlsmAvoiding N K (fun d => f (X d)) = nlsmAvoiding N (insert C K) (fun d => f (X d)) +
      nlsmAvoiding (headLen N C + 1) (pkRBPull N (headStart C) (headLen N C + 1) K)
          (fun d => f (X (relab N (headStart C) d))) *
        nlsmAvoiding (tailLen N C + 1) (pkRBPull N (tailStart C) (tailLen N C + 1) K)
          (fun d => f (X (relab N (tailStart C) d))) / f (X C) := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  have hCo : C ∈ oddDiagonals N := hK (mem_insert_self C K)
  have f1 := pkR_b_head_facts hE' hCo
  have htl : tailLen N C = N - headLen N C := rfl
  have hstep := congrArg f (pkR_b_step (R := ℚ) hN hE' hK hC)
  unfold pkRBTerm at hstep
  rw [
    nlsmAvoiding_numerator_hom f (by omega) K (fun d _ => hf d), map_add, map_mul, map_mul,
    map_mul, nlsmAvoiding_numerator_hom f (by omega) (insert C K) (fun d _ => hf d),
    nlsmAvoiding_child_hom f hf N (headStart C) (by omega),
    nlsmAvoiding_child_hom f hf N (tailStart C) (by omega)] at hstep
  have hsplit : oddDiagonals N \ K = insert C (oddDiagonals N \ insert C K) := by
    ext d
    simp only [mem_sdiff, mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h : d = C
      · exact Or.inl h
      · exact Or.inr ⟨h1, fun h' => h'.elim h h2⟩
    · rintro (h | ⟨h1, h2⟩)
      · exact h ▸ ⟨hCo, hC⟩
      · exact ⟨h1, fun h => h2 (Or.inr h)⟩
  have hnot : C ∉ oddDiagonals N \ insert C K := fun h => (mem_sdiff.1 h).2 (mem_insert_self C K)
  have hfac := congrArg f (prod_oddDiagonals_avoiding hE hCo K)
  rw [map_prod, map_mul, map_mul] at hfac
  rw [hsplit, prod_insert hnot, hfac] at hstep
  set A := nlsmAvoiding N K (fun d => f (X d))
  set B := nlsmAvoiding N (insert C K) (fun d => f (X d))
  set a := nlsmAvoiding (headLen N C + 1) (pkRBPull N (headStart C) (headLen N C + 1) K)
    (fun d => f (X (relab N (headStart C) d)))
  set b := nlsmAvoiding (tailLen N C + 1) (pkRBPull N (tailStart C) (tailLen N C + 1) K)
    (fun d => f (X (relab N (tailStart C) d)))
  set DA := f (rename (relab N (headStart C)) (∏ d ∈ oddDiagonals (headLen N C + 1) \
      pkRBPull N (headStart C) (headLen N C + 1) K, (X d : MvPolynomial (ℕ × ℕ) ℚ)))
  set DB := f (rename (relab N (tailStart C)) (∏ d ∈ oddDiagonals (tailLen N C + 1) \
      pkRBPull N (tailStart C) (tailLen N C + 1) K, (X d : MvPolynomial (ℕ × ℕ) ℚ)))
  have hDA : DA ≠ 0 := by
    simp only [DA, map_prod]; exact prod_ne_zero_iff.2 fun d _ => by simpa using hf _
  have hDB : DB ≠ 0 := by
    simp only [DB, map_prod]; exact prod_ne_zero_iff.2 fun d _ => by simpa using hf _
  have hcr : f (pkRBCross ℚ N K C) ≠ 0 := by
    unfold pkRBCross; rw [map_prod]; exact prod_ne_zero_iff.2 fun d _ => hf d
  have h2 : A * f (X C) = f (X C) * B + a * b :=
    mul_right_cancel₀ (mul_ne_zero (mul_ne_zero hDA hDB) hcr) (by linear_combination hstep)
  have hXC := hf C
  field_simp
  linear_combination h2

open MvPolynomial in
-- registry: C-XKD2
/-- **The grouping identity**, the one-chord recursion (the general sums over non-crossing sets
are not part of it). Let `n ≥ 4` be even and `K` a set of
odd chords of the `n`-gon (a sub-polygon is read through its relabelling, `nlsmAvoiding_step`).
(a) `A^{¬K}_n(X + δ v₀) = O(δ^{−(n−2)})` (the coefficients of `δ^{−j}`, `j < n − 2`, vanish), and
the only denominators of `N^{¬K}_n` are the odd diagonals outside `K`, each simple
(`N^{¬K}_n · ∏_{P odd ∉ K} X_P` is a polynomial). (b) For an odd chord `C ∉ K`,
`N^{¬K} = N^{¬(K ∪ C)} + N^{¬K}_A · N^{¬K}_B / X_C`, `A` and `B` the sub-polygons cut off by `C`
(its odd-ended and even-ended side, each closed by `C`, `K` read in each); for `K = ∅`,
`N = N^{¬C} + N_A · N_B / X_C`. All as rational functions (the generic point). -/
theorem NLSM.Amplitude.grouping_identity {n : ℕ} (hn : 4 ≤ n) (hE : Even n) {K : Finset (ℕ × ℕ)}
    (hK : K ⊆ oddDiagonals n) :
    (∀ j : ℤ, j < (n : ℤ) - 2 → (ampAvoiding n K (shifted gen)).coeff j = 0) ∧
    (∃ P : MvPolynomial (ℕ × ℕ) ℚ,
      nlsmAvoiding n K gen * ∏ d ∈ oddDiagonals n \ K, gen d = algebraMap _ RF P) ∧
    (∀ C ∈ oddDiagonals n, C ∉ K → nlsmAvoiding n K gen = nlsmAvoiding n (insert C K) gen +
      avoidingA n K C * avoidingB n K C / gen C) ∧
    ∀ C ∈ oddDiagonals n,
      NLSM n gen = nlsmAvoiding n {C} gen + childAmpA n C * childAmpB n C / gen C := by
  have hE' : n % 2 = 0 := Nat.even_iff.1 hE
  have hg : ∀ d, (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) RF) (X d) = gen d := fun _ => rfl
  refine ⟨fun j hj => ?_, ⟨pkRBNP ℚ n K, ?_⟩, fun C hC hCK => ?_, fun C hC => ?_⟩
  · rcases lt_or_ge j 0 with h | h
    · rw [ampAvoiding_shifted, HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_of_notMem_range]
      simp only [Set.mem_range, not_exists]
      intro k e
      have : (0 : ℤ) ≤ j := by rw [← e]; simp
      omega
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    have e := ampAvoiding_coeff_numerator_hom (algebraMap _ RF) n m K
      (fun d _ => gen_ne_zero d)
    rw [pkR_b_low n hn hE' K hK m (by omega), map_zero] at e
    exact (mul_eq_zero.1 e.symm).resolve_right (prod_ne_zero_iff.2 fun d _ => gen_ne_zero d)
  · have e := nlsmAvoiding_numerator_hom (algebraMap _ RF) (n := n) (by omega) K
      (fun d _ => gen_ne_zero d)
    exact e.symm
  · have h := nlsmAvoiding_step (algebraMap _ RF) (fun d => gen_ne_zero d) hn hE
      (insert_subset hC hK) hCK
    exact h
  · have h := nlsmAvoiding_step (algebraMap _ RF) (fun d => gen_ne_zero d) hn hE
      (insert_subset hC (empty_subset _)) (Finset.notMem_empty C)
    rw [nlsmAvoiding_empty, pkR_b_pull_empty, pkR_b_pull_empty, nlsmAvoiding_empty,
      nlsmAvoiding_empty, insert_empty_eq] at h
    exact h

open MvPolynomial in
/-- **Top-down peeling, rational form**: for even `N ≥ 4`, a set `K` of odd chords whose
non-crossing members are nested, and a down-closed `R ⊆ K`, at any point where no variable
vanishes, `N^{¬(K∖R)} = N^{¬K} + Σ_{Q ∈ R} a_Q · N_{A(Q)} / X_Q`: `a_Q` is `N^{¬K}` of the tail
child of `Q`, `N_{A(Q)}` the full amplitude of its head child. -/
theorem nlsmAvoiding_top {F : Type*} [Field F] (f : MvPolynomial (ℕ × ℕ) ℚ →+* F)
    (hf : ∀ d, f (X d) ≠ 0) {N : ℕ} (hN : 4 ≤ N) (hE : Even N) {K : Finset (ℕ × ℕ)}
    (hK : K ⊆ oddDiagonals N)
    (hnc : ∀ Q ∈ K, ∀ Q' ∈ K, ¬ Crosses Q' Q → oddSide N Q ⊆ oddSide N Q' ∨
        oddSide N Q' ⊆ oddSide N Q)
    (R : Finset (ℕ × ℕ)) (hRK : R ⊆ K)
    (hdown : ∀ Q ∈ R, ∀ Q' ∈ K, oddSide N Q' ⊆ oddSide N Q → Q' ∈ R) :
    nlsmAvoiding N (K \ R) (fun d => f (X d)) = nlsmAvoiding N K (fun d => f (X d)) +
      ∑ Q ∈ R, nlsmAvoiding (tailLen N Q + 1) (pkRBPull N (tailStart Q) (tailLen N Q + 1) K)
          (fun d => f (X (relab N (tailStart Q) d))) *
        NLSM (headLen N Q + 1) (fun d => f (X (relab N (headStart Q) d))) / f (X Q) := by
  induction R using Finset.strongInduction with
  | H R ih =>
  rcases R.eq_empty_or_nonempty with hR | hR
  · subst hR
    rw [sdiff_empty, sum_empty, add_zero]
  obtain ⟨Q, hQR, hmax⟩ := exists_max_image R (fun Q => (oddSide N Q).card) hR
  have hQK := hRK hQR
  have hQo := hK hQK
  have hsame : ∀ Q' ∈ R, oddSide N Q ⊆ oddSide N Q' → Q' = Q := fun Q' hQ' hs =>
    (pkR_d2_eq_of_head hQo (hK (hRK hQ')) (eq_of_subset_of_card_le hs (hmax Q' hQ'))).symm
  have hR'K : R.erase Q ⊆ K := (erase_subset Q R).trans hRK
  have hdown' : ∀ Q₁ ∈ R.erase Q, ∀ Q' ∈ K, oddSide N Q' ⊆ oddSide N Q₁ → Q' ∈ R.erase Q := by
    intro Q₁ hQ₁ Q' hQ' hs
    have hQ₁R := mem_of_mem_erase hQ₁
    refine mem_erase.2 ⟨fun h => ?_, hdown Q₁ hQ₁R Q' hQ' hs⟩
    rw [h] at hs
    exact ne_of_mem_erase hQ₁ (hsame Q₁ hQ₁R hs)
  have hQn : Q ∉ K \ R := fun h => (mem_sdiff.1 h).2 hQR
  have hins : insert Q (K \ R) ⊆ oddDiagonals N := by
    intro d hd
    rcases mem_insert.1 hd with h | h
    · rw [h]
      exact hQo
    · exact hK (mem_sdiff.1 h).1
  have heq : insert Q (K \ R) = K \ R.erase Q := by
    ext d
    simp only [mem_insert, mem_sdiff, mem_erase]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · rw [h]
        exact ⟨hQK, fun h' => h'.1 rfl⟩
      · exact ⟨h1, fun h' => h2 h'.2⟩
    · rintro ⟨h1, h2⟩
      by_cases hdQ : d = Q
      · exact Or.inl hdQ
      · exact Or.inr ⟨h1, fun h => h2 ⟨hdQ, h⟩⟩
  have hpullH : pkRBPull N (headStart Q) (headLen N Q + 1) (K \ R) = ∅ := by
    refine pkR_d2_pull_head hQo (fun d hd => hK (mem_sdiff.1 hd).1) fun Q' hQ' => ?_
    obtain ⟨hQ'K, hQ'R⟩ := mem_sdiff.1 hQ'
    by_cases hc : Crosses Q' Q
    · exact Or.inr hc
    · rcases hnc Q hQK Q' hQ'K hc with h | h
      · exact Or.inl h
      · exact absurd (hdown Q hQR Q' hQ'K h) hQ'R
  have hpullT : pkRBPull N (tailStart Q) (tailLen N Q + 1) (K \ R) =
      pkRBPull N (tailStart Q) (tailLen N Q + 1) K := by
    refine (pkR_b_pull_mono sdiff_subset ?_).symm
    rw [Finset.sdiff_sdiff_eq_self hRK]
    refine pkR_d2_pull_tail hQo (fun d hd => hK (hRK hd)) fun Q' hQ' => ?_
    by_cases hc : Crosses Q' Q
    · exact Or.inr hc
    · rcases hnc Q hQK Q' (hRK hQ') hc with h | h
      · rw [hsame Q' hQ' h]
        exact Or.inl subset_rfl
      · exact Or.inl h
  rw [nlsmAvoiding_step f hf hN hE hins hQn, heq, ih (R.erase Q) (erase_ssubset hQR) hR'K hdown',
    hpullH, hpullT, nlsmAvoiding_empty, ← add_sum_erase R _ hQR]
  ring

open MvPolynomial in
/-- **Bottom-up peeling, rational form** (the mirror of `nlsmAvoiding_top`): for an up-closed
`R ⊆ K`, `N^{¬(K∖R)} = N^{¬K} + Σ_{Q ∈ R} b_Q · N_{B(Q)} / X_Q`, `b_Q` the part avoiding `K` of
the head child of `Q` and `N_{B(Q)}` the full amplitude of its tail child. -/
theorem nlsmAvoiding_bot {F : Type*} [Field F] (f : MvPolynomial (ℕ × ℕ) ℚ →+* F)
    (hf : ∀ d, f (X d) ≠ 0) {N : ℕ} (hN : 4 ≤ N) (hE : Even N) {K : Finset (ℕ × ℕ)}
    (hK : K ⊆ oddDiagonals N)
    (hnc : ∀ Q ∈ K, ∀ Q' ∈ K, ¬ Crosses Q' Q → oddSide N Q ⊆ oddSide N Q' ∨
        oddSide N Q' ⊆ oddSide N Q)
    (R : Finset (ℕ × ℕ)) (hRK : R ⊆ K)
    (hup : ∀ Q ∈ R, ∀ Q' ∈ K, oddSide N Q ⊆ oddSide N Q' → Q' ∈ R) :
    nlsmAvoiding N (K \ R) (fun d => f (X d)) = nlsmAvoiding N K (fun d => f (X d)) +
      ∑ Q ∈ R, nlsmAvoiding (headLen N Q + 1) (pkRBPull N (headStart Q) (headLen N Q + 1) K)
          (fun d => f (X (relab N (headStart Q) d))) *
        NLSM (tailLen N Q + 1) (fun d => f (X (relab N (tailStart Q) d))) / f (X Q) := by
  induction R using Finset.strongInduction with
  | H R ih =>
  rcases R.eq_empty_or_nonempty with hR | hR
  · subst hR
    rw [sdiff_empty, sum_empty, add_zero]
  obtain ⟨Q, hQR, hmin⟩ := exists_min_image R (fun Q => (oddSide N Q).card) hR
  have hQK := hRK hQR
  have hQo := hK hQK
  have hsame : ∀ Q' ∈ R, oddSide N Q' ⊆ oddSide N Q → Q' = Q := fun Q' hQ' hs =>
    pkR_d2_eq_of_head (hK (hRK hQ')) hQo (eq_of_subset_of_card_le hs (hmin Q' hQ'))
  have hR'K : R.erase Q ⊆ K := (erase_subset Q R).trans hRK
  have hup' : ∀ Q₁ ∈ R.erase Q, ∀ Q' ∈ K, oddSide N Q₁ ⊆ oddSide N Q' → Q' ∈ R.erase Q := by
    intro Q₁ hQ₁ Q' hQ' hs
    have hQ₁R := mem_of_mem_erase hQ₁
    refine mem_erase.2 ⟨fun h => ?_, hup Q₁ hQ₁R Q' hQ' hs⟩
    rw [h] at hs
    exact ne_of_mem_erase hQ₁ (hsame Q₁ hQ₁R hs)
  have hQn : Q ∉ K \ R := fun h => (mem_sdiff.1 h).2 hQR
  have hins : insert Q (K \ R) ⊆ oddDiagonals N := by
    intro d hd
    rcases mem_insert.1 hd with h | h
    · rw [h]
      exact hQo
    · exact hK (mem_sdiff.1 h).1
  have heq : insert Q (K \ R) = K \ R.erase Q := by
    ext d
    simp only [mem_insert, mem_sdiff, mem_erase]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · rw [h]
        exact ⟨hQK, fun h' => h'.1 rfl⟩
      · exact ⟨h1, fun h' => h2 h'.2⟩
    · rintro ⟨h1, h2⟩
      by_cases hdQ : d = Q
      · exact Or.inl hdQ
      · exact Or.inr ⟨h1, fun h => h2 ⟨hdQ, h⟩⟩
  have hpullT : pkRBPull N (tailStart Q) (tailLen N Q + 1) (K \ R) = ∅ := by
    refine pkR_d2_pull_tail hQo (fun d hd => hK (mem_sdiff.1 hd).1) fun Q' hQ' => ?_
    obtain ⟨hQ'K, hQ'R⟩ := mem_sdiff.1 hQ'
    by_cases hc : Crosses Q' Q
    · exact Or.inr hc
    · rcases hnc Q hQK Q' hQ'K hc with h | h
      · exact absurd (hup Q hQR Q' hQ'K h) hQ'R
      · exact Or.inl h
  have hpullH : pkRBPull N (headStart Q) (headLen N Q + 1) (K \ R) =
      pkRBPull N (headStart Q) (headLen N Q + 1) K := by
    refine (pkR_b_pull_mono sdiff_subset ?_).symm
    rw [Finset.sdiff_sdiff_eq_self hRK]
    refine pkR_d2_pull_head hQo (fun d hd => hK (hRK hd)) fun Q' hQ' => ?_
    by_cases hc : Crosses Q' Q
    · exact Or.inr hc
    · rcases hnc Q hQK Q' (hRK hQ') hc with h | h
      · exact Or.inl h
      · rw [hsame Q' hQ' h]
        exact Or.inl subset_rfl
  rw [nlsmAvoiding_step f hf hN hE hins hQn, heq, ih (R.erase Q) (erase_ssubset hQR) hR'K hup',
    hpullH, hpullT, nlsmAvoiding_empty, ← add_sum_erase R _ hQR]
  ring

/-- `N^{¬K}_n` reads its point only at the diagonals of the `n`-gon. -/
theorem nlsmAvoiding_congr {F : Type*} [Field F] {n : ℕ} (K : Finset (ℕ × ℕ))
    {X Y : ℕ × ℕ → F} (h : ∀ d ∈ diagonals n, X d = Y d) :
    nlsmAvoiding n K X = nlsmAvoiding n K Y := by
  unfold nlsmAvoiding ampAvoiding
  congr 1
  refine sum_congr rfl fun T hT => prod_congr rfl fun d hd => ?_
  have hd' := (mem_triangulations.1 (mem_filter.1 hT).1).1 hd
  simp only [shifted, h d hd']

/-- `NLSM_n` reads its point only at the diagonals of the `n`-gon (over any field;
`pkG_nlsm_congr` of `C5` over `ℚ`). -/
theorem nlsm_congr {F : Type*} [Field F] {n : ℕ} {X Y : ℕ × ℕ → F}
    (h : ∀ d ∈ diagonals n, X d = Y d) : NLSM n X = NLSM n Y := by
  rw [← nlsmAvoiding_empty, ← nlsmAvoiding_empty, nlsmAvoiding_congr ∅ h]

/-- A relabelled child chord is read at the sub-polygon point of the child's vertex list (over any
field; `pkR_b_relab_subX` of `C9` over `ℚ`). -/
theorem relab_eq_subX {F : Type*} [Field F] {N s n : ℕ} (hs : 1 ≤ s ∧ s ≤ N) (hn : n ≤ N)
    (X : ℕ × ℕ → F) {d : ℕ × ℕ} (hd : d ∈ diagonals n) :
    X (relab N s d) = pkRSubX N (fun k => vtx N (k + s - 1)) X d := by
  rw [pkR_subX_relab (by omega) s X d, ite_eq_left (pkR_b_relab_mem hs hn hd)]

/-- A sub-polygon point at a relabelled pair is the sub-polygon point of the composed list (over
any field; `pkR_b_subX_relab` of `C9` over `ℚ`). -/
theorem subX_at_relab {F : Type*} [Field F] {N n s : ℕ} (g : ℕ → ℕ) (X : ℕ × ℕ → F) (d : ℕ × ℕ) :
    pkRSubX N g X (relab n s d) = pkRSubX N (fun k => g (vtx n (k + s - 1))) X d := by
  change planar N X (g (relab n s d).1) (g (relab n s d).2) =
    planar N X (g (vtx n (d.1 + s - 1))) (g (vtx n (d.2 + s - 1)))
  have e : relab n s d = (min (vtx n (d.1 + s - 1)) (vtx n (d.2 + s - 1)),
      max (vtx n (d.1 + s - 1)) (vtx n (d.2 + s - 1))) := rfl
  rw [e]
  dsimp only
  rcases le_total (vtx n (d.1 + s - 1)) (vtx n (d.2 + s - 1)) with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, pkR_planar_comm]

/-- A sub-polygon point read through `rot m` is that of the list shifted by one child leg (over
any field; `pkR_b_subX_rot` of `C8` over `ℚ`). -/
theorem subX_rot {F : Type*} [Field F] {N m : ℕ} (f : ℕ → ℕ) (X : ℕ × ℕ → F) :
    (fun d => pkRSubX N f X (rot m d)) = pkRSubX N (fun j => f (vtx m (j + 1))) X := by
  funext d
  change planar N X (f (rot m d).1) (f (rot m d).2) = planar N X (f (vtx m (d.1 + 1)))
      (f (vtx m (d.2 + 1)))
  have e : rot m d =
      (min (vtx m (d.1 + 1)) (vtx m (d.2 + 1)), max (vtx m (d.1 + 1)) (vtx m (d.2 + 1))) := rfl
  rw [e]
  dsimp only
  rcases le_total (vtx m (d.1 + 1)) (vtx m (d.2 + 1)) with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, pkR_planar_comm]

/-- **A rotated vertex list gives the same `NLSM`** (over any field; the rational form of
`pkR_b_NP_subX_rot` of `C8`): for even `m ≥ 4`, reading the list `f` from child leg `r + 1` on
does not change `NLSM_m` at the sub-polygon point. -/
theorem nlsm_subX_rot {F : Type*} [Field F] {N m : ℕ} (hm : 4 ≤ m) (hE : m % 2 = 0)
    (f : ℕ → ℕ) (X : ℕ × ℕ → F) (r : ℕ) :
    NLSM m (pkRSubX N (fun j => f (vtx m (j + r))) X) = NLSM m (pkRSubX N f X) := by
  have hm1 : 1 ≤ m := by omega
  induction r with
  | zero =>
    refine nlsm_congr fun d hd => ?_
    have hdd := mem_diagonals.1 hd
    change planar N X (f (vtx m (d.1 + 0))) (f (vtx m (d.2 + 0))) = planar N X (f d.1) (f d.2)
    rw [Nat.add_zero, Nat.add_zero, vtx_of_mem (show 1 ≤ d.1 by omega) (show d.1 ≤ m by omega),
      vtx_of_mem (show 1 ≤ d.2 by omega) (show d.2 ≤ m by omega)]
  | succ r ih =>
    have e := subX_rot (N := N) (m := m) (fun j => f (vtx m (j + r))) X
    have h : pkRSubX N (fun j => (fun j => f (vtx m (j + r))) (vtx m (j + 1))) X =
        pkRSubX N (fun j => f (vtx m (j + (r + 1)))) X := by
      congr 1
      funext j
      change f (vtx m (vtx m (j + 1) + r)) = f (vtx m (j + (r + 1)))
      rw [pkR_b_vtx_add hm1, show j + 1 + r = j + (r + 1) by omega]
    rw [← (e.trans h)]
    exact (NLSM_rot hm hE (pkRSubX N (fun j => f (vtx m (j + r))) X)).trans ih

/-- **The Ω bridge, rational form** (`pkR_b_omega_relab` of `C9` for `NLSM` over any field):
inside the head child of a chord (base `a`, `L + 1` legs), the tail child of the child chord
`(p + 1, p + L′ + 1)`, read in the parent, is the region `pkRBOmL N a p L′`. -/
theorem nlsm_omega_relab {F : Type*} [Field F] {N a p L L' : ℕ} (ha : 1 ≤ a ∧ a ≤ N)
    (hp : p % 2 = 0) (hL : L % 2 = 1) (hL' : L' % 2 = 1) (hpL : p + L' ≤ L) (hLL : L' + 2 ≤ L)
    (hLN : L + 1 ≤ N) (X : ℕ × ℕ → F) :
    NLSM (L - L' + 2) (fun d => X (relab N a (relab (L + 1) (p + L' + 1) d))) =
      NLSM (L - L' + 2) (pkRSubX N (pkRBOmL N a p L') X) := by
  rw [← nlsm_subX_rot (N := N) (m := L - L' + 2) (by omega) (by omega) (pkRBOmL N a p L') X
    (p + 1)]
  refine nlsm_congr fun d hd => ?_
  have hdd := mem_diagonals.1 hd
  have he := pkR_b_relab_mem (N := L + 1) (s := p + L' + 1) (n := L - L' + 2) ⟨by omega, by omega⟩
      (by omega) hd
  rw [relab_eq_subX ha hLN X he, subX_at_relab]
  change planar N X (vtx N (vtx (L + 1) (d.1 + (p + L' + 1) - 1) + a - 1))
      (vtx N (vtx (L + 1) (d.2 + (p + L' + 1) - 1) + a - 1)) =
    planar N X (vtx N (a + pkRBOlo p L' (vtx (L - L' + 2) (d.1 + (p + 1)))))
      (vtx N (a + pkRBOlo p L' (vtx (L - L' + 2) (d.2 + (p + 1)))))
  rw [pkR_b_om_rot_pos (k := d.1) (by omega) hpL ⟨by omega, by omega⟩ a,
    pkR_b_om_rot_pos (k := d.2) (by omega) hpL ⟨by omega, by omega⟩ a]

open MvPolynomial in
-- registry: C-60WX
/-- **The A-side expansion, rational form**: for even `N`, a set `K` of odd chords whose
non-crossing members are nested and whose odd-ended sides `A_c` share a leg `ℓ`, and `Q ∈ K`, the
full amplitude of the head child of `Q` is `b_Q + Σ_{c below Q} b_c · N_{Ω(Q,c)} / X_c`
(the grouping identity (b) inside the A-side polygon of `Q`, its `K`-diagonals being the members
below `Q`). -/
theorem NLSM.Amplitude.childAmpA_expansion {N : ℕ} (hE : Even N) {K : Finset (ℕ × ℕ)}
    (hK : K ⊆ oddDiagonals N)
    (hnc : ∀ Q ∈ K, ∀ Q' ∈ K, ¬ Crosses Q' Q → oddSide N Q ⊆ oddSide N Q' ∨
        oddSide N Q' ⊆ oddSide N Q)
    {ℓ : ℕ} (hℓ : ∀ c ∈ K, ℓ ∈ oddSide N c) {Q : ℕ × ℕ} (hQK : Q ∈ K) :
    childAmpA N Q = avoidingA N K Q +
      ∑ c ∈ pkRD2Below N K Q, avoidingA N K c * regionAmp N Q c / gen c := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  have hQo := hK hQK
  have f1 := pkR_b_head_facts hE' hQo
  have hKQK : pkRD2Below N K Q ⊆ K := filter_subset _ _
  have hKQ : ∀ c ∈ pkRD2Below N K Q, c ≠ Q ∧ oddSide N c ⊆ oddSide N Q :=
      fun c hc => (mem_filter.1 hc).2
  have np := fun c (hc : c ∈ pkRD2Below N K Q) =>
    pkR_b_nest_pos hE' hQo (hK (hKQK hc)) (hKQ c hc).2 (hKQ c hc).1.symm
  have fc := fun c (hc : c ∈ pkRD2Below N K Q) => pkR_b_head_facts hE' (hK (hKQK hc))
  have hrel : ∀ c ∈ pkRD2Below N K Q, relab N (headStart Q) (pkRBCc N Q c) = c := by
    intro c hc
    obtain ⟨a1, a2, a3, -⟩ := np c hc
    exact pkR_b_relab_head (hK (hKQK hc)) ⟨f1.1, f1.2.1⟩ (by omega)
      (pkR_b_vtx_cyc ⟨f1.1, f1.2.1⟩ ⟨(fc c hc).1, (fc c hc).2.1⟩)
  have hC' : ∀ c ∈ pkRD2Below N K Q, pkRBCc N Q c ∈ oddDiagonals (headLen N Q + 1) := by
    intro c hc
    obtain ⟨a1, a2, a3, -⟩ := np c hc
    have b := fc c hc
    exact pkR_b_odd_iff.2 ⟨by omega, by omega, by omega, by omega, by omega⟩
  have hS : ∀ c ∈ pkRD2Below N K Q, oddSide (headLen N Q + 1) (pkRBCc N Q c) =
      Icc (cycPos N (headStart Q) (headStart c) + 1)
          (cycPos N (headStart Q) (headStart c) + headLen N c) :=
    fun c hc => pkR_b_oS1 (np c hc).1
  have hinj : Set.InjOn (pkRBCc N Q) ↑(pkRD2Below N K Q) := fun c hc c' hc' e =>
    (hrel c hc).symm.trans ((congrArg (relab N (headStart Q)) e).trans (hrel c' hc'))
  have hKcI : pkRBPull N (headStart Q) (headLen N Q + 1) K =
      (pkRD2Below N K Q).image (pkRBCc N Q) := by
    have h1 : pkRBPull N (headStart Q) (headLen N Q + 1) K =
        pkRBPull N (headStart Q) (headLen N Q + 1) (pkRD2Below N K Q) := by
      refine pkR_b_pull_mono hKQK (pkR_d2_pull_head hQo (fun d hd =>
          hK (mem_sdiff.1 hd).1) fun Q' hQ' => ?_)
      obtain ⟨hQ'K, hQ'n⟩ := mem_sdiff.1 hQ'
      by_cases hc : Crosses Q' Q
      · exact Or.inr hc
      · rcases hnc Q hQK Q' hQ'K hc with h | h
        · exact Or.inl h
        · by_cases he : Q' = Q
          · rw [he]
            exact Or.inl subset_rfl
          · exact absurd (mem_filter.2 ⟨hQ'K, he, h⟩) hQ'n
    rw [h1, pkR_b_pull_head hE' hQo (fun d hd => hK (hKQK hd)) (fun d hd => (hKQ d hd).2),
      erase_eq_self.2 (fun h => (hKQ Q h).1 rfl)]
    rfl
  have hKco : pkRBPull N (headStart Q) (headLen N Q + 1) K ⊆ oddDiagonals (headLen N Q + 1) := by
    rw [hKcI]
    intro d hd
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hd
    exact hC' c hc
  have hncc : ∀ d ∈ pkRBPull N (headStart Q) (headLen N Q + 1) K,
      ∀ d' ∈ pkRBPull N (headStart Q) (headLen N Q + 1) K, ¬ Crosses d' d →
        oddSide (headLen N Q + 1) d ⊆ oddSide (headLen N Q + 1) d' ∨
          oddSide (headLen N Q + 1) d' ⊆ oddSide (headLen N Q + 1) d := by
    rw [hKcI]
    intro d hd d' hd' hcr
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hd
    obtain ⟨c', hc', rfl⟩ := mem_image.1 hd'
    obtain ⟨a1, a2, a3, a4⟩ := np c hc
    obtain ⟨b1, b2, b3, b4⟩ := np c' hc'
    have hb := pkR_d2_side_bd hQo ((hKQ c hc).2 (hℓ c (hKQK hc)))
    have hi : cycPos N (headStart Q) ℓ < N := Nat.mod_lt _ (by omega)
    have hv := pkR_b_vtx_cyc (N := N) (s := headStart Q) (x := ℓ) ⟨f1.1, f1.2.1⟩ hb
    have i1 := (a4 _ hi).1 (by rw [hv]; exact hℓ c (hKQK hc))
    have i2 := (b4 _ hi).1 (by rw [hv]; exact hℓ c' (hKQK hc'))
    rw [hS c hc, hS c' hc']
    have e : ∀ c₀, pkRBCc N Q c₀ = (cycPos N (headStart Q) (headStart c₀) + 1,
        cycPos N (headStart Q) (headStart c₀) + headLen N c₀ + 1) := fun _ => rfl
    rw [e c, e c'] at hcr
    unfold Crosses at hcr
    dsimp only at hcr
    have fcc := fc c hc
    have fcc' := fc c' hc'
    by_cases h : cycPos N (headStart Q) (headStart c') ≤ cycPos N (headStart Q) (headStart c) ∧
        cycPos N (headStart Q) (headStart c) + headLen N c ≤ cycPos N (headStart Q)
            (headStart c') + headLen N c'
    · exact Or.inl (Icc_subset_Icc (by omega) (by omega))
    · exact Or.inr (Icc_subset_Icc (by omega) (by omega))
  -- the bottom-up peeling inside the head child of `Q`
  set f : MvPolynomial (ℕ × ℕ) ℚ →+* RF :=
    (algebraMap _ RF).comp (rename (relab N (headStart Q))).toRingHom with hf
  have hfX : ∀ e, f (X e) = gen (relab N (headStart Q) e) := fun e => by
    simp [hf, gen]
  have hbot := nlsmAvoiding_bot f (fun e => by rw [hfX]; exact gen_ne_zero _)
    (N := headLen N Q + 1) (by omega) (Nat.even_iff.2 (by omega)) hKco hncc
    (pkRBPull N (headStart Q) (headLen N Q + 1) K) subset_rfl (fun d hd d' hd' _ => hd')
  simp only [hfX] at hbot
  rw [Finset.sdiff_self, nlsmAvoiding_empty] at hbot
  unfold childAmpA avoidingA
  rw [hbot]
  refine congrArg₂ (· + ·) rfl ((sum_congr hKcI fun _ _ => rfl).trans ?_)
  rw [sum_image hinj]
  refine sum_congr rfl fun c hc => ?_
  obtain ⟨a1, a2, a3, -⟩ := np c hc
  have fci := fc c hc
  have hd := pkR_b_cc_data (n := headLen N Q + 1) Q c a1
  rw [hrel c hc, hd.1, hd.2.1, hd.2.2.1, hd.2.2.2,
    pkR_b_pull_comp (N := N) (s := headStart Q) (n := headLen N Q + 1)
      (p := cycPos N (headStart Q) (headStart c)) (L' := headLen N c) ⟨f1.1, f1.2.1⟩ (by omega)
      (by omega) (by omega),
    pkR_b_vtx_cyc ⟨f1.1, f1.2.1⟩ ⟨fci.1, fci.2.1⟩]
  have e1 : nlsmAvoiding (headLen N c + 1) (pkRBPull N (headStart c) (headLen N c + 1) K)
      (fun d => gen (relab N (headStart Q) (relab (headLen N Q + 1)
        (cycPos N (headStart Q) (headStart c) + 1) d))) = avoidingA N K c := by
    refine nlsmAvoiding_congr _ fun d hd' => ?_
    have hdd := mem_diagonals.1 hd'
    rw [pkR_b_relab_comp (N := N) (s := headStart Q) (n := headLen N Q + 1)
      (p := cycPos N (headStart Q) (headStart c)) (d := d) ⟨f1.1, f1.2.1⟩ (by omega)
          (by omega) (by omega),
      pkR_b_vtx_cyc ⟨f1.1, f1.2.1⟩ ⟨fci.1, fci.2.1⟩]
  have e2 : NLSM (headLen N Q + 1 - headLen N c + 1)
      (fun d => gen (relab N (headStart Q) (relab (headLen N Q + 1)
        (cycPos N (headStart Q) (headStart c) + headLen N c + 1) d))) = regionAmp N Q c := by
    rw [show headLen N Q + 1 - headLen N c + 1 = headLen N Q - headLen N c + 2 by omega]
    exact nlsm_omega_relab (N := N) (a := headStart Q) (p := cycPos N (headStart Q) (headStart c))
      ⟨f1.1, f1.2.1⟩ a1 f1.2.2.2.1 fci.2.2.2.1 (by omega) (by omega) (by omega) gen
  rw [e1, e2]
  rfl

open MvPolynomial in
-- registry: C-60WX
/-- **`N_N` through the parts avoiding `K`** (generic: every variable its own indeterminate): for
even `N ≥ 4`, a set `K` of odd chords whose non-crossing members are nested and whose odd-ended
sides share a leg,
`NLSM_N = N^{¬K} + Σ_{Q ∈ K} a_Q · (b_Q + Σ_{c below Q} b_c · N_{Ω(Q,c)} / X_c) / X_Q`. -/
theorem NLSM.Amplitude.nlsm_collapse {N : ℕ} (hN : 4 ≤ N) (hE : Even N) {K : Finset (ℕ × ℕ)}
    (hK : K ⊆ oddDiagonals N)
    (hnc : ∀ Q ∈ K, ∀ Q' ∈ K, ¬ Crosses Q' Q → oddSide N Q ⊆ oddSide N Q' ∨
        oddSide N Q' ⊆ oddSide N Q)
    {ℓ : ℕ} (hℓ : ∀ c ∈ K, ℓ ∈ oddSide N c) :
    NLSM N gen = nlsmAvoiding N K gen + ∑ Q ∈ K, avoidingB N K Q *
      (avoidingA N K Q + ∑ c ∈ pkRD2Below N K Q, avoidingA N K c * regionAmp N Q c / gen c) /
        gen Q := by
  have h := nlsmAvoiding_top (algebraMap _ RF) (fun d => gen_ne_zero d) hN hE hK hnc K subset_rfl
    (fun _ _ _ hQ' _ => hQ')
  rw [Finset.sdiff_self, nlsmAvoiding_empty] at h
  refine h.trans (congrArg₂ (· + ·) rfl (sum_congr rfl fun Q hQ => ?_))
  rw [← childAmpA_expansion hE hK hnc hℓ hQ]
  rfl

open MvPolynomial in
/-- The denominator of `N_{Ω(Q,Q′)}` (`regionAmp_eq`) is not identically zero on `L_S`: its factors
are odd chords, none of which vanishes identically there ((H1)). -/
theorem region_den_witness {N : ℕ} (hE : Even N) {S K : Finset (ℕ × ℕ)} {P t b : ℕ × ℕ}
    (h : FlankClassPoleHypotheses N S K P t b) {Q Q' : ℕ × ℕ} (hQo : Q ∈ oddDiagonals N)
    (hQ'o : Q' ∈ oddDiagonals N) (hsub : oddSide N Q' ⊆ oddSide N Q) (hne : Q ≠ Q') :
    ∃ w ∈ {X : ℕ × ℕ → ℚ | OnLocus N S X}, eval w (aeval (pkRD2SubP N (pkRBOmL N
        (headStart Q) (cycPos N (headStart Q) (headStart Q')) (headLen N Q')))
        (∏ d ∈ oddDiagonals (pkRBOmM N Q Q'), (X d : MvPolynomial (ℕ × ℕ) ℚ))) ≠ 0 := by
  have hodd := fun d (hd : d ∈ oddDiagonals (pkRBOmM N Q Q')) =>
    region_subP_odd hE hQo hQ'o hsub hne hd
  obtain ⟨w, hw, hall⟩ := pkR_avoid (pkR_d_locus_sub N S)
    (fun d => (X (relab N (headStart Q)
      (pkRWOm (cycPos N (headStart Q) (headStart Q')) (headLen N Q') d)) :
        MvPolynomial (ℕ × ℕ) ℚ)) (oddDiagonals (pkRBOmM N Q Q')) (fun d hd => by
      obtain ⟨X, hX, hXd⟩ := h.h1 _ (hodd d hd).2
      exact ⟨X, hX, by simpa using hXd⟩)
  refine ⟨w, hw, ?_⟩
  rw [map_prod, map_prod]
  refine prod_ne_zero_iff.2 fun d hd => ?_
  rw [aeval_X, (hodd d hd).1]
  exact hall d hd

-- registry: C-60WX
/-- **The collapse identity**. Under (H1)–(H4) (`FlankClassPoleHypotheses`; `x = X_P`,
`H = L_S ∩ {x = 0}`), for even `N ≥ 6`: on `L_S`,
`x · NLSM_N = x · N^{¬K} + Σ_{Q ⪰ Q′ in K} φ(Q, Q′) a_Q b_{Q′}` (the difference restricts to the
zero rational function on `L_S`; `Q ⪰ Q′` is `A_{Q′} ⊆ A_Q`), and `N^{¬K}`, `a_Q`, `b_Q` have no
pole along `H`. -/
theorem NLSM.Amplitude.collapse_identity {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {S K : Finset (ℕ × ℕ)}
    {P t b : ℕ × ℕ} (h : FlankClassPoleHypotheses N S K P t b) :
    RatZeroOn {X | OnLocus N S X} (gen P * NLSM N gen - (gen P * nlsmAvoiding N K gen +
      ∑ Q ∈ K, ∑ Q' ∈ K.filter (fun Q' => oddSide N Q' ⊆ oddSide N Q),
        stripFactor N P Q Q' * avoidingB N K Q * avoidingA N K Q')) ∧
    HasNoPoleAlong {X | OnLocus N S X} (residueHyperplane N S P) (nlsmAvoiding N K gen) ∧
    (∀ Q ∈ K, HasNoPoleAlong {X | OnLocus N S X} (residueHyperplane N S P) (avoidingB N K Q)) ∧
    ∀ Q ∈ K, HasNoPoleAlong {X | OnLocus N S X} (residueHyperplane N S P) (avoidingA N K Q) := by
  classical
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  have hVs := pkR_d_locus_sub N S
  have hV : (fun _ => (0 : ℚ)) ∈ {X : ℕ × ℕ → ℚ | OnLocus N S X} := hVs.1
  have hℓ : ∀ c ∈ K, headStart b ∈ oddSide N c := fun c hc =>
    h.bottom.2 c hc (pkR_d2_hs_mem (h.odd h.bottom.1))
  -- the representations of `a_Q`, `b_Q` over their denominators
  have repB : ∀ Q ∈ K, avoidingB N K Q * algebraMap _ RF (MvPolynomial.rename
      (relab N (tailStart Q)) (∏ d ∈ oddDiagonals (tailLen N Q + 1) \
        pkRBPull N (tailStart Q) (tailLen N Q + 1) K,
          (MvPolynomial.X d : MvPolynomial (ℕ × ℕ) ℚ))) =
      algebraMap _ RF (MvPolynomial.rename (relab N (tailStart Q))
        (pkRBNP ℚ (tailLen N Q + 1) (pkRBPull N (tailStart Q) (tailLen N Q + 1) K))) ∧
      ∃ w ∈ residueHyperplane N S P, MvPolynomial.eval w (MvPolynomial.rename
        (relab N (tailStart Q)) (∏ d ∈ oddDiagonals (tailLen N Q + 1) \
          pkRBPull N (tailStart Q) (tailLen N Q + 1) K,
            (MvPolynomial.X d : MvPolynomial (ℕ × ℕ) ℚ))) ≠ 0 := by
    intro Q hQ
    have hQo := h.odd hQ
    have f1 := pkR_b_head_facts hE' hQo
    have hts1 : 1 ≤ tailStart Q ∧ tailStart Q ≤ N := by
      have hd := mem_diagonals.1 (mem_filter.1 hQo).1
      rcases pkR_b_tail_data hQo with e | e <;> omega
    have htl : tailLen N Q = N - headLen N Q := rfl
    exact ⟨nlsmAvoiding_child_eq N _ _ (by omega) K, child_den_nonvanishing hE h hts1 (by omega)⟩
  have repA : ∀ Q ∈ K, avoidingA N K Q * algebraMap _ RF (MvPolynomial.rename
      (relab N (headStart Q)) (∏ d ∈ oddDiagonals (headLen N Q + 1) \
        pkRBPull N (headStart Q) (headLen N Q + 1) K,
          (MvPolynomial.X d : MvPolynomial (ℕ × ℕ) ℚ))) =
      algebraMap _ RF (MvPolynomial.rename (relab N (headStart Q))
        (pkRBNP ℚ (headLen N Q + 1) (pkRBPull N (headStart Q) (headLen N Q + 1) K))) ∧
      ∃ w ∈ residueHyperplane N S P, MvPolynomial.eval w (MvPolynomial.rename
        (relab N (headStart Q)) (∏ d ∈ oddDiagonals (headLen N Q + 1) \
          pkRBPull N (headStart Q) (headLen N Q + 1) K,
            (MvPolynomial.X d : MvPolynomial (ℕ × ℕ) ℚ))) ≠ 0 := by
    intro Q hQ
    have f1 := pkR_b_head_facts hE' (h.odd hQ)
    exact ⟨nlsmAvoiding_child_eq N _ _ (by omega) K,
      child_den_nonvanishing hE h ⟨f1.1, f1.2.1⟩ (by omega)⟩
  have toV : ∀ {D : MvPolynomial (ℕ × ℕ) ℚ}, (∃ w ∈ residueHyperplane N S P,
      MvPolynomial.eval w D ≠ 0) → ∃ w ∈ {X : ℕ × ℕ → ℚ | OnLocus N S X},
        MvPolynomial.eval w D ≠ 0 := fun ⟨w, hw, hD⟩ => ⟨w, hw.1, hD⟩
  refine ⟨?_, ?_, fun Q hQ => hasNoPoleAlong_of_eq hV (repB Q hQ).1 (repB Q hQ).2,
    fun Q hQ => hasNoPoleAlong_of_eq hV (repA Q hQ).1 (repA Q hQ).2⟩
  · -- the identity
    have G := nlsm_collapse (by omega) hE h.odd h.nested hℓ
    have hfil : ∀ Q ∈ K, K.filter (fun Q' => oddSide N Q' ⊆ oddSide N Q) =
        insert Q (pkRD2Below N K Q) := by
      intro Q hQ
      ext Q'
      simp only [mem_filter, mem_insert, pkRD2Below]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases e : Q' = Q
        · exact Or.inl e
        · exact Or.inr ⟨h1, e, h2⟩
      · rintro (rfl | ⟨h1, -, h2⟩)
        · exact ⟨hQ, subset_rfl⟩
        · exact ⟨h1, h2⟩
    have hQb : ∀ Q, Q ∉ pkRD2Below N K Q := fun Q hc => (mem_filter.1 hc).2.1 rfl
    have key : gen P * NLSM N gen - (gen P * nlsmAvoiding N K gen +
        ∑ Q ∈ K, ∑ Q' ∈ K.filter (fun Q' => oddSide N Q' ⊆ oddSide N Q),
          stripFactor N P Q Q' * avoidingB N K Q * avoidingA N K Q') =
        ∑ Q ∈ K, (avoidingB N K Q * (avoidingA N K Q * (gen P / gen Q - 1)) +
          ∑ c ∈ pkRD2Below N K Q, avoidingB N K Q * (avoidingA N K c * (regionAmp N Q c *
            (gen P / (gen Q * gen c) - 1 / gen P)))) := by
      rw [G, mul_add, mul_sum, add_sub_add_left_eq_sub, ← sum_sub_distrib]
      refine sum_congr rfl fun Q hQ => ?_
      rw [hfil Q hQ, sum_insert (hQb Q), stripFactor, ite_eq_left_of_eq_true _ _ (eq_self Q)]
      have hs : ∑ c ∈ pkRD2Below N K Q, stripFactor N P Q c * avoidingB N K Q *
          avoidingA N K c = ∑ c ∈ pkRD2Below N K Q, regionAmp N Q c / gen P *
            avoidingB N K Q * avoidingA N K c :=
        sum_congr rfl fun c hc => by
          rw [stripFactor, ite_eq_right_of_eq_false _ _
            (eq_false fun e => (mem_filter.1 hc).2.1 e.symm)]
      rw [hs]
      have s1 : ∑ c ∈ pkRD2Below N K Q, avoidingB N K Q * (avoidingA N K c * (regionAmp N Q c *
          (gen P / (gen Q * gen c) - 1 / gen P))) =
          gen P / gen Q * avoidingB N K Q *
              ∑ c ∈ pkRD2Below N K Q, avoidingA N K c * regionAmp N Q c / gen c -
            ∑ c ∈ pkRD2Below N K Q, regionAmp N Q c / gen P * avoidingB N K Q *
              avoidingA N K c := by
        rw [mul_sum, ← sum_sub_distrib]
        refine sum_congr rfl fun c _ => ?_
        ring
      rw [s1]
      ring
    rw [key]
    refine ratZeroOn_sum hVs K fun Q hQ => ratZeroOn_add hVs ?_
      (ratZeroOn_sum hVs _ fun c hc => ?_)
    · -- `a_Q b_Q (x / X_Q − 1)`
      have hQo := h.odd hQ
      have r : RatZeroOn {X | OnLocus N S X} (gen P / gen Q - 1) := by
        refine ⟨MvPolynomial.X P - MvPolynomial.X Q, MvPolynomial.X Q, ?_, ?_, fun X hX => ?_⟩
        · rw [map_sub]
          change (gen P / gen Q - 1) * gen Q = gen P - gen Q
          field_simp [gen_ne_zero Q]
        · obtain ⟨X, hX, hXQ⟩ := h.h1 Q hQo
          exact ⟨X, hX, by simpa using hXQ⟩
        · simp [h.h2' Q hQ X hX]
      exact ratZeroOn_mul_of_eq hVs (ratZeroOn_mul_of_eq hVs r (repA Q hQ).1 (toV (repA Q hQ).2))
        (repB Q hQ).1 (toV (repB Q hQ).2)
    · -- `a_Q b_c N_Ω (x / (X_Q X_c) − 1 / x)`
      obtain ⟨hcK, hcQ, hsub⟩ := mem_filter.1 hc
      have hQo := h.odd hQ
      have hco := h.odd hcK
      have r : RatZeroOn {X | OnLocus N S X} (gen P / (gen Q * gen c) - 1 / gen P) := by
        refine ⟨MvPolynomial.X P * MvPolynomial.X P - MvPolynomial.X Q * MvPolynomial.X c,
          MvPolynomial.X P * (MvPolynomial.X Q * MvPolynomial.X c), ?_, ?_, fun X hX => ?_⟩
        · simp only [map_sub, map_mul]
          change (gen P / (gen Q * gen c) - 1 / gen P) * (gen P * (gen Q * gen c)) =
            gen P * gen P - gen Q * gen c
          field_simp [gen_ne_zero P, gen_ne_zero Q, gen_ne_zero c]
        · have w : ∀ d ∈ oddDiagonals N, ∃ w ∈ {X : ℕ × ℕ → ℚ | OnLocus N S X},
              MvPolynomial.eval w (MvPolynomial.X d : MvPolynomial (ℕ × ℕ) ℚ) ≠ 0 :=
            fun d hd => by
              obtain ⟨X, hX, hXd⟩ := h.h1 d hd
              exact ⟨X, hX, by simpa using hXd⟩
          exact exists_eval_mul_ne_zero hVs (w P (h.odd h.mem))
            (exists_eval_mul_ne_zero hVs (w Q hQo) (w c hco))
        · simp [h.h2' Q hQ X hX, h.h2' c hcK X hX]
      exact ratZeroOn_mul_of_eq hVs (ratZeroOn_mul_of_eq hVs (ratZeroOn_mul_of_eq hVs r
        (regionAmp_eq hE hQo hco hsub (Ne.symm hcQ))
        (region_den_witness hE h hQo hco hsub (Ne.symm hcQ)))
        (repA c hcK).1 (toV (repA c hcK).2)) (repB Q hQ).1 (toV (repB Q hQ).2)
  · -- `N^{¬K}` has no pole along `H`
    have e := nlsmAvoiding_numerator_hom (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) RF)
      (n := N) (by omega) K (fun d _ => gen_ne_zero d)
    obtain ⟨w, hw, hall⟩ := pkR_avoid (residueHyperplane_sub N S P)
      (fun d => (MvPolynomial.X d : MvPolynomial (ℕ × ℕ) ℚ)) (oddDiagonals N \ K) (fun d hd => by
        obtain ⟨X, hX, hXd⟩ := odd_chord_outside_class_nonvanishing_on_hyperplane h
          (mem_sdiff.1 hd).1 (mem_sdiff.1 hd).2
        exact ⟨X, hX, by simpa using hXd⟩)
    refine hasNoPoleAlong_of_eq hV (P := pkRBNP ℚ N K)
      (D := ∏ d ∈ oddDiagonals N \ K, (MvPolynomial.X d : MvPolynomial (ℕ × ℕ) ℚ)) ?_ ⟨w, hw, ?_⟩
    · rw [e, map_prod]
      rfl
    · rw [map_prod]
      exact prod_ne_zero_iff.2 hall

-- registry: C-ZW0Z
/-- **The value of the strip factor** (the paper's `(−1)^d` is a remark, not formalised). Under
(H1)–(H4), for even `N ≥ 6`, `φ(t, b)|_H = ε` for a non-zero constant `ε`. -/
theorem NLSM.Amplitude.strip_factor_value {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {S K : Finset (ℕ × ℕ)}
    {P t b : ℕ × ℕ} (h : FlankClassPoleHypotheses N S K P t b) :
    ∃ ε : ℚ, ε ≠ 0 ∧ RestrictsToZeroAlong {X | OnLocus N S X} (residueHyperplane N S P)
      (stripFactor N P t b - (ε : RF)) :=
  stripFactor_sub_const_restrictsToZero hN hE h h.top.1 h.bottom.1 (h.top.2 b h.bottom.1)

-- registry: C-CGN9
/-- "The child amplitudes are those of the full children", for the top:
no chord of `K` is a diagonal of the B-side polygon of `t`, so `a_t` (`avoidingB`) is the full
B-child amplitude (`childAmpB`). -/
theorem NLSM.Amplitude.avoidingB_top_eq {N : ℕ} {S K : Finset (ℕ × ℕ)} {P t b : ℕ × ℕ}
    (h : FlankClassPoleHypotheses N S K P t b) : avoidingB N K t = childAmpB N t := by
  unfold avoidingB childAmpB
  rw [pkR_b_R17_tail (h.odd h.top.1) h.odd h.top.2, nlsmAvoiding_empty]

-- registry: C-CGN9
/-- The mirror for the bottom: `b_b` (`avoidingA`) is the full A-child amplitude
(`childAmpA`). -/
theorem NLSM.Amplitude.avoidingA_bottom_eq {N : ℕ} {S K : Finset (ℕ × ℕ)} {P t b : ℕ × ℕ}
    (h : FlankClassPoleHypotheses N S K P t b) : avoidingA N K b = childAmpA N b := by
  unfold avoidingA childAmpA
  rw [pkR_b_R17_head (h.odd h.bottom.1) h.odd h.bottom.2, nlsmAvoiding_empty]

open MvPolynomial in
-- registry: C-CGN9
/-- **The class residue** (the paper's `(−1)^d` is a remark, not formalised). Under (H1)–(H4)
(`FlankClassPoleHypotheses`; `x = X_P`, `H = L_S ∩ {x = 0}`), for even `N ≥ 6`:
`x · NLSM_N|_{L_S}` has no pole along `H` (so `NLSM_N|_{L_S}` has at most a simple pole along `H`),
`a_t` and `b_b` have no pole along `H`, and
`(x · NLSM_N|_{L_S})|_H = ε · a_t|_H · b_b|_H` for a non-zero constant `ε`, where `a_t` is the
amplitude of the B-child of `t` and `b_b` that of the A-child of `b` (stated as: the difference
restricts to zero along `H`). -/
theorem NLSM.Amplitude.simple_pole_along_flank_class {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    {S K : Finset (ℕ × ℕ)} {P t b : ℕ × ℕ} (h : FlankClassPoleHypotheses N S K P t b) :
    HasNoPoleAlong {X | OnLocus N S X} (residueHyperplane N S P) (gen P * NLSM N gen) ∧
      HasNoPoleAlong {X | OnLocus N S X} (residueHyperplane N S P) (childAmpB N t) ∧
      HasNoPoleAlong {X | OnLocus N S X} (residueHyperplane N S P) (childAmpA N b) ∧
      ∃ ε : ℚ, ε ≠ 0 ∧ RestrictsToZeroAlong {X | OnLocus N S X} (residueHyperplane N S P)
        (gen P * NLSM N gen - (ε : RF) * childAmpB N t * childAmpA N b) := by
  classical
  have hV := pkR_d_locus_sub N S
  have hH := residueHyperplane_sub N S P
  have hH0 : ∃ w, w ∈ residueHyperplane N S P := ⟨_, hH.1⟩
  obtain ⟨hcol, hNK, hregB, hregA⟩ := collapse_identity hN hE h
  obtain ⟨hvA, hvB⟩ := only_extreme_term_survives hN hE h
  have hφ : ∀ Q ∈ K, ∀ Q' ∈ K, oddSide N Q' ⊆ oddSide N Q →
      HasNoPoleAlong {X | OnLocus N S X} (residueHyperplane N S P) (stripFactor N P Q Q') :=
    fun _ hQ _ hQ' hsub => stripFactor_hasNoPoleAlong hN hE h hQ hQ' hsub
  obtain ⟨ε, hε, hφε⟩ := strip_factor_value hN hE h
  have hxH : RestrictsToZeroAlong {X | OnLocus N S X} (residueHyperplane N S P) (gen P) :=
    ⟨X P, 1, ⟨0, 1, by simp [gen], ⟨_, hV.1, by simp⟩, fun _ _ => by simp⟩,
      ⟨_, hH.1, by simp⟩, fun x hx => by simpa using hx.2⟩
  -- every term of the sum, minus `ε a_t b_b` for `(t, b)`, restricts to zero along `H`
  have hterm : ∀ Q ∈ K, ∀ Q' ∈ K.filter (fun Q' => oddSide N Q' ⊆ oddSide N Q),
      RestrictsToZeroAlong {X | OnLocus N S X} (residueHyperplane N S P)
        (stripFactor N P Q Q' * avoidingB N K Q * avoidingA N K Q' -
          if Q = t ∧ Q' = b then (ε : RF) * avoidingB N K Q * avoidingA N K Q' else 0) := by
    intro Q hQ Q' hQ'
    obtain ⟨hQ'K, hsub⟩ := mem_filter.1 hQ'
    by_cases ht : Q = t
    · by_cases hb : Q' = b
      · rw [ite_eq_left ⟨ht, hb⟩, ← sub_mul, ← sub_mul]
        exact (hφε.congr hV (by rw [ht, hb, sub_self]; exact ⟨0, 1, by simp,
          ⟨_, hV.1, by simp⟩, fun _ _ => by simp⟩)).mul hV hH (hregB Q hQ) |>.mul hV hH
          (hregA Q' hQ'K)
      · rw [ite_eq_right fun e => hb e.2, sub_zero, mul_comm]
        exact (hvA Q' hQ'K hb).mul hV hH ((hφ Q hQ Q' hQ'K hsub).mul hV hH (hregB Q hQ))
    · rw [ite_eq_right fun e => ht e.1, sub_zero, mul_comm (stripFactor N P Q Q'), mul_assoc]
      exact (hvB Q hQ ht).mul hV hH ((hφ Q hQ Q' hQ'K hsub).mul hV hH (hregA Q' hQ'K))
  have hsum : RestrictsToZeroAlong {X | OnLocus N S X} (residueHyperplane N S P)
      (gen P * nlsmAvoiding N K gen + ∑ Q ∈ K, ∑ Q' ∈ K.filter (fun Q' => oddSide N Q' ⊆
        oddSide N Q), stripFactor N P Q Q' * avoidingB N K Q * avoidingA N K Q' -
          (ε : RF) * childAmpB N t * childAmpA N b) := by
    have hsplit : ∑ Q ∈ K, ∑ Q' ∈ K.filter (fun Q' => oddSide N Q' ⊆ oddSide N Q),
        (if Q = t ∧ Q' = b then (ε : RF) * avoidingB N K Q * avoidingA N K Q' else 0) =
        (ε : RF) * childAmpB N t * childAmpA N b := by
      rw [sum_eq_single_of_mem t h.top.1 fun Q _ hQt => sum_eq_zero fun Q' _ =>
          ite_eq_right fun e => hQt e.1,
        sum_eq_single_of_mem b (mem_filter.2 ⟨h.bottom.1, h.top.2 b h.bottom.1⟩)
          fun Q' _ hQ'b => ite_eq_right fun e => hQ'b e.2,
        ite_eq_left ⟨rfl, rfl⟩, avoidingB_top_eq h, avoidingA_bottom_eq h]
    rw [add_sub_assoc, ← hsplit, ← sum_sub_distrib]
    refine (hxH.mul hV hH hNK).add hV hH ?_
    simp only [← sum_sub_distrib]
    exact RestrictsToZeroAlong.sum hV hH K fun Q hQ =>
      RestrictsToZeroAlong.sum hV hH _ fun Q' hQ' => hterm Q hQ Q' hQ'
  have hfin := hsum.congr hV (f := gen P * NLSM N gen - (ε : RF) * childAmpB N t * childAmpA N b)
    (by
      have e : gen P * NLSM N gen - (ε : RF) * childAmpB N t * childAmpA N b -
          (gen P * nlsmAvoiding N K gen + ∑ Q ∈ K, ∑ Q' ∈ K.filter (fun Q' => oddSide N Q' ⊆
            oddSide N Q), stripFactor N P Q Q' * avoidingB N K Q * avoidingA N K Q' -
              (ε : RF) * childAmpB N t * childAmpA N b) =
          gen P * NLSM N gen - (gen P * nlsmAvoiding N K gen + ∑ Q ∈ K, ∑ Q' ∈ K.filter
            (fun Q' => oddSide N Q' ⊆ oddSide N Q),
              stripFactor N P Q Q' * avoidingB N K Q * avoidingA N K Q') := by ring
      rw [e]
      exact hcol)
  refine ⟨?_, avoidingB_top_eq h ▸ hregB t h.top.1, avoidingA_bottom_eq h ▸ hregA b h.bottom.1,
    ε, hε, hfin⟩
  have hab : HasNoPoleAlong {X | OnLocus N S X} (residueHyperplane N S P)
      ((ε : RF) * childAmpB N t * childAmpA N b) := by
    rw [← avoidingB_top_eq h, ← avoidingA_bottom_eq h]
    exact ((hasNoPoleAlong_const hV hH0 ε).mul hV hH (hregB t h.top.1)).mul hV hH
      (hregA b h.bottom.1)
  have := hfin.hasNoPoleAlong.add hV hH hab
  rwa [sub_add_cancel] at this

/-! ## Strip regions, corners and the ear lemma

In mesh language (no momenta): strip regions for chords of `𝒫₀` with equal flank sets
(`strip_regions`, through the library's positional form `strip_pairs_positions`), corners for a
polygon with side values (`planarWithSides`, `meshWithSides`, `corner_identity`), and the ear lemma
on its locus `earLocus` (equal to the library's `pkRBZ5`, `earLocus_iff`) in rational form
(`polygon_numerators_vanish_on_ear_locus`). -/

set_option maxHeartbeats 1000000 in
-- the proof of `pkR_d2_OT` (`C10`) for chords of `𝒫₀`; the budget of `pkR_d2_OT` (it times out at
-- the default inside `Paper`)
-- registry: C-DA1A
/-- For chords `Q ≠ Q′` of `𝒫₀` with `A_{Q′} ⊆ A_Q` and `h_Q = h_{Q′}`, on `L_S`: the mesh variables
of the pairs `T(Q, Q′)` (`pkRBTP`) vanish, and the positional form `pkRBOT` from
`a = headStart Q` holds (`pkR_d2_OT` of `C10` asks for members of a flank class). -/
theorem Amplitudes.Kinematics.Mesh.strip_pairs_positions {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0)
    {S : Finset (ℕ × ℕ)} {Q Q' : ℕ × ℕ} (hQ : Q ∈ cleanChords N S) (hQ' : Q' ∈ cleanChords N S)
    (hsub : oddSide N Q' ⊆ oddSide N Q) (hne : Q ≠ Q') (hh : hitSet N S Q = hitSet N S Q')
    {X : ℕ × ℕ → ℚ} (hX : OnLocus N S X) :
    (∀ a b, (a, b) ∈ diagonals N → pkRBTP N Q Q' a b → mesh N X a b = 0) ∧
    pkRBOT N (headStart Q) (cycPos N (headStart Q) (headStart Q')) (headLen N Q)
        (headLen N Q') X := by
  have hQo := (mem_filter.1 hQ).1
  have hQ'o := (mem_filter.1 hQ').1
  have f1 := pkR_b_head_facts hE hQo
  have f2 := pkR_b_head_facts hE hQ'o
  obtain ⟨hp, hpL, hLL, hpos⟩ := pkR_b_nest_pos hE hQo hQ'o hsub hne
  have i1 := pkR_d_inner_sub hN hE hQo hQ'o hh
  have i2 := pkR_d_inner_sub hN hE hQ'o hQo hh.symm
  have hT : ∀ a b, (a, b) ∈ diagonals N → pkRBTP N Q Q' a b → mesh N X a b = 0 :=
      fun a b hab hTP =>
    hX _ (pkR_b_omegaHyp hsub (mem_filter.1 hQ).2 (mem_filter.1 hQ').2
      (Subset.antisymm i1.1 i2.1) (Subset.antisymm i1.2 i2.2) hab hTP)
  refine ⟨hT, (pkR_b_OT_iff _ _ _ _ _ X).2 ⟨?_, ?_, ?_⟩⟩
  · intro i j hi hj hij hne'
    obtain ⟨A1, -, V1⟩ := pkR_b_posQ hE hQo (i := i) (by omega)
    obtain ⟨A2, -, V2⟩ := pkR_b_posQ hE hQo (i := j) (by omega)
    have B1 := hpos i (by omega)
    have B2 := hpos j (by omega)
    refine pkR_b_TP_mesh hT (mem_diagonals.2 (by dsimp only; omega))
        ((pkR_b_TP_iff N Q Q' _ _).2 (Or.inl ?_))
    exact ⟨by omega, A1.2 (by omega), fun h => by have := B1.1 h; omega, A2.2 (by omega),
      fun h => by have := B2.1 h; omega⟩
  · intro i j hi hi2 hj1 hj2
    obtain ⟨A1, -, V1⟩ := pkR_b_posQ hE hQo (i := i) (by omega)
    obtain ⟨A2, -, V2⟩ := pkR_b_posQ hE hQo (i := j) (by omega)
    have B1 := hpos i (by omega)
    have B2 := hpos j (by omega)
    refine pkR_b_TP_mesh hT (mem_diagonals.2 (by dsimp only; omega))
      ((pkR_b_TP_iff N Q Q' _ _).2 (Or.inr (Or.inl ?_)))
    exact ⟨by omega, A1.2 (by omega), fun h => by have := B1.1 h; omega, B2.2 ⟨hj1, hj2⟩⟩
  · intro i j hi hi2 hj1 hj2
    obtain ⟨A1, -, V1⟩ := pkR_b_posQ hE hQo (i := i) (by omega)
    obtain ⟨-, E2, V2⟩ := pkR_b_posQ hE hQo (i := j) (by omega)
    have B1 := hpos i (by omega)
    refine pkR_b_TP_mesh hT (mem_diagonals.2 (by dsimp only; omega))
      ((pkR_b_TP_iff N Q Q' _ _).2 (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
    exact ⟨by omega, A1.2 (by omega), fun h => by have := B1.1 h; omega, E2.2 hj1⟩

-- registry: C-DA1A
/-- **Strip regions**, in mesh language. For even `N ≥ 6`, let
`Q ≻ Q′` be chords of `𝒫₀` (`A_{Q′} ⊊ A_Q`) with `h_Q = h_{Q′}`, and `St = A_Q ∖ A_{Q′}` the
strip legs of `Ω(Q, Q′)`. On `L_S`:
(i) every same-parity mesh variable of `Ω(Q, Q′)` vanishes, read in the parent (the mesh variable
of two legs of `Ω` is the sum of the parent mesh variables over their blocks; `ℓ_A` has block
`A_{Q′}`, `ℓ_B` has block `B_Q`): `c_{u,v} = 0` for strip legs `u ≠ v` of the same parity,
`Σ_{w ∈ A_{Q′}} c_{u,w} = 0` for an odd strip leg `u` (the pair `u`, `ℓ_A`), and
`Σ_{w ∈ B_Q} c_{u,w} = 0` for an even strip leg `u` (the pair `u`, `ℓ_B`);
(ii) `ℓ_A` and `ℓ_B` sit at positions of opposite parity in `Ω` (in its vertex list
`pkRBOmL`, `ℓ_A` is leg `p + 1`, `p` the length of the first strip, and `ℓ_B` is leg
`m = |Ω|`), and `X_Q = X_{Q′}`;
(iii) `c_{u,w} = 0` for each odd strip leg `u` and each leg `w` of `A_{Q′}`, and for each even
strip leg `u` and each leg `w` of `B_Q`. -/
theorem Amplitudes.Kinematics.Mesh.strip_regions {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    {S : Finset (ℕ × ℕ)} {Q Q' : ℕ × ℕ} (hQ : Q ∈ cleanChords N S) (hQ' : Q' ∈ cleanChords N S)
    (hsub : oddSide N Q' ⊆ oddSide N Q) (hne : Q ≠ Q') (hh : hitSet N S Q = hitSet N S Q')
    {X : ℕ × ℕ → ℚ} (hX : OnLocus N S X) :
    ((∀ u ∈ oddSide N Q \ oddSide N Q', ∀ v ∈ oddSide N Q \ oddSide N Q', u ≠ v →
        u % 2 = v % 2 → mesh N X u v = 0) ∧
      (∀ u ∈ oddSide N Q \ oddSide N Q', u % 2 = 1 → ∑ w ∈ oddSide N Q', mesh N X u w = 0) ∧
      ∀ u ∈ oddSide N Q \ oddSide N Q', u % 2 = 0 → ∑ w ∈ evenSide N Q, mesh N X u w = 0) ∧
    ((cycPos N (headStart Q) (headStart Q') + 1) % 2 ≠ pkRBOmM N Q Q' % 2 ∧ X Q = X Q') ∧
    (∀ u ∈ oddSide N Q \ oddSide N Q', u % 2 = 1 → ∀ w ∈ oddSide N Q', mesh N X u w = 0) ∧
    ∀ u ∈ oddSide N Q \ oddSide N Q', u % 2 = 0 → ∀ w ∈ evenSide N Q, mesh N X u w = 0 := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  have hQo := (mem_filter.1 hQ).1
  have hQ'o := (mem_filter.1 hQ').1
  have f1 := pkR_b_head_facts hE' hQo
  have f2 := pkR_b_head_facts hE' hQ'o
  obtain ⟨hp, hpL, hLL, hpos⟩ := pkR_b_nest_pos hE' hQo hQ'o hsub hne
  obtain ⟨hT, hOT⟩ := strip_pairs_positions hN hE' hQ hQ' hsub hne hh hX
  obtain ⟨O1, O2, O3⟩ := (pkR_b_OT_iff _ _ _ _ _ X).1 hOT
  -- every leg is read in positions from `a = headStart Q`
  have pos : ∀ u, 1 ≤ u ∧ u ≤ N → ∃ i < N, vtx N (headStart Q + i) = u ∧
      (u ∈ oddSide N Q ↔ i < headLen N Q) ∧ (u ∈ evenSide N Q ↔ headLen N Q ≤ i) ∧
      (u ∈ oddSide N Q' ↔ cycPos N (headStart Q) (headStart Q') ≤ i ∧
        i < cycPos N (headStart Q) (headStart Q') + headLen N Q') ∧ (u % 2 = 1 ↔ i % 2 = 0) := by
    intro u hu
    refine ⟨cycPos N (headStart Q) u, Nat.mod_lt _ (by omega),
      pkR_b_vtx_cyc ⟨f1.1, f1.2.1⟩ hu, ?_⟩
    have hi : cycPos N (headStart Q) u < N := Nat.mod_lt _ (by omega)
    obtain ⟨A, E, V⟩ := pkR_b_posQ hE' hQo hi
    rw [pkR_b_vtx_cyc ⟨f1.1, f1.2.1⟩ hu] at A E V
    refine ⟨A, E, ?_, ?_⟩
    · have := hpos _ hi
      rwa [pkR_b_vtx_cyc ⟨f1.1, f1.2.1⟩ hu] at this
    · rcases V with ⟨-, e⟩ | ⟨-, e⟩ <;> omega
  have bdA : ∀ u ∈ oddSide N Q, 1 ≤ u ∧ u ≤ N := fun u hu => pkR_d2_side_bd hQo hu
  have bdB : ∀ u ∈ evenSide N Q, 1 ≤ u ∧ u ≤ N := fun u hu => by
    have : u ∈ Icc 1 N \ oddSide N Q := hu
    exact mem_Icc.1 (mem_sdiff.1 this).1
  have iiiA : ∀ u ∈ oddSide N Q \ oddSide N Q', u % 2 = 1 → ∀ w ∈ oddSide N Q',
      mesh N X u w = 0 := by
    intro u hu hu1 w hw
    obtain ⟨huA, huA'⟩ := mem_sdiff.1 hu
    obtain ⟨i, hi, rfl, a1, -, a3, a4⟩ := pos u (bdA u huA)
    obtain ⟨j, hj, rfl, -, -, b3, -⟩ := pos w (bdA w (hsub hw))
    exact O2 i j (by have := a1.1 huA; have := mt a3.2 huA'; omega) (a4.1 hu1) (b3.1 hw).1
      (b3.1 hw).2
  have iiiB : ∀ u ∈ oddSide N Q \ oddSide N Q', u % 2 = 0 → ∀ w ∈ evenSide N Q,
      mesh N X u w = 0 := by
    intro u hu hu0 w hw
    obtain ⟨huA, huA'⟩ := mem_sdiff.1 hu
    obtain ⟨i, hi, rfl, a1, -, a3, a4⟩ := pos u (bdA u huA)
    obtain ⟨j, hj, rfl, -, b2, -, -⟩ := pos w (bdB w hw)
    exact O3 i j (by have := a1.1 huA; have := mt a3.2 huA'; omega)
      (by have := mt a4.2; omega) (b2.1 hw) hj
  refine ⟨⟨fun u hu v hv huv hpar => ?_, fun u hu hu1 => sum_eq_zero fun w hw => iiiA u hu hu1 w hw,
    fun u hu hu0 => sum_eq_zero fun w hw => iiiB u hu hu0 w hw⟩,
    ⟨?_, (pkR_b_omegaTiles hE' hQo hQ'o hsub hne hT).2.2⟩, iiiA, iiiB⟩
  · obtain ⟨huA, huA'⟩ := mem_sdiff.1 hu
    obtain ⟨hvA, hvA'⟩ := mem_sdiff.1 hv
    obtain ⟨i, hi, rfl, a1, -, a3, a4⟩ := pos u (bdA u huA)
    obtain ⟨j, hj, rfl, b1, -, b3, b4⟩ := pos v (bdA v hvA)
    refine O1 i j (by have := a1.1 huA; have := mt a3.2 huA'; omega)
      (by have := b1.1 hvA; have := mt b3.2 hvA'; omega) ?_ (fun e => huv (by rw [e]))
    by_cases h : vtx N (headStart Q + i) % 2 = 1
    · have := a4.1 h; have := b4.1 (by rw [← hpar]; exact h); omega
    · have := mt a4.2 h; have := mt b4.2 (by rw [← hpar]; exact h); omega
  · change (cycPos N (headStart Q) (headStart Q') + 1) % 2 ≠ (headLen N Q - headLen N Q' + 2) % 2
    omega

section SideValues

variable {F : Type*} [Field F]

-- registry: C-2R8J
/-- The planar variables of an `n`-gon with side values (`corner_identity`): `X_{k,k+1} = m_k`
on the sides (leg `k` between the dual points `k`, `k + 1`), `X` on the diagonals, `0` on
coincident labels; labels read cyclically. -/
def Amplitudes.Kinematics.Mesh.planarWithSides (n : ℕ) (X : ℕ × ℕ → F) (m : ℕ → F) (i j : ℕ) : F :=
  if vtx n j = vtx n (i + 1) then m (vtx n i)
  else if vtx n i = vtx n (j + 1) then m (vtx n j) else planar n X i j

-- registry: C-2R8J
/-- The mesh variable `c_{i,j} = X_{i,j} + X_{i+1,j+1} − X_{i,j+1} − X_{i+1,j}` of a polygon with
side values (`mesh` is the same with every side set to `0`). -/
def Amplitudes.Kinematics.Mesh.meshWithSides (n : ℕ) (X : ℕ × ℕ → F) (m : ℕ → F) (i j : ℕ) : F :=
  planarWithSides n X m i j + planarWithSides n X m (i + 1) (j + 1) -
    planarWithSides n X m i (j + 1) - planarWithSides n X m (i + 1) j

/-- A planar variable of two adjacent dual points is `0` (a side of the polygon). -/
theorem planar_adjacent {n : ℕ} (hn : 1 ≤ n) (X : ℕ × ℕ → F) {i j : ℕ}
    (h : vtx n j = vtx n (i + 1)) : planar n X i j = 0 := by
  rw [pkR_planar_congr hn X rfl h, pkR_planar_succ hn]

/-- Shifting two labels by one keeps their (cyclic) equality. -/
theorem vtx_succ_eq_iff {n : ℕ} (hn : 1 ≤ n) (a b : ℕ) :
    vtx n (a + 1) = vtx n (b + 1) ↔ vtx n a = vtx n b := by
  rw [vtx_succ hn, vtx_succ hn]
  have ba := vtx_bounds n a hn
  have bb := vtx_bounds n b hn
  unfold nxt
  constructor
  · intro h
    split_ifs at h <;> omega
  · intro h
    rw [h]

/-- With side values, a planar variable is the one without side values plus the side value when
the two dual points are adjacent. -/
theorem planarWithSides_eq {n : ℕ} (hn3 : 3 ≤ n) (X : ℕ × ℕ → F) (m : ℕ → F) (a b : ℕ) :
    planarWithSides n X m a b = planar n X a b +
      (if vtx n b = vtx n (a + 1) then m (vtx n a) else 0) +
      (if vtx n a = vtx n (b + 1) then m (vtx n b) else 0) := by
  have hn : 1 ≤ n := by omega
  unfold planarWithSides
  by_cases h1 : vtx n b = vtx n (a + 1)
  · have h2 : ¬ vtx n a = vtx n (b + 1) := by
      intro h2
      rw [vtx_succ hn] at h1 h2
      have ba := vtx_bounds n a hn
      have bb := vtx_bounds n b hn
      unfold nxt at h1 h2
      split_ifs at h1 h2 <;> omega
    rw [ite_eq_left h1, ite_eq_left h1, ite_eq_right h2, planar_adjacent hn X h1]
    ring
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : vtx n a = vtx n (b + 1)
    · rw [ite_eq_left h2, ite_eq_left h2, pkR_planar_comm, planar_adjacent hn X h2]
      ring
    · rw [ite_eq_right h2, ite_eq_right h2]
      ring

-- registry: C-2R8J
/-- **Corners**, in mesh language (corrected for the `4`-gon, where `c_{1,3}` straddles two
sides). For an `n`-gon
(`n ≥ 4`) with side values `X_{k,k+1} = m_k`, let `c` be its mesh variables and `c⁰` those of the
same polygon with every side set to `0` (`mesh`). For two non-adjacent legs `i`, `j`,
`c⁰_{i,j} = c_{i,j} + Σ m_k` over the legs `k` that `i`, `j` straddle (`{i, j} = {k − 1, k + 1}`;
at most one for `n ≥ 5`, both legs `2`, `4` for `c_{1,3}` at `n = 4`); so `c⁰_{i,j} = c_{i,j}`
unless `i`, `j` straddle a leg. -/
theorem Amplitudes.Kinematics.Mesh.corner_identity {n : ℕ} (hn : 4 ≤ n) (X : ℕ × ℕ → F) (m : ℕ → F)
    {i j : ℕ} (hi : i ∈ Icc 1 n) (hj : j ∈ Icc 1 n) (hij : (min i j, max i j) ∈ diagonals n) :
    mesh n X i j = meshWithSides n X m i j +
      (if vtx n j = vtx n (i + 2) then m (vtx n (i + 1)) else 0) +
      (if vtx n i = vtx n (j + 2) then m (vtx n (j + 1)) else 0) := by
  have hn1 : 1 ≤ n := by omega
  have hi' := mem_Icc.1 hi
  have hj' := mem_Icc.1 hj
  have hd := mem_diagonals.1 hij
  have vi : vtx n i = i := vtx_of_mem hi'.1 hi'.2
  have vj : vtx n j = j := vtx_of_mem hj'.1 hj'.2
  have vi1 : vtx n (i + 1) = nxt n i := by rw [vtx_succ hn1, vi]
  have vj1 : vtx n (j + 1) = nxt n j := by rw [vtx_succ hn1, vj]
  dsimp only at hd
  have nij : ¬ vtx n j = vtx n (i + 1) := by
    rw [vj, vi1]; unfold nxt
    split_ifs <;> (rcases le_total i j with c | c <;>
      simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right, c] at hd <;> omega)
  have nji : ¬ vtx n i = vtx n (j + 1) := by
    rw [vi, vj1]; unfold nxt
    split_ifs <;> (rcases le_total i j with c | c <;>
      simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right, c] at hd <;> omega)
  have ne : vtx n i ≠ vtx n j := by
    rw [vi, vj]; intro e; subst e; simp at hd
  have s2 : i + 2 = i + 1 + 1 := rfl
  have t2 : j + 2 = j + 1 + 1 := rfl
  unfold meshWithSides
  rw [planarWithSides_eq (by omega) X m i j, ite_eq_right nij, ite_eq_right nji,
    planarWithSides_eq (by omega) X m (i + 1) (j + 1),
    ite_eq_right (fun e => nij ((vtx_succ_eq_iff hn1 j (i + 1)).1 e)),
    ite_eq_right (fun e => nji ((vtx_succ_eq_iff hn1 i (j + 1)).1 e)),
    planarWithSides_eq (by omega) X m i (j + 1),
    ite_eq_right (fun e => ne ((vtx_succ_eq_iff hn1 j i).1 e).symm),
    planarWithSides_eq (by omega) X m (i + 1) j,
    ite_eq_right (fun e => ne ((vtx_succ_eq_iff hn1 i j).1 e)), ← s2, ← t2]
  unfold mesh
  ring

end SideValues

-- registry: C-KMMK
/-- The locus `Z′` of the ear lemma, for the `n`-gon labelled so that `s` is leg `n`
(class `π` even) and `R` a run whose end legs are odd, and a set `K` of members: (z1) the odd
legs outside `R` (`μ⁺`) are pairwise orthogonal; (z2) each of them is orthogonal to each leg of
`R`; (z3) for `Q ∈ K`, the mesh variables of `□_Q` (even legs of `A_Q` × odd legs of `B_Q`)
vanish. Orthogonal means mesh variable `0` (mesh language). -/
def NLSM.Amplitude.earLocus (n : ℕ) (R : Finset ℕ) (K : Finset (ℕ × ℕ)) (X : ℕ × ℕ → ℚ) : Prop :=
  (∀ a ∈ Icc 1 n, ∀ b ∈ Icc 1 n, a % 2 = 1 → a ∉ R → b % 2 = 1 → b ∉ R → mesh n X a b = 0) ∧
  (∀ a ∈ Icc 1 n, a % 2 = 1 → a ∉ R → ∀ w ∈ R, mesh n X a w = 0) ∧
  ∀ Q ∈ K, ∀ w ∈ oddSide n Q, w % 2 = 0 → ∀ a ∈ evenSide n Q, a % 2 = 1 → mesh n X w a = 0

/-- A leg of the `n`-gon is in the odd-ended side of an odd chord `Q` iff it lies in
`[Q.1, Q.2)` exactly when `Q.1` is odd. -/
theorem mem_oddSide_iff_interval {n : ℕ} {Q : ℕ × ℕ} (hQ : Q ∈ oddDiagonals n) {x : ℕ}
    (hx : x ∈ Icc 1 n) : x ∈ oddSide n Q ↔ ((Q.1 ≤ x ∧ x < Q.2) ↔ Q.1 % 2 = 1) := by
  have hd := mem_diagonals.1 (mem_filter.1 hQ).1
  have hx' := mem_Icc.1 hx
  unfold oddSide
  split_ifs with h
  · rw [mem_Icc]
    constructor
    · intro hm; exact ⟨fun _ => h, fun _ => ⟨hm.1, by omega⟩⟩
    · intro hm; have := hm.2 h; omega
  · rw [mem_sdiff, mem_Icc, mem_Icc]
    constructor
    · intro hm; exact ⟨fun h' => absurd ⟨h'.1, by omega⟩ hm.2, fun h' => absurd h' h⟩
    · intro hm; exact ⟨⟨by omega, by omega⟩, fun h' => h (hm.1 ⟨h'.1, by omega⟩)⟩

/-- The odd-ended side of an odd chord consists of legs. -/
theorem oddSide_sub_Icc {n : ℕ} {Q : ℕ × ℕ} (hQ : Q ∈ oddDiagonals n) :
    oddSide n Q ⊆ Icc 1 n := by
  have hd := mem_diagonals.1 (mem_filter.1 hQ).1
  intro x hx
  unfold oddSide at hx
  split_ifs at hx
  · rw [mem_Icc] at hx ⊢; omega
  · exact (mem_sdiff.1 hx).1

-- registry: C-KMMK
/-- `earLocus` is the library's `pkRBZ5 n 1 R K` (`C8`), which reads the sides of a member `Q`
through the interval `[Q.1, Q.2)` and the legs of `R`. -/
theorem NLSM.Amplitude.earLocus_iff {n : ℕ} {R : Finset ℕ} {K : Finset (ℕ × ℕ)} {r₀ : ℕ}
    (hr₀ : r₀ ∈ R) (hK : ∀ Q ∈ K, Q ∈ oddDiagonals n ∧ R ⊆ oddSide n Q) (X : ℕ × ℕ → ℚ) :
    earLocus n R K X ↔ pkRBZ5 n 1 R K X := by
  have hR : ∀ Q ∈ K, ∀ r ∈ R, ((Q.1 ≤ r ∧ r < Q.2) ↔ Q.1 % 2 = 1) := fun Q hQ r hr =>
    (mem_oddSide_iff_interval (hK Q hQ).1 (oddSide_sub_Icc (hK Q hQ).1 ((hK Q hQ).2 hr))).1
      ((hK Q hQ).2 hr)
  have same : ∀ Q ∈ K, ∀ x ∈ Icc 1 n,
      ((∀ r ∈ R, ((Q.1 ≤ x ∧ x < Q.2) ↔ (Q.1 ≤ r ∧ r < Q.2))) ↔ x ∈ oddSide n Q) := by
    intro Q hQ x hx
    rw [mem_oddSide_iff_interval (hK Q hQ).1 hx]
    constructor
    · intro h; rw [h r₀ hr₀, hR Q hQ r₀ hr₀]
    · intro h r hr; rw [h, hR Q hQ r hr]
  have other : ∀ Q ∈ K, ∀ x ∈ Icc 1 n,
      ((∀ r ∈ R, ¬ ((Q.1 ≤ x ∧ x < Q.2) ↔ (Q.1 ≤ r ∧ r < Q.2))) ↔ x ∉ oddSide n Q) := by
    intro Q hQ x hx
    rw [mem_oddSide_iff_interval (hK Q hQ).1 hx]
    constructor
    · intro h; rw [← hR Q hQ r₀ hr₀]; exact h r₀ hr₀
    · intro h r hr; rwa [hR Q hQ r hr]
  unfold earLocus pkRBZ5
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h Q hQ w hw a ha hw2 ha2 haR hwR haR' => ?_,
    fun h Q hQ w hw hw2 a ha ha2 => ?_⟩)
  · exact h Q hQ w ((same Q hQ w hw).1 hwR) (by omega) a
      (mem_sdiff.2 ⟨ha, (other Q hQ a ha).1 haR'⟩) ha2
  · have hwI := oddSide_sub_Icc (hK Q hQ).1 hw
    obtain ⟨haI, haQ⟩ := mem_sdiff.1 ha
    exact h Q hQ w hwI a haI (by omega) ha2 (fun haR => haQ ((hK Q hQ).2 haR))
      ((same Q hQ w hwI).2 hw) ((other Q hQ a haI).2 haQ)

open MvPolynomial in
-- registry: C-KMMK
/-- **The ear lemma** (its conclusion `N^{¬K}(𝖯_Q) ≡ 0` is a step of the proof). Let `𝖯` be the
`n`-gon (`n ≥ 4` even) with legs, cyclically, `s = n`, `U = 1..lo−1`, `R = lo..hi`, `V = hi+1..n−1`:
`U`, `V` of even length, not both empty, `R` of odd length with odd end legs (position parity
opposite to `s`). Let `K` be a set of members (odd chords that separate `s` from `R`: `R ⊆ A_Q`,
`s ∉ A_Q`; they cut `U` and `V` into arcs of even length), and assume (gen): no odd diagonal of `𝖯`
vanishes identically on the locus `Z′` (`earLocus`). Then on `Z′`, `N` of `𝖯`, `N` of the
sub-polygon between `s` and `Q` (the B-child of `Q`) for each `Q ∈ K`, and `N^{¬K}` of `𝖯` vanish
(each restricts to the zero rational function). The paper's further hypothesis "`K` contains the
chord that cuts off `R` if `|R| ≥ 3`" is not needed. -/
theorem NLSM.Amplitude.polygon_numerators_vanish_on_ear_locus {n : ℕ} (hn : 4 ≤ n) (hE : Even n)
    {lo hi : ℕ} (hlo : lo % 2 = 1) (hhi : hi % 2 = 1) (hlh : lo ≤ hi) (h2 : hi < n)
    (hUV : 1 < lo ∨ hi + 1 < n) {K : Finset (ℕ × ℕ)}
    (hK : ∀ Q ∈ K, Q ∈ oddDiagonals n ∧ Icc lo hi ⊆ oddSide n Q ∧ n ∉ oddSide n Q)
    (hgen : ∀ d ∈ oddDiagonals n, ∃ X, earLocus n (Icc lo hi) K X ∧ X d ≠ 0) :
    RatZeroOn {X | earLocus n (Icc lo hi) K X} (NLSM n gen) ∧
    (∀ Q ∈ K, RatZeroOn {X | earLocus n (Icc lo hi) K X} (childAmpB n Q)) ∧
    RatZeroOn {X | earLocus n (Icc lo hi) K X} (nlsmAvoiding n K gen) := by
  have hE' : n % 2 = 0 := Nat.even_iff.1 hE
  have hlo' : lo ∈ Icc lo hi := mem_Icc.2 ⟨le_rfl, hlh⟩
  have hset : {X | earLocus n (Icc lo hi) K X} = {X | pkRBZ5 n 1 (Icc lo hi) K X} :=
    Set.ext fun X => earLocus_iff hlo' (fun Q hQ => ⟨(hK Q hQ).1, (hK Q hQ).2.1⟩) X
  have hgen' : ∀ d ∈ oddDiagonals n, ∃ w ∈ {X | pkRBZ5 n 1 (Icc lo hi) K X},
      eval w (X d : MvPolynomial (ℕ × ℕ) ℚ) ≠ 0 := fun d hd => by
    obtain ⟨w, hw, hwd⟩ := hgen d hd
    exact ⟨w, (earLocus_iff hlo' (fun Q hQ => ⟨(hK Q hQ).1, (hK Q hQ).2.1⟩) w).1 hw,
      by simpa using hwd⟩
  have hVs := pkR_b_Z5_sub n 1 (Icc lo hi) K
  rw [hset]
  -- two even legs outside `R`: `s` and one leg of `U` or `V`
  have ht1 : n ∈ pkRBT5 n 1 (Icc lo hi) :=
    mem_filter.2 ⟨mem_Icc.2 ⟨by omega, le_rfl⟩, by omega, fun h => by rw [mem_Icc] at h; omega⟩
  obtain ⟨t₂, ht2, h12⟩ : ∃ t₂, t₂ ∈ pkRBT5 n 1 (Icc lo hi) ∧ n ≠ t₂ := by
    rcases hUV with h | h
    · exact ⟨lo - 1, mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega,
        fun h' => by rw [mem_Icc] at h'; omega⟩, by omega⟩
    · exact ⟨hi + 1, mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega,
        fun h' => by rw [mem_Icc] at h'; omega⟩, by omega⟩
  have wit : ∀ (s : Finset (ℕ × ℕ)) (ρ : ℕ × ℕ → ℕ × ℕ), (∀ d ∈ s, ρ d ∈ oddDiagonals n) →
      ∃ w ∈ {X | pkRBZ5 n 1 (Icc lo hi) K X},
        eval w (∏ d ∈ s, (X (ρ d) : MvPolynomial (ℕ × ℕ) ℚ)) ≠ 0 := by
    intro s ρ hρ
    obtain ⟨w, hw, hall⟩ := pkR_avoid hVs (fun d => (X (ρ d) : MvPolynomial (ℕ × ℕ) ℚ)) s
      fun d hd => hgen' _ (hρ d hd)
    exact ⟨w, hw, by rw [map_prod]; exact prod_ne_zero_iff.2 hall⟩
  refine ⟨?_, fun Q hQ => ?_, ?_⟩
  · -- `N(𝖯) ≡ 0`
    refine ⟨NP ℚ n, oddDen ℚ n, ?_, wit _ id fun d hd => hd, fun x hx =>
      pkR_b_R5a_NP hE' hn (by norm_num) hx pkR_b_ivl_RR ht1 ht2 h12⟩
    rw [nlsm_numerator_hom (algebraMap _ RF) (by omega) (fun d _ => gen_ne_zero d)]
    rfl
  · -- `N(𝖯_Q) ≡ 0`
    obtain ⟨hQo, hRQ, -⟩ := hK Q hQ
    have f1 := pkR_b_head_facts hE' hQo
    have hts : 1 ≤ tailStart Q ∧ tailStart Q ≤ n := by
      have hd := mem_diagonals.1 (mem_filter.1 hQo).1
      rcases pkR_b_tail_data hQo with e | e <;> omega
    have htl : tailLen n Q = n - headLen n Q := rfl
    have h := nlsm_numerator_hom ((algebraMap _ RF).comp (rename (relab n (tailStart Q))).toRingHom)
      (N := tailLen n Q + 1) (by omega) (fun d _ => by simp)
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, rename_X] at h
    refine ⟨rename (relab n (tailStart Q)) (NP ℚ (tailLen n Q + 1)),
      rename (relab n (tailStart Q)) (oddDen ℚ (tailLen n Q + 1)), h.symm, ?_, fun x hx =>
        pkR_b_R5bT hE' hn hQo hRQ hQ hx⟩
    obtain ⟨w, hw, hne⟩ := wit (oddDiagonals (tailLen n Q + 1)) (relab n (tailStart Q))
      fun d hd => pkR_w_relab_odd hE' hts (by omega) hd
    refine ⟨w, hw, ?_⟩
    simpa [oddDen, map_prod] using hne
  · -- `N^{¬K}(𝖯) ≡ 0`
    have hnc : ∀ Q ∈ K, ∀ Q' ∈ K, ¬ Crosses Q' Q → oddSide n Q ⊆ oddSide n Q' ∨
        oddSide n Q' ⊆ oddSide n Q := by
      intro Q hQ Q' hQ' hc
      obtain ⟨q1, q2⟩ := Q
      obtain ⟨r1, r2⟩ := Q'
      exact (((pkR_b_R1 (hK _ hQ').1 (hK _ hQ).1 ((hK _ hQ').2.1 hlo') ((hK _ hQ).2.1 hlo')
        ⟨by omega, le_rfl⟩ (hK _ hQ').2.2 (hK _ hQ).2.2).1 hc).symm)
    have e := nlsmAvoiding_numerator_hom (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) RF)
      (n := n) (by omega) K (fun d _ => gen_ne_zero d)
    refine ⟨pkRBNP ℚ n K, ∏ d ∈ oddDiagonals n \ K, X d, ?_,
      wit _ id fun d hd => (mem_sdiff.1 hd).1, fun x hx =>
        pkR_d2_R5d hE' hn (fun Q hQ => (hK Q hQ).1) hnc (fun x hx => by
          rw [mem_Icc] at hx ⊢; omega) (fun Q hQ => (hK Q hQ).2.1) hlo' hlo pkR_b_ivl_RR
          ht1 ht2 h12 x hx⟩
    rw [e, map_prod]
    rfl

/-! ## The polygon with a marked leg and its marked locus

The `n`-gon with a marked leg `r` is the library's standard polygon `(n, d₁)` (`C6`), `r = 2d₁ + 1`.
Its Gram model (`gram_model`), the genericity clauses and the regions (`genericity` and companions)
and the value on the marked locus (a non-zero constant `c`: `polygon_numerator_value`). Parts of
the Gram model and of the genericity clauses that only an earlier proof of the value used are not
formalised; the library proves the value another way (`pkR_omega`). -/

/-! Genericity and regions on the polygon with a marked leg. The library's standard polygon
`(n, d₁)` labels the paper's legs `s, u₁, …, u_{2d₁}, r, v₁, …, v_{2d₂}` as
`s = n`, `u_k = k`, `r = 2d₁ + 1`, `v_k = 2d₁ + 1 + k` (`n = 2d + 2`, `d₂ = n/2 − 1 − d₁`); class
`π` is the even legs. A member (a chord over `r`) `Q = (i, j)` has `A_Q = [2i + 1, 2d₁ + 2j + 1]`
(`pkRHead`) and chord `(2i + 1, 2d₁ + 2j + 2)` (`pkRMchord`); `pkRIsMem` excludes `Q_⊥ = (d₁, 0)`
and `Q_⊤ = (0, d₂)`. `x = c⋆ = c_{1,n−1}`, `c⋆′` is `pkRCstp`, `Λ^I` is `pkRLam`, `W_q` is `pkRW`,
`c∘ = τ_q` is `pkRTau`, `□_Q` is `pkRMinrect`. -/

-- registry: C-5DFW
/-- **Genericity (G)**: no odd diagonal of the polygon with a marked leg vanishes identically on
`Λ₀ = Λ ∩ {x = 0}`. -/
theorem NLSM.Amplitude.genericity {n : ℕ} (hE : Even n) (hn : 4 ≤ n) (d₁ : ℕ) (hd : 2 * d₁ + 2 ≤ n)
    {Q : ℕ × ℕ} (hQ : Q ∈ oddDiagonals n) :
    ∃ X : ℕ × ℕ → ℚ, pkRLam n d₁ ∅ X ∧ mesh n X 1 (n - 1) = 0 ∧ X Q ≠ 0 :=
  pkR_G (Nat.even_iff.1 hE) hn d₁ hd hQ

-- registry: C-5DFW
/-- **Genericity (G′)**: for distinct odd diagonals `Q`, `Q′`, `X_{Q′}` is not in the span of
`X_Q` and `x` on `Λ`. -/
theorem NLSM.Amplitude.genericity_span {n : ℕ} (hE : Even n) (hn : 4 ≤ n) (d₁ : ℕ)
    (hd : 2 * d₁ + 2 ≤ n) {Q Q' : ℕ × ℕ} (hQ : Q ∈ oddDiagonals n) (hQ' : Q' ∈ oddDiagonals n)
    (hne : Q ≠ Q') :
    ¬ ∃ α β : ℚ, ∀ X : ℕ × ℕ → ℚ, pkRLam n d₁ ∅ X →
      X Q' = α * X Q + β * mesh n X 1 (n - 1) := by
  rintro ⟨α, β, h⟩
  obtain ⟨X, hX, hx, hXQ, hXQ'⟩ := pkR_G2 (Nat.even_iff.1 hE) hn d₁ hd hQ hQ' hne
  exact hXQ' (by rw [h X hX, hXQ, hx]; ring)

-- registry: C-5DFW
/-- **Genericity (G″)**: if `d₁ ≥ 1`, let `b′` be the member `(d₁ − 1, 0)`, the chord cutting
off `(u_{2d₁−1}, u_{2d₁}, r)`, and `Λ″ = Λ^{b′}`. Every odd diagonal other than `b′` does not
vanish identically on `Λ″₀`. -/
theorem NLSM.Amplitude.genericity_double_prime {n : ℕ} (hE : Even n) (hn : 4 ≤ n) (d₁ : ℕ)
    (hd1 : 1 ≤ d₁) (hd : 2 * d₁ + 2 ≤ n) {Q : ℕ × ℕ} (hQ : Q ∈ oddDiagonals n)
    (hne : Q ≠ pkRMchord d₁ (d₁ - 1, 0)) :
    ∃ X : ℕ × ℕ → ℚ, pkRLam n d₁ {(d₁ - 1, 0)} X ∧ mesh n X 1 (n - 1) = 0 ∧ X Q ≠ 0 :=
  pkR_G3 (Nat.even_iff.1 hE) hn d₁ hd1 hd hQ hne

-- registry: C-5DFW
/-- **Genericity (W-ind)**, for `c∘ = τ_q` (the mesh variable of the two end legs of `A_q`) and
the mixed set `□_q`, `q` a member, i.e. on `W = W_q` (the only instance a proof uses):
`c⋆′ = c⋆ + c∘` on `W_q`, and `c⋆`, `c⋆′` are linearly independent on `W_q`. -/
theorem NLSM.Amplitude.genericity_w_independent {n : ℕ} (hE : Even n) (hn : 4 ≤ n) {d₁ : ℕ}
    {q : ℕ × ℕ} (hq : pkRIsMem n d₁ q) :
    (∀ X : ℕ × ℕ → ℚ, pkRW n d₁ q X →
      mesh n X (pkRCstp n d₁).1 (pkRCstp n d₁).2 =
        mesh n X 1 (n - 1) + mesh n X (pkRTau d₁ q).1 (pkRTau d₁ q).2) ∧
    ∀ α β : ℚ, (∀ X : ℕ × ℕ → ℚ, pkRW n d₁ q X →
      α * mesh n X 1 (n - 1) + β * mesh n X (pkRCstp n d₁).1 (pkRCstp n d₁).2 = 0) →
        α = 0 ∧ β = 0 := by
  have hE' : n % 2 = 0 := Nat.even_iff.1 hE
  obtain ⟨i, j⟩ := q
  obtain ⟨hi, hj, hb, ha⟩ := (pkR_isMem_iff _ _ _).1 hq
  dsimp only at hi hj hb ha
  refine ⟨fun X hX => ?_, fun α β h => ?_⟩
  · obtain ⟨hz, -⟩ := (pkR_W_iff _ _ _ _).1 hX
    have l := lemma65 hn hE X
    have hcs : pkRCstp n d₁ ∈ (diagonals n).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0) := by
      unfold pkRCstp
      split_ifs <;> exact mem_filter.2 ⟨mem_diagonals.2 (by dsimp only; omega), by omega⟩
    have hee : ∑ t ∈ (diagonals n).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0), mesh n X t.1 t.2 =
        mesh n X (pkRCstp n d₁).1 (pkRCstp n d₁).2 := by
      refine sum_eq_single_of_mem _ hcs fun t ht htc => ?_
      obtain ⟨htd, hp⟩ := mem_filter.1 ht
      have h' := mem_diagonals.1 htd
      refine hz t.1 (mem_Icc.2 ⟨by omega, by omega⟩) t.2 (mem_Icc.2 ⟨by omega, by omega⟩)
        (by omega) (by omega) (fun e => by have := congrArg Prod.snd e; simp at this; omega)
        (fun e => htc (Prod.ext (congrArg Prod.fst e) (congrArg Prod.snd e))) ?_
      intro e
      have := congrArg Prod.fst e
      simp [pkRTau] at this
      omega
    have h1 : ((1, n - 1) : ℕ × ℕ) ∈ (diagonals n).filter (fun p => p.1 % 2 = 1 ∧ p.2 % 2 = 1) :=
      mem_filter.2 ⟨mem_diagonals.2 (by dsimp only; omega), by dsimp only; omega⟩
    have h2 : pkRTau d₁ (i, j) ∈ (diagonals n).filter (fun p => p.1 % 2 = 1 ∧ p.2 % 2 = 1) :=
      mem_filter.2 ⟨mem_diagonals.2 (by simp only [pkRTau]; omega), by simp only [pkRTau]; omega⟩
    have h12 : ((1, n - 1) : ℕ × ℕ) ≠ pkRTau d₁ (i, j) := by
      intro e
      simp only [pkRTau, Prod.mk.injEq] at e
      omega
    have hoo : ∑ t ∈ (diagonals n).filter (fun p => p.1 % 2 = 1 ∧ p.2 % 2 = 1), mesh n X t.1 t.2 =
        mesh n X 1 (n - 1) + mesh n X (pkRTau d₁ (i, j)).1 (pkRTau d₁ (i, j)).2 := by
      rw [← sum_pair (f := fun t : ℕ × ℕ => mesh n X t.1 t.2) h12]
      refine (sum_subset (insert_subset h1 (singleton_subset_iff.2 h2)) fun t ht hn' => ?_).symm
      obtain ⟨htd, hp⟩ := mem_filter.1 ht
      have h' := mem_diagonals.1 htd
      rw [mem_insert, mem_singleton, not_or] at hn'
      refine hz t.1 (mem_Icc.2 ⟨by omega, by omega⟩) t.2 (mem_Icc.2 ⟨by omega, by omega⟩)
        (by omega) (by omega) (fun e => hn'.1 (Prod.ext (congrArg Prod.fst e)
          (congrArg Prod.snd e))) ?_ (fun e => hn'.2 (Prod.ext (congrArg Prod.fst e)
          (congrArg Prod.snd e)))
      intro e
      have := congrArg Prod.fst e
      unfold pkRCstp at this
      split_ifs at this <;> simp at this <;> omega
    rw [← hee, l, hoo]
  · obtain ⟨X₁, hX₁, hx₁, hc₁⟩ := pkR_Wind1 hE' hn hi hj hb ha
    obtain ⟨X₂, hX₂, hx₂, hc₂⟩ := pkR_Wind2 hE' hn hi hj hb ha
    have e1 := h X₁ hX₁
    have e2 := h X₂ hX₂
    rw [hx₁, mul_zero, zero_add] at e1
    rw [hc₂, mul_zero, add_zero] at e2
    exact ⟨(mul_eq_zero.1 e2).resolve_right hx₂, (mul_eq_zero.1 e1).resolve_right hc₁⟩

-- registry: C-5DFW
/-- **Genericity (G^I)**: if `I` is closed (`Î = I ∪ {Q_⊤, Q_⊥}` closed under meet and join),
no odd diagonal that is not (the chord of) a member of `I` vanishes identically on `Λ^I₀`. -/
theorem NLSM.Amplitude.genericity_closed {n : ℕ} (hE : Even n) (hn : 4 ≤ n) {d₁ : ℕ}
    (hd : 2 * d₁ + 2 ≤ n) {I : Finset (ℕ × ℕ)} (hI : ∀ Q ∈ I, pkRIsMem n d₁ Q)
    (hcl : pkRClosed n d₁ I) {Q : ℕ × ℕ} (hQ : Q ∈ oddDiagonals n)
    (hnot : ∀ Q' ∈ I, Q ≠ pkRMchord d₁ Q') :
    ∃ X : ℕ × ℕ → ℚ, pkRLam n d₁ I X ∧ mesh n X 1 (n - 1) = 0 ∧ X Q ≠ 0 :=
  pkR_GI (Nat.even_iff.1 hE) hn hd (fun Q' hQ' => ⟨(hI Q' hQ').1, (hI Q' hQ').2.1⟩) hcl hQ hnot

-- registry: C-5DFW
/-- **Genericity (G_W)**, the non-vanishing and non-proportionality the library proves: for a
member `q` and every odd diagonal `Q` other than the chord of `q` (in particular the chords of
`Q ∈ I ∖ q`), on `W_q` the forms `c⋆`, `c⋆′`, `X_Q` are non-zero and `c⋆`, `c⋆′` and `X_Q`, `c⋆`
and `X_Q`, `c⋆′` are pairwise non-proportional (neither is a constant multiple of the other). Two
such chords `X_Q`, `X_{Q′}` are not stated here; the library's `pkR_GW_pair` states them. -/
theorem NLSM.Amplitude.genericity_w_pairs {n : ℕ} (hE : Even n) (hn : 4 ≤ n) {d₁ : ℕ} {q : ℕ × ℕ}
    (hq : pkRIsMem n d₁ q) {Q : ℕ × ℕ} (hQ : Q ∈ oddDiagonals n) (hne : Q ≠ pkRMchord d₁ q) :
    let cs : (ℕ × ℕ → ℚ) → ℚ := fun X => mesh n X 1 (n - 1)
    let cp : (ℕ × ℕ → ℚ) → ℚ := fun X => mesh n X (pkRCstp n d₁).1 (pkRCstp n d₁).2
    let xQ : (ℕ × ℕ → ℚ) → ℚ := fun X => X Q
    let nonProp : ((ℕ × ℕ → ℚ) → ℚ) → ((ℕ × ℕ → ℚ) → ℚ) → Prop := fun f g =>
      ∀ c : ℚ, ¬ ∀ X, pkRW n d₁ q X → f X = c * g X
    (∃ X, pkRW n d₁ q X ∧ cs X ≠ 0) ∧ (∃ X, pkRW n d₁ q X ∧ cp X ≠ 0) ∧
      (∃ X, pkRW n d₁ q X ∧ xQ X ≠ 0) ∧
      nonProp cs cp ∧ nonProp cp cs ∧ nonProp xQ cs ∧ nonProp cs xQ ∧ nonProp xQ cp ∧
        nonProp cp xQ := by
  intro cs cp xQ nonProp
  have hE' : n % 2 = 0 := Nat.even_iff.1 hE
  obtain ⟨i, j⟩ := q
  obtain ⟨hi, hj, hb, ha⟩ := (pkR_isMem_iff _ _ _).1 hq
  dsimp only at hi hj hb ha
  obtain ⟨X₁, hX₁, hx₁, hc₁⟩ := pkR_Wind1 hE' hn hi hj hb ha
  obtain ⟨X₂, hX₂, hx₂, hc₂⟩ := pkR_Wind2 hE' hn hi hj hb ha
  obtain ⟨X₃, hX₃, hx₃, hc₃, hQ₃⟩ := pkR_GW_Q hE' hn hi hj hb hQ hne
  obtain ⟨X₄, hX₄, hQ₄, hx₄⟩ := pkR_GW_star hE' hn hi hj hb ha hQ hne
  obtain ⟨X₅, hX₅, hQ₅, hc₅⟩ := pkR_GW_starp hE' hn hi hj hb ha hQ hne
  -- `f = λ g` fails at a point where `g = 0 ≠ f`
  have key : ∀ f g : (ℕ × ℕ → ℚ) → ℚ, ∀ X, pkRW n d₁ (i, j) X → g X = 0 → f X ≠ 0 →
      nonProp f g := fun f g X hX hg hf c h => hf (by rw [h X hX, hg, mul_zero])
  exact ⟨⟨X₂, hX₂, hx₂⟩, ⟨X₁, hX₁, hc₁⟩, ⟨X₃, hX₃, hQ₃⟩, key _ _ X₂ hX₂ hc₂ hx₂,
    key _ _ X₁ hX₁ hx₁ hc₁, key _ _ X₃ hX₃ hx₃ hQ₃, key _ _ X₄ hX₄ hQ₄ hx₄,
    key _ _ X₃ hX₃ hc₃ hQ₃, key _ _ X₅ hX₅ hQ₅ hc₅⟩

-- registry: C-5DFW
/-- `Λ^I` only gets weaker for a smaller `I`. -/
theorem NLSM.Amplitude.markedLocus_mono {n d₁ : ℕ} {I I' : Finset (ℕ × ℕ)} (h : I' ⊆ I)
    {X : ℕ × ℕ → ℚ} (hX : pkRLam n d₁ I X) : pkRLam n d₁ I' X :=
  ⟨hX.1, hX.2.1, fun Q hQ => hX.2.2 Q (h hQ)⟩

-- registry: C-5DFW
/-- **Regions**, for `I` a set of members, the parts the library proves: on `Λ^I`,
(a) `X_Q = x` for every `Q ∈ I`; (b) for `q ∈ I`, the region `Ω(q, Q_⊥)` between `q` and `r` (the
A-side child of `q`, read by `relab n (2i + 1)`) is a standard polygon `(|A_q| + 1, d₁ − i)` on
its locus `Λ^J`, `J` the members of `I` strictly between `q` and `Q_⊥` shifted by `(i, 0)`, with
the same `x`; (c) likewise the region `Ω(Q_⊤, q)` between `s` and `q` (the B-side child, read in
the rotated labelling of `pkR_childB`), `(|B_q| + 1, i)`, `J` the members strictly between
`Q_⊤` and `q` shifted by `(0, j)`. That a standard polygon on `Λ^J` has every same-class mesh
variable `0` except its two sides of mass `x`, and `□^Ω_Q ⊆ □_Q`, is the definition of `Λ^J`. -/
theorem NLSM.Amplitude.genericity_regions {n : ℕ} (hE : Even n) (hn : 4 ≤ n) {d₁ : ℕ}
    {I : Finset (ℕ × ℕ)} (hI : ∀ Q ∈ I, pkRIsMem n d₁ Q) {X : ℕ × ℕ → ℚ} (hX : pkRLam n d₁ I X) :
    (∀ Q ∈ I, X (pkRMchord d₁ Q) = mesh n X 1 (n - 1)) ∧
    (∀ q ∈ I, pkRLam (2 * d₁ + 2 * q.2 + 2 - (2 * q.1 + 1) + 1) (d₁ - q.1)
        ((I.filter (fun Q => q.1 ≤ Q.1 ∧ Q.2 ≤ q.2 ∧ Q ≠ q)).image (fun Q => (Q.1 - q.1, Q.2)))
        (X ∘ relab n (2 * q.1 + 1)) ∧
      mesh (2 * d₁ + 2 * q.2 + 2 - (2 * q.1 + 1) + 1) (X ∘ relab n (2 * q.1 + 1)) 1
        (2 * d₁ + 2 * q.2 + 2 - (2 * q.1 + 1) + 1 - 1) = mesh n X 1 (n - 1)) ∧
    ∀ q ∈ I, pkRLam (n - (2 * d₁ + 2 * q.2 + 2) + (2 * q.1 + 1) + 1) q.1
        ((I.filter (fun Q => Q.1 ≤ q.1 ∧ q.2 ≤ Q.2 ∧ Q ≠ q)).image (fun Q => (Q.1, Q.2 - q.2)))
        (X ∘ (relab n (2 * d₁ + 2 * q.2 + 2) ∘
          (rot (n - (2 * d₁ + 2 * q.2 + 2) + (2 * q.1 + 1) + 1))^[n - (2 * d₁ + 2 * q.2 + 2) +
            1])) ∧ mesh (n - (2 * d₁ + 2 * q.2 + 2) + (2 * q.1 + 1) + 1)
          (X ∘ (relab n (2 * d₁ + 2 * q.2 + 2) ∘
            (rot (n - (2 * d₁ + 2 * q.2 + 2) + (2 * q.1 + 1) + 1))^[n - (2 * d₁ + 2 * q.2 + 2) +
              1])) 1 (n - (2 * d₁ + 2 * q.2 + 2) + (2 * q.1 + 1) + 1 - 1) = mesh n X 1 (n - 1) := by
  have hE' : n % 2 = 0 := Nat.even_iff.1 hE
  refine ⟨fun Q hQ => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · obtain ⟨m1, m2, m3, m4⟩ := (pkR_isMem_iff _ _ _).1 (hI Q hQ)
    have hm := pkR_mchord_mem m1 m2 m3 m4
    have hmd := mem_diagonals.1 (mem_filter.1 hm).1
    have e := pkR_XQ hE' hn m1 m2 m3 m4 hX (hX.2.2 Q hQ)
    simp only [pkRMchord] at hmd hm ⊢
    rw [planar_of_mem X (by omega) (by omega) (by omega), ite_eq_left (mem_filter.1 hm).1] at e
    exact e
  · obtain ⟨i, j⟩ := q
    obtain ⟨m1, m2, m3, m4⟩ := (pkR_isMem_iff _ _ _).1 (hI _ hq)
    obtain ⟨h1, h2⟩ := pkR_childA hE' hn m1 m2 m3 m4 hq hX
    refine ⟨markedLocus_mono ?_ h1, h2⟩
    intro Q' hQ'
    obtain ⟨Q, hQ, rfl⟩ := mem_image.1 hQ'
    obtain ⟨hQI, a1, a2, -⟩ := mem_filter.1 hQ
    have := ((pkR_isMem_iff _ _ _).1 (hI Q hQI)).1
    exact mem_image.2 ⟨Q, mem_filter.2 ⟨hQI, a1, by dsimp only at a1 ⊢; omega, Nat.zero_le _,
      by dsimp only at a2 ⊢; omega⟩, by simp⟩
  · obtain ⟨i, j⟩ := q
    obtain ⟨m1, m2, m3, m4⟩ := (pkR_isMem_iff _ _ _).1 (hI _ hq)
    obtain ⟨h1, h2⟩ := pkR_childB hE' hn m1 m2 m3 m4 hq hX
    refine ⟨markedLocus_mono ?_ h1, h2⟩
    intro Q' hQ'
    obtain ⟨Q, hQ, rfl⟩ := mem_image.1 hQ'
    obtain ⟨hQI, a1, a2, -⟩ := mem_filter.1 hQ
    have := ((pkR_isMem_iff _ _ _).1 (hI Q hQI)).2.1
    exact mem_image.2 ⟨Q, mem_filter.2 ⟨hQI, Nat.zero_le _, by dsimp only at a1 ⊢; omega,
      a2, by dsimp only at a2 ⊢; omega⟩, by simp⟩

-- registry: C-27FF
/-- **The value on the marked locus** (a non-zero constant `c`; the value `(−1)^d` is a remark,
not formalised). Let `𝖯` be the
standard polygon `(n, d₁)` (legs `s = n`, `r = 2d₁ + 1`, `2d₁ + 2 ≤ n`, `n ≥ 4` even), `I` a closed
set of members (`pkRIsMem`, `pkRClosed`), `Λ^I = pkRLam n d₁ I`, `x = c⋆ = c_{1,n−1}` and `D′`
the product of the odd diagonals that are not chords of `I`. There are `c ≠ 0` and a polynomial `F`
with `N(𝖯) = c·x + x²·R`, `R = F / D′`, at every point of `Λ^I` where the odd diagonals are
non-zero; so `R` is regular wherever the odd diagonals not in `I` are non-zero. And `D′` does not
vanish identically on `Λ^I₀` (`x = 0`; this is where closedness enters, (G^I)). Points of `Λ^I`
where the odd diagonals are non-zero exist for `n = 6`, `d₁ = 1` and `I = {(0, 0)}`
(`PaperTests.marked_locus_nonvacuous`; the same point lies on `Λ^∅`); for every closed `I` this is
not shown here. -/
theorem NLSM.Amplitude.polygon_numerator_value {n : ℕ} (hE : Even n) (hn : 4 ≤ n) (d₁ : ℕ)
    (hd : 2 * d₁ + 2 ≤ n) (I : Finset (ℕ × ℕ)) (hI : ∀ Q ∈ I, pkRIsMem n d₁ Q)
    (hcl : pkRClosed n d₁ I) :
    ∃ (c : ℚ) (F : MvPolynomial (ℕ × ℕ) ℚ), c ≠ 0 ∧
      (∀ X : ℕ × ℕ → ℚ, pkRLam n d₁ I X → (∀ d ∈ oddDiagonals n, X d ≠ 0) →
        NLSM n X = c * mesh n X 1 (n - 1) + mesh n X 1 (n - 1) ^ 2 *
          (MvPolynomial.eval X F /
            ∏ Q ∈ (oddDiagonals n).filter (fun Q => Q ∉ I.image (pkRMchord d₁)), X Q)) ∧
      ∃ X : ℕ × ℕ → ℚ, pkRLam n d₁ I X ∧ mesh n X 1 (n - 1) = 0 ∧
        ∏ Q ∈ (oddDiagonals n).filter (fun Q => Q ∉ I.image (pkRMchord d₁)), X Q ≠ 0 := by
  have hE' : n % 2 = 0 := Nat.even_iff.1 hE
  obtain ⟨c, F, hc, hF⟩ := pkR_omega hE' hn d₁ hd I hI
  set D := (oddDiagonals n).filter (fun Q => Q ∉ I.image (pkRMchord d₁)) with hD
  have himg : I.image (pkRMchord d₁) ⊆ oddDiagonals n := fun Q hQ => by
    obtain ⟨Q', hQ', rfl⟩ := mem_image.1 hQ
    obtain ⟨h1, h2, h3, h4⟩ := hI Q' hQ'
    exact pkR_mchord_mem h1 h2 h3 h4
  refine ⟨c, F, hc, fun X hX hX0 => ?_, ?_⟩
  · -- the odd chords: the member chords (each `= x`) and `D′`
    have hmem : ∀ Q ∈ I, X (pkRMchord d₁ Q) = mesh n X 1 (n - 1) := by
      intro Q hQ
      obtain ⟨h1, h2, h3, h4⟩ := hI Q hQ
      have hdg := (mem_filter.1 (pkR_mchord_mem h1 h2 h3 h4)).1
      have hdg' := mem_diagonals.1 hdg
      rw [← pkR_XQ hE' hn h1 h2 h3 h4 hX (hX.2.2 Q hQ)]
      change X (2 * Q.1 + 1, 2 * d₁ + 2 * Q.2 + 2) = _
      rw [planar_of_mem X (by omega) (by omega) (by omega),
        ite_eq_left (show (2 * Q.1 + 1, 2 * d₁ + 2 * Q.2 + 2) ∈ diagonals n from hdg)]
    have hprod : ∏ d ∈ oddDiagonals n, X d =
        mesh n X 1 (n - 1) ^ I.card * ∏ Q ∈ D, X Q := by
      rw [← prod_filter_mul_prod_filter_not (oddDiagonals n)
        (fun Q => Q ∈ I.image (pkRMchord d₁))]
      congr 1
      rw [filter_mem_eq_inter, inter_eq_right.2 himg,
        prod_image fun a _ b _ e => pkR_mchord_inj e, prod_congr rfl hmem, prod_const]
    have hnum := nlsm_numerator_hom (MvPolynomial.eval X) (N := n) (by omega)
      (fun d hd => by simpa using hX0 d hd)
    simp only [MvPolynomial.eval_X, oddDen, map_prod] at hnum
    rw [hF X hX, hprod] at hnum
    have hDne : ∏ Q ∈ D, X Q ≠ 0 := prod_ne_zero_iff.2 fun Q hQ => hX0 Q (mem_filter.1 hQ).1
    have hxI : mesh n X 1 (n - 1) ^ I.card ≠ 0 := by
      rcases I.eq_empty_or_nonempty with h | ⟨Q, hQ⟩
      · rw [h, card_empty, pow_zero]; exact one_ne_zero
      · refine pow_ne_zero _ ?_
        rw [← hmem Q hQ]
        exact hX0 _ (himg (mem_image_of_mem _ hQ))
    have e := mul_left_cancel₀ hxI (show
      mesh n X 1 (n - 1) ^ I.card * (NLSM n X * ∏ Q ∈ D, X Q) =
        mesh n X 1 (n - 1) ^ I.card * (c * mesh n X 1 (n - 1) * ∏ Q ∈ D, X Q +
          mesh n X 1 (n - 1) ^ 2 * MvPolynomial.eval X F) by linear_combination (-1 : ℚ) * hnum)
    field_simp
    linear_combination e
  · -- (G^I): every factor of `D′` is non-zero somewhere on `Λ^I₀`
    have hsub : pkRSub {X : ℕ × ℕ → ℚ | pkRLam n d₁ I X ∧
        MvPolynomial.eval X (pkRMeshP n 1 (n - 1)) = 0} := by
      refine ⟨⟨(pkR_lam_sub n d₁ I).1, by rw [pkR_meshP_eval]; exact pkR_b_mesh_zero n 1 (n - 1)⟩,
        fun x hx y hy a b => ⟨(pkR_lam_sub n d₁ I).2 x hx.1 y hy.1 a b, ?_⟩⟩
      have := pkR_meshP_lin n 1 (n - 1) x y a b
      simp only [pkR_meshP_eval] at this hx hy ⊢
      rw [this, hx.2, hy.2]; ring
    obtain ⟨w, hw, hall⟩ := pkR_avoid hsub (fun Q => (MvPolynomial.X Q :
      MvPolynomial (ℕ × ℕ) ℚ)) D (fun Q hQ => by
        obtain ⟨hQo, hQn⟩ := mem_filter.1 hQ
        obtain ⟨X, hX, hx0, hXQ⟩ := pkR_GI hE' hn hd
          (fun Q' hQ' => ⟨(hI Q' hQ').1, (hI Q' hQ').2.1⟩) hcl hQo
          (fun Q' hQ' e => hQn (e ▸ mem_image_of_mem _ hQ'))
        exact ⟨X, ⟨hX, by rw [pkR_meshP_eval]; exact hx0⟩, by simpa using hXQ⟩)
    refine ⟨w, hw.1, by rw [← pkR_meshP_eval]; exact hw.2, prod_ne_zero_iff.2 fun Q hQ => ?_⟩
    simpa using hall Q hQ

-- registry: C-9Q5Q
/-- **The Gram model**, the parts the library's proofs use. For `n ≥ 4`
even and `G` symmetric with zero diagonal and zero row sums on legs `1..n` (`Sym⁰_n`): (1) the point
`pkRGramPt (−2G)` is `X_A(G) := Σ_{a ≠ b ∈ A} G_{ab}` at the planar variable `X_{i,j}`, `A` the arc
`i..j−1` (the map `G ↦ (X_A(G))_A`); (2) the mesh variable of two distinct legs `a`, `b` at
this point is `−2 G_{ab}`; (3) the image of the mesh map lies in the kernel of
`ρ = Σ_{class π+1} c − Σ_{class π} c`: at every point, the sum of the mesh variables of the odd–odd
pairs equals that of the even–even pairs. (That `G ↦ X(G)` is an isomorphism onto the kinematic
space and that the image is all of `ker ρ` are not formalised.) -/
theorem Amplitudes.Kinematics.Mesh.gram_model {n : ℕ} (hn : 4 ≤ n) (hE : Even n) (G : ℕ → ℕ → ℚ)
    (hs : ∀ a b, G a b = G b a) (hd : ∀ a, G a a = 0)
    (hr : ∀ a ∈ Icc 1 n, ∑ b ∈ Icc 1 n, G a b = 0) :
    (∀ i j, pkRGramPt (fun a b => -2 * G a b) (i, j) =
      ∑ p ∈ (Ico i j).offDiag, G p.1 p.2) ∧
    (∀ a ∈ Icc 1 n, ∀ b ∈ Icc 1 n, a ≠ b →
      mesh n (pkRGramPt (fun a b => -2 * G a b)) a b = -2 * G a b) ∧
    ∀ X : ℕ × ℕ → ℚ,
      ∑ t ∈ (diagonals n).filter (fun p => p.1 % 2 = 1 ∧ p.2 % 2 = 1), mesh n X t.1 t.2 =
        ∑ t ∈ (diagonals n).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0), mesh n X t.1 t.2 := by
  refine ⟨fun i j => ?_, fun a ha b hb hab => ?_, fun X => (lemma65 hn hE X).symm⟩
  · -- `X_A(G) = Σ_{c < d ∈ A} 2 G_{cd}`, by induction on the end of the arc
    have off : ∀ A : Finset ℕ, ∑ p ∈ A.offDiag, G p.1 p.2 = ∑ a ∈ A, ∑ b ∈ A, G a b := by
      intro A
      rw [← sum_product' (f := fun a b => G a b), ← diag_union_offDiag A,
        sum_union (disjoint_diag_offDiag A)]
      simp [diag, hd]
    rw [off]
    change pkRArcX _ i j = _
    rcases le_or_gt j i with hji | hij
    · rw [Ico_eq_empty_of_le hji, sum_empty, pkR_arcX_def, Ico_eq_empty_of_le hji, sum_empty,
        neg_zero]
    have hle := hij.le
    clear hij
    induction j, hle using Nat.le_induction with
    | base => rw [pkR_arcX_self, Ico_self, sum_empty]
    | succ k hik ih =>
      rw [pkR_arcX_succ _ hik, ih, Finset.sum_Ico_succ_top hik, sum_Ico_succ_top hik]
      simp only [sum_Ico_succ_top hik, sum_add_distrib, hd, add_zero]
      have hsym : ∑ x ∈ Ico i k, G k x = ∑ x ∈ Ico i k, G x k :=
        sum_congr rfl fun x _ => hs k x
      rw [hsym, ← mul_sum]
      ring
  · exact pkR_gram (by omega) _ (fun a b => by rw [hs]) (fun a => by rw [hd, mul_zero])
      (fun a ha => by rw [← mul_sum, hr a ha, mul_zero]) ha hb hab

/-! ## The children of an odd chord

The restriction to a side's child (`relab`) maps `L_S ∩ {X_P = 0}` onto the child's locus
(`child_onLocus` for "into", the library's lift for "onto"), the children's sizes, their
linkedness, and a flank class's hyperplane with its children. -/

-- registry: C-R5D5 C-XRTT
/-- **The child mesh variables pull back** (the children (1), "⊆", for the child on an arc):
let `L` be the arc of `k` legs starting at `s` (`3 ≤ k ≤ N − 3`) and `P` the chord with dual
points `s`, `s + k` (`X_P = planar N X s (s + k)`). At a point of `L_S` with `X_P = 0`, the child
point `ρ_L(X) = X ∘ relab N s` lies on the child locus of the child set (`ChildPairIn`, the
new leg `P̂` = child leg `k + 1`): a child pair inside `L` has the parent mesh variable, and a
pair `{u, P̂}` the block sum `Σ_{w ∉ L} c_{u,w}` (`pkR_subTile`; the corner terms vanish since
`X_P = 0`). -/
theorem NLSM.Zeros.child_onLocus {N s k : ℕ} (hs : s ∈ Icc 1 N) (hk3 : 3 ≤ k) (hkN : k + 3 ≤ N)
    {S : Finset (ℕ × ℕ)} {X : ℕ × ℕ → ℚ} (hX : OnLocus N S X)
    (hXP : planar N X s (s + k) = 0) :
    OnLocus (k + 1) ((diagonals (k + 1)).filter (fun σ => ChildPairIn N S s k (k + 1)
      (fun j => vtx N (s + j - 1)) σ.1 σ.2)) (fun d => X (relab N s d)) := by
  have hN1 : 1 ≤ N := by omega
  have hs' := mem_Icc.1 hs
  set m := k + 1 with hm
  set g : ℕ → ℕ := fun i => vtx N (i + s - 1) with hg
  have hcyc : pkRCycList N m g := by
    intro i hi
    have hi' := mem_Icc.1 hi
    refine ⟨mem_Icc.2 (vtx_bounds N _ hN1), ?_⟩
    by_cases him : i = m
    · subst him
      rw [show m + 1 = 1 + m by omega, vtx_add_n, vtx_of_mem le_rfl (by omega)]
      simp only [hg]
      rw [show 1 + s - 1 = s by omega, vtx_of_mem hs'.1 hs'.2]
      intro e
      have v := pkR_b_vtx2 (N := N) (u := m + s - 1) (by omega) (by omega)
      omega
    · rw [vtx_of_mem (by omega) (by omega)]
      simp only [hg]
      rw [show i + 1 + s - 1 = (i + s - 1) + 1 by omega, vtx_succ hN1]
      have b := vtx_bounds N (i + s - 1) hN1
      unfold nxt
      split_ifs <;> omega
  -- a planar variable of consecutive list points is 0, except at the new leg
  have hadj : ∀ i, 1 ≤ i → i < m → planar N X (g i) (g (i + 1)) = 0 := by
    intro i h1 h2
    refine planar_adjacent hN1 X ?_
    simp only [hg]
    rw [pkR_vtx_vtx hN1, show i + 1 + s - 1 = (i + s - 1) + 1 by omega, pkR_b_vtx_add hN1]
  have hlen : ∀ i, 1 ≤ i → i < m → pkRBlk N m g i = {g i} := by
    intro i h1 h2
    have e1 : vtx m i = i := vtx_of_mem h1 (by omega)
    have e2 : vtx m (i + 1) = i + 1 := vtx_of_mem (by omega) (by omega)
    have hl : pkRLen N m g i = 1 := by
      change (g (vtx m (i + 1)) + N - g (vtx m i)) % N = 1
      rw [e1, e2]
      simp only [hg]
      rw [show i + 1 + s - 1 = (i + s - 1) + 1 by omega, vtx_succ hN1]
      have b := vtx_bounds N (i + s - 1) hN1
      unfold nxt
      split_ifs with h
      · rw [h, show 1 + N - N = 1 by omega, Nat.mod_eq_of_lt (by omega)]
      · rw [show vtx N (i + s - 1) + 1 + N - vtx N (i + s - 1) = 1 + N by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    change Icc (g (vtx m i)) (g (vtx m i) + pkRLen N m g i - 1) = {g i}
    rw [hl, e1, Nat.add_sub_cancel, Icc_self]
  -- the block of the new leg lies outside `L`
  have hlast : ∀ b ∈ pkRBlk N m g m, vtx N b ∈ Icc 1 N ∧ vtx N b ∉ cycArc N s k := by
    intro b hb
    have e1 : vtx m m = m := vtx_of_mem (by omega) le_rfl
    have e2 : vtx m (m + 1) = 1 := by
      rw [show m + 1 = 1 + m by omega, vtx_add_n, vtx_of_mem le_rfl (by omega)]
    have gm : g m = vtx N (s + k) := by simp only [hg]; congr 1; omega
    have g1 : g 1 = s := by simp only [hg]; rw [show 1 + s - 1 = s by omega, vtx_of_mem hs'.1 hs'.2]
    have hl : pkRLen N m g m ≤ N - k := by
      change (g (vtx m (m + 1)) + N - g (vtx m m)) % N ≤ N - k
      rw [e1, e2, gm, g1]
      rcases pkR_b_vtx2 (N := N) (u := s + k) (by omega) (by omega) with ⟨h0, v⟩ | ⟨h0, v⟩
      · rw [v, Nat.mod_eq_of_lt (by omega)]
        omega
      · rw [v]
        rcases pkR_b_mod2 (N := N) (z := s + N - (s + k - N)) (by omega) with ⟨hz, h⟩ | ⟨hz, h⟩ <;>
          rw [h] <;> omega
    change b ∈ Icc (g (vtx m m)) (g (vtx m m) + pkRLen N m g m - 1) at hb
    rw [e1, mem_Icc] at hb
    have hcomp := pkCo_cycArc_compl hs (show k ≤ N by omega)
    have hmem : vtx N b ∈ cycArc N (vtx N (s + k)) (N - k) := by
      refine pkCo_mem_cycArc.2 ⟨b - g m, by omega, ?_⟩
      rw [← gm, show g m + (b - g m) = b by omega]
    rw [← hcomp] at hmem
    exact ⟨(mem_sdiff.1 hmem).1, (mem_sdiff.1 hmem).2⟩
  -- the parent mesh of a pair in `S` vanishes, in either order
  have hzero : ∀ x y, (min x y, max x y) ∈ S → mesh N X x y = 0 := by
    intro x y h
    rcases le_total x y with c | c
    · have := hX _ h; rwa [min_eq_left c, max_eq_right c] at this
    · have := hX _ h; rw [min_eq_right c, max_eq_left c] at this; rwa [pkR_mesh_comm]
  intro σ hσ
  obtain ⟨hd, hc⟩ := mem_filter.1 hσ
  obtain ⟨j, l⟩ := σ
  have hdd := mem_diagonals.1 hd
  dsimp only at hdd hc ⊢
  have hj : j ∈ Icc 1 m := mem_Icc.2 ⟨hdd.1, by omega⟩
  have hl : l ∈ Icc 1 m := mem_Icc.2 ⟨by omega, hdd.2.1⟩
  rw [pkR_mesh_congrD (Y' := pkRSubX N g X) (fun d hd' => relab_eq_subX ⟨hs'.1, hs'.2⟩
    (by omega) X hd'), pkR_subTile hN1 (by omega) hcyc X hj hl
      (by rw [min_eq_left (by omega), max_eq_right (by omega)]; exact hd)]
  have vj1 : vtx m (j + 1) = j + 1 := vtx_of_mem (by omega) (by omega)
  have vj2 : vtx m (j + 2) = j + 2 := vtx_of_mem (by omega) (by omega)
  -- the corner terms vanish
  have c1 : (if vtx m l = vtx m (j + 2) then planar N X (g (vtx m (j + 1))) (g (vtx m (j + 2)))
      else 0) = 0 := by
    rw [vj1, vj2, show j + 2 = j + 1 + 1 from rfl, hadj (j + 1) (by omega) (by omega), ite_self]
  have c2 : (if vtx m j = vtx m (l + 2) then planar N X (g (vtx m (l + 1))) (g (vtx m (l + 2)))
      else 0) = 0 := by
    rcases (show l + 2 ≤ m ∨ l + 1 = m ∨ l = m by omega) with h | h | h
    · rw [vtx_of_mem (by omega) (show l + 1 ≤ m by omega), vtx_of_mem (by omega) h,
        show l + 2 = l + 1 + 1 from rfl, hadj (l + 1) (by omega) (by omega), ite_self]
    · rw [show l + 1 = m from h, vtx_of_mem (by omega) le_rfl,
        show l + 2 = 1 + m by omega, vtx_add_n, vtx_of_mem le_rfl (by omega)]
      have gm : g m = vtx N (s + k) := by simp only [hg]; congr 1; omega
      have g1 : g 1 = s := by
        simp only [hg]; rw [show 1 + s - 1 = s by omega, vtx_of_mem hs'.1 hs'.2]
      rw [gm, g1, pkR_planar_comm, pkR_planar_vtx hN1, pkR_vtx_vtx hN1, ← pkR_planar_vtx hN1,
        hXP, ite_self]
    · have e1 : vtx m (l + 1) = 1 := by
        rw [h, show m + 1 = 1 + m by omega, vtx_add_n, vtx_of_mem le_rfl (by omega)]
      have e2 : vtx m (l + 2) = 1 + 1 := by
        rw [h, show m + 2 = 2 + m by omega, vtx_add_n, vtx_of_mem (by omega) (by omega)]
      rw [e1, e2, hadj 1 le_rfl (by omega), ite_self]
  rw [c1, c2, add_zero, add_zero, hlen j hdd.1 (by omega), sum_singleton]
  have hjm : j ≠ m := by omega
  unfold ChildPairIn at hc
  rw [ite_eq_right hjm] at hc
  by_cases hlm : l = m
  · rw [ite_eq_left hlm] at hc
    rw [hlm]
    refine sum_eq_zero fun b hb => ?_
    obtain ⟨hbI, hbL⟩ := hlast b hb
    rw [pkR_b_mesh_congr hN1 X rfl (pkR_vtx_vtx hN1 b).symm]
    refine hzero _ _ ?_
    have := hc (vtx N b) hbI hbL
    simpa [hg, show j + s - 1 = s + j - 1 by omega] using this
  · rw [ite_eq_right hlm] at hc
    rw [hlen l (by omega) (by omega), sum_singleton]
    refine hzero _ _ ?_
    simpa [hg, show j + s - 1 = s + j - 1 by omega, show l + s - 1 = s + l - 1 by omega] using hc

-- registry: C-R5D5
/-- **The children (1)**: the child loci. For even `N ≥ 6`, a set `S` of pairs
(`S ⊆ diagonals N`) and `P ∈ 𝒫₁`: `ρ_L(L_S ∩ {X_P = 0}) = L^{(m)}_{S_L}` for both sides. Here
`ρ_L(X)` is the child point `d ↦ X(relab N s d)` (each child planar variable read as the parent
`X` of the corresponding chord) and the equality is stated as its two inclusions ("into": the
child point of a point of `L_S` with `X_P = 0` lies on the child locus; "onto": every point `y`
of the child locus is `ρ_L(X)`, on the child diagonals, for some such `X`). A-child: the paper's
labelling (child dual point `j ↦ α + j − 1`, `P̂` the child leg `m`), child set `childSetA`.
B-child: labelled by `relab N (tailStart P)` with `P̂` the last child leg (`pkRBChildB'`), the
paper's labelling (`P̂` the child leg `1`, `childSetB`) rotated by one leg (`pkR_b_childB_rot`). -/
theorem NLSM.Zeros.children_of_odd_chord_locus {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    {S : Finset (ℕ × ℕ)} (hS : S ⊆ diagonals N) {P : ℕ × ℕ} (hP : P ∈ poleChords N S) :
    ((∀ X : ℕ × ℕ → ℚ, OnLocus N S X → X P = 0 →
        OnLocus (headLen N P + 1) (childSetA N S P) (fun d => X (relab N (headStart P) d))) ∧
      ∀ y : ℕ × ℕ → ℚ, OnLocus (headLen N P + 1) (childSetA N S P) y →
        ∃ X : ℕ × ℕ → ℚ, OnLocus N S X ∧ X P = 0 ∧
          ∀ d ∈ diagonals (headLen N P + 1), X (relab N (headStart P) d) = y d) ∧
    ((∀ X : ℕ × ℕ → ℚ, OnLocus N S X → X P = 0 →
        OnLocus (tailLen N P + 1) (pkRBChildB' N S P) (fun d => X (relab N (tailStart P) d))) ∧
      ∀ y : ℕ × ℕ → ℚ, OnLocus (tailLen N P + 1) (pkRBChildB' N S P) y →
        ∃ X : ℕ × ℕ → ℚ, OnLocus N S X ∧ X P = 0 ∧
          ∀ d ∈ diagonals (tailLen N P + 1), X (relab N (tailStart P) d) = y d) := by
  have hEN : N % 2 = 0 := Nat.even_iff.1 hE
  have hPO : P ∈ oddDiagonals N := (mem_filter.1 (mem_filter.1 hP).1).1
  obtain ⟨ts, -, -, tk3, tkN, hs, -, -, hk3, hkN⟩ := pkCh_sides hEN hPO
  refine ⟨⟨fun X hX hXP => child_onLocus hs hk3 hkN hX (by rw [pkR_ch_chordH X hPO]; exact hXP),
    fun y hy => ?_⟩, ⟨fun X hX hXP => child_onLocus ts tk3 tkN hX
      (by rw [pkR_ch_chordT X hPO]; exact hXP), fun y hy => ?_⟩⟩
  · -- onto, A-child: balancing pair from `e_in(P) ≠ ∅`
    obtain ⟨g, hg⟩ := (mem_filter.1 hP).2.1
    obtain ⟨hgM, hg1, hg2⟩ := mem_filter.1 hg
    obtain ⟨hgmiss, hgo⟩ := mem_filter.1 hgM
    obtain ⟨hgd, hgS⟩ := mem_sdiff.1 hgmiss
    have hcyc : ∀ x, x ∈ evenSide N P → x ∉ cycArc N (headStart P) (headLen N P) :=
      fun x hx hc => by
        rw [← (sides_eq_cycArc (by omega) hE hPO).1] at hc
        exact (mem_sdiff.1 hx).2 hc
    have hgp : g.1 % 2 = g.2 % 2 := by
      obtain ⟨o1, o2⟩ := hgo
      omega
    obtain ⟨q1, q2, q3, q4, q5⟩ := pkR_ch_gpair hEN (mem_Icc.1 hs) (by omega) hgd hgS hgp
      (hcyc _ hg1) (hcyc _ hg2)
    obtain ⟨X, hX, hXP, hXd⟩ := pkR_ch_gen (mem_Icc.1 hs) hk3 hkN hS q1 q2 q3 q4 q5 y hy
    exact ⟨X, hX, by rw [← pkR_ch_chordH X hPO]; exact hXP, hXd⟩
  · -- onto, B-child: balancing pair from `o_in(P) ≠ ∅`
    obtain ⟨g, hg⟩ := (mem_filter.1 hP).2.2
    obtain ⟨hgM, hg1, hg2⟩ := mem_filter.1 hg
    obtain ⟨hgmiss, hgo⟩ := mem_filter.1 hgM
    obtain ⟨hgd, hgS⟩ := mem_sdiff.1 hgmiss
    have hcyc : ∀ x, x ∈ oddSide N P → x ∉ cycArc N (tailStart P) (tailLen N P) :=
      fun x hx hc => by
        rw [← (sides_eq_cycArc (by omega) hE hPO).2] at hc
        exact (mem_sdiff.1 hc).2 hx
    have hgp : g.1 % 2 = g.2 % 2 := by
      obtain ⟨o1, o2⟩ := hgo
      omega
    obtain ⟨q1, q2, q3, q4, q5⟩ := pkR_ch_gpair hEN (mem_Icc.1 ts) (by omega) hgd hgS hgp
      (hcyc _ hg1) (hcyc _ hg2)
    obtain ⟨X, hX, hXP, hXd⟩ := pkR_ch_gen (mem_Icc.1 ts) tk3 tkN hS q1 q2 q3 q4 q5 y hy
    exact ⟨X, hX, by rw [← pkR_ch_chordT X hPO]; exact hXP, hXd⟩

-- registry: C-R5D5
/-- **The children (2)**: sizes. For even `N ≥ 6` and an odd chord `P`, the children
have `m = |A_P| + 1 = headLen N P + 1` and `m = |B_P| + 1 = tailLen N P + 1` legs; each `m` is even
and `4 ≤ m ≤ N − 2`. -/
theorem NLSM.Zeros.children_of_odd_chord_size {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    {P : ℕ × ℕ} (hPO : P ∈ oddDiagonals N) :
    ((oddSide N P).card = headLen N P ∧ Even (headLen N P + 1) ∧ 4 ≤ headLen N P + 1 ∧
      headLen N P + 1 ≤ N - 2) ∧
    ((evenSide N P).card = tailLen N P ∧ Even (tailLen N P + 1) ∧ 4 ≤ tailLen N P + 1 ∧
      tailLen N P + 1 ≤ N - 2) := by
  have hEN : N % 2 = 0 := Nat.even_iff.1 hE
  obtain ⟨ts, -, tl1, tk3, tkN, hs, -, hl1, hk3, hkN⟩ := pkCh_sides hEN hPO
  obtain ⟨eA, eB⟩ := sides_eq_cycArc (by omega) hE hPO
  refine ⟨⟨by rw [eA, pkCo_card_cycArc hs (by omega)], Nat.even_iff.2 (by omega), by omega,
    by omega⟩, ⟨by rw [eB, pkCo_card_cycArc ts (by omega)], Nat.even_iff.2 (by omega), by omega,
    by omega⟩⟩

-- registry: C-R5D5
/-- **The children (3)**: candidate sets. For even `N ≥ 6`, a candidate set `S` and
an odd chord `P`: the child set on a side `L` of `P` is a candidate set of the child iff `L` is
linked, for `L = A_P` and `L = B_P` (the children in the paper's labelling, `childSetA`,
`childSetB`). -/
theorem NLSM.Zeros.children_of_odd_chord_linked {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    {S : Finset (ℕ × ℕ)} (hF : IsCandidateSet N S) {P : ℕ × ℕ} (hPo : P ∈ oddDiagonals N) :
    (IsCandidateSet (headLen N P + 1) (childSetA N S P) ↔
      NoFreeSep N S (headStart P) (headLen N P) 0) ∧
    (IsCandidateSet (tailLen N P + 1) (childSetB N S P) ↔
      NoFreeSep N S (tailStart P) (tailLen N P) 1) := by
  -- the proof of the library's `childF`, which uses only that `P` is odd
  replace hF := (isCandidateSet_iff_inFpi hE).1 hF
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  obtain ⟨⟨-, hEA, -⟩, ⟨-, hEB, -⟩⟩ := children_of_odd_chord_size hN hE hPo
  rw [isCandidateSet_iff_inFpi hEA, isCandidateSet_iff_inFpi hEB]
  obtain ⟨-, hts2, -, -, -, -, hhs2, -⟩ := pkCh_sides hE' hPo
  have eA := pkCh_childGen (pkCh_CH_head hE' hPo) hF
  have eB := pkCh_childGen (pkCh_CH_tail hE' hPo) hF
  rw [show (headStart P + 1) % 2 = 0 by omega] at eA
  rw [show (tailStart P + 1) % 2 = 1 by omega] at eB
  exact ⟨eA, eB⟩

-- registry: C-R5D5
/-- **The children (4)**: the children of a flank class. For even `N ≥ 6`, a set `S` of pairs,
`t ∈ 𝒫₁` and `b` in the flank class of `t` (in the paper, `t` and `b` are the top and the bottom
of the class; the statement holds for every member `b`), with `H = L_S ∩ {X_t = 0}`: (4a)
`H = L_S ∩ {X_b = 0}`; (4b) `ρ_{B_t}` and `ρ_{A_b}` map `H` onto the child loci of `S_{B_t}`,
`S_{A_b}` (both inclusions; labellings as in `children_of_odd_chord_locus`); (4c) if `NLSM_m ≢ 0`
on a child locus (in the paper's labelling, `childSetB`, `childSetA`), then `NLSM_m ∘ ρ_L ≢ 0` on
`H` (witness form, as `NonzeroOn`: a point of `H` off the child's poles where it is non-zero). -/
theorem NLSM.Zeros.children_of_odd_chord_flank_class {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    {S : Finset (ℕ × ℕ)} (hS : S ⊆ diagonals N) {t b : ℕ × ℕ} (ht : t ∈ poleChords N S)
    (hb : b ∈ hitClass N S t) :
    residueHyperplane N S t = residueHyperplane N S b ∧
    ((∀ X ∈ residueHyperplane N S t, OnLocus (tailLen N t + 1) (pkRBChildB' N S t)
        (fun d => X (relab N (tailStart t) d))) ∧
      ∀ y : ℕ × ℕ → ℚ, OnLocus (tailLen N t + 1) (pkRBChildB' N S t) y →
        ∃ X ∈ residueHyperplane N S t, ∀ d ∈ diagonals (tailLen N t + 1),
          X (relab N (tailStart t) d) = y d) ∧
    ((∀ X ∈ residueHyperplane N S t, OnLocus (headLen N b + 1) (childSetA N S b)
        (fun d => X (relab N (headStart b) d))) ∧
      ∀ y : ℕ × ℕ → ℚ, OnLocus (headLen N b + 1) (childSetA N S b) y →
        ∃ X ∈ residueHyperplane N S t, ∀ d ∈ diagonals (headLen N b + 1),
          X (relab N (headStart b) d) = y d) ∧
    (NonzeroOn (tailLen N t + 1) (childSetB N S t) → ∃ X ∈ residueHyperplane N S t,
      (∀ d ∈ oddDiagonals (tailLen N t + 1), X (relab N (tailStart t) d) ≠ 0) ∧
        NLSM (tailLen N t + 1) (fun d => X (relab N (tailStart t) d)) ≠ 0) ∧
    (NonzeroOn (headLen N b + 1) (childSetA N S b) → ∃ X ∈ residueHyperplane N S t,
      (∀ d ∈ oddDiagonals (headLen N b + 1), X (relab N (headStart b) d) ≠ 0) ∧
        NLSM (headLen N b + 1) (fun d => X (relab N (headStart b) d)) ≠ 0) := by
  have hEN : N % 2 = 0 := Nat.even_iff.1 hE
  have hbP : b ∈ poleChords N S := (mem_filter.1 hb).1
  have htO : t ∈ oddDiagonals N := (mem_filter.1 (mem_filter.1 ht).1).1
  have hbO : b ∈ oddDiagonals N := (mem_filter.1 (mem_filter.1 hbP).1).1
  -- (4a): `X_t = X_b` on `L_S` (equal flank sets, `chord_restrict`)
  have htb : ∀ X : ℕ × ℕ → ℚ, OnLocus N S X → X t = X b := by
    intro X hX
    have et := chord_restrict (by omega) hE hS X hX htO
    have eb := chord_restrict (by omega) hE hS X hX hbO
    rw [(mem_filter.1 hb).2] at eb
    rw [et, eb]
  have hH : residueHyperplane N S t = residueHyperplane N S b := by
    ext X
    exact ⟨fun ⟨hX, h0⟩ => ⟨hX, by rw [← htb X hX]; exact h0⟩,
      fun ⟨hX, h0⟩ => ⟨hX, by rw [htb X hX]; exact h0⟩⟩
  obtain ⟨-, ⟨intoB, ontoB⟩⟩ := children_of_odd_chord_locus hN hE hS ht
  obtain ⟨⟨intoA, ontoA⟩, -⟩ := children_of_odd_chord_locus hN hE hS hbP
  obtain ⟨-, ⟨-, tBE, tB4, -⟩⟩ := children_of_odd_chord_size hN hE htO
  obtain ⟨⟨-, -, hA4, -⟩, -⟩ := children_of_odd_chord_size hN hE hbO
  have onB : ∀ y : ℕ × ℕ → ℚ, OnLocus (tailLen N t + 1) (pkRBChildB' N S t) y →
      ∃ X ∈ residueHyperplane N S t, ∀ d ∈ diagonals (tailLen N t + 1),
        X (relab N (tailStart t) d) = y d := fun y hy => by
    obtain ⟨X, hX, h0, hd⟩ := ontoB y hy
    exact ⟨X, ⟨hX, h0⟩, hd⟩
  have onA : ∀ y : ℕ × ℕ → ℚ, OnLocus (headLen N b + 1) (childSetA N S b) y →
      ∃ X ∈ residueHyperplane N S t, ∀ d ∈ diagonals (headLen N b + 1),
        X (relab N (headStart b) d) = y d := fun y hy => by
    obtain ⟨X, hX, h0, hd⟩ := ontoA y hy
    exact ⟨X, hH ▸ ⟨hX, h0⟩, hd⟩
  have lift : ∀ {m s : ℕ} {SL : Finset (ℕ × ℕ)}, 2 ≤ m → NonzeroOn m SL →
      (∀ y : ℕ × ℕ → ℚ, OnLocus m SL y → ∃ X ∈ residueHyperplane N S t,
        ∀ d ∈ diagonals m, X (relab N s d) = y d) →
      ∃ X ∈ residueHyperplane N S t, (∀ d ∈ oddDiagonals m, X (relab N s d) ≠ 0) ∧
        NLSM m (fun d => X (relab N s d)) ≠ 0 := by
    intro m s SL _ hnz hon
    obtain ⟨y, hy, hpole, hne⟩ := hnz
    obtain ⟨X, hXH, hXd⟩ := hon y hy
    refine ⟨X, hXH, fun d hd => by rw [hXd d (mem_filter.1 hd).1]; exact hpole d hd, ?_⟩
    rwa [nlsm_congr hXd]
  refine ⟨hH, ⟨fun X hX => intoB X hX.1 hX.2, onB⟩,
    ⟨fun X hX => intoA X hX.1 (by rw [← htb X hX.1]; exact hX.2), onA⟩,
    fun hnz => lift (by omega) (pkR_b_nonzero_B' tB4 (Nat.even_iff.1 tBE) hnz) onB,
    fun hnz => lift (by omega) hnz onA⟩

/-! ## The image of the cut at an odd chord

For the side `D = s, …, s + k − 1` of the chord `P` with dual points `s`, `s + k`: the child's mesh
variables in the parent's at any point (`cut_mesh_pull`), the cut equation as the child's momentum
conservation (`cut_relation`), the cut image as the child's whole coordinate locus when `D` has an
absorber or no missing pair is of one parity (`cut_image_onto`) and as a hyperplane of it otherwise
(`cut_image_hyperplane`), the absorbers that the pairs of `e_in(P)` and `o_in(P)` give
(`cut_absorber_of_inner_pair`, `cut_absorber_of_residue_chord`), and an example
(`PaperTests.example_cut_image_hyperplane`). The proofs number the legs from `s` (`relab N s`, the
side `1..k`, the set of pairs `rotSet N s S`) and come back through `rot_lift`. -/

/-- The child's planar variables are the parent's, numbered from the side's first leg
(`3 ≤ k`, `k + 3 ≤ N`): `X'_{p,q} = X_{p,q}` for `1 ≤ p ≤ q ≤ k + 1`, except the child's side
`{1, k + 1}`. -/
theorem cut_planar_child {N k : ℕ} (hkN : k + 3 ≤ N) (Y : ℕ × ℕ → ℚ) {p q : ℕ}
    (hp : 1 ≤ p) (hpq : p ≤ q) (hq : q ≤ k + 1) (hne : ¬ (p = 1 ∧ q = k + 1)) :
    planar (k + 1) Y p q = planar N Y p q := by
  rw [pkR_planar_def, pkR_planar_def, vtx_of_mem hp (by omega), vtx_of_mem (by omega) hq,
    vtx_of_mem hp (by omega), vtx_of_mem (by omega) (by omega), min_eq_left hpq, max_eq_right hpq]
  by_cases h : (p, q) ∈ diagonals (k + 1)
  · rw [ite_eq_left h, ite_eq_left (by rw [mem_diagonals] at h ⊢; dsimp only at h ⊢; omega)]
  · rw [ite_eq_right h, ite_eq_right (by rw [mem_diagonals] at h ⊢; dsimp only at h ⊢; omega)]

/-- The child reads its side `{1, k + 1}` as `0`. -/
theorem cut_planar_child_side {k : ℕ} (hk : 1 ≤ k) (Y : ℕ × ℕ → ℚ) :
    planar (k + 1) Y 1 (k + 1) = 0 := by
  rw [pkR_planar_comm]
  refine planar_adjacent (by omega) Y ?_
  rw [show k + 1 + 1 = 1 + (k + 1) by omega, vtx_add_n]

/-- **The child's mesh variables in the parent's** (numbered from the side's first leg; any point):
for a pair `{a, b}` of two side legs other than the end legs, `c'_{a,b} = c_{a,b}`. -/
theorem cut_mesh_inside {N k : ℕ} (hkN : k + 3 ≤ N) (Y : ℕ × ℕ → ℚ) {a b : ℕ}
    (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ k) (hne : ¬ (a = 1 ∧ b = k)) :
    mesh (k + 1) Y a b = mesh N Y a b := by
  rw [pkR_mesh_def, pkR_mesh_def, cut_planar_child hkN Y ha hab.le (by omega) (by omega),
    cut_planar_child hkN Y (by omega) (by omega) (by omega) (by omega),
    cut_planar_child hkN Y ha (by omega) (by omega) (by omega),
    cut_planar_child hkN Y (by omega) (by omega) (by omega) (by omega)]

/-- The end legs: `c'_{1,k} = c_{1,k} + X_P`, `X_P = X_{1,k+1}`. -/
theorem cut_mesh_ends {N k : ℕ} (hk : 3 ≤ k) (hkN : k + 3 ≤ N) (Y : ℕ × ℕ → ℚ) :
    mesh (k + 1) Y 1 k = mesh N Y 1 k + planar N Y 1 (k + 1) := by
  rw [pkR_mesh_def, pkR_mesh_def, cut_planar_child hkN Y le_rfl (by omega) (by omega) (by omega),
    cut_planar_child hkN Y (by omega) (by omega) (by omega) (by omega),
    cut_planar_child_side (by omega) Y,
    cut_planar_child hkN Y (by omega) (by omega) (by omega) (by omega)]
  ring

/-- A leg `j` of the side that is not an end leg, with the new leg `k + 1`:
`c'_{j, P̂} = Σ_{w = k+1}^{N} c_{j,w}`. -/
theorem cut_mesh_hat {N k : ℕ} (hk : 3 ≤ k) (hkN : k + 3 ≤ N) (Y : ℕ × ℕ → ℚ) {j : ℕ}
    (hj : 2 ≤ j) (hjk : j ≤ k - 1) :
    mesh (k + 1) Y j (k + 1) = ∑ w ∈ Icc (k + 1) N, mesh N Y j w := by
  have h := mesh_telescope N Y (p := j) (q := j) (r := k + 1) (t := N) le_rfl (by omega)
  rw [Icc_self, sum_singleton] at h
  rw [h, pkR_mesh_def]
  have e1 : planar (k + 1) Y (j + 1) (k + 1 + 1) = planar N Y (j + 1) (N + 1) := by
    rw [pkR_planar_vtx (by omega), show k + 1 + 1 = 1 + (k + 1) by omega, vtx_add_n,
      vtx_of_mem le_rfl (by omega), vtx_of_mem (by omega) (by omega), pkR_planar_comm,
      cut_planar_child hkN Y le_rfl (by omega) (by omega) (by omega),
      pkR_planar_vtx (n := N) (by omega) Y (j + 1) (N + 1), show N + 1 = 1 + N by omega, vtx_add_n,
      vtx_of_mem le_rfl (by omega), vtx_of_mem (by omega) (by omega), pkR_planar_comm]
  have e2 : planar (k + 1) Y j (k + 1 + 1) = planar N Y j (N + 1) := by
    rw [pkR_planar_vtx (by omega), show k + 1 + 1 = 1 + (k + 1) by omega, vtx_add_n,
      vtx_of_mem le_rfl (by omega), vtx_of_mem (by omega) (by omega), pkR_planar_comm,
      cut_planar_child hkN Y le_rfl (by omega) (by omega) (by omega),
      pkR_planar_vtx (n := N) (by omega) Y j (N + 1), show N + 1 = 1 + N by omega, vtx_add_n,
      vtx_of_mem le_rfl (by omega), vtx_of_mem (by omega) (by omega), pkR_planar_comm]
  rw [e1, e2, cut_planar_child hkN Y (by omega) (by omega) le_rfl (by omega),
    cut_planar_child hkN Y (by omega) (by omega) le_rfl (by omega)]

/-- A pair of the `N`-gon unseen by the side `1..k` (numbered from its first leg): both legs
outside the side, or an end leg of the side and a leg outside. -/
abbrev CutUnseen1 (k : ℕ) (t : ℕ × ℕ) : Prop := k + 1 ≤ t.1 ∨ ((t.1 = 1 ∨ t.1 = k) ∧ k + 1 ≤ t.2)

/-- **The sum over the pairs, by kind** (side `1..k`, `3 ≤ k`, `k + 3 ≤ N`): the pairs of two
side legs are the child's pairs inside the side; those of a leg `j` that is not an end leg with a
leg outside are grouped by `j`, as the child's pair `{j, k + 1}`; the rest are unseen. -/
theorem cut_sum_split {N k : ℕ} (hk : 3 ≤ k) (hkN : k + 3 ≤ N) (F : ℕ × ℕ → ℚ) :
    ∑ t ∈ diagonals N, F t =
      ∑ σ ∈ diagonals (k + 1), (if σ.2 = k + 1 then ∑ w ∈ Icc (k + 1) N, F (σ.1, w) else F σ) +
        ∑ t ∈ (diagonals N).filter (CutUnseen1 k), F t := by
  classical
  rw [sum_ite, ← sum_filter_add_sum_filter_not (diagonals N) (fun t => t.2 ≤ k)]
  have eA : (diagonals N).filter (fun t => t.2 ≤ k) =
      (diagonals (k + 1)).filter (fun σ => ¬ σ.2 = k + 1) := by
    ext ⟨a, b⟩
    simp only [mem_filter, mem_diagonals]
    omega
  have eB : ∑ σ ∈ (diagonals (k + 1)).filter (fun σ => σ.2 = k + 1),
      ∑ w ∈ Icc (k + 1) N, F (σ.1, w) =
      ∑ t ∈ (diagonals N).filter (fun t => 2 ≤ t.1 ∧ t.1 ≤ k - 1 ∧ k + 1 ≤ t.2), F t := by
    have e1 : (diagonals (k + 1)).filter (fun σ => σ.2 = k + 1) =
        (Icc 2 (k - 1)).image (fun j => (j, k + 1)) := by
      ext ⟨a, b⟩
      simp only [mem_filter, mem_diagonals, mem_image, mem_Icc, Prod.mk.injEq]
      constructor
      · intro h; exact ⟨a, by omega, rfl, h.2.symm⟩
      · rintro ⟨j, hj, rfl, rfl⟩; omega
    have e2 : (diagonals N).filter (fun t => 2 ≤ t.1 ∧ t.1 ≤ k - 1 ∧ k + 1 ≤ t.2) =
        Icc 2 (k - 1) ×ˢ Icc (k + 1) N := by
      ext ⟨a, b⟩
      simp only [mem_filter, mem_diagonals, mem_product, mem_Icc]
      omega
    rw [e1, sum_image (fun x _ y _ h => (Prod.mk.inj h).1), e2, sum_product]
  have eC : (diagonals N).filter (fun t => ¬ t.2 ≤ k) =
      (diagonals N).filter (fun t => 2 ≤ t.1 ∧ t.1 ≤ k - 1 ∧ k + 1 ≤ t.2) ∪
        (diagonals N).filter (CutUnseen1 k) := by
    ext ⟨a, b⟩
    simp only [mem_filter, mem_union, mem_diagonals, CutUnseen1]
    omega
  have hdisj : Disjoint ((diagonals N).filter (fun t => 2 ≤ t.1 ∧ t.1 ≤ k - 1 ∧ k + 1 ≤ t.2))
      ((diagonals N).filter (CutUnseen1 k)) := by
    rw [disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    simp only [mem_filter, CutUnseen1] at h1 h2
    omega
  rw [eA, eC, sum_union hdisj, eB]
  ring

/-- The child set, numbered from the side's first leg: a pair `{a, b}` of side legs is in it iff
it is in `R`; `{j, k + 1}` iff every `{j, w}`, `w` outside the side, is. -/
abbrev CutChildIn1 (N k : ℕ) (R : Finset (ℕ × ℕ)) (σ : ℕ × ℕ) : Prop :=
  if σ.2 = k + 1 then ∀ w ∈ Icc (k + 1) N, (σ.1, w) ∈ R else σ ∈ R

/-- The child set, numbered from the side's first leg. -/
def cutChildSet1 (N k : ℕ) (R : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  (diagonals (k + 1)).filter (CutChildIn1 N k R)

/-- An absorber of the side `1..k` (numbered from its first leg): a missing same-parity pair
unseen by the side, or two missing pairs `{j, w}`, `{j, w'}`, `j` not an end leg, `w`, `w'`
outside the side of opposite parity. -/
def HasCutAbsorber1 (N k : ℕ) (R : Finset (ℕ × ℕ)) : Prop :=
  (∃ t ∈ diagonals N, t ∉ R ∧ t.1 % 2 = t.2 % 2 ∧ CutUnseen1 k t) ∨
    ∃ j ∈ Icc 2 (k - 1), ∃ w ∈ Icc (k + 1) N, ∃ w' ∈ Icc (k + 1) N,
      w % 2 ≠ w' % 2 ∧ (j, w) ∉ R ∧ (j, w') ∉ R

-- registry: C-XRTT
/-- The parent's values read as the child's: `y_σ` for a pair of side legs, `Σ_w y_{j,w}` for
`σ = {j, k + 1}`. -/
def cutVal (N k : ℕ) (y : ℕ × ℕ → ℚ) (σ : ℕ × ℕ) : ℚ :=
  if σ.2 = k + 1 then ∑ w ∈ Icc (k + 1) N, y (σ.1, w) else y σ

open Classical in
/-- The weights of the hyperplane (numbered from the side's first leg): the weight of the pair for
a pair of side legs; for `{j, k + 1}`, the weight of the missing pairs `{j, w}` if one of them is
of one parity (`shiftSign (j, j)`), else `0`. -/
noncomputable def cutWeight1 (N k : ℕ) (R : Finset (ℕ × ℕ)) (σ : ℕ × ℕ) : ℚ :=
  if σ.2 = k + 1 then
    (if ∃ w ∈ Icc (k + 1) N, w % 2 = σ.1 % 2 ∧ (σ.1, w) ∉ R then (shiftSign (σ.1, σ.1) : ℚ) else 0)
  else shiftSign σ

/-- The parity form `Σ_t ϱ_t y_t` of values on the pairs. -/
def parityVal (N : ℕ) (y : ℕ × ℕ → ℚ) : ℚ := ∑ t ∈ diagonals N, (shiftSign t : ℚ) * y t

/-- The pull-back, pointwise: `c'_σ = c↑_σ`, plus `X_P` for the end legs. -/
theorem cut_mesh_pull {N k : ℕ} (hk : 3 ≤ k) (hkN : k + 3 ≤ N) (Y : ℕ × ℕ → ℚ) {σ : ℕ × ℕ}
    (hσ : σ ∈ diagonals (k + 1)) :
    mesh (k + 1) Y σ.1 σ.2 = cutVal N k (fun t => mesh N Y t.1 t.2) σ +
      if σ = (1, k) then planar N Y 1 (k + 1) else 0 := by
  obtain ⟨a, b⟩ := σ
  have h := mem_diagonals.1 hσ
  dsimp only at h ⊢
  unfold cutVal
  dsimp only
  by_cases hb : b = k + 1
  · subst hb
    rw [ite_eq_left rfl, ite_eq_right (by intro e; simp only [Prod.mk.injEq] at e; omega), add_zero]
    exact cut_mesh_hat hk hkN Y (by omega) (by omega)
  · rw [ite_eq_right hb]
    by_cases he : a = 1 ∧ b = k
    · obtain ⟨rfl, rfl⟩ := he
      rw [ite_eq_left rfl]
      exact cut_mesh_ends hk hkN Y
    · rw [ite_eq_right (by intro e; simp only [Prod.mk.injEq] at e; omega), add_zero]
      exact cut_mesh_inside hkN Y (by omega) (by omega) (by omega) he

/-- The parity form is the difference of the ee and oo sums. -/
theorem parityVal_eq (N : ℕ) (y : ℕ × ℕ → ℚ) :
    parityVal N y = ∑ t ∈ (diagonals N).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0), y t -
      ∑ t ∈ (diagonals N).filter (fun p => p.1 % 2 = 1 ∧ p.2 % 2 = 1), y t :=
  sum_shiftSign_mul y

/-- **(a) The cut is the child's momentum conservation** (numbered from the side's first leg, `k`
odd): `X_P = Σ_σ ϱ'_σ c↑_σ`, the child's parity form of the parent's values. -/
theorem cut_relation1 {N k : ℕ} (hk : 3 ≤ k) (hkN : k + 3 ≤ N) (hko : k % 2 = 1)
    (Y : ℕ × ℕ → ℚ) :
    parityVal (k + 1) (cutVal N k (fun t => mesh N Y t.1 t.2)) = planar N Y 1 (k + 1) := by
  have hrel := (momentum_conservation_relation (N := k + 1) (by omega)
    (Nat.even_iff.2 (by omega))).1 Y
  have h1k : ((1, k) : ℕ × ℕ) ∈ diagonals (k + 1) := mem_diagonals.2 (by dsimp only; omega)
  have hpull : ∀ σ ∈ diagonals (k + 1), (shiftSign σ : ℚ) * mesh (k + 1) Y σ.1 σ.2 =
      (shiftSign σ : ℚ) * cutVal N k (fun t => mesh N Y t.1 t.2) σ +
        if σ = (1, k) then -planar N Y 1 (k + 1) else 0 := by
    intro σ hσ
    rw [cut_mesh_pull hk hkN Y hσ, mul_add]
    congr 1
    split_ifs with h
    · subst h
      unfold shiftSign
      dsimp only
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      push_cast
      ring
    · rw [mul_zero]
  have hsum := sum_congr rfl hpull
  rw [sum_add_distrib, sum_ite_eq' (diagonals (k + 1)) (1, k), ite_eq_left h1k] at hsum
  have h0 : ∑ σ ∈ diagonals (k + 1), (shiftSign σ : ℚ) * mesh (k + 1) Y σ.1 σ.2 = 0 := by
    rw [sum_shiftSign_mul (fun σ => mesh (k + 1) Y σ.1 σ.2), hrel, sub_self]
  unfold parityVal
  linarith

/-- A planar variable of a chord `(p, q)` of the polygon is its value. -/
theorem cut_planar_diag {n : ℕ} (Y : ℕ × ℕ → ℚ) {p q : ℕ} (h : (p, q) ∈ diagonals n) :
    planar n Y p q = Y (p, q) := by
  have hd := mem_diagonals.1 h
  dsimp only at hd
  rw [pkR_planar_def, vtx_of_mem hd.1 (by omega), vtx_of_mem (by omega) hd.2.1,
    min_eq_left (by omega), max_eq_right (by omega)]
  exact ite_eq_left h

/-- **The canonical values** (numbered from the side's first leg): for a point `z` of the child's
coordinate locus, values on the pairs of the `N`-gon that vanish on `R` and read as the child's
mesh variables of `z`. -/
theorem cut_canonical1 {N k : ℕ} (hk : 3 ≤ k) (hkN : k + 3 ≤ N) {R : Finset (ℕ × ℕ)}
    (hR : R ⊆ diagonals N) {z : ℕ × ℕ → ℚ} (hz : OnLocus (k + 1) (cutChildSet1 N k R) z) :
    ∃ y : ℕ × ℕ → ℚ, (∀ t ∈ R, y t = 0) ∧
      ∀ σ ∈ diagonals (k + 1), cutVal N k y σ = mesh (k + 1) z σ.1 σ.2 := by
  classical
  let W : ℕ → ℕ := fun j => if h : ∃ w ∈ Icc (k + 1) N, (j, w) ∉ R then h.choose else k + 1
  have hW : ∀ j, W j ∈ Icc (k + 1) N := by
    intro j
    simp only [W]
    split_ifs with h
    · exact h.choose_spec.1
    · exact mem_Icc.2 ⟨le_rfl, by omega⟩
  have hWR : ∀ j, (∃ w ∈ Icc (k + 1) N, (j, w) ∉ R) → (j, W j) ∉ R := by
    intro j h
    simp only [W, dite_eq_left h]
    exact h.choose_spec.2
  refine ⟨fun t => if t.2 ≤ k then mesh (k + 1) z t.1 t.2 else
    if 2 ≤ t.1 ∧ t.1 ≤ k - 1 ∧ t.2 = W t.1 then mesh (k + 1) z t.1 (k + 1) else 0, ?_, ?_⟩
  · rintro ⟨a, b⟩ ht
    have hd := mem_diagonals.1 (hR ht)
    dsimp only at hd ⊢
    split_ifs with h1 h2
    · refine hz (a, b) (mem_filter.2 ⟨mem_diagonals.2 (by dsimp only; omega), ?_⟩)
      unfold CutChildIn1
      rw [ite_eq_right (by dsimp only; omega)]
      exact ht
    · by_cases hex : ∃ w ∈ Icc (k + 1) N, (a, w) ∉ R
      · exact absurd (h2.2.2 ▸ ht) (hWR a hex)
      · push Not at hex
        refine hz (a, k + 1) (mem_filter.2 ⟨mem_diagonals.2 (by dsimp only; omega), ?_⟩)
        unfold CutChildIn1
        rw [ite_eq_left rfl]
        exact hex
    · rfl
  · rintro ⟨a, b⟩ hσ
    have hd := mem_diagonals.1 hσ
    dsimp only at hd ⊢
    unfold cutVal
    dsimp only
    by_cases hb : b = k + 1
    · subst hb
      rw [ite_eq_left rfl]
      rw [sum_congr rfl (g := fun w => if w = W a then mesh (k + 1) z a (k + 1) else 0)
        (fun w hw => by
          have := mem_Icc.1 hw
          rw [ite_eq_right (by omega)]
          by_cases hw' : w = W a
          · rw [ite_eq_left ⟨by omega, by omega, hw'⟩, ite_eq_left hw']
          · rw [ite_eq_right (fun h => hw' h.2.2), ite_eq_right hw']),
        sum_ite_eq' (Icc (k + 1) N) (W a), ite_eq_left (hW a)]
    · rw [ite_eq_right hb, ite_eq_left (by omega)]

/-- `cutVal` and `parityVal` are linear in the values. -/
theorem cutVal_add_smul (N k : ℕ) (y κ : ℕ × ℕ → ℚ) (c : ℚ) (σ : ℕ × ℕ) :
    cutVal N k (fun t => y t + c * κ t) σ = cutVal N k y σ + c * cutVal N k κ σ := by
  unfold cutVal
  split_ifs
  · rw [sum_add_distrib, mul_sum]
  · rfl

/-- The parity form is linear in the values. -/
theorem parityVal_add_smul (N : ℕ) (y κ : ℕ × ℕ → ℚ) (c : ℚ) :
    parityVal N (fun t => y t + c * κ t) = parityVal N y + c * parityVal N κ := by
  unfold parityVal
  rw [mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun _ _ => by ring

/-- **The lift** (numbered from the side's first leg; `N` even, `k` odd): values on the pairs that
vanish on `R`, satisfy the relation and read as the child's mesh variables of `z` come from a point
of `L_R ∩ {X_P = 0}` whose child point is `z`. -/
theorem cut_lift1 {N k : ℕ} (hE : N % 2 = 0) (hk : 3 ≤ k) (hkN : k + 3 ≤ N) (hko : k % 2 = 1)
    {R : Finset (ℕ × ℕ)} (hR : R ⊆ diagonals N) {z y : ℕ × ℕ → ℚ} (hy0 : ∀ t ∈ R, y t = 0)
    (hyz : ∀ σ ∈ diagonals (k + 1), cutVal N k y σ = mesh (k + 1) z σ.1 σ.2)
    (hrel : parityVal N y = 0) :
    ∃ Y : ℕ × ℕ → ℚ, OnLocus N R Y ∧ planar N Y 1 (k + 1) = 0 ∧
      ∀ d ∈ diagonals (k + 1), Y d = z d := by
  have hN4 : 4 ≤ N := by omega
  have hEN : Even N := Nat.even_iff.2 hE
  have hEm : Even (k + 1) := Nat.even_iff.2 (by omega)
  obtain ⟨-, -, -, hiv⟩ := momentum_conservation_relation hN4 hEN
  rw [parityVal_eq] at hrel
  obtain ⟨Y0, hY0⟩ := (hiv y).2 (by linarith)
  have hcv : ∀ σ ∈ diagonals (k + 1),
      cutVal N k (fun t => mesh N Y0 t.1 t.2) σ = cutVal N k y σ := by
    rintro ⟨a, b⟩ hσ
    have h := mem_diagonals.1 hσ
    dsimp only at h
    unfold cutVal
    dsimp only
    split_ifs with hb
    · exact sum_congr rfl fun w hw => by
        have := mem_Icc.1 hw
        exact hY0 (a, w) (mem_diagonals.2 (by dsimp only; omega))
    · exact hY0 (a, b) (mem_diagonals.2 (by dsimp only; omega))
  have hm : ∀ σ ∈ diagonals (k + 1), mesh (k + 1) Y0 σ.1 σ.2 =
      mesh (k + 1) z σ.1 σ.2 + if σ = (1, k) then planar N Y0 1 (k + 1) else 0 := by
    intro σ hσ
    rw [cut_mesh_pull hk hkN Y0 hσ, hcv σ hσ, hyz σ hσ]
  have h1k : ((1, k) : ℕ × ℕ) ∈ diagonals (k + 1) := mem_diagonals.2 (by dsimp only; omega)
  have hXP : planar N Y0 1 (k + 1) = 0 := by
    have r0 : ∑ σ ∈ diagonals (k + 1), (shiftSign σ : ℚ) * mesh (k + 1) Y0 σ.1 σ.2 = 0 := by
      rw [sum_shiftSign_mul (fun σ => mesh (k + 1) Y0 σ.1 σ.2),
        (momentum_conservation_relation (by omega) hEm).1 Y0, sub_self]
    have rz : ∑ σ ∈ diagonals (k + 1), (shiftSign σ : ℚ) * mesh (k + 1) z σ.1 σ.2 = 0 := by
      rw [sum_shiftSign_mul (fun σ => mesh (k + 1) z σ.1 σ.2),
        (momentum_conservation_relation (by omega) hEm).1 z, sub_self]
    rw [sum_congr rfl (fun σ hσ => by rw [hm σ hσ]), sum_congr rfl (fun σ _ => mul_add _ _ _),
      sum_add_distrib, rz, zero_add, sum_congr rfl (fun σ _ => mul_ite _ _ _ _)] at r0
    simp only [mul_zero] at r0
    rw [sum_ite_eq' (diagonals (k + 1)) (1, k), ite_eq_left h1k] at r0
    unfold shiftSign at r0
    dsimp only at r0
    rw [ite_eq_right (by omega), ite_eq_left (by omega)] at r0
    push_cast at r0
    linarith
  have hker : ∀ t ∈ diagonals (k + 1), mesh (k + 1) (Y0 + (-1 : ℚ) • z) t.1 t.2 = 0 := by
    intro t ht
    rw [mesh_add, mesh_smul, hm t ht, hXP]
    simp
  obtain ⟨u, hu⟩ := mesh_kernel (N := k + 1) (by omega) hker
  refine ⟨Y0 + (-u) • (fun d => (shiftSign d : ℚ)), fun t ht => ?_, ?_, fun d hd => ?_⟩
  · have hd := mem_diagonals.1 (hR ht)
    rw [mesh_add, mesh_smul, hY0 t (hR ht), hy0 t ht,
      mesh_shiftSign hN4 hE hd.1 hd.2.2.1 (by omega)]
    ring
  · have hP : ((1, k + 1) : ℕ × ℕ) ∈ diagonals N := mem_diagonals.2 (by dsimp only; omega)
    rw [cut_planar_diag _ hP]
    rw [cut_planar_diag _ hP] at hXP
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hXP]
    unfold shiftSign
    dsimp only
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    simp
  · have := hu d hd
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    linarith

/-- A pair of opposite parity has weight `0`. -/
theorem shiftSign_of_parity_ne {t : ℕ × ℕ} (h : t.1 % 2 ≠ t.2 % 2) : shiftSign t = 0 := by
  unfold shiftSign
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- A same-parity pair has weight `±1`. -/
theorem shiftSign_ne_zero_of_parity {t : ℕ × ℕ} (h : t.1 % 2 = t.2 % 2) :
    (shiftSign t : ℚ) ≠ 0 := by
  unfold shiftSign
  split_ifs <;> first | omega | norm_num

/-- **The step (∗∗)** (numbered from the side's first leg): without an absorber, for values that
vanish on `R`, the parity form of the `N`-gon is `Σ_σ λ_σ c↑_σ`. -/
theorem cut_parity_split {N k : ℕ} (hk : 3 ≤ k) (hkN : k + 3 ≤ N) {R : Finset (ℕ × ℕ)}
    (hno : ¬ HasCutAbsorber1 N k R) {y : ℕ × ℕ → ℚ} (hy0 : ∀ t ∈ R, y t = 0) :
    parityVal N y = ∑ σ ∈ diagonals (k + 1), cutWeight1 N k R σ * cutVal N k y σ := by
  classical
  unfold HasCutAbsorber1 at hno
  push Not at hno
  obtain ⟨hno1, hno2⟩ := hno
  unfold parityVal
  rw [cut_sum_split hk hkN, sum_eq_zero (s := (diagonals N).filter (CutUnseen1 k)) ?_, add_zero]
  · refine sum_congr rfl fun σ hσ => ?_
    obtain ⟨j, b⟩ := σ
    have hd := mem_diagonals.1 hσ
    dsimp only at hd ⊢
    unfold cutWeight1 cutVal
    dsimp only
    by_cases hb : b = k + 1
    · subst hb
      rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_left rfl, mul_sum]
      refine sum_congr rfl fun w hw => ?_
      have hw' := mem_Icc.1 hw
      by_cases hR : (j, w) ∈ R
      · rw [hy0 _ hR, mul_zero, mul_zero]
      by_cases hp : w % 2 = j % 2
      · rw [ite_eq_left ⟨w, hw, hp, hR⟩]
        congr 1
        unfold shiftSign
        dsimp only
        split_ifs <;> first | rfl | omega
      · rw [shiftSign_of_parity_ne (by dsimp only; omega)]
        split_ifs with hex
        · obtain ⟨w', hw'1, hp', hR'⟩ := hex
          exact absurd (hno2 j (mem_Icc.2 ⟨by omega, by omega⟩) w' hw'1 w hw (by omega) hR') hR
        · simp
    · rw [ite_eq_right hb, ite_eq_right hb, ite_eq_right hb]
  · intro t ht
    obtain ⟨ht1, ht2⟩ := mem_filter.1 ht
    by_cases hR : t ∈ R
    · rw [hy0 t hR, mul_zero]
    · by_cases hp : t.1 % 2 = t.2 % 2
      · exact absurd ht2 (fun h => by
          have := hno1 t ht1 hR hp
          unfold CutUnseen1 at h
          omega)
      · rw [shiftSign_of_parity_ne hp, Int.cast_zero, zero_mul]

/-- The relation, as the parity form of a point's mesh variables. -/
theorem parityVal_mesh {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (Y : ℕ × ℕ → ℚ) :
    parityVal N (fun t => mesh N Y t.1 t.2) = 0 := by
  rw [parityVal_eq, (momentum_conservation_relation hN (Nat.even_iff.2 hE)).1 Y, sub_self]

/-- Corrected values: adding a multiple of values `κ` that vanish on `R`, read as `0` by the
child and have a non-zero parity form gives values that also satisfy the relation. -/
theorem cut_correct {N k : ℕ} {R : Finset (ℕ × ℕ)} {y κ : ℕ × ℕ → ℚ} {z : ℕ × ℕ → ℚ}
    (hy0 : ∀ t ∈ R, y t = 0)
    (hyz : ∀ σ ∈ diagonals (k + 1), cutVal N k y σ = mesh (k + 1) z σ.1 σ.2)
    (hκ0 : ∀ t ∈ R, κ t = 0) (hκz : ∀ σ ∈ diagonals (k + 1), cutVal N k κ σ = 0)
    (hκ : parityVal N κ ≠ 0) :
    ∃ y' : ℕ × ℕ → ℚ, (∀ t ∈ R, y' t = 0) ∧
      (∀ σ ∈ diagonals (k + 1), cutVal N k y' σ = mesh (k + 1) z σ.1 σ.2) ∧ parityVal N y' = 0 := by
  refine ⟨fun t => y t + (-(parityVal N y) / parityVal N κ) * κ t, fun t ht => ?_,
    fun σ hσ => ?_, ?_⟩
  · dsimp only; rw [hy0 t ht, hκ0 t ht]; ring
  · rw [cutVal_add_smul, hyz σ hσ, hκz σ hσ]; ring
  · rw [parityVal_add_smul]; field_simp; ring

/-- **(b) The cut image is the child's locus** (numbered from the side's first leg; `N` even, `k`
odd) when the side has an absorber, or when no missing pair is of one parity. -/
theorem cut_onto1 {N k : ℕ} (hE : N % 2 = 0) (hk : 3 ≤ k) (hkN : k + 3 ≤ N) (hko : k % 2 = 1)
    {R : Finset (ℕ × ℕ)} (hR : R ⊆ diagonals N)
    (hab : HasCutAbsorber1 N k R ∨ ∀ t ∈ diagonals N, t ∉ R → t.1 % 2 ≠ t.2 % 2)
    {z : ℕ × ℕ → ℚ} (hz : OnLocus (k + 1) (cutChildSet1 N k R) z) :
    ∃ Y : ℕ × ℕ → ℚ, OnLocus N R Y ∧ planar N Y 1 (k + 1) = 0 ∧
      ∀ d ∈ diagonals (k + 1), Y d = z d := by
  classical
  obtain ⟨y, hy0, hyz⟩ := cut_canonical1 hk hkN hR hz
  suffices h : ∃ y' : ℕ × ℕ → ℚ, (∀ t ∈ R, y' t = 0) ∧
      (∀ σ ∈ diagonals (k + 1), cutVal N k y' σ = mesh (k + 1) z σ.1 σ.2) ∧ parityVal N y' = 0 by
    obtain ⟨y', h0, hz', hrel⟩ := h
    exact cut_lift1 hE hk hkN hko hR h0 hz' hrel
  by_cases hrel : parityVal N y = 0
  · exact ⟨y, hy0, hyz, hrel⟩
  rcases hab with (⟨g, hg, hgR, hgp, hgu⟩ | ⟨j, hj, w, hw, w', hw', hww, hjw, hjw'⟩) | hnone
  · -- an unseen same-parity missing pair
    have hgd := mem_diagonals.1 hg
    refine cut_correct hy0 hyz (κ := fun t => if t = g then 1 else 0)
      (fun t ht => ite_eq_right (fun (e : t = g) => hgR (e ▸ ht))) (fun σ hσ => ?_) ?_
    · obtain ⟨a, b⟩ := σ
      have hd := mem_diagonals.1 hσ
      dsimp only at hd
      unfold cutVal CutUnseen1 at *
      dsimp only
      by_cases hb : b = k + 1
      · rw [ite_eq_left hb]
        refine sum_eq_zero fun v _ => ite_eq_right fun e => ?_
        rw [← e] at hgu
        dsimp only at hgu
        omega
      · rw [ite_eq_right hb]
        exact ite_eq_right fun e => by rw [← e] at hgu; dsimp only at hgu; omega
    · unfold parityVal
      simp only [mul_ite, mul_one, mul_zero]
      rw [sum_ite_eq' (diagonals N) g, ite_eq_left hg]
      exact shiftSign_ne_zero_of_parity hgp
  · -- two missing pairs of opposite parity at one leg
    have hj' := mem_Icc.1 hj
    have hw1 := mem_Icc.1 hw
    have hw1' := mem_Icc.1 hw'
    have hd : ((j, w) : ℕ × ℕ) ∈ diagonals N := mem_diagonals.2 (by dsimp only; omega)
    have hd' : ((j, w') : ℕ × ℕ) ∈ diagonals N := mem_diagonals.2 (by dsimp only; omega)
    have hne : ((j, w) : ℕ × ℕ) ≠ (j, w') := fun e => hww (by rw [(Prod.mk.inj e).2])
    refine cut_correct hy0 hyz
      (κ := fun t => (if t = (j, w) then 1 else 0) - if t = (j, w') then 1 else 0)
      (fun t ht => by
        rw [ite_eq_right (fun (e : t = (j, w)) => hjw (e ▸ ht)),
          ite_eq_right (fun (e : t = (j, w')) => hjw' (e ▸ ht)), sub_zero])
      (fun σ hσ => ?_) ?_
    · obtain ⟨a, b⟩ := σ
      have hdσ := mem_diagonals.1 hσ
      dsimp only at hdσ
      unfold cutVal
      dsimp only
      by_cases hb : b = k + 1
      · rw [ite_eq_left hb, sum_sub_distrib]
        by_cases ha : a = j
        · subst ha
          simp only [Prod.mk.injEq, true_and]
          rw [sum_ite_eq' (Icc (k + 1) N) w, sum_ite_eq' (Icc (k + 1) N) w', ite_eq_left hw,
            ite_eq_left hw', sub_self]
        · simp only [Prod.mk.injEq, ha, false_and, ite_false, sum_const_zero, sub_self]
      · rw [ite_eq_right hb, ite_eq_right (fun e => by simp only [Prod.mk.injEq] at e; omega),
          ite_eq_right (fun e => by simp only [Prod.mk.injEq] at e; omega), sub_self]
    · unfold parityVal
      simp only [mul_sub, mul_ite, mul_one, mul_zero]
      rw [sum_sub_distrib, sum_ite_eq' (diagonals N) (j, w), sum_ite_eq' (diagonals N) (j, w'),
        ite_eq_left hd, ite_eq_left hd']
      intro h0
      rcases (show w % 2 = j % 2 ∨ w' % 2 = j % 2 by omega) with hp | hp
      · rw [shiftSign_of_parity_ne (t := (j, w')) (by dsimp only; omega), Int.cast_zero,
          sub_zero] at h0
        exact shiftSign_ne_zero_of_parity (t := (j, w)) (by dsimp only; omega) h0
      · rw [shiftSign_of_parity_ne (t := (j, w)) (by dsimp only; omega), Int.cast_zero,
          zero_sub, neg_eq_zero] at h0
        exact shiftSign_ne_zero_of_parity (t := (j, w')) (by dsimp only; omega) h0
  · -- no missing pair of one parity
    refine absurd (sum_eq_zero fun t ht => ?_) hrel
    by_cases hR : t ∈ R
    · rw [hy0 t hR, mul_zero]
    · rw [shiftSign_of_parity_ne (hnone t ht hR), Int.cast_zero, zero_mul]

/-- **(c) Without an absorber the cut image is a hyperplane of the child's locus** (numbered from
the side's first leg; `N` even, `k` odd): if some missing pair is of one parity and `X_P` does not
vanish on `L_R`, a point of the child's locus is the child point of a point of `L_R ∩ {X_P = 0}`
iff `ℓ = Σ_σ λ_σ c'_σ` vanishes there, and `ℓ` does not vanish on the child's locus. -/
theorem cut_hyperplane1 {N k : ℕ} (hE : N % 2 = 0) (hk : 3 ≤ k) (hkN : k + 3 ≤ N)
    (hko : k % 2 = 1) {R : Finset (ℕ × ℕ)} (hR : R ⊆ diagonals N) (hno : ¬ HasCutAbsorber1 N k R)
    (hsame : ∃ t ∈ diagonals N, t ∉ R ∧ t.1 % 2 = t.2 % 2)
    (hX0 : ∃ Y0 : ℕ × ℕ → ℚ, OnLocus N R Y0 ∧ planar N Y0 1 (k + 1) ≠ 0) :
    (∀ z : ℕ × ℕ → ℚ, OnLocus (k + 1) (cutChildSet1 N k R) z →
      ((∃ Y : ℕ × ℕ → ℚ, OnLocus N R Y ∧ planar N Y 1 (k + 1) = 0 ∧
          ∀ d ∈ diagonals (k + 1), Y d = z d) ↔
        ∑ σ ∈ diagonals (k + 1), cutWeight1 N k R σ * mesh (k + 1) z σ.1 σ.2 = 0)) ∧
    ∃ z : ℕ × ℕ → ℚ, OnLocus (k + 1) (cutChildSet1 N k R) z ∧
      ∑ σ ∈ diagonals (k + 1), cutWeight1 N k R σ * mesh (k + 1) z σ.1 σ.2 ≠ 0 := by
  classical
  have hN4 : 4 ≤ N := by omega
  have hEm : Even (k + 1) := Nat.even_iff.2 (by omega)
  -- the mesh values of a point of `L_R` vanish on `R`
  have hv0 : ∀ Y : ℕ × ℕ → ℚ, OnLocus N R Y → ∀ t ∈ R, (fun t => mesh N Y t.1 t.2) t = 0 :=
    fun Y hY t ht => hY t ht
  refine ⟨fun z hz => ⟨?_, fun hl => ?_⟩, ?_⟩
  · rintro ⟨Y, hY, hXP, hYz⟩
    have hmz : ∀ σ ∈ diagonals (k + 1), mesh (k + 1) z σ.1 σ.2 =
        cutVal N k (fun t => mesh N Y t.1 t.2) σ := by
      intro σ hσ
      rw [pkR_mesh_congrD (Y' := Y) (fun d hd => (hYz d hd).symm), cut_mesh_pull hk hkN Y hσ, hXP,
        ite_self, add_zero]
    rw [sum_congr rfl (fun σ hσ => by rw [hmz σ hσ]), ← cut_parity_split hk hkN hno (hv0 Y hY)]
    exact parityVal_mesh hN4 hE Y
  · obtain ⟨y, hy0, hyz⟩ := cut_canonical1 hk hkN hR hz
    refine cut_lift1 hE hk hkN hko hR hy0 hyz ?_
    rw [cut_parity_split hk hkN hno hy0, ← hl]
    exact sum_congr rfl fun σ hσ => by rw [hyz σ hσ]
  · obtain ⟨t0, ht0, ht0R, ht0p⟩ := hsame
    obtain ⟨Y0, hY0, hXP0⟩ := hX0
    have hno' := hno
    unfold HasCutAbsorber1 at hno'
    push Not at hno'
    obtain ⟨hno1, hno2⟩ := hno'
    have hd0 := mem_diagonals.1 ht0
    -- the child's pair that sees `t0`
    have hnu : ¬ CutUnseen1 k t0 := fun h => by
      have := hno1 t0 ht0 ht0R ht0p
      unfold CutUnseen1 at h
      omega
    unfold CutUnseen1 at hnu
    obtain ⟨σ0, hσ0, hσ0S, hσ0w⟩ : ∃ σ0 ∈ diagonals (k + 1), σ0 ∉ cutChildSet1 N k R ∧
        cutWeight1 N k R σ0 ≠ 0 := by
      by_cases hin : t0.2 ≤ k
      · refine ⟨t0, mem_diagonals.2 (by omega), fun h => ?_, ?_⟩
        · have := (mem_filter.1 h).2
          unfold CutChildIn1 at this
          rw [ite_eq_right (by omega)] at this
          exact ht0R this
        · unfold cutWeight1
          rw [ite_eq_right (by omega)]
          exact shiftSign_ne_zero_of_parity ht0p
      · refine ⟨(t0.1, k + 1), mem_diagonals.2 (by dsimp only; omega), fun h => ?_, ?_⟩
        · have := (mem_filter.1 h).2
          unfold CutChildIn1 at this
          rw [ite_eq_left rfl] at this
          exact ht0R (this t0.2 (mem_Icc.2 ⟨by omega, by omega⟩))
        · unfold cutWeight1
          rw [ite_eq_left rfl, ite_eq_left ⟨t0.2, mem_Icc.2 ⟨by omega, by omega⟩, by omega, ht0R⟩]
          exact shiftSign_ne_zero_of_parity (t := (t0.1, t0.1)) rfl
    -- the values `e_{σ0} − κ c↑(Y0)`, which satisfy the child's relation
    set c0 := cutVal N k (fun t => mesh N Y0 t.1 t.2) with hc0
    set κ := (shiftSign σ0 : ℚ) / planar N Y0 1 (k + 1) with hκ
    have hrel0 := cut_relation1 hk hkN hko Y0
    set v : ℕ × ℕ → ℚ := fun σ => (if σ = σ0 then 1 else 0) - κ * c0 σ with hv
    have hpv : parityVal (k + 1) v = 0 := by
      unfold parityVal
      simp only [hv, mul_sub, mul_ite, mul_one, mul_zero]
      rw [sum_sub_distrib, sum_ite_eq' (diagonals (k + 1)) σ0, ite_eq_left hσ0]
      have : ∑ x ∈ diagonals (k + 1), (shiftSign x : ℚ) * (κ * c0 x) =
          κ * parityVal (k + 1) c0 := by
        unfold parityVal; rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
      rw [this, hrel0, hκ]
      field_simp
      ring
    obtain ⟨-, -, -, hiv⟩ := momentum_conservation_relation (N := k + 1) (by omega) hEm
    obtain ⟨z, hz⟩ := (hiv v).2 (by rw [parityVal_eq] at hpv; linarith)
    -- `c↑(Y0)` vanishes on the child set
    have hc00 : ∀ σ ∈ cutChildSet1 N k R, c0 σ = 0 := by
      intro σ hσ
      obtain ⟨hσd, hσc⟩ := mem_filter.1 hσ
      have hd := mem_diagonals.1 hσd
      unfold CutChildIn1 at hσc
      rw [hc0]
      unfold cutVal
      split_ifs at hσc ⊢ with hb
      · exact sum_eq_zero fun w hw => hY0 _ (hσc w hw)
      · exact hY0 _ hσc
    refine ⟨z, fun σ hσ => ?_, ?_⟩
    · rw [hz σ (mem_filter.1 hσ).1, hv]
      dsimp only
      rw [ite_eq_right (fun (e : σ = σ0) => hσ0S (e ▸ hσ)), hc00 σ hσ, mul_zero, sub_zero]
    · rw [sum_congr rfl (fun σ hσ => by rw [hz σ hσ])]
      simp only [hv, mul_sub, mul_ite, mul_one, mul_zero]
      rw [sum_sub_distrib, sum_ite_eq' (diagonals (k + 1)) σ0, ite_eq_left hσ0]
      have : ∑ x ∈ diagonals (k + 1), cutWeight1 N k R x * (κ * c0 x) =
          κ * parityVal N (fun t => mesh N Y0 t.1 t.2) := by
        rw [cut_parity_split hk hkN hno (hv0 Y0 hY0), mul_sum]
        exact sum_congr rfl fun _ _ => by ring
      rw [this, parityVal_mesh hN4 hE Y0, mul_zero, sub_zero]
      exact hσ0w

/-! ### From the side's first leg to any side -/

/-- Rotating by `s` keeps the pairs. -/
theorem relab_mem_diagonals_iff {N s a b : ℕ} (hs : 1 ≤ s ∧ s ≤ N) (ha : 1 ≤ a) (hab : a < b)
    (hb : b ≤ N) : (a, b) ∈ diagonals N ↔ relab N s (a, b) ∈ diagonals N := by
  have v1 := pkR_b_vtx2 (N := N) (u := a + s - 1) (by omega) (by omega)
  have v2 := pkR_b_vtx2 (N := N) (u := b + s - 1) (by omega) (by omega)
  change _ ↔ (min (vtx N (a + s - 1)) (vtx N (b + s - 1)), max (vtx N (a + s - 1))
    (vtx N (b + s - 1))) ∈ diagonals N
  rw [mem_diagonals, mem_diagonals]
  dsimp only
  rcases v1 with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;> rcases v2 with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;> rw [e1, e2] <;>
    omega

/-- The rotated point's planar variables, on two labels `A < B` of `1..N`. -/
theorem rot_planar_lt {N s : ℕ} (hs : 1 ≤ s ∧ s ≤ N) (X : ℕ × ℕ → ℚ) {A B : ℕ} (hA : 1 ≤ A)
    (hAB : A < B) (hB : B ≤ N) :
    planar N (fun r => X (relab N s r)) A B = planar N X (A + s - 1) (B + s - 1) := by
  have hN : 1 ≤ N := by omega
  have e : planar N X (A + s - 1) (B + s - 1) =
      pkRSubX N (fun k => vtx N (k + s - 1)) X (A, B) := by
    change _ = planar N X (vtx N (A + s - 1)) (vtx N (B + s - 1))
    rw [← pkR_planar_vtx hN]
  rw [e, pkR_subX_relab hN s X (A, B), pkR_planar_def, vtx_of_mem hA (by omega),
    vtx_of_mem (by omega) hB, min_eq_left hAB.le, max_eq_right hAB.le]
  by_cases h : (A, B) ∈ diagonals N
  · rw [ite_eq_left h, ite_eq_left ((relab_mem_diagonals_iff hs hA hAB hB).1 h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h ((relab_mem_diagonals_iff hs hA hAB hB).2 h'))]

/-- The rotated point's planar variables (`1 ≤ s ≤ N`, `1 ≤ a`, `1 ≤ b`). -/
theorem rot_planar {N s : ℕ} (hs : 1 ≤ s ∧ s ≤ N) (X : ℕ × ℕ → ℚ) {a b : ℕ} (ha : 1 ≤ a)
    (hb : 1 ≤ b) :
    planar N (fun r => X (relab N s r)) a b = planar N X (a + s - 1) (b + s - 1) := by
  have hN : 1 ≤ N := by omega
  have red : ∀ x, 1 ≤ x → vtx N (x + s - 1) = vtx N (vtx N x + s - 1) := fun x hx => by
    have := vtx_bounds N x hN
    rw [show vtx N x + s - 1 = vtx N x + (s - 1) by omega, pkR_b_vtx_add hN,
      show x + (s - 1) = x + s - 1 by omega]
  rw [pkR_planar_vtx hN (fun r => X (relab N s r)), pkR_planar_vtx hN X, red a ha, red b hb,
    ← pkR_planar_vtx hN X]
  have hA := vtx_bounds N a hN
  have hB := vtx_bounds N b hN
  generalize vtx N a = A at hA ⊢
  generalize vtx N b = B at hB ⊢
  rcases lt_trichotomy A B with h | h | h
  · exact rot_planar_lt hs X hA.1 h hB.2
  · subst h; rw [pkR_planar_self, pkR_planar_self]
  · rw [pkR_planar_comm, rot_planar_lt hs X hB.1 h hA.2, pkR_planar_comm]

/-- The rotated point's mesh variables. -/
theorem rot_mesh {N s : ℕ} (hs : 1 ≤ s ∧ s ≤ N) (X : ℕ × ℕ → ℚ) {a b : ℕ} (ha : 1 ≤ a)
    (hb : 1 ≤ b) : mesh N (fun r => X (relab N s r)) a b = mesh N X (a + s - 1) (b + s - 1) := by
  rw [pkR_mesh_def, pkR_mesh_def, rot_planar hs X ha hb, rot_planar hs X (by omega) (by omega),
    rot_planar hs X ha (by omega), rot_planar hs X (by omega) hb,
    show a + 1 + s - 1 = a + s - 1 + 1 by omega, show b + 1 + s - 1 = b + s - 1 + 1 by omega]

/-- The mesh variable of a rotated pair. -/
theorem mesh_relab {N s : ℕ} (hN : 1 ≤ N) (X : ℕ × ℕ → ℚ) (r : ℕ × ℕ) :
    mesh N X (relab N s r).1 (relab N s r).2 = mesh N X (r.1 + s - 1) (r.2 + s - 1) := by
  change mesh N X (min (vtx N (r.1 + s - 1)) (vtx N (r.2 + s - 1)))
    (max (vtx N (r.1 + s - 1)) (vtx N (r.2 + s - 1))) = _
  rw [pkR_mesh_vtx hN X (r.1 + s - 1) (r.2 + s - 1)]
  rcases le_total (vtx N (r.1 + s - 1)) (vtx N (r.2 + s - 1)) with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, pkR_mesh_comm]

/-- The inverse rotation. -/
def rotInv (N s : ℕ) : ℕ := if s = 1 then 1 else N + 2 - s

/-- The inverse rotation's first leg is a leg. -/
theorem rotInv_mem {N s : ℕ} (hs : 1 ≤ s ∧ s ≤ N) : 1 ≤ rotInv N s ∧ rotInv N s ≤ N := by
  unfold rotInv; split_ifs <;> omega

/-- The inverse of the inverse rotation is the rotation. -/
theorem rotInv_rotInv {N s : ℕ} (hs : 1 ≤ s ∧ s ≤ N) : rotInv N (rotInv N s) = s := by
  unfold rotInv; split_ifs <;> omega

/-- `relab N s` undoes `relab N (rotInv N s)` on the pairs. -/
theorem relab_rotInv {N s : ℕ} (hs : 1 ≤ s ∧ s ≤ N) {t : ℕ × ℕ} (ht : t ∈ diagonals N) :
    relab N s (relab N (rotInv N s) t) = t := by
  have h := mem_diagonals.1 ht
  have hi := rotInv_mem hs
  have key : ∀ x, 1 ≤ x → x ≤ N → vtx N (vtx N (x + rotInv N s - 1) + s - 1) = x := by
    intro x hx1 hx2
    have v := pkR_b_vtx2 (N := N) (u := x + rotInv N s - 1) (by omega) (by omega)
    rcases v with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;> rw [e1] <;>
    · have v' := pkR_b_vtx2 (N := N) (u := (if x + rotInv N s - 1 ≤ N then x + rotInv N s - 1
          else x + rotInv N s - 1 - N) + s - 1) (by split_ifs <;> omega) (by split_ifs <;> omega)
      unfold rotInv at *
      split_ifs at * <;> rcases v' with ⟨h3, e3⟩ | ⟨h3, e3⟩ <;> omega
  obtain ⟨a, b⟩ := t
  dsimp only at h
  change npair N ((min (vtx N (a + rotInv N s - 1)) (vtx N (b + rotInv N s - 1))) + s - 1)
    ((max (vtx N (a + rotInv N s - 1)) (vtx N (b + rotInv N s - 1))) + s - 1) = (a, b)
  unfold npair
  rcases le_total (vtx N (a + rotInv N s - 1)) (vtx N (b + rotInv N s - 1)) with c | c
  · rw [min_eq_left c, max_eq_right c, key a h.1 (by omega), key b (by omega) h.2.1,
      min_eq_left (by omega), max_eq_right (by omega)]
  · rw [min_eq_right c, max_eq_left c, key a h.1 (by omega), key b (by omega) h.2.1,
      min_eq_right (by omega), max_eq_left (by omega)]

/-- The set of pairs, numbered from leg `s`. -/
def rotSet (N s : ℕ) (S : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  (diagonals N).filter (fun r => relab N s r ∈ S)

/-- The rotated set consists of pairs. -/
theorem rotSet_sub (N s : ℕ) (S : Finset (ℕ × ℕ)) : rotSet N s S ⊆ diagonals N := filter_subset _ _

/-- The rotated point lies on the rotated set's locus exactly when the point lies on `L_S`. -/
theorem onLocus_rot {N s : ℕ} (hs : 1 ≤ s ∧ s ≤ N) {S : Finset (ℕ × ℕ)} (hS : S ⊆ diagonals N)
    (X : ℕ × ℕ → ℚ) : OnLocus N S X ↔ OnLocus N (rotSet N s S) (fun r => X (relab N s r)) := by
  have hN : 1 ≤ N := by omega
  constructor
  · intro hX r hr
    obtain ⟨hrd, hrS⟩ := mem_filter.1 hr
    have h := mem_diagonals.1 hrd
    rw [rot_mesh hs X h.1 (by omega), ← mesh_relab hN]
    exact hX _ hrS
  · intro hY t ht
    have htd := hS ht
    have hi := rotInv_mem hs
    have hr : relab N (rotInv N s) t ∈ rotSet N s S :=
      mem_filter.2 ⟨pkR_b_relab_mem hi le_rfl htd, by rw [relab_rotInv hs htd]; exact ht⟩
    have h := mem_diagonals.1 (filter_subset _ _ hr)
    have := hY _ hr
    rw [rot_mesh hs X h.1 (by omega), ← mesh_relab hN, relab_rotInv hs htd] at this
    exact this

/-- The child set, numbered from the side's first leg. -/
theorem childSet_rot {N s k : ℕ} (hs : s ∈ Icc 1 N) (hk : 3 ≤ k) (hkN : k + 3 ≤ N)
    (S : Finset (ℕ × ℕ)) :
    (diagonals (k + 1)).filter (fun σ => ChildPairIn N S s k (k + 1)
      (fun j => vtx N (s + j - 1)) σ.1 σ.2) = cutChildSet1 N k (rotSet N s S) := by
  have hs' := mem_Icc.1 hs
  have hN : 1 ≤ N := by omega
  ext ⟨a, b⟩
  simp only [cutChildSet1, mem_filter]
  refine and_congr_right fun hσ => ?_
  have hd := mem_diagonals.1 hσ
  dsimp only at hd
  unfold ChildPairIn CutChildIn1
  dsimp only
  rw [ite_eq_right (show ¬ a = k + 1 by omega)]
  have er : ∀ c, relab N s (a, c) = (min (vtx N (s + a - 1)) (vtx N (s + c - 1)),
      max (vtx N (s + a - 1)) (vtx N (s + c - 1))) := fun c => by
    change npair N (a + s - 1) (c + s - 1) = _
    rw [show a + s - 1 = s + a - 1 by omega, show c + s - 1 = s + c - 1 by omega]
    rfl
  by_cases hb : b = k + 1
  · subst hb
    rw [ite_eq_left rfl, ite_eq_left rfl]
    constructor
    · intro h w hw
      have hw' := mem_Icc.1 hw
      refine mem_filter.2 ⟨mem_diagonals.2 (by dsimp only; omega), ?_⟩
      rw [er]
      refine h _ (vtx_bounds N _ hN |> mem_Icc.2) ?_
      rw [pkCo_mem_cycArc_pos hs (by omega)]
      rintro ⟨-, hc⟩
      have := pkR_ch_chi_psi (N := N) (s := s) (j := w) hs' ⟨by omega, hw'.2⟩
      unfold pkRChChi at this
      omega
    · intro h w hw hwc
      have hw' := mem_Icc.1 hw
      have hc := pkR_ch_chi_eq hs' hw'
      have hnot : ¬ cycPos N s w < k := fun hlt =>
        hwc ((pkCo_mem_cycArc_pos hs (by omega)).2 ⟨hw, hlt⟩)
      have hm := (mem_filter.1 (h (pkRChChi N s w) (mem_Icc.2 ⟨by unfold pkRChChi; omega,
        by rw [hc]; split_ifs <;> omega⟩))).2
      rw [er, pkR_ch_psi_chi hs' hw'] at hm
      exact hm
  · rw [ite_eq_right hb, ite_eq_right hb]
    constructor
    · intro h
      refine mem_filter.2 ⟨mem_diagonals.2 (by dsimp only; omega), ?_⟩
      rw [er]
      exact h
    · intro h
      have := (mem_filter.1 h).2
      rw [er] at this
      exact this

/-- Rotating by `s` (`N` even) keeps whether a pair is of one parity. -/
theorem relab_parity {N s : ℕ} (hE : N % 2 = 0) (hN : 1 ≤ N) (hs : 1 ≤ s) {r : ℕ × ℕ}
    (h1 : 1 ≤ r.1)
    (h2 : 1 ≤ r.2) : ((relab N s r).1 % 2 = (relab N s r).2 % 2 ↔ r.1 % 2 = r.2 % 2) := by
  change (min (vtx N (r.1 + s - 1)) (vtx N (r.2 + s - 1))) % 2 =
    (max (vtx N (r.1 + s - 1)) (vtx N (r.2 + s - 1))) % 2 ↔ _
  have e1 := pkCo_vtx_mod_two hN hE (r.1 + s - 1)
  have e2 := pkCo_vtx_mod_two hN hE (r.2 + s - 1)
  rcases le_total (vtx N (r.1 + s - 1)) (vtx N (r.2 + s - 1)) with c | c
  · rw [min_eq_left c, max_eq_right c]; omega
  · rw [min_eq_right c, max_eq_left c]; omega

/-- The weight of a rotated pair: `ϱ_{relab r} = ε_s ϱ_r`, `ε_s = ±1` by the parity of `s`. -/
theorem shiftSign_relab {N s : ℕ} (hE : N % 2 = 0) (hN : 1 ≤ N) (hs : 1 ≤ s) {r : ℕ × ℕ}
    (h1 : 1 ≤ r.1)
    (h2 : 1 ≤ r.2) :
    (shiftSign (relab N s r) : ℚ) = (if s % 2 = 1 then 1 else -1) * shiftSign r := by
  change (shiftSign (min (vtx N (r.1 + s - 1)) (vtx N (r.2 + s - 1)),
    max (vtx N (r.1 + s - 1)) (vtx N (r.2 + s - 1))) : ℚ) = _
  have e1 := pkCo_vtx_mod_two hN hE (r.1 + s - 1)
  have e2 := pkCo_vtx_mod_two hN hE (r.2 + s - 1)
  have key : ∀ p q : ℕ, p % 2 = (r.1 + s - 1) % 2 → q % 2 = (r.2 + s - 1) % 2 →
      (shiftSign (p, q) : ℚ) = (if s % 2 = 1 then 1 else -1) * shiftSign r := by
    intro p q hp hq
    unfold shiftSign
    dsimp only
    split_ifs <;> first | omega | norm_num
  rcases le_total (vtx N (r.1 + s - 1)) (vtx N (r.2 + s - 1)) with c | c
  · rw [min_eq_left c, max_eq_right c]; exact key _ _ e1 e2
  · rw [min_eq_right c, max_eq_left c]
    have := key _ _ e1 e2
    unfold shiftSign at this ⊢
    dsimp only at this ⊢
    split_ifs at this ⊢ <;> omega

-- registry: C-XRTT
/-- **An absorber of a side** `D = s, …, s + k − 1`, in the numbering from its first leg
(`relab N s`: the side is `1..k`, the legs outside it `k + 1..N`): a missing same-parity pair
unseen by `D` (both legs outside `D`, or an end leg of `D` and a leg outside), or two missing pairs
`{j, w}`, `{j, w'}` with `j` a leg of `D` that is not an end leg and `w`, `w'` legs outside `D` of
opposite parity. -/
abbrev HasCutAbsorber (N : ℕ) (S : Finset (ℕ × ℕ)) (s k : ℕ) : Prop :=
  (∃ r ∈ diagonals N, relab N s r ∉ S ∧ r.1 % 2 = r.2 % 2 ∧ CutUnseen1 k r) ∨
    ∃ j ∈ Icc 2 (k - 1), ∃ w ∈ Icc (k + 1) N, ∃ w' ∈ Icc (k + 1) N,
      w % 2 ≠ w' % 2 ∧ relab N s (j, w) ∉ S ∧ relab N s (j, w') ∉ S

/-- An absorber of the side from `s` is one of the side `1..k` for the rotated set. -/
theorem hasCutAbsorber_rot {N s k : ℕ} (S : Finset (ℕ × ℕ)) :
    HasCutAbsorber N S s k ↔ HasCutAbsorber1 N k (rotSet N s S) := by
  unfold HasCutAbsorber HasCutAbsorber1 rotSet
  refine or_congr ?_ ?_
  · refine exists_congr fun r => and_congr_right fun hr => ?_
    rw [mem_filter, not_and, imp_iff_right hr]
  · refine exists_congr fun j => and_congr_right fun hj => exists_congr fun w =>
      and_congr_right fun hw => exists_congr fun w' => and_congr_right fun hw' => ?_
    have hj' := mem_Icc.1 hj
    have h1 := mem_Icc.1 hw
    have h2 := mem_Icc.1 hw'
    rw [mem_filter, mem_filter, not_and, not_and,
      imp_iff_right (mem_diagonals.2 (by dsimp only; omega)),
      imp_iff_right (mem_diagonals.2 (by dsimp only; omega))]

open Classical in
-- registry: C-XRTT
/-- **The weights of the hyperplane**: for a pair of two legs of the side, the weight of the pair
of the `N`-gon (`shiftSign`: `+1` ee, `−1` oo, `0` opposite parity); for `{j, P̂}`, the weight of
the missing pairs `{u, w}` (`u` the leg `j`, `w` outside the side) if one of them is of one
parity, that of `(u, u)`, else `0`. -/
noncomputable def cutWeight (N : ℕ) (S : Finset (ℕ × ℕ)) (s k : ℕ) (σ : ℕ × ℕ) : ℚ :=
  if σ.2 = k + 1 then
    (if ∃ w ∈ Icc (k + 1) N, w % 2 = σ.1 % 2 ∧ relab N s (σ.1, w) ∉ S then
      (shiftSign (relab N s (σ.1, σ.1)) : ℚ) else 0)
  else shiftSign (relab N s σ)

/-- The weights of the side from `s` are `±1` times those of the side `1..k` for the rotated
set. -/
theorem cutWeight_rot {N s k : ℕ} (hE : N % 2 = 0) (hs : 1 ≤ s ∧ s ≤ N) (S : Finset (ℕ × ℕ))
    {σ : ℕ × ℕ} (hσ : σ ∈ diagonals (k + 1)) :
    cutWeight N S s k σ = (if s % 2 = 1 then 1 else -1) * cutWeight1 N k (rotSet N s S) σ := by
  classical
  have hN : 1 ≤ N := by omega
  have hd := mem_diagonals.1 hσ
  unfold cutWeight cutWeight1
  by_cases h1 : σ.2 = k + 1
  · rw [ite_eq_left h1, ite_eq_left h1]
    have hex : (∃ w ∈ Icc (k + 1) N, w % 2 = σ.1 % 2 ∧ relab N s (σ.1, w) ∉ S) ↔
        ∃ w ∈ Icc (k + 1) N, w % 2 = σ.1 % 2 ∧ (σ.1, w) ∉ rotSet N s S := by
      refine exists_congr fun w => and_congr_right fun hw => and_congr_right fun _ => ?_
      have := mem_Icc.1 hw
      rw [rotSet, mem_filter, not_and, imp_iff_right (mem_diagonals.2 (by dsimp only; omega))]
    by_cases h2 : ∃ w ∈ Icc (k + 1) N, w % 2 = σ.1 % 2 ∧ relab N s (σ.1, w) ∉ S
    · rw [ite_eq_left h2, ite_eq_left (hex.1 h2)]
      exact shiftSign_relab hE hN hs.1 (r := (σ.1, σ.1)) (by dsimp only; omega)
        (by dsimp only; omega)
    · rw [ite_eq_right h2, ite_eq_right (fun h => h2 (hex.2 h)), mul_zero]
  · rw [ite_eq_right h1, ite_eq_right h1]
    exact shiftSign_relab hE hN hs.1 (by omega) (by omega)

/-- The relation of the child read on the rotated values. -/
theorem cutVal_rot {N s k : ℕ} (hs : 1 ≤ s ∧ s ≤ N) (X : ℕ × ℕ → ℚ) {σ : ℕ × ℕ}
    (hσ : σ ∈ diagonals (k + 1)) :
    cutVal N k (fun t => mesh N (fun r => X (relab N s r)) t.1 t.2) σ =
      cutVal N k (fun t => mesh N X (t.1 + s - 1) (t.2 + s - 1)) σ := by
  have hd := mem_diagonals.1 hσ
  unfold cutVal
  split_ifs
  · exact sum_congr rfl fun w hw => by
      have := mem_Icc.1 hw
      exact rot_mesh hs X (by omega) (by omega)
  · exact rot_mesh hs X (by omega) (by omega)

-- registry: C-XRTT
/-- **The cut image (a)**: the cut equation is the child's momentum conservation. For the
side `D = s, …, s + k − 1` of `k` legs (`k` odd, `3 ≤ k`, `k + 3 ≤ N`) and the chord `P` with dual
points `s`, `s + k` (`X_P = planar N X s (s + k)`): `X_P = Σ_ee c↑_σ − Σ_oo c↑_σ`, the sums over the
ee and the oo pairs `σ` of the child (legs `1..k` the legs of `D`, `k + 1` the new leg), with
`c↑_σ = c_{u,w}` for `σ` the pair of the legs `u`, `w` of `D` and `c↑_{j, k+1} = Σ_w c_{u,w}`
over the legs `w` outside `D`, `u` the leg `j` (`cutVal`, the legs numbered from `s`). -/
theorem NLSM.Zeros.cut_relation {N s k : ℕ} (hs : s ∈ Icc 1 N) (hk3 : 3 ≤ k)
    (hkN : k + 3 ≤ N) (hko : k % 2 = 1) (X : ℕ × ℕ → ℚ) :
    planar N X s (s + k) =
      ∑ σ ∈ (diagonals (k + 1)).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0),
          cutVal N k (fun t => mesh N X (t.1 + s - 1) (t.2 + s - 1)) σ -
        ∑ σ ∈ (diagonals (k + 1)).filter (fun p => p.1 % 2 = 1 ∧ p.2 % 2 = 1),
          cutVal N k (fun t => mesh N X (t.1 + s - 1) (t.2 + s - 1)) σ := by
  have hs' := mem_Icc.1 hs
  have h := cut_relation1 hk3 hkN hko (fun r => X (relab N s r))
  rw [rot_planar hs' X le_rfl (by omega), show 1 + s - 1 = s by omega,
    show k + 1 + s - 1 = s + k by omega, parityVal_eq] at h
  rw [← h]
  congr 1
  · exact sum_congr rfl fun σ hσ => cutVal_rot hs' X (mem_filter.1 hσ).1
  · exact sum_congr rfl fun σ hσ => cutVal_rot hs' X (mem_filter.1 hσ).1

/-- Lifting back a rotated point. -/
theorem rot_lift {N s k : ℕ} (hs : 1 ≤ s ∧ s ≤ N) (hkN : k + 3 ≤ N) {S : Finset (ℕ × ℕ)}
    (hS : S ⊆ diagonals N) {Y z : ℕ × ℕ → ℚ} (hY : OnLocus N (rotSet N s S) Y)
    (hXP : planar N Y 1 (k + 1) = 0) (hYz : ∀ d ∈ diagonals (k + 1), Y d = z d) :
    ∃ X : ℕ × ℕ → ℚ, OnLocus N S X ∧ planar N X s (s + k) = 0 ∧
      ∀ d ∈ diagonals (k + 1), X (relab N s d) = z d := by
  have hi := rotInv_mem hs
  have hback : ∀ r ∈ diagonals N, (fun t => Y (relab N (rotInv N s) t)) (relab N s r) = Y r := by
    intro r hr
    dsimp only
    have := relab_rotInv (s := rotInv N s) hi hr
    rw [rotInv_rotInv hs] at this
    rw [this]
  refine ⟨fun t => Y (relab N (rotInv N s) t), ?_, ?_, fun d hd => ?_⟩
  · rw [onLocus_rot hs hS]
    intro r hr
    rw [pkR_mesh_congrD (Y' := Y) hback]
    exact hY r hr
  · have e := rot_planar hs (fun t => Y (relab N (rotInv N s) t)) (a := 1) (b := k + 1) le_rfl
      (by omega)
    rw [show 1 + s - 1 = s by omega, show k + 1 + s - 1 = s + k by omega,
      pkR_planar_congrD hback] at e
    rw [← e, hXP]
  · have hdN : d ∈ diagonals N := by
      have := mem_diagonals.1 hd
      exact mem_diagonals.2 (by omega)
    rw [hback d hdN, hYz d hd]

-- registry: C-XRTT
/-- **The cut image (b)**: for even `N`, a set `S ⊆ diagonals N` of pairs, the side
`D = s, …, s + k − 1` (`k` odd, `3 ≤ k`, `k + 3 ≤ N`) and the chord `P` with dual points `s`,
`s + k`: if `D` has an absorber, or no missing pair is of one parity, every point `y` of the child
locus is `ρ_D(X)`, on the child diagonals, for a point `X` of `L_S` with `X_P = 0` (the inclusion
the other way is `child_onLocus`). -/
theorem NLSM.Zeros.cut_image_onto {N s k : ℕ} (hE : Even N) (hs : s ∈ Icc 1 N) (hk3 : 3 ≤ k)
    (hkN : k + 3 ≤ N) (hko : k % 2 = 1) {S : Finset (ℕ × ℕ)} (hS : S ⊆ diagonals N)
    (hab : HasCutAbsorber N S s k ∨ ∀ t ∈ diagonals N, t ∉ S → t.1 % 2 ≠ t.2 % 2)
    (y : ℕ × ℕ → ℚ)
    (hy : OnLocus (k + 1) ((diagonals (k + 1)).filter (fun σ => ChildPairIn N S s k (k + 1)
      (fun j => vtx N (s + j - 1)) σ.1 σ.2)) y) :
    ∃ X : ℕ × ℕ → ℚ, OnLocus N S X ∧ planar N X s (s + k) = 0 ∧
      ∀ d ∈ diagonals (k + 1), X (relab N s d) = y d := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  have hs' := mem_Icc.1 hs
  have hN : 1 ≤ N := by omega
  rw [childSet_rot hs hk3 hkN] at hy
  have hab' : HasCutAbsorber1 N k (rotSet N s S) ∨
      ∀ t ∈ diagonals N, t ∉ rotSet N s S → t.1 % 2 ≠ t.2 % 2 := by
    rcases hab with h | h
    · exact Or.inl ((hasCutAbsorber_rot S).1 h)
    · refine Or.inr fun r hr hrS hp => ?_
      have hd := mem_diagonals.1 hr
      have hrel : relab N s r ∉ S := fun h' => hrS (mem_filter.2 ⟨hr, h'⟩)
      exact h _ (pkR_b_relab_mem hs' le_rfl hr) hrel
        ((relab_parity hE' hN hs'.1 (by omega) (by omega)).2 hp)
  obtain ⟨Y, hY, hXP, hYz⟩ := cut_onto1 hE' hk3 hkN hko (rotSet_sub N s S) hab' hy
  exact rot_lift hs' hkN hS hY hXP hYz

/-- A rotated point lies on the rotated locus, with the rotated chord. -/
theorem rot_point {N s k : ℕ} (hs : 1 ≤ s ∧ s ≤ N) {S : Finset (ℕ × ℕ)} (hS : S ⊆ diagonals N)
    {X : ℕ × ℕ → ℚ} (hX : OnLocus N S X) :
    OnLocus N (rotSet N s S) (fun r => X (relab N s r)) ∧
      planar N (fun r => X (relab N s r)) 1 (k + 1) = planar N X s (s + k) := by
  refine ⟨(onLocus_rot hs hS X).1 hX, ?_⟩
  rw [rot_planar hs X le_rfl (by omega), show 1 + s - 1 = s by omega,
    show k + 1 + s - 1 = s + k by omega]

-- registry: C-XRTT
/-- **The cut image (c)**: for even `N`, `S ⊆ diagonals N`, the side `D = s, …, s + k − 1` (`k`
odd, `3 ≤ k`, `k + 3 ≤ N`) and the chord `P` with dual points `s`, `s + k`: if `D` has no
absorber, some missing pair is of one parity and `X_P` does not vanish identically on `L_S`, then a
point `y` of the child locus is `ρ_D(X)` for a point `X` of `L_S` with `X_P = 0` iff
`ℓ(y) = Σ_σ λ_σ c'_σ(y) = 0` (`λ = cutWeight`), and `ℓ` does not vanish on the child locus: the cut
image is a hyperplane of the child locus. -/
theorem NLSM.Zeros.cut_image_hyperplane {N s k : ℕ} (hE : Even N) (hs : s ∈ Icc 1 N)
    (hk3 : 3 ≤ k) (hkN : k + 3 ≤ N) (hko : k % 2 = 1) {S : Finset (ℕ × ℕ)}
    (hS : S ⊆ diagonals N) (hno : ¬ HasCutAbsorber N S s k)
    (hsame : ∃ t ∈ diagonals N, t ∉ S ∧ t.1 % 2 = t.2 % 2)
    (hX0 : ∃ X0 : ℕ × ℕ → ℚ, OnLocus N S X0 ∧ planar N X0 s (s + k) ≠ 0) :
    (∀ y : ℕ × ℕ → ℚ, OnLocus (k + 1) ((diagonals (k + 1)).filter (fun σ => ChildPairIn N S s k
        (k + 1) (fun j => vtx N (s + j - 1)) σ.1 σ.2)) y →
      ((∃ X : ℕ × ℕ → ℚ, OnLocus N S X ∧ planar N X s (s + k) = 0 ∧
          ∀ d ∈ diagonals (k + 1), X (relab N s d) = y d) ↔
        ∑ σ ∈ diagonals (k + 1), cutWeight N S s k σ * mesh (k + 1) y σ.1 σ.2 = 0)) ∧
    ∃ y : ℕ × ℕ → ℚ, OnLocus (k + 1) ((diagonals (k + 1)).filter (fun σ => ChildPairIn N S s k
        (k + 1) (fun j => vtx N (s + j - 1)) σ.1 σ.2)) y ∧
      ∑ σ ∈ diagonals (k + 1), cutWeight N S s k σ * mesh (k + 1) y σ.1 σ.2 ≠ 0 := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  have hs' := mem_Icc.1 hs
  have hN : 1 ≤ N := by omega
  rw [childSet_rot hs hk3 hkN]
  have hno' : ¬ HasCutAbsorber1 N k (rotSet N s S) := fun h => hno ((hasCutAbsorber_rot S).2 h)
  have hsame' : ∃ r ∈ diagonals N, r ∉ rotSet N s S ∧ r.1 % 2 = r.2 % 2 := by
    obtain ⟨t, ht, htS, htp⟩ := hsame
    have hi := rotInv_mem hs'
    have hr := pkR_b_relab_mem hi le_rfl ht
    have hd := mem_diagonals.1 hr
    refine ⟨_, hr, fun h => htS ?_, ?_⟩
    · have := (mem_filter.1 h).2
      rwa [relab_rotInv hs' ht] at this
    · have := relab_parity (s := s) hE' hN hs'.1 (r := relab N (rotInv N s) t) (by omega) (by omega)
      rw [relab_rotInv hs' ht] at this
      exact this.1 htp
  have hX0' : ∃ Y0 : ℕ × ℕ → ℚ, OnLocus N (rotSet N s S) Y0 ∧ planar N Y0 1 (k + 1) ≠ 0 := by
    obtain ⟨X0, hX0, hP0⟩ := hX0
    obtain ⟨h1, h2⟩ := rot_point (k := k) hs' hS hX0
    exact ⟨_, h1, by rw [h2]; exact hP0⟩
  obtain ⟨hiff, z, hz, hzl⟩ := cut_hyperplane1 hE' hk3 hkN hko (rotSet_sub N s S) hno' hsame' hX0'
  have hε : (if s % 2 = 1 then (1 : ℚ) else -1) ≠ 0 := by split_ifs <;> norm_num
  have hsum : ∀ y : ℕ × ℕ → ℚ,
      ∑ σ ∈ diagonals (k + 1), cutWeight N S s k σ * mesh (k + 1) y σ.1 σ.2 =
      (if s % 2 = 1 then 1 else -1) *
        ∑ σ ∈ diagonals (k + 1), cutWeight1 N k (rotSet N s S) σ * mesh (k + 1) y σ.1 σ.2 := by
    intro y
    rw [mul_sum]
    exact sum_congr rfl fun σ hσ => by rw [cutWeight_rot hE' hs' S hσ]; ring
  refine ⟨fun y hy => ?_, z, hz, by rw [hsum]; exact mul_ne_zero hε hzl⟩
  rw [hsum, mul_eq_zero, or_iff_right hε, ← hiff y hy]
  constructor
  · rintro ⟨X, hX, hXP, hXy⟩
    obtain ⟨h1, h2⟩ := rot_point (k := k) hs' hS hX
    exact ⟨_, h1, by rw [h2]; exact hXP, fun d hd => hXy d hd⟩
  · rintro ⟨Y, hY, hXP, hYz⟩
    exact rot_lift hs' hkN hS hY hXP hYz

-- registry: C-XRTT
/-- **The cut image (d)**: for even `N ≥ 6` and an odd chord `P`, every pair `g` of `e_in(P)` is
an absorber of `A_P` of the first kind: in the numbering from `headStart P`, `g` is a missing
same-parity pair `relab N (headStart P) r` with `r` unseen by the side (`CutUnseen1`; the proof
gives both legs outside it); likewise every pair of `o_in(P)` for `B_P`, from `tailStart P`. -/
theorem NLSM.Zeros.cut_absorber_of_inner_pair {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ} (hPO : P ∈ oddDiagonals N) :
    (∀ g ∈ innerEE N S P, ∃ r ∈ diagonals N, relab N (headStart P) r = g ∧ g ∉ S ∧
      r.1 % 2 = r.2 % 2 ∧ CutUnseen1 (headLen N P) r) ∧
    ∀ g ∈ innerOO N S P, ∃ r ∈ diagonals N, relab N (tailStart P) r = g ∧ g ∉ S ∧
      r.1 % 2 = r.2 % 2 ∧ CutUnseen1 (tailLen N P) r := by
  have hEN : N % 2 = 0 := Nat.even_iff.1 hE
  obtain ⟨ts, -, -, tk3, tkN, hs, -, -, hk3, hkN⟩ := pkCh_sides hEN hPO
  -- a missing same-parity pair with both legs outside the side, in rotated indices
  have mk : ∀ {s k : ℕ} (g : ℕ × ℕ), s ∈ Icc 1 N → k + 3 ≤ N → g ∈ diagonals N → g ∉ S →
      g.1 % 2 = g.2 % 2 → g.1 ∉ cycArc N s k → g.2 ∉ cycArc N s k →
      ∃ r ∈ diagonals N, relab N s r = g ∧ g ∉ S ∧ r.1 % 2 = r.2 % 2 ∧ CutUnseen1 k r := by
    intro s k g hs hkN hgd hgS hgp h1 h2
    obtain ⟨q1, q2, q3, q4, q5⟩ := pkR_ch_gpair hEN (mem_Icc.1 hs) (by omega) hgd hgS hgp h1 h2
    set a := pkRChChi N s g.1
    set b := pkRChChi N s g.2
    have hs' := mem_Icc.1 hs
    have er : ∀ x y, relab N s (x, y) = (min (vtx N (s + x - 1)) (vtx N (s + y - 1)),
        max (vtx N (s + x - 1)) (vtx N (s + y - 1))) := fun x y => by
      change npair N (x + s - 1) (y + s - 1) = _
      rw [show x + s - 1 = s + x - 1 by omega, show y + s - 1 = s + y - 1 by omega]
      rfl
    have hrel : relab N s (min a b, max a b) = relab N s (a, b) := by
      rw [er, er]
      rcases le_total a b with c | c
      · rw [min_eq_left c, max_eq_right c]
      · rw [min_eq_right c, max_eq_left c, min_comm, max_comm]
    have hgd2 := mem_diagonals.1 hgd
    have hgd' : relab N s (a, b) = g := by
      rw [er, pkR_ch_psi_chi hs' ⟨by omega, by omega⟩, pkR_ch_psi_chi hs' ⟨by omega, by omega⟩,
        min_eq_left (by omega), max_eq_right (by omega)]
    have hmem : (min a b, max a b) ∈ diagonals N :=
      (relab_mem_diagonals_iff hs' (by omega) (by omega) (by omega)).2
        (by rw [hrel, hgd']; exact hgd)
    exact ⟨(min a b, max a b), hmem, by rw [hrel, hgd'], hgS, by dsimp only; omega,
      Or.inl (by dsimp only; omega)⟩
  refine ⟨fun g hg => ?_, fun g hg => ?_⟩
  · -- A_P: a pair of `e_in(P)`
    obtain ⟨hgM, hg1, hg2⟩ := mem_filter.1 hg
    obtain ⟨hgmiss, hgo⟩ := mem_filter.1 hgM
    obtain ⟨hgd, hgS⟩ := mem_sdiff.1 hgmiss
    have hcyc : ∀ x, x ∈ evenSide N P → x ∉ cycArc N (headStart P) (headLen N P) :=
      fun x hx hc => by
        rw [← (sides_eq_cycArc (by omega) hE hPO).1] at hc
        exact (mem_sdiff.1 hx).2 hc
    exact mk g hs hkN hgd hgS (by obtain ⟨o1, o2⟩ := hgo; omega) (hcyc _ hg1) (hcyc _ hg2)
  · -- B_P: a pair of `o_in(P)`
    obtain ⟨hgM, hg1, hg2⟩ := mem_filter.1 hg
    obtain ⟨hgmiss, hgo⟩ := mem_filter.1 hgM
    obtain ⟨hgd, hgS⟩ := mem_sdiff.1 hgmiss
    have hcyc : ∀ x, x ∈ oddSide N P → x ∉ cycArc N (tailStart P) (tailLen N P) :=
      fun x hx hc => by
        rw [← (sides_eq_cycArc (by omega) hE hPO).2] at hc
        exact (mem_sdiff.1 hc).2 hx
    exact mk g ts tkN hgd hgS (by obtain ⟨o1, o2⟩ := hgo; omega) (hcyc _ hg1) (hcyc _ hg2)

-- registry: C-XRTT
/-- **The cut image (d), for a residue chord**: for even `N ≥ 6` and a residue chord `P`
(`P ∈ poleChords N S`, so `e_in(P)` and `o_in(P)` are not empty), both sides have an
absorber. -/
theorem NLSM.Zeros.cut_absorber_of_residue_chord {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ} (hP : P ∈ poleChords N S) :
    HasCutAbsorber N S (headStart P) (headLen N P) ∧
      HasCutAbsorber N S (tailStart P) (tailLen N P) := by
  have hPO : P ∈ oddDiagonals N := (mem_filter.1 (mem_filter.1 hP).1).1
  obtain ⟨hA, hB⟩ := cut_absorber_of_inner_pair (S := S) hN hE hPO
  obtain ⟨g, hg⟩ := (mem_filter.1 hP).2.1
  obtain ⟨g', hg'⟩ := (mem_filter.1 hP).2.2
  obtain ⟨r, hr, hrg, hgS, hrp, hru⟩ := hA g hg
  obtain ⟨r', hr', hrg', hgS', hrp', hru'⟩ := hB g' hg'
  exact ⟨Or.inl ⟨r, hr, by rw [hrg]; exact hgS, hrp, hru⟩,
    Or.inl ⟨r', hr', by rw [hrg']; exact hgS', hrp', hru'⟩⟩

/-! ## Clause 2 of Theorem Π -/

-- registry: C-2NFT
/-- If clause 1 (every regular coordinate zero contains a member of the list) holds at an even
size `N ≥ 6`, then every member of the list is a minimal regular coordinate zero. -/
theorem NLSM.Zeros.minimality_from_containment {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    (clause1 : ∀ S : Finset (ℕ × ℕ), IsRegularCoordinateZero N S → ∃ Z, IsListMember N Z ∧ Z ⊆ S)
    {Z : Finset (ℕ × ℕ)} (hZ : IsListMember N Z) : IsMinimalCoordinateZero N Z := by
  rw [isMinimalCoordinateZero_iff_isMinimalZero (by omega) hE]
  refine prop14_7 hN hE (fun S hS => ?_) (fun _ h => cl2a hN hE h)
    ((isListMember_iff_mem_gFamily hE).1 hZ)
  obtain ⟨Z', hZ', hZS⟩ := clause1 S ((isRegularCoordinateZero_iff_isNDZero (by omega) hE).2 hS)
  exact ⟨Z', (isListMember_iff_mem_gFamily hE).1 hZ', hZS⟩

-- registry: C-6FXC
/-- **The main theorem, clause 2** (minimality): for even `N ≥ 6`, every member `Z` of the list
`𝒢_N` is a minimal regular coordinate zero of `A_N^NLSM`: a regular coordinate zero such that
`Z ∖ {t}` is not a zero, for each pair `t ∈ Z`. -/
theorem NLSM.Zeros.family_members_are_minimal_zeros {N : ℕ} (hN : 6 ≤ N) (hE : Even N) :
    ∀ Z, IsListMember N Z → IsMinimalCoordinateZero N Z :=
  fun _ hZ => (isMinimalCoordinateZero_iff_isMinimalZero (by omega) hE).2
    (pi_clause2 hN hE ((isListMember_iff_mem_gFamily hE).1 hZ)).2

/-! ## The members of the list -/

/-- Every member of the list (`N ≥ 6` even) misses two distinct same-parity pairs. (Proof: for two
legs `g ≠ g'` of its leg set `G`, the pairs `{g, g+2}` and `{g', g'+2}`, labels mod `N`.) -/
theorem list_member_two_same_parity_pairs_outside {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    {Z : Finset (ℕ × ℕ)} (hZ : IsListMember N Z) :
    ∃ p ∈ diagonals N, ∃ p' ∈ diagonals N, p ≠ p' ∧ p ∉ Z ∧ p' ∉ Z ∧
      p.1 % 2 = p.2 % 2 ∧ p'.1 % 2 = p'.2 % 2 := by
  replace hZ := (isListMember_iff_mem_gFamily hE).1 hZ
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  obtain ⟨G, hG, rfl⟩ := mem_image.1 hZ
  obtain ⟨hGsub, hGset⟩ := mem_filter.1 hG
  have hGI : G ⊆ Icc 1 N := mem_powerset.1 hGsub
  have hcard : 1 < G.card := by
    rcases hGset with (h | h) | ⟨a, -, b, -, rfl, hab, -, -⟩
    · exact (pkG_adm_iff.1 h).2.1
    · exact (pkG_adm_iff.1 h).2.1
    · rw [card_pair (by omega)]; norm_num
  obtain ⟨g, hg, g', hg', hne⟩ := one_lt_card.1 hcard
  -- the pair `{x, x+2}` through the leg `x`, as a sorted pair
  let q : ℕ → ℕ × ℕ := fun x => if x + 2 ≤ N then (x, x + 2) else (x + 2 - N, x)
  have hq : ∀ x ∈ G, q x ∈ diagonals N ∧ q x ∉ sepPairs N G ∧ (q x).1 % 2 = (q x).2 % 2 := by
    intro x hx
    have hx' := mem_Icc.1 (hGI hx)
    have hleg : (q x).1 = x ∨ (q x).2 = x := by
      simp only [q]; split_ifs <;> simp
    have hd : q x ∈ diagonals N := by
      simp only [q]; split_ifs <;> exact mem_diagonals.2 (by dsimp only; omega)
    refine ⟨hd, fun h => ?_, by simp only [q]; split_ifs <;> dsimp only <;> omega⟩
    obtain ⟨h1, h2, -⟩ := (mem_filter.1 h).2
    rcases hleg with e | e
    · rw [e] at h1; exact h1 hx
    · rw [e] at h2; exact h2 hx
  have hqne : q g ≠ q g' := by
    have h1 := mem_Icc.1 (hGI hg)
    have h2 := mem_Icc.1 (hGI hg')
    simp only [q]
    split_ifs <;> simp only [ne_eq, Prod.mk.injEq] <;> omega
  exact ⟨q g, (hq g hg).1, q g', (hq g' hg').1, hqne, (hq g hg).2.1, (hq g' hg').2.1,
    (hq g hg).2.2, (hq g' hg').2.2⟩

-- registry: C-CQPT
/-- Members of the list: for even `N ≥ 6` and a member `Z` of the list, (a) `Z` is regular; (b) `Z`
is a zero: `NLSM_N ≡ 0` on `L_Z`; (c) `Z` is linearly closed: for every pair `t ∉ Z`, `c_t ≢ 0` on
`L_Z`. -/
theorem NLSM.Zeros.Families.members_are_closed_zeros {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    {Z : Finset (ℕ × ℕ)} (hZl : IsListMember N Z) :
    IsRegularSet N Z ∧ IsCoordinateZero N Z ∧
    ∀ t ∈ diagonals N, t ∉ Z → ∃ X : ℕ × ℕ → ℚ, OnLocus N Z X ∧ mesh N X t.1 t.2 ≠ 0 := by
  have hZ := (isListMember_iff_mem_gFamily hE).1 hZl
  have hnd : Nondeg N Z := nonDeg_of_pt (cl2a_nondeg hN hE hZ)
  refine ⟨isRegularSet_iff_nondeg.2 hnd,
    (ampZeroOn_iff_ratZero (by omega) hE (gFamily_sub hZ) hnd).1 (cl2a hN hE hZ).2,
    fun t ht htZ => ?_⟩
  by_contra hc
  simp only [not_exists, not_and, not_not] at hc
  -- `locus_coordinates` with `φ = e_t`: `e_t − κϱ` is supported on `S_G`
  obtain ⟨κ, hκ⟩ := ((locus_coordinates (by omega) hE (gFamily_sub hZ)).2.2.2.2
    (fun s => if s = t then 1 else 0)).1 fun X hX => by
      simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', ite_eq_left ht]
      exact hc X hX
  have ht1 := hκ t ht htZ
  rw [ite_eq_left rfl] at ht1
  -- a same-parity pair outside `S_G ∪ {t}` forces `κ = 0`
  obtain ⟨p, hp, p', hp', hne, hpZ, hp'Z, hpp, hpp'⟩ :=
    list_member_two_same_parity_pairs_outside hN hE hZl
  have key : ∀ s ∈ diagonals N, s ∉ Z → s ≠ t → s.1 % 2 = s.2 % 2 → False := by
    intro s hs hsZ hst hsp
    have h := hκ s hs hsZ
    rw [ite_eq_right hst] at h
    have hs0 : (shiftSign s : ℚ) ≠ 0 := by
      unfold shiftSign
      split_ifs with h1 h2
      · norm_num
      · norm_num
      · omega
    have hκ0 : κ = 0 := by
      rcases mul_eq_zero.1 h.symm with h | h
      · exact h
      · exact absurd h hs0
    rw [hκ0, zero_mul] at ht1
    norm_num at ht1
  by_cases hpt : p = t
  · exact key p' hp' hp'Z (fun h => hne (hpt.trans h.symm)) hpp'
  · exact key p hp hpZ hpt hpp

/-! ## The members of a child's list

For an odd chord `P` and a side, a leg set `T` of the child's list (`IsGSet`, the list's second
form) without the new leg gives a member `S_T` inside the child set exactly when its legs in the
`N`-gon give one inside `S` (`child_zeros_away_from_new_leg`); one with the new leg exactly when the
rest of `T` is a free separator of the side (`child_zeros_at_new_leg`), so the side is linked iff
the child set contains no such member. Neither needs a hypothesis on `S`. If the side is not linked,
the child set contains a member of the child's list and, for `m ≥ 6`, `NLSM_m` vanishes at every
point of its locus at which no odd planar variable vanishes (`unlinked_side_child_vanishes`). As in
`children_of_odd_chord_linked`, the B-child is `childSetB`, numbered from the new leg. -/

-- registry: C-7QZ2
/-- **The members of a child's list without the new leg**: for even `N`, a set `S` of pairs and an
odd chord `P`, on the A-child (child leg `j` the leg `headStart P + j − 1` of `A_P`, the new leg
`headLen N P + 1`; `childSetA`): for a set `T` of child legs without the new leg, its legs in the
`N`-gon lie in `A_P`, `T` is a leg set of the child's list iff they are one of the `N`-gon's, and
the child set contains `S_T` iff `S` contains their separated pairs; every set of legs of `A_P` is
the legs of exactly one such `T`. Likewise on the B-child, numbered from the new leg
(`childSetB`: new leg `1`, child leg `j ≥ 2` the leg `tailStart P + j − 2` of `B_P`). -/
theorem NLSM.Zeros.child_zeros_away_from_new_leg {N : ℕ} (hE : Even N)
    (S : Finset (ℕ × ℕ)) {P : ℕ × ℕ} (hPo : P ∈ oddDiagonals N) :
    ((∀ T ⊆ Icc 1 (headLen N P + 1), headLen N P + 1 ∉ T →
      T.image (fun j => vtx N (headStart P + j - 1)) ⊆ oddSide N P ∧
      (IsGSet (headLen N P + 1) T ↔ IsGSet N (T.image (fun j => vtx N (headStart P + j - 1)))) ∧
      (sepPairs (headLen N P + 1) T ⊆ childSetA N S P ↔
        sepPairs N (T.image (fun j => vtx N (headStart P + j - 1))) ⊆ S)) ∧
    ∀ G ⊆ oddSide N P, ∃! T, T ⊆ Icc 1 (headLen N P + 1) ∧ headLen N P + 1 ∉ T ∧
      T.image (fun j => vtx N (headStart P + j - 1)) = G) ∧
    ((∀ T ⊆ Icc 1 (tailLen N P + 1), 1 ∉ T →
      T.image (fun j => vtx N (tailStart P + j - 2)) ⊆ evenSide N P ∧
      (IsGSet (tailLen N P + 1) T ↔ IsGSet N (T.image (fun j => vtx N (tailStart P + j - 2)))) ∧
      (sepPairs (tailLen N P + 1) T ⊆ childSetB N S P ↔
        sepPairs N (T.image (fun j => vtx N (tailStart P + j - 2))) ⊆ S)) ∧
    ∀ G ⊆ evenSide N P, ∃! T, T ⊆ Icc 1 (tailLen N P + 1) ∧ 1 ∉ T ∧
      T.image (fun j => vtx N (tailStart P + j - 2)) = G) := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  have hN : 4 ≤ N := by
    obtain ⟨-, -, -, -, -, -, -, -, hhl3, hhlN⟩ := pkCh_sides hE' hPo
    omega
  obtain ⟨eA, eB⟩ := sides_eq_cycArc hN hE hPo
  rw [eA, eB]
  exact ⟨pkCh_child_zero_nohat_side S (pkCh_CH_head hE' hPo),
    pkCh_child_zero_nohat_side S (pkCh_CH_tail hE' hPo)⟩

-- registry: C-40A6
/-- **The members of a child's list with the new leg**: for even `N`, a set `S` of pairs and an
odd chord `P`, on the A-child (numbered as in `child_zeros_away_from_new_leg`): for a leg set `T` of
the child's list with the new leg, the legs `Θ` in the `N`-gon of `T` without the new leg are an
admissible separator of `A_P`, and the child set contains `S_T` iff `Θ` is free; every admissible
separator of `A_P` is `Θ` for exactly one such `T`; hence `A_P` is linked iff the child set contains
`S_T` for no such `T`. Likewise on the B-child (`childSetB`, new leg `1`). -/
theorem NLSM.Zeros.child_zeros_at_new_leg {N : ℕ} (hE : Even N)
    (S : Finset (ℕ × ℕ)) {P : ℕ × ℕ} (hPo : P ∈ oddDiagonals N) :
    ((∀ T ⊆ Icc 1 (headLen N P + 1), IsGSet (headLen N P + 1) T → headLen N P + 1 ∈ T →
      (T.erase (headLen N P + 1)).image (fun j => vtx N (headStart P + j - 1)) ∈
        admSeps N (headStart P) (headLen N P) 0 ∧
      (sepPairs (headLen N P + 1) T ⊆ childSetA N S P ↔
        Disjoint (sepIn N (headStart P) (headLen N P)
          ((T.erase (headLen N P + 1)).image (fun j => vtx N (headStart P + j - 1))))
          (missing N S))) ∧
    (∀ Θ ∈ admSeps N (headStart P) (headLen N P) 0, ∃! T, T ⊆ Icc 1 (headLen N P + 1) ∧
      IsGSet (headLen N P + 1) T ∧ headLen N P + 1 ∈ T ∧
      (T.erase (headLen N P + 1)).image (fun j => vtx N (headStart P + j - 1)) = Θ) ∧
    (NoFreeSep N S (headStart P) (headLen N P) 0 ↔ ∀ T ⊆ Icc 1 (headLen N P + 1),
      IsGSet (headLen N P + 1) T → headLen N P + 1 ∈ T →
        ¬ sepPairs (headLen N P + 1) T ⊆ childSetA N S P)) ∧
    ((∀ T ⊆ Icc 1 (tailLen N P + 1), IsGSet (tailLen N P + 1) T → 1 ∈ T →
      (T.erase 1).image (fun j => vtx N (tailStart P + j - 2)) ∈
        admSeps N (tailStart P) (tailLen N P) 1 ∧
      (sepPairs (tailLen N P + 1) T ⊆ childSetB N S P ↔
        Disjoint (sepIn N (tailStart P) (tailLen N P)
          ((T.erase 1).image (fun j => vtx N (tailStart P + j - 2)))) (missing N S))) ∧
    (∀ Θ ∈ admSeps N (tailStart P) (tailLen N P) 1, ∃! T, T ⊆ Icc 1 (tailLen N P + 1) ∧
      IsGSet (tailLen N P + 1) T ∧ 1 ∈ T ∧
      (T.erase 1).image (fun j => vtx N (tailStart P + j - 2)) = Θ) ∧
    (NoFreeSep N S (tailStart P) (tailLen N P) 1 ↔ ∀ T ⊆ Icc 1 (tailLen N P + 1),
      IsGSet (tailLen N P + 1) T → 1 ∈ T → ¬ sepPairs (tailLen N P + 1) T ⊆ childSetB N S P)) := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  obtain ⟨-, hts2, -, -, -, -, hhs2, -⟩ := pkCh_sides hE' hPo
  have hA := pkCh_child_zero_hat_side S (pkCh_CH_head hE' hPo)
  have hB := pkCh_child_zero_hat_side S (pkCh_CH_tail hE' hPo)
  rw [show (headStart P + 1) % 2 = 0 by omega] at hA
  rw [show (tailStart P + 1) % 2 = 1 by omega] at hB
  exact ⟨hA, hB⟩

-- registry: C-VFC2
/-- **The child of a side that is not linked**: for even `N`, a set `S` of pairs and an odd chord
`P`, if `A_P` is not linked, the A-child's set contains a member of the list of
`m = headLen N P + 1` legs, and, when `m ≥ 6`, `NLSM_m` vanishes at every point of the child's
coordinate locus at which no odd planar variable of the `m`-gon vanishes; likewise for `B_P` and the
B-child (`childSetB`). -/
theorem NLSM.Zeros.unlinked_side_child_vanishes {N : ℕ} (hE : Even N)
    (S : Finset (ℕ × ℕ)) {P : ℕ × ℕ} (hPo : P ∈ oddDiagonals N) :
    (¬ NoFreeSep N S (headStart P) (headLen N P) 0 →
      (∃ Z, IsListMember (headLen N P + 1) Z ∧ Z ⊆ childSetA N S P) ∧
      (6 ≤ headLen N P + 1 → ∀ z : ℕ × ℕ → ℚ, OnLocus (headLen N P + 1) (childSetA N S P) z →
        (∀ d ∈ oddDiagonals (headLen N P + 1), z d ≠ 0) → NLSM (headLen N P + 1) z = 0)) ∧
    (¬ NoFreeSep N S (tailStart P) (tailLen N P) 1 →
      (∃ Z, IsListMember (tailLen N P + 1) Z ∧ Z ⊆ childSetB N S P) ∧
      (6 ≤ tailLen N P + 1 → ∀ z : ℕ × ℕ → ℚ, OnLocus (tailLen N P + 1) (childSetB N S P) z →
        (∀ d ∈ oddDiagonals (tailLen N P + 1), z d ≠ 0) → NLSM (tailLen N P + 1) z = 0)) := by
  have hN : 6 ≤ N := by
    obtain ⟨-, -, -, -, -, -, -, -, hhl3, hhlN⟩ := pkCh_sides (Nat.even_iff.1 hE) hPo
    omega
  obtain ⟨⟨-, hEA, -⟩, ⟨-, hEB, -⟩⟩ := children_of_odd_chord_size hN hE hPo
  obtain ⟨⟨-, -, hA⟩, ⟨-, -, hB⟩⟩ := child_zeros_at_new_leg hE S hPo
  -- one side: a member inside the child set, and the vanishing at the points off the poles
  have key : ∀ {m : ℕ} {C : Finset (ℕ × ℕ)}, Even m → ∀ T ⊆ Icc 1 m, IsGSet m T →
      sepPairs m T ⊆ C → (∃ Z, IsListMember m Z ∧ Z ⊆ C) ∧ (6 ≤ m → ∀ z : ℕ × ℕ → ℚ,
        OnLocus m C z → (∀ d ∈ oddDiagonals m, z d ≠ 0) → NLSM m z = 0) := by
    intro m C hEm T hTsub hTG hsub
    have hZ : IsListMember m (sepPairs m T) := (isListMember_iff_mem_gFamily hEm).2
      (mem_image.2 ⟨T, pkCh_mem_gLeg.2 ⟨hTsub, hTG⟩, rfl⟩)
    refine ⟨⟨_, hZ, hsub⟩, fun h6 z hz hodd => ?_⟩
    obtain ⟨⟨hZd, hZr, hZz⟩, -⟩ := family_members_are_minimal_zeros h6 hEm _ hZ
    exact (isCoordinateZero_iff_pointwise (by omega) hEm hZd hZr).1 hZz z
      (fun t ht => hz t (hsub ht)) hodd
  refine ⟨fun hn => ?_, fun hn => ?_⟩
  · have := mt hA.2 hn
    push Not at this
    obtain ⟨T, hTsub, hTG, -, hsub⟩ := this
    exact key hEA T hTsub hTG hsub
  · have := mt hB.2 hn
    push Not at this
    obtain ⟨T, hTsub, hTG, -, hsub⟩ := this
    exact key hEB T hTsub hTG hsub

/-! ## The main theorem, the chord formula, proportionality, the antichain and the quartic rules

The main theorem's clause 1 and its "Hence", in the paper's terms (clause 2 is above), and
statements of the paper restated here so that each claim has a pinned declaration in this module.
-/

-- registry: C-AN6R
/-- **The main theorem, clause 1** (completeness): for even `N ≥ 6`, every regular coordinate zero
`S` of `A_N^NLSM` contains a member of the list `𝒢_N`: a causal diamond or an `S_T` for a set `T` of
at least three legs of one parity. -/
theorem NLSM.Zeros.every_coordinate_zero_contains_a_family_member {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    {S : Finset (ℕ × ℕ)} (hS : IsRegularCoordinateZero N S) : ∃ Z, IsListMember N Z ∧ Z ⊆ S := by
  obtain ⟨Z, hZ, hZS⟩ :=
    pi_clause1 hN hE ((isRegularCoordinateZero_iff_isNDZero (by omega) hE).1 hS)
  exact ⟨Z, (isListMember_iff_mem_gFamily hE).2 hZ, hZS⟩

-- registry: C-CGQH
/-- **The main theorem, "Hence"**: for even `N ≥ 6`, the minimal regular coordinate zeros of
`A_N^NLSM` are exactly the members of the list `𝒢_N`. -/
theorem NLSM.Zeros.minimal_coordinate_zeros_are_the_list {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    {Z : Finset (ℕ × ℕ)} : IsMinimalCoordinateZero N Z ↔ IsListMember N Z := by
  rw [isMinimalCoordinateZero_iff_isMinimalZero (by omega) hE, isListMember_iff_mem_gFamily hE]
  exact pi_minimal_iff hN hE

-- registry: C-7HAA
/-- **The chord formula**: for even `N ≥ 4`, every set `S` of pairs and every odd chord
`P`, `X_P|_{L_S} = y(h_P) − E|_{L_S}`, with `y(h) = Σ_{t ∈ h} c_t|_{L_S}` and `E = Σ_{ee} c` the
parity form. -/
theorem Amplitudes.Kinematics.Mesh.chord_formula {N : ℕ} (hN : 4 ≤ N) (hE : Even N)
    {S : Finset (ℕ × ℕ)} (hS : S ⊆ diagonals N) {P : ℕ × ℕ} (hP : P ∈ oddDiagonals N)
    (X : ℕ × ℕ → ℚ) (hX : OnLocus N S X) :
    X P = ∑ t ∈ hitSet N S P, mesh N X t.1 t.2 - pkGE N X := by
  rw [chord_restrict hN hE hS X hX hP, pkGE]
  congr 1
  apply sum_subset
  · intro t ht
    exact mem_filter.2 ⟨(mem_sdiff.1 (mem_filter.1 ht).1).1, (mem_filter.1 ht).2⟩
  · intro t ht hn
    have ht' : t ∈ S := by
      by_contra hS'
      exact hn (mem_filter.2 ⟨mem_sdiff.2 ⟨(mem_filter.1 ht).1, hS'⟩, (mem_filter.1 ht).2⟩)
    exact hX t ht'

-- registry: C-00Q1
/-- **Proportionality**: for a candidate set `S` at even `N ≥ 6` and `P ∈ 𝒫₁`, an odd
chord `Q` satisfies `X_Q = λ X_P` on `L_S` for some `λ ≠ 0` iff `h_Q = h_P`; and then `λ = +1` and
`Q ∈ 𝒫₁`. -/
theorem Amplitudes.Kinematics.Mesh.proportional_odd_chords_share_missing_flank_set {N : ℕ}
    (hN : 6 ≤ N) (hE : Even N) {S : Finset (ℕ × ℕ)} (hF : IsCandidateSet N S) {P Q : ℕ × ℕ}
    (hP : P ∈ poleChords N S) (hQ : Q ∈ oddDiagonals N) :
    ((∃ c : ℚ, c ≠ 0 ∧ ∀ X : ℕ × ℕ → ℚ, OnLocus N S X → X Q = c * X P) ↔
        hitSet N S Q = hitSet N S P) ∧
      ∀ c : ℚ, c ≠ 0 → (∀ X : ℕ × ℕ → ℚ, OnLocus N S X → X Q = c * X P) → c = 1 ∧
          Q ∈ poleChords N S :=
  lemma14_6 hN hE ((isCandidateSet_iff_inFpi hE).1 hF) hP hQ

-- registry: C-81MZ
/-- **Antichain**: for even `N ≥ 6`, no member of the list contains another. -/
theorem Combinatorics.SetSystems.separated_pair_family_is_antichain {N : ℕ} (hN : 6 ≤ N)
    (hE : Even N) {Z Z' : Finset (ℕ × ℕ)} (hZ : IsListMember N Z) (hZ' : IsListMember N Z')
    (h : Z ⊆ Z') : Z = Z' :=
  gFamily_antichain hN hE ((isListMember_iff_mem_gFamily hE).1 hZ)
    ((isListMember_iff_mem_gFamily hE).1 hZ') h

-- registry: C-E9C4
/-- The two whole-parity members: `S_T` for `T` the odd legs is the set of ee pairs, and for `T`
the even legs the set of oo pairs (even `N ≥ 4`). -/
theorem Amplitudes.Kinematics.Mesh.whole_parity_members {N : ℕ} (hN : 4 ≤ N)
    (hE : Even N) :
    sepPairs N ((Icc 1 N).filter (fun a => a % 2 = 1)) =
        (diagonals N).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0) ∧
      sepPairs N ((Icc 1 N).filter (fun a => a % 2 = 0)) =
        (diagonals N).filter (fun p => p.1 % 2 = 1 ∧ p.2 % 2 = 1) := by
  obtain ⟨n, rfl⟩ := hE
  constructor
  · ext ⟨u, w⟩
    rw [mem_filter]
    constructor
    · intro h
      obtain ⟨hd, hst⟩ := pkL_mem_sep.1 h
      have hd' := mem_diagonals.1 hd
      obtain ⟨hu, hw, -, -⟩ := (pkL_inST_iff (by dsimp only at hd'; omega)).1 hst
      simp only [mem_filter, mem_Icc, not_and] at hu hw
      dsimp only at hd'
      exact ⟨hd, by omega, by omega⟩
    · rintro ⟨hd, hu, hw⟩
      have hd' := mem_diagonals.1 hd
      dsimp only at hd' hu hw
      exact pkL_sep_mk (filter_subset _ _) (by omega) (by omega) (by omega)
        (by simp only [mem_filter]; omega) (by simp only [mem_filter]; omega)
        (t1 := u + 1) (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩) (by omega)
        (by omega) (t2 := 1) (mem_filter.2 ⟨mem_Icc.2 ⟨le_rfl, by omega⟩, rfl⟩) (Or.inl (by omega))
  · ext ⟨u, w⟩
    rw [mem_filter]
    constructor
    · intro h
      obtain ⟨hd, hst⟩ := pkL_mem_sep.1 h
      have hd' := mem_diagonals.1 hd
      obtain ⟨hu, hw, -, -⟩ := (pkL_inST_iff (by dsimp only at hd'; omega)).1 hst
      simp only [mem_filter, mem_Icc, not_and] at hu hw
      dsimp only at hd'
      exact ⟨hd, by omega, by omega⟩
    · rintro ⟨hd, hu, hw⟩
      have hd' := mem_diagonals.1 hd
      dsimp only at hd' hu hw
      exact pkL_sep_mk (filter_subset _ _) (by omega) (by omega) (by omega)
        (by simp only [mem_filter]; omega) (by simp only [mem_filter]; omega)
        (t1 := u + 1) (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩) (by omega)
        (by omega) (t2 := n + n) (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, le_rfl⟩, by omega⟩)
        (Or.inr (by omega))

-- registry: C-E9C4
/-- **Where the parity form vanishes**: for even `N ≥ 4` and a set `S` of pairs, `E` vanishes
identically on `L_S` iff `S` contains one of the two whole-parity members, `S_T` for `T` the odd
legs (the ee pairs) or for `T` the even legs (the oo pairs). -/
theorem Amplitudes.Kinematics.Mesh.parity_form_vanishes_iff_contains_whole_parity {N : ℕ}
    (hN : 4 ≤ N) (hE : Even N) {S : Finset (ℕ × ℕ)} (hS : S ⊆ diagonals N) :
    (∀ X : ℕ × ℕ → ℚ, OnLocus N S X → pkGE N X = 0) ↔
      sepPairs N ((Icc 1 N).filter (fun a => a % 2 = 1)) ⊆ S ∨
        sepPairs N ((Icc 1 N).filter (fun a => a % 2 = 0)) ⊆ S := by
  obtain ⟨hodd, hev⟩ := whole_parity_members (by omega) hE
  constructor
  · intro h0
    rcases (parity_form_nonvanishing (by omega) hE hS).1 h0 with h | h
    · left; rw [hodd]; intro t ht; exact h t (mem_filter.1 ht).1 (mem_filter.1 ht).2
    · right; rw [hev]; intro t ht; exact h t (mem_filter.1 ht).1 (mem_filter.1 ht).2
  · rintro (h | h) X hX
    · unfold pkGE
      exact sum_eq_zero fun t ht => hX t (h (by rw [hodd]; exact ht))
    · rw [pkGE, (momentum_conservation_relation (by omega) hE).1 X]
      exact sum_eq_zero fun t ht => hX t (h (by rw [hev]; exact ht))

-- registry: C-E9C4
/-- **Where the parity form vanishes on the list**: for even `N ≥ 4` and a member `Z` of the list,
`E` vanishes identically on `L_Z` iff `Z` is one of the two whole-parity members, `S_T` for `T`
the odd legs or `T` the even legs. At `N = 4` these two are the only members. -/
theorem Amplitudes.Kinematics.Mesh.parity_form_vanishes_on_member_iff {N : ℕ} (hN : 4 ≤ N)
    (hE : Even N) {Z : Finset (ℕ × ℕ)} (hZ : IsListMember N Z) :
    (∀ X : ℕ × ℕ → ℚ, OnLocus N Z X → pkGE N X = 0) ↔
      Z = sepPairs N ((Icc 1 N).filter (fun a => a % 2 = 1)) ∨
        Z = sepPairs N ((Icc 1 N).filter (fun a => a % 2 = 0)) := by
  obtain ⟨hodd, hev⟩ := whole_parity_members hN hE
  have hZd : Z ⊆ diagonals N := gFamily_sub ((isListMember_iff_mem_gFamily hE).1 hZ)
  constructor
  · intro h0
    have h4 : N = 4 ∨ 6 ≤ N := by obtain ⟨n, hn⟩ := hE; omega
    rcases h4 with rfl | h6
    · -- at `N = 4` the only members are the two whole-parity sets
      exact (by decide : ∀ Z ∈ gFamily 4,
        Z = sepPairs 4 ((Icc 1 4).filter (fun a => a % 2 = 1)) ∨
          Z = sepPairs 4 ((Icc 1 4).filter (fun a => a % 2 = 0))) Z
        ((isListMember_iff_mem_gFamily hE).1 hZ)
    -- the whole-parity members are list members (`{1, 3, 5}`, `{2, 4, 6}` are among the legs)
    have hmem : ∀ r < 2, IsListMember N (sepPairs N ((Icc 1 N).filter (fun a => a % 2 = r))) := by
      intro r hr
      refine Or.inr ⟨_, filter_subset _ _, ?_, fun t ht u hu => ?_, rfl⟩
      · have hsub :
          ({2 - r, 4 - r, 6 - r} : Finset ℕ) ⊆ (Icc 1 N).filter (fun a => a % 2 = r) := by
          obtain ⟨n, rfl⟩ := hE
          intro x hx
          simp only [mem_insert, mem_singleton] at hx
          rw [mem_filter, mem_Icc]
          rcases hx with rfl | rfl | rfl <;> omega
        have := card_le_card hsub
        rw [card_insert_of_notMem (by simp; omega), card_pair (by omega)] at this
        exact this
      · rw [(mem_filter.1 ht).2, (mem_filter.1 hu).2]
    rcases (parity_form_nonvanishing hN hE hZd).1 h0 with hee | hoo
    · left
      refine (separated_pair_family_is_antichain h6 hE (hmem 1 (by norm_num)) hZ ?_).symm
      rw [hodd]
      intro t ht
      exact hee t (mem_filter.1 ht).1 (mem_filter.1 ht).2
    · right
      refine (separated_pair_family_is_antichain h6 hE (hmem 0 (by norm_num)) hZ ?_).symm
      rw [hev]
      intro t ht
      exact hoo t (mem_filter.1 ht).1 (mem_filter.1 ht).2
  · rintro (rfl | rfl) X hX
    · unfold pkGE
      exact sum_eq_zero fun t ht => hX t (by rw [hodd]; exact ht)
    · rw [pkGE, (momentum_conservation_relation (by omega) hE).1 X]
      exact sum_eq_zero fun t ht => hX t (by rw [hev]; exact ht)

-- registry: C-6VT8
/-- **The quartic rules give the NLSM amplitude**: for both polarities `π` and every even `N ≥ 4`,
`Q^π_N = (−1)^{N/2−1} NLSM_N` as rational functions. -/
theorem NLSM.FeynmanRules.quartic_rules_give_nlsm {N π : ℕ} (hN : 4 ≤ N) (hE : Even N)
    (hπ : π < 2) :
    Qpi N π gen = (-1) ^ (N / 2 - 1) * NLSM N gen := by
  rw [theoremB_rat hN (Nat.even_iff.1 hE) hπ, sigma]
  -- `σ_N = (−1)^{N/2+1}` and `(−1)^{N/2−1}` agree: the exponents differ by 2
  obtain ⟨j, rfl⟩ : ∃ j, N = 2 * j + 2 := ⟨N / 2 - 1, by obtain ⟨k, rfl⟩ := hE; omega⟩
  rw [show (2 * j + 2) / 2 + 1 = j + 2 by omega, show (2 * j + 2) / 2 - 1 = j by omega]
  push_cast
  ring

end PionCompleteness.Paper
