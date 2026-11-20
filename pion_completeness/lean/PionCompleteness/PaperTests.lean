/-
Copyright (c) 2026 Henru Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henru Wang
-/
module

public import PionCompleteness.Paper

/-!
# Tests of the paper's statements and definitions

This module holds the statements that check the paper's form of the results (module `Paper`), in one
place, after the `test` statements of the formal-conjectures project
(google-deepmind/formal-conjectures: "a statement that serves as a sanity check (e.g. for a new
definition)"): that a definition says on an example what the paper's says, where it holds and where
it fails; that the hypotheses of a theorem can hold together; and that the main theorem is not
vacuous. Most are about given objects; some are stated for every size: the main theorem's
non-vacuity (for every even `N ≥ 6`) and a few facts about definitions (`faces_empty`,
`hasNoPoleAlong_can_fail` and their helpers). The library's own controls stay in `C0`–`C10`, the
base modules and `Conventions`.

* **The main theorem is not vacuous**, for every even `N ≥ 6`, not only at the sizes `C10`'s
  controls compute: every member of the list `𝒢_N` is non-empty (`sepPairs_nonempty`), so the empty
  set never counts as one; for odd `N ≥ 3` the family does contain `∅`
  (`empty_mem_gFamily_of_odd`; at `N = 7`, `empty_mem_gFamily_seven`), so without `Even N` clause 1
  would hold for every `S` (`containsGMember_of_odd`); the amplitude is not identically zero
  (`not_ampZeroOn_empty`, `exists_NLSM_ne_zero`); and `S_{1,3}` is a non-degenerate zero
  (`isNDZero_sepPairs_one_three`), so the hypothesis of clause 1 can hold. The same in the paper's
  terms: `not_isListMember_empty`, `not_isCoordinateZero_empty`, `isListMember_sepPairs_one_three`,
  `isRegularCoordinateZero_sepPairs_one_three`.
* **The definitions a reader checks to trust the main theorem**, at `N = 6`: `S_{1,3,5}` is a
  regular set, a zero, a regular coordinate zero and a minimal one; the set of all pairs is not
  regular; the empty set is not a zero; `S_{1,3,5} ∪ {(1, 4)}` is a regular coordinate zero that is
  not minimal; `S_{1,4}` is a causal diamond and `S_{1,3,5}` is not; the list at eight legs has 30
  members (`list_eight_card`).
* **The library definitions of the amplitude**: the sign of the shift, triangulations of the
  pentagon, the shift `δ`, and the shifted point's two coefficients.
* **The examples of the paper and of its proofs**: the empty dissection (`faces_empty`); the Cayley
  sum at `N = 4`; a configuration of the three-cut setting (`figure_nine_configuration`); a spread
  separator and the hypotheses of the shortening lemma; the predicates of the class residue
  (`not_hasNoPoleAlong_inv`, `not_restrictsToZeroAlong_one`, `hasNoPoleAlong_can_fail`, with the
  well-definedness `restrictsToZeroAlong_numerator`); the class residue's hypotheses with a class of
  two members (`example_four_six_residue_regime`), its residue chords
  (`example_no_residue_chord_with_both_sides_linked`) and the extreme terms there
  (`example_four_six_extreme_terms_nonvanishing`); the strip region of that example; the marked
  locus (`marked_locus_nonvacuous`) and the hypotheses of the value on it
  (`polygon_value_hypotheses`, `numerator_hom_at_one`); the hypothesis of the `T`-separated zeros
  (`isSameParitySet_six_one_three_five`); a cut image that is a hyperplane
  (`example_cut_image_hyperplane`); and a pole-free locus at six legs
  (`example_pole_free_locus_six`, `example_pole_free_locus_six_rational`).
-/

@[expose] public section

namespace PionCompleteness.PaperTests

open Finset PionCompleteness.TreeRectangleZero PionCompleteness.ChainSlice
  PionCompleteness.PionZeros PionCompleteness.PionNLSM PionCompleteness.Pi
  PionCompleteness.Paper PionCompleteness.Paper.Algebra.RationalFunctions
  PionCompleteness.Paper.Amplitudes.Kinematics.Mesh PionCompleteness.Paper.Combinatorics.Polygons
  PionCompleteness.Paper.Combinatorics.SetSystems PionCompleteness.Paper.NLSM.Amplitude
  PionCompleteness.Paper.NLSM.FeynmanRules PionCompleteness.Paper.NLSM.Zeros
  PionCompleteness.Paper.NLSM.Zeros.Families

/-! ## The main theorem is not vacuous -/

/-- For even `N`, an admissible leg set `G` (of either parity class `r`) cuts at least one pair:
`S_G` is non-empty. -/
theorem sepPairs_nonempty_of_admissible {N r : ℕ} (hE : N % 2 = 0) {G : Finset ℕ}
    (h : Admissible N r G) : (sepPairs N G).Nonempty := by
  obtain ⟨hs, hc, hp⟩ := h
  have hne : G.Nonempty := card_pos.1 (by omega)
  have haG : G.min' hne ∈ G := G.min'_mem hne
  have hbG : G.max' hne ∈ G := G.max'_mem hne
  have hab : G.min' hne < G.max' hne := G.min'_lt_max'_of_card (by omega)
  have hmin : ∀ x ∈ G, G.min' hne ≤ x := fun x hx => G.min'_le x hx
  have hmax : ∀ x ∈ G, x ≤ G.max' hne := fun x hx => G.le_max' x hx
  have hpa := hp _ haG
  have hpb := hp _ hbG
  have ha1 := mem_Icc.1 (hs haG)
  have hb1 := mem_Icc.1 (hs hbG)
  generalize G.min' hne = a at *
  generalize G.max' hne = b at *
  have hab2 : a + 2 ≤ b := by omega
  rcases lt_or_eq_of_le hb1.2 with hbN | hbN
  · refine ⟨(a + 1, b + 1), ?_⟩
    rw [sepPairs, mem_filter]
    refine ⟨by simp only [diagonals, mem_filter, mem_product, mem_Icc]; omega, ?_⟩
    change InST G (a + 1) (b + 1)
    unfold InST
    refine ⟨fun h => ?_, fun h => ?_, ⟨b, hbG, ?_⟩, ⟨a, haG, ?_⟩⟩
    · have := hp _ h; omega
    · have := hmax _ h; omega
    · rw [min_eq_left (by omega), max_eq_right (by omega)]; omega
    · rw [min_eq_left (by omega)]; left; omega
  · have ha2 : 2 ≤ a := by
      by_contra h0
      have h1 : a = 1 := by omega
      subst h1
      omega
    refine ⟨(a - 1, a + 1), ?_⟩
    rw [sepPairs, mem_filter]
    refine ⟨by simp only [diagonals, mem_filter, mem_product, mem_Icc]; omega, ?_⟩
    change InST G (a - 1) (a + 1)
    unfold InST
    refine ⟨fun h => ?_, fun h => ?_, ⟨a, haG, ?_⟩, ⟨b, hbG, ?_⟩⟩
    · have := hmin _ h; omega
    · have := hp _ h; omega
    · rw [min_eq_left (by omega), max_eq_right (by omega)]; omega
    · rw [max_eq_right (by omega)]; right; omega

/-- A mixed anchor `{a, b}` cuts at least one pair: `S_{a,b}` is non-empty. -/
theorem sepPairs_nonempty_of_mixedAnchor {N : ℕ} {G : Finset ℕ} (h : IsMixedAnchor N G) :
    (sepPairs N G).Nonempty := by
  obtain ⟨a, ha, b, hb, rfl, hab, hn, hp⟩ := h
  rw [mem_Icc] at ha hb
  rcases lt_or_eq_of_le hb.2 with hbN | hbN
  · refine ⟨(a + 1, b + 1), ?_⟩
    rw [sepPairs, mem_filter]
    refine ⟨by simp only [diagonals, mem_filter, mem_product, mem_Icc]; omega, ?_⟩
    change InST {a, b} (a + 1) (b + 1)
    unfold InST
    refine ⟨by simp only [mem_insert, mem_singleton]; omega,
      by simp only [mem_insert, mem_singleton]; omega, ⟨b, by simp, ?_⟩, ⟨a, by simp, ?_⟩⟩
    · rw [min_eq_left (by omega), max_eq_right (by omega)]; omega
    · rw [min_eq_left (by omega)]; left; omega
  · have ha2 : 2 ≤ a := by omega
    refine ⟨(a - 1, a + 1), ?_⟩
    rw [sepPairs, mem_filter]
    refine ⟨by simp only [diagonals, mem_filter, mem_product, mem_Icc]; omega, ?_⟩
    change InST {a, b} (a - 1) (a + 1)
    unfold InST
    refine ⟨by simp only [mem_insert, mem_singleton]; omega,
      by simp only [mem_insert, mem_singleton]; omega, ⟨a, by simp, ?_⟩, ⟨b, by simp, ?_⟩⟩
    · rw [min_eq_left (by omega), max_eq_right (by omega)]; omega
    · rw [max_eq_right (by omega)]; right; omega

/-- For even `N`, the set `S_G` of every leg set `G` of `𝒢_N` is non-empty, so `ContainsGMember`
is never true by an empty member. -/
theorem sepPairs_nonempty {N : ℕ} (hE : Even N) {G : Finset ℕ} (hG : IsGSet N G) :
    (sepPairs N G).Nonempty := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  rcases hG with (h | h) | h
  · exact sepPairs_nonempty_of_admissible hE' h
  · exact sepPairs_nonempty_of_admissible hE' h
  · exact sepPairs_nonempty_of_mixedAnchor h

/-- For even `N`, the empty set is not a member of `𝒢_N`. -/
theorem empty_notMem_gFamily {N : ℕ} (hE : Even N) : (∅ : Finset (ℕ × ℕ)) ∉ gFamily N := by
  intro h
  obtain ⟨G, hG, hGe⟩ := mem_image.1 h
  have hne := sepPairs_nonempty hE (mem_filter.1 hG).2
  rw [hGe] at hne
  exact not_nonempty_empty hne

/-- Negative control: at `N = 7` (odd) the family `𝒢_7` contains `∅` (`T = {1, 7}`: two odd legs
with no leg between them on one side), so without the hypothesis `Even N` clause 1 of Theorem Π
could be trivial. -/
theorem empty_mem_gFamily_seven : (∅ : Finset (ℕ × ℕ)) ∈ gFamily 7 :=
  mem_image.2 ⟨{1, 7}, by decide, by decide⟩

/-- For every odd `N ≥ 3`, the empty set is a member of `𝒢_N`: `G = {1, N}` is a same-parity leg
set (both legs odd), and no pair of legs has a leg of `G` strictly between them, so `S_G = ∅`. -/
theorem empty_mem_gFamily_of_odd {N : ℕ} (hN : 3 ≤ N) (hO : Odd N) :
    (∅ : Finset (ℕ × ℕ)) ∈ gFamily N := by
  obtain ⟨k, rfl⟩ := hO
  refine mem_image.2 ⟨{1, 2 * k + 1}, mem_filter.2 ⟨mem_powerset.2 ?_,
    Or.inl (Or.inr ⟨?_, ?_, ?_⟩)⟩, ?_⟩
  · intro x hx; simp only [mem_insert, mem_singleton] at hx; rw [mem_Icc]; omega
  · intro x hx; simp only [mem_insert, mem_singleton] at hx; rw [mem_Icc]; omega
  · rw [card_pair (by omega)]
  · intro t ht; simp only [mem_insert, mem_singleton] at ht; omega
  · rw [sepPairs, filter_eq_empty_iff]
    rintro ⟨a, b⟩ hp ⟨-, -, ⟨t, ht, h1, h2⟩, -⟩
    simp only [diagonals, mem_filter, mem_product, mem_Icc] at hp
    simp only [mem_insert, mem_singleton] at ht
    omega

/-- **Clause 1 says nothing at odd `N`**: for every odd `N ≥ 3`, every `S` contains a member of
`𝒢_N` (the empty one, `empty_mem_gFamily_of_odd`). So `pi_clause1` (`C10`) needs its hypothesis
`Even N` to say something: without it, the statement would hold at odd `N` for this reason alone. -/
theorem containsGMember_of_odd {N : ℕ} (hN : 3 ≤ N) (hO : Odd N) (S : Finset (ℕ × ℕ)) :
    ContainsGMember N S :=
  ⟨∅, empty_mem_gFamily_of_odd hN hO, empty_subset S⟩

/-- The empty set has a point of its locus (here: all of `ℚ^{diagonals}`) with every chord
non-zero. -/
theorem nonDegPt_empty (N : ℕ) : NonDegPt N ∅ :=
  ⟨fun _ => 1, by intro t ht; simp at ht, by intro d _; norm_num⟩

/-- **`𝒜_N` is not identically zero** for even `N ≥ 6`: at some rational point with no odd chord
zero, `𝒜_N ≠ 0`. From clause 1 (`pi_clause1`, `C10`): the empty set is non-degenerate, so if it
were a zero it would contain a member of `𝒢_N`, which would be empty. -/
theorem not_ampZeroOn_empty {N : ℕ} (hN : 6 ≤ N) (hE : Even N) : ¬ AmpZeroOn N ∅ := by
  intro hz
  obtain ⟨Z, hZ, hZs⟩ := pi_clause1 hN hE ⟨empty_subset _, nonDeg_of_pt (nonDegPt_empty N), hz⟩
  rw [subset_empty] at hZs
  exact empty_notMem_gFamily hE (hZs ▸ hZ)

/-- **`NLSM_N` is not identically zero** for even `N ≥ 6`: some rational point at which no odd
chord vanishes (so off every pole, where `NLSM` is not a junk value) has `NLSM N X ≠ 0` (from
`not_ampZeroOn_empty`, through `nonzeroOn_iff_not_ampZeroOn` of `C0`). -/
theorem exists_NLSM_ne_zero {N : ℕ} (hN : 6 ≤ N) (hE : Even N) :
    ∃ X : ℕ × ℕ → ℚ, (∀ d ∈ oddDiagonals N, X d ≠ 0) ∧ NLSM N X ≠ 0 := by
  obtain ⟨X, -, hX, h⟩ := nonzeroOn_iff_not_ampZeroOn.2 (not_ampZeroOn_empty hN hE)
  exact ⟨X, hX, h⟩

/-- `S_{1,3}` is a member of `𝒢_N` for every `N ≥ 3`. -/
theorem sepPairs_one_three_mem_gFamily {N : ℕ} (hN : 3 ≤ N) : sepPairs N {1, 3} ∈ gFamily N := by
  refine mem_image.2 ⟨{1, 3}, mem_filter.2 ⟨mem_powerset.2 ?_,
    Or.inl (Or.inr ⟨?_, by decide, by decide⟩)⟩, rfl⟩ <;>
  · intro x hx; simp only [mem_insert, mem_singleton] at hx; rw [mem_Icc]; omega

/-- **The hypothesis of clause 1 is satisfiable for every even `N ≥ 6`**: `S_{1,3}` is a
non-degenerate coordinate zero (by `cl2a`, `C10`). -/
theorem isNDZero_sepPairs_one_three {N : ℕ} (hN : 6 ≤ N) (hE : Even N) :
    IsNDZero N (sepPairs N {1, 3}) :=
  have hZ := sepPairs_one_three_mem_gFamily (N := N) (by omega)
  have h := cl2a hN hE hZ
  ⟨gFamily_sub hZ, nonDeg_of_pt h.1, h.2⟩

/-- For even `N`, the empty set is not a member of the list. -/
theorem not_isListMember_empty {N : ℕ} (hE : Even N) : ¬ IsListMember N ∅ :=
  fun h => empty_notMem_gFamily hE ((isListMember_iff_mem_gFamily hE).1 h)

/-- **`A_N^NLSM` is not identically zero** for even `N ≥ 6`: the empty set is not a zero. -/
theorem not_isCoordinateZero_empty {N : ℕ} (hN : 6 ≤ N) (hE : Even N) :
    ¬ IsCoordinateZero N ∅ := by
  rw [isCoordinateZero_iff_ampZeroOn (by omega) hE (empty_subset _)
    (nonDeg_of_pt (nonDegPt_empty N))]
  exact not_ampZeroOn_empty hN hE

/-- `S_{1,3}` is a member of the list for every even `N ≥ 6`. -/
theorem isListMember_sepPairs_one_three {N : ℕ} (hN : 6 ≤ N) (hE : Even N) :
    IsListMember N (sepPairs N {1, 3}) :=
  (isListMember_iff_mem_gFamily hE).2 (sepPairs_one_three_mem_gFamily (by omega))

/-- **The hypothesis of clause 1 of the main theorem can hold for every even `N ≥ 6`**: `S_{1,3}` is
a regular coordinate zero. -/
theorem isRegularCoordinateZero_sepPairs_one_three {N : ℕ} (hN : 6 ≤ N) (hE : Even N) :
    IsRegularCoordinateZero N (sepPairs N {1, 3}) :=
  (isRegularCoordinateZero_iff_isNDZero (by omega) hE).2 (isNDZero_sepPairs_one_three hN hE)

/-! ## The definitions of the main theorem, at six legs -/

/-- `S_{1,3,5}` is a **minimal regular coordinate zero** at `N = 6`. -/
theorem isMinimalCoordinateZero_six_one_three_five :
    IsMinimalCoordinateZero 6 (sepPairs 6 {1, 3, 5}) :=
  (isMinimalCoordinateZero_iff_isMinimalZero (by norm_num) (by decide)).2
    clause2_six_instances.1

/-- `S_{1,3,5}` is a **regular coordinate zero** at `N = 6`. -/
theorem isRegularCoordinateZero_six_one_three_five :
    IsRegularCoordinateZero 6 (sepPairs 6 {1, 3, 5}) :=
  isMinimalCoordinateZero_six_one_three_five.1

/-- `S_{1,3,5}` is a **regular** set at `N = 6`. -/
theorem isRegularSet_six_one_three_five : IsRegularSet 6 (sepPairs 6 {1, 3, 5}) :=
  isRegularCoordinateZero_six_one_three_five.2.1

/-- `S_{1,3,5}` is a **zero** at `N = 6`. -/
theorem isCoordinateZero_six_one_three_five : IsCoordinateZero 6 (sepPairs 6 {1, 3, 5}) :=
  isRegularCoordinateZero_six_one_three_five.2.2

/-- The set of all pairs is **not regular** at `N = 6`: on its locus `X_{1,4}` vanishes. -/
theorem not_isRegularSet_six_all_pairs : ¬ IsRegularSet 6 (diagonals 6) :=
  fun h => degenerate_full.1 (isRegularSet_iff_nondeg.1 h)

/-- The set of all pairs is **not a regular coordinate zero** at `N = 6`. -/
theorem not_isRegularCoordinateZero_six_all_pairs : ¬ IsRegularCoordinateZero 6 (diagonals 6) :=
  fun h => not_isRegularSet_six_all_pairs h.2.1

/-- The empty set is **not a zero** at `N = 6`: `A_6^NLSM` is not identically zero. -/
theorem not_isCoordinateZero_six_empty : ¬ IsCoordinateZero 6 ∅ :=
  not_isCoordinateZero_empty (by norm_num) (by decide)

/-- **Minimality is a condition**: `S_{1,3,5} ∪ {(1, 4)}` is a regular coordinate zero at `N = 6`
that is not minimal (removing `(1, 4)` leaves the zero `S_{1,3,5}`). -/
theorem not_isMinimalCoordinateZero_six_one_three_five_insert :
    IsRegularCoordinateZero 6 (insert (1, 4) (sepPairs 6 {1, 3, 5})) ∧
      ¬ IsMinimalCoordinateZero 6 (insert (1, 4) (sepPairs 6 {1, 3, 5})) :=
  ⟨(isRegularCoordinateZero_iff_isNDZero (by norm_num) (by decide)).2
      control_ndZero_not_minimal.1,
    fun h => control_ndZero_not_minimal.2
      ((isMinimalCoordinateZero_iff_isMinimalZero (by norm_num) (by decide)).1 h)⟩

/-- `S_{1,4}` is a **causal diamond** at `N = 6`: the legs `1 < 4` have the leg `2` between them
and the leg `5` outside. -/
theorem isCausalDiamond_six_one_four : IsCausalDiamond 6 (sepPairs 6 {1, 4}) :=
  ⟨1, by decide, 4, by decide, by decide, ⟨2, by decide, by decide⟩, ⟨5, by decide, by decide⟩,
    rfl⟩

/-- `S_{1,3,5}` is **not a causal diamond** at `N = 6` (a set of three legs of one parity). -/
theorem not_isCausalDiamond_six_one_three_five : ¬ IsCausalDiamond 6 (sepPairs 6 {1, 3, 5}) :=
  fun h => no_causal_diamond_in_separated_pairs (by decide) (by decide) ⟨_, h, subset_refl _⟩

-- registry: C-EVH5
/-- The list at eight legs has `30` members (the paper's example of the list at `N = 8`), through
the library's count of `gFamily 8` (`rev_card8`, computed). -/
theorem list_eight_card : Set.ncard {Z | IsListMember 8 Z} = 30 := by
  have h : {Z | IsListMember 8 Z} = ↑(gFamily 8) := by
    ext Z
    exact isListMember_iff_mem_gFamily (by decide)
  rw [h, Set.ncard_coe_finset]
  exact rev_card8

/-! ## The library's definitions of the amplitude -/

/-- The **sign of the shift** `v₀`: `+1` on an even-even pair, `−1` on an odd-odd pair, `0` on a
pair of mixed parity. -/
theorem shiftSign_values : shiftSign (2, 4) = 1 ∧ shiftSign (1, 3) = -1 ∧ shiftSign (1, 4) = 0 := by
  decide

/-- `{(1, 3), (1, 4)}` is a **triangulation** of the pentagon. -/
theorem isTriangulation_five : IsTriangulation 5 {(1, 3), (1, 4)} := by decide

/-- `{(1, 3)}` is **not a triangulation** of the pentagon: not maximal, `(1, 4)` crosses
nothing of it. -/
theorem not_isTriangulation_five_not_maximal : ¬ IsTriangulation 5 {(1, 3)} := by decide

/-- `{(1, 3), (2, 4)}` is **not a triangulation** of the pentagon: the two diagonals cross. -/
theorem not_isTriangulation_five_crossing : ¬ IsTriangulation 5 {(1, 3), (2, 4)} := by decide

/-- The shift **`δ` is the monomial `e⁻¹`**: its coefficient of `e⁻¹` is `1`, of `e⁰` is `0`. -/
theorem delta_coeff :
    (delta : LaurentSeries ℚ).coeff (-1) = 1 ∧ (delta : LaurentSeries ℚ).coeff 0 = 0 := by
  simp [delta]

/-- The **shifted point** `X + δ v₀` at the planar variable `X_{1,3} = 2`: its coefficient of `e⁰`
is `2`, of `e⁻¹` the sign `−1` of the odd pair `(1, 3)`. -/
theorem shifted_coeff :
    (shifted (fun _ => (2 : ℚ)) (1, 3)).coeff 0 = 2 ∧
      (shifted (fun _ => (2 : ℚ)) (1, 3)).coeff (-1) = -1 := by
  simp only [shifted, delta, shiftSign, HahnSeries.C_apply]
  norm_num [HahnSeries.coeff_single]

/-! ## Dissections, faces and the Cayley sum -/

/-- The empty dissection has one face, the whole polygon. -/
theorem faces_empty {N : ℕ} (hN : 4 ≤ N) (hE : Even N) : faces N ∅ = {Icc 1 N} := by
  have hE : N % 2 = 0 := Nat.even_iff.1 hE
  have hD : (∅ : Finset (ℕ × ℕ)) ∈ pkGDis N := pkG_mem_dis.2 ⟨empty_subset _, by simp⟩
  rw [faces_eq_image hN hE hD]
  have : pkGVerts ∅ (1, N) = Icc 1 N := by
    ext w
    rw [pkG_mem_verts, pkG_kids_empty, mem_Icc]
    simp
  simp [pkGRoots, this]

/-- The **Cayley sum** at `N = 4` is `X_{1,3} + X_{2,4}`: the amplitude
`NLSM_4 = −(X_{1,3} + X_{2,4})` is `−Cay_4` (`cayley_form`). -/
theorem cayleySum_four : cayleySum 4 gen = gen (1, 3) + gen (2, 4) := by
  have h := cayley_form (N := 4) (by norm_num) (by decide)
  rw [NLSM_four] at h
  linear_combination h

/-- The **Cayley vertex** of the whole quadrilateral is `X_{1,3} + X_{2,4}`: at `N = 4` the only
dissection by odd chords is the empty one, whose one face is the polygon. -/
theorem faceVertex_four : faceVertex 4 gen (Icc 1 4) = gen (1, 3) + gen (2, 4) := by
  have hD : pkGDis 4 = {∅} := by decide
  rw [← cayleySum_four, cayleySum, hD, sum_singleton, faces_empty (by norm_num) (by decide)]
  simp

/-! ## The three-cut setting, spread separators and shortening -/

/-- A configuration at `N = 10` is in the three-cut setting and in case (Z): `A′ = [1, 7]`,
`Θ = {4}`, `X = [1, 3]`, `Y = [5, 7]`, `τ = {5, 7}`, `σ = {1, 3}`. So the hypotheses of the
three-cut theorem (`three_separators_single_parity_arc_witness`) and of the zone-case lemmas can
hold together. -/
theorem figure_nine_configuration :
    ThreeSepSetting 10 7 1 3 5 7 {4} {5, 7} {1, 3} ∧ (∀ t ∈ ({5, 7} : Finset ℕ), t % 2 = 1) ∧
      (∀ s ∈ ({1, 3} : Finset ℕ), s % 2 = 1) ∧ ¬ CaseEP 1 3 5 7 {4} {5, 7} {1, 3} := by
  refine ⟨?_, by decide, by decide, ?_⟩
  · unfold ThreeSepSetting IsRun AdmSepCompl TailAvoiding intCompl prevLeg
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, Or.inr (by decide), Or.inr (by decide), by decide, by decide,
      Or.inl (by decide), Or.inl (by decide)⟩
  · unfold CaseEP HasWideGap
    decide

/-- A spread separator at `N = 10`: for `P* = (1, 8)` (odd-ended side
`A* = [1, 7]`), `Θ = {4}` is a free even separator of `A*` that is spread (runs `[1, 3]`,
`[5, 7]` hold `{1,3}`, `{5,7}`). -/
theorem example_eight_c_spread :
    oddSide 10 (1, 8) = Icc 1 7 ∧ {4} ∈ admSeps 10 (headStart (1, 8)) (headLen 10 (1, 8)) 0 ∧
      (∀ θ ∈ ({4} : Finset ℕ), θ % 2 = 0) ∧
      Disjoint (sepIn 10 (headStart (1, 8)) (headLen 10 (1, 8)) {4})
        (missing 10 (diagonals 10 \ {(1, 3), (5, 7), (8, 10)})) ∧
      IsSpread 10 (diagonals 10 \ {(1, 3), (5, 7), (8, 10)}) (1, 8) {4} :=
  ⟨by decide, by decide, by decide, by decide,
    (isSpread_iff_spread (by norm_num) (by decide) (by decide) (by decide)).2 (by decide)⟩

/-- The hypotheses of the shortening lemma (`shortening_spread_separator`) hold together: at
`N = 12`, for the missing set `M` of the eleven pairs below, `P′ = (8, 11)`
(`A′ = {11, 12, 1, …, 7}`, `B′ = {8, 9, 10}` linked), `Θ = {4, 12}`, the occupied runs
`X = {1, 2, 3}` before `Y = {5, 6, 7}` (`y₀ = 5`), `Q_X = (1, 4)` and `τ = {10}`, non-reaching
(`R_τ = {4, …, 10}`); then `Θ′ = {4}`. -/
theorem example_shortening_nonvacuous :
    let S : Finset (ℕ × ℕ) := diagonals 12 \ {(1, 3), (1, 10), (2, 8), (2, 12), (3, 10), (3, 12),
      (5, 7), (5, 8), (6, 9), (6, 10), (8, 10)}
    (8, 11) ∈ oddDiagonals 12 ∧ NoFreeSep 12 S (tailStart (8, 11)) (tailLen 12 (8, 11)) 1 ∧
      {4, 12} ∈ admSeps 12 (headStart (8, 11)) (headLen 12 (8, 11)) 0 ∧
      (∀ θ ∈ ({4, 12} : Finset ℕ), θ % 2 = 0) ∧
      Disjoint (sepIn 12 (headStart (8, 11)) (headLen 12 (8, 11)) {4, 12}) (missing 12 S) ∧
      IsOccupiedRun 12 S (8, 11) {4, 12} {1, 2, 3} ∧ IsOccupiedRun 12 S (8, 11) {4, 12} {5, 6, 7} ∧
      (∀ x ∈ ({1, 2, 3} : Finset ℕ), ∀ y ∈ ({5, 6, 7} : Finset ℕ),
        cycPos 12 (headStart (8, 11)) x < cycPos 12 (headStart (8, 11)) y) ∧
      (5 : ℕ) ∈ ({5, 6, 7} : Finset ℕ) ∧ (∀ y ∈ ({5, 6, 7} : Finset ℕ),
        cycPos 12 (headStart (8, 11)) 5 ≤ cycPos 12 (headStart (8, 11)) y) ∧
      (1, 4) ∈ oddDiagonals 12 ∧ oddSide 12 (1, 4) = {1, 2, 3} ∧
      {10} ∈ admSeps 12 (tailStart (1, 4)) (tailLen 12 (1, 4)) 1 ∧
      Disjoint (sepIn 12 (tailStart (1, 4)) (tailLen 12 (1, 4)) {10}) (missing 12 S) ∧
      5 ∉ Icc 1 12 \ reachPiece 12 (8, 11) (1, 4) {10} ∧
      ({4, 12} : Finset ℕ) \ (Icc 1 12 \ reachPiece 12 (8, 11) (1, 4) {10}) = {4} := by
  intro S
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, ?_, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩ <;>
  · unfold IsOccupiedRun IsRunOf; decide

/-! ## The predicates of the class residue -/

open MvPolynomial in
/-- On a line-closed `V`, if `g · D = P` in `RF` and `g` restricts to zero on `V`
(`RatZeroOn V g`), then `P` vanishes on `V`. -/
theorem ratZeroOn_poly {V : Set (ℕ × ℕ → ℚ)}
    (hV : ∀ x ∈ V, ∀ y ∈ V, ∀ t : ℚ, x + t • (y - x) ∈ V) {g : RF} {P D : MvPolynomial (ℕ × ℕ) ℚ}
    (hg : g * algebraMap _ RF D = algebraMap _ RF P) (h : RatZeroOn V g) :
    ∀ x ∈ V, eval x P = 0 := by
  obtain ⟨A, B, hAB, ⟨w, hw, hBw⟩, hA⟩ := h
  have hpoly : P * B = A * D := by
    apply IsFractionRing.injective (MvPolynomial (ℕ × ℕ) ℚ) RF
    rw [map_mul, map_mul, ← hg, ← hAB]
    ring
  refine line_bridge V hV P B hw hBw fun x hx hBx => ?_
  have e := congrArg (eval x) hpoly
  rw [map_mul, map_mul, hA x hx, zero_mul] at e
  exact (mul_eq_zero.1 e).resolve_right hBx

/-- **Non-vacuity of `HasNoPoleAlong`.** On a line-closed `V`, `1 / X_C` has a pole along
`H = V ∩ {X_C = 0}`: a denominator that vanishes on all of `H` is not allowed. -/
theorem not_hasNoPoleAlong_inv {V : Set (ℕ × ℕ → ℚ)}
    (hV : ∀ x ∈ V, ∀ y ∈ V, ∀ t : ℚ, x + t • (y - x) ∈ V) (C : ℕ × ℕ) :
    ¬ HasNoPoleAlong V {x | x ∈ V ∧ x C = 0} (gen C)⁻¹ := by
  rintro ⟨P, D, h, w, ⟨hwV, hwC⟩, hDw⟩
  have hg : ((gen C)⁻¹ * algebraMap _ RF D - algebraMap _ RF P) *
      algebraMap _ RF (MvPolynomial.X C : MvPolynomial (ℕ × ℕ) ℚ) =
        algebraMap _ RF (D - P * MvPolynomial.X C) := by
    rw [map_sub, map_mul, sub_mul, mul_assoc, mul_comm (algebraMap _ RF D),
      ← mul_assoc,
      show algebraMap _ RF (MvPolynomial.X C : MvPolynomial (ℕ × ℕ) ℚ) = gen C from rfl,
      inv_mul_cancel₀ (gen_ne_zero C), one_mul]
  have := ratZeroOn_poly hV hg h w hwV
  rw [map_sub, map_mul, MvPolynomial.eval_X, hwC, mul_zero, sub_zero] at this
  exact hDw this

/-- **Non-vacuity of `RestrictsToZeroAlong`.** On a line-closed `V`, the constant `1` does not
restrict to zero along any `H ⊆ V`. -/
theorem not_restrictsToZeroAlong_one {V H : Set (ℕ × ℕ → ℚ)}
    (hV : ∀ x ∈ V, ∀ y ∈ V, ∀ t : ℚ, x + t • (y - x) ∈ V) (hH : H ⊆ V) :
    ¬ RestrictsToZeroAlong V H 1 := by
  rintro ⟨P, D, h, ⟨w, hw, hDw⟩, hP⟩
  have hg : (1 * algebraMap _ RF D - algebraMap _ RF P) * algebraMap _ RF 1 =
      algebraMap _ RF (D - P) := by
    rw [map_one, mul_one, one_mul, map_sub]
  have := ratZeroOn_poly hV hg h w (hH hw)
  rw [map_sub, hP w hw, sub_zero] at this
  exact hDw this

/-- `L_S` is closed under lines (the library's `pkBr_line`, stated with the locus as a set). -/
theorem onLocus_line_closed (N : ℕ) (S : Finset (ℕ × ℕ)) :
    ∀ x ∈ {X : ℕ × ℕ → ℚ | OnLocus N S X}, ∀ y ∈ {X : ℕ × ℕ → ℚ | OnLocus N S X}, ∀ t : ℚ,
      x + t • (y - x) ∈ {X : ℕ × ℕ → ℚ | OnLocus N S X} :=
  pkBr_line

open MvPolynomial in
/-- **"`f|_H = 0`" does not depend on the representation.** On a line-closed `V` and a line-closed
`H ⊆ V`, if `f` restricts to zero along `H`, then for every representation of `f` on `V`
(`RatZeroOn V (f · D₀ − P₀)`, the form the definitions use) the numerator `P₀` vanishes on `H`. -/
theorem restrictsToZeroAlong_numerator {V H : Set (ℕ × ℕ → ℚ)}
    (hV : ∀ x ∈ V, ∀ y ∈ V, ∀ t : ℚ, x + t • (y - x) ∈ V)
    (hH : ∀ x ∈ H, ∀ y ∈ H, ∀ t : ℚ, x + t • (y - x) ∈ H) (hHV : H ⊆ V) {f : RF}
    (h : RestrictsToZeroAlong V H f) {P₀ D₀ : MvPolynomial (ℕ × ℕ) ℚ}
    (hf : RatZeroOn V (f * algebraMap _ RF D₀ - algebraMap _ RF P₀)) :
    ∀ x ∈ H, eval x P₀ = 0 := by
  obtain ⟨P, D, ⟨A, B, hAB, ⟨w, hw, hBw⟩, hA⟩, ⟨u, hu, hDu⟩, hP⟩ := h
  obtain ⟨A₀, B₀, hAB₀, ⟨w₀, hw₀, hBw₀⟩, hA₀⟩ := hf
  have hpoly : (P₀ * D - P * D₀) * (B * B₀) = A * B₀ * D₀ - A₀ * B * D := by
    apply IsFractionRing.injective (MvPolynomial (ℕ × ℕ) ℚ) RF
    simp only [map_mul, map_sub]
    rw [← hAB, ← hAB₀]
    ring
  have hBB : ∃ z ∈ V, eval z (B * B₀) ≠ 0 := by
    by_contra hc
    push Not at hc
    refine hBw₀ (line_bridge V hV B₀ B hw hBw (fun x hx hBx => ?_) w₀ hw₀)
    have e := hc x hx
    rw [map_mul] at e
    exact (mul_eq_zero.1 e).resolve_left hBx
  obtain ⟨z, hz, hBz⟩ := hBB
  have hV0 : ∀ x ∈ V, eval x (P₀ * D - P * D₀) = 0 :=
    line_bridge V hV _ (B * B₀) hz hBz fun x hx hx0 => by
      have e := congrArg (eval x) hpoly
      simp only [map_mul, map_sub, hA x hx, hA₀ x hx, zero_mul, sub_zero] at e
      rw [map_sub, map_mul, map_mul]
      exact (mul_eq_zero.1 e).resolve_right (by simpa using hx0)
  refine line_bridge H hH P₀ D hu hDu fun x hx hDx => ?_
  have e := hV0 x (hHV hx)
  rw [map_sub, map_mul, map_mul, hP x hx, zero_mul, sub_zero] at e
  exact (mul_eq_zero.1 e).resolve_right hDx

/-- **Non-vacuity in the setting of the extreme term**: `1 / x` (`x = X_P`) has a pole along `H` on
`L_S`, for every `S` and `P`; so "has no pole along `H`" is a condition (`not_hasNoPoleAlong_inv`).
-/
theorem hasNoPoleAlong_can_fail (N : ℕ) (S : Finset (ℕ × ℕ)) (P : ℕ × ℕ) :
    ¬ HasNoPoleAlong {X | OnLocus N S X} (residueHyperplane N S P) (gen P)⁻¹ :=
  not_hasNoPoleAlong_inv (onLocus_line_closed N S) P

/-! ## The class residue with a class of two members -/

-- registry: C-WGY9
/-- **The hypotheses of the residue theorem can hold with a class of two members**: an example of
the paper (`N = 8`, residue regime; `S` is every pair but `M = {13, 14, 26, 57, 68}`) is a
candidate set, the flank class of `X_{1,6}` is `{X_{1,4}, X_{1,6}}`, and (H1)–(H4) hold with
`x = X_{1,6}`, top `X_{1,6}`, bottom `X_{1,4}` and `d = 1`; so the class residue
(`simple_pole_along_flank_class`) and the extreme term (`only_extreme_term_survives`) are not
vacuous. -/
theorem example_four_six_residue_regime :
    IsCandidateSet 8 (diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)}) ∧
      hitClass 8 (diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)}) (1, 6) =
        {(1, 4), (1, 6)} ∧
      FlankClassPoleHypotheses 8 (diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)})
        (hitClass 8 (diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)}) (1, 6))
        (1, 6) (1, 6) (1, 4) ∧
      stripHalfLength 8 (1, 6) (1, 4) = 1 := by
  have hF : IsCandidateSet 8 (diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)}) := by
    rw [isCandidateSet_iff_inFpi (by decide), fpi_iff (by norm_num) (by decide) sdiff_subset]
    have hG : ¬ ContainsGMember 8 (diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)}) := by
      unfold ContainsGMember
      decide
    intro Z hZ
    by_contra h
    apply hG
    refine ⟨Z, hZ, fun p hp => ?_⟩
    by_contra hp'
    exact h ⟨p, mem_inter.2 ⟨hp, mem_sdiff.2 ⟨gFamily_sub hZ hp, hp'⟩⟩⟩
  exact ⟨hF, by decide, flank_class_pole_hypotheses_innermost (by norm_num) (by decide) hF
    (by decide) (by decide) (by decide), by decide⟩

-- registry: C-WGY9
/-- **No residue chord with both sides linked**: for the candidate set of
`example_four_six_residue_regime` (`N = 8`, every pair but `M = {13, 14, 26, 57, 68}`), the residue
chords are `X_{1,4}` and `X_{1,6}`; the separator `{5}` of `B_{1,4} = {4, …, 8}` and the separator
`{4}` of `A_{1,6} = {1, …, 5}` are free; `X_{1,6}` is an innermost chord; and no residue chord has
both sides linked. -/
theorem example_no_residue_chord_with_both_sides_linked :
    poleChords 8 (diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)}) = {(1, 4), (1, 6)} ∧
      ({5} ∈ admSeps 8 (tailStart (1, 4)) (tailLen 8 (1, 4)) 1 ∧
        Disjoint (sepIn 8 (tailStart (1, 4)) (tailLen 8 (1, 4)) {5})
          (missing 8 (diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)}))) ∧
      ({4} ∈ admSeps 8 (headStart (1, 6)) (headLen 8 (1, 6)) 0 ∧
        Disjoint (sepIn 8 (headStart (1, 6)) (headLen 8 (1, 6)) {4})
          (missing 8 (diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)}))) ∧
      IsInnermostChord 8 (diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)}) (1, 6) ∧
      ∀ P ∈ poleChords 8 (diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)}),
        ¬ (NoFreeSep 8 (diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)})
            (headStart P) (headLen 8 P) 0 ∧
          NoFreeSep 8 (diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)})
            (tailStart P) (tailLen 8 P) 1) :=
  ⟨by decide, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, by decide, by decide⟩

/-- `H` is closed under lines. -/
theorem residueHyperplane_line_closed (N : ℕ) (S : Finset (ℕ × ℕ)) (P : ℕ × ℕ) :
    ∀ x ∈ residueHyperplane N S P, ∀ y ∈ residueHyperplane N S P, ∀ t : ℚ,
      x + t • (y - x) ∈ residueHyperplane N S P := by
  intro x hx y hy t
  have h := (residueHyperplane_sub N S P).2 x hx y hy (1 - t) t
  convert h using 1
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- **The cases the extreme term excludes do fail** (non-vacuity of its (i) and (ii)): in the
example of `example_four_six_residue_regime`, the extreme terms do not restrict to zero on `H`:
`b_b` (`b = X_{1,4}`, the child amplitude `−(X_{1,3} + X_{2,4})`) and `a_t` (`t = X_{1,6}`,
`−(X_{6,8} + X_{1,7})`), each non-zero at an explicit rational point of `H`. -/
theorem example_four_six_extreme_terms_nonvanishing :
    ¬ RestrictsToZeroAlong
        {X | OnLocus 8 (diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)}) X}
        (residueHyperplane 8 (diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)}) (1, 6))
        (avoidingA 8 (hitClass 8 (diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)}) (1, 6))
          (1, 4)) ∧
      ¬ RestrictsToZeroAlong
        {X | OnLocus 8 (diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)}) X}
        (residueHyperplane 8 (diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)}) (1, 6))
        (avoidingB 8 (hitClass 8 (diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)}) (1, 6))
          (1, 6)) := by
  have hS : diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)} =
      ({(1, 5), (1, 6), (1, 7), (2, 4), (2, 5), (2, 7), (2, 8), (3, 5), (3, 6), (3, 7), (3, 8),
        (4, 6), (4, 7), (4, 8), (5, 8)} : Finset (ℕ × ℕ)) := by decide
  have hK := example_four_six_residue_regime.2.1
  have hV0 := (pkR_d_locus_sub 8 (diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)})).1
  -- the value of `f = algebraMap Q` on `H` is that of `Q`
  have key : ∀ (Q : MvPolynomial (ℕ × ℕ) ℚ) (x : ℕ × ℕ → ℚ),
      OnLocus 8 (diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)}) x → x (1, 6) = 0 →
      MvPolynomial.eval x Q ≠ 0 →
      ¬ RestrictsToZeroAlong
        {X | OnLocus 8 (diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)}) X}
        (residueHyperplane 8 (diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)}) (1, 6))
        (algebraMap _ RF Q) := fun Q x hx hx0 hQ h =>
    hQ (restrictsToZeroAlong_numerator (onLocus_line_closed _ _)
      (residueHyperplane_line_closed _ _ _) (fun _ hy => hy.1) h (D₀ := 1) (P₀ := Q)
      ⟨0, 1, by simp, ⟨_, hV0, by simp⟩, by simp⟩ x ⟨hx, hx0⟩)
  constructor
  · rw [hK]
    have e : avoidingA 8 {(1, 4), (1, 6)} (1, 4) =
        algebraMap _ RF
          (-(MvPolynomial.X (1, 3) + MvPolynomial.X (2, 4)) : MvPolynomial (ℕ × ℕ) ℚ) := by
      unfold avoidingA
      rw [show pkRBPull 8 (headStart (1, 4)) (headLen 8 (1, 4) + 1) {(1, 4), (1, 6)} = ∅ by
          decide, nlsmAvoiding_empty, show headLen 8 (1, 4) + 1 = 4 by decide, NLSM_four,
        show relab 8 (headStart (1, 4)) (1, 3) = (1, 3) by decide,
        show relab 8 (headStart (1, 4)) (2, 4) = (2, 4) by decide]
      simp [gen]
    rw [e]
    refine key _ (fun d => if d = (1, 3) ∨ d = (1, 5) ∨ d = (2, 5) ∨ d = (3, 5) ∨ d = (3, 7) ∨
      d = (3, 8) ∨ d = (5, 7) ∨ d = (5, 8) then 1 else if d = (4, 6) then -1 else 0) ?_
      (by decide) (by simp)
    unfold OnLocus
    rw [hS]
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
    norm_num [mesh, planar, vtx, diagonals]
  · rw [hK]
    have e : avoidingB 8 {(1, 4), (1, 6)} (1, 6) =
        algebraMap _ RF
          (-(MvPolynomial.X (6, 8) + MvPolynomial.X (1, 7)) : MvPolynomial (ℕ × ℕ) ℚ) := by
      unfold avoidingB
      rw [show pkRBPull 8 (tailStart (1, 6)) (tailLen 8 (1, 6) + 1) {(1, 4), (1, 6)} = ∅ by
          decide, nlsmAvoiding_empty, show tailLen 8 (1, 6) + 1 = 4 by decide, NLSM_four,
        show relab 8 (tailStart (1, 6)) (1, 3) = (6, 8) by decide,
        show relab 8 (tailStart (1, 6)) (2, 4) = (1, 7) by decide]
      simp [gen]
    rw [e]
    refine key _ (fun d => if d = (1, 7) ∨ d = (2, 7) ∨ d = (3, 7) ∨ d = (4, 7) ∨ d = (5, 7)
      then 1 else 0) ?_ (by decide) (by simp)
    unfold OnLocus
    rw [hS]
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
    norm_num [mesh, planar, vtx, diagonals]

/-! ## The strip region -/

/-- The **strip factor** of a member with itself is `1`. -/
theorem stripFactor_eight_self : stripFactor 8 (1, 6) (1, 6) (1, 6) = 1 := by
  simp [stripFactor]

/-- The **region** `Ω((1, 6), (1, 4))` at `N = 8` is the quadrilateral on the legs `1, 4, 5, 6`,
so its amplitude is `NLSM_4 = −(X_{1,5} + X_{4,6})` in the parent's planar variables. -/
theorem regionAmp_eight : regionAmp 8 (1, 6) (1, 4) = -(gen (1, 5) + gen (4, 6)) := by
  rw [regionAmp, show pkRBOmM 8 (1, 6) (1, 4) = 4 by decide, NLSM_four]
  simp [pkRSubX, pkRBOmL, pkRBOlo, planar, vtx, headStart, headLen, cycPos, diagonals]

/-- The **strip factor** of the example of `example_four_six_residue_regime` (`P = t = (1, 6)`,
`b = (1, 4)`): `N_Ω / x = −(X_{1,5} + X_{4,6}) / X_{1,6}`. -/
theorem stripFactor_eight :
    stripFactor 8 (1, 6) (1, 6) (1, 4) = -(gen (1, 5) + gen (4, 6)) / gen (1, 6) := by
  simp [stripFactor, regionAmp_eight]

/-! ## The marked locus and the value on it -/

-- registry: C-27FF
/-- **The value on the marked locus is not vacuous for a non-empty `I`**: for the standard polygon
`(6, 1)` and `I = {(0, 0)}` (a member, and closed), `Λ^I` has a point with `x ≠ 0` at which every
odd diagonal is non-zero, so the identity of `polygon_numerator_value` is asserted somewhere. -/
theorem marked_locus_nonvacuous :
    pkRClosed 6 1 {(0, 0)} ∧ pkRIsMem 6 1 (0, 0) ∧
      ∃ X : ℕ × ℕ → ℚ, pkRLam 6 1 {(0, 0)} X ∧ mesh 6 X 1 5 ≠ 0 ∧
        ∀ d ∈ oddDiagonals 6, X d ≠ 0 := by
  refine ⟨by unfold pkRClosed; decide, by unfold pkRIsMem; decide, fun d =>
    if d = (1, 3) then 3 else if d = (1, 4) then 5 else if d = (1, 5) then 7 else
    if d = (2, 4) then 2 else if d = (2, 5) then 2 else if d = (2, 6) then 0 else
    if d = (3, 5) then 5 else if d = (3, 6) then 3 else if d = (4, 6) then -2 else 0,
    ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro a ha b hb h2 hp h1 hc
    simp only [mem_Icc] at ha hb
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    interval_cases a <;> interval_cases b <;>
      simp_all (config := {decide := true}) [mesh, planar] <;> norm_num
  · simp (config := {decide := true}) [mesh, planar]; norm_num
  · intro Q hQ t ht
    simp only [mem_singleton] at hQ
    subst hQ
    have : pkRMinrect 6 1 (0, 0) = {(5, 2)} := by decide
    rw [this, mem_singleton] at ht
    subst ht
    simp (config := {decide := true}) [mesh, planar]; norm_num
  · simp (config := {decide := true}) [mesh, planar]; norm_num
  · have : oddDiagonals 6 = {(1, 4), (2, 5), (3, 6)} := by decide
    rw [this]
    intro d hd
    simp only [mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl | rfl <;> simp

/-! ## Hypotheses that hold -/

/-- The hypothesis of the `T`-separated zeros (`t_separated_zero`) holds for `T = {1, 3, 5}` at
`N = 6`. -/
theorem isSameParitySet_six_one_three_five : IsSameParitySet 6 {1, 3, 5} := by decide

/-- The hypotheses of the value on the marked locus (`pkR_omega`) hold with a member: `n = 6`,
`d₁ = 1`, `I = {(0, 0)}`, and its locus `Λ^I` has a point, so the identity is about something. -/
theorem polygon_value_hypotheses :
    (∀ Q ∈ ({(0, 0)} : Finset (ℕ × ℕ)), pkRIsMem 6 1 Q) ∧ ∃ X, pkRLam 6 1 {(0, 0)} X := by
  obtain ⟨-, hmem, X, hX, -⟩ := marked_locus_nonvacuous
  exact ⟨fun Q hQ => by rw [mem_singleton.1 hQ]; exact hmem, X, hX⟩

/-- The numerator of `NLSM_N` (`nlsm_numerator_hom`) at `N = 4`, for the evaluation at the point
with every planar variable `1`, where no odd planar variable vanishes, so its hypothesis holds. -/
theorem numerator_hom_at_one :
    MvPolynomial.eval (fun _ => (1 : ℚ)) (NP ℚ 4) =
      NLSM 4 (fun d => MvPolynomial.eval (fun _ => (1 : ℚ)) (MvPolynomial.X d)) *
        MvPolynomial.eval (fun _ => (1 : ℚ)) (oddDen ℚ 4) :=
  nlsm_numerator_hom (MvPolynomial.eval fun _ => (1 : ℚ)) (by norm_num) (by simp)

/-! ## The image of the cut -/

/-- The two candidate sets of `example_cut_image_hyperplane`: the set of pairs, and the child set of
its even-ended side `B_{1,4}` (`decide`). -/
theorem example_cut_image_hyperplane_candidates :
    IsCandidateSet 8 (diagonals 8 \ {(1, 7), (2, 6), (3, 5), (4, 6), (4, 8)}) ∧
      IsCandidateSet 6 ((diagonals 6).filter (fun σ => ChildPairIn 8
        (diagonals 8 \ {(1, 7), (2, 6), (3, 5), (4, 6), (4, 8)}) 4 5 6 (fun j => vtx 8 (4 + j - 1))
        σ.1 σ.2)) := by
  have hF : IsCandidateSet 8 (diagonals 8 \ {(1, 7), (2, 6), (3, 5), (4, 6), (4, 8)}) := by
    rw [isCandidateSet_iff_inFpi (by decide), fpi_iff (by norm_num) (by decide) sdiff_subset]
    have hG : ¬ ContainsGMember 8 (diagonals 8 \ {(1, 7), (2, 6), (3, 5), (4, 6), (4, 8)}) := by
      unfold ContainsGMember
      decide
    intro Z hZ
    by_contra h
    apply hG
    refine ⟨Z, hZ, fun p hp => ?_⟩
    by_contra hp'
    exact h ⟨p, mem_inter.2 ⟨hp, mem_sdiff.2 ⟨gFamily_sub hZ hp, hp'⟩⟩⟩
  have hC : IsCandidateSet 6 ((diagonals 6).filter (fun σ => ChildPairIn 8
      (diagonals 8 \ {(1, 7), (2, 6), (3, 5), (4, 6), (4, 8)}) 4 5 6 (fun j => vtx 8 (4 + j - 1))
      σ.1 σ.2)) := by
    rw [isCandidateSet_iff_inFpi (by decide), fpi_iff (by norm_num) (by decide) (filter_subset _ _)]
    have hG : ¬ ContainsGMember 6 ((diagonals 6).filter (fun σ => ChildPairIn 8
        (diagonals 8 \ {(1, 7), (2, 6), (3, 5), (4, 6), (4, 8)}) 4 5 6
        (fun j => vtx 8 (4 + j - 1)) σ.1 σ.2)) := by
      unfold ContainsGMember
      decide
    intro Z hZ
    by_contra h
    apply hG
    refine ⟨Z, hZ, fun p hp => ?_⟩
    by_contra hp'
    exact h ⟨p, mem_inter.2 ⟨hp, mem_sdiff.2 ⟨gFamily_sub hZ hp, hp'⟩⟩⟩
  exact ⟨hF, hC⟩

-- registry: C-VRVR
/-- **A cut image that is a hyperplane**: an example of the paper (`N = 8`, `S` every pair but
`M = {17, 26, 35, 46, 48}`) is a candidate set at which the chord `(1, 4)` is on shell
(`cleanChords`) and not a residue chord (`poleChords`), its even-ended side
`B_{1,4} = (4, 5, 6, 7, 8)` has no absorber and a child set that is a candidate set of the
`6`-gon, and some point of the B-child's locus is not the child point of a point of
`L_S` with `X_{1,4} = 0`. -/
theorem example_cut_image_hyperplane :
    IsCandidateSet 8 (diagonals 8 \ {(1, 7), (2, 6), (3, 5), (4, 6), (4, 8)}) ∧
      (1, 4) ∈ cleanChords 8 (diagonals 8 \ {(1, 7), (2, 6), (3, 5), (4, 6), (4, 8)}) ∧
      (1, 4) ∉ poleChords 8 (diagonals 8 \ {(1, 7), (2, 6), (3, 5), (4, 6), (4, 8)}) ∧
      ¬ HasCutAbsorber 8 (diagonals 8 \ {(1, 7), (2, 6), (3, 5), (4, 6), (4, 8)}) 4 5 ∧
      IsCandidateSet 6 ((diagonals 6).filter (fun σ => ChildPairIn 8
        (diagonals 8 \ {(1, 7), (2, 6), (3, 5), (4, 6), (4, 8)}) 4 5 6 (fun j => vtx 8 (4 + j - 1))
        σ.1 σ.2)) ∧
      ∃ y : ℕ × ℕ → ℚ,
        OnLocus 6 ((diagonals 6).filter (fun σ => ChildPairIn 8
          (diagonals 8 \ {(1, 7), (2, 6), (3, 5), (4, 6), (4, 8)}) 4 5 6
          (fun j => vtx 8 (4 + j - 1)) σ.1 σ.2)) y ∧
        ¬ ∃ X : ℕ × ℕ → ℚ, OnLocus 8 (diagonals 8 \ {(1, 7), (2, 6), (3, 5), (4, 6), (4, 8)}) X ∧
          X (1, 4) = 0 ∧ ∀ d ∈ diagonals 6, X (relab 8 4 d) = y d := by
  obtain ⟨hF, hC⟩ := example_cut_image_hyperplane_candidates
  have hno : ¬ HasCutAbsorber 8 (diagonals 8 \ {(1, 7), (2, 6), (3, 5), (4, 6), (4, 8)}) 4 5 := by
    decide
  have hPO : ((1, 4) : ℕ × ℕ) ∈ oddDiagonals 8 := by decide
  have hX0 : ∃ X0 : ℕ × ℕ → ℚ,
      OnLocus 8 (diagonals 8 \ {(1, 7), (2, 6), (3, 5), (4, 6), (4, 8)}) X0 ∧
        planar 8 X0 4 (4 + 5) ≠ 0 := by
    obtain ⟨X0, hX0, hP0⟩ := ((isCandidateSet_iff_inFpi (by decide)).1 hF).2.1 (1, 4)
      (mem_filter.1 hPO).1
    have hc : planar 8 X0 4 (4 + 5) = X0 (1, 4) := pkR_ch_chordT X0 hPO
    exact ⟨X0, hX0, by rw [hc]; exact hP0⟩
  obtain ⟨hiff, y, hy, hyl⟩ := cut_image_hyperplane (N := 8) (s := 4) (k := 5) (by decide)
    (by decide) (by norm_num) (by norm_num) (by norm_num) sdiff_subset hno (by decide) hX0
  refine ⟨hF, by decide, by decide, hno, hC, y, hy, fun ⟨X, hX, hXP, hXy⟩ => hyl ?_⟩
  refine (hiff y hy).1 ⟨X, hX, ?_, hXy⟩
  have hc : planar 8 X 4 (4 + 5) = X (1, 4) := pkR_ch_chordT X hPO
  rw [hc]
  exact hXP

/-! ## A pole-free locus at six legs -/

-- registry: C-D8ZX
/-- **A pole-free locus at six legs**: an example of the paper (`N = 6`,
`S = {24, 25, 35, 36, 46}`) is a candidate set with no residue chord (`poleChords`), and on `L_S`
the amplitude is the parity form `E`, a linear form: `NLSM_6 = E` at every rational point of `L_S`
at which no odd chord vanishes. -/
theorem example_pole_free_locus_six :
    IsCandidateSet 6 {(2, 4), (2, 5), (3, 5), (3, 6), (4, 6)} ∧
      poleChords 6 {(2, 4), (2, 5), (3, 5), (3, 6), (4, 6)} = ∅ ∧
      ∀ X : ℕ × ℕ → ℚ, OnLocus 6 {(2, 4), (2, 5), (3, 5), (3, 6), (4, 6)} X →
        (∀ d ∈ oddDiagonals 6, X d ≠ 0) → NLSM 6 X = pkGE 6 X := by
  refine ⟨?_, by decide, fun X hL hX => ?_⟩
  · rw [isCandidateSet_iff_inFpi (by decide), fpi_iff (by norm_num) (by decide) (by decide)]
    have hG : ¬ ContainsGMember 6 {(2, 4), (2, 5), (3, 5), (3, 6), (4, 6)} := by
      unfold ContainsGMember
      decide
    intro Z hZ
    by_contra h
    apply hG
    refine ⟨Z, hZ, fun p hp => ?_⟩
    by_contra hp'
    exact h ⟨p, mem_inter.2 ⟨hp, mem_sdiff.2 ⟨gFamily_sub hZ hp, hp'⟩⟩⟩
  have m24 := hL (2, 4) (by decide)
  have m25 := hL (2, 5) (by decide)
  have m35 := hL (3, 5) (by decide)
  have m36 := hL (3, 6) (by decide)
  have m46 := hL (4, 6) (by decide)
  simp only [mesh, planar] at m24 m25 m35 m36 m46
  norm_num [vtx, diagonals] at m24 m25 m35 m36 m46
  have n14 : X (1, 4) ≠ 0 := hX (1, 4) (by decide)
  have n25 : X (2, 5) ≠ 0 := hX (2, 5) (by decide)
  have n36 : X (3, 6) ≠ 0 := hX (3, 6) (by decide)
  have hset : (diagonals 6).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0) =
      {(2, 4), (2, 6), (4, 6)} := by decide
  rw [NLSM_six, paper43, pkGE, hset, sum_insert (by decide), sum_insert (by decide), sum_singleton]
  simp only [mesh, planar]
  norm_num [vtx, diagonals]
  -- the five mesh equations solved for five planar variables
  have e24 : X (2, 4) = X (2, 5) - X (3, 5) := by linarith
  have e46 : X (4, 6) = X (3, 6) - X (3, 5) := by linarith
  have e15 : X (1, 5) = X (1, 4) - X (3, 6) + X (3, 5) := by linarith
  have e13 : X (1, 3) = X (1, 4) + X (3, 5) := by linarith
  have e26 : X (2, 6) = X (2, 5) + X (3, 6) - X (3, 5) := by linarith
  rw [e24, e46, e15, e13, e26]
  field_simp
  ring

open MvPolynomial in
-- registry: C-D8ZX
/-- **The same locus, as rational functions**: on the locus of `S = {24, 25, 35, 36, 46}` at
`N = 6`, `NLSM_6 - E` restricts to the zero rational function (`RatZeroOn`, the form of a zero),
with `E` the parity form at the generic point; so `NLSM_6` restricted to `L_S` is the linear form
`E`, with no pole. -/
theorem example_pole_free_locus_six_rational :
    RatZeroOn {x | OnLocus 6 {(2, 4), (2, 5), (3, 5), (3, 6), (4, 6)} x}
      (NLSM 6 gen - ∑ t ∈ (diagonals 6).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0),
        mesh 6 gen t.1 t.2) := by
  have hset : (diagonals 6).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0) =
      {(2, 4), (2, 6), (4, 6)} := by decide
  -- `Q` clears the three odd poles; `P = (NLSM_6 - E) Q`, written out from `paper43`
  let Q : MvPolynomial (ℕ × ℕ) ℚ := X (1, 4) * X (2, 5) * X (3, 6)
  let E : MvPolynomial (ℕ × ℕ) ℚ := X (2, 4) + X (3, 5) - X (2, 5) +
    (X (2, 6) + X (1, 3) - X (3, 6)) + (X (4, 6) + X (1, 5) - X (1, 4))
  let P : MvPolynomial (ℕ × ℕ) ℚ :=
    (X (1, 3) + X (2, 4)) * (X (1, 5) + X (4, 6)) * X (2, 5) * X (3, 6) +
      (X (3, 5) + X (4, 6)) * (X (1, 3) + X (2, 6)) * X (1, 4) * X (2, 5) +
      (X (1, 5) + X (2, 6)) * (X (3, 5) + X (2, 4)) * X (1, 4) * X (3, 6) -
      (X (1, 3) + X (2, 4) + X (3, 5) + X (4, 6) + X (1, 5) + X (2, 6) + E) * Q
  refine ⟨P, Q, ?_, ?_, ?_⟩
  · rw [NLSM_six, paper43, hset, sum_insert (by decide), sum_insert (by decide), sum_singleton]
    simp only [mesh, planar]
    norm_num [vtx, diagonals]
    have h14 := gen_ne_zero (1, 4)
    have h25 := gen_ne_zero (2, 5)
    have h36 := gen_ne_zero (3, 6)
    simp only [P, Q, E, map_add, map_sub, map_mul]
    simp only [gen] at h14 h25 h36 ⊢
    field_simp
    ring
  · -- a point of the locus off the three poles
    refine ⟨fun d => if d = (1, 3) then 1 else if d = (2, 6) then 2 else
      if d = (1, 5) ∨ d = (3, 5) then 0 else 1, ?_, ?_⟩
    · intro t ht
      fin_cases ht <;> norm_num [mesh, planar, vtx, diagonals]
    · simp [Q]
  · intro x hx
    have hL : OnLocus 6 {(2, 4), (2, 5), (3, 5), (3, 6), (4, 6)} x := hx
    have m24 := hL (2, 4) (by decide)
    have m25 := hL (2, 5) (by decide)
    have m35 := hL (3, 5) (by decide)
    have m36 := hL (3, 6) (by decide)
    have m46 := hL (4, 6) (by decide)
    simp only [mesh, planar] at m24 m25 m35 m36 m46
    norm_num [vtx, diagonals] at m24 m25 m35 m36 m46
    have e24 : x (2, 4) = x (2, 5) - x (3, 5) := by linarith
    have e46 : x (4, 6) = x (3, 6) - x (3, 5) := by linarith
    have e15 : x (1, 5) = x (1, 4) - x (3, 6) + x (3, 5) := by linarith
    have e13 : x (1, 3) = x (1, 4) + x (3, 5) := by linarith
    have e26 : x (2, 6) = x (2, 5) + x (3, 6) - x (3, 5) := by linarith
    simp only [P, Q, E, map_add, map_sub, map_mul, eval_X]
    rw [e24, e46, e15, e13, e26]
    ring

end PionCompleteness.PaperTests
