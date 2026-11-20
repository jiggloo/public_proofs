/-
Copyright (c) 2026 Henru Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henru Wang
-/
module

import PionCompleteness

/-!
# The statements, pinned

`lake build Statements` prints each statement below (`#check`) and the body of each definition
below (`#print`), and compares the output with the text written above it (`#guard_msgs`), so any
change to one of them fails the build until the text here is updated and reviewed. A reader can
check the statements here, side by side with the paper, instead of in the modules.

Pinned: the statements of Theorem Π (module `C10`) and, after them, the main theorem in the paper's
terms (module `Paper`: its definitions and their equalities with the library's forms, its three
statements and the pointwise reading of a zero); every declaration of `Paper` (the paper's
statements in its exact form), of `PaperTests` (every test of `Paper`: non-vacuity, definitions on
given objects, examples, hypotheses that hold), of `Conventions` (the outside anchors: KNT's closed
forms and their Feynman rules in the Cayley parametrisation, transcribed from arXiv:1304.3048, and
their controls), and the library definitions a paper definition is matched by (those of coordinate
loci, zeros, minimal zeros, separated pairs, the list, the missing set, the sides of an odd chord,
the chord families, dissections and linked sides; the forms of the block sums and the face identity;
the three-cut setting and the flank class `K*`; those the class residue's definitions are read
through; and those of the polygon with a marked leg and of the children of an odd chord).
At the end: the library definitions that appear only in helper statements relating a `Paper`
statement or definition to the library's (`pkTZoneSet`, `pkTZH` in `C1`; `pkGV` in `C4`;
`pkRBAP`, `pkRBNP`, `pkRBTP`, `pkRBOT`, `pkRBZ5`, `pkRBCross`, `pkRBPsi` in `C6`–`C8`), and nine
library theorems the paper cites by name (`onRect_inhabited`, `amp_ratZero_onRect`,
`pkL_onLocus_anchor`, `pkM_base4`, `pkR_const9`, `pkR_omega0`, `pkR_psi_all`, `pkR_notq_lam`,
`pkR_omega`). The other declarations of the library are not pinned, among them some the paper cites
and some definitions that pinned statements and definitions use: the pins do not cover the
definitional closure.
`PaperTests` shows that Theorem Π says something: for odd `N ≥ 3`, `∅ ∈ 𝒢_N`, so clause 1
without `Even N` would hold for every `S`; and the hypothesis of clause 1 can hold. It shows the
same for the main theorem in the paper's terms, but the odd case.

Limits. The output is printed with the default options, so a change visible only in implicit or
instance arguments would not show, and a change of notation or of the pretty-printer fails a pin
that says the same thing. A pin checks the statement, not the definitions of the other modules it
uses, and not docstrings. That every declaration of `Paper`, `PaperTests` and `Conventions` has a
pin here is checked outside this project, by the private tooling of its source repository.
-/

-- Theorem Π (`C10`): clause 1, the members of `𝒢_N` as zeros, clause 2, and the minimal zeros.
/--
info: PionCompleteness.Pi.pi_clause1 {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {S : Finset (ℕ × ℕ)}
  (hS : PionCompleteness.Pi.IsNDZero N S) : PionCompleteness.Pi.ContainsGMember N S
-/
#guard_msgs in
#check PionCompleteness.Pi.pi_clause1
/--
info: PionCompleteness.Pi.cl2a {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {Z : Finset (ℕ × ℕ)}
  (hZ : Z ∈ PionCompleteness.Pi.gFamily N) : PionCompleteness.Pi.NonDegPt N Z ∧ PionCompleteness.Pi.AmpZeroOn N Z
-/
#guard_msgs in
#check PionCompleteness.Pi.cl2a
/--
info: PionCompleteness.Pi.pi_clause2 {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {Z : Finset (ℕ × ℕ)}
  (hZ : Z ∈ PionCompleteness.Pi.gFamily N) : PionCompleteness.Pi.NonDegPt N Z ∧ PionCompleteness.Pi.IsMinimalZero N Z
-/
#guard_msgs in
#check PionCompleteness.Pi.pi_clause2
/--
info: PionCompleteness.Pi.pi_minimal_iff {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {Z : Finset (ℕ × ℕ)} :
  PionCompleteness.Pi.IsMinimalZero N Z ↔ Z ∈ PionCompleteness.Pi.gFamily N
-/
#guard_msgs in
#check PionCompleteness.Pi.pi_minimal_iff

-- `Paper`: the main theorem in the paper's terms: the definitions of its statement (regular sets,
-- zeros, regular coordinate zeros and minimal ones, causal diamonds, the list), its three
-- statements, the equalities of the definitions with the library's forms that the statements of
-- `C10` use, and the pointwise reading of a zero.
/--
info: def PionCompleteness.Paper.NLSM.Zeros.IsRegularSet : ℕ → Finset (ℕ × ℕ) → Prop :=
fun N S =>
  ∀ d ∈ PionCompleteness.TreeRectangleZero.diagonals N,
    ¬∀ (x : ℕ × ℕ → ℚ), PionCompleteness.ChainSlice.OnLocus N S x → x d = 0
-/
#guard_msgs in
#print PionCompleteness.Paper.NLSM.Zeros.IsRegularSet
/--
info: def PionCompleteness.Paper.NLSM.Zeros.IsCoordinateZero : ℕ → Finset (ℕ × ℕ) → Prop :=
fun N S =>
  PionCompleteness.PionNLSM.RatZeroOn {x | PionCompleteness.ChainSlice.OnLocus N S x}
    (PionCompleteness.PionNLSM.NLSM N PionCompleteness.PionNLSM.gen)
-/
#guard_msgs in
#print PionCompleteness.Paper.NLSM.Zeros.IsCoordinateZero
/--
info: def PionCompleteness.Paper.NLSM.Zeros.IsRegularCoordinateZero : ℕ → Finset (ℕ × ℕ) → Prop :=
fun N S =>
  S ⊆ PionCompleteness.TreeRectangleZero.diagonals N ∧
    PionCompleteness.Paper.NLSM.Zeros.IsRegularSet N S ∧ PionCompleteness.Paper.NLSM.Zeros.IsCoordinateZero N S
-/
#guard_msgs in
#print PionCompleteness.Paper.NLSM.Zeros.IsRegularCoordinateZero
/--
info: def PionCompleteness.Paper.NLSM.Zeros.IsMinimalCoordinateZero : ℕ → Finset (ℕ × ℕ) → Prop :=
fun N Z =>
  PionCompleteness.Paper.NLSM.Zeros.IsRegularCoordinateZero N Z ∧
    ∀ t ∈ Z, ¬PionCompleteness.Paper.NLSM.Zeros.IsCoordinateZero N (Z.erase t)
-/
#guard_msgs in
#print PionCompleteness.Paper.NLSM.Zeros.IsMinimalCoordinateZero
/--
info: def PionCompleteness.Paper.NLSM.Zeros.Families.IsCausalDiamond : ℕ → Finset (ℕ × ℕ) → Prop :=
fun N Z =>
  ∃ a ∈ Finset.Icc 1 N,
    ∃ b ∈ Finset.Icc 1 N,
      a < b ∧ (∃ u, a < u ∧ u < b) ∧ (∃ u ∈ Finset.Icc 1 N, u < a ∨ b < u) ∧ Z = PionCompleteness.Pi.sepPairs N {a, b}
-/
#guard_msgs in
#print PionCompleteness.Paper.NLSM.Zeros.Families.IsCausalDiamond
/--
info: def PionCompleteness.Paper.NLSM.Zeros.Families.IsListMember : ℕ → Finset (ℕ × ℕ) → Prop :=
fun N Z =>
  PionCompleteness.Paper.NLSM.Zeros.Families.IsCausalDiamond N Z ∨
    ∃ T ⊆ Finset.Icc 1 N, 3 ≤ T.card ∧ (∀ t ∈ T, ∀ u ∈ T, t % 2 = u % 2) ∧ Z = PionCompleteness.Pi.sepPairs N T
-/
#guard_msgs in
#print PionCompleteness.Paper.NLSM.Zeros.Families.IsListMember
/--
info: PionCompleteness.Paper.NLSM.Zeros.every_coordinate_zero_contains_a_family_member {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
  {S : Finset (ℕ × ℕ)} (hS : PionCompleteness.Paper.NLSM.Zeros.IsRegularCoordinateZero N S) :
  ∃ Z, PionCompleteness.Paper.NLSM.Zeros.Families.IsListMember N Z ∧ Z ⊆ S
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.every_coordinate_zero_contains_a_family_member
/--
info: PionCompleteness.Paper.NLSM.Zeros.family_members_are_minimal_zeros {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
  (Z : Finset (ℕ × ℕ)) :
  PionCompleteness.Paper.NLSM.Zeros.Families.IsListMember N Z →
    PionCompleteness.Paper.NLSM.Zeros.IsMinimalCoordinateZero N Z
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.family_members_are_minimal_zeros
/--
info: PionCompleteness.Paper.NLSM.Zeros.minimal_coordinate_zeros_are_the_list {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
  {Z : Finset (ℕ × ℕ)} :
  PionCompleteness.Paper.NLSM.Zeros.IsMinimalCoordinateZero N Z ↔
    PionCompleteness.Paper.NLSM.Zeros.Families.IsListMember N Z
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.minimal_coordinate_zeros_are_the_list
/--
info: PionCompleteness.Paper.NLSM.Zeros.isRegularSet_iff_nondeg {N : ℕ} {S : Finset (ℕ × ℕ)} :
  PionCompleteness.Paper.NLSM.Zeros.IsRegularSet N S ↔ PionCompleteness.ChainSlice.Nondeg N S
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.isRegularSet_iff_nondeg
/--
info: PionCompleteness.Paper.NLSM.Zeros.isCoordinateZero_iff_ampZeroOn {N : ℕ} (hN : 4 ≤ N) (hE : Even N) {S : Finset (ℕ × ℕ)}
  (hS : S ⊆ PionCompleteness.TreeRectangleZero.diagonals N) (hreg : PionCompleteness.ChainSlice.Nondeg N S) :
  PionCompleteness.Paper.NLSM.Zeros.IsCoordinateZero N S ↔ PionCompleteness.Pi.AmpZeroOn N S
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.isCoordinateZero_iff_ampZeroOn
/--
info: PionCompleteness.Paper.NLSM.Zeros.isCoordinateZero_iff_pointwise {N : ℕ} (hN : 4 ≤ N) (hE : Even N) {S : Finset (ℕ × ℕ)}
  (hS : S ⊆ PionCompleteness.TreeRectangleZero.diagonals N)
  (hreg : PionCompleteness.Paper.NLSM.Zeros.IsRegularSet N S) :
  PionCompleteness.Paper.NLSM.Zeros.IsCoordinateZero N S ↔
    ∀ (x : ℕ × ℕ → ℚ),
      PionCompleteness.ChainSlice.OnLocus N S x →
        (∀ d ∈ PionCompleteness.PionZeros.oddDiagonals N, x d ≠ 0) → PionCompleteness.PionNLSM.NLSM N x = 0
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.isCoordinateZero_iff_pointwise
/--
info: PionCompleteness.Paper.NLSM.Zeros.isRegularCoordinateZero_iff_isNDZero {N : ℕ} (hN : 4 ≤ N) (hE : Even N)
  {S : Finset (ℕ × ℕ)} :
  PionCompleteness.Paper.NLSM.Zeros.IsRegularCoordinateZero N S ↔ PionCompleteness.Pi.IsNDZero N S
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.isRegularCoordinateZero_iff_isNDZero
/--
info: PionCompleteness.Paper.NLSM.Zeros.isMinimalCoordinateZero_iff_isMinimalZero {N : ℕ} (hN : 4 ≤ N) (hE : Even N)
  {Z : Finset (ℕ × ℕ)} :
  PionCompleteness.Paper.NLSM.Zeros.IsMinimalCoordinateZero N Z ↔ PionCompleteness.Pi.IsMinimalZero N Z
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.isMinimalCoordinateZero_iff_isMinimalZero
/--
info: PionCompleteness.Paper.NLSM.Zeros.Families.isListMember_iff_mem_gFamily {N : ℕ} (hE : Even N) {Z : Finset (ℕ × ℕ)} :
  PionCompleteness.Paper.NLSM.Zeros.Families.IsListMember N Z ↔ Z ∈ PionCompleteness.Pi.gFamily N
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.Families.isListMember_iff_mem_gFamily

-- `Paper`: the paper's statements in its exact form, and its definitions.
/--
info: def PionCompleteness.Paper.NLSM.FeynmanRules.cayleySum.{u_1} : {K : Type u_1} → [Field K] → ℕ → (ℕ × ℕ → K) → K :=
fun {K} [Field K] N X =>
  ∑ D ∈ PionCompleteness.Pi.pkGDis N,
    (∏ F ∈ PionCompleteness.Paper.Combinatorics.Polygons.faces N D,
        PionCompleteness.Paper.NLSM.FeynmanRules.faceVertex N X F) *
      ∏ P ∈ D, -(X P)⁻¹
-/
#guard_msgs in
#print PionCompleteness.Paper.NLSM.FeynmanRules.cayleySum

/--
info: PionCompleteness.Paper.onLocus_sepPairs_of_onZT {N : ℕ} {T : Finset ℕ} {X : ℕ × ℕ → ℚ}
  (hX : PionCompleteness.PionZeros.OnZT N T X) :
  PionCompleteness.ChainSlice.OnLocus N (PionCompleteness.Pi.sepPairs N T) X
-/
#guard_msgs in
#check PionCompleteness.Paper.onLocus_sepPairs_of_onZT

/--
info: PionCompleteness.Paper.onZT_iff_onLocus_sepPairs {N : ℕ} {T : Finset ℕ} (hT : T ⊆ Finset.Icc 1 N) {X : ℕ × ℕ → ℚ} :
  PionCompleteness.PionZeros.OnZT N T X ↔ PionCompleteness.ChainSlice.OnLocus N (PionCompleteness.Pi.sepPairs N T) X
-/
#guard_msgs in
#check PionCompleteness.Paper.onZT_iff_onLocus_sepPairs

/--
info: PionCompleteness.Paper.NLSM.Zeros.Families.t_separated_locus_nondegenerate {N : ℕ} (hN : 4 ≤ N) (hE : Even N)
  {T : Finset ℕ} (hT : PionCompleteness.Pi.IsSameParitySet N T) :
  PionCompleteness.Paper.NLSM.Zeros.IsRegularSet N (PionCompleteness.Pi.sepPairs N T)
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.Families.t_separated_locus_nondegenerate

/--
info: PionCompleteness.Paper.t_separated_zero_pointwise {N : ℕ} (hN : 4 ≤ N) (hE : Even N) {T : Finset ℕ}
  (hT : PionCompleteness.Pi.IsSameParitySet N T) : PionCompleteness.Pi.NLSMZeroOn N (PionCompleteness.Pi.sepPairs N T)
-/
#guard_msgs in
#check PionCompleteness.Paper.t_separated_zero_pointwise

/--
info: PionCompleteness.Paper.NLSM.Zeros.Families.t_separated_zero {N : ℕ} (hN : 4 ≤ N) (hE : Even N) {T : Finset ℕ}
  (hT : PionCompleteness.Pi.IsSameParitySet N T) :
  PionCompleteness.Paper.NLSM.Zeros.IsCoordinateZero N (PionCompleteness.Pi.sepPairs N T)
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.Families.t_separated_zero

/--
info: PionCompleteness.Paper.NLSM.FeynmanRules.diagrams_vanish_on_t_separated_locus {N r : ℕ} (hN : 4 ≤ N) (hE : Even N)
  (hr : r < 2) {T : Finset ℕ} (hT : PionCompleteness.PionZeros.Admissible N r T) :
  (∀ G ∈ PionCompleteness.PionZeros.quadrangulations N,
      PionCompleteness.PionNLSM.RatZeroOn
        {x | PionCompleteness.ChainSlice.OnLocus N (PionCompleteness.Pi.sepPairs N T) x}
        (PionCompleteness.PionZeros.diagram N (1 - r) PionCompleteness.PionNLSM.gen G)) ∧
    PionCompleteness.PionNLSM.RatZeroOn {x | PionCompleteness.ChainSlice.OnLocus N (PionCompleteness.Pi.sepPairs N T) x}
      (PionCompleteness.PionZeros.Qpi N (1 - r) PionCompleteness.PionNLSM.gen)
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.FeynmanRules.diagrams_vanish_on_t_separated_locus

/--
info: PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.three_row_zeros {N : ℕ} (hN : 6 ≤ N) (hE : Even N) (α : ℕ × ℕ → ℚ) :
  ((∀ (X : ℕ × ℕ → ℚ),
        PionCompleteness.TreeRectangleZero.OnRect N 1 1 X ∨
            PionCompleteness.TreeRectangleZero.OnRect N 1 3 X ∨ PionCompleteness.TreeRectangleZero.OnRect N 1 5 X →
          ∑ d ∈ PionCompleteness.TreeRectangleZero.diagonals N, α d * X d = 0) →
      ∀ d ∈ PionCompleteness.TreeRectangleZero.diagonals N, α d = 0) ∧
    ((∀ (X : ℕ × ℕ → ℚ),
        PionCompleteness.TreeRectangleZero.OnRect N 1 2 X ∨
            PionCompleteness.TreeRectangleZero.OnRect N 1 4 X ∨ PionCompleteness.TreeRectangleZero.OnRect N 1 6 X →
          ∑ d ∈ PionCompleteness.TreeRectangleZero.diagonals N, α d * X d = 0) →
      ∀ d ∈ PionCompleteness.TreeRectangleZero.diagonals N, α d = 0)
-/
#guard_msgs in
#check PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.three_row_zeros

/--
info: PionCompleteness.Paper.NLSM.FeynmanRules.pkG_V_eq_faceVertex {N : ℕ} (hN : 4 ≤ N) (hE : Even N) {D : Finset (ℕ × ℕ)}
  (hD : D ∈ PionCompleteness.Pi.pkGDis N) {r : ℕ × ℕ} (hr : r ∈ PionCompleteness.Pi.pkGRoots N D) (X : ℕ × ℕ → ℚ) :
  PionCompleteness.Pi.pkGV N X D r =
    PionCompleteness.Paper.NLSM.FeynmanRules.faceVertex N X (PionCompleteness.Pi.pkGVerts D r)
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.FeynmanRules.pkG_V_eq_faceVertex

/--
info: PionCompleteness.Paper.NLSM.FeynmanRules.cayley_form {N : ℕ} (hN : 4 ≤ N) (hE : Even N) :
  PionCompleteness.PionNLSM.NLSM N PionCompleteness.PionNLSM.gen =
    -PionCompleteness.Paper.NLSM.FeynmanRules.cayleySum N PionCompleteness.PionNLSM.gen
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.FeynmanRules.cayley_form

/--
info: PionCompleteness.Paper.Combinatorics.Polygons.dissection_face_count {N : ℕ} (hN : 4 ≤ N) (hE : Even N)
  (S : Finset (ℕ × ℕ)) {D : Finset (ℕ × ℕ)} (hD : D ∈ PionCompleteness.Pi.pkGDis N)
  (hDP : ¬D ⊆ PionCompleteness.Pi.cleanChords N S) :
  (D ∩ PionCompleteness.Pi.cleanChords N S).card + 2 ≤
    {F ∈ PionCompleteness.Paper.Combinatorics.Polygons.faces N D |
        (PionCompleteness.Paper.Combinatorics.Polygons.chordSides D F \ PionCompleteness.Pi.cleanChords N S).card ≤
          1}.card
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.dissection_face_count

/--
info: PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.on_shell_dissection_has_vanishing_face {N : ℕ} (hN : 4 ≤ N)
  (hE : Even N) {S D : Finset (ℕ × ℕ)} (hD : D ∈ PionCompleteness.Pi.pkGDis N)
  (hsub : D ⊆ PionCompleteness.Pi.cleanChords N S) (hne : D.Nonempty) :
  (∀ P ∈ D,
      PionCompleteness.Pi.innerOO N S P = ∅ ∨ PionCompleteness.Pi.innerEE N S P = ∅ →
        ∃ F ∈ PionCompleteness.Paper.Combinatorics.Polygons.faces N D,
          ∀ (X : ℕ × ℕ → ℚ),
            PionCompleteness.ChainSlice.OnLocus N S X → PionCompleteness.Paper.NLSM.FeynmanRules.faceVertex N X F = 0) ∧
    (PionCompleteness.Pi.poleChords N S = ∅ →
      ∃ F ∈ PionCompleteness.Paper.Combinatorics.Polygons.faces N D,
        ∀ (X : ℕ × ℕ → ℚ),
          PionCompleteness.ChainSlice.OnLocus N S X → PionCompleteness.Paper.NLSM.FeynmanRules.faceVertex N X F = 0)
-/
#guard_msgs in
#check PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.on_shell_dissection_has_vanishing_face

/--
info: PionCompleteness.Paper.NLSM.Amplitude.nonvanishing_without_residue_chords {N : ℕ} (hN : 4 ≤ N) (hE : Even N)
  {S : Finset (ℕ × ℕ)} (hF : PionCompleteness.Paper.NLSM.Zeros.IsCandidateSet N S)
  (hP1 : PionCompleteness.Pi.poleChords N S = ∅) : PionCompleteness.Pi.NonzeroOn N S
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.nonvanishing_without_residue_chords

/--
info: PionCompleteness.Paper.Combinatorics.Polygons.innermost_chord_exists {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
  {S : Finset (ℕ × ℕ)} (hP : (PionCompleteness.Pi.poleChords N S).Nonempty) :
  (PionCompleteness.Pi.goodTail N S).Nonempty ∧ ∃ P, PionCompleteness.Pi.IsInnermostChord N S P
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.innermost_chord_exists

/--
info: PionCompleteness.Paper.Combinatorics.Polygons.separators_avoid_linked_side {N : ℕ} (hE : Even N) {S : Finset (ℕ × ℕ)}
  {P Q : ℕ × ℕ} (hP : P ∈ PionCompleteness.PionZeros.oddDiagonals N)
  (hlinked : PionCompleteness.Pi.NoFreeSep N S (PionCompleteness.Pi.tailStart P) (PionCompleteness.Pi.tailLen N P) 1)
  (hQ : Q ∈ PionCompleteness.PionZeros.oddDiagonals N)
  (hsub : PionCompleteness.Pi.oddSide N Q ⊆ PionCompleteness.Pi.oddSide N P) {τ : Finset ℕ}
  (hτ : τ ∈ PionCompleteness.Pi.admSeps N (PionCompleteness.Pi.tailStart Q) (PionCompleteness.Pi.tailLen N Q) 1)
  (hfree :
    Disjoint (PionCompleteness.Pi.sepIn N (PionCompleteness.Pi.tailStart Q) (PionCompleteness.Pi.tailLen N Q) τ)
      (PionCompleteness.Pi.missing N S)) :
  Disjoint τ (PionCompleteness.Pi.intArc N (PionCompleteness.Pi.tailStart P) (PionCompleteness.Pi.tailLen N P)) ∧
    ((∀ t ∈ τ, t % 2 = 1) → Disjoint τ (PionCompleteness.Pi.evenSide N P))
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.separators_avoid_linked_side

/--
info: PionCompleteness.Paper.Combinatorics.Polygons.innermost_class_has_linked_member {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
  {S : Finset (ℕ × ℕ)} (hF : PionCompleteness.Paper.NLSM.Zeros.IsCandidateSet N S) {P : ℕ × ℕ}
  (hP : PionCompleteness.Pi.IsInnermostChord N S P) :
  ∃ b ∈ PionCompleteness.Pi.hitClass N S P,
    PionCompleteness.Pi.NoFreeSep N S (PionCompleteness.Pi.headStart b) (PionCompleteness.Pi.headLen N b) 0
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.innermost_class_has_linked_member
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.both_sides_linked_alone_in_flank_class {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
  {S : Finset (ℕ × ℕ)} :
  (∀ P ∈ PionCompleteness.Pi.poleChords N S,
      PionCompleteness.Pi.NoFreeSep N S (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P) 0 →
        PionCompleteness.Pi.NoFreeSep N S (PionCompleteness.Pi.tailStart P) (PionCompleteness.Pi.tailLen N P) 1 →
          PionCompleteness.Pi.hitClass N S P = {P}) ∧
    (PionCompleteness.Paper.NLSM.Zeros.IsCandidateSet N S →
      ∀ (P : ℕ × ℕ),
        PionCompleteness.Pi.IsInnermostChord N S P →
          (PionCompleteness.Pi.NoFreeSep N S (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P) 0 ↔
            PionCompleteness.Pi.hitClass N S P = {P}))
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.both_sides_linked_alone_in_flank_class

/--
info: PionCompleteness.Paper.NLSM.Zeros.minimality_from_containment {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
  (clause1 :
    ∀ (S : Finset (ℕ × ℕ)),
      PionCompleteness.Paper.NLSM.Zeros.IsRegularCoordinateZero N S →
        ∃ Z, PionCompleteness.Paper.NLSM.Zeros.Families.IsListMember N Z ∧ Z ⊆ S)
  {Z : Finset (ℕ × ℕ)} (hZ : PionCompleteness.Paper.NLSM.Zeros.Families.IsListMember N Z) :
  PionCompleteness.Paper.NLSM.Zeros.IsMinimalCoordinateZero N Z
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.minimality_from_containment

-- `Paper`, continued: the analytic inputs, candidate sets as transversals, the block sums, the
-- parity form, top and bottom, the skinny rectangles, the lemmas of the `T`-separated zeros and of
-- the quartic rules, and the bridge from rational functions to numerators.
/--
info: PionCompleteness.Paper.eval_zeroAt (C : ℕ × ℕ) (x : ℕ × ℕ → ℚ) (P : MvPolynomial (ℕ × ℕ) ℚ) :
  (MvPolynomial.eval x) ((PionCompleteness.PionNLSM.zeroAt ℚ C) P) =
    (MvPolynomial.eval fun d => if d = C then 0 else x d) P
-/
#guard_msgs in
#check PionCompleteness.Paper.eval_zeroAt
/--
info: PionCompleteness.Paper.zeroAt_zeroAt (C : ℕ × ℕ) (P : MvPolynomial (ℕ × ℕ) ℚ) :
  (PionCompleteness.PionNLSM.zeroAt ℚ C) ((PionCompleteness.PionNLSM.zeroAt ℚ C) P) =
    (PionCompleteness.PionNLSM.zeroAt ℚ C) P
-/
#guard_msgs in
#check PionCompleteness.Paper.zeroAt_zeroAt
/--
info: PionCompleteness.Paper.ratZeroOn_hyperplane_iff_zeroAt {C : ℕ × ℕ} {F : PionCompleteness.PionNLSM.RF}
  {P Q : MvPolynomial (ℕ × ℕ) ℚ}
  (hF :
    F * (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) Q =
      (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) P)
  (hQ : (PionCompleteness.PionNLSM.zeroAt ℚ C) Q ≠ 0) :
  PionCompleteness.PionNLSM.RatZeroOn {x | x C = 0} F ↔ (PionCompleteness.PionNLSM.zeroAt ℚ C) P = 0
-/
#guard_msgs in
#check PionCompleteness.Paper.ratZeroOn_hyperplane_iff_zeroAt
/--
info: PionCompleteness.Paper.ratZeroOn_mul_left {V : Set (ℕ × ℕ → ℚ)} {F : PionCompleteness.PionNLSM.RF}
  (h : PionCompleteness.PionNLSM.RatZeroOn V F) (u : MvPolynomial (ℕ × ℕ) ℚ) :
  PionCompleteness.PionNLSM.RatZeroOn V ((algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) u * F)
-/
#guard_msgs in
#check PionCompleteness.Paper.ratZeroOn_mul_left
/--
info: PionCompleteness.Paper.ringHom_eq_eval_map.{u_1} {K : Type u_1} [CommRing K] (f : MvPolynomial (ℕ × ℕ) ℚ →+* K)
  (p : MvPolynomial (ℕ × ℕ) ℚ) :
  f p = (MvPolynomial.eval fun d => f (MvPolynomial.X d)) ((MvPolynomial.map (f.comp MvPolynomial.C)) p)
-/
#guard_msgs in
#check PionCompleteness.Paper.ringHom_eq_eval_map
/--
info: PionCompleteness.Paper.shiftCoeff_numerator_hom.{u_1} {K : Type u_1} [Field K] (f : MvPolynomial (ℕ × ℕ) ℚ →+* K)
  (N m : ℕ) (hX : ∀ d ∈ PionCompleteness.PionZeros.oddDiagonals N, f (MvPolynomial.X d) ≠ 0) :
  f (PionCompleteness.PionNLSM.AP ℚ N m) =
    (PionCompleteness.PionNLSM.shiftCoeff N ↑m fun d => f (MvPolynomial.X d)) * f (PionCompleteness.PionNLSM.oddDen ℚ N)
-/
#guard_msgs in
#check PionCompleteness.Paper.shiftCoeff_numerator_hom
/--
info: PionCompleteness.Paper.nlsm_numerator_hom.{u_1} {K : Type u_1} [Field K] (f : MvPolynomial (ℕ × ℕ) ℚ →+* K) {N : ℕ}
  (hN : 2 ≤ N) (hX : ∀ d ∈ PionCompleteness.PionZeros.oddDiagonals N, f (MvPolynomial.X d) ≠ 0) :
  f (PionCompleteness.PionNLSM.NP ℚ N) =
    (PionCompleteness.PionNLSM.NLSM N fun d => f (MvPolynomial.X d)) * f (PionCompleteness.PionNLSM.oddDen ℚ N)
-/
#guard_msgs in
#check PionCompleteness.Paper.nlsm_numerator_hom
/--
info: PionCompleteness.Paper.eval_mul_of_isHomogeneous.{u_1, u_2} {R : Type u_1} {σ : Type u_2} [CommRing R]
  {P : MvPolynomial σ R} {m : ℕ} (h : P.IsHomogeneous m) (c : R) (x : σ → R) :
  (MvPolynomial.eval fun i => c * x i) P = c ^ m * (MvPolynomial.eval x) P
-/
#guard_msgs in
#check PionCompleteness.Paper.eval_mul_of_isHomogeneous
/--
info: PionCompleteness.Paper.homogeneous_of_numerator.{u_1} {K : Type u_1} [Field K] {N : ℕ} {Num : MvPolynomial (ℕ × ℕ) K}
  (hNum : Num.IsHomogeneous ((PionCompleteness.PionZeros.oddDiagonals N).card + 1)) {F : (ℕ × ℕ → K) → K}
  (hF :
    ∀ (Y : ℕ × ℕ → K),
      (∀ d ∈ PionCompleteness.PionZeros.oddDiagonals N, Y d ≠ 0) →
        (MvPolynomial.eval Y) Num = F Y * ∏ d ∈ PionCompleteness.PionZeros.oddDiagonals N, Y d)
  {c : K} (hc : c ≠ 0) {X : ℕ × ℕ → K} (hX : ∀ d ∈ PionCompleteness.PionZeros.oddDiagonals N, X d ≠ 0) :
  (F fun d => c * X d) = c * F X
-/
#guard_msgs in
#check PionCompleteness.Paper.homogeneous_of_numerator
/--
info: PionCompleteness.Paper.prod_oddDiagonals_erase {N : ℕ} (hE : Even N) {C : ℕ × ℕ}
  (hC : C ∈ PionCompleteness.PionZeros.oddDiagonals N) :
  ∏ d ∈ (PionCompleteness.PionZeros.oddDiagonals N).erase C, MvPolynomial.X d =
    PionCompleteness.PionNLSM.crossProd ℚ N C *
        (MvPolynomial.rename (PionCompleteness.PionNLSM.relab N C.1))
          (PionCompleteness.PionNLSM.oddDen ℚ (C.2 - C.1 + 1)) *
      (MvPolynomial.rename (PionCompleteness.PionNLSM.relab N C.2))
        (PionCompleteness.PionNLSM.oddDen ℚ (N - C.2 + C.1 + 1))
-/
#guard_msgs in
#check PionCompleteness.Paper.prod_oddDiagonals_erase
/--
info: PionCompleteness.Paper.zeroAt_prod_erase_ne_zero (N : ℕ) (C : ℕ × ℕ) :
  (PionCompleteness.PionNLSM.zeroAt ℚ C) (∏ d ∈ (PionCompleteness.PionZeros.oddDiagonals N).erase C, MvPolynomial.X d) ≠
    0
-/
#guard_msgs in
#check PionCompleteness.Paper.zeroAt_prod_erase_ne_zero
/--
info: PionCompleteness.Paper.ratZeroOn_of_sub_zeroAt {N : ℕ} {C : ℕ × ℕ} {F : PionCompleteness.PionNLSM.RF}
  {Num : MvPolynomial (ℕ × ℕ) ℚ}
  (hF :
    F *
        (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF)
          (∏ d ∈ (PionCompleteness.PionZeros.oddDiagonals N).erase C, MvPolynomial.X d) =
      (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF)
        (Num - (PionCompleteness.PionNLSM.zeroAt ℚ C) Num)) :
  PionCompleteness.PionNLSM.RatZeroOn {x | x C = 0} F
-/
#guard_msgs in
#check PionCompleteness.Paper.ratZeroOn_of_sub_zeroAt
/--
info: PionCompleteness.Paper.NLSM.Amplitude.analytic_facts_delta_order.{u_1} {N : ℕ} (hN : 4 ≤ N) (hE : Even N) :
  (∀ j < ↑N - 2, PionCompleteness.PionNLSM.shiftCoeff N j PionCompleteness.PionNLSM.gen = 0) ∧
    (∀ (K : Type u_1) [inst : Field K] (c : K) (X : ℕ × ℕ → K),
        c ≠ 0 →
          (∀ d ∈ PionCompleteness.PionZeros.oddDiagonals N, X d ≠ 0) →
            (PionCompleteness.PionNLSM.NLSM N fun d => c * X d) = c * PionCompleteness.PionNLSM.NLSM N X) ∧
      ∃ P,
        PionCompleteness.PionNLSM.NLSM N PionCompleteness.PionNLSM.gen *
            ∏ d ∈ PionCompleteness.PionZeros.oddDiagonals N, PionCompleteness.PionNLSM.gen d =
          (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) P
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.analytic_facts_delta_order
/--
info: PionCompleteness.Paper.NLSM.Amplitude.analytic_facts_factorisation {N : ℕ} (hN : 4 ≤ N) (hE : Even N) {C : ℕ × ℕ}
  (hC : C ∈ PionCompleteness.PionZeros.oddDiagonals N) :
  PionCompleteness.PionNLSM.RatZeroOn {x | x C = 0}
    (PionCompleteness.PionNLSM.gen C * PionCompleteness.PionNLSM.NLSM N PionCompleteness.PionNLSM.gen -
      (PionCompleteness.PionNLSM.NLSM (C.2 - C.1 + 1) fun d =>
          PionCompleteness.PionNLSM.gen (PionCompleteness.PionNLSM.relab N C.1 d)) *
        PionCompleteness.PionNLSM.NLSM (N - C.2 + C.1 + 1) fun d =>
          PionCompleteness.PionNLSM.gen (PionCompleteness.PionNLSM.relab N C.2 d))
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.analytic_facts_factorisation
/--
info: PionCompleteness.Paper.NLSM.Amplitude.analytic_facts_symmetry.{u_1} {K : Type u_1} [Field K] {N : ℕ} (hN : 4 ≤ N)
  (hE : Even N) (X : ℕ × ℕ → K) (k : ℕ) :
  PionCompleteness.PionNLSM.NLSM N (X ∘ (PionCompleteness.TreeRectangleZero.rot N)^[k]) =
    PionCompleteness.PionNLSM.NLSM N X
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.analytic_facts_symmetry
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.quadrangulation_has_good_quad {N r : ℕ} (hN : 4 ≤ N) (hE : Even N)
  (hr : r < 2) {T : Finset ℕ} (hT : PionCompleteness.PionZeros.Admissible N r T) {G : Finset (ℕ × ℕ)}
  (hG : G ∈ PionCompleteness.PionZeros.quadrangulations N) :
  ∃ q ∈ PionCompleteness.PionZeros.quads N G, PionCompleteness.PionZeros.GoodQ N T (1 - r) q
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.quadrangulation_has_good_quad
/--
info: PionCompleteness.Paper.NLSM.FeynmanRules.good_vertex_factor_vanishes {N r : ℕ} (hN : 4 ≤ N) (hE : Even N) (hr : r < 2)
  {T : Finset ℕ} (hT : PionCompleteness.PionZeros.Admissible N r T) {G : Finset (ℕ × ℕ)}
  (hG : G ∈ PionCompleteness.PionZeros.quadrangulations N) {q : PionCompleteness.PionZeros.Quad}
  (hq : q ∈ PionCompleteness.PionZeros.quads N G) (hg : PionCompleteness.PionZeros.GoodQ N T (1 - r) q) :
  (∀
      a ∈
        PionCompleteness.PionZeros.blk (PionCompleteness.PionZeros.plusPair N (1 - r) q).1.1
          (PionCompleteness.PionZeros.plusPair N (1 - r) q).1.2,
      ∀
        b ∈
          PionCompleteness.PionZeros.blk (PionCompleteness.PionZeros.plusPair N (1 - r) q).2.1
            (PionCompleteness.PionZeros.plusPair N (1 - r) q).2.2,
        PionCompleteness.PionZeros.npair N a b ∈ PionCompleteness.Pi.sepPairs N T) ∧
    ∀ (X : ℕ × ℕ → ℚ),
      PionCompleteness.ChainSlice.OnLocus N (PionCompleteness.Pi.sepPairs N T) X →
        PionCompleteness.PionZeros.vnum N (1 - r) X q = 0
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.FeynmanRules.good_vertex_factor_vanishes
/--
info: PionCompleteness.Paper.quartic_residue {N π : ℕ} (hN : 4 ≤ N) (hE : Even N) (hπ : π < 2) {C : ℕ × ℕ}
  (hC : C ∈ PionCompleteness.PionZeros.oddDiagonals N) :
  PionCompleteness.PionNLSM.RatZeroOn {x | x C = 0}
    (PionCompleteness.PionNLSM.gen C * PionCompleteness.PionZeros.Qpi N π PionCompleteness.PionNLSM.gen -
      (PionCompleteness.PionZeros.Qpi (C.2 - C.1 + 1) ((π + C.1 + 1) % 2) fun d =>
          PionCompleteness.PionNLSM.gen (PionCompleteness.PionNLSM.relab N C.1 d)) *
        PionCompleteness.PionZeros.Qpi (N - C.2 + C.1 + 1) ((π + C.2 + 1) % 2) fun d =>
          PionCompleteness.PionNLSM.gen (PionCompleteness.PionNLSM.relab N C.2 d))
-/
#guard_msgs in
#check PionCompleteness.Paper.quartic_residue
/--
info: PionCompleteness.Paper.NLSM.FeynmanRules.quartic_diagram_sum_structure.{u_1} {N π : ℕ} (hN : 4 ≤ N) (hE : Even N)
  (hπ : π < 2) :
  ((∀ (K : Type u_1) [inst : Field K] (c : K) (X : ℕ × ℕ → K),
        c ≠ 0 →
          (∀ d ∈ PionCompleteness.PionZeros.oddDiagonals N, X d ≠ 0) →
            (PionCompleteness.PionZeros.Qpi N π fun d => c * X d) = c * PionCompleteness.PionZeros.Qpi N π X) ∧
      (∃ P,
          PionCompleteness.PionZeros.Qpi N π PionCompleteness.PionNLSM.gen *
              ∏ d ∈ PionCompleteness.PionZeros.oddDiagonals N, PionCompleteness.PionNLSM.gen d =
            (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) P) ∧
        ∀ G ∈ PionCompleteness.PionZeros.quadrangulations N,
          (PionCompleteness.PionZeros.quads N G).card = (N - 2) / 2 ∧
            (∀ q ∈ PionCompleteness.PionZeros.quads N G, (PionCompleteness.PionNLSM.vnumP ℚ N π q).IsHomogeneous 1) ∧
              G.card = (N - 4) / 2 ∧ G ⊆ PionCompleteness.PionZeros.oddDiagonals N) ∧
    ∀ C ∈ PionCompleteness.PionZeros.oddDiagonals N,
      PionCompleteness.PionNLSM.RatZeroOn {x | x C = 0}
        (PionCompleteness.PionNLSM.gen C * PionCompleteness.PionZeros.Qpi N π PionCompleteness.PionNLSM.gen -
          (PionCompleteness.PionZeros.Qpi (C.2 - C.1 + 1) ((π + C.1 + 1) % 2) fun d =>
              PionCompleteness.PionNLSM.gen (PionCompleteness.PionNLSM.relab N C.1 d)) *
            PionCompleteness.PionZeros.Qpi (N - C.2 + C.1 + 1) ((π + C.2 + 1) % 2) fun d =>
              PionCompleteness.PionNLSM.gen (PionCompleteness.PionNLSM.relab N C.2 d))
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.FeynmanRules.quartic_diagram_sum_structure
/--
info: PionCompleteness.Paper.NLSM.Zeros.single_leg_locus {n a : ℕ} (hn : 4 ≤ n) (ha : a ∈ Finset.Icc 1 n) :
  PionCompleteness.PionNLSM.RatZeroOn {x | PionCompleteness.TreeRectangleZero.OnRect n 1 a x}
      (PionCompleteness.TreeRectangleZero.amp n PionCompleteness.PionNLSM.gen) ∧
    (Even n →
      (∀ (m : ℤ),
          PionCompleteness.PionNLSM.RatZeroOn {x | PionCompleteness.TreeRectangleZero.OnRect n 1 a x}
            (PionCompleteness.PionNLSM.shiftCoeff n m PionCompleteness.PionNLSM.gen)) ∧
        PionCompleteness.PionNLSM.RatZeroOn {x | PionCompleteness.TreeRectangleZero.OnRect n 1 a x}
          (PionCompleteness.PionNLSM.NLSM n PionCompleteness.PionNLSM.gen))
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.single_leg_locus
/--
info: PionCompleteness.Paper.NLSM.Amplitude.delta_order_factorisation_single_leg_vanishing {N : ℕ} (hN : 4 ≤ N)
  (hE : Even N) :
  (∀ j < ↑N - 2, PionCompleteness.PionNLSM.shiftCoeff N j PionCompleteness.PionNLSM.gen = 0) ∧
    (∀ C ∈ PionCompleteness.PionZeros.oddDiagonals N,
        PionCompleteness.PionNLSM.RatZeroOn {x | x C = 0}
          (PionCompleteness.PionNLSM.gen C * PionCompleteness.PionNLSM.NLSM N PionCompleteness.PionNLSM.gen -
            (PionCompleteness.PionNLSM.NLSM (C.2 - C.1 + 1) fun d =>
                PionCompleteness.PionNLSM.gen (PionCompleteness.PionNLSM.relab N C.1 d)) *
              PionCompleteness.PionNLSM.NLSM (N - C.2 + C.1 + 1) fun d =>
                PionCompleteness.PionNLSM.gen (PionCompleteness.PionNLSM.relab N C.2 d))) ∧
      ∀ i ∈ Finset.Icc 1 N,
        PionCompleteness.PionNLSM.RatZeroOn {x | PionCompleteness.TreeRectangleZero.OnRect N 1 i x}
          (PionCompleteness.PionNLSM.NLSM N PionCompleteness.PionNLSM.gen)
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.delta_order_factorisation_single_leg_vanishing
/--
info: PionCompleteness.Paper.Algebra.RationalFunctions.pole_free_on_odd_chords_is_polynomial {N : ℕ}
  {J : PionCompleteness.PionNLSM.RF}
  (hden :
    ∃ P,
      J * (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) (PionCompleteness.PionNLSM.oddDen ℚ N) =
        (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) P)
  (hres :
    ∀ C ∈ PionCompleteness.PionZeros.oddDiagonals N,
      PionCompleteness.PionNLSM.RatZeroOn {x | x C = 0} (PionCompleteness.PionNLSM.gen C * J)) :
  ∃ P, J = (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) P
-/
#guard_msgs in
#check PionCompleteness.Paper.Algebra.RationalFunctions.pole_free_on_odd_chords_is_polynomial
/--
info: def PionCompleteness.Paper.NLSM.Zeros.IsCandidateSet : ℕ → Finset (ℕ × ℕ) → Prop :=
fun N S =>
  S ⊆ PionCompleteness.TreeRectangleZero.diagonals N ∧
    PionCompleteness.Paper.NLSM.Zeros.IsRegularSet N S ∧
      ¬∃ Z, PionCompleteness.Paper.NLSM.Zeros.Families.IsListMember N Z ∧ Z ⊆ S
-/
#guard_msgs in
#print PionCompleteness.Paper.NLSM.Zeros.IsCandidateSet
/--
info: PionCompleteness.Paper.NLSM.Zeros.isCandidateSet_iff_inFpi {N : ℕ} (hE : Even N) {S : Finset (ℕ × ℕ)} :
  PionCompleteness.Paper.NLSM.Zeros.IsCandidateSet N S ↔ PionCompleteness.Pi.InFpi N S
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.isCandidateSet_iff_inFpi
/--
info: PionCompleteness.Paper.NLSM.Zeros.Families.candidate_sets_are_transversals {N : ℕ} (hN : 4 ≤ N) (hE : Even N) :
  (∀ S ⊆ PionCompleteness.TreeRectangleZero.diagonals N,
      PionCompleteness.Paper.NLSM.Zeros.IsCandidateSet N S ↔
        ∀ (Z : Finset (ℕ × ℕ)),
          PionCompleteness.Paper.NLSM.Zeros.Families.IsListMember N Z →
            (Z ∩ PionCompleteness.Pi.missing N S).Nonempty) ∧
    (∀ S ⊆ PionCompleteness.TreeRectangleZero.diagonals N,
        (¬∃ Z, PionCompleteness.Paper.NLSM.Zeros.Families.IsListMember N Z ∧ Z ⊆ S) →
          PionCompleteness.Paper.NLSM.Zeros.IsRegularSet N S) ∧
      ∀ (S S' : Finset (ℕ × ℕ)),
        PionCompleteness.Paper.NLSM.Zeros.IsCandidateSet N S →
          S' ⊆ S → PionCompleteness.Paper.NLSM.Zeros.IsCandidateSet N S'
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.Families.candidate_sets_are_transversals
/--
info: PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.block_sums {N : ℕ} (hN : 4 ≤ N) (hE : Even N) (X : ℕ × ℕ → ℚ) :
  (∀ a ∈ Finset.Icc 1 N,
      -PionCompleteness.TreeRectangleZero.mesh N X a (a + 1) =
        PionCompleteness.TreeRectangleZero.planar N X a (a + 2)) ∧
    (∀ (i j : ℕ),
        (i, j) ∈ PionCompleteness.TreeRectangleZero.diagonals N →
          X (i, j) = PionCompleteness.Pi.pkGQ N X (Finset.Icc i (j - 1))) ∧
      (∀ a ∈ Finset.Icc 1 N, ∑ b ∈ (Finset.Icc 1 N).erase a, -PionCompleteness.TreeRectangleZero.mesh N X a b = 0) ∧
        ((∀ U ⊆ Finset.Icc 1 N, PionCompleteness.Pi.pkGQ N X U = PionCompleteness.Pi.pkGQ N X (Finset.Icc 1 N \ U)) ∧
            PionCompleteness.Pi.pkGQ N X (Finset.Icc 1 N) = 0) ∧
          (PionCompleteness.Pi.pkGE N X = -PionCompleteness.Pi.pkGQ N X (PionCompleteness.Pi.evens (Finset.Icc 1 N)) ∧
              PionCompleteness.Pi.pkGE N X =
                -PionCompleteness.Pi.pkGQ N X (PionCompleteness.Pi.odds (Finset.Icc 1 N))) ∧
            ∀ P ∈ PionCompleteness.PionZeros.oddDiagonals N,
              X P =
                ∑ t ∈ PionCompleteness.Pi.minRect N P, PionCompleteness.TreeRectangleZero.mesh N X t.1 t.2 +
                    (PionCompleteness.Pi.pkGE N X - PionCompleteness.Pi.pkGSee N X (PionCompleteness.Pi.evenSide N P)) -
                  PionCompleteness.Pi.pkGSoo N X (PionCompleteness.Pi.oddSide N P)
-/
#guard_msgs in
#check PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.block_sums
/--
info: PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.parity_form_nonvanishing {N : ℕ} (hN : 4 ≤ N) (hE : Even N)
  {S : Finset (ℕ × ℕ)} (hS : S ⊆ PionCompleteness.TreeRectangleZero.diagonals N) :
  ((∀ (X : ℕ × ℕ → ℚ), PionCompleteness.ChainSlice.OnLocus N S X → PionCompleteness.Pi.pkGE N X = 0) →
      (∀ t ∈ PionCompleteness.TreeRectangleZero.diagonals N, t.1 % 2 = 0 ∧ t.2 % 2 = 0 → t ∈ S) ∨
        ∀ t ∈ PionCompleteness.TreeRectangleZero.diagonals N, t.1 % 2 = 1 ∧ t.2 % 2 = 1 → t ∈ S) ∧
    (PionCompleteness.Paper.NLSM.Zeros.IsCandidateSet N S →
      ∃ X, PionCompleteness.ChainSlice.OnLocus N S X ∧ PionCompleteness.Pi.pkGE N X ≠ 0)
-/
#guard_msgs in
#check PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.parity_form_nonvanishing
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.flank_class_top_and_bottom {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
  {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ} (hP : P ∈ PionCompleteness.Pi.goodTail N S) :
  (P ∈ PionCompleteness.Pi.hitClass N S P ∧
      ∀ Q ∈ PionCompleteness.Pi.hitClass N S P, PionCompleteness.Pi.oddSide N Q ⊆ PionCompleteness.Pi.oddSide N P) ∧
    (∀ b ∈ PionCompleteness.Pi.hitClass N S P,
        PionCompleteness.Pi.NoFreeSep N S (PionCompleteness.Pi.headStart b) (PionCompleteness.Pi.headLen N b) 0 →
          (∀ Q ∈ PionCompleteness.Pi.hitClass N S P,
              PionCompleteness.Pi.oddSide N b ⊆ PionCompleteness.Pi.oddSide N Q) ∧
            ∀ b' ∈ PionCompleteness.Pi.hitClass N S P,
              (∀ Q ∈ PionCompleteness.Pi.hitClass N S P,
                  PionCompleteness.Pi.oddSide N b' ⊆ PionCompleteness.Pi.oddSide N Q) →
                b' = b) ∧
      ((∃ b ∈ PionCompleteness.Pi.hitClass N S P,
          PionCompleteness.Pi.NoFreeSep N S (PionCompleteness.Pi.headStart b) (PionCompleteness.Pi.headLen N b) 0) →
        (∃ t ∈ PionCompleteness.Pi.hitClass N S P,
            ∀ Q ∈ PionCompleteness.Pi.hitClass N S P,
              PionCompleteness.Pi.oddSide N Q ⊆ PionCompleteness.Pi.oddSide N t) ∧
          ∃ b ∈ PionCompleteness.Pi.hitClass N S P,
            ∀ Q ∈ PionCompleteness.Pi.hitClass N S P, PionCompleteness.Pi.oddSide N b ⊆ PionCompleteness.Pi.oddSide N Q)
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.flank_class_top_and_bottom

-- `Paper`, continued: momentum conservation, coordinates on a locus, the flank sets, the
-- "equivalently" of on-shell chords, odd chords on the same-parity sublocus, the members of the
-- list, the mesh map `meshMap`, and the helpers they use
-- (`mesh_add`, `mesh_smul`, `card_diagonals`, `mesh_kernel`, `sum_shiftSign_mul`,
-- `exists_mesh_combination_of_vanishing`, the membership lemmas `mem_*`, and
-- `list_member_two_same_parity_pairs_outside`).
/--
info: PionCompleteness.Paper.mesh_add {N : ℕ} (X Y : ℕ × ℕ → ℚ) (a b : ℕ) :
  PionCompleteness.TreeRectangleZero.mesh N (X + Y) a b =
    PionCompleteness.TreeRectangleZero.mesh N X a b + PionCompleteness.TreeRectangleZero.mesh N Y a b
-/
#guard_msgs in
#check PionCompleteness.Paper.mesh_add
/--
info: PionCompleteness.Paper.mesh_smul {N : ℕ} (u : ℚ) (X : ℕ × ℕ → ℚ) (a b : ℕ) :
  PionCompleteness.TreeRectangleZero.mesh N (u • X) a b = u * PionCompleteness.TreeRectangleZero.mesh N X a b
-/
#guard_msgs in
#check PionCompleteness.Paper.mesh_smul
/--
info: def PionCompleteness.Paper.meshMap : (N : ℕ) →
  (ℕ × ℕ → ℚ) →ₗ[ℚ] ↥(PionCompleteness.TreeRectangleZero.diagonals N) → ℚ :=
fun N =>
  { toFun := fun X t => PionCompleteness.TreeRectangleZero.mesh N X (↑t).1 (↑t).2, map_add' := ⋯, map_smul' := ⋯ }
-/
#guard_msgs in
#print PionCompleteness.Paper.meshMap
/--
info: PionCompleteness.Paper.card_diagonals (N : ℕ) : (PionCompleteness.TreeRectangleZero.diagonals N).card = N * (N - 3) / 2
-/
#guard_msgs in
#check PionCompleteness.Paper.card_diagonals
/--
info: PionCompleteness.Paper.mesh_kernel {N : ℕ} (hN : 4 ≤ N) {X : ℕ × ℕ → ℚ}
  (hX : ∀ t ∈ PionCompleteness.TreeRectangleZero.diagonals N, PionCompleteness.TreeRectangleZero.mesh N X t.1 t.2 = 0) :
  ∃ u, ∀ d ∈ PionCompleteness.TreeRectangleZero.diagonals N, X d = u * ↑(PionCompleteness.PionNLSM.shiftSign d)
-/
#guard_msgs in
#check PionCompleteness.Paper.mesh_kernel
/--
info: PionCompleteness.Paper.sum_shiftSign_mul {N : ℕ} (y : ℕ × ℕ → ℚ) :
  ∑ t ∈ PionCompleteness.TreeRectangleZero.diagonals N, ↑(PionCompleteness.PionNLSM.shiftSign t) * y t =
    ∑ t ∈ PionCompleteness.TreeRectangleZero.diagonals N with t.1 % 2 = 0 ∧ t.2 % 2 = 0, y t -
      ∑ t ∈ PionCompleteness.TreeRectangleZero.diagonals N with t.1 % 2 = 1 ∧ t.2 % 2 = 1, y t
-/
#guard_msgs in
#check PionCompleteness.Paper.sum_shiftSign_mul
/--
info: PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.momentum_conservation_relation {N : ℕ} (hN : 4 ≤ N) (hE : Even N) :
  (∀ (X : ℕ × ℕ → ℚ),
      ∑ t ∈ PionCompleteness.TreeRectangleZero.diagonals N with t.1 % 2 = 0 ∧ t.2 % 2 = 0,
          PionCompleteness.TreeRectangleZero.mesh N X t.1 t.2 =
        ∑ t ∈ PionCompleteness.TreeRectangleZero.diagonals N with t.1 % 2 = 1 ∧ t.2 % 2 = 1,
          PionCompleteness.TreeRectangleZero.mesh N X t.1 t.2) ∧
    (∀ (X : ℕ × ℕ → ℚ),
        (∀ t ∈ PionCompleteness.TreeRectangleZero.diagonals N,
            PionCompleteness.TreeRectangleZero.mesh N X t.1 t.2 = 0) ↔
          ∃ u,
            ∀ d ∈ PionCompleteness.TreeRectangleZero.diagonals N, X d = u * ↑(PionCompleteness.PionNLSM.shiftSign d)) ∧
      (Module.finrank ℚ ↥(PionCompleteness.Paper.meshMap N).range = N * (N - 3) / 2 - 1 ∧
          ∀ (lam : ℕ × ℕ → ℚ),
            (∀ (X : ℕ × ℕ → ℚ),
                ∑ t ∈ PionCompleteness.TreeRectangleZero.diagonals N,
                    lam t * PionCompleteness.TreeRectangleZero.mesh N X t.1 t.2 =
                  0) →
              ∃ κ,
                ∀ t ∈ PionCompleteness.TreeRectangleZero.diagonals N,
                  lam t = κ * ↑(PionCompleteness.PionNLSM.shiftSign t)) ∧
        ∀ (y : ℕ × ℕ → ℚ),
          (∃ X,
              ∀ t ∈ PionCompleteness.TreeRectangleZero.diagonals N,
                PionCompleteness.TreeRectangleZero.mesh N X t.1 t.2 = y t) ↔
            ∑ t ∈ PionCompleteness.TreeRectangleZero.diagonals N with t.1 % 2 = 0 ∧ t.2 % 2 = 0, y t =
              ∑ t ∈ PionCompleteness.TreeRectangleZero.diagonals N with t.1 % 2 = 1 ∧ t.2 % 2 = 1, y t
-/
#guard_msgs in
#check PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.momentum_conservation_relation
/--
info: PionCompleteness.Paper.exists_mesh_combination_of_vanishing {N : ℕ} {S : Finset (ℕ × ℕ)}
  (hS : S ⊆ PionCompleteness.TreeRectangleZero.diagonals N) (K : (ℕ × ℕ → ℚ) →ₗ[ℚ] ℚ)
  (hK : ∀ (X : ℕ × ℕ → ℚ), PionCompleteness.ChainSlice.OnLocus N S X → K X = 0) :
  ∃ φ, ∀ (X : ℕ × ℕ → ℚ), K X = ∑ t ∈ S, φ t * PionCompleteness.TreeRectangleZero.mesh N X t.1 t.2
-/
#guard_msgs in
#check PionCompleteness.Paper.exists_mesh_combination_of_vanishing
/--
info: PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.locus_coordinates {N : ℕ} (hN : 4 ≤ N) (hE : Even N)
  {S : Finset (ℕ × ℕ)} (hS : S ⊆ PionCompleteness.TreeRectangleZero.diagonals N) :
  (∀ (X : ℕ × ℕ → ℚ),
      PionCompleteness.ChainSlice.OnLocus N S X →
        ∑ t ∈ PionCompleteness.Pi.Mee N S, PionCompleteness.TreeRectangleZero.mesh N X t.1 t.2 =
          ∑ t ∈ PionCompleteness.Pi.Moo N S, PionCompleteness.TreeRectangleZero.mesh N X t.1 t.2) ∧
    (∀ (y : ℕ × ℕ → ℚ),
        ∑ t ∈ PionCompleteness.Pi.Mee N S, y t = ∑ t ∈ PionCompleteness.Pi.Moo N S, y t →
          ∃ X,
            PionCompleteness.ChainSlice.OnLocus N S X ∧
              ∀ t ∈ PionCompleteness.Pi.missing N S, PionCompleteness.TreeRectangleZero.mesh N X t.1 t.2 = y t) ∧
      (∀ (X : ℕ × ℕ → ℚ),
          (PionCompleteness.ChainSlice.OnLocus N S X ∧
              ∀ t ∈ PionCompleteness.Pi.missing N S, PionCompleteness.TreeRectangleZero.mesh N X t.1 t.2 = 0) ↔
            ∃ u,
              ∀ d ∈ PionCompleteness.TreeRectangleZero.diagonals N,
                X d = u * ↑(PionCompleteness.PionNLSM.shiftSign d)) ∧
        (∀ (α : ℕ × ℕ → ℚ),
            (∀ (X : ℕ × ℕ → ℚ),
                PionCompleteness.ChainSlice.OnLocus N S X →
                  ∑ d ∈ PionCompleteness.TreeRectangleZero.diagonals N, α d * X d = 0) ↔
              ∃ φ,
                ∀ (X : ℕ × ℕ → ℚ),
                  ∑ d ∈ PionCompleteness.TreeRectangleZero.diagonals N, α d * X d =
                    ∑ t ∈ S, φ t * PionCompleteness.TreeRectangleZero.mesh N X t.1 t.2) ∧
          ∀ (φ : ℕ × ℕ → ℚ),
            (∀ (X : ℕ × ℕ → ℚ),
                PionCompleteness.ChainSlice.OnLocus N S X →
                  ∑ t ∈ PionCompleteness.TreeRectangleZero.diagonals N,
                      φ t * PionCompleteness.TreeRectangleZero.mesh N X t.1 t.2 =
                    0) ↔
              ∃ κ,
                ∀ t ∈ PionCompleteness.TreeRectangleZero.diagonals N,
                  t ∉ S → φ t = κ * ↑(PionCompleteness.PionNLSM.shiftSign t)
-/
#guard_msgs in
#check PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.locus_coordinates
/--
info: PionCompleteness.Paper.mem_oddSideSplit_iff {N i j a b : ℕ} (hP : (i, j) ∈ PionCompleteness.PionZeros.oddDiagonals N) :
  (a, b) ∈ PionCompleteness.Pi.oddSideSplit N (i, j) ↔
    a < b ∧
      (a ∈ PionCompleteness.Pi.evens (PionCompleteness.Pi.oddSide N (i, j)) ∧
          b ∈ PionCompleteness.Pi.evens (PionCompleteness.Pi.oddSide N (i, j)) ∨
        a ∈ PionCompleteness.Pi.evens (PionCompleteness.Pi.oddSide N (i, j)) ∧
            b ∈ PionCompleteness.Pi.evenSide N (i, j) ∨
          a ∈ PionCompleteness.Pi.evenSide N (i, j) ∧
            b ∈ PionCompleteness.Pi.evens (PionCompleteness.Pi.oddSide N (i, j)))
-/
#guard_msgs in
#check PionCompleteness.Paper.mem_oddSideSplit_iff
/--
info: PionCompleteness.Paper.mem_evenSideSplit_iff {N i j a b : ℕ} (hE : Even N)
  (hP : (i, j) ∈ PionCompleteness.PionZeros.oddDiagonals N) :
  (a, b) ∈ PionCompleteness.Pi.evenSideSplit N (i, j) ↔
    a < b ∧
      (a ∈ PionCompleteness.Pi.odds (PionCompleteness.Pi.evenSide N (i, j)) ∧
          b ∈ PionCompleteness.Pi.odds (PionCompleteness.Pi.evenSide N (i, j)) ∨
        a ∈ PionCompleteness.Pi.odds (PionCompleteness.Pi.evenSide N (i, j)) ∧
            b ∈ PionCompleteness.Pi.oddSide N (i, j) ∨
          a ∈ PionCompleteness.Pi.oddSide N (i, j) ∧
            b ∈ PionCompleteness.Pi.odds (PionCompleteness.Pi.evenSide N (i, j)))
-/
#guard_msgs in
#check PionCompleteness.Paper.mem_evenSideSplit_iff
/--
info: PionCompleteness.Paper.mem_minRect_iff {N : ℕ} {P : ℕ × ℕ} {a b : ℕ} :
  (a, b) ∈ PionCompleteness.Pi.minRect N P ↔
    a < b ∧
      (a ∈ PionCompleteness.Pi.evens (PionCompleteness.Pi.oddSide N P) ∧
          b ∈ PionCompleteness.Pi.odds (PionCompleteness.Pi.evenSide N P) ∨
        a ∈ PionCompleteness.Pi.odds (PionCompleteness.Pi.evenSide N P) ∧
          b ∈ PionCompleteness.Pi.evens (PionCompleteness.Pi.oddSide N P))
-/
#guard_msgs in
#check PionCompleteness.Paper.mem_minRect_iff
/--
info: PionCompleteness.Paper.mem_flank_split {N i j a b : ℕ} (hE : Even N)
  (hP : (i, j) ∈ PionCompleteness.PionZeros.oddDiagonals N) :
  ((a, b) ∈ PionCompleteness.Pi.oddSideSplit N (i, j) ↔
      (a, b) ∈ PionCompleteness.Pi.minRect N (i, j) ∨
        (a, b) ∈ PionCompleteness.TreeRectangleZero.diagonals N ∧
          a % 2 = 0 ∧
            b % 2 = 0 ∧ ¬(a ∈ PionCompleteness.Pi.evenSide N (i, j) ∧ b ∈ PionCompleteness.Pi.evenSide N (i, j))) ∧
    ((a, b) ∈ PionCompleteness.Pi.evenSideSplit N (i, j) ↔
      (a, b) ∈ PionCompleteness.Pi.minRect N (i, j) ∨
        (a, b) ∈ PionCompleteness.TreeRectangleZero.diagonals N ∧
          a % 2 = 1 ∧
            b % 2 = 1 ∧ ¬(a ∈ PionCompleteness.Pi.oddSide N (i, j) ∧ b ∈ PionCompleteness.Pi.oddSide N (i, j)))
-/
#guard_msgs in
#check PionCompleteness.Paper.mem_flank_split
/--
info: PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.flank_sets_of_odd_chord {N : ℕ} (hE : Even N) {P : ℕ × ℕ}
  (hP : P ∈ PionCompleteness.PionZeros.oddDiagonals N) (S : Finset (ℕ × ℕ)) :
  (PionCompleteness.Pi.oddSideSplit N P =
        {t ∈
            PionCompleteness.Pi.evens (PionCompleteness.Pi.oddSide N P) ×ˢ
                  PionCompleteness.Pi.evens (PionCompleteness.Pi.oddSide N P) ∪
                PionCompleteness.Pi.evens (PionCompleteness.Pi.oddSide N P) ×ˢ PionCompleteness.Pi.evenSide N P ∪
              PionCompleteness.Pi.evenSide N P ×ˢ PionCompleteness.Pi.evens (PionCompleteness.Pi.oddSide N P) |
          t.1 < t.2} ∧
      PionCompleteness.Pi.oddSideSplit N P =
          PionCompleteness.Pi.minRect N P ∪
            {t ∈ PionCompleteness.TreeRectangleZero.diagonals N |
              t.1 % 2 = 0 ∧
                t.2 % 2 = 0 ∧ ¬(t.1 ∈ PionCompleteness.Pi.evenSide N P ∧ t.2 ∈ PionCompleteness.Pi.evenSide N P)} ∧
        Disjoint (PionCompleteness.Pi.minRect N P)
          ({t ∈ PionCompleteness.TreeRectangleZero.diagonals N |
            t.1 % 2 = 0 ∧
              t.2 % 2 = 0 ∧ ¬(t.1 ∈ PionCompleteness.Pi.evenSide N P ∧ t.2 ∈ PionCompleteness.Pi.evenSide N P)})) ∧
    (PionCompleteness.Pi.evenSideSplit N P =
          {t ∈
              PionCompleteness.Pi.odds (PionCompleteness.Pi.evenSide N P) ×ˢ
                    PionCompleteness.Pi.odds (PionCompleteness.Pi.evenSide N P) ∪
                  PionCompleteness.Pi.odds (PionCompleteness.Pi.evenSide N P) ×ˢ PionCompleteness.Pi.oddSide N P ∪
                PionCompleteness.Pi.oddSide N P ×ˢ PionCompleteness.Pi.odds (PionCompleteness.Pi.evenSide N P) |
            t.1 < t.2} ∧
        PionCompleteness.Pi.evenSideSplit N P =
            PionCompleteness.Pi.minRect N P ∪
              {t ∈ PionCompleteness.TreeRectangleZero.diagonals N |
                t.1 % 2 = 1 ∧
                  t.2 % 2 = 1 ∧ ¬(t.1 ∈ PionCompleteness.Pi.oddSide N P ∧ t.2 ∈ PionCompleteness.Pi.oddSide N P)} ∧
          Disjoint (PionCompleteness.Pi.minRect N P)
            ({t ∈ PionCompleteness.TreeRectangleZero.diagonals N |
              t.1 % 2 = 1 ∧
                t.2 % 2 = 1 ∧ ¬(t.1 ∈ PionCompleteness.Pi.oddSide N P ∧ t.2 ∈ PionCompleteness.Pi.oddSide N P)})) ∧
      PionCompleteness.Pi.oddSideSplit N P ∩ PionCompleteness.Pi.evenSideSplit N P = PionCompleteness.Pi.minRect N P ∧
        (∀ t ∈ PionCompleteness.Pi.oddSideSplit N P, ¬(t.1 % 2 = 1 ∧ t.2 % 2 = 1)) ∧
          (∀ t ∈ PionCompleteness.Pi.evenSideSplit N P, ¬(t.1 % 2 = 0 ∧ t.2 % 2 = 0)) ∧
            PionCompleteness.Paper.NLSM.Zeros.Families.IsListMember N (PionCompleteness.Pi.oddSideSplit N P) ∧
              PionCompleteness.Paper.NLSM.Zeros.Families.IsListMember N (PionCompleteness.Pi.evenSideSplit N P) ∧
                ((P ∈ PionCompleteness.Pi.cleanChords N S ↔
                      PionCompleteness.Pi.missing N S ∩ PionCompleteness.Pi.oddSideSplit N P ⊆
                        PionCompleteness.Pi.Mee N S) ∧
                    (P ∈ PionCompleteness.Pi.cleanChords N S ↔
                      PionCompleteness.Pi.missing N S ∩ PionCompleteness.Pi.evenSideSplit N P ⊆
                        PionCompleteness.Pi.Moo N S)) ∧
                  PionCompleteness.Pi.innerEE N S P = PionCompleteness.Pi.Mee N S \ PionCompleteness.Pi.hitSet N S P ∧
                    PionCompleteness.Pi.innerOO N S P = PionCompleteness.Pi.Moo N S \ PionCompleteness.Pi.hitSet N S P
-/
#guard_msgs in
#check PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.flank_sets_of_odd_chord
/--
info: PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.on_shell_iff_flank_sets_share_no_missing_pair {N : ℕ} (hE : Even N)
  {P : ℕ × ℕ} (hP : P ∈ PionCompleteness.PionZeros.oddDiagonals N) (S : Finset (ℕ × ℕ)) :
  P ∈ PionCompleteness.Pi.cleanChords N S ↔
    Disjoint (PionCompleteness.Pi.oddSideSplit N P ∩ PionCompleteness.Pi.evenSideSplit N P)
      (PionCompleteness.Pi.missing N S)
-/
#guard_msgs in
#check
  PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.on_shell_iff_flank_sets_share_no_missing_pair
/--
info: PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.odd_chord_vanishing_on_same_parity_sublocus {N : ℕ} (hN : 4 ≤ N)
  (hE : Even N) {S : Finset (ℕ × ℕ)} (hS : S ⊆ PionCompleteness.TreeRectangleZero.diagonals N) {P : ℕ × ℕ}
  (hP : P ∈ PionCompleteness.PionZeros.oddDiagonals N) :
  (∃ φ,
      ∀ (X : ℕ × ℕ → ℚ),
        X P - ∑ t ∈ PionCompleteness.Pi.minRect N P, PionCompleteness.TreeRectangleZero.mesh N X t.1 t.2 =
          ∑ t ∈ PionCompleteness.Pi.pkGSame N, φ t * PionCompleteness.TreeRectangleZero.mesh N X t.1 t.2) ∧
    ((∀ (X : ℕ × ℕ → ℚ), PionCompleteness.ChainSlice.OnLocus N (S ∪ PionCompleteness.Pi.pkGSame N) X → X P = 0) ↔
        PionCompleteness.Pi.minRect N P ⊆ S) ∧
      ((∀ (X : ℕ × ℕ → ℚ), PionCompleteness.ChainSlice.OnLocus N (S ∪ PionCompleteness.Pi.pkGSame N) X → X P = 0) ↔
        P ∈ PionCompleteness.Pi.cleanChords N S)
-/
#guard_msgs in
#check PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.odd_chord_vanishing_on_same_parity_sublocus
/--
info: PionCompleteness.Paper.list_member_two_same_parity_pairs_outside {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {Z : Finset (ℕ × ℕ)}
  (hZ : PionCompleteness.Paper.NLSM.Zeros.Families.IsListMember N Z) :
  ∃ p ∈ PionCompleteness.TreeRectangleZero.diagonals N,
    ∃ p' ∈ PionCompleteness.TreeRectangleZero.diagonals N,
      p ≠ p' ∧ p ∉ Z ∧ p' ∉ Z ∧ p.1 % 2 = p.2 % 2 ∧ p'.1 % 2 = p'.2 % 2
-/
#guard_msgs in
#check PionCompleteness.Paper.list_member_two_same_parity_pairs_outside
/--
info: PionCompleteness.Paper.NLSM.Zeros.Families.members_are_closed_zeros {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
  {Z : Finset (ℕ × ℕ)} (hZl : PionCompleteness.Paper.NLSM.Zeros.Families.IsListMember N Z) :
  PionCompleteness.Paper.NLSM.Zeros.IsRegularSet N Z ∧
    PionCompleteness.Paper.NLSM.Zeros.IsCoordinateZero N Z ∧
      ∀ t ∈ PionCompleteness.TreeRectangleZero.diagonals N,
        t ∉ Z → ∃ X, PionCompleteness.ChainSlice.OnLocus N Z X ∧ PionCompleteness.TreeRectangleZero.mesh N X t.1 t.2 ≠ 0
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.Families.members_are_closed_zeros
/--
info: PionCompleteness.Paper.NLSM.Zeros.child_zeros_away_from_new_leg {N : ℕ} (hE : Even N) (S : Finset (ℕ × ℕ)) {P : ℕ × ℕ}
  (hPo : P ∈ PionCompleteness.PionZeros.oddDiagonals N) :
  ((∀ T ⊆ Finset.Icc 1 (PionCompleteness.Pi.headLen N P + 1),
        PionCompleteness.Pi.headLen N P + 1 ∉ T →
          Finset.image (fun j => PionCompleteness.TreeRectangleZero.vtx N (PionCompleteness.Pi.headStart P + j - 1)) T ⊆
              PionCompleteness.Pi.oddSide N P ∧
            (PionCompleteness.Pi.IsGSet (PionCompleteness.Pi.headLen N P + 1) T ↔
                PionCompleteness.Pi.IsGSet N
                  (Finset.image
                    (fun j => PionCompleteness.TreeRectangleZero.vtx N (PionCompleteness.Pi.headStart P + j - 1)) T)) ∧
              (PionCompleteness.Pi.sepPairs (PionCompleteness.Pi.headLen N P + 1) T ⊆
                  PionCompleteness.Pi.childSetA N S P ↔
                PionCompleteness.Pi.sepPairs N
                    (Finset.image
                      (fun j => PionCompleteness.TreeRectangleZero.vtx N (PionCompleteness.Pi.headStart P + j - 1)) T) ⊆
                  S)) ∧
      ∀ G ⊆ PionCompleteness.Pi.oddSide N P,
        ∃! T,
          T ⊆ Finset.Icc 1 (PionCompleteness.Pi.headLen N P + 1) ∧
            PionCompleteness.Pi.headLen N P + 1 ∉ T ∧
              Finset.image (fun j => PionCompleteness.TreeRectangleZero.vtx N (PionCompleteness.Pi.headStart P + j - 1))
                  T =
                G) ∧
    (∀ T ⊆ Finset.Icc 1 (PionCompleteness.Pi.tailLen N P + 1),
        1 ∉ T →
          Finset.image (fun j => PionCompleteness.TreeRectangleZero.vtx N (PionCompleteness.Pi.tailStart P + j - 2)) T ⊆
              PionCompleteness.Pi.evenSide N P ∧
            (PionCompleteness.Pi.IsGSet (PionCompleteness.Pi.tailLen N P + 1) T ↔
                PionCompleteness.Pi.IsGSet N
                  (Finset.image
                    (fun j => PionCompleteness.TreeRectangleZero.vtx N (PionCompleteness.Pi.tailStart P + j - 2)) T)) ∧
              (PionCompleteness.Pi.sepPairs (PionCompleteness.Pi.tailLen N P + 1) T ⊆
                  PionCompleteness.Pi.childSetB N S P ↔
                PionCompleteness.Pi.sepPairs N
                    (Finset.image
                      (fun j => PionCompleteness.TreeRectangleZero.vtx N (PionCompleteness.Pi.tailStart P + j - 2)) T) ⊆
                  S)) ∧
      ∀ G ⊆ PionCompleteness.Pi.evenSide N P,
        ∃! T,
          T ⊆ Finset.Icc 1 (PionCompleteness.Pi.tailLen N P + 1) ∧
            1 ∉ T ∧
              Finset.image (fun j => PionCompleteness.TreeRectangleZero.vtx N (PionCompleteness.Pi.tailStart P + j - 2))
                  T =
                G
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.child_zeros_away_from_new_leg
/--
info: PionCompleteness.Paper.NLSM.Zeros.child_zeros_at_new_leg {N : ℕ} (hE : Even N) (S : Finset (ℕ × ℕ)) {P : ℕ × ℕ}
  (hPo : P ∈ PionCompleteness.PionZeros.oddDiagonals N) :
  ((∀ T ⊆ Finset.Icc 1 (PionCompleteness.Pi.headLen N P + 1),
        PionCompleteness.Pi.IsGSet (PionCompleteness.Pi.headLen N P + 1) T →
          PionCompleteness.Pi.headLen N P + 1 ∈ T →
            Finset.image (fun j => PionCompleteness.TreeRectangleZero.vtx N (PionCompleteness.Pi.headStart P + j - 1))
                  (T.erase (PionCompleteness.Pi.headLen N P + 1)) ∈
                PionCompleteness.Pi.admSeps N (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P) 0 ∧
              (PionCompleteness.Pi.sepPairs (PionCompleteness.Pi.headLen N P + 1) T ⊆
                  PionCompleteness.Pi.childSetA N S P ↔
                Disjoint
                  (PionCompleteness.Pi.sepIn N (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P)
                    (Finset.image
                      (fun j => PionCompleteness.TreeRectangleZero.vtx N (PionCompleteness.Pi.headStart P + j - 1))
                      (T.erase (PionCompleteness.Pi.headLen N P + 1))))
                  (PionCompleteness.Pi.missing N S))) ∧
      (∀ Θ ∈ PionCompleteness.Pi.admSeps N (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P) 0,
          ∃! T,
            T ⊆ Finset.Icc 1 (PionCompleteness.Pi.headLen N P + 1) ∧
              PionCompleteness.Pi.IsGSet (PionCompleteness.Pi.headLen N P + 1) T ∧
                PionCompleteness.Pi.headLen N P + 1 ∈ T ∧
                  Finset.image
                      (fun j => PionCompleteness.TreeRectangleZero.vtx N (PionCompleteness.Pi.headStart P + j - 1))
                      (T.erase (PionCompleteness.Pi.headLen N P + 1)) =
                    Θ) ∧
        (PionCompleteness.Pi.NoFreeSep N S (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P) 0 ↔
          ∀ T ⊆ Finset.Icc 1 (PionCompleteness.Pi.headLen N P + 1),
            PionCompleteness.Pi.IsGSet (PionCompleteness.Pi.headLen N P + 1) T →
              PionCompleteness.Pi.headLen N P + 1 ∈ T →
                ¬PionCompleteness.Pi.sepPairs (PionCompleteness.Pi.headLen N P + 1) T ⊆
                    PionCompleteness.Pi.childSetA N S P)) ∧
    (∀ T ⊆ Finset.Icc 1 (PionCompleteness.Pi.tailLen N P + 1),
        PionCompleteness.Pi.IsGSet (PionCompleteness.Pi.tailLen N P + 1) T →
          1 ∈ T →
            Finset.image (fun j => PionCompleteness.TreeRectangleZero.vtx N (PionCompleteness.Pi.tailStart P + j - 2))
                  (T.erase 1) ∈
                PionCompleteness.Pi.admSeps N (PionCompleteness.Pi.tailStart P) (PionCompleteness.Pi.tailLen N P) 1 ∧
              (PionCompleteness.Pi.sepPairs (PionCompleteness.Pi.tailLen N P + 1) T ⊆
                  PionCompleteness.Pi.childSetB N S P ↔
                Disjoint
                  (PionCompleteness.Pi.sepIn N (PionCompleteness.Pi.tailStart P) (PionCompleteness.Pi.tailLen N P)
                    (Finset.image
                      (fun j => PionCompleteness.TreeRectangleZero.vtx N (PionCompleteness.Pi.tailStart P + j - 2))
                      (T.erase 1)))
                  (PionCompleteness.Pi.missing N S))) ∧
      (∀ Θ ∈ PionCompleteness.Pi.admSeps N (PionCompleteness.Pi.tailStart P) (PionCompleteness.Pi.tailLen N P) 1,
          ∃! T,
            T ⊆ Finset.Icc 1 (PionCompleteness.Pi.tailLen N P + 1) ∧
              PionCompleteness.Pi.IsGSet (PionCompleteness.Pi.tailLen N P + 1) T ∧
                1 ∈ T ∧
                  Finset.image
                      (fun j => PionCompleteness.TreeRectangleZero.vtx N (PionCompleteness.Pi.tailStart P + j - 2))
                      (T.erase 1) =
                    Θ) ∧
        (PionCompleteness.Pi.NoFreeSep N S (PionCompleteness.Pi.tailStart P) (PionCompleteness.Pi.tailLen N P) 1 ↔
          ∀ T ⊆ Finset.Icc 1 (PionCompleteness.Pi.tailLen N P + 1),
            PionCompleteness.Pi.IsGSet (PionCompleteness.Pi.tailLen N P + 1) T →
              1 ∈ T →
                ¬PionCompleteness.Pi.sepPairs (PionCompleteness.Pi.tailLen N P + 1) T ⊆
                    PionCompleteness.Pi.childSetB N S P)
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.child_zeros_at_new_leg
/--
info: PionCompleteness.Paper.NLSM.Zeros.unlinked_side_child_vanishes {N : ℕ} (hE : Even N) (S : Finset (ℕ × ℕ)) {P : ℕ × ℕ}
  (hPo : P ∈ PionCompleteness.PionZeros.oddDiagonals N) :
  (¬PionCompleteness.Pi.NoFreeSep N S (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P) 0 →
      (∃ Z,
          PionCompleteness.Paper.NLSM.Zeros.Families.IsListMember (PionCompleteness.Pi.headLen N P + 1) Z ∧
            Z ⊆ PionCompleteness.Pi.childSetA N S P) ∧
        (6 ≤ PionCompleteness.Pi.headLen N P + 1 →
          ∀ (z : ℕ × ℕ → ℚ),
            PionCompleteness.ChainSlice.OnLocus (PionCompleteness.Pi.headLen N P + 1)
                (PionCompleteness.Pi.childSetA N S P) z →
              (∀ d ∈ PionCompleteness.PionZeros.oddDiagonals (PionCompleteness.Pi.headLen N P + 1), z d ≠ 0) →
                PionCompleteness.PionNLSM.NLSM (PionCompleteness.Pi.headLen N P + 1) z = 0)) ∧
    (¬PionCompleteness.Pi.NoFreeSep N S (PionCompleteness.Pi.tailStart P) (PionCompleteness.Pi.tailLen N P) 1 →
      (∃ Z,
          PionCompleteness.Paper.NLSM.Zeros.Families.IsListMember (PionCompleteness.Pi.tailLen N P + 1) Z ∧
            Z ⊆ PionCompleteness.Pi.childSetB N S P) ∧
        (6 ≤ PionCompleteness.Pi.tailLen N P + 1 →
          ∀ (z : ℕ × ℕ → ℚ),
            PionCompleteness.ChainSlice.OnLocus (PionCompleteness.Pi.tailLen N P + 1)
                (PionCompleteness.Pi.childSetB N S P) z →
              (∀ d ∈ PionCompleteness.PionZeros.oddDiagonals (PionCompleteness.Pi.tailLen N P + 1), z d ≠ 0) →
                PionCompleteness.PionNLSM.NLSM (PionCompleteness.Pi.tailLen N P + 1) z = 0))
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.unlinked_side_child_vanishes

-- Library definitions that a definition of the paper is matched by, read once and pinned:
-- the missing set and its parts (`missing`, `Mee`, `Moo`), the sides of an odd chord, its flank
-- sets, `□_P` and hit set (with `odds`, `evens`), and the chord families' `e_in(P)`, `o_in(P)`,
-- `𝒫₀`, `𝒫₁` and `Same` (its same-parity sublocus is `L_{S ∪ Same}`).
/--
info: def PionCompleteness.Pi.missing : ℕ → Finset (ℕ × ℕ) → Finset (ℕ × ℕ) :=
fun N S => PionCompleteness.TreeRectangleZero.diagonals N \ S
-/
#guard_msgs in
#print PionCompleteness.Pi.missing
/--
info: def PionCompleteness.Pi.Mee : ℕ → Finset (ℕ × ℕ) → Finset (ℕ × ℕ) :=
fun N S => {p ∈ PionCompleteness.Pi.missing N S | p.1 % 2 = 0 ∧ p.2 % 2 = 0}
-/
#guard_msgs in
#print PionCompleteness.Pi.Mee
/--
info: def PionCompleteness.Pi.Moo : ℕ → Finset (ℕ × ℕ) → Finset (ℕ × ℕ) :=
fun N S => {p ∈ PionCompleteness.Pi.missing N S | p.1 % 2 = 1 ∧ p.2 % 2 = 1}
-/
#guard_msgs in
#print PionCompleteness.Pi.Moo
/--
info: def PionCompleteness.Pi.odds : Finset ℕ → Finset ℕ :=
fun L => {a ∈ L | a % 2 = 1}
-/
#guard_msgs in
#print PionCompleteness.Pi.odds
/--
info: def PionCompleteness.Pi.evens : Finset ℕ → Finset ℕ :=
fun L => {a ∈ L | a % 2 = 0}
-/
#guard_msgs in
#print PionCompleteness.Pi.evens
/--
info: def PionCompleteness.Pi.oddSide : ℕ → ℕ × ℕ → Finset ℕ :=
fun N P => if P.1 % 2 = 1 then Finset.Icc P.1 (P.2 - 1) else Finset.Icc 1 N \ Finset.Icc P.1 (P.2 - 1)
-/
#guard_msgs in
#print PionCompleteness.Pi.oddSide
/--
info: def PionCompleteness.Pi.evenSide : ℕ → ℕ × ℕ → Finset ℕ :=
fun N P => Finset.Icc 1 N \ PionCompleteness.Pi.oddSide N P
-/
#guard_msgs in
#print PionCompleteness.Pi.evenSide
/--
info: def PionCompleteness.Pi.oddSideSplit : ℕ → ℕ × ℕ → Finset (ℕ × ℕ) :=
fun N P => PionCompleteness.Pi.sepPairs N (PionCompleteness.Pi.odds (PionCompleteness.Pi.oddSide N P))
-/
#guard_msgs in
#print PionCompleteness.Pi.oddSideSplit
/--
info: def PionCompleteness.Pi.evenSideSplit : ℕ → ℕ × ℕ → Finset (ℕ × ℕ) :=
fun N P => PionCompleteness.Pi.sepPairs N (PionCompleteness.Pi.evens (PionCompleteness.Pi.evenSide N P))
-/
#guard_msgs in
#print PionCompleteness.Pi.evenSideSplit
/--
info: def PionCompleteness.Pi.minRect : ℕ → ℕ × ℕ → Finset (ℕ × ℕ) :=
fun N P =>
  Finset.image (fun q => (min q.1 q.2, max q.1 q.2))
    (PionCompleteness.Pi.evens (PionCompleteness.Pi.oddSide N P) ×ˢ
      PionCompleteness.Pi.odds (PionCompleteness.Pi.evenSide N P))
-/
#guard_msgs in
#print PionCompleteness.Pi.minRect
/--
info: def PionCompleteness.Pi.hitSet : ℕ → Finset (ℕ × ℕ) → ℕ × ℕ → Finset (ℕ × ℕ) :=
fun N S P =>
  PionCompleteness.Pi.missing N S ∩ (PionCompleteness.Pi.oddSideSplit N P ∪ PionCompleteness.Pi.evenSideSplit N P)
-/
#guard_msgs in
#print PionCompleteness.Pi.hitSet
/--
info: def PionCompleteness.Pi.innerEE : ℕ → Finset (ℕ × ℕ) → ℕ × ℕ → Finset (ℕ × ℕ) :=
fun N S P =>
  {p ∈ PionCompleteness.Pi.Mee N S | p.1 ∈ PionCompleteness.Pi.evenSide N P ∧ p.2 ∈ PionCompleteness.Pi.evenSide N P}
-/
#guard_msgs in
#print PionCompleteness.Pi.innerEE
/--
info: def PionCompleteness.Pi.innerOO : ℕ → Finset (ℕ × ℕ) → ℕ × ℕ → Finset (ℕ × ℕ) :=
fun N S P =>
  {p ∈ PionCompleteness.Pi.Moo N S | p.1 ∈ PionCompleteness.Pi.oddSide N P ∧ p.2 ∈ PionCompleteness.Pi.oddSide N P}
-/
#guard_msgs in
#print PionCompleteness.Pi.innerOO
/--
info: def PionCompleteness.Pi.cleanChords : ℕ → Finset (ℕ × ℕ) → Finset (ℕ × ℕ) :=
fun N S =>
  {P ∈ PionCompleteness.PionZeros.oddDiagonals N |
    Disjoint (PionCompleteness.Pi.minRect N P) (PionCompleteness.Pi.missing N S)}
-/
#guard_msgs in
#print PionCompleteness.Pi.cleanChords
/--
info: def PionCompleteness.Pi.poleChords : ℕ → Finset (ℕ × ℕ) → Finset (ℕ × ℕ) :=
fun N S =>
  {P ∈ PionCompleteness.Pi.cleanChords N S |
    (PionCompleteness.Pi.innerEE N S P).Nonempty ∧ (PionCompleteness.Pi.innerOO N S P).Nonempty}
-/
#guard_msgs in
#print PionCompleteness.Pi.poleChords
/--
info: def PionCompleteness.Pi.pkGSame : ℕ → Finset (ℕ × ℕ) :=
fun N => {t ∈ PionCompleteness.TreeRectangleZero.diagonals N | t.1 % 2 = t.2 % 2}
-/
#guard_msgs in
#print PionCompleteness.Pi.pkGSame

-- `Conventions`: KNT's closed forms, the controls and their negative controls.
/--
info: def PionCompleteness.Pi.kntS.{u_1} : {K : Type u_1} → [Field K] → ℕ → (ℕ × ℕ → K) → ℕ → ℕ → K :=
fun {K} [Field K] N X i j => PionCompleteness.TreeRectangleZero.planar N X i (j + 1)
-/
#guard_msgs in
#print PionCompleteness.Pi.kntS

/--
info: def PionCompleteness.Pi.kntM4.{u_1} : {K : Type u_1} → [Field K] → K → (ℕ → ℕ → K) → K :=
fun {K} [Field K] F s => (s 1 2 + s 2 3) / (2 * F ^ 2)
-/
#guard_msgs in
#print PionCompleteness.Pi.kntM4

/--
info: def PionCompleteness.Pi.kntM6.{u_1} : {K : Type u_1} → [Field K] → K → (ℕ → ℕ → K) → K :=
fun {K} [Field K] F s =>
  (-((s 1 2 + s 2 3) * (s 1 4 + s 4 5) / s 1 3) - (s 1 4 + s 2 5) * (s 2 3 + s 3 4) / s 2 4 -
        (s 1 2 + s 2 5) * (s 3 4 + s 4 5) / s 3 5 +
      (s 1 2 + s 1 4 + s 2 3 + s 2 5 + s 3 4 + s 4 5)) /
    (4 * F ^ 4)
-/
#guard_msgs in
#print PionCompleteness.Pi.kntM6

/--
info: def PionCompleteness.Pi.kntM8.{u_1} : {K : Type u_1} → [Field K] → K → (ℕ → ℕ → K) → K :=
fun {K} [Field K] F s =>
  (∑ k ∈ Finset.range 8,
      (1 / 2 *
                ((s (1 + k) (2 + k) + s (2 + k) (3 + k)) * (s (1 + k) (4 + k) + s (4 + k) (7 + k)) *
                    (s (5 + k) (6 + k) + s (6 + k) (7 + k)) /
                  (s (1 + k) (3 + k) * s (5 + k) (7 + k))) +
              (s (1 + k) (2 + k) + s (2 + k) (3 + k)) * (s (1 + k) (4 + k) + s (4 + k) (5 + k)) *
                  (s (6 + k) (7 + k) + s (7 + k) (8 + k)) /
                (s (1 + k) (3 + k) * s (6 + k) (8 + k)) -
            (s (1 + k) (2 + k) + s (2 + k) (3 + k)) *
                (s (4 + k) (5 + k) + s (4 + k) (7 + k) + s (5 + k) (6 + k) + s (5 + k) (8 + k) + s (6 + k) (7 + k) +
                  s (7 + k) (8 + k)) /
              s (1 + k) (3 + k) +
          2 * s (1 + k) (2 + k) +
        1 / 2 * s (1 + k) (4 + k))) /
    (8 * F ^ 6)
-/
#guard_msgs in
#print PionCompleteness.Pi.kntM8

/--
info: def PionCompleteness.Pi.kntConst.{u_1} : {K : Type u_1} → [Field K] → ℕ → K → K :=
fun {K} [Field K] N F => (-1) ^ (N / 2) * (2 * F ^ 2) ^ ((N - 2) / 2)
-/
#guard_msgs in
#print PionCompleteness.Pi.kntConst

/--
info: PionCompleteness.Pi.calA_four_knt.{u_1} {K : Type u_1} [Field K] [CharZero K] (F : K) (hF : F ≠ 0) (X : ℕ × ℕ → K) :
  PionCompleteness.Pi.calA 4 X =
    PionCompleteness.Pi.kntConst 4 F * PionCompleteness.Pi.kntM4 F (PionCompleteness.Pi.kntS 4 X)
-/
#guard_msgs in
#check PionCompleteness.Pi.calA_four_knt

/--
info: PionCompleteness.Pi.calA_six_knt.{u_1} {K : Type u_1} [Field K] [CharZero K] (F : K) (hF : F ≠ 0) (X : ℕ × ℕ → K) :
  PionCompleteness.Pi.calA 6 X =
    PionCompleteness.Pi.kntConst 6 F * PionCompleteness.Pi.kntM6 F (PionCompleteness.Pi.kntS 6 X)
-/
#guard_msgs in
#check PionCompleteness.Pi.calA_six_knt

/--
info: PionCompleteness.Pi.oddDiagonals_eight :
  PionCompleteness.PionZeros.oddDiagonals 8 = {(1, 4), (1, 6), (2, 5), (2, 7), (3, 6), (3, 8), (4, 7), (5, 8)}
-/
#guard_msgs in
#check PionCompleteness.Pi.oddDiagonals_eight
/--
info: PionCompleteness.Pi.calA_eight_knt.{u_1} {K : Type u_1} [Field K] [CharZero K] (F : K) (hF : F ≠ 0) (X : ℕ × ℕ → K)
  (hX : ∀ d ∈ PionCompleteness.PionZeros.oddDiagonals 8, X d ≠ 0) :
  PionCompleteness.Pi.calA 8 X =
    PionCompleteness.Pi.kntConst 8 F * PionCompleteness.Pi.kntM8 F (PionCompleteness.Pi.kntS 8 X)
-/
#guard_msgs in
#check PionCompleteness.Pi.calA_eight_knt
/--
info: PionCompleteness.Pi.nlsm_four_knt.{u_1} {K : Type u_1} [Field K] [CharZero K] (F : K) (hF : F ≠ 0) (X : ℕ × ℕ → K) :
  PionCompleteness.PionNLSM.NLSM 4 X =
    -(2 * F ^ 2) ^ ((4 - 2) / 2) * PionCompleteness.Pi.kntM4 F (PionCompleteness.Pi.kntS 4 X)
-/
#guard_msgs in
#check PionCompleteness.Pi.nlsm_four_knt
/--
info: PionCompleteness.Pi.nlsm_six_knt.{u_1} {K : Type u_1} [Field K] [CharZero K] (F : K) (hF : F ≠ 0) (X : ℕ × ℕ → K) :
  PionCompleteness.PionNLSM.NLSM 6 X =
    -(2 * F ^ 2) ^ ((6 - 2) / 2) * PionCompleteness.Pi.kntM6 F (PionCompleteness.Pi.kntS 6 X)
-/
#guard_msgs in
#check PionCompleteness.Pi.nlsm_six_knt
/--
info: PionCompleteness.Pi.nlsm_eight_knt.{u_1} {K : Type u_1} [Field K] [CharZero K] (F : K) (hF : F ≠ 0) (X : ℕ × ℕ → K)
  (hX : ∀ d ∈ PionCompleteness.PionZeros.oddDiagonals 8, X d ≠ 0) :
  PionCompleteness.PionNLSM.NLSM 8 X =
    -(2 * F ^ 2) ^ ((8 - 2) / 2) * PionCompleteness.Pi.kntM8 F (PionCompleteness.Pi.kntS 8 X)
-/
#guard_msgs in
#check PionCompleteness.Pi.nlsm_eight_knt

/--
info: PionCompleteness.Pi.negctl_knt_sign :
  PionCompleteness.Pi.calA 6 (PionCompleteness.PionZeros.hexPt 2 3 5 7 11 13 17 19 23) ≠
    (-1) ^ (6 / 2 - 1) * (2 * 1 ^ 2) ^ ((6 - 2) / 2) *
      PionCompleteness.Pi.kntM6 1 (PionCompleteness.Pi.kntS 6 (PionCompleteness.PionZeros.hexPt 2 3 5 7 11 13 17 19 23))
-/
#guard_msgs in
#check PionCompleteness.Pi.negctl_knt_sign

/--
info: PionCompleteness.Pi.negctl_knt_dictionary :
  PionCompleteness.Pi.calA 6 (PionCompleteness.PionZeros.hexPt 2 3 5 7 11 13 17 19 23) ≠
    PionCompleteness.Pi.kntConst 6 1 *
      PionCompleteness.Pi.kntM6 1
        (PionCompleteness.TreeRectangleZero.planar 6 (PionCompleteness.PionZeros.hexPt 2 3 5 7 11 13 17 19 23))
-/
#guard_msgs in
#check PionCompleteness.Pi.negctl_knt_dictionary

-- `Conventions`, continued: every N, through the Cayley form, in the paper's order (KNT's Feynman
-- sum in the Cayley parametrisation transcribed, the constant with the face count, the
-- identification, the checks of the transcription).
/--
info: def PionCompleteness.Pi.kntV.{u_1} : {K : Type u_1} → [Field K] → K → ℕ → K → K :=
fun {K} [Field K] F n q => (-1) ^ n / 2 ^ n * (1 / F) ^ (2 * n) * q
-/
#guard_msgs in
#print PionCompleteness.Pi.kntV

/--
info: def PionCompleteness.Pi.kntDot.{u_1} : {K : Type u_1} → [Field K] → (ℕ → ℕ → K) → ℕ → ℕ → K :=
fun {K} [Field K] s a b => s a b - s (a + 1) b - s a (b - 1) + s (a + 1) (b - 1)
-/
#guard_msgs in
#print PionCompleteness.Pi.kntDot

/--
info: def PionCompleteness.Pi.kntSq.{u_1} : {K : Type u_1} → [Field K] → (ℕ → ℕ → K) → Finset ℕ → K :=
fun {K} [Field K] s U => ∑ p ∈ U ×ˢ U with p.1 < p.2, PionCompleteness.Pi.kntDot s p.1 p.2
-/
#guard_msgs in
#print PionCompleteness.Pi.kntSq

/--
info: def PionCompleteness.Pi.kntFeynman.{u_1} : {K : Type u_1} → [Field K] → ℕ → (ℕ → K → K) → (K → K) → (ℕ → ℕ → K) → K :=
fun {K} [Field K] N V Δ s =>
  ∑ D ∈ PionCompleteness.Pi.pkGDis N,
    (∏ f ∈ PionCompleteness.Paper.Combinatorics.Polygons.faces N D,
        V (f.card / 2 - 1)
          (PionCompleteness.Pi.kntSq s (PionCompleteness.Paper.Combinatorics.Polygons.oddStartLegs N f))) *
      ∏ P ∈ D, Δ (s P.1 (P.2 - 1))
-/
#guard_msgs in
#print PionCompleteness.Pi.kntFeynman

/--
info: def PionCompleteness.Pi.kntCayleySum.{u_1} : {K : Type u_1} → [Field K] → ℕ → K → (ℕ → ℕ → K) → K :=
fun {K} [Field K] N F s => PionCompleteness.Pi.kntFeynman N (PionCompleteness.Pi.kntV F) (fun x => -1 / x) s
-/
#guard_msgs in
#print PionCompleteness.Pi.kntCayleySum

/--
info: PionCompleteness.Pi.kntSq_kntS.{u_1} {K : Type u_1} [Field K] (N : ℕ) (X : ℕ × ℕ → K) (U : Finset ℕ) :
  PionCompleteness.Pi.kntSq (PionCompleteness.Pi.kntS N X) U =
    ∑ p ∈ U ×ˢ U with p.1 < p.2, -PionCompleteness.TreeRectangleZero.mesh N X p.1 p.2
-/
#guard_msgs in
#check PionCompleteness.Pi.kntSq_kntS

/--
info: PionCompleteness.Pi.kntV_const.{u_1} {K : Type u_1} [Field K] [CharZero K] (F : K) (hF : F ≠ 0) (n : ℕ) (q : K) :
  (2 * F ^ 2) ^ n * PionCompleteness.Pi.kntV F n q = (-1) ^ n * q
-/
#guard_msgs in
#check PionCompleteness.Pi.kntV_const

/--
info: PionCompleteness.Pi.pkG_sum_kids {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)}
  (hD : D ∈ PionCompleteness.Pi.pkGDis N) (f : ℕ × ℕ → ℕ) :
  ∑ r ∈ PionCompleteness.Pi.pkGRoots N D, ∑ K ∈ PionCompleteness.Pi.pkGKids D r, f K = ∑ K ∈ D, f K
-/
#guard_msgs in
#check PionCompleteness.Pi.pkG_sum_kids

/--
info: PionCompleteness.Pi.pkG_card_Ico_root {N : ℕ} {D : Finset (ℕ × ℕ)} (hD : D ∈ PionCompleteness.Pi.pkGDis N) (r : ℕ × ℕ) :
  r.2 - r.1 = (PionCompleteness.Pi.pkGOwn D r).card + ∑ K ∈ PionCompleteness.Pi.pkGKids D r, (K.2 - K.1)
-/
#guard_msgs in
#check PionCompleteness.Pi.pkG_card_Ico_root

/--
info: PionCompleteness.Pi.faces_card_sum {N : ℕ} (hN : 4 ≤ N) (hE : Even N) {D : Finset (ℕ × ℕ)}
  (hD : D ∈ PionCompleteness.Pi.pkGDis N) :
  ∑ f ∈ PionCompleteness.Paper.Combinatorics.Polygons.faces N D, f.card = N + 2 * D.card
-/
#guard_msgs in
#check PionCompleteness.Pi.faces_card_sum

/--
info: PionCompleteness.Pi.faces_card_sub_two_sum {N : ℕ} (hN : 4 ≤ N) (hE : Even N) {D : Finset (ℕ × ℕ)}
  (hD : D ∈ PionCompleteness.Pi.pkGDis N) :
  ∑ f ∈ PionCompleteness.Paper.Combinatorics.Polygons.faces N D, (f.card - 2) = N - 2
-/
#guard_msgs in
#check PionCompleteness.Pi.faces_card_sub_two_sum

/--
info: PionCompleteness.Pi.faces_half_sum {N : ℕ} (hN : 4 ≤ N) (hE : Even N) {D : Finset (ℕ × ℕ)}
  (hD : D ∈ PionCompleteness.Pi.pkGDis N) :
  ∑ f ∈ PionCompleteness.Paper.Combinatorics.Polygons.faces N D, (f.card / 2 - 1) = (N - 2) / 2
-/
#guard_msgs in
#check PionCompleteness.Pi.faces_half_sum

/--
info: PionCompleteness.Pi.kntCayleySum_eq.{u_1} {K : Type u_1} [Field K] [CharZero K] {N : ℕ} (hN : 4 ≤ N) (hE : Even N)
  (F : K) (hF : F ≠ 0) (X : ℕ × ℕ → K) :
  (2 * F ^ 2) ^ ((N - 2) / 2) * PionCompleteness.Pi.kntCayleySum N F (PionCompleteness.Pi.kntS N X) =
    PionCompleteness.Paper.NLSM.FeynmanRules.cayleySum N X
-/
#guard_msgs in
#check PionCompleteness.Pi.kntCayleySum_eq

/--
info: PionCompleteness.Pi.nlsm_knt_cayley {N : ℕ} (hN : 4 ≤ N) (hE : Even N) (F : PionCompleteness.PionNLSM.RF) (hF : F ≠ 0) :
  PionCompleteness.PionNLSM.NLSM N PionCompleteness.PionNLSM.gen =
    -(2 * F ^ 2) ^ ((N - 2) / 2) *
      PionCompleteness.Pi.kntCayleySum N F (PionCompleteness.Pi.kntS N PionCompleteness.PionNLSM.gen)
-/
#guard_msgs in
#check PionCompleteness.Pi.nlsm_knt_cayley

/--
info: PionCompleteness.Pi.kntFeynman_four.{u_1} {K : Type u_1} [Field K] (V : ℕ → K → K) (Δ : K → K) (s : ℕ → ℕ → K) :
  PionCompleteness.Pi.kntFeynman 4 V Δ s = V 1 (PionCompleteness.Pi.kntSq s {1, 3})
-/
#guard_msgs in
#check PionCompleteness.Pi.kntFeynman_four

/--
info: PionCompleteness.Pi.kntFeynman_six.{u_1} {K : Type u_1} [Field K] (V : ℕ → K → K) (Δ : K → K) (s : ℕ → ℕ → K) :
  PionCompleteness.Pi.kntFeynman 6 V Δ s =
    V 2 (PionCompleteness.Pi.kntSq s {1, 3, 5}) +
          V 1 (PionCompleteness.Pi.kntSq s {1, 3}) * V 1 (PionCompleteness.Pi.kntSq s {1, 2, 3, 5}) * Δ (s 1 3) +
        V 1 (PionCompleteness.Pi.kntSq s {1, 5}) * V 1 (PionCompleteness.Pi.kntSq s {1, 3, 5, 6}) * Δ (s 2 4) +
      V 1 (PionCompleteness.Pi.kntSq s {1, 3, 4, 5}) * V 1 (PionCompleteness.Pi.kntSq s {3, 5}) * Δ (s 3 5)
-/
#guard_msgs in
#check PionCompleteness.Pi.kntFeynman_six

/--
info: PionCompleteness.Pi.kntCayleySum_four_knt.{u_1} {K : Type u_1} [Field K] (F : K) (X : ℕ × ℕ → K) :
  PionCompleteness.Pi.kntCayleySum 4 F (PionCompleteness.Pi.kntS 4 X) =
    PionCompleteness.Pi.kntM4 F (PionCompleteness.Pi.kntS 4 X)
-/
#guard_msgs in
#check PionCompleteness.Pi.kntCayleySum_four_knt

/--
info: PionCompleteness.Pi.kntCayleySum_six_knt.{u_1} {K : Type u_1} [Field K] (F : K) (X : ℕ × ℕ → K) (h14 : X (1, 4) ≠ 0)
  (h25 : X (2, 5) ≠ 0) (h36 : X (3, 6) ≠ 0) :
  PionCompleteness.Pi.kntCayleySum 6 F (PionCompleteness.Pi.kntS 6 X) =
    PionCompleteness.Pi.kntM6 F (PionCompleteness.Pi.kntS 6 X)
-/
#guard_msgs in
#check PionCompleteness.Pi.kntCayleySum_six_knt

/--
info: PionCompleteness.Pi.kntCayleySum_eight_knt (F : PionCompleteness.PionNLSM.RF) (hF : F ≠ 0) :
  PionCompleteness.Pi.kntCayleySum 8 F (PionCompleteness.Pi.kntS 8 PionCompleteness.PionNLSM.gen) =
    PionCompleteness.Pi.kntM8 F (PionCompleteness.Pi.kntS 8 PionCompleteness.PionNLSM.gen)
-/
#guard_msgs in
#check PionCompleteness.Pi.kntCayleySum_eight_knt

/--
info: PionCompleteness.Pi.negctl_knt_vertex_constant :
  PionCompleteness.Pi.kntFeynman 6 (fun n q => -(1 / 2) * PionCompleteness.Pi.kntV 1 n q) (fun x => -1 / x)
      (PionCompleteness.Pi.kntS 6 (PionCompleteness.PionZeros.hexPt 2 3 5 7 11 13 17 19 23)) ≠
    PionCompleteness.Pi.kntM6 1 (PionCompleteness.Pi.kntS 6 (PionCompleteness.PionZeros.hexPt 2 3 5 7 11 13 17 19 23))
-/
#guard_msgs in
#check PionCompleteness.Pi.negctl_knt_vertex_constant

/--
info: PionCompleteness.Pi.negctl_knt_vertex_sign :
  PionCompleteness.Pi.kntFeynman 6 (fun n q => -PionCompleteness.Pi.kntV 1 n q) (fun x => -1 / x)
      (PionCompleteness.Pi.kntS 6 (PionCompleteness.PionZeros.hexPt 2 3 5 7 11 13 17 19 23)) ≠
    PionCompleteness.Pi.kntM6 1 (PionCompleteness.Pi.kntS 6 (PionCompleteness.PionZeros.hexPt 2 3 5 7 11 13 17 19 23))
-/
#guard_msgs in
#check PionCompleteness.Pi.negctl_knt_vertex_sign

/--
info: PionCompleteness.Pi.negctl_knt_propagator_sign :
  PionCompleteness.Pi.kntFeynman 6 (PionCompleteness.Pi.kntV 1) (fun x => 1 / x)
      (PionCompleteness.Pi.kntS 6 (PionCompleteness.PionZeros.hexPt 2 3 5 7 11 13 17 19 23)) ≠
    PionCompleteness.Pi.kntM6 1 (PionCompleteness.Pi.kntS 6 (PionCompleteness.PionZeros.hexPt 2 3 5 7 11 13 17 19 23))
-/
#guard_msgs in
#check PionCompleteness.Pi.negctl_knt_propagator_sign

-- `Paper`, continued: dissections in readable form (faces as maximal sets of vertices no two of
-- which a chord separates, `U_f`, chord sides) with their equality to the library's root-side
-- faces, the claims of the definitions of sides (`odd_chord_sides`) and dissections
-- (`dissections`), the face identity, the identities of the forms, and the helpers they use.
/--
info: def PionCompleteness.Paper.Separates : ℕ × ℕ → ℕ → ℕ → Prop :=
fun P u v => (P.1 < u ∧ u < P.2) ∧ (v < P.1 ∨ P.2 < v)
-/
#guard_msgs in
#print PionCompleteness.Paper.Separates

/--
info: def PionCompleteness.Paper.Combinatorics.Polygons.IsFace : ℕ → Finset (ℕ × ℕ) → Finset ℕ → Prop :=
fun N D F =>
  F ⊆ Finset.Icc 1 N ∧
    (∀ u ∈ F, ∀ v ∈ F, ∀ P ∈ D, ¬PionCompleteness.Paper.Separates P u v) ∧
      ∀ w ∈ Finset.Icc 1 N,
        w ∉ F → ∃ u ∈ F, ∃ P ∈ D, PionCompleteness.Paper.Separates P u w ∨ PionCompleteness.Paper.Separates P w u
-/
#guard_msgs in
#print PionCompleteness.Paper.Combinatorics.Polygons.IsFace

/--
info: def PionCompleteness.Paper.Combinatorics.Polygons.faces : ℕ → Finset (ℕ × ℕ) → Finset (Finset ℕ) :=
fun N D => Finset.filter (PionCompleteness.Paper.Combinatorics.Polygons.IsFace N D) (Finset.Icc 1 N).powerset
-/
#guard_msgs in
#print PionCompleteness.Paper.Combinatorics.Polygons.faces

/--
info: def PionCompleteness.Paper.Combinatorics.Polygons.sideStart : Finset ℕ → ℕ → ℕ :=
fun F x => if {w ∈ F | w ≤ x}.Nonempty then {w ∈ F | w ≤ x}.sup fun w => w else F.sup fun w => w
-/
#guard_msgs in
#print PionCompleteness.Paper.Combinatorics.Polygons.sideStart

/--
info: def PionCompleteness.Paper.Combinatorics.Polygons.oddStartLegs : ℕ → Finset ℕ → Finset ℕ :=
fun N F => {x ∈ Finset.Icc 1 N | PionCompleteness.Paper.Combinatorics.Polygons.sideStart F x % 2 = 1}
-/
#guard_msgs in
#print PionCompleteness.Paper.Combinatorics.Polygons.oddStartLegs

/--
info: def PionCompleteness.Paper.Combinatorics.Polygons.chordSides : Finset (ℕ × ℕ) → Finset ℕ → Finset (ℕ × ℕ) :=
fun D F => {P ∈ D | P.1 ∈ F ∧ P.2 ∈ F}
-/
#guard_msgs in
#print PionCompleteness.Paper.Combinatorics.Polygons.chordSides

/--
info: def PionCompleteness.Paper.NLSM.FeynmanRules.faceVertex.{u_1} : {K : Type u_1} →
  [Field K] → ℕ → (ℕ × ℕ → K) → Finset ℕ → K :=
fun {K} [Field K] N X F =>
  (-1) ^ (F.card / 2 - 1) *
    ∑
      p ∈
        PionCompleteness.Paper.Combinatorics.Polygons.oddStartLegs N F ×ˢ
          PionCompleteness.Paper.Combinatorics.Polygons.oddStartLegs N F with
      p.1 < p.2, -PionCompleteness.TreeRectangleZero.mesh N X p.1 p.2
-/
#guard_msgs in
#print PionCompleteness.Paper.NLSM.FeynmanRules.faceVertex

/--
info: PionCompleteness.Paper.pkG_r2_vert {D : Finset (ℕ × ℕ)} {r : ℕ × ℕ} (h : r.1 ≤ r.2) :
  r.2 ∈ PionCompleteness.Pi.pkGVerts D r
-/
#guard_msgs in
#check PionCompleteness.Paper.pkG_r2_vert

/--
info: PionCompleteness.Paper.pkG_kid_vert_right {N : ℕ} {D : Finset (ℕ × ℕ)} (hD : D ∈ PionCompleteness.Pi.pkGDis N)
  {r R : ℕ × ℕ} (hR : R ∈ PionCompleteness.Pi.pkGKids D r) : R.2 ∈ PionCompleteness.Pi.pkGVerts D r
-/
#guard_msgs in
#check PionCompleteness.Paper.pkG_kid_vert_right

/--
info: PionCompleteness.Paper.pkG_verts_Icc {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)}
  (hD : D ∈ PionCompleteness.Pi.pkGDis N) {r : ℕ × ℕ} (hr : r ∈ PionCompleteness.Pi.pkGRoots N D) :
  PionCompleteness.Pi.pkGVerts D r ⊆ Finset.Icc 1 N
-/
#guard_msgs in
#check PionCompleteness.Paper.pkG_verts_Icc

/--
info: PionCompleteness.Paper.pkG_inner_vert {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)}
  (hD : D ∈ PionCompleteness.Pi.pkGDis N) {r : ℕ × ℕ} (hr : r ∈ PionCompleteness.Pi.pkGRoots N D) :
  ∃ u ∈ PionCompleteness.Pi.pkGVerts D r, r.1 < u ∧ u < r.2
-/
#guard_msgs in
#check PionCompleteness.Paper.pkG_inner_vert

/--
info: PionCompleteness.Paper.pkG_verts_not_separated {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)}
  (hD : D ∈ PionCompleteness.Pi.pkGDis N) {r : ℕ × ℕ} (hr : r ∈ PionCompleteness.Pi.pkGRoots N D) {u v : ℕ}
  (hu : u ∈ PionCompleteness.Pi.pkGVerts D r) (hv : v ∈ PionCompleteness.Pi.pkGVerts D r) {P : ℕ × ℕ} (hP : P ∈ D) :
  ¬PionCompleteness.Paper.Separates P u v
-/
#guard_msgs in
#check PionCompleteness.Paper.pkG_verts_not_separated

/--
info: PionCompleteness.Paper.pkG_verts_maximal {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)}
  (hD : D ∈ PionCompleteness.Pi.pkGDis N) {r : ℕ × ℕ} (hr : r ∈ PionCompleteness.Pi.pkGRoots N D) {w : ℕ}
  (hw : w ∈ Finset.Icc 1 N) (hwF : w ∉ PionCompleteness.Pi.pkGVerts D r) :
  ∃ u ∈ PionCompleteness.Pi.pkGVerts D r,
    ∃ P ∈ D, PionCompleteness.Paper.Separates P u w ∨ PionCompleteness.Paper.Separates P w u
-/
#guard_msgs in
#check PionCompleteness.Paper.pkG_verts_maximal

/--
info: PionCompleteness.Paper.pkG_verts_isFace {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)}
  (hD : D ∈ PionCompleteness.Pi.pkGDis N) {r : ℕ × ℕ} (hr : r ∈ PionCompleteness.Pi.pkGRoots N D) :
  PionCompleteness.Paper.Combinatorics.Polygons.IsFace N D (PionCompleteness.Pi.pkGVerts D r)
-/
#guard_msgs in
#check PionCompleteness.Paper.pkG_verts_isFace

/--
info: PionCompleteness.Paper.Combinatorics.Polygons.isFace_iff {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)}
  (hD : D ∈ PionCompleteness.Pi.pkGDis N) {F : Finset ℕ} :
  PionCompleteness.Paper.Combinatorics.Polygons.IsFace N D F ↔
    ∃ r ∈ PionCompleteness.Pi.pkGRoots N D, PionCompleteness.Pi.pkGVerts D r = F
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.isFace_iff

/--
info: PionCompleteness.Paper.pkG_verts_injOn {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)}
  (hD : D ∈ PionCompleteness.Pi.pkGDis N) :
  Set.InjOn (PionCompleteness.Pi.pkGVerts D) ↑(PionCompleteness.Pi.pkGRoots N D)
-/
#guard_msgs in
#check PionCompleteness.Paper.pkG_verts_injOn

/--
info: PionCompleteness.Paper.Combinatorics.Polygons.faces_eq_image {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)}
  (hD : D ∈ PionCompleteness.Pi.pkGDis N) :
  PionCompleteness.Paper.Combinatorics.Polygons.faces N D =
    Finset.image (PionCompleteness.Pi.pkGVerts D) (PionCompleteness.Pi.pkGRoots N D)
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.faces_eq_image

/--
info: PionCompleteness.Paper.pkG_verts_sup {D : Finset (ℕ × ℕ)} {r : ℕ × ℕ} (h : r.1 ≤ r.2) :
  ((PionCompleteness.Pi.pkGVerts D r).sup fun w => w) = r.2
-/
#guard_msgs in
#check PionCompleteness.Paper.pkG_verts_sup

/--
info: PionCompleteness.Paper.pkG_W_eq_oddStartLegs {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)}
  (hD : D ∈ PionCompleteness.Pi.pkGDis N) {r : ℕ × ℕ} (hr : r ∈ PionCompleteness.Pi.pkGRoots N D) :
  PionCompleteness.Pi.pkGW N D r =
    PionCompleteness.Paper.Combinatorics.Polygons.oddStartLegs N (PionCompleteness.Pi.pkGVerts D r)
-/
#guard_msgs in
#check PionCompleteness.Paper.pkG_W_eq_oddStartLegs

/--
info: PionCompleteness.Paper.chordSides_pkG_verts {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)}
  (hD : D ∈ PionCompleteness.Pi.pkGDis N) {r : ℕ × ℕ} (hr : r ∈ PionCompleteness.Pi.pkGRoots N D) {P : ℕ × ℕ} :
  P ∈ PionCompleteness.Paper.Combinatorics.Polygons.chordSides D (PionCompleteness.Pi.pkGVerts D r) ↔
    P ∈ PionCompleteness.Pi.pkGKids D r ∨ P = r ∧ r ∈ D
-/
#guard_msgs in
#check PionCompleteness.Paper.chordSides_pkG_verts

/--
info: PionCompleteness.Paper.pkG_deg_eq_card_chordSides {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)}
  (hD : D ∈ PionCompleteness.Pi.pkGDis N) {r : ℕ × ℕ} (hr : r ∈ PionCompleteness.Pi.pkGRoots N D) (C : Finset (ℕ × ℕ)) :
  PionCompleteness.Pi.pkGDeg (PionCompleteness.Pi.pkGCh D) (D \ C) r =
    (PionCompleteness.Paper.Combinatorics.Polygons.chordSides D (PionCompleteness.Pi.pkGVerts D r) \ C).card
-/
#guard_msgs in
#check PionCompleteness.Paper.pkG_deg_eq_card_chordSides

/--
info: PionCompleteness.Paper.pkG_verts_alternate {N : ℕ} {D : Finset (ℕ × ℕ)} (hD : D ∈ PionCompleteness.Pi.pkGDis N)
  {r : ℕ × ℕ} {u v : ℕ} (hu : u ∈ PionCompleteness.Pi.pkGVerts D r) (hv : v ∈ PionCompleteness.Pi.pkGVerts D r)
  (huv : u < v) (hcons : ∀ w ∈ PionCompleteness.Pi.pkGVerts D r, ¬(u < w ∧ w < v)) : (v - u) % 2 = 1
-/
#guard_msgs in
#check PionCompleteness.Paper.pkG_verts_alternate


/--
info: PionCompleteness.Paper.Combinatorics.Polygons.dissections {N : ℕ} (hN : 4 ≤ N) (hE : Even N) {D : Finset (ℕ × ℕ)}
  (hD : D ∈ PionCompleteness.Pi.pkGDis N) :
  (PionCompleteness.Paper.Combinatorics.Polygons.faces N D).card = D.card + 1 ∧
    ∀ F ∈ PionCompleteness.Paper.Combinatorics.Polygons.faces N D,
      4 ≤ F.card ∧
        Even F.card ∧
          (∀ u ∈ F, ∀ v ∈ F, u < v → (∀ w ∈ F, ¬(u < w ∧ w < v)) → (v - u) % 2 = 1) ∧
            ∀ u ∈ F, ∀ v ∈ F, (∀ w ∈ F, u ≤ w ∧ w ≤ v) → (v - u) % 2 = 1
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.dissections

/--
info: PionCompleteness.Paper.faceVertex_eq_Q {N : ℕ} (X : ℕ × ℕ → ℚ) (F : Finset ℕ) :
  PionCompleteness.Paper.NLSM.FeynmanRules.faceVertex N X F =
    (-1) ^ (F.card / 2 - 1) *
      PionCompleteness.Pi.pkGQ N X (PionCompleteness.Paper.Combinatorics.Polygons.oddStartLegs N F)
-/
#guard_msgs in
#check PionCompleteness.Paper.faceVertex_eq_Q

/--
info: PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.face_identity {N : ℕ} (hN : 4 ≤ N) (hE : Even N) {D : Finset (ℕ × ℕ)}
  (hD : D ∈ PionCompleteness.Pi.pkGDis N) :
  (∀ F ∈ PionCompleteness.Paper.Combinatorics.Polygons.faces N D,
      (∀ (X : ℕ × ℕ → ℚ),
          PionCompleteness.Pi.pkGQ N X (PionCompleteness.Paper.Combinatorics.Polygons.oddStartLegs N F) =
            ∑
                    p ∈
                      PionCompleteness.Pi.evens (PionCompleteness.Paper.Combinatorics.Polygons.oddStartLegs N F) ×ˢ
                        PionCompleteness.Pi.odds
                          (Finset.Icc 1 N \ PionCompleteness.Paper.Combinatorics.Polygons.oddStartLegs N F),
                    PionCompleteness.TreeRectangleZero.mesh N X (min p.1 p.2) (max p.1 p.2) +
                  PionCompleteness.Pi.pkGE N X -
                PionCompleteness.Pi.pkGSee N X
                  (Finset.Icc 1 N \ PionCompleteness.Paper.Combinatorics.Polygons.oddStartLegs N F) -
              PionCompleteness.Pi.pkGSoo N X (PionCompleteness.Paper.Combinatorics.Polygons.oddStartLegs N F)) ∧
        ∀ (S : Finset (ℕ × ℕ)),
          (PionCompleteness.Paper.Combinatorics.Polygons.chordSides D F \ PionCompleteness.Pi.cleanChords N S).card ≤
              1 →
            (∀ (X : ℕ × ℕ → ℚ),
                PionCompleteness.ChainSlice.OnLocus N (S ∪ PionCompleteness.Pi.pkGSame N) X →
                  PionCompleteness.Paper.NLSM.FeynmanRules.faceVertex N X F = 0) ∧
              ∀ (X : ℕ × ℕ → ℚ),
                PionCompleteness.ChainSlice.OnLocus N S X →
                  PionCompleteness.Paper.NLSM.FeynmanRules.faceVertex N X F =
                    (-1) ^ (F.card / 2 - 1) *
                      (PionCompleteness.Pi.pkGE N X -
                          PionCompleteness.Pi.pkGSee N X
                            (Finset.Icc 1 N \ PionCompleteness.Paper.Combinatorics.Polygons.oddStartLegs N F) -
                        PionCompleteness.Pi.pkGSoo N X
                          (PionCompleteness.Paper.Combinatorics.Polygons.oddStartLegs N F))) ∧
    ∀ (X : ℕ × ℕ → ℚ),
      -PionCompleteness.Paper.NLSM.FeynmanRules.faceVertex N X (Finset.Icc 1 N) =
        (-1) ^ ((N - 2) / 2) * PionCompleteness.Pi.pkGE N X
-/
#guard_msgs in
#check PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.face_identity

/--
info: PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.mesh_independent_of_omits_same_parity {N : ℕ} (hN : 4 ≤ N)
  (hE : Even N) {T : Finset (ℕ × ℕ)} (hT : T ⊆ PionCompleteness.TreeRectangleZero.diagonals N) {t₀ : ℕ × ℕ}
  (ht₀ : t₀ ∈ PionCompleteness.TreeRectangleZero.diagonals N) (ht₀T : t₀ ∉ T) (hpar : t₀.1 % 2 = t₀.2 % 2)
  (lam : ℕ × ℕ → ℚ) (hrel : ∀ (X : ℕ × ℕ → ℚ), ∑ t ∈ T, lam t * PionCompleteness.TreeRectangleZero.mesh N X t.1 t.2 = 0)
  (t : ℕ × ℕ) : t ∈ T → lam t = 0
-/
#guard_msgs in
#check PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.mesh_independent_of_omits_same_parity

/--
info: PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.rows_one_two_span_meet {N : ℕ} (hN : 6 ≤ N) (hE : Even N) :
  Disjoint (Finset.image (fun b => (1, b)) (Finset.Icc 3 (N - 1))) (Finset.image (fun b => (2, b)) (Finset.Icc 4 N)) ∧
    (3, 5) ∈ PionCompleteness.TreeRectangleZero.diagonals N ∧
      (3, 5) ∉ Finset.image (fun b => (1, b)) (Finset.Icc 3 (N - 1)) ∪ Finset.image (fun b => (2, b)) (Finset.Icc 4 N) ∧
        ∀ (α β : ℕ → ℚ),
          (∀ (X : ℕ × ℕ → ℚ),
              ∑ b ∈ Finset.Icc 3 (N - 1), α b * PionCompleteness.TreeRectangleZero.mesh N X 1 b =
                ∑ b ∈ Finset.Icc 4 N, β b * PionCompleteness.TreeRectangleZero.mesh N X 2 b) →
            ∀ (X : ℕ × ℕ → ℚ), ∑ b ∈ Finset.Icc 3 (N - 1), α b * PionCompleteness.TreeRectangleZero.mesh N X 1 b = 0
-/
#guard_msgs in
#check PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.rows_one_two_span_meet

/--
info: PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.form_identities {N : ℕ} (hN : 4 ≤ N) (hE : Even N) :
  (∀ (X : ℕ × ℕ → ℚ),
      ∀ a ∈ Finset.Icc 1 N,
        -PionCompleteness.TreeRectangleZero.mesh N X a (a + 1) =
          PionCompleteness.TreeRectangleZero.planar N X a (a + 2)) ∧
    (∀ (X : ℕ × ℕ → ℚ) (i j : ℕ),
        (i, j) ∈ PionCompleteness.TreeRectangleZero.diagonals N →
          X (i, j) = PionCompleteness.Pi.pkGQ N X (Finset.Icc i (j - 1))) ∧
      (∀ (X : ℕ × ℕ → ℚ),
          ∀ a ∈ Finset.Icc 1 N, ∑ b ∈ (Finset.Icc 1 N).erase a, -PionCompleteness.TreeRectangleZero.mesh N X a b = 0) ∧
        (∀ (X : ℕ × ℕ → ℚ),
            (∀ U ⊆ Finset.Icc 1 N, PionCompleteness.Pi.pkGQ N X U = PionCompleteness.Pi.pkGQ N X (Finset.Icc 1 N \ U)) ∧
              PionCompleteness.Pi.pkGQ N X (Finset.Icc 1 N) = 0) ∧
          (∀ T ⊆ PionCompleteness.TreeRectangleZero.diagonals N,
              (∃ t₀ ∈ PionCompleteness.TreeRectangleZero.diagonals N, t₀ ∉ T ∧ t₀.1 % 2 = t₀.2 % 2) →
                ∀ (lam : ℕ × ℕ → ℚ),
                  (∀ (X : ℕ × ℕ → ℚ), ∑ t ∈ T, lam t * PionCompleteness.TreeRectangleZero.mesh N X t.1 t.2 = 0) →
                    ∀ t ∈ T, lam t = 0) ∧
            (6 ≤ N →
              Disjoint (Finset.image (fun b => (1, b)) (Finset.Icc 3 (N - 1)))
                  (Finset.image (fun b => (2, b)) (Finset.Icc 4 N)) ∧
                (3, 5) ∈ PionCompleteness.TreeRectangleZero.diagonals N ∧
                  (3, 5) ∉
                      Finset.image (fun b => (1, b)) (Finset.Icc 3 (N - 1)) ∪
                        Finset.image (fun b => (2, b)) (Finset.Icc 4 N) ∧
                    ∀ (α β : ℕ → ℚ),
                      (∀ (X : ℕ × ℕ → ℚ),
                          ∑ b ∈ Finset.Icc 3 (N - 1), α b * PionCompleteness.TreeRectangleZero.mesh N X 1 b =
                            ∑ b ∈ Finset.Icc 4 N, β b * PionCompleteness.TreeRectangleZero.mesh N X 2 b) →
                        ∀ (X : ℕ × ℕ → ℚ),
                          ∑ b ∈ Finset.Icc 3 (N - 1), α b * PionCompleteness.TreeRectangleZero.mesh N X 1 b = 0)
-/
#guard_msgs in
#check PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.form_identities

/--
info: PionCompleteness.Paper.Combinatorics.Polygons.odd_chord_sides {N : ℕ} (hE : Even N) :
  (∀ P ∈ PionCompleteness.PionZeros.oddDiagonals N,
      (PionCompleteness.Pi.oddSide N P).card % 2 = 1 ∧
        3 ≤ (PionCompleteness.Pi.oddSide N P).card ∧
          (PionCompleteness.Pi.evenSide N P).card % 2 = 1 ∧ 3 ≤ (PionCompleteness.Pi.evenSide N P).card) ∧
    ∀ P ∈ PionCompleteness.PionZeros.oddDiagonals N,
      ∀ Q ∈ PionCompleteness.PionZeros.oddDiagonals N,
        PionCompleteness.Pi.oddSide N P = PionCompleteness.Pi.oddSide N Q → P = Q
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.odd_chord_sides

-- Library definitions matched with paper definitions: the library forms of coordinate loci,
-- regularity (non-degeneracy) and zeros (with the planar and mesh variables they use), minimal
-- zeros and the list (`𝒢_N`), which the paper's definitions in `Paper` are proved equal to
-- (pinned with the main theorem above), separated pairs (`S_G`), dissections, linked sides
-- (admissible separators, linked sides, `𝒮_B`, innermost chords), and the forms `Q_U`, `E`,
-- `Σ^{ee}_L`, `Σ^{oo}_L` of the block sums and the face identity.
/--
info: def PionCompleteness.TreeRectangleZero.vtx : ℕ → ℕ → ℕ :=
fun n i => (i + n - 1) % n + 1
-/
#guard_msgs in
#print PionCompleteness.TreeRectangleZero.vtx

/--
info: def PionCompleteness.TreeRectangleZero.planar.{u_1} : {K : Type u_1} → [Field K] → ℕ → (ℕ × ℕ → K) → ℕ → ℕ → K :=
fun {K} [Field K] n X i j =>
  if
      (min (PionCompleteness.TreeRectangleZero.vtx n i) (PionCompleteness.TreeRectangleZero.vtx n j),
          max (PionCompleteness.TreeRectangleZero.vtx n i) (PionCompleteness.TreeRectangleZero.vtx n j)) ∈
        PionCompleteness.TreeRectangleZero.diagonals n then
    X
      (min (PionCompleteness.TreeRectangleZero.vtx n i) (PionCompleteness.TreeRectangleZero.vtx n j),
        max (PionCompleteness.TreeRectangleZero.vtx n i) (PionCompleteness.TreeRectangleZero.vtx n j))
  else 0
-/
#guard_msgs in
#print PionCompleteness.TreeRectangleZero.planar

/--
info: def PionCompleteness.TreeRectangleZero.mesh.{u_1} : {K : Type u_1} → [Field K] → ℕ → (ℕ × ℕ → K) → ℕ → ℕ → K :=
fun {K} [Field K] n X i j =>
  PionCompleteness.TreeRectangleZero.planar n X i j + PionCompleteness.TreeRectangleZero.planar n X (i + 1) (j + 1) -
      PionCompleteness.TreeRectangleZero.planar n X i (j + 1) -
    PionCompleteness.TreeRectangleZero.planar n X (i + 1) j
-/
#guard_msgs in
#print PionCompleteness.TreeRectangleZero.mesh

/--
info: def PionCompleteness.TreeRectangleZero.diagonals : ℕ → Finset (ℕ × ℕ) :=
fun n => {p ∈ Finset.Icc 1 n ×ˢ Finset.Icc 1 n | p.1 + 2 ≤ p.2 ∧ ¬(p.1 = 1 ∧ p.2 = n)}
-/
#guard_msgs in
#print PionCompleteness.TreeRectangleZero.diagonals

/--
info: def PionCompleteness.PionZeros.oddDiagonals : ℕ → Finset (ℕ × ℕ) :=
fun N => {d ∈ PionCompleteness.TreeRectangleZero.diagonals N | (d.2 - d.1) % 2 = 1}
-/
#guard_msgs in
#print PionCompleteness.PionZeros.oddDiagonals

/--
info: def PionCompleteness.ChainSlice.OnLocus.{u_1} : {K : Type u_1} → [Field K] → ℕ → Finset (ℕ × ℕ) → (ℕ × ℕ → K) → Prop :=
fun {K} [Field K] m S X => ∀ t ∈ S, PionCompleteness.TreeRectangleZero.mesh m X t.1 t.2 = 0
-/
#guard_msgs in
#print PionCompleteness.ChainSlice.OnLocus

/--
info: def PionCompleteness.ChainSlice.Nondeg : ℕ → Finset (ℕ × ℕ) → Prop :=
fun m S =>
  ∀ d ∈ PionCompleteness.TreeRectangleZero.diagonals m, ∃ X, PionCompleteness.ChainSlice.OnLocus m S X ∧ X d ≠ 0
-/
#guard_msgs in
#print PionCompleteness.ChainSlice.Nondeg

/--
info: def PionCompleteness.PionNLSM.RatZeroOn : Set (ℕ × ℕ → ℚ) → PionCompleteness.PionNLSM.RF → Prop :=
fun V F =>
  ∃ P Q,
    F * (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) Q =
        (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) P ∧
      (∃ w ∈ V, (MvPolynomial.eval w) Q ≠ 0) ∧ ∀ x ∈ V, (MvPolynomial.eval x) P = 0
-/
#guard_msgs in
#print PionCompleteness.PionNLSM.RatZeroOn

/--
info: def PionCompleteness.Pi.calA.{u_1} : {K : Type u_1} → [Field K] → ℕ → (ℕ × ℕ → K) → K :=
fun {K} [Field K] N X => (-1) ^ (N / 2 - 1) * PionCompleteness.PionNLSM.NLSM N X
-/
#guard_msgs in
#print PionCompleteness.Pi.calA
/--
info: def PionCompleteness.PionNLSM.NLSM.{u_1} : {K : Type u_1} → [Field K] → ℕ → (ℕ × ℕ → K) → K :=
fun {K} [Field K] N X => PionCompleteness.PionNLSM.shiftCoeff N (↑N - 2) X
-/
#guard_msgs in
#print PionCompleteness.PionNLSM.NLSM

/--
info: def PionCompleteness.Pi.AmpZeroOn : ℕ → Finset (ℕ × ℕ) → Prop :=
fun N S =>
  ∀ (X : ℕ × ℕ → ℚ),
    PionCompleteness.ChainSlice.OnLocus N S X →
      (∀ d ∈ PionCompleteness.PionZeros.oddDiagonals N, X d ≠ 0) → PionCompleteness.Pi.calA N X = 0
-/
#guard_msgs in
#print PionCompleteness.Pi.AmpZeroOn

/--
info: def PionCompleteness.Pi.NLSMZeroOn : ℕ → Finset (ℕ × ℕ) → Prop :=
fun N S =>
  ∀ (X : ℕ × ℕ → ℚ),
    PionCompleteness.ChainSlice.OnLocus N S X →
      (∀ d ∈ PionCompleteness.PionZeros.oddDiagonals N, X d ≠ 0) → PionCompleteness.PionNLSM.NLSM N X = 0
-/
#guard_msgs in
#print PionCompleteness.Pi.NLSMZeroOn

/--
info: def PionCompleteness.Pi.IsNDZero : ℕ → Finset (ℕ × ℕ) → Prop :=
fun N S =>
  S ⊆ PionCompleteness.TreeRectangleZero.diagonals N ∧
    PionCompleteness.ChainSlice.Nondeg N S ∧ PionCompleteness.Pi.AmpZeroOn N S
-/
#guard_msgs in
#print PionCompleteness.Pi.IsNDZero

/--
info: def PionCompleteness.PionZeros.InST : Finset ℕ → ℕ → ℕ → Prop :=
fun T a b => a ∉ T ∧ b ∉ T ∧ (∃ t ∈ T, min a b < t ∧ t < max a b) ∧ ∃ t ∈ T, t < min a b ∨ max a b < t
-/
#guard_msgs in
#print PionCompleteness.PionZeros.InST

/--
info: def PionCompleteness.Pi.sepPairs : ℕ → Finset ℕ → Finset (ℕ × ℕ) :=
fun N G => {p ∈ PionCompleteness.TreeRectangleZero.diagonals N | PionCompleteness.PionZeros.InST G p.1 p.2}
-/
#guard_msgs in
#print PionCompleteness.Pi.sepPairs

/--
info: def PionCompleteness.PionZeros.Admissible : ℕ → ℕ → Finset ℕ → Prop :=
fun N r T => T ⊆ Finset.Icc 1 N ∧ 2 ≤ T.card ∧ ∀ t ∈ T, t % 2 = r
-/
#guard_msgs in
#print PionCompleteness.PionZeros.Admissible

/--
info: def PionCompleteness.Pi.IsSameParitySet : ℕ → Finset ℕ → Prop :=
fun N G => PionCompleteness.PionZeros.Admissible N 0 G ∨ PionCompleteness.PionZeros.Admissible N 1 G
-/
#guard_msgs in
#print PionCompleteness.Pi.IsSameParitySet

/--
info: def PionCompleteness.Pi.IsMixedAnchor : ℕ → Finset ℕ → Prop :=
fun N G => ∃ a ∈ Finset.Icc 1 N, ∃ b ∈ Finset.Icc 1 N, G = {a, b} ∧ a + 2 ≤ b ∧ ¬(a = 1 ∧ b = N) ∧ a % 2 ≠ b % 2
-/
#guard_msgs in
#print PionCompleteness.Pi.IsMixedAnchor

/--
info: def PionCompleteness.Pi.IsGSet : ℕ → Finset ℕ → Prop :=
fun N G => PionCompleteness.Pi.IsSameParitySet N G ∨ PionCompleteness.Pi.IsMixedAnchor N G
-/
#guard_msgs in
#print PionCompleteness.Pi.IsGSet

/--
info: def PionCompleteness.Pi.gLegSets : ℕ → Finset (Finset ℕ) :=
fun N => Finset.filter (PionCompleteness.Pi.IsGSet N) (Finset.Icc 1 N).powerset
-/
#guard_msgs in
#print PionCompleteness.Pi.gLegSets

/--
info: def PionCompleteness.Pi.gFamily : ℕ → Finset (Finset (ℕ × ℕ)) :=
fun N => Finset.image (PionCompleteness.Pi.sepPairs N) (PionCompleteness.Pi.gLegSets N)
-/
#guard_msgs in
#print PionCompleteness.Pi.gFamily

/--
info: def PionCompleteness.TreeRectangleZero.Crosses : ℕ × ℕ → ℕ × ℕ → Prop :=
fun p q => p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2 ∨ q.1 < p.1 ∧ p.1 < q.2 ∧ q.2 < p.2
-/
#guard_msgs in
#print PionCompleteness.TreeRectangleZero.Crosses

/--
info: def PionCompleteness.Pi.pkGDis : ℕ → Finset (Finset (ℕ × ℕ)) :=
fun N =>
  {D ∈ (PionCompleteness.PionZeros.oddDiagonals N).powerset |
    ∀ p ∈ D, ∀ q ∈ D, ¬PionCompleteness.TreeRectangleZero.Crosses p q}
-/
#guard_msgs in
#print PionCompleteness.Pi.pkGDis

/--
info: def PionCompleteness.Pi.cycArc : ℕ → ℕ → ℕ → Finset ℕ :=
fun N a len => Finset.image (fun k => PionCompleteness.TreeRectangleZero.vtx N (a + k)) (Finset.range len)
-/
#guard_msgs in
#print PionCompleteness.Pi.cycArc

/--
info: def PionCompleteness.Pi.cycPos : ℕ → ℕ → ℕ → ℕ :=
fun N s x => (x + N - s) % N
-/
#guard_msgs in
#print PionCompleteness.Pi.cycPos

/--
info: def PionCompleteness.Pi.headStart : ℕ × ℕ → ℕ :=
fun P => if P.1 % 2 = 1 then P.1 else P.2
-/
#guard_msgs in
#print PionCompleteness.Pi.headStart

/--
info: def PionCompleteness.Pi.headLen : ℕ → ℕ × ℕ → ℕ :=
fun N P => if P.1 % 2 = 1 then P.2 - P.1 else N - (P.2 - P.1)
-/
#guard_msgs in
#print PionCompleteness.Pi.headLen

/--
info: def PionCompleteness.Pi.tailStart : ℕ × ℕ → ℕ :=
fun P => if P.1 % 2 = 1 then P.2 else P.1
-/
#guard_msgs in
#print PionCompleteness.Pi.tailStart

/--
info: def PionCompleteness.Pi.tailLen : ℕ → ℕ × ℕ → ℕ :=
fun N P => N - PionCompleteness.Pi.headLen N P
-/
#guard_msgs in
#print PionCompleteness.Pi.tailLen

/--
info: def PionCompleteness.Pi.intArc : ℕ → ℕ → ℕ → Finset ℕ :=
fun N s k =>
  {x ∈ PionCompleteness.Pi.cycArc N s k |
    1 ≤ PionCompleteness.Pi.cycPos N s x ∧ PionCompleteness.Pi.cycPos N s x + 2 ≤ k}
-/
#guard_msgs in
#print PionCompleteness.Pi.intArc

/--
info: def PionCompleteness.Pi.admSeps : ℕ → ℕ → ℕ → ℕ → Finset (Finset ℕ) :=
fun N s k q => {Θ ∈ (PionCompleteness.Pi.intArc N s k).powerset | Θ.card = 1 ∨ 2 ≤ Θ.card ∧ ∀ θ ∈ Θ, θ % 2 = q}
-/
#guard_msgs in
#print PionCompleteness.Pi.admSeps

/--
info: def PionCompleteness.Pi.sepIn : ℕ → ℕ → ℕ → Finset ℕ → Finset (ℕ × ℕ) :=
fun N s k Θ =>
  {p ∈ PionCompleteness.TreeRectangleZero.diagonals N |
    p.1 ∈ PionCompleteness.Pi.cycArc N s k ∧
      p.2 ∈ PionCompleteness.Pi.cycArc N s k ∧
        p.1 ∉ Θ ∧
          p.2 ∉ Θ ∧
            ∃ θ ∈ Θ,
              min (PionCompleteness.Pi.cycPos N s p.1) (PionCompleteness.Pi.cycPos N s p.2) <
                  PionCompleteness.Pi.cycPos N s θ ∧
                PionCompleteness.Pi.cycPos N s θ <
                  max (PionCompleteness.Pi.cycPos N s p.1) (PionCompleteness.Pi.cycPos N s p.2)}
-/
#guard_msgs in
#print PionCompleteness.Pi.sepIn

/--
info: def PionCompleteness.Pi.NoFreeSep : ℕ → Finset (ℕ × ℕ) → ℕ → ℕ → ℕ → Prop :=
fun N S s k q =>
  ∀ Θ ∈ PionCompleteness.Pi.admSeps N s k q,
    ¬Disjoint (PionCompleteness.Pi.sepIn N s k Θ) (PionCompleteness.Pi.missing N S)
-/
#guard_msgs in
#print PionCompleteness.Pi.NoFreeSep

/--
info: def PionCompleteness.Pi.goodTail : ℕ → Finset (ℕ × ℕ) → Finset (ℕ × ℕ) :=
fun N S =>
  {P ∈ PionCompleteness.Pi.poleChords N S |
    PionCompleteness.Pi.NoFreeSep N S (PionCompleteness.Pi.tailStart P) (PionCompleteness.Pi.tailLen N P) 1}
-/
#guard_msgs in
#print PionCompleteness.Pi.goodTail

/--
info: def PionCompleteness.Pi.IsInnermostChord : ℕ → Finset (ℕ × ℕ) → ℕ × ℕ → Prop :=
fun N S P =>
  P ∈ PionCompleteness.Pi.goodTail N S ∧
    ∀ Q ∈ PionCompleteness.Pi.goodTail N S, ¬PionCompleteness.Pi.oddSide N Q ⊂ PionCompleteness.Pi.oddSide N P
-/
#guard_msgs in
#print PionCompleteness.Pi.IsInnermostChord

/--
info: def PionCompleteness.Pi.IsMinimalZero : ℕ → Finset (ℕ × ℕ) → Prop :=
fun N Z => PionCompleteness.Pi.IsNDZero N Z ∧ ∀ t ∈ Z, ¬PionCompleteness.Pi.AmpZeroOn N (Z.erase t)
-/
#guard_msgs in
#print PionCompleteness.Pi.IsMinimalZero

/--
info: def PionCompleteness.Pi.pkGQ : ℕ → (ℕ × ℕ → ℚ) → Finset ℕ → ℚ :=
fun N X U => ∑ p ∈ U ×ˢ U with p.1 < p.2, -PionCompleteness.TreeRectangleZero.mesh N X p.1 p.2
-/
#guard_msgs in
#print PionCompleteness.Pi.pkGQ

/--
info: def PionCompleteness.Pi.pkGE : ℕ → (ℕ × ℕ → ℚ) → ℚ :=
fun N X =>
  ∑ t ∈ PionCompleteness.TreeRectangleZero.diagonals N with t.1 % 2 = 0 ∧ t.2 % 2 = 0,
    PionCompleteness.TreeRectangleZero.mesh N X t.1 t.2
-/
#guard_msgs in
#print PionCompleteness.Pi.pkGE

/--
info: def PionCompleteness.Pi.pkGSee : ℕ → (ℕ × ℕ → ℚ) → Finset ℕ → ℚ :=
fun N X W =>
  ∑ p ∈ W ×ˢ W with p.1 < p.2 ∧ p.1 % 2 = 0 ∧ p.2 % 2 = 0, PionCompleteness.TreeRectangleZero.mesh N X p.1 p.2
-/
#guard_msgs in
#print PionCompleteness.Pi.pkGSee

/--
info: def PionCompleteness.Pi.pkGSoo : ℕ → (ℕ × ℕ → ℚ) → Finset ℕ → ℚ :=
fun N X W =>
  ∑ p ∈ W ×ˢ W with p.1 < p.2 ∧ p.1 % 2 = 1 ∧ p.2 % 2 = 1, PionCompleteness.TreeRectangleZero.mesh N X p.1 p.2
-/
#guard_msgs in
#print PionCompleteness.Pi.pkGSoo

-- `Paper`, continued: the three-cut theorem (single-family form) and its corollary (three cuts, one
-- parity), the lemmas of its proof with case (EP) and the zone set `G′`, absorption, the helpers
-- they use (`zoneSet_eq_pkT_zoneSet`, `pkT_ZH_of_not_caseEP`).
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.three_separators_single_parity_arc_witness {N ω x0 x1 y0 y1 : ℕ}
  {Θ τ σ : Finset ℕ} (h : PionCompleteness.Pi.ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ) :
  ∃ G,
    PionCompleteness.Pi.ConsecWit N Θ τ σ G ∧
      PionCompleteness.Pi.sepPairs N G ⊆ PionCompleteness.Pi.threeSepCut N ω x0 x1 y0 y1 Θ τ σ
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.three_separators_single_parity_arc_witness
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.three_separators_contain_t_separated_set {N ω x0 x1 y0 y1 : ℕ}
  {Θ τ σ : Finset ℕ} (h : PionCompleteness.Pi.ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ) :
  ∃ G,
    PionCompleteness.Pi.IsSameParitySet N G ∧
      PionCompleteness.Pi.sepPairs N G ⊆ PionCompleteness.Pi.threeSepCut N ω x0 x1 y0 y1 Θ τ σ
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.three_separators_contain_t_separated_set
/--
info: PionCompleteness.Paper.zoneSet_eq_pkT_zoneSet {ω x0 y1 : ℕ} {Θ τ σ : Finset ℕ} (hτ : ∀ t ∈ τ, 1 ≤ t)
  (hσ : ∀ s ∈ σ, 1 ≤ s) : PionCompleteness.Paper.zoneSet ω x0 y1 Θ τ σ = PionCompleteness.Pi.pkTZoneSet ω x0 y1 Θ τ σ
-/
#guard_msgs in
#check PionCompleteness.Paper.zoneSet_eq_pkT_zoneSet
/--
info: PionCompleteness.Paper.pkT_ZH_of_not_caseEP {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ}
  (h : PionCompleteness.Pi.ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ) (hτ : ∀ t ∈ τ, t % 2 = 1) (hσ : ∀ s ∈ σ, s % 2 = 1)
  (hEP : ¬PionCompleteness.Paper.CaseEP x0 x1 y0 y1 Θ τ σ) : PionCompleteness.Pi.pkTZH N ω x0 x1 y0 y1 Θ τ σ
-/
#guard_msgs in
#check PionCompleteness.Paper.pkT_ZH_of_not_caseEP
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.parity_block_witness_in_cut {N ω : ℕ} {Θ K G : Finset ℕ} {a b : ℕ}
  (ha : a ∈ K) (hb : b ∈ K) (hK : ∀ k ∈ K, ¬(a < k ∧ k < b)) (hbω : b ≤ ω + 1) (hG : G ⊆ Finset.Icc a b)
  (hGΘ : ∀ (x : ℕ), a < x → x < b → (x ∈ G ↔ x ∈ Θ)) (hKA : ∀ k ∈ K, k ∉ G → k ∈ Finset.Icc 1 ω ∧ k ∉ Θ)
  (hbx : b ∈ G → b ∉ Θ → K ⊆ Finset.Icc 1 b) (hax : a ∈ G → a ∉ Θ → K ⊆ Finset.Icc a N) (p : ℕ × ℕ) :
  p ∈ PionCompleteness.Pi.sepPairs N G →
    PionCompleteness.Pi.runSepA ω Θ p.1 p.2 ∨ PionCompleteness.PionZeros.InST K p.1 p.2
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.parity_block_witness_in_cut
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.separator_meets_every_gap_interval {x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ}
  (hτ : ∀ t ∈ τ, t % 2 = 1) (hσ : ∀ s ∈ σ, s % 2 = 1) (hEP : ¬PionCompleteness.Paper.CaseEP x0 x1 y0 y1 Θ τ σ)
  {K : Finset ℕ} (hK : K = Finset.Icc x0 x1 ∪ τ ∨ K = Finset.Icc y0 y1 ∪ σ) {p q : ℕ} (hp : p ∈ Θ) (hq : q ∈ Θ)
  (hpq : p < q) (hlo : ∃ k ∈ K, k < p) (hhi : ∃ k ∈ K, q < k) : ∃ k ∈ K, p ≤ k ∧ k ≤ q
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.separator_meets_every_gap_interval
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.removed_leg_of_tau_iff {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ}
  (h : PionCompleteness.Pi.ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ) (hτ : ∀ t ∈ τ, t % 2 = 1) (hσ : ∀ s ∈ σ, s % 2 = 1)
  (hEP : ¬PionCompleteness.Paper.CaseEP x0 x1 y0 y1 Θ τ σ) {t : ℕ} :
  PionCompleteness.Paper.RemovedTau ω x0 y1 Θ σ t ↔
    PionCompleteness.Paper.PX x0 σ ∧ (t < x0 ∨ y1 < t ∧ ∃ θ ∈ Θ, y1 < θ ∧ θ < t ∧ Disjoint σ (Finset.Icc θ ω))
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.removed_leg_of_tau_iff
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.removed_leg_of_sigma_iff {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ}
  (h : PionCompleteness.Pi.ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ) (hτ : ∀ t ∈ τ, t % 2 = 1) (hσ : ∀ s ∈ σ, s % 2 = 1)
  (hEP : ¬PionCompleteness.Paper.CaseEP x0 x1 y0 y1 Θ τ σ) {s : ℕ} (hs : s ∈ σ) :
  PionCompleteness.Paper.RemovedSigma ω x0 y1 Θ τ s ↔
    PionCompleteness.Paper.PY ω y1 τ ∧ (y1 < s ∨ s < x0 ∧ ∃ θ ∈ Θ, s < θ ∧ θ < x0 ∧ Disjoint τ (Finset.Icc 1 θ))
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.removed_leg_of_sigma_iff
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.side_gap_gamma_sigma {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ}
  (h : PionCompleteness.Pi.ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ) (hτ : ∀ t ∈ τ, t % 2 = 1) (hσ : ∀ s ∈ σ, s % 2 = 1)
  (hEP : ¬PionCompleteness.Paper.CaseEP x0 x1 y0 y1 Θ τ σ) {q : ℕ} (hq : q ∈ Θ) (h1 : x1 + 1 < q) (h2 : q < y0) :
  ∃ k ∈ σ, x1 + 1 < k ∧ k < q
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.side_gap_gamma_sigma
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.side_gap_gamma_tau {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ}
  (h : PionCompleteness.Pi.ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ) (hτ : ∀ t ∈ τ, t % 2 = 1) (hσ : ∀ s ∈ σ, s % 2 = 1)
  (hEP : ¬PionCompleteness.Paper.CaseEP x0 x1 y0 y1 Θ τ σ) {p : ℕ} (hp : p ∈ Θ) (h1 : x1 < p) (h2 : p < y0 - 1) :
  ∃ k ∈ τ, p < k ∧ k < y0 - 1
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.side_gap_gamma_tau
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.side_gap_left_sigma {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ}
  (h : PionCompleteness.Pi.ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ) (hτ : ∀ t ∈ τ, t % 2 = 1) (hσ : ∀ s ∈ σ, s % 2 = 1)
  (hEP : ¬PionCompleteness.Paper.CaseEP x0 x1 y0 y1 Θ τ σ) {p : ℕ} (hp : p ∈ Θ) (h1 : p < x0 - 1)
  (hlo : ∃ s ∈ σ, s < p) : ∃ k ∈ σ, p < k ∧ k < x0 - 1
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.side_gap_left_sigma
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.side_gap_right_tau {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ}
  (h : PionCompleteness.Pi.ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ) (hτ : ∀ t ∈ τ, t % 2 = 1) (hσ : ∀ s ∈ σ, s % 2 = 1)
  (hEP : ¬PionCompleteness.Paper.CaseEP x0 x1 y0 y1 Θ τ σ) {q : ℕ} (hq : q ∈ Θ) (h1 : y1 + 1 < q)
  (hhi : ∃ t ∈ τ, q < t) : ∃ k ∈ τ, y1 + 1 < k ∧ k < q
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.side_gap_right_tau
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.zoneSet_keeps_middle_legs {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ}
  (h : PionCompleteness.Pi.ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ) (hτ : ∀ t ∈ τ, t % 2 = 1) (hσ : ∀ s ∈ σ, s % 2 = 1)
  (hEP : ¬PionCompleteness.Paper.CaseEP x0 x1 y0 y1 Θ τ σ) {g : ℕ} (hg : g ∈ τ ∪ σ) (h1 : x0 ≤ g) (h2 : g ≤ y1) :
  g ∈ PionCompleteness.Paper.zoneSet ω x0 y1 Θ τ σ
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.zoneSet_keeps_middle_legs
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.zoneSet_keeps_common_legs {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ}
  (h : PionCompleteness.Pi.ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ) (hτ : ∀ t ∈ τ, t % 2 = 1) (hσ : ∀ s ∈ σ, s % 2 = 1)
  (hEP : ¬PionCompleteness.Paper.CaseEP x0 x1 y0 y1 Θ τ σ) {g : ℕ} (hg : g ∈ τ ∩ σ) :
  g ∈ PionCompleteness.Paper.zoneSet ω x0 y1 Θ τ σ
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.zoneSet_keeps_common_legs
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.reach_witness_is_odd_interval {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ}
  (h : PionCompleteness.Pi.ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ) (hτ : ∀ t ∈ τ, t % 2 = 1) (hσ : ∀ s ∈ σ, s % 2 = 1)
  (hEP : ¬PionCompleteness.Paper.CaseEP x0 x1 y0 y1 Θ τ σ) :
  PionCompleteness.Paper.zoneSet ω x0 y1 Θ τ σ ⊆ Finset.Icc 1 ω ∧
    ∀ (hne : (PionCompleteness.Paper.zoneSet ω x0 y1 Θ τ σ).Nonempty),
      PionCompleteness.Paper.zoneSet ω x0 y1 Θ τ σ =
        PionCompleteness.Pi.odds (τ ∪ σ) ∩
          Finset.Icc ((PionCompleteness.Paper.zoneSet ω x0 y1 Θ τ σ).min' hne)
            ((PionCompleteness.Paper.zoneSet ω x0 y1 Θ τ σ).max' hne)
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.reach_witness_is_odd_interval
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.reach_witness_has_two_legs {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ}
  (h : PionCompleteness.Pi.ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ) (hτ : ∀ t ∈ τ, t % 2 = 1) (hσ : ∀ s ∈ σ, s % 2 = 1)
  (hEP : ¬PionCompleteness.Paper.CaseEP x0 x1 y0 y1 Θ τ σ) : 2 ≤ (PionCompleteness.Paper.zoneSet ω x0 y1 Θ τ σ).card
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.reach_witness_has_two_legs
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.reach_witness_pairs_in_cut {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ}
  (h : PionCompleteness.Pi.ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ) (hτ : ∀ t ∈ τ, t % 2 = 1) (hσ : ∀ s ∈ σ, s % 2 = 1)
  (hEP : ¬PionCompleteness.Paper.CaseEP x0 x1 y0 y1 Θ τ σ) :
  PionCompleteness.Pi.sepPairs N (PionCompleteness.Paper.zoneSet ω x0 y1 Θ τ σ) ⊆
    PionCompleteness.Pi.threeSepCut N ω x0 x1 y0 y1 Θ τ σ
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.reach_witness_pairs_in_cut
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.residue_chord_joins_innermost_flank_class {N : ℕ} (hN : 6 ≤ N)
  (hE : Even N) {S : Finset (ℕ × ℕ)} (hF : PionCompleteness.Paper.NLSM.Zeros.IsCandidateSet N S) {P : ℕ × ℕ}
  (hP : PionCompleteness.Pi.IsInnermostChord N S P) {Q : ℕ × ℕ} (hQ : Q ∈ PionCompleteness.Pi.poleChords N S)
  (hsub : PionCompleteness.Pi.oddSide N Q ⊆ PionCompleteness.Pi.oddSide N P)
  (hoo : PionCompleteness.Pi.innerOO N S Q = PionCompleteness.Pi.innerOO N S P) : Q ∈ PionCompleteness.Pi.hitClass N S P
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.residue_chord_joins_innermost_flank_class
/--
info: def PionCompleteness.Paper.Combinatorics.Polygons.IsRunOf : ℕ → ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Prop :=
fun N s L Θ Z =>
  Z.Nonempty ∧
    Z ⊆ L \ Θ ∧
      (∀ u ∈ Z, ∀ v ∈ Z, PionCompleteness.Pi.SameRun N s Θ u v) ∧
        ∀ u ∈ Z, ∀ v ∈ L \ Θ, PionCompleteness.Pi.SameRun N s Θ u v → v ∈ Z
-/
#guard_msgs in
#print PionCompleteness.Paper.Combinatorics.Polygons.IsRunOf
/--
info: def PionCompleteness.Paper.Combinatorics.Polygons.IsOccupiedRun : ℕ →
  Finset (ℕ × ℕ) → ℕ × ℕ → Finset ℕ → Finset ℕ → Prop :=
fun N S P Θ Z =>
  PionCompleteness.Paper.Combinatorics.Polygons.IsRunOf N (PionCompleteness.Pi.headStart P)
      (PionCompleteness.Pi.oddSide N P) Θ Z ∧
    ∃ p ∈ PionCompleteness.Pi.Moo N S, p.1 ∈ Z ∧ p.2 ∈ Z
-/
#guard_msgs in
#print PionCompleteness.Paper.Combinatorics.Polygons.IsOccupiedRun
/--
info: def PionCompleteness.Paper.Combinatorics.Polygons.IsSpread : ℕ → Finset (ℕ × ℕ) → ℕ × ℕ → Finset ℕ → Prop :=
fun N S P Θ =>
  ∃ X Y,
    PionCompleteness.Paper.Combinatorics.Polygons.IsOccupiedRun N S P Θ X ∧
      PionCompleteness.Paper.Combinatorics.Polygons.IsOccupiedRun N S P Θ Y ∧ X ≠ Y
-/
#guard_msgs in
#print PionCompleteness.Paper.Combinatorics.Polygons.IsSpread
/--
info: def PionCompleteness.Paper.Combinatorics.Polygons.reachPiece : ℕ → ℕ × ℕ → ℕ × ℕ → Finset ℕ → Finset ℕ :=
fun N P Q τ =>
  {x ∈ PionCompleteness.Pi.evenSide N Q |
      x ∉ τ ∧
        PionCompleteness.Pi.SameRun N (PionCompleteness.Pi.tailStart Q) τ x
          (PionCompleteness.TreeRectangleZero.vtx N (PionCompleteness.Pi.tailStart P + 1))} ∪
    {y ∈ τ | τ = {y} ∧ y % 2 = 0}
-/
#guard_msgs in
#print PionCompleteness.Paper.Combinatorics.Polygons.reachPiece
/--
info: PionCompleteness.Paper.isRunOf_through {N s : ℕ} {L Θ : Finset ℕ} (hs : s ∈ Finset.Icc 1 N) (hL : L ⊆ Finset.Icc 1 N)
  (hΘ : Θ ⊆ Finset.Icc 1 N) {u : ℕ} (hu : u ∈ L \ Θ) :
  PionCompleteness.Paper.Combinatorics.Polygons.IsRunOf N s L Θ
    (Finset.filter (PionCompleteness.Pi.SameRun N s Θ u) (L \ Θ))
-/
#guard_msgs in
#check PionCompleteness.Paper.isRunOf_through
/--
info: PionCompleteness.Paper.isRunOf_eq {N s : ℕ} {L Θ X Y : Finset ℕ}
  (hX : PionCompleteness.Paper.Combinatorics.Polygons.IsRunOf N s L Θ X)
  (hY : PionCompleteness.Paper.Combinatorics.Polygons.IsRunOf N s L Θ Y) {u : ℕ} (huX : u ∈ X) (huY : u ∈ Y) : X = Y
-/
#guard_msgs in
#check PionCompleteness.Paper.isRunOf_eq
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.inner_oo_pair_in_one_run {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
  {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ} (hP : P ∈ PionCompleteness.PionZeros.oddDiagonals N) {Θ : Finset ℕ}
  (hΘ : Θ ∈ PionCompleteness.Pi.admSeps N (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P) 0)
  (hΘe : ∀ θ ∈ Θ, θ % 2 = 0)
  (hΘd :
    Disjoint (PionCompleteness.Pi.sepIn N (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P) Θ)
      (PionCompleteness.Pi.missing N S))
  {p : ℕ × ℕ} (hp : p ∈ PionCompleteness.Pi.innerOO N S P) :
  ∃ Z,
    PionCompleteness.Paper.Combinatorics.Polygons.IsRunOf N (PionCompleteness.Pi.headStart P)
        (PionCompleteness.Pi.oddSide N P) Θ Z ∧
      p.1 ∈ Z ∧ p.2 ∈ Z
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.inner_oo_pair_in_one_run
/--
info: PionCompleteness.Paper.spread_of_isSpread {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ}
  (hP : P ∈ PionCompleteness.PionZeros.oddDiagonals N) {Θ : Finset ℕ}
  (h : PionCompleteness.Paper.Combinatorics.Polygons.IsSpread N S P Θ) :
  PionCompleteness.Pi.Spread N S (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P) Θ
-/
#guard_msgs in
#check PionCompleteness.Paper.spread_of_isSpread
/--
info: PionCompleteness.Paper.legs_of_mem_admSeps {N q : ℕ} (hE : Even N) {P : ℕ × ℕ}
  (hP : P ∈ PionCompleteness.PionZeros.oddDiagonals N) {Θ : Finset ℕ}
  (h : Θ ∈ PionCompleteness.Pi.admSeps N (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P) q) :
  Θ ⊆ Finset.Icc 1 N
-/
#guard_msgs in
#check PionCompleteness.Paper.legs_of_mem_admSeps
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.isSpread_iff_spread {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
  {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ} (hP : P ∈ PionCompleteness.PionZeros.oddDiagonals N) {Θ : Finset ℕ}
  (hΘ : Θ ⊆ Finset.Icc 1 N) :
  PionCompleteness.Paper.Combinatorics.Polygons.IsSpread N S P Θ ↔
    PionCompleteness.Pi.Spread N S (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P) Θ
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.isSpread_iff_spread
/--
info: PionCompleteness.Paper.isRunOf_lin {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {P : ℕ × ℕ}
  (hP : P ∈ PionCompleteness.PionZeros.oddDiagonals N) {Θ : Finset ℕ}
  (hΘ : Θ ∈ PionCompleteness.Pi.admSeps N (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P) 0)
  {Z : Finset ℕ}
  (hZ :
    PionCompleteness.Paper.Combinatorics.Polygons.IsRunOf N (PionCompleteness.Pi.headStart P)
      (PionCompleteness.Pi.oddSide N P) Θ Z)
  {a b : ℕ}
  (hR :
    PionCompleteness.Pi.IsRun (PionCompleteness.Pi.headLen N P)
      (Finset.image (PionCompleteness.Pi.rotLeg N (N + 1 - PionCompleteness.Pi.headStart P)) Θ) a b)
  {y : ℕ} (hy : y ∈ Z) (hya : a ≤ PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart P) y + 1)
  (hyb : PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart P) y + 1 ≤ b) (x : ℕ) :
  x ∈ Z ↔
    x ∈ Finset.Icc 1 N ∧
      a ≤ PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart P) x + 1 ∧
        PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart P) x + 1 ≤ b
-/
#guard_msgs in
#check PionCompleteness.Paper.isRunOf_lin
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.occupied_run_chords {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
  {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ} (hP : P ∈ PionCompleteness.Pi.poleChords N S) {Θ : Finset ℕ}
  (hΘ : Θ ∈ PionCompleteness.Pi.admSeps N (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P) 0)
  (hΘe : ∀ θ ∈ Θ, θ % 2 = 0)
  (hΘd :
    Disjoint (PionCompleteness.Pi.sepIn N (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P) Θ)
      (PionCompleteness.Pi.missing N S))
  {Z : Finset ℕ} (hZ : PionCompleteness.Paper.Combinatorics.Polygons.IsOccupiedRun N S P Θ Z) :
  ∃ Q ∈ PionCompleteness.Pi.poleChords N S, PionCompleteness.Pi.oddSide N Q = Z
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.occupied_run_chords
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.separated_pairs_of_sub_arc {N s k s' k' : ℕ} (hs : s ∈ Finset.Icc 1 N)
  (hk : k < N) (hs' : s' ∈ Finset.Icc 1 N)
  (hsub : PionCompleteness.Pi.cycArc N s' k' ⊆ PionCompleteness.Pi.cycArc N s k) (Θ : Finset ℕ) :
  PionCompleteness.Pi.sepIn N s' k' (Θ ∩ PionCompleteness.Pi.cycArc N s' k') ⊆ PionCompleteness.Pi.sepIn N s k Θ
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.separated_pairs_of_sub_arc
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.innermost_chord_has_no_spread_separator {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
  {S : Finset (ℕ × ℕ)} (hF : PionCompleteness.Paper.NLSM.Zeros.IsCandidateSet N S) {P : ℕ × ℕ}
  (hP : PionCompleteness.Pi.IsInnermostChord N S P) {Θ : Finset ℕ}
  (hΘ : Θ ∈ PionCompleteness.Pi.admSeps N (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P) 0)
  (hΘe : ∀ θ ∈ Θ, θ % 2 = 0)
  (hΘd :
    Disjoint (PionCompleteness.Pi.sepIn N (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P) Θ)
      (PionCompleteness.Pi.missing N S)) :
  ¬PionCompleteness.Paper.Combinatorics.Polygons.IsSpread N S P Θ
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.innermost_chord_has_no_spread_separator
/--
info: PionCompleteness.Paper.sameRun_between {N s : ℕ} {τ : Finset ℕ} {a w b : ℕ} (h : PionCompleteness.Pi.SameRun N s τ a b)
  (hw :
    PionCompleteness.Pi.cycPos N s a < PionCompleteness.Pi.cycPos N s w ∧
        PionCompleteness.Pi.cycPos N s w < PionCompleteness.Pi.cycPos N s b ∨
      PionCompleteness.Pi.cycPos N s b < PionCompleteness.Pi.cycPos N s w ∧
        PionCompleteness.Pi.cycPos N s w < PionCompleteness.Pi.cycPos N s a) :
  (∀ t ∈ τ, PionCompleteness.Pi.cycPos N s t ≠ PionCompleteness.Pi.cycPos N s w) ∧ PionCompleteness.Pi.SameRun N s τ w b
-/
#guard_msgs in
#check PionCompleteness.Paper.sameRun_between
/--
info: PionCompleteness.Paper.mem_of_adj_run {N s : ℕ} {L Θ Z : Finset ℕ}
  (hZ : PionCompleteness.Paper.Combinatorics.Polygons.IsRunOf N s L Θ Z) {z x : ℕ} (hz : z ∈ Z) (hxL : x ∈ L)
  (hxZ : x ∉ Z)
  (hadj :
    PionCompleteness.Pi.cycPos N s x + 1 = PionCompleteness.Pi.cycPos N s z ∨
      PionCompleteness.Pi.cycPos N s z + 1 = PionCompleteness.Pi.cycPos N s x) :
  x ∈ Θ
-/
#guard_msgs in
#check PionCompleteness.Paper.mem_of_adj_run
/--
info: PionCompleteness.Paper.second_leg_pos {N : ℕ} (hE : N % 2 = 0) {P : ℕ × ℕ}
  (hP : P ∈ PionCompleteness.PionZeros.oddDiagonals N) :
  PionCompleteness.TreeRectangleZero.vtx N (PionCompleteness.Pi.tailStart P + 1) ∈ Finset.Icc 1 N ∧
    PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart P)
        (PionCompleteness.TreeRectangleZero.vtx N (PionCompleteness.Pi.tailStart P + 1)) =
      PionCompleteness.Pi.headLen N P + 1
-/
#guard_msgs in
#check PionCompleteness.Paper.second_leg_pos
/--
info: PionCompleteness.Paper.run_chord_frame {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {P Q : ℕ × ℕ}
  (hP : P ∈ PionCompleteness.PionZeros.oddDiagonals N) (hQ : Q ∈ PionCompleteness.PionZeros.oddDiagonals N)
  (hsub : PionCompleteness.Pi.oddSide N Q ⊆ PionCompleteness.Pi.oddSide N P) :
  ∃ c,
    c + PionCompleteness.Pi.headLen N Q ≤ PionCompleteness.Pi.headLen N P ∧
      (∀ x ∈ Finset.Icc 1 N,
          x ∈ PionCompleteness.Pi.oddSide N Q ↔
            c ≤ PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart P) x ∧
              PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart P) x < c + PionCompleteness.Pi.headLen N Q) ∧
        (∀ x ∈ Finset.Icc 1 N,
            c + PionCompleteness.Pi.headLen N Q ≤ PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart P) x →
              PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.tailStart Q) x =
                PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart P) x -
                  (c + PionCompleteness.Pi.headLen N Q)) ∧
          ∀ x ∈ Finset.Icc 1 N,
            PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart P) x < c →
              PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.tailStart Q) x =
                PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart P) x + N -
                  (c + PionCompleteness.Pi.headLen N Q)
-/
#guard_msgs in
#check PionCompleteness.Paper.run_chord_frame
/--
info: PionCompleteness.Paper.shortening_core {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {S : Finset (ℕ × ℕ)} {P Q : ℕ × ℕ}
  (hP : P ∈ PionCompleteness.PionZeros.oddDiagonals N)
  (hlinked : PionCompleteness.Pi.NoFreeSep N S (PionCompleteness.Pi.tailStart P) (PionCompleteness.Pi.tailLen N P) 1)
  {Θ : Finset ℕ}
  (hΘ : Θ ∈ PionCompleteness.Pi.admSeps N (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P) 0)
  (hΘe : ∀ θ ∈ Θ, θ % 2 = 0)
  (hΘd :
    Disjoint (PionCompleteness.Pi.sepIn N (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P) Θ)
      (PionCompleteness.Pi.missing N S))
  {X Y Z : Finset ℕ} (hX : PionCompleteness.Paper.Combinatorics.Polygons.IsOccupiedRun N S P Θ X)
  (hY : PionCompleteness.Paper.Combinatorics.Polygons.IsOccupiedRun N S P Θ Y)
  (hZ :
    PionCompleteness.Paper.Combinatorics.Polygons.IsRunOf N (PionCompleteness.Pi.headStart P)
      (PionCompleteness.Pi.oddSide N P) Θ Z)
  (hQ : Q ∈ PionCompleteness.PionZeros.oddDiagonals N) (hQZ : PionCompleteness.Pi.oddSide N Q = Z) {τ : Finset ℕ}
  (hτ : τ ∈ PionCompleteness.Pi.admSeps N (PionCompleteness.Pi.tailStart Q) (PionCompleteness.Pi.tailLen N Q) 1)
  (hτd :
    Disjoint (PionCompleteness.Pi.sepIn N (PionCompleteness.Pi.tailStart Q) (PionCompleteness.Pi.tailLen N Q) τ)
      (PionCompleteness.Pi.missing N S))
  {d0 : ℕ} (hd0 : d0 ∈ Θ)
  (hd0r :
    PionCompleteness.Pi.SameRun N (PionCompleteness.Pi.tailStart Q) τ d0
      (PionCompleteness.TreeRectangleZero.vtx N (PionCompleteness.Pi.tailStart P + 1)))
  (hd0X :
    ∀ x ∈ X,
      PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart P) x <
        PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart P) d0)
  (hd0Y :
    ∀ y ∈ Y,
      PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart P) d0 <
        PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart P) y) :
  Θ \ (Finset.Icc 1 N \ PionCompleteness.Paper.Combinatorics.Polygons.reachPiece N P Q τ) ∈
      PionCompleteness.Pi.admSeps N (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P) 0 ∧
    (∀ θ ∈ Θ \ (Finset.Icc 1 N \ PionCompleteness.Paper.Combinatorics.Polygons.reachPiece N P Q τ), θ % 2 = 0) ∧
      Disjoint
          (PionCompleteness.Pi.sepIn N (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P)
            (Θ \ (Finset.Icc 1 N \ PionCompleteness.Paper.Combinatorics.Polygons.reachPiece N P Q τ)))
          (PionCompleteness.Pi.missing N S) ∧
        Θ \ (Finset.Icc 1 N \ PionCompleteness.Paper.Combinatorics.Polygons.reachPiece N P Q τ) ⊂ Θ ∧
          (∀ x ∈ X,
              ∀ y ∈ Y,
                ¬PionCompleteness.Pi.SameRun N (PionCompleteness.Pi.headStart P)
                    (Θ \ (Finset.Icc 1 N \ PionCompleteness.Paper.Combinatorics.Polygons.reachPiece N P Q τ)) x y) ∧
            PionCompleteness.Paper.Combinatorics.Polygons.IsSpread N S P
              (Θ \ (Finset.Icc 1 N \ PionCompleteness.Paper.Combinatorics.Polygons.reachPiece N P Q τ))
-/
#guard_msgs in
#check PionCompleteness.Paper.shortening_core
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.shortening_spread_separator {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
  {S : Finset (ℕ × ℕ)} {P QX : ℕ × ℕ} (hP : P ∈ PionCompleteness.PionZeros.oddDiagonals N)
  (hlinked : PionCompleteness.Pi.NoFreeSep N S (PionCompleteness.Pi.tailStart P) (PionCompleteness.Pi.tailLen N P) 1)
  {Θ : Finset ℕ}
  (hΘ : Θ ∈ PionCompleteness.Pi.admSeps N (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P) 0)
  (hΘe : ∀ θ ∈ Θ, θ % 2 = 0)
  (hΘd :
    Disjoint (PionCompleteness.Pi.sepIn N (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P) Θ)
      (PionCompleteness.Pi.missing N S))
  {X Y : Finset ℕ} (hX : PionCompleteness.Paper.Combinatorics.Polygons.IsOccupiedRun N S P Θ X)
  (hY : PionCompleteness.Paper.Combinatorics.Polygons.IsOccupiedRun N S P Θ Y)
  (hXY :
    ∀ x ∈ X,
      ∀ y ∈ Y,
        PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart P) x <
          PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart P) y)
  {y0 : ℕ} (hy0 : y0 ∈ Y)
  (hy0f :
    ∀ y ∈ Y,
      PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart P) y0 ≤
        PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart P) y)
  (hQX : QX ∈ PionCompleteness.PionZeros.oddDiagonals N) (hQXX : PionCompleteness.Pi.oddSide N QX = X) {τ : Finset ℕ}
  (hτ : τ ∈ PionCompleteness.Pi.admSeps N (PionCompleteness.Pi.tailStart QX) (PionCompleteness.Pi.tailLen N QX) 1)
  (hτd :
    Disjoint (PionCompleteness.Pi.sepIn N (PionCompleteness.Pi.tailStart QX) (PionCompleteness.Pi.tailLen N QX) τ)
      (PionCompleteness.Pi.missing N S))
  (hnr : y0 ∉ Finset.Icc 1 N \ PionCompleteness.Paper.Combinatorics.Polygons.reachPiece N P QX τ) :
  Θ \ (Finset.Icc 1 N \ PionCompleteness.Paper.Combinatorics.Polygons.reachPiece N P QX τ) ∈
      PionCompleteness.Pi.admSeps N (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P) 0 ∧
    (∀ θ ∈ Θ \ (Finset.Icc 1 N \ PionCompleteness.Paper.Combinatorics.Polygons.reachPiece N P QX τ), θ % 2 = 0) ∧
      Disjoint
          (PionCompleteness.Pi.sepIn N (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P)
            (Θ \ (Finset.Icc 1 N \ PionCompleteness.Paper.Combinatorics.Polygons.reachPiece N P QX τ)))
          (PionCompleteness.Pi.missing N S) ∧
        Θ \ (Finset.Icc 1 N \ PionCompleteness.Paper.Combinatorics.Polygons.reachPiece N P QX τ) ⊂ Θ ∧
          (∀ x ∈ X,
              ∀ y ∈ Y,
                ¬PionCompleteness.Pi.SameRun N (PionCompleteness.Pi.headStart P)
                    (Θ \ (Finset.Icc 1 N \ PionCompleteness.Paper.Combinatorics.Polygons.reachPiece N P QX τ)) x y) ∧
            PionCompleteness.Paper.Combinatorics.Polygons.IsSpread N S P
              (Θ \ (Finset.Icc 1 N \ PionCompleteness.Paper.Combinatorics.Polygons.reachPiece N P QX τ))
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.shortening_spread_separator
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.shortening_spread_separator_mirror {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
  {S : Finset (ℕ × ℕ)} {P QY : ℕ × ℕ} (hP : P ∈ PionCompleteness.PionZeros.oddDiagonals N)
  (hlinked : PionCompleteness.Pi.NoFreeSep N S (PionCompleteness.Pi.tailStart P) (PionCompleteness.Pi.tailLen N P) 1)
  {Θ : Finset ℕ}
  (hΘ : Θ ∈ PionCompleteness.Pi.admSeps N (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P) 0)
  (hΘe : ∀ θ ∈ Θ, θ % 2 = 0)
  (hΘd :
    Disjoint (PionCompleteness.Pi.sepIn N (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P) Θ)
      (PionCompleteness.Pi.missing N S))
  {X Y : Finset ℕ} (hX : PionCompleteness.Paper.Combinatorics.Polygons.IsOccupiedRun N S P Θ X)
  (hY : PionCompleteness.Paper.Combinatorics.Polygons.IsOccupiedRun N S P Θ Y)
  (hXY :
    ∀ x ∈ X,
      ∀ y ∈ Y,
        PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart P) x <
          PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart P) y)
  {x1 : ℕ} (hx1 : x1 ∈ X)
  (hx1l :
    ∀ x ∈ X,
      PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart P) x ≤
        PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart P) x1)
  (hQY : QY ∈ PionCompleteness.PionZeros.oddDiagonals N) (hQYY : PionCompleteness.Pi.oddSide N QY = Y) {σ : Finset ℕ}
  (hσ : σ ∈ PionCompleteness.Pi.admSeps N (PionCompleteness.Pi.tailStart QY) (PionCompleteness.Pi.tailLen N QY) 1)
  (hσd :
    Disjoint (PionCompleteness.Pi.sepIn N (PionCompleteness.Pi.tailStart QY) (PionCompleteness.Pi.tailLen N QY) σ)
      (PionCompleteness.Pi.missing N S))
  (hnr : x1 ∉ Finset.Icc 1 N \ PionCompleteness.Paper.Combinatorics.Polygons.reachPiece N P QY σ) :
  Θ \ (Finset.Icc 1 N \ PionCompleteness.Paper.Combinatorics.Polygons.reachPiece N P QY σ) ∈
      PionCompleteness.Pi.admSeps N (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P) 0 ∧
    (∀ θ ∈ Θ \ (Finset.Icc 1 N \ PionCompleteness.Paper.Combinatorics.Polygons.reachPiece N P QY σ), θ % 2 = 0) ∧
      Disjoint
          (PionCompleteness.Pi.sepIn N (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P)
            (Θ \ (Finset.Icc 1 N \ PionCompleteness.Paper.Combinatorics.Polygons.reachPiece N P QY σ)))
          (PionCompleteness.Pi.missing N S) ∧
        Θ \ (Finset.Icc 1 N \ PionCompleteness.Paper.Combinatorics.Polygons.reachPiece N P QY σ) ⊂ Θ ∧
          (∀ x ∈ X,
              ∀ y ∈ Y,
                ¬PionCompleteness.Pi.SameRun N (PionCompleteness.Pi.headStart P)
                    (Θ \ (Finset.Icc 1 N \ PionCompleteness.Paper.Combinatorics.Polygons.reachPiece N P QY σ)) x y) ∧
            PionCompleteness.Paper.Combinatorics.Polygons.IsSpread N S P
              (Θ \ (Finset.Icc 1 N \ PionCompleteness.Paper.Combinatorics.Polygons.reachPiece N P QY σ))
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.shortening_spread_separator_mirror
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.unlinked_side_has_smaller_linked_chord {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
  {S : Finset (ℕ × ℕ)} (hF : PionCompleteness.Paper.NLSM.Zeros.IsCandidateSet N S) {P Q : ℕ × ℕ}
  (hP : P ∈ PionCompleteness.Pi.goodTail N S) (hQ : Q ∈ PionCompleteness.Pi.poleChords N S)
  (hsub : PionCompleteness.Pi.oddSide N Q ⊆ PionCompleteness.Pi.oddSide N P)
  (hoo : PionCompleteness.Pi.innerOO N S Q = PionCompleteness.Pi.innerOO N S P) {x : ℕ}
  (hx : {x} ∈ PionCompleteness.Pi.admSeps N (PionCompleteness.Pi.headStart Q) (PionCompleteness.Pi.headLen N Q) 0)
  (hx2 : x % 2 = 1)
  (hxd :
    Disjoint (PionCompleteness.Pi.sepIn N (PionCompleteness.Pi.headStart Q) (PionCompleteness.Pi.headLen N Q) {x})
      (PionCompleteness.Pi.missing N S))
  (hpair :
    ∃ p ∈ PionCompleteness.Pi.innerOO N S Q,
      PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart Q) x ≤
          PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart Q) p.1 ∧
        PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart Q) x ≤
          PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart Q) p.2) :
  ∃ Z ∈ PionCompleteness.Pi.goodTail N S,
    PionCompleteness.Pi.oddSide N Z ⊆
        {z ∈ PionCompleteness.Pi.oddSide N P |
          PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart P) x ≤
            PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart P) z} ∧
      {z ∈ PionCompleteness.Pi.oddSide N P |
          PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart P) x ≤
            PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart P) z} ⊂
        PionCompleteness.Pi.oddSide N P
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.unlinked_side_has_smaller_linked_chord
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.unlinked_side_has_smaller_linked_chord_mirror {N : ℕ} (hN : 6 ≤ N)
  (hE : Even N) {S : Finset (ℕ × ℕ)} (hF : PionCompleteness.Paper.NLSM.Zeros.IsCandidateSet N S) {P Q : ℕ × ℕ}
  (hP : P ∈ PionCompleteness.Pi.goodTail N S) (hQ : Q ∈ PionCompleteness.Pi.poleChords N S)
  (hsub : PionCompleteness.Pi.oddSide N Q ⊆ PionCompleteness.Pi.oddSide N P)
  (hoo : PionCompleteness.Pi.innerOO N S Q = PionCompleteness.Pi.innerOO N S P) {x : ℕ}
  (hx : {x} ∈ PionCompleteness.Pi.admSeps N (PionCompleteness.Pi.headStart Q) (PionCompleteness.Pi.headLen N Q) 0)
  (hx2 : x % 2 = 1)
  (hxd :
    Disjoint (PionCompleteness.Pi.sepIn N (PionCompleteness.Pi.headStart Q) (PionCompleteness.Pi.headLen N Q) {x})
      (PionCompleteness.Pi.missing N S))
  (hpair :
    ∃ p ∈ PionCompleteness.Pi.innerOO N S Q,
      PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart Q) p.1 ≤
          PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart Q) x ∧
        PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart Q) p.2 ≤
          PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart Q) x) :
  ∃ Z ∈ PionCompleteness.Pi.goodTail N S,
    PionCompleteness.Pi.oddSide N Z ⊆
        {z ∈ PionCompleteness.Pi.oddSide N P |
          PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart P) z ≤
            PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart P) x} ∧
      {z ∈ PionCompleteness.Pi.oddSide N P |
          PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart P) z ≤
            PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart P) x} ⊂
        PionCompleteness.Pi.oddSide N P
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.unlinked_side_has_smaller_linked_chord_mirror
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.no_odd_singleton_separator {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
  {S : Finset (ℕ × ℕ)} (hF : PionCompleteness.Paper.NLSM.Zeros.IsCandidateSet N S) {P : ℕ × ℕ}
  (hP : PionCompleteness.Pi.IsInnermostChord N S P) {Q : ℕ × ℕ} (hQ : Q ∈ PionCompleteness.Pi.hitClass N S P) {x : ℕ}
  (hx : {x} ∈ PionCompleteness.Pi.admSeps N (PionCompleteness.Pi.headStart Q) (PionCompleteness.Pi.headLen N Q) 0)
  (hx2 : x % 2 = 1) :
  ¬Disjoint (PionCompleteness.Pi.sepIn N (PionCompleteness.Pi.headStart Q) (PionCompleteness.Pi.headLen N Q) {x})
      (PionCompleteness.Pi.missing N S)
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.no_odd_singleton_separator
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.thin_runs {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {S : Finset (ℕ × ℕ)}
  (hF : PionCompleteness.Paper.NLSM.Zeros.IsCandidateSet N S) {P Q : ℕ × ℕ} (hP : P ∈ PionCompleteness.Pi.goodTail N S)
  (hQ : Q ∈ PionCompleteness.Pi.cleanChords N S)
  (hsub : PionCompleteness.Pi.oddSide N Q ⊂ PionCompleteness.Pi.oddSide N P)
  (hoo : PionCompleteness.Pi.innerOO N S Q = PionCompleteness.Pi.innerOO N S P) {τ : Finset ℕ}
  (hτ : τ ∈ PionCompleteness.Pi.admSeps N (PionCompleteness.Pi.tailStart Q) (PionCompleteness.Pi.tailLen N Q) 1)
  (hτd :
    Disjoint (PionCompleteness.Pi.sepIn N (PionCompleteness.Pi.tailStart Q) (PionCompleteness.Pi.tailLen N Q) τ)
      (PionCompleteness.Pi.missing N S)) :
  (∀ t ∈ τ, t % 2 = 1) ∧
    ∃ R,
      PionCompleteness.Paper.Combinatorics.Polygons.IsRunOf N (PionCompleteness.Pi.tailStart Q)
          (PionCompleteness.Pi.evenSide N Q) τ R ∧
        PionCompleteness.Pi.evenSide N P ⊆ R ∧
          (∀ (Z : Finset ℕ),
              PionCompleteness.Paper.Combinatorics.Polygons.IsRunOf N (PionCompleteness.Pi.tailStart Q)
                  (PionCompleteness.Pi.evenSide N Q) τ Z →
                Z ≠ R → ∃ e, e % 2 = 0 ∧ Z = {e}) ∧
            ((PionCompleteness.Pi.innerEE N S Q).Nonempty →
              ∃ Qp ∈ PionCompleteness.Pi.poleChords N S,
                PionCompleteness.Pi.evenSide N Qp = R ∧
                  PionCompleteness.Pi.innerOO N S Qp = PionCompleteness.Pi.innerOO N S P ∧
                    PionCompleteness.Pi.hitSet N S Qp = PionCompleteness.Pi.hitSet N S Q ∧
                      PionCompleteness.Pi.oddSide N Q ⊂ PionCompleteness.Pi.oddSide N Qp ∧
                        PionCompleteness.Pi.oddSide N Qp ⊆ PionCompleteness.Pi.oddSide N P)
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.thin_runs
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.spread_separator_passes_to_innermost_chord {N : ℕ} (hN : 6 ≤ N)
  (hE : Even N) {S : Finset (ℕ × ℕ)} {P Ps : ℕ × ℕ} (hP : P ∈ PionCompleteness.Pi.cleanChords N S)
  (hPs : Ps ∈ PionCompleteness.PionZeros.oddDiagonals N)
  (hsub : PionCompleteness.Pi.oddSide N P ⊆ PionCompleteness.Pi.oddSide N Ps)
  (hoo : PionCompleteness.Pi.innerOO N S Ps ⊆ PionCompleteness.Pi.innerOO N S P) {Θ : Finset ℕ}
  (hΘ : Θ ∈ PionCompleteness.Pi.admSeps N (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P) 0)
  (hΘe : ∀ θ ∈ Θ, θ % 2 = 0)
  (hΘd :
    Disjoint (PionCompleteness.Pi.sepIn N (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P) Θ)
      (PionCompleteness.Pi.missing N S))
  (hsp : PionCompleteness.Paper.Combinatorics.Polygons.IsSpread N S P Θ) :
  Θ ∪ PionCompleteness.Pi.evens (PionCompleteness.Pi.oddSide N Ps \ PionCompleteness.Pi.oddSide N P) ∈
      PionCompleteness.Pi.admSeps N (PionCompleteness.Pi.headStart Ps) (PionCompleteness.Pi.headLen N Ps) 0 ∧
    (∀ θ ∈ Θ ∪ PionCompleteness.Pi.evens (PionCompleteness.Pi.oddSide N Ps \ PionCompleteness.Pi.oddSide N P),
        θ % 2 = 0) ∧
      Disjoint
          (PionCompleteness.Pi.sepIn N (PionCompleteness.Pi.headStart Ps) (PionCompleteness.Pi.headLen N Ps)
            (Θ ∪ PionCompleteness.Pi.evens (PionCompleteness.Pi.oddSide N Ps \ PionCompleteness.Pi.oddSide N P)))
          (PionCompleteness.Pi.missing N S) ∧
        PionCompleteness.Paper.Combinatorics.Polygons.IsSpread N S Ps
          (Θ ∪ PionCompleteness.Pi.evens (PionCompleteness.Pi.oddSide N Ps \ PionCompleteness.Pi.oddSide N P))
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.spread_separator_passes_to_innermost_chord
/--
info: PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.chord_formula {N : ℕ} (hN : 4 ≤ N) (hE : Even N) {S : Finset (ℕ × ℕ)}
  (hS : S ⊆ PionCompleteness.TreeRectangleZero.diagonals N) {P : ℕ × ℕ}
  (hP : P ∈ PionCompleteness.PionZeros.oddDiagonals N) (X : ℕ × ℕ → ℚ)
  (hX : PionCompleteness.ChainSlice.OnLocus N S X) :
  X P =
    ∑ t ∈ PionCompleteness.Pi.hitSet N S P, PionCompleteness.TreeRectangleZero.mesh N X t.1 t.2 -
      PionCompleteness.Pi.pkGE N X
-/
#guard_msgs in
#check PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.chord_formula
/--
info: PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.proportional_odd_chords_share_missing_flank_set {N : ℕ} (hN : 6 ≤ N)
  (hE : Even N) {S : Finset (ℕ × ℕ)} (hF : PionCompleteness.Paper.NLSM.Zeros.IsCandidateSet N S) {P Q : ℕ × ℕ}
  (hP : P ∈ PionCompleteness.Pi.poleChords N S) (hQ : Q ∈ PionCompleteness.PionZeros.oddDiagonals N) :
  ((∃ c, c ≠ 0 ∧ ∀ (X : ℕ × ℕ → ℚ), PionCompleteness.ChainSlice.OnLocus N S X → X Q = c * X P) ↔
      PionCompleteness.Pi.hitSet N S Q = PionCompleteness.Pi.hitSet N S P) ∧
    ∀ (c : ℚ),
      c ≠ 0 →
        (∀ (X : ℕ × ℕ → ℚ), PionCompleteness.ChainSlice.OnLocus N S X → X Q = c * X P) →
          c = 1 ∧ Q ∈ PionCompleteness.Pi.poleChords N S
-/
#guard_msgs in
#check
  PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.proportional_odd_chords_share_missing_flank_set
/--
info: PionCompleteness.Paper.Combinatorics.SetSystems.separated_pair_family_is_antichain {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
  {Z Z' : Finset (ℕ × ℕ)} (hZ : PionCompleteness.Paper.NLSM.Zeros.Families.IsListMember N Z)
  (hZ' : PionCompleteness.Paper.NLSM.Zeros.Families.IsListMember N Z') (h : Z ⊆ Z') : Z = Z'
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.SetSystems.separated_pair_family_is_antichain
/--
info: PionCompleteness.Paper.NLSM.FeynmanRules.quartic_rules_give_nlsm {N π : ℕ} (hN : 4 ≤ N) (hE : Even N) (hπ : π < 2) :
  PionCompleteness.PionZeros.Qpi N π PionCompleteness.PionNLSM.gen =
    (-1) ^ (N / 2 - 1) * PionCompleteness.PionNLSM.NLSM N PionCompleteness.PionNLSM.gen
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.FeynmanRules.quartic_rules_give_nlsm
/--
info: def PionCompleteness.Paper.HasWideGap : Finset ℕ → Finset ℕ → Prop :=
fun K Θ => ∃ a ∈ K, ∃ b ∈ K, a < b ∧ (∀ k ∈ K, ¬(a < k ∧ k < b)) ∧ 2 ≤ {x ∈ Θ | a < x ∧ x < b}.card
-/
#guard_msgs in
#print PionCompleteness.Paper.HasWideGap
/--
info: def PionCompleteness.Paper.CaseEP : ℕ → ℕ → ℕ → ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Prop :=
fun x0 x1 y0 y1 Θ τ σ =>
  (∀ t ∈ τ, t % 2 = 1) ∧
    (∀ s ∈ σ, s % 2 = 1) ∧
      (PionCompleteness.Paper.HasWideGap (Finset.Icc x0 x1 ∪ τ) Θ ∨
        PionCompleteness.Paper.HasWideGap (Finset.Icc y0 y1 ∪ σ) Θ)
-/
#guard_msgs in
#print PionCompleteness.Paper.CaseEP
/--
info: def PionCompleteness.Paper.PX : ℕ → Finset ℕ → Prop :=
fun x0 σ => Disjoint σ (Finset.Icc 1 x0)
-/
#guard_msgs in
#print PionCompleteness.Paper.PX
/--
info: def PionCompleteness.Paper.PY : ℕ → ℕ → Finset ℕ → Prop :=
fun ω y1 τ => Disjoint τ (Finset.Icc y1 ω)
-/
#guard_msgs in
#print PionCompleteness.Paper.PY
/--
info: def PionCompleteness.Paper.RemovedTau : ℕ → ℕ → ℕ → Finset ℕ → Finset ℕ → ℕ → Prop :=
fun ω x0 y1 Θ σ t =>
  t < x0 ∧
      Disjoint σ (Finset.Icc t x0) ∧ (PionCompleteness.Paper.PX x0 σ ∨ ∃ θ ∈ Θ, θ < t ∧ Disjoint σ (Finset.Icc θ x0)) ∨
    y1 < t ∧ PionCompleteness.Paper.PX x0 σ ∧ ∃ θ ∈ Θ, y1 < θ ∧ θ < t ∧ Disjoint σ (Finset.Icc θ ω)
-/
#guard_msgs in
#print PionCompleteness.Paper.RemovedTau
/--
info: def PionCompleteness.Paper.RemovedSigma : ℕ → ℕ → ℕ → Finset ℕ → Finset ℕ → ℕ → Prop :=
fun ω x0 y1 Θ τ s =>
  y1 < s ∧
      Disjoint τ (Finset.Icc y1 s) ∧
        (PionCompleteness.Paper.PY ω y1 τ ∨ ∃ θ ∈ Θ, s < θ ∧ Disjoint τ (Finset.Icc y1 θ)) ∨
    s < x0 ∧ PionCompleteness.Paper.PY ω y1 τ ∧ ∃ θ ∈ Θ, s < θ ∧ θ < x0 ∧ Disjoint τ (Finset.Icc 1 θ)
-/
#guard_msgs in
#print PionCompleteness.Paper.RemovedSigma
/--
info: def PionCompleteness.Paper.zoneSet : ℕ → ℕ → ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ :=
fun ω x0 y1 Θ τ σ =>
  {t ∈ τ | ¬PionCompleteness.Paper.RemovedTau ω x0 y1 Θ σ t} ∪
    {s ∈ σ | ¬PionCompleteness.Paper.RemovedSigma ω x0 y1 Θ τ s}
-/
#guard_msgs in
#print PionCompleteness.Paper.zoneSet

-- Library definitions of the three-cut setting: `ThreeSepSetting` and its parts (runs, the interior
-- of `B_X`, admissible and W-avoiding separators), the separated-pair sets `𝒞_A` and `𝒞`, the
-- single-family witnesses `ConsecWit`, and the flank class `hitClass` (`K*`).
/--
info: def PionCompleteness.Pi.prevLeg : ℕ → ℕ → ℕ :=
fun N a => if a = 1 then N else a - 1
-/
#guard_msgs in
#print PionCompleteness.Pi.prevLeg
/--
info: def PionCompleteness.Pi.IsRun : ℕ → Finset ℕ → ℕ → ℕ → Prop :=
fun ω Θ a b => 1 ≤ a ∧ a ≤ b ∧ b ≤ ω ∧ (a = 1 ∨ a - 1 ∈ Θ) ∧ (b = ω ∨ b + 1 ∈ Θ) ∧ ∀ w ∈ Finset.Icc a b, w ∉ Θ
-/
#guard_msgs in
#print PionCompleteness.Pi.IsRun
/--
info: def PionCompleteness.Pi.intCompl : ℕ → ℕ → ℕ → Finset ℕ :=
fun N a b => Finset.Icc 1 N \ (Finset.Icc a b ∪ {b + 1, PionCompleteness.Pi.prevLeg N a})
-/
#guard_msgs in
#print PionCompleteness.Pi.intCompl
/--
info: def PionCompleteness.Pi.AdmSepCompl : ℕ → ℕ → ℕ → Finset ℕ → Prop :=
fun N a b τ =>
  (∃ t ∈ PionCompleteness.Pi.intCompl N a b, τ = {t}) ∨
    2 ≤ τ.card ∧ τ ⊆ PionCompleteness.Pi.intCompl N a b ∧ ∀ t ∈ τ, t % 2 = 1
-/
#guard_msgs in
#print PionCompleteness.Pi.AdmSepCompl
/--
info: def PionCompleteness.Pi.TailAvoiding : ℕ → ℕ → Finset ℕ → Prop :=
fun N ω τ => Disjoint τ (Finset.Icc (ω + 2) (N - 1)) ∧ ((∀ t ∈ τ, t % 2 = 1) → Disjoint τ (Finset.Icc (ω + 1) N))
-/
#guard_msgs in
#print PionCompleteness.Pi.TailAvoiding
/--
info: def PionCompleteness.Pi.ThreeSepSetting : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Prop :=
fun N ω x0 x1 y0 y1 Θ τ σ =>
  N % 2 = 0 ∧
    ω % 2 = 1 ∧
      ω + 3 ≤ N ∧
        Θ.Nonempty ∧
          Θ ⊆ Finset.Icc 2 (ω - 1) ∧
            (∀ θ ∈ Θ, θ % 2 = 0) ∧
              PionCompleteness.Pi.IsRun ω Θ x0 x1 ∧
                PionCompleteness.Pi.IsRun ω Θ y0 y1 ∧
                  x1 < y0 ∧
                    x0 + 2 ≤ x1 ∧
                      y0 + 2 ≤ y1 ∧
                        PionCompleteness.Pi.AdmSepCompl N x0 x1 τ ∧
                          PionCompleteness.Pi.AdmSepCompl N y0 y1 σ ∧
                            PionCompleteness.Pi.TailAvoiding N ω τ ∧
                              PionCompleteness.Pi.TailAvoiding N ω σ ∧
                                (y0 ∈ τ ∨ PionCompleteness.PionZeros.InST (Finset.Icc x0 x1 ∪ τ) y0 (ω + 2)) ∧
                                  (x1 ∈ σ ∨ PionCompleteness.PionZeros.InST (Finset.Icc y0 y1 ∪ σ) x1 (ω + 2))
-/
#guard_msgs in
#print PionCompleteness.Pi.ThreeSepSetting
/--
info: def PionCompleteness.Pi.runSepA : ℕ → Finset ℕ → ℕ → ℕ → Prop :=
fun ω Θ u v => u ∈ Finset.Icc 1 ω ∧ v ∈ Finset.Icc 1 ω ∧ u ∉ Θ ∧ v ∉ Θ ∧ ∃ θ ∈ Θ, min u v < θ ∧ θ < max u v
-/
#guard_msgs in
#print PionCompleteness.Pi.runSepA
/--
info: def PionCompleteness.Pi.threeSepCut : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset (ℕ × ℕ) :=
fun N ω x0 x1 y0 y1 Θ τ σ =>
  {p ∈ PionCompleteness.TreeRectangleZero.diagonals N |
    PionCompleteness.Pi.runSepA ω Θ p.1 p.2 ∨
      PionCompleteness.PionZeros.InST (Finset.Icc x0 x1 ∪ τ) p.1 p.2 ∨
        PionCompleteness.PionZeros.InST (Finset.Icc y0 y1 ∪ σ) p.1 p.2}
-/
#guard_msgs in
#print PionCompleteness.Pi.threeSepCut
/--
info: def PionCompleteness.Pi.ConsecWit : ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Prop :=
fun N Θ τ σ G =>
  2 ≤ G.card ∧
    ∃ a ∈ Finset.Icc 1 N,
      ∃ len ∈ Finset.range (N + 1),
        G = PionCompleteness.Pi.evens (Θ ∪ τ ∪ σ) ∩ PionCompleteness.Pi.cycArc N a len ∨
          G = PionCompleteness.Pi.odds (τ ∪ σ) ∩ PionCompleteness.Pi.cycArc N a len
-/
#guard_msgs in
#print PionCompleteness.Pi.ConsecWit
/--
info: def PionCompleteness.Pi.hitClass : ℕ → Finset (ℕ × ℕ) → ℕ × ℕ → Finset (ℕ × ℕ) :=
fun N S P =>
  {Q ∈ PionCompleteness.Pi.poleChords N S | PionCompleteness.Pi.hitSet N S Q = PionCompleteness.Pi.hitSet N S P}
-/
#guard_msgs in
#print PionCompleteness.Pi.hitClass
/--
info: def PionCompleteness.Pi.SameRun : ℕ → ℕ → Finset ℕ → ℕ → ℕ → Prop :=
fun N s Θ u v =>
  ¬∃ θ ∈ Θ,
      min (PionCompleteness.Pi.cycPos N s u) (PionCompleteness.Pi.cycPos N s v) < PionCompleteness.Pi.cycPos N s θ ∧
        PionCompleteness.Pi.cycPos N s θ < max (PionCompleteness.Pi.cycPos N s u) (PionCompleteness.Pi.cycPos N s v)
-/
#guard_msgs in
#print PionCompleteness.Pi.SameRun
/--
info: def PionCompleteness.Pi.InOneRun : ℕ → ℕ → ℕ → Finset ℕ → ℕ × ℕ → Prop :=
fun N s k Θ p =>
  p.1 ∈ PionCompleteness.Pi.cycArc N s k ∧
    p.2 ∈ PionCompleteness.Pi.cycArc N s k ∧ p.1 ∉ Θ ∧ p.2 ∉ Θ ∧ PionCompleteness.Pi.SameRun N s Θ p.1 p.2
-/
#guard_msgs in
#print PionCompleteness.Pi.InOneRun
/--
info: def PionCompleteness.Pi.Spread : ℕ → Finset (ℕ × ℕ) → ℕ → ℕ → Finset ℕ → Prop :=
fun N S s k Θ =>
  ∃ p ∈ PionCompleteness.Pi.Moo N S,
    ∃ p' ∈ PionCompleteness.Pi.Moo N S,
      PionCompleteness.Pi.InOneRun N s k Θ p ∧
        PionCompleteness.Pi.InOneRun N s k Θ p' ∧ ¬PionCompleteness.Pi.SameRun N s Θ p.1 p'.1
-/
#guard_msgs in
#print PionCompleteness.Pi.Spread
/--
info: def PionCompleteness.Pi.EvenTopP : ℕ → Finset (ℕ × ℕ) → ℕ × ℕ → Prop :=
fun N S P =>
  ∀ Θ ∈ PionCompleteness.Pi.admSeps N (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P) 0,
    (∀ θ ∈ Θ, θ % 2 = 0) →
      Disjoint (PionCompleteness.Pi.sepIn N (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P) Θ)
          (PionCompleteness.Pi.missing N S) →
        ¬PionCompleteness.Pi.Spread N S (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P) Θ
-/
#guard_msgs in
#print PionCompleteness.Pi.EvenTopP

-- `Paper`, continued: the class residue in the paper's language: the predicates "has no pole
-- along `H`" and "restricts to zero on `H`" for rational functions on `L_S`, the amplitude avoiding
-- a set of chords and its numerator lemma, the hypotheses of the residue theorem
-- (`FlankClassPoleHypotheses`, `H`, `d`, `a_t`, `b_b`) with `K = hitClass`, its derived remark, the
-- remark on `K*`, the parts `a_Q`, `b_Q` and the strip factor `φ`, the extreme term
-- (`only_extreme_term_survives`), and the helpers they use.
/--
info: def PionCompleteness.Paper.NLSM.Amplitude.HasNoPoleAlong : Set (ℕ × ℕ → ℚ) →
  Set (ℕ × ℕ → ℚ) → PionCompleteness.PionNLSM.RF → Prop :=
fun V H f =>
  ∃ P D,
    PionCompleteness.PionNLSM.RatZeroOn V
        (f * (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) D -
          (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) P) ∧
      ∃ w ∈ H, (MvPolynomial.eval w) D ≠ 0
-/
#guard_msgs in
#print PionCompleteness.Paper.NLSM.Amplitude.HasNoPoleAlong
/--
info: def PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong : Set (ℕ × ℕ → ℚ) →
  Set (ℕ × ℕ → ℚ) → PionCompleteness.PionNLSM.RF → Prop :=
fun V H f =>
  ∃ P D,
    PionCompleteness.PionNLSM.RatZeroOn V
        (f * (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) D -
          (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) P) ∧
      (∃ w ∈ H, (MvPolynomial.eval w) D ≠ 0) ∧ ∀ x ∈ H, (MvPolynomial.eval x) P = 0
-/
#guard_msgs in
#print PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong
/--
info: PionCompleteness.Paper.hasNoPoleAlong_of_eq {V H : Set (ℕ × ℕ → ℚ)} (hV : (fun x => 0) ∈ V)
  {f : PionCompleteness.PionNLSM.RF} {P D : MvPolynomial (ℕ × ℕ) ℚ}
  (hf :
    f * (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) D =
      (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) P)
  (hD : ∃ w ∈ H, (MvPolynomial.eval w) D ≠ 0) : PionCompleteness.Paper.NLSM.Amplitude.HasNoPoleAlong V H f
-/
#guard_msgs in
#check PionCompleteness.Paper.hasNoPoleAlong_of_eq
/--
info: PionCompleteness.Paper.restrictsToZeroAlong_of_eq {V H : Set (ℕ × ℕ → ℚ)} (hV : (fun x => 0) ∈ V)
  {f : PionCompleteness.PionNLSM.RF} {P D : MvPolynomial (ℕ × ℕ) ℚ}
  (hf :
    f * (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) D =
      (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) P)
  (hD : ∃ w ∈ H, (MvPolynomial.eval w) D ≠ 0) (hP : ∀ x ∈ H, (MvPolynomial.eval x) P = 0) :
  PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong V H f
-/
#guard_msgs in
#check PionCompleteness.Paper.restrictsToZeroAlong_of_eq
/--
info: PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong.hasNoPoleAlong {V H : Set (ℕ × ℕ → ℚ)}
  {f : PionCompleteness.PionNLSM.RF} (h : PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong V H f) :
  PionCompleteness.Paper.NLSM.Amplitude.HasNoPoleAlong V H f
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong.hasNoPoleAlong
/--
info: def PionCompleteness.Paper.ampAvoiding.{u_1} : {F : Type u_1} → [Field F] → ℕ → Finset (ℕ × ℕ) → (ℕ × ℕ → F) → F :=
fun {F} [Field F] n K X => ∑ T ∈ PionCompleteness.TreeRectangleZero.triangulations n with Disjoint T K, ∏ d ∈ T, (X d)⁻¹
-/
#guard_msgs in
#print PionCompleteness.Paper.ampAvoiding
/--
info: def PionCompleteness.Paper.NLSM.Amplitude.nlsmAvoiding.{u_1} : {F : Type u_1} →
  [Field F] → ℕ → Finset (ℕ × ℕ) → (ℕ × ℕ → F) → F :=
fun {F} [Field F] n K X => (PionCompleteness.Paper.ampAvoiding n K (PionCompleteness.PionNLSM.shifted X)).coeff (↑n - 2)
-/
#guard_msgs in
#print PionCompleteness.Paper.NLSM.Amplitude.nlsmAvoiding
/--
info: PionCompleteness.Paper.nlsmAvoiding_empty.{u_1} {F : Type u_1} [Field F] (n : ℕ) (X : ℕ × ℕ → F) :
  PionCompleteness.Paper.NLSM.Amplitude.nlsmAvoiding n ∅ X = PionCompleteness.PionNLSM.NLSM n X
-/
#guard_msgs in
#check PionCompleteness.Paper.nlsmAvoiding_empty
/--
info: PionCompleteness.Paper.nlsmAvoiding_numerator_hom.{u_1} {F : Type u_1} [Field F] (f : MvPolynomial (ℕ × ℕ) ℚ →+* F)
  {n : ℕ} (hn : 2 ≤ n) (K : Finset (ℕ × ℕ))
  (hX : ∀ d ∈ PionCompleteness.PionZeros.oddDiagonals n \ K, f (MvPolynomial.X d) ≠ 0) :
  f (PionCompleteness.Pi.pkRBNP ℚ n K) =
    (PionCompleteness.Paper.NLSM.Amplitude.nlsmAvoiding n K fun d => f (MvPolynomial.X d)) *
      ∏ d ∈ PionCompleteness.PionZeros.oddDiagonals n \ K, f (MvPolynomial.X d)
-/
#guard_msgs in
#check PionCompleteness.Paper.nlsmAvoiding_numerator_hom
/--
info: structure PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses (N : ℕ) (S K : Finset (ℕ × ℕ))
  (P t b : ℕ × ℕ) : Prop
number of parameters: 6
fields:
  PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses.candidate : PionCompleteness.Paper.NLSM.Zeros.IsCandidateSet
      N S
  PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses.odd : K ⊆ PionCompleteness.PionZeros.oddDiagonals N
  PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses.mem : P ∈ K
  PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses.h1 : ∀ Q ∈ PionCompleteness.PionZeros.oddDiagonals N,
      ∃ X, PionCompleteness.ChainSlice.OnLocus N S X ∧ X Q ≠ 0
  PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses.h2 : ∀ Q ∈ PionCompleteness.PionZeros.oddDiagonals N,
      Q ∈ K ↔ ∃ c, c ≠ 0 ∧ ∀ (X : ℕ × ℕ → ℚ), PionCompleteness.ChainSlice.OnLocus N S X → X Q = c * X P
  PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses.h2' : ∀ Q ∈ K,
      ∀ (X : ℕ × ℕ → ℚ), PionCompleteness.ChainSlice.OnLocus N S X → X Q = X P
  PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses.h3 : K ⊆ PionCompleteness.Pi.poleChords N S
  PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses.h3' : ∀ Q ∈ K,
      ∀ Q' ∈ K, PionCompleteness.Pi.hitSet N S Q = PionCompleteness.Pi.hitSet N S Q'
  PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses.top : t ∈ K ∧
      ∀ Q ∈ K, PionCompleteness.Pi.oddSide N Q ⊆ PionCompleteness.Pi.oddSide N t
  PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses.bottom : b ∈ K ∧
      ∀ Q ∈ K, PionCompleteness.Pi.oddSide N b ⊆ PionCompleteness.Pi.oddSide N Q
constructor:
  PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses.mk {N : ℕ} {S K : Finset (ℕ × ℕ)} {P t b : ℕ × ℕ}
    (candidate : PionCompleteness.Paper.NLSM.Zeros.IsCandidateSet N S)
    (odd : K ⊆ PionCompleteness.PionZeros.oddDiagonals N) (mem : P ∈ K)
    (h1 : ∀ Q ∈ PionCompleteness.PionZeros.oddDiagonals N, ∃ X, PionCompleteness.ChainSlice.OnLocus N S X ∧ X Q ≠ 0)
    (h2 :
      ∀ Q ∈ PionCompleteness.PionZeros.oddDiagonals N,
        Q ∈ K ↔ ∃ c, c ≠ 0 ∧ ∀ (X : ℕ × ℕ → ℚ), PionCompleteness.ChainSlice.OnLocus N S X → X Q = c * X P)
    (h2' : ∀ Q ∈ K, ∀ (X : ℕ × ℕ → ℚ), PionCompleteness.ChainSlice.OnLocus N S X → X Q = X P)
    (h3 : K ⊆ PionCompleteness.Pi.poleChords N S)
    (h3' : ∀ Q ∈ K, ∀ Q' ∈ K, PionCompleteness.Pi.hitSet N S Q = PionCompleteness.Pi.hitSet N S Q')
    (top : t ∈ K ∧ ∀ Q ∈ K, PionCompleteness.Pi.oddSide N Q ⊆ PionCompleteness.Pi.oddSide N t)
    (bottom : b ∈ K ∧ ∀ Q ∈ K, PionCompleteness.Pi.oddSide N b ⊆ PionCompleteness.Pi.oddSide N Q) :
    PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses N S K P t b
-/
#guard_msgs in
#print PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses
/--
info: def PionCompleteness.Paper.NLSM.Amplitude.residueHyperplane : ℕ → Finset (ℕ × ℕ) → ℕ × ℕ → Set (ℕ × ℕ → ℚ) :=
fun N S P => {X | PionCompleteness.ChainSlice.OnLocus N S X ∧ X P = 0}
-/
#guard_msgs in
#print PionCompleteness.Paper.NLSM.Amplitude.residueHyperplane
/--
info: def PionCompleteness.Paper.NLSM.Amplitude.stripHalfLength : ℕ → ℕ × ℕ → ℕ × ℕ → ℕ :=
fun N t b => (PionCompleteness.Pi.headLen N t - PionCompleteness.Pi.headLen N b) / 2
-/
#guard_msgs in
#print PionCompleteness.Paper.NLSM.Amplitude.stripHalfLength
/--
info: def PionCompleteness.Paper.NLSM.Amplitude.childAmpB : ℕ → ℕ × ℕ → PionCompleteness.PionNLSM.RF :=
fun N t =>
  PionCompleteness.PionNLSM.NLSM (PionCompleteness.Pi.tailLen N t + 1) fun d =>
    PionCompleteness.PionNLSM.gen (PionCompleteness.PionNLSM.relab N (PionCompleteness.Pi.tailStart t) d)
-/
#guard_msgs in
#print PionCompleteness.Paper.NLSM.Amplitude.childAmpB
/--
info: def PionCompleteness.Paper.NLSM.Amplitude.childAmpA : ℕ → ℕ × ℕ → PionCompleteness.PionNLSM.RF :=
fun N b =>
  PionCompleteness.PionNLSM.NLSM (PionCompleteness.Pi.headLen N b + 1) fun d =>
    PionCompleteness.PionNLSM.gen (PionCompleteness.PionNLSM.relab N (PionCompleteness.Pi.headStart b) d)
-/
#guard_msgs in
#print PionCompleteness.Paper.NLSM.Amplitude.childAmpA
/--
info: PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses.eq_hitClass {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
  {S K : Finset (ℕ × ℕ)} {P t b : ℕ × ℕ}
  (h : PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses N S K P t b) :
  K = PionCompleteness.Pi.hitClass N S t
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses.eq_hitClass
/--
info: PionCompleteness.Paper.odd_chord_outside_class_nonvanishing_on_hyperplane {N : ℕ} {S K : Finset (ℕ × ℕ)} {P t b : ℕ × ℕ}
  (h : PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses N S K P t b) {Q : ℕ × ℕ}
  (hQ : Q ∈ PionCompleteness.PionZeros.oddDiagonals N) (hQK : Q ∉ K) :
  ∃ X ∈ PionCompleteness.Paper.NLSM.Amplitude.residueHyperplane N S P, X Q ≠ 0
-/
#guard_msgs in
#check PionCompleteness.Paper.odd_chord_outside_class_nonvanishing_on_hyperplane
/--
info: PionCompleteness.Paper.flank_class_pole_hypotheses_innermost {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {S : Finset (ℕ × ℕ)}
  (hF : PionCompleteness.Paper.NLSM.Zeros.IsCandidateSet N S) {P b : ℕ × ℕ}
  (hP : PionCompleteness.Pi.IsInnermostChord N S P) (hb : b ∈ PionCompleteness.Pi.hitClass N S P)
  (hbl : PionCompleteness.Pi.NoFreeSep N S (PionCompleteness.Pi.headStart b) (PionCompleteness.Pi.headLen N b) 0) :
  PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses N S (PionCompleteness.Pi.hitClass N S P) P P b
-/
#guard_msgs in
#check PionCompleteness.Paper.flank_class_pole_hypotheses_innermost
/--
info: def PionCompleteness.Paper.NLSM.Amplitude.avoidingA : ℕ → Finset (ℕ × ℕ) → ℕ × ℕ → PionCompleteness.PionNLSM.RF :=
fun N K Q =>
  PionCompleteness.Paper.NLSM.Amplitude.nlsmAvoiding (PionCompleteness.Pi.headLen N Q + 1)
    (PionCompleteness.Pi.pkRBPull N (PionCompleteness.Pi.headStart Q) (PionCompleteness.Pi.headLen N Q + 1) K) fun d =>
    PionCompleteness.PionNLSM.gen (PionCompleteness.PionNLSM.relab N (PionCompleteness.Pi.headStart Q) d)
-/
#guard_msgs in
#print PionCompleteness.Paper.NLSM.Amplitude.avoidingA
/--
info: def PionCompleteness.Paper.NLSM.Amplitude.avoidingB : ℕ → Finset (ℕ × ℕ) → ℕ × ℕ → PionCompleteness.PionNLSM.RF :=
fun N K Q =>
  PionCompleteness.Paper.NLSM.Amplitude.nlsmAvoiding (PionCompleteness.Pi.tailLen N Q + 1)
    (PionCompleteness.Pi.pkRBPull N (PionCompleteness.Pi.tailStart Q) (PionCompleteness.Pi.tailLen N Q + 1) K) fun d =>
    PionCompleteness.PionNLSM.gen (PionCompleteness.PionNLSM.relab N (PionCompleteness.Pi.tailStart Q) d)
-/
#guard_msgs in
#print PionCompleteness.Paper.NLSM.Amplitude.avoidingB
/--
info: PionCompleteness.Paper.residueHyperplane_sub (N : ℕ) (S : Finset (ℕ × ℕ)) (P : ℕ × ℕ) :
  PionCompleteness.Pi.pkRSub (PionCompleteness.Paper.NLSM.Amplitude.residueHyperplane N S P)
-/
#guard_msgs in
#check PionCompleteness.Paper.residueHyperplane_sub
/--
info: PionCompleteness.Paper.nlsmAvoiding_child_eq (N s n : ℕ) (hn : 2 ≤ n) (K : Finset (ℕ × ℕ)) :
  (PionCompleteness.Paper.NLSM.Amplitude.nlsmAvoiding n (PionCompleteness.Pi.pkRBPull N s n K) fun d =>
        PionCompleteness.PionNLSM.gen (PionCompleteness.PionNLSM.relab N s d)) *
      (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF)
        ((MvPolynomial.rename (PionCompleteness.PionNLSM.relab N s))
          (∏ d ∈ PionCompleteness.PionZeros.oddDiagonals n \ PionCompleteness.Pi.pkRBPull N s n K, MvPolynomial.X d)) =
    (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF)
      ((MvPolynomial.rename (PionCompleteness.PionNLSM.relab N s))
        (PionCompleteness.Pi.pkRBNP ℚ n (PionCompleteness.Pi.pkRBPull N s n K)))
-/
#guard_msgs in
#check PionCompleteness.Paper.nlsmAvoiding_child_eq
/--
info: PionCompleteness.Paper.child_den_nonvanishing {N : ℕ} (hE : Even N) {S K : Finset (ℕ × ℕ)} {P t b : ℕ × ℕ}
  (h : PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses N S K P t b) {s n : ℕ} (hs : 1 ≤ s ∧ s ≤ N)
  (hn : n ≤ N) :
  ∃ w ∈ PionCompleteness.Paper.NLSM.Amplitude.residueHyperplane N S P,
    (MvPolynomial.eval w)
        ((MvPolynomial.rename (PionCompleteness.PionNLSM.relab N s))
          (∏ d ∈ PionCompleteness.PionZeros.oddDiagonals n \ PionCompleteness.Pi.pkRBPull N s n K, MvPolynomial.X d)) ≠
      0
-/
#guard_msgs in
#check PionCompleteness.Paper.child_den_nonvanishing
/--
info: PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses.nested {N : ℕ} {S K : Finset (ℕ × ℕ)} {P t b : ℕ × ℕ}
  (h : PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses N S K P t b) (Q : ℕ × ℕ) :
  Q ∈ K →
    ∀ Q' ∈ K,
      ¬PionCompleteness.TreeRectangleZero.Crosses Q' Q →
        PionCompleteness.Pi.oddSide N Q ⊆ PionCompleteness.Pi.oddSide N Q' ∨
          PionCompleteness.Pi.oddSide N Q' ⊆ PionCompleteness.Pi.oddSide N Q
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses.nested
/--
info: PionCompleteness.Paper.avoidingA_restrictsToZero {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {S K : Finset (ℕ × ℕ)}
  {P t b : ℕ × ℕ} (h : PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses N S K P t b) {Q : ℕ × ℕ}
  (hQ : Q ∈ K) (hQb : Q ≠ b) :
  PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong {X | PionCompleteness.ChainSlice.OnLocus N S X}
    (PionCompleteness.Paper.NLSM.Amplitude.residueHyperplane N S P)
    (PionCompleteness.Paper.NLSM.Amplitude.avoidingA N K Q)
-/
#guard_msgs in
#check PionCompleteness.Paper.avoidingA_restrictsToZero
/--
info: PionCompleteness.Paper.avoidingB_restrictsToZero {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {S K : Finset (ℕ × ℕ)}
  {P t b : ℕ × ℕ} (h : PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses N S K P t b) {Q : ℕ × ℕ}
  (hQ : Q ∈ K) (hQt : Q ≠ t) :
  PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong {X | PionCompleteness.ChainSlice.OnLocus N S X}
    (PionCompleteness.Paper.NLSM.Amplitude.residueHyperplane N S P)
    (PionCompleteness.Paper.NLSM.Amplitude.avoidingB N K Q)
-/
#guard_msgs in
#check PionCompleteness.Paper.avoidingB_restrictsToZero
/--
info: def PionCompleteness.Paper.NLSM.Amplitude.regionAmp : ℕ → ℕ × ℕ → ℕ × ℕ → PionCompleteness.PionNLSM.RF :=
fun N Q Q' =>
  PionCompleteness.PionNLSM.NLSM (PionCompleteness.Pi.pkRBOmM N Q Q')
    (PionCompleteness.Pi.pkRSubX N
      (PionCompleteness.Pi.pkRBOmL N (PionCompleteness.Pi.headStart Q)
        (PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart Q) (PionCompleteness.Pi.headStart Q'))
        (PionCompleteness.Pi.headLen N Q'))
      PionCompleteness.PionNLSM.gen)
-/
#guard_msgs in
#print PionCompleteness.Paper.NLSM.Amplitude.regionAmp
/--
info: def PionCompleteness.Paper.NLSM.Amplitude.stripFactor : ℕ → ℕ × ℕ → ℕ × ℕ → ℕ × ℕ → PionCompleteness.PionNLSM.RF :=
fun N P Q Q' =>
  if Q = Q' then 1 else PionCompleteness.Paper.NLSM.Amplitude.regionAmp N Q Q' / PionCompleteness.PionNLSM.gen P
-/
#guard_msgs in
#print PionCompleteness.Paper.NLSM.Amplitude.stripFactor
/--
info: PionCompleteness.Paper.region_diag_not_member {N : ℕ} (hE : Even N) {S K : Finset (ℕ × ℕ)} {P t b : ℕ × ℕ}
  (h : PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses N S K P t b) {Q Q' : ℕ × ℕ} (hQ : Q ∈ K)
  (hQ' : Q' ∈ K) (hsub : PionCompleteness.Pi.oddSide N Q' ⊆ PionCompleteness.Pi.oddSide N Q) (hne : Q ≠ Q') {d : ℕ × ℕ}
  (hd : d ∈ PionCompleteness.PionZeros.oddDiagonals (PionCompleteness.Pi.pkRBOmM N Q Q'))
  (hex :
    d ∉
      Finset.image (PionCompleteness.Pi.pkRMchord (PionCompleteness.Pi.pkRBOmD N Q Q'))
        (Finset.image (PionCompleteness.Pi.pkRBOmI N Q Q')
          (PionCompleteness.Pi.pkRD2Above N (PionCompleteness.Pi.pkRD2Below N K Q) Q'))) :
  PionCompleteness.PionNLSM.relab N (PionCompleteness.Pi.headStart Q)
      (PionCompleteness.Pi.pkRWOm
        (PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart Q) (PionCompleteness.Pi.headStart Q'))
        (PionCompleteness.Pi.headLen N Q') d) ∉
    K
-/
#guard_msgs in
#check PionCompleteness.Paper.region_diag_not_member
/--
info: PionCompleteness.Paper.region_member_diag {N : ℕ} (hE : Even N) {S K : Finset (ℕ × ℕ)} {P t b : ℕ × ℕ}
  (h : PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses N S K P t b) {Q Q' : ℕ × ℕ} (hQ : Q ∈ K)
  (hQ' : Q' ∈ K) (hsub : PionCompleteness.Pi.oddSide N Q' ⊆ PionCompleteness.Pi.oddSide N Q) (hne : Q ≠ Q') {c : ℕ × ℕ}
  (hc : c ∈ PionCompleteness.Pi.pkRD2Above N (PionCompleteness.Pi.pkRD2Below N K Q) Q') :
  PionCompleteness.Pi.pkRMchord (PionCompleteness.Pi.pkRBOmD N Q Q') (PionCompleteness.Pi.pkRBOmI N Q Q' c) ∈
      PionCompleteness.PionZeros.oddDiagonals (PionCompleteness.Pi.pkRBOmM N Q Q') ∧
    PionCompleteness.Pi.pkRWOm
          (PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart Q) (PionCompleteness.Pi.headStart Q'))
          (PionCompleteness.Pi.headLen N Q')
          (PionCompleteness.Pi.pkRMchord (PionCompleteness.Pi.pkRBOmD N Q Q') (PionCompleteness.Pi.pkRBOmI N Q Q' c)) ∈
        PionCompleteness.TreeRectangleZero.diagonals (PionCompleteness.Pi.headLen N Q + 1) ∧
      PionCompleteness.PionNLSM.relab N (PionCompleteness.Pi.headStart Q)
          (PionCompleteness.Pi.pkRWOm
            (PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart Q) (PionCompleteness.Pi.headStart Q'))
            (PionCompleteness.Pi.headLen N Q')
            (PionCompleteness.Pi.pkRMchord (PionCompleteness.Pi.pkRBOmD N Q Q')
              (PionCompleteness.Pi.pkRBOmI N Q Q' c))) =
        c
-/
#guard_msgs in
#check PionCompleteness.Paper.region_member_diag
/--
info: PionCompleteness.Paper.region_subP_odd {N : ℕ} (hE : Even N) {Q Q' : ℕ × ℕ}
  (hQo : Q ∈ PionCompleteness.PionZeros.oddDiagonals N) (hQ'o : Q' ∈ PionCompleteness.PionZeros.oddDiagonals N)
  (hsub : PionCompleteness.Pi.oddSide N Q' ⊆ PionCompleteness.Pi.oddSide N Q) (hne : Q ≠ Q') {d : ℕ × ℕ}
  (hd : d ∈ PionCompleteness.PionZeros.oddDiagonals (PionCompleteness.Pi.pkRBOmM N Q Q')) :
  PionCompleteness.Pi.pkRD2SubP N
        (PionCompleteness.Pi.pkRBOmL N (PionCompleteness.Pi.headStart Q)
          (PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart Q) (PionCompleteness.Pi.headStart Q'))
          (PionCompleteness.Pi.headLen N Q'))
        d =
      MvPolynomial.X
        (PionCompleteness.PionNLSM.relab N (PionCompleteness.Pi.headStart Q)
          (PionCompleteness.Pi.pkRWOm
            (PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart Q) (PionCompleteness.Pi.headStart Q'))
            (PionCompleteness.Pi.headLen N Q') d)) ∧
    PionCompleteness.PionNLSM.relab N (PionCompleteness.Pi.headStart Q)
        (PionCompleteness.Pi.pkRWOm
          (PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart Q) (PionCompleteness.Pi.headStart Q'))
          (PionCompleteness.Pi.headLen N Q') d) ∈
      PionCompleteness.PionZeros.oddDiagonals N
-/
#guard_msgs in
#check PionCompleteness.Paper.region_subP_odd
/--
info: PionCompleteness.Paper.regionAmp_eq {N : ℕ} (hE : Even N) {Q Q' : ℕ × ℕ}
  (hQo : Q ∈ PionCompleteness.PionZeros.oddDiagonals N) (hQ'o : Q' ∈ PionCompleteness.PionZeros.oddDiagonals N)
  (hsub : PionCompleteness.Pi.oddSide N Q' ⊆ PionCompleteness.Pi.oddSide N Q) (hne : Q ≠ Q') :
  PionCompleteness.Paper.NLSM.Amplitude.regionAmp N Q Q' *
      (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF)
        ((MvPolynomial.aeval
            (PionCompleteness.Pi.pkRD2SubP N
              (PionCompleteness.Pi.pkRBOmL N (PionCompleteness.Pi.headStart Q)
                (PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart Q) (PionCompleteness.Pi.headStart Q'))
                (PionCompleteness.Pi.headLen N Q'))))
          (∏ d ∈ PionCompleteness.PionZeros.oddDiagonals (PionCompleteness.Pi.pkRBOmM N Q Q'), MvPolynomial.X d)) =
    (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF)
      ((MvPolynomial.aeval
          (PionCompleteness.Pi.pkRD2SubP N
            (PionCompleteness.Pi.pkRBOmL N (PionCompleteness.Pi.headStart Q)
              (PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart Q) (PionCompleteness.Pi.headStart Q'))
              (PionCompleteness.Pi.headLen N Q'))))
        (PionCompleteness.PionNLSM.NP ℚ (PionCompleteness.Pi.pkRBOmM N Q Q')))
-/
#guard_msgs in
#check PionCompleteness.Paper.regionAmp_eq
/--
info: PionCompleteness.Paper.region_den_eval {N : ℕ} (hE : Even N) {S K : Finset (ℕ × ℕ)} {P t b : ℕ × ℕ}
  (h : PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses N S K P t b) {Q Q' : ℕ × ℕ} (hQ : Q ∈ K)
  (hQ' : Q' ∈ K) (hsub : PionCompleteness.Pi.oddSide N Q' ⊆ PionCompleteness.Pi.oddSide N Q) (hne : Q ≠ Q')
  {X : ℕ × ℕ → ℚ} (hX : PionCompleteness.ChainSlice.OnLocus N S X) :
  (MvPolynomial.eval X)
      ((MvPolynomial.aeval
          (PionCompleteness.Pi.pkRD2SubP N
            (PionCompleteness.Pi.pkRBOmL N (PionCompleteness.Pi.headStart Q)
              (PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart Q) (PionCompleteness.Pi.headStart Q'))
              (PionCompleteness.Pi.headLen N Q'))))
        (∏ d ∈ PionCompleteness.PionZeros.oddDiagonals (PionCompleteness.Pi.pkRBOmM N Q Q'), MvPolynomial.X d)) =
    X P ^ (PionCompleteness.Pi.pkRD2Above N (PionCompleteness.Pi.pkRD2Below N K Q) Q').card *
      (MvPolynomial.eval X) (PionCompleteness.Pi.pkRD2Dp N K Q Q')
-/
#guard_msgs in
#check PionCompleteness.Paper.region_den_eval
/--
info: PionCompleteness.Paper.stripFactor_hasNoPoleAlong {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {S K : Finset (ℕ × ℕ)}
  {P t b : ℕ × ℕ} (h : PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses N S K P t b) {Q Q' : ℕ × ℕ}
  (hQ : Q ∈ K) (hQ' : Q' ∈ K) (hsub : PionCompleteness.Pi.oddSide N Q' ⊆ PionCompleteness.Pi.oddSide N Q) :
  PionCompleteness.Paper.NLSM.Amplitude.HasNoPoleAlong {X | PionCompleteness.ChainSlice.OnLocus N S X}
    (PionCompleteness.Paper.NLSM.Amplitude.residueHyperplane N S P)
    (PionCompleteness.Paper.NLSM.Amplitude.stripFactor N P Q Q')
-/
#guard_msgs in
#check PionCompleteness.Paper.stripFactor_hasNoPoleAlong
/--
info: PionCompleteness.Paper.NLSM.Amplitude.only_extreme_term_survives {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
  {S K : Finset (ℕ × ℕ)} {P t b : ℕ × ℕ}
  (h : PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses N S K P t b) :
  (∀ Q ∈ K,
      Q ≠ b →
        PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong {X | PionCompleteness.ChainSlice.OnLocus N S X}
          (PionCompleteness.Paper.NLSM.Amplitude.residueHyperplane N S P)
          (PionCompleteness.Paper.NLSM.Amplitude.avoidingA N K Q)) ∧
    ∀ Q ∈ K,
      Q ≠ t →
        PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong {X | PionCompleteness.ChainSlice.OnLocus N S X}
          (PionCompleteness.Paper.NLSM.Amplitude.residueHyperplane N S P)
          (PionCompleteness.Paper.NLSM.Amplitude.avoidingB N K Q)
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.only_extreme_term_survives

-- Library definitions that the class residue's definitions above are read through: the child
-- relabelling `relab` (with `npair`), the pulled-back banned set `pkRBPull`, and the region
-- point of `Ω(Q, Q′)` (`pkRSubX` with the vertex list `pkRBOmL`, `pkRBOlo`, and the size
-- `pkRBOmM`); and `F_N` (`InFpi`, with `ContainsGMember`), the library's candidate sets, read
-- through `isCandidateSet_iff_inFpi`.
/--
info: def PionCompleteness.PionNLSM.relab : ℕ → ℕ → ℕ × ℕ → ℕ × ℕ :=
fun N b d => PionCompleteness.PionZeros.npair N (d.1 + b - 1) (d.2 + b - 1)
-/
#guard_msgs in
#print PionCompleteness.PionNLSM.relab
/--
info: def PionCompleteness.PionZeros.npair : ℕ → ℕ → ℕ → ℕ × ℕ :=
fun N u v =>
  (min (PionCompleteness.TreeRectangleZero.vtx N u) (PionCompleteness.TreeRectangleZero.vtx N v),
    max (PionCompleteness.TreeRectangleZero.vtx N u) (PionCompleteness.TreeRectangleZero.vtx N v))
-/
#guard_msgs in
#print PionCompleteness.PionZeros.npair
/--
info: def PionCompleteness.Pi.pkRBPull : ℕ → ℕ → ℕ → Finset (ℕ × ℕ) → Finset (ℕ × ℕ) :=
fun N b n K => {d ∈ PionCompleteness.TreeRectangleZero.diagonals n | PionCompleteness.PionNLSM.relab N b d ∈ K}
-/
#guard_msgs in
#print PionCompleteness.Pi.pkRBPull
/--
info: def PionCompleteness.Pi.pkRSubX.{u_1} : {K : Type u_1} → [Field K] → ℕ → (ℕ → ℕ) → (ℕ × ℕ → K) → ℕ × ℕ → K :=
fun {K} [Field K] n f X p => PionCompleteness.TreeRectangleZero.planar n X (f p.1) (f p.2)
-/
#guard_msgs in
#print PionCompleteness.Pi.pkRSubX
/--
info: def PionCompleteness.Pi.pkRBOlo : ℕ → ℕ → ℕ → ℕ :=
fun p L' k => if k ≤ p + 1 then k - 1 else k - 2 + L'
-/
#guard_msgs in
#print PionCompleteness.Pi.pkRBOlo
/--
info: def PionCompleteness.Pi.pkRBOmL : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ :=
fun N a p L' k => PionCompleteness.TreeRectangleZero.vtx N (a + PionCompleteness.Pi.pkRBOlo p L' k)
-/
#guard_msgs in
#print PionCompleteness.Pi.pkRBOmL
/--
info: def PionCompleteness.Pi.pkRBOmM : ℕ → ℕ × ℕ → ℕ × ℕ → ℕ :=
fun N Q Q' => PionCompleteness.Pi.headLen N Q - PionCompleteness.Pi.headLen N Q' + 2
-/
#guard_msgs in
#print PionCompleteness.Pi.pkRBOmM
/--
info: def PionCompleteness.Pi.InFpi : ℕ → Finset (ℕ × ℕ) → Prop :=
fun N S =>
  S ⊆ PionCompleteness.TreeRectangleZero.diagonals N ∧
    PionCompleteness.ChainSlice.Nondeg N S ∧ ¬PionCompleteness.Pi.ContainsGMember N S
-/
#guard_msgs in
#print PionCompleteness.Pi.InFpi
/--
info: def PionCompleteness.Pi.ContainsGMember : ℕ → Finset (ℕ × ℕ) → Prop :=
fun N S => ∃ Z ∈ PionCompleteness.Pi.gFamily N, Z ⊆ S
-/
#guard_msgs in
#print PionCompleteness.Pi.ContainsGMember
-- The rest of the class residue and of the polygon with a marked leg (descent and containment,
-- grouping, chains, collapse, strip regions, corners, the ear lemma, the class residue, the value
-- of the strip factor, the children of an odd chord, the Gram model, genericity, the value on the
-- marked locus), with their helpers.
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.descent_to_smaller_side {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
  {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ} (hP : P ∈ PionCompleteness.Pi.poleChords N S)
  (hB : ¬PionCompleteness.Pi.NoFreeSep N S (PionCompleteness.Pi.tailStart P) (PionCompleteness.Pi.tailLen N P) 1) :
  ∃ Q ∈ PionCompleteness.Pi.poleChords N S,
    (PionCompleteness.Pi.evenSide N Q).card < (PionCompleteness.Pi.evenSide N P).card
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.descent_to_smaller_side
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.odd_side_nesting {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {S : Finset (ℕ × ℕ)}
  {P Q : ℕ × ℕ} (hP : P ∈ PionCompleteness.Pi.poleChords N S)
  (hPB : PionCompleteness.Pi.NoFreeSep N S (PionCompleteness.Pi.tailStart P) (PionCompleteness.Pi.tailLen N P) 1)
  (hQ : Q ∈ PionCompleteness.Pi.cleanChords N S)
  (hee : PionCompleteness.Pi.innerEE N S P ⊆ PionCompleteness.Pi.innerEE N S Q)
  (hmeet : (PionCompleteness.Pi.oddSide N Q ∩ PionCompleteness.Pi.oddSide N P).Nonempty) :
  PionCompleteness.Pi.oddSide N Q ⊆ PionCompleteness.Pi.oddSide N P
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.odd_side_nesting
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.odd_side_nesting_mirror {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
  {S : Finset (ℕ × ℕ)} {P Q : ℕ × ℕ} (hP : P ∈ PionCompleteness.Pi.poleChords N S)
  (hPA : PionCompleteness.Pi.NoFreeSep N S (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P) 0)
  (hQ : Q ∈ PionCompleteness.Pi.cleanChords N S)
  (hoo : PionCompleteness.Pi.innerOO N S P ⊆ PionCompleteness.Pi.innerOO N S Q)
  (hmeet : (PionCompleteness.Pi.evenSide N Q ∩ PionCompleteness.Pi.evenSide N P).Nonempty) :
  PionCompleteness.Pi.oddSide N P ⊆ PionCompleteness.Pi.oddSide N Q
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.odd_side_nesting_mirror
/--
info: PionCompleteness.Paper.exists_eval_mul_ne_zero {V : Set (ℕ × ℕ → ℚ)} (hV : PionCompleteness.Pi.pkRSub V)
  {D₁ D₂ : MvPolynomial (ℕ × ℕ) ℚ} (h₁ : ∃ w ∈ V, (MvPolynomial.eval w) D₁ ≠ 0)
  (h₂ : ∃ w ∈ V, (MvPolynomial.eval w) D₂ ≠ 0) : ∃ w ∈ V, (MvPolynomial.eval w) (D₁ * D₂) ≠ 0
-/
#guard_msgs in
#check PionCompleteness.Paper.exists_eval_mul_ne_zero
/--
info: PionCompleteness.Paper.ratZeroOn_add {V : Set (ℕ × ℕ → ℚ)} (hV : PionCompleteness.Pi.pkRSub V)
  {f g : PionCompleteness.PionNLSM.RF} (hf : PionCompleteness.PionNLSM.RatZeroOn V f)
  (hg : PionCompleteness.PionNLSM.RatZeroOn V g) : PionCompleteness.PionNLSM.RatZeroOn V (f + g)
-/
#guard_msgs in
#check PionCompleteness.Paper.ratZeroOn_add
/--
info: PionCompleteness.Paper.ratZeroOn_sum.{u_1} {ι : Type u_1} {V : Set (ℕ × ℕ → ℚ)} (hV : PionCompleteness.Pi.pkRSub V)
  (s : Finset ι) {f : ι → PionCompleteness.PionNLSM.RF} (h : ∀ i ∈ s, PionCompleteness.PionNLSM.RatZeroOn V (f i)) :
  PionCompleteness.PionNLSM.RatZeroOn V (∑ i ∈ s, f i)
-/
#guard_msgs in
#check PionCompleteness.Paper.ratZeroOn_sum
/--
info: PionCompleteness.Paper.ratZeroOn_mul_of_eq {V : Set (ℕ × ℕ → ℚ)} (hV : PionCompleteness.Pi.pkRSub V)
  {f g : PionCompleteness.PionNLSM.RF} (hf : PionCompleteness.PionNLSM.RatZeroOn V f) {P D : MvPolynomial (ℕ × ℕ) ℚ}
  (hg :
    g * (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) D =
      (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) P)
  (hD : ∃ w ∈ V, (MvPolynomial.eval w) D ≠ 0) : PionCompleteness.PionNLSM.RatZeroOn V (g * f)
-/
#guard_msgs in
#check PionCompleteness.Paper.ratZeroOn_mul_of_eq
/--
info: PionCompleteness.Paper.ratZeroOn_mul {V : Set (ℕ × ℕ → ℚ)} (hV : PionCompleteness.Pi.pkRSub V)
  {f g : PionCompleteness.PionNLSM.RF} (hf : PionCompleteness.PionNLSM.RatZeroOn V f)
  (hg : PionCompleteness.PionNLSM.RatZeroOn V g) : PionCompleteness.PionNLSM.RatZeroOn V (f * g)
-/
#guard_msgs in
#check PionCompleteness.Paper.ratZeroOn_mul
/--
info: PionCompleteness.Paper.ratZeroOn_rep_add {V : Set (ℕ × ℕ → ℚ)} (hV : PionCompleteness.Pi.pkRSub V)
  {f g : PionCompleteness.PionNLSM.RF} {P₁ D₁ P₂ D₂ : MvPolynomial (ℕ × ℕ) ℚ}
  (h₁ :
    PionCompleteness.PionNLSM.RatZeroOn V
      (f * (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) D₁ -
        (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) P₁))
  (h₂ :
    PionCompleteness.PionNLSM.RatZeroOn V
      (g * (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) D₂ -
        (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) P₂)) :
  PionCompleteness.PionNLSM.RatZeroOn V
    ((f + g) * (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) (D₁ * D₂) -
      (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) (P₁ * D₂ + P₂ * D₁))
-/
#guard_msgs in
#check PionCompleteness.Paper.ratZeroOn_rep_add
/--
info: PionCompleteness.Paper.ratZeroOn_rep_mul {V : Set (ℕ × ℕ → ℚ)} (hV : PionCompleteness.Pi.pkRSub V)
  {f g : PionCompleteness.PionNLSM.RF} {P₁ D₁ P₂ D₂ : MvPolynomial (ℕ × ℕ) ℚ}
  (h₁ :
    PionCompleteness.PionNLSM.RatZeroOn V
      (f * (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) D₁ -
        (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) P₁))
  (h₂ :
    PionCompleteness.PionNLSM.RatZeroOn V
      (g * (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) D₂ -
        (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) P₂)) :
  PionCompleteness.PionNLSM.RatZeroOn V
    (f * g * (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) (D₁ * D₂) -
      (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) (P₁ * P₂))
-/
#guard_msgs in
#check PionCompleteness.Paper.ratZeroOn_rep_mul
/--
info: PionCompleteness.Paper.NLSM.Amplitude.HasNoPoleAlong.add {V H : Set (ℕ × ℕ → ℚ)} (hV : PionCompleteness.Pi.pkRSub V)
  (hH : PionCompleteness.Pi.pkRSub H) {f g : PionCompleteness.PionNLSM.RF}
  (hf : PionCompleteness.Paper.NLSM.Amplitude.HasNoPoleAlong V H f)
  (hg : PionCompleteness.Paper.NLSM.Amplitude.HasNoPoleAlong V H g) :
  PionCompleteness.Paper.NLSM.Amplitude.HasNoPoleAlong V H (f + g)
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.HasNoPoleAlong.add
/--
info: PionCompleteness.Paper.NLSM.Amplitude.HasNoPoleAlong.mul {V H : Set (ℕ × ℕ → ℚ)} (hV : PionCompleteness.Pi.pkRSub V)
  (hH : PionCompleteness.Pi.pkRSub H) {f g : PionCompleteness.PionNLSM.RF}
  (hf : PionCompleteness.Paper.NLSM.Amplitude.HasNoPoleAlong V H f)
  (hg : PionCompleteness.Paper.NLSM.Amplitude.HasNoPoleAlong V H g) :
  PionCompleteness.Paper.NLSM.Amplitude.HasNoPoleAlong V H (f * g)
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.HasNoPoleAlong.mul
/--
info: PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong.add {V H : Set (ℕ × ℕ → ℚ)}
  (hV : PionCompleteness.Pi.pkRSub V) (hH : PionCompleteness.Pi.pkRSub H) {f g : PionCompleteness.PionNLSM.RF}
  (hf : PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong V H f)
  (hg : PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong V H g) :
  PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong V H (f + g)
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong.add
/--
info: PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong.mul {V H : Set (ℕ × ℕ → ℚ)}
  (hV : PionCompleteness.Pi.pkRSub V) (hH : PionCompleteness.Pi.pkRSub H) {f g : PionCompleteness.PionNLSM.RF}
  (hf : PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong V H f)
  (hg : PionCompleteness.Paper.NLSM.Amplitude.HasNoPoleAlong V H g) :
  PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong V H (f * g)
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong.mul
/--
info: PionCompleteness.Paper.restrictsToZeroAlong_of_ratZeroOn {V H : Set (ℕ × ℕ → ℚ)} (hH : ∃ w, w ∈ H)
  {f : PionCompleteness.PionNLSM.RF} (hf : PionCompleteness.PionNLSM.RatZeroOn V f) :
  PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong V H f
-/
#guard_msgs in
#check PionCompleteness.Paper.restrictsToZeroAlong_of_ratZeroOn
/--
info: PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong.sum.{u_1} {V H : Set (ℕ × ℕ → ℚ)}
  (hV : PionCompleteness.Pi.pkRSub V) (hH : PionCompleteness.Pi.pkRSub H) {ι : Type u_1} (s : Finset ι)
  {f : ι → PionCompleteness.PionNLSM.RF}
  (h : ∀ i ∈ s, PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong V H (f i)) :
  PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong V H (∑ i ∈ s, f i)
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong.sum
/--
info: PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong.congr {V H : Set (ℕ × ℕ → ℚ)}
  (hV : PionCompleteness.Pi.pkRSub V) {f g : PionCompleteness.PionNLSM.RF}
  (hfg : PionCompleteness.PionNLSM.RatZeroOn V (f - g))
  (hg : PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong V H g) :
  PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong V H f
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong.congr
/--
info: PionCompleteness.Paper.hasNoPoleAlong_const {V H : Set (ℕ × ℕ → ℚ)} (hV : PionCompleteness.Pi.pkRSub V)
  (hH : ∃ w, w ∈ H) (c : ℚ) : PionCompleteness.Paper.NLSM.Amplitude.HasNoPoleAlong V H ↑c
-/
#guard_msgs in
#check PionCompleteness.Paper.hasNoPoleAlong_const
/--
info: PionCompleteness.Paper.ampAvoiding_shifted.{u_1} {F : Type u_1} [Field F] (n : ℕ) (K : Finset (ℕ × ℕ)) (x : ℕ × ℕ → F) :
  PionCompleteness.Paper.ampAvoiding n K (PionCompleteness.PionNLSM.shifted x) =
    (HahnSeries.ofPowerSeries ℤ F)
      (∑ T ∈ PionCompleteness.TreeRectangleZero.triangulations n with Disjoint T K,
        ∏ d ∈ T, PionCompleteness.PionNLSM.phi x d)
-/
#guard_msgs in
#check PionCompleteness.Paper.ampAvoiding_shifted
/--
info: PionCompleteness.Paper.NLSM.Amplitude.ampAvoiding_coeff_numerator_hom.{u_1} {F : Type u_1} [Field F]
  (f : MvPolynomial (ℕ × ℕ) ℚ →+* F) (n m : ℕ) (K : Finset (ℕ × ℕ))
  (hX : ∀ d ∈ PionCompleteness.PionZeros.oddDiagonals n \ K, f (MvPolynomial.X d) ≠ 0) :
  f (PionCompleteness.Pi.pkRBAP ℚ n m K) =
    (PionCompleteness.Paper.ampAvoiding n K (PionCompleteness.PionNLSM.shifted fun d => f (MvPolynomial.X d))).coeff
        ↑m *
      ∏ d ∈ PionCompleteness.PionZeros.oddDiagonals n \ K, f (MvPolynomial.X d)
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.ampAvoiding_coeff_numerator_hom
/--
info: PionCompleteness.Paper.NLSM.Amplitude.stripFactor_sub_const_restrictsToZero {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
  {S K : Finset (ℕ × ℕ)} {P t b : ℕ × ℕ}
  (h : PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses N S K P t b) {Q Q' : ℕ × ℕ} (hQ : Q ∈ K)
  (hQ' : Q' ∈ K) (hsub : PionCompleteness.Pi.oddSide N Q' ⊆ PionCompleteness.Pi.oddSide N Q) :
  ∃ ε,
    ε ≠ 0 ∧
      PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong {X | PionCompleteness.ChainSlice.OnLocus N S X}
        (PionCompleteness.Paper.NLSM.Amplitude.residueHyperplane N S P)
        (PionCompleteness.Paper.NLSM.Amplitude.stripFactor N P Q Q' - ↑ε)
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.stripFactor_sub_const_restrictsToZero
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.flank_class_members_form_chains {N : ℕ} {K : Finset (ℕ × ℕ)} {t b : ℕ × ℕ}
  (hK : K ⊆ PionCompleteness.PionZeros.oddDiagonals N)
  (htop : t ∈ K ∧ ∀ Q ∈ K, PionCompleteness.Pi.oddSide N Q ⊆ PionCompleteness.Pi.oddSide N t)
  (hbot : b ∈ K ∧ ∀ Q ∈ K, PionCompleteness.Pi.oddSide N b ⊆ PionCompleteness.Pi.oddSide N Q) :
  (∀ Q ∈ K,
      ∀ Q' ∈ K,
        Q ≠ Q' →
          (¬PionCompleteness.TreeRectangleZero.Crosses Q Q' ↔
            PionCompleteness.Pi.oddSide N Q ⊂ PionCompleteness.Pi.oddSide N Q' ∨
              PionCompleteness.Pi.oddSide N Q' ⊂ PionCompleteness.Pi.oddSide N Q)) ∧
    ∀ D ⊆ K,
      (∀ Q ∈ D, ∀ Q' ∈ D, ¬PionCompleteness.TreeRectangleZero.Crosses Q Q') ↔
        ∀ Q ∈ D,
          ∀ Q' ∈ D,
            PionCompleteness.Pi.oddSide N Q ⊆ PionCompleteness.Pi.oddSide N Q' ∨
              PionCompleteness.Pi.oddSide N Q' ⊆ PionCompleteness.Pi.oddSide N Q
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.flank_class_members_form_chains
/--
info: PionCompleteness.Paper.rename_oddDen_avoiding (N s n : ℕ) (K : Finset (ℕ × ℕ)) :
  (PionCompleteness.Pi.pkRBPsi ℚ fun d => d ∈ K)
      ((MvPolynomial.rename (PionCompleteness.PionNLSM.relab N s)) (PionCompleteness.PionNLSM.oddDen ℚ n)) =
    (MvPolynomial.rename (PionCompleteness.PionNLSM.relab N s))
      (∏ d ∈ PionCompleteness.PionZeros.oddDiagonals n \ PionCompleteness.Pi.pkRBPull N s n K, MvPolynomial.X d)
-/
#guard_msgs in
#check PionCompleteness.Paper.rename_oddDen_avoiding
/--
info: PionCompleteness.Paper.prod_oddDiagonals_avoiding {N : ℕ} (hE : Even N) {C : ℕ × ℕ}
  (hC : C ∈ PionCompleteness.PionZeros.oddDiagonals N) (K : Finset (ℕ × ℕ)) :
  ∏ d ∈ PionCompleteness.PionZeros.oddDiagonals N \ insert C K, MvPolynomial.X d =
    (MvPolynomial.rename (PionCompleteness.PionNLSM.relab N (PionCompleteness.Pi.headStart C)))
          (∏
            d ∈
              PionCompleteness.PionZeros.oddDiagonals (PionCompleteness.Pi.headLen N C + 1) \
                PionCompleteness.Pi.pkRBPull N (PionCompleteness.Pi.headStart C) (PionCompleteness.Pi.headLen N C + 1)
                  K,
            MvPolynomial.X d) *
        (MvPolynomial.rename (PionCompleteness.PionNLSM.relab N (PionCompleteness.Pi.tailStart C)))
          (∏
            d ∈
              PionCompleteness.PionZeros.oddDiagonals (PionCompleteness.Pi.tailLen N C + 1) \
                PionCompleteness.Pi.pkRBPull N (PionCompleteness.Pi.tailStart C) (PionCompleteness.Pi.tailLen N C + 1)
                  K,
            MvPolynomial.X d) *
      PionCompleteness.Pi.pkRBCross ℚ N K C
-/
#guard_msgs in
#check PionCompleteness.Paper.prod_oddDiagonals_avoiding
/--
info: PionCompleteness.Paper.nlsmAvoiding_child_hom.{u_1} {F : Type u_1} [Field F] (f : MvPolynomial (ℕ × ℕ) ℚ →+* F)
  (hf : ∀ (d : ℕ × ℕ), f (MvPolynomial.X d) ≠ 0) (N s : ℕ) {n : ℕ} (hn : 2 ≤ n) (K : Finset (ℕ × ℕ)) :
  f ((MvPolynomial.rename (PionCompleteness.PionNLSM.relab N s)) (PionCompleteness.Pi.pkRBNP ℚ n K)) =
    (PionCompleteness.Paper.NLSM.Amplitude.nlsmAvoiding n K fun d =>
        f (MvPolynomial.X (PionCompleteness.PionNLSM.relab N s d))) *
      f
        ((MvPolynomial.rename (PionCompleteness.PionNLSM.relab N s))
          (∏ d ∈ PionCompleteness.PionZeros.oddDiagonals n \ K, MvPolynomial.X d))
-/
#guard_msgs in
#check PionCompleteness.Paper.nlsmAvoiding_child_hom
/--
info: PionCompleteness.Paper.NLSM.Amplitude.nlsmAvoiding_step.{u_1} {F : Type u_1} [Field F]
  (f : MvPolynomial (ℕ × ℕ) ℚ →+* F) (hf : ∀ (d : ℕ × ℕ), f (MvPolynomial.X d) ≠ 0) {N : ℕ} (hN : 4 ≤ N) (hE : Even N)
  {K : Finset (ℕ × ℕ)} {C : ℕ × ℕ} (hK : insert C K ⊆ PionCompleteness.PionZeros.oddDiagonals N) (hC : C ∉ K) :
  (PionCompleteness.Paper.NLSM.Amplitude.nlsmAvoiding N K fun d => f (MvPolynomial.X d)) =
    (PionCompleteness.Paper.NLSM.Amplitude.nlsmAvoiding N (insert C K) fun d => f (MvPolynomial.X d)) +
      ((PionCompleteness.Paper.NLSM.Amplitude.nlsmAvoiding (PionCompleteness.Pi.headLen N C + 1)
            (PionCompleteness.Pi.pkRBPull N (PionCompleteness.Pi.headStart C) (PionCompleteness.Pi.headLen N C + 1) K)
            fun d => f (MvPolynomial.X (PionCompleteness.PionNLSM.relab N (PionCompleteness.Pi.headStart C) d))) *
          PionCompleteness.Paper.NLSM.Amplitude.nlsmAvoiding (PionCompleteness.Pi.tailLen N C + 1)
            (PionCompleteness.Pi.pkRBPull N (PionCompleteness.Pi.tailStart C) (PionCompleteness.Pi.tailLen N C + 1) K)
            fun d => f (MvPolynomial.X (PionCompleteness.PionNLSM.relab N (PionCompleteness.Pi.tailStart C) d))) /
        f (MvPolynomial.X C)
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.nlsmAvoiding_step
/--
info: PionCompleteness.Paper.NLSM.Amplitude.grouping_identity {n : ℕ} (hn : 4 ≤ n) (hE : Even n) {K : Finset (ℕ × ℕ)}
  (hK : K ⊆ PionCompleteness.PionZeros.oddDiagonals n) :
  (∀ j < ↑n - 2,
      (PionCompleteness.Paper.ampAvoiding n K (PionCompleteness.PionNLSM.shifted PionCompleteness.PionNLSM.gen)).coeff
          j =
        0) ∧
    (∃ P,
        PionCompleteness.Paper.NLSM.Amplitude.nlsmAvoiding n K PionCompleteness.PionNLSM.gen *
            ∏ d ∈ PionCompleteness.PionZeros.oddDiagonals n \ K, PionCompleteness.PionNLSM.gen d =
          (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) P) ∧
      (∀ C ∈ PionCompleteness.PionZeros.oddDiagonals n,
          C ∉ K →
            PionCompleteness.Paper.NLSM.Amplitude.nlsmAvoiding n K PionCompleteness.PionNLSM.gen =
              PionCompleteness.Paper.NLSM.Amplitude.nlsmAvoiding n (insert C K) PionCompleteness.PionNLSM.gen +
                PionCompleteness.Paper.NLSM.Amplitude.avoidingA n K C *
                    PionCompleteness.Paper.NLSM.Amplitude.avoidingB n K C /
                  PionCompleteness.PionNLSM.gen C) ∧
        ∀ C ∈ PionCompleteness.PionZeros.oddDiagonals n,
          PionCompleteness.PionNLSM.NLSM n PionCompleteness.PionNLSM.gen =
            PionCompleteness.Paper.NLSM.Amplitude.nlsmAvoiding n {C} PionCompleteness.PionNLSM.gen +
              PionCompleteness.Paper.NLSM.Amplitude.childAmpA n C *
                  PionCompleteness.Paper.NLSM.Amplitude.childAmpB n C /
                PionCompleteness.PionNLSM.gen C
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.grouping_identity
/--
info: PionCompleteness.Paper.nlsmAvoiding_top.{u_1} {F : Type u_1} [Field F] (f : MvPolynomial (ℕ × ℕ) ℚ →+* F)
  (hf : ∀ (d : ℕ × ℕ), f (MvPolynomial.X d) ≠ 0) {N : ℕ} (hN : 4 ≤ N) (hE : Even N) {K : Finset (ℕ × ℕ)}
  (hK : K ⊆ PionCompleteness.PionZeros.oddDiagonals N)
  (hnc :
    ∀ Q ∈ K,
      ∀ Q' ∈ K,
        ¬PionCompleteness.TreeRectangleZero.Crosses Q' Q →
          PionCompleteness.Pi.oddSide N Q ⊆ PionCompleteness.Pi.oddSide N Q' ∨
            PionCompleteness.Pi.oddSide N Q' ⊆ PionCompleteness.Pi.oddSide N Q)
  (R : Finset (ℕ × ℕ)) (hRK : R ⊆ K)
  (hdown : ∀ Q ∈ R, ∀ Q' ∈ K, PionCompleteness.Pi.oddSide N Q' ⊆ PionCompleteness.Pi.oddSide N Q → Q' ∈ R) :
  (PionCompleteness.Paper.NLSM.Amplitude.nlsmAvoiding N (K \ R) fun d => f (MvPolynomial.X d)) =
    (PionCompleteness.Paper.NLSM.Amplitude.nlsmAvoiding N K fun d => f (MvPolynomial.X d)) +
      ∑ Q ∈ R,
        ((PionCompleteness.Paper.NLSM.Amplitude.nlsmAvoiding (PionCompleteness.Pi.tailLen N Q + 1)
              (PionCompleteness.Pi.pkRBPull N (PionCompleteness.Pi.tailStart Q) (PionCompleteness.Pi.tailLen N Q + 1) K)
              fun d => f (MvPolynomial.X (PionCompleteness.PionNLSM.relab N (PionCompleteness.Pi.tailStart Q) d))) *
            PionCompleteness.PionNLSM.NLSM (PionCompleteness.Pi.headLen N Q + 1) fun d =>
              f (MvPolynomial.X (PionCompleteness.PionNLSM.relab N (PionCompleteness.Pi.headStart Q) d))) /
          f (MvPolynomial.X Q)
-/
#guard_msgs in
#check PionCompleteness.Paper.nlsmAvoiding_top
/--
info: PionCompleteness.Paper.nlsmAvoiding_bot.{u_1} {F : Type u_1} [Field F] (f : MvPolynomial (ℕ × ℕ) ℚ →+* F)
  (hf : ∀ (d : ℕ × ℕ), f (MvPolynomial.X d) ≠ 0) {N : ℕ} (hN : 4 ≤ N) (hE : Even N) {K : Finset (ℕ × ℕ)}
  (hK : K ⊆ PionCompleteness.PionZeros.oddDiagonals N)
  (hnc :
    ∀ Q ∈ K,
      ∀ Q' ∈ K,
        ¬PionCompleteness.TreeRectangleZero.Crosses Q' Q →
          PionCompleteness.Pi.oddSide N Q ⊆ PionCompleteness.Pi.oddSide N Q' ∨
            PionCompleteness.Pi.oddSide N Q' ⊆ PionCompleteness.Pi.oddSide N Q)
  (R : Finset (ℕ × ℕ)) (hRK : R ⊆ K)
  (hup : ∀ Q ∈ R, ∀ Q' ∈ K, PionCompleteness.Pi.oddSide N Q ⊆ PionCompleteness.Pi.oddSide N Q' → Q' ∈ R) :
  (PionCompleteness.Paper.NLSM.Amplitude.nlsmAvoiding N (K \ R) fun d => f (MvPolynomial.X d)) =
    (PionCompleteness.Paper.NLSM.Amplitude.nlsmAvoiding N K fun d => f (MvPolynomial.X d)) +
      ∑ Q ∈ R,
        ((PionCompleteness.Paper.NLSM.Amplitude.nlsmAvoiding (PionCompleteness.Pi.headLen N Q + 1)
              (PionCompleteness.Pi.pkRBPull N (PionCompleteness.Pi.headStart Q) (PionCompleteness.Pi.headLen N Q + 1) K)
              fun d => f (MvPolynomial.X (PionCompleteness.PionNLSM.relab N (PionCompleteness.Pi.headStart Q) d))) *
            PionCompleteness.PionNLSM.NLSM (PionCompleteness.Pi.tailLen N Q + 1) fun d =>
              f (MvPolynomial.X (PionCompleteness.PionNLSM.relab N (PionCompleteness.Pi.tailStart Q) d))) /
          f (MvPolynomial.X Q)
-/
#guard_msgs in
#check PionCompleteness.Paper.nlsmAvoiding_bot
/--
info: PionCompleteness.Paper.nlsmAvoiding_congr.{u_1} {F : Type u_1} [Field F] {n : ℕ} (K : Finset (ℕ × ℕ)) {X Y : ℕ × ℕ → F}
  (h : ∀ d ∈ PionCompleteness.TreeRectangleZero.diagonals n, X d = Y d) :
  PionCompleteness.Paper.NLSM.Amplitude.nlsmAvoiding n K X = PionCompleteness.Paper.NLSM.Amplitude.nlsmAvoiding n K Y
-/
#guard_msgs in
#check PionCompleteness.Paper.nlsmAvoiding_congr
/--
info: PionCompleteness.Paper.nlsm_congr.{u_1} {F : Type u_1} [Field F] {n : ℕ} {X Y : ℕ × ℕ → F}
  (h : ∀ d ∈ PionCompleteness.TreeRectangleZero.diagonals n, X d = Y d) :
  PionCompleteness.PionNLSM.NLSM n X = PionCompleteness.PionNLSM.NLSM n Y
-/
#guard_msgs in
#check PionCompleteness.Paper.nlsm_congr
/--
info: PionCompleteness.Paper.relab_eq_subX.{u_1} {F : Type u_1} [Field F] {N s n : ℕ} (hs : 1 ≤ s ∧ s ≤ N) (hn : n ≤ N)
  (X : ℕ × ℕ → F) {d : ℕ × ℕ} (hd : d ∈ PionCompleteness.TreeRectangleZero.diagonals n) :
  X (PionCompleteness.PionNLSM.relab N s d) =
    PionCompleteness.Pi.pkRSubX N (fun k => PionCompleteness.TreeRectangleZero.vtx N (k + s - 1)) X d
-/
#guard_msgs in
#check PionCompleteness.Paper.relab_eq_subX
/--
info: PionCompleteness.Paper.subX_at_relab.{u_1} {F : Type u_1} [Field F] {N n s : ℕ} (g : ℕ → ℕ) (X : ℕ × ℕ → F)
  (d : ℕ × ℕ) :
  PionCompleteness.Pi.pkRSubX N g X (PionCompleteness.PionNLSM.relab n s d) =
    PionCompleteness.Pi.pkRSubX N (fun k => g (PionCompleteness.TreeRectangleZero.vtx n (k + s - 1))) X d
-/
#guard_msgs in
#check PionCompleteness.Paper.subX_at_relab
/--
info: PionCompleteness.Paper.subX_rot.{u_1} {F : Type u_1} [Field F] {N m : ℕ} (f : ℕ → ℕ) (X : ℕ × ℕ → F) :
  (fun d => PionCompleteness.Pi.pkRSubX N f X (PionCompleteness.TreeRectangleZero.rot m d)) =
    PionCompleteness.Pi.pkRSubX N (fun j => f (PionCompleteness.TreeRectangleZero.vtx m (j + 1))) X
-/
#guard_msgs in
#check PionCompleteness.Paper.subX_rot
/--
info: PionCompleteness.Paper.nlsm_subX_rot.{u_1} {F : Type u_1} [Field F] {N m : ℕ} (hm : 4 ≤ m) (hE : m % 2 = 0) (f : ℕ → ℕ)
  (X : ℕ × ℕ → F) (r : ℕ) :
  PionCompleteness.PionNLSM.NLSM m
      (PionCompleteness.Pi.pkRSubX N (fun j => f (PionCompleteness.TreeRectangleZero.vtx m (j + r))) X) =
    PionCompleteness.PionNLSM.NLSM m (PionCompleteness.Pi.pkRSubX N f X)
-/
#guard_msgs in
#check PionCompleteness.Paper.nlsm_subX_rot
/--
info: PionCompleteness.Paper.nlsm_omega_relab.{u_1} {F : Type u_1} [Field F] {N a p L L' : ℕ} (ha : 1 ≤ a ∧ a ≤ N)
  (hp : p % 2 = 0) (hL : L % 2 = 1) (hL' : L' % 2 = 1) (hpL : p + L' ≤ L) (hLL : L' + 2 ≤ L) (hLN : L + 1 ≤ N)
  (X : ℕ × ℕ → F) :
  (PionCompleteness.PionNLSM.NLSM (L - L' + 2) fun d =>
      X (PionCompleteness.PionNLSM.relab N a (PionCompleteness.PionNLSM.relab (L + 1) (p + L' + 1) d))) =
    PionCompleteness.PionNLSM.NLSM (L - L' + 2) (PionCompleteness.Pi.pkRSubX N (PionCompleteness.Pi.pkRBOmL N a p L') X)
-/
#guard_msgs in
#check PionCompleteness.Paper.nlsm_omega_relab
/--
info: PionCompleteness.Paper.NLSM.Amplitude.childAmpA_expansion {N : ℕ} (hE : Even N) {K : Finset (ℕ × ℕ)}
  (hK : K ⊆ PionCompleteness.PionZeros.oddDiagonals N)
  (hnc :
    ∀ Q ∈ K,
      ∀ Q' ∈ K,
        ¬PionCompleteness.TreeRectangleZero.Crosses Q' Q →
          PionCompleteness.Pi.oddSide N Q ⊆ PionCompleteness.Pi.oddSide N Q' ∨
            PionCompleteness.Pi.oddSide N Q' ⊆ PionCompleteness.Pi.oddSide N Q)
  {ℓ : ℕ} (hℓ : ∀ c ∈ K, ℓ ∈ PionCompleteness.Pi.oddSide N c) {Q : ℕ × ℕ} (hQK : Q ∈ K) :
  PionCompleteness.Paper.NLSM.Amplitude.childAmpA N Q =
    PionCompleteness.Paper.NLSM.Amplitude.avoidingA N K Q +
      ∑ c ∈ PionCompleteness.Pi.pkRD2Below N K Q,
        PionCompleteness.Paper.NLSM.Amplitude.avoidingA N K c * PionCompleteness.Paper.NLSM.Amplitude.regionAmp N Q c /
          PionCompleteness.PionNLSM.gen c
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.childAmpA_expansion
/--
info: PionCompleteness.Paper.NLSM.Amplitude.nlsm_collapse {N : ℕ} (hN : 4 ≤ N) (hE : Even N) {K : Finset (ℕ × ℕ)}
  (hK : K ⊆ PionCompleteness.PionZeros.oddDiagonals N)
  (hnc :
    ∀ Q ∈ K,
      ∀ Q' ∈ K,
        ¬PionCompleteness.TreeRectangleZero.Crosses Q' Q →
          PionCompleteness.Pi.oddSide N Q ⊆ PionCompleteness.Pi.oddSide N Q' ∨
            PionCompleteness.Pi.oddSide N Q' ⊆ PionCompleteness.Pi.oddSide N Q)
  {ℓ : ℕ} (hℓ : ∀ c ∈ K, ℓ ∈ PionCompleteness.Pi.oddSide N c) :
  PionCompleteness.PionNLSM.NLSM N PionCompleteness.PionNLSM.gen =
    PionCompleteness.Paper.NLSM.Amplitude.nlsmAvoiding N K PionCompleteness.PionNLSM.gen +
      ∑ Q ∈ K,
        PionCompleteness.Paper.NLSM.Amplitude.avoidingB N K Q *
            (PionCompleteness.Paper.NLSM.Amplitude.avoidingA N K Q +
              ∑ c ∈ PionCompleteness.Pi.pkRD2Below N K Q,
                PionCompleteness.Paper.NLSM.Amplitude.avoidingA N K c *
                    PionCompleteness.Paper.NLSM.Amplitude.regionAmp N Q c /
                  PionCompleteness.PionNLSM.gen c) /
          PionCompleteness.PionNLSM.gen Q
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.nlsm_collapse
/--
info: PionCompleteness.Paper.region_den_witness {N : ℕ} (hE : Even N) {S K : Finset (ℕ × ℕ)} {P t b : ℕ × ℕ}
  (h : PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses N S K P t b) {Q Q' : ℕ × ℕ}
  (hQo : Q ∈ PionCompleteness.PionZeros.oddDiagonals N) (hQ'o : Q' ∈ PionCompleteness.PionZeros.oddDiagonals N)
  (hsub : PionCompleteness.Pi.oddSide N Q' ⊆ PionCompleteness.Pi.oddSide N Q) (hne : Q ≠ Q') :
  ∃ w ∈ {X | PionCompleteness.ChainSlice.OnLocus N S X},
    (MvPolynomial.eval w)
        ((MvPolynomial.aeval
            (PionCompleteness.Pi.pkRD2SubP N
              (PionCompleteness.Pi.pkRBOmL N (PionCompleteness.Pi.headStart Q)
                (PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart Q) (PionCompleteness.Pi.headStart Q'))
                (PionCompleteness.Pi.headLen N Q'))))
          (∏ d ∈ PionCompleteness.PionZeros.oddDiagonals (PionCompleteness.Pi.pkRBOmM N Q Q'), MvPolynomial.X d)) ≠
      0
-/
#guard_msgs in
#check PionCompleteness.Paper.region_den_witness
/--
info: PionCompleteness.Paper.NLSM.Amplitude.collapse_identity {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {S K : Finset (ℕ × ℕ)}
  {P t b : ℕ × ℕ} (h : PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses N S K P t b) :
  PionCompleteness.PionNLSM.RatZeroOn {X | PionCompleteness.ChainSlice.OnLocus N S X}
      (PionCompleteness.PionNLSM.gen P * PionCompleteness.PionNLSM.NLSM N PionCompleteness.PionNLSM.gen -
        (PionCompleteness.PionNLSM.gen P *
            PionCompleteness.Paper.NLSM.Amplitude.nlsmAvoiding N K PionCompleteness.PionNLSM.gen +
          ∑ Q ∈ K,
            ∑ Q' ∈ K with PionCompleteness.Pi.oddSide N Q' ⊆ PionCompleteness.Pi.oddSide N Q,
              PionCompleteness.Paper.NLSM.Amplitude.stripFactor N P Q Q' *
                  PionCompleteness.Paper.NLSM.Amplitude.avoidingB N K Q *
                PionCompleteness.Paper.NLSM.Amplitude.avoidingA N K Q')) ∧
    PionCompleteness.Paper.NLSM.Amplitude.HasNoPoleAlong {X | PionCompleteness.ChainSlice.OnLocus N S X}
        (PionCompleteness.Paper.NLSM.Amplitude.residueHyperplane N S P)
        (PionCompleteness.Paper.NLSM.Amplitude.nlsmAvoiding N K PionCompleteness.PionNLSM.gen) ∧
      (∀ Q ∈ K,
          PionCompleteness.Paper.NLSM.Amplitude.HasNoPoleAlong {X | PionCompleteness.ChainSlice.OnLocus N S X}
            (PionCompleteness.Paper.NLSM.Amplitude.residueHyperplane N S P)
            (PionCompleteness.Paper.NLSM.Amplitude.avoidingB N K Q)) ∧
        ∀ Q ∈ K,
          PionCompleteness.Paper.NLSM.Amplitude.HasNoPoleAlong {X | PionCompleteness.ChainSlice.OnLocus N S X}
            (PionCompleteness.Paper.NLSM.Amplitude.residueHyperplane N S P)
            (PionCompleteness.Paper.NLSM.Amplitude.avoidingA N K Q)
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.collapse_identity
/--
info: PionCompleteness.Paper.NLSM.Amplitude.strip_factor_value {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {S K : Finset (ℕ × ℕ)}
  {P t b : ℕ × ℕ} (h : PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses N S K P t b) :
  ∃ ε,
    ε ≠ 0 ∧
      PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong {X | PionCompleteness.ChainSlice.OnLocus N S X}
        (PionCompleteness.Paper.NLSM.Amplitude.residueHyperplane N S P)
        (PionCompleteness.Paper.NLSM.Amplitude.stripFactor N P t b - ↑ε)
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.strip_factor_value
/--
info: PionCompleteness.Paper.NLSM.Amplitude.avoidingB_top_eq {N : ℕ} {S K : Finset (ℕ × ℕ)} {P t b : ℕ × ℕ}
  (h : PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses N S K P t b) :
  PionCompleteness.Paper.NLSM.Amplitude.avoidingB N K t = PionCompleteness.Paper.NLSM.Amplitude.childAmpB N t
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.avoidingB_top_eq
/--
info: PionCompleteness.Paper.NLSM.Amplitude.avoidingA_bottom_eq {N : ℕ} {S K : Finset (ℕ × ℕ)} {P t b : ℕ × ℕ}
  (h : PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses N S K P t b) :
  PionCompleteness.Paper.NLSM.Amplitude.avoidingA N K b = PionCompleteness.Paper.NLSM.Amplitude.childAmpA N b
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.avoidingA_bottom_eq
/--
info: PionCompleteness.Paper.NLSM.Amplitude.simple_pole_along_flank_class {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
  {S K : Finset (ℕ × ℕ)} {P t b : ℕ × ℕ}
  (h : PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses N S K P t b) :
  PionCompleteness.Paper.NLSM.Amplitude.HasNoPoleAlong {X | PionCompleteness.ChainSlice.OnLocus N S X}
      (PionCompleteness.Paper.NLSM.Amplitude.residueHyperplane N S P)
      (PionCompleteness.PionNLSM.gen P * PionCompleteness.PionNLSM.NLSM N PionCompleteness.PionNLSM.gen) ∧
    PionCompleteness.Paper.NLSM.Amplitude.HasNoPoleAlong {X | PionCompleteness.ChainSlice.OnLocus N S X}
        (PionCompleteness.Paper.NLSM.Amplitude.residueHyperplane N S P)
        (PionCompleteness.Paper.NLSM.Amplitude.childAmpB N t) ∧
      PionCompleteness.Paper.NLSM.Amplitude.HasNoPoleAlong {X | PionCompleteness.ChainSlice.OnLocus N S X}
          (PionCompleteness.Paper.NLSM.Amplitude.residueHyperplane N S P)
          (PionCompleteness.Paper.NLSM.Amplitude.childAmpA N b) ∧
        ∃ ε,
          ε ≠ 0 ∧
            PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong {X | PionCompleteness.ChainSlice.OnLocus N S X}
              (PionCompleteness.Paper.NLSM.Amplitude.residueHyperplane N S P)
              (PionCompleteness.PionNLSM.gen P * PionCompleteness.PionNLSM.NLSM N PionCompleteness.PionNLSM.gen -
                ↑ε * PionCompleteness.Paper.NLSM.Amplitude.childAmpB N t *
                  PionCompleteness.Paper.NLSM.Amplitude.childAmpA N b)
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.simple_pole_along_flank_class
/--
info: PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.strip_pairs_positions {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0)
  {S : Finset (ℕ × ℕ)} {Q Q' : ℕ × ℕ} (hQ : Q ∈ PionCompleteness.Pi.cleanChords N S)
  (hQ' : Q' ∈ PionCompleteness.Pi.cleanChords N S)
  (hsub : PionCompleteness.Pi.oddSide N Q' ⊆ PionCompleteness.Pi.oddSide N Q) (hne : Q ≠ Q')
  (hh : PionCompleteness.Pi.hitSet N S Q = PionCompleteness.Pi.hitSet N S Q') {X : ℕ × ℕ → ℚ}
  (hX : PionCompleteness.ChainSlice.OnLocus N S X) :
  (∀ (a b : ℕ),
      (a, b) ∈ PionCompleteness.TreeRectangleZero.diagonals N →
        PionCompleteness.Pi.pkRBTP N Q Q' a b → PionCompleteness.TreeRectangleZero.mesh N X a b = 0) ∧
    PionCompleteness.Pi.pkRBOT N (PionCompleteness.Pi.headStart Q)
      (PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart Q) (PionCompleteness.Pi.headStart Q'))
      (PionCompleteness.Pi.headLen N Q) (PionCompleteness.Pi.headLen N Q') X
-/
#guard_msgs in
#check PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.strip_pairs_positions
/--
info: PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.strip_regions {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {S : Finset (ℕ × ℕ)}
  {Q Q' : ℕ × ℕ} (hQ : Q ∈ PionCompleteness.Pi.cleanChords N S) (hQ' : Q' ∈ PionCompleteness.Pi.cleanChords N S)
  (hsub : PionCompleteness.Pi.oddSide N Q' ⊆ PionCompleteness.Pi.oddSide N Q) (hne : Q ≠ Q')
  (hh : PionCompleteness.Pi.hitSet N S Q = PionCompleteness.Pi.hitSet N S Q') {X : ℕ × ℕ → ℚ}
  (hX : PionCompleteness.ChainSlice.OnLocus N S X) :
  ((∀ u ∈ PionCompleteness.Pi.oddSide N Q \ PionCompleteness.Pi.oddSide N Q',
        ∀ v ∈ PionCompleteness.Pi.oddSide N Q \ PionCompleteness.Pi.oddSide N Q',
          u ≠ v → u % 2 = v % 2 → PionCompleteness.TreeRectangleZero.mesh N X u v = 0) ∧
      (∀ u ∈ PionCompleteness.Pi.oddSide N Q \ PionCompleteness.Pi.oddSide N Q',
          u % 2 = 1 → ∑ w ∈ PionCompleteness.Pi.oddSide N Q', PionCompleteness.TreeRectangleZero.mesh N X u w = 0) ∧
        ∀ u ∈ PionCompleteness.Pi.oddSide N Q \ PionCompleteness.Pi.oddSide N Q',
          u % 2 = 0 → ∑ w ∈ PionCompleteness.Pi.evenSide N Q, PionCompleteness.TreeRectangleZero.mesh N X u w = 0) ∧
    ((PionCompleteness.Pi.cycPos N (PionCompleteness.Pi.headStart Q) (PionCompleteness.Pi.headStart Q') + 1) % 2 ≠
          PionCompleteness.Pi.pkRBOmM N Q Q' % 2 ∧
        X Q = X Q') ∧
      (∀ u ∈ PionCompleteness.Pi.oddSide N Q \ PionCompleteness.Pi.oddSide N Q',
          u % 2 = 1 → ∀ w ∈ PionCompleteness.Pi.oddSide N Q', PionCompleteness.TreeRectangleZero.mesh N X u w = 0) ∧
        ∀ u ∈ PionCompleteness.Pi.oddSide N Q \ PionCompleteness.Pi.oddSide N Q',
          u % 2 = 0 → ∀ w ∈ PionCompleteness.Pi.evenSide N Q, PionCompleteness.TreeRectangleZero.mesh N X u w = 0
-/
#guard_msgs in
#check PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.strip_regions
/--
info: def PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.planarWithSides.{u_1} : {F : Type u_1} →
  [Field F] → ℕ → (ℕ × ℕ → F) → (ℕ → F) → ℕ → ℕ → F :=
fun {F} [Field F] n X m i j =>
  if PionCompleteness.TreeRectangleZero.vtx n j = PionCompleteness.TreeRectangleZero.vtx n (i + 1) then
    m (PionCompleteness.TreeRectangleZero.vtx n i)
  else
    if PionCompleteness.TreeRectangleZero.vtx n i = PionCompleteness.TreeRectangleZero.vtx n (j + 1) then
      m (PionCompleteness.TreeRectangleZero.vtx n j)
    else PionCompleteness.TreeRectangleZero.planar n X i j
-/
#guard_msgs in
#print PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.planarWithSides
/--
info: def PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.meshWithSides.{u_1} : {F : Type u_1} →
  [Field F] → ℕ → (ℕ × ℕ → F) → (ℕ → F) → ℕ → ℕ → F :=
fun {F} [Field F] n X m i j =>
  PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.planarWithSides n X m i j +
        PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.planarWithSides n X m (i + 1) (j + 1) -
      PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.planarWithSides n X m i (j + 1) -
    PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.planarWithSides n X m (i + 1) j
-/
#guard_msgs in
#print PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.meshWithSides
/--
info: PionCompleteness.Paper.planar_adjacent.{u_1} {F : Type u_1} [Field F] {n : ℕ} (hn : 1 ≤ n) (X : ℕ × ℕ → F) {i j : ℕ}
  (h : PionCompleteness.TreeRectangleZero.vtx n j = PionCompleteness.TreeRectangleZero.vtx n (i + 1)) :
  PionCompleteness.TreeRectangleZero.planar n X i j = 0
-/
#guard_msgs in
#check PionCompleteness.Paper.planar_adjacent
/--
info: PionCompleteness.Paper.vtx_succ_eq_iff {n : ℕ} (hn : 1 ≤ n) (a b : ℕ) :
  PionCompleteness.TreeRectangleZero.vtx n (a + 1) = PionCompleteness.TreeRectangleZero.vtx n (b + 1) ↔
    PionCompleteness.TreeRectangleZero.vtx n a = PionCompleteness.TreeRectangleZero.vtx n b
-/
#guard_msgs in
#check PionCompleteness.Paper.vtx_succ_eq_iff
/--
info: PionCompleteness.Paper.planarWithSides_eq.{u_1} {F : Type u_1} [Field F] {n : ℕ} (hn3 : 3 ≤ n) (X : ℕ × ℕ → F)
  (m : ℕ → F) (a b : ℕ) :
  PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.planarWithSides n X m a b =
    (PionCompleteness.TreeRectangleZero.planar n X a b +
        if PionCompleteness.TreeRectangleZero.vtx n b = PionCompleteness.TreeRectangleZero.vtx n (a + 1) then
          m (PionCompleteness.TreeRectangleZero.vtx n a)
        else 0) +
      if PionCompleteness.TreeRectangleZero.vtx n a = PionCompleteness.TreeRectangleZero.vtx n (b + 1) then
        m (PionCompleteness.TreeRectangleZero.vtx n b)
      else 0
-/
#guard_msgs in
#check PionCompleteness.Paper.planarWithSides_eq
/--
info: PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.corner_identity.{u_1} {F : Type u_1} [Field F] {n : ℕ} (hn : 4 ≤ n)
  (X : ℕ × ℕ → F) (m : ℕ → F) {i j : ℕ} (hi : i ∈ Finset.Icc 1 n) (hj : j ∈ Finset.Icc 1 n)
  (hij : (min i j, max i j) ∈ PionCompleteness.TreeRectangleZero.diagonals n) :
  PionCompleteness.TreeRectangleZero.mesh n X i j =
    (PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.meshWithSides n X m i j +
        if PionCompleteness.TreeRectangleZero.vtx n j = PionCompleteness.TreeRectangleZero.vtx n (i + 2) then
          m (PionCompleteness.TreeRectangleZero.vtx n (i + 1))
        else 0) +
      if PionCompleteness.TreeRectangleZero.vtx n i = PionCompleteness.TreeRectangleZero.vtx n (j + 2) then
        m (PionCompleteness.TreeRectangleZero.vtx n (j + 1))
      else 0
-/
#guard_msgs in
#check PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.corner_identity
/--
info: def PionCompleteness.Paper.NLSM.Amplitude.earLocus : ℕ → Finset ℕ → Finset (ℕ × ℕ) → (ℕ × ℕ → ℚ) → Prop :=
fun n R K X =>
  (∀ a ∈ Finset.Icc 1 n,
      ∀ b ∈ Finset.Icc 1 n,
        a % 2 = 1 → a ∉ R → b % 2 = 1 → b ∉ R → PionCompleteness.TreeRectangleZero.mesh n X a b = 0) ∧
    (∀ a ∈ Finset.Icc 1 n, a % 2 = 1 → a ∉ R → ∀ w ∈ R, PionCompleteness.TreeRectangleZero.mesh n X a w = 0) ∧
      ∀ Q ∈ K,
        ∀ w ∈ PionCompleteness.Pi.oddSide n Q,
          w % 2 = 0 →
            ∀ a ∈ PionCompleteness.Pi.evenSide n Q, a % 2 = 1 → PionCompleteness.TreeRectangleZero.mesh n X w a = 0
-/
#guard_msgs in
#print PionCompleteness.Paper.NLSM.Amplitude.earLocus
/--
info: PionCompleteness.Paper.mem_oddSide_iff_interval {n : ℕ} {Q : ℕ × ℕ} (hQ : Q ∈ PionCompleteness.PionZeros.oddDiagonals n)
  {x : ℕ} (hx : x ∈ Finset.Icc 1 n) : x ∈ PionCompleteness.Pi.oddSide n Q ↔ (Q.1 ≤ x ∧ x < Q.2 ↔ Q.1 % 2 = 1)
-/
#guard_msgs in
#check PionCompleteness.Paper.mem_oddSide_iff_interval
/--
info: PionCompleteness.Paper.oddSide_sub_Icc {n : ℕ} {Q : ℕ × ℕ} (hQ : Q ∈ PionCompleteness.PionZeros.oddDiagonals n) :
  PionCompleteness.Pi.oddSide n Q ⊆ Finset.Icc 1 n
-/
#guard_msgs in
#check PionCompleteness.Paper.oddSide_sub_Icc
/--
info: PionCompleteness.Paper.NLSM.Amplitude.earLocus_iff {n : ℕ} {R : Finset ℕ} {K : Finset (ℕ × ℕ)} {r₀ : ℕ} (hr₀ : r₀ ∈ R)
  (hK : ∀ Q ∈ K, Q ∈ PionCompleteness.PionZeros.oddDiagonals n ∧ R ⊆ PionCompleteness.Pi.oddSide n Q) (X : ℕ × ℕ → ℚ) :
  PionCompleteness.Paper.NLSM.Amplitude.earLocus n R K X ↔ PionCompleteness.Pi.pkRBZ5 n 1 R K X
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.earLocus_iff
/--
info: PionCompleteness.Paper.NLSM.Amplitude.polygon_numerators_vanish_on_ear_locus {n : ℕ} (hn : 4 ≤ n) (hE : Even n)
  {lo hi : ℕ} (hlo : lo % 2 = 1) (hhi : hi % 2 = 1) (hlh : lo ≤ hi) (h2 : hi < n) (hUV : 1 < lo ∨ hi + 1 < n)
  {K : Finset (ℕ × ℕ)}
  (hK :
    ∀ Q ∈ K,
      Q ∈ PionCompleteness.PionZeros.oddDiagonals n ∧
        Finset.Icc lo hi ⊆ PionCompleteness.Pi.oddSide n Q ∧ n ∉ PionCompleteness.Pi.oddSide n Q)
  (hgen :
    ∀ d ∈ PionCompleteness.PionZeros.oddDiagonals n,
      ∃ X, PionCompleteness.Paper.NLSM.Amplitude.earLocus n (Finset.Icc lo hi) K X ∧ X d ≠ 0) :
  PionCompleteness.PionNLSM.RatZeroOn {X | PionCompleteness.Paper.NLSM.Amplitude.earLocus n (Finset.Icc lo hi) K X}
      (PionCompleteness.PionNLSM.NLSM n PionCompleteness.PionNLSM.gen) ∧
    (∀ Q ∈ K,
        PionCompleteness.PionNLSM.RatZeroOn
          {X | PionCompleteness.Paper.NLSM.Amplitude.earLocus n (Finset.Icc lo hi) K X}
          (PionCompleteness.Paper.NLSM.Amplitude.childAmpB n Q)) ∧
      PionCompleteness.PionNLSM.RatZeroOn {X | PionCompleteness.Paper.NLSM.Amplitude.earLocus n (Finset.Icc lo hi) K X}
        (PionCompleteness.Paper.NLSM.Amplitude.nlsmAvoiding n K PionCompleteness.PionNLSM.gen)
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.polygon_numerators_vanish_on_ear_locus
/--
info: PionCompleteness.Paper.NLSM.Amplitude.genericity {n : ℕ} (hE : Even n) (hn : 4 ≤ n) (d₁ : ℕ) (hd : 2 * d₁ + 2 ≤ n)
  {Q : ℕ × ℕ} (hQ : Q ∈ PionCompleteness.PionZeros.oddDiagonals n) :
  ∃ X, PionCompleteness.Pi.pkRLam n d₁ ∅ X ∧ PionCompleteness.TreeRectangleZero.mesh n X 1 (n - 1) = 0 ∧ X Q ≠ 0
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.genericity
/--
info: PionCompleteness.Paper.NLSM.Amplitude.genericity_span {n : ℕ} (hE : Even n) (hn : 4 ≤ n) (d₁ : ℕ) (hd : 2 * d₁ + 2 ≤ n)
  {Q Q' : ℕ × ℕ} (hQ : Q ∈ PionCompleteness.PionZeros.oddDiagonals n)
  (hQ' : Q' ∈ PionCompleteness.PionZeros.oddDiagonals n) (hne : Q ≠ Q') :
  ¬∃ α β,
      ∀ (X : ℕ × ℕ → ℚ),
        PionCompleteness.Pi.pkRLam n d₁ ∅ X → X Q' = α * X Q + β * PionCompleteness.TreeRectangleZero.mesh n X 1 (n - 1)
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.genericity_span
/--
info: PionCompleteness.Paper.NLSM.Amplitude.genericity_double_prime {n : ℕ} (hE : Even n) (hn : 4 ≤ n) (d₁ : ℕ) (hd1 : 1 ≤ d₁)
  (hd : 2 * d₁ + 2 ≤ n) {Q : ℕ × ℕ} (hQ : Q ∈ PionCompleteness.PionZeros.oddDiagonals n)
  (hne : Q ≠ PionCompleteness.Pi.pkRMchord d₁ (d₁ - 1, 0)) :
  ∃ X,
    PionCompleteness.Pi.pkRLam n d₁ {(d₁ - 1, 0)} X ∧
      PionCompleteness.TreeRectangleZero.mesh n X 1 (n - 1) = 0 ∧ X Q ≠ 0
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.genericity_double_prime
/--
info: PionCompleteness.Paper.NLSM.Amplitude.genericity_w_independent {n : ℕ} (hE : Even n) (hn : 4 ≤ n) {d₁ : ℕ} {q : ℕ × ℕ}
  (hq : PionCompleteness.Pi.pkRIsMem n d₁ q) :
  (∀ (X : ℕ × ℕ → ℚ),
      PionCompleteness.Pi.pkRW n d₁ q X →
        PionCompleteness.TreeRectangleZero.mesh n X (PionCompleteness.Pi.pkRCstp n d₁).1
            (PionCompleteness.Pi.pkRCstp n d₁).2 =
          PionCompleteness.TreeRectangleZero.mesh n X 1 (n - 1) +
            PionCompleteness.TreeRectangleZero.mesh n X (PionCompleteness.Pi.pkRTau d₁ q).1
              (PionCompleteness.Pi.pkRTau d₁ q).2) ∧
    ∀ (α β : ℚ),
      (∀ (X : ℕ × ℕ → ℚ),
          PionCompleteness.Pi.pkRW n d₁ q X →
            α * PionCompleteness.TreeRectangleZero.mesh n X 1 (n - 1) +
                β *
                  PionCompleteness.TreeRectangleZero.mesh n X (PionCompleteness.Pi.pkRCstp n d₁).1
                    (PionCompleteness.Pi.pkRCstp n d₁).2 =
              0) →
        α = 0 ∧ β = 0
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.genericity_w_independent
/--
info: PionCompleteness.Paper.NLSM.Amplitude.genericity_closed {n : ℕ} (hE : Even n) (hn : 4 ≤ n) {d₁ : ℕ}
  (hd : 2 * d₁ + 2 ≤ n) {I : Finset (ℕ × ℕ)} (hI : ∀ Q ∈ I, PionCompleteness.Pi.pkRIsMem n d₁ Q)
  (hcl : PionCompleteness.Pi.pkRClosed n d₁ I) {Q : ℕ × ℕ} (hQ : Q ∈ PionCompleteness.PionZeros.oddDiagonals n)
  (hnot : ∀ Q' ∈ I, Q ≠ PionCompleteness.Pi.pkRMchord d₁ Q') :
  ∃ X, PionCompleteness.Pi.pkRLam n d₁ I X ∧ PionCompleteness.TreeRectangleZero.mesh n X 1 (n - 1) = 0 ∧ X Q ≠ 0
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.genericity_closed
/--
info: PionCompleteness.Paper.NLSM.Amplitude.genericity_w_pairs {n : ℕ} (hE : Even n) (hn : 4 ≤ n) {d₁ : ℕ} {q : ℕ × ℕ}
  (hq : PionCompleteness.Pi.pkRIsMem n d₁ q) {Q : ℕ × ℕ} (hQ : Q ∈ PionCompleteness.PionZeros.oddDiagonals n)
  (hne : Q ≠ PionCompleteness.Pi.pkRMchord d₁ q) :
  have cs := fun X => PionCompleteness.TreeRectangleZero.mesh n X 1 (n - 1);
  have cp := fun X =>
    PionCompleteness.TreeRectangleZero.mesh n X (PionCompleteness.Pi.pkRCstp n d₁).1
      (PionCompleteness.Pi.pkRCstp n d₁).2;
  have xQ := fun X => X Q;
  have nonProp := fun f g => ∀ (c : ℚ), ¬∀ (X : ℕ × ℕ → ℚ), PionCompleteness.Pi.pkRW n d₁ q X → f X = c * g X;
  (∃ X, PionCompleteness.Pi.pkRW n d₁ q X ∧ cs X ≠ 0) ∧
    (∃ X, PionCompleteness.Pi.pkRW n d₁ q X ∧ cp X ≠ 0) ∧
      (∃ X, PionCompleteness.Pi.pkRW n d₁ q X ∧ xQ X ≠ 0) ∧
        nonProp cs cp ∧ nonProp cp cs ∧ nonProp xQ cs ∧ nonProp cs xQ ∧ nonProp xQ cp ∧ nonProp cp xQ
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.genericity_w_pairs
/--
info: PionCompleteness.Paper.NLSM.Amplitude.markedLocus_mono {n d₁ : ℕ} {I I' : Finset (ℕ × ℕ)} (h : I' ⊆ I) {X : ℕ × ℕ → ℚ}
  (hX : PionCompleteness.Pi.pkRLam n d₁ I X) : PionCompleteness.Pi.pkRLam n d₁ I' X
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.markedLocus_mono
/--
info: PionCompleteness.Paper.NLSM.Amplitude.genericity_regions {n : ℕ} (hE : Even n) (hn : 4 ≤ n) {d₁ : ℕ}
  {I : Finset (ℕ × ℕ)} (hI : ∀ Q ∈ I, PionCompleteness.Pi.pkRIsMem n d₁ Q) {X : ℕ × ℕ → ℚ}
  (hX : PionCompleteness.Pi.pkRLam n d₁ I X) :
  (∀ Q ∈ I, X (PionCompleteness.Pi.pkRMchord d₁ Q) = PionCompleteness.TreeRectangleZero.mesh n X 1 (n - 1)) ∧
    (∀ q ∈ I,
        PionCompleteness.Pi.pkRLam (2 * d₁ + 2 * q.2 + 2 - (2 * q.1 + 1) + 1) (d₁ - q.1)
            (Finset.image (fun Q => (Q.1 - q.1, Q.2)) ({Q ∈ I | q.1 ≤ Q.1 ∧ Q.2 ≤ q.2 ∧ Q ≠ q}))
            (X ∘ PionCompleteness.PionNLSM.relab n (2 * q.1 + 1)) ∧
          PionCompleteness.TreeRectangleZero.mesh (2 * d₁ + 2 * q.2 + 2 - (2 * q.1 + 1) + 1)
              (X ∘ PionCompleteness.PionNLSM.relab n (2 * q.1 + 1)) 1 (2 * d₁ + 2 * q.2 + 2 - (2 * q.1 + 1) + 1 - 1) =
            PionCompleteness.TreeRectangleZero.mesh n X 1 (n - 1)) ∧
      ∀ q ∈ I,
        PionCompleteness.Pi.pkRLam (n - (2 * d₁ + 2 * q.2 + 2) + (2 * q.1 + 1) + 1) q.1
            (Finset.image (fun Q => (Q.1, Q.2 - q.2)) ({Q ∈ I | Q.1 ≤ q.1 ∧ q.2 ≤ Q.2 ∧ Q ≠ q}))
            (X ∘
              PionCompleteness.PionNLSM.relab n (2 * d₁ + 2 * q.2 + 2) ∘
                (PionCompleteness.TreeRectangleZero.rot
                    (n - (2 * d₁ + 2 * q.2 + 2) + (2 * q.1 + 1) + 1))^[n - (2 * d₁ + 2 * q.2 + 2) + 1]) ∧
          PionCompleteness.TreeRectangleZero.mesh (n - (2 * d₁ + 2 * q.2 + 2) + (2 * q.1 + 1) + 1)
              (X ∘
                PionCompleteness.PionNLSM.relab n (2 * d₁ + 2 * q.2 + 2) ∘
                  (PionCompleteness.TreeRectangleZero.rot
                      (n - (2 * d₁ + 2 * q.2 + 2) + (2 * q.1 + 1) + 1))^[n - (2 * d₁ + 2 * q.2 + 2) + 1])
              1 (n - (2 * d₁ + 2 * q.2 + 2) + (2 * q.1 + 1) + 1 - 1) =
            PionCompleteness.TreeRectangleZero.mesh n X 1 (n - 1)
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.genericity_regions
/--
info: PionCompleteness.Paper.NLSM.Amplitude.polygon_numerator_value {n : ℕ} (hE : Even n) (hn : 4 ≤ n) (d₁ : ℕ)
  (hd : 2 * d₁ + 2 ≤ n) (I : Finset (ℕ × ℕ)) (hI : ∀ Q ∈ I, PionCompleteness.Pi.pkRIsMem n d₁ Q)
  (hcl : PionCompleteness.Pi.pkRClosed n d₁ I) :
  ∃ c F,
    c ≠ 0 ∧
      (∀ (X : ℕ × ℕ → ℚ),
          PionCompleteness.Pi.pkRLam n d₁ I X →
            (∀ d ∈ PionCompleteness.PionZeros.oddDiagonals n, X d ≠ 0) →
              PionCompleteness.PionNLSM.NLSM n X =
                c * PionCompleteness.TreeRectangleZero.mesh n X 1 (n - 1) +
                  PionCompleteness.TreeRectangleZero.mesh n X 1 (n - 1) ^ 2 *
                    ((MvPolynomial.eval X) F /
                      ∏ Q ∈ PionCompleteness.PionZeros.oddDiagonals n with
                        Q ∉ Finset.image (PionCompleteness.Pi.pkRMchord d₁) I, X Q)) ∧
        ∃ X,
          PionCompleteness.Pi.pkRLam n d₁ I X ∧
            PionCompleteness.TreeRectangleZero.mesh n X 1 (n - 1) = 0 ∧
              ∏ Q ∈ PionCompleteness.PionZeros.oddDiagonals n with
                  Q ∉ Finset.image (PionCompleteness.Pi.pkRMchord d₁) I, X Q ≠
                0
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Amplitude.polygon_numerator_value
/--
info: PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.gram_model {n : ℕ} (hn : 4 ≤ n) (hE : Even n) (G : ℕ → ℕ → ℚ)
  (hs : ∀ (a b : ℕ), G a b = G b a) (hd : ∀ (a : ℕ), G a a = 0)
  (hr : ∀ a ∈ Finset.Icc 1 n, ∑ b ∈ Finset.Icc 1 n, G a b = 0) :
  (∀ (i j : ℕ),
      PionCompleteness.Pi.pkRGramPt (fun a b => -2 * G a b) (i, j) = ∑ p ∈ (Finset.Ico i j).offDiag, G p.1 p.2) ∧
    (∀ a ∈ Finset.Icc 1 n,
        ∀ b ∈ Finset.Icc 1 n,
          a ≠ b →
            PionCompleteness.TreeRectangleZero.mesh n (PionCompleteness.Pi.pkRGramPt fun a b => -2 * G a b) a b =
              -2 * G a b) ∧
      ∀ (X : ℕ × ℕ → ℚ),
        ∑ t ∈ PionCompleteness.TreeRectangleZero.diagonals n with t.1 % 2 = 1 ∧ t.2 % 2 = 1,
            PionCompleteness.TreeRectangleZero.mesh n X t.1 t.2 =
          ∑ t ∈ PionCompleteness.TreeRectangleZero.diagonals n with t.1 % 2 = 0 ∧ t.2 % 2 = 0,
            PionCompleteness.TreeRectangleZero.mesh n X t.1 t.2
-/
#guard_msgs in
#check PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.gram_model
/--
info: PionCompleteness.Paper.NLSM.Zeros.child_onLocus {N s k : ℕ} (hs : s ∈ Finset.Icc 1 N) (hk3 : 3 ≤ k) (hkN : k + 3 ≤ N)
  {S : Finset (ℕ × ℕ)} {X : ℕ × ℕ → ℚ} (hX : PionCompleteness.ChainSlice.OnLocus N S X)
  (hXP : PionCompleteness.TreeRectangleZero.planar N X s (s + k) = 0) :
  PionCompleteness.ChainSlice.OnLocus (k + 1)
    ({σ ∈ PionCompleteness.TreeRectangleZero.diagonals (k + 1) |
      PionCompleteness.Pi.ChildPairIn N S s k (k + 1) (fun j => PionCompleteness.TreeRectangleZero.vtx N (s + j - 1))
        σ.1 σ.2})
    fun d => X (PionCompleteness.PionNLSM.relab N s d)
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.child_onLocus
/--
info: PionCompleteness.Paper.NLSM.Zeros.children_of_odd_chord_locus {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {S : Finset (ℕ × ℕ)}
  (hS : S ⊆ PionCompleteness.TreeRectangleZero.diagonals N) {P : ℕ × ℕ} (hP : P ∈ PionCompleteness.Pi.poleChords N S) :
  ((∀ (X : ℕ × ℕ → ℚ),
        PionCompleteness.ChainSlice.OnLocus N S X →
          X P = 0 →
            PionCompleteness.ChainSlice.OnLocus (PionCompleteness.Pi.headLen N P + 1)
              (PionCompleteness.Pi.childSetA N S P) fun d =>
              X (PionCompleteness.PionNLSM.relab N (PionCompleteness.Pi.headStart P) d)) ∧
      ∀ (y : ℕ × ℕ → ℚ),
        PionCompleteness.ChainSlice.OnLocus (PionCompleteness.Pi.headLen N P + 1) (PionCompleteness.Pi.childSetA N S P)
            y →
          ∃ X,
            PionCompleteness.ChainSlice.OnLocus N S X ∧
              X P = 0 ∧
                ∀ d ∈ PionCompleteness.TreeRectangleZero.diagonals (PionCompleteness.Pi.headLen N P + 1),
                  X (PionCompleteness.PionNLSM.relab N (PionCompleteness.Pi.headStart P) d) = y d) ∧
    (∀ (X : ℕ × ℕ → ℚ),
        PionCompleteness.ChainSlice.OnLocus N S X →
          X P = 0 →
            PionCompleteness.ChainSlice.OnLocus (PionCompleteness.Pi.tailLen N P + 1)
              (PionCompleteness.Pi.pkRBChildB' N S P) fun d =>
              X (PionCompleteness.PionNLSM.relab N (PionCompleteness.Pi.tailStart P) d)) ∧
      ∀ (y : ℕ × ℕ → ℚ),
        PionCompleteness.ChainSlice.OnLocus (PionCompleteness.Pi.tailLen N P + 1)
            (PionCompleteness.Pi.pkRBChildB' N S P) y →
          ∃ X,
            PionCompleteness.ChainSlice.OnLocus N S X ∧
              X P = 0 ∧
                ∀ d ∈ PionCompleteness.TreeRectangleZero.diagonals (PionCompleteness.Pi.tailLen N P + 1),
                  X (PionCompleteness.PionNLSM.relab N (PionCompleteness.Pi.tailStart P) d) = y d
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.children_of_odd_chord_locus
/--
info: PionCompleteness.Paper.NLSM.Zeros.children_of_odd_chord_size {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {P : ℕ × ℕ}
  (hPO : P ∈ PionCompleteness.PionZeros.oddDiagonals N) :
  ((PionCompleteness.Pi.oddSide N P).card = PionCompleteness.Pi.headLen N P ∧
      Even (PionCompleteness.Pi.headLen N P + 1) ∧
        4 ≤ PionCompleteness.Pi.headLen N P + 1 ∧ PionCompleteness.Pi.headLen N P + 1 ≤ N - 2) ∧
    (PionCompleteness.Pi.evenSide N P).card = PionCompleteness.Pi.tailLen N P ∧
      Even (PionCompleteness.Pi.tailLen N P + 1) ∧
        4 ≤ PionCompleteness.Pi.tailLen N P + 1 ∧ PionCompleteness.Pi.tailLen N P + 1 ≤ N - 2
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.children_of_odd_chord_size
/--
info: PionCompleteness.Paper.NLSM.Zeros.children_of_odd_chord_linked {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {S : Finset (ℕ × ℕ)}
  (hF : PionCompleteness.Paper.NLSM.Zeros.IsCandidateSet N S) {P : ℕ × ℕ}
  (hPo : P ∈ PionCompleteness.PionZeros.oddDiagonals N) :
  (PionCompleteness.Paper.NLSM.Zeros.IsCandidateSet (PionCompleteness.Pi.headLen N P + 1)
        (PionCompleteness.Pi.childSetA N S P) ↔
      PionCompleteness.Pi.NoFreeSep N S (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P) 0) ∧
    (PionCompleteness.Paper.NLSM.Zeros.IsCandidateSet (PionCompleteness.Pi.tailLen N P + 1)
        (PionCompleteness.Pi.childSetB N S P) ↔
      PionCompleteness.Pi.NoFreeSep N S (PionCompleteness.Pi.tailStart P) (PionCompleteness.Pi.tailLen N P) 1)
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.children_of_odd_chord_linked
/--
info: PionCompleteness.Paper.NLSM.Zeros.children_of_odd_chord_flank_class {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
  {S : Finset (ℕ × ℕ)} (hS : S ⊆ PionCompleteness.TreeRectangleZero.diagonals N) {t b : ℕ × ℕ}
  (ht : t ∈ PionCompleteness.Pi.poleChords N S) (hb : b ∈ PionCompleteness.Pi.hitClass N S t) :
  PionCompleteness.Paper.NLSM.Amplitude.residueHyperplane N S t =
      PionCompleteness.Paper.NLSM.Amplitude.residueHyperplane N S b ∧
    ((∀ X ∈ PionCompleteness.Paper.NLSM.Amplitude.residueHyperplane N S t,
          PionCompleteness.ChainSlice.OnLocus (PionCompleteness.Pi.tailLen N t + 1)
            (PionCompleteness.Pi.pkRBChildB' N S t) fun d =>
            X (PionCompleteness.PionNLSM.relab N (PionCompleteness.Pi.tailStart t) d)) ∧
        ∀ (y : ℕ × ℕ → ℚ),
          PionCompleteness.ChainSlice.OnLocus (PionCompleteness.Pi.tailLen N t + 1)
              (PionCompleteness.Pi.pkRBChildB' N S t) y →
            ∃ X ∈ PionCompleteness.Paper.NLSM.Amplitude.residueHyperplane N S t,
              ∀ d ∈ PionCompleteness.TreeRectangleZero.diagonals (PionCompleteness.Pi.tailLen N t + 1),
                X (PionCompleteness.PionNLSM.relab N (PionCompleteness.Pi.tailStart t) d) = y d) ∧
      ((∀ X ∈ PionCompleteness.Paper.NLSM.Amplitude.residueHyperplane N S t,
            PionCompleteness.ChainSlice.OnLocus (PionCompleteness.Pi.headLen N b + 1)
              (PionCompleteness.Pi.childSetA N S b) fun d =>
              X (PionCompleteness.PionNLSM.relab N (PionCompleteness.Pi.headStart b) d)) ∧
          ∀ (y : ℕ × ℕ → ℚ),
            PionCompleteness.ChainSlice.OnLocus (PionCompleteness.Pi.headLen N b + 1)
                (PionCompleteness.Pi.childSetA N S b) y →
              ∃ X ∈ PionCompleteness.Paper.NLSM.Amplitude.residueHyperplane N S t,
                ∀ d ∈ PionCompleteness.TreeRectangleZero.diagonals (PionCompleteness.Pi.headLen N b + 1),
                  X (PionCompleteness.PionNLSM.relab N (PionCompleteness.Pi.headStart b) d) = y d) ∧
        (PionCompleteness.Pi.NonzeroOn (PionCompleteness.Pi.tailLen N t + 1) (PionCompleteness.Pi.childSetB N S t) →
            ∃ X ∈ PionCompleteness.Paper.NLSM.Amplitude.residueHyperplane N S t,
              (∀ d ∈ PionCompleteness.PionZeros.oddDiagonals (PionCompleteness.Pi.tailLen N t + 1),
                  X (PionCompleteness.PionNLSM.relab N (PionCompleteness.Pi.tailStart t) d) ≠ 0) ∧
                (PionCompleteness.PionNLSM.NLSM (PionCompleteness.Pi.tailLen N t + 1) fun d =>
                    X (PionCompleteness.PionNLSM.relab N (PionCompleteness.Pi.tailStart t) d)) ≠
                  0) ∧
          (PionCompleteness.Pi.NonzeroOn (PionCompleteness.Pi.headLen N b + 1) (PionCompleteness.Pi.childSetA N S b) →
            ∃ X ∈ PionCompleteness.Paper.NLSM.Amplitude.residueHyperplane N S t,
              (∀ d ∈ PionCompleteness.PionZeros.oddDiagonals (PionCompleteness.Pi.headLen N b + 1),
                  X (PionCompleteness.PionNLSM.relab N (PionCompleteness.Pi.headStart b) d) ≠ 0) ∧
                (PionCompleteness.PionNLSM.NLSM (PionCompleteness.Pi.headLen N b + 1) fun d =>
                    X (PionCompleteness.PionNLSM.relab N (PionCompleteness.Pi.headStart b) d)) ≠
                  0)
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.children_of_odd_chord_flank_class
/--
info: PionCompleteness.Paper.cut_planar_child {N k : ℕ} (hkN : k + 3 ≤ N) (Y : ℕ × ℕ → ℚ) {p q : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q)
  (hq : q ≤ k + 1) (hne : ¬(p = 1 ∧ q = k + 1)) :
  PionCompleteness.TreeRectangleZero.planar (k + 1) Y p q = PionCompleteness.TreeRectangleZero.planar N Y p q
-/
#guard_msgs in
#check PionCompleteness.Paper.cut_planar_child
/--
info: PionCompleteness.Paper.cut_planar_child_side {k : ℕ} (hk : 1 ≤ k) (Y : ℕ × ℕ → ℚ) :
  PionCompleteness.TreeRectangleZero.planar (k + 1) Y 1 (k + 1) = 0
-/
#guard_msgs in
#check PionCompleteness.Paper.cut_planar_child_side
/--
info: PionCompleteness.Paper.cut_mesh_inside {N k : ℕ} (hkN : k + 3 ≤ N) (Y : ℕ × ℕ → ℚ) {a b : ℕ} (ha : 1 ≤ a) (hab : a < b)
  (hb : b ≤ k) (hne : ¬(a = 1 ∧ b = k)) :
  PionCompleteness.TreeRectangleZero.mesh (k + 1) Y a b = PionCompleteness.TreeRectangleZero.mesh N Y a b
-/
#guard_msgs in
#check PionCompleteness.Paper.cut_mesh_inside
/--
info: PionCompleteness.Paper.cut_mesh_ends {N k : ℕ} (hk : 3 ≤ k) (hkN : k + 3 ≤ N) (Y : ℕ × ℕ → ℚ) :
  PionCompleteness.TreeRectangleZero.mesh (k + 1) Y 1 k =
    PionCompleteness.TreeRectangleZero.mesh N Y 1 k + PionCompleteness.TreeRectangleZero.planar N Y 1 (k + 1)
-/
#guard_msgs in
#check PionCompleteness.Paper.cut_mesh_ends
/--
info: PionCompleteness.Paper.cut_mesh_hat {N k : ℕ} (hk : 3 ≤ k) (hkN : k + 3 ≤ N) (Y : ℕ × ℕ → ℚ) {j : ℕ} (hj : 2 ≤ j)
  (hjk : j ≤ k - 1) :
  PionCompleteness.TreeRectangleZero.mesh (k + 1) Y j (k + 1) =
    ∑ w ∈ Finset.Icc (k + 1) N, PionCompleteness.TreeRectangleZero.mesh N Y j w
-/
#guard_msgs in
#check PionCompleteness.Paper.cut_mesh_hat
/--
info: @[reducible] def PionCompleteness.Paper.CutUnseen1 : ℕ → ℕ × ℕ → Prop :=
fun k t => k + 1 ≤ t.1 ∨ (t.1 = 1 ∨ t.1 = k) ∧ k + 1 ≤ t.2
-/
#guard_msgs in
#print PionCompleteness.Paper.CutUnseen1
/--
info: PionCompleteness.Paper.cut_sum_split {N k : ℕ} (hk : 3 ≤ k) (hkN : k + 3 ≤ N) (F : ℕ × ℕ → ℚ) :
  ∑ t ∈ PionCompleteness.TreeRectangleZero.diagonals N, F t =
    (∑ σ ∈ PionCompleteness.TreeRectangleZero.diagonals (k + 1),
        if σ.2 = k + 1 then ∑ w ∈ Finset.Icc (k + 1) N, F (σ.1, w) else F σ) +
      ∑ t ∈ PionCompleteness.TreeRectangleZero.diagonals N with (PionCompleteness.Paper.CutUnseen1 k) t, F t
-/
#guard_msgs in
#check PionCompleteness.Paper.cut_sum_split
/--
info: @[reducible] def PionCompleteness.Paper.CutChildIn1 : ℕ → ℕ → Finset (ℕ × ℕ) → ℕ × ℕ → Prop :=
fun N k R σ => if σ.2 = k + 1 then ∀ w ∈ Finset.Icc (k + 1) N, (σ.1, w) ∈ R else σ ∈ R
-/
#guard_msgs in
#print PionCompleteness.Paper.CutChildIn1
/--
info: def PionCompleteness.Paper.cutChildSet1 : ℕ → ℕ → Finset (ℕ × ℕ) → Finset (ℕ × ℕ) :=
fun N k R =>
  Finset.filter (PionCompleteness.Paper.CutChildIn1 N k R) (PionCompleteness.TreeRectangleZero.diagonals (k + 1))
-/
#guard_msgs in
#print PionCompleteness.Paper.cutChildSet1
/--
info: def PionCompleteness.Paper.HasCutAbsorber1 : ℕ → ℕ → Finset (ℕ × ℕ) → Prop :=
fun N k R =>
  (∃ t ∈ PionCompleteness.TreeRectangleZero.diagonals N,
      t ∉ R ∧ t.1 % 2 = t.2 % 2 ∧ PionCompleteness.Paper.CutUnseen1 k t) ∨
    ∃ j ∈ Finset.Icc 2 (k - 1),
      ∃ w ∈ Finset.Icc (k + 1) N, ∃ w' ∈ Finset.Icc (k + 1) N, w % 2 ≠ w' % 2 ∧ (j, w) ∉ R ∧ (j, w') ∉ R
-/
#guard_msgs in
#print PionCompleteness.Paper.HasCutAbsorber1
/--
info: def PionCompleteness.Paper.cutVal : ℕ → ℕ → (ℕ × ℕ → ℚ) → ℕ × ℕ → ℚ :=
fun N k y σ => if σ.2 = k + 1 then ∑ w ∈ Finset.Icc (k + 1) N, y (σ.1, w) else y σ
-/
#guard_msgs in
#print PionCompleteness.Paper.cutVal
/--
info: def PionCompleteness.Paper.cutWeight1 : ℕ → ℕ → Finset (ℕ × ℕ) → ℕ × ℕ → ℚ :=
fun N k R σ =>
  if σ.2 = k + 1 then
    if ∃ w ∈ Finset.Icc (k + 1) N, w % 2 = σ.1 % 2 ∧ (σ.1, w) ∉ R then ↑(PionCompleteness.PionNLSM.shiftSign (σ.1, σ.1))
    else 0
  else ↑(PionCompleteness.PionNLSM.shiftSign σ)
-/
#guard_msgs in
#print PionCompleteness.Paper.cutWeight1
/--
info: def PionCompleteness.Paper.parityVal : ℕ → (ℕ × ℕ → ℚ) → ℚ :=
fun N y => ∑ t ∈ PionCompleteness.TreeRectangleZero.diagonals N, ↑(PionCompleteness.PionNLSM.shiftSign t) * y t
-/
#guard_msgs in
#print PionCompleteness.Paper.parityVal
/--
info: PionCompleteness.Paper.cut_mesh_pull {N k : ℕ} (hk : 3 ≤ k) (hkN : k + 3 ≤ N) (Y : ℕ × ℕ → ℚ) {σ : ℕ × ℕ}
  (hσ : σ ∈ PionCompleteness.TreeRectangleZero.diagonals (k + 1)) :
  PionCompleteness.TreeRectangleZero.mesh (k + 1) Y σ.1 σ.2 =
    PionCompleteness.Paper.cutVal N k (fun t => PionCompleteness.TreeRectangleZero.mesh N Y t.1 t.2) σ +
      if σ = (1, k) then PionCompleteness.TreeRectangleZero.planar N Y 1 (k + 1) else 0
-/
#guard_msgs in
#check PionCompleteness.Paper.cut_mesh_pull
/--
info: PionCompleteness.Paper.parityVal_eq (N : ℕ) (y : ℕ × ℕ → ℚ) :
  PionCompleteness.Paper.parityVal N y =
    ∑ t ∈ PionCompleteness.TreeRectangleZero.diagonals N with t.1 % 2 = 0 ∧ t.2 % 2 = 0, y t -
      ∑ t ∈ PionCompleteness.TreeRectangleZero.diagonals N with t.1 % 2 = 1 ∧ t.2 % 2 = 1, y t
-/
#guard_msgs in
#check PionCompleteness.Paper.parityVal_eq
/--
info: PionCompleteness.Paper.cut_relation1 {N k : ℕ} (hk : 3 ≤ k) (hkN : k + 3 ≤ N) (hko : k % 2 = 1) (Y : ℕ × ℕ → ℚ) :
  PionCompleteness.Paper.parityVal (k + 1)
      (PionCompleteness.Paper.cutVal N k fun t => PionCompleteness.TreeRectangleZero.mesh N Y t.1 t.2) =
    PionCompleteness.TreeRectangleZero.planar N Y 1 (k + 1)
-/
#guard_msgs in
#check PionCompleteness.Paper.cut_relation1
/--
info: PionCompleteness.Paper.cut_planar_diag {n : ℕ} (Y : ℕ × ℕ → ℚ) {p q : ℕ}
  (h : (p, q) ∈ PionCompleteness.TreeRectangleZero.diagonals n) :
  PionCompleteness.TreeRectangleZero.planar n Y p q = Y (p, q)
-/
#guard_msgs in
#check PionCompleteness.Paper.cut_planar_diag
/--
info: PionCompleteness.Paper.cut_canonical1 {N k : ℕ} (hk : 3 ≤ k) (hkN : k + 3 ≤ N) {R : Finset (ℕ × ℕ)}
  (hR : R ⊆ PionCompleteness.TreeRectangleZero.diagonals N) {z : ℕ × ℕ → ℚ}
  (hz : PionCompleteness.ChainSlice.OnLocus (k + 1) (PionCompleteness.Paper.cutChildSet1 N k R) z) :
  ∃ y,
    (∀ t ∈ R, y t = 0) ∧
      ∀ σ ∈ PionCompleteness.TreeRectangleZero.diagonals (k + 1),
        PionCompleteness.Paper.cutVal N k y σ = PionCompleteness.TreeRectangleZero.mesh (k + 1) z σ.1 σ.2
-/
#guard_msgs in
#check PionCompleteness.Paper.cut_canonical1
/--
info: PionCompleteness.Paper.cutVal_add_smul (N k : ℕ) (y κ : ℕ × ℕ → ℚ) (c : ℚ) (σ : ℕ × ℕ) :
  PionCompleteness.Paper.cutVal N k (fun t => y t + c * κ t) σ =
    PionCompleteness.Paper.cutVal N k y σ + c * PionCompleteness.Paper.cutVal N k κ σ
-/
#guard_msgs in
#check PionCompleteness.Paper.cutVal_add_smul
/--
info: PionCompleteness.Paper.parityVal_add_smul (N : ℕ) (y κ : ℕ × ℕ → ℚ) (c : ℚ) :
  (PionCompleteness.Paper.parityVal N fun t => y t + c * κ t) =
    PionCompleteness.Paper.parityVal N y + c * PionCompleteness.Paper.parityVal N κ
-/
#guard_msgs in
#check PionCompleteness.Paper.parityVal_add_smul
/--
info: PionCompleteness.Paper.cut_lift1 {N k : ℕ} (hE : N % 2 = 0) (hk : 3 ≤ k) (hkN : k + 3 ≤ N) (hko : k % 2 = 1)
  {R : Finset (ℕ × ℕ)} (hR : R ⊆ PionCompleteness.TreeRectangleZero.diagonals N) {z y : ℕ × ℕ → ℚ}
  (hy0 : ∀ t ∈ R, y t = 0)
  (hyz :
    ∀ σ ∈ PionCompleteness.TreeRectangleZero.diagonals (k + 1),
      PionCompleteness.Paper.cutVal N k y σ = PionCompleteness.TreeRectangleZero.mesh (k + 1) z σ.1 σ.2)
  (hrel : PionCompleteness.Paper.parityVal N y = 0) :
  ∃ Y,
    PionCompleteness.ChainSlice.OnLocus N R Y ∧
      PionCompleteness.TreeRectangleZero.planar N Y 1 (k + 1) = 0 ∧
        ∀ d ∈ PionCompleteness.TreeRectangleZero.diagonals (k + 1), Y d = z d
-/
#guard_msgs in
#check PionCompleteness.Paper.cut_lift1
/--
info: PionCompleteness.Paper.shiftSign_of_parity_ne {t : ℕ × ℕ} (h : t.1 % 2 ≠ t.2 % 2) :
  PionCompleteness.PionNLSM.shiftSign t = 0
-/
#guard_msgs in
#check PionCompleteness.Paper.shiftSign_of_parity_ne
/--
info: PionCompleteness.Paper.shiftSign_ne_zero_of_parity {t : ℕ × ℕ} (h : t.1 % 2 = t.2 % 2) :
  ↑(PionCompleteness.PionNLSM.shiftSign t) ≠ 0
-/
#guard_msgs in
#check PionCompleteness.Paper.shiftSign_ne_zero_of_parity
/--
info: PionCompleteness.Paper.cut_parity_split {N k : ℕ} (hk : 3 ≤ k) (hkN : k + 3 ≤ N) {R : Finset (ℕ × ℕ)}
  (hno : ¬PionCompleteness.Paper.HasCutAbsorber1 N k R) {y : ℕ × ℕ → ℚ} (hy0 : ∀ t ∈ R, y t = 0) :
  PionCompleteness.Paper.parityVal N y =
    ∑ σ ∈ PionCompleteness.TreeRectangleZero.diagonals (k + 1),
      PionCompleteness.Paper.cutWeight1 N k R σ * PionCompleteness.Paper.cutVal N k y σ
-/
#guard_msgs in
#check PionCompleteness.Paper.cut_parity_split
/--
info: PionCompleteness.Paper.parityVal_mesh {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (Y : ℕ × ℕ → ℚ) :
  (PionCompleteness.Paper.parityVal N fun t => PionCompleteness.TreeRectangleZero.mesh N Y t.1 t.2) = 0
-/
#guard_msgs in
#check PionCompleteness.Paper.parityVal_mesh
/--
info: PionCompleteness.Paper.cut_correct {N k : ℕ} {R : Finset (ℕ × ℕ)} {y κ z : ℕ × ℕ → ℚ} (hy0 : ∀ t ∈ R, y t = 0)
  (hyz :
    ∀ σ ∈ PionCompleteness.TreeRectangleZero.diagonals (k + 1),
      PionCompleteness.Paper.cutVal N k y σ = PionCompleteness.TreeRectangleZero.mesh (k + 1) z σ.1 σ.2)
  (hκ0 : ∀ t ∈ R, κ t = 0)
  (hκz : ∀ σ ∈ PionCompleteness.TreeRectangleZero.diagonals (k + 1), PionCompleteness.Paper.cutVal N k κ σ = 0)
  (hκ : PionCompleteness.Paper.parityVal N κ ≠ 0) :
  ∃ y',
    (∀ t ∈ R, y' t = 0) ∧
      (∀ σ ∈ PionCompleteness.TreeRectangleZero.diagonals (k + 1),
          PionCompleteness.Paper.cutVal N k y' σ = PionCompleteness.TreeRectangleZero.mesh (k + 1) z σ.1 σ.2) ∧
        PionCompleteness.Paper.parityVal N y' = 0
-/
#guard_msgs in
#check PionCompleteness.Paper.cut_correct
/--
info: PionCompleteness.Paper.cut_onto1 {N k : ℕ} (hE : N % 2 = 0) (hk : 3 ≤ k) (hkN : k + 3 ≤ N) (hko : k % 2 = 1)
  {R : Finset (ℕ × ℕ)} (hR : R ⊆ PionCompleteness.TreeRectangleZero.diagonals N)
  (hab :
    PionCompleteness.Paper.HasCutAbsorber1 N k R ∨
      ∀ t ∈ PionCompleteness.TreeRectangleZero.diagonals N, t ∉ R → t.1 % 2 ≠ t.2 % 2)
  {z : ℕ × ℕ → ℚ} (hz : PionCompleteness.ChainSlice.OnLocus (k + 1) (PionCompleteness.Paper.cutChildSet1 N k R) z) :
  ∃ Y,
    PionCompleteness.ChainSlice.OnLocus N R Y ∧
      PionCompleteness.TreeRectangleZero.planar N Y 1 (k + 1) = 0 ∧
        ∀ d ∈ PionCompleteness.TreeRectangleZero.diagonals (k + 1), Y d = z d
-/
#guard_msgs in
#check PionCompleteness.Paper.cut_onto1
/--
info: PionCompleteness.Paper.cut_hyperplane1 {N k : ℕ} (hE : N % 2 = 0) (hk : 3 ≤ k) (hkN : k + 3 ≤ N) (hko : k % 2 = 1)
  {R : Finset (ℕ × ℕ)} (hR : R ⊆ PionCompleteness.TreeRectangleZero.diagonals N)
  (hno : ¬PionCompleteness.Paper.HasCutAbsorber1 N k R)
  (hsame : ∃ t ∈ PionCompleteness.TreeRectangleZero.diagonals N, t ∉ R ∧ t.1 % 2 = t.2 % 2)
  (hX0 :
    ∃ Y0, PionCompleteness.ChainSlice.OnLocus N R Y0 ∧ PionCompleteness.TreeRectangleZero.planar N Y0 1 (k + 1) ≠ 0) :
  (∀ (z : ℕ × ℕ → ℚ),
      PionCompleteness.ChainSlice.OnLocus (k + 1) (PionCompleteness.Paper.cutChildSet1 N k R) z →
        ((∃ Y,
            PionCompleteness.ChainSlice.OnLocus N R Y ∧
              PionCompleteness.TreeRectangleZero.planar N Y 1 (k + 1) = 0 ∧
                ∀ d ∈ PionCompleteness.TreeRectangleZero.diagonals (k + 1), Y d = z d) ↔
          ∑ σ ∈ PionCompleteness.TreeRectangleZero.diagonals (k + 1),
              PionCompleteness.Paper.cutWeight1 N k R σ * PionCompleteness.TreeRectangleZero.mesh (k + 1) z σ.1 σ.2 =
            0)) ∧
    ∃ z,
      PionCompleteness.ChainSlice.OnLocus (k + 1) (PionCompleteness.Paper.cutChildSet1 N k R) z ∧
        ∑ σ ∈ PionCompleteness.TreeRectangleZero.diagonals (k + 1),
            PionCompleteness.Paper.cutWeight1 N k R σ * PionCompleteness.TreeRectangleZero.mesh (k + 1) z σ.1 σ.2 ≠
          0
-/
#guard_msgs in
#check PionCompleteness.Paper.cut_hyperplane1
/--
info: PionCompleteness.Paper.relab_mem_diagonals_iff {N s a b : ℕ} (hs : 1 ≤ s ∧ s ≤ N) (ha : 1 ≤ a) (hab : a < b)
  (hb : b ≤ N) :
  (a, b) ∈ PionCompleteness.TreeRectangleZero.diagonals N ↔
    PionCompleteness.PionNLSM.relab N s (a, b) ∈ PionCompleteness.TreeRectangleZero.diagonals N
-/
#guard_msgs in
#check PionCompleteness.Paper.relab_mem_diagonals_iff
/--
info: PionCompleteness.Paper.rot_planar_lt {N s : ℕ} (hs : 1 ≤ s ∧ s ≤ N) (X : ℕ × ℕ → ℚ) {A B : ℕ} (hA : 1 ≤ A) (hAB : A < B)
  (hB : B ≤ N) :
  PionCompleteness.TreeRectangleZero.planar N (fun r => X (PionCompleteness.PionNLSM.relab N s r)) A B =
    PionCompleteness.TreeRectangleZero.planar N X (A + s - 1) (B + s - 1)
-/
#guard_msgs in
#check PionCompleteness.Paper.rot_planar_lt
/--
info: PionCompleteness.Paper.rot_planar {N s : ℕ} (hs : 1 ≤ s ∧ s ≤ N) (X : ℕ × ℕ → ℚ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
  PionCompleteness.TreeRectangleZero.planar N (fun r => X (PionCompleteness.PionNLSM.relab N s r)) a b =
    PionCompleteness.TreeRectangleZero.planar N X (a + s - 1) (b + s - 1)
-/
#guard_msgs in
#check PionCompleteness.Paper.rot_planar
/--
info: PionCompleteness.Paper.rot_mesh {N s : ℕ} (hs : 1 ≤ s ∧ s ≤ N) (X : ℕ × ℕ → ℚ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
  PionCompleteness.TreeRectangleZero.mesh N (fun r => X (PionCompleteness.PionNLSM.relab N s r)) a b =
    PionCompleteness.TreeRectangleZero.mesh N X (a + s - 1) (b + s - 1)
-/
#guard_msgs in
#check PionCompleteness.Paper.rot_mesh
/--
info: PionCompleteness.Paper.mesh_relab {N s : ℕ} (hN : 1 ≤ N) (X : ℕ × ℕ → ℚ) (r : ℕ × ℕ) :
  PionCompleteness.TreeRectangleZero.mesh N X (PionCompleteness.PionNLSM.relab N s r).1
      (PionCompleteness.PionNLSM.relab N s r).2 =
    PionCompleteness.TreeRectangleZero.mesh N X (r.1 + s - 1) (r.2 + s - 1)
-/
#guard_msgs in
#check PionCompleteness.Paper.mesh_relab
/--
info: def PionCompleteness.Paper.rotInv : ℕ → ℕ → ℕ :=
fun N s => if s = 1 then 1 else N + 2 - s
-/
#guard_msgs in
#print PionCompleteness.Paper.rotInv
/--
info: PionCompleteness.Paper.rotInv_mem {N s : ℕ} (hs : 1 ≤ s ∧ s ≤ N) :
  1 ≤ PionCompleteness.Paper.rotInv N s ∧ PionCompleteness.Paper.rotInv N s ≤ N
-/
#guard_msgs in
#check PionCompleteness.Paper.rotInv_mem
/--
info: PionCompleteness.Paper.rotInv_rotInv {N s : ℕ} (hs : 1 ≤ s ∧ s ≤ N) :
  PionCompleteness.Paper.rotInv N (PionCompleteness.Paper.rotInv N s) = s
-/
#guard_msgs in
#check PionCompleteness.Paper.rotInv_rotInv
/--
info: PionCompleteness.Paper.relab_rotInv {N s : ℕ} (hs : 1 ≤ s ∧ s ≤ N) {t : ℕ × ℕ}
  (ht : t ∈ PionCompleteness.TreeRectangleZero.diagonals N) :
  PionCompleteness.PionNLSM.relab N s (PionCompleteness.PionNLSM.relab N (PionCompleteness.Paper.rotInv N s) t) = t
-/
#guard_msgs in
#check PionCompleteness.Paper.relab_rotInv
/--
info: def PionCompleteness.Paper.rotSet : ℕ → ℕ → Finset (ℕ × ℕ) → Finset (ℕ × ℕ) :=
fun N s S => {r ∈ PionCompleteness.TreeRectangleZero.diagonals N | PionCompleteness.PionNLSM.relab N s r ∈ S}
-/
#guard_msgs in
#print PionCompleteness.Paper.rotSet
/--
info: PionCompleteness.Paper.rotSet_sub (N s : ℕ) (S : Finset (ℕ × ℕ)) :
  PionCompleteness.Paper.rotSet N s S ⊆ PionCompleteness.TreeRectangleZero.diagonals N
-/
#guard_msgs in
#check PionCompleteness.Paper.rotSet_sub
/--
info: PionCompleteness.Paper.onLocus_rot {N s : ℕ} (hs : 1 ≤ s ∧ s ≤ N) {S : Finset (ℕ × ℕ)}
  (hS : S ⊆ PionCompleteness.TreeRectangleZero.diagonals N) (X : ℕ × ℕ → ℚ) :
  PionCompleteness.ChainSlice.OnLocus N S X ↔
    PionCompleteness.ChainSlice.OnLocus N (PionCompleteness.Paper.rotSet N s S) fun r =>
      X (PionCompleteness.PionNLSM.relab N s r)
-/
#guard_msgs in
#check PionCompleteness.Paper.onLocus_rot
/--
info: PionCompleteness.Paper.childSet_rot {N s k : ℕ} (hs : s ∈ Finset.Icc 1 N) (hk : 3 ≤ k) (hkN : k + 3 ≤ N)
  (S : Finset (ℕ × ℕ)) :
  {σ ∈ PionCompleteness.TreeRectangleZero.diagonals (k + 1) |
      PionCompleteness.Pi.ChildPairIn N S s k (k + 1) (fun j => PionCompleteness.TreeRectangleZero.vtx N (s + j - 1))
        σ.1 σ.2} =
    PionCompleteness.Paper.cutChildSet1 N k (PionCompleteness.Paper.rotSet N s S)
-/
#guard_msgs in
#check PionCompleteness.Paper.childSet_rot
/--
info: PionCompleteness.Paper.relab_parity {N s : ℕ} (hE : N % 2 = 0) (hN : 1 ≤ N) (hs : 1 ≤ s) {r : ℕ × ℕ} (h1 : 1 ≤ r.1)
  (h2 : 1 ≤ r.2) :
  (PionCompleteness.PionNLSM.relab N s r).1 % 2 = (PionCompleteness.PionNLSM.relab N s r).2 % 2 ↔ r.1 % 2 = r.2 % 2
-/
#guard_msgs in
#check PionCompleteness.Paper.relab_parity
/--
info: PionCompleteness.Paper.shiftSign_relab {N s : ℕ} (hE : N % 2 = 0) (hN : 1 ≤ N) (hs : 1 ≤ s) {r : ℕ × ℕ} (h1 : 1 ≤ r.1)
  (h2 : 1 ≤ r.2) :
  ↑(PionCompleteness.PionNLSM.shiftSign (PionCompleteness.PionNLSM.relab N s r)) =
    (if s % 2 = 1 then 1 else -1) * ↑(PionCompleteness.PionNLSM.shiftSign r)
-/
#guard_msgs in
#check PionCompleteness.Paper.shiftSign_relab
/--
info: @[reducible] def PionCompleteness.Paper.HasCutAbsorber : ℕ → Finset (ℕ × ℕ) → ℕ → ℕ → Prop :=
fun N S s k =>
  (∃ r ∈ PionCompleteness.TreeRectangleZero.diagonals N,
      PionCompleteness.PionNLSM.relab N s r ∉ S ∧ r.1 % 2 = r.2 % 2 ∧ PionCompleteness.Paper.CutUnseen1 k r) ∨
    ∃ j ∈ Finset.Icc 2 (k - 1),
      ∃ w ∈ Finset.Icc (k + 1) N,
        ∃ w' ∈ Finset.Icc (k + 1) N,
          w % 2 ≠ w' % 2 ∧
            PionCompleteness.PionNLSM.relab N s (j, w) ∉ S ∧ PionCompleteness.PionNLSM.relab N s (j, w') ∉ S
-/
#guard_msgs in
#print PionCompleteness.Paper.HasCutAbsorber
/--
info: PionCompleteness.Paper.hasCutAbsorber_rot {N s k : ℕ} (S : Finset (ℕ × ℕ)) :
  PionCompleteness.Paper.HasCutAbsorber N S s k ↔
    PionCompleteness.Paper.HasCutAbsorber1 N k (PionCompleteness.Paper.rotSet N s S)
-/
#guard_msgs in
#check PionCompleteness.Paper.hasCutAbsorber_rot
/--
info: def PionCompleteness.Paper.cutWeight : ℕ → Finset (ℕ × ℕ) → ℕ → ℕ → ℕ × ℕ → ℚ :=
fun N S s k σ =>
  if σ.2 = k + 1 then
    if ∃ w ∈ Finset.Icc (k + 1) N, w % 2 = σ.1 % 2 ∧ PionCompleteness.PionNLSM.relab N s (σ.1, w) ∉ S then
      ↑(PionCompleteness.PionNLSM.shiftSign (PionCompleteness.PionNLSM.relab N s (σ.1, σ.1)))
    else 0
  else ↑(PionCompleteness.PionNLSM.shiftSign (PionCompleteness.PionNLSM.relab N s σ))
-/
#guard_msgs in
#print PionCompleteness.Paper.cutWeight
/--
info: PionCompleteness.Paper.cutWeight_rot {N s k : ℕ} (hE : N % 2 = 0) (hs : 1 ≤ s ∧ s ≤ N) (S : Finset (ℕ × ℕ)) {σ : ℕ × ℕ}
  (hσ : σ ∈ PionCompleteness.TreeRectangleZero.diagonals (k + 1)) :
  PionCompleteness.Paper.cutWeight N S s k σ =
    (if s % 2 = 1 then 1 else -1) * PionCompleteness.Paper.cutWeight1 N k (PionCompleteness.Paper.rotSet N s S) σ
-/
#guard_msgs in
#check PionCompleteness.Paper.cutWeight_rot
/--
info: PionCompleteness.Paper.cutVal_rot {N s k : ℕ} (hs : 1 ≤ s ∧ s ≤ N) (X : ℕ × ℕ → ℚ) {σ : ℕ × ℕ}
  (hσ : σ ∈ PionCompleteness.TreeRectangleZero.diagonals (k + 1)) :
  PionCompleteness.Paper.cutVal N k
      (fun t => PionCompleteness.TreeRectangleZero.mesh N (fun r => X (PionCompleteness.PionNLSM.relab N s r)) t.1 t.2)
      σ =
    PionCompleteness.Paper.cutVal N k (fun t => PionCompleteness.TreeRectangleZero.mesh N X (t.1 + s - 1) (t.2 + s - 1))
      σ
-/
#guard_msgs in
#check PionCompleteness.Paper.cutVal_rot
/--
info: PionCompleteness.Paper.NLSM.Zeros.cut_relation {N s k : ℕ} (hs : s ∈ Finset.Icc 1 N) (hk3 : 3 ≤ k) (hkN : k + 3 ≤ N)
  (hko : k % 2 = 1) (X : ℕ × ℕ → ℚ) :
  PionCompleteness.TreeRectangleZero.planar N X s (s + k) =
    ∑ σ ∈ PionCompleteness.TreeRectangleZero.diagonals (k + 1) with σ.1 % 2 = 0 ∧ σ.2 % 2 = 0,
        PionCompleteness.Paper.cutVal N k
          (fun t => PionCompleteness.TreeRectangleZero.mesh N X (t.1 + s - 1) (t.2 + s - 1)) σ -
      ∑ σ ∈ PionCompleteness.TreeRectangleZero.diagonals (k + 1) with σ.1 % 2 = 1 ∧ σ.2 % 2 = 1,
        PionCompleteness.Paper.cutVal N k
          (fun t => PionCompleteness.TreeRectangleZero.mesh N X (t.1 + s - 1) (t.2 + s - 1)) σ
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.cut_relation
/--
info: PionCompleteness.Paper.rot_lift {N s k : ℕ} (hs : 1 ≤ s ∧ s ≤ N) (hkN : k + 3 ≤ N) {S : Finset (ℕ × ℕ)}
  (hS : S ⊆ PionCompleteness.TreeRectangleZero.diagonals N) {Y z : ℕ × ℕ → ℚ}
  (hY : PionCompleteness.ChainSlice.OnLocus N (PionCompleteness.Paper.rotSet N s S) Y)
  (hXP : PionCompleteness.TreeRectangleZero.planar N Y 1 (k + 1) = 0)
  (hYz : ∀ d ∈ PionCompleteness.TreeRectangleZero.diagonals (k + 1), Y d = z d) :
  ∃ X,
    PionCompleteness.ChainSlice.OnLocus N S X ∧
      PionCompleteness.TreeRectangleZero.planar N X s (s + k) = 0 ∧
        ∀ d ∈ PionCompleteness.TreeRectangleZero.diagonals (k + 1), X (PionCompleteness.PionNLSM.relab N s d) = z d
-/
#guard_msgs in
#check PionCompleteness.Paper.rot_lift
/--
info: PionCompleteness.Paper.NLSM.Zeros.cut_image_onto {N s k : ℕ} (hE : Even N) (hs : s ∈ Finset.Icc 1 N) (hk3 : 3 ≤ k)
  (hkN : k + 3 ≤ N) (hko : k % 2 = 1) {S : Finset (ℕ × ℕ)} (hS : S ⊆ PionCompleteness.TreeRectangleZero.diagonals N)
  (hab :
    PionCompleteness.Paper.HasCutAbsorber N S s k ∨
      ∀ t ∈ PionCompleteness.TreeRectangleZero.diagonals N, t ∉ S → t.1 % 2 ≠ t.2 % 2)
  (y : ℕ × ℕ → ℚ)
  (hy :
    PionCompleteness.ChainSlice.OnLocus (k + 1)
      ({σ ∈ PionCompleteness.TreeRectangleZero.diagonals (k + 1) |
        PionCompleteness.Pi.ChildPairIn N S s k (k + 1) (fun j => PionCompleteness.TreeRectangleZero.vtx N (s + j - 1))
          σ.1 σ.2})
      y) :
  ∃ X,
    PionCompleteness.ChainSlice.OnLocus N S X ∧
      PionCompleteness.TreeRectangleZero.planar N X s (s + k) = 0 ∧
        ∀ d ∈ PionCompleteness.TreeRectangleZero.diagonals (k + 1), X (PionCompleteness.PionNLSM.relab N s d) = y d
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.cut_image_onto
/--
info: PionCompleteness.Paper.rot_point {N s k : ℕ} (hs : 1 ≤ s ∧ s ≤ N) {S : Finset (ℕ × ℕ)}
  (hS : S ⊆ PionCompleteness.TreeRectangleZero.diagonals N) {X : ℕ × ℕ → ℚ}
  (hX : PionCompleteness.ChainSlice.OnLocus N S X) :
  (PionCompleteness.ChainSlice.OnLocus N (PionCompleteness.Paper.rotSet N s S) fun r =>
      X (PionCompleteness.PionNLSM.relab N s r)) ∧
    PionCompleteness.TreeRectangleZero.planar N (fun r => X (PionCompleteness.PionNLSM.relab N s r)) 1 (k + 1) =
      PionCompleteness.TreeRectangleZero.planar N X s (s + k)
-/
#guard_msgs in
#check PionCompleteness.Paper.rot_point
/--
info: PionCompleteness.Paper.NLSM.Zeros.cut_image_hyperplane {N s k : ℕ} (hE : Even N) (hs : s ∈ Finset.Icc 1 N) (hk3 : 3 ≤ k)
  (hkN : k + 3 ≤ N) (hko : k % 2 = 1) {S : Finset (ℕ × ℕ)} (hS : S ⊆ PionCompleteness.TreeRectangleZero.diagonals N)
  (hno : ¬PionCompleteness.Paper.HasCutAbsorber N S s k)
  (hsame : ∃ t ∈ PionCompleteness.TreeRectangleZero.diagonals N, t ∉ S ∧ t.1 % 2 = t.2 % 2)
  (hX0 :
    ∃ X0, PionCompleteness.ChainSlice.OnLocus N S X0 ∧ PionCompleteness.TreeRectangleZero.planar N X0 s (s + k) ≠ 0) :
  (∀ (y : ℕ × ℕ → ℚ),
      PionCompleteness.ChainSlice.OnLocus (k + 1)
          ({σ ∈ PionCompleteness.TreeRectangleZero.diagonals (k + 1) |
            PionCompleteness.Pi.ChildPairIn N S s k (k + 1)
              (fun j => PionCompleteness.TreeRectangleZero.vtx N (s + j - 1)) σ.1 σ.2})
          y →
        ((∃ X,
            PionCompleteness.ChainSlice.OnLocus N S X ∧
              PionCompleteness.TreeRectangleZero.planar N X s (s + k) = 0 ∧
                ∀ d ∈ PionCompleteness.TreeRectangleZero.diagonals (k + 1),
                  X (PionCompleteness.PionNLSM.relab N s d) = y d) ↔
          ∑ σ ∈ PionCompleteness.TreeRectangleZero.diagonals (k + 1),
              PionCompleteness.Paper.cutWeight N S s k σ * PionCompleteness.TreeRectangleZero.mesh (k + 1) y σ.1 σ.2 =
            0)) ∧
    ∃ y,
      PionCompleteness.ChainSlice.OnLocus (k + 1)
          ({σ ∈ PionCompleteness.TreeRectangleZero.diagonals (k + 1) |
            PionCompleteness.Pi.ChildPairIn N S s k (k + 1)
              (fun j => PionCompleteness.TreeRectangleZero.vtx N (s + j - 1)) σ.1 σ.2})
          y ∧
        ∑ σ ∈ PionCompleteness.TreeRectangleZero.diagonals (k + 1),
            PionCompleteness.Paper.cutWeight N S s k σ * PionCompleteness.TreeRectangleZero.mesh (k + 1) y σ.1 σ.2 ≠
          0
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.cut_image_hyperplane
/--
info: PionCompleteness.Paper.NLSM.Zeros.cut_absorber_of_inner_pair {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {S : Finset (ℕ × ℕ)}
  {P : ℕ × ℕ} (hPO : P ∈ PionCompleteness.PionZeros.oddDiagonals N) :
  (∀ g ∈ PionCompleteness.Pi.innerEE N S P,
      ∃ r ∈ PionCompleteness.TreeRectangleZero.diagonals N,
        PionCompleteness.PionNLSM.relab N (PionCompleteness.Pi.headStart P) r = g ∧
          g ∉ S ∧ r.1 % 2 = r.2 % 2 ∧ PionCompleteness.Paper.CutUnseen1 (PionCompleteness.Pi.headLen N P) r) ∧
    ∀ g ∈ PionCompleteness.Pi.innerOO N S P,
      ∃ r ∈ PionCompleteness.TreeRectangleZero.diagonals N,
        PionCompleteness.PionNLSM.relab N (PionCompleteness.Pi.tailStart P) r = g ∧
          g ∉ S ∧ r.1 % 2 = r.2 % 2 ∧ PionCompleteness.Paper.CutUnseen1 (PionCompleteness.Pi.tailLen N P) r
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.cut_absorber_of_inner_pair
/--
info: PionCompleteness.Paper.NLSM.Zeros.cut_absorber_of_residue_chord {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {S : Finset (ℕ × ℕ)}
  {P : ℕ × ℕ} (hP : P ∈ PionCompleteness.Pi.poleChords N S) :
  PionCompleteness.Paper.HasCutAbsorber N S (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P) ∧
    PionCompleteness.Paper.HasCutAbsorber N S (PionCompleteness.Pi.tailStart P) (PionCompleteness.Pi.tailLen N P)
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.cut_absorber_of_residue_chord
-- The library definitions the statements of the polygon with a marked leg, the children of an odd
-- chord and the collapse identity read.
/--
info: def PionCompleteness.Pi.pkRLam : ℕ → ℕ → Finset (ℕ × ℕ) → (ℕ × ℕ → ℚ) → Prop :=
fun n d₁ I X =>
  (∀ a ∈ Finset.Icc 1 n,
      ∀ b ∈ Finset.Icc 1 n,
        a + 2 ≤ b →
          a % 2 = b % 2 →
            (a, b) ≠ (1, n - 1) →
              (a, b) ≠ PionCompleteness.Pi.pkRCstp n d₁ → PionCompleteness.TreeRectangleZero.mesh n X a b = 0) ∧
    PionCompleteness.TreeRectangleZero.mesh n X 1 (n - 1) =
        PionCompleteness.TreeRectangleZero.mesh n X (PionCompleteness.Pi.pkRCstp n d₁).1
          (PionCompleteness.Pi.pkRCstp n d₁).2 ∧
      ∀ Q ∈ I, ∀ t ∈ PionCompleteness.Pi.pkRMinrect n d₁ Q, PionCompleteness.TreeRectangleZero.mesh n X t.1 t.2 = 0
-/
#guard_msgs in
#print PionCompleteness.Pi.pkRLam
/--
info: def PionCompleteness.Pi.pkRMinrect : ℕ → ℕ → ℕ × ℕ → Finset (ℕ × ℕ) :=
fun n d₁ Q =>
  {w ∈ Finset.Icc 1 n | w % 2 = 1 ∧ w ≠ 2 * d₁ + 1 ∧ w ∉ PionCompleteness.Pi.pkRHead d₁ Q} ×ˢ
    {c ∈ Finset.Icc 1 n | c % 2 = 0 ∧ c ≠ n ∧ c ∈ PionCompleteness.Pi.pkRHead d₁ Q}
-/
#guard_msgs in
#print PionCompleteness.Pi.pkRMinrect
/--
info: def PionCompleteness.Pi.pkRHead : ℕ → ℕ × ℕ → Finset ℕ :=
fun d₁ Q => Finset.Icc (2 * Q.1 + 1) (2 * d₁ + 2 * Q.2 + 1)
-/
#guard_msgs in
#print PionCompleteness.Pi.pkRHead
/--
info: def PionCompleteness.Pi.pkRIsMem : ℕ → ℕ → ℕ × ℕ → Prop :=
fun n d₁ Q => Q.1 ≤ d₁ ∧ 2 * d₁ + 2 * Q.2 + 2 ≤ n ∧ ¬(Q.1 = d₁ ∧ Q.2 = 0) ∧ ¬(Q.1 = 0 ∧ 2 * d₁ + 2 * Q.2 + 2 = n)
-/
#guard_msgs in
#print PionCompleteness.Pi.pkRIsMem
/--
info: def PionCompleteness.Pi.pkRClosed : ℕ → ℕ → Finset (ℕ × ℕ) → Prop :=
fun n d₁ I =>
  ∀ Q1 ∈ insert (d₁, 0) (insert (0, n / 2 - 1 - d₁) I),
    ∀ Q2 ∈ insert (d₁, 0) (insert (0, n / 2 - 1 - d₁) I),
      (max Q1.1 Q2.1, min Q1.2 Q2.2) ∈ insert (d₁, 0) (insert (0, n / 2 - 1 - d₁) I) ∧
        (min Q1.1 Q2.1, max Q1.2 Q2.2) ∈ insert (d₁, 0) (insert (0, n / 2 - 1 - d₁) I)
-/
#guard_msgs in
#print PionCompleteness.Pi.pkRClosed
/--
info: def PionCompleteness.Pi.pkRMchord : ℕ → ℕ × ℕ → ℕ × ℕ :=
fun d₁ Q => (2 * Q.1 + 1, 2 * d₁ + 2 * Q.2 + 2)
-/
#guard_msgs in
#print PionCompleteness.Pi.pkRMchord
/--
info: def PionCompleteness.Pi.pkRW : ℕ → ℕ → ℕ × ℕ → (ℕ × ℕ → ℚ) → Prop :=
fun n d₁ Q X =>
  (∀ a ∈ Finset.Icc 1 n,
      ∀ b ∈ Finset.Icc 1 n,
        a + 2 ≤ b →
          a % 2 = b % 2 →
            (a, b) ≠ (1, n - 1) →
              (a, b) ≠ PionCompleteness.Pi.pkRCstp n d₁ →
                (a, b) ≠ PionCompleteness.Pi.pkRTau d₁ Q → PionCompleteness.TreeRectangleZero.mesh n X a b = 0) ∧
    ∀ t ∈ PionCompleteness.Pi.pkRMinrect n d₁ Q, PionCompleteness.TreeRectangleZero.mesh n X t.1 t.2 = 0
-/
#guard_msgs in
#print PionCompleteness.Pi.pkRW
/--
info: def PionCompleteness.Pi.pkRCstp : ℕ → ℕ → ℕ × ℕ :=
fun n d₁ => if d₁ = 0 then (2, n) else (2 * d₁, 2 * d₁ + 2)
-/
#guard_msgs in
#print PionCompleteness.Pi.pkRCstp
/--
info: def PionCompleteness.Pi.pkRTau : ℕ → ℕ × ℕ → ℕ × ℕ :=
fun d₁ Q => (2 * Q.1 + 1, 2 * d₁ + 2 * Q.2 + 1)
-/
#guard_msgs in
#print PionCompleteness.Pi.pkRTau
/--
info: def PionCompleteness.Pi.pkRGramPt.{u_1} : {K : Type u_1} → [Field K] → (ℕ → ℕ → K) → ℕ × ℕ → K :=
fun {K} [Field K] C p => PionCompleteness.Pi.pkRArcX C p.1 p.2
-/
#guard_msgs in
#print PionCompleteness.Pi.pkRGramPt
/--
info: def PionCompleteness.Pi.pkRArcX.{u_1} : {K : Type u_1} → [Field K] → (ℕ → ℕ → K) → ℕ → ℕ → K :=
fun {K} [Field K] C i j => -∑ d ∈ Finset.Ico i j, ∑ c ∈ Finset.Ico i d, C c d
-/
#guard_msgs in
#print PionCompleteness.Pi.pkRArcX
/--
info: def PionCompleteness.TreeRectangleZero.rot : ℕ → ℕ × ℕ → ℕ × ℕ :=
fun n d =>
  (min (PionCompleteness.TreeRectangleZero.vtx n (d.1 + 1)) (PionCompleteness.TreeRectangleZero.vtx n (d.2 + 1)),
    max (PionCompleteness.TreeRectangleZero.vtx n (d.1 + 1)) (PionCompleteness.TreeRectangleZero.vtx n (d.2 + 1)))
-/
#guard_msgs in
#print PionCompleteness.TreeRectangleZero.rot
/--
info: def PionCompleteness.Pi.pkRD2Below : ℕ → Finset (ℕ × ℕ) → ℕ × ℕ → Finset (ℕ × ℕ) :=
fun N R Q => {Q' ∈ R | Q' ≠ Q ∧ PionCompleteness.Pi.oddSide N Q' ⊆ PionCompleteness.Pi.oddSide N Q}
-/
#guard_msgs in
#print PionCompleteness.Pi.pkRD2Below
/--
info: def PionCompleteness.Pi.ChildPairIn : ℕ → Finset (ℕ × ℕ) → ℕ → ℕ → ℕ → (ℕ → ℕ) → ℕ → ℕ → Prop :=
fun N S s k hat f j l =>
  if j = hat then ∀ w ∈ Finset.Icc 1 N, w ∉ PionCompleteness.Pi.cycArc N s k → (min (f l) w, max (f l) w) ∈ S
  else
    if l = hat then ∀ w ∈ Finset.Icc 1 N, w ∉ PionCompleteness.Pi.cycArc N s k → (min (f j) w, max (f j) w) ∈ S
    else (min (f j) (f l), max (f j) (f l)) ∈ S
-/
#guard_msgs in
#print PionCompleteness.Pi.ChildPairIn
/--
info: def PionCompleteness.Pi.childSetA : ℕ → Finset (ℕ × ℕ) → ℕ × ℕ → Finset (ℕ × ℕ) :=
fun N S P =>
  {σ ∈ PionCompleteness.TreeRectangleZero.diagonals (PionCompleteness.Pi.headLen N P + 1) |
    PionCompleteness.Pi.ChildPairIn N S (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen N P)
      (PionCompleteness.Pi.headLen N P + 1)
      (fun j => PionCompleteness.TreeRectangleZero.vtx N (PionCompleteness.Pi.headStart P + j - 1)) σ.1 σ.2}
-/
#guard_msgs in
#print PionCompleteness.Pi.childSetA
/--
info: def PionCompleteness.Pi.childSetB : ℕ → Finset (ℕ × ℕ) → ℕ × ℕ → Finset (ℕ × ℕ) :=
fun N S P =>
  {σ ∈ PionCompleteness.TreeRectangleZero.diagonals (PionCompleteness.Pi.tailLen N P + 1) |
    PionCompleteness.Pi.ChildPairIn N S (PionCompleteness.Pi.tailStart P) (PionCompleteness.Pi.tailLen N P) 1
      (fun j => PionCompleteness.TreeRectangleZero.vtx N (PionCompleteness.Pi.tailStart P + j - 2)) σ.1 σ.2}
-/
#guard_msgs in
#print PionCompleteness.Pi.childSetB
/--
info: def PionCompleteness.Pi.NonzeroOn : ℕ → Finset (ℕ × ℕ) → Prop :=
fun N S =>
  ∃ X,
    PionCompleteness.ChainSlice.OnLocus N S X ∧
      (∀ d ∈ PionCompleteness.PionZeros.oddDiagonals N, X d ≠ 0) ∧ PionCompleteness.PionNLSM.NLSM N X ≠ 0
-/
#guard_msgs in
#print PionCompleteness.Pi.NonzeroOn
/--
info: def PionCompleteness.Pi.pkRBChildB' : ℕ → Finset (ℕ × ℕ) → ℕ × ℕ → Finset (ℕ × ℕ) :=
fun N S P =>
  {σ ∈ PionCompleteness.TreeRectangleZero.diagonals (PionCompleteness.Pi.tailLen N P + 1) |
    PionCompleteness.Pi.ChildPairIn N S (PionCompleteness.Pi.tailStart P) (PionCompleteness.Pi.tailLen N P)
      (PionCompleteness.Pi.tailLen N P + 1)
      (fun j => PionCompleteness.TreeRectangleZero.vtx N (PionCompleteness.Pi.tailStart P + j - 1)) σ.1 σ.2}
-/
#guard_msgs in
#print PionCompleteness.Pi.pkRBChildB'
-- `Paper`, continued: short arguments of the remarks on the definitions and the main theorem
-- (zeros upward, the gaps of a set of legs with `nextCut`, the diamond containment, `S_G` as
-- blocks of tiles, with the library definitions they are read through, `tlab` and
-- `ChainSlice.diamond`).
/--
info: PionCompleteness.Paper.NLSM.Zeros.isRegularSet_mono {N : ℕ} {Z S : Finset (ℕ × ℕ)} (h : Z ⊆ S)
  (hreg : PionCompleteness.Paper.NLSM.Zeros.IsRegularSet N S) : PionCompleteness.Paper.NLSM.Zeros.IsRegularSet N Z
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.isRegularSet_mono
/--
info: PionCompleteness.Paper.NLSM.Zeros.isCoordinateZero_of_subset {N : ℕ} (hN : 4 ≤ N) (hE : Even N) {Z S : Finset (ℕ × ℕ)}
  (hS : S ⊆ PionCompleteness.TreeRectangleZero.diagonals N) (hreg : PionCompleteness.Paper.NLSM.Zeros.IsRegularSet N S)
  (hZS : Z ⊆ S) (hZ : PionCompleteness.Paper.NLSM.Zeros.IsCoordinateZero N Z) :
  PionCompleteness.Paper.NLSM.Zeros.IsCoordinateZero N S
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.isCoordinateZero_of_subset
/--
info: PionCompleteness.Paper.NLSM.Zeros.exists_minimal_coordinate_zero_subset {N : ℕ} {S : Finset (ℕ × ℕ)}
  (hS : PionCompleteness.Paper.NLSM.Zeros.IsRegularCoordinateZero N S) :
  ∃ Z ⊆ S, PionCompleteness.Paper.NLSM.Zeros.IsMinimalCoordinateZero N Z
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.exists_minimal_coordinate_zero_subset
/--
info: PionCompleteness.Paper.NLSM.Zeros.isCoordinateZero_iff_contains_minimal {N : ℕ} (hN : 4 ≤ N) (hE : Even N)
  {S : Finset (ℕ × ℕ)} (hS : S ⊆ PionCompleteness.TreeRectangleZero.diagonals N)
  (hreg : PionCompleteness.Paper.NLSM.Zeros.IsRegularSet N S) :
  PionCompleteness.Paper.NLSM.Zeros.IsCoordinateZero N S ↔
    ∃ Z ⊆ S, PionCompleteness.Paper.NLSM.Zeros.IsMinimalCoordinateZero N Z
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.isCoordinateZero_iff_contains_minimal
/--
info: def PionCompleteness.Paper.Combinatorics.Polygons.nextCut : ℕ → Finset ℕ → ℕ → ℕ :=
fun N G g =>
  if h : {x ∈ G | g < x}.Nonempty then {x ∈ G | g < x}.min' h else if h' : G.Nonempty then G.min' h' + N else g + N
-/
#guard_msgs in
#print PionCompleteness.Paper.Combinatorics.Polygons.nextCut
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.nextCut_of_above {N : ℕ} {G : Finset ℕ} {g : ℕ} (h : ∃ y ∈ G, g < y) :
  PionCompleteness.Paper.Combinatorics.Polygons.nextCut N G g ∈ G ∧
    g < PionCompleteness.Paper.Combinatorics.Polygons.nextCut N G g ∧
      ∀ y ∈ G, g < y → PionCompleteness.Paper.Combinatorics.Polygons.nextCut N G g ≤ y
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.nextCut_of_above
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.nextCut_of_top {N : ℕ} {G : Finset ℕ} {g : ℕ} (hg : g ∈ G)
  (h : ∀ y ∈ G, y ≤ g) : PionCompleteness.Paper.Combinatorics.Polygons.nextCut N G g = G.min' ⋯ + N
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.nextCut_of_top
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.nextCut_pair {N a b : ℕ} (hab : a < b) :
  PionCompleteness.Paper.Combinatorics.Polygons.nextCut N {a, b} a = b ∧
    PionCompleteness.Paper.Combinatorics.Polygons.nextCut N {a, b} b = a + N
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.nextCut_pair
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.one_parity_iff_gaps_odd {N : ℕ} (hE : Even N) {G : Finset ℕ}
  (hG : G ⊆ Finset.Icc 1 N) :
  (∀ g ∈ G, ∀ g' ∈ G, g % 2 = g' % 2) ↔
    ∀ g ∈ G, Odd (PionCompleteness.Paper.Combinatorics.Polygons.nextCut N G g - g - 1)
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.one_parity_iff_gaps_odd
/--
info: PionCompleteness.Paper.Combinatorics.Polygons.opposite_parity_gaps_even {N : ℕ} (hE : Even N) {a b : ℕ} (ha : 1 ≤ a)
  (hb : b ≤ N) (hab : a + 2 ≤ b) (hout : ¬(a = 1 ∧ b = N)) (hp : a % 2 ≠ b % 2) :
  Even (PionCompleteness.Paper.Combinatorics.Polygons.nextCut N {a, b} a - a - 1) ∧
    Even (PionCompleteness.Paper.Combinatorics.Polygons.nextCut N {a, b} b - b - 1) ∧
      (a, b) ∈ PionCompleteness.PionZeros.oddDiagonals N ∧
        PionCompleteness.ChainSlice.tlab N (a + 1) (b + 1) ∈ PionCompleteness.PionZeros.oddDiagonals N
-/
#guard_msgs in
#check PionCompleteness.Paper.Combinatorics.Polygons.opposite_parity_gaps_even
/--
info: PionCompleteness.Paper.NLSM.Zeros.Families.subset_pair_of_causal_diamond_subset {N : ℕ} {G : Finset ℕ}
  (hG : G ⊆ Finset.Icc 1 N) {a b : ℕ} (ha : a ∈ Finset.Icc 1 N) (hb : b ∈ Finset.Icc 1 N) (hab : a < b)
  (hin : ∃ u, a < u ∧ u < b) (hout : ∃ u ∈ Finset.Icc 1 N, u < a ∨ b < u)
  (h : PionCompleteness.Pi.sepPairs N {a, b} ⊆ PionCompleteness.Pi.sepPairs N G) : G ⊆ {a, b}
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.Families.subset_pair_of_causal_diamond_subset
/--
info: PionCompleteness.Paper.NLSM.Zeros.Families.no_causal_diamond_in_separated_pairs {N : ℕ} {T : Finset ℕ}
  (hT : T ⊆ Finset.Icc 1 N) (h3 : 3 ≤ T.card) :
  ¬∃ Z, PionCompleteness.Paper.NLSM.Zeros.Families.IsCausalDiamond N Z ∧ Z ⊆ PionCompleteness.Pi.sepPairs N T
-/
#guard_msgs in
#check PionCompleteness.Paper.NLSM.Zeros.Families.no_causal_diamond_in_separated_pairs
/--
info: PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.separated_pairs_block_tile {N : ℕ} {G : Finset ℕ}
  (hG : G ⊆ Finset.Icc 1 N) {g h i j : ℕ} (hg : g ∈ G) (hh : h ∈ G) (hgh : g < h)
  (hi : g < i ∧ i < PionCompleteness.Paper.Combinatorics.Polygons.nextCut N G g)
  (hj : h < j ∧ j < PionCompleteness.Paper.Combinatorics.Polygons.nextCut N G h) :
  PionCompleteness.ChainSlice.tlab N i j ∈ PionCompleteness.Pi.sepPairs N G ∧ i < j ∧ j < i + N
-/
#guard_msgs in
#check PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.separated_pairs_block_tile
/--
info: PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.separated_pairs_eq_blocks {N : ℕ} {G : Finset ℕ}
  (hG : G ⊆ Finset.Icc 1 N) :
  (PionCompleteness.Pi.sepPairs N G =
      {q ∈ G ×ˢ G | q.1 < q.2}.biUnion fun q =>
        Finset.image (fun p => PionCompleteness.ChainSlice.tlab N p.1 p.2)
          (Finset.Ioo q.1 (PionCompleteness.Paper.Combinatorics.Polygons.nextCut N G q.1) ×ˢ
            Finset.Ioo q.2 (PionCompleteness.Paper.Combinatorics.Polygons.nextCut N G q.2))) ∧
    ∀ g ∈ G,
      ∀ h ∈ G,
        g < h →
          ∀ i ∈ Finset.Ioo g (PionCompleteness.Paper.Combinatorics.Polygons.nextCut N G g),
            ∀ j ∈ Finset.Ioo h (PionCompleteness.Paper.Combinatorics.Polygons.nextCut N G h), i < j ∧ j < i + N
-/
#guard_msgs in
#check PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.separated_pairs_eq_blocks
/--
info: PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.separated_pairs_of_two_legs_eq_diamond {N a b : ℕ} (ha : 1 ≤ a)
  (hab : a < b) (hb : b ≤ N) :
  PionCompleteness.Pi.sepPairs N {a, b} = PionCompleteness.ChainSlice.diamond N (a + 1) (b + 1)
-/
#guard_msgs in
#check PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.separated_pairs_of_two_legs_eq_diamond
/--
info: def PionCompleteness.ChainSlice.tlab : ℕ → ℕ → ℕ → ℕ × ℕ :=
fun m i j =>
  (min (PionCompleteness.TreeRectangleZero.vtx m i) (PionCompleteness.TreeRectangleZero.vtx m j),
    max (PionCompleteness.TreeRectangleZero.vtx m i) (PionCompleteness.TreeRectangleZero.vtx m j))
-/
#guard_msgs in
#print PionCompleteness.ChainSlice.tlab
/--
info: def PionCompleteness.ChainSlice.diamond : ℕ → ℕ → ℕ → Finset (ℕ × ℕ) :=
fun m a b =>
  Finset.image (fun p => PionCompleteness.ChainSlice.tlab m p.1 p.2) (Finset.Icc a (b - 2) ×ˢ Finset.Icc b (a + m - 2))
-/
#guard_msgs in
#print PionCompleteness.ChainSlice.diamond
/--
info: PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.whole_parity_members {N : ℕ} (hN : 4 ≤ N) (hE : Even N) :
  PionCompleteness.Pi.sepPairs N ({a ∈ Finset.Icc 1 N | a % 2 = 1}) =
      {p ∈ PionCompleteness.TreeRectangleZero.diagonals N | p.1 % 2 = 0 ∧ p.2 % 2 = 0} ∧
    PionCompleteness.Pi.sepPairs N ({a ∈ Finset.Icc 1 N | a % 2 = 0}) =
      {p ∈ PionCompleteness.TreeRectangleZero.diagonals N | p.1 % 2 = 1 ∧ p.2 % 2 = 1}
-/
#guard_msgs in
#check PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.whole_parity_members
/--
info: PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.parity_form_vanishes_on_member_iff {N : ℕ} (hN : 4 ≤ N) (hE : Even N)
  {Z : Finset (ℕ × ℕ)} (hZ : PionCompleteness.Paper.NLSM.Zeros.Families.IsListMember N Z) :
  (∀ (X : ℕ × ℕ → ℚ), PionCompleteness.ChainSlice.OnLocus N Z X → PionCompleteness.Pi.pkGE N X = 0) ↔
    Z = PionCompleteness.Pi.sepPairs N ({a ∈ Finset.Icc 1 N | a % 2 = 1}) ∨
      Z = PionCompleteness.Pi.sepPairs N ({a ∈ Finset.Icc 1 N | a % 2 = 0})
-/
#guard_msgs in
#check PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.parity_form_vanishes_on_member_iff
/--
info: PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.parity_form_vanishes_iff_contains_whole_parity {N : ℕ} (hN : 4 ≤ N)
  (hE : Even N) {S : Finset (ℕ × ℕ)} (hS : S ⊆ PionCompleteness.TreeRectangleZero.diagonals N) :
  (∀ (X : ℕ × ℕ → ℚ), PionCompleteness.ChainSlice.OnLocus N S X → PionCompleteness.Pi.pkGE N X = 0) ↔
    PionCompleteness.Pi.sepPairs N ({a ∈ Finset.Icc 1 N | a % 2 = 1}) ⊆ S ∨
      PionCompleteness.Pi.sepPairs N ({a ∈ Finset.Icc 1 N | a % 2 = 0}) ⊆ S
-/
#guard_msgs in
#check
  PionCompleteness.Paper.Amplitudes.Kinematics.Mesh.parity_form_vanishes_iff_contains_whole_parity

-- `PaperTests`: every test of `Paper`: the main theorem is not vacuous (for every even `N ≥ 6`; why
-- `Even N` is needed), the definitions on given sets (where they hold and where they fail), the
-- paper's examples with a Lean form, and hypotheses of theorems that hold together.
/--
info: PionCompleteness.PaperTests.sepPairs_nonempty_of_admissible {N r : ℕ} (hE : N % 2 = 0) {G : Finset ℕ}
  (h : PionCompleteness.PionZeros.Admissible N r G) : (PionCompleteness.Pi.sepPairs N G).Nonempty
-/
#guard_msgs in
#check PionCompleteness.PaperTests.sepPairs_nonempty_of_admissible
/--
info: PionCompleteness.PaperTests.sepPairs_nonempty_of_mixedAnchor {N : ℕ} {G : Finset ℕ}
  (h : PionCompleteness.Pi.IsMixedAnchor N G) : (PionCompleteness.Pi.sepPairs N G).Nonempty
-/
#guard_msgs in
#check PionCompleteness.PaperTests.sepPairs_nonempty_of_mixedAnchor
/--
info: PionCompleteness.PaperTests.sepPairs_nonempty {N : ℕ} (hE : Even N) {G : Finset ℕ}
  (hG : PionCompleteness.Pi.IsGSet N G) : (PionCompleteness.Pi.sepPairs N G).Nonempty
-/
#guard_msgs in
#check PionCompleteness.PaperTests.sepPairs_nonempty
/--
info: PionCompleteness.PaperTests.empty_notMem_gFamily {N : ℕ} (hE : Even N) : ∅ ∉ PionCompleteness.Pi.gFamily N
-/
#guard_msgs in
#check PionCompleteness.PaperTests.empty_notMem_gFamily
/--
info: PionCompleteness.PaperTests.empty_mem_gFamily_seven : ∅ ∈ PionCompleteness.Pi.gFamily 7
-/
#guard_msgs in
#check PionCompleteness.PaperTests.empty_mem_gFamily_seven
/--
info: PionCompleteness.PaperTests.empty_mem_gFamily_of_odd {N : ℕ} (hN : 3 ≤ N) (hO : Odd N) :
  ∅ ∈ PionCompleteness.Pi.gFamily N
-/
#guard_msgs in
#check PionCompleteness.PaperTests.empty_mem_gFamily_of_odd
/--
info: PionCompleteness.PaperTests.containsGMember_of_odd {N : ℕ} (hN : 3 ≤ N) (hO : Odd N) (S : Finset (ℕ × ℕ)) :
  PionCompleteness.Pi.ContainsGMember N S
-/
#guard_msgs in
#check PionCompleteness.PaperTests.containsGMember_of_odd
/--
info: PionCompleteness.PaperTests.nonDegPt_empty (N : ℕ) : PionCompleteness.Pi.NonDegPt N ∅
-/
#guard_msgs in
#check PionCompleteness.PaperTests.nonDegPt_empty
/--
info: PionCompleteness.PaperTests.not_ampZeroOn_empty {N : ℕ} (hN : 6 ≤ N) (hE : Even N) : ¬PionCompleteness.Pi.AmpZeroOn N ∅
-/
#guard_msgs in
#check PionCompleteness.PaperTests.not_ampZeroOn_empty
/--
info: PionCompleteness.PaperTests.exists_NLSM_ne_zero {N : ℕ} (hN : 6 ≤ N) (hE : Even N) :
  ∃ X, (∀ d ∈ PionCompleteness.PionZeros.oddDiagonals N, X d ≠ 0) ∧ PionCompleteness.PionNLSM.NLSM N X ≠ 0
-/
#guard_msgs in
#check PionCompleteness.PaperTests.exists_NLSM_ne_zero
/--
info: PionCompleteness.PaperTests.sepPairs_one_three_mem_gFamily {N : ℕ} (hN : 3 ≤ N) :
  PionCompleteness.Pi.sepPairs N {1, 3} ∈ PionCompleteness.Pi.gFamily N
-/
#guard_msgs in
#check PionCompleteness.PaperTests.sepPairs_one_three_mem_gFamily
/--
info: PionCompleteness.PaperTests.isNDZero_sepPairs_one_three {N : ℕ} (hN : 6 ≤ N) (hE : Even N) :
  PionCompleteness.Pi.IsNDZero N (PionCompleteness.Pi.sepPairs N {1, 3})
-/
#guard_msgs in
#check PionCompleteness.PaperTests.isNDZero_sepPairs_one_three
/--
info: PionCompleteness.PaperTests.not_isListMember_empty {N : ℕ} (hE : Even N) :
  ¬PionCompleteness.Paper.NLSM.Zeros.Families.IsListMember N ∅
-/
#guard_msgs in
#check PionCompleteness.PaperTests.not_isListMember_empty
/--
info: PionCompleteness.PaperTests.not_isCoordinateZero_empty {N : ℕ} (hN : 6 ≤ N) (hE : Even N) :
  ¬PionCompleteness.Paper.NLSM.Zeros.IsCoordinateZero N ∅
-/
#guard_msgs in
#check PionCompleteness.PaperTests.not_isCoordinateZero_empty
/--
info: PionCompleteness.PaperTests.isListMember_sepPairs_one_three {N : ℕ} (hN : 6 ≤ N) (hE : Even N) :
  PionCompleteness.Paper.NLSM.Zeros.Families.IsListMember N (PionCompleteness.Pi.sepPairs N {1, 3})
-/
#guard_msgs in
#check PionCompleteness.PaperTests.isListMember_sepPairs_one_three
/--
info: PionCompleteness.PaperTests.isRegularCoordinateZero_sepPairs_one_three {N : ℕ} (hN : 6 ≤ N) (hE : Even N) :
  PionCompleteness.Paper.NLSM.Zeros.IsRegularCoordinateZero N (PionCompleteness.Pi.sepPairs N {1, 3})
-/
#guard_msgs in
#check PionCompleteness.PaperTests.isRegularCoordinateZero_sepPairs_one_three
/--
info: PionCompleteness.PaperTests.isMinimalCoordinateZero_six_one_three_five :
  PionCompleteness.Paper.NLSM.Zeros.IsMinimalCoordinateZero 6 (PionCompleteness.Pi.sepPairs 6 {1, 3, 5})
-/
#guard_msgs in
#check PionCompleteness.PaperTests.isMinimalCoordinateZero_six_one_three_five
/--
info: PionCompleteness.PaperTests.isRegularCoordinateZero_six_one_three_five :
  PionCompleteness.Paper.NLSM.Zeros.IsRegularCoordinateZero 6 (PionCompleteness.Pi.sepPairs 6 {1, 3, 5})
-/
#guard_msgs in
#check PionCompleteness.PaperTests.isRegularCoordinateZero_six_one_three_five
/--
info: PionCompleteness.PaperTests.isRegularSet_six_one_three_five :
  PionCompleteness.Paper.NLSM.Zeros.IsRegularSet 6 (PionCompleteness.Pi.sepPairs 6 {1, 3, 5})
-/
#guard_msgs in
#check PionCompleteness.PaperTests.isRegularSet_six_one_three_five
/--
info: PionCompleteness.PaperTests.isCoordinateZero_six_one_three_five :
  PionCompleteness.Paper.NLSM.Zeros.IsCoordinateZero 6 (PionCompleteness.Pi.sepPairs 6 {1, 3, 5})
-/
#guard_msgs in
#check PionCompleteness.PaperTests.isCoordinateZero_six_one_three_five
/--
info: PionCompleteness.PaperTests.not_isRegularSet_six_all_pairs :
  ¬PionCompleteness.Paper.NLSM.Zeros.IsRegularSet 6 (PionCompleteness.TreeRectangleZero.diagonals 6)
-/
#guard_msgs in
#check PionCompleteness.PaperTests.not_isRegularSet_six_all_pairs
/--
info: PionCompleteness.PaperTests.not_isRegularCoordinateZero_six_all_pairs :
  ¬PionCompleteness.Paper.NLSM.Zeros.IsRegularCoordinateZero 6 (PionCompleteness.TreeRectangleZero.diagonals 6)
-/
#guard_msgs in
#check PionCompleteness.PaperTests.not_isRegularCoordinateZero_six_all_pairs
/--
info: PionCompleteness.PaperTests.not_isCoordinateZero_six_empty : ¬PionCompleteness.Paper.NLSM.Zeros.IsCoordinateZero 6 ∅
-/
#guard_msgs in
#check PionCompleteness.PaperTests.not_isCoordinateZero_six_empty
/--
info: PionCompleteness.PaperTests.not_isMinimalCoordinateZero_six_one_three_five_insert :
  PionCompleteness.Paper.NLSM.Zeros.IsRegularCoordinateZero 6
      (insert (1, 4) (PionCompleteness.Pi.sepPairs 6 {1, 3, 5})) ∧
    ¬PionCompleteness.Paper.NLSM.Zeros.IsMinimalCoordinateZero 6
        (insert (1, 4) (PionCompleteness.Pi.sepPairs 6 {1, 3, 5}))
-/
#guard_msgs in
#check PionCompleteness.PaperTests.not_isMinimalCoordinateZero_six_one_three_five_insert
/--
info: PionCompleteness.PaperTests.isCausalDiamond_six_one_four :
  PionCompleteness.Paper.NLSM.Zeros.Families.IsCausalDiamond 6 (PionCompleteness.Pi.sepPairs 6 {1, 4})
-/
#guard_msgs in
#check PionCompleteness.PaperTests.isCausalDiamond_six_one_four
/--
info: PionCompleteness.PaperTests.not_isCausalDiamond_six_one_three_five :
  ¬PionCompleteness.Paper.NLSM.Zeros.Families.IsCausalDiamond 6 (PionCompleteness.Pi.sepPairs 6 {1, 3, 5})
-/
#guard_msgs in
#check PionCompleteness.PaperTests.not_isCausalDiamond_six_one_three_five
/--
info: PionCompleteness.PaperTests.list_eight_card :
  {Z | PionCompleteness.Paper.NLSM.Zeros.Families.IsListMember 8 Z}.ncard = 30
-/
#guard_msgs in
#check PionCompleteness.PaperTests.list_eight_card
/--
info: PionCompleteness.PaperTests.shiftSign_values :
  PionCompleteness.PionNLSM.shiftSign (2, 4) = 1 ∧
    PionCompleteness.PionNLSM.shiftSign (1, 3) = -1 ∧ PionCompleteness.PionNLSM.shiftSign (1, 4) = 0
-/
#guard_msgs in
#check PionCompleteness.PaperTests.shiftSign_values
/--
info: PionCompleteness.PaperTests.isTriangulation_five : PionCompleteness.TreeRectangleZero.IsTriangulation 5 {(1, 3), (1, 4)}
-/
#guard_msgs in
#check PionCompleteness.PaperTests.isTriangulation_five
/--
info: PionCompleteness.PaperTests.not_isTriangulation_five_not_maximal :
  ¬PionCompleteness.TreeRectangleZero.IsTriangulation 5 {(1, 3)}
-/
#guard_msgs in
#check PionCompleteness.PaperTests.not_isTriangulation_five_not_maximal
/--
info: PionCompleteness.PaperTests.not_isTriangulation_five_crossing :
  ¬PionCompleteness.TreeRectangleZero.IsTriangulation 5 {(1, 3), (2, 4)}
-/
#guard_msgs in
#check PionCompleteness.PaperTests.not_isTriangulation_five_crossing
/--
info: PionCompleteness.PaperTests.delta_coeff :
  PionCompleteness.PionNLSM.delta.coeff (-1) = 1 ∧ PionCompleteness.PionNLSM.delta.coeff 0 = 0
-/
#guard_msgs in
#check PionCompleteness.PaperTests.delta_coeff
/--
info: PionCompleteness.PaperTests.shifted_coeff :
  (PionCompleteness.PionNLSM.shifted (fun x => 2) (1, 3)).coeff 0 = 2 ∧
    (PionCompleteness.PionNLSM.shifted (fun x => 2) (1, 3)).coeff (-1) = -1
-/
#guard_msgs in
#check PionCompleteness.PaperTests.shifted_coeff
/--
info: PionCompleteness.PaperTests.faces_empty {N : ℕ} (hN : 4 ≤ N) (hE : Even N) :
  PionCompleteness.Paper.Combinatorics.Polygons.faces N ∅ = {Finset.Icc 1 N}
-/
#guard_msgs in
#check PionCompleteness.PaperTests.faces_empty
/--
info: PionCompleteness.PaperTests.cayleySum_four :
  PionCompleteness.Paper.NLSM.FeynmanRules.cayleySum 4 PionCompleteness.PionNLSM.gen =
    PionCompleteness.PionNLSM.gen (1, 3) + PionCompleteness.PionNLSM.gen (2, 4)
-/
#guard_msgs in
#check PionCompleteness.PaperTests.cayleySum_four
/--
info: PionCompleteness.PaperTests.faceVertex_four :
  PionCompleteness.Paper.NLSM.FeynmanRules.faceVertex 4 PionCompleteness.PionNLSM.gen (Finset.Icc 1 4) =
    PionCompleteness.PionNLSM.gen (1, 3) + PionCompleteness.PionNLSM.gen (2, 4)
-/
#guard_msgs in
#check PionCompleteness.PaperTests.faceVertex_four
/--
info: PionCompleteness.PaperTests.figure_nine_configuration :
  PionCompleteness.Pi.ThreeSepSetting 10 7 1 3 5 7 {4} {5, 7} {1, 3} ∧
    (∀ t ∈ {5, 7}, t % 2 = 1) ∧ (∀ s ∈ {1, 3}, s % 2 = 1) ∧ ¬PionCompleteness.Paper.CaseEP 1 3 5 7 {4} {5, 7} {1, 3}
-/
#guard_msgs in
#check PionCompleteness.PaperTests.figure_nine_configuration
/--
info: PionCompleteness.PaperTests.example_eight_c_spread :
  PionCompleteness.Pi.oddSide 10 (1, 8) = Finset.Icc 1 7 ∧
    {4} ∈
        PionCompleteness.Pi.admSeps 10 (PionCompleteness.Pi.headStart (1, 8)) (PionCompleteness.Pi.headLen 10 (1, 8))
          0 ∧
      (∀ θ ∈ {4}, θ % 2 = 0) ∧
        Disjoint
            (PionCompleteness.Pi.sepIn 10 (PionCompleteness.Pi.headStart (1, 8)) (PionCompleteness.Pi.headLen 10 (1, 8))
              {4})
            (PionCompleteness.Pi.missing 10
              (PionCompleteness.TreeRectangleZero.diagonals 10 \ {(1, 3), (5, 7), (8, 10)})) ∧
          PionCompleteness.Paper.Combinatorics.Polygons.IsSpread 10
            (PionCompleteness.TreeRectangleZero.diagonals 10 \ {(1, 3), (5, 7), (8, 10)}) (1, 8) {4}
-/
#guard_msgs in
#check PionCompleteness.PaperTests.example_eight_c_spread
/--
info: PionCompleteness.PaperTests.example_shortening_nonvacuous :
  have S :=
    PionCompleteness.TreeRectangleZero.diagonals 12 \
      {(1, 3), (1, 10), (2, 8), (2, 12), (3, 10), (3, 12), (5, 7), (5, 8), (6, 9), (6, 10), (8, 10)};
  (8, 11) ∈ PionCompleteness.PionZeros.oddDiagonals 12 ∧
    PionCompleteness.Pi.NoFreeSep 12 S (PionCompleteness.Pi.tailStart (8, 11)) (PionCompleteness.Pi.tailLen 12 (8, 11))
        1 ∧
      {4, 12} ∈
          PionCompleteness.Pi.admSeps 12 (PionCompleteness.Pi.headStart (8, 11))
            (PionCompleteness.Pi.headLen 12 (8, 11)) 0 ∧
        (∀ θ ∈ {4, 12}, θ % 2 = 0) ∧
          Disjoint
              (PionCompleteness.Pi.sepIn 12 (PionCompleteness.Pi.headStart (8, 11))
                (PionCompleteness.Pi.headLen 12 (8, 11)) {4, 12})
              (PionCompleteness.Pi.missing 12 S) ∧
            PionCompleteness.Paper.Combinatorics.Polygons.IsOccupiedRun 12 S (8, 11) {4, 12} {1, 2, 3} ∧
              PionCompleteness.Paper.Combinatorics.Polygons.IsOccupiedRun 12 S (8, 11) {4, 12} {5, 6, 7} ∧
                (∀ x ∈ {1, 2, 3},
                    ∀ y ∈ {5, 6, 7},
                      PionCompleteness.Pi.cycPos 12 (PionCompleteness.Pi.headStart (8, 11)) x <
                        PionCompleteness.Pi.cycPos 12 (PionCompleteness.Pi.headStart (8, 11)) y) ∧
                  5 ∈ {5, 6, 7} ∧
                    (∀ y ∈ {5, 6, 7},
                        PionCompleteness.Pi.cycPos 12 (PionCompleteness.Pi.headStart (8, 11)) 5 ≤
                          PionCompleteness.Pi.cycPos 12 (PionCompleteness.Pi.headStart (8, 11)) y) ∧
                      (1, 4) ∈ PionCompleteness.PionZeros.oddDiagonals 12 ∧
                        PionCompleteness.Pi.oddSide 12 (1, 4) = {1, 2, 3} ∧
                          {10} ∈
                              PionCompleteness.Pi.admSeps 12 (PionCompleteness.Pi.tailStart (1, 4))
                                (PionCompleteness.Pi.tailLen 12 (1, 4)) 1 ∧
                            Disjoint
                                (PionCompleteness.Pi.sepIn 12 (PionCompleteness.Pi.tailStart (1, 4))
                                  (PionCompleteness.Pi.tailLen 12 (1, 4)) {10})
                                (PionCompleteness.Pi.missing 12 S) ∧
                              5 ∉
                                  Finset.Icc 1 12 \
                                    PionCompleteness.Paper.Combinatorics.Polygons.reachPiece 12 (8, 11) (1, 4) {10} ∧
                                {4, 12} \
                                    (Finset.Icc 1 12 \
                                      PionCompleteness.Paper.Combinatorics.Polygons.reachPiece 12 (8, 11) (1, 4) {10}) =
                                  {4}
-/
#guard_msgs in
#check PionCompleteness.PaperTests.example_shortening_nonvacuous
/--
info: PionCompleteness.PaperTests.ratZeroOn_poly {V : Set (ℕ × ℕ → ℚ)} (hV : ∀ x ∈ V, ∀ y ∈ V, ∀ (t : ℚ), x + t • (y - x) ∈ V)
  {g : PionCompleteness.PionNLSM.RF} {P D : MvPolynomial (ℕ × ℕ) ℚ}
  (hg :
    g * (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) D =
      (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) P)
  (h : PionCompleteness.PionNLSM.RatZeroOn V g) (x : ℕ × ℕ → ℚ) : x ∈ V → (MvPolynomial.eval x) P = 0
-/
#guard_msgs in
#check PionCompleteness.PaperTests.ratZeroOn_poly
/--
info: PionCompleteness.PaperTests.not_hasNoPoleAlong_inv {V : Set (ℕ × ℕ → ℚ)}
  (hV : ∀ x ∈ V, ∀ y ∈ V, ∀ (t : ℚ), x + t • (y - x) ∈ V) (C : ℕ × ℕ) :
  ¬PionCompleteness.Paper.NLSM.Amplitude.HasNoPoleAlong V {x | x ∈ V ∧ x C = 0} (PionCompleteness.PionNLSM.gen C)⁻¹
-/
#guard_msgs in
#check PionCompleteness.PaperTests.not_hasNoPoleAlong_inv
/--
info: PionCompleteness.PaperTests.not_restrictsToZeroAlong_one {V H : Set (ℕ × ℕ → ℚ)}
  (hV : ∀ x ∈ V, ∀ y ∈ V, ∀ (t : ℚ), x + t • (y - x) ∈ V) (hH : H ⊆ V) :
  ¬PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong V H 1
-/
#guard_msgs in
#check PionCompleteness.PaperTests.not_restrictsToZeroAlong_one
/--
info: PionCompleteness.PaperTests.onLocus_line_closed (N : ℕ) (S : Finset (ℕ × ℕ)) (x : ℕ × ℕ → ℚ) :
  x ∈ {X | PionCompleteness.ChainSlice.OnLocus N S X} →
    ∀ y ∈ {X | PionCompleteness.ChainSlice.OnLocus N S X},
      ∀ (t : ℚ), x + t • (y - x) ∈ {X | PionCompleteness.ChainSlice.OnLocus N S X}
-/
#guard_msgs in
#check PionCompleteness.PaperTests.onLocus_line_closed
/--
info: PionCompleteness.PaperTests.restrictsToZeroAlong_numerator {V H : Set (ℕ × ℕ → ℚ)}
  (hV : ∀ x ∈ V, ∀ y ∈ V, ∀ (t : ℚ), x + t • (y - x) ∈ V) (hH : ∀ x ∈ H, ∀ y ∈ H, ∀ (t : ℚ), x + t • (y - x) ∈ H)
  (hHV : H ⊆ V) {f : PionCompleteness.PionNLSM.RF}
  (h : PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong V H f) {P₀ D₀ : MvPolynomial (ℕ × ℕ) ℚ}
  (hf :
    PionCompleteness.PionNLSM.RatZeroOn V
      (f * (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) D₀ -
        (algebraMap (MvPolynomial (ℕ × ℕ) ℚ) PionCompleteness.PionNLSM.RF) P₀))
  (x : ℕ × ℕ → ℚ) : x ∈ H → (MvPolynomial.eval x) P₀ = 0
-/
#guard_msgs in
#check PionCompleteness.PaperTests.restrictsToZeroAlong_numerator
/--
info: PionCompleteness.PaperTests.hasNoPoleAlong_can_fail (N : ℕ) (S : Finset (ℕ × ℕ)) (P : ℕ × ℕ) :
  ¬PionCompleteness.Paper.NLSM.Amplitude.HasNoPoleAlong {X | PionCompleteness.ChainSlice.OnLocus N S X}
      (PionCompleteness.Paper.NLSM.Amplitude.residueHyperplane N S P) (PionCompleteness.PionNLSM.gen P)⁻¹
-/
#guard_msgs in
#check PionCompleteness.PaperTests.hasNoPoleAlong_can_fail
/--
info: PionCompleteness.PaperTests.example_four_six_residue_regime :
  PionCompleteness.Paper.NLSM.Zeros.IsCandidateSet 8
      (PionCompleteness.TreeRectangleZero.diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)}) ∧
    PionCompleteness.Pi.hitClass 8
          (PionCompleteness.TreeRectangleZero.diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)}) (1, 6) =
        {(1, 4), (1, 6)} ∧
      PionCompleteness.Paper.NLSM.Amplitude.FlankClassPoleHypotheses 8
          (PionCompleteness.TreeRectangleZero.diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)})
          (PionCompleteness.Pi.hitClass 8
            (PionCompleteness.TreeRectangleZero.diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)}) (1, 6))
          (1, 6) (1, 6) (1, 4) ∧
        PionCompleteness.Paper.NLSM.Amplitude.stripHalfLength 8 (1, 6) (1, 4) = 1
-/
#guard_msgs in
#check PionCompleteness.PaperTests.example_four_six_residue_regime
/--
info: PionCompleteness.PaperTests.example_no_residue_chord_with_both_sides_linked :
  PionCompleteness.Pi.poleChords 8
        (PionCompleteness.TreeRectangleZero.diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)}) =
      {(1, 4), (1, 6)} ∧
    ({5} ∈
          PionCompleteness.Pi.admSeps 8 (PionCompleteness.Pi.tailStart (1, 4)) (PionCompleteness.Pi.tailLen 8 (1, 4))
            1 ∧
        Disjoint
          (PionCompleteness.Pi.sepIn 8 (PionCompleteness.Pi.tailStart (1, 4)) (PionCompleteness.Pi.tailLen 8 (1, 4))
            {5})
          (PionCompleteness.Pi.missing 8
            (PionCompleteness.TreeRectangleZero.diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)}))) ∧
      ({4} ∈
            PionCompleteness.Pi.admSeps 8 (PionCompleteness.Pi.headStart (1, 6)) (PionCompleteness.Pi.headLen 8 (1, 6))
              0 ∧
          Disjoint
            (PionCompleteness.Pi.sepIn 8 (PionCompleteness.Pi.headStart (1, 6)) (PionCompleteness.Pi.headLen 8 (1, 6))
              {4})
            (PionCompleteness.Pi.missing 8
              (PionCompleteness.TreeRectangleZero.diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)}))) ∧
        PionCompleteness.Pi.IsInnermostChord 8
            (PionCompleteness.TreeRectangleZero.diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)}) (1, 6) ∧
          ∀
            P ∈
              PionCompleteness.Pi.poleChords 8
                (PionCompleteness.TreeRectangleZero.diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)}),
            ¬(PionCompleteness.Pi.NoFreeSep 8
                  (PionCompleteness.TreeRectangleZero.diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)})
                  (PionCompleteness.Pi.headStart P) (PionCompleteness.Pi.headLen 8 P) 0 ∧
                PionCompleteness.Pi.NoFreeSep 8
                  (PionCompleteness.TreeRectangleZero.diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)})
                  (PionCompleteness.Pi.tailStart P) (PionCompleteness.Pi.tailLen 8 P) 1)
-/
#guard_msgs in
#check PionCompleteness.PaperTests.example_no_residue_chord_with_both_sides_linked
/--
info: PionCompleteness.PaperTests.residueHyperplane_line_closed (N : ℕ) (S : Finset (ℕ × ℕ)) (P : ℕ × ℕ) (x : ℕ × ℕ → ℚ) :
  x ∈ PionCompleteness.Paper.NLSM.Amplitude.residueHyperplane N S P →
    ∀ y ∈ PionCompleteness.Paper.NLSM.Amplitude.residueHyperplane N S P,
      ∀ (t : ℚ), x + t • (y - x) ∈ PionCompleteness.Paper.NLSM.Amplitude.residueHyperplane N S P
-/
#guard_msgs in
#check PionCompleteness.PaperTests.residueHyperplane_line_closed
/--
info: PionCompleteness.PaperTests.example_four_six_extreme_terms_nonvanishing :
  ¬PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong
        {X |
          PionCompleteness.ChainSlice.OnLocus 8
            (PionCompleteness.TreeRectangleZero.diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)}) X}
        (PionCompleteness.Paper.NLSM.Amplitude.residueHyperplane 8
          (PionCompleteness.TreeRectangleZero.diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)}) (1, 6))
        (PionCompleteness.Paper.NLSM.Amplitude.avoidingA 8
          (PionCompleteness.Pi.hitClass 8
            (PionCompleteness.TreeRectangleZero.diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)}) (1, 6))
          (1, 4)) ∧
    ¬PionCompleteness.Paper.NLSM.Amplitude.RestrictsToZeroAlong
        {X |
          PionCompleteness.ChainSlice.OnLocus 8
            (PionCompleteness.TreeRectangleZero.diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)}) X}
        (PionCompleteness.Paper.NLSM.Amplitude.residueHyperplane 8
          (PionCompleteness.TreeRectangleZero.diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)}) (1, 6))
        (PionCompleteness.Paper.NLSM.Amplitude.avoidingB 8
          (PionCompleteness.Pi.hitClass 8
            (PionCompleteness.TreeRectangleZero.diagonals 8 \ {(1, 3), (1, 4), (2, 6), (5, 7), (6, 8)}) (1, 6))
          (1, 6))
-/
#guard_msgs in
#check PionCompleteness.PaperTests.example_four_six_extreme_terms_nonvanishing
/--
info: PionCompleteness.PaperTests.stripFactor_eight_self :
  PionCompleteness.Paper.NLSM.Amplitude.stripFactor 8 (1, 6) (1, 6) (1, 6) = 1
-/
#guard_msgs in
#check PionCompleteness.PaperTests.stripFactor_eight_self
/--
info: PionCompleteness.PaperTests.regionAmp_eight :
  PionCompleteness.Paper.NLSM.Amplitude.regionAmp 8 (1, 6) (1, 4) =
    -(PionCompleteness.PionNLSM.gen (1, 5) + PionCompleteness.PionNLSM.gen (4, 6))
-/
#guard_msgs in
#check PionCompleteness.PaperTests.regionAmp_eight
/--
info: PionCompleteness.PaperTests.stripFactor_eight :
  PionCompleteness.Paper.NLSM.Amplitude.stripFactor 8 (1, 6) (1, 6) (1, 4) =
    -(PionCompleteness.PionNLSM.gen (1, 5) + PionCompleteness.PionNLSM.gen (4, 6)) /
      PionCompleteness.PionNLSM.gen (1, 6)
-/
#guard_msgs in
#check PionCompleteness.PaperTests.stripFactor_eight
/--
info: PionCompleteness.PaperTests.marked_locus_nonvacuous :
  PionCompleteness.Pi.pkRClosed 6 1 {(0, 0)} ∧
    PionCompleteness.Pi.pkRIsMem 6 1 (0, 0) ∧
      ∃ X,
        PionCompleteness.Pi.pkRLam 6 1 {(0, 0)} X ∧
          PionCompleteness.TreeRectangleZero.mesh 6 X 1 5 ≠ 0 ∧ ∀ d ∈ PionCompleteness.PionZeros.oddDiagonals 6, X d ≠ 0
-/
#guard_msgs in
#check PionCompleteness.PaperTests.marked_locus_nonvacuous
/--
info: PionCompleteness.PaperTests.isSameParitySet_six_one_three_five : PionCompleteness.Pi.IsSameParitySet 6 {1, 3, 5}
-/
#guard_msgs in
#check PionCompleteness.PaperTests.isSameParitySet_six_one_three_five
/--
info: PionCompleteness.PaperTests.polygon_value_hypotheses :
  (∀ Q ∈ {(0, 0)}, PionCompleteness.Pi.pkRIsMem 6 1 Q) ∧ ∃ X, PionCompleteness.Pi.pkRLam 6 1 {(0, 0)} X
-/
#guard_msgs in
#check PionCompleteness.PaperTests.polygon_value_hypotheses
/--
info: PionCompleteness.PaperTests.numerator_hom_at_one :
  (MvPolynomial.eval fun x => 1) (PionCompleteness.PionNLSM.NP ℚ 4) =
    (PionCompleteness.PionNLSM.NLSM 4 fun d => (MvPolynomial.eval fun x => 1) (MvPolynomial.X d)) *
      (MvPolynomial.eval fun x => 1) (PionCompleteness.PionNLSM.oddDen ℚ 4)
-/
#guard_msgs in
#check PionCompleteness.PaperTests.numerator_hom_at_one
/--
info: PionCompleteness.PaperTests.example_cut_image_hyperplane_candidates :
  PionCompleteness.Paper.NLSM.Zeros.IsCandidateSet 8
      (PionCompleteness.TreeRectangleZero.diagonals 8 \ {(1, 7), (2, 6), (3, 5), (4, 6), (4, 8)}) ∧
    PionCompleteness.Paper.NLSM.Zeros.IsCandidateSet 6
      ({σ ∈ PionCompleteness.TreeRectangleZero.diagonals 6 |
        PionCompleteness.Pi.ChildPairIn 8
          (PionCompleteness.TreeRectangleZero.diagonals 8 \ {(1, 7), (2, 6), (3, 5), (4, 6), (4, 8)}) 4 5 6
          (fun j => PionCompleteness.TreeRectangleZero.vtx 8 (4 + j - 1)) σ.1 σ.2})
-/
#guard_msgs in
#check PionCompleteness.PaperTests.example_cut_image_hyperplane_candidates
/--
info: PionCompleteness.PaperTests.example_cut_image_hyperplane :
  PionCompleteness.Paper.NLSM.Zeros.IsCandidateSet 8
      (PionCompleteness.TreeRectangleZero.diagonals 8 \ {(1, 7), (2, 6), (3, 5), (4, 6), (4, 8)}) ∧
    (1, 4) ∈
        PionCompleteness.Pi.cleanChords 8
          (PionCompleteness.TreeRectangleZero.diagonals 8 \ {(1, 7), (2, 6), (3, 5), (4, 6), (4, 8)}) ∧
      (1, 4) ∉
          PionCompleteness.Pi.poleChords 8
            (PionCompleteness.TreeRectangleZero.diagonals 8 \ {(1, 7), (2, 6), (3, 5), (4, 6), (4, 8)}) ∧
        ¬PionCompleteness.Paper.HasCutAbsorber 8
              (PionCompleteness.TreeRectangleZero.diagonals 8 \ {(1, 7), (2, 6), (3, 5), (4, 6), (4, 8)}) 4 5 ∧
          PionCompleteness.Paper.NLSM.Zeros.IsCandidateSet 6
              ({σ ∈ PionCompleteness.TreeRectangleZero.diagonals 6 |
                PionCompleteness.Pi.ChildPairIn 8
                  (PionCompleteness.TreeRectangleZero.diagonals 8 \ {(1, 7), (2, 6), (3, 5), (4, 6), (4, 8)}) 4 5 6
                  (fun j => PionCompleteness.TreeRectangleZero.vtx 8 (4 + j - 1)) σ.1 σ.2}) ∧
            ∃ y,
              PionCompleteness.ChainSlice.OnLocus 6
                  ({σ ∈ PionCompleteness.TreeRectangleZero.diagonals 6 |
                    PionCompleteness.Pi.ChildPairIn 8
                      (PionCompleteness.TreeRectangleZero.diagonals 8 \ {(1, 7), (2, 6), (3, 5), (4, 6), (4, 8)}) 4 5 6
                      (fun j => PionCompleteness.TreeRectangleZero.vtx 8 (4 + j - 1)) σ.1 σ.2})
                  y ∧
                ¬∃ X,
                    PionCompleteness.ChainSlice.OnLocus 8
                        (PionCompleteness.TreeRectangleZero.diagonals 8 \ {(1, 7), (2, 6), (3, 5), (4, 6), (4, 8)}) X ∧
                      X (1, 4) = 0 ∧
                        ∀ d ∈ PionCompleteness.TreeRectangleZero.diagonals 6,
                          X (PionCompleteness.PionNLSM.relab 8 4 d) = y d
-/
#guard_msgs in
#check PionCompleteness.PaperTests.example_cut_image_hyperplane
/--
info: PionCompleteness.PaperTests.example_pole_free_locus_six :
  PionCompleteness.Paper.NLSM.Zeros.IsCandidateSet 6 {(2, 4), (2, 5), (3, 5), (3, 6), (4, 6)} ∧
    PionCompleteness.Pi.poleChords 6 {(2, 4), (2, 5), (3, 5), (3, 6), (4, 6)} = ∅ ∧
      ∀ (X : ℕ × ℕ → ℚ),
        PionCompleteness.ChainSlice.OnLocus 6 {(2, 4), (2, 5), (3, 5), (3, 6), (4, 6)} X →
          (∀ d ∈ PionCompleteness.PionZeros.oddDiagonals 6, X d ≠ 0) →
            PionCompleteness.PionNLSM.NLSM 6 X = PionCompleteness.Pi.pkGE 6 X
-/
#guard_msgs in
#check PionCompleteness.PaperTests.example_pole_free_locus_six
/--
info: PionCompleteness.PaperTests.example_pole_free_locus_six_rational :
  PionCompleteness.PionNLSM.RatZeroOn
    {x | PionCompleteness.ChainSlice.OnLocus 6 {(2, 4), (2, 5), (3, 5), (3, 6), (4, 6)} x}
    (PionCompleteness.PionNLSM.NLSM 6 PionCompleteness.PionNLSM.gen -
      ∑ t ∈ PionCompleteness.TreeRectangleZero.diagonals 6 with t.1 % 2 = 0 ∧ t.2 % 2 = 0,
        PionCompleteness.TreeRectangleZero.mesh 6 PionCompleteness.PionNLSM.gen t.1 t.2)
-/
#guard_msgs in
#check PionCompleteness.PaperTests.example_pole_free_locus_six_rational

-- The library definitions read only by the helper statements that relate a `Paper` statement or
-- definition to the library's (`pkTZoneSet`, `pkTZH` in `C1`; `pkGV` in `C4`; `pkRBAP`, `pkRBNP`,
-- `pkRBCross`, `pkRBPsi` in `C6`; `pkRBTP`, `pkRBOT` in `C7`; `pkRBZ5` in `C8`), and nine library
-- theorems the paper cites by name.
/--
info: def PionCompleteness.Pi.pkTZoneSet : ℕ → ℕ → ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ :=
fun ω x0 y1 Θ τ σ =>
  {t ∈ τ |
      ¬(t < x0 ∧ (∀ s ∈ σ, ¬(t ≤ s ∧ s ≤ x0)) ∧ ((∀ s ∈ σ, ¬s ≤ x0) ∨ ∃ θ ∈ Θ, θ < t ∧ ∀ s ∈ σ, ¬(θ ≤ s ∧ s ≤ x0)) ∨
          y1 < t ∧ (∀ s ∈ σ, ¬s ≤ x0) ∧ ∃ θ ∈ Θ, y1 < θ ∧ θ < t ∧ ∀ s ∈ σ, ¬(θ ≤ s ∧ s ≤ ω))} ∪
    {s ∈ σ |
      ¬(y1 < s ∧
            (∀ t ∈ τ, ¬(y1 ≤ t ∧ t ≤ s)) ∧
              ((∀ t ∈ τ, ¬(y1 ≤ t ∧ t ≤ ω)) ∨ ∃ θ ∈ Θ, s < θ ∧ ∀ t ∈ τ, ¬(y1 ≤ t ∧ t ≤ θ)) ∨
          s < x0 ∧ (∀ t ∈ τ, ¬(y1 ≤ t ∧ t ≤ ω)) ∧ ∃ θ ∈ Θ, s < θ ∧ θ < x0 ∧ ∀ t ∈ τ, ¬t ≤ θ)}
-/
#guard_msgs in
#print PionCompleteness.Pi.pkTZoneSet
/--
info: def PionCompleteness.Pi.pkTZH : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Prop :=
fun N ω x0 x1 y0 y1 Θ τ σ =>
  PionCompleteness.Pi.ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ ∧
    (∀ t ∈ τ, t % 2 = 1) ∧
      (∀ t ∈ σ, t % 2 = 1) ∧
        (∀ a ∈ Finset.Icc x0 x1 ∪ τ,
            ∀ b ∈ Finset.Icc x0 x1 ∪ τ,
              a < b → (∀ k ∈ Finset.Icc x0 x1 ∪ τ, ¬(a < k ∧ k < b)) → {x ∈ Θ | a < x ∧ x < b}.card ≤ 1) ∧
          ∀ a ∈ Finset.Icc y0 y1 ∪ σ,
            ∀ b ∈ Finset.Icc y0 y1 ∪ σ,
              a < b → (∀ k ∈ Finset.Icc y0 y1 ∪ σ, ¬(a < k ∧ k < b)) → {x ∈ Θ | a < x ∧ x < b}.card ≤ 1
-/
#guard_msgs in
#print PionCompleteness.Pi.pkTZH
/--
info: def PionCompleteness.Pi.pkGV : ℕ → (ℕ × ℕ → ℚ) → Finset (ℕ × ℕ) → ℕ × ℕ → ℚ :=
fun N X D r =>
  PionCompleteness.Pi.pkGSgn (PionCompleteness.Pi.pkGVerts D r).card *
    PionCompleteness.Pi.pkGQ N X (PionCompleteness.Pi.pkGU D r)
-/
#guard_msgs in
#print PionCompleteness.Pi.pkGV
/--
info: def PionCompleteness.Pi.pkRBAP.{u_1} : (R : Type u_1) →
  [inst : CommRing R] → ℕ → ℕ → Finset (ℕ × ℕ) → MvPolynomial (ℕ × ℕ) R :=
fun R [CommRing R] n m K =>
  (PowerSeries.coeff m)
    (∑ T ∈ PionCompleteness.TreeRectangleZero.triangulations n with Disjoint T K, PionCompleteness.Pi.pkRBF R n K T)
-/
#guard_msgs in
#print PionCompleteness.Pi.pkRBAP
/--
info: def PionCompleteness.Pi.pkRBNP.{u_1} : (R : Type u_1) →
  [inst : CommRing R] → ℕ → Finset (ℕ × ℕ) → MvPolynomial (ℕ × ℕ) R :=
fun R [CommRing R] n K => PionCompleteness.Pi.pkRBAP R n (n - 2) K
-/
#guard_msgs in
#print PionCompleteness.Pi.pkRBNP
/--
info: def PionCompleteness.Pi.pkRBCross.{u_1} : (R : Type u_1) →
  [inst : CommRing R] → ℕ → Finset (ℕ × ℕ) → ℕ × ℕ → MvPolynomial (ℕ × ℕ) R :=
fun R [CommRing R] N K C =>
  ∏ d ∈ {d ∈ PionCompleteness.PionZeros.oddDiagonals N | PionCompleteness.TreeRectangleZero.Crosses d C} \ K,
    MvPolynomial.X d
-/
#guard_msgs in
#print PionCompleteness.Pi.pkRBCross
/--
info: def PionCompleteness.Pi.pkRBPsi.{u_1} : (R : Type u_1) →
  [inst : CommRing R] → (P : ℕ × ℕ → Prop) → [DecidablePred P] → MvPolynomial (ℕ × ℕ) R →ₐ[R] MvPolynomial (ℕ × ℕ) R :=
fun R [CommRing R] P [DecidablePred P] => MvPolynomial.aeval fun d => if P d then 1 else MvPolynomial.X d
-/
#guard_msgs in
#print PionCompleteness.Pi.pkRBPsi
/--
info: def PionCompleteness.Pi.pkRBTP : ℕ → ℕ × ℕ → ℕ × ℕ → ℕ → ℕ → Prop :=
fun N Q Q' a b =>
  a % 2 = b % 2 ∧
      a ∈ PionCompleteness.Pi.oddSide N Q ∧
        a ∉ PionCompleteness.Pi.oddSide N Q' ∧
          b ∈ PionCompleteness.Pi.oddSide N Q ∧ b ∉ PionCompleteness.Pi.oddSide N Q' ∨
    a % 2 = 1 ∧
        a ∈ PionCompleteness.Pi.oddSide N Q ∧
          a ∉ PionCompleteness.Pi.oddSide N Q' ∧ b ∈ PionCompleteness.Pi.oddSide N Q' ∨
      b % 2 = 1 ∧
          b ∈ PionCompleteness.Pi.oddSide N Q ∧
            b ∉ PionCompleteness.Pi.oddSide N Q' ∧ a ∈ PionCompleteness.Pi.oddSide N Q' ∨
        a % 2 = 0 ∧
            a ∈ PionCompleteness.Pi.oddSide N Q ∧
              a ∉ PionCompleteness.Pi.oddSide N Q' ∧ b ∈ PionCompleteness.Pi.evenSide N Q ∨
          b % 2 = 0 ∧
            b ∈ PionCompleteness.Pi.oddSide N Q ∧
              b ∉ PionCompleteness.Pi.oddSide N Q' ∧ a ∈ PionCompleteness.Pi.evenSide N Q
-/
#guard_msgs in
#print PionCompleteness.Pi.pkRBTP
/--
info: def PionCompleteness.Pi.pkRBOT : ℕ → ℕ → ℕ → ℕ → ℕ → (ℕ × ℕ → ℚ) → Prop :=
fun N a p L L' X =>
  (∀ (i j : ℕ),
      i < p ∨ p + L' ≤ i ∧ i < L →
        j < p ∨ p + L' ≤ j ∧ j < L →
          i % 2 = j % 2 →
            i ≠ j →
              PionCompleteness.TreeRectangleZero.mesh N X (PionCompleteness.TreeRectangleZero.vtx N (a + i))
                  (PionCompleteness.TreeRectangleZero.vtx N (a + j)) =
                0) ∧
    (∀ (i j : ℕ),
        i < p ∨ p + L' ≤ i ∧ i < L →
          i % 2 = 0 →
            p ≤ j →
              j < p + L' →
                PionCompleteness.TreeRectangleZero.mesh N X (PionCompleteness.TreeRectangleZero.vtx N (a + i))
                    (PionCompleteness.TreeRectangleZero.vtx N (a + j)) =
                  0) ∧
      ∀ (i j : ℕ),
        i < p ∨ p + L' ≤ i ∧ i < L →
          i % 2 = 1 →
            L ≤ j →
              j < N →
                PionCompleteness.TreeRectangleZero.mesh N X (PionCompleteness.TreeRectangleZero.vtx N (a + i))
                    (PionCompleteness.TreeRectangleZero.vtx N (a + j)) =
                  0
-/
#guard_msgs in
#print PionCompleteness.Pi.pkRBOT
/--
info: def PionCompleteness.Pi.pkRBZ5 : ℕ → ℕ → Finset ℕ → Finset (ℕ × ℕ) → (ℕ × ℕ → ℚ) → Prop :=
fun n ε R K X =>
  (∀ a ∈ Finset.Icc 1 n,
      ∀ b ∈ Finset.Icc 1 n,
        a % 2 = ε → a ∉ R → b % 2 = ε → b ∉ R → PionCompleteness.TreeRectangleZero.mesh n X a b = 0) ∧
    (∀ a ∈ Finset.Icc 1 n, a % 2 = ε → a ∉ R → ∀ w ∈ R, PionCompleteness.TreeRectangleZero.mesh n X a w = 0) ∧
      ∀ Q ∈ K,
        ∀ w ∈ Finset.Icc 1 n,
          ∀ a ∈ Finset.Icc 1 n,
            w % 2 ≠ ε →
              a % 2 = ε →
                a ∉ R →
                  (∀ r ∈ R, Q.1 ≤ w ∧ w < Q.2 ↔ Q.1 ≤ r ∧ r < Q.2) →
                    (∀ r ∈ R, ¬(Q.1 ≤ a ∧ a < Q.2 ↔ Q.1 ≤ r ∧ r < Q.2)) →
                      PionCompleteness.TreeRectangleZero.mesh n X w a = 0
-/
#guard_msgs in
#print PionCompleteness.Pi.pkRBZ5
/--
info: PionCompleteness.TreeRectangleZero.onRect_inhabited {n k m : ℕ} (hk : 1 ≤ k) (hkn : k + 3 ≤ n) (hm : 1 ≤ m)
  (hmn : m ≤ n) :
  ∃ X,
    (∀ d ∈ PionCompleteness.TreeRectangleZero.diagonals n, X d ≠ 0) ∧ PionCompleteness.TreeRectangleZero.OnRect n k m X
-/
#guard_msgs in
#check PionCompleteness.TreeRectangleZero.onRect_inhabited
/--
info: PionCompleteness.PionNLSM.amp_ratZero_onRect {n k m : ℕ} (hk : 1 ≤ k) (hkn : k + 3 ≤ n) (hm : 1 ≤ m) (hmn : m ≤ n) :
  PionCompleteness.PionNLSM.RatZeroOn {x | PionCompleteness.TreeRectangleZero.OnRect n k m x}
    (PionCompleteness.TreeRectangleZero.amp n PionCompleteness.PionNLSM.gen)
-/
#guard_msgs in
#check PionCompleteness.PionNLSM.amp_ratZero_onRect
/--
info: PionCompleteness.Pi.pkL_onLocus_anchor {N a b : ℕ} (hN : 4 ≤ N) (ha : 1 ≤ a) (hab : a + 2 ≤ b) (hb : b ≤ N)
  {X : ℕ × ℕ → ℚ} (hR : PionCompleteness.TreeRectangleZero.OnRect N (b - a - 1) (a + 1) X) :
  PionCompleteness.ChainSlice.OnLocus N (PionCompleteness.Pi.sepPairs N {a, b}) X
-/
#guard_msgs in
#check PionCompleteness.Pi.pkL_onLocus_anchor
/--
info: PionCompleteness.Pi.pkM_base4 {S : Finset (ℕ × ℕ)} (hF : PionCompleteness.Pi.InFpi 4 S) :
  PionCompleteness.Pi.NonzeroOn 4 S
-/
#guard_msgs in
#check PionCompleteness.Pi.pkM_base4
/--
info: PionCompleteness.Pi.pkR_const9 {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) (d₁ : ℕ) (hd : 2 * d₁ + 2 ≤ n) :
  ∃ F₁ c,
    (∀ (X : ℕ × ℕ → ℚ),
        PionCompleteness.Pi.pkRLam n d₁ ∅ X →
          (MvPolynomial.eval X) (PionCompleteness.PionNLSM.NP ℚ n) =
            PionCompleteness.TreeRectangleZero.mesh n X 1 (n - 1) * (MvPolynomial.eval X) F₁) ∧
      ∀ (X : ℕ × ℕ → ℚ),
        PionCompleteness.Pi.pkRLam n d₁ ∅ X →
          PionCompleteness.TreeRectangleZero.mesh n X 1 (n - 1) = 0 →
            (MvPolynomial.eval X) F₁ = c * (MvPolynomial.eval X) (PionCompleteness.PionNLSM.oddDen ℚ n)
-/
#guard_msgs in
#check PionCompleteness.Pi.pkR_const9
/--
info: PionCompleteness.Pi.pkR_omega0
  (hR5two :
    ∀ {n : ℕ},
      n % 2 = 0 →
        4 ≤ n →
          ∀ {p q lo hi : ℕ},
            (p, q) ∈ PionCompleteness.PionZeros.oddDiagonals n →
              p ≤ lo →
                lo ≤ hi →
                  hi < q →
                    lo % 2 = p % 2 →
                      ∀ X ∈ {X | PionCompleteness.Pi.pkRZ5c n (p % 2) (Finset.Icc lo hi) {(p, q)} X},
                        (MvPolynomial.eval X) (PionCompleteness.Pi.pkRBNP ℚ n {(p, q)}) = 0)
  (hR5one :
    ∀ {n : ℕ},
      n % 2 = 0 →
        4 ≤ n →
          ∀ {p q lo hi : ℕ},
            (p, q) ∈ PionCompleteness.PionZeros.oddDiagonals n →
              lo ≤ p →
                q ≤ hi + 1 →
                  ∀ {r₀ : ℕ},
                    r₀ ∈ {c ∈ Finset.Icc 1 n | c < lo ∨ hi < c} →
                      r₀ % 2 = q % 2 →
                        ∀
                          X ∈
                            {X |
                              PionCompleteness.Pi.pkRZ5c n (q % 2) ({c ∈ Finset.Icc 1 n | c < lo ∨ hi < c}) {(p, q)} X},
                          (MvPolynomial.eval X) (PionCompleteness.Pi.pkRBNP ℚ n {(p, q)}) = 0)
  {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) (d₁ : ℕ) (hd : 2 * d₁ + 2 ≤ n) :
  ∃ c F,
    c ≠ 0 ∧
      ∀ (X : ℕ × ℕ → ℚ),
        PionCompleteness.Pi.pkRLam n d₁ ∅ X →
          (MvPolynomial.eval X) (PionCompleteness.PionNLSM.NP ℚ n) =
            PionCompleteness.TreeRectangleZero.mesh n X 1 (n - 1) *
              (c * (MvPolynomial.eval X) (PionCompleteness.PionNLSM.oddDen ℚ n) +
                PionCompleteness.TreeRectangleZero.mesh n X 1 (n - 1) * (MvPolynomial.eval X) F)
-/
#guard_msgs in
#check PionCompleteness.Pi.pkR_omega0
/--
info: PionCompleteness.Pi.pkR_psi_all
  (hR5two :
    ∀ {n : ℕ},
      n % 2 = 0 →
        4 ≤ n →
          ∀ {p q lo hi : ℕ},
            (p, q) ∈ PionCompleteness.PionZeros.oddDiagonals n →
              p ≤ lo →
                lo ≤ hi →
                  hi < q →
                    lo % 2 = p % 2 →
                      ∀ X ∈ {X | PionCompleteness.Pi.pkRZ5c n (p % 2) (Finset.Icc lo hi) {(p, q)} X},
                        (MvPolynomial.eval X) (PionCompleteness.Pi.pkRBNP ℚ n {(p, q)}) = 0)
  (hR5one :
    ∀ {n : ℕ},
      n % 2 = 0 →
        4 ≤ n →
          ∀ {p q lo hi : ℕ},
            (p, q) ∈ PionCompleteness.PionZeros.oddDiagonals n →
              lo ≤ p →
                q ≤ hi + 1 →
                  ∀ {r₀ : ℕ},
                    r₀ ∈ {c ∈ Finset.Icc 1 n | c < lo ∨ hi < c} →
                      r₀ % 2 = q % 2 →
                        ∀
                          X ∈
                            {X |
                              PionCompleteness.Pi.pkRZ5c n (q % 2) ({c ∈ Finset.Icc 1 n | c < lo ∨ hi < c}) {(p, q)} X},
                          (MvPolynomial.eval X) (PionCompleteness.Pi.pkRBNP ℚ n {(p, q)}) = 0)
  (n : ℕ) :
  n % 2 = 0 →
    4 ≤ n →
      ∀ (d₁ : ℕ),
        2 * d₁ + 2 ≤ n →
          ∀ (F₁ : MvPolynomial (ℕ × ℕ) ℚ) (c : ℚ),
            (∀ (X : ℕ × ℕ → ℚ),
                PionCompleteness.Pi.pkRLam n d₁ ∅ X →
                  (MvPolynomial.eval X) (PionCompleteness.PionNLSM.NP ℚ n) =
                    PionCompleteness.TreeRectangleZero.mesh n X 1 (n - 1) * (MvPolynomial.eval X) F₁) →
              (∀ (X : ℕ × ℕ → ℚ),
                  PionCompleteness.Pi.pkRLam n d₁ ∅ X →
                    PionCompleteness.TreeRectangleZero.mesh n X 1 (n - 1) = 0 →
                      (MvPolynomial.eval X) F₁ = c * (MvPolynomial.eval X) (PionCompleteness.PionNLSM.oddDen ℚ n)) →
                c ≠ 0
-/
#guard_msgs in
#check PionCompleteness.Pi.pkR_psi_all
/--
info: PionCompleteness.Pi.pkR_notq_lam {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ : ℕ} {I : Finset (ℕ × ℕ)}
  (hI : ∀ Q ∈ I, PionCompleteness.Pi.pkRIsMem n d₁ Q) {q : ℕ × ℕ} (hq : q ∈ I)
  (hR5two :
    ∀ {n : ℕ},
      n % 2 = 0 →
        4 ≤ n →
          ∀ {p q lo hi : ℕ},
            (p, q) ∈ PionCompleteness.PionZeros.oddDiagonals n →
              p ≤ lo →
                lo ≤ hi →
                  hi < q →
                    lo % 2 = p % 2 →
                      ∀ X ∈ {X | PionCompleteness.Pi.pkRZ5c n (p % 2) (Finset.Icc lo hi) {(p, q)} X},
                        (MvPolynomial.eval X) (PionCompleteness.Pi.pkRBNP ℚ n {(p, q)}) = 0)
  (hR5one :
    ∀ {n : ℕ},
      n % 2 = 0 →
        4 ≤ n →
          ∀ {p q lo hi : ℕ},
            (p, q) ∈ PionCompleteness.PionZeros.oddDiagonals n →
              lo ≤ p →
                q ≤ hi + 1 →
                  ∀ {r₀ : ℕ},
                    r₀ ∈ {c ∈ Finset.Icc 1 n | c < lo ∨ hi < c} →
                      r₀ % 2 = q % 2 →
                        ∀
                          X ∈
                            {X |
                              PionCompleteness.Pi.pkRZ5c n (q % 2) ({c ∈ Finset.Icc 1 n | c < lo ∨ hi < c}) {(p, q)} X},
                          (MvPolynomial.eval X) (PionCompleteness.Pi.pkRBNP ℚ n {(p, q)}) = 0) :
  ∃ G,
    ∀ (X : ℕ × ℕ → ℚ),
      PionCompleteness.Pi.pkRLam n d₁ I X →
        (MvPolynomial.eval X) (PionCompleteness.Pi.pkRBNP ℚ n {PionCompleteness.Pi.pkRMchord d₁ q}) =
          PionCompleteness.TreeRectangleZero.mesh n X 1 (n - 1) ^ (I.card + 1) * (MvPolynomial.eval X) G
-/
#guard_msgs in
#check PionCompleteness.Pi.pkR_notq_lam
/--
info: PionCompleteness.Pi.pkR_omega {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) (d₁ : ℕ) (hd : 2 * d₁ + 2 ≤ n) (I : Finset (ℕ × ℕ))
  (hI : ∀ Q ∈ I, PionCompleteness.Pi.pkRIsMem n d₁ Q) :
  ∃ c F,
    c ≠ 0 ∧
      ∀ (X : ℕ × ℕ → ℚ),
        PionCompleteness.Pi.pkRLam n d₁ I X →
          (MvPolynomial.eval X) (PionCompleteness.PionNLSM.NP ℚ n) =
            PionCompleteness.TreeRectangleZero.mesh n X 1 (n - 1) ^ I.card *
              (c * PionCompleteness.TreeRectangleZero.mesh n X 1 (n - 1) *
                  ∏ Q ∈ PionCompleteness.PionZeros.oddDiagonals n with
                    Q ∉ Finset.image (PionCompleteness.Pi.pkRMchord d₁) I, X Q +
                PionCompleteness.TreeRectangleZero.mesh n X 1 (n - 1) ^ 2 * (MvPolynomial.eval X) F)
-/
#guard_msgs in
#check PionCompleteness.Pi.pkR_omega
