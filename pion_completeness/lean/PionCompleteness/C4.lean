/-
Copyright (c) 2026 Henru Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henru Wang
-/
module

public import PionCompleteness.C3

/-!
# Theorem Π, part 4: the M2 form, and dissections for the germ input

This module continues the chain of modules that prove Theorem Π; the chain is cut by size, not by
topic, so the sections run on from `C3`.
It continues section 8 (Theorem Π), whose heading ends `C3`.

It defines the three analytic inputs `GermInput`, `ResChildInput` and `STZeroInput` and proves
Theorem Π with them as hypotheses (the M2 form, conditional on the inputs; the M3 form proves the
inputs and so states Theorem Π without hypotheses): clause 1 `pi_clause1_M2` (by the induction
`pkM_c1_ind`, base case `pkM_base4`), the members of `𝒢_N` as non-degenerate zeros (`cl2a_M2`),
clause 2 from clause 1 (`prop14_7`) and the characterisation of the minimal zeros
(`minimal_iff_of`), and `pi_clause2_M2`, `pi_minimal_iff_M2`.

Then the M3 part begins with the helpers (prefix `pkG_`) of the proof of the germ input
(`germ_input`, `C5`): dissections by odd chords as rooted laminar families of faces (`pkGDis`,
`pkGKids`, `pkGVerts`, the class `pkGU`), the tree lemma `pkG_tree`, the face counts
`pkG_G3_clean`, `pkG_G3_leaf`, the Cayley vertex `pkGV` of a face and the faces on which it
vanishes (`pkG_V_base`, `pkG_V_leaf`, `pkG_G4`); the linear layer (`pkG_A4_all`, `pkG_A5_all`,
`pkG_S1`, `pkG_V_empty`, the clean chords `pkG_G1_clean`, `pkG_G1_wit`, the witness `pkG_Ewit`,
the avoidance lemma `pkG_avoid_locus`); and the start of the split of a dissection along a chord
(the relabellings `pkGSh`, `pkGCt`, the transport of variables, vertices, classes and Cayley
vertices to the two children, `pkG_glue_dis`, `pkGSplit`), which continues in `C5`.

The conventions are those of `C0`'s module docstring.
-/

@[expose] public section

namespace PionCompleteness.Pi

open Finset PionCompleteness.TreeRectangleZero PionCompleteness.ChainSlice
  PionCompleteness.PionZeros PionCompleteness.PionNLSM

/-- **The germ input** (analytic) at size `N` (the paper's first-order regime: non-vanishing without
residue chords): every `S ∈ F^π` with `𝒫₁ = ∅` has `NonzeroOn N S`. It is proved as `germ_input`
(`C5`). -/
def GermInput (N : ℕ) : Prop :=
  ∀ S : Finset (ℕ × ℕ), InFpi N S → poleChords N S = ∅ → NonzeroOn N S

/-- **The residue and children input** (analytic) at size `N`. Let `S ∈ F^π`, `t ∈ 𝒫₁`, and `b` a
member of the class `K = hitClass N S t` such that every member's head lies between the heads of `b`
and `t` (`A_b ⊆ A_Q ⊆ A_t` for `Q ∈ K`: `t` is the top and `b` the bottom of `K` for head
inclusion). Assume (H2): `K` is exactly the set of odd chords `Q` with `X_Q = c · X_t` on `L_S` for
some rational `c ≠ 0`, and every member equals `X_t` on `L_S`. Then `NonzeroOn` for the B-child set
`childSetB N S t` of `t` (size `tailLen N t + 1`) and for the A-child set `childSetA N S b` of `b`
(size `headLen N b + 1`) gives `NonzeroOn N S`. It is proved as `resChild_input` (`C10`). -/
def ResChildInput (N : ℕ) : Prop :=
  ∀ (S : Finset (ℕ × ℕ)) (t b : ℕ × ℕ), InFpi N S → t ∈ poleChords N S → b ∈ hitClass N S t →
    (∀ Q ∈ hitClass N S t, oddSide N b ⊆ oddSide N Q ∧ oddSide N Q ⊆ oddSide N t) →
    (∀ Q ∈ oddDiagonals N,
      (∃ c : ℚ, c ≠ 0 ∧ ∀ X : ℕ × ℕ → ℚ, OnLocus N S X → X Q = c * X t) ↔ Q ∈ hitClass N S t) →
    (∀ Q ∈ hitClass N S t, ∀ X : ℕ × ℕ → ℚ, OnLocus N S X → X Q = X t) →
    NonzeroOn (tailLen N t + 1) (childSetB N S t) → NonzeroOn (headLen N b + 1) (childSetA N S b) →
    NonzeroOn N S

/-- **The S_T zero input** (analytic): for every same-parity leg set `G`, `𝒜_N` vanishes on
`L_{S_G}` (`AmpZeroOn N (sepPairs N G)`); with `cl2a_diamond` (`C3`) it gives that every member of
`𝒢_N` is a zero. It is proved as `stZero_input` (`C10`), from `nlsm_zero_on_ZT` of `PionNLSM`. -/
def STZeroInput (N : ℕ) : Prop :=
  ∀ G : Finset ℕ, IsSameParitySet N G → AmpZeroOn N (sepPairs N G)

theorem pkM_diag4 : diagonals 4 = {(1, 3), (2, 4)} := by decide

theorem pkM_sep24 : sepPairs 4 {2, 4} = {(1, 3)} := by decide
theorem pkM_sep13 : sepPairs 4 {1, 3} = {(2, 4)} := by decide

theorem pkM_mem_gFamily4 {G : Finset ℕ} (hG : G ⊆ Icc 1 4) (hG' : IsGSet 4 G) :
    sepPairs 4 G ∈ gFamily 4 :=
  mem_image.2 ⟨G, mem_filter.2 ⟨mem_powerset.2 hG, hG'⟩, rfl⟩

-- registry: C-KTX6
/-- Base case: every `S ∈ F^π_4` (necessarily `S = ∅`) has `NonzeroOn`. -/
theorem pkM_base4 {S : Finset (ℕ × ℕ)} (hF : InFpi 4 S) : NonzeroOn 4 S := by
  have h13 : (1, 3) ∉ S := by
    intro h
    apply hF.2.2
    refine ⟨_, pkM_mem_gFamily4 (G := {2, 4}) (by decide) (by decide), ?_⟩
    rw [pkM_sep24]; simpa using h
  have h24 : (2, 4) ∉ S := by
    intro h
    apply hF.2.2
    refine ⟨_, pkM_mem_gFamily4 (G := {1, 3}) (by decide) (by decide), ?_⟩
    rw [pkM_sep13]; simpa using h
  have hS : S = ∅ := by
    ext p
    constructor
    · intro hp
      have := hF.1 hp
      rw [pkM_diag4] at this
      rcases mem_insert.1 this with rfl | h
      · exact absurd hp h13
      · rw [mem_singleton] at h; subst h; exact absurd hp h24
    · simp
  subst hS
  refine ⟨fun _ => 1, fun t ht => by simp at ht, ?_, ?_⟩
  · intro d hd
    have : oddDiagonals 4 = ∅ := by decide
    rw [this] at hd; simp at hd
  · rw [NLSM_four]; norm_num

theorem pkM_poleChords_odd {n : ℕ} {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ} (h : P ∈ poleChords n S) :
    P ∈ oddDiagonals n :=
  (mem_filter.1 (mem_filter.1 h).1).1

theorem pkM_hitClass_pole {n : ℕ} {S : Finset (ℕ × ℕ)} {P Q : ℕ × ℕ} (h : Q ∈ hitClass n S P) :
    Q ∈ poleChords n S :=
  (mem_filter.1 h).1

/-- The induction for clause 1: given `GermInput n` and `ResChildInput n` at every even size
`6 ≤ n ≤ N`, every `S ∈ F^π_n`, `4 ≤ n ≤ N` even, has `NonzeroOn`. -/
theorem pkM_c1_ind {N : ℕ} (hGerm : ∀ n, 6 ≤ n → n ≤ N → Even n → GermInput n)
    (hRes : ∀ n, 6 ≤ n → n ≤ N → Even n → ResChildInput n) :
    ∀ n, 4 ≤ n → n ≤ N → Even n → ∀ S, InFpi n S → NonzeroOn n S := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih
  · intro h4 hnN hEn S hF
    by_cases h6 : 6 ≤ n
    · by_cases hP : (poleChords n S).Nonempty
      · obtain ⟨t, ht, b, hb, hBt, hAb, hint⟩ := chain_interval h6 hEn hF hP
        have hbP : b ∈ poleChords n S := pkM_hitClass_pole hb
        have cB : InFpi (tailLen n t + 1) (childSetB n S t) := (childF h6 hEn hF ht).2.2 hBt
        have cA : InFpi (headLen n b + 1) (childSetA n S b) := (childF h6 hEn hF hbP).1.2 hAb
        obtain ⟨-, -, -, eB, lB, uB⟩ := childSize_bounds (by omega) hEn (pkM_poleChords_odd ht)
        obtain ⟨eA, lA, uA, -, -, -⟩ := childSize_bounds (by omega) hEn (pkM_poleChords_odd hbP)
        have nB := ih _ (by omega) lB (by omega) eB _ cB
        have nA := ih _ (by omega) lA (by omega) eA _ cA
        have hH2 : ∀ Q ∈ oddDiagonals n,
            (∃ c : ℚ, c ≠ 0 ∧ ∀ X : ℕ × ℕ → ℚ, OnLocus n S X → X Q = c * X t) ↔
                Q ∈ hitClass n S t := by
          intro Q hQ
          have L := lemma14_6 h6 hEn hF ht hQ
          constructor
          · rintro ⟨c, hc0, hcX⟩
            exact mem_filter.2 ⟨(L.2 c hc0 hcX).2, L.1.1 ⟨c, hc0, hcX⟩⟩
          · intro hQK
            exact L.1.2 (mem_filter.1 hQK).2
        have hplus : ∀ Q ∈ hitClass n S t, ∀ X : ℕ × ℕ → ℚ, OnLocus n S X → X Q = X t := by
          intro Q hQK X hL
          have L := lemma14_6 h6 hEn hF ht (pkM_poleChords_odd (pkM_hitClass_pole hQK))
          obtain ⟨c, hc0, hcX⟩ := L.1.2 (mem_filter.1 hQK).2
          rw [hcX X hL, (L.2 c hc0 hcX).1, one_mul]
        exact hRes n h6 hnN hEn S t b hF ht hb hint hH2 hplus nB nA
      · exact hGerm n h6 hnN hEn S hF (not_nonempty_iff_eq_empty.1 hP)
    · have : n = 4 := by obtain ⟨k, hk⟩ := hEn; omega
      subst this
      exact pkM_base4 hF

/-- **Theorem Π, clause 1, M2 form**: for even `N ≥ 6`, given `GermInput n` and `ResChildInput n` at
every even size `6 ≤ n ≤ N`, every non-degenerate coordinate zero of `𝒜_N` contains a member of
`𝒢_N`. The proof is a strong induction on even `n` (`pkM_c1_ind`), base `n = 4` from `NLSM_four`
(`PionNLSM`), with `lemma14_6` (`C0`), `childSize_bounds` (`C1`), `chain_interval`, `childF`
(`C3`) and the two inputs. -/
theorem pi_clause1_M2 {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    (hGerm : ∀ n, 6 ≤ n → n ≤ N → Even n → GermInput n)
    (hRes : ∀ n, 6 ≤ n → n ≤ N → Even n → ResChildInput n)
    {S : Finset (ℕ × ℕ)} (hS : IsNDZero N S) : ContainsGMember N S := by
  by_contra hc
  have := pkM_c1_ind hGerm hRes N (by omega) le_rfl hE S ⟨hS.1, hS.2.1, hc⟩
  rw [nonzeroOn_iff_not_ampZeroOn] at this
  exact this hS.2.2

/-- **Members of `𝒢_N` are non-degenerate zeros**, M2 form: for even `N ≥ 6`, given
`STZeroInput N`, every member `Z` of `𝒢_N` is non-degenerate at a point (`NonDegPt`) and `𝒜_N`
vanishes on `L_Z`. -/
theorem cl2a_M2 {N : ℕ} (hN : 6 ≤ N) (hE : Even N) (hST : STZeroInput N) {Z : Finset (ℕ × ℕ)}
    (hZ : Z ∈ gFamily N) :
    NonDegPt N Z ∧ AmpZeroOn N Z := by
  refine ⟨cl2a_nondeg hN hE hZ, ?_⟩
  obtain ⟨G, hG, rfl⟩ := mem_image.1 hZ
  rcases (show IsSameParitySet N G ∨ IsMixedAnchor N G from (mem_filter.1 hG).2) with h | h
  · exact hST G h
  · exact cl2a_diamond hN hE h

/-- **Clause 2 from clause 1**: for even `N ≥ 6`, given clause 1 and, for every member of `𝒢_N`,
`NonDegPt` and the vanishing of `𝒜_N`, every member of `𝒢_N` is a minimal non-degenerate
coordinate zero. The proof:
`S := Z ∖ {t}` misses `t`; if it contained a member `Z'`, the antichain gives `Z' = Z ⊆ Z ∖ {t}`,
impossible; so clause 1 says `S` is not a zero. -/
theorem prop14_7 {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    (clause1 : ∀ S : Finset (ℕ × ℕ), IsNDZero N S → ContainsGMember N S)
    (hcl2a : ∀ Z ∈ gFamily N, NonDegPt N Z ∧ AmpZeroOn N Z) {Z : Finset (ℕ × ℕ)}
    (hZ : Z ∈ gFamily N) :
    IsMinimalZero N Z := by
  obtain ⟨hpt, hz⟩ := hcl2a Z hZ
  refine ⟨⟨gFamily_sub hZ, nonDeg_of_pt hpt, hz⟩, fun t ht h0 => ?_⟩
  have hsub : Z.erase t ⊆ Z := erase_subset t Z
  obtain ⟨Z', hZ', hZ'sub⟩ :=
    clause1 (Z.erase t) ⟨hsub.trans (gFamily_sub hZ), nonDeg_mono hsub (nonDeg_of_pt hpt), h0⟩
  have heq := gFamily_antichain hN hE hZ' hZ (hZ'sub.trans hsub)
  rw [heq] at hZ'sub
  have := hZ'sub ht
  simp at this

/-- **The minimal zeros are the members of `𝒢_N`**: for even `N ≥ 6`, given clause 1 and, for every
member of `𝒢_N`, `NonDegPt` and the vanishing of `𝒜_N`, a set `Z` is a minimal non-degenerate
coordinate zero iff `Z ∈ 𝒢_N`. -/
theorem minimal_iff_of {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    (clause1 : ∀ S : Finset (ℕ × ℕ), IsNDZero N S → ContainsGMember N S)
    (hcl2a : ∀ Z ∈ gFamily N, NonDegPt N Z ∧ AmpZeroOn N Z) {Z : Finset (ℕ × ℕ)} :
    IsMinimalZero N Z ↔ Z ∈ gFamily N := by
  constructor
  · rintro ⟨hZ, hmin⟩
    obtain ⟨Z', hZ', hsub⟩ := clause1 Z hZ
    by_contra hne
    have hne' : Z' ≠ Z := fun h => hne (h ▸ hZ')
    obtain ⟨t, htZ, htZ'⟩ := exists_of_ssubset (lt_of_le_of_ne hsub hne')
    apply hmin t htZ
    exact ampZeroOn_mono (fun x hx => mem_erase.2 ⟨fun h => htZ' (h ▸ hx), hsub hx⟩)
        (hcl2a Z' hZ').2
  · exact fun hZ => prop14_7 hN hE clause1 hcl2a hZ

/-- **Theorem Π, clause 2, M2 form**: for even `N ≥ 6`, given `GermInput n` and `ResChildInput n` at
every even size `6 ≤ n ≤ N` and `STZeroInput N`, every member `Z` of `𝒢_N` is non-degenerate at a
point (`NonDegPt`) and a minimal non-degenerate coordinate zero. -/
theorem pi_clause2_M2 {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    (hGerm : ∀ n, 6 ≤ n → n ≤ N → Even n → GermInput n)
    (hRes : ∀ n, 6 ≤ n → n ≤ N → Even n → ResChildInput n)
    (hST : STZeroInput N) {Z : Finset (ℕ × ℕ)} (hZ : Z ∈ gFamily N) : NonDegPt N Z ∧
        IsMinimalZero N Z :=
  ⟨cl2a_nondeg hN hE hZ,
    prop14_7 hN hE (fun _ h => pi_clause1_M2 hN hE hGerm hRes h)
        (fun _ h => cl2a_M2 hN hE hST h) hZ⟩

/-- **The minimal zeros, M2 form**: for even `N ≥ 6`, given `GermInput n` and `ResChildInput n` at
every even size `6 ≤ n ≤ N` and `STZeroInput N`, the minimal non-degenerate coordinate zeros of
`𝒜_N` are exactly the members of `𝒢_N`. -/
theorem pi_minimal_iff_M2 {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    (hGerm : ∀ n, 6 ≤ n → n ≤ N → Even n → GermInput n)
    (hRes : ∀ n, 6 ≤ n → n ≤ N → Even n → ResChildInput n)
    (hST : STZeroInput N) {Z : Finset (ℕ × ℕ)} : IsMinimalZero N Z ↔ Z ∈ gFamily N :=
  minimal_iff_of hN hE (fun _ h => pi_clause1_M2 hN hE hGerm hRes h)
      (fun _ h => cl2a_M2 hN hE hST h)

/-! ### M3: the proofs of the inputs, and Π without hypotheses

The helpers that follow (prefix `pkG_`, on into `C5`) prove the germ input (`germ_input`, `C5`);
the other two inputs are proved in later modules (`resChild_input`, `stZero_input`, `C10`), and
Theorem Π without hypotheses is stated and proved in `C10`. -/

/-! ### Helpers of the proof of the germ input (prefix `pkG_`): faces of dissections

Dissections by odd chords, read as rooted laminar families of faces. -/

-- registry: C-8TJ0 T-688E
/-- Dissections by odd chords: sets of pairwise non-crossing odd chords. -/
def pkGDis (N : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  (oddDiagonals N).powerset.filter (fun D => ∀ p ∈ D, ∀ q ∈ D, ¬ Crosses p q)

/-- Strict interval containment of chords. -/
def pkGIn (R r : ℕ × ℕ) : Prop := R ≠ r ∧ r.1 ≤ R.1 ∧ R.2 ≤ r.2

theorem pkG_In_iff {R r : ℕ × ℕ} : pkGIn R r ↔ R ≠ r ∧ r.1 ≤ R.1 ∧ R.2 ≤ r.2 := Iff.rfl

/-- Root sides = face indices. -/
def pkGRoots (N : ℕ) (D : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) := insert (1, N) D

/-- Children of the face with root side `r`: maximal chords of `D` strictly inside `r`. -/
def pkGKids (D : Finset (ℕ × ℕ)) (r : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  D.filter (fun R => (R ≠ r ∧ r.1 ≤ R.1 ∧ R.2 ≤ r.2) ∧
    ∀ R' ∈ D, (R' ≠ r ∧ r.1 ≤ R'.1 ∧ R'.2 ≤ r.2) → ¬ (R ≠ R' ∧ R'.1 ≤ R.1 ∧ R.2 ≤ R'.2))

/-- Vertices of the face with root side `r`. -/
def pkGVerts (D : Finset (ℕ × ℕ)) (r : ℕ × ℕ) : Finset ℕ :=
  (Icc r.1 r.2).filter (fun w => ∀ R ∈ pkGKids D r, ¬ (R.1 < w ∧ w < R.2))

/-- Governing vertex of leg `x` in face `r`: the largest face vertex `≤ x` (`Finset.sup`; `0` if
none). -/
def pkGGov (D : Finset (ℕ × ℕ)) (r : ℕ × ℕ) (x : ℕ) : ℕ :=
  ((pkGVerts D r).filter (fun w => w ≤ x)).sup (fun w => w)

/-- The relative class `U'(D, r)`: legs of `[r.1, r.2)` whose governing vertex has the parity of
`r.1`. -/
def pkGU (D : Finset (ℕ × ℕ)) (r : ℕ × ℕ) : Finset ℕ :=
  (Ico r.1 r.2).filter (fun x => (pkGGov D r x + r.1) % 2 = 0)

theorem pkG_mem_dis {N : ℕ} {D : Finset (ℕ × ℕ)} :
    D ∈ pkGDis N ↔ D ⊆ oddDiagonals N ∧ ∀ p ∈ D, ∀ q ∈ D, ¬ Crosses p q := by
  change D ∈ (oddDiagonals N).powerset.filter _ ↔ _
  rw [mem_filter, mem_powerset]

theorem pkG_mem_kids {D : Finset (ℕ × ℕ)} {r R : ℕ × ℕ} :
    R ∈ pkGKids D r ↔ R ∈ D ∧ pkGIn R r ∧ ∀ R' ∈ D, pkGIn R' r → ¬ pkGIn R R' := by
  change R ∈ D.filter _ ↔ _
  exact mem_filter

theorem pkG_mem_verts {D : Finset (ℕ × ℕ)} {r : ℕ × ℕ} {w : ℕ} :
    w ∈ pkGVerts D r ↔ r.1 ≤ w ∧ w ≤ r.2 ∧ ∀ R ∈ pkGKids D r, ¬ (R.1 < w ∧ w < R.2) := by
  change w ∈ (Icc r.1 r.2).filter _ ↔ _
  rw [mem_filter, mem_Icc, and_assoc]

theorem pkG_mem_U {D : Finset (ℕ × ℕ)} {r : ℕ × ℕ} {x : ℕ} :
    x ∈ pkGU D r ↔ r.1 ≤ x ∧ x < r.2 ∧ (pkGGov D r x + r.1) % 2 = 0 := by
  change x ∈ (Ico r.1 r.2).filter _ ↔ _
  rw [mem_filter, mem_Ico, and_assoc]

theorem pkG_crosses_iff {p q : ℕ × ℕ} :
    Crosses p q ↔ (p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2) ∨
        (q.1 < p.1 ∧ p.1 < q.2 ∧ q.2 < p.2) := Iff.rfl

/-- A chord of a dissection: an odd chord `R` with `R.1 + 3 ≤ R.2`, other than `(1, N)`. -/
theorem pkG_chord {N : ℕ} {D : Finset (ℕ × ℕ)} (hD : D ∈ pkGDis N) {R : ℕ × ℕ} (hR : R ∈ D) :
    1 ≤ R.1 ∧ R.2 ≤ N ∧ R.1 + 3 ≤ R.2 ∧ (R.2 - R.1) % 2 = 1 ∧ ¬ (R.1 = 1 ∧ R.2 = N) := by
  have h1 := (pkG_mem_dis.1 hD).1 hR
  have h2 := mem_filter.1 h1
  obtain ⟨a, b, c, d⟩ := mem_diagonals.1 h2.1
  have e := h2.2
  omega

/-- A root side: `(1, N)` or a chord. -/
theorem pkG_root {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)}
    (hD : D ∈ pkGDis N) {r : ℕ × ℕ}
    (hr : r ∈ pkGRoots N D) : 1 ≤ r.1 ∧ r.2 ≤ N ∧ r.1 + 3 ≤ r.2 ∧ (r.2 - r.1) % 2 = 1 := by
  rcases mem_insert.1 hr with h | h
  · have e1 : r.1 = 1 := by rw [h]
    have e2 : r.2 = N := by rw [h]
    omega
  · have := pkG_chord hD h
    omega

/-- **Laminarity**: two non-crossing chords are nested or disjoint (as intervals). -/
theorem pkG_lam {p q : ℕ × ℕ} (h : ¬ Crosses p q) :
    (q.1 ≤ p.1 ∧ p.2 ≤ q.2) ∨ (p.1 ≤ q.1 ∧ q.2 ≤ p.2) ∨ p.2 ≤ q.1 ∨ q.2 ≤ p.1 := by
  rw [pkG_crosses_iff] at h
  omega

/-- Root sides do not cross. -/
theorem pkG_root_nc {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)} (hD : D ∈ pkGDis N)
    {p q : ℕ × ℕ}
    (hp : p ∈ pkGRoots N D) (hq : q ∈ pkGRoots N D) : ¬ Crosses p q := by
  rcases mem_insert.1 hp with h | h
  · have e1 : p.1 = 1 := by rw [h]
    have e2 : p.2 = N := by rw [h]
    have := pkG_root hN hE hD hq
    rw [pkG_crosses_iff]
    omega
  · rcases mem_insert.1 hq with h' | h'
    · have e1 : q.1 = 1 := by rw [h']
      have e2 : q.2 = N := by rw [h']
      have := pkG_root hN hE hD hp
      rw [pkG_crosses_iff]
      omega
    · exact (pkG_mem_dis.1 hD).2 p h q h'

theorem pkG_ne_of {p q : ℕ × ℕ} (h : ¬ (p.1 = q.1 ∧ p.2 = q.2)) : p ≠ q :=
  fun e => h ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩

theorem pkG_eq_of {p q : ℕ × ℕ} (h1 : p.1 = q.1) (h2 : p.2 = q.2) : p = q := Prod.ext h1 h2

/-- The root `(1, N)` is not a chord. -/
theorem pkG_top_nmem {N : ℕ} {D : Finset (ℕ × ℕ)} (hD : D ∈ pkGDis N) : (1, N) ∉ D := by
  intro h
  have := pkG_chord hD h
  dsimp only at this
  omega

/-- `|faces| = |D| + 1`. -/
theorem pkG_card_roots {N : ℕ} {D : Finset (ℕ × ℕ)} (hD : D ∈ pkGDis N) :
    (pkGRoots N D).card = D.card + 1 :=
  card_insert_of_notMem (pkG_top_nmem hD)

/-- A kid violating maximality. -/
theorem pkG_kid_max {D : Finset (ℕ × ℕ)} {r R R' : ℕ × ℕ} (hR : R ∈ pkGKids D r) (hR' : R' ∈ D)
    (h1 : pkGIn R' r) (h2 : pkGIn R R') : False :=
  (pkG_mem_kids.1 hR).2.2 R' hR' h1 h2

/-- **Parent of a chord, existence**: every chord is a kid of some root side. -/
theorem pkG_par_ex {N : ℕ} (_hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)} (hD : D ∈ pkGDis N)
    {R : ℕ × ℕ} (hR : R ∈ D) : ∃ h ∈ pkGRoots N D, R ∈ pkGKids D h := by
  have cR := pkG_chord hD hR
  have hmem : (1, N) ∈ (pkGRoots N D).filter (fun r => R ≠ r ∧ r.1 ≤ R.1 ∧ R.2 ≤ r.2) := by
    refine mem_filter.2 ⟨mem_insert_self _ _, pkG_ne_of (by dsimp only; omega),
        by dsimp only; omega, by dsimp only; omega⟩
  obtain ⟨h, hh, hmin⟩ := exists_min_image _ (fun r : ℕ × ℕ => r.2 - r.1) ⟨_, hmem⟩
  obtain ⟨hh1, hh2⟩ := mem_filter.1 hh
  refine ⟨h, hh1, pkG_mem_kids.2 ⟨hR, hh2, fun R' hR' hR'h hRR' => ?_⟩⟩
  have hm := hmin R' (mem_filter.2 ⟨mem_insert_of_mem hR', hRR'⟩)
  have cR' := pkG_chord hD hR'
  obtain ⟨n1, a1, b1⟩ := hR'h
  have hnn : ¬ (R'.1 = h.1 ∧ R'.2 = h.2) := fun ⟨u, v⟩ => n1 (pkG_eq_of u v)
  omega

/-- **Parent of a chord, uniqueness**: a chord is a kid of at most one root side. -/
theorem pkG_par_uniq {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)} (hD : D ∈ pkGDis N)
    {R h h' : ℕ × ℕ} (hh : h ∈ pkGRoots N D) (hh' : h' ∈ pkGRoots N D) (k : R ∈ pkGKids D h)
    (k' : R ∈ pkGKids D h') : h = h' := by
  by_contra hne
  obtain ⟨hRD, ⟨n1, a1, b1⟩, -⟩ := pkG_mem_kids.1 k
  obtain ⟨-, ⟨n2, a2, b2⟩, -⟩ := pkG_mem_kids.1 k'
  have cR := pkG_chord hD hRD
  have ch := pkG_root hN hE hD hh
  have ch' := pkG_root hN hE hD hh'
  have hl := pkG_lam (pkG_root_nc hN hE hD hh hh')
  have hnn : ¬ (h.1 = h'.1 ∧ h.2 = h'.2) := fun ⟨u, v⟩ => hne (pkG_eq_of u v)
  rcases hl with hl | hl | hl | hl
  · -- h ⊆ h' strictly: h ∈ D
    rcases mem_insert.1 hh with e | e
    · have e1 : h.1 = 1 := by rw [e]
      have e2 : h.2 = N := by rw [e]
      omega
    · exact pkG_kid_max k' e ⟨hne, hl.1, hl.2⟩ ⟨n1, a1, b1⟩
  · rcases mem_insert.1 hh' with e | e
    · have e1 : h'.1 = 1 := by rw [e]
      have e2 : h'.2 = N := by rw [e]
      omega
    · exact pkG_kid_max k e ⟨fun q => hne q.symm, hl.1, hl.2⟩ ⟨n2, a2, b2⟩
  · omega
  · omega

/-- **Block partition, disjointness**: distinct kids of a face have disjoint blocks. -/
theorem pkG_kids_disj {N : ℕ} {D : Finset (ℕ × ℕ)} (hD : D ∈ pkGDis N) {r R R' : ℕ × ℕ}
    (hR : R ∈ pkGKids D r) (hR' : R' ∈ pkGKids D r) (hne : R ≠ R') : R.2 ≤ R'.1 ∨ R'.2 ≤ R.1 := by
  obtain ⟨hRD, hRr, -⟩ := pkG_mem_kids.1 hR
  obtain ⟨hR'D, hR'r, -⟩ := pkG_mem_kids.1 hR'
  rcases pkG_lam ((pkG_mem_dis.1 hD).2 R hRD R' hR'D) with hl | hl | hl | hl
  · exact (pkG_kid_max hR hR'D hR'r ⟨hne, hl.1, hl.2⟩).elim
  · exact (pkG_kid_max hR' hRD hRr ⟨fun q => hne q.symm, hl.1, hl.2⟩).elim
  · exact Or.inl hl
  · exact Or.inr hl

/-- Kid blocks lie in the face's block. -/
theorem pkG_kid_in {D : Finset (ℕ × ℕ)} {r R : ℕ × ℕ} (hR : R ∈ pkGKids D r) :
    R ∈ D ∧ R ≠ r ∧ r.1 ≤ R.1 ∧ R.2 ≤ r.2 :=
  ⟨(pkG_mem_kids.1 hR).1, (pkG_mem_kids.1 hR).2.1⟩

/-- A kid's left end is a vertex of the face. -/
theorem pkG_kid_vert {N : ℕ} {D : Finset (ℕ × ℕ)} (hD : D ∈ pkGDis N) {r R : ℕ × ℕ}
    (hR : R ∈ pkGKids D r) :
    R.1 ∈ pkGVerts D r := by
  obtain ⟨hRD, -, a, b⟩ := pkG_kid_in hR
  have cR := pkG_chord hD hRD
  refine pkG_mem_verts.2 ⟨a, by omega, fun R'' hR'' hc => ?_⟩
  by_cases e : R = R''
  · subst e
    omega
  · have := pkG_kids_disj hD hR hR'' e
    omega

/-- **Governing vertex in a kid block**: a leg in the block `[R.1, R.2)` of a kid `R` has governing
vertex `R.1`. -/
theorem pkG_gov_kid {N : ℕ} {D : Finset (ℕ × ℕ)} (hD : D ∈ pkGDis N) {r R : ℕ × ℕ}
    (hR : R ∈ pkGKids D r)
    {x : ℕ} (h1 : R.1 ≤ x) (h2 : x < R.2) : pkGGov D r x = R.1 := by
  have hv := pkG_kid_vert hD hR
  apply le_antisymm
  · refine Finset.sup_le (fun w hw => ?_)
    obtain ⟨hwv, hwx⟩ := mem_filter.1 hw
    have := (pkG_mem_verts.1 hwv).2.2 R hR
    omega
  · exact le_sup (f := fun w => w) (mem_filter.2 ⟨hv, h1⟩)

/-- **Governing vertex of an own leg**: a leg of `[r.1, r.2]` in no kid block is its own governing
vertex. -/
theorem pkG_gov_own {D : Finset (ℕ × ℕ)} {r : ℕ × ℕ} {x : ℕ} (h1 : r.1 ≤ x) (h2 : x ≤ r.2)
    (hown : ∀ R ∈ pkGKids D r, ¬ (R.1 ≤ x ∧ x < R.2)) : pkGGov D r x = x := by
  have hv : x ∈ pkGVerts D r :=
    pkG_mem_verts.2 ⟨h1, h2, fun R hR hc => hown R hR ⟨by omega, hc.2⟩⟩
  apply le_antisymm
  · refine Finset.sup_le (fun w hw => ?_)
    exact (mem_filter.1 hw).2
  · exact le_sup (f := fun w => w) (mem_filter.2 ⟨hv, le_refl x⟩)

/-- **Class on a kid block**: all-or-nothing, by the parity of the kid's start. -/
theorem pkG_U_kid {N : ℕ} {D : Finset (ℕ × ℕ)} (hD : D ∈ pkGDis N) {r R : ℕ × ℕ}
    (hR : R ∈ pkGKids D r)
    {x : ℕ} (h1 : R.1 ≤ x) (h2 : x < R.2) : x ∈ pkGU D r ↔ (R.1 + r.1) % 2 = 0 := by
  obtain ⟨-, -, a, b⟩ := pkG_kid_in hR
  rw [pkG_mem_U, pkG_gov_kid hD hR h1 h2]
  constructor
  · intro h
    exact h.2.2
  · intro h
    exact ⟨by omega, by omega, h⟩

/-- **Class on own legs**: by the parity of the leg. -/
theorem pkG_U_own {D : Finset (ℕ × ℕ)} {r : ℕ × ℕ} {x : ℕ} (h1 : r.1 ≤ x) (h2 : x < r.2)
    (hown : ∀ R ∈ pkGKids D r, ¬ (R.1 ≤ x ∧ x < R.2)) : x ∈ pkGU D r ↔ (x + r.1) % 2 = 0 := by
  rw [pkG_mem_U, pkG_gov_own h1 (by omega) hown]
  constructor
  · intro h
    exact h.2.2
  · intro h
    exact ⟨h1, h2, h⟩

/-- The class lies in the face's block. -/
theorem pkG_U_sub {D : Finset (ℕ × ℕ)} {r : ℕ × ℕ} {x : ℕ} (h : x ∈ pkGU D r) :
    r.1 ≤ x ∧ x < r.2 :=
  ⟨(pkG_mem_U.1 h).1, (pkG_mem_U.1 h).2.1⟩

/-- Degree of `v` in the forest `B` with children function `ch`: `[v ∈ B] + #{c ∈ B : c ∈ ch v}`. -/
def pkGDeg {α : Type*} [DecidableEq α] (ch : α → Finset α) (B : Finset α) (v : α) : ℕ :=
  (if v ∈ B then 1 else 0) + (B.filter (fun c => c ∈ ch v)).card

theorem pkG_deg_eq {α : Type*} [DecidableEq α] (ch : α → Finset α) (B : Finset α) (v : α) :
    pkGDeg ch B v = (if v ∈ B then 1 else 0) + (B.filter (fun c => c ∈ ch v)).card := rfl

/-- **Tree lemma**: a children function with at most one parent per node inside `V` and a strictly
decreasing potential; `z B + |B| ≥ |V| + [B ≠ ∅]` for every `B ⊆ V`, where `z B` counts the nodes of
degree `≤ 1`. -/
theorem pkG_tree {α : Type*} [DecidableEq α] (ch : α → Finset α) (φ : α → ℕ) (V : Finset α)
    (hpar : ∀ c v w, v ∈ V → w ∈ V → c ∈ ch v → c ∈ ch w → v = w) :
    ∀ n : ℕ, ∀ B : Finset α, B.card = n → B ⊆ V → (∀ c ∈ B, ∀ v, c ∈ ch v → φ c < φ v) →
      V.card + (if B.Nonempty then 1 else 0) ≤
          (V.filter (fun v => pkGDeg ch B v ≤ 1)).card + B.card := by
  intro n
  induction n with
  | zero =>
    intro B hB _ _
    have hB0 : B = ∅ := card_eq_zero.1 hB
    subst hB0
    have e : V.filter (fun v => pkGDeg ch ∅ v ≤ 1) = V :=
      filter_true_of_mem (fun v _ => by rw [pkG_deg_eq]; simp)
    rw [e]
    simp
  | succ n ih =>
    intro B hB hBV hφ
    have hne : B.Nonempty := card_pos.1 (by omega)
    obtain ⟨b, hb, hbmin⟩ := exists_min_image B φ hne
    have hcard := card_erase_of_mem hb
    -- b has no children in B
    have hbch : (B.filter (fun c => c ∈ ch b)).card = 0 := by
      rw [card_eq_zero, filter_eq_empty_iff]
      intro c hc hcb
      have h1 := hφ c hc b hcb
      have h2 := hbmin c hc
      omega
    have hdegb : pkGDeg ch B b ≤ 1 := by
      rw [pkG_deg_eq, hbch, ite_eq_left hb]
    -- away from b and its parents the degree does not change
    have hsame : ∀ v, v ≠ b → b ∉ ch v → pkGDeg ch B v = pkGDeg ch (B.erase b) v := by
      intro v hvb hbv
      have e1 : (B.erase b).filter (fun c => c ∈ ch v) = B.filter (fun c => c ∈ ch v) := by
        ext c
        simp only [mem_filter, mem_erase]
        constructor
        · rintro ⟨⟨-, h1⟩, h2⟩
          exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩
          refine ⟨⟨fun h => ?_, h1⟩, h2⟩
          subst h
          exact hbv h2
      have e2 : (v ∈ B.erase b) ↔ v ∈ B := by
        rw [mem_erase]
        exact ⟨fun h => h.2, fun h => ⟨hvb, h⟩⟩
      rw [pkG_deg_eq, pkG_deg_eq, e1]
      by_cases hv : v ∈ B
      · rw [ite_eq_left hv, ite_eq_left (e2.2 hv)]
      · rw [ite_eq_right hv, ite_eq_right (fun h => hv (e2.1 h))]
    have hc1 : (V.filter (fun v => b ∈ ch v)).card ≤ 1 :=
      card_le_one.2 (fun v hv w hw =>
          hpar b v w (mem_filter.1 hv).1 (mem_filter.1 hw).1 (mem_filter.1 hv).2
          (mem_filter.1 hw).2)
    by_cases hE : (B.erase b).Nonempty
    · have hih := ih (B.erase b) (by omega) (subset_trans (erase_subset _ _) hBV)
        (fun c hc => hφ c (mem_of_mem_erase hc))
      rw [ite_eq_left hE] at hih
      rw [ite_eq_left hne]
      have key : V.filter (fun v => pkGDeg ch (B.erase b) v ≤ 1) ⊆
          V.filter (fun v => pkGDeg ch B v ≤ 1) ∪ V.filter (fun v => b ∈ ch v) := by
        intro v hv
        obtain ⟨hvV, hvd⟩ := mem_filter.1 hv
        by_cases h1 : b ∈ ch v
        · exact mem_union_right _ (mem_filter.2 ⟨hvV, h1⟩)
        · by_cases h2 : v = b
          · subst h2
            exact mem_union_left _ (mem_filter.2 ⟨hvV, hdegb⟩)
          · refine mem_union_left _ (mem_filter.2 ⟨hvV, ?_⟩)
            rw [hsame v h2 h1]
            exact hvd
      have k1 := card_le_card key
      have k2 := card_union_le (V.filter (fun v => pkGDeg ch B v ≤ 1))
          (V.filter (fun v => b ∈ ch v))
      have k3 := card_pos.2 hne
      omega
    · have hB1 : (B.erase b).card = 0 := card_eq_zero.2 (not_nonempty_iff_eq_empty.1 hE)
      have e : V.filter (fun v => pkGDeg ch B v ≤ 1) = V := by
        refine filter_true_of_mem (fun v _ => ?_)
        by_cases h2 : v = b
        · subst h2
          exact hdegb
        · have hvB : v ∉ B := fun h => by
            have : v ∈ B.erase b := mem_erase.2 ⟨h2, h⟩
            rw [card_eq_zero] at hB1
            rw [hB1] at this
            exact absurd this (notMem_empty v)
          rw [pkG_deg_eq, ite_eq_right hvB]
          have := card_filter_le B (fun c => c ∈ ch v)
          omega
      rw [ite_eq_left hne, e]
      omega

/-- The children function of a dissection's faces. -/
def pkGCh (D : Finset (ℕ × ℕ)) : ℕ × ℕ → Finset (ℕ × ℕ) := fun r => pkGKids D r

/-- **Face count**: for `B ⊆ D`, the faces `r` with `[r ∈ B] + #(kids r ∩ B) ≤ 1` number at least
`|D| + 1 + [B ≠ ∅] − |B|`. (The chord sides of face `r` are `kids r` and, if `r ∈ D`, `r` itself.)
-/
theorem pkG_G3 {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)} (hD : D ∈ pkGDis N)
    {B : Finset (ℕ × ℕ)} (hB : B ⊆ D) :
    D.card + 1 + (if B.Nonempty then 1 else 0) ≤
      ((pkGRoots N D).filter (fun r => pkGDeg (pkGCh D) B r ≤ 1)).card + B.card := by
  have h := pkG_tree (pkGCh D) (fun r => r.2 - r.1) (pkGRoots N D)
    (fun c v w hv hw k k' => pkG_par_uniq hN hE hD hv hw k k') B.card B rfl
    (subset_trans hB (subset_insert _ _)) (fun c hc v hcv => ?_)
  · rw [pkG_card_roots hD] at h
    exact h
  · obtain ⟨hcD, hne, a, b⟩ := pkG_kid_in (show c ∈ pkGKids D v from hcv)
    have cc := pkG_chord hD hcD
    have hnn : ¬ (c.1 = v.1 ∧ c.2 = v.2) := fun ⟨u, w⟩ => hne (pkG_eq_of u w)
    change c.2 - c.1 < v.2 - v.1
    omega

/-- **Faces with at most one non-clean chord side**: for a set `P0` of chords (used with the clean
chords `𝒫₀`) with `B := D \ P0 ≠ ∅`, at least `|D ∩ P0| + 2` faces have at most one chord side
outside `P0`. -/
theorem pkG_G3_clean {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)} (hD : D ∈ pkGDis N)
    (P0 : Finset (ℕ × ℕ)) (hB : (D \ P0).Nonempty) :
    (D ∩ P0).card + 2 ≤
        ((pkGRoots N D).filter (fun r => pkGDeg (pkGCh D) (D \ P0) r ≤ 1)).card := by
  have h := pkG_G3 hN hE hD (sdiff_subset : D \ P0 ⊆ D)
  rw [ite_eq_left hB] at h
  have e := card_sdiff_add_card_inter D P0
  omega

/-- **Leaf faces**: every non-empty dissection has at least two faces with at most one chord side.
-/
theorem pkG_G3_leaf {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)} (hD : D ∈ pkGDis N)
    (hne : D.Nonempty) : 2 ≤
        ((pkGRoots N D).filter (fun r => pkGDeg (pkGCh D) D r ≤ 1)).card := by
  have h := pkG_G3 hN hE hD (subset_refl D)
  rw [ite_eq_left hne] at h
  omega

/-! #### Vertex forms, and the identities `pkGA4`, `pkGA5` as statements

The identities are hypotheses of the lemmas that follow; the next section proves them at every
point (`pkG_A4_all`, `pkG_A5_all`). -/

-- registry: T-RQ7Q
/-- `Q_U = Σ_{a < b ∈ U} s_{ab}`, `s = −mesh`. -/
def pkGQ (N : ℕ) (X : ℕ × ℕ → ℚ) (U : Finset ℕ) : ℚ :=
  ∑ p ∈ (U ×ˢ U).filter (fun p => p.1 < p.2), -mesh N X p.1 p.2

/-- Face sign `(−1)^(k/2 − 1)`. -/
def pkGSgn (k : ℕ) : ℚ := (-1) ^ (k / 2 - 1)

/-- The Cayley vertex of the face with root side `r`: the face sign `pkGSgn |verts|` times `Q_U` of
the face's class `U = pkGU D r`. -/
def pkGV (N : ℕ) (X : ℕ × ℕ → ℚ) (D : Finset (ℕ × ℕ)) (r : ℕ × ℕ) : ℚ :=
  pkGSgn (pkGVerts D r).card * pkGQ N X (pkGU D r)

-- registry: T-G353
/-- `E = Σ_{ee pairs} mesh`. -/
def pkGE (N : ℕ) (X : ℕ × ℕ → ℚ) : ℚ :=
  ∑ t ∈ (diagonals N).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0), mesh N X t.1 t.2

/-- `Σee_W`: the sum of the mesh variables over the ee pairs `a < b` inside `W`. -/
def pkGSee (N : ℕ) (X : ℕ × ℕ → ℚ) (W : Finset ℕ) : ℚ :=
  ∑ p ∈ (W ×ˢ W).filter (fun p => p.1 < p.2 ∧ p.1 % 2 = 0 ∧ p.2 % 2 = 0), mesh N X p.1 p.2
/-- `Σoo_W`: the sum of the mesh variables over the oo pairs `a < b` inside `W`. -/
def pkGSoo (N : ℕ) (X : ℕ × ℕ → ℚ) (W : Finset ℕ) : ℚ :=
  ∑ p ∈ (W ×ˢ W).filter (fun p => p.1 < p.2 ∧ p.1 % 2 = 1 ∧ p.2 % 2 = 1), mesh N X p.1 p.2

/-- The mixed cross sum `Σ_{x ∈ evens U, y ∈ odds Uᶜ} mesh(min, max)` of `pkGA5` (`Uᶜ` taken in
`1..N`). -/
def pkGCross (N : ℕ) (X : ℕ × ℕ → ℚ) (U : Finset ℕ) : ℚ :=
  ∑ p ∈ evens U ×ˢ odds (Icc 1 N \ U), mesh N X (min p.1 p.2) (max p.1 p.2)

/-- **Complement symmetry of `Q`** at `X`, as a statement: `Q_U = Q_{Uᶜ}` for every leg set
`U ⊆ 1..N`. -/
def pkGA4 (N : ℕ) (X : ℕ × ℕ → ℚ) : Prop :=
  ∀ U : Finset ℕ, U ⊆ Icc 1 N → pkGQ N X U = pkGQ N X (Icc 1 N \ U)

/-- **The cross-sum identity** at `X`, as a statement: `Q_U = cross(U) + E − Σee_{Uᶜ} − Σoo_U` for
every leg set `U ⊆ 1..N` (total `mesh`). -/
def pkGA5 (N : ℕ) (X : ℕ × ℕ → ℚ) : Prop :=
  ∀ U : Finset ℕ, U ⊆ Icc 1 N →
    pkGQ N X U = pkGCross N X U + pkGE N X - pkGSee N X (Icc 1 N \ U) - pkGSoo N X U

-- registry: C-J1M2
/-- The same-parity pairs. -/
def pkGSame (N : ℕ) : Finset (ℕ × ℕ) := (diagonals N).filter (fun t => t.1 % 2 = t.2 % 2)

/-- A chord side of the face with root side `r`: a kid, or `r` itself when `r` is a chord. -/
def pkGSide (D : Finset (ℕ × ℕ)) (r R : ℕ × ℕ) : Prop := R ∈ pkGKids D r ∨ (R = r ∧ r ∈ D)

theorem pkG_side_iff {D : Finset (ℕ × ℕ)} {r R : ℕ × ℕ} :
    pkGSide D r R ↔ R ∈ pkGKids D r ∨ (R = r ∧ r ∈ D) := Iff.rfl

theorem pkG_mem_oddSide {N : ℕ} {R : ℕ × ℕ} (h1 : 1 ≤ R.1) (h2 : R.2 ≤ N) {x : ℕ} :
    x ∈ oddSide N R ↔ 1 ≤ x ∧ x ≤ N ∧
      ((R.1 % 2 = 1 ∧ R.1 ≤ x ∧ x < R.2) ∨ (R.1 % 2 = 0 ∧ ¬ (R.1 ≤ x ∧ x < R.2))) := by
  have e : oddSide N R = if R.1 % 2 =
      1 then Icc R.1 (R.2 - 1) else Icc 1 N \ Icc R.1 (R.2 - 1) := rfl
  rw [e]
  by_cases h : R.1 % 2 = 1
  · rw [ite_eq_left h]
    simp only [mem_Icc]
    constructor <;> intro h' <;> omega
  · rw [ite_eq_right h]
    simp only [mem_Icc, mem_sdiff]
    constructor <;> intro h' <;> omega

theorem pkG_mem_evenSide {N : ℕ} {R : ℕ × ℕ} (h1 : 1 ≤ R.1) (h2 : R.2 ≤ N) {x : ℕ} :
    x ∈ evenSide N R ↔ 1 ≤ x ∧ x ≤ N ∧
      ((R.1 % 2 = 0 ∧ R.1 ≤ x ∧ x < R.2) ∨ (R.1 % 2 = 1 ∧ ¬ (R.1 ≤ x ∧ x < R.2))) := by
  have e : evenSide N R = Icc 1 N \ oddSide N R := rfl
  rw [e, mem_sdiff, pkG_mem_oddSide h1 h2, mem_Icc]
  constructor <;> intro h' <;> omega

theorem pkG_mem_minRect_of {N : ℕ} {R : ℕ × ℕ} {x y : ℕ} (hx : x ∈ oddSide N R) (hxe : x % 2 = 0)
    (hy : y ∈ evenSide N R) (hyo : y % 2 = 1) : (min x y, max x y) ∈ minRect N R := by
  change (min x y, max x y) ∈ (evens (oddSide N R) ×ˢ odds (evenSide N R)).image (fun q =>
      (min q.1 q.2, max q.1 q.2))
  exact mem_image.2 ⟨(x, y), mem_product.2 ⟨mem_filter.2 ⟨hx, hxe⟩, mem_filter.2 ⟨hy, hyo⟩⟩, rfl⟩

/-- `minRect` pairs of an odd chord are diagonals. -/
theorem pkG_minRect_diag {N : ℕ} {R : ℕ × ℕ} (hR : R ∈ oddDiagonals N) {p : ℕ × ℕ}
    (hp : p ∈ minRect N R) :
    p ∈ diagonals N := by
  have hR2 := mem_filter.1 hR
  obtain ⟨a, b, c, d⟩ := mem_diagonals.1 hR2.1
  have hodd := hR2.2
  have e : minRect N R =
      (evens (oddSide N R) ×ˢ odds (evenSide N R)).image (fun q => (min q.1 q.2, max q.1 q.2)) :=
    rfl
  rw [e] at hp
  obtain ⟨⟨x, y⟩, hq, rfl⟩ := mem_image.1 hp
  obtain ⟨hx, hy⟩ := mem_product.1 hq
  obtain ⟨hx1, hx2⟩ := mem_filter.1 hx
  obtain ⟨hy1, hy2⟩ := mem_filter.1 hy
  have hx3 := (pkG_mem_oddSide a b).1 hx1
  have hy3 := (pkG_mem_evenSide a b).1 hy1
  refine mem_diagonals.2 ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only <;> omega

/-- **Even legs of the odd-start class**: an even leg of the odd-start class lies in the head of an
out-chord side. -/
theorem pkG_xside {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)}
    (hD : D ∈ pkGDis N) {r : ℕ × ℕ} (hr : r ∈ pkGRoots N D) {x : ℕ} (_hx1 : 1 ≤ x) (_hxN : x ≤ N)
    (hxe : x % 2 = 0) (hW : x ∈ pkGU D r ↔ r.1 % 2 = 1) :
    (∃ K ∈ pkGKids D r, K.1 % 2 = 1 ∧ K.1 ≤ x ∧ x < K.2) ∨
        (r ∈ D ∧ r.1 % 2 = 0 ∧ ¬ (r.1 ≤ x ∧ x < r.2)) := by
  have cr := pkG_root hN hE hD hr
  by_cases hin : r.1 ≤ x ∧ x < r.2
  · left
    by_cases hk : ∃ K ∈ pkGKids D r, K.1 ≤ x ∧ x < K.2
    · obtain ⟨K, hK, k1, k2⟩ := hk
      have := pkG_U_kid hD hK k1 k2
      refine ⟨K, hK, ?_, k1, k2⟩
      by_cases h : r.1 % 2 = 1
      · have := this.1 (hW.2 h)
        omega
      · have h' : x ∉ pkGU D r := fun q => h (hW.1 q)
        rw [this] at h'
        omega
    · have hown : ∀ R ∈ pkGKids D r, ¬ (R.1 ≤ x ∧ x < R.2) := fun R hR q => hk ⟨R, hR, q⟩
      have := pkG_U_own hin.1 hin.2 hown
      exfalso
      by_cases h : r.1 % 2 = 1
      · have := this.1 (hW.2 h)
        omega
      · have h' : x ∉ pkGU D r := fun q => h (hW.1 q)
        rw [this] at h'
        omega
  · right
    by_cases h : r.1 % 2 = 1
    · exact absurd (pkG_U_sub (hW.2 h)) hin
    · rcases mem_insert.1 hr with e | e
      · exfalso
        have e1 : r.1 = 1 := by rw [e]
        omega
      · exact ⟨e, by omega, hin⟩

/-- **Odd legs outside the odd-start class**: an odd leg outside the odd-start class lies in the
tail of an in-chord side. -/
theorem pkG_yside {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)}
    (hD : D ∈ pkGDis N) {r : ℕ × ℕ} (hr : r ∈ pkGRoots N D) {y : ℕ} (hy1 : 1 ≤ y) (hyN : y ≤ N)
    (hyo : y % 2 = 1) (hW : y ∈ pkGU D r ↔ r.1 % 2 = 0) :
    (∃ K ∈ pkGKids D r, K.1 % 2 = 0 ∧ K.1 ≤ y ∧ y < K.2) ∨
        (r ∈ D ∧ r.1 % 2 = 1 ∧ ¬ (r.1 ≤ y ∧ y < r.2)) := by
  have cr := pkG_root hN hE hD hr
  by_cases hin : r.1 ≤ y ∧ y < r.2
  · left
    by_cases hk : ∃ K ∈ pkGKids D r, K.1 ≤ y ∧ y < K.2
    · obtain ⟨K, hK, k1, k2⟩ := hk
      have := pkG_U_kid hD hK k1 k2
      refine ⟨K, hK, ?_, k1, k2⟩
      by_cases h : r.1 % 2 = 0
      · have := this.1 (hW.2 h)
        omega
      · have h' : y ∉ pkGU D r := fun q => h (hW.1 q)
        rw [this] at h'
        omega
    · have hown : ∀ R ∈ pkGKids D r, ¬ (R.1 ≤ y ∧ y < R.2) := fun R hR q => hk ⟨R, hR, q⟩
      have := pkG_U_own hin.1 hin.2 hown
      exfalso
      by_cases h : r.1 % 2 = 0
      · have := this.1 (hW.2 h)
        omega
      · have h' : y ∉ pkGU D r := fun q => h (hW.1 q)
        rw [this] at h'
        omega
  · right
    by_cases h : r.1 % 2 = 0
    · exact absurd (pkG_U_sub (hW.2 h)) hin
    · rcases mem_insert.1 hr with e | e
      · exfalso
        have e1 : r.1 = 1 := by rw [e]
        have e2 : r.2 = N := by rw [e]
        omega
      · exact ⟨e, by omega, hin⟩

/-- The odd-start class `U_f` of the face `r`: `U'` if `r.1` is odd, else its complement in `1..N`.
-/
def pkGW (N : ℕ) (D : Finset (ℕ × ℕ)) (r : ℕ × ℕ) : Finset ℕ :=
  if r.1 % 2 = 1 then pkGU D r else Icc 1 N \ pkGU D r

theorem pkG_U_Icc {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)}
    (hD : D ∈ pkGDis N) {r : ℕ × ℕ}
    (hr : r ∈ pkGRoots N D) : pkGU D r ⊆ Icc 1 N := by
  intro x hx
  have := pkG_U_sub hx
  have := pkG_root hN hE hD hr
  exact mem_Icc.2 ⟨by omega, by omega⟩

theorem pkG_W_Icc {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)}
    (hD : D ∈ pkGDis N) {r : ℕ × ℕ}
    (hr : r ∈ pkGRoots N D) : pkGW N D r ⊆ Icc 1 N := by
  have e : pkGW N D r = if r.1 % 2 = 1 then pkGU D r else Icc 1 N \ pkGU D r := rfl
  rw [e]
  by_cases h : r.1 % 2 = 1
  · rw [ite_eq_left h]
    exact pkG_U_Icc hN hE hD hr
  · rw [ite_eq_right h]
    exact sdiff_subset

/-- `x ∈ U_f ↔ (x ∈ U' ↔ r.1 odd)` on legs `1..N`. -/
theorem pkG_mem_W {N : ℕ} {D : Finset (ℕ × ℕ)} {r : ℕ × ℕ} {x : ℕ} (hx : x ∈ Icc 1 N) :
    x ∈ pkGW N D r ↔ (x ∈ pkGU D r ↔ r.1 % 2 = 1) := by
  have e : pkGW N D r = if r.1 % 2 = 1 then pkGU D r else Icc 1 N \ pkGU D r := rfl
  rw [e]
  by_cases h : r.1 % 2 = 1
  · rw [ite_eq_left h]
    exact ⟨fun q => ⟨fun _ => h, fun _ => q⟩, fun q => q.2 h⟩
  · rw [ite_eq_right h, mem_sdiff]
    exact ⟨fun q => ⟨fun q' => (q.2 q').elim, fun q' => (h q').elim⟩, fun q =>
        ⟨hx, fun q' => h (q.1 q')⟩⟩

/-- **Pairing**: every pair of the cross sum of `U_f` lies in the `minRect` of two distinct chord
sides of the face (an out-chord and an in-chord). -/
theorem pkG_pair {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)}
    (hD : D ∈ pkGDis N) {r : ℕ × ℕ} (hr : r ∈ pkGRoots N D) {x y : ℕ} (hx : x ∈ pkGW N D r)
    (hxe : x % 2 = 0) (hy : y ∈ Icc 1 N) (hy' : y ∉ pkGW N D r) (hyo : y % 2 = 1) :
    ∃ R R', pkGSide D r R ∧ pkGSide D r R' ∧ R ≠ R' ∧ (min x y, max x y) ∈ minRect N R ∧
      (min x y, max x y) ∈ minRect N R' := by
  have hxI := pkG_W_Icc hN hE hD hr hx
  have hWx := (pkG_mem_W hxI).1 hx
  have hWy : y ∈ pkGU D r ↔ r.1 % 2 = 0 := by
    have q := fun h => hy' ((pkG_mem_W hy).2 h)
    constructor
    · intro h
      by_contra h'
      exact q ⟨fun _ => by omega, fun _ => h⟩
    · intro h
      by_contra h'
      exact q ⟨fun q' => (h' q').elim, fun q' => absurd h (by omega)⟩
  obtain ⟨hx1, hxN⟩ := mem_Icc.1 hxI
  obtain ⟨hy1, hyN⟩ := mem_Icc.1 hy
  have cr := pkG_root hN hE hD hr
  rcases pkG_xside hN hE hD hr hx1 hxN hxe hWx with ⟨K, hK, k0, k1, k2⟩ | ⟨hrD, r0, rx⟩ <;>
    rcases pkG_yside hN hE hD hr hy1 hyN hyo hWy with ⟨K', hK', k0', k1', k2'⟩ | ⟨hrD', r0', ry⟩
  · -- kid K (odd start) and kid K' (even start)
    have hne : K ≠ K' := fun e => by rw [e] at k0; omega
    have hdisj := pkG_kids_disj hD hK hK' hne
    obtain ⟨hKD, -, -, -⟩ := pkG_kid_in hK
    obtain ⟨hK'D, -, -, -⟩ := pkG_kid_in hK'
    have c := pkG_chord hD hKD
    have c' := pkG_chord hD hK'D
    refine ⟨K, K', Or.inl hK, Or.inl hK', hne, pkG_mem_minRect_of ?_ hxe ?_ hyo,
      pkG_mem_minRect_of ?_ hxe ?_ hyo⟩
    · exact (pkG_mem_oddSide c.1 c.2.1).2 ⟨hx1, hxN, by omega⟩
    · exact (pkG_mem_evenSide c.1 c.2.1).2 ⟨hy1, hyN, by omega⟩
    · exact (pkG_mem_oddSide c'.1 c'.2.1).2 ⟨hx1, hxN, by omega⟩
    · exact (pkG_mem_evenSide c'.1 c'.2.1).2 ⟨hy1, hyN, by omega⟩
  · -- kid K (odd start) and the root side r (odd start, in-chord)
    obtain ⟨hKD, hKr, a, b⟩ := pkG_kid_in hK
    have c := pkG_chord hD hKD
    have c' := pkG_chord hD hrD'
    refine ⟨K, r, Or.inl hK, Or.inr ⟨rfl, hrD'⟩, hKr, pkG_mem_minRect_of ?_ hxe ?_ hyo,
      pkG_mem_minRect_of ?_ hxe ?_ hyo⟩
    · exact (pkG_mem_oddSide c.1 c.2.1).2 ⟨hx1, hxN, by omega⟩
    · exact (pkG_mem_evenSide c.1 c.2.1).2 ⟨hy1, hyN, by omega⟩
    · exact (pkG_mem_oddSide c'.1 c'.2.1).2 ⟨hx1, hxN, by omega⟩
    · exact (pkG_mem_evenSide c'.1 c'.2.1).2 ⟨hy1, hyN, by omega⟩
  · -- the root side r (even start, out-chord) and kid K' (even start)
    obtain ⟨hK'D, hK'r, a, b⟩ := pkG_kid_in hK'
    have c := pkG_chord hD hrD
    have c' := pkG_chord hD hK'D
    refine ⟨r, K', Or.inr ⟨rfl, hrD⟩, Or.inl hK', fun e => hK'r e.symm,
        pkG_mem_minRect_of ?_ hxe ?_ hyo,
        pkG_mem_minRect_of ?_ hxe ?_ hyo⟩
    · exact (pkG_mem_oddSide c.1 c.2.1).2 ⟨hx1, hxN, by omega⟩
    · exact (pkG_mem_evenSide c.1 c.2.1).2 ⟨hy1, hyN, by omega⟩
    · exact (pkG_mem_oddSide c'.1 c'.2.1).2 ⟨hx1, hxN, by omega⟩
    · exact (pkG_mem_evenSide c'.1 c'.2.1).2 ⟨hy1, hyN, by omega⟩
  · exfalso
    omega

/-- Two distinct chord sides in `B` give degree `≥ 2`. -/
theorem pkG_deg_two {D B : Finset (ℕ × ℕ)} {r R R' : ℕ × ℕ} (hR : pkGSide D r R)
    (hR' : pkGSide D r R')
    (hne : R ≠ R') (hRB : R ∈ B) (hR'B : R' ∈ B) : 2 ≤ pkGDeg (pkGCh D) B r := by
  rw [pkG_deg_eq]
  rcases hR with k | ⟨e, -⟩ <;> rcases hR' with k' | ⟨e', -⟩
  · have hsub : ({R, R'} : Finset (ℕ × ℕ)) ⊆ B.filter (fun c => c ∈ pkGCh D r) := by
      intro c hc
      rcases mem_insert.1 hc with h | h
      · rw [h]
        exact mem_filter.2 ⟨hRB, k⟩
      · rw [mem_singleton.1 h]
        exact mem_filter.2 ⟨hR'B, k'⟩
    have := card_le_card hsub
    rw [card_pair hne] at this
    omega
  · have h1 : r ∈ B := by rw [← e']; exact hR'B
    have h2 : 0 < (B.filter (fun c => c ∈ pkGCh D r)).card := card_pos.2 ⟨R, mem_filter.2 ⟨hRB, k⟩⟩
    rw [ite_eq_left h1]
    omega
  · have h1 : r ∈ B := by rw [← e]; exact hRB
    have h2 : 0 < (B.filter (fun c => c ∈ pkGCh D r)).card :=
        card_pos.2 ⟨R', mem_filter.2 ⟨hR'B, k'⟩⟩
    rw [ite_eq_left h1]
    omega
  · exact absurd (e.trans e'.symm) hne

theorem pkG_side_mem {D : Finset (ℕ × ℕ)} {r R : ℕ × ℕ} (h : pkGSide D r R) : R ∈ D := by
  rcases h with k | ⟨e, h⟩
  · exact (pkG_kid_in k).1
  · rw [e]
    exact h

/-- **The cross sum vanishes**: at a face with at most one chord side outside `P0`, the cross sum of
`U_f` vanishes at every `X` at which the `minRect` pairs of the chords in `P0` vanish. -/
theorem pkG_cross_zero {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)}
    (hD : D ∈ pkGDis N) {r : ℕ × ℕ} (hr : r ∈ pkGRoots N D) (P0 : Finset (ℕ × ℕ))
    (hdeg : pkGDeg (pkGCh D) (D \ P0) r ≤ 1) (X : ℕ × ℕ → ℚ)
    (hP0 : ∀ R ∈ D, R ∈ P0 → ∀ p ∈ minRect N R, mesh N X p.1 p.2 = 0) :
    pkGCross N X (pkGW N D r) = 0 := by
  refine sum_eq_zero (fun p hp => ?_)
  obtain ⟨hx, hy⟩ := mem_product.1 hp
  obtain ⟨hx1, hx2⟩ := mem_filter.1 hx
  obtain ⟨hy1, hy2⟩ := mem_filter.1 hy
  obtain ⟨hyI, hyW⟩ := mem_sdiff.1 hy1
  obtain ⟨R, R', hR, hR', hne, m, m'⟩ := pkG_pair hN hE hD hr hx1 hx2 hyI hyW hy2
  by_cases h1 : R ∈ P0
  · exact hP0 R (pkG_side_mem hR) h1 (min p.1 p.2, max p.1 p.2) m
  · by_cases h2 : R' ∈ P0
    · exact hP0 R' (pkG_side_mem hR') h2 (min p.1 p.2, max p.1 p.2) m'
    · have := pkG_deg_two hR hR' hne (mem_sdiff.2 ⟨pkG_side_mem hR, h1⟩)
        (mem_sdiff.2 ⟨pkG_side_mem hR', h2⟩)
      omega

/-- On the same-parity locus, `E` vanishes (`pkG_See_zero` and `pkG_Soo_zero` below give the same
for `Σee_W`, `Σoo_W` with `W ⊆ 1..N`, the latter for even `N`). -/
theorem pkG_E_zero {N : ℕ} {X : ℕ × ℕ → ℚ} (hs : ∀ t ∈ pkGSame N, mesh N X t.1 t.2 = 0) :
    pkGE N X = 0 := by
  refine sum_eq_zero (fun t ht => hs t ?_)
  obtain ⟨h1, h2⟩ := mem_filter.1 ht
  exact mem_filter.2 ⟨h1, by omega⟩

theorem pkG_See_zero {N : ℕ} {X : ℕ × ℕ → ℚ} (hs : ∀ t ∈ pkGSame N, mesh N X t.1 t.2 = 0)
    {W : Finset ℕ}
    (hW : W ⊆ Icc 1 N) : pkGSee N X W = 0 := by
  refine sum_eq_zero (fun t ht => hs t ?_)
  obtain ⟨h1, h2⟩ := mem_filter.1 ht
  obtain ⟨a, b⟩ := mem_product.1 h1
  have a' := mem_Icc.1 (hW a)
  have b' := mem_Icc.1 (hW b)
  exact mem_filter.2 ⟨mem_diagonals.2 ⟨by omega, by omega, by omega, by omega⟩, by omega⟩

theorem pkG_Soo_zero {N : ℕ} (hE : N % 2 = 0) {X : ℕ × ℕ → ℚ}
    (hs : ∀ t ∈ pkGSame N, mesh N X t.1 t.2 = 0)
    {W : Finset ℕ} (hW : W ⊆ Icc 1 N) : pkGSoo N X W = 0 := by
  refine sum_eq_zero (fun t ht => hs t ?_)
  obtain ⟨h1, h2⟩ := mem_filter.1 ht
  obtain ⟨a, b⟩ := mem_product.1 h1
  have a' := mem_Icc.1 (hW a)
  have b' := mem_Icc.1 (hW b)
  exact mem_filter.2 ⟨mem_diagonals.2 ⟨by omega, by omega, by omega, by omega⟩, by omega⟩

/-- **Vanishing faces, general form**: given `pkGA4 N X` and `pkGA5 N X` and the same-parity pairs
vanishing at `X`, a face with at most one chord side outside `P0` has `V = 0` whenever the `minRect`
pairs of the chords of `D` in `P0` vanish. -/
theorem pkG_V_zero {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)} (hD : D ∈ pkGDis N)
    {r : ℕ × ℕ} (hr : r ∈ pkGRoots N D) (P0 : Finset (ℕ × ℕ))
    (hdeg : pkGDeg (pkGCh D) (D \ P0) r ≤ 1) (X : ℕ × ℕ → ℚ) (hA4 : pkGA4 N X) (hA5 : pkGA5 N X)
    (hs : ∀ t ∈ pkGSame N, mesh N X t.1 t.2 = 0)
    (hP0 : ∀ R ∈ D, R ∈ P0 → ∀ p ∈ minRect N R, mesh N X p.1 p.2 = 0) : pkGV N X D r = 0 := by
  have hQ : pkGQ N X (pkGU D r) = pkGQ N X (pkGW N D r) := by
    have e : pkGW N D r = if r.1 % 2 = 1 then pkGU D r else Icc 1 N \ pkGU D r := rfl
    rw [e]
    by_cases h : r.1 % 2 = 1
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]
      exact hA4 _ (pkG_U_Icc hN hE hD hr)
  have hWI := pkG_W_Icc hN hE hD hr
  have h5 := hA5 _ hWI
  rw [pkG_cross_zero hN hE hD hr P0 hdeg X hP0, pkG_E_zero hs, pkG_See_zero hs sdiff_subset,
    pkG_Soo_zero hE hs hWI] at h5
  have e : pkGV N X D r = pkGSgn (pkGVerts D r).card * pkGQ N X (pkGU D r) := rfl
  rw [e, hQ, h5]
  ring

/-- `minRect` pairs of a clean chord lie in `S`. -/
theorem pkG_clean_minRect {N : ℕ} {S : Finset (ℕ × ℕ)} {R : ℕ × ℕ}
    (hR : R ∈ cleanChords N S) {p : ℕ × ℕ}
    (hp : p ∈ minRect N R) : p ∈ S := by
  obtain ⟨hRo, hdisj⟩ := mem_filter.1 hR
  have hd := pkG_minRect_diag hRo hp
  by_contra hS
  have hm : p ∈ missing N S := mem_sdiff.2 ⟨hd, hS⟩
  exact disjoint_left.1 hdisj hp hm

/-- **Vanishing faces on the base locus**: on `L_{S ∪ same}`, a face with at most one non-clean
chord side has `V = 0` at every point at which `pkGA4` and `pkGA5` hold. -/
theorem pkG_V_base {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)} (hD : D ∈ pkGDis N)
    {r : ℕ × ℕ} (hr : r ∈ pkGRoots N D) (S : Finset (ℕ × ℕ))
    (hdeg : pkGDeg (pkGCh D) (D \ cleanChords N S) r ≤ 1) (X : ℕ × ℕ → ℚ) (hA4 : pkGA4 N X)
    (hA5 : pkGA5 N X) (hL : OnLocus N (S ∪ pkGSame N) X) : pkGV N X D r = 0 :=
  pkG_V_zero hN hE hD hr _ hdeg X hA4 hA5 (fun t ht => hL t (mem_union_right _ ht))
    (fun _R _ hR p hp => hL p (mem_union_left _ (pkG_clean_minRect hR hp)))

/-- **Leaf lemma**: on `L_same`, a face with at most one chord side has `V = 0` at every point at
which `pkGA4` and `pkGA5` hold. -/
theorem pkG_V_leaf {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)} (hD : D ∈ pkGDis N)
    {r : ℕ × ℕ} (hr : r ∈ pkGRoots N D) (hdeg : pkGDeg (pkGCh D) D r ≤ 1) (X : ℕ × ℕ → ℚ)
    (hA4 : pkGA4 N X) (hA5 : pkGA5 N X)
        (hs : ∀ t ∈ pkGSame N, mesh N X t.1 t.2 = 0) : pkGV N X D r = 0 := by
  refine pkG_V_zero hN hE hD hr ∅ ?_ X hA4 hA5 hs (fun R _ hR => absurd hR (notMem_empty R))
  rw [sdiff_empty]
  exact hdeg

/-- `Q_U = 0` on `L_S` when `U` holds only odd legs of the head of `P` and `o_in(P) = ∅`. -/
theorem pkG_Q_zero_oo {N : ℕ} (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ} (hP1 : 1 ≤ P.1)
    (hP2 : P.2 ≤ N) (hin : innerOO N S P = ∅) {U : Finset ℕ}
    (hU : ∀ x ∈ U, x % 2 = 1 ∧ x ∈ oddSide N P) {X : ℕ × ℕ → ℚ}
    (hL : OnLocus N S X) : pkGQ N X U = 0 := by
  refine sum_eq_zero (fun p hp => ?_)
  obtain ⟨h1, h2⟩ := mem_filter.1 hp
  obtain ⟨a, b⟩ := mem_product.1 h1
  obtain ⟨ao, aP⟩ := hU _ a
  obtain ⟨bo, bP⟩ := hU _ b
  have aP' := (pkG_mem_oddSide hP1 hP2).1 aP
  have bP' := (pkG_mem_oddSide hP1 hP2).1 bP
  have hd : p ∈ diagonals N := mem_diagonals.2 ⟨by omega, by omega, by omega, by omega⟩
  have hpS : p ∈ S := by
    by_contra hS
    have hm : p ∈ innerOO N S P :=
        mem_filter.2 ⟨mem_filter.2 ⟨mem_sdiff.2 ⟨hd, hS⟩, ao, bo⟩, aP, bP⟩
    rw [hin] at hm
    exact notMem_empty p hm
  rw [hL p hpS, neg_zero]

/-- `Q_U = 0` on `L_S` when `U` holds only even legs of the tail of `P` and `e_in(P) = ∅`. -/
theorem pkG_Q_zero_ee {N : ℕ} {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ} (hP1 : 1 ≤ P.1) (hP2 : P.2 ≤ N)
    (hin : innerEE N S P = ∅) {U : Finset ℕ} (hU : ∀ x ∈ U, x % 2 = 0 ∧ x ∈ evenSide N P)
    {X : ℕ × ℕ → ℚ}
    (hL : OnLocus N S X) : pkGQ N X U = 0 := by
  refine sum_eq_zero (fun p hp => ?_)
  obtain ⟨h1, h2⟩ := mem_filter.1 hp
  obtain ⟨a, b⟩ := mem_product.1 h1
  obtain ⟨ao, aP⟩ := hU _ a
  obtain ⟨bo, bP⟩ := hU _ b
  have aP' := (pkG_mem_evenSide hP1 hP2).1 aP
  have bP' := (pkG_mem_evenSide hP1 hP2).1 bP
  have hd : p ∈ diagonals N := mem_diagonals.2 ⟨by omega, by omega, by omega, by omega⟩
  have hpS : p ∈ S := by
    by_contra hS
    have hm : p ∈ innerEE N S P :=
        mem_filter.2 ⟨mem_filter.2 ⟨mem_sdiff.2 ⟨hd, hS⟩, ao, bo⟩, aP, bP⟩
    rw [hin] at hm
    exact notMem_empty p hm
  rw [hL p hpS, neg_zero]

/-- **A face that vanishes, head case**: `o_in(P) = ∅` for a chord `P ∈ D` ⇒ some face has `V = 0`
at every point of `L_S` (a sink face, by head-minimality). -/
theorem pkG_G4_o {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)} (hD : D ∈ pkGDis N)
    {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ} (hPD : P ∈ D) (hin : innerOO N S P = ∅) :
    ∃ r ∈ pkGRoots N D, ∀ X : ℕ × ℕ → ℚ, OnLocus N S X → pkGV N X D r = 0 := by
  obtain ⟨R, hRm, hmin⟩ := exists_min_image (D.filter (fun R => oddSide N R ⊆ oddSide N P))
    (fun R => (oddSide N R).card) ⟨P, mem_filter.2 ⟨hPD, subset_refl _⟩⟩
  obtain ⟨hRD, hRP⟩ := mem_filter.1 hRm
  have cR := pkG_chord hD hRD
  have cP := pkG_chord hD hPD
  have hmin' : ∀ K ∈ D, oddSide N K ⊆ oddSide N R → ∀ w ∈ oddSide N R, w ∉ oddSide N K → False := by
    intro K hK hsub w hw hw'
    have h1 := hmin K (mem_filter.2 ⟨hK, subset_trans hsub hRP⟩)
    have h2 := card_lt_card ((ssubset_iff_of_subset hsub).2 ⟨w, hw, hw'⟩)
    omega
  have key : ∃ h ∈ pkGRoots N D, ∀ x ∈ pkGU D h, x % 2 = 1 ∧ x ∈ oddSide N R := by
    by_cases hR1 : R.1 % 2 = 1
    · refine ⟨R, mem_insert_of_mem hRD, fun x hx => ?_⟩
      obtain ⟨x1, x2⟩ := pkG_U_sub hx
      by_cases hk : ∃ K ∈ pkGKids D R, K.1 ≤ x ∧ x < K.2
      · exfalso
        obtain ⟨K, hK, k1, k2⟩ := hk
        have hKp := (pkG_U_kid hD hK k1 k2).1 hx
        obtain ⟨hKD, hKR, a, b⟩ := pkG_kid_in hK
        have cK := pkG_chord hD hKD
        have hnn : ¬ (K.1 = R.1 ∧ K.2 = R.2) := fun ⟨u, v⟩ => hKR (pkG_eq_of u v)
        refine hmin' K hKD ?_ (if R.1 < K.1 then R.1 else R.2 - 1) ?_ ?_
        · intro z hz
          rw [pkG_mem_oddSide cK.1 cK.2.1] at hz
          rw [pkG_mem_oddSide cR.1 cR.2.1]
          omega
        · rw [pkG_mem_oddSide cR.1 cR.2.1]
          split_ifs <;> omega
        · rw [pkG_mem_oddSide cK.1 cK.2.1]
          split_ifs <;> omega
      · have hown : ∀ K ∈ pkGKids D R, ¬ (K.1 ≤ x ∧ x < K.2) := fun K hK q => hk ⟨K, hK, q⟩
        have := (pkG_U_own x1 x2 hown).1 hx
        refine ⟨by omega, ?_⟩
        rw [pkG_mem_oddSide cR.1 cR.2.1]
        omega
    · obtain ⟨h, hh, hRh⟩ := pkG_par_ex hN hE hD hRD
      obtain ⟨-, hRne, a, b⟩ := pkG_kid_in hRh
      have ch := pkG_root hN hE hD hh
      have hh1 : h.1 % 2 = 1 := by
        by_contra hh1
        rcases mem_insert.1 hh with e | e
        · have e1 : h.1 = 1 := by rw [e]
          omega
        · have hnn : ¬ (R.1 = h.1 ∧ R.2 = h.2) := fun ⟨u, v⟩ => hRne (pkG_eq_of u v)
          have cH := pkG_chord hD e
          refine hmin' h e ?_ (if h.1 < R.1 then h.1 else h.2 - 1) ?_ ?_
          · intro z hz
            rw [pkG_mem_oddSide cH.1 cH.2.1] at hz
            rw [pkG_mem_oddSide cR.1 cR.2.1]
            omega
          · rw [pkG_mem_oddSide cR.1 cR.2.1]
            split_ifs <;> omega
          · rw [pkG_mem_oddSide cH.1 cH.2.1]
            split_ifs <;> omega
      refine ⟨h, hh, fun x hx => ?_⟩
      obtain ⟨x1, x2⟩ := pkG_U_sub hx
      by_cases hk : ∃ K ∈ pkGKids D h, K.1 ≤ x ∧ x < K.2
      · exfalso
        obtain ⟨K, hK, k1, k2⟩ := hk
        have hKp := (pkG_U_kid hD hK k1 k2).1 hx
        have hKR : K ≠ R := fun e => by
          rw [e] at hKp
          omega
        have hdisj := pkG_kids_disj hD hK hRh hKR
        obtain ⟨hKD, -, -, -⟩ := pkG_kid_in hK
        have cK := pkG_chord hD hKD
        refine hmin' K hKD ?_ N ?_ ?_
        · intro z hz
          rw [pkG_mem_oddSide cK.1 cK.2.1] at hz
          rw [pkG_mem_oddSide cR.1 cR.2.1]
          omega
        · rw [pkG_mem_oddSide cR.1 cR.2.1]
          omega
        · rw [pkG_mem_oddSide cK.1 cK.2.1]
          omega
      · have hown : ∀ K ∈ pkGKids D h, ¬ (K.1 ≤ x ∧ x < K.2) := fun K hK q => hk ⟨K, hK, q⟩
        have := (pkG_U_own x1 x2 hown).1 hx
        have hxR := hown R hRh
        refine ⟨by omega, ?_⟩
        rw [pkG_mem_oddSide cR.1 cR.2.1]
        omega
  obtain ⟨h, hh, hx⟩ := key
  refine ⟨h, hh, fun X hL => ?_⟩
  have hQ : pkGQ N X (pkGU D h) = 0 :=
    pkG_Q_zero_oo hE cP.1 cP.2.1 hin (fun x hx' => ⟨(hx x hx').1, hRP (hx x hx').2⟩) hL
  have e : pkGV N X D h = pkGSgn (pkGVerts D h).card * pkGQ N X (pkGU D h) := rfl
  rw [e, hQ, mul_zero]

/-- **A face that vanishes, tail case**: `e_in(P) = ∅` for a chord `P ∈ D` ⇒ some face has `V = 0`
at every point of `L_S` at which `pkGA4` holds (a source face, by tail-minimality; `pkGA4` is used
at the root face). -/
theorem pkG_G4_e {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)} (hD : D ∈ pkGDis N)
    {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ} (hPD : P ∈ D) (hin : innerEE N S P = ∅) :
    ∃ r ∈ pkGRoots N D, ∀ X : ℕ × ℕ → ℚ, pkGA4 N X → OnLocus N S X → pkGV N X D r = 0 := by
  obtain ⟨R, hRm, hmin⟩ := exists_min_image (D.filter (fun R => evenSide N R ⊆ evenSide N P))
    (fun R => (evenSide N R).card) ⟨P, mem_filter.2 ⟨hPD, subset_refl _⟩⟩
  obtain ⟨hRD, hRP⟩ := mem_filter.1 hRm
  have cR := pkG_chord hD hRD
  have cP := pkG_chord hD hPD
  have hmin' : ∀ K ∈ D, evenSide N K ⊆ evenSide N R → ∀ w ∈ evenSide N R,
      w ∉ evenSide N K → False := by
    intro K hK hsub w hw hw'
    have h1 := hmin K (mem_filter.2 ⟨hK, subset_trans hsub hRP⟩)
    have h2 := card_lt_card ((ssubset_iff_of_subset hsub).2 ⟨w, hw, hw'⟩)
    omega
  have key : ∃ h ∈ pkGRoots N D, ∃ T : Finset ℕ, (T = pkGU D h ∨ T = Icc 1 N \ pkGU D h) ∧
      ∀ x ∈ T, x % 2 = 0 ∧ x ∈ evenSide N R := by
    by_cases hR1 : R.1 % 2 = 0
    · refine ⟨R, mem_insert_of_mem hRD, pkGU D R, Or.inl rfl, fun x hx => ?_⟩
      obtain ⟨x1, x2⟩ := pkG_U_sub hx
      by_cases hk : ∃ K ∈ pkGKids D R, K.1 ≤ x ∧ x < K.2
      · exfalso
        obtain ⟨K, hK, k1, k2⟩ := hk
        have hKp := (pkG_U_kid hD hK k1 k2).1 hx
        obtain ⟨hKD, hKR, a, b⟩ := pkG_kid_in hK
        have cK := pkG_chord hD hKD
        have hnn : ¬ (K.1 = R.1 ∧ K.2 = R.2) := fun ⟨u, v⟩ => hKR (pkG_eq_of u v)
        refine hmin' K hKD ?_ (if R.1 < K.1 then R.1 else R.2 - 1) ?_ ?_
        · intro z hz
          rw [pkG_mem_evenSide cK.1 cK.2.1] at hz
          rw [pkG_mem_evenSide cR.1 cR.2.1]
          omega
        · rw [pkG_mem_evenSide cR.1 cR.2.1]
          split_ifs <;> omega
        · rw [pkG_mem_evenSide cK.1 cK.2.1]
          split_ifs <;> omega
      · have hown : ∀ K ∈ pkGKids D R, ¬ (K.1 ≤ x ∧ x < K.2) := fun K hK q => hk ⟨K, hK, q⟩
        have := (pkG_U_own x1 x2 hown).1 hx
        refine ⟨by omega, ?_⟩
        rw [pkG_mem_evenSide cR.1 cR.2.1]
        omega
    · obtain ⟨h, hh, hRh⟩ := pkG_par_ex hN hE hD hRD
      obtain ⟨-, hRne, a, b⟩ := pkG_kid_in hRh
      have ch := pkG_root hN hE hD hh
      -- a kid of `h` in `U'`-position with even start contradicts minimality
      have hkid : ∀ K ∈ pkGKids D h, K.1 % 2 = 0 → False := by
        intro K hK hK0
        have hKR : K ≠ R := fun e => by
          rw [e] at hK0
          omega
        have hdisj := pkG_kids_disj hD hK hRh hKR
        obtain ⟨hKD, -, -, -⟩ := pkG_kid_in hK
        have cK := pkG_chord hD hKD
        refine hmin' K hKD ?_ N ?_ ?_
        · intro z hz
          rw [pkG_mem_evenSide cK.1 cK.2.1] at hz
          rw [pkG_mem_evenSide cR.1 cR.2.1]
          omega
        · rw [pkG_mem_evenSide cR.1 cR.2.1]
          omega
        · rw [pkG_mem_evenSide cK.1 cK.2.1]
          omega
      by_cases hh0 : h.1 % 2 = 0
      · refine ⟨h, hh, pkGU D h, Or.inl rfl, fun x hx => ?_⟩
        obtain ⟨x1, x2⟩ := pkG_U_sub hx
        by_cases hk : ∃ K ∈ pkGKids D h, K.1 ≤ x ∧ x < K.2
        · exfalso
          obtain ⟨K, hK, k1, k2⟩ := hk
          have hKp := (pkG_U_kid hD hK k1 k2).1 hx
          exact hkid K hK (by omega)
        · have hown : ∀ K ∈ pkGKids D h, ¬ (K.1 ≤ x ∧ x < K.2) := fun K hK q => hk ⟨K, hK, q⟩
          have := (pkG_U_own x1 x2 hown).1 hx
          have hxR := hown R hRh
          refine ⟨by omega, ?_⟩
          rw [pkG_mem_evenSide cR.1 cR.2.1]
          omega
      · -- `h.1` odd: `h` is the root `(1, N)` (a chord `h` would contradict tail-minimality)
        have hh1 : h = (1, N) := by
          rcases mem_insert.1 hh with e | e
          · exact e
          · exfalso
            have hnn : ¬ (R.1 = h.1 ∧ R.2 = h.2) := fun ⟨u, v⟩ => hRne (pkG_eq_of u v)
            have cH := pkG_chord hD e
            refine hmin' h e ?_ (if h.1 < R.1 then h.1 else h.2 - 1) ?_ ?_
            · intro z hz
              rw [pkG_mem_evenSide cH.1 cH.2.1] at hz
              rw [pkG_mem_evenSide cR.1 cR.2.1]
              omega
            · rw [pkG_mem_evenSide cR.1 cR.2.1]
              split_ifs <;> omega
            · rw [pkG_mem_evenSide cH.1 cH.2.1]
              split_ifs <;> omega
        have e1 : h.1 = 1 := by rw [hh1]
        have e2 : h.2 = N := by rw [hh1]
        refine ⟨h, hh, Icc 1 N \ pkGU D h, Or.inr rfl, fun x hx => ?_⟩
        obtain ⟨hxI, hxU⟩ := mem_sdiff.1 hx
        obtain ⟨x1, x2⟩ := mem_Icc.1 hxI
        by_cases hxN : x = N
        · refine ⟨by omega, ?_⟩
          rw [pkG_mem_evenSide cR.1 cR.2.1]
          omega
        · by_cases hk : ∃ K ∈ pkGKids D h, K.1 ≤ x ∧ x < K.2
          · exfalso
            obtain ⟨K, hK, k1, k2⟩ := hk
            have hKp := pkG_U_kid hD hK k1 k2
            have hK0 : K.1 % 2 = 0 := by
              by_contra hK0
              exact hxU (hKp.2 (by omega))
            exact hkid K hK hK0
          · have hown : ∀ K ∈ pkGKids D h, ¬ (K.1 ≤ x ∧ x < K.2) := fun K hK q => hk ⟨K, hK, q⟩
            have hU := pkG_U_own (D := D) (r := h) (x := x) (by omega) (by omega) hown
            have hxR := hown R hRh
            have hx0 : x % 2 = 0 := by
              by_contra hx0
              exact hxU (hU.2 (by omega))
            refine ⟨hx0, ?_⟩
            rw [pkG_mem_evenSide cR.1 cR.2.1]
            omega
  obtain ⟨h, hh, T, hT, hx⟩ := key
  refine ⟨h, hh, fun X hA4 hL => ?_⟩
  have hQT : pkGQ N X T = 0 :=
    pkG_Q_zero_ee cP.1 cP.2.1 hin (fun x hx' => ⟨(hx x hx').1, hRP (hx x hx').2⟩) hL
  have hQ : pkGQ N X (pkGU D h) = 0 := by
    rcases hT with e | e
    · rw [← e]
      exact hQT
    · rw [hA4 _ (pkG_U_Icc hN hE hD hh), ← e]
      exact hQT
  have e : pkGV N X D h = pkGSgn (pkGVerts D h).card * pkGQ N X (pkGU D h) := rfl
  rw [e, hQ, mul_zero]

/-- **A face that vanishes**: `𝒫₁ = ∅` and `∅ ≠ D ⊆ 𝒫₀` ⇒ some face of `D` has `V = 0` at every
point of `L_S` at which `pkGA4` holds. -/
theorem pkG_G4 {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)} (hD : D ∈ pkGDis N)
    {S : Finset (ℕ × ℕ)} (hP1 : poleChords N S = ∅) (hsub : D ⊆ cleanChords N S)
    (hne : D.Nonempty) :
    ∃ r ∈ pkGRoots N D, ∀ X : ℕ × ℕ → ℚ, pkGA4 N X → OnLocus N S X → pkGV N X D r = 0 := by
  obtain ⟨P, hPD⟩ := hne
  have hPc := hsub hPD
  have hnp : ¬ ((innerEE N S P).Nonempty ∧ (innerOO N S P).Nonempty) := by
    intro q
    have hm : P ∈ poleChords N S := mem_filter.2 ⟨hPc, q⟩
    rw [hP1] at hm
    exact notMem_empty P hm
  by_cases hoo : (innerOO N S P).Nonempty
  · have hee : innerEE N S P = ∅ := not_nonempty_iff_eq_empty.1 (fun q => hnp ⟨q, hoo⟩)
    exact pkG_G4_e hN hE hD hPD hee
  · obtain ⟨r, hr, hV⟩ := pkG_G4_o hN hE hD hPD (not_nonempty_iff_eq_empty.1 hoo)
    exact ⟨r, hr, fun X _ hL => hV X hL⟩

/-- **Descendants**: a chord strictly inside a root side lies inside one of its kids (or is one). -/
theorem pkG_desc {N : ℕ} {D : Finset (ℕ × ℕ)} (hD : D ∈ pkGDis N) {r R : ℕ × ℕ} (hR : R ∈ D)
    (hRr : pkGIn R r) : ∃ K ∈ pkGKids D r, K.1 ≤ R.1 ∧ R.2 ≤ K.2 := by
  obtain ⟨K, hKm, hmax⟩ := exists_max_image
    (D.filter (fun K => (K ≠ r ∧ r.1 ≤ K.1 ∧ K.2 ≤ r.2) ∧ K.1 ≤ R.1 ∧ R.2 ≤ K.2))
    (fun K : ℕ × ℕ => K.2 - K.1)
    ⟨R, mem_filter.2 ⟨hR, hRr, le_refl _, le_refl _⟩⟩
  obtain ⟨hKD, hKr, k1, k2⟩ := mem_filter.1 hKm
  refine ⟨K, pkG_mem_kids.2 ⟨hKD, hKr, fun K' hK' hK'r hKK' => ?_⟩, k1, k2⟩
  obtain ⟨n1, a1, b1⟩ := hKK'
  have hm := hmax K' (mem_filter.2 ⟨hK', hK'r, by omega, by omega⟩)
  have cK := pkG_chord hD hKD
  have cK' := pkG_chord hD hK'
  have hnn : ¬ (K.1 = K'.1 ∧ K.2 = K'.2) := fun ⟨u, v⟩ => n1 (pkG_eq_of u v)
  omega

/-- **All-or-nothing on descendant blocks**: the class `U'` is constant on the block of every chord
strictly inside the face. -/
theorem pkG_U_desc {N : ℕ} {D : Finset (ℕ × ℕ)} (hD : D ∈ pkGDis N) {r R : ℕ × ℕ} (hR : R ∈ D)
    (hRr : pkGIn R r) {x x' : ℕ} (h1 : R.1 ≤ x) (h2 : x < R.2) (h1' : R.1 ≤ x') (h2' : x' < R.2) :
    x ∈ pkGU D r ↔ x' ∈ pkGU D r := by
  obtain ⟨K, hK, k1, k2⟩ := pkG_desc hD hR hRr
  rw [pkG_U_kid hD hK (by omega) (by omega), pkG_U_kid hD hK (by omega) (by omega)]

/-- Own legs of the face with root side `r`: legs of `[r.1, r.2)` in no kid block. -/
def pkGOwn (D : Finset (ℕ × ℕ)) (r : ℕ × ℕ) : Finset ℕ :=
  (Ico r.1 r.2).filter (fun x => ∀ K ∈ pkGKids D r, ¬ (K.1 ≤ x ∧ x < K.2))

theorem pkG_mem_own {D : Finset (ℕ × ℕ)} {r : ℕ × ℕ} {x : ℕ} :
    x ∈ pkGOwn D r ↔ r.1 ≤ x ∧ x < r.2 ∧ ∀ K ∈ pkGKids D r, ¬ (K.1 ≤ x ∧ x < K.2) := by
  change x ∈ (Ico r.1 r.2).filter _ ↔ _
  rw [mem_filter, mem_Ico, and_assoc]

/-- **Vertices of a face**: `verts = own ∪ {kid left ends} ∪ {r.2}`. -/
theorem pkG_verts_eq {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)} (hD : D ∈ pkGDis N)
    {r : ℕ × ℕ} (hr : r ∈ pkGRoots N D) :
    pkGVerts D r = pkGOwn D r ∪ ((pkGKids D r).image (fun K => K.1) ∪ {r.2}) := by
  have cr := pkG_root hN hE hD hr
  ext w
  rw [pkG_mem_verts, mem_union, mem_union, mem_image, mem_singleton, pkG_mem_own]
  constructor
  · rintro ⟨w1, w2, hw⟩
    by_cases hw2 : w = r.2
    · exact Or.inr (Or.inr hw2)
    · by_cases hk : ∃ K ∈ pkGKids D r, K.1 ≤ w ∧ w < K.2
      · obtain ⟨K, hK, k1, k2⟩ := hk
        have := hw K hK
        exact Or.inr (Or.inl ⟨K, hK, by omega⟩)
      · exact Or.inl ⟨w1, by omega, fun K hK q => hk ⟨K, hK, q⟩⟩
  · rintro (⟨w1, w2, hw⟩ | ⟨K, hK, rfl⟩ | hw)
    · exact ⟨w1, by omega, fun K hK q => hw K hK ⟨by omega, q.2⟩⟩
    · exact pkG_mem_verts.1 (pkG_kid_vert hD hK)
    · rw [hw]
      refine ⟨by omega, le_refl _, fun K hK q => ?_⟩
      have := (pkG_kid_in hK).2.2.2
      omega

/-- **Vertex count**: `|verts| = |own| + |kids| + 1`. -/
theorem pkG_card_verts {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)}
    (hD : D ∈ pkGDis N) {r : ℕ × ℕ} (hr : r ∈ pkGRoots N D) :
    (pkGVerts D r).card = (pkGOwn D r).card + (pkGKids D r).card + 1 := by
  have cr := pkG_root hN hE hD hr
  have hinj : Set.InjOn (fun K : ℕ × ℕ => K.1) (pkGKids D r) := by
    intro K hK K' hK' e
    by_contra hne
    have := pkG_kids_disj hD hK hK' hne
    have c := pkG_chord hD (pkG_kid_in hK).1
    have c' := pkG_chord hD (pkG_kid_in hK').1
    dsimp only at e
    omega
  have hci := card_image_of_injOn hinj
  have hd1 : Disjoint ((pkGKids D r).image (fun K => K.1)) {r.2} := by
    rw [disjoint_singleton_right, mem_image]
    rintro ⟨K, hK, e⟩
    have := (pkG_kid_in hK).2.2.2
    have c := pkG_chord hD (pkG_kid_in hK).1
    omega
  have hd2 : Disjoint (pkGOwn D r) ((pkGKids D r).image (fun K => K.1) ∪ {r.2}) := by
    rw [disjoint_left]
    intro w hw hw'
    obtain ⟨w1, w2, hw⟩ := pkG_mem_own.1 hw
    rcases mem_union.1 hw' with h | h
    · obtain ⟨K, hK, e⟩ := mem_image.1 h
      have c := pkG_chord hD (pkG_kid_in hK).1
      exact hw K hK ⟨by omega, by omega⟩
    · rw [mem_singleton] at h
      omega
  rw [pkG_verts_eq hN hE hD hr, card_union_of_disjoint hd2, card_union_of_disjoint hd1, hci,
      card_singleton]
  omega

/-- **Block partition**: `[r.1, r.2) = own ⊔ ⨆_{kids} [K.1, K.2)`. -/
theorem pkG_Ico_eq {D : Finset (ℕ × ℕ)} {r : ℕ × ℕ} :
    Ico r.1 r.2 = pkGOwn D r ∪ (pkGKids D r).biUnion (fun K => Ico K.1 K.2) := by
  ext x
  rw [mem_union, mem_biUnion, pkG_mem_own, mem_Ico]
  constructor
  · rintro ⟨x1, x2⟩
    by_cases hk : ∃ K ∈ pkGKids D r, K.1 ≤ x ∧ x < K.2
    · obtain ⟨K, hK, k⟩ := hk
      exact Or.inr ⟨K, hK, mem_Ico.2 k⟩
    · exact Or.inl ⟨x1, x2, fun K hK q => hk ⟨K, hK, q⟩⟩
  · rintro (⟨x1, x2, -⟩ | ⟨K, hK, hx⟩)
    · exact ⟨x1, x2⟩
    · have := (pkG_kid_in hK).2.2
      have := mem_Ico.1 hx
      omega

/-- **Faces have an even number of vertices**: `|verts|` is even. -/
theorem pkG_verts_even {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)}
    (hD : D ∈ pkGDis N)
    {r : ℕ × ℕ} (hr : r ∈ pkGRoots N D) : (pkGVerts D r).card % 2 = 0 := by
  have cr := pkG_root hN hE hD hr
  have hdisjK : ∀ K ∈ pkGKids D r, ∀ K' ∈ pkGKids D r, K ≠ K' →
      Disjoint ((fun K : ℕ × ℕ => Ico K.1 K.2) K) ((fun K : ℕ × ℕ => Ico K.1 K.2) K') := by
    intro K hK K' hK' hne
    have := pkG_kids_disj hD hK hK' hne
    rw [disjoint_left]
    intro x hx hx'
    have := mem_Ico.1 hx
    have := mem_Ico.1 hx'
    omega
  have hcb := card_biUnion hdisjK
  have hd : Disjoint (pkGOwn D r) ((pkGKids D r).biUnion (fun K => Ico K.1 K.2)) := by
    rw [disjoint_left]
    intro x hx hx'
    obtain ⟨-, -, hw⟩ := pkG_mem_own.1 hx
    obtain ⟨K, hK, hxK⟩ := mem_biUnion.1 hx'
    exact hw K hK (mem_Ico.1 hxK)
  have hc := card_union_of_disjoint hd
  rw [← pkG_Ico_eq, Nat.card_Ico, hcb] at hc
  have hmod : (∑ K ∈ pkGKids D r, (Ico K.1 K.2).card) % 2 = (pkGKids D r).card % 2 := by
    rw [Finset.sum_nat_mod]
    have e : ∀ K ∈ pkGKids D r, (Ico K.1 K.2).card % 2 = 1 := by
      intro K hK
      have c := pkG_chord hD (pkG_kid_in hK).1
      rw [Nat.card_Ico]
      omega
    rw [sum_congr rfl e, sum_const, smul_eq_mul, mul_one]
  have hcv := pkG_card_verts hN hE hD hr
  omega

/-! ### Helpers of the proof of the germ input (prefix `pkG_`): the linear layer -/

/-- The double sum `F(A, B) = Σ_{a ∈ A} Σ_{b ∈ B} m a b` of a function of two legs. -/
def pkGF (m : ℕ → ℕ → ℚ) (A B : Finset ℕ) : ℚ := ∑ a ∈ A, ∑ b ∈ B, m a b

theorem pkG_F_unionL (m : ℕ → ℕ → ℚ) {A B : Finset ℕ} (h : Disjoint A B) (C : Finset ℕ) :
    pkGF m (A ∪ B) C = pkGF m A C + pkGF m B C := by
  have e : ∀ A' : Finset ℕ, pkGF m A' C = ∑ a ∈ A', ∑ b ∈ C, m a b := fun A' => rfl
  rw [e, e, e, sum_union h]

theorem pkG_F_unionR (m : ℕ → ℕ → ℚ) {A B : Finset ℕ} (h : Disjoint A B) (C : Finset ℕ) :
    pkGF m C (A ∪ B) = pkGF m C A + pkGF m C B := by
  have e : ∀ B' : Finset ℕ, pkGF m C B' = ∑ a ∈ C, ∑ b ∈ B', m a b := fun B' => rfl
  rw [e, e, e, ← sum_add_distrib]
  exact sum_congr rfl (fun a _ => sum_union h)

theorem pkG_F_comm {m : ℕ → ℕ → ℚ} (hs : ∀ a b, m a b = m b a) (A B : Finset ℕ) :
    pkGF m A B = pkGF m B A := by
  have e : ∀ A' B' : Finset ℕ, pkGF m A' B' = ∑ a ∈ A', ∑ b ∈ B', m a b := fun A' B' => rfl
  rw [e, e, sum_comm]
  exact sum_congr rfl (fun b _ => sum_congr rfl (fun a _ => hs a b))

/-- Row sums: `F(A, I) = 0` when every row sum over `I` vanishes. -/
theorem pkG_F_row {m : ℕ → ℕ → ℚ} {I : Finset ℕ} (hr : ∀ a ∈ I, ∑ b ∈ I, m a b = 0) {A : Finset ℕ}
    (hA : A ⊆ I) :
    pkGF m A I = 0 := by
  have e : pkGF m A I = ∑ a ∈ A, ∑ b ∈ I, m a b := rfl
  rw [e]
  exact sum_eq_zero (fun a ha => hr a (hA ha))

/-- `2 Σ_{a < b ∈ U} m a b = F(U, U)` for a symmetric `m` vanishing on the diagonal. -/
theorem pkG_F_tri {m : ℕ → ℕ → ℚ} (hs : ∀ a b, m a b = m b a) (hd : ∀ a, m a a = 0) (U : Finset ℕ) :
    2 * ∑ p ∈ (U ×ˢ U).filter (fun p => p.1 < p.2), m p.1 p.2 = pkGF m U U := by
  rw [sum_filter, sum_product]
  have hsw : ∑ a ∈ U, ∑ b ∈ U, (if b < a then m a b else 0) = ∑ a ∈ U, ∑ b ∈ U,
      (if a < b then m a b else 0) := by
    rw [sum_comm]
    exact sum_congr rfl (fun a _ => sum_congr rfl (fun b _ => by rw [hs b a]))
  have hpt : pkGF m U U = ∑ a ∈ U, ∑ b ∈ U,
      ((if a < b then m a b else 0) + (if b < a then m a b else 0)) := by
    refine sum_congr rfl (fun a _ => sum_congr rfl (fun b _ => ?_))
    rcases lt_trichotomy a b with h | h | h
    · rw [ite_eq_left h, ite_eq_right (by omega)]; ring
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), h, hd b]; ring
    · rw [ite_eq_right (by omega), ite_eq_left h]; ring
  rw [hpt]
  simp only [sum_add_distrib]
  rw [hsw]
  ring

/-- `evens W ∪ odds W = W`, disjointly. -/
theorem pkG_eo_union (W : Finset ℕ) : evens W ∪ odds W = W := by
  ext x
  simp only [mem_union, evens, odds, mem_filter]
  constructor
  · intro h
    rcases h with h | h
    · exact h.1
    · exact h.1
  · intro h
    rcases Nat.mod_two_eq_zero_or_one x with h2 | h2
    · exact Or.inl ⟨h, h2⟩
    · exact Or.inr ⟨h, h2⟩

theorem pkG_eo_disj (W : Finset ℕ) : Disjoint (evens W) (odds W) := by
  rw [disjoint_left]
  intro x h1 h2
  have a := (mem_filter.1 h1).2
  have b := (mem_filter.1 h2).2
  omega

/-- `F(W, W) = F(evens, evens) + F(odds, odds) + 2 F(evens, odds)` for a symmetric `m`. -/
theorem pkG_F_split {m : ℕ → ℕ → ℚ} (hs : ∀ a b, m a b = m b a) (W : Finset ℕ) :
    pkGF m W W = pkGF m (evens W) (evens W) + pkGF m (odds W) (odds W) + 2 * pkGF m (evens W)
        (odds W) := by
  have hW := pkG_eo_union W
  have hd := pkG_eo_disj W
  have e1 : pkGF m W W = pkGF m (evens W ∪ odds W) (evens W ∪ odds W) := by rw [hW]
  rw [e1, pkG_F_unionL m hd, pkG_F_unionR m hd, pkG_F_unionR m hd, pkG_F_comm hs (odds W) (evens W)]
  ring

/-- **Complement symmetry, generic form**: for a symmetric `m` with vanishing row sums over `I`, and
`U ⊆ I`: `F(U,U) = F(I∖U, I∖U)`. -/
theorem pkG_gen_A4 {m : ℕ → ℕ → ℚ} (hs : ∀ a b, m a b = m b a) {I : Finset ℕ}
    (hr : ∀ a ∈ I, ∑ b ∈ I, m a b = 0) {U : Finset ℕ} (hU : U ⊆ I) :
    pkGF m U U = pkGF m (I \ U) (I \ U) := by
  have hI : U ∪ (I \ U) = I := union_sdiff_of_subset hU
  have hd : Disjoint U (I \ U) := disjoint_sdiff
  have r1 := pkG_F_row hr hU
  have r2 := pkG_F_row hr (sdiff_subset : I \ U ⊆ I)
  have s1 : pkGF m U I = pkGF m U U + pkGF m U (I \ U) := by rw [← pkG_F_unionR m hd, hI]
  have s2 : pkGF m (I \ U) I = pkGF m (I \ U) U + pkGF m (I \ U) (I \ U) :=
      by rw [← pkG_F_unionR m hd, hI]
  rw [pkG_F_comm hs (I \ U) U] at s2
  linarith

/-- **Cross-sum identity, generic form**: for a symmetric `m` with vanishing row sums over `I`, and
`U ⊆ I`: `F(U,U) + 2 F(Ue, Vo) + F(Ie, Ie) − F(Ve, Ve) − F(Uo, Uo) = 0` (`Ue`/`Uo` = evens/odds of
`U`, `Ve`/`Vo` of `I ∖ U`, `Ie` = evens of `I`). -/
theorem pkG_gen_A5 {m : ℕ → ℕ → ℚ} (hs : ∀ a b, m a b = m b a) {I : Finset ℕ}
    (hr : ∀ a ∈ I, ∑ b ∈ I, m a b = 0) {U : Finset ℕ} (hU : U ⊆ I) :
    pkGF m U U + 2 * pkGF m (evens U) (odds (I \ U)) + pkGF m (evens I) (evens I) -
      pkGF m (evens (I \ U)) (evens (I \ U)) - pkGF m (odds U) (odds U) = 0 := by
  have hI : U ∪ (I \ U) = I := union_sdiff_of_subset hU
  have hd : Disjoint U (I \ U) := disjoint_sdiff
  have hIe : evens U ∪ evens (I \ U) = evens I := by
    have e : evens I = evens (U ∪ (I \ U)) := by rw [hI]
    rw [e]
    change U.filter (fun a => a % 2 = 0) ∪ (I \ U).filter (fun a => a % 2 = 0) =
      (U ∪ (I \ U)).filter (fun a => a % 2 = 0)
    rw [filter_union]
  have hde : Disjoint (evens U) (evens (I \ U)) := disjoint_filter_filter hd
  -- the row sums over `I` from the even legs of `U`
  have r1 : pkGF m (evens U) I = 0 :=
      pkG_F_row hr (subset_trans (filter_subset _ _ : evens U ⊆ U) hU)
  have s1 : pkGF m (evens U) I = pkGF m (evens U) U + pkGF m (evens U) (I \ U) := by
    rw [← pkG_F_unionR m hd, hI]
  have s2 : pkGF m (evens U) U = pkGF m (evens U) (evens U) + pkGF m (evens U) (odds U) := by
    rw [← pkG_F_unionR m (pkG_eo_disj U), pkG_eo_union U]
  have s3 : pkGF m (evens U) (I \ U) = pkGF m (evens U) (evens (I \ U)) + pkGF m (evens U)
      (odds (I \ U)) := by
    rw [← pkG_F_unionR m (pkG_eo_disj (I \ U)), pkG_eo_union (I \ U)]
  have hU2 := pkG_F_split hs U
  have hIe2 : pkGF m (evens I) (evens I) = pkGF m (evens U) (evens U) + pkGF m (evens (I \ U))
      (evens (I \ U)) +
      2 * pkGF m (evens U) (evens (I \ U)) := by
    rw [← hIe, pkG_F_unionL m hde, pkG_F_unionR m hde, pkG_F_unionR m hde,
      pkG_F_comm hs (evens (I \ U)) (evens U)]
    ring
  rw [hU2, hIe2]
  linarith

-- registry: T-SZXS
/-- The mesh variables as a function of two legs. -/
def pkGM (N : ℕ) (X : ℕ × ℕ → ℚ) : ℕ → ℕ → ℚ := fun a b => mesh N X a b

theorem pkG_m_symm (N : ℕ) (X : ℕ × ℕ → ℚ) (a b : ℕ) :
    pkGM N X a b = pkGM N X b a := pkL_mesh_comm N X a b

theorem pkG_m_self {N : ℕ} (hN : 2 ≤ N) (X : ℕ × ℕ → ℚ) (a : ℕ) :
    pkGM N X a a = 0 := pkL_mesh_self hN X a

/-- **Row sums**: the row sums of the mesh variables over all legs vanish. -/
theorem pkG_m_row {N : ℕ} (hN : 1 ≤ N) (X : ℕ × ℕ → ℚ) :
    ∀ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, pkGM N X a b = 0 :=
  fun a _ => pkL_row hN X a

/-- `Q_U = −½ F(U, U)` with `m = mesh`. -/
theorem pkG_Q_F {N : ℕ} (hN : 2 ≤ N) (X : ℕ × ℕ → ℚ) (U : Finset ℕ) :
    2 * pkGQ N X U = - pkGF (pkGM N X) U U := by
  rw [← pkG_F_tri (pkG_m_symm N X) (pkG_m_self hN X) U]
  change 2 * (∑ p ∈ (U ×ˢ U).filter (fun p => p.1 < p.2), -mesh N X p.1 p.2) =
    -(2 * ∑ p ∈ (U ×ˢ U).filter (fun p => p.1 < p.2), mesh N X p.1 p.2)
  rw [sum_neg_distrib]
  ring

/-- `2·Σee_W = F(evens W, evens W)` for the function `pkGM` of the mesh variables
(`pkG_Soo_F` below gives `2·Σoo_W = F(odds W, odds W)`). -/
theorem pkG_See_F {N : ℕ} (hN : 2 ≤ N) (X : ℕ × ℕ → ℚ) (W : Finset ℕ) :
    2 * pkGSee N X W = pkGF (pkGM N X) (evens W) (evens W) := by
  rw [← pkG_F_tri (pkG_m_symm N X) (pkG_m_self hN X) (evens W)]
  have e : pkGSee N X W =
      ∑ p ∈ (W ×ˢ W).filter (fun p => p.1 < p.2 ∧ p.1 % 2 = 0 ∧ p.2 % 2 = 0),
          mesh N X p.1 p.2 := rfl
  have hs : (W ×ˢ W).filter (fun p => p.1 < p.2 ∧ p.1 % 2 = 0 ∧ p.2 % 2 = 0) =
      (evens W ×ˢ evens W).filter (fun p => p.1 < p.2) := by
    ext p
    simp only [mem_filter, mem_product, evens]
    constructor
    · intro h
      exact ⟨⟨⟨h.1.1, h.2.2.1⟩, ⟨h.1.2, h.2.2.2⟩⟩, h.2.1⟩
    · intro h
      exact ⟨⟨h.1.1.1, h.1.2.1⟩, h.2, h.1.1.2, h.1.2.2⟩
  rw [e, hs]
  rfl

theorem pkG_Soo_F {N : ℕ} (hN : 2 ≤ N) (X : ℕ × ℕ → ℚ) (W : Finset ℕ) :
    2 * pkGSoo N X W = pkGF (pkGM N X) (odds W) (odds W) := by
  rw [← pkG_F_tri (pkG_m_symm N X) (pkG_m_self hN X) (odds W)]
  have e : pkGSoo N X W =
      ∑ p ∈ (W ×ˢ W).filter (fun p => p.1 < p.2 ∧ p.1 % 2 = 1 ∧ p.2 % 2 = 1),
          mesh N X p.1 p.2 := rfl
  have hs : (W ×ˢ W).filter (fun p => p.1 < p.2 ∧ p.1 % 2 = 1 ∧ p.2 % 2 = 1) =
      (odds W ×ˢ odds W).filter (fun p => p.1 < p.2) := by
    ext p
    simp only [mem_filter, mem_product, odds]
    constructor
    · intro h
      exact ⟨⟨⟨h.1.1, h.2.2.1⟩, ⟨h.1.2, h.2.2.2⟩⟩, h.2.1⟩
    · intro h
      exact ⟨⟨h.1.1.1, h.1.2.1⟩, h.2, h.1.1.2, h.1.2.2⟩
  rw [e, hs]
  rfl

/-- `E` is the sum over ee pairs `a < b` of all legs. -/
theorem pkG_E_See {N : ℕ} (X : ℕ × ℕ → ℚ) : pkGE N X = pkGSee N X (Icc 1 N) := by
  have e1 : pkGE N X = ∑ t ∈ (diagonals N).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0),
      mesh N X t.1 t.2 := rfl
  have e2 : pkGSee N X (Icc 1 N) = ∑ p ∈ (Icc 1 N ×ˢ Icc 1 N).filter
      (fun p => p.1 < p.2 ∧ p.1 % 2 = 0 ∧ p.2 % 2 = 0), mesh N X p.1 p.2 := rfl
  have hs : (diagonals N).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0) =
      (Icc 1 N ×ˢ Icc 1 N).filter (fun p => p.1 < p.2 ∧ p.1 % 2 = 0 ∧ p.2 % 2 = 0) := by
    ext p
    simp only [mem_filter, mem_diagonals, mem_product, mem_Icc]
    constructor
    · intro h
      obtain ⟨⟨h1, h2, h3, h4⟩, h6, h7⟩ := h
      exact ⟨⟨⟨h1, by omega⟩, ⟨by omega, h2⟩⟩, by omega, h6, h7⟩
    · intro h
      obtain ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, h5, h6, h7⟩ := h
      exact ⟨⟨h1, h4, by omega, by omega⟩, h6, h7⟩
  rw [e1, e2, hs]

/-- The cross sum as `F(evens U, odds Uᶜ)`. -/
theorem pkG_cross_F (N : ℕ) (X : ℕ × ℕ → ℚ) (U : Finset ℕ) :
    pkGCross N X U = pkGF (pkGM N X) (evens U) (odds (Icc 1 N \ U)) := by
  have e : pkGCross N X U = ∑ p ∈ evens U ×ˢ odds (Icc 1 N \ U), mesh N X (min p.1 p.2)
      (max p.1 p.2) := rfl
  rw [e, sum_product]
  refine sum_congr rfl (fun a _ => sum_congr rfl (fun b _ => ?_))
  change mesh N X (min a b) (max a b) = mesh N X a b
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, pkL_mesh_comm N X b a]

/-- **`pkGA4` holds everywhere**: `pkGA4 N X` for every `N ≥ 2` and every `X`. -/
theorem pkG_A4_all {N : ℕ} (hN : 2 ≤ N) (X : ℕ × ℕ → ℚ) : pkGA4 N X := by
  intro U hU
  have h := pkG_gen_A4 (pkG_m_symm N X) (pkG_m_row (by omega) X) hU
  have q1 := pkG_Q_F hN X U
  have q2 := pkG_Q_F hN X (Icc 1 N \ U)
  linarith

/-- **`pkGA5` holds everywhere**: `pkGA5 N X` for every `N ≥ 2` and every `X`. -/
theorem pkG_A5_all {N : ℕ} (hN : 2 ≤ N) (X : ℕ × ℕ → ℚ) : pkGA5 N X := by
  intro U hU
  have h := pkG_gen_A5 (pkG_m_symm N X) (pkG_m_row (by omega) X) hU
  have q := pkG_Q_F hN X U
  have c := pkG_cross_F N X U
  have e1 := pkG_See_F hN X (Icc 1 N \ U)
  have e2 := pkG_See_F hN X (Icc 1 N)
  have o := pkG_Soo_F hN X U
  have eE := pkG_E_See (N := N) X
  linarith


/-- **Planar variables as vertex forms**: `X_{ij} = Q_{[i, j)}` for a diagonal `(i, j)`. -/
theorem pkG_S1 {N : ℕ} (hN : 2 ≤ N) (X : ℕ × ℕ → ℚ) {i j : ℕ} (h : (i, j) ∈ diagonals N) :
    X (i, j) = pkGQ N X (Ico i j) := by
  have hd := mem_diagonals.1 h
  dsimp only at hd
  have ht := pkL_tri hN X (u := i) (v := j - 1) hd.1 (by omega) (by omega)
  rw [show j - 1 + 1 = j by omega, planar_eq_X X hd.1 hd.2.2.1 hd.2.1 hd.2.2.2] at ht
  have hs : (Ico i j ×ˢ Ico i j).filter (fun p => p.1 < p.2) =
      (Icc 1 N ×ˢ Icc 1 N).filter (fun p => i ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ j - 1) := by
    ext ⟨a, b⟩
    simp only [mem_filter, mem_product, mem_Ico, mem_Icc]
    omega
  have c : ∑ p ∈ (Ico i j ×ˢ Ico i j).filter (fun p => p.1 < p.2), mesh N X p.1 p.2 =
      ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, (if i ≤ a ∧ a < b ∧ b ≤ j - 1 then mesh N X a b else 0) := by
    rw [hs, sum_filter, sum_product]
  have e : pkGQ N X (Ico i j) = ∑ p ∈ (Ico i j ×ˢ Ico i j).filter (fun p => p.1 < p.2),
      -mesh N X p.1 p.2 := rfl
  rw [e, sum_neg_distrib, c, ht]
  ring

/-- **The base locus**: on `L_{S ∪ same}` every same-parity mesh variable vanishes. -/
theorem pkG_same_zero {N : ℕ} {S : Finset (ℕ × ℕ)} {X : ℕ × ℕ → ℚ}
    (hL : OnLocus N (S ∪ pkGSame N) X) :
    ∀ t ∈ pkGSame N, mesh N X t.1 t.2 = 0 :=
  fun t ht => hL t (mem_union_right _ ht)

theorem pkG_mem_same {N : ℕ} {t : ℕ × ℕ} :
    t ∈ pkGSame N ↔ t ∈ diagonals N ∧ t.1 % 2 = t.2 % 2 := by
  change t ∈ (diagonals N).filter _ ↔ _
  exact mem_filter

/-- A same-parity pair `a < b` of legs (N even) is a diagonal. -/
theorem pkG_same_diag {N : ℕ} (hE : N % 2 = 0) {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ N)
    (hp : a % 2 = b % 2) : (a, b) ∈ pkGSame N :=
  pkG_mem_same.2 ⟨mem_diagonals.2 (by dsimp only; omega), hp⟩

/-- `Σoo` over all legs is the oo-diagonal sum (N even). -/
theorem pkG_Soo_all {N : ℕ} (hE : N % 2 = 0) (X : ℕ × ℕ → ℚ) :
    pkGSoo N X (Icc 1 N) = ∑ t ∈ (diagonals N).filter (fun p => p.1 % 2 = 1 ∧ p.2 % 2 = 1),
        mesh N X t.1 t.2 := by
  have e2 : pkGSoo N X (Icc 1 N) = ∑ p ∈ (Icc 1 N ×ˢ Icc 1 N).filter
      (fun p => p.1 < p.2 ∧ p.1 % 2 = 1 ∧ p.2 % 2 = 1), mesh N X p.1 p.2 := rfl
  have hs : (diagonals N).filter (fun p => p.1 % 2 = 1 ∧ p.2 % 2 = 1) =
      (Icc 1 N ×ˢ Icc 1 N).filter (fun p => p.1 < p.2 ∧ p.1 % 2 = 1 ∧ p.2 % 2 = 1) := by
    ext p
    simp only [mem_filter, mem_diagonals, mem_product, mem_Icc]
    constructor
    · intro h
      obtain ⟨⟨h1, h2, h3, h4⟩, h6, h7⟩ := h
      exact ⟨⟨⟨h1, by omega⟩, ⟨by omega, h2⟩⟩, by omega, h6, h7⟩
    · intro h
      obtain ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, h5, h6, h7⟩ := h
      exact ⟨⟨h1, h4, by omega, by omega⟩, h6, h7⟩
  rw [e2, hs]

theorem pkG_kids_empty (r : ℕ × ℕ) : pkGKids ∅ r = ∅ := by
  change (∅ : Finset (ℕ × ℕ)).filter _ = ∅
  exact filter_empty _

/-- **The empty dissection**: the one face of the empty dissection has `V = −ε_N E`,
`ε_N = (−1)^(N/2+1)`. -/
theorem pkG_V_empty {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (X : ℕ × ℕ → ℚ) :
    pkGV N X ∅ (1, N) = -((-1 : ℚ) ^ (N / 2 + 1)) * pkGE N X := by
  have hown : ∀ R ∈ pkGKids ∅ (1, N), ∀ x : ℕ, ¬ (R.1 ≤ x ∧ x < R.2) := by
    intro R hR x
    rw [pkG_kids_empty] at hR
    exact absurd hR (notMem_empty R)
  have hv : pkGVerts ∅ (1, N) = Icc 1 N := by
    ext w
    rw [pkG_mem_verts, mem_Icc]
    constructor
    · intro h
      exact ⟨h.1, h.2.1⟩
    · intro h
      refine ⟨h.1, h.2, fun R hR => ?_⟩
      rw [pkG_kids_empty] at hR
      exact absurd hR (notMem_empty R)
  have hU : pkGU ∅ (1, N) = odds (Icc 1 N) := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, b⟩ := pkG_U_sub hx
      have h := (pkG_U_own a b (fun R hR => hown R hR x)).1 hx
      exact mem_filter.2 ⟨mem_Icc.2 ⟨a, by omega⟩, by dsimp only at h; omega⟩
    · intro hx
      obtain ⟨h1, h2⟩ := mem_filter.1 hx
      obtain ⟨a, b⟩ := mem_Icc.1 h1
      exact (pkG_U_own (show (1, N).1 ≤ x from a) (show x < (1, N).2 by dsimp only; omega)
        (fun R hR => hown R hR x)).2 (by dsimp only; omega)
  have eV : pkGV N X ∅ (1, N) =
      pkGSgn (pkGVerts ∅ (1, N)).card * pkGQ N X (pkGU ∅ (1, N)) := rfl
  have eS : pkGSgn N = (-1 : ℚ) ^ (N / 2 - 1) := rfl
  rw [eV, hv, hU, Nat.card_Icc, show N + 1 - 1 = N by omega, eS]
  have q := pkG_Q_F (show 2 ≤ N by omega) X (odds (Icc 1 N))
  have o := pkG_Soo_F (show 2 ≤ N by omega) X (Icc 1 N)
  have oo := pkG_Soo_all hE X
  have l := pkL_l65 hN hE X
  have eE : pkGE N X = ∑ t ∈ (diagonals N).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0),
      mesh N X t.1 t.2 := rfl
  have hQ : pkGQ N X (odds (Icc 1 N)) = - pkGE N X := by linarith
  rw [hQ, show N / 2 + 1 = (N / 2 - 1) + 2 by omega, pow_add]
  ring

/-- **Clean chords vanish**: a clean odd chord vanishes on `L_{S ∪ same}`. -/
theorem pkG_G1_clean {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ}
    (hP : P ∈ cleanChords N S) {X : ℕ × ℕ → ℚ} (hL : OnLocus N (S ∪ pkGSame N) X) : X P = 0 := by
  obtain ⟨i, j⟩ := P
  have hc : (i, j) ∈ (oddDiagonals N).filter (fun P => Disjoint (minRect N P) (missing N S)) := hP
  obtain ⟨hPo, hdisj⟩ := mem_filter.1 hc
  obtain ⟨hi1, hjN, hij, hne, hodd⟩ := pkL_oddD hPo
  have hHsub : oddSideSplit N (i, j) ∪ evenSideSplit N (i, j) ⊆ diagonals N :=
    union_subset (fun t ht => (mem_filter.1 ht).1) (fun t ht => (mem_filter.1 ht).1)
  rw [pkL_hit0 hN hE X hPo]
  have h2 : ∑ t ∈ (diagonals N).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0),
      mesh N X t.1 t.2 = 0 := by
    refine sum_eq_zero (fun t ht => pkG_same_zero hL t ?_)
    obtain ⟨h1, h2⟩ := mem_filter.1 ht
    exact pkG_mem_same.2 ⟨h1, by omega⟩
  have h1 : ∑ t ∈ oddSideSplit N (i, j) ∪ evenSideSplit N (i, j), mesh N X t.1 t.2 = 0 := by
    refine sum_eq_zero (fun t ht => ?_)
    obtain ⟨a, b⟩ := t
    have hd := hHsub ht
    have hd' := mem_diagonals.1 hd
    dsimp only at hd' ⊢
    by_cases hp : a % 2 = b % 2
    · exact pkG_same_zero hL (a, b) (pkG_mem_same.2 ⟨hd, hp⟩)
    · have hΨ := pkL_H_to hPo (by omega) ht
      have hm := pkL_Psi_minRect hi1 hjN hd'.1 (by omega) hd'.2.1 hp hΨ
      have hS : (a, b) ∈ S := by
        by_contra hnS
        have hmis : (a, b) ∈ missing N S := by
          change (a, b) ∈ diagonals N \ S
          exact mem_sdiff.2 ⟨hd, hnS⟩
        exact disjoint_left.1 hdisj hm hmis
      exact hL (a, b) (mem_union_left _ hS)
  rw [h1, h2]
  ring

/-- **Other chords do not vanish**: an odd chord that is not clean is `2` at some point of
`L_{S ∪ same}`. -/
theorem pkG_G1_wit {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} (hS : S ⊆ diagonals N)
    {P : ℕ × ℕ} (hPo : P ∈ oddDiagonals N) (hnc : P ∉ cleanChords N S) :
    ∃ X : ℕ × ℕ → ℚ, OnLocus N (S ∪ pkGSame N) X ∧ X P = 2 := by
  obtain ⟨i, j⟩ := P
  obtain ⟨hi1, hjN, hij, hne, hodd⟩ := pkL_oddD hPo
  have hnd : ¬ Disjoint (minRect N (i, j)) (missing N S) := by
    intro h
    apply hnc
    change (i, j) ∈ (oddDiagonals N).filter (fun P => Disjoint (minRect N P) (missing N S))
    exact mem_filter.2 ⟨hPo, h⟩
  obtain ⟨t, htm, htmis⟩ := not_disjoint_iff.1 hnd
  obtain ⟨a, b⟩ := t
  have hmis : (a, b) ∈ diagonals N \ S := htmis
  obtain ⟨hd, hnS⟩ := mem_sdiff.1 hmis
  have hd' := mem_diagonals.1 hd
  dsimp only at hd'
  obtain ⟨hmix, hΨ⟩ := pkL_minRect_Psi hi1 hjN htm
  have hS' : S ∪ pkGSame N ⊆ diagonals N := union_subset hS (fun t ht => (pkG_mem_same.1 ht).1)
  have hnS' : (a, b) ∉ S ∪ pkGSame N := by
    intro h
    rcases mem_union.1 h with h | h
    · exact hnS h
    · exact hmix (pkG_mem_same.1 h).2
  obtain ⟨X, hL, hX⟩ := pkL_gA hN hE hS' hd hnS' hmix
  have hH := pkL_H_of hE hPo hd'.1 hd'.2.2.1 hd'.2.1 hd'.2.2.2 hΨ
  refine ⟨X, hL, ?_⟩
  rw [hX (i, j) hPo, ite_eq_left hH]

/-- The mesh variables at the Gram point `p3bXs (pkLSB e1 e2 o1 o2)` of `pkL_gB` (`C0`): `−2` on
the pairs `(e1, e2)` and `(o1, o2)`, `0` on the other diagonals; in `pkL_gB` they are only a local
`have`. -/
theorem pkG_gB_mesh {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {e1 e2 o1 o2 : ℕ}
    (he : (e1, e2) ∈ diagonals N) (ho : (o1, o2) ∈ diagonals N) (hee : e1 % 2 = 0 ∧ e2 % 2 = 0)
    (hoo : o1 % 2 = 1 ∧ o2 % 2 = 1) :
    ∀ t ∈ diagonals N, mesh N (p3bXs (pkLSB e1 e2 o1 o2)) t.1 t.2 =
      (if t = (e1, e2) then -2 else 0) + (if t = (o1, o2) then -2 else 0) := by
  have hd1 := mem_diagonals.1 he
  have hd2 := mem_diagonals.1 ho
  dsimp only at hd1 hd2
  have hsym : ∀ x y, pkLSB e1 e2 o1 o2 x y = pkLSB e1 e2 o1 o2 y x := fun x y => by
    rw [pkLSB, pkLSB, pkL_path_symm (min e1 o1), pkL_path_symm (min e2 o2), p3b_e_symm e1,
        p3b_e_symm o1]
  have hdiag : ∀ x, pkLSB e1 e2 o1 o2 x x = 0 := fun x => by
    rw [pkLSB, pkL_path_diag, pkL_path_diag, p3b_e_diag (by omega), p3b_e_diag (by omega)]
    ring
  have hrow : ∀ x ∈ Icc 1 N, ∑ y ∈ Icc 1 N, pkLSB e1 e2 o1 o2 x y = 0 := fun x hx => by
    have e : ∀ y ∈ Icc 1 N, pkLSB e1 e2 o1 o2 x y = p3bE e1 e2 x y + p3bE o1 o2 x y -
        pkLPath (min e1 o1) (max e1 o1) x y - pkLPath (min e2 o2) (max e2 o2) x y :=
            fun y _ => rfl
    rw [sum_congr rfl e, sum_sub_distrib, sum_sub_distrib, sum_add_distrib,
      p3b_e_row (mem_Icc.2 ⟨by omega, by omega⟩) (mem_Icc.2 ⟨by omega, by omega⟩),
      p3b_e_row (mem_Icc.2 ⟨by omega, by omega⟩) (mem_Icc.2 ⟨by omega, by omega⟩),
      pkL_path_row' (by omega) (by omega) (by omega) (by omega) (by omega) hx,
      pkL_path_row' (by omega) (by omega) (by omega) (by omega) (by omega) hx]
    ring
  intro t ht
  obtain ⟨a, b⟩ := t
  have h' := mem_diagonals.1 ht
  dsimp only at h' ⊢
  rw [p3b_mesh_Xs (by omega) hsym hdiag hrow (by omega) (by omega) (by omega), pkLSB,
    pkL_path_far (by omega), pkL_path_far (by omega), pkL_e_far (by omega) (by omega),
    pkL_e_far (by omega) (by omega)]
  split_ifs <;> norm_num

theorem pkG_isGSet_iff {N : ℕ} {G : Finset ℕ} :
    IsGSet N G ↔ (IsSameParitySet N G ∨ IsMixedAnchor N G) := Iff.rfl
theorem pkG_isSP_iff {N : ℕ} {G : Finset ℕ} :
    IsSameParitySet N G ↔ (Admissible N 0 G ∨ Admissible N 1 G) := Iff.rfl
theorem pkG_adm_iff {N r : ℕ} {G : Finset ℕ} :
    Admissible N r G ↔ (G ⊆ Icc 1 N ∧ 2 ≤ G.card ∧ ∀ t ∈ G, t % 2 = r) := Iff.rfl
theorem pkG_cgm_iff {N : ℕ} {S : Finset (ℕ × ℕ)} :
    ContainsGMember N S ↔ ∃ Z ∈ gFamily N, Z ⊆ S := Iff.rfl

/-- A missing pair of the parity class *not* in a same-parity leg set `G = {legs of parity r}`
(`N ≥ 4`): if `S` contains no member of `𝒢_N`, some diagonal with both legs of parity `1 − r` is not
in `S`. -/
theorem pkG_miss_class {N : ℕ} (hN : 4 ≤ N) {S : Finset (ℕ × ℕ)} (hG : ¬ ContainsGMember N S)
    (r : ℕ) (hr : r < 2) :
    ∃ a b : ℕ, (a, b) ∈ diagonals N ∧ (a, b) ∉ S ∧ a % 2 ≠ r ∧ b % 2 ≠ r := by
  have hsub : (Icc 1 N).filter (fun a => a % 2 = r) ⊆ Icc 1 N := filter_subset _ _
  have hcard : 2 ≤ ((Icc 1 N).filter (fun a => a % 2 = r)).card := by
    have h2 : ({2 - r, 4 - r} : Finset ℕ) ⊆ (Icc 1 N).filter (fun a => a % 2 = r) := by
      intro x hx
      rcases mem_insert.1 hx with h | h
      · rw [h]
        exact mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩
      · rw [mem_singleton.1 h]
        exact mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩
    have c := card_le_card h2
    rw [card_pair (by omega)] at c
    exact c
  have hadm : Admissible N r ((Icc 1 N).filter (fun a => a % 2 = r)) :=
    pkG_adm_iff.2 ⟨hsub, hcard, fun t ht => (mem_filter.1 ht).2⟩
  have hSP : IsSameParitySet N ((Icc 1 N).filter (fun a => a % 2 = r)) := by
    rw [pkG_isSP_iff]
    rcases (show r = 0 ∨ r = 1 by omega) with h | h
    · subst h
      exact Or.inl hadm
    · subst h
      exact Or.inr hadm
  have hZ : sepPairs N ((Icc 1 N).filter (fun a => a % 2 = r)) ∈ gFamily N := by
    change _ ∈ (gLegSets N).image (sepPairs N)
    refine mem_image.2 ⟨_, ?_, rfl⟩
    change _ ∈ (Icc 1 N).powerset.filter (IsGSet N)
    exact mem_filter.2 ⟨mem_powerset.2 hsub, pkG_isGSet_iff.2 (Or.inl hSP)⟩
  have hns : ¬ sepPairs N ((Icc 1 N).filter (fun a => a % 2 = r)) ⊆ S :=
      fun h => hG (pkG_cgm_iff.2 ⟨_, hZ, h⟩)
  obtain ⟨t, ht, htS⟩ := not_subset.1 hns
  obtain ⟨a, b⟩ := t
  have ht' : (a, b) ∈ (diagonals N).filter (fun p =>
      InST ((Icc 1 N).filter (fun a => a % 2 = r)) p.1 p.2) := ht
  obtain ⟨hd, hst⟩ := mem_filter.1 ht'
  obtain ⟨ha, hb, -, -⟩ := hst
  have hd' := mem_diagonals.1 hd
  dsimp only at hd'
  refine ⟨a, b, hd, htS, fun h => ha (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, h⟩),
    fun h => hb (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, h⟩)⟩

/-- **A point where `E` is not zero**: on `L_S` with `S ∈ F^π`, `E` is not identically zero (value
`−2` at the Gram point of `pkL_gB`, `C0`). -/
theorem pkG_Ewit {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} (hF : InFpi N S) :
    ∃ X : ℕ × ℕ → ℚ, OnLocus N S X ∧ pkGE N X = -2 := by
  obtain ⟨hS, -, hG⟩ := hF
  obtain ⟨e1, e2, he, heS, he1, he2⟩ := pkG_miss_class hN hG 1 (by omega)
  obtain ⟨o1, o2, ho, hoS, ho1, ho2⟩ := pkG_miss_class hN hG 0 (by omega)
  have hm := pkG_gB_mesh hN hE he ho ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  refine ⟨p3bXs (pkLSB e1 e2 o1 o2), fun t ht => ?_, ?_⟩
  · rw [hm t (hS ht), ite_eq_right (fun e : t = (e1, e2) => heS (e ▸ ht)),
      ite_eq_right (fun e : t = (o1, o2) => hoS (e ▸ ht))]
    norm_num
  · have eE : pkGE N (p3bXs (pkLSB e1 e2 o1 o2)) =
      ∑ t ∈ (diagonals N).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0),
        mesh N (p3bXs (pkLSB e1 e2 o1 o2)) t.1 t.2 := rfl
    rw [eE, sum_congr rfl (fun t ht => hm t (mem_filter.1 ht).1), sum_add_distrib, sum_ite_eq',
        sum_ite_eq',
        ite_eq_left (mem_filter.2 ⟨he, by omega, by omega⟩),
      ite_eq_right (fun h => by have := (mem_filter.1 h).2; dsimp only at this; omega)]
    ring

/-- The mesh variables are linear in `X`. -/
theorem pkG_mesh_lin (N : ℕ) (X Y : ℕ × ℕ → ℚ) (t : ℚ) (a b : ℕ) :
    mesh N (fun e => X e + t * Y e) a b = mesh N X a b + t * mesh N Y a b := by
  rw [pkL_mesh_eq N (fun e => X e + t * Y e), pkL_mesh_eq N X, pkL_mesh_eq N Y]
  simp only [pkBr_planar_lin]
  ring

theorem pkG_E_lin (N : ℕ) (X Y : ℕ × ℕ → ℚ) (t : ℚ) :
    pkGE N (fun e => X e + t * Y e) = pkGE N X + t * pkGE N Y := by
  have e : ∀ Z : ℕ × ℕ → ℚ, pkGE N Z =
      ∑ u ∈ (diagonals N).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0), mesh N Z u.1 u.2 :=
          fun Z => rfl
  rw [e, e, e, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl (fun u _ => pkG_mesh_lin N X Y t u.1 u.2)

/-- **Avoidance**: finitely many linear functions, each non-zero somewhere on a linearly closed set
`L`, are simultaneously non-zero at one point of `L` (ℚ is infinite; the pattern of
`pkBr_pt_of_nondeg`, `C0`). -/
theorem pkG_avoid {ι : Type*} {L : (ℕ × ℕ → ℚ) → Prop} (h0 : L (fun _ => 0))
    (hlin : ∀ X Y : ℕ × ℕ → ℚ, L X → L Y → ∀ t : ℚ, L (fun e => X e + t * Y e))
    (f : ι → (ℕ × ℕ → ℚ) → ℚ) (hf : ∀ i X Y t, f i (fun e => X e + t * Y e) = f i X + t * f i Y) :
    ∀ F : Finset ι, (∀ i ∈ F, ∃ X, L X ∧ f i X ≠ 0) → ∃ X, L X ∧ ∀ i ∈ F, f i X ≠ 0 := by
  classical
  intro F
  induction F using Finset.induction_on with
  | empty => exact fun _ => ⟨fun _ => 0, h0, by simp⟩
  | insert d D hdD ih =>
    intro hex
    obtain ⟨X, hXL, hXD⟩ := ih (fun i hi => hex i (mem_insert_of_mem hi))
    obtain ⟨Y, hYL, hYd⟩ := hex d (mem_insert_self d D)
    obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset ((insert d D).image (fun e => -f e X / f e Y))
    have key : ∀ e ∈ insert d D, f e X + t * f e Y = 0 → f e Y = 0 := by
      intro e he h0'
      by_contra hY
      apply ht
      rw [mem_image]
      refine ⟨e, he, ?_⟩
      field_simp
      linear_combination -h0'
    refine ⟨fun e => X e + t * Y e, hlin X Y hXL hYL t, ?_⟩
    intro e he h0'
    rw [hf] at h0'
    have hY0 := key e he h0'
    rcases mem_insert.1 he with rfl | he'
    · exact hYd hY0
    · apply hXD e he'
      simpa [hY0] using h0'

/-- **Avoidance on a locus**: `L = L_S` (closed under lines by `pkBr_onLocus_lin`, `C0`). -/
theorem pkG_avoid_locus {ι : Type*} {N : ℕ} {S : Finset (ℕ × ℕ)} (f : ι → (ℕ × ℕ → ℚ) → ℚ)
    (hf : ∀ i X Y t, f i (fun e => X e + t * Y e) = f i X + t * f i Y) (F : Finset ι)
    (hex : ∀ i ∈ F, ∃ X, OnLocus N S X ∧ f i X ≠ 0) : ∃ X, OnLocus N S X ∧ ∀ i ∈ F, f i X ≠ 0 :=
  pkG_avoid (pkBr_onLocus_zero N S) (fun _X _Y hX hY t => pkBr_onLocus_lin hX hY t) f hf F hex

/-! ### Helpers of the proof of the germ input (prefix `pkG_`): splitting a dissection

Pointwise over ℚ: the two child relabellings (inside: shift `pkGSh`; outside: contraction
`pkGCt`, with the collapse `pkGCl` and its fibres `pkGFib` on legs) and the face transport
through the split (`pkGGlue`, `pkGSplit`). The section continues in `C5` with the Cayley
numerator `pkGNum` (a sum over the dissections by odd chords), the residue `pkG_num_res`, and the
polynomial twin `pkGCP` with `pkG_CP_eval`, `pkG_CP_hom` and `pkG_CP_res`. -/

/-- Inside-child relabelling `k ↦ k + a − 1`. -/
def pkGSh (a k : ℕ) : ℕ := k + a - 1

/-- Outside-child (contraction) relabelling: `k ↦ k` for `k ≤ a`, `k ↦ k + (b − a − 1)` for
`k > a`. -/
def pkGCt (a b k : ℕ) : ℕ := if k ≤ a then k else k + (b - a - 1)

/-- The inside relabelling on chords. -/
def pkGShP (a : ℕ) (d : ℕ × ℕ) : ℕ × ℕ := (pkGSh a d.1, pkGSh a d.2)
/-- The outside relabelling (contraction) on chords. -/
def pkGCtP (a b : ℕ) (d : ℕ × ℕ) : ℕ × ℕ := (pkGCt a b d.1, pkGCt a b d.2)

/-- Collapse of parent legs onto outside-child legs: the block `[a, b − 1]` goes to leg `a`. -/
def pkGCl (a b x : ℕ) : ℕ := if x < a then x else if x < b then a else x - (b - a - 1)

/-- Fibre of the collapse over the child leg `i`. -/
def pkGFib (a b i : ℕ) : Finset ℕ := if i = a then Ico a b else {pkGCt a b i}

theorem pkG_sh_eq (a k : ℕ) : pkGSh a k = k + a - 1 := rfl
theorem pkG_ct_eq (a b k : ℕ) : pkGCt a b k = if k ≤ a then k else k + (b - a - 1) := rfl
theorem pkG_shP_eq (a : ℕ) (d : ℕ × ℕ) : pkGShP a d = (pkGSh a d.1, pkGSh a d.2) := rfl
theorem pkG_ctP_eq (a b : ℕ) (d : ℕ × ℕ) : pkGCtP a b d = (pkGCt a b d.1, pkGCt a b d.2) := rfl

/-- The two cases of the contraction. -/
theorem pkG_ct_cases (a b k : ℕ) :
    (k ≤ a ∧ pkGCt a b k = k) ∨ (a < k ∧ pkGCt a b k = k + (b - a - 1)) := by
  rw [pkG_ct_eq]
  by_cases h : k ≤ a
  · exact Or.inl ⟨h, ite_eq_left h⟩
  · exact Or.inr ⟨by omega, ite_eq_right h⟩

/-- The three cases of the collapse. -/
theorem pkG_cl_cases (a b x : ℕ) : (x < a ∧ pkGCl a b x = x) ∨ (a ≤ x ∧ x < b ∧ pkGCl a b x = a) ∨
    (b ≤ x ∧ pkGCl a b x = x - (b - a - 1)) := by
  have e : pkGCl a b x = if x < a then x else if x < b then a else x - (b - a - 1) := rfl
  rw [e]
  by_cases h1 : x < a
  · exact Or.inl ⟨h1, ite_eq_left h1⟩
  · rw [ite_eq_right h1]
    by_cases h2 : x < b
    · exact Or.inr (Or.inl ⟨by omega, h2, ite_eq_left h2⟩)
    · exact Or.inr (Or.inr ⟨by omega, ite_eq_right h2⟩)

/-- Membership in a fibre: `x ∈ fib i ↔ cl x = i`. -/
theorem pkG_mem_fib {a b : ℕ} (hab : a < b) (i x : ℕ) : x ∈ pkGFib a b i ↔ pkGCl a b x = i := by
  have e : pkGFib a b i = if i = a then Ico a b else {pkGCt a b i} := rfl
  rw [e]
  by_cases hi : i = a
  · rw [ite_eq_left hi, mem_Ico]
    rcases pkG_cl_cases a b x with h | h | h <;> omega
  · rw [ite_eq_right hi, mem_singleton]
    rcases pkG_cl_cases a b x with h | h | h <;> rcases pkG_ct_cases a b i with k | k <;> omega

/-- Contraction and collapse: `ct w ≤ x ↔ w ≤ cl x`. -/
theorem pkG_ct_le_iff {a b : ℕ} (hab : a < b) (w x : ℕ) : pkGCt a b w ≤ x ↔ w ≤ pkGCl a b x := by
  rcases pkG_cl_cases a b x with h | h | h <;> rcases pkG_ct_cases a b w with k | k <;> omega

/-- A telescoping sum of mesh variables over a block of legs. -/
theorem pkG_mesh_tel0 {N : ℕ} (y : ℕ × ℕ → ℚ) (a v : ℕ) : ∀ n : ℕ,
    ∑ u ∈ Ico a (a + n), mesh N y u v =
      planar N y a v + planar N y (a + n)
          (v + 1) - planar N y a (v + 1) - planar N y (a + n) v := by
  intro n
  induction n with
  | zero =>
    simp only [add_zero, Ico_self, sum_empty]
    ring
  | succ n ih =>
    rw [show a + (n + 1) = (a + n) + 1 by omega, sum_Ico_succ_top (by omega), ih, pkL_mesh_eq]
    ring

theorem pkG_mesh_tel {N : ℕ} (y : ℕ × ℕ → ℚ) {a b : ℕ} (hab : a ≤ b) (v : ℕ) :
    ∑ u ∈ Ico a b, mesh N y u v =
      planar N y a v + planar N y b (v + 1) - planar N y a (v + 1) - planar N y b v := by
  obtain ⟨n, rfl⟩ : ∃ n, b = a + n := ⟨b - a, by omega⟩
  exact pkG_mesh_tel0 y a v n

/-- `planar` on labels `1 ≤ u ≤ v ≤ n`. -/
theorem pkG_pl_le {n : ℕ} (X : ℕ × ℕ → ℚ) {u v : ℕ} (h1 : 1 ≤ u) (h2 : u ≤ v) (h3 : v ≤ n) :
    planar n X u v = if (u, v) ∈ diagonals n then X (u, v) else 0 := by
  have e : planar n X u v = if (min (vtx n u) (vtx n v), max (vtx n u) (vtx n v)) ∈ diagonals n then
      X (min (vtx n u) (vtx n v), max (vtx n u) (vtx n v)) else 0 := rfl
  rw [e, vtx_of_mem h1 (by omega), vtx_of_mem (by omega) h3, min_eq_left h2, max_eq_right h2]

/-- **Planar variables of the inside child**, ordered labels: for `y` with `y (a, b) = 0`, a planar
variable of the inside child (size `b − a + 1`, variables pulled back by `pkGShP a`) is the
parent's at the shifted labels. -/
theorem pkG_pl_sh_le {N a b : ℕ} (ha : 1 ≤ a) (hb : b ≤ N) (hab : a + 3 ≤ b) (y : ℕ × ℕ → ℚ)
    (hy : y (a, b) = 0) {u v : ℕ} (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ b - a + 1) :
    planar (b - a + 1) (fun d => y (pkGShP a d)) u v = planar N y (pkGSh a u) (pkGSh a v) := by
  have g1 : 1 ≤ u + a - 1 := by omega
  have g2 : u + a - 1 ≤ v + a - 1 := by omega
  have g3 : v + a - 1 ≤ N := by omega
  rw [pkG_sh_eq, pkG_sh_eq, pkG_pl_le _ hu huv hv, pkG_pl_le y g1 g2 g3]
  by_cases h1 : (u, v) ∈ diagonals (b - a + 1)
  · have h1' := mem_diagonals.1 h1
    dsimp only at h1'
    rw [ite_eq_left h1, ite_eq_left (mem_diagonals.2 (by dsimp only; omega))]
    rfl
  · rw [ite_eq_right h1]
    by_cases h2 : (u + a - 1, v + a - 1) ∈ diagonals N
    · have h2' := mem_diagonals.1 h2
      dsimp only at h2'
      rw [ite_eq_left h2]
      have hne : ¬ (1 ≤ u ∧ v ≤ b - a + 1 ∧ u + 2 ≤ v ∧ ¬ (u = 1 ∧ v = b - a + 1)) :=
        fun q => h1 (mem_diagonals.2 q)
      have e : (u + a - 1, v + a - 1) = (a, b) := Prod.ext (by dsimp only; omega)
          (by dsimp only; omega)
      rw [e, hy]
    · rw [ite_eq_right h2]

/-- **Planar variables of the inside child**: `pkG_pl_sh_le` for labels in either order. -/
theorem pkG_pl_sh {N a b : ℕ} (ha : 1 ≤ a) (hb : b ≤ N) (hab : a + 3 ≤ b) (y : ℕ × ℕ → ℚ)
    (hy : y (a, b) = 0) {u v : ℕ} (hu : 1 ≤ u) (hv : 1 ≤ v) (hu' : u ≤ b - a + 1)
    (hv' : v ≤ b - a + 1) :
    planar (b - a + 1) (fun d => y (pkGShP a d)) u v = planar N y (pkGSh a u) (pkGSh a v) := by
  rcases le_total u v with h | h
  · exact pkG_pl_sh_le ha hb hab y hy hu h hv'
  · rw [PionCompleteness.ChainSlice.planar_comm _ _ u v,
      PionCompleteness.ChainSlice.planar_comm N y (pkGSh a u) (pkGSh a v)]
    exact pkG_pl_sh_le ha hb hab y hy hv h hu'

/-- **Mesh variables of the inside child**: for `y` with `y (a, b) = 0`, the mesh variables of the
inside child (of size `b − a + 1`) on its legs `1..b − a` are the parent's at the shifted legs. -/
theorem pkG_mesh_sh {N a b : ℕ} (ha : 1 ≤ a) (hb : b ≤ N) (hab : a + 3 ≤ b) (y : ℕ × ℕ → ℚ)
    (hy : y (a, b) = 0) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) (hi' : i + 1 ≤ b - a + 1)
    (hj' : j + 1 ≤ b - a + 1) :
    mesh (b - a + 1) (fun d => y (pkGShP a d)) i j = mesh N y (pkGSh a i) (pkGSh a j) := by
  rw [pkL_mesh_eq, pkL_mesh_eq, pkG_pl_sh ha hb hab y hy hi hj (by omega) (by omega),
    pkG_pl_sh ha hb hab y hy (u := i + 1) (v := j + 1) (by omega) (by omega) hi' hj',
    pkG_pl_sh ha hb hab y hy (u := i) (v := j + 1) hi (by omega) (by omega) hj',
    pkG_pl_sh ha hb hab y hy (u := i + 1) (v := j) (by omega) hj hi' (by omega)]
  have e1 : pkGSh a (i + 1) = pkGSh a i + 1 := by rw [pkG_sh_eq, pkG_sh_eq]; omega
  have e2 : pkGSh a (j + 1) = pkGSh a j + 1 := by rw [pkG_sh_eq, pkG_sh_eq]; omega
  rw [e1, e2]

/-- **Planar variables of the outside child**, ordered labels: for `y` with `y (a, b) = 0`, a planar
variable of the outside child (size `N − (b − a) + 1`, variables pulled back by `pkGCtP a b`) is
the parent's at the contracted labels. -/
theorem pkG_pl_ct_le {N a b : ℕ} (ha : 1 ≤ a) (hb : b ≤ N) (hab : a + 3 ≤ b) (y : ℕ × ℕ → ℚ)
    (hy : y (a, b) = 0) {u v : ℕ} (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ N - (b - a) + 1) :
    planar (N - (b - a) + 1) (fun d => y (pkGCtP a b d)) u v = planar N y (pkGCt a b u)
        (pkGCt a b v) := by
  have ku := pkG_ct_cases a b u
  have kv := pkG_ct_cases a b v
  have g1 : 1 ≤ pkGCt a b u := by omega
  have g2 : pkGCt a b u ≤ pkGCt a b v := by omega
  have g3 : pkGCt a b v ≤ N := by omega
  rw [pkG_pl_le _ hu huv hv, pkG_pl_le y g1 g2 g3]
  change (if (u, v) ∈ diagonals (N - (b - a) + 1) then y (pkGCt a b u, pkGCt a b v) else 0) =
    if (pkGCt a b u, pkGCt a b v) ∈ diagonals N then y (pkGCt a b u, pkGCt a b v) else 0
  by_cases h1 : (u, v) ∈ diagonals (N - (b - a) + 1)
  · have h1' := mem_diagonals.1 h1
    dsimp only at h1'
    rw [ite_eq_left h1, ite_eq_left (mem_diagonals.2 (by dsimp only; omega))]
  · rw [ite_eq_right h1]
    by_cases h2 : (pkGCt a b u, pkGCt a b v) ∈ diagonals N
    · have h2' := mem_diagonals.1 h2
      dsimp only at h2'
      rw [ite_eq_left h2]
      have hne : ¬ (1 ≤ u ∧ v ≤ N - (b - a) + 1 ∧ u + 2 ≤ v ∧ ¬ (u = 1 ∧ v = N - (b - a) + 1)) :=
        fun q => h1 (mem_diagonals.2 q)
      have e : (pkGCt a b u, pkGCt a b v) = (a, b) := Prod.ext (by dsimp only; omega)
          (by dsimp only; omega)
      rw [e, hy]
    · rw [ite_eq_right h2]

/-- **Planar variables of the outside child**: `pkG_pl_ct_le` for labels in either order. -/
theorem pkG_pl_ct {N a b : ℕ} (ha : 1 ≤ a) (hb : b ≤ N) (hab : a + 3 ≤ b) (y : ℕ × ℕ → ℚ)
    (hy : y (a, b) = 0) {u v : ℕ} (hu : 1 ≤ u) (hv : 1 ≤ v) (hu' : u ≤ N - (b - a) + 1)
    (hv' : v ≤ N - (b - a) + 1) :
    planar (N - (b - a) + 1) (fun d => y (pkGCtP a b d)) u v = planar N y (pkGCt a b u)
        (pkGCt a b v) := by
  rcases le_total u v with h | h
  · exact pkG_pl_ct_le ha hb hab y hy hu h hv'
  · rw [PionCompleteness.ChainSlice.planar_comm _ _ u v,
      PionCompleteness.ChainSlice.planar_comm N y (pkGCt a b u) (pkGCt a b v)]
    exact pkG_pl_ct_le ha hb hab y hy hv h hu'

/-- The contraction moves a leg `≠ a` by a constant. -/
theorem pkG_ct_succ {a b i : ℕ} (hi : i ≠ a) : pkGCt a b (i + 1) = pkGCt a b i + 1 := by
  rcases pkG_ct_cases a b i with k | k <;> rcases pkG_ct_cases a b (i + 1) with k' | k' <;> omega

/-- **Mesh variables of the outside child**, legs `≠ a`: for `y` with `y (a, b) = 0`, they are the
parent's at the contracted legs. -/
theorem pkG_mesh_ct {N a b : ℕ} (ha : 1 ≤ a) (hb : b ≤ N) (hab : a + 3 ≤ b) (y : ℕ × ℕ → ℚ)
    (hy : y (a, b) = 0) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) (hi' : i + 1 ≤ N - (b - a) + 1)
    (hj' : j + 1 ≤ N - (b - a) + 1) (hia : i ≠ a) (hja : j ≠ a) :
    mesh (N - (b - a) + 1) (fun d => y (pkGCtP a b d)) i j = mesh N y (pkGCt a b i)
        (pkGCt a b j) := by
  rw [pkL_mesh_eq, pkL_mesh_eq, pkG_pl_ct ha hb hab y hy hi hj (by omega) (by omega),
    pkG_pl_ct ha hb hab y hy (u := i + 1) (v := j + 1) (by omega) (by omega) hi' hj',
    pkG_pl_ct ha hb hab y hy (u := i) (v := j + 1) hi (by omega) (by omega) hj',
    pkG_pl_ct ha hb hab y hy (u := i + 1) (v := j) (by omega) hj hi' (by omega),
    pkG_ct_succ hia, pkG_ct_succ hja]

/-- **The collapsed leg `a` against a leg `j ≠ a`**: the block sum telescopes to one child mesh
variable. -/
theorem pkG_mesh_blk {N a b : ℕ} (ha : 1 ≤ a) (hb : b ≤ N) (hab : a + 3 ≤ b) (y : ℕ × ℕ → ℚ)
    (hy : y (a, b) = 0) {j : ℕ} (hj : 1 ≤ j) (hj' : j + 1 ≤ N - (b - a) + 1) (hja : j ≠ a) :
    ∑ u ∈ Ico a b, mesh N y u (pkGCt a b j) = mesh (N - (b - a) + 1)
        (fun d => y (pkGCtP a b d)) a j := by
  have ca : pkGCt a b a = a := by rw [pkG_ct_eq, ite_eq_left (le_refl a)]
  have ca1 : pkGCt a b (a + 1) = b := by rw [pkG_ct_eq, ite_eq_right (by omega)]; omega
  rw [pkG_mesh_tel (N := N) y (a := a) (b := b) (by omega), pkL_mesh_eq,
      pkG_pl_ct ha hb hab y hy (u := a) (v := j) ha hj (by omega) (by omega),
      pkG_pl_ct ha hb hab y hy (u := a + 1) (v := j + 1) (by omega) (by omega) (by omega) hj',
    pkG_pl_ct ha hb hab y hy (u := a) (v := j + 1) ha (by omega) (by omega) hj',
    pkG_pl_ct ha hb hab y hy (u := a + 1) (v := j) (by omega) hj (by omega) (by omega),
    pkG_ct_succ hja, ca, ca1]

/-- **Fibre sums**: the mesh sum over the fibres of two child legs is the child mesh variable. -/
theorem pkG_fib_mesh {N a b : ℕ} (hN : 4 ≤ N) (ha : 1 ≤ a) (hb : b ≤ N) (hab : a + 3 ≤ b)
    (hC : ¬ (a = 1 ∧ b = N)) (y : ℕ × ℕ → ℚ) (hy : y (a, b) = 0) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hi' : i + 1 ≤ N - (b - a) + 1) (hj' : j + 1 ≤ N - (b - a) + 1) :
    ∑ u ∈ pkGFib a b i, ∑ v ∈ pkGFib a b j, mesh N y u v =
      mesh (N - (b - a) + 1) (fun d => y (pkGCtP a b d)) i j := by
  have ef : ∀ k, pkGFib a b k = if k = a then Ico a b else {pkGCt a b k} := fun k => rfl
  by_cases hia : i = a
  · by_cases hja : j = a
    · -- both collapsed: `F(block, block) = −2 Q_block = −2 X_C = 0`
      rw [ef i, ef j, ite_eq_left hia, ite_eq_left hja, hia, hja,
          pkL_mesh_self (N := N - (b - a) + 1) (by omega)]
      have hd : (a, b) ∈ diagonals N := mem_diagonals.2 (by dsimp only; omega)
      have h1 := pkG_S1 (by omega) y hd
      have h2 := pkG_Q_F (N := N) (by omega) y (Ico a b)
      have e3 : pkGF (pkGM N y) (Ico a b) (Ico a b) = ∑ u ∈ Ico a b, ∑ v ∈ Ico a b,
          mesh N y u v := rfl
      rw [← e3]
      rw [hy] at h1
      rw [← h1] at h2
      linarith
    · rw [ef i, ite_eq_left hia, ef j, ite_eq_right hja]
      simp only [sum_singleton]
      rw [hia]
      exact pkG_mesh_blk ha hb hab y hy hj hj' hja
  · by_cases hja : j = a
    · rw [ef i, ite_eq_right hia, ef j, ite_eq_left hja, sum_singleton, hja,
        pkL_mesh_comm (N - (b - a) + 1) _ i a, ← pkG_mesh_blk ha hb hab y hy hi hi' hia]
      exact sum_congr rfl (fun u _ => pkL_mesh_comm N y _ _)
    · rw [ef i, ite_eq_right hia, ef j, ite_eq_right hja, sum_singleton, sum_singleton]
      exact (pkG_mesh_ct ha hb hab y hy hi hj hi' hj' hia hja).symm

/-- **Vertex forms of the outside child**: `Q` of a union of fibres is the child `Q`. -/
theorem pkG_Q_fib {N a b : ℕ} (hN : 4 ≤ N) (ha : 1 ≤ a) (hb : b ≤ N) (hab : a + 3 ≤ b)
    (hC : ¬ (a = 1 ∧ b = N)) (y : ℕ × ℕ → ℚ) (hy : y (a, b) = 0) (W : Finset ℕ)
    (hW : ∀ i ∈ W, 1 ≤ i ∧ i + 1 ≤ N - (b - a) + 1) :
    pkGQ N y (W.biUnion (pkGFib a b)) = pkGQ (N - (b - a) + 1)
        (fun d => y (pkGCtP a b d)) W := by
  have hpd : (W : Set ℕ).PairwiseDisjoint (pkGFib a b) := by
    intro i _ j _ hij
    change Disjoint (pkGFib a b i) (pkGFib a b j)
    rw [disjoint_left]
    intro x hx hx'
    rw [pkG_mem_fib (by omega)] at hx hx'
    exact hij (hx.symm.trans hx')
  have h1 := pkG_Q_F (N := N) (by omega) y (W.biUnion (pkGFib a b))
  have h2 := pkG_Q_F (N := N - (b - a) + 1) (by omega) (fun d => y (pkGCtP a b d)) W
  have hF : pkGF (pkGM N y) (W.biUnion (pkGFib a b)) (W.biUnion (pkGFib a b)) =
      pkGF (pkGM (N - (b - a) + 1) (fun d => y (pkGCtP a b d))) W W := by
    have e1 : pkGF (pkGM N y) (W.biUnion (pkGFib a b)) (W.biUnion (pkGFib a b)) =
        ∑ u ∈ W.biUnion (pkGFib a b), ∑ v ∈ W.biUnion (pkGFib a b), mesh N y u v := rfl
    have e2 : pkGF (pkGM (N - (b - a) + 1) (fun d => y (pkGCtP a b d))) W W =
        ∑ i ∈ W, ∑ j ∈ W, mesh (N - (b - a) + 1) (fun d => y (pkGCtP a b d)) i j := rfl
    rw [e1, e2, sum_biUnion hpd]
    refine sum_congr rfl (fun i hi => ?_)
    have e3 : ∀ u, ∑ v ∈ W.biUnion (pkGFib a b), mesh N y u v = ∑ j ∈ W, ∑ v ∈ pkGFib a b j,
        mesh N y u v :=
      fun u => sum_biUnion hpd
    rw [sum_congr rfl (fun u _ => e3 u), sum_comm]
    refine sum_congr rfl (fun j hj => ?_)
    exact pkG_fib_mesh hN ha hb hab hC y hy (hW i hi).1 (hW j hj).1 (hW i hi).2 (hW j hj).2
  linarith

/-- **Vertex forms of the inside child**: `Q` of a shifted leg set is the child `Q`. -/
theorem pkG_Q_sh {N a b : ℕ} (hN : 4 ≤ N) (ha : 1 ≤ a) (hb : b ≤ N) (hab : a + 3 ≤ b)
    (y : ℕ × ℕ → ℚ) (hy : y (a, b) = 0) (W : Finset ℕ) (hW : ∀ i ∈ W, 1 ≤ i ∧ i + 1 ≤ b - a + 1) :
    pkGQ N y (W.image (pkGSh a)) = pkGQ (b - a + 1) (fun d => y (pkGShP a d)) W := by
  have hinj : Set.InjOn (pkGSh a) (W : Set ℕ) := by
    intro x _ x' _ e
    rw [pkG_sh_eq, pkG_sh_eq] at e
    omega
  have h1 := pkG_Q_F (N := N) (by omega) y (W.image (pkGSh a))
  have h2 := pkG_Q_F (N := b - a + 1) (by omega) (fun d => y (pkGShP a d)) W
  have hF : pkGF (pkGM N y) (W.image (pkGSh a)) (W.image (pkGSh a)) =
      pkGF (pkGM (b - a + 1) (fun d => y (pkGShP a d))) W W := by
    have e1 : pkGF (pkGM N y) (W.image (pkGSh a)) (W.image (pkGSh a)) =
        ∑ u ∈ W.image (pkGSh a), ∑ v ∈ W.image (pkGSh a), mesh N y u v := rfl
    have e2 : pkGF (pkGM (b - a + 1) (fun d => y (pkGShP a d))) W W =
        ∑ i ∈ W, ∑ j ∈ W, mesh (b - a + 1) (fun d => y (pkGShP a d)) i j := rfl
    rw [e1, e2, sum_image hinj]
    refine sum_congr rfl (fun i hi => ?_)
    rw [sum_image hinj]
    refine sum_congr rfl (fun j hj => ?_)
    exact (pkG_mesh_sh ha hb hab y hy (hW i hi).1 (hW j hj).1 (hW i hi).2 (hW j hj).2).symm
  linarith

/-- **Gluing**: the parent dissection of a pair of child dissections, `sh D₁ ∪ {C} ∪ ct D₂` with
`C = (a, b)`. -/
def pkGGlue (a b : ℕ) (D₁ D₂ : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  insert (a, b) (D₁.image (pkGShP a) ∪ D₂.image (pkGCtP a b))

theorem pkG_mem_glue {a b : ℕ} {D₁ D₂ : Finset (ℕ × ℕ)} {R : ℕ × ℕ} :
    R ∈ pkGGlue a b D₁ D₂ ↔ R = (a, b) ∨ (∃ R₁ ∈ D₁, pkGShP a R₁ = R) ∨ ∃ R₂ ∈ D₂,
        pkGCtP a b R₂ = R := by
  change R ∈ insert (a, b) (D₁.image (pkGShP a) ∪ D₂.image (pkGCtP a b)) ↔ _
  rw [mem_insert, mem_union, mem_image, mem_image]

theorem pkG_shP_fst (a : ℕ) (d : ℕ × ℕ) : (pkGShP a d).1 = d.1 + a - 1 := rfl
theorem pkG_shP_snd (a : ℕ) (d : ℕ × ℕ) : (pkGShP a d).2 = d.2 + a - 1 := rfl
theorem pkG_ctP_fst (a b : ℕ) (d : ℕ × ℕ) : (pkGCtP a b d).1 = pkGCt a b d.1 := rfl
theorem pkG_ctP_snd (a b : ℕ) (d : ℕ × ℕ) : (pkGCtP a b d).2 = pkGCt a b d.2 := rfl

/-- `pkGIn` in components. -/
theorem pkG_In_iff' {R r : ℕ × ℕ} :
    pkGIn R r ↔ ¬ (R.1 = r.1 ∧ R.2 = r.2) ∧ r.1 ≤ R.1 ∧ R.2 ≤ r.2 := by
  rw [pkG_In_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun q => h1 (pkG_eq_of q.1 q.2), h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨pkG_ne_of h1, h2, h3⟩

/-- **Vertices, kid-free form**: a vertex is a label of `[r.1, r.2]` strictly inside no chord inside
`r`. -/
theorem pkG_mem_verts' {N : ℕ} {D : Finset (ℕ × ℕ)} (hD : D ∈ pkGDis N) {r : ℕ × ℕ} {w : ℕ} :
    w ∈ pkGVerts D r ↔ r.1 ≤ w ∧ w ≤ r.2 ∧ ∀ R ∈ D, pkGIn R r → ¬ (R.1 < w ∧ w < R.2) := by
  rw [pkG_mem_verts]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun R hR hRr hw => ?_⟩
    obtain ⟨K, hK, k1, k2⟩ := pkG_desc hD hR hRr
    exact h3 K hK ⟨by omega, by omega⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun K hK => h3 K (pkG_kid_in hK).1 (pkG_In_iff.2 (pkG_kid_in hK).2)⟩

/-- The start of a root side is a vertex of its face. -/
theorem pkG_r1_vert {D : Finset (ℕ × ℕ)} {r : ℕ × ℕ} (h : r.1 ≤ r.2) : r.1 ∈ pkGVerts D r :=
  pkG_mem_verts.2 ⟨le_refl _, h, fun K hK q => by have := (pkG_kid_in hK).2.2.1; omega⟩

/-- **Vertices of inside faces**: the vertices of the glued face of a root side `r` of the inside
child are the shifted vertices of the child's face `r`. -/
theorem pkG_verts_sh {N a b : ℕ} (ha : 1 ≤ a) (_hb : b ≤ N) (hab : a + 3 ≤ b)
    (hodd : (b - a) % 2 = 1) {D₁ D₂ : Finset (ℕ × ℕ)} (hD₁ : D₁ ∈ pkGDis (b - a + 1))
    (hD₂ : D₂ ∈ pkGDis (N - (b - a) + 1)) (hD : pkGGlue a b D₁ D₂ ∈ pkGDis N) {r : ℕ × ℕ}
    (hr : r ∈ pkGRoots (b - a + 1) D₁) :
    pkGVerts (pkGGlue a b D₁ D₂) (pkGShP a r) = (pkGVerts D₁ r).image (pkGSh a) := by
  have cr := pkG_root (by omega) (by omega) hD₁ hr
  ext w
  rw [pkG_mem_verts' hD, mem_image, pkG_shP_fst, pkG_shP_snd]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨w + 1 - a, (pkG_mem_verts' hD₁).2 ⟨by omega, by omega, fun R hR hRr hw => ?_⟩,
        by rw [pkG_sh_eq]; omega⟩
    have cR := pkG_chord hD₁ hR
    rw [pkG_In_iff'] at hRr
    refine h3 (pkGShP a R) (pkG_mem_glue.2 (Or.inr (Or.inl ⟨R, hR, rfl⟩))) ?_ ?_
    · rw [pkG_In_iff', pkG_shP_fst, pkG_shP_snd, pkG_shP_fst, pkG_shP_snd]
      omega
    · rw [pkG_shP_fst, pkG_shP_snd]
      omega
  · rintro ⟨w₁, hw₁, rfl⟩
    obtain ⟨h1, h2, h3⟩ := (pkG_mem_verts' hD₁).1 hw₁
    rw [pkG_sh_eq]
    refine ⟨by omega, by omega, fun R hR hRr hw => ?_⟩
    rw [pkG_In_iff', pkG_shP_fst, pkG_shP_snd] at hRr
    rcases pkG_mem_glue.1 hR with rfl | ⟨R₁, hR₁, rfl⟩ | ⟨R₂, hR₂, rfl⟩
    · dsimp only at hRr
      omega
    · rw [pkG_shP_fst, pkG_shP_snd] at hRr hw
      have cR := pkG_chord hD₁ hR₁
      refine h3 R₁ hR₁ ?_ ⟨by omega, by omega⟩
      rw [pkG_In_iff']
      omega
    · rw [pkG_ctP_fst, pkG_ctP_snd] at hRr
      have cR := pkG_chord hD₂ hR₂
      have k1 := pkG_ct_cases a b R₂.1
      have k2 := pkG_ct_cases a b R₂.2
      omega

/-- **Vertices of outside faces**: the vertices of the glued face of a root side `r` of the outside
child are the contracted vertices of the child's face `r`. -/
theorem pkG_verts_ct {N a b : ℕ} (_hN : 4 ≤ N) (hE : N % 2 = 0) (ha : 1 ≤ a) (hb : b ≤ N)
    (hab : a + 3 ≤ b) (hC : ¬ (a = 1 ∧ b = N)) (hodd : (b - a) % 2 = 1) {D₁ D₂ : Finset (ℕ × ℕ)}
    (hD₁ : D₁ ∈ pkGDis (b - a + 1)) (hD₂ : D₂ ∈ pkGDis (N - (b - a) + 1))
    (hD : pkGGlue a b D₁ D₂ ∈ pkGDis N) {r : ℕ × ℕ} (hr : r ∈ pkGRoots (N - (b - a) + 1) D₂) :
    pkGVerts (pkGGlue a b D₁ D₂) (pkGCtP a b r) = (pkGVerts D₂ r).image (pkGCt a b) := by
  have cr := pkG_root (by omega) (by omega) hD₂ hr
  have k1 := pkG_ct_cases a b r.1
  have k2 := pkG_ct_cases a b r.2
  ext w
  rw [pkG_mem_verts' hD, mem_image, pkG_ctP_fst, pkG_ctP_snd]
  constructor
  · rintro ⟨h1, h2, h3⟩
    by_cases hw : a < w ∧ w < b
    · exfalso
      refine h3 (a, b) (pkG_mem_glue.2 (Or.inl rfl)) ?_ hw
      rw [pkG_In_iff', pkG_ctP_fst, pkG_ctP_snd]
      dsimp only
      omega
    · have kw := pkG_cl_cases a b w
      refine ⟨pkGCl a b w, (pkG_mem_verts' hD₂).2 ⟨by omega, by omega, fun R hR hRr hRw => ?_⟩, by
        rcases pkG_ct_cases a b (pkGCl a b w) with k | k <;> omega⟩
      have cR := pkG_chord hD₂ hR
      have k3 := pkG_ct_cases a b R.1
      have k4 := pkG_ct_cases a b R.2
      rw [pkG_In_iff'] at hRr
      refine h3 (pkGCtP a b R) (pkG_mem_glue.2 (Or.inr (Or.inr ⟨R, hR, rfl⟩))) ?_ ?_
      · rw [pkG_In_iff', pkG_ctP_fst, pkG_ctP_snd, pkG_ctP_fst, pkG_ctP_snd]
        omega
      · rw [pkG_ctP_fst, pkG_ctP_snd]
        omega
  · rintro ⟨w₂, hw₂, rfl⟩
    obtain ⟨h1, h2, h3⟩ := (pkG_mem_verts' hD₂).1 hw₂
    have kw := pkG_ct_cases a b w₂
    refine ⟨by omega, by omega, fun R hR hRr hw => ?_⟩
    rw [pkG_In_iff', pkG_ctP_fst, pkG_ctP_snd] at hRr
    rcases pkG_mem_glue.1 hR with rfl | ⟨R₁, hR₁, rfl⟩ | ⟨R₂, hR₂, rfl⟩
    · dsimp only at hw
      omega
    · rw [pkG_shP_fst, pkG_shP_snd] at hw
      have cR := pkG_chord hD₁ hR₁
      omega
    · rw [pkG_ctP_fst, pkG_ctP_snd] at hRr hw
      have cR := pkG_chord hD₂ hR₂
      have k3 := pkG_ct_cases a b R₂.1
      have k4 := pkG_ct_cases a b R₂.2
      refine h3 R₂ hR₂ ?_ ⟨by omega, by omega⟩
      rw [pkG_In_iff']
      omega

/-- **Governing vertex under an order-preserving map of the vertices**: if the vertices of face `r`
of `D` are the image under a monotone `f` of those of face `r'` of `D'`, and `f w ≤ x ↔ w ≤ x'`,
and some vertex of face `r'` is `≤ x'`, then the governing vertex of `x` is `f` of that of `x'`. -/
theorem pkG_gov_map {D D' : Finset (ℕ × ℕ)} {r r' : ℕ × ℕ} {f : ℕ → ℕ} (hf : Monotone f)
    (hV : pkGVerts D r = (pkGVerts D' r').image f) {x x' : ℕ} (hx : ∀ w, f w ≤ x ↔ w ≤ x')
    (hne : ∃ w ∈ pkGVerts D' r', w ≤ x') : pkGGov D r x = f (pkGGov D' r' x') := by
  have e1 : pkGGov D r x = ((pkGVerts D r).filter (fun w => w ≤ x)).sup (fun w => w) := rfl
  have e2 : pkGGov D' r' x' = ((pkGVerts D' r').filter (fun w => w ≤ x')).sup (fun w => w) := rfl
  have hfil : ((pkGVerts D' r').image f).filter (fun w => w ≤ x) =
      ((pkGVerts D' r').filter (fun w => w ≤ x')).image f := by
    ext w
    simp only [mem_filter, mem_image]
    constructor
    · rintro ⟨⟨w', hw', rfl⟩, h⟩
      exact ⟨w', ⟨hw', (hx w').1 h⟩, rfl⟩
    · rintro ⟨w', ⟨hw', h⟩, rfl⟩
      exact ⟨⟨w', hw', rfl⟩, (hx w').2 h⟩
  rw [e1, e2, hV, hfil, sup_image]
  obtain ⟨w0, hw0, hw0x⟩ := hne
  have hsne : ((pkGVerts D' r').filter (fun w => w ≤ x')).Nonempty :=
      ⟨w0, mem_filter.2 ⟨hw0, hw0x⟩⟩
  obtain ⟨m, hm, hmeq⟩ := exists_mem_eq_sup _ hsne (fun w => w)
  rw [hmeq]
  apply le_antisymm
  · refine Finset.sup_le (fun w hw => ?_)
    have h := le_sup (f := fun w => w) hw
    rw [hmeq] at h
    exact hf h
  · exact le_sup (f := Function.comp (fun w => w) f) hm

/-- **Classes of inside faces**: the class of the glued face is the shifted class of the child's
face. -/
theorem pkG_U_sh {N a b : ℕ} (ha : 1 ≤ a) (hb : b ≤ N) (hab : a + 3 ≤ b) (hodd : (b - a) % 2 = 1)
    {D₁ D₂ : Finset (ℕ × ℕ)} (hD₁ : D₁ ∈ pkGDis (b - a + 1)) (hD₂ : D₂ ∈ pkGDis (N - (b - a) + 1))
    (hD : pkGGlue a b D₁ D₂ ∈ pkGDis N) {r : ℕ × ℕ} (hr : r ∈ pkGRoots (b - a + 1) D₁) :
    pkGU (pkGGlue a b D₁ D₂) (pkGShP a r) = (pkGU D₁ r).image (pkGSh a) := by
  have cr := pkG_root (by omega) (by omega) hD₁ hr
  have hV := pkG_verts_sh ha hb hab hodd hD₁ hD₂ hD hr
  have hmono : Monotone (pkGSh a) := fun x y h => by rw [pkG_sh_eq, pkG_sh_eq]; omega
  ext x
  rw [pkG_mem_U, mem_image, pkG_shP_fst, pkG_shP_snd]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hg := pkG_gov_map hmono hV (x := x) (x' := x + 1 - a) (fun w => by rw [pkG_sh_eq]; omega)
      ⟨r.1, pkG_r1_vert (by omega), by omega⟩
    rw [hg, pkG_sh_eq] at h3
    exact ⟨x + 1 - a, pkG_mem_U.2 ⟨by omega, by omega, by omega⟩, by rw [pkG_sh_eq]; omega⟩
  · rintro ⟨x', hx', rfl⟩
    obtain ⟨h1, h2, h3⟩ := pkG_mem_U.1 hx'
    have hg := pkG_gov_map hmono hV (x := pkGSh a x') (x' := x')
        (fun w => by rw [pkG_sh_eq, pkG_sh_eq]; omega)
      ⟨r.1, pkG_r1_vert (by omega), h1⟩
    rw [hg]
    simp only [pkG_sh_eq]
    omega

/-- **Classes of outside faces**: the parent class is the union of the fibres of the child class. -/
theorem pkG_U_ct {N a b : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (ha : 1 ≤ a) (hb : b ≤ N)
    (hab : a + 3 ≤ b) (hC : ¬ (a = 1 ∧ b = N)) (hodd : (b - a) % 2 = 1) {D₁ D₂ : Finset (ℕ × ℕ)}
    (hD₁ : D₁ ∈ pkGDis (b - a + 1)) (hD₂ : D₂ ∈ pkGDis (N - (b - a) + 1))
    (hD : pkGGlue a b D₁ D₂ ∈ pkGDis N) {r : ℕ × ℕ} (hr : r ∈ pkGRoots (N - (b - a) + 1) D₂) :
    pkGU (pkGGlue a b D₁ D₂) (pkGCtP a b r) = (pkGU D₂ r).biUnion (pkGFib a b) := by
  have cr := pkG_root (by omega) (by omega) hD₂ hr
  have hV := pkG_verts_ct hN hE ha hb hab hC hodd hD₁ hD₂ hD hr
  have hmono : Monotone (pkGCt a b) := fun x y h => by
    rcases pkG_ct_cases a b x with k | k <;> rcases pkG_ct_cases a b y with k' | k' <;> omega
  have key : ∀ w x, pkGCt a b w ≤ x ↔ w ≤ pkGCl a b x := fun w x => pkG_ct_le_iff (by omega) w x
  ext x
  rw [pkG_mem_U, mem_biUnion, pkG_ctP_fst, pkG_ctP_snd]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have g1 : r.1 ≤ pkGCl a b x := (key r.1 x).1 h1
    have g2 : pkGCl a b x < r.2 := by
      by_contra hc
      have := (key r.2 x).2 (by omega)
      omega
    have hg := pkG_gov_map hmono hV (fun w => key w x) ⟨r.1, pkG_r1_vert (by omega), g1⟩
    rw [hg] at h3
    refine ⟨pkGCl a b x, pkG_mem_U.2 ⟨g1, g2, ?_⟩, (pkG_mem_fib (by omega) _ x).2 rfl⟩
    have k1 := pkG_ct_cases a b (pkGGov D₂ r (pkGCl a b x))
    have k2 := pkG_ct_cases a b r.1
    omega
  · rintro ⟨i, hi, hx⟩
    rw [pkG_mem_fib (by omega)] at hx
    obtain ⟨g1, g2, g3⟩ := pkG_mem_U.1 hi
    rw [← hx] at g1 g2 g3
    have hg := pkG_gov_map hmono hV (fun w => key w x) ⟨r.1, pkG_r1_vert (by omega), g1⟩
    refine ⟨(key r.1 x).2 g1, ?_, ?_⟩
    · by_contra hc
      have := (key r.2 x).1 (by omega)
      omega
    · rw [hg]
      have k1 := pkG_ct_cases a b (pkGGov D₂ r (pkGCl a b x))
      have k2 := pkG_ct_cases a b r.1
      omega

/-- **Cayley vertices of inside faces**: for `y` with `y (a, b) = 0`, the Cayley vertex of the glued
face is the child's at the pulled-back point. -/
theorem pkG_V_sh {N a b : ℕ} (hN : 4 ≤ N) (ha : 1 ≤ a) (hb : b ≤ N) (hab : a + 3 ≤ b)
    (hodd : (b - a) % 2 = 1) {D₁ D₂ : Finset (ℕ × ℕ)} (hD₁ : D₁ ∈ pkGDis (b - a + 1))
    (hD₂ : D₂ ∈ pkGDis (N - (b - a) + 1)) (hD : pkGGlue a b D₁ D₂ ∈ pkGDis N) (y : ℕ × ℕ → ℚ)
    (hy : y (a, b) = 0) {r : ℕ × ℕ} (hr : r ∈ pkGRoots (b - a + 1) D₁) :
    pkGV N y (pkGGlue a b D₁ D₂) (pkGShP a r) = pkGV (b - a + 1)
        (fun d => y (pkGShP a d)) D₁ r := by
  have cr := pkG_root (by omega) (by omega) hD₁ hr
  have e : ∀ n z D r, pkGV n z D r = pkGSgn (pkGVerts D r).card * pkGQ n z (pkGU D r) :=
      fun _ _ _ _ => rfl
  have hinj : Function.Injective (pkGSh a) :=
      fun x x' h => by rw [pkG_sh_eq, pkG_sh_eq] at h; omega
  rw [e, e, pkG_verts_sh ha hb hab hodd hD₁ hD₂ hD hr, pkG_U_sh ha hb hab hodd hD₁ hD₂ hD hr,
    card_image_of_injective _ hinj, pkG_Q_sh hN ha hb hab y hy (pkGU D₁ r) (fun i hi => by
      have := pkG_U_sub hi
      omega)]

/-- **Cayley vertices of outside faces**: for `y` with `y (a, b) = 0`, the Cayley vertex of the
glued face is the child's at the pulled-back point. -/
theorem pkG_V_ct {N a b : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (ha : 1 ≤ a) (hb : b ≤ N)
    (hab : a + 3 ≤ b) (hC : ¬ (a = 1 ∧ b = N)) (hodd : (b - a) % 2 = 1) {D₁ D₂ : Finset (ℕ × ℕ)}
    (hD₁ : D₁ ∈ pkGDis (b - a + 1)) (hD₂ : D₂ ∈ pkGDis (N - (b - a) + 1))
    (hD : pkGGlue a b D₁ D₂ ∈ pkGDis N) (y : ℕ × ℕ → ℚ) (hy : y (a, b) = 0) {r : ℕ × ℕ}
    (hr : r ∈ pkGRoots (N - (b - a) + 1) D₂) :
    pkGV N y (pkGGlue a b D₁ D₂) (pkGCtP a b r) =
      pkGV (N - (b - a) + 1) (fun d => y (pkGCtP a b d)) D₂ r := by
  have cr := pkG_root (by omega) (by omega) hD₂ hr
  have e : ∀ n z D r, pkGV n z D r = pkGSgn (pkGVerts D r).card * pkGQ n z (pkGU D r) :=
      fun _ _ _ _ => rfl
  have hinj : Function.Injective (pkGCt a b) := fun x x' h => by
    rcases pkG_ct_cases a b x with k | k <;> rcases pkG_ct_cases a b x' with k' | k' <;> omega
  rw [e, e, pkG_verts_ct hN hE ha hb hab hC hodd hD₁ hD₂ hD hr,
      pkG_U_ct hN hE ha hb hab hC hodd hD₁ hD₂ hD hr,
      card_image_of_injective _ hinj, pkG_Q_fib hN ha hb hab hC y hy (pkGU D₂ r) (fun i hi => by
      have := pkG_U_sub hi
      omega)]

/-- Odd chords in components. -/
theorem pkG_mem_odd {N : ℕ} {d : ℕ × ℕ} : d ∈ oddDiagonals N ↔
    (1 ≤ d.1 ∧ d.2 ≤ N ∧ d.1 + 2 ≤ d.2 ∧ ¬ (d.1 = 1 ∧ d.2 = N)) ∧ (d.2 - d.1) % 2 = 1 := by
  change d ∈ (diagonals N).filter _ ↔ _
  rw [mem_filter, mem_diagonals]

/-- A chord inside `[a, b]` crosses no chord with both ends outside `(a, b)`. -/
theorem pkG_nc_io {a b : ℕ} {p q : ℕ × ℕ} (hp : a ≤ p.1 ∧ p.2 ≤ b)
    (hq : (q.1 ≤ a ∨ b ≤ q.1) ∧ (q.2 ≤ a ∨ b ≤ q.2)) : ¬ Crosses p q ∧ ¬ Crosses q p := by
  rw [pkG_crosses_iff, pkG_crosses_iff]
  omega

/-- The contraction never lands strictly inside `(a, b)`. -/
theorem pkG_ct_out {a b : ℕ} (hab : a < b) (k : ℕ) : pkGCt a b k ≤ a ∨ b ≤ pkGCt a b k := by
  rcases pkG_ct_cases a b k with h | h <;> omega

/-- **Gluing gives a dissection**: for `C = (a, b)` an odd chord other than `(1, N)` and child
dissections `D₁`, `D₂`, the set `pkGGlue a b D₁ D₂` (which contains `C`) is a dissection. -/
theorem pkG_glue_dis {N a b : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (ha : 1 ≤ a) (hb : b ≤ N)
    (hab : a + 3 ≤ b) (hC : ¬ (a = 1 ∧ b = N)) (hodd : (b - a) % 2 = 1) {D₁ D₂ : Finset (ℕ × ℕ)}
    (hD₁ : D₁ ∈ pkGDis (b - a + 1)) (hD₂ : D₂ ∈ pkGDis (N - (b - a) + 1)) :
    pkGGlue a b D₁ D₂ ∈ pkGDis N := by
  have hin : ∀ R₁ ∈ D₁, a ≤ (pkGShP a R₁).1 ∧ (pkGShP a R₁).2 ≤ b := by
    intro R₁ hR₁
    have c := pkG_chord hD₁ hR₁
    rw [pkG_shP_fst, pkG_shP_snd]
    omega
  have hout : ∀ R₂ : ℕ × ℕ, ((pkGCtP a b R₂).1 ≤ a ∨ b ≤ (pkGCtP a b R₂).1) ∧
      ((pkGCtP a b R₂).2 ≤ a ∨ b ≤ (pkGCtP a b R₂).2) := by
    intro R₂
    rw [pkG_ctP_fst, pkG_ctP_snd]
    exact ⟨pkG_ct_out (by omega) _, pkG_ct_out (by omega) _⟩
  have hCin : a ≤ (a, b).1 ∧ (a, b).2 ≤ b := ⟨le_refl a, le_refl b⟩
  have hCout : ((a, b).1 ≤ a ∨ b ≤ (a, b).1) ∧ ((a, b).2 ≤ a ∨ b ≤ (a, b).2) :=
      ⟨Or.inl (le_refl a), Or.inr (le_refl b)⟩
  refine pkG_mem_dis.2 ⟨fun R hR => ?_, fun p hp q hq => ?_⟩
  · rcases pkG_mem_glue.1 hR with rfl | ⟨R₁, hR₁, rfl⟩ | ⟨R₂, hR₂, rfl⟩
    · rw [pkG_mem_odd]
      dsimp only
      omega
    · have c := pkG_chord hD₁ hR₁
      rw [pkG_mem_odd, pkG_shP_fst, pkG_shP_snd]
      omega
    · have c := pkG_chord hD₂ hR₂
      have k1 := pkG_ct_cases a b R₂.1
      have k2 := pkG_ct_cases a b R₂.2
      rw [pkG_mem_odd, pkG_ctP_fst, pkG_ctP_snd]
      omega
  · rcases pkG_mem_glue.1 hp with rfl | ⟨P₁, hP₁, rfl⟩ | ⟨P₂, hP₂, rfl⟩ <;>
      rcases pkG_mem_glue.1 hq with rfl | ⟨Q₁, hQ₁, rfl⟩ | ⟨Q₂, hQ₂, rfl⟩
    · rw [pkG_crosses_iff]
      dsimp only
      omega
    · exact (pkG_nc_io (hin Q₁ hQ₁) hCout).2
    · exact (pkG_nc_io hCin (hout Q₂)).1
    · exact (pkG_nc_io (hin P₁ hP₁) hCout).1
    · have h := (pkG_mem_dis.1 hD₁).2 P₁ hP₁ Q₁ hQ₁
      rw [pkG_crosses_iff] at h ⊢
      rw [pkG_shP_fst, pkG_shP_snd, pkG_shP_fst, pkG_shP_snd]
      omega
    · exact (pkG_nc_io (hin P₁ hP₁) (hout Q₂)).1
    · exact (pkG_nc_io hCin (hout P₂)).2
    · exact (pkG_nc_io (hin Q₁ hQ₁) (hout P₂)).2
    · have h := (pkG_mem_dis.1 hD₂).2 P₂ hP₂ Q₂ hQ₂
      have k1 := pkG_ct_cases a b P₂.1
      have k2 := pkG_ct_cases a b P₂.2
      have k3 := pkG_ct_cases a b Q₂.1
      have k4 := pkG_ct_cases a b Q₂.2
      rw [pkG_crosses_iff] at h ⊢
      rw [pkG_ctP_fst, pkG_ctP_snd, pkG_ctP_fst, pkG_ctP_snd]
      omega

/-- Inverse of the inside relabelling on chords. -/
def pkGShI (a : ℕ) (d : ℕ × ℕ) : ℕ × ℕ := (d.1 + 1 - a, d.2 + 1 - a)
/-- Inverse of the contraction on chords with both ends outside `(a, b)`. -/
def pkGClP (a b : ℕ) (d : ℕ × ℕ) : ℕ × ℕ := (pkGCl a b d.1, pkGCl a b d.2)

/-- **Splitting**: the two child dissections of a parent dissection, from the chords inside `[a, b]`
other than `C = (a, b)` (relabelled by `pkGShI a`) and the chords not inside `[a, b]` (collapsed by
`pkGClP a b`). -/
def pkGSplit (a b : ℕ) (D : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) × Finset (ℕ × ℕ) :=
  ((D.filter (fun R => a ≤ R.1 ∧ R.2 ≤ b ∧ ¬ (R.1 = a ∧ R.2 = b))).image (pkGShI a),
   (D.filter (fun R => ¬ (a ≤ R.1 ∧ R.2 ≤ b))).image (pkGClP a b))

theorem pkG_mem_split1 {a b : ℕ} {D : Finset (ℕ × ℕ)} {d : ℕ × ℕ} : d ∈ (pkGSplit a b D).1 ↔
    ∃ R ∈ D, (a ≤ R.1 ∧ R.2 ≤ b ∧ ¬ (R.1 = a ∧ R.2 = b)) ∧ pkGShI a R = d := by
  dsimp only [pkGSplit]
  rw [mem_image]
  constructor
  · rintro ⟨R, hR, e⟩
    exact ⟨R, (mem_filter.1 hR).1, (mem_filter.1 hR).2, e⟩
  · rintro ⟨R, hR, h, e⟩
    exact ⟨R, mem_filter.2 ⟨hR, h⟩, e⟩

theorem pkG_mem_split2 {a b : ℕ} {D : Finset (ℕ × ℕ)} {d : ℕ × ℕ} : d ∈ (pkGSplit a b D).2 ↔
    ∃ R ∈ D, ¬ (a ≤ R.1 ∧ R.2 ≤ b) ∧ pkGClP a b R = d := by
  change d ∈ (D.filter (fun R => ¬ (a ≤ R.1 ∧ R.2 ≤ b))).image (pkGClP a b) ↔ _
  rw [mem_image]
  constructor
  · rintro ⟨R, hR, e⟩
    exact ⟨R, (mem_filter.1 hR).1, (mem_filter.1 hR).2, e⟩
  · rintro ⟨R, hR, h, e⟩
    exact ⟨R, mem_filter.2 ⟨hR, h⟩, e⟩

theorem pkG_shI_fst (a : ℕ) (d : ℕ × ℕ) : (pkGShI a d).1 = d.1 + 1 - a := rfl
theorem pkG_shI_snd (a : ℕ) (d : ℕ × ℕ) : (pkGShI a d).2 = d.2 + 1 - a := rfl
theorem pkG_clP_fst (a b : ℕ) (d : ℕ × ℕ) : (pkGClP a b d).1 = pkGCl a b d.1 := rfl
theorem pkG_clP_snd (a b : ℕ) (d : ℕ × ℕ) : (pkGClP a b d).2 = pkGCl a b d.2 := rfl

/-- A chord of a dissection through `C` that is not inside `C` has both ends outside `(a, b)`. -/
theorem pkG_out_ends {N a b : ℕ} {D : Finset (ℕ × ℕ)} (hD : D ∈ pkGDis N)
    (hCD : (a, b) ∈ D) {R : ℕ × ℕ}
    (hR : R ∈ D) (h : ¬ (a ≤ R.1 ∧ R.2 ≤ b)) : (R.1 ≤ a ∨ b ≤ R.1) ∧ (R.2 ≤ a ∨ b ≤ R.2) := by
  have c := pkG_chord hD hR
  have h1 := (pkG_mem_dis.1 hD).2 R hR (a, b) hCD
  rw [pkG_crosses_iff] at h1
  dsimp only at h1
  omega


end PionCompleteness.Pi
