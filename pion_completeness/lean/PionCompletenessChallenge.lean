/-
Copyright (c) 2026 Henru Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henru Wang
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Challenge: the minimal coordinate zeros of the NLSM amplitude

The main theorem of the paper, in the paper's terms: for an even number `N ≥ 6` of legs, with
`A_N^NLSM` the tree-level amplitude of the non-linear sigma model as a rational function of the
planar variables `X_ab`,
* every regular coordinate zero of `A_N^NLSM` contains a member of the list `𝒢_N` (a causal
  diamond, or an `S_T` for a set `T` of at least three legs of one parity);
* every member of `𝒢_N` is a minimal regular coordinate zero;
* hence the minimal regular coordinate zeros are exactly the members of `𝒢_N`.

This file is the Challenge for Palomar's comparator (`comparator.json`). It imports Mathlib only.
Every definition the three statements use is copied, under the same name and character for
character, from the library module named in its section heading; the statements are copied from
`PionCompleteness.Paper`, with `sorry` for their proofs. Comparator checks that
`PionCompleteness.Paper` proves the three statements, with definitions equal to these and no axiom
beyond `propext`, `Quot.sound` and `Classical.choice`, in the Lean kernel. The imports are the
Mathlib modules that the library imports on its way to `PionCompleteness.Paper`, so that each
definition elaborates as it does there. Never import this module: its theorems are `sorry`; their
proofs are `PionCompleteness.Paper`'s.

The amplitude is built as in arXiv:2312.16282: the colour-ordered tree amplitude of the `φ³`
theory (a sum over the triangulations of the `N`-gon, `amp`), shifted by `δ v₀`, and `NLSM_N` its
coefficient of `δ^{−(N−2)}` (`NLSM`); then evaluated at the generic point `gen` of the field `RF`
of rational functions in the planar variables. The coordinate locus `L_S` sets the mesh variables
`c_ab` (`mesh`) of a set `S` of pairs of legs to zero (`OnLocus`); the docstrings call the mesh
variable `c_ab` of a pair `(a, b)` a *tile*. Docstrings may cite library results that this file
does not copy (`NLSM_four`, the normalisation of `NLSM`).
-/

@[expose] public section

/-! ## Polygons, triangulations and the amplitude (`PionCompleteness.Base.TreeRectangleZero`) -/

namespace PionCompleteness.TreeRectangleZero

open Finset

/-- Diagonals of the convex `n`-gon with vertices `1..n`. -/
def diagonals (n : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 n ×ˢ Icc 1 n).filter (fun p => p.1 + 2 ≤ p.2 ∧ ¬ (p.1 = 1 ∧ p.2 = n))

/-- Two diagonals `(a,b)`, `(c,d)` (with `a < b`, `c < d`) cross iff their endpoints interleave. -/
def Crosses (p q : ℕ × ℕ) : Prop :=
  (p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2) ∨ (q.1 < p.1 ∧ p.1 < q.2 ∧ q.2 < p.2)

/-- Whether two diagonals cross is decidable: it unfolds to comparisons of natural numbers. -/
instance : DecidableRel Crosses := fun _ _ => by unfold Crosses; infer_instance

/-- A triangulation is a maximal set of pairwise non-crossing diagonals. -/
def IsTriangulation (n : ℕ) (T : Finset (ℕ × ℕ)) : Prop :=
  T ⊆ diagonals n ∧ (∀ p ∈ T, ∀ q ∈ T, ¬ Crosses p q) ∧
    (∀ d ∈ diagonals n, d ∉ T → ∃ p ∈ T, Crosses p d)

/-- Whether a set of diagonals is a triangulation is decidable, so that `triangulations` can select
the triangulations among the subsets of `diagonals n`. -/
instance (n : ℕ) : DecidablePred (IsTriangulation n) := fun _ => by
  unfold IsTriangulation; infer_instance

/-- The triangulations of the `n`-gon, as a `Finset`: the sets with `IsTriangulation n`. -/
def triangulations (n : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  (diagonals n).powerset.filter (IsTriangulation n)

variable {K : Type*} [Field K]

/-- The colour-ordered tree amplitude: sum over triangulations of `∏ 1/X`
([arXiv:2312.16282 eqs. (3.1), (3.6)]). -/
def amp (n : ℕ) (X : ℕ × ℕ → K) : K :=
  ∑ T ∈ triangulations n, ∏ d ∈ T, (X d)⁻¹

/-- Vertex label mod `n`, into `1..n`. -/
def vtx (n i : ℕ) : ℕ := (i + n - 1) % n + 1

/-- Planar variable for arbitrary (cyclic) labels: `0` on edges and on coincident labels. -/
def planar (n : ℕ) (X : ℕ × ℕ → K) (i j : ℕ) : K :=
  if (min (vtx n i) (vtx n j), max (vtx n i) (vtx n j)) ∈ diagonals n then
    X (min (vtx n i) (vtx n j), max (vtx n i) (vtx n j)) else 0

/-- Mesh variable `c_{i,j}` ([arXiv:2312.16282 eq. (2.4)]). -/
def mesh (n : ℕ) (X : ℕ × ℕ → K) (i j : ℕ) : K :=
  planar n X i j + planar n X (i + 1) (j + 1) - planar n X i (j + 1) - planar n X (i + 1) j

end PionCompleteness.TreeRectangleZero

/-! ## The coordinate locus (`PionCompleteness.Base.ChainSlice`) -/

namespace PionCompleteness.ChainSlice

open Finset PionCompleteness.TreeRectangleZero

/-- The locus `L_S = {c_S = 0}`: every tile of `S` vanishes at `X`. -/
def OnLocus {K : Type*} [Field K] (m : ℕ) (S : Finset (ℕ × ℕ)) (X : ℕ × ℕ → K) : Prop :=
  ∀ t ∈ S, mesh m X t.1 t.2 = 0

end PionCompleteness.ChainSlice

/-! ## The tiles of `S_T` (`PionCompleteness.Base.PionZeros`) -/

namespace PionCompleteness.PionZeros

open Finset PionCompleteness.TreeRectangleZero

/-- The tile `c_ab` (legs `a, b ∈ 1..N`) lies in `S_T`: neither leg is in `T`, and `a`, `b` lie in
different arcs of the leg circle cut at `T`, i.e. a leg of `T` lies strictly between them on each
side. (Non-adjacency follows.) -/
def InST (T : Finset ℕ) (a b : ℕ) : Prop :=
  a ∉ T ∧ b ∉ T ∧ (∃ t ∈ T, min a b < t ∧ t < max a b) ∧ (∃ t ∈ T, t < min a b ∨ max a b < t)

/-- Whether the tile `c_ab` lies in `S_T` is decidable, so that `S_T` can be computed as a
`Finset` (`Pi.sepPairs`). -/
instance (T : Finset ℕ) (a b : ℕ) : Decidable (InST T a b) := by unfold InST; infer_instance

end PionCompleteness.PionZeros

/-! ## The NLSM amplitude and rational functions (`PionCompleteness.Base.PionNLSM`) -/

namespace PionCompleteness.PionNLSM

open Finset PionCompleteness.TreeRectangleZero PionCompleteness.PionZeros

section NLSMdef

variable {K : Type*} [Field K]

/-- The δ-shift direction `v₀` [arXiv:2312.16282 §7.1 eqs. (7.6)–(7.7)]: `+1` on `X_{e,e}`, `−1` on
`X_{o,o}`, `0` on `X_{o,e}` (vertex labels `1..N`, parity of the labels). -/
def shiftSign (d : ℕ × ℕ) : ℤ :=
  if d.1 % 2 = 0 ∧ d.2 % 2 = 0 then 1 else if d.1 % 2 = 1 ∧ d.2 % 2 = 1 then -1 else 0

/-- `δ = e⁻¹` as a Laurent series in `e`. -/
noncomputable def delta : LaurentSeries K := HahnSeries.single (-1 : ℤ) 1

/-- The δ-shifted point `X + δ v₀`, coordinates in `K⸨e⸩`. -/
noncomputable def shifted (X : ℕ × ℕ → K) : ℕ × ℕ → LaurentSeries K :=
  fun d => HahnSeries.C (X d) + (shiftSign d : LaurentSeries K) * delta

/-- The coefficient of `e^m = δ^{−m}` in `A_N(X + δ v₀)`, with `A_N` the amplitude `amp` over the
field `K⸨e⸩`. -/
noncomputable def shiftCoeff (N : ℕ) (m : ℤ) (X : ℕ × ℕ → K) : K := (amp N (shifted X)).coeff m

/-- **The NLSM amplitude** `NLSM_N`: the coefficient of `δ^{−(N−2)}` in `A_N(X + δ v₀)`
[arXiv:2312.16282 eq. (7.15); arXiv:2401.05483 eq. (2)]. Normalisation: `NLSM_4 = −(X₁₃ + X₂₄)`
(`NLSM_four`), i.e. arXiv:2312.16282 eqs. (4.3)–(4.4) times `(−1)^{N/2−1}`. -/
noncomputable def NLSM (N : ℕ) (X : ℕ × ℕ → K) : K := shiftCoeff N ((N : ℤ) - 2) X

end NLSMdef

section Rational

open MvPolynomial

/-- The field of rational functions in the planar variables. -/
abbrev RF := FractionRing (MvPolynomial (ℕ × ℕ) ℚ)

/-- The generic point: every planar variable is its own indeterminate. -/
noncomputable def gen : ℕ × ℕ → RF := fun d => algebraMap (MvPolynomial (ℕ × ℕ) ℚ) RF (X d)

/-- `F` restricts to the zero rational function on the set of ℚ-points `V`: `F = P/Q` with `Q` not
identically zero on `V` and `P` identically zero on `V`. For `V` a linear subspace (irreducible)
this does not depend on the choice of `P, Q`. -/
def RatZeroOn (V : Set (ℕ × ℕ → ℚ)) (F : RF) : Prop :=
  ∃ P Q : MvPolynomial (ℕ × ℕ) ℚ, F * algebraMap _ RF Q = algebraMap _ RF P ∧
    (∃ w ∈ V, eval w Q ≠ 0) ∧ ∀ x ∈ V, eval x P = 0

end Rational

end PionCompleteness.PionNLSM

/-! ## Separated pairs (`PionCompleteness.C0`) -/

namespace PionCompleteness.Pi

open Finset PionCompleteness.TreeRectangleZero PionCompleteness.ChainSlice
  PionCompleteness.PionZeros PionCompleteness.PionNLSM

/-- **`S_G`**: the pairs of legs lying in different arcs of `G` (both legs outside `G`, a leg of `G`
on each side), i.e. `InST` of `PionZeros` on the pairs `diagonals N`; non-adjacency is automatic. -/
def sepPairs (N : ℕ) (G : Finset ℕ) :
    Finset (ℕ × ℕ) := (diagonals N).filter (fun p => InST G p.1 p.2)

end PionCompleteness.Pi

/-! ## The paper's definitions and the main theorem (`PionCompleteness.Paper`) -/

namespace PionCompleteness.Paper

open Finset PionCompleteness.Pi PionCompleteness.PionNLSM PionCompleteness.PionZeros
  PionCompleteness.ChainSlice PionCompleteness.TreeRectangleZero

namespace NLSM.Zeros
end NLSM.Zeros
namespace NLSM.Zeros.Families
end NLSM.Zeros.Families
open NLSM.Zeros NLSM.Zeros.Families

/-- A set `S` of pairs is **regular**: no planar variable vanishes identically on the coordinate
locus `L_S`. -/
def NLSM.Zeros.IsRegularSet (N : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  ∀ d ∈ diagonals N, ¬ ∀ x : ℕ × ℕ → ℚ, OnLocus N S x → x d = 0

/-- `S` is a **zero**: `A_N^NLSM ≡ 0` on `L_S`, as a rational function on the kinematic space. -/
def NLSM.Zeros.IsCoordinateZero (N : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  RatZeroOn {x | OnLocus N S x} (NLSM N gen)

/-- A **regular coordinate zero**: a regular set of pairs that is a zero. -/
def NLSM.Zeros.IsRegularCoordinateZero (N : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  S ⊆ diagonals N ∧ IsRegularSet N S ∧ IsCoordinateZero N S

/-- A **minimal** regular coordinate zero `Z`: for every pair `t ∈ Z`, the set `Z ∖ {t}` is not a
zero. -/
def NLSM.Zeros.IsMinimalCoordinateZero (N : ℕ) (Z : Finset (ℕ × ℕ)) : Prop :=
  IsRegularCoordinateZero N Z ∧ ∀ t ∈ Z, ¬ IsCoordinateZero N (Z.erase t)

/-- A **causal diamond**: `S_{a,b}` for two legs `a < b` whose two arcs are both non-empty (a leg
strictly between them, and a leg outside them). -/
def NLSM.Zeros.Families.IsCausalDiamond (N : ℕ) (Z : Finset (ℕ × ℕ)) : Prop :=
  ∃ a ∈ Icc 1 N, ∃ b ∈ Icc 1 N, a < b ∧ (∃ u, a < u ∧ u < b) ∧ (∃ u ∈ Icc 1 N, u < a ∨ b < u) ∧
    Z = sepPairs N {a, b}

/-- `Z` is a member of **the list** `𝒢_N`: a causal diamond, or `S_T` for a set `T` of at least
three legs of one parity. -/
def NLSM.Zeros.Families.IsListMember (N : ℕ) (Z : Finset (ℕ × ℕ)) : Prop :=
  IsCausalDiamond N Z ∨
    ∃ T ⊆ Icc 1 N, 3 ≤ T.card ∧ (∀ t ∈ T, ∀ u ∈ T, t % 2 = u % 2) ∧ Z = sepPairs N T

/-- **The main theorem, clause 1** (completeness): for even `N ≥ 6`, every regular coordinate zero
`S` of `A_N^NLSM` contains a member of the list `𝒢_N`: a causal diamond or an `S_T` for a set `T` of
at least three legs of one parity. -/
theorem NLSM.Zeros.every_coordinate_zero_contains_a_family_member {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    {S : Finset (ℕ × ℕ)} (hS : IsRegularCoordinateZero N S) : ∃ Z, IsListMember N Z ∧ Z ⊆ S := by
  sorry

/-- **The main theorem, clause 2** (minimality): for even `N ≥ 6`, every member `Z` of the list
`𝒢_N` is a minimal regular coordinate zero of `A_N^NLSM`: a regular coordinate zero such that
`Z ∖ {t}` is not a zero, for each pair `t ∈ Z`. -/
theorem NLSM.Zeros.family_members_are_minimal_zeros {N : ℕ} (hN : 6 ≤ N) (hE : Even N) :
    ∀ Z, IsListMember N Z → IsMinimalCoordinateZero N Z := by
  sorry

/-- **The main theorem, "Hence"**: for even `N ≥ 6`, the minimal regular coordinate zeros of
`A_N^NLSM` are exactly the members of the list `𝒢_N`. -/
theorem NLSM.Zeros.minimal_coordinate_zeros_are_the_list {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    {Z : Finset (ℕ × ℕ)} : IsMinimalCoordinateZero N Z ↔ IsListMember N Z := by
  sorry

end PionCompleteness.Paper
