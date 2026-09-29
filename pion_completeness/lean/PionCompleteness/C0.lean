import ChainSlice
import PionNLSM

/-!
# Theorem Π (completeness of the pion coordinate zeros): frozen base for milestones M1 / M2 / M3

R12-P7b0 (stage 0), from R12-P7a's reviewed statement file (md5 63a8c871…, R1: no must-fix) with the R1 should-fixes and
the reconciliation with `writeups/pion-st-zeros/lean/BLUEPRINT.md` applied. Thread `surfaceology/threads/R12-P7b0.md`;
plan `R12-P7.md` (§4b owner decision: M1 → M2 → M3, one Lean process at a time). Reference text, cited "[v3 …]":
`writeups/pion-st-zeros/COMPLETENESS-DRAFT-v3.md` §14.1–§14.5; "[DRAFT …]": `DRAFT.md` §2; "[BP …]": the blueprint.

**Reconciliation decisions (thread §4 C1).**
* *Carrier.* Every frozen definition and statement uses the base's ℕ labels: legs and dual points `1..N`, a pair of
  non-adjacent legs / a chord stored sorted as `(a, b)`, `a < b`, the set of all of them `diagonals N`. Cyclic sides of a
  chord are `(start, length)` arcs read through `vtx` (`cycArc`, `cycPos`). The blueprint's `ZMod N` carrier (BP §1.1)
  may be used inside proofs; the frozen bridge `legZ` / `labZ` (§3b) fixes the translation.
* *Normalisation.* The top statements (clauses 1, 2, "hence") are for `𝒜_N = calA` (DRAFT (2.3)), as reviewed in P7a.
  Every internal statement about the amplitude (the M2 inputs, `NonzeroOn`, `NLSMZeroOn`) is for the raw δ-coefficient
  `R12P3C.NLSM` (BP §1.3: [Res]'s sign `(−1)^d` is a raw-normalisation statement). The conversion is PROVED
  (`ampZeroOn_iff_nlsmZeroOn`, `nonzeroOn_iff_not_ampZeroOn`).
* *Predicates.* One family: `NLSMZeroOn` (raw, pointwise off the poles), `NonzeroOn` (raw, a witness point) and
  `AmpZeroOn` (= P7a `IsZero`, for 𝒜_N). No bare `¬ RatZeroOn` anywhere (BP G-2).
* *Names.* BP §7 Lean identifiers, namespace `PiZ` (no clash with Mathlib's `IsZero`, `Minimal`, `trace`, `List.head`,
  or the base's `R12P1.tri`): `sepPairs` (S_G), `IsSameParitySet` (G ∈ 𝒯, same-parity only), `IsMixedAnchor`,
  `IsGSet` (all of 𝒢_N), `gFamily` (𝒢_N), `oddSide` / `evenSide` (head / tail), `oddSideSplit` / `evenSideSplit`
  (the cuts), `minRect`, `innerEE` / `innerOO`, `cleanChords` (𝒫₀), `poleChords` (𝒫₁), `hitClass`, `admSeps`
  (admissible traces), `sepIn` (runcut), `NoFreeSep` (Sep_all), `goodTail` (𝒮_B), `IsMinimalChord` (canonical chord),
  `ThreeSepSetting` / `threeSep` ((Tri)), `ConsecWit` (F_U), `childSet` (children). The rename map is
  `../rename_p7a.py`; expert-facing names are not decided here.

**Milestones (BP §5; owner 2026-09-27).**
* M1 (combinatorial core, no amplitude): the `sorry` targets of packages pkgComb, pkgTri, pkgChain, pkgLin.
* M2 (Π modulo named analytic inputs): `pi_clause1_M2`, `pi_clause2_M2`, `pi_minimal_iff_M2` take the analytic inputs
  as explicit hypotheses (`GermInput`, `ResChildInput`, `STZeroInput`; frozen `Prop` definitions, no `axiom`).
* M3 (full Π): the inputs are the targets `germ_input`, `resChild_input`, `stZero_input`; `pi_clause1`, `pi_clause2`,
  `pi_minimal_iff` are ASSEMBLED from the M2 forms and these targets.

Base, imported unchanged (copies with recorded md5 in `base/`, oleans in `base/build/`):
* `TreeRectangleZero` (Phase 1: `diagonals`, `amp`, `vtx`, `planar`, `mesh`, `Crosses`, `rot`);
* `ChainSlice` (Phase 4b: `OnLocus`, `Nondeg`, `diamond`, `amp_zero_of_diamond`);
* `PionZeros` (Phase 3: `oddDiagonals`, `Admissible`, `InST`, `OnZT`, `theoremA`);
* `PionNLSM` (R12-P3c, 3c-a reviewed: `NLSM` = the raw δ-coefficient, `NLSM_four`, `NLSM_six`, `paper43`, `gen`,
  `RatZeroOn`; its `sorry`s `NLSM_rot`, `AP_eval`, `AP_residue`, `NP_residue`, `theoremB`, `nlsm_zero_on_ZT`, … are the
  3c-b targets of R12-P3cb: a proof here that uses one of them stays unclean until 3c-b's accepted module replaces this
  import).

Conventions (C0): leg `a` lies between dual points `a` and `a+1`; the pair `{a, b}` carries `c_{a,b} = mesh N X a b`
(DRAFT (2.1)); the chord `(i, j)` carries `X_{i,j}`.

Status markers: PROVED (no `sorry` in its closure; `#print axioms` at the end), ASSEMBLED (proved from `sorry`
statements above it), `sorry` (a package target; the package is named in the docstring and in `packages.json`).
-/

namespace PiZ

open Finset R12P1 R12P4A R12P3 R12P3C

/-! ## 1. The amplitude 𝒜_N of DRAFT (2.3)

Design decision (thread §4 C1). No new amplitude: `calA N X := (−1)^{N/2−1} · NLSM N X`, where `NLSM` is R12-P3c's
reviewed definition (the coefficient of `δ^{−(N−2)}` in `A_N^{φ³}(X + δ v₀)`, computed in `K⸨e⸩`, `e = 1/δ`). This is
DRAFT (2.3) literally, sign included, so `calA 4 = X₁₃ + X₂₄` and `calA 6 = ` arXiv:2312.16282 (4.3) (proved below). The
sign cannot affect any statement of Π (they are all "= 0" / "≠ 0"); it is kept so that the object is the one v3 names.
R12-P6a's `nlsmDelta` (a `RatFunc` coerced to `LaurentSeries`) is the same coefficient by a different road; it is not
imported (it lives in a non-base file); an equality lemma `nlsmDelta = NLSM` (and `mixedDiagonals =
oddDiagonals`) is needed only if pkgGerm (M3) builds Theorem I on R12-P6a's definitions (thread §5). -/

section Amp

variable {K : Type*} [Field K]

/-- **𝒜_N** [DRAFT (2.3)]: `(−1)^{N/2−1}` times the coefficient of `δ^{−(N−2)}` in `A_N^{φ³}(X + δ v₀)`. -/
noncomputable def calA (N : ℕ) (X : ℕ × ℕ → K) : K := (-1 : K) ^ (N / 2 - 1) * NLSM N X

/-- PROVED. `𝒜₄ = X₁₃ + X₂₄ = c_{1,3}` [DRAFT §2 "The sign is chosen so that 𝒜₄ = X_{1,3} + X_{2,4}"]. -/
theorem calA_four (X : ℕ × ℕ → K) : calA 4 X = X (1, 3) + X (2, 4) := by
  rw [calA, NLSM_four]; norm_num

/-- PROVED. `𝒜₆` is arXiv:2312.16282 eq. (4.3) [DRAFT §2 "and 𝒜₆ is [ACDFH eq. (4.3)]"]. -/
theorem calA_six (X : ℕ × ℕ → K) : calA 6 X = paper43 X := by
  rw [calA, NLSM_six]; norm_num

end Amp

/-! ## 2. Coordinate loci, non-degeneracy, zeros [v3 Definitions 14.1, 14.3]

Design decision (thread §4 C1): **"𝒜_N vanishes identically on L_S" is read pointwise over ℚ, off the polar
hyperplanes**: at every rational point of `L_S` at which no odd (= mixed) chord vanishes, `𝒜_N = 0`. The poles of `𝒜_N`
are exactly the odd chords (same-parity chords are units `X ± δ` in `K⸨e⸩`), so this is `𝒜_N` evaluated where it is
defined, with no junk `0⁻¹` term. For non-degenerate `S` the reading equals "`𝒜_N|_{L_S}` is the zero element of the
function field of `L_S`" (rational points off finitely many proper hyperplanes of `L_S` are Zariski dense), which is the
v3 reading; the equivalence is stated as `ampZeroOn_iff_ratZero` (`sorry`, pkgBridge, optional). For degenerate `S` the pointwise reading can
be vacuous (`degenerate_full` below), which is why every statement carries non-degeneracy. Non-degeneracy is stated
literally (every chord is somewhere non-zero on `L_S`, `Nondeg`); the one-point form `NonDegPt` is stronger and is what
clause 2 concludes. -/

/-! Non-degeneracy [v3 Def. 14.1] is the base definition `R12P4A.Nondeg` (ChainSlice, reviewed in Phase 4): every chord
`X_C` is non-zero at some rational point of `L_S`, i.e. no planar variable vanishes identically on `L_S`. -/

/-- One rational point of `L_S` with every chord non-zero (implies `Nondeg`; equivalent over ℚ, `nonDeg_iff_pt`). -/
def NonDegPt (N : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  ∃ X : ℕ × ℕ → ℚ, OnLocus N S X ∧ ∀ d ∈ diagonals N, X d ≠ 0

/-- `S` is a **zero** [v3 Def. 14.1 "NLSM_N|_{L_S} ≡ 0"]: `𝒜_N = 0` at every rational point of `L_S` where no pole
(odd chord) vanishes. -/
def AmpZeroOn (N : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  ∀ X : ℕ × ℕ → ℚ, OnLocus N S X → (∀ d ∈ oddDiagonals N, X d ≠ 0) → calA N X = 0

/-- A **non-degenerate coordinate zero** [v3 Def. 14.1]: a set of pairs (of non-adjacent legs) that is non-degenerate and
a zero. -/
def IsNDZero (N : ℕ) (S : Finset (ℕ × ℕ)) : Prop := S ⊆ diagonals N ∧ Nondeg N S ∧ AmpZeroOn N S

/-- A **minimal** non-degenerate coordinate zero [v3 Def. 14.3]: `𝒜_N ≢ 0` on `L_{Z∖{t}}` for every pair `t ∈ Z`. -/
def IsMinimalZero (N : ℕ) (Z : Finset (ℕ × ℕ)) : Prop := IsNDZero N Z ∧ ∀ t ∈ Z, ¬ AmpZeroOn N (Z.erase t)

theorem nonDeg_of_pt {N : ℕ} {S : Finset (ℕ × ℕ)} (h : NonDegPt N S) : Nondeg N S := by
  obtain ⟨X, hL, hX⟩ := h
  exact fun d hd => ⟨X, hL, hX d hd⟩

theorem onLocus_mono {N : ℕ} {S S' : Finset (ℕ × ℕ)} (h : S ⊆ S') {X : ℕ × ℕ → ℚ} (hX : OnLocus N S' X) :
    OnLocus N S X := fun t ht => hX t (h ht)

/-- PROVED. Subsets of a non-degenerate set are non-degenerate (their loci are larger) [v3 Def. 14.3, parenthesis]. -/
theorem nonDeg_mono {N : ℕ} {S S' : Finset (ℕ × ℕ)} (h : S ⊆ S') (hnd : Nondeg N S') : Nondeg N S := by
  intro d hd
  obtain ⟨X, hL, hX⟩ := hnd d hd
  exact ⟨X, onLocus_mono h hL, hX⟩

/-- PROVED. A zero stays a zero on a smaller locus (larger set of pairs) [v3 §14.2 route step 1, [Mono], contrapositive]. -/
theorem ampZeroOn_mono {N : ℕ} {S S' : Finset (ℕ × ℕ)} (h : S ⊆ S') (hz : AmpZeroOn N S) : AmpZeroOn N S' :=
  fun X hL hX => hz X (onLocus_mono h hL) hX

theorem pkBr_planar_lin (N : ℕ) (X Y : ℕ × ℕ → ℚ) (t : ℚ) (i j : ℕ) :
    planar N (fun e => X e + t * Y e) i j = planar N X i j + t * planar N Y i j := by
  unfold planar
  split_ifs <;> simp

theorem pkBr_onLocus_lin {N : ℕ} {S : Finset (ℕ × ℕ)} {X Y : ℕ × ℕ → ℚ} (hX : OnLocus N S X)
    (hY : OnLocus N S Y) (t : ℚ) : OnLocus N S (fun e => X e + t * Y e) := by
  intro p hp
  have h1 := hX p hp
  have h2 := hY p hp
  unfold mesh at h1 h2 ⊢
  simp only [pkBr_planar_lin]
  linear_combination h1 + t * h2

theorem pkBr_onLocus_zero (N : ℕ) (S : Finset (ℕ × ℕ)) : OnLocus N S (fun _ => (0 : ℚ)) := by
  intro p _
  unfold mesh planar
  simp

theorem pkBr_pt_of_nondeg {N : ℕ} {S : Finset (ℕ × ℕ)} (hnd : Nondeg N S) :
    ∀ D : Finset (ℕ × ℕ), D ⊆ diagonals N → ∃ X : ℕ × ℕ → ℚ, OnLocus N S X ∧ ∀ d ∈ D, X d ≠ 0 := by
  intro D
  induction D using Finset.induction_on with
  | empty => exact fun _ => ⟨fun _ => 0, pkBr_onLocus_zero N S, by simp⟩
  | insert d D hdD ih =>
    intro hsub
    obtain ⟨X, hXL, hXD⟩ := ih ((subset_insert d D).trans hsub)
    obtain ⟨Y, hYL, hYd⟩ := hnd d (hsub (mem_insert_self d D))
    obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset ((insert d D).image (fun e => -X e / Y e))
    have key : ∀ e ∈ insert d D, X e + t * Y e = 0 → Y e = 0 := by
      intro e he h0
      by_contra hY
      apply ht
      rw [mem_image]
      refine ⟨e, he, ?_⟩
      field_simp
      linear_combination -h0
    refine ⟨fun e => X e + t * Y e, pkBr_onLocus_lin hXL hYL t, ?_⟩
    intro e he h0
    have hY0 := key e he h0
    rcases mem_insert.1 he with rfl | he'
    · exact hYd hY0
    · apply hXD e he'
      simpa [hY0] using h0

/-- `sorry` (pkgBridge, optional). The two forms of non-degeneracy agree over ℚ (a ℚ-vector space is not a finite union of proper
subspaces). -/
theorem nonDeg_iff_pt {N : ℕ} {S : Finset (ℕ × ℕ)} : Nondeg N S ↔ NonDegPt N S :=
  ⟨fun h => by
    obtain ⟨X, hL, hX⟩ := pkBr_pt_of_nondeg h (diagonals N) subset_rfl
    exact ⟨X, hL, hX⟩, nonDeg_of_pt⟩

/-- The sign of DRAFT (2.3) is a unit (local copy for use before §2a). -/
theorem pkBr_calA_zero_iff (N : ℕ) (X : ℕ × ℕ → ℚ) : calA N X = 0 ↔ NLSM N X = 0 := by
  simp [calA]

/-- Polynomial factor of one diagonal in the δ-expansion: `1` on odd diagonals (their `1/X` goes to the common
denominator), `e · Σ_k s^{k+1} (−X_d)^k e^k` on the others (as `phi`). -/
noncomputable def pkBr_phiP (d : ℕ × ℕ) : PowerSeries (MvPolynomial (ℕ × ℕ) ℚ) :=
  if shiftSign d = 0 then 1 else
    PowerSeries.X * PowerSeries.mk (fun k =>
      ((shiftSign d : ℤ) : MvPolynomial (ℕ × ℕ) ℚ) ^ (k + 1) * (-MvPolynomial.X d) ^ k)

/-- A polynomial numerator of `NLSM_N` over the common denominator `∏_{odd} X_d`. -/
noncomputable def pkBr_numP (N : ℕ) : MvPolynomial (ℕ × ℕ) ℚ :=
  PowerSeries.coeff (N - 2) (∑ T ∈ triangulations N,
    (T.prod (fun d => pkBr_phiP d)) * PowerSeries.C ((oddDiagonals N \ T).prod (fun d => MvPolynomial.X d)))

theorem pkBr_shiftSign_eq_zero {N : ℕ} {d : ℕ × ℕ} (hd : d ∈ diagonals N) :
    shiftSign d = 0 ↔ d ∈ oddDiagonals N := by
  have hd' := mem_diagonals.1 hd
  show _ ↔ d ∈ (diagonals N).filter (fun d => (d.2 - d.1) % 2 = 1)
  rw [mem_filter]
  unfold shiftSign
  constructor
  · intro h
    refine ⟨hd, ?_⟩
    split_ifs at h <;> omega
  · rintro ⟨-, h⟩
    split_ifs <;> omega

theorem pkBr_phi_map {K : Type*} [Field K] (f : RingHom (MvPolynomial (ℕ × ℕ) ℚ) K) (d : ℕ × ℕ) :
    phi (fun e => f (MvPolynomial.X e)) d =
      PowerSeries.map f (pkBr_phiP d) *
        PowerSeries.C (if shiftSign d = 0 then Inv.inv (f (MvPolynomial.X d)) else 1) := by
  unfold phi pkBr_phiP
  split_ifs with h
  · simp
  · unfold shiftSeries
    rw [map_one, mul_one, map_mul, PowerSeries.map_X]
    refine congrArg _ ?_
    ext k
    simp [PowerSeries.coeff_map]

/-- The scalar identity behind the numerator: `∏_{T ∩ odd} x⁻¹ · ∏_{odd} x = ∏_{odd ∖ T} x`. -/
theorem pkBr_prod_scalar {K : Type*} [Field K] {N : ℕ} (x : ℕ × ℕ → K) (hx : ∀ d ∈ oddDiagonals N, x d ≠ 0)
    {T : Finset (ℕ × ℕ)} (hT : T ⊆ diagonals N) :
    T.prod (fun d => if shiftSign d = 0 then Inv.inv (x d) else 1) * (oddDiagonals N).prod (fun d => x d) =
      (oddDiagonals N \ T).prod (fun d => x d) := by
  have h1 : T.prod (fun d => if shiftSign d = 0 then Inv.inv (x d) else 1) =
      (oddDiagonals N ∩ T).prod (fun d => Inv.inv (x d)) := by
    rw [← prod_filter, inter_comm, ← filter_mem_eq_inter]
    refine prod_congr ?_ (fun _ _ => rfl)
    ext d
    simp only [mem_filter]
    constructor
    · rintro ⟨hd, h⟩; exact ⟨hd, (pkBr_shiftSign_eq_zero (hT hd)).1 h⟩
    · rintro ⟨hd, h⟩; exact ⟨hd, (pkBr_shiftSign_eq_zero (hT hd)).2 h⟩
  rw [h1, ← prod_sdiff (inter_subset_left : oddDiagonals N ∩ T ⊆ oddDiagonals N)]
  rw [sdiff_inter_self_left]
  have h2 : (oddDiagonals N ∩ T).prod (fun d => Inv.inv (x d)) * (oddDiagonals N ∩ T).prod (fun d => x d) = 1 := by
    rw [← prod_mul_distrib]
    exact prod_eq_one fun d hd => inv_mul_cancel₀ (hx d (mem_inter.1 hd).1)
  rw [show (oddDiagonals N ∩ T).prod (fun d => Inv.inv (x d)) *
        ((oddDiagonals N \ T).prod (fun d => x d) * (oddDiagonals N ∩ T).prod (fun d => x d))
      = (oddDiagonals N \ T).prod (fun d => x d) *
        ((oddDiagonals N ∩ T).prod (fun d => Inv.inv (x d)) * (oddDiagonals N ∩ T).prod (fun d => x d)) by ring,
    h2, mul_one]

/-- Numerator lemma for `NLSM_N` (own form; no 3c-b input). -/
theorem pkBr_numP_hom {K : Type*} [Field K] (f : RingHom (MvPolynomial (ℕ × ℕ) ℚ) K) {N : ℕ} (hN : 2 ≤ N)
    (hX : ∀ d ∈ oddDiagonals N, f (MvPolynomial.X d) ≠ 0) :
    f (pkBr_numP N) =
      NLSM N (fun d => f (MvPolynomial.X d)) * (oddDiagonals N).prod (fun d => f (MvPolynomial.X d)) := by
  rw [NLSM_eq_ps hN, pkBr_numP, ← PowerSeries.coeff_map, ← PowerSeries.coeff_mul_C]
  refine congrArg _ ?_
  rw [map_sum, sum_mul]
  refine sum_congr rfl fun T hT => ?_
  have hTs : T ⊆ diagonals N := (mem_filter.1 hT).2.1
  simp only [pkBr_phi_map]
  rw [map_mul, PowerSeries.map_C, map_prod (PowerSeries.map f), prod_mul_distrib, ← map_prod PowerSeries.C,
    mul_assoc, ← map_mul PowerSeries.C, pkBr_prod_scalar (fun d => f (MvPolynomial.X d)) hX hTs, map_prod f]

theorem pkBr_line {N : ℕ} {S : Finset (ℕ × ℕ)} :
    ∀ x ∈ {x : ℕ × ℕ → ℚ | OnLocus N S x}, ∀ y ∈ {x : ℕ × ℕ → ℚ | OnLocus N S x}, ∀ t : ℚ,
      x + HSMul.hSMul t (y - x) ∈ {x : ℕ × ℕ → ℚ | OnLocus N S x} := by
  intro x hx y hy t
  have hf : (x + HSMul.hSMul t (y - x)) = fun d => x d + t * (fun d => y d + (-1) * x d) d := by
    ext d
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  rw [hf]
  exact pkBr_onLocus_lin hx (pkBr_onLocus_lin hy hx (-1)) t

theorem pkBr_eval_oddDen_ne {x : ℕ × ℕ → ℚ} {N : ℕ} (hx : ∀ d ∈ oddDiagonals N, x d ≠ 0) :
    MvPolynomial.eval x (oddDen ℚ N) ≠ 0 := by
  rw [oddDen, map_prod]
  simpa using prod_ne_zero_iff.2 hx

theorem pkBr_odd_of_eval {x : ℕ × ℕ → ℚ} {N : ℕ} (h : MvPolynomial.eval x (oddDen ℚ N) ≠ 0) :
    ∀ d ∈ oddDiagonals N, x d ≠ 0 := by
  rw [oddDen, map_prod] at h
  simpa using prod_ne_zero_iff.1 h

theorem pkBr_gen_hom {N : ℕ} (hN : 2 ≤ N) :
    algebraMap _ RF (pkBr_numP N) = NLSM N gen * algebraMap _ RF (oddDen ℚ N) := by
  rw [pkBr_numP_hom (algebraMap _ RF) hN (fun d _ => gen_ne_zero d), oddDen, map_prod]
  rfl

/-- `sorry` (pkgBridge, optional). **Pointwise zero = zero in the function field of `L_S`** for non-degenerate `S` (R12-P3c's
`RatZeroOn` at the generic point; the proof is R12-P3c's `line_bridge`). Fixes the reading of "≡ 0" (thread §4 C1). -/
theorem ampZeroOn_iff_ratZero {N : ℕ} (hN : 4 ≤ N) (hE : Even N) {S : Finset (ℕ × ℕ)} (hS : S ⊆ diagonals N)
    (hnd : Nondeg N S) : AmpZeroOn N S ↔ RatZeroOn {x | OnLocus N S x} (NLSM N gen) := by
  have hN2 : 2 ≤ N := by omega
  have hev : ∀ x : ℕ × ℕ → ℚ, (∀ d ∈ oddDiagonals N, x d ≠ 0) →
      MvPolynomial.eval x (pkBr_numP N) = NLSM N x * MvPolynomial.eval x (oddDen ℚ N) := by
    intro x hx
    rw [pkBr_numP_hom (MvPolynomial.eval x) hN2 (by simpa using hx), oddDen, map_prod]
    simp
  constructor
  · intro hz
    obtain ⟨w, hwL, hw0⟩ := nonDeg_iff_pt.1 hnd
    have hwodd : ∀ d ∈ oddDiagonals N, w d ≠ 0 := fun d hd => hw0 d (mem_filter.1 hd).1
    refine ⟨pkBr_numP N, oddDen ℚ N, (pkBr_gen_hom hN2).symm, ⟨w, hwL, pkBr_eval_oddDen_ne hwodd⟩, ?_⟩
    refine line_bridge _ pkBr_line _ _ hwL (pkBr_eval_oddDen_ne hwodd) fun x hx hQ => ?_
    have hxo := pkBr_odd_of_eval hQ
    rw [hev x hxo, (pkBr_calA_zero_iff N x).1 (hz x hx hxo), zero_mul]
  · rintro ⟨P, Q, hPQ, ⟨w, hwV, hQw⟩, hP⟩
    have hpoly : pkBr_numP N * Q = P * oddDen ℚ N := by
      apply IsFractionRing.injective (MvPolynomial (ℕ × ℕ) ℚ) RF
      rw [map_mul, map_mul, pkBr_gen_hom hN2, ← hPQ]
      ring
    have hnum : ∀ x ∈ {x : ℕ × ℕ → ℚ | OnLocus N S x}, MvPolynomial.eval x (pkBr_numP N) = 0 := by
      refine line_bridge _ pkBr_line _ _ hwV hQw fun x hx hQx => ?_
      have := congrArg (MvPolynomial.eval x) hpoly
      rw [map_mul, map_mul, hP x hx, zero_mul] at this
      exact (mul_eq_zero.1 this).resolve_right hQx
    intro x hx hxo
    rw [pkBr_calA_zero_iff]
    have h0 := hnum x hx
    rw [hev x hxo] at h0
    exact (mul_eq_zero.1 h0).resolve_right (pkBr_eval_oddDen_ne hxo)

/-! ### 2a. The raw-normalisation predicates (BP §1.3–§1.4) and their PROVED links to `AmpZeroOn`

One predicate family (thread §4 C1): `NLSMZeroOn` (zero, raw), `NonzeroOn` (witness of non-vanishing, raw) and
`AmpZeroOn` (zero of 𝒜_N, used by the top statements). All three read the amplitude pointwise over ℚ off the odd-chord
poles; none is a bare `¬ RatZeroOn` (vacuous on a degenerate locus, BP G-2). -/

/-- `S` is an **NLSM zero** (raw normalisation; BP §1.4 `NLSMZeroOn`): `NLSM_N = 0` at every rational point of `L_S`
at which no odd chord vanishes. -/
def NLSMZeroOn (N : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  ∀ X : ℕ × ℕ → ℚ, OnLocus N S X → (∀ d ∈ oddDiagonals N, X d ≠ 0) → NLSM N X = 0

/-- **`NLSM_N ≢ 0` on `L_S`**, positive form (BP §1.4 `NonzeroOn`): a rational point of `L_S`, off every pole, at which
`NLSM_N ≠ 0`. Clause 1's induction and the M2 inputs are stated in this form. -/
def NonzeroOn (N : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  ∃ X : ℕ × ℕ → ℚ, OnLocus N S X ∧ (∀ d ∈ oddDiagonals N, X d ≠ 0) ∧ NLSM N X ≠ 0

/-- PROVED. The sign of DRAFT (2.3) is a unit. -/
theorem calA_eq_zero_iff (N : ℕ) (X : ℕ × ℕ → ℚ) : calA N X = 0 ↔ NLSM N X = 0 := by
  simp [calA]

/-- PROVED. `𝒜_N` and `NLSM_N` have the same zero sets (normalisation policy, thread §4 C1). -/
theorem ampZeroOn_iff_nlsmZeroOn {N : ℕ} {S : Finset (ℕ × ℕ)} : AmpZeroOn N S ↔ NLSMZeroOn N S := by
  simp only [AmpZeroOn, NLSMZeroOn, calA_eq_zero_iff]

/-- PROVED. The witness form is the negation of the zero form. -/
theorem nonzeroOn_iff_not_nlsmZeroOn {N : ℕ} {S : Finset (ℕ × ℕ)} : NonzeroOn N S ↔ ¬ NLSMZeroOn N S := by
  unfold NonzeroOn NLSMZeroOn
  push Not
  exact Iff.rfl

/-- PROVED. The witness form (raw) is the negation of the top statements' zero form (𝒜_N). -/
theorem nonzeroOn_iff_not_ampZeroOn {N : ℕ} {S : Finset (ℕ × ℕ)} : NonzeroOn N S ↔ ¬ AmpZeroOn N S := by
  rw [nonzeroOn_iff_not_nlsmZeroOn, ampZeroOn_iff_nlsmZeroOn]

/-! ## 3. Arcs, S_G and the list 𝒢_N [v3 Def. 14.2; DRAFT Defs. 2.1–2.2] -/

/-- **S_G** [v3 Def. 14.2; DRAFT Def. 2.1]: the pairs of legs lying in different arcs of `G` (both legs outside `G`, a leg
of `G` on each side). Phase 3's `InST` read on the pair set `diagonals N`; non-adjacency is automatic. -/
def sepPairs (N : ℕ) (G : Finset ℕ) : Finset (ℕ × ℕ) := (diagonals N).filter (fun p => InST G p.1 p.2)

/-- `G` is a **same-parity leg set** (`G ∈ 𝒯`; not the diamonds): at least two legs of `1..N`, all of one parity [v3 Def. 14.2 "S_T"; Phase 3's
`Admissible`]. -/
def IsSameParitySet (N : ℕ) (G : Finset ℕ) : Prop := Admissible N 0 G ∨ Admissible N 1 G

instance (N : ℕ) : DecidablePred (IsSameParitySet N) := fun _ => by unfold IsSameParitySet; infer_instance

/-- `G = {a, b}` anchors a **mixed-anchored diamond** [v3 Def. 14.2]: legs of different parity whose two arcs are both
non-empty (`a + 2 ≤ b`: the arc `(a, b)` is non-empty; `(a, b) ≠ (1, N)`: the other arc is non-empty). -/
def IsMixedAnchor (N : ℕ) (G : Finset ℕ) : Prop :=
  ∃ a ∈ Icc 1 N, ∃ b ∈ Icc 1 N, G = {a, b} ∧ a + 2 ≤ b ∧ ¬ (a = 1 ∧ b = N) ∧ a % 2 ≠ b % 2

instance (N : ℕ) : DecidablePred (IsMixedAnchor N) := fun _ => by unfold IsMixedAnchor; infer_instance

/-- `G` indexes a member of `𝒢_N` (BP §7 `IsGSet`; all of `𝒢_N`): a same-parity leg set or a mixed anchor. -/
def IsGSet (N : ℕ) (G : Finset ℕ) : Prop := IsSameParitySet N G ∨ IsMixedAnchor N G

instance (N : ℕ) : DecidablePred (IsGSet N) := fun _ => by unfold IsGSet; infer_instance

/-- The leg sets of `𝒢_N`. -/
def gLegSets (N : ℕ) : Finset (Finset ℕ) := (Icc 1 N).powerset.filter (IsGSet N)

/-- **𝒢_N** [v3 Def. 14.2] `= {S_T : |T| ≥ 2, one parity} ∪ {mixed-anchored diamonds}`. -/
def gFamily (N : ℕ) : Finset (Finset (ℕ × ℕ)) := (gLegSets N).image (sepPairs N)

/-- `S` contains a member of `𝒢_N`. -/
def ContainsGMember (N : ℕ) (S : Finset (ℕ × ℕ)) : Prop := ∃ Z ∈ gFamily N, Z ⊆ S

/-- PROVED. Members of `𝒢_N` are sets of pairs. -/
theorem gFamily_sub {N : ℕ} {Z : Finset (ℕ × ℕ)} (hZ : Z ∈ gFamily N) : Z ⊆ diagonals N := by
  obtain ⟨G, -, rfl⟩ := mem_image.1 hZ
  exact filter_subset _ _

/-- `M` is a **transversal** (hitting set) of `𝒢_N` [BP §2.3 `Transversal`; v3 §14.2 "M meets every member of 𝒢_N"]. -/
def Transversal (N : ℕ) (M : Finset (ℕ × ℕ)) : Prop := ∀ Z ∈ gFamily N, (Z ∩ M).Nonempty

/-! ## 3b. The `ZMod N` bridge and rotations [BP §1.1, §2.2; P7a R1 S3]

Statements are on ℕ labels; proofs may work on `ZMod N` (BP §1.1: rotation is `x ↦ x + r`, parity a ring hom for even
`N`). `legZ` / `labZ` are the translation (label `N` ↔ `0`); `rotLeg` is the rotation of legs (and dual points) by `r`
on labels. The bridge and transport statements below are OPTIONAL targets of pkgBridge / pkgComb: a package that
works on `ZMod N` proves the ones it uses. Transport of `threeSepCut`, `ConsecWit`, `ThreeSepSetting` under even
rotations (P7a R1 S3; needed where Lemma 14.5 applies (Tri) at a rotated head) is a pkgChain-internal TODO built on
`inST_rotLeg` (README of pkgChain). -/

/-- Leg label `a` as an element of `ZMod N` (label `N` ↦ `0`). -/
def legZ (N a : ℕ) : ZMod N := (a : ZMod N)

/-- The label in `1..N` of `x : ZMod N` (`0` ↦ `N`). -/
def labZ (N : ℕ) (x : ZMod N) : ℕ := if x.val = 0 then N else x.val

/-- Rotation of a leg (or dual point) label by `r`, normalised to `1..N` by `vtx`. -/
def rotLeg (N r a : ℕ) : ℕ := vtx N (a + r)

/-- Rotation of a sorted pair / chord by `r` (re-sorted). -/
def rotPair (N r : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  (min (rotLeg N r p.1) (rotLeg N r p.2), max (rotLeg N r p.1) (rotLeg N r p.2))

/-- `sorry` (pkgBridge, optional). `labZ` inverts `legZ` on labels `1..N`. -/
theorem labZ_legZ {N a : ℕ} [NeZero N] (ha : a ∈ Icc 1 N) : labZ N (legZ N a) = a := by
  rw [mem_Icc] at ha
  unfold labZ legZ
  rw [ZMod.val_natCast]
  rcases lt_or_eq_of_le ha.2 with h | h
  · rw [Nat.mod_eq_of_lt h, if_neg (by omega)]
  · rw [h, Nat.mod_self, if_pos rfl]

/-- `sorry` (pkgBridge, optional). `legZ` inverts `labZ`. -/
theorem legZ_labZ {N : ℕ} [NeZero N] (x : ZMod N) : legZ N (labZ N x) = x := by
  unfold legZ labZ
  split_ifs with h
  · rw [ZMod.natCast_self]
    exact ((ZMod.val_eq_zero x).1 h).symm
  · exact ZMod.natCast_zmod_val x

/-- `sorry` (pkgBridge, optional). For even `N`, the parity of a label is the image of `x` in `ZMod 2`. -/
theorem labZ_parity {N : ℕ} [NeZero N] (h2 : 2 ∣ N) (x : ZMod N) :
    labZ N x % 2 = (ZMod.castHom h2 (ZMod 2) x).val := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
  unfold labZ
  split_ifs with h
  · rw [h]; omega
  · rfl

/-- `sorry` (pkgBridge, optional). Rotation on labels is addition in `ZMod N`. -/
theorem legZ_rotLeg {N : ℕ} [NeZero N] (r a : ℕ) : legZ N (rotLeg N r a) = legZ N a + (r : ZMod N) := by
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  unfold legZ rotLeg vtx
  rw [Nat.cast_add, ZMod.natCast_mod, Nat.cast_one, show a + r + N - 1 = (a + r) + (N - 1) by omega,
    Nat.cast_add, Nat.cast_sub hN, ZMod.natCast_self, Nat.cast_add]
  ring

theorem pkCo_vtx_add_mul (N m q : ℕ) : vtx N (m + N * q) = vtx N m := by
  induction q with
  | zero => rw [Nat.mul_zero, Nat.add_zero]
  | succ q ih => rw [Nat.mul_succ, ← Nat.add_assoc, vtx_add_n, ih]

/-- Rotation of a label of `1..N` in closed form (`c = r % N`). -/
theorem pkCo_rotLeg_eq {N r x : ℕ} (hN : 1 ≤ N) (h1 : 1 ≤ x) (h2 : x ≤ N) :
    rotLeg N r x = if x + r % N ≤ N then x + r % N else x + r % N - N := by
  have hc := Nat.mod_lt r (by omega : 0 < N)
  have h : rotLeg N r x = vtx N (x + r % N) := by
    show vtx N (x + r) = _
    rw [show x + r = x + r % N + N * (r / N) by rw [Nat.add_assoc, Nat.mod_add_div]]
    exact pkCo_vtx_add_mul N _ _
  rw [h]
  split_ifs with h3
  · exact vtx_of_mem (by omega) h3
  · exact vtx_of_gt (by omega) (by omega)

theorem pkCo_rotLeg_mem {N r x : ℕ} (hN : 1 ≤ N) (hx : x ∈ Icc 1 N) : rotLeg N r x ∈ Icc 1 N := by
  rw [mem_Icc] at hx ⊢
  have hc := Nat.mod_lt r (by omega : 0 < N)
  rw [pkCo_rotLeg_eq hN hx.1 hx.2]
  split_ifs <;> omega

theorem pkCo_rotLeg_inj {N r x y : ℕ} (hN : 1 ≤ N) (hx : x ∈ Icc 1 N) (hy : y ∈ Icc 1 N)
    (h : rotLeg N r x = rotLeg N r y) : x = y := by
  rw [mem_Icc] at hx hy
  have hc := Nat.mod_lt r (by omega : 0 < N)
  rw [pkCo_rotLeg_eq hN hx.1 hx.2, pkCo_rotLeg_eq hN hy.1 hy.2] at h
  split_ifs at h <;> omega

theorem pkCo_rotLeg_surj {N r y : ℕ} (hN : 1 ≤ N) (hy : y ∈ Icc 1 N) : ∃ x ∈ Icc 1 N, rotLeg N r x = y := by
  rw [mem_Icc] at hy
  have hc := Nat.mod_lt r (by omega : 0 < N)
  by_cases h : r % N < y
  · refine ⟨y - r % N, mem_Icc.2 ⟨by omega, by omega⟩, ?_⟩
    rw [pkCo_rotLeg_eq hN (by omega) (by omega)]
    split_ifs <;> omega
  · refine ⟨y + N - r % N, mem_Icc.2 ⟨by omega, by omega⟩, ?_⟩
    rw [pkCo_rotLeg_eq hN (by omega) (by omega)]
    split_ifs <;> omega

theorem pkCo_mem_image_rotLeg {N r x : ℕ} {G : Finset ℕ} (hN : 1 ≤ N) (hG : G ⊆ Icc 1 N) (hx : x ∈ Icc 1 N) :
    rotLeg N r x ∈ G.image (rotLeg N r) ↔ x ∈ G := by
  rw [mem_image]
  constructor
  · rintro ⟨y, hy, h⟩
    rw [← pkCo_rotLeg_inj hN (hG hy) hx h]
    exact hy
  · intro h
    exact ⟨x, h, rfl⟩

theorem pkCo_inST_iff {T : Finset ℕ} {a b : ℕ} :
    InST T a b ↔ a ∉ T ∧ b ∉ T ∧ (∃ t ∈ T, min a b < t ∧ t < max a b) ∧ (∃ t ∈ T, t < min a b ∨ max a b < t) :=
  Iff.rfl

theorem pkCo_inST_comm {T : Finset ℕ} {a b : ℕ} : InST T a b ↔ InST T b a := by
  rw [pkCo_inST_iff, pkCo_inST_iff, min_comm, max_comm]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h2, h1, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨h2, h1, h3⟩⟩

/-- Rotation preserves "between" and "outside" when `a`, `b` wrap alike. -/
theorem pkCo_rot_pres {N r a b t : ℕ} (hN : 1 ≤ N) (ha : a ∈ Icc 1 N) (hb : b ∈ Icc 1 N) (ht : t ∈ Icc 1 N)
    (hF : (a + r % N ≤ N ∧ b + r % N ≤ N) ∨ (N < a + r % N ∧ N < b + r % N)) :
    ((min (rotLeg N r a) (rotLeg N r b) < rotLeg N r t ∧ rotLeg N r t < max (rotLeg N r a) (rotLeg N r b)) ↔
      (min a b < t ∧ t < max a b)) ∧
    ((rotLeg N r t < min (rotLeg N r a) (rotLeg N r b) ∨ max (rotLeg N r a) (rotLeg N r b) < rotLeg N r t) ↔
      (t < min a b ∨ max a b < t)) := by
  rw [mem_Icc] at ha hb ht
  have hc := Nat.mod_lt r (by omega : 0 < N)
  rw [pkCo_rotLeg_eq hN ha.1 ha.2, pkCo_rotLeg_eq hN hb.1 hb.2, pkCo_rotLeg_eq hN ht.1 ht.2]
  refine ⟨?_, ?_⟩ <;> (split_ifs <;> omega)

/-- Rotation swaps "between" and "outside" when exactly one of `a`, `b` wraps. -/
theorem pkCo_rot_swap {N r a b t : ℕ} (hN : 1 ≤ N) (ha : a ∈ Icc 1 N) (hb : b ∈ Icc 1 N) (ht : t ∈ Icc 1 N)
    (hF : (a + r % N ≤ N ∧ N < b + r % N) ∨ (N < a + r % N ∧ b + r % N ≤ N)) :
    ((min (rotLeg N r a) (rotLeg N r b) < rotLeg N r t ∧ rotLeg N r t < max (rotLeg N r a) (rotLeg N r b)) ↔
      (t < min a b ∨ max a b < t)) ∧
    ((rotLeg N r t < min (rotLeg N r a) (rotLeg N r b) ∨ max (rotLeg N r a) (rotLeg N r b) < rotLeg N r t) ↔
      (min a b < t ∧ t < max a b)) := by
  rw [mem_Icc] at ha hb ht
  have hc := Nat.mod_lt r (by omega : 0 < N)
  rw [pkCo_rotLeg_eq hN ha.1 ha.2, pkCo_rotLeg_eq hN hb.1 hb.2, pkCo_rotLeg_eq hN ht.1 ht.2]
  refine ⟨?_, ?_⟩ <;> (split_ifs <;> omega)

theorem pkCo_exists_image_rotLeg {N r : ℕ} {G : Finset ℕ} (p : ℕ → Prop) :
    (∃ t ∈ G.image (rotLeg N r), p t) ↔ ∃ t ∈ G, p (rotLeg N r t) := by
  constructor
  · rintro ⟨y, ht, h⟩
    obtain ⟨t, ht', rfl⟩ := mem_image.1 ht
    exact ⟨t, ht', h⟩
  · rintro ⟨t, ht, h⟩
    exact ⟨rotLeg N r t, mem_image_of_mem _ ht, h⟩

/-- `sorry` (pkgComb, optional) · **rotation transport of "different arcs"** [P7a R1 S3]: for legs and a leg set in
`1..N`, rotating everything by `r` preserves `InST` (Python: 0 failures, N = 4, 6, 8, every G, r, u, v;
`../mirror_rot.out`). -/
theorem inST_rotLeg {N : ℕ} (hN : 1 ≤ N) (r : ℕ) {G : Finset ℕ} (hG : G ⊆ Icc 1 N) {u v : ℕ} (hu : u ∈ Icc 1 N)
    (hv : v ∈ Icc 1 N) : InST (G.image (rotLeg N r)) (rotLeg N r u) (rotLeg N r v) ↔ InST G u v := by
  rw [pkCo_inST_iff, pkCo_inST_iff, pkCo_mem_image_rotLeg hN hG hu, pkCo_mem_image_rotLeg hN hG hv,
    pkCo_exists_image_rotLeg (fun t => min (rotLeg N r u) (rotLeg N r v) < t ∧ t < max (rotLeg N r u) (rotLeg N r v)),
    pkCo_exists_image_rotLeg (fun t => t < min (rotLeg N r u) (rotLeg N r v) ∨ max (rotLeg N r u) (rotLeg N r v) < t)]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  by_cases hF : (u + r % N ≤ N ∧ v + r % N ≤ N) ∨ (N < u + r % N ∧ N < v + r % N)
  · refine and_congr ?_ ?_
    · exact exists_congr fun t => and_congr_right fun ht => (pkCo_rot_pres hN hu hv (hG ht) hF).1
    · exact exists_congr fun t => and_congr_right fun ht => (pkCo_rot_pres hN hu hv (hG ht) hF).2
  · have hF' : (u + r % N ≤ N ∧ N < v + r % N) ∨ (N < u + r % N ∧ v + r % N ≤ N) := by omega
    rw [and_comm]
    refine and_congr ?_ ?_
    · exact exists_congr fun t => and_congr_right fun ht =>
        (pkCo_rot_swap hN hu hv (hG ht) hF').2
    · exact exists_congr fun t => and_congr_right fun ht =>
        (pkCo_rot_swap hN hu hv (hG ht) hF').1

/-- A separated pair of legs of `1..N` (sorted) is a diagonal. -/
theorem pkCo_diag_of_inST {N a b : ℕ} {G : Finset ℕ} (hG : G ⊆ Icc 1 N) (ha : a ∈ Icc 1 N) (hb : b ∈ Icc 1 N)
    (hab : a < b) (h : InST G a b) : (a, b) ∈ diagonals N := by
  rw [pkCo_inST_iff, min_eq_left hab.le, max_eq_right hab.le] at h
  obtain ⟨-, -, ⟨t, ht, h1⟩, ⟨t', ht', h2⟩⟩ := h
  have := mem_Icc.1 (hG ht')
  rw [mem_Icc] at ha hb
  rw [mem_diagonals]
  dsimp only
  omega

theorem pkCo_mem_sepPairs {N : ℕ} {G : Finset ℕ} (hG : G ⊆ Icc 1 N) {p : ℕ × ℕ} :
    p ∈ sepPairs N G ↔ p.1 ∈ Icc 1 N ∧ p.2 ∈ Icc 1 N ∧ p.1 < p.2 ∧ InST G p.1 p.2 := by
  show p ∈ (diagonals N).filter (fun p => InST G p.1 p.2) ↔ _
  rw [mem_filter]
  constructor
  · rintro ⟨hd, h⟩
    have := mem_diagonals.1 hd
    exact ⟨mem_Icc.2 ⟨by omega, by omega⟩, mem_Icc.2 ⟨by omega, by omega⟩, by omega, h⟩
  · rintro ⟨h1, h2, h3, h⟩
    exact ⟨pkCo_diag_of_inST hG h1 h2 h3 h, h⟩

/-- `sorry` (pkgComb, optional) · **rotation transport of `S_G`** [P7a R1 S3]. -/
theorem sepPairs_rotLeg {N : ℕ} (hN : 4 ≤ N) (r : ℕ) {G : Finset ℕ} (hG : G ⊆ Icc 1 N) :
    sepPairs N (G.image (rotLeg N r)) = (sepPairs N G).image (rotPair N r) := by
  have hN1 : 1 ≤ N := by omega
  have hG' : G.image (rotLeg N r) ⊆ Icc 1 N := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
    exact pkCo_rotLeg_mem hN1 (hG hx)
  ext ⟨a, b⟩
  rw [pkCo_mem_sepPairs hG', mem_image]
  constructor
  · rintro ⟨hq1, hq2, hq, h⟩
    dsimp only at hq1 hq2 hq h
    obtain ⟨u, hu, rfl⟩ := pkCo_rotLeg_surj (r := r) hN1 hq1
    obtain ⟨v, hv, rfl⟩ := pkCo_rotLeg_surj (r := r) hN1 hq2
    rw [inST_rotLeg hN1 r hG hu hv] at h
    have huv : u ≠ v := fun e => by rw [e] at hq; omega
    refine ⟨(min u v, max u v), ?_, ?_⟩
    · rw [pkCo_mem_sepPairs hG]
      rcases lt_or_gt_of_ne huv with e | e
      · rw [min_eq_left e.le, max_eq_right e.le]; exact ⟨hu, hv, e, h⟩
      · rw [min_eq_right e.le, max_eq_left e.le]; exact ⟨hv, hu, e, pkCo_inST_comm.1 h⟩
    · show (min (rotLeg N r (min u v)) (rotLeg N r (max u v)), max (rotLeg N r (min u v)) (rotLeg N r (max u v))) =
        (rotLeg N r u, rotLeg N r v)
      rcases le_total u v with e | e
      · rw [min_eq_left e, max_eq_right e, min_eq_left hq.le, max_eq_right hq.le]
      · rw [min_eq_right e, max_eq_left e, min_eq_right hq.le, max_eq_left hq.le]
  · rintro ⟨p, hp, hpq⟩
    rw [← hpq]
    rw [pkCo_mem_sepPairs hG] at hp
    obtain ⟨h1, h2, h3, h⟩ := hp
    have hne : rotLeg N r p.1 ≠ rotLeg N r p.2 := fun e => by
      have := pkCo_rotLeg_inj hN1 h1 h2 e; omega
    have hI := (inST_rotLeg hN1 r hG h1 h2).2 h
    show min (rotLeg N r p.1) (rotLeg N r p.2) ∈ Icc 1 N ∧ max (rotLeg N r p.1) (rotLeg N r p.2) ∈ Icc 1 N ∧
      min (rotLeg N r p.1) (rotLeg N r p.2) < max (rotLeg N r p.1) (rotLeg N r p.2) ∧
      InST (G.image (rotLeg N r)) (min (rotLeg N r p.1) (rotLeg N r p.2)) (max (rotLeg N r p.1) (rotLeg N r p.2))
    have m1 := pkCo_rotLeg_mem (r := r) hN1 h1
    have m2 := pkCo_rotLeg_mem (r := r) hN1 h2
    rcases lt_or_gt_of_ne hne with e | e
    · rw [min_eq_left e.le, max_eq_right e.le]; exact ⟨m1, m2, e, hI⟩
    · rw [min_eq_right e.le, max_eq_left e.le]; exact ⟨m2, m1, e, pkCo_inST_comm.1 hI⟩

/-! ## 5. Objects of the route [v3 §14.2, §14.2a] (combinatorial; no amplitude) -/

/-- The missing set `M` of `S`: the pairs not in `S`. -/
def missing (N : ℕ) (S : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) := diagonals N \ S

/-- `M_e`, `M_o`: missing pairs with both legs even, both odd. -/
def Mee (N : ℕ) (S : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) := (missing N S).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0)
def Moo (N : ℕ) (S : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) := (missing N S).filter (fun p => p.1 % 2 = 1 ∧ p.2 % 2 = 1)

def odds (L : Finset ℕ) : Finset ℕ := L.filter (fun a => a % 2 = 1)
def evens (L : Finset ℕ) : Finset ℕ := L.filter (fun a => a % 2 = 0)

/-- The **head** `A_P` of a mixed (= odd) chord `P = (i, j)`: of the two leg blocks `[i, j−1]` and its complement, the one
whose end legs are odd [v3 §14.2]. (`[i, j−1]` has end legs `i`, `j−1`, of the parity of `i`.) -/
def oddSide (N : ℕ) (P : ℕ × ℕ) : Finset ℕ :=
  if P.1 % 2 = 1 then Icc P.1 (P.2 - 1) else Icc 1 N \ Icc P.1 (P.2 - 1)

/-- The **tail** `B_P`: the even-ended block. -/
def evenSide (N : ℕ) (P : ℕ × ℕ) : Finset ℕ := Icc 1 N \ oddSide N P

/-- The cuts `H^A = S_{odds(A_P)}`, `H^B = S_{evens(B_P)}` and the **hit set** `h_P = M ∩ (H^A ∪ H^B)` [v3 §14.2]. -/
def oddSideSplit (N : ℕ) (P : ℕ × ℕ) : Finset (ℕ × ℕ) := sepPairs N (odds (oddSide N P))
def evenSideSplit (N : ℕ) (P : ℕ × ℕ) : Finset (ℕ × ℕ) := sepPairs N (evens (evenSide N P))
def hitSet (N : ℕ) (S : Finset (ℕ × ℕ)) (P : ℕ × ℕ) : Finset (ℕ × ℕ) := missing N S ∩ (oddSideSplit N P ∪ evenSideSplit N P)

/-- `minRect(P) = evens(A_P) × odds(B_P)` as sorted pairs [v3 §14.2a]. -/
def minRect (N : ℕ) (P : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  (evens (oddSide N P) ×ˢ odds (evenSide N P)).image (fun q => (min q.1 q.2, max q.1 q.2))

/-- `e_in(P)`: missing ee pairs inside `B_P`; `o_in(P)`: missing oo pairs inside `A_P` [v3 §14.2a]. -/
def innerEE (N : ℕ) (S : Finset (ℕ × ℕ)) (P : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  (Mee N S).filter (fun p => p.1 ∈ evenSide N P ∧ p.2 ∈ evenSide N P)
def innerOO (N : ℕ) (S : Finset (ℕ × ℕ)) (P : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  (Moo N S).filter (fun p => p.1 ∈ oddSide N P ∧ p.2 ∈ oddSide N P)

/-- `𝒫₀`: mixed chords whose `minRect` holds no missing pair; `𝒫₁`: those with `e_in ≠ ∅` and `o_in ≠ ∅`
[v3 §14.2a]. -/
def cleanChords (N : ℕ) (S : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  (oddDiagonals N).filter (fun P => Disjoint (minRect N P) (missing N S))
def poleChords (N : ℕ) (S : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  (cleanChords N S).filter (fun P => (innerEE N S P).Nonempty ∧ (innerOO N S P).Nonempty)

/-- **F^π_N** [v3 §14.2]: non-degenerate sets of pairs containing no member of `𝒢_N`. -/
def InFpi (N : ℕ) (S : Finset (ℕ × ℕ)) : Prop := S ⊆ diagonals N ∧ Nondeg N S ∧ ¬ ContainsGMember N S

/-! ### pkgLin helpers (`pkL_`): mesh sums, Lemma 6.5, the hit-set identity -/

theorem pkL_mesh_eq {K : Type*} [Field K] (N : ℕ) (X : ℕ × ℕ → K) (a b : ℕ) :
    mesh N X a b = planar N X a b + planar N X (a + 1) (b + 1) - planar N X a (b + 1) - planar N X (a + 1) b :=
  rfl

theorem pkL_pl_self {K : Type*} [Field K] (N : ℕ) (X : ℕ × ℕ → K) (a : ℕ) : planar N X a a = 0 := by
  have e : planar N X a a = if (min (vtx N a) (vtx N a), max (vtx N a) (vtx N a)) ∈ diagonals N then
      X (min (vtx N a) (vtx N a), max (vtx N a) (vtx N a)) else 0 := rfl
  rw [e, if_neg]
  intro h
  have := mem_diagonals.1 h
  simp only [min_self, max_self] at this
  omega

theorem pkL_vtx_N1 (N : ℕ) : vtx N (N + 1) = vtx N 1 := by
  rw [show N + 1 = 1 + N by omega, vtx_add_n]

theorem pkL_pl_succ {K : Type*} [Field K] {N : ℕ} (hN : 2 ≤ N) (X : ℕ × ℕ → K) (a : ℕ) : planar N X a (a + 1) = 0 := by
  have h1 : 1 ≤ N := by omega
  rw [planar_congr X (vtx_vtx h1 a).symm (vtx_vtx_succ h1 a).symm]
  obtain ⟨hv1, hv2⟩ := vtx_bounds N a h1
  rcases Nat.lt_or_ge (vtx N a) N with h | h
  · exact planar_side X hv1 (by omega)
  · have hv : vtx N a = N := by omega
    rw [hv, planar_congr X (i' := N) (j' := 1) rfl (pkL_vtx_N1 N), R12P4A.planar_comm]
    exact planar_one_n X hN

theorem pkL_mesh_comm {K : Type*} [Field K] (N : ℕ) (X : ℕ × ℕ → K) (a b : ℕ) : mesh N X a b = mesh N X b a := by
  rw [pkL_mesh_eq, pkL_mesh_eq, R12P4A.planar_comm N X b a, R12P4A.planar_comm N X (b + 1) (a + 1), R12P4A.planar_comm N X b (a + 1),
    R12P4A.planar_comm N X (b + 1) a]
  ring

theorem pkL_mesh_self {K : Type*} [Field K] {N : ℕ} (hN : 2 ≤ N) (X : ℕ × ℕ → K) (a : ℕ) : mesh N X a a = 0 := by
  rw [pkL_mesh_eq, pkL_pl_self, pkL_pl_self, pkL_pl_succ hN, R12P4A.planar_comm N X (a + 1) a, pkL_pl_succ hN]
  ring

/-- Row sums of the mesh variables vanish (a full cycle of `b`). -/
theorem pkL_row {K : Type*} [Field K] {N : ℕ} (hN : 1 ≤ N) (X : ℕ × ℕ → K) (a : ℕ) : ∑ b ∈ Icc 1 N, mesh N X a b = 0 := by
  have h := mesh_telescope N X (p := a) (q := a) (r := 1) (t := N) le_rfl hN
  rw [Icc_self, sum_singleton] at h
  rw [h, planar_congr X (i := a + 1) (j := N + 1) (i' := a + 1) (j' := 1) rfl (pkL_vtx_N1 N),
    planar_congr X (i := a) (j := N + 1) (i' := a) (j' := 1) rfl (pkL_vtx_N1 N)]
  ring

/-- A sum over a set of pairs as a double sum over labels. -/
theorem pkL_sumD {K : Type*} [Field K] {N : ℕ} (X : ℕ × ℕ → K) {D : Finset (ℕ × ℕ)} (hD : D ⊆ diagonals N) :
    ∑ t ∈ D, mesh N X t.1 t.2 = ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, if (a, b) ∈ D then mesh N X a b else 0 := by
  have hsub : (Icc 1 N ×ˢ Icc 1 N).filter (fun t => t ∈ D) = D := by
    rw [filter_mem_eq_inter, inter_eq_right]
    intro t ht
    have := mem_diagonals.1 (hD ht)
    exact mem_product.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, mem_Icc.2 ⟨by omega, by omega⟩⟩
  have h1 := sum_filter (s := Icc 1 N ×ˢ Icc 1 N) (fun t => t ∈ D) (fun t => mesh N X t.1 t.2)
  rw [hsub] at h1
  rw [h1, sum_product]

/-- Block sums: `Σ_{u ≤ a < b ≤ v} c_{a,b} = −X_{u,v+1}` (planar form). -/
theorem pkL_tri {K : Type*} [Field K] {N : ℕ} (hN : 2 ≤ N) (X : ℕ × ℕ → K) {u v : ℕ} (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ N) :
    ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, (if u ≤ a ∧ a < b ∧ b ≤ v then mesh N X a b else 0) =
      - planar N X u (v + 1) := by
  have inner : ∀ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, (if u ≤ a ∧ a < b ∧ b ≤ v then mesh N X a b else 0) =
      if u ≤ a ∧ a ≤ v then planar N X (a + 1) (v + 1) - planar N X a (v + 1) else 0 := by
    intro a ha
    by_cases h : u ≤ a ∧ a ≤ v
    · rw [if_pos h, ← sum_filter]
      have hf : (Icc 1 N).filter (fun b => u ≤ a ∧ a < b ∧ b ≤ v) = Icc (a + 1) v := by
        ext b; simp only [mem_filter, mem_Icc]; omega
      rw [hf]
      by_cases h2 : a < v
      · have ht := mesh_telescope N X (p := a) (q := a) (r := a + 1) (t := v) le_rfl (by omega)
        rw [Icc_self, sum_singleton] at ht
        rw [ht, pkL_pl_succ hN, pkL_pl_self]
        ring
      · have e : a = v := by omega
        rw [Icc_eq_empty (by omega), sum_empty, e, pkL_pl_self, pkL_pl_succ hN]
        ring
    · rw [if_neg h]
      exact sum_eq_zero (fun b _ => by rw [if_neg (by omega)])
  rw [sum_congr rfl inner, ← sum_filter]
  have hf : (Icc 1 N).filter (fun a => u ≤ a ∧ a ≤ v) = Icc u v := by
    ext a; simp only [mem_filter, mem_Icc]; omega
  rw [hf]
  have ht := sum_Icc_telescope (fun a => planar N X a (v + 1)) huv
  have e : ∑ a ∈ Icc u v, (planar N X (a + 1) (v + 1) - planar N X a (v + 1)) =
      - ∑ a ∈ Icc u v, (planar N X a (v + 1) - planar N X (a + 1) (v + 1)) := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl (fun a _ => by ring)
  rw [e, ht, pkL_pl_self]
  ring

theorem pkL_rows {K : Type*} [Field K] {N : ℕ} (hN : 2 ≤ N) (X : ℕ × ℕ → K) (q : ℕ → Prop) [DecidablePred q] :
    ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, ((if q a ∧ a < b then mesh N X a b else 0) +
      (if q b ∧ a < b then mesh N X a b else 0)) = 0 := by
  have hswap : ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, (if q b ∧ a < b then mesh N X a b else 0) =
      ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, (if q a ∧ b < a then mesh N X a b else 0) := by
    rw [sum_comm]
    refine sum_congr rfl (fun a _ => sum_congr rfl (fun b _ => ?_))
    rw [pkL_mesh_comm N X b a]
  have key : ∀ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, ((if q a ∧ a < b then mesh N X a b else 0) +
      (if q a ∧ b < a then mesh N X a b else 0)) = 0 := by
    intro a _
    by_cases hq : q a
    · have e : ∀ b ∈ Icc 1 N, ((if q a ∧ a < b then mesh N X a b else 0) +
          (if q a ∧ b < a then mesh N X a b else 0)) = mesh N X a b := by
        intro b _
        rcases lt_trichotomy a b with h | h | h
        · rw [if_pos ⟨hq, h⟩, if_neg (by omega)]; ring
        · rw [if_neg (by omega), if_neg (by omega), h, pkL_mesh_self hN]; ring
        · rw [if_neg (by omega), if_pos ⟨hq, h⟩]; ring
      rw [sum_congr rfl e]
      exact pkL_row (by omega) X a
    · exact sum_eq_zero (fun b _ => by rw [if_neg (fun h => hq h.1), if_neg (fun h => hq h.1)]; ring)
  have e1 := sum_eq_zero key
  simp only [sum_add_distrib] at e1 ⊢
  rw [hswap]
  exact e1

theorem pkL_rowR {K : Type*} [Field K] {N : ℕ} (hN : 2 ≤ N) (X : ℕ × ℕ → K) {a : ℕ} (ha : a ∈ Icc 1 N) :
    ∑ b ∈ Icc 1 N, (if a < b then mesh N X a b else 0) = planar N X (a + 1) (N + 1) - planar N X a (N + 1) := by
  obtain ⟨ha1, ha2⟩ := mem_Icc.1 ha
  rw [← sum_filter]
  have hf : (Icc 1 N).filter (fun b => a < b) = Icc (a + 1) N := by
    ext b; simp only [mem_filter, mem_Icc]; omega
  rw [hf]
  rcases Nat.lt_or_ge a N with h | h
  · have ht := mesh_telescope N X (p := a) (q := a) (r := a + 1) (t := N) le_rfl (by omega)
    rw [Icc_self, sum_singleton] at ht
    rw [ht, pkL_pl_succ hN, pkL_pl_self]
    ring
  · have e : a = N := by omega
    rw [Icc_eq_empty (by omega), sum_empty, e, pkL_pl_self, pkL_pl_succ hN]
    ring

theorem pkL_rowL {K : Type*} [Field K] {N : ℕ} (hN : 2 ≤ N) (X : ℕ × ℕ → K) {b : ℕ} (hb : b ∈ Icc 1 N) :
    ∑ a ∈ Icc 1 N, (if a < b then mesh N X a b else 0) = planar N X 1 b - planar N X 1 (b + 1) := by
  obtain ⟨hb1, hb2⟩ := mem_Icc.1 hb
  rw [← sum_filter]
  have hf : (Icc 1 N).filter (fun a => a < b) = Icc 1 (b - 1) := by
    ext a; simp only [mem_filter, mem_Icc]; omega
  rw [hf]
  rcases Nat.lt_or_ge 1 b with h | h
  · have ht := mesh_telescope N X (p := 1) (q := b - 1) (r := b) (t := b) (by omega) le_rfl
    simp only [Icc_self, sum_singleton] at ht
    rw [show b - 1 + 1 = b by omega, pkL_pl_succ hN, pkL_pl_self] at ht
    rw [ht]
    ring
  · have e : b = 1 := by omega
    rw [Icc_eq_empty (by omega), sum_empty, e, pkL_pl_self, pkL_pl_succ hN]
    ring

/-- **Lemma 6.5 relation** (char-free proof): `Σ_{ee} c = Σ_{oo} c`. -/
theorem pkL_l65 {K : Type*} [Field K] {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (X : ℕ × ℕ → K) :
    ∑ t ∈ (diagonals N).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0), mesh N X t.1 t.2 =
      ∑ t ∈ (diagonals N).filter (fun p => p.1 % 2 = 1 ∧ p.2 % 2 = 1), mesh N X t.1 t.2 := by
  have hN2 : 2 ≤ N := by omega
  rw [pkL_sumD X (filter_subset _ _), pkL_sumD X (filter_subset _ _)]
  have pw : ∀ a ∈ Icc 1 N, ∀ b ∈ Icc 1 N,
      (if (a, b) ∈ (diagonals N).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0) then mesh N X a b else 0) =
        (if (a, b) ∈ (diagonals N).filter (fun p => p.1 % 2 = 1 ∧ p.2 % 2 = 1) then mesh N X a b else 0) +
        (if a % 2 = 0 ∧ a < b then mesh N X a b else 0) - (if b % 2 = 1 ∧ a < b then mesh N X a b else 0) := by
    intro a ha b hb
    obtain ⟨ha1, ha2⟩ := mem_Icc.1 ha
    obtain ⟨hb1, hb2⟩ := mem_Icc.1 hb
    simp only [mem_filter, mem_diagonals]
    split_ifs <;> (try simp) <;> omega
  rw [sum_congr rfl (fun a ha => sum_congr rfl (fun b hb => pw a ha b hb))]
  simp only [sum_add_distrib, sum_sub_distrib]
  -- the two telescoping parts agree
  have hev : ∀ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, (if a % 2 = 0 ∧ a < b then mesh N X a b else 0) =
      if a % 2 = 0 then planar N X (a + 1) (N + 1) - planar N X a (N + 1) else 0 := by
    intro a ha
    by_cases h : a % 2 = 0
    · rw [if_pos h, ← pkL_rowR hN2 X ha]
      exact sum_congr rfl (fun b _ => by simp only [h, true_and])
    · rw [if_neg h]
      exact sum_eq_zero (fun b _ => by rw [if_neg (by omega)])
  have hod : ∀ b ∈ Icc 1 N, ∑ a ∈ Icc 1 N, (if b % 2 = 1 ∧ a < b then mesh N X a b else 0) =
      if b % 2 = 1 then planar N X b (N + 1) - planar N X (b + 1) (N + 1) else 0 := by
    intro b hb
    by_cases h : b % 2 = 1
    · rw [if_pos h, R12P4A.planar_comm N X b, R12P4A.planar_comm N X (b + 1),
        planar_congr X (i := N + 1) (j := b) (i' := 1) (j' := b) (pkL_vtx_N1 N) rfl,
        planar_congr X (i := N + 1) (j := b + 1) (i' := 1) (j' := b + 1) (pkL_vtx_N1 N) rfl,
        ← pkL_rowL hN2 X hb]
      exact sum_congr rfl (fun a _ => by simp only [h, true_and])
    · rw [if_neg h]
      exact sum_eq_zero (fun a _ => by rw [if_neg (by omega)])
  rw [sum_congr rfl hev, sum_comm (s := Icc 1 N) (t := Icc 1 N)
    (f := fun a b => if b % 2 = 1 ∧ a < b then mesh N X a b else 0), sum_congr rfl hod]
  have htot : ∑ a ∈ Icc 1 N, (if a % 2 = 0 then planar N X (a + 1) (N + 1) - planar N X a (N + 1) else 0) -
      ∑ b ∈ Icc 1 N, (if b % 2 = 1 then planar N X b (N + 1) - planar N X (b + 1) (N + 1) else 0) = 0 := by
    rw [← sum_sub_distrib]
    have e : ∀ a ∈ Icc 1 N, ((if a % 2 = 0 then planar N X (a + 1) (N + 1) - planar N X a (N + 1) else 0) -
        (if a % 2 = 1 then planar N X a (N + 1) - planar N X (a + 1) (N + 1) else 0)) =
        -(planar N X a (N + 1) - planar N X (a + 1) (N + 1)) := by
      intro a _
      by_cases h : a % 2 = 0
      · rw [if_pos h, if_neg (by omega)]
        ring
      · rw [if_neg h, if_pos (by omega)]
        ring
    rw [sum_congr rfl e, sum_neg_distrib, sum_Icc_telescope (fun a => planar N X a (N + 1)) (by omega : 1 ≤ N),
      pkL_pl_self, planar_congr X (i := 1) (j := N + 1) (i' := 1) (j' := 1) rfl (pkL_vtx_N1 N), pkL_pl_self]
    ring
  linear_combination htot

theorem pkL_oddD {N i j : ℕ} (hP : (i, j) ∈ oddDiagonals N) :
    1 ≤ i ∧ j ≤ N ∧ i + 2 ≤ j ∧ ¬ (i = 1 ∧ j = N) ∧ (j - i) % 2 = 1 := by
  have h := mem_filter.1 hP
  have h1 := mem_diagonals.1 h.1
  exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h.2⟩

theorem pkL_mem_oddsA {N i j t : ℕ} (hi : 1 ≤ i) (hj : j ≤ N) :
    t ∈ odds (oddSide N (i, j)) ↔ (1 ≤ t ∧ t ≤ N ∧ t % 2 = 1 ∧ ((i % 2 = 1 ∧ i ≤ t ∧ t ≤ j - 1) ∨ (i % 2 = 0 ∧ ¬ (i ≤ t ∧ t ≤ j - 1)))) := by
  have e : oddSide N (i, j) = if i % 2 = 1 then Icc i (j - 1) else Icc 1 N \ Icc i (j - 1) := rfl
  have e2 : odds (oddSide N (i, j)) = (oddSide N (i, j)).filter (fun a => a % 2 = 1) := rfl
  rw [e2, mem_filter, e]
  by_cases h : i % 2 = 1
  · rw [if_pos h]
    simp only [mem_Icc]
    constructor <;> intro h' <;> omega
  · rw [if_neg h]
    simp only [mem_Icc, mem_sdiff]
    constructor <;> intro h' <;> omega

theorem pkL_mem_evensB {N i j t : ℕ} (hi : 1 ≤ i) (hj : j ≤ N) :
    t ∈ evens (evenSide N (i, j)) ↔ (1 ≤ t ∧ t ≤ N ∧ t % 2 = 0 ∧ ((i % 2 = 1 ∧ ¬ (i ≤ t ∧ t ≤ j - 1)) ∨ (i % 2 = 0 ∧ i ≤ t ∧ t ≤ j - 1))) := by
  have e : oddSide N (i, j) = if i % 2 = 1 then Icc i (j - 1) else Icc 1 N \ Icc i (j - 1) := rfl
  have e2 : evens (evenSide N (i, j)) = (Icc 1 N \ oddSide N (i, j)).filter (fun a => a % 2 = 0) := rfl
  rw [e2, mem_filter, mem_sdiff, e]
  by_cases h : i % 2 = 1
  · rw [if_pos h]
    simp only [mem_Icc]
    constructor <;> intro h' <;> omega
  · rw [if_neg h]
    simp only [mem_Icc, mem_sdiff]
    constructor <;> intro h' <;> omega

theorem pkL_mem_sep {N : ℕ} {G : Finset ℕ} {a b : ℕ} :
    (a, b) ∈ sepPairs N G ↔ (a, b) ∈ diagonals N ∧ InST G a b := by
  show (a, b) ∈ (diagonals N).filter (fun p => InST G p.1 p.2) ↔ _
  rw [mem_filter]

theorem pkL_inST_iff {T : Finset ℕ} {a b : ℕ} (hab : a < b) :
    InST T a b ↔ a ∉ T ∧ b ∉ T ∧ (∃ t ∈ T, a < t ∧ t < b) ∧ (∃ t ∈ T, t < a ∨ b < t) := by
  show (a ∉ T ∧ b ∉ T ∧ (∃ t ∈ T, min a b < t ∧ t < max a b) ∧ (∃ t ∈ T, t < min a b ∨ max a b < t)) ↔ _
  rw [min_eq_left hab.le, max_eq_right hab.le]

set_option maxHeartbeats 1000000 in
theorem pkL_memH_toA {N i j a b : ℕ} (hP : (i, j) ∈ oddDiagonals N) (hab : a < b) (ha : 1 ≤ a) (hb : b ≤ N)
    (h : (a, b) ∈ oddSideSplit N (i, j)) :
    (i ≤ a ∧ a ≤ j - 1 ∧ i ≤ b ∧ b ≤ j - 1 ∧ a % 2 ≠ i % 2 ∧ b % 2 ≠ i % 2) ∨
      (i ≤ a ∧ a ≤ j - 1 ∧ j ≤ b ∧ (a % 2 ≠ i % 2 ∨ b % 2 = i % 2)) ∨
      (a < i ∧ i ≤ b ∧ b ≤ j - 1 ∧ (b % 2 ≠ i % 2 ∨ a % 2 = i % 2)) ∨
      ((b < i ∨ j ≤ a ∨ (a < i ∧ j ≤ b)) ∧ a % 2 = i % 2 ∧ b % 2 = i % 2) := by
  obtain ⟨hi1, hjN, hij, hne, hodd⟩ := pkL_oddD hP
  obtain ⟨hA, hB, ⟨t1, ht1, h11, h12⟩, ⟨t2, ht2, h2⟩⟩ := (pkL_inST_iff hab).1 (pkL_mem_sep.1 h).2
  rw [pkL_mem_oddsA hi1 hjN] at hA hB ht1 ht2
  rcases Nat.mod_two_eq_zero_or_one i with hp | hp <;>
    simp only [hp, Nat.zero_ne_one, Nat.one_ne_zero, false_and, true_and, or_false, false_or, ne_eq] at hA hB ht1 ht2 ⊢ <;>
    rcases h2 with h2 | h2 <;> rcases Nat.lt_or_ge a i with ha' | ha' <;>
    rcases Nat.lt_or_ge (j - 1) b with hb' | hb' <;> omega

set_option maxHeartbeats 1000000 in
theorem pkL_memH_toB {N i j a b : ℕ} (hP : (i, j) ∈ oddDiagonals N) (hab : a < b) (ha : 1 ≤ a) (hb : b ≤ N)
    (h : (a, b) ∈ evenSideSplit N (i, j)) :
    (i ≤ a ∧ a ≤ j - 1 ∧ i ≤ b ∧ b ≤ j - 1 ∧ a % 2 ≠ i % 2 ∧ b % 2 ≠ i % 2) ∨
      (i ≤ a ∧ a ≤ j - 1 ∧ j ≤ b ∧ (a % 2 ≠ i % 2 ∨ b % 2 = i % 2)) ∨
      (a < i ∧ i ≤ b ∧ b ≤ j - 1 ∧ (b % 2 ≠ i % 2 ∨ a % 2 = i % 2)) ∨
      ((b < i ∨ j ≤ a ∨ (a < i ∧ j ≤ b)) ∧ a % 2 = i % 2 ∧ b % 2 = i % 2) := by
  obtain ⟨hi1, hjN, hij, hne, hodd⟩ := pkL_oddD hP
  obtain ⟨hA, hB, ⟨t1, ht1, h11, h12⟩, ⟨t2, ht2, h2⟩⟩ := (pkL_inST_iff hab).1 (pkL_mem_sep.1 h).2
  rw [pkL_mem_evensB hi1 hjN] at hA hB ht1 ht2
  rcases Nat.mod_two_eq_zero_or_one i with hp | hp <;>
    simp only [hp, Nat.zero_ne_one, Nat.one_ne_zero, false_and, true_and, or_false, false_or, ne_eq] at hA hB ht1 ht2 ⊢ <;>
    rcases h2 with h2 | h2 <;> rcases Nat.lt_or_ge a i with ha' | ha' <;>
    rcases Nat.lt_or_ge (j - 1) b with hb' | hb' <;> omega

/-- Membership in `H^A ∪ H^B` for a mixed chord `(i, j)`, forward direction. -/
theorem pkL_memH_to {N i j a b : ℕ} (hP : (i, j) ∈ oddDiagonals N) (hab : a < b)
    (h : (a, b) ∈ oddSideSplit N (i, j) ∪ evenSideSplit N (i, j)) :
    (i ≤ a ∧ a ≤ j - 1 ∧ i ≤ b ∧ b ≤ j - 1 ∧ a % 2 ≠ i % 2 ∧ b % 2 ≠ i % 2) ∨
      (i ≤ a ∧ a ≤ j - 1 ∧ j ≤ b ∧ (a % 2 ≠ i % 2 ∨ b % 2 = i % 2)) ∨
      (a < i ∧ i ≤ b ∧ b ≤ j - 1 ∧ (b % 2 ≠ i % 2 ∨ a % 2 = i % 2)) ∨
      ((b < i ∨ j ≤ a ∨ (a < i ∧ j ≤ b)) ∧ a % 2 = i % 2 ∧ b % 2 = i % 2) := by
  have hd := mem_diagonals.1 ((union_subset (fun t ht => (mem_filter.1 ht).1) (fun t ht => (mem_filter.1 ht).1) :
    oddSideSplit N (i, j) ∪ evenSideSplit N (i, j) ⊆ diagonals N) h)
  dsimp only at hd
  rcases mem_union.1 h with h | h
  · exact pkL_memH_toA hP hab (by omega) (by omega) h
  · exact pkL_memH_toB hP hab (by omega) (by omega) h

/-- Membership in `H^A ∪ H^B`, backward direction (explicit witnesses). -/
theorem pkL_memH_of {N i j a b : ℕ} (hE : N % 2 = 0) (hP : (i, j) ∈ oddDiagonals N) (ha : 1 ≤ a)
    (hab : a < b) (hb : b ≤ N) (h : (i ≤ a ∧ a ≤ j - 1 ∧ i ≤ b ∧ b ≤ j - 1 ∧ a % 2 ≠ i % 2 ∧ b % 2 ≠ i % 2) ∨
      (i ≤ a ∧ a ≤ j - 1 ∧ j ≤ b ∧ (a % 2 ≠ i % 2 ∨ b % 2 = i % 2)) ∨
      (a < i ∧ i ≤ b ∧ b ≤ j - 1 ∧ (b % 2 ≠ i % 2 ∨ a % 2 = i % 2)) ∨
      ((b < i ∨ j ≤ a ∨ (a < i ∧ j ≤ b)) ∧ a % 2 = i % 2 ∧ b % 2 = i % 2)) :
    (a, b) ∈ oddSideSplit N (i, j) ∪ evenSideSplit N (i, j) := by
  obtain ⟨hi1, hjN, hij, hne, hodd⟩ := pkL_oddD hP
  have hA : ∀ t1 t2, a < t1 → t1 < b → (t2 < a ∨ b < t2) → (1 ≤ t1 ∧ t1 ≤ N ∧ t1 % 2 = 1 ∧ ((i % 2 = 1 ∧ i ≤ t1 ∧ t1 ≤ j - 1) ∨ (i % 2 = 0 ∧ ¬ (i ≤ t1 ∧ t1 ≤ j - 1)))) → (1 ≤ t2 ∧ t2 ≤ N ∧ t2 % 2 = 1 ∧ ((i % 2 = 1 ∧ i ≤ t2 ∧ t2 ≤ j - 1) ∨ (i % 2 = 0 ∧ ¬ (i ≤ t2 ∧ t2 ≤ j - 1)))) → ¬ (1 ≤ a ∧ a ≤ N ∧ a % 2 = 1 ∧ ((i % 2 = 1 ∧ i ≤ a ∧ a ≤ j - 1) ∨ (i % 2 = 0 ∧ ¬ (i ≤ a ∧ a ≤ j - 1)))) → ¬ (1 ≤ b ∧ b ≤ N ∧ b % 2 = 1 ∧ ((i % 2 = 1 ∧ i ≤ b ∧ b ≤ j - 1) ∨ (i % 2 = 0 ∧ ¬ (i ≤ b ∧ b ≤ j - 1)))) →
      (a, b) ∈ oddSideSplit N (i, j) ∪ evenSideSplit N (i, j) := by
    intro t1 t2 h1 h2 h3 m1 m2 ma mb
    refine mem_union.2 (Or.inl (pkL_mem_sep.2 ⟨mem_diagonals.2 (by dsimp only; omega), (pkL_inST_iff hab).2
      ⟨?_, ?_, ⟨t1, (pkL_mem_oddsA hi1 hjN).2 m1, h1, h2⟩, ⟨t2, (pkL_mem_oddsA hi1 hjN).2 m2, h3⟩⟩⟩))
    · rw [pkL_mem_oddsA hi1 hjN]; exact ma
    · rw [pkL_mem_oddsA hi1 hjN]; exact mb
  have hB : ∀ t1 t2, a < t1 → t1 < b → (t2 < a ∨ b < t2) → (1 ≤ t1 ∧ t1 ≤ N ∧ t1 % 2 = 0 ∧ ((i % 2 = 1 ∧ ¬ (i ≤ t1 ∧ t1 ≤ j - 1)) ∨ (i % 2 = 0 ∧ i ≤ t1 ∧ t1 ≤ j - 1))) → (1 ≤ t2 ∧ t2 ≤ N ∧ t2 % 2 = 0 ∧ ((i % 2 = 1 ∧ ¬ (i ≤ t2 ∧ t2 ≤ j - 1)) ∨ (i % 2 = 0 ∧ i ≤ t2 ∧ t2 ≤ j - 1))) → ¬ (1 ≤ a ∧ a ≤ N ∧ a % 2 = 0 ∧ ((i % 2 = 1 ∧ ¬ (i ≤ a ∧ a ≤ j - 1)) ∨ (i % 2 = 0 ∧ i ≤ a ∧ a ≤ j - 1))) → ¬ (1 ≤ b ∧ b ≤ N ∧ b % 2 = 0 ∧ ((i % 2 = 1 ∧ ¬ (i ≤ b ∧ b ≤ j - 1)) ∨ (i % 2 = 0 ∧ i ≤ b ∧ b ≤ j - 1))) →
      (a, b) ∈ oddSideSplit N (i, j) ∪ evenSideSplit N (i, j) := by
    intro t1 t2 h1 h2 h3 m1 m2 ma mb
    refine mem_union.2 (Or.inr (pkL_mem_sep.2 ⟨mem_diagonals.2 (by dsimp only; omega), (pkL_inST_iff hab).2
      ⟨?_, ?_, ⟨t1, (pkL_mem_evensB hi1 hjN).2 m1, h1, h2⟩, ⟨t2, (pkL_mem_evensB hi1 hjN).2 m2, h3⟩⟩⟩))
    · rw [pkL_mem_evensB hi1 hjN]; exact ma
    · rw [pkL_mem_evensB hi1 hjN]; exact mb
  rcases Nat.mod_two_eq_zero_or_one i with hp | hp
  · rcases h with h | h | h | h
    · exact hB (a + 1) i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · by_cases ha2 : a % 2 = 0
      · exact hA j (i - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      · exact hB (j - 1) i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · by_cases hb2 : b % 2 = 0
      · exact hA (i - 1) j (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      · exact hB i (j - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · by_cases hc : a < i ∧ j ≤ b
      · exact hA (i - 1) 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      · exact hA (a + 1) j (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · rcases h with h | h | h | h
    · exact hA (a + 1) i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · by_cases ha2 : a % 2 = 0
      · exact hA (j - 1) i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      · by_cases hi3 : 3 ≤ i
        · exact hB j (i - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        · exact hB j N (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · by_cases hb2 : b % 2 = 0
      · exact hA i (j - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      · exact hB (i - 1) j (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · by_cases hc : a < i ∧ j ≤ b
      · exact hB (i - 1) N (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      · exact hB (a + 1) j (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem pkL_memH_not {N i j a b : ℕ} (hE : N % 2 = 0) (hP : (i, j) ∈ oddDiagonals N) (ha : 1 ≤ a)
    (hab : a < b) (hb : b ≤ N) (hH : (a, b) ∉ oddSideSplit N (i, j) ∪ evenSideSplit N (i, j)) :
    ¬ ((i ≤ a ∧ a ≤ j - 1 ∧ i ≤ b ∧ b ≤ j - 1 ∧ a % 2 ≠ i % 2 ∧ b % 2 ≠ i % 2) ∨
      (i ≤ a ∧ a ≤ j - 1 ∧ j ≤ b ∧ (a % 2 ≠ i % 2 ∨ b % 2 = i % 2)) ∨
      (a < i ∧ i ≤ b ∧ b ≤ j - 1 ∧ (b % 2 ≠ i % 2 ∨ a % 2 = i % 2)) ∨
      ((b < i ∨ j ≤ a ∨ (a < i ∧ j ≤ b)) ∧ a % 2 = i % 2 ∧ b % 2 = i % 2)) := fun h => hH (pkL_memH_of hE hP ha hab hb h)

/-- **[Hit] at S = ∅** (the face-form identity, X-level): `X_P = Σ_{H^A ∪ H^B} c − Σ_{ee} c`. -/
theorem pkL_hit0 {K : Type*} [Field K] {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (X : ℕ × ℕ → K) {i j : ℕ}
    (hP : (i, j) ∈ oddDiagonals N) :
    X (i, j) = ∑ t ∈ oddSideSplit N (i, j) ∪ evenSideSplit N (i, j), mesh N X t.1 t.2 -
      ∑ t ∈ (diagonals N).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0), mesh N X t.1 t.2 := by
  obtain ⟨hi1, hjN, hij, hne, hodd⟩ := pkL_oddD hP
  have hN2 : 2 ≤ N := by omega
  have hHsub : oddSideSplit N (i, j) ∪ evenSideSplit N (i, j) ⊆ diagonals N :=
    union_subset (fun t ht => (mem_filter.1 ht).1) (fun t ht => (mem_filter.1 ht).1)
  have pw : ∀ a ∈ Icc 1 N, ∀ b ∈ Icc 1 N,
      (if (a, b) ∈ oddSideSplit N (i, j) ∪ evenSideSplit N (i, j) then mesh N X a b else 0) =
        ((if (i ≤ a ∧ a ≤ j - 1 ∧ a % 2 ≠ i % 2) ∧ a < b then mesh N X a b else 0) +
        (if (i ≤ b ∧ b ≤ j - 1 ∧ b % 2 ≠ i % 2) ∧ a < b then mesh N X a b else 0)) +
        (if (a, b) ∈ (diagonals N).filter (fun p => p.1 % 2 = i % 2 ∧ p.2 % 2 = i % 2) then mesh N X a b
          else 0) -
        (if i ≤ a ∧ a < b ∧ b ≤ j - 1 then mesh N X a b else 0) := by
    intro a ha b hb
    obtain ⟨ha1, ha2⟩ := mem_Icc.1 ha
    obtain ⟨hb1, hb2⟩ := mem_Icc.1 hb
    by_cases hab : a < b
    · by_cases hH : (a, b) ∈ oddSideSplit N (i, j) ∪ evenSideSplit N (i, j)
      · have hΦ := pkL_memH_to hP hab hH
        rw [if_pos hH]
        simp only [mem_filter, mem_diagonals]
        split_ifs <;> (try simp) <;> omega
      · have hΦ := pkL_memH_not hE hP ha1 hab hb2 hH
        rw [if_neg hH]
        simp only [mem_filter, mem_diagonals]
        split_ifs <;> (try simp) <;> omega
    · have hH : (a, b) ∉ oddSideSplit N (i, j) ∪ evenSideSplit N (i, j) := fun h => hab (by
        have := mem_diagonals.1 (hHsub h); dsimp only at this; omega)
      rw [if_neg hH]
      simp only [mem_filter, mem_diagonals]
      split_ifs <;> (try simp) <;> omega
  rw [pkL_sumD X hHsub, sum_congr rfl (fun a ha => sum_congr rfl (fun b hb => pw a ha b hb))]
  simp only [sum_add_distrib, sum_sub_distrib]
  have hrows := pkL_rows hN2 X (fun x => i ≤ x ∧ x ≤ j - 1 ∧ x % 2 ≠ i % 2)
  simp only [sum_add_distrib] at hrows
  rw [hrows, pkL_tri hN2 X hi1 (by omega : i ≤ j - 1) (by omega : j - 1 ≤ N),
    ← pkL_sumD X (filter_subset _ _), show j - 1 + 1 = j by omega, planar_eq_X X hi1 hij hjN hne]
  rcases Nat.mod_two_eq_zero_or_one i with hp | hp
  · rw [hp]
    ring
  · rw [hp, ← pkL_l65 hN hE X]
    ring




/-! ### pkgLin helpers (`pkL_`): 𝒢_N antichain and witness points -/

theorem pkL_gprops {N : ℕ} (hE : N % 2 = 0) {G : Finset ℕ} (hG : G ∈ gLegSets N) :
    G ⊆ Icc 1 N ∧ 1 < G.card ∧ (∀ g ∈ G, g + 1 ∉ G) ∧ ¬ (1 ∈ G ∧ N ∈ G) := by
  have h := mem_filter.1 hG
  have hsub : G ⊆ Icc 1 N := mem_powerset.1 h.1
  refine ⟨hsub, ?_⟩
  rcases h.2 with hS | hM
  · have hpar : ∃ r, 2 ≤ G.card ∧ ∀ t ∈ G, t % 2 = r := by
      rcases hS with h0 | h1
      · exact ⟨0, h0.2.1, h0.2.2⟩
      · exact ⟨1, h1.2.1, h1.2.2⟩
    obtain ⟨r, hc, hr⟩ := hpar
    refine ⟨by omega, fun g hg hg1 => ?_, fun h1N => ?_⟩
    · have e1 := hr g hg
      have e2 := hr (g + 1) hg1
      omega
    · have e1 := hr 1 h1N.1
      have e2 := hr N h1N.2
      omega
  · obtain ⟨a, ha, b, hb, rfl, hab, hne, hpar⟩ := hM
    rw [mem_Icc] at ha hb
    refine ⟨?_, ?_, ?_⟩
    · rw [card_pair (by omega)]
      omega
    · intro g hg hg1
      simp only [mem_insert, mem_singleton] at hg hg1
      omega
    · intro h1N
      have e1 := h1N.1
      have e2 := h1N.2
      simp only [mem_insert, mem_singleton] at e1 e2
      omega

theorem pkL_sep_mk {N : ℕ} {G : Finset ℕ} (hsub : G ⊆ Icc 1 N) {u v t1 t2 : ℕ} (huv : u < v) (hu : 1 ≤ u)
    (hv : v ≤ N) (hu' : u ∉ G) (hv' : v ∉ G) (ht1 : t1 ∈ G) (h1 : u < t1) (h2 : t1 < v) (ht2 : t2 ∈ G)
    (h3 : t2 < u ∨ v < t2) : (u, v) ∈ sepPairs N G := by
  have ht2' := mem_Icc.1 (hsub ht2)
  exact pkL_mem_sep.2 ⟨mem_diagonals.2 (by dsimp only; omega),
    (pkL_inST_iff huv).2 ⟨hu', hv', ⟨t1, ht1, h1, h2⟩, ⟨t2, ht2, h3⟩⟩⟩

/-- Every leg outside `G` lies on a pair of `S_G`. -/
theorem pkL_supp {N : ℕ} (hE : N % 2 = 0) {G : Finset ℕ} (hG : G ∈ gLegSets N) {x : ℕ} (hx : x ∈ Icc 1 N)
    (hxG : x ∉ G) : ∃ p ∈ sepPairs N G, p.1 = x ∨ p.2 = x := by
  obtain ⟨hsub, hc, hadj, h1N⟩ := pkL_gprops hE hG
  have hne : G.Nonempty := card_pos.1 (by omega)
  have hlo := min'_mem G hne
  have hhi := max'_mem G hne
  have hlt : G.min' hne < G.max' hne := min'_lt_max'_of_card G hc
  have hlo1 := mem_Icc.1 (hsub hlo)
  have hhi1 := mem_Icc.1 (hsub hhi)
  have hlow : ∀ y, y < G.min' hne → y ∉ G := fun y hy hyG => by
    have := min'_le G y hyG
    omega
  have hhigh : ∀ y, G.max' hne < y → y ∉ G := fun y hy hyG => by
    have := le_max' G y hyG
    omega
  have hl1 : G.min' hne + 1 ∉ G := hadj _ hlo
  have hlt1 : G.min' hne + 1 < G.max' hne := by
    rcases Nat.lt_or_ge (G.min' hne + 1) (G.max' hne) with h | h
    · exact h
    · have e : G.min' hne + 1 = G.max' hne := by omega
      rw [e] at hl1
      exact absurd hhi hl1
  have hxl : x ≠ G.min' hne := fun e => hxG (e ▸ hlo)
  have hxh : x ≠ G.max' hne := fun e => hxG (e ▸ hhi)
  rw [mem_Icc] at hx
  rcases Nat.lt_or_ge x (G.min' hne) with h | h
  · exact ⟨_, pkL_sep_mk hsub (u := x) (v := G.min' hne + 1) (t1 := G.min' hne) (t2 := G.max' hne) (by omega)
      (by omega) (by omega) hxG hl1 hlo (by omega) (by omega) hhi (by omega), Or.inl rfl⟩
  · rcases Nat.lt_or_ge (G.max' hne) x with h' | h'
    · exact ⟨_, pkL_sep_mk hsub (u := G.min' hne + 1) (v := x) (t1 := G.max' hne) (t2 := G.min' hne) (by omega)
        (by omega) (by omega) hl1 hxG hhi (by omega) (by omega) hlo (by omega), Or.inr rfl⟩
    · by_cases h2 : 2 ≤ G.min' hne
      · exact ⟨_, pkL_sep_mk hsub (u := G.min' hne - 1) (v := x) (t1 := G.min' hne) (t2 := G.max' hne) (by omega)
          (by omega) (by omega) (hlow _ (by omega)) hxG hlo (by omega) (by omega) hhi (by omega), Or.inr rfl⟩
      · by_cases h3 : G.max' hne + 1 ≤ N
        · exact ⟨_, pkL_sep_mk hsub (u := x) (v := G.max' hne + 1) (t1 := G.max' hne) (t2 := G.min' hne)
            (by omega) (by omega) (by omega) hxG (hhigh _ (by omega)) hhi (by omega) (by omega) hlo (by omega),
            Or.inl rfl⟩
        · have e1 : G.min' hne = 1 := by omega
          have e2 : G.max' hne = N := by omega
          rw [e1] at hlo
          rw [e2] at hhi
          exact absurd ⟨hlo, hhi⟩ h1N

/-- A leg of `G` outside `G'` gives a pair of `S_G` outside `S_{G'}` (its two neighbours). -/
theorem pkL_sep_step {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {G G' : Finset ℕ} (hG : G ∈ gLegSets N)
    (hG' : G' ⊆ Icc 1 N) {t : ℕ} (ht : t ∈ G) (ht' : t ∉ G') : ∃ p ∈ sepPairs N G, p ∉ sepPairs N G' := by
  obtain ⟨hsub, hc, hadj, h1N⟩ := pkL_gprops hE hG
  obtain ⟨g, hg, hgt⟩ : ∃ g ∈ G, g ≠ t := by
    obtain ⟨u, hu, v, hv, huv⟩ := one_lt_card.1 hc
    by_cases h : u = t
    · exact ⟨v, hv, fun h' => huv (h.trans h'.symm)⟩
    · exact ⟨u, hu, h⟩
  have htI := mem_Icc.1 (hsub ht)
  have hgI := mem_Icc.1 (hsub hg)
  have hgp : g ≠ t + 1 := fun e => hadj t ht (e ▸ hg)
  have hgm : g + 1 ≠ t := fun e => hadj g hg (e ▸ ht)
  have hnot : ∀ u v, u < v → (u, v) ∈ sepPairs N G' → (∀ s, u < s → s < v → s = t) ∨ (∀ s, s ∈ Icc 1 N → (s < u ∨ v < s) → s = t) → False := by
    intro u v huv hp hs
    obtain ⟨-, -, ⟨s1, hs1, h11, h12⟩, ⟨s2, hs2, h2⟩⟩ := (pkL_inST_iff huv).1 (pkL_mem_sep.1 hp).2
    rcases hs with hs | hs
    · exact ht' (hs s1 h11 h12 ▸ hs1)
    · exact ht' (hs s2 (hG' hs2) h2 ▸ hs2)
  rcases Nat.lt_or_ge 1 t with h1 | h1
  · rcases Nat.lt_or_ge t N with h2 | h2
    · -- the pair (t − 1, t + 1)
      have hm1 : t - 1 ∉ G := fun hm => hadj (t - 1) hm (by rw [show t - 1 + 1 = t by omega]; exact ht)
      refine ⟨(t - 1, t + 1), pkL_sep_mk hsub (t1 := t) (t2 := g) (by omega) (by omega) (by omega) hm1
        (hadj t ht) ht (by omega) (by omega) hg (by omega), fun hp => hnot _ _ (by omega) hp (Or.inl ?_)⟩
      intro s hs1 hs2
      omega
    · -- t = N: the pair (1, N − 1)
      have hN1 : N - 1 ∉ G := fun hm => hadj (N - 1) hm (by rw [show N - 1 + 1 = t by omega]; exact ht)
      have h1G : 1 ∉ G := fun hm => h1N ⟨hm, by rw [show N = t by omega]; exact ht⟩
      have hg1 : g ≠ 1 := fun e => h1N ⟨by rw [← e]; exact hg, by rw [show N = t by omega]; exact ht⟩
      refine ⟨(1, N - 1), pkL_sep_mk hsub (t1 := g) (t2 := t) (by omega) le_rfl (by omega) h1G hN1 hg
        (by omega) (by omega) ht (by omega), fun hp => hnot _ _ (by omega) hp (Or.inr ?_)⟩
      intro s hs hs'
      rw [mem_Icc] at hs
      omega
  · -- t = 1: the pair (2, N)
    have hNG : N ∉ G := fun hm => h1N ⟨by rw [show 1 = t by omega]; exact ht, hm⟩
    have h2G : 2 ∉ G := by rw [show 2 = t + 1 by omega]; exact hadj t ht
    have hgN : g ≠ N := fun e => h1N ⟨by rw [show 1 = t by omega]; exact ht, by rw [← e]; exact hg⟩
    refine ⟨(2, N), pkL_sep_mk hsub (t1 := g) (t2 := t) (by omega) (by omega) le_rfl h2G hNG hg
      (by omega) (by omega) ht (by omega), fun hp => hnot _ _ (by omega) hp (Or.inr ?_)⟩
    intro s hs hs'
    rw [mem_Icc] at hs
    omega


/-- A point of the `(k, m)`-rectangle locus with `m = a + 1`, `k = b − a − 1` lies on `L_{S_{a,b}}`. -/
theorem pkL_onLocus_anchor {N a b : ℕ} (hN : 4 ≤ N) (ha : 1 ≤ a) (hab : a + 2 ≤ b) (hb : b ≤ N)
    {X : ℕ × ℕ → ℚ} (hR : OnRect N (b - a - 1) (a + 1) X) : OnLocus N (sepPairs N {a, b}) X := by
  intro p hp
  obtain ⟨hd, hst⟩ := mem_filter.1 hp
  have hd' := mem_diagonals.1 hd
  obtain ⟨hA, hB, ⟨s1, hs1, h11, h12⟩, ⟨s2, hs2, h2⟩⟩ := (pkL_inST_iff (show p.1 < p.2 by omega)).1 hst
  simp only [mem_insert, mem_singleton] at hA hB hs1 hs2
  have hR' : ∀ i ∈ Ico (a + 1) (a + 1 + (b - a - 1)), ∀ j ∈ Icc (b - a - 1 + (a + 1) + 1) (a + 1 + N - 2),
      mesh N X i j = 0 := hR
  rcases hs1 with e1 | e1 <;> rcases hs2 with e2 | e2
  · omega
  · -- p.1 < a < p.2 and b outside: p.1 < a, p.2 ∈ (a, b)
    have := hR' p.2 (mem_Ico.2 ⟨by omega, by omega⟩) (p.1 + N) (mem_Icc.2 ⟨by omega, by omega⟩)
    have e : mesh N X p.2 (p.1 + N) = mesh N X p.2 p.1 := by
      rw [pkL_mesh_eq, pkL_mesh_eq,
        planar_congr X (i := p.2) (j := p.1 + N) (i' := p.2) (j' := p.1) rfl (vtx_add_n N p.1),
        planar_congr X (i := p.2 + 1) (j := p.1 + N + 1) (i' := p.2 + 1) (j' := p.1 + 1) rfl
          (by rw [show p.1 + N + 1 = (p.1 + 1) + N by omega, vtx_add_n]),
        planar_congr X (i := p.2) (j := p.1 + N + 1) (i' := p.2) (j' := p.1 + 1) rfl
          (by rw [show p.1 + N + 1 = (p.1 + 1) + N by omega, vtx_add_n]),
        planar_congr X (i := p.2 + 1) (j := p.1 + N) (i' := p.2 + 1) (j' := p.1) rfl (vtx_add_n N p.1)]
    rw [pkL_mesh_comm, ← e]
    exact this
  · -- a < p.1 < b < p.2
    exact hR' p.1 (mem_Ico.2 ⟨by omega, by omega⟩) p.2 (mem_Icc.2 ⟨by omega, by omega⟩)
  · omega


/-! ### pkgLin helpers (`pkL_`): [Fπ] — Gram points (base `p3b_Xs`) with alternating-path matrices -/

def pkL_tau (x y : ℕ) : ℚ := if x % 2 = y % 2 then (if x % 2 = 0 then 1 else -1) else 0

theorem pkL_planar_sign {N x y : ℕ} (hE : N % 2 = 0) (hx1 : 1 ≤ x) (hxN : x ≤ N) (hy1 : 1 ≤ y) (hyN : y ≤ N)
    (hxy : x ≠ y) :
    planar N (fun d => ((shiftSign d : ℤ) : ℚ)) x y = pkL_tau x y := by
  unfold planar
  rw [vtx_of_mem hx1 hxN, vtx_of_mem hy1 hyN]
  rcases lt_or_gt_of_ne hxy with h | h
  · rw [min_eq_left h.le, max_eq_right h.le]
    split_ifs with hd
    · rw [mem_diagonals] at hd
      unfold shiftSign pkL_tau
      dsimp only
      split_ifs <;> (try omega) <;> norm_num
    · rw [mem_diagonals] at hd
      dsimp only at hd
      unfold pkL_tau
      simp [show ¬ (x % 2 = y % 2) by omega]
  · rw [min_eq_right h.le, max_eq_left h.le]
    split_ifs with hd
    · rw [mem_diagonals] at hd
      unfold shiftSign pkL_tau
      dsimp only
      split_ifs <;> (try omega) <;> norm_num
    · rw [mem_diagonals] at hd
      dsimp only at hd
      unfold pkL_tau
      simp [show ¬ (x % 2 = y % 2) by omega]

/-- (copy of pkgBridge `pkBr_mesh_sign`, which sits after `fpi_iff` in the merged file) `c(v₀) = 0` on every tile `(u, v) ∈ diagonals N`, `N` even (Z26 Lemma 3.2; reproved here). -/
theorem pkL_mesh_sign {N : ℕ} (hE : N % 2 = 0) {u v : ℕ} (huv : (u, v) ∈ diagonals N) :
    mesh N (fun d => ((shiftSign d : ℤ) : ℚ)) u v = 0 := by
  rw [mem_diagonals] at huv
  dsimp only at huv
  obtain ⟨h1, h2, h3, h4⟩ := huv
  unfold mesh
  rcases lt_or_eq_of_le h2 with hv | hv
  · rw [pkL_planar_sign hE h1 (by omega) (by omega) h2 (by omega),
      pkL_planar_sign hE (by omega) (by omega) (by omega) (by omega) (by omega),
      pkL_planar_sign hE h1 (by omega) (by omega) (by omega) (by omega),
      pkL_planar_sign hE (by omega) (by omega) (by omega) h2 (by omega)]
    unfold pkL_tau
    split_ifs <;> (try omega) <;> norm_num
  · rw [hv]
    have hw : ∀ x, planar N (fun d => ((shiftSign d : ℤ) : ℚ)) x (N + 1) =
        planar N (fun d => ((shiftSign d : ℤ) : ℚ)) x 1 := by
      intro x
      unfold planar
      rw [show N + 1 = 1 + N by omega, vtx_add_n]
    rw [hw, hw, pkL_planar_sign hE h1 (by omega) (by omega) le_rfl (by omega),
      pkL_planar_sign hE (by omega) (by omega) (by omega) (by omega) (by omega),
      pkL_planar_sign hE h1 (by omega) le_rfl (by omega) (by omega),
      pkL_planar_sign hE (by omega) (by omega) (by omega) le_rfl (by omega)]
    unfold pkL_tau
    split_ifs <;> (try omega) <;> norm_num


/-- The alternating path on the adjacent pairs `(x, x + 1)`, `a ≤ x < b`, with sign `(−1)^(x − a)` (symmetric). -/
def pkL_path (a b x y : ℕ) : ℚ :=
  (if y = x + 1 ∧ a ≤ x ∧ x < b then (-1 : ℚ) ^ (x - a) else 0) +
    (if x = y + 1 ∧ a ≤ y ∧ y < b then (-1 : ℚ) ^ (y - a) else 0)

theorem pkL_path_eq (a b x y : ℕ) : pkL_path a b x y =
    (if y = x + 1 ∧ a ≤ x ∧ x < b then (-1 : ℚ) ^ (x - a) else 0) +
      (if x = y + 1 ∧ a ≤ y ∧ y < b then (-1 : ℚ) ^ (y - a) else 0) := rfl

theorem pkL_path_symm (a b x y : ℕ) : pkL_path a b x y = pkL_path a b y x := by
  rw [pkL_path_eq, pkL_path_eq, add_comm]

theorem pkL_path_diag (a b x : ℕ) : pkL_path a b x x = 0 := by
  rw [pkL_path_eq, if_neg (by omega), add_zero]

theorem pkL_path_far {a b x y : ℕ} (h : x + 2 ≤ y) : pkL_path a b x y = 0 := by
  rw [pkL_path_eq, if_neg (by omega), if_neg (by omega), add_zero]

theorem pkL_path_row {N a b x : ℕ} (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ N) (hodd : (b - a) % 2 = 1)
    (hx : x ∈ Icc 1 N) :
    ∑ y ∈ Icc 1 N, pkL_path a b x y = (if x = a then 1 else 0) + (if x = b then 1 else 0) := by
  obtain ⟨hx1, hxN⟩ := mem_Icc.1 hx
  simp only [pkL_path_eq, sum_add_distrib]
  rw [sum_eq_single (x + 1) (fun y _ hy => by rw [if_neg (by omega)]) (fun h => by
      rw [if_neg]
      intro hc
      exact h (mem_Icc.2 ⟨by omega, by omega⟩)),
    sum_eq_single (x - 1) (fun y _ hy => by rw [if_neg (by omega)]) (fun h => by
      rw [if_neg]
      intro hc
      exact h (mem_Icc.2 ⟨by omega, by omega⟩))]
  have hpow : ∀ n : ℕ, (-1 : ℚ) ^ (n + 1) + (-1 : ℚ) ^ n = 0 := fun n => by rw [pow_succ]; ring
  have hev : (-1 : ℚ) ^ (b - 1 - a) = 1 := (Nat.even_iff.2 (by omega)).neg_one_pow
  by_cases h1 : x = a
  · rw [if_pos ⟨rfl, by omega, by omega⟩, if_neg (by omega), if_pos h1, if_neg (by omega), h1, Nat.sub_self,
      pow_zero]
  · by_cases h2 : x = b
    · rw [if_neg (by omega), if_pos ⟨by omega, by omega, by omega⟩, if_neg h1, if_pos h2, h2, hev]
    · by_cases h3 : a < x ∧ x < b
      · rw [if_pos ⟨rfl, by omega, by omega⟩, if_pos ⟨by omega, by omega, by omega⟩, if_neg h1, if_neg h2,
          show x - a = (x - 1 - a) + 1 by omega, hpow, add_zero]
      · rw [if_neg (by omega), if_neg (by omega), if_neg h1, if_neg h2]

theorem pkL_path_row' {N a b x : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (haN : a ≤ N) (hbN : b ≤ N) (hp : a % 2 ≠ b % 2)
    (hx : x ∈ Icc 1 N) :
    ∑ y ∈ Icc 1 N, pkL_path (min a b) (max a b) x y = (if x = a then 1 else 0) + (if x = b then 1 else 0) := by
  rcases Nat.lt_or_ge a b with h | h
  · rw [min_eq_left h.le, max_eq_right h.le]
    exact pkL_path_row ha h hbN (by omega) hx
  · rw [min_eq_right h, max_eq_left h, add_comm]
    exact pkL_path_row hb (by omega) haN (by omega) hx

/-- Case (a) matrix: the alternating cycle `u, u+1, …, v` closed by the pair `(u, v)`. -/
def pkL_sA (u v x y : ℕ) : ℚ := pkL_path u v x y - p3b_e u v x y

/-- Case (b) matrix: `e_{e₁e₂} + e_{o₁o₂}` corrected along two alternating paths. -/
def pkL_sB (e1 e2 o1 o2 x y : ℕ) : ℚ :=
  p3b_e e1 e2 x y + p3b_e o1 o2 x y - pkL_path (min e1 o1) (max e1 o1) x y - pkL_path (min e2 o2) (max e2 o2) x y

theorem pkL_e_far {u v a b : ℕ} (huv : u < v) (hab : a < b) :
    p3b_e u v a b = if (a, b) = (u, v) then 1 else 0 := by
  have e : p3b_e u v a b = (if a = u ∧ b = v then 1 else 0) + (if a = v ∧ b = u then 1 else 0) := rfl
  rw [e, if_neg (show ¬ (a = v ∧ b = u) by omega), add_zero]
  by_cases h : a = u ∧ b = v
  · rw [if_pos h, if_pos (by rw [h.1, h.2])]
  · rw [if_neg h, if_neg (fun e => h (Prod.ext_iff.1 e))]

theorem pkL_sumH_ite {D : Finset (ℕ × ℕ)} (c : ℚ) (p : ℕ × ℕ) :
    ∑ t ∈ D, (if t = p then c else 0) = if p ∈ D then c else 0 := sum_ite_eq' D p (fun _ => c)

/-- Case (a): a missing mixed pair in `H^A ∪ H^B` gives a point of `L_S` with `X_P = 2`. -/
theorem pkL_nd_mixed {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} (hS : S ⊆ diagonals N)
    {i j u v : ℕ} (hP : (i, j) ∈ oddDiagonals N)
    (huvH : (u, v) ∈ oddSideSplit N (i, j) ∪ evenSideSplit N (i, j))
    (huv : (u, v) ∈ diagonals N) (hnS : (u, v) ∉ S) (hmix : u % 2 ≠ v % 2) :
    ∃ X : ℕ × ℕ → ℚ, OnLocus N S X ∧ X (i, j) ≠ 0 := by
  have hd := mem_diagonals.1 huv
  dsimp only at hd
  have hsym : ∀ x y, pkL_sA u v x y = pkL_sA u v y x := fun x y => by
    rw [pkL_sA, pkL_sA, pkL_path_symm, p3b_e_symm]
  have hdiag : ∀ x, pkL_sA u v x x = 0 := fun x => by
    rw [pkL_sA, pkL_path_diag, p3b_e_diag (by omega)]
    ring
  have hrow : ∀ x ∈ Icc 1 N, ∑ y ∈ Icc 1 N, pkL_sA u v x y = 0 := fun x hx => by
    have e : ∀ y ∈ Icc 1 N, pkL_sA u v x y = pkL_path u v x y - p3b_e u v x y := fun y _ => rfl
    rw [sum_congr rfl e, sum_sub_distrib, pkL_path_row hd.1 (by omega) (by omega) (by omega) hx,
      p3b_e_row (mem_Icc.2 ⟨by omega, by omega⟩) (mem_Icc.2 ⟨by omega, by omega⟩), sub_self]
  have hm : ∀ t ∈ diagonals N, mesh N (p3b_Xs (pkL_sA u v)) t.1 t.2 = if t = (u, v) then 2 else 0 := by
    intro t ht
    obtain ⟨a, b⟩ := t
    have h' := mem_diagonals.1 ht
    dsimp only at h' ⊢
    rw [p3b_mesh_Xs (by omega) hsym hdiag hrow (by omega) (by omega) (by omega), pkL_sA,
      pkL_path_far (by omega), pkL_e_far (by omega) (by omega)]
    by_cases h : (a, b) = (u, v)
    · rw [if_pos h, if_pos h]
      norm_num
    · rw [if_neg h, if_neg h]
      norm_num
  have hHsub : oddSideSplit N (i, j) ∪ evenSideSplit N (i, j) ⊆ diagonals N :=
    union_subset (fun t ht => (mem_filter.1 ht).1) (fun t ht => (mem_filter.1 ht).1)
  refine ⟨p3b_Xs (pkL_sA u v), fun t ht => ?_, ?_⟩
  · rw [hm t (hS ht), if_neg (fun e : t = (u, v) => hnS (e ▸ ht))]
  · rw [pkL_hit0 hN hE (p3b_Xs (pkL_sA u v)) hP, sum_congr rfl (fun t ht => hm t (hHsub ht)),
      sum_congr rfl (fun t ht => hm t (filter_subset _ _ ht)), pkL_sumH_ite, pkL_sumH_ite, if_pos huvH,
      if_neg (fun h => by have := (mem_filter.1 h).2; dsimp only at this; omega)]
    norm_num

/-- Case (b): a missing ee pair and a missing oo pair in `H^A ∪ H^B` give a point of `L_S` with `X_P = −2`. -/
theorem pkL_nd_same {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} (hS : S ⊆ diagonals N)
    {i j e1 e2 o1 o2 : ℕ} (hP : (i, j) ∈ oddDiagonals N)
    (heH : (e1, e2) ∈ oddSideSplit N (i, j) ∪ evenSideSplit N (i, j))
    (hoH : (o1, o2) ∈ oddSideSplit N (i, j) ∪ evenSideSplit N (i, j))
    (he : (e1, e2) ∈ diagonals N) (ho : (o1, o2) ∈ diagonals N) (heS : (e1, e2) ∉ S) (hoS : (o1, o2) ∉ S)
    (hee : e1 % 2 = 0 ∧ e2 % 2 = 0) (hoo : o1 % 2 = 1 ∧ o2 % 2 = 1) :
    ∃ X : ℕ × ℕ → ℚ, OnLocus N S X ∧ X (i, j) ≠ 0 := by
  have hd1 := mem_diagonals.1 he
  have hd2 := mem_diagonals.1 ho
  dsimp only at hd1 hd2
  have hsym : ∀ x y, pkL_sB e1 e2 o1 o2 x y = pkL_sB e1 e2 o1 o2 y x := fun x y => by
    rw [pkL_sB, pkL_sB, pkL_path_symm (min e1 o1), pkL_path_symm (min e2 o2), p3b_e_symm e1, p3b_e_symm o1]
  have hdiag : ∀ x, pkL_sB e1 e2 o1 o2 x x = 0 := fun x => by
    rw [pkL_sB, pkL_path_diag, pkL_path_diag, p3b_e_diag (by omega), p3b_e_diag (by omega)]
    ring
  have hrow : ∀ x ∈ Icc 1 N, ∑ y ∈ Icc 1 N, pkL_sB e1 e2 o1 o2 x y = 0 := fun x hx => by
    have e : ∀ y ∈ Icc 1 N, pkL_sB e1 e2 o1 o2 x y = p3b_e e1 e2 x y + p3b_e o1 o2 x y -
        pkL_path (min e1 o1) (max e1 o1) x y - pkL_path (min e2 o2) (max e2 o2) x y := fun y _ => rfl
    rw [sum_congr rfl e, sum_sub_distrib, sum_sub_distrib, sum_add_distrib,
      p3b_e_row (mem_Icc.2 ⟨by omega, by omega⟩) (mem_Icc.2 ⟨by omega, by omega⟩),
      p3b_e_row (mem_Icc.2 ⟨by omega, by omega⟩) (mem_Icc.2 ⟨by omega, by omega⟩),
      pkL_path_row' (by omega) (by omega) (by omega) (by omega) (by omega) hx,
      pkL_path_row' (by omega) (by omega) (by omega) (by omega) (by omega) hx]
    ring
  have hm : ∀ t ∈ diagonals N, mesh N (p3b_Xs (pkL_sB e1 e2 o1 o2)) t.1 t.2 =
      (if t = (e1, e2) then -2 else 0) + (if t = (o1, o2) then -2 else 0) := by
    intro t ht
    obtain ⟨a, b⟩ := t
    have h' := mem_diagonals.1 ht
    dsimp only at h' ⊢
    rw [p3b_mesh_Xs (by omega) hsym hdiag hrow (by omega) (by omega) (by omega), pkL_sB,
      pkL_path_far (by omega), pkL_path_far (by omega), pkL_e_far (by omega) (by omega),
      pkL_e_far (by omega) (by omega)]
    split_ifs <;> norm_num
  have hHsub : oddSideSplit N (i, j) ∪ evenSideSplit N (i, j) ⊆ diagonals N :=
    union_subset (fun t ht => (mem_filter.1 ht).1) (fun t ht => (mem_filter.1 ht).1)
  refine ⟨p3b_Xs (pkL_sB e1 e2 o1 o2), fun t ht => ?_, ?_⟩
  · rw [hm t (hS ht), if_neg (fun e : t = (e1, e2) => heS (e ▸ ht)), if_neg (fun e : t = (o1, o2) => hoS (e ▸ ht))]
    norm_num
  · rw [pkL_hit0 hN hE (p3b_Xs (pkL_sB e1 e2 o1 o2)) hP, sum_congr rfl (fun t ht => hm t (hHsub ht)),
      sum_congr rfl (fun t ht => hm t (filter_subset _ _ ht)), sum_add_distrib, sum_add_distrib,
      pkL_sumH_ite, pkL_sumH_ite, pkL_sumH_ite, pkL_sumH_ite, if_pos heH, if_pos hoH,
      if_pos (mem_filter.2 ⟨he, hee⟩), if_neg (fun h => by have := (mem_filter.1 h).2; dsimp only at this; omega)]
    norm_num

theorem pkL_HA_mem {N i j : ℕ} (hP : (i, j) ∈ oddDiagonals N) : oddSideSplit N (i, j) ∈ gFamily N := by
  obtain ⟨hi1, hjN, hij, hne, hodd⟩ := pkL_oddD hP
  have hsub : odds (oddSide N (i, j)) ⊆ Icc 1 N := fun t ht => by
    have := (pkL_mem_oddsA hi1 hjN).1 ht
    exact mem_Icc.2 ⟨this.1, this.2.1⟩
  have hcard : 2 ≤ (odds (oddSide N (i, j))).card := by
    rcases Nat.mod_two_eq_zero_or_one i with hp | hp
    · have h1 : j ∈ odds (oddSide N (i, j)) := (pkL_mem_oddsA hi1 hjN).2 (by omega)
      have h2 : i - 1 ∈ odds (oddSide N (i, j)) := (pkL_mem_oddsA hi1 hjN).2 (by omega)
      exact one_lt_card.2 ⟨j, h1, i - 1, h2, by omega⟩
    · have h1 : i ∈ odds (oddSide N (i, j)) := (pkL_mem_oddsA hi1 hjN).2 (by omega)
      have h2 : j - 1 ∈ odds (oddSide N (i, j)) := (pkL_mem_oddsA hi1 hjN).2 (by omega)
      exact one_lt_card.2 ⟨i, h1, j - 1, h2, by omega⟩
  exact mem_image.2 ⟨odds (oddSide N (i, j)), mem_filter.2 ⟨mem_powerset.2 hsub,
    Or.inl (Or.inr ⟨hsub, hcard, fun t ht => ((pkL_mem_oddsA hi1 hjN).1 ht).2.2.1⟩)⟩, rfl⟩

theorem pkL_HB_mem {N i j : ℕ} (hE : N % 2 = 0) (hP : (i, j) ∈ oddDiagonals N) :
    evenSideSplit N (i, j) ∈ gFamily N := by
  obtain ⟨hi1, hjN, hij, hne, hodd⟩ := pkL_oddD hP
  have hsub : evens (evenSide N (i, j)) ⊆ Icc 1 N := fun t ht => by
    have := (pkL_mem_evensB hi1 hjN).1 ht
    exact mem_Icc.2 ⟨this.1, this.2.1⟩
  have hcard : 2 ≤ (evens (evenSide N (i, j))).card := by
    rcases Nat.mod_two_eq_zero_or_one i with hp | hp
    · have h1 : i ∈ evens (evenSide N (i, j)) := (pkL_mem_evensB hi1 hjN).2 (by omega)
      have h2 : j - 1 ∈ evens (evenSide N (i, j)) := (pkL_mem_evensB hi1 hjN).2 (by omega)
      exact one_lt_card.2 ⟨i, h1, j - 1, h2, by omega⟩
    · have h1 : j ∈ evens (evenSide N (i, j)) := (pkL_mem_evensB hi1 hjN).2 (by omega)
      by_cases hi3 : 3 ≤ i
      · have h2 : i - 1 ∈ evens (evenSide N (i, j)) := (pkL_mem_evensB hi1 hjN).2 (by omega)
        exact one_lt_card.2 ⟨j, h1, i - 1, h2, by omega⟩
      · have h2 : N ∈ evens (evenSide N (i, j)) := (pkL_mem_evensB hi1 hjN).2 (by omega)
        exact one_lt_card.2 ⟨j, h1, N, h2, by omega⟩
  exact mem_image.2 ⟨evens (evenSide N (i, j)), mem_filter.2 ⟨mem_powerset.2 hsub,
    Or.inl (Or.inl ⟨hsub, hcard, fun t ht => ((pkL_mem_evensB hi1 hjN).1 ht).2.2.1⟩)⟩, rfl⟩

set_option maxHeartbeats 1000000 in
theorem pkL_HA_noOO {N i j a b : ℕ} (hP : (i, j) ∈ oddDiagonals N) (h : (a, b) ∈ oddSideSplit N (i, j))
    (hab : a < b) : ¬ (a % 2 = 1 ∧ b % 2 = 1) := by
  obtain ⟨hi1, hjN, hij, hne, hodd⟩ := pkL_oddD hP
  have hd := mem_diagonals.1 (pkL_mem_sep.1 h).1
  dsimp only at hd
  obtain ⟨hA, hB, ⟨t1, ht1, h11, h12⟩, ⟨t2, ht2, h2⟩⟩ := (pkL_inST_iff hab).1 (pkL_mem_sep.1 h).2
  rw [pkL_mem_oddsA hi1 hjN] at hA hB ht1 ht2
  rcases Nat.mod_two_eq_zero_or_one i with hp | hp <;>
    simp only [hp, Nat.zero_ne_one, Nat.one_ne_zero, false_and, true_and, or_false, false_or] at hA hB ht1 ht2 <;>
    rcases h2 with h2 | h2 <;> omega

set_option maxHeartbeats 1000000 in
theorem pkL_HB_noEE {N i j a b : ℕ} (hP : (i, j) ∈ oddDiagonals N) (h : (a, b) ∈ evenSideSplit N (i, j))
    (hab : a < b) : ¬ (a % 2 = 0 ∧ b % 2 = 0) := by
  obtain ⟨hi1, hjN, hij, hne, hodd⟩ := pkL_oddD hP
  have hd := mem_diagonals.1 (pkL_mem_sep.1 h).1
  dsimp only at hd
  obtain ⟨hA, hB, ⟨t1, ht1, h11, h12⟩, ⟨t2, ht2, h2⟩⟩ := (pkL_inST_iff hab).1 (pkL_mem_sep.1 h).2
  rw [pkL_mem_evensB hi1 hjN] at hA hB ht1 ht2
  rcases Nat.mod_two_eq_zero_or_one i with hp | hp <;>
    simp only [hp, Nat.zero_ne_one, Nat.one_ne_zero, false_and, true_and, or_false, false_or] at hA hB ht1 ht2 <;>
    rcases h2 with h2 | h2 <;> omega

/-- **Transversal ⇒ non-degenerate** (BP G-14, route "[Hit] at S = ∅"). -/
theorem pkL_nondeg {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} (hS : S ⊆ diagonals N)
    (hT : Transversal N (missing N S)) {d : ℕ × ℕ} (hd : d ∈ diagonals N) :
    ∃ X : ℕ × ℕ → ℚ, OnLocus N S X ∧ X d ≠ 0 := by
  obtain ⟨i, j⟩ := d
  have hd' := mem_diagonals.1 hd
  dsimp only at hd'
  by_cases hpar : (j - i) % 2 = 1
  · have hP : (i, j) ∈ oddDiagonals N := mem_filter.2 ⟨hd, hpar⟩
    obtain ⟨tA, htA⟩ := hT _ (pkL_HA_mem hP)
    obtain ⟨tB, htB⟩ := hT _ (pkL_HB_mem hE hP)
    obtain ⟨hA1, hA2⟩ := mem_inter.1 htA
    obtain ⟨hB1, hB2⟩ := mem_inter.1 htB
    obtain ⟨hAd, hAS⟩ := mem_sdiff.1 hA2
    obtain ⟨hBd, hBS⟩ := mem_sdiff.1 hB2
    obtain ⟨a1, a2⟩ := tA
    obtain ⟨b1, b2⟩ := tB
    have hAd' := mem_diagonals.1 hAd
    have hBd' := mem_diagonals.1 hBd
    dsimp only at hAd' hBd'
    by_cases hmA : a1 % 2 ≠ a2 % 2
    · exact pkL_nd_mixed hN hE hS hP (mem_union_left _ hA1) hAd hAS hmA
    · by_cases hmB : b1 % 2 ≠ b2 % 2
      · exact pkL_nd_mixed hN hE hS hP (mem_union_right _ hB1) hBd hBS hmB
      · have h1 := pkL_HA_noOO hP hA1 (by omega)
        have h2 := pkL_HB_noEE hP hB1 (by omega)
        exact pkL_nd_same hN hE hS hP (mem_union_left _ hA1) (mem_union_right _ hB1) hAd hBd hAS hBS
          (by omega) (by omega)
  · refine ⟨fun d => ((shiftSign d : ℤ) : ℚ), fun t ht => ?_, ?_⟩
    · obtain ⟨u, v⟩ := t
      exact pkL_mesh_sign hE (hS ht)
    · show (((if i % 2 = 0 ∧ j % 2 = 0 then 1 else if i % 2 = 1 ∧ j % 2 = 1 then -1 else 0 : ℤ)) : ℚ) ≠ 0
      rcases Nat.mod_two_eq_zero_or_one i with hi | hi
      · rw [if_pos ⟨hi, by omega⟩]
        norm_num
      · rw [if_neg (by omega), if_pos ⟨hi, by omega⟩]
        norm_num

/-- `sorry` (pkgLin) · **[Fπ]** [v3 §14.2, R2-Z178 C1; BP App. A §7]: `S ∈ F^π` iff `M` is a transversal of `𝒢_N`;
non-degeneracy is then automatic. Stated for `4 ≤ N` (P7a R1 S2: [Child] applies it to children of size 4). (Mirror: no degenerate pattern-free set at N = 6 (all 512 sets) or N = 8 (|S| ≤ 6), thread §6.) -/
theorem fpi_iff {N : ℕ} (hN : 4 ≤ N) (hE : Even N) {S : Finset (ℕ × ℕ)} (hS : S ⊆ diagonals N) :
    InFpi N S ↔ Transversal N (missing N S) := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  constructor
  · rintro ⟨-, -, hG⟩ Z hZ
    by_contra hne
    apply hG
    refine ⟨Z, hZ, fun t ht => ?_⟩
    by_contra htS
    exact hne ⟨t, mem_inter.2 ⟨ht, mem_sdiff.2 ⟨gFamily_sub hZ ht, htS⟩⟩⟩
  · intro hT
    refine ⟨hS, fun d hd => pkL_nondeg hN hE' hS hT hd, ?_⟩
    rintro ⟨Z, hZ, hZS⟩
    obtain ⟨t, ht⟩ := hT Z hZ
    have h2 := mem_inter.1 ht
    exact (mem_sdiff.1 h2.2).2 (hZS h2.1)

/-- `sorry` (pkgLin) · **Lemma 6.5 relation** [v3 §14.2 "exactly one relation"; DRAFT §6 Lemma 6.5], the identity on all of
`𝒳` from which the relation on `L_S` follows: `Σ_{ee pairs} c = Σ_{oo pairs} c`. (Mirror: exact random points, N = 6, 8,
10.) "No other relation" is TODO (used in Lemma U step (0)). -/
theorem lemma65 {K : Type*} [Field K] {N : ℕ} (hN : 4 ≤ N) (hE : Even N) (X : ℕ × ℕ → K) :
    ∑ t ∈ (diagonals N).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0), mesh N X t.1 t.2 =
      ∑ t ∈ (diagonals N).filter (fun p => p.1 % 2 = 1 ∧ p.2 % 2 = 1), mesh N X t.1 t.2 := by
  exact pkL_l65 hN (Nat.even_iff.1 hE) X

/-- `sorry` (pkgLin) · **Hit-set formula** (BP [Hit]; stated for `4 ≤ N`, P7a R1 S2) [v3 §14.2, input (1); R2-Z182 C1(d)]: on `L_S`, for every mixed chord `P`,
`X_P = y(h_P) − E`, with `y_t = c_t|_{L_S}` and `E = y(M_e)`. (Mirror: holds at S = ∅ as an identity on `𝒳`, N = 6, 8,
10, and on 20 random loci at N = 8, thread §6.) -/
theorem chord_restrict {K : Type*} [Field K] {N : ℕ} (hN : 4 ≤ N) (hE : Even N) {S : Finset (ℕ × ℕ)}
    (hS : S ⊆ diagonals N) (X : ℕ × ℕ → K) (hL : OnLocus N S X) {P : ℕ × ℕ} (hP : P ∈ oddDiagonals N) :
    X P = ∑ t ∈ hitSet N S P, mesh N X t.1 t.2 - ∑ t ∈ Mee N S, mesh N X t.1 t.2 := by
  obtain ⟨i, j⟩ := P
  rw [pkL_hit0 hN (Nat.even_iff.1 hE) X hP]
  have hHsub : oddSideSplit N (i, j) ∪ evenSideSplit N (i, j) ⊆ diagonals N :=
    union_subset (fun t ht => (mem_filter.1 ht).1) (fun t ht => (mem_filter.1 ht).1)
  have e1 : ∑ t ∈ hitSet N S (i, j), mesh N X t.1 t.2 =
      ∑ t ∈ oddSideSplit N (i, j) ∪ evenSideSplit N (i, j), mesh N X t.1 t.2 := by
    apply sum_subset
    · intro t ht
      exact (mem_inter.1 ht).2
    · intro t ht hn
      have ht' : t ∈ S := by
        by_contra hS'
        exact hn (mem_inter.2 ⟨mem_sdiff.2 ⟨hHsub ht, hS'⟩, ht⟩)
      exact hL t ht'
  have e2 : ∑ t ∈ Mee N S, mesh N X t.1 t.2 =
      ∑ t ∈ (diagonals N).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0), mesh N X t.1 t.2 := by
    apply sum_subset
    · intro t ht
      exact mem_filter.2 ⟨(mem_sdiff.1 (mem_filter.1 ht).1).1, (mem_filter.1 ht).2⟩
    · intro t ht hn
      have ht' : t ∈ S := by
        by_contra hS'
        exact hn (mem_filter.2 ⟨mem_sdiff.2 ⟨(mem_filter.1 ht).1, hS'⟩, (mem_filter.1 ht).2⟩)
      exact hL t ht'
  rw [e1, e2]

/-! ### pkgLin-2 helpers (`pkL_`): Lemma 14.6 — the cut dictionary in arithmetic form and step (3) [NoSign] -/

/-- Leg `x` lies in the head (odd-ended side) of the mixed chord `(i, j)`. -/
def pkL_inA (i j x : ℕ) : Prop := (i % 2 = 1 ∧ i ≤ x ∧ x ≤ j - 1) ∨ (i % 2 = 0 ∧ ¬ (i ≤ x ∧ x ≤ j - 1))

theorem pkL_inA_iff {i j x : ℕ} :
    pkL_inA i j x ↔ ((i % 2 = 1 ∧ i ≤ x ∧ x ≤ j - 1) ∨ (i % 2 = 0 ∧ ¬ (i ≤ x ∧ x ≤ j - 1))) := Iff.rfl

/-- Cut dictionary: the pair `(a, b)` lies in `H^A ∪ H^B` of `(i, j)`. -/
def pkL_Psi (i j a b : ℕ) : Prop :=
  (a % 2 = 0 ∧ b % 2 = 1 ∧ pkL_inA i j a ∧ ¬ pkL_inA i j b) ∨
    (a % 2 = 1 ∧ b % 2 = 0 ∧ pkL_inA i j b ∧ ¬ pkL_inA i j a) ∨
    (a % 2 = 0 ∧ b % 2 = 0 ∧ (pkL_inA i j a ∨ pkL_inA i j b)) ∨
    (a % 2 = 1 ∧ b % 2 = 1 ∧ (¬ pkL_inA i j a ∨ ¬ pkL_inA i j b))

theorem pkL_Psi_iff {i j a b : ℕ} : pkL_Psi i j a b ↔
    ((a % 2 = 0 ∧ b % 2 = 1 ∧ pkL_inA i j a ∧ ¬ pkL_inA i j b) ∨
      (a % 2 = 1 ∧ b % 2 = 0 ∧ pkL_inA i j b ∧ ¬ pkL_inA i j a) ∨
      (a % 2 = 0 ∧ b % 2 = 0 ∧ (pkL_inA i j a ∨ pkL_inA i j b)) ∨
      (a % 2 = 1 ∧ b % 2 = 1 ∧ (¬ pkL_inA i j a ∨ ¬ pkL_inA i j b))) := Iff.rfl

set_option maxHeartbeats 4000000 in
theorem pkL_H_to {N i j a b : ℕ} (hP : (i, j) ∈ oddDiagonals N) (hab : a < b)
    (h : (a, b) ∈ oddSideSplit N (i, j) ∪ evenSideSplit N (i, j)) : pkL_Psi i j a b := by
  obtain ⟨hi1, hjN, hij, hne, hodd⟩ := pkL_oddD hP
  have hΦ := pkL_memH_to hP hab h
  simp only [pkL_Psi_iff, pkL_inA_iff]
  rcases Nat.mod_two_eq_zero_or_one i with hp | hp <;> rcases Nat.mod_two_eq_zero_or_one a with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one b with h2 | h2 <;> omega

set_option maxHeartbeats 4000000 in
theorem pkL_H_of {N i j a b : ℕ} (hE : N % 2 = 0) (hP : (i, j) ∈ oddDiagonals N) (ha : 1 ≤ a) (hab : a + 2 ≤ b)
    (hb : b ≤ N) (hne : ¬ (a = 1 ∧ b = N)) (h : pkL_Psi i j a b) :
    (a, b) ∈ oddSideSplit N (i, j) ∪ evenSideSplit N (i, j) := by
  obtain ⟨hi1, hjN, hij, hne', hodd⟩ := pkL_oddD hP
  apply pkL_memH_of hE hP ha (by omega) hb
  simp only [pkL_Psi_iff, pkL_inA_iff] at h
  rcases Nat.mod_two_eq_zero_or_one i with hp | hp <;> rcases Nat.mod_two_eq_zero_or_one a with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one b with h2 | h2 <;> omega

/-- What a missing pair satisfies in the case `λ = −1` of Lemma 14.6 (`h_Q = M_same ∖ h_P`, no mixed pair hit). -/
def pkL_Cond (i j k l a b : ℕ) : Prop :=
  (a % 2 ≠ b % 2 → ¬ pkL_Psi i j a b ∧ ¬ pkL_Psi k l a b) ∧
    (a % 2 = b % 2 → (pkL_Psi i j a b ∨ pkL_Psi k l a b) ∧ ¬ (pkL_Psi i j a b ∧ pkL_Psi k l a b))

theorem pkL_Cond_iff {i j k l a b : ℕ} : pkL_Cond i j k l a b ↔
    ((a % 2 ≠ b % 2 → ¬ pkL_Psi i j a b ∧ ¬ pkL_Psi k l a b) ∧
      (a % 2 = b % 2 → (pkL_Psi i j a b ∨ pkL_Psi k l a b) ∧ ¬ (pkL_Psi i j a b ∧ pkL_Psi k l a b))) := Iff.rfl

theorem pkL_Psi_ee {i j a b : ℕ} (ha : a % 2 = 0) (hb : b % 2 = 0) :
    pkL_Psi i j a b ↔ (pkL_inA i j a ∨ pkL_inA i j b) := by
  rw [pkL_Psi_iff]
  constructor
  · rintro (h | h | h | h)
    · exact absurd h.2.1 (by omega)
    · exact absurd h.1 (by omega)
    · exact h.2.2
    · exact absurd h.1 (by omega)
  · intro h
    exact Or.inr (Or.inr (Or.inl ⟨ha, hb, h⟩))

theorem pkL_Psi_oo {i j a b : ℕ} (ha : a % 2 = 1) (hb : b % 2 = 1) :
    pkL_Psi i j a b ↔ (¬ pkL_inA i j a ∨ ¬ pkL_inA i j b) := by
  rw [pkL_Psi_iff]
  constructor
  · rintro (h | h | h | h)
    · exact absurd h.1 (by omega)
    · exact absurd h.2.1 (by omega)
    · exact absurd h.1 (by omega)
    · exact h.2.2
  · intro h
    exact Or.inr (Or.inr (Or.inr ⟨ha, hb, h⟩))

theorem pkL_Psi_eo {i j a b : ℕ} (ha : a % 2 = 0) (hb : b % 2 = 1) :
    pkL_Psi i j a b ↔ (pkL_inA i j a ∧ ¬ pkL_inA i j b) := by
  rw [pkL_Psi_iff]
  constructor
  · rintro (h | h | h | h)
    · exact h.2.2
    · exact absurd h.1 (by omega)
    · exact absurd h.2.1 (by omega)
    · exact absurd h.1 (by omega)
  · intro h
    exact Or.inl ⟨ha, hb, h⟩

theorem pkL_Psi_oe {i j a b : ℕ} (ha : a % 2 = 1) (hb : b % 2 = 0) :
    pkL_Psi i j a b ↔ (pkL_inA i j b ∧ ¬ pkL_inA i j a) := by
  rw [pkL_Psi_iff]
  constructor
  · rintro (h | h | h | h)
    · exact absurd h.1 (by omega)
    · exact h.2.2
    · exact absurd h.1 (by omega)
    · exact absurd h.2.1 (by omega)
  · intro h
    exact Or.inr (Or.inl ⟨ha, hb, h⟩)

/-- A head is an arc: two of its legs are not separated by legs outside it. -/
theorem pkL_arcA {i j a b t1 t2 : ℕ} (ha : pkL_inA i j a) (hb : pkL_inA i j b) (h1 : ¬ pkL_inA i j t1)
    (h2 : ¬ pkL_inA i j t2) (hs1 : a < t1 ∧ t1 < b) (hs2 : t2 < a ∨ b < t2) : False := by
  rw [pkL_inA_iff] at ha hb h1 h2
  omega

/-- A tail is an arc. -/
theorem pkL_arcB {i j a b t1 t2 : ℕ} (ha : ¬ pkL_inA i j a) (hb : ¬ pkL_inA i j b) (h1 : pkL_inA i j t1)
    (h2 : pkL_inA i j t2) (hs1 : a < t1 ∧ t1 < b) (hs2 : t2 < a ∨ b < t2) : False := by
  rw [pkL_inA_iff] at ha hb h1 h2
  omega

theorem pkL_par (x : ℕ) : x % 2 = 0 ∨ x % 2 = 1 := Nat.mod_two_eq_zero_or_one x

/-- Step (3), generic cut `T = evens(B_P ∩ B_Q)`: no pair allowed by `pkL_Cond` is separated by it. -/
theorem pkL_T1 {i j k l a b t1 t2 : ℕ} (hC : pkL_Cond i j k l a b)
    (hTa : ¬ (a % 2 = 0 ∧ ¬ pkL_inA i j a ∧ ¬ pkL_inA k l a))
    (hTb : ¬ (b % 2 = 0 ∧ ¬ pkL_inA i j b ∧ ¬ pkL_inA k l b))
    (ht1 : ¬ pkL_inA i j t1 ∧ ¬ pkL_inA k l t1) (ht2 : ¬ pkL_inA i j t2 ∧ ¬ pkL_inA k l t2)
    (h1 : a < t1 ∧ t1 < b) (h2 : t2 < a ∨ b < t2) : False := by
  rw [pkL_Cond_iff] at hC
  by_cases hAa : pkL_inA i j a <;> by_cases hAb : pkL_inA i j b <;> by_cases hBa : pkL_inA k l a <;>
    by_cases hBb : pkL_inA k l b <;> (try exact pkL_arcA hAa hAb ht1.1 ht2.1 h1 h2) <;>
    (try exact pkL_arcA hBa hBb ht1.2 ht2.2 h1 h2) <;>
    rcases pkL_par a with h3 | h3 <;> rcases pkL_par b with h4 | h4 <;>
    simp [pkL_Psi_ee, pkL_Psi_oo, pkL_Psi_eo, pkL_Psi_oe, h3, h4, hAa, hAb, hBa, hBb] at hC hTa hTb

/-- Step (3), generic cut `T = odds(A_P ∩ A_Q)`. -/
theorem pkL_T2 {i j k l a b t1 t2 : ℕ} (hC : pkL_Cond i j k l a b)
    (hTa : ¬ (a % 2 = 1 ∧ pkL_inA i j a ∧ pkL_inA k l a))
    (hTb : ¬ (b % 2 = 1 ∧ pkL_inA i j b ∧ pkL_inA k l b))
    (ht1 : pkL_inA i j t1 ∧ pkL_inA k l t1) (ht2 : pkL_inA i j t2 ∧ pkL_inA k l t2)
    (h1 : a < t1 ∧ t1 < b) (h2 : t2 < a ∨ b < t2) : False := by
  rw [pkL_Cond_iff] at hC
  by_cases hAa : pkL_inA i j a <;> by_cases hAb : pkL_inA i j b <;> by_cases hBa : pkL_inA k l a <;>
    by_cases hBb : pkL_inA k l b <;> (try exact pkL_arcB hAa hAb ht1.1 ht2.1 h1 h2) <;>
    (try exact pkL_arcB hBa hBb ht1.2 ht2.2 h1 h2) <;>
    rcases pkL_par a with h3 | h3 <;> rcases pkL_par b with h4 | h4 <;>
    simp [pkL_Psi_ee, pkL_Psi_oo, pkL_Psi_eo, pkL_Psi_oe, h3, h4, hAa, hAb, hBa, hBb] at hC hTa hTb

set_option maxHeartbeats 4000000 in
/-- Step (3), the three configurations where `A_P ∩ A_Q = {x}` and `B_P ∩ B_Q = {y}`: the diamond `{x, y}`. -/
theorem pkL_T3 {N i j k l a b t1 t2 x y : ℕ}
    (hcfg : (i % 2 = 1 ∧ k % 2 = 1 ∧ i = 1 ∧ j = k + 1 ∧ l = N ∧ x = k ∧ y = N) ∨
      (i % 2 = 1 ∧ k % 2 = 0 ∧ k = i + 1 ∧ l = j + 1 ∧ x = i ∧ y = j) ∨
      (i % 2 = 0 ∧ k % 2 = 1 ∧ k = i + 1 ∧ l = j + 1 ∧ x = i ∧ y = j))
    (hc1 : 1 ≤ i ∧ i + 2 ≤ j ∧ j ≤ N) (hc2 : 1 ≤ k ∧ k + 2 ≤ l ∧ l ≤ N)
    (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ N) (hC : pkL_Cond i j k l a b)
    (hTa : a ≠ x ∧ a ≠ y) (hTb : b ≠ x ∧ b ≠ y) (ht1 : t1 = x ∨ t1 = y) (ht2 : t2 = x ∨ t2 = y)
    (h1 : a < t1 ∧ t1 < b) (h2 : t2 < a ∨ b < t2) : False := by
  rw [pkL_Cond_iff] at hC
  by_cases hAa : pkL_inA i j a <;> by_cases hAb : pkL_inA i j b <;> by_cases hBa : pkL_inA k l a <;>
    by_cases hBb : pkL_inA k l b <;>
    rcases pkL_par a with h3 | h3 <;> rcases pkL_par b with h4 | h4 <;>
    simp [pkL_Psi_ee, pkL_Psi_oo, pkL_Psi_eo, pkL_Psi_oe, h3, h4, hAa, hAb, hBa, hBb] at hC <;>
    simp only [pkL_inA_iff] at hAa hAb hBa hBb <;>
    rcases hcfg with ⟨c1, c2, c3, c4, c5, c6, c7⟩ | ⟨c1, c2, c3, c4, c5, c6⟩ | ⟨c1, c2, c3, c4, c5, c6⟩ <;> omega

set_option maxHeartbeats 4000000 in
/-- **[NoSign]** (BP §3.1 step (3)), arithmetic core for `i ≤ k`: a transversal `M` cannot satisfy `pkL_Cond` for two
mixed chords with tails not nested (witnessed by `e_in(P)`, `e_in(Q)`). -/
theorem pkL_noSign_core {N i j k l : ℕ} (hE : N % 2 = 0) (hP : (i, j) ∈ oddDiagonals N)
    (hQ : (k, l) ∈ oddDiagonals N) (hik : i ≤ k) {M : Finset (ℕ × ℕ)} (hMd : M ⊆ diagonals N)
    (hT : Transversal N M) (hC : ∀ a b, (a, b) ∈ M → pkL_Cond i j k l a b)
    (hw0 : ∃ a b, (a, b) ∈ M ∧ a % 2 = 0 ∧ b % 2 = 0 ∧ ¬ pkL_Psi i j a b)
    (hw1 : ∃ a b, (a, b) ∈ M ∧ a % 2 = 0 ∧ b % 2 = 0 ∧ ¬ pkL_Psi k l a b) : False := by
  obtain ⟨hi1, hjN, hij, hne1, hod1⟩ := pkL_oddD hP
  obtain ⟨hk1, hlN, hkl, hne2, hod2⟩ := pkL_oddD hQ
  obtain ⟨e1, e2, he, he1, he2, hnP⟩ := hw0
  obtain ⟨f1, f2, hf, hf1, hf2, hnQ⟩ := hw1
  have ce := hC e1 e2 he
  have cf := hC f1 f2 hf
  rw [pkL_Cond_iff, pkL_Psi_ee he1 he2, pkL_Psi_ee he1 he2] at ce
  rw [pkL_Cond_iff, pkL_Psi_ee hf1 hf2, pkL_Psi_ee hf1 hf2] at cf
  rw [pkL_Psi_ee he1 he2] at hnP
  rw [pkL_Psi_ee hf1 hf2] at hnQ
  have W0 : ¬ pkL_inA i j e1 ∧ ¬ pkL_inA i j e2 ∧ (pkL_inA k l e1 ∨ pkL_inA k l e2) :=
    ⟨fun h => hnP (Or.inl h), fun h => hnP (Or.inr h), ((ce.2 (by omega)).1).resolve_left hnP⟩
  have W1 : ¬ pkL_inA k l f1 ∧ ¬ pkL_inA k l f2 ∧ (pkL_inA i j f1 ∨ pkL_inA i j f2) :=
    ⟨fun h => hnQ (Or.inl h), fun h => hnQ (Or.inr h), ((cf.2 (by omega)).1).resolve_right hnQ⟩
  have hde := mem_diagonals.1 (hMd he)
  have hdf := mem_diagonals.1 (hMd hf)
  dsimp only at hde hdf
  have key : ∀ G : Finset ℕ, G ∈ gLegSets N → (∀ a b, (a, b) ∈ M → ¬ InST G a b) → False := by
    intro G hG hcl
    obtain ⟨t, ht⟩ := hT (sepPairs N G) (mem_image.2 ⟨G, hG, rfl⟩)
    obtain ⟨ht1, ht2⟩ := mem_inter.1 ht
    exact hcl t.1 t.2 ht2 (mem_filter.1 ht1).2
  have hT1 : ∀ u v, u ≠ v →
      u ∈ (Icc 1 N).filter (fun x => x % 2 = 0 ∧ ¬ ((i % 2 = 1 ∧ i ≤ x ∧ x ≤ j - 1) ∨ (i % 2 = 0 ∧ ¬ (i ≤ x ∧ x ≤ j - 1))) ∧
        ¬ ((k % 2 = 1 ∧ k ≤ x ∧ x ≤ l - 1) ∨ (k % 2 = 0 ∧ ¬ (k ≤ x ∧ x ≤ l - 1)))) →
      v ∈ (Icc 1 N).filter (fun x => x % 2 = 0 ∧ ¬ ((i % 2 = 1 ∧ i ≤ x ∧ x ≤ j - 1) ∨ (i % 2 = 0 ∧ ¬ (i ≤ x ∧ x ≤ j - 1))) ∧
        ¬ ((k % 2 = 1 ∧ k ≤ x ∧ x ≤ l - 1) ∨ (k % 2 = 0 ∧ ¬ (k ≤ x ∧ x ≤ l - 1)))) → False := by
    intro u v huv hu hv
    refine key _ (mem_filter.2 ⟨mem_powerset.2 (filter_subset _ _), Or.inl (Or.inl ⟨filter_subset _ _,
      one_lt_card.2 ⟨u, hu, v, hv, huv⟩, fun t ht => (mem_filter.1 ht).2.1⟩)⟩) ?_
    intro a b hab hsep
    have hd := mem_diagonals.1 (hMd hab)
    dsimp only at hd
    obtain ⟨hA, hB, ⟨t1, ht1, h11, h12⟩, ⟨t2, ht2, h2⟩⟩ := (pkL_inST_iff (by omega : a < b)).1 hsep
    exact pkL_T1 (hC a b hab) (fun h => hA (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, h⟩))
      (fun h => hB (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, h⟩)) (mem_filter.1 ht1).2.2
      (mem_filter.1 ht2).2.2 ⟨h11, h12⟩ h2
  have hT2 : ∀ u v, u ≠ v →
      u ∈ (Icc 1 N).filter (fun x => x % 2 = 1 ∧ ((i % 2 = 1 ∧ i ≤ x ∧ x ≤ j - 1) ∨ (i % 2 = 0 ∧ ¬ (i ≤ x ∧ x ≤ j - 1))) ∧
        ((k % 2 = 1 ∧ k ≤ x ∧ x ≤ l - 1) ∨ (k % 2 = 0 ∧ ¬ (k ≤ x ∧ x ≤ l - 1)))) →
      v ∈ (Icc 1 N).filter (fun x => x % 2 = 1 ∧ ((i % 2 = 1 ∧ i ≤ x ∧ x ≤ j - 1) ∨ (i % 2 = 0 ∧ ¬ (i ≤ x ∧ x ≤ j - 1))) ∧
        ((k % 2 = 1 ∧ k ≤ x ∧ x ≤ l - 1) ∨ (k % 2 = 0 ∧ ¬ (k ≤ x ∧ x ≤ l - 1)))) → False := by
    intro u v huv hu hv
    refine key _ (mem_filter.2 ⟨mem_powerset.2 (filter_subset _ _), Or.inl (Or.inr ⟨filter_subset _ _,
      one_lt_card.2 ⟨u, hu, v, hv, huv⟩, fun t ht => (mem_filter.1 ht).2.1⟩)⟩) ?_
    intro a b hab hsep
    have hd := mem_diagonals.1 (hMd hab)
    dsimp only at hd
    obtain ⟨hA, hB, ⟨t1, ht1, h11, h12⟩, ⟨t2, ht2, h2⟩⟩ := (pkL_inST_iff (by omega : a < b)).1 hsep
    exact pkL_T2 (hC a b hab) (fun h => hA (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, h⟩))
      (fun h => hB (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, h⟩)) (mem_filter.1 ht1).2.2
      (mem_filter.1 ht2).2.2 ⟨h11, h12⟩ h2
  have hT3 : ∀ x y, ((i % 2 = 1 ∧ k % 2 = 1 ∧ i = 1 ∧ j = k + 1 ∧ l = N ∧ x = k ∧ y = N) ∨
      (i % 2 = 1 ∧ k % 2 = 0 ∧ k = i + 1 ∧ l = j + 1 ∧ x = i ∧ y = j) ∨
      (i % 2 = 0 ∧ k % 2 = 1 ∧ k = i + 1 ∧ l = j + 1 ∧ x = i ∧ y = j)) → False := by
    intro x y hcfg
    have hxy : 1 ≤ x ∧ x + 2 ≤ y ∧ y ≤ N ∧ ¬ (x = 1 ∧ y = N) ∧ x % 2 ≠ y % 2 := by omega
    have hsub : ({x, y} : Finset ℕ) ⊆ Icc 1 N := by
      intro t ht
      rcases mem_insert.1 ht with h | h
      · exact mem_Icc.2 ⟨by omega, by omega⟩
      · rw [mem_singleton.1 h]
        exact mem_Icc.2 ⟨by omega, by omega⟩
    refine key {x, y} (mem_filter.2 ⟨mem_powerset.2 hsub, Or.inr ⟨x, mem_Icc.2 ⟨by omega, by omega⟩, y,
      mem_Icc.2 ⟨by omega, by omega⟩, rfl, hxy.2.1, hxy.2.2.2.1, hxy.2.2.2.2⟩⟩) ?_
    intro a b hab hsep
    have hd := mem_diagonals.1 (hMd hab)
    dsimp only at hd
    obtain ⟨hA, hB, ⟨t1, ht1, h11, h12⟩, ⟨t2, ht2, h2⟩⟩ := (pkL_inST_iff (by omega : a < b)).1 hsep
    have m1 : t1 = x ∨ t1 = y := by
      rcases mem_insert.1 ht1 with h | h
      · exact Or.inl h
      · exact Or.inr (mem_singleton.1 h)
    have m2 : t2 = x ∨ t2 = y := by
      rcases mem_insert.1 ht2 with h | h
      · exact Or.inl h
      · exact Or.inr (mem_singleton.1 h)
    have na : a ≠ x ∧ a ≠ y := ⟨fun h => hA (h ▸ mem_insert_self x {y}),
      fun h => hA (by rw [h]; exact mem_insert_of_mem (mem_singleton_self y))⟩
    have nb : b ≠ x ∧ b ≠ y := ⟨fun h => hB (h ▸ mem_insert_self x {y}),
      fun h => hB (by rw [h]; exact mem_insert_of_mem (mem_singleton_self y))⟩
    exact pkL_T3 hcfg ⟨hi1, hij, hjN⟩ ⟨hk1, hkl, hlN⟩ (by omega) (by omega) (by omega) (hC a b hab) na nb m1 m2
      ⟨h11, h12⟩ h2
  rcases pkL_par i with hp | hp <;> rcases pkL_par k with hq | hq
  · -- (even, even)
    by_cases h1 : j ≤ k
    · exact hT2 j l (by omega) (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩)
        (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩)
    by_cases h2 : l ≤ j
    · simp only [pkL_inA_iff] at W0 W1
      omega
    by_cases h3 : i = k
    · simp only [pkL_inA_iff] at W0 W1
      omega
    exact hT2 1 l (by omega) (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩)
      (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩)
  · -- (even, odd)
    by_cases h1 : j ≤ k
    · simp only [pkL_inA_iff] at W0 W1
      omega
    by_cases h2 : l ≤ j
    · exact hT1 i (j - 1) (by omega) (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩)
        (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩)
    by_cases h3 : i = k
    · simp only [pkL_inA_iff] at W0 W1
      omega
    by_cases h4 : j < l - 1
    · exact hT2 j (l - 1) (by omega) (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩)
        (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩)
    by_cases h5 : i < k - 1
    · exact hT1 i (k - 1) (by omega) (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩)
        (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩)
    exact hT3 i j (Or.inr (Or.inr ⟨hp, hq, by omega, by omega, rfl, rfl⟩))
  · -- (odd, even)
    by_cases h1 : j ≤ k
    · simp only [pkL_inA_iff] at W0 W1
      omega
    by_cases h2 : l ≤ j
    · exact hT2 i (j - 1) (by omega) (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩)
        (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩)
    by_cases h3 : i = k
    · simp only [pkL_inA_iff] at W0 W1
      omega
    by_cases h4 : i < k - 1
    · exact hT2 i (k - 1) (by omega) (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩)
        (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩)
    by_cases h5 : j < l - 1
    · exact hT1 j (l - 1) (by omega) (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩)
        (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩)
    exact hT3 i j (Or.inr (Or.inl ⟨hp, hq, by omega, by omega, rfl, rfl⟩))
  · -- (odd, odd)
    by_cases h1 : j ≤ k
    · exact hT1 j l (by omega) (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩)
        (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩)
    by_cases h2 : l ≤ j
    · simp only [pkL_inA_iff] at W0 W1
      omega
    by_cases h3 : i = k
    · simp only [pkL_inA_iff] at W0 W1
      omega
    by_cases h4 : k < j - 1
    · exact hT2 k (j - 1) (by omega) (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩)
        (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩)
    by_cases h5 : 3 ≤ i
    · exact hT1 2 l (by omega) (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩)
        (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩)
    by_cases h6 : l < N
    · exact hT1 l N (by omega) (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩)
        (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩)
    exact hT3 k N (Or.inl ⟨hp, hq, by omega, by omega, by omega, rfl, rfl⟩)

/-! ### pkgLin-2 helpers (`pkL_`): Lemma 14.6 — Gram points evaluated on every mixed chord, sides, `minRect` -/

/-- A missing mixed pair `t` gives a point of `L_S` with `X_R = 2·[t ∈ H^A_R ∪ H^B_R]` for every mixed chord `R`. -/
theorem pkL_gA {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} (hS : S ⊆ diagonals N)
    {u v : ℕ} (huv : (u, v) ∈ diagonals N) (hnS : (u, v) ∉ S) (hmix : u % 2 ≠ v % 2) :
    ∃ X : ℕ × ℕ → ℚ, OnLocus N S X ∧ ∀ R ∈ oddDiagonals N,
      X R = if (u, v) ∈ oddSideSplit N R ∪ evenSideSplit N R then 2 else 0 := by
  have hd := mem_diagonals.1 huv
  dsimp only at hd
  have hsym : ∀ x y, pkL_sA u v x y = pkL_sA u v y x := fun x y => by
    rw [pkL_sA, pkL_sA, pkL_path_symm, p3b_e_symm]
  have hdiag : ∀ x, pkL_sA u v x x = 0 := fun x => by
    rw [pkL_sA, pkL_path_diag, p3b_e_diag (by omega)]
    ring
  have hrow : ∀ x ∈ Icc 1 N, ∑ y ∈ Icc 1 N, pkL_sA u v x y = 0 := fun x hx => by
    have e : ∀ y ∈ Icc 1 N, pkL_sA u v x y = pkL_path u v x y - p3b_e u v x y := fun y _ => rfl
    rw [sum_congr rfl e, sum_sub_distrib, pkL_path_row hd.1 (by omega) (by omega) (by omega) hx,
      p3b_e_row (mem_Icc.2 ⟨by omega, by omega⟩) (mem_Icc.2 ⟨by omega, by omega⟩), sub_self]
  have hm : ∀ t ∈ diagonals N, mesh N (p3b_Xs (pkL_sA u v)) t.1 t.2 = if t = (u, v) then 2 else 0 := by
    intro t ht
    obtain ⟨a, b⟩ := t
    have h' := mem_diagonals.1 ht
    dsimp only at h' ⊢
    rw [p3b_mesh_Xs (by omega) hsym hdiag hrow (by omega) (by omega) (by omega), pkL_sA,
      pkL_path_far (by omega), pkL_e_far (by omega) (by omega)]
    by_cases h : (a, b) = (u, v)
    · rw [if_pos h, if_pos h]
      norm_num
    · rw [if_neg h, if_neg h]
      norm_num
  refine ⟨p3b_Xs (pkL_sA u v), fun t ht => ?_, ?_⟩
  · rw [hm t (hS ht), if_neg (fun e : t = (u, v) => hnS (e ▸ ht))]
  · intro R hR
    obtain ⟨i, j⟩ := R
    have hHsub : oddSideSplit N (i, j) ∪ evenSideSplit N (i, j) ⊆ diagonals N :=
      union_subset (fun t ht => (mem_filter.1 ht).1) (fun t ht => (mem_filter.1 ht).1)
    rw [pkL_hit0 hN hE (p3b_Xs (pkL_sA u v)) hR, sum_congr rfl (fun t ht => hm t (hHsub ht)),
      sum_congr rfl (fun t ht => hm t (filter_subset _ _ ht)), pkL_sumH_ite, pkL_sumH_ite,
      if_neg (show (u, v) ∉ (diagonals N).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0) from
        fun h => by have := (mem_filter.1 h).2; dsimp only at this; omega), sub_zero]

/-- A missing ee pair `e` and a missing oo pair `o` give a point of `L_S` with
`X_R = 2 − 2·[e ∈ H_R] − 2·[o ∈ H_R]` for every mixed chord `R`. -/
theorem pkL_gB {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} (hS : S ⊆ diagonals N)
    {e1 e2 o1 o2 : ℕ} (he : (e1, e2) ∈ diagonals N) (ho : (o1, o2) ∈ diagonals N) (heS : (e1, e2) ∉ S)
    (hoS : (o1, o2) ∉ S) (hee : e1 % 2 = 0 ∧ e2 % 2 = 0) (hoo : o1 % 2 = 1 ∧ o2 % 2 = 1) :
    ∃ X : ℕ × ℕ → ℚ, OnLocus N S X ∧ ∀ R ∈ oddDiagonals N,
      X R = 2 + (if (e1, e2) ∈ oddSideSplit N R ∪ evenSideSplit N R then -2 else 0) +
        (if (o1, o2) ∈ oddSideSplit N R ∪ evenSideSplit N R then -2 else 0) := by
  have hd1 := mem_diagonals.1 he
  have hd2 := mem_diagonals.1 ho
  dsimp only at hd1 hd2
  have hsym : ∀ x y, pkL_sB e1 e2 o1 o2 x y = pkL_sB e1 e2 o1 o2 y x := fun x y => by
    rw [pkL_sB, pkL_sB, pkL_path_symm (min e1 o1), pkL_path_symm (min e2 o2), p3b_e_symm e1, p3b_e_symm o1]
  have hdiag : ∀ x, pkL_sB e1 e2 o1 o2 x x = 0 := fun x => by
    rw [pkL_sB, pkL_path_diag, pkL_path_diag, p3b_e_diag (by omega), p3b_e_diag (by omega)]
    ring
  have hrow : ∀ x ∈ Icc 1 N, ∑ y ∈ Icc 1 N, pkL_sB e1 e2 o1 o2 x y = 0 := fun x hx => by
    have e : ∀ y ∈ Icc 1 N, pkL_sB e1 e2 o1 o2 x y = p3b_e e1 e2 x y + p3b_e o1 o2 x y -
        pkL_path (min e1 o1) (max e1 o1) x y - pkL_path (min e2 o2) (max e2 o2) x y := fun y _ => rfl
    rw [sum_congr rfl e, sum_sub_distrib, sum_sub_distrib, sum_add_distrib,
      p3b_e_row (mem_Icc.2 ⟨by omega, by omega⟩) (mem_Icc.2 ⟨by omega, by omega⟩),
      p3b_e_row (mem_Icc.2 ⟨by omega, by omega⟩) (mem_Icc.2 ⟨by omega, by omega⟩),
      pkL_path_row' (by omega) (by omega) (by omega) (by omega) (by omega) hx,
      pkL_path_row' (by omega) (by omega) (by omega) (by omega) (by omega) hx]
    ring
  have hm : ∀ t ∈ diagonals N, mesh N (p3b_Xs (pkL_sB e1 e2 o1 o2)) t.1 t.2 =
      (if t = (e1, e2) then -2 else 0) + (if t = (o1, o2) then -2 else 0) := by
    intro t ht
    obtain ⟨a, b⟩ := t
    have h' := mem_diagonals.1 ht
    dsimp only at h' ⊢
    rw [p3b_mesh_Xs (by omega) hsym hdiag hrow (by omega) (by omega) (by omega), pkL_sB,
      pkL_path_far (by omega), pkL_path_far (by omega), pkL_e_far (by omega) (by omega),
      pkL_e_far (by omega) (by omega)]
    split_ifs <;> norm_num
  refine ⟨p3b_Xs (pkL_sB e1 e2 o1 o2), fun t ht => ?_, ?_⟩
  · rw [hm t (hS ht), if_neg (fun e : t = (e1, e2) => heS (e ▸ ht)), if_neg (fun e : t = (o1, o2) => hoS (e ▸ ht))]
    norm_num
  · intro R hR
    obtain ⟨i, j⟩ := R
    have hHsub : oddSideSplit N (i, j) ∪ evenSideSplit N (i, j) ⊆ diagonals N :=
      union_subset (fun t ht => (mem_filter.1 ht).1) (fun t ht => (mem_filter.1 ht).1)
    rw [pkL_hit0 hN hE (p3b_Xs (pkL_sB e1 e2 o1 o2)) hR, sum_congr rfl (fun t ht => hm t (hHsub ht)),
      sum_congr rfl (fun t ht => hm t (filter_subset _ _ ht)), sum_add_distrib, sum_add_distrib,
      pkL_sumH_ite, pkL_sumH_ite, pkL_sumH_ite, pkL_sumH_ite,
      if_pos (mem_filter.2 ⟨he, hee⟩), if_neg (show (o1, o2) ∉ (diagonals N).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0) from
        fun h => by have := (mem_filter.1 h).2; dsimp only at this; omega)]
    ring

theorem pkL_mem_oddSide {N i j x : ℕ} (hi : 1 ≤ i) (hj : j ≤ N) :
    x ∈ oddSide N (i, j) ↔ (1 ≤ x ∧ x ≤ N ∧ pkL_inA i j x) := by
  have e : oddSide N (i, j) = if i % 2 = 1 then Icc i (j - 1) else Icc 1 N \ Icc i (j - 1) := rfl
  rw [e, pkL_inA_iff]
  by_cases h : i % 2 = 1
  · rw [if_pos h]
    simp only [mem_Icc]
    constructor <;> intro h' <;> omega
  · rw [if_neg h]
    simp only [mem_Icc, mem_sdiff]
    constructor <;> intro h' <;> omega

theorem pkL_mem_evenSide {N i j x : ℕ} (hi : 1 ≤ i) (hj : j ≤ N) :
    x ∈ evenSide N (i, j) ↔ (1 ≤ x ∧ x ≤ N ∧ ¬ pkL_inA i j x) := by
  have e : evenSide N (i, j) = Icc 1 N \ oddSide N (i, j) := rfl
  rw [e, mem_sdiff, pkL_mem_oddSide hi hj, mem_Icc]
  exact ⟨fun h => ⟨h.1.1, h.1.2, fun h' => h.2 ⟨h.1.1, h.1.2, h'⟩⟩, fun h => ⟨⟨h.1, h.2.1⟩, fun h' => h.2.2 h'.2.2⟩⟩

/-- `minRect(R)` pairs are mixed and in the cut dictionary of `R`. -/
theorem pkL_minRect_Psi {N i j a b : ℕ} (hi : 1 ≤ i) (hj : j ≤ N) (h : (a, b) ∈ minRect N (i, j)) :
    a % 2 ≠ b % 2 ∧ pkL_Psi i j a b := by
  have e : minRect N (i, j) = (evens (oddSide N (i, j)) ×ˢ odds (evenSide N (i, j))).image
      (fun q => (min q.1 q.2, max q.1 q.2)) := rfl
  rw [e] at h
  obtain ⟨⟨u, w⟩, hq, he⟩ := mem_image.1 h
  obtain ⟨hu, hw⟩ := mem_product.1 hq
  have hu' := mem_filter.1 hu
  have hw' := mem_filter.1 hw
  dsimp only at hu' hw' he
  have hu2 := (pkL_mem_oddSide hi hj).1 hu'.1
  have hw2 := (pkL_mem_evenSide hi hj).1 hw'.1
  obtain ⟨h1, h2⟩ := Prod.ext_iff.1 he
  dsimp only at h1 h2
  rw [pkL_Psi_iff]
  rcases Nat.lt_or_ge u w with hlt | hge
  · rw [min_eq_left hlt.le] at h1
    rw [max_eq_right hlt.le] at h2
    subst h1
    subst h2
    exact ⟨by omega, Or.inl ⟨hu'.2, hw'.2, hu2.2.2, hw2.2.2⟩⟩
  · rw [min_eq_right hge] at h1
    rw [max_eq_left hge] at h2
    subst h1
    subst h2
    exact ⟨by omega, Or.inr (Or.inl ⟨hw'.2, hu'.2, hu2.2.2, hw2.2.2⟩)⟩

/-- A mixed pair in the cut dictionary of `R` lies in `minRect(R)`. -/
theorem pkL_Psi_minRect {N i j a b : ℕ} (hi : 1 ≤ i) (hj : j ≤ N) (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ N)
    (hmix : a % 2 ≠ b % 2) (h : pkL_Psi i j a b) : (a, b) ∈ minRect N (i, j) := by
  have e : minRect N (i, j) = (evens (oddSide N (i, j)) ×ˢ odds (evenSide N (i, j))).image
      (fun q => (min q.1 q.2, max q.1 q.2)) := rfl
  rw [e]
  rw [pkL_Psi_iff] at h
  rcases h with h | h | h | h
  · refine mem_image.2 ⟨(a, b), mem_product.2 ⟨mem_filter.2 ⟨(pkL_mem_oddSide hi hj).2 ⟨ha, by omega, h.2.2.1⟩, h.1⟩,
      mem_filter.2 ⟨(pkL_mem_evenSide hi hj).2 ⟨by omega, hb, h.2.2.2⟩, h.2.1⟩⟩, ?_⟩
    dsimp only
    rw [min_eq_left hab.le, max_eq_right hab.le]
  · refine mem_image.2 ⟨(b, a), mem_product.2 ⟨mem_filter.2 ⟨(pkL_mem_oddSide hi hj).2 ⟨by omega, hb, h.2.2.1⟩, h.2.1⟩,
      mem_filter.2 ⟨(pkL_mem_evenSide hi hj).2 ⟨ha, by omega, h.2.2.2⟩, h.1⟩⟩, ?_⟩
    dsimp only
    rw [min_eq_right hab.le, max_eq_left hab.le]
  · exact absurd (h.1.trans h.2.1.symm) hmix
  · exact absurd (h.1.trans h.2.1.symm) hmix

theorem pkL_Cond_swap {i j k l a b : ℕ} (h : pkL_Cond i j k l a b) : pkL_Cond k l i j a b := by
  rw [pkL_Cond_iff] at h ⊢
  exact ⟨fun hm => (h.1 hm).symm, fun hs => ⟨(h.2 hs).1.symm, fun hb => (h.2 hs).2 hb.symm⟩⟩

theorem pkL_ite_iff {p q : Prop} [Decidable p] [Decidable q]
    (h : (if q then (-2 : ℚ) else 0) = (if p then -2 else 0)) : q ↔ p := by
  by_cases hp : p <;> by_cases hq : q
  · exact ⟨fun _ => hp, fun _ => hq⟩
  · rw [if_pos hp, if_neg hq] at h
    norm_num at h
  · rw [if_neg hp, if_pos hq] at h
    norm_num at h
  · exact ⟨fun h' => absurd h' hq, fun h' => absurd h' hp⟩

theorem pkL_ite_flip {p q : Prop} [Decidable p] [Decidable q]
    (h : (if q then (-2 : ℚ) else 0) = -2 - (if p then -2 else 0)) : q ↔ ¬ p := by
  by_cases hp : p <;> by_cases hq : q
  · rw [if_pos hp, if_pos hq] at h
    norm_num at h
  · exact ⟨fun h' => absurd h' hq, fun h' => absurd hp h'⟩
  · exact ⟨fun _ => hp, fun _ => hq⟩
  · rw [if_neg hp, if_neg hq] at h
    norm_num at h

/-- `sorry` (pkgLin) · **Lemma 14.6 (proportionality; Lemma U)** [v3 §14.4]: for `S ∈ F^π_N`, `P ∈ 𝒫₁` and a mixed chord
`Q`: `X_Q = λ X_P` on `L_S` for some `λ ≠ 0` iff `h_Q = h_P`; and any such `λ` is `+1`, with `Q ∈ 𝒫₁`. -/
theorem lemma14_6 {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {S : Finset (ℕ × ℕ)} (hF : InFpi N S) {P Q : ℕ × ℕ}
    (hP : P ∈ poleChords N S) (hQ : Q ∈ oddDiagonals N) :
    ((∃ c : ℚ, c ≠ 0 ∧ ∀ X : ℕ × ℕ → ℚ, OnLocus N S X → X Q = c * X P) ↔ hitSet N S Q = hitSet N S P) ∧
      ∀ c : ℚ, c ≠ 0 → (∀ X : ℕ × ℕ → ℚ, OnLocus N S X → X Q = c * X P) → c = 1 ∧ Q ∈ poleChords N S := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  have hS : S ⊆ diagonals N := hF.1
  have hT : Transversal N (missing N S) := (fpi_iff (by omega) hE hS).1 hF
  have hMd : missing N S ⊆ diagonals N := sdiff_subset
  obtain ⟨i, j⟩ := P
  obtain ⟨k, l⟩ := Q
  have hPc := (mem_filter.1 hP).1
  have hPo : (i, j) ∈ oddDiagonals N := (mem_filter.1 hPc).1
  have hdisj : Disjoint (minRect N (i, j)) (missing N S) := (mem_filter.1 hPc).2
  obtain ⟨⟨e0, he0⟩, ⟨o0, ho0⟩⟩ := (mem_filter.1 hP).2
  obtain ⟨hi1, hjN, hij, hne1, hod1⟩ := pkL_oddD hPo
  obtain ⟨hk1, hlN, hkl, hne2, hod2⟩ := pkL_oddD hQ
  have hH : ∀ r s, (r, s) ∈ oddDiagonals N → ∀ a b, (a, b) ∈ missing N S →
      ((a, b) ∈ oddSideSplit N (r, s) ∪ evenSideSplit N (r, s) ↔ pkL_Psi r s a b) := by
    intro r s hR a b hm
    have hd := mem_diagonals.1 (hMd hm)
    dsimp only at hd
    exact ⟨pkL_H_to hR (by omega), pkL_H_of hE' hR (by omega) (by omega) (by omega) (by omega)⟩
  -- (1) the pattern of `P`
  have F1 : ∀ a b, (a, b) ∈ missing N S → a % 2 ≠ b % 2 → ¬ pkL_Psi i j a b := by
    intro a b hm hmix hΨ
    have hd := mem_diagonals.1 (hMd hm)
    dsimp only at hd
    exact disjoint_left.1 hdisj (pkL_Psi_minRect hi1 hjN (by omega) (by omega) (by omega) hmix hΨ) hm
  have F2e : ∃ a b, (a, b) ∈ missing N S ∧ a % 2 = 0 ∧ b % 2 = 0 ∧ pkL_Psi i j a b := by
    obtain ⟨⟨a, b⟩, ht⟩ := hT _ (pkL_HA_mem hPo)
    obtain ⟨h1, h2⟩ := mem_inter.1 ht
    have hd := mem_diagonals.1 (hMd h2)
    dsimp only at hd
    have hΨ : pkL_Psi i j a b := (hH i j hPo a b h2).1 (mem_union_left _ h1)
    have hno := pkL_HA_noOO hPo h1 (by omega)
    rcases pkL_par a with ha | ha <;> rcases pkL_par b with hb | hb
    · exact ⟨a, b, h2, ha, hb, hΨ⟩
    · exact absurd hΨ (F1 a b h2 (by omega))
    · exact absurd hΨ (F1 a b h2 (by omega))
    · exact absurd ⟨ha, hb⟩ hno
  have F2o : ∃ a b, (a, b) ∈ missing N S ∧ a % 2 = 1 ∧ b % 2 = 1 ∧ pkL_Psi i j a b := by
    obtain ⟨⟨a, b⟩, ht⟩ := hT _ (pkL_HB_mem hE' hPo)
    obtain ⟨h1, h2⟩ := mem_inter.1 ht
    have hd := mem_diagonals.1 (hMd h2)
    dsimp only at hd
    have hΨ : pkL_Psi i j a b := (hH i j hPo a b h2).1 (mem_union_right _ h1)
    have hno := pkL_HB_noEE hPo h1 (by omega)
    rcases pkL_par a with ha | ha <;> rcases pkL_par b with hb | hb
    · exact absurd ⟨ha, hb⟩ hno
    · exact absurd hΨ (F1 a b h2 (by omega))
    · exact absurd hΨ (F1 a b h2 (by omega))
    · exact ⟨a, b, h2, ha, hb, hΨ⟩
  obtain ⟨a1, b1, hm1, ha1, hb1, hΨ1⟩ := F2e
  obtain ⟨c1, d1, hn1, hc1, hd1, hΦ1⟩ := F2o
  obtain ⟨a0, b0⟩ := e0
  obtain ⟨c0, d0⟩ := o0
  have he0' := mem_filter.1 he0
  have he0'' := mem_filter.1 he0'.1
  have ho0' := mem_filter.1 ho0
  have ho0'' := mem_filter.1 ho0'.1
  dsimp only at he0' he0'' ho0' ho0''
  have hm0 : (a0, b0) ∈ missing N S := he0''.1
  have hn0 : (c0, d0) ∈ missing N S := ho0''.1
  have hΨ0 : ¬ pkL_Psi i j a0 b0 := by
    rw [pkL_Psi_ee he0''.2.1 he0''.2.2]
    rintro (h | h)
    · exact ((pkL_mem_evenSide hi1 hjN).1 he0'.2.1).2.2 h
    · exact ((pkL_mem_evenSide hi1 hjN).1 he0'.2.2).2.2 h
  have hΦ0 : ¬ pkL_Psi i j c0 d0 := by
    rw [pkL_Psi_oo ho0''.2.1 ho0''.2.2]
    rintro (h | h)
    · exact h ((pkL_mem_oddSide hi1 hjN).1 ho0'.2.1).2.2
    · exact h ((pkL_mem_oddSide hi1 hjN).1 ho0'.2.2).2.2
  have nPe0 : (a0, b0) ∉ oddSideSplit N (i, j) ∪ evenSideSplit N (i, j) := fun h => hΨ0 ((hH i j hPo a0 b0 hm0).1 h)
  have nPo0 : (c0, d0) ∉ oddSideSplit N (i, j) ∪ evenSideSplit N (i, j) := fun h => hΦ0 ((hH i j hPo c0 d0 hn0).1 h)
  have yPe1 : (a1, b1) ∈ oddSideSplit N (i, j) ∪ evenSideSplit N (i, j) := (hH i j hPo a1 b1 hm1).2 hΨ1
  have yPo1 : (c1, d1) ∈ oddSideSplit N (i, j) ∪ evenSideSplit N (i, j) := (hH i j hPo c1 d1 hn1).2 hΦ1
  -- (2) the Gram points turn `X_Q = c·X_P` into coordinate conditions
  have main : ∀ c : ℚ, c ≠ 0 → (∀ X : ℕ × ℕ → ℚ, OnLocus N S X → X (k, l) = c * X (i, j)) →
      c = 1 ∧ ∀ t ∈ missing N S, (t ∈ oddSideSplit N (k, l) ∪ evenSideSplit N (k, l) ↔
        t ∈ oddSideSplit N (i, j) ∪ evenSideSplit N (i, j)) := by
    intro c hc0 hc
    have G1 : ∀ a b, (a, b) ∈ missing N S → a % 2 ≠ b % 2 → ¬ pkL_Psi k l a b := by
      intro a b hm hmix hΨ
      have hm' := mem_sdiff.1 hm
      obtain ⟨X, hX, hXR⟩ := pkL_gA (by omega) hE' hS hm'.1 hm'.2 hmix
      have h := hc X hX
      rw [hXR _ hQ, hXR _ hPo, if_pos ((hH k l hQ a b hm).2 hΨ),
        if_neg (fun h => F1 a b hm hmix ((hH i j hPo a b hm).1 h))] at h
      norm_num at h
    have G2 : ∀ a b a' b', (a, b) ∈ missing N S → a % 2 = 0 → b % 2 = 0 → (a', b') ∈ missing N S →
        a' % 2 = 1 → b' % 2 = 1 →
        2 + (if (a, b) ∈ oddSideSplit N (k, l) ∪ evenSideSplit N (k, l) then (-2 : ℚ) else 0) +
          (if (a', b') ∈ oddSideSplit N (k, l) ∪ evenSideSplit N (k, l) then -2 else 0) =
          c * (2 + (if (a, b) ∈ oddSideSplit N (i, j) ∪ evenSideSplit N (i, j) then -2 else 0) +
            (if (a', b') ∈ oddSideSplit N (i, j) ∪ evenSideSplit N (i, j) then -2 else 0)) := by
      intro a b a' b' hm ha hb hm' ha' hb'
      have h1 := mem_sdiff.1 hm
      have h2 := mem_sdiff.1 hm'
      obtain ⟨X, hX, hXR⟩ := pkL_gB (by omega) hE' hS h1.1 h2.1 h1.2 h2.2 ⟨ha, hb⟩ ⟨ha', hb'⟩
      have h := hc X hX
      rw [hXR _ hQ, hXR _ hPo] at h
      exact h
    have hcase : (c = 1 ∧ (a0, b0) ∉ oddSideSplit N (k, l) ∪ evenSideSplit N (k, l) ∧
          (c0, d0) ∉ oddSideSplit N (k, l) ∪ evenSideSplit N (k, l)) ∨
        (c = -1 ∧ (a0, b0) ∈ oddSideSplit N (k, l) ∪ evenSideSplit N (k, l) ∧
          (c0, d0) ∈ oddSideSplit N (k, l) ∪ evenSideSplit N (k, l)) := by
      have E := G2 a0 b0 c0 d0 hm0 he0''.2.1 he0''.2.2 hn0 ho0''.2.1 ho0''.2.2
      rw [if_neg nPe0, if_neg nPo0] at E
      by_cases q1 : (a0, b0) ∈ oddSideSplit N (k, l) ∪ evenSideSplit N (k, l) <;>
        by_cases q2 : (c0, d0) ∈ oddSideSplit N (k, l) ∪ evenSideSplit N (k, l)
      · rw [if_pos q1, if_pos q2] at E
        exact Or.inr ⟨by linarith, q1, q2⟩
      · rw [if_pos q1, if_neg q2] at E
        exact absurd (by linarith : c = 0) hc0
      · rw [if_neg q1, if_pos q2] at E
        exact absurd (by linarith : c = 0) hc0
      · rw [if_neg q1, if_neg q2] at E
        exact Or.inl ⟨by linarith, q1, q2⟩
    rcases hcase with ⟨rfl, q1, q2⟩ | ⟨rfl, q1, q2⟩
    · refine ⟨rfl, ?_⟩
      rintro ⟨a, b⟩ hm
      have hd := mem_diagonals.1 (hMd hm)
      dsimp only at hd
      rcases pkL_par a with ha | ha <;> rcases pkL_par b with hb | hb
      · have E := G2 a b c0 d0 hm ha hb hn0 ho0''.2.1 ho0''.2.2
        rw [if_neg nPo0, if_neg q2] at E
        exact pkL_ite_iff (by linarith)
      · exact ⟨fun h => absurd ((hH k l hQ a b hm).1 h) (G1 a b hm (by omega)),
          fun h => absurd ((hH i j hPo a b hm).1 h) (F1 a b hm (by omega))⟩
      · exact ⟨fun h => absurd ((hH k l hQ a b hm).1 h) (G1 a b hm (by omega)),
          fun h => absurd ((hH i j hPo a b hm).1 h) (F1 a b hm (by omega))⟩
      · have E := G2 a0 b0 a b hm0 he0''.2.1 he0''.2.2 hm ha hb
        rw [if_neg nPe0, if_neg q1] at E
        exact pkL_ite_iff (by linarith)
    · exfalso
      have hflip : ∀ a b, (a, b) ∈ missing N S → a % 2 = b % 2 → (pkL_Psi k l a b ↔ ¬ pkL_Psi i j a b) := by
        intro a b hm hs
        rw [← hH k l hQ a b hm, ← hH i j hPo a b hm]
        rcases pkL_par a with ha | ha
        · have E := G2 a b c0 d0 hm ha (by omega) hn0 ho0''.2.1 ho0''.2.2
          rw [if_neg nPo0, if_pos q2] at E
          exact pkL_ite_flip (by linarith)
        · have E := G2 a0 b0 a b hm0 he0''.2.1 he0''.2.2 hm ha (by omega)
          rw [if_neg nPe0, if_pos q1] at E
          exact pkL_ite_flip (by linarith)
      have hC : ∀ a b, (a, b) ∈ missing N S → pkL_Cond i j k l a b := by
        intro a b hm
        rw [pkL_Cond_iff]
        refine ⟨fun hmix => ⟨F1 a b hm hmix, G1 a b hm hmix⟩, fun hs => ⟨?_, fun h => (hflip a b hm hs).1 h.2 h.1⟩⟩
        by_cases hp : pkL_Psi i j a b
        · exact Or.inl hp
        · exact Or.inr ((hflip a b hm hs).2 hp)
      have hw0 : ∃ a b, (a, b) ∈ missing N S ∧ a % 2 = 0 ∧ b % 2 = 0 ∧ ¬ pkL_Psi i j a b :=
        ⟨a0, b0, hm0, he0''.2.1, he0''.2.2, hΨ0⟩
      have hw1 : ∃ a b, (a, b) ∈ missing N S ∧ a % 2 = 0 ∧ b % 2 = 0 ∧ ¬ pkL_Psi k l a b :=
        ⟨a1, b1, hm1, ha1, hb1, fun h => (hflip a1 b1 hm1 (by omega)).1 h hΨ1⟩
      rcases le_total i k with hik | hki
      · exact pkL_noSign_core hE' hPo hQ hik hMd hT hC hw0 hw1
      · exact pkL_noSign_core hE' hQ hPo hki hMd hT (fun a b hm => pkL_Cond_swap (hC a b hm)) hw1 hw0
  -- (3) assembly
  have hitEq : ∀ c : ℚ, c ≠ 0 → (∀ X : ℕ × ℕ → ℚ, OnLocus N S X → X (k, l) = c * X (i, j)) →
      hitSet N S (k, l) = hitSet N S (i, j) := by
    intro c hc0 hc
    have hm := (main c hc0 hc).2
    have e1 : hitSet N S (k, l) = missing N S ∩ (oddSideSplit N (k, l) ∪ evenSideSplit N (k, l)) := rfl
    have e2 : hitSet N S (i, j) = missing N S ∩ (oddSideSplit N (i, j) ∪ evenSideSplit N (i, j)) := rfl
    rw [e1, e2]
    ext t
    rw [mem_inter, mem_inter]
    exact ⟨fun h => ⟨h.1, (hm t h.1).1 h.2⟩, fun h => ⟨h.1, (hm t h.1).2 h.2⟩⟩
  have pole : ∀ c : ℚ, c ≠ 0 → (∀ X : ℕ × ℕ → ℚ, OnLocus N S X → X (k, l) = c * X (i, j)) →
      (k, l) ∈ poleChords N S := by
    intro c hc0 hc
    have hm := (main c hc0 hc).2
    have nQe : ¬ pkL_Psi k l a0 b0 := fun h => nPe0 ((hm _ hm0).1 ((hH k l hQ a0 b0 hm0).2 h))
    have nQo : ¬ pkL_Psi k l c0 d0 := fun h => nPo0 ((hm _ hn0).1 ((hH k l hQ c0 d0 hn0).2 h))
    rw [pkL_Psi_ee he0''.2.1 he0''.2.2] at nQe
    rw [pkL_Psi_oo ho0''.2.1 ho0''.2.2] at nQo
    have hd0 := mem_diagonals.1 (hMd hm0)
    have hd1 := mem_diagonals.1 (hMd hn0)
    dsimp only at hd0 hd1
    refine mem_filter.2 ⟨mem_filter.2 ⟨hQ, disjoint_left.2 (fun t ht htm => ?_)⟩, ⟨⟨(a0, b0), ?_⟩, ⟨(c0, d0), ?_⟩⟩⟩
    · obtain ⟨a, b⟩ := t
      obtain ⟨hmix, hΨ⟩ := pkL_minRect_Psi hk1 hlN ht
      exact F1 a b htm hmix ((hH i j hPo a b htm).1 ((hm _ htm).1 ((hH k l hQ a b htm).2 hΨ)))
    · exact mem_filter.2 ⟨he0'.1, (pkL_mem_evenSide hk1 hlN).2 ⟨by omega, by omega, fun h => nQe (Or.inl h)⟩,
        (pkL_mem_evenSide hk1 hlN).2 ⟨by omega, by omega, fun h => nQe (Or.inr h)⟩⟩
    · exact mem_filter.2 ⟨ho0'.1, (pkL_mem_oddSide hk1 hlN).2 ⟨by omega, by omega, not_not.1 (fun h => nQo (Or.inl h))⟩,
        (pkL_mem_oddSide hk1 hlN).2 ⟨by omega, by omega, not_not.1 (fun h => nQo (Or.inr h))⟩⟩
  refine ⟨⟨fun h => ?_, fun heq => ⟨1, one_ne_zero, fun X hX => ?_⟩⟩, fun c hc0 hc => ⟨(main c hc0 hc).1, pole c hc0 hc⟩⟩
  · obtain ⟨c, hc0, hc⟩ := h
    exact hitEq c hc0 hc
  · rw [chord_restrict (by omega) hE hS X hX hQ, chord_restrict (by omega) hE hS X hX hPo, heq, one_mul]

/-! ## 5b. Sides as cyclic arcs, admissible separators (traces), Sep_all, the canonical chord, children
[v3 §14.2a; BP §2.4–§2.5, §2.8]

A side of a mixed chord is a cyclic arc `(s, k)`: its legs are `vtx N (s + i)`, `i < k`, and the position of a leg `x` in
it is `cycPos N s x = (x + N − s) % N` (legs are `1..N`, so `x + N − s` does not truncate). A mixed chord `P = (i, j)`
cuts the legs into `[i, j − 1]` and its complement; the head (odd-ended side) starts at the odd one of `i`, `j`
(`headStart`), the tail at the even one (`tailStart`); `oddSide`/`evenSide` (P7a) are the same sets
(`sides_eq_cycArc`, pkgComb). Hub parity: `0` (even) for a head, `1` (odd) for a tail [v3 §14.2a]. Python mirror of
this section: `../mirror_b.py` (thread §6). -/

/-- The cyclic arc of `len` legs starting at leg `a`. -/
def cycArc (N a len : ℕ) : Finset ℕ := (range len).image (fun k => vtx N (a + k))

/-- Position of leg `x` in the cyclic arc starting at `s` (`0` for `s` itself). -/
def cycPos (N s x : ℕ) : ℕ := (x + N - s) % N

/-- First leg of the head (odd-ended side) of a mixed chord `P = (i, j)`. -/
def headStart (P : ℕ × ℕ) : ℕ := if P.1 % 2 = 1 then P.1 else P.2

/-- Number of legs of the head of `P`. -/
def headLen (N : ℕ) (P : ℕ × ℕ) : ℕ := if P.1 % 2 = 1 then P.2 - P.1 else N - (P.2 - P.1)

/-- First leg of the tail (even-ended side) of `P`. -/
def tailStart (P : ℕ × ℕ) : ℕ := if P.1 % 2 = 1 then P.2 else P.1

/-- Number of legs of the tail of `P`. -/
def tailLen (N : ℕ) (P : ℕ × ℕ) : ℕ := N - headLen N P

/-- `int L`: the legs of the arc other than its two end legs. -/
def intArc (N s k : ℕ) : Finset ℕ := (cycArc N s k).filter (fun x => 1 ≤ cycPos N s x ∧ cycPos N s x + 2 ≤ k)

/-- **Admissible separators (traces)** of the arc `(s, k)` with hub parity `q` [v3 §14.2a "admissible trace"]: one
interior leg (either parity), or at least two interior legs, all of parity `q`. -/
def admSeps (N s k q : ℕ) : Finset (Finset ℕ) :=
  (intArc N s k).powerset.filter (fun Θ => Θ.card = 1 ∨ (2 ≤ Θ.card ∧ ∀ θ ∈ Θ, θ % 2 = q))

/-- **`runcut_L(Θ)`** (BP §7 `sepIn`: the pairs of `L` separated by `Θ`) [v3 §14.2a]: pairs with both legs in the arc,
no leg in `Θ`, and a leg of `Θ` strictly between them along the arc. -/
def sepIn (N s k : ℕ) (Θ : Finset ℕ) : Finset (ℕ × ℕ) :=
  (diagonals N).filter (fun p => p.1 ∈ cycArc N s k ∧ p.2 ∈ cycArc N s k ∧ p.1 ∉ Θ ∧ p.2 ∉ Θ ∧
    ∃ θ ∈ Θ, min (cycPos N s p.1) (cycPos N s p.2) < cycPos N s θ ∧ cycPos N s θ < max (cycPos N s p.1) (cycPos N s p.2))

/-- **`Sep_all(L)`** (BP §7 `NoFreeSep`) [v3 §14.2a, failing-trace form]: no admissible separator `Θ` of the arc has
`runcut_L(Θ) ∩ M = ∅` (every missing pair counts, mixed ones included; BP G-6). -/
def NoFreeSep (N : ℕ) (S : Finset (ℕ × ℕ)) (s k q : ℕ) : Prop :=
  ∀ Θ ∈ admSeps N s k q, ¬ Disjoint (sepIn N s k Θ) (missing N S)

instance (N : ℕ) (S : Finset (ℕ × ℕ)) (s k q : ℕ) : Decidable (NoFreeSep N S s k q) := by
  unfold NoFreeSep; infer_instance

/-- **`𝒮_B`** (BP §7 `goodTail`) [v3 §14.2a]: the `𝒫₁` chords whose tail satisfies `Sep_all`. -/
def goodTail (N : ℕ) (S : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  (poleChords N S).filter (fun P => NoFreeSep N S (tailStart P) (tailLen N P) 1)

/-- A **canonical chord** (BP §7 `IsMinimalChord`) [v3 §14.2a]: a chord of `𝒮_B` with no chord of `𝒮_B` whose head is
strictly inside its head. -/
def IsMinimalChord (N : ℕ) (S : Finset (ℕ × ℕ)) (P : ℕ × ℕ) : Prop :=
  P ∈ goodTail N S ∧ ∀ Q ∈ goodTail N S, ¬ oddSide N Q ⊂ oddSide N P

instance (N : ℕ) (S : Finset (ℕ × ℕ)) (P : ℕ × ℕ) : Decidable (IsMinimalChord N S P) := by
  unfold IsMinimalChord; infer_instance

/-- The **class** of `P` (BP §7 `hitClass`) [v3 §14.2a]: the `𝒫₁` chords with the hit set of `P`. -/
def hitClass (N : ℕ) (S : Finset (ℕ × ℕ)) (P : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  (poleChords N S).filter (fun Q => hitSet N S Q = hitSet N S P)

/-- `u`, `v` lie in the same run of `L ∖ Θ` (no leg of `Θ` strictly between them along the arc starting at `s`). -/
def SameRun (N s : ℕ) (Θ : Finset ℕ) (u v : ℕ) : Prop :=
  ¬ ∃ θ ∈ Θ, min (cycPos N s u) (cycPos N s v) < cycPos N s θ ∧ cycPos N s θ < max (cycPos N s u) (cycPos N s v)

instance (N s : ℕ) (Θ : Finset ℕ) (u v : ℕ) : Decidable (SameRun N s Θ u v) := by unfold SameRun; infer_instance

/-- A missing oo pair lies inside one run of `L ∖ Θ` (both legs in the arc, not in `Θ`, same run). -/
def InOneRun (N s k : ℕ) (Θ : Finset ℕ) (p : ℕ × ℕ) : Prop :=
  p.1 ∈ cycArc N s k ∧ p.2 ∈ cycArc N s k ∧ p.1 ∉ Θ ∧ p.2 ∉ Θ ∧ SameRun N s Θ p.1 p.2

instance (N s k : ℕ) (Θ : Finset ℕ) (p : ℕ × ℕ) : Decidable (InOneRun N s k Θ p) := by
  unfold InOneRun; infer_instance

/-- `Θ` is **spread** [v3 §14.2a]: at least two runs of `L ∖ Θ` are O-runs (contain a missing oo pair). -/
def Spread (N : ℕ) (S : Finset (ℕ × ℕ)) (s k : ℕ) (Θ : Finset ℕ) : Prop :=
  ∃ p ∈ Moo N S, ∃ p' ∈ Moo N S, InOneRun N s k Θ p ∧ InOneRun N s k Θ p' ∧ ¬ SameRun N s Θ p.1 p'.1

instance (N : ℕ) (S : Finset (ℕ × ℕ)) (s k : ℕ) (Θ : Finset ℕ) : Decidable (Spread N S s k Θ) := by
  unfold Spread; infer_instance

/-- **(Even-top′)** at `P` [v3 §14.2a]: the head of `P` has no spread failing even trace. -/
def EvenTopP (N : ℕ) (S : Finset (ℕ × ℕ)) (P : ℕ × ℕ) : Prop :=
  ∀ Θ ∈ admSeps N (headStart P) (headLen N P) 0, (∀ θ ∈ Θ, θ % 2 = 0) →
    Disjoint (sepIn N (headStart P) (headLen N P) Θ) (missing N S) → ¬ Spread N S (headStart P) (headLen N P) Θ

instance (N : ℕ) (S : Finset (ℕ × ℕ)) (P : ℕ × ℕ) : Decidable (EvenTopP N S P) := by unfold EvenTopP; infer_instance

/-! ### Children [BP §2.8, App. C §C-2 (R2-Z182 D3), parity-preserving labelling δ_L]

The child of side `L = (s, k)` is the `(k+1)`-gon whose legs are the legs of `L` in order plus the new leg `P̂`. Head
child (`s` odd): child leg `j ↦ vtx N (s + j − 1)` for `j = 1..k`, `P̂ = k + 1` (even). Tail child (`s` even): `P̂ = 1`
(odd), child leg `j ↦ vtx N (s + j − 2)` for `j = 2..k+1`. Both are shifts by an even number, so parities are preserved.
`childSet` is the child's coordinate set `S_L` [BP §2.8]: a child pair of two legs of `L` is in `S_L` iff the parent pair
is in `S`; a child pair `{u, P̂}` is in `S_L` iff every parent pair `{u, w}`, `w ∉ L`, is in `S`. (Any rotation of the
child labels gives the same F^π status and the same NLSM zero set, BP §2.8 "base caveat"; mirror plant `tailrot`.) -/

/-- Whether child pair `(j, l)` (child legs; `hat` = the new leg; `f` = child leg ↦ parent leg) is in the child set. -/
def ChildPairIn (N : ℕ) (S : Finset (ℕ × ℕ)) (s k hat : ℕ) (f : ℕ → ℕ) (j l : ℕ) : Prop :=
  if j = hat then ∀ w ∈ Icc 1 N, w ∉ cycArc N s k → (min (f l) w, max (f l) w) ∈ S
  else if l = hat then ∀ w ∈ Icc 1 N, w ∉ cycArc N s k → (min (f j) w, max (f j) w) ∈ S
  else (min (f j) (f l), max (f j) (f l)) ∈ S

instance (N : ℕ) (S : Finset (ℕ × ℕ)) (s k hat : ℕ) (f : ℕ → ℕ) (j l : ℕ) :
    Decidable (ChildPairIn N S s k hat f j l) := by unfold ChildPairIn; infer_instance

/-- The **A-child** coordinate set `S_A` of `P` (size `headLen N P + 1`) [BP §2.8]. -/
def childSetA (N : ℕ) (S : Finset (ℕ × ℕ)) (P : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  (diagonals (headLen N P + 1)).filter (fun σ => ChildPairIn N S (headStart P) (headLen N P) (headLen N P + 1)
    (fun j => vtx N (headStart P + j - 1)) σ.1 σ.2)

/-- The **B-child** coordinate set `S_B` of `P` (size `tailLen N P + 1`) [BP §2.8]. -/
def childSetB (N : ℕ) (S : Finset (ℕ × ℕ)) (P : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  (diagonals (tailLen N P + 1)).filter (fun σ => ChildPairIn N S (tailStart P) (tailLen N P) 1
    (fun j => vtx N (tailStart P + j - 2)) σ.1 σ.2)

/-! ## 6. The combinatorial core (Tri), single-witness-family form [v3 §14.3 Setting, (Tri), Remark (ii)]

Normalised as in v3: head `A′ = [1, ω]`, `ω` odd; tail `W = [ω+1, N]`, `|W| ≥ 3`; `Θ` a non-empty set of even legs of
`int A′ = [2, ω−1]`; runs `X = [x0, x1]` before `Y = [y0, y1]` of `A′ ∖ Θ`, each with at least 3 legs. Legs are `1..N`;
the leg before `x0` is `prevLeg N x0` (`N` when `x0 = 1`). "Different τ-pieces" (components of `C_N ∖ (X ∪ τ)`) is
`InST (X ∪ τ)`, the same predicate as "different arcs" in `S_G`. -/

def prevLeg (N a : ℕ) : ℕ := if a = 1 then N else a - 1

/-- `[a, b]` is a run (maximal interval) of `A′ ∖ Θ`, `A′ = [1, ω]`. -/
def IsRun (ω : ℕ) (Θ : Finset ℕ) (a b : ℕ) : Prop :=
  1 ≤ a ∧ a ≤ b ∧ b ≤ ω ∧ (a = 1 ∨ a - 1 ∈ Θ) ∧ (b = ω ∨ b + 1 ∈ Θ) ∧ ∀ w ∈ Icc a b, w ∉ Θ

instance (ω : ℕ) (Θ : Finset ℕ) (a b : ℕ) : Decidable (IsRun ω Θ a b) := by unfold IsRun; infer_instance

/-- The interior of `B = C_N ∖ [a, b]`: its legs other than its two end legs `b + 1` and `prevLeg N a`. -/
def intCompl (N a b : ℕ) : Finset ℕ := Icc 1 N \ (Icc a b ∪ {b + 1, prevLeg N a})

/-- An **admissible trace** of `C_N ∖ [a, b]`: one interior leg, or at least two odd interior legs. -/
def AdmSepCompl (N a b : ℕ) (τ : Finset ℕ) : Prop :=
  (∃ t ∈ intCompl N a b, τ = {t}) ∨ (2 ≤ τ.card ∧ τ ⊆ intCompl N a b ∧ ∀ t ∈ τ, t % 2 = 1)

instance (N a b : ℕ) (τ : Finset ℕ) : Decidable (AdmSepCompl N a b τ) := by unfold AdmSepCompl; infer_instance

/-- **(b0)-shaped**: `τ ∩ int W = ∅`, and `τ ∩ W = ∅` if `τ` is odd. -/
def TailAvoiding (N ω : ℕ) (τ : Finset ℕ) : Prop :=
  Disjoint τ (Icc (ω + 2) (N - 1)) ∧ ((∀ t ∈ τ, t % 2 = 1) → Disjoint τ (Icc (ω + 1) N))

instance (N ω : ℕ) (τ : Finset ℕ) : Decidable (TailAvoiding N ω τ) := by unfold TailAvoiding; infer_instance

/-- The **(Tri) setting** with admissible, (b0)-shaped, long traces `τ` of `B_X` and `σ` of `B_Y`. *Long*: `y0 ∉ R_τ`,
i.e. `y0 ∈ τ` or `y0` and the int-W leg `ω + 2` lie in different τ-pieces; mirror for `σ`, `x1`. -/
def ThreeSepSetting (N ω x0 x1 y0 y1 : ℕ) (Θ τ σ : Finset ℕ) : Prop :=
  N % 2 = 0 ∧ ω % 2 = 1 ∧ ω + 3 ≤ N ∧ Θ.Nonempty ∧ Θ ⊆ Icc 2 (ω - 1) ∧ (∀ θ ∈ Θ, θ % 2 = 0) ∧
    IsRun ω Θ x0 x1 ∧ IsRun ω Θ y0 y1 ∧ x1 < y0 ∧ x0 + 2 ≤ x1 ∧ y0 + 2 ≤ y1 ∧
    AdmSepCompl N x0 x1 τ ∧ AdmSepCompl N y0 y1 σ ∧ TailAvoiding N ω τ ∧ TailAvoiding N ω σ ∧
    (y0 ∈ τ ∨ InST (Icc x0 x1 ∪ τ) y0 (ω + 2)) ∧ (x1 ∈ σ ∨ InST (Icc y0 y1 ∪ σ) x1 (ω + 2))

instance (N ω x0 x1 y0 y1 : ℕ) (Θ τ σ : Finset ℕ) : Decidable (ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ) := by
  unfold ThreeSepSetting; infer_instance

/-- `RC_A`: `u, v ∈ A′ ∖ Θ` in different runs of `A′ ∖ Θ`. -/
def runSepA (ω : ℕ) (Θ : Finset ℕ) (u v : ℕ) : Prop :=
  u ∈ Icc 1 ω ∧ v ∈ Icc 1 ω ∧ u ∉ Θ ∧ v ∉ Θ ∧ ∃ θ ∈ Θ, min u v < θ ∧ θ < max u v

instance (ω : ℕ) (Θ : Finset ℕ) (u v : ℕ) : Decidable (runSepA ω Θ u v) := by unfold runSepA; infer_instance

/-- `C₀ = RC_A ∪ RC_X ∪ RC_Y`, as a set of pairs. -/
def threeSepCut (N ω x0 x1 y0 y1 : ℕ) (Θ τ σ : Finset ℕ) : Finset (ℕ × ℕ) :=
  (diagonals N).filter (fun p => runSepA ω Θ p.1 p.2 ∨ InST (Icc x0 x1 ∪ τ) p.1 p.2 ∨ InST (Icc y0 y1 ∪ σ) p.1 p.2)

/-- `F_U` [v3 §14.3 Remark (ii)]: at least two cyclically consecutive legs of `U_e` (even legs of `Θ ∪ τ ∪ σ`) or of
`U_o` (odd legs of `τ ∪ σ`), i.e. `U_• ∩ (one cyclic arc)` with at least two legs. -/
def ConsecWit (N : ℕ) (Θ τ σ G : Finset ℕ) : Prop :=
  2 ≤ G.card ∧ ∃ a ∈ Icc 1 N, ∃ len ∈ range (N + 1),
    G = evens (Θ ∪ τ ∪ σ) ∩ cycArc N a len ∨ G = odds (τ ∪ σ) ∩ cycArc N a len

instance (N : ℕ) (Θ τ σ G : Finset ℕ) : Decidable (ConsecWit N Θ τ σ G) := by unfold ConsecWit; infer_instance

/-! ### pkgTri helpers (prefix `pkT_`; R12-P7b-pkgTri, opus-2026-09-27-pkgTri, model claude-opus-5-5) -/
/-! pkgTri: own copies of four small pkgComb facts (pkT_mem_cycArc_lin is declared after the target in the merged file). -/
theorem pkT_inST_iff {T : Finset ℕ} {a b : ℕ} :
    InST T a b ↔ a ∉ T ∧ b ∉ T ∧ (∃ t ∈ T, min a b < t ∧ t < max a b) ∧ (∃ t ∈ T, t < min a b ∨ max a b < t) :=
  Iff.rfl

theorem pkT_inST_comm {T : Finset ℕ} {a b : ℕ} : InST T a b ↔ InST T b a := by
  rw [pkT_inST_iff, pkT_inST_iff, min_comm, max_comm]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h2, h1, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨h2, h1, h3⟩⟩

theorem pkT_mem_cycArc {N a len x : ℕ} : x ∈ cycArc N a len ↔ ∃ k, k < len ∧ vtx N (a + k) = x := by
  show x ∈ (range len).image (fun k => vtx N (a + k)) ↔ _
  rw [mem_image]
  simp only [mem_range]

theorem pkT_mem_cycArc_lin {N a len x : ℕ} (ha : 1 ≤ a) (hl : a + len ≤ N + 1) :
    x ∈ cycArc N a len ↔ a ≤ x ∧ x < a + len := by
  rw [pkT_mem_cycArc]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [vtx_of_mem (by omega) (by omega)]
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨x - a, by omega, by rw [vtx_of_mem (by omega) (by omega)]; omega⟩



end PiZ
