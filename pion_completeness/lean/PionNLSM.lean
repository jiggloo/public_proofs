import PionZeros

/-!
# R12-P3c: Theorem B of R2-Z30 (quartic sum = NLSM) — definitions and statements (Phase 3, step 3c-a)

Thread `surfaceology/threads/R12-P3c.md`. Reference proof: `../r2z30/PROOFS.md` §2 (Theorem B; cited PROOFS §k),
reviewed in `../r2z30rev/REVIEW.md`; NLSM-side lemmas `../r2z26/PROOFS.md` §3–§4 (cited Z26 Lemma k).
Conventions: C0 = arXiv:2312.16282 §2, exactly as Phases 1 and 3.

Phases 1 and 3 are imported unchanged: `TreeRectangleZero.lean` and `PionZeros.lean` here are byte-identical copies of
`../r12p3b/base/TreeRectangleZero.lean` and `../r12p3b/final/PionZeros.lean`, compiled to `build/` (thread §6 E1).
Reused unchanged: `amp`, `triangulations`, `diagonals`, `Crosses`, `mesh`, `OnRect`, `amp_eq_zero_of_onRect`,
`onRect_inhabited` (Phase 1); `oddDiagonals`, `quadrangulations`, `quads`, `vnumX`, `diagram`, `Qpi`, `OnZT`,
`Admissible`, `theoremA`, `ZT_inhabited`, `Qpi_six` (Phase 3).

Status markers in docstrings:
* PROVED — no `sorry` in its closure (checked by `#print axioms` at the end of the file);
* ASSEMBLED — proved from statements above it, some still `sorry`;
* `sorry` — statement only, a 3c-b target.

Design decisions (thread §4):
* **NLSM_N** is C0's definition read literally: the coefficient of `δ^{−(N−2)}` in `A_N(X + δ v₀)`, where `A_N` is
  Phase 1's `amp` evaluated over the field of Laurent series `K⸨e⸩` in `e = 1/δ`, at the point
  `X_d + v₀(d)·e⁻¹` (`shifted`). `v₀ = +1` on even–even diagonals, `−1` on odd–odd, `0` on odd diagonals
  [arXiv:2312.16282 §7.1 eqs. (7.6)–(7.7), (7.15); arXiv:2401.05483 eq. (2)]. The δ-direction is formal, the
  kinematic point is pointwise over any field `K`. Lean's `0⁻¹ = 0` can only enter through the odd diagonals, which are
  exactly NLSM's poles; every shifted diagonal is a non-zero Laurent series.
* `NLSM_eq_ps` (PROVED) turns the definition into a power-series coefficient with no Laurent series left:
  `1/(x + s/e) = e·Σ_k s^{k+1}(−x)^k e^k` for `s = ±1`.
* **Pointwise / rational boundary (IDEAS L-3).** Pointwise statements over any field stay the primary form. The
  rational-function layer is (i) polynomial numerators over a commutative ring `R` (`QP`, `AP`, `NP`, common
  denominator `oddDen`), in which residues are `zeroAt C` (set `X_C = 0`) and "no poles ⇒ polynomial" is
  divisibility (Z26 Lemma 3.1 = `prod_X_dvd_of_zeroAt`); (ii) the generic point `gen` in `RF = Frac ℚ[X]`, where
  every pointwise theorem over all fields applies with no `X ≠ 0` side conditions; (iii) `RatZeroOn V F` ("F restricts
  to the zero rational function on the linear locus V") with the one analytic bridge `line_bridge` (a polynomial
  that vanishes on `V` off a proper hypersurface vanishes on `V`), which is Phase 2's `generic_bridge` argument
  abstracted; it states the rational forms of Phase 1 (`amp_ratZero_onRect`) and Phase 3 (`theoremA_rat`) too.
-/

namespace R12P3C

open Finset R12P1 R12P3

/-! ## 1. NLSM_N (C0 δ-shift bullet) -/

section NLSMdef

variable {K : Type*} [Field K]

/-- The δ-shift direction `v₀` [arXiv:2312.16282 §7.1 eqs. (7.6)–(7.7)]: `+1` on `X_{e,e}`, `−1` on `X_{o,o}`,
`0` on `X_{o,e}` (vertex labels `1..N`, parity of the labels). -/
def shiftSign (d : ℕ × ℕ) : ℤ :=
  if d.1 % 2 = 0 ∧ d.2 % 2 = 0 then 1 else if d.1 % 2 = 1 ∧ d.2 % 2 = 1 then -1 else 0

/-- `δ = e⁻¹` as a Laurent series in `e`. -/
noncomputable def delta : LaurentSeries K := HahnSeries.single (-1 : ℤ) 1

/-- The δ-shifted point `X + δ v₀`, coordinates in `K⸨e⸩`. -/
noncomputable def shifted (X : ℕ × ℕ → K) : ℕ × ℕ → LaurentSeries K :=
  fun d => HahnSeries.C (X d) + (shiftSign d : LaurentSeries K) * delta

/-- The coefficient of `e^m = δ^{−m}` in `A_N(X + δ v₀)`, `A_N` = Phase 1's `amp` over the field `K⸨e⸩`. -/
noncomputable def shiftCoeff (N : ℕ) (m : ℤ) (X : ℕ × ℕ → K) : K := (amp N (shifted X)).coeff m

/-- **NLSM_N** (C0): the coefficient of `δ^{−(N−2)}` in `A_N(X + δ v₀)` [arXiv:2312.16282 eq. (7.15);
arXiv:2401.05483 eq. (2)]. Normalisation: `NLSM_4 = −(X₁₃ + X₂₄)` (`NLSM_four`), i.e. arXiv:2312.16282 eqs. (4.3)–(4.4)
times `(−1)^{N/2−1}` (C0). -/
noncomputable def NLSM (N : ℕ) (X : ℕ × ℕ → K) : K := shiftCoeff N ((N : ℤ) - 2) X

/-- The sign of Theorem B, `σ_N = (−1)^{N/2+1}` (PROOFS §2). -/
def sigma (N : ℕ) : ℤ := (-1) ^ (N / 2 + 1)

/-- `e · Σ_k s^{k+1} (−x)^k e^k`, the expansion of `1/(x + s·δ)` at `δ = ∞` for `s = ±1`. -/
noncomputable def shiftSeries (s : ℤ) (x : K) : PowerSeries K :=
  PowerSeries.X * PowerSeries.mk (fun k => (s : K) ^ (k + 1) * (-x) ^ k)

/-- The factor of one diagonal in the expansion: `1/X_d` (odd diagonal) or `shiftSeries`. -/
noncomputable def phi (X : ℕ × ℕ → K) (d : ℕ × ℕ) : PowerSeries K :=
  if shiftSign d = 0 then PowerSeries.C (X d)⁻¹ else shiftSeries (shiftSign d) (X d)

lemma geom_mul (s x : K) (hs : s * s = 1) :
    (PowerSeries.C s + PowerSeries.C x * PowerSeries.X) *
      PowerSeries.mk (fun k => s ^ (k + 1) * (-x) ^ k) = 1 := by
  ext n
  rw [add_mul, map_add, PowerSeries.coeff_C_mul, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_one]
  rcases n with _ | n
  · simp [pow_succ, hs]
  · rw [mul_comm PowerSeries.X, PowerSeries.coeff_succ_mul_X]
    simp only [PowerSeries.coeff_mk, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
    have : s ^ (n + 1 + 1) = s ^ n * (s * s) := by ring
    rw [this, hs]
    ring

lemma sign_sq {d : ℕ × ℕ} (h : shiftSign d ≠ 0) : ((shiftSign d : ℤ) : K) * (shiftSign d : K) = 1 := by
  unfold shiftSign at *
  split_ifs at h ⊢ <;> first | exact absurd rfl h | norm_num

/-- PROVED. `1/(X_d + v₀(d) δ)` expanded at `δ = ∞`. -/
lemma inv_shifted (X : ℕ × ℕ → K) (d : ℕ × ℕ) :
    (shifted X d)⁻¹ = HahnSeries.ofPowerSeries ℤ K (phi X d) := by
  unfold phi shifted
  split_ifs with h
  · rw [h, Int.cast_zero, zero_mul, add_zero, ← map_inv₀, HahnSeries.ofPowerSeries_C]
  · apply inv_eq_of_mul_eq_one_right
    have hδ : (delta : LaurentSeries K) * HahnSeries.single (1 : ℤ) 1 = 1 := by
      rw [delta, HahnSeries.single_mul_single]; simp
    unfold shiftSeries
    rw [map_mul, HahnSeries.ofPowerSeries_X, ← mul_assoc, add_mul, mul_assoc, hδ, mul_one]
    have e1 : HahnSeries.C (X d) * HahnSeries.single (1 : ℤ) (1 : K) + ((shiftSign d : ℤ) : LaurentSeries K) =
        HahnSeries.ofPowerSeries ℤ K (PowerSeries.C (shiftSign d : K) + PowerSeries.C (X d) * PowerSeries.X) := by
      rw [map_add, map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X,
        map_intCast]
      ring
    rw [e1, ← map_mul, geom_mul _ _ (sign_sq h), map_one]

/-- PROVED. The shifted amplitude is a power series in `e`. -/
theorem amp_shifted (N : ℕ) (X : ℕ × ℕ → K) :
    amp N (shifted X) = HahnSeries.ofPowerSeries ℤ K (∑ T ∈ triangulations N, ∏ d ∈ T, phi X d) := by
  rw [amp, map_sum]
  simp only [map_prod, inv_shifted]

/-- PROVED. `shiftCoeff` at a natural order as a power-series coefficient. -/
theorem shiftCoeff_eq_ps (N m : ℕ) (X : ℕ × ℕ → K) :
    shiftCoeff N m X = PowerSeries.coeff m (∑ T ∈ triangulations N, ∏ d ∈ T, phi X d) := by
  rw [shiftCoeff, amp_shifted, HahnSeries.ofPowerSeries_apply_coeff]

/-- PROVED. Negative orders vanish: `A_N(X + δv₀)` is `O(1/δ)`-regular at `δ = ∞`. -/
theorem shiftCoeff_neg (N : ℕ) (X : ℕ × ℕ → K) {m : ℤ} (hm : m < 0) : shiftCoeff N m X = 0 := by
  rw [shiftCoeff, amp_shifted, PowerSeries.coeff_coe, if_pos hm]

/-- PROVED. `NLSM_N` as a power-series coefficient (`N ≥ 2`). -/
theorem NLSM_eq_ps {N : ℕ} (hN : 2 ≤ N) (X : ℕ × ℕ → K) :
    NLSM N X = PowerSeries.coeff (N - 2) (∑ T ∈ triangulations N, ∏ d ∈ T, phi X d) := by
  rw [NLSM, show ((N : ℤ) - 2) = ((N - 2 : ℕ) : ℤ) by omega, shiftCoeff_eq_ps]

end NLSMdef

/-! ## 2. Structural statements on the NLSM side (Z26 Lemmas 4.1–4.3; PROOFS Lemmas B.3, B.4) -/

section NLSMside

variable {K : Type*} [Field K]

lemma pkI_vtx {N x : ℕ} (h1 : 1 ≤ x) (h2 : x ≤ 2 * N) : vtx N x = if x ≤ N then x else x - N := by
  split_ifs with h
  · exact vtx_of_mem h1 h
  · exact vtx_of_gt (by omega) h2

/-- On a pair of labels at cyclic distance `1 … N − 1`, the planar variable of `v₀` is `shiftSign` of the raw labels. -/
lemma pkI_planar_sign {N u v : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (hu : 1 ≤ u) (huv : u < v)
    (hvu : v ≤ u + N - 1) (hv : v ≤ 2 * N) :
    planar N (fun d => (shiftSign d : K)) u v = (shiftSign (u, v) : K) := by
  unfold planar
  rw [pkI_vtx hu (by omega), pkI_vtx (by omega) hv]
  by_cases h1 : u ≤ N <;> by_cases h2 : v ≤ N <;> simp only [h1, h2, if_true, if_false, mem_diagonals] <;>
    simp only [min_def, max_def] <;> unfold shiftSign <;> split_ifs <;> first | omega | norm_num

lemma pkI_planar_add (N : ℕ) (X : ℕ × ℕ → K) (a b : ℕ) : planar N X (a + N) (b + N) = planar N X a b := by
  unfold planar
  rw [vtx_add_n, vtx_add_n]

lemma pkI_mesh_add (N : ℕ) (X : ℕ × ℕ → K) (a b : ℕ) : mesh N X (a + N) (b + N) = mesh N X a b := by
  unfold mesh
  rw [show a + N + 1 = (a + 1) + N by omega, show b + N + 1 = (b + 1) + N by omega, pkI_planar_add,
    pkI_planar_add, pkI_planar_add, pkI_planar_add]

lemma pkI_mesh_core {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {i j : ℕ} (hi : 1 ≤ i) (hiN : i ≤ N) (hj : i + 2 ≤ j)
    (hj' : j ≤ i + N - 2) : mesh N (fun d => (shiftSign d : K)) i j = 0 := by
  unfold mesh
  rw [pkI_planar_sign hN hE hi (by omega) (by omega) (by omega),
    pkI_planar_sign hN hE (by omega) (by omega) (by omega) (by omega),
    pkI_planar_sign hN hE hi (by omega) (by omega) (by omega),
    pkI_planar_sign hN hE (by omega) (by omega) (by omega) (by omega)]
  unfold shiftSign
  split_ifs <;> first | omega | norm_num

/-- `sorry` (3c-b). `v₀` preserves every tile of a row: `c_{ij}(v₀) = 0` for `j` non-adjacent to `i` (N even;
Z26 Lemma 3.2). [mirror: `mesh(v₀) = 0` on all non-adjacent pairs, N = 4…12, E2 extra] -/
theorem mesh_shiftSign {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {i j : ℕ} (hi : 1 ≤ i) (hj : i + 2 ≤ j)
    (hj' : j ≤ i + N - 2) : mesh N (fun d => (shiftSign d : K)) i j = 0 := by
  have key : ∀ n : ℕ, ∀ i j : ℕ, i ≤ n → 1 ≤ i → i + 2 ≤ j → j ≤ i + N - 2 →
      mesh N (fun d => (shiftSign d : K)) i j = 0 := by
    intro n
    induction n with
    | zero => intro i j h1 h2; omega
    | succ n ih =>
      intro i j h1 h2 h3 h4
      by_cases hiN : i ≤ N
      · exact pkI_mesh_core hN hE h2 hiN h3 h4
      · rw [show i = (i - N) + N by omega, show j = (j - N) + N by omega, pkI_mesh_add]
        exact ih (i - N) (j - N) (by omega) (by omega) (by omega) (by omega)
  exact key i i j le_rfl hi hj hj'

lemma pkI_shifted_ne {X : ℕ × ℕ → K} {d : ℕ × ℕ} (h : shiftSign d = 0 → X d ≠ 0) : shifted X d ≠ 0 := by
  intro h0
  have h1 : HahnSeries.ofPowerSeries ℤ K (phi X d) = 0 := by rw [← inv_shifted, h0, inv_zero]
  have h2 : phi X d = 0 := HahnSeries.ofPowerSeries_injective (by rw [h1, map_zero])
  by_cases hs : shiftSign d = 0
  · unfold phi at h2
    rw [if_pos hs] at h2
    have h3 := congrArg (PowerSeries.coeff 0) h2
    rw [PowerSeries.coeff_zero_C, map_zero, inv_eq_zero] at h3
    exact h hs h3
  · unfold phi at h2
    rw [if_neg hs] at h2
    have h3 := congrArg (PowerSeries.coeff 1) h2
    unfold shiftSeries at h3
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, map_zero] at h3
    have h4 := sign_sq (K := K) hs
    simp at h3
    rw [h3, zero_mul] at h4
    exact zero_ne_one h4

lemma pkI_planar_shifted (N : ℕ) (X : ℕ × ℕ → K) (u v : ℕ) :
    planar N (shifted X) u v =
      HahnSeries.C (planar N X u v) + planar N (fun d => ((shiftSign d : ℤ) : LaurentSeries K)) u v * delta := by
  unfold planar shifted
  split_ifs <;> simp

lemma pkI_mesh_shifted (N : ℕ) (X : ℕ × ℕ → K) (u v : ℕ) :
    mesh N (shifted X) u v =
      HahnSeries.C (mesh N X u v) + mesh N (fun d => ((shiftSign d : ℤ) : LaurentSeries K)) u v * delta := by
  unfold mesh
  rw [pkI_planar_shifted, pkI_planar_shifted, pkI_planar_shifted, pkI_planar_shifted, map_sub, map_sub, map_add]
  ring

/-- `sorry` (3c-b). **Row zero at every δ-order (Z26 Lemma 4.3, PROOFS Lemma B.4)**, from Phase 1's pointwise
theorem applied over the field `K⸨e⸩` (row loci are δ-invariant by `mesh_shiftSign`). -/
theorem shiftCoeff_row_zero {N i : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (hi : 1 ≤ i ∧ i ≤ N) (X : ℕ × ℕ → K)
    (hX : ∀ d ∈ oddDiagonals N, X d ≠ 0) (hR : OnRect N 1 i X) (m : ℤ) : shiftCoeff N m X = 0 := by
  have hne : ∀ d ∈ diagonals N, shifted X d ≠ 0 := by
    intro d hd
    refine pkI_shifted_ne fun hs => hX d (mem_filter.2 ⟨hd, ?_⟩)
    have h1 := mem_diagonals.1 hd
    unfold shiftSign at hs
    rcases Nat.mod_two_eq_zero_or_one d.1 with a | a <;> rcases Nat.mod_two_eq_zero_or_one d.2 with b | b <;>
      simp [a, b] at hs <;> omega
  have hR' : OnRect N 1 i (shifted X) := by
    intro a ha b hb
    rw [pkI_mesh_shifted, hR a ha b hb, mesh_shiftSign hN hE (by simp only [mem_Ico] at ha; omega)
      (by simp only [mem_Ico, mem_Icc] at ha hb; omega) (by simp only [mem_Ico, mem_Icc] at ha hb; omega)]
    simp
  have h0 := amp_eq_zero_of_onRect (le_refl 1) (by omega) hi.1 hi.2 (shifted X) hne hR'
  unfold shiftCoeff
  rw [h0]
  rfl

/-- ASSEMBLED. NLSM's row zero. -/
theorem NLSM_row_zero {N i : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (hi : 1 ≤ i ∧ i ≤ N) (X : ℕ × ℕ → K)
    (hX : ∀ d ∈ oddDiagonals N, X d ≠ 0) (hR : OnRect N 1 i X) : NLSM N X = 0 :=
  shiftCoeff_row_zero hN hE hi X hX hR _

/-- The two children of an odd chord `C` of an even `N`-gon are even polygons with at least four vertices, and their
orders `L − 2`, `R − 2` add up to `N − 2`. -/
lemma pkZ_child {N : ℕ} (hE : N % 2 = 0) {C : ℕ × ℕ} (hC : C ∈ oddDiagonals N) :
    4 ≤ C.2 - C.1 + 1 ∧ (C.2 - C.1 + 1) % 2 = 0 ∧ C.2 - C.1 + 1 < N ∧
      4 ≤ N - C.2 + C.1 + 1 ∧ (N - C.2 + C.1 + 1) % 2 = 0 ∧ N - C.2 + C.1 + 1 < N ∧
      (C.2 - C.1 + 1 - 2) + (N - C.2 + C.1 + 1 - 2) = N - 2 := by
  have h1 := mem_filter.1 hC
  have h2 := mem_diagonals.1 h1.1
  have h3 := h1.2
  omega

lemma pkZ_prod_ne (s : Finset (ℕ × ℕ)) : (∏ C ∈ s, (MvPolynomial.X C : MvPolynomial (ℕ × ℕ) ℤ)) ≠ 0 :=
  prod_ne_zero_iff.2 fun c _ => MvPolynomial.X_ne_zero c

lemma pkZ_prod_deg (s : Finset (ℕ × ℕ)) :
    (∏ C ∈ s, (MvPolynomial.X C : MvPolynomial (ℕ × ℕ) ℤ)).totalDegree = s.card := by
  have h := MvPolynomial.IsHomogeneous.prod s (fun d => (MvPolynomial.X d : MvPolynomial (ℕ × ℕ) ℤ)) (fun _ => 1)
    (fun d _ => MvPolynomial.isHomogeneous_X ℤ d)
  rw [sum_const, smul_eq_mul, mul_one] at h
  exact h.totalDegree (pkZ_prod_ne s)

/-- `shiftSeries` with a polynomial variable. -/
noncomputable def pkZ_sP (R : Type*) [CommRing R] (d : ℕ × ℕ) : PowerSeries (MvPolynomial (ℕ × ℕ) R) :=
  PowerSeries.X * PowerSeries.mk (fun k => ((shiftSign d : ℤ) : MvPolynomial (ℕ × ℕ) R) ^ (k + 1) * (-MvPolynomial.X d) ^ k)

/-- Numerator of the order-`m` coefficient: `shiftCoeff N m · oddDen = pkZ_AP N m` (`pkZ_APeval`). -/
noncomputable def pkZ_AP (R : Type*) [CommRing R] (N m : ℕ) : MvPolynomial (ℕ × ℕ) R :=
  PowerSeries.coeff m (∑ T ∈ triangulations N,
    PowerSeries.C (∏ d ∈ oddDiagonals N \ T, MvPolynomial.X d) *
      ∏ d ∈ T.filter (fun d => shiftSign d ≠ 0), pkZ_sP R d)

/-- Set the variable `C` to `0` (the residue operation on numerators). -/
noncomputable def pkZ_zeroAt (R : Type*) [CommRing R] (C : ℕ × ℕ) : MvPolynomial (ℕ × ℕ) R →ₐ[R] MvPolynomial (ℕ × ℕ) R :=
  MvPolynomial.aeval (fun d => if d = C then 0 else MvPolynomial.X d)

/-- Child-to-parent relabelling: child vertex `a` ↦ parent vertex `a + b − 1` read mod `N` (PROOFS Lemma B.2: `P_L`
has `b = i`, `P_R` has `b = j`). -/
def pkZ_relab (N b : ℕ) (d : ℕ × ℕ) : ℕ × ℕ := npair N (d.1 + b - 1) (d.2 + b - 1)

/-- The odd diagonals crossing `C` (in neither sub-polygon). -/
noncomputable def pkZ_cross (R : Type*) [CommRing R] (N : ℕ) (C : ℕ × ℕ) : MvPolynomial (ℕ × ℕ) R :=
  ∏ d ∈ (oddDiagonals N).filter (fun d => Crosses d C), MvPolynomial.X d

lemma pkZ_i_map_mk {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (g : ℕ → A) :
    PowerSeries.map f (PowerSeries.mk g) = PowerSeries.mk (fun k => f (g k)) := by
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk]

lemma pkZ_i_evalShift {K : Type*} [Field K] (X : ℕ × ℕ → K) (d : ℕ × ℕ) :
    PowerSeries.map (MvPolynomial.eval X) (pkZ_sP K d) = shiftSeries (shiftSign d) (X d) := by
  rw [pkZ_sP, shiftSeries, map_mul, PowerSeries.map_X, pkZ_i_map_mk]
  simp

lemma pkZ_i_mapShiftP {R : Type*} [CommRing R] {S : Type*} [CommRing S] (f : R →+* S) (d : ℕ × ℕ) :
    PowerSeries.map (MvPolynomial.map f) (pkZ_sP R d) = pkZ_sP S d := by
  rw [pkZ_sP, pkZ_sP, map_mul, PowerSeries.map_X, pkZ_i_map_mk]
  simp

lemma pkZ_i_odd_sign {N : ℕ} {d : ℕ × ℕ} (hd : d ∈ oddDiagonals N) : shiftSign d = 0 := by
  have h1 := mem_filter.1 hd
  have h2 := mem_diagonals.1 h1.1
  have h3 := h1.2
  unfold shiftSign
  rcases Nat.mod_two_eq_zero_or_one d.1 with a | a <;> rcases Nat.mod_two_eq_zero_or_one d.2 with b | b <;>
    simp [a, b] <;> omega

lemma pkZ_i_sign_zero {N : ℕ} {d : ℕ × ℕ} (hd : d ∈ diagonals N) (hs : shiftSign d = 0) : d ∈ oddDiagonals N := by
  refine mem_filter.2 ⟨hd, ?_⟩
  have h1 := mem_diagonals.1 hd
  unfold shiftSign at hs
  rcases Nat.mod_two_eq_zero_or_one d.1 with a | a <;> rcases Nat.mod_two_eq_zero_or_one d.2 with b | b <;>
    simp [a, b] at hs <;> omega

lemma pkZ_i_ring_aux {A : Type*} [CommRing A] (a p i z : A) (h : i * z = 1) : a * p = (i * p) * (a * z) := by
  calc a * p = a * p * (i * z) := by rw [h, mul_one]
    _ = _ := by ring

/-- pkgAz copy: Numerator lemma for the δ-coefficients. -/
theorem pkZ_APeval {K : Type*} [Field K] (N m : ℕ) (X : ℕ × ℕ → K) (hX : ∀ d ∈ oddDiagonals N, X d ≠ 0) :
    MvPolynomial.eval X (pkZ_AP K N m) = shiftCoeff N m X * ∏ d ∈ oddDiagonals N, X d := by
  have hT : ∀ T ∈ triangulations N, PowerSeries.C (∏ d ∈ oddDiagonals N \ T, X d) *
        ∏ d ∈ T.filter (fun d => shiftSign d ≠ 0), shiftSeries (shiftSign d) (X d) =
      (∏ d ∈ T, phi X d) * PowerSeries.C (∏ d ∈ oddDiagonals N, X d) := by
    intro T hT
    have hTd : T ⊆ diagonals N := (mem_triangulations.1 hT).1
    have hsub : T.filter (fun d => shiftSign d = 0) ⊆ oddDiagonals N := fun d hd =>
      pkZ_i_sign_zero (hTd (mem_filter.1 hd).1) (mem_filter.1 hd).2
    have hsd : oddDiagonals N \ T = oddDiagonals N \ T.filter (fun d => shiftSign d = 0) := by
      ext d
      simp only [mem_sdiff, mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun h => h2 h.1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun h => h2 ⟨h, pkZ_i_odd_sign h1⟩⟩
    have h0 : ∏ d ∈ T.filter (fun d => shiftSign d = 0), phi X d =
        PowerSeries.C (∏ d ∈ T.filter (fun d => shiftSign d = 0), (X d)⁻¹) := by
      rw [map_prod]
      exact prod_congr rfl fun d hd => by unfold phi; rw [if_pos (mem_filter.1 hd).2]
    have h1 : ∏ d ∈ T.filter (fun d => ¬ shiftSign d = 0), phi X d =
        ∏ d ∈ T.filter (fun d => shiftSign d ≠ 0), shiftSeries (shiftSign d) (X d) :=
      prod_congr rfl fun d hd => by unfold phi; rw [if_neg (mem_filter.1 hd).2]
    have hinv : (∏ d ∈ T.filter (fun d => shiftSign d = 0), (X d)⁻¹) *
        ∏ d ∈ T.filter (fun d => shiftSign d = 0), X d = 1 := by
      rw [← prod_mul_distrib]
      exact prod_eq_one fun d hd => inv_mul_cancel₀ (hX d (hsub hd))
    rw [← prod_sdiff hsub, ← hsd, ← prod_filter_mul_prod_filter_not T (fun d => shiftSign d = 0), h0, h1]
    have hc : PowerSeries.C ((∏ d ∈ oddDiagonals N \ T, X d) * ∏ d ∈ T.filter (fun d => shiftSign d = 0), X d) =
        PowerSeries.C (∏ d ∈ oddDiagonals N \ T, X d) *
          PowerSeries.C (∏ d ∈ T.filter (fun d => shiftSign d = 0), X d) := map_mul _ _ _
    rw [hc]
    exact pkZ_i_ring_aux _ _ _ _ (by rw [← map_mul, hinv, map_one])
  rw [pkZ_AP, ← PowerSeries.coeff_map (MvPolynomial.eval X), map_sum, shiftCoeff_eq_ps, ← PowerSeries.coeff_mul_C, sum_mul]
  refine congrArg _ (sum_congr rfl fun T hT' => ?_)
  have e1 : PowerSeries.map (MvPolynomial.eval X) (PowerSeries.C (∏ d ∈ oddDiagonals N \ T, (MvPolynomial.X d : MvPolynomial (ℕ × ℕ) K))) =
      PowerSeries.C (∏ d ∈ oddDiagonals N \ T, X d) := by
    rw [PowerSeries.map_C, map_prod]
    simp only [MvPolynomial.eval_X]
  have e2 : PowerSeries.map (MvPolynomial.eval X) (∏ d ∈ T.filter (fun d => shiftSign d ≠ 0), pkZ_sP K d) =
      ∏ d ∈ T.filter (fun d => shiftSign d ≠ 0), shiftSeries (shiftSign d) (X d) := by
    rw [map_prod]
    exact prod_congr rfl fun d _ => pkZ_i_evalShift X d
  rw [map_mul, e1, e2, hT T hT']

theorem pkZ_APmap {R : Type*} [CommRing R] {S : Type*} [CommRing S] (f : R →+* S) (N m : ℕ) : MvPolynomial.map f (pkZ_AP R N m) = pkZ_AP S N m := by
  rw [pkZ_AP, pkZ_AP, ← PowerSeries.coeff_map (MvPolynomial.map f), map_sum]
  refine congrArg _ (sum_congr rfl fun T _ => ?_)
  simp only [map_mul, map_prod, PowerSeries.map_C, MvPolynomial.map_X, pkZ_i_mapShiftP]

lemma pkZ_d_sign_zero {N : ℕ} {d : ℕ × ℕ} (hd : d ∈ diagonals N) (hs : shiftSign d = 0) : d ∈ oddDiagonals N := by
  refine mem_filter.2 ⟨hd, ?_⟩
  have h1 := mem_diagonals.1 hd
  unfold shiftSign at hs
  rcases Nat.mod_two_eq_zero_or_one d.1 with a | a <;> rcases Nat.mod_two_eq_zero_or_one d.2 with b | b <;>
    simp [a, b] at hs <;> omega

lemma pkZ_d_sign_ne {N : ℕ} {d : ℕ × ℕ} (hd : d ∈ oddDiagonals N) : ¬ shiftSign d ≠ 0 := by
  have h1 := mem_diagonals.1 (mem_filter.1 hd).1
  have h2 := (mem_filter.1 hd).2
  unfold shiftSign
  rcases Nat.mod_two_eq_zero_or_one d.1 with a | a <;> rcases Nat.mod_two_eq_zero_or_one d.2 with b | b <;>
    simp [a, b] <;> omega

lemma pkZ_d_card_glue {a b k : ℕ} {T1 T2 : Finset (ℕ × ℕ)} (hak : a < k) (hkb : k < b)
    (h1 : T1 ⊆ sdiag a k) (h2 : T2 ⊆ sdiag k b) :
    (glue a b k T1 T2).card =
      T1.card + T2.card + (if a + 1 < k then 1 else 0) + (if k + 1 < b then 1 else 0) := by
  have hA : ∀ d ∈ (if a + 1 < k then {(a, k)} else ∅ : Finset (ℕ × ℕ)), d = (a, k) := by
    intro d hd; split_ifs at hd <;> simp only [mem_singleton, notMem_empty] at hd <;> exact hd
  have hB : ∀ d ∈ (if k + 1 < b then {(k, b)} else ∅ : Finset (ℕ × ℕ)), d = (k, b) := by
    intro d hd; split_ifs at hd <;> simp only [mem_singleton, notMem_empty] at hd <;> exact hd
  have d12 : Disjoint T1 T2 := by
    rw [disjoint_left]
    intro d hd1 hd2
    have := mem_sdiag.1 (h1 hd1); have := mem_sdiag.1 (h2 hd2); omega
  have dAB : Disjoint (if a + 1 < k then {(a, k)} else ∅ : Finset (ℕ × ℕ))
      (if k + 1 < b then {(k, b)} else ∅) := by
    rw [disjoint_left]
    intro d hd1 hd2
    have e1 := hA d hd1; have e2 := hB d hd2
    rw [e1] at e2; simp only [Prod.mk.injEq] at e2; omega
  have dTAB : Disjoint (T1 ∪ T2) ((if a + 1 < k then {(a, k)} else ∅ : Finset (ℕ × ℕ)) ∪
      (if k + 1 < b then {(k, b)} else ∅)) := by
    rw [disjoint_left]
    intro d hd hd'
    rw [mem_union] at hd hd'
    rcases hd' with hd' | hd'
    · have e := hA d hd'; subst e
      rcases hd with hd | hd
      · have := mem_sdiag.1 (h1 hd); dsimp only at this; omega
      · have := mem_sdiag.1 (h2 hd); dsimp only at this; omega
    · have e := hB d hd'; subst e
      rcases hd with hd | hd
      · have := mem_sdiag.1 (h1 hd); dsimp only at this; omega
      · have := mem_sdiag.1 (h2 hd); dsimp only at this; omega
  show (T1 ∪ T2 ∪ ((if a + 1 < k then {(a, k)} else ∅) ∪ (if k + 1 < b then {(k, b)} else ∅))).card = _
  rw [card_union_of_disjoint dTAB, card_union_of_disjoint d12, card_union_of_disjoint dAB]
  split_ifs <;> simp only [card_singleton, card_empty] <;> omega

lemma pkZ_d_card_tri : ∀ n a b : ℕ, b - a ≤ n → a < b → ∀ T : Finset (ℕ × ℕ), IsTri a b T →
    T.card = b - a - 2 := by
  intro n
  induction n with
  | zero => intro a b h1 h2; omega
  | succ n ih =>
    intro a b h1 h2 T hT
    by_cases hab : a + 1 < b
    · obtain ⟨k, hak, hkb, hA, hB⟩ := exists_apex hab hT
      have e := glue_split hT hak hkb hA hB
      have hL := left_isTri hT hak hkb hA hB
      have hR := right_isTri hT hak hkb hA hB
      have c1 := ih a k (by omega) hak _ hL
      have c2 := ih k b (by omega) hkb _ hR
      rw [← e, pkZ_d_card_glue hak hkb hL.1 hR.1, c1, c2]
      split_ifs <;> omega
    · have hs : T = ∅ := by
        refine eq_empty_of_forall_notMem fun d hd => ?_
        have := mem_sdiag.1 (hT.1 hd)
        omega
      rw [hs, card_empty]
      omega

lemma pkZ_d_prodX {R : Type*} [CommRing R] (s : Finset (ℕ × ℕ)) :
    (Finset.prod s (fun d => (MvPolynomial.X d : MvPolynomial (ℕ × ℕ) R))).IsHomogeneous s.card := by
  have h := MvPolynomial.IsHomogeneous.prod s (fun d => (MvPolynomial.X d : MvPolynomial (ℕ × ℕ) R)) (fun _ => 1)
    (fun d _ => MvPolynomial.isHomogeneous_X R d)
  rwa [sum_const, smul_eq_mul, mul_one] at h

lemma pkZ_d_mul {R : Type*} [CommRing R] {f g : PowerSeries (MvPolynomial (ℕ × ℕ) R)} {r s : ℕ}
    (hf : ∀ k, (PowerSeries.coeff k f).IsHomogeneous (k - r) ∧ (k < r → PowerSeries.coeff k f = 0))
    (hg : ∀ k, (PowerSeries.coeff k g).IsHomogeneous (k - s) ∧ (k < s → PowerSeries.coeff k g = 0)) (k : ℕ) :
    (PowerSeries.coeff k (f * g)).IsHomogeneous (k - (r + s)) ∧
      (k < r + s → PowerSeries.coeff k (f * g) = 0) := by
  rw [PowerSeries.coeff_mul]
  constructor
  · refine MvPolynomial.IsHomogeneous.sum _ _ _ fun p hp => ?_
    have hk := mem_antidiagonal.1 hp
    by_cases h1 : p.1 < r
    · rw [(hf p.1).2 h1, zero_mul]; exact MvPolynomial.isHomogeneous_zero _ _ _
    by_cases h2 : p.2 < s
    · rw [(hg p.2).2 h2, mul_zero]; exact MvPolynomial.isHomogeneous_zero _ _ _
    have h := (hf p.1).1.mul (hg p.2).1
    rwa [show p.1 - r + (p.2 - s) = k - (r + s) by omega] at h
  · intro hk
    refine sum_eq_zero fun p hp => ?_
    have hk' := mem_antidiagonal.1 hp
    by_cases h1 : p.1 < r
    · rw [(hf p.1).2 h1, zero_mul]
    · rw [(hg p.2).2 (by omega), mul_zero]

lemma pkZ_d_prod {R : Type*} [CommRing R] (s : Finset (ℕ × ℕ)) (f : ℕ × ℕ → PowerSeries (MvPolynomial (ℕ × ℕ) R))
    (hf : ∀ d ∈ s, ∀ k, (PowerSeries.coeff k (f d)).IsHomogeneous (k - 1) ∧
      (k < 1 → PowerSeries.coeff k (f d) = 0)) :
    ∀ k, (PowerSeries.coeff k (Finset.prod s f)).IsHomogeneous (k - s.card) ∧
      (k < s.card → PowerSeries.coeff k (Finset.prod s f) = 0) := by
  induction s using Finset.induction_on with
  | empty =>
    intro k
    rw [prod_empty, card_empty, PowerSeries.coeff_one]
    refine ⟨?_, fun h => absurd h (Nat.not_lt_zero _)⟩
    split_ifs with h
    · subst h; exact MvPolynomial.isHomogeneous_one _ _
    · exact MvPolynomial.isHomogeneous_zero _ _ _
  | insert a s ha ih =>
    intro k
    rw [prod_insert ha, card_insert_of_notMem ha]
    have h := pkZ_d_mul (hf a (mem_insert_self a s)) (ih fun d hd => hf d (mem_insert_of_mem hd)) k
    rwa [show 1 + s.card = s.card + 1 by omega] at h

lemma pkZ_d_shift {R : Type*} [CommRing R] (d : ℕ × ℕ) (k : ℕ) :
    (PowerSeries.coeff k (pkZ_sP R d)).IsHomogeneous (k - 1) ∧
      (k < 1 → PowerSeries.coeff k (pkZ_sP R d) = 0) := by
  have e : pkZ_sP R d = PowerSeries.X * PowerSeries.mk
      (fun k => ((shiftSign d : ℤ) : MvPolynomial (ℕ × ℕ) R) ^ (k + 1) * (-MvPolynomial.X d) ^ k) := rfl
  rw [e]
  rcases k with _ | k
  · rw [PowerSeries.coeff_zero_X_mul]; exact ⟨MvPolynomial.isHomogeneous_zero _ _ _, fun _ => rfl⟩
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]
    refine ⟨?_, fun h => absurd h (by omega)⟩
    have h1 : (((shiftSign d : ℤ) : MvPolynomial (ℕ × ℕ) R) ^ (k + 1)).IsHomogeneous (0 * (k + 1)) := by
      rw [← map_intCast (MvPolynomial.C : R →+* MvPolynomial (ℕ × ℕ) R)]
      exact (MvPolynomial.isHomogeneous_C _ _).pow _
    have h2 := h1.mul ((MvPolynomial.isHomogeneous_X R d).neg.pow k)
    rwa [show 0 * (k + 1) + 1 * k = k + 1 - 1 by omega] at h2

/-- pkgAz copy: Z26 Lemma 4.1 (degree): `pkZ_AP N m` is homogeneous of degree `#odd + m − (N − 3)`. [mirror D4] -/
theorem pkZ_APhom {R : Type*} [CommRing R] {N : ℕ} (hN : 4 ≤ N) (m : ℕ) (hm : N - 3 ≤ (oddDiagonals N).card + m) :
    (pkZ_AP R N m).IsHomogeneous ((oddDiagonals N).card + m - (N - 3)) := by
  show (PowerSeries.coeff m (Finset.sum (triangulations N) (fun T =>
    PowerSeries.C (Finset.prod (oddDiagonals N \ T) (fun d => MvPolynomial.X d)) *
      Finset.prod (T.filter (fun d => shiftSign d ≠ 0)) (fun d => pkZ_sP R d)))).IsHomogeneous _
  rw [map_sum]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun T hT => ?_
  rw [PowerSeries.coeff_C_mul]
  have hTd : T ⊆ diagonals N := (mem_triangulations.1 hT).1
  have hcard : T.card = N - 3 := by
    have h := pkZ_d_card_tri N 1 N (by omega) (by omega) T
      (mem_tri.1 (by rw [← triangulations_eq_tri]; exact hT))
    omega
  have hsplit : (T.filter (fun d => shiftSign d ≠ 0)).card + (T.filter (fun d => ¬ shiftSign d ≠ 0)).card =
      T.card := card_filter_add_card_filter_not _
  have heq : T.filter (fun d => ¬ shiftSign d ≠ 0) = T ∩ oddDiagonals N := by
    ext d
    rw [mem_filter, mem_inter]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, pkZ_d_sign_zero (hTd h1) (not_not.1 h2)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, pkZ_d_sign_ne h2⟩
  have hsd : (oddDiagonals N \ T).card = (oddDiagonals N).card - (T ∩ oddDiagonals N).card := card_sdiff
  have hle : (T ∩ oddDiagonals N).card ≤ (oddDiagonals N).card := card_le_card inter_subset_right
  rw [heq] at hsplit
  have hP := pkZ_d_prod (T.filter (fun d => shiftSign d ≠ 0)) (fun d => pkZ_sP R d)
    (fun d _ k => pkZ_d_shift d k) m
  by_cases hr : m < (T.filter (fun d => shiftSign d ≠ 0)).card
  · rw [hP.2 hr, mul_zero]
    exact MvPolynomial.isHomogeneous_zero _ _ _
  · have h := (pkZ_d_prodX (oddDiagonals N \ T)).mul hP.1
    rwa [show (oddDiagonals N \ T).card + (m - (T.filter (fun d => shiftSign d ≠ 0)).card) =
      (oddDiagonals N).card + m - (N - 3) by omega] at h

/-- pkgAz copy: Orders below `#shifted` vanish identically (each shifted diagonal contributes `e^{≥1}`). -/
theorem pkZ_APsmall {R : Type*} [CommRing R] {N : ℕ} (hN : 4 ≤ N) (m : ℕ) (hm : (oddDiagonals N).card + m < N - 3) :
    pkZ_AP R N m = 0 := by
  rw [pkZ_AP, map_sum]
  refine sum_eq_zero fun T hT => ?_
  have hTd : T ⊆ diagonals N := (mem_triangulations.1 hT).1
  have hcard : T.card = N - 3 := by
    have h := pkZ_d_card_tri N 1 N (by omega) (by omega) T
      (mem_tri.1 (by rw [← triangulations_eq_tri]; exact hT))
    omega
  have hsub : T.filter (fun d => ¬ shiftSign d ≠ 0) ⊆ oddDiagonals N := fun d hd =>
    pkZ_i_sign_zero (hTd (mem_filter.1 hd).1) (not_not.1 (mem_filter.1 hd).2)
  have hsplit : (T.filter (fun d => shiftSign d ≠ 0)).card + (T.filter (fun d => ¬ shiftSign d ≠ 0)).card =
      T.card := card_filter_add_card_filter_not _
  have hle := card_le_card hsub
  have hprod : ∏ d ∈ T.filter (fun d => shiftSign d ≠ 0), pkZ_sP R d =
      PowerSeries.X ^ (T.filter (fun d => shiftSign d ≠ 0)).card *
        ∏ d ∈ T.filter (fun d => shiftSign d ≠ 0),
          PowerSeries.mk (fun k => ((shiftSign d : ℤ) : MvPolynomial (ℕ × ℕ) R) ^ (k + 1) * (-MvPolynomial.X d) ^ k) := by
    rw [← prod_const, ← prod_mul_distrib]
    rfl
  rw [hprod, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_neg (by omega), mul_zero]

lemma pkZ_i_zeroAt_X {R : Type*} [CommRing R] (c d : ℕ × ℕ) : pkZ_zeroAt R c (MvPolynomial.X d) = if d = c then 0 else MvPolynomial.X d := by
  rw [pkZ_zeroAt, MvPolynomial.aeval_X]

lemma pkZ_i_sub_zeroAt {R : Type*} [CommRing R] (c : ℕ × ℕ) (P : MvPolynomial (ℕ × ℕ) R) : MvPolynomial.X c ∣ P - pkZ_zeroAt R c P := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [pkZ_zeroAt, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, sub_self]
    exact dvd_zero _
  | add p q hp hq =>
    rw [map_add, add_sub_add_comm]
    exact dvd_add hp hq
  | mul_X p n hp =>
    rw [map_mul, pkZ_i_zeroAt_X]
    split_ifs with h
    · rw [mul_zero, sub_zero, h]
      exact dvd_mul_left _ _
    · rw [← sub_mul]
      exact dvd_mul_of_dvd_left hp _

/-- pkgAz copy: **Z26 Lemma 3.1, numerator form**: a polynomial with `pkZ_zeroAt C P = 0` for every `C ∈ S` is
divisible by `∏_{C∈S} X_C` (distinct variables are pairwise non-associated primes). -/
theorem pkZ_dvd {R : Type*} [CommRing R] [IsDomain R] (S : Finset (ℕ × ℕ)) (P : MvPolynomial (ℕ × ℕ) R)
    (h : ∀ C ∈ S, pkZ_zeroAt R C P = 0) : (∏ C ∈ S, MvPolynomial.X C) ∣ P := by
  induction S using Finset.induction_on generalizing P with
  | empty =>
    rw [prod_empty]
    exact one_dvd _
  | insert a s ha ih =>
    obtain ⟨Q, hQ⟩ := ih P (fun c hc => h c (mem_insert_of_mem hc))
    have hz : pkZ_zeroAt R a Q = 0 := by
      have h1 := h a (mem_insert_self a s)
      rw [hQ, map_mul, map_prod] at h1
      have h2 : ∏ c ∈ s, pkZ_zeroAt R a (MvPolynomial.X c) = ∏ c ∈ s, MvPolynomial.X c := prod_congr rfl fun c hc => by
        rw [pkZ_i_zeroAt_X, if_neg (fun e : c = a => ha (e ▸ hc))]
      rw [h2] at h1
      exact (mul_eq_zero.1 h1).resolve_left (prod_ne_zero_iff.2 fun c _ => MvPolynomial.X_ne_zero c)
    obtain ⟨Q', hQ'⟩ : MvPolynomial.X a ∣ Q := by
      have h3 := pkZ_i_sub_zeroAt a Q
      rwa [hz, sub_zero] at h3
    rw [prod_insert ha, hQ, hQ']
    exact ⟨Q', by ring⟩

lemma pkZ_s_vtx {N x : ℕ} (h1 : 1 ≤ x) (h2 : x ≤ 2 * N) : vtx N x = if x ≤ N then x else x - N := by
  split_ifs with h
  · exact vtx_of_mem h1 h
  · exact vtx_of_gt (by omega) h2

/-- `pkZ_relab` in coordinates: no wrap, one endpoint wraps, both wrap. -/
lemma pkZ_s_spec {N b a c x y : ℕ} (hb : 1 ≤ b) (ha : 1 ≤ a) (hac : a < c) (hca : c < a + N)
    (hc : c + b - 1 ≤ 2 * N) (he : pkZ_relab N b (a, c) = (x, y)) :
    (c + b - 1 ≤ N ∧ x = a + b - 1 ∧ y = c + b - 1) ∨
    (a + b - 1 ≤ N ∧ N < c + b - 1 ∧ x = c + b - 1 - N ∧ y = a + b - 1) ∨
    (N < a + b - 1 ∧ x = a + b - 1 - N ∧ y = c + b - 1 - N) := by
  unfold pkZ_relab npair at he
  dsimp only at he
  by_cases h1 : c + b - 1 ≤ N
  · rw [vtx_of_mem (by omega) (by omega), vtx_of_mem (by omega) h1] at he
    simp only [Prod.mk.injEq, min_def, max_def] at he
    split_ifs at he <;> omega
  · by_cases h2 : a + b - 1 ≤ N
    · rw [vtx_of_mem (by omega) h2, vtx_of_gt (by omega) hc] at he
      simp only [Prod.mk.injEq, min_def, max_def] at he
      split_ifs at he <;> omega
    · rw [vtx_of_gt (by omega) (by omega), vtx_of_gt (by omega) hc] at he
      simp only [Prod.mk.injEq, min_def, max_def] at he
      split_ifs at he <;> omega

/-- `pkZ_s_spec` read on the components of `pkZ_relab`. -/
lemma pkZ_s_spec2 {N b a c : ℕ} (hb : 1 ≤ b) (ha : 1 ≤ a) (hac : a < c) (hca : c < a + N)
    (hc : c + b - 1 ≤ 2 * N) :
    (c + b - 1 ≤ N ∧ (pkZ_relab N b (a, c)).1 = a + b - 1 ∧ (pkZ_relab N b (a, c)).2 = c + b - 1) ∨
    (a + b - 1 ≤ N ∧ N < c + b - 1 ∧ (pkZ_relab N b (a, c)).1 = c + b - 1 - N ∧
      (pkZ_relab N b (a, c)).2 = a + b - 1) ∨
    (N < a + b - 1 ∧ (pkZ_relab N b (a, c)).1 = a + b - 1 - N ∧ (pkZ_relab N b (a, c)).2 = c + b - 1 - N) :=
  pkZ_s_spec hb ha hac hca hc rfl

/-- Diagonals of the `n`-gon whose length parity satisfies `Q` (all: `Q = True`; odd: `Q = (· = 1)`). -/
def pkZ_s_S (Q : ℕ → Prop) [DecidablePred Q] (n : ℕ) : Finset (ℕ × ℕ) :=
  (diagonals n).filter (fun d => Q ((d.2 - d.1) % 2))

lemma pkZ_s_mem_S {Q : ℕ → Prop} [DecidablePred Q] {n : ℕ} {d : ℕ × ℕ} :
    d ∈ pkZ_s_S Q n ↔ d ∈ diagonals n ∧ Q ((d.2 - d.1) % 2) := by
  unfold pkZ_s_S; rw [mem_filter]

/-- Maximal pairwise non-crossing subsets of `S` (`IsTriangulation n = pkZ_s_IsMax (diagonals n)`,
`IsQuadrangulation N = pkZ_s_IsMax (oddDiagonals N)`, both by definition). -/
def pkZ_s_IsMax (S T : Finset (ℕ × ℕ)) : Prop :=
  T ⊆ S ∧ (∀ p ∈ T, ∀ q ∈ T, ¬ Crosses p q) ∧ ∀ d ∈ S, d ∉ T → ∃ p ∈ T, Crosses p d

/-- Strictly inside the chord `(i, j)`. -/
def pkZ_s_In (i j : ℕ) (d : ℕ × ℕ) : Prop := i ≤ d.1 ∧ d.2 ≤ j ∧ ¬ (d.1 = i ∧ d.2 = j)

/-- On the other side of the chord `(i, j)`. -/
def pkZ_s_Out (i j : ℕ) (d : ℕ × ℕ) : Prop :=
  (d.2 ≤ i ∨ j ≤ d.1 ∨ (d.1 ≤ i ∧ j ≤ d.2)) ∧ ¬ (d.1 = i ∧ d.2 = j)

lemma pkZ_s_mapL {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N) (hne : ¬ (i = 1 ∧ j = N))
    {d : ℕ × ℕ} (hd : d ∈ diagonals (j - i + 1)) :
    pkZ_relab N i d ∈ diagonals N ∧ pkZ_s_In i j (pkZ_relab N i d) ∧
      ((pkZ_relab N i d).2 - (pkZ_relab N i d).1) % 2 = (d.2 - d.1) % 2 := by
  obtain ⟨a, c⟩ := d
  rw [mem_diagonals] at hd; dsimp only at hd
  have h := pkZ_s_spec2 (N := N) (b := i) (a := a) (c := c) (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [mem_diagonals]; unfold pkZ_s_In; try dsimp only
  omega

lemma pkZ_s_mapR {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N) (hne : ¬ (i = 1 ∧ j = N))
    (hE : N % 2 = 0) {d : ℕ × ℕ} (hd : d ∈ diagonals (N - j + i + 1)) :
    pkZ_relab N j d ∈ diagonals N ∧ pkZ_s_Out i j (pkZ_relab N j d) ∧
      ((pkZ_relab N j d).2 - (pkZ_relab N j d).1) % 2 = (d.2 - d.1) % 2 := by
  obtain ⟨a, c⟩ := d
  rw [mem_diagonals] at hd; dsimp only at hd
  have h := pkZ_s_spec2 (N := N) (b := j) (a := a) (c := c) (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [mem_diagonals]; unfold pkZ_s_Out; try dsimp only
  omega

lemma pkZ_s_surjL {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N)
    {d : ℕ × ℕ} (hd : d ∈ diagonals N) (hin : pkZ_s_In i j d) :
    ∃ d' ∈ diagonals (j - i + 1), pkZ_relab N i d' = d := by
  obtain ⟨c, e⟩ := d
  rw [mem_diagonals] at hd; unfold pkZ_s_In at hin; dsimp only at hd hin
  refine ⟨(c - i + 1, e - i + 1), ?_, ?_⟩
  · rw [mem_diagonals]; dsimp only; omega
  · have h := pkZ_s_spec2 (N := N) (b := i) (a := c - i + 1) (c := e - i + 1) (by omega) (by omega) (by omega)
      (by omega) (by omega)
    exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)

lemma pkZ_s_surjR {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N)
    {d : ℕ × ℕ} (hd : d ∈ diagonals N) (hout : pkZ_s_Out i j d) :
    ∃ d' ∈ diagonals (N - j + i + 1), pkZ_relab N j d' = d := by
  obtain ⟨c, e⟩ := d
  rw [mem_diagonals] at hd; unfold pkZ_s_Out at hout; dsimp only at hd hout
  by_cases h1 : j ≤ c
  · refine ⟨(c - j + 1, e - j + 1), ?_, ?_⟩
    · rw [mem_diagonals]; dsimp only; omega
    · have h := pkZ_s_spec2 (N := N) (b := j) (a := c - j + 1) (c := e - j + 1) (by omega) (by omega) (by omega)
        (by omega) (by omega)
      exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)
  · by_cases h2 : e ≤ i
    · refine ⟨(c + N - j + 1, e + N - j + 1), ?_, ?_⟩
      · rw [mem_diagonals]; dsimp only; omega
      · have h := pkZ_s_spec2 (N := N) (b := j) (a := c + N - j + 1) (c := e + N - j + 1) (by omega) (by omega) (by omega)
          (by omega) (by omega)
        exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)
    · refine ⟨(e - j + 1, c + N - j + 1), ?_, ?_⟩
      · rw [mem_diagonals]; dsimp only; omega
      · have h := pkZ_s_spec2 (N := N) (b := j) (a := e - j + 1) (c := c + N - j + 1) (by omega) (by omega) (by omega)
          (by omega) (by omega)
        exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)

/-- Injectivity and crossing, for any relabelling `b ≥ 1` of the diagonals of an `n`-gon with `n + b − 1 ≤ 2N`. -/
lemma pkZ_s_inj {N b n : ℕ} (hb : 1 ≤ b) (hn : n + b - 1 ≤ 2 * N) (hnN : n ≤ N) {d d' : ℕ × ℕ} (hd : d ∈ diagonals n)
    (hd' : d' ∈ diagonals n) (h : pkZ_relab N b d = pkZ_relab N b d') : d = d' := by
  obtain ⟨a, c⟩ := d
  obtain ⟨a', c'⟩ := d'
  rw [mem_diagonals] at hd hd'; dsimp only at hd hd'
  have h1 := pkZ_s_spec2 (N := N) (b := b) (a := a) (c := c) (by omega) (by omega) (by omega) (by omega) (by omega)
  have h2 := pkZ_s_spec2 (N := N) (b := b) (a := a') (c := c') (by omega) (by omega) (by omega) (by omega)
    (by omega)
  have e1 := congrArg Prod.fst h
  have e2 := congrArg Prod.snd h
  exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)

lemma pkZ_s_cross {N b n : ℕ} (hb : 1 ≤ b) (hn : n + b - 1 ≤ 2 * N) (hnN : n ≤ N) {d d' : ℕ × ℕ}
    (hd : d ∈ diagonals n) (hd' : d' ∈ diagonals n) :
    Crosses (pkZ_relab N b d) (pkZ_relab N b d') ↔ Crosses d d' := by
  obtain ⟨a, c⟩ := d
  obtain ⟨a', c'⟩ := d'
  rw [mem_diagonals] at hd hd'; dsimp only at hd hd'
  have h1 := pkZ_s_spec2 (N := N) (b := b) (a := a) (c := c) (by omega) (by omega) (by omega) (by omega) (by omega)
  have h2 := pkZ_s_spec2 (N := N) (b := b) (a := a') (c := c') (by omega) (by omega) (by omega) (by omega)
    (by omega)
  simp only [Crosses]
  omega

lemma pkZ_s_cross_symm {p q : ℕ × ℕ} : Crosses p q ↔ Crosses q p := by
  simp only [Crosses]; omega

/-- Every diagonal is the chord, crosses it, or lies on one side. -/
lemma pkZ_s_part {N i j : ℕ} {d : ℕ × ℕ} (hd : d ∈ diagonals N) :
    d = (i, j) ∨ Crosses d (i, j) ∨ pkZ_s_In i j d ∨ pkZ_s_Out i j d := by
  obtain ⟨c, e⟩ := d
  rw [mem_diagonals] at hd
  simp only [Prod.mk.injEq, Crosses, pkZ_s_In, pkZ_s_Out]
  omega

lemma pkZ_s_In_nc {i j : ℕ} {d : ℕ × ℕ} (h : pkZ_s_In i j d) : ¬ Crosses d (i, j) := by
  unfold pkZ_s_In at h; simp only [Crosses]; omega

lemma pkZ_s_Out_nc {i j : ℕ} {d : ℕ × ℕ} (h : pkZ_s_Out i j d) : ¬ Crosses d (i, j) := by
  unfold pkZ_s_Out at h; simp only [Crosses]; omega

lemma pkZ_s_In_Out_nc {i j : ℕ} {d q : ℕ × ℕ} (hd : d.1 < d.2) (hq : q.1 < q.2) (h : pkZ_s_In i j d)
    (h' : pkZ_s_Out i j q) : ¬ Crosses d q := by
  unfold pkZ_s_In at h; unfold pkZ_s_Out at h'; simp only [Crosses]; omega

lemma pkZ_s_In_ne {i j : ℕ} {d : ℕ × ℕ} (h : pkZ_s_In i j d) : d ≠ (i, j) := by
  rintro rfl; exact h.2.2 ⟨rfl, rfl⟩

lemma pkZ_s_Out_ne {i j : ℕ} {d : ℕ × ℕ} (h : pkZ_s_Out i j d) : d ≠ (i, j) := by
  rintro rfl; exact h.2 ⟨rfl, rfl⟩

lemma pkZ_s_In_not_Out {i j : ℕ} {d : ℕ × ℕ} (hd : d.1 < d.2) (h : pkZ_s_In i j d) : ¬ pkZ_s_Out i j d := by
  unfold pkZ_s_In at h; unfold pkZ_s_Out; omega

/-- A diagonal crossing one on a side, but not the chord, lies on that side. -/
lemma pkZ_s_In_of_cross {i j : ℕ} {p d : ℕ × ℕ} (hp : p.1 < p.2) (hd : pkZ_s_In i j d) (hc : Crosses p d)
    (hpC : ¬ Crosses p (i, j)) (hne : p ≠ (i, j)) : pkZ_s_In i j p := by
  obtain ⟨c, e⟩ := p
  simp only [ne_eq, Prod.mk.injEq] at hne
  unfold pkZ_s_In at hd ⊢; simp only [Crosses] at hc hpC; dsimp only at *
  omega

lemma pkZ_s_Out_of_cross {i j : ℕ} {p d : ℕ × ℕ} (hp : p.1 < p.2) (hd : pkZ_s_Out i j d) (hc : Crosses p d)
    (hpC : ¬ Crosses p (i, j)) (hne : p ≠ (i, j)) : pkZ_s_Out i j p := by
  obtain ⟨c, e⟩ := p
  simp only [ne_eq, Prod.mk.injEq] at hne
  unfold pkZ_s_Out at hd ⊢; simp only [Crosses] at hc hpC; dsimp only at *
  omega

lemma pkZ_s_lt {n : ℕ} {d : ℕ × ℕ} (hd : d ∈ diagonals n) : d.1 < d.2 := by
  rw [mem_diagonals] at hd; omega

lemma pkZ_s_mapLQ {Q : ℕ → Prop} [DecidablePred Q] {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N)
    (hne : ¬ (i = 1 ∧ j = N)) {d : ℕ × ℕ} (hd : d ∈ pkZ_s_S Q (j - i + 1)) :
    pkZ_relab N i d ∈ pkZ_s_S Q N ∧ pkZ_s_In i j (pkZ_relab N i d) := by
  rw [pkZ_s_mem_S] at hd ⊢
  obtain ⟨h1, h2, h3⟩ := pkZ_s_mapL hi hij hjN hne hd.1
  exact ⟨⟨h1, by rw [h3]; exact hd.2⟩, h2⟩

lemma pkZ_s_mapRQ {Q : ℕ → Prop} [DecidablePred Q] {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N)
    (hne : ¬ (i = 1 ∧ j = N)) (hE : N % 2 = 0) {d : ℕ × ℕ} (hd : d ∈ pkZ_s_S Q (N - j + i + 1)) :
    pkZ_relab N j d ∈ pkZ_s_S Q N ∧ pkZ_s_Out i j (pkZ_relab N j d) := by
  rw [pkZ_s_mem_S] at hd ⊢
  obtain ⟨h1, h2, h3⟩ := pkZ_s_mapR hi hij hjN hne hE hd.1
  exact ⟨⟨h1, by rw [h3]; exact hd.2⟩, h2⟩

lemma pkZ_s_surjLQ {Q : ℕ → Prop} [DecidablePred Q] {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N)
    (hne : ¬ (i = 1 ∧ j = N)) {d : ℕ × ℕ} (hd : d ∈ pkZ_s_S Q N) (hin : pkZ_s_In i j d) :
    ∃ d' ∈ pkZ_s_S Q (j - i + 1), pkZ_relab N i d' = d := by
  rw [pkZ_s_mem_S] at hd
  obtain ⟨d', hd', rfl⟩ := pkZ_s_surjL hi hij hjN hd.1 hin
  obtain ⟨-, -, h3⟩ := pkZ_s_mapL (N := N) hi hij hjN hne hd'
  exact ⟨d', pkZ_s_mem_S.2 ⟨hd', by rw [← h3]; exact hd.2⟩, rfl⟩

lemma pkZ_s_surjRQ {Q : ℕ → Prop} [DecidablePred Q] {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N)
    (hne : ¬ (i = 1 ∧ j = N)) (hE : N % 2 = 0) {d : ℕ × ℕ} (hd : d ∈ pkZ_s_S Q N) (hout : pkZ_s_Out i j d) :
    ∃ d' ∈ pkZ_s_S Q (N - j + i + 1), pkZ_relab N j d' = d := by
  rw [pkZ_s_mem_S] at hd
  obtain ⟨d', hd', rfl⟩ := pkZ_s_surjR hi hij hjN hd.1 hout
  obtain ⟨-, -, h3⟩ := pkZ_s_mapR (N := N) hi hij hjN hne hE hd'
  exact ⟨d', pkZ_s_mem_S.2 ⟨hd', by rw [← h3]; exact hd.2⟩, rfl⟩

/-- The glued set: the chord, the left child relabelled by `pkZ_relab N i`, the right child by `pkZ_relab N j`. -/
def pkZ_s_glue (N i j : ℕ) (T1 T2 : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  insert (i, j) (T1.image (pkZ_relab N i) ∪ T2.image (pkZ_relab N j))

lemma pkZ_s_mem_glue_L {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N) (hne : ¬ (i = 1 ∧ j = N))
    (hE : N % 2 = 0) {T1 T2 : Finset (ℕ × ℕ)} (h1 : T1 ⊆ diagonals (j - i + 1))
    (h2 : T2 ⊆ diagonals (N - j + i + 1)) {d : ℕ × ℕ} (hd : d ∈ diagonals (j - i + 1)) :
    pkZ_relab N i d ∈ pkZ_s_glue N i j T1 T2 ↔ d ∈ T1 := by
  obtain ⟨hdN, hin, -⟩ := pkZ_s_mapL hi hij hjN hne hd
  rw [pkZ_s_glue, mem_insert, mem_union, mem_image, mem_image]
  constructor
  · rintro (h | ⟨d', hd', he⟩ | ⟨d', hd', he⟩)
    · exact absurd h (pkZ_s_In_ne hin)
    · rwa [← pkZ_s_inj (N := N) (b := i) (n := j - i + 1) (by omega) (by omega) (by omega) (h1 hd') hd he]
    · exfalso
      obtain ⟨-, hout, -⟩ := pkZ_s_mapR hi hij hjN hne hE (h2 hd')
      rw [he] at hout
      exact pkZ_s_In_not_Out (pkZ_s_lt hdN) hin hout
  · intro h; exact Or.inr (Or.inl ⟨d, h, rfl⟩)

lemma pkZ_s_mem_glue_R {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N) (hne : ¬ (i = 1 ∧ j = N))
    (hE : N % 2 = 0) {T1 T2 : Finset (ℕ × ℕ)} (h1 : T1 ⊆ diagonals (j - i + 1))
    (h2 : T2 ⊆ diagonals (N - j + i + 1)) {d : ℕ × ℕ} (hd : d ∈ diagonals (N - j + i + 1)) :
    pkZ_relab N j d ∈ pkZ_s_glue N i j T1 T2 ↔ d ∈ T2 := by
  obtain ⟨hdN, hout, -⟩ := pkZ_s_mapR hi hij hjN hne hE hd
  rw [pkZ_s_glue, mem_insert, mem_union, mem_image, mem_image]
  constructor
  · rintro (h | ⟨d', hd', he⟩ | ⟨d', hd', he⟩)
    · exact absurd h (pkZ_s_Out_ne hout)
    · exfalso
      obtain ⟨-, hin, -⟩ := pkZ_s_mapL hi hij hjN hne (h1 hd')
      rw [he] at hin
      exact pkZ_s_In_not_Out (pkZ_s_lt hdN) hin hout
    · rwa [← pkZ_s_inj (N := N) (b := j) (n := N - j + i + 1) (by omega) (by omega) (by omega) (h2 hd') hd he]
  · intro h; exact Or.inr (Or.inr ⟨d, h, rfl⟩)

/-- Nothing in a glued set crosses the chord. -/
lemma pkZ_s_glue_nc {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N) (hne : ¬ (i = 1 ∧ j = N))
    (hE : N % 2 = 0) {T1 T2 : Finset (ℕ × ℕ)} (h1 : T1 ⊆ diagonals (j - i + 1))
    (h2 : T2 ⊆ diagonals (N - j + i + 1)) {p : ℕ × ℕ} (hp : p ∈ pkZ_s_glue N i j T1 T2) :
    ¬ Crosses p (i, j) := by
  rw [pkZ_s_glue, mem_insert, mem_union, mem_image, mem_image] at hp
  rcases hp with rfl | ⟨p', hp', rfl⟩ | ⟨p', hp', rfl⟩
  · simp only [Crosses]; omega
  · exact pkZ_s_In_nc (pkZ_s_mapL hi hij hjN hne (h1 hp')).2.1
  · exact pkZ_s_Out_nc (pkZ_s_mapR hi hij hjN hne hE (h2 hp')).2.1

/-- Gluing maximal sets of the two children gives a maximal set through the chord. -/
lemma pkZ_s_glue_max {Q : ℕ → Prop} [DecidablePred Q] {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N)
    (hne : ¬ (i = 1 ∧ j = N)) (hE : N % 2 = 0) (hQC : (i, j) ∈ pkZ_s_S Q N) {T1 T2 : Finset (ℕ × ℕ)}
    (h1 : pkZ_s_IsMax (pkZ_s_S Q (j - i + 1)) T1) (h2 : pkZ_s_IsMax (pkZ_s_S Q (N - j + i + 1)) T2) :
    pkZ_s_IsMax (pkZ_s_S Q N) (pkZ_s_glue N i j T1 T2) := by
  have hL : T1 ⊆ diagonals (j - i + 1) := fun d hd => (pkZ_s_mem_S.1 (h1.1 hd)).1
  have hR : T2 ⊆ diagonals (N - j + i + 1) := fun d hd => (pkZ_s_mem_S.1 (h2.1 hd)).1
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    rw [pkZ_s_glue, mem_insert, mem_union, mem_image, mem_image] at hd
    rcases hd with rfl | ⟨d', hd', rfl⟩ | ⟨d', hd', rfl⟩
    · exact hQC
    · exact (pkZ_s_mapLQ hi hij hjN hne (h1.1 hd')).1
    · exact (pkZ_s_mapRQ hi hij hjN hne hE (h2.1 hd')).1
  · intro p hp q hq
    have hpc := pkZ_s_glue_nc hi hij hjN hne hE hL hR hp
    have hqc := pkZ_s_glue_nc hi hij hjN hne hE hL hR hq
    rw [pkZ_s_glue, mem_insert, mem_union, mem_image, mem_image] at hp hq
    rcases hp with rfl | ⟨p', hp', rfl⟩ | ⟨p', hp', rfl⟩
    · exact fun h => hqc (pkZ_s_cross_symm.1 h)
    · rcases hq with rfl | ⟨q', hq', rfl⟩ | ⟨q', hq', rfl⟩
      · exact hpc
      · rw [pkZ_s_cross (N := N) (b := i) (n := j - i + 1) (by omega) (by omega) (by omega) (hL hp') (hL hq')]
        exact h1.2.1 _ hp' _ hq'
      · obtain ⟨hpN, hin, -⟩ := pkZ_s_mapL hi hij hjN hne (hL hp')
        obtain ⟨hqN, hout, -⟩ := pkZ_s_mapR hi hij hjN hne hE (hR hq')
        exact pkZ_s_In_Out_nc (pkZ_s_lt hpN) (pkZ_s_lt hqN) hin hout
    · rcases hq with rfl | ⟨q', hq', rfl⟩ | ⟨q', hq', rfl⟩
      · exact hpc
      · obtain ⟨hqN, hin, -⟩ := pkZ_s_mapL hi hij hjN hne (hL hq')
        obtain ⟨hpN, hout, -⟩ := pkZ_s_mapR hi hij hjN hne hE (hR hp')
        exact fun h => pkZ_s_In_Out_nc (pkZ_s_lt hqN) (pkZ_s_lt hpN) hin hout (pkZ_s_cross_symm.1 h)
      · rw [pkZ_s_cross (N := N) (b := j) (n := N - j + i + 1) (by omega) (by omega) (by omega) (hR hp') (hR hq')]
        exact h2.2.1 _ hp' _ hq'
  · intro d hd hnot
    have hdN := (pkZ_s_mem_S.1 hd).1
    rcases pkZ_s_part (i := i) (j := j) hdN with rfl | hc | hin | hout
    · exact absurd (mem_insert_self _ _) hnot
    · exact ⟨(i, j), mem_insert_self _ _, pkZ_s_cross_symm.1 hc⟩
    · obtain ⟨d', hd', rfl⟩ := pkZ_s_surjLQ hi hij hjN hne hd hin
      have hd'L := (pkZ_s_mem_S.1 hd').1
      have hn1 : d' ∉ T1 := fun h => hnot ((pkZ_s_mem_glue_L hi hij hjN hne hE hL hR hd'L).2 h)
      obtain ⟨p', hp', hc⟩ := h1.2.2 d' hd' hn1
      refine ⟨pkZ_relab N i p', (pkZ_s_mem_glue_L hi hij hjN hne hE hL hR (hL hp')).2 hp', ?_⟩
      rwa [pkZ_s_cross (N := N) (b := i) (n := j - i + 1) (by omega) (by omega) (by omega) (hL hp') hd'L]
    · obtain ⟨d', hd', rfl⟩ := pkZ_s_surjRQ hi hij hjN hne hE hd hout
      have hd'R := (pkZ_s_mem_S.1 hd').1
      have hn2 : d' ∉ T2 := fun h => hnot ((pkZ_s_mem_glue_R hi hij hjN hne hE hL hR hd'R).2 h)
      obtain ⟨p', hp', hc⟩ := h2.2.2 d' hd' hn2
      refine ⟨pkZ_relab N j p', (pkZ_s_mem_glue_R hi hij hjN hne hE hL hR (hR hp')).2 hp', ?_⟩
      rwa [pkZ_s_cross (N := N) (b := j) (n := N - j + i + 1) (by omega) (by omega) (by omega) (hR hp') hd'R]

/-- The left restriction of a maximal set through the chord is maximal. -/
lemma pkZ_s_left_max {Q : ℕ → Prop} [DecidablePred Q] {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N)
    (hne : ¬ (i = 1 ∧ j = N)) {T : Finset (ℕ × ℕ)} (hT : pkZ_s_IsMax (pkZ_s_S Q N) T) (hC : (i, j) ∈ T) :
    pkZ_s_IsMax (pkZ_s_S Q (j - i + 1)) ((pkZ_s_S Q (j - i + 1)).filter (fun d => pkZ_relab N i d ∈ T)) := by
  refine ⟨filter_subset _ _, ?_, ?_⟩
  · intro p hp q hq
    rw [mem_filter] at hp hq
    rw [← pkZ_s_cross (N := N) (b := i) (n := j - i + 1) (by omega) (by omega) (by omega)
      (pkZ_s_mem_S.1 hp.1).1 (pkZ_s_mem_S.1 hq.1).1]
    exact hT.2.1 _ hp.2 _ hq.2
  · intro d hd hnot
    have hnT : pkZ_relab N i d ∉ T := fun h => hnot (mem_filter.2 ⟨hd, h⟩)
    obtain ⟨hdN, hin⟩ := pkZ_s_mapLQ hi hij hjN hne hd
    obtain ⟨p, hp, hc⟩ := hT.2.2 _ hdN hnT
    have hpN := hT.1 hp
    have hne' : p ≠ (i, j) := by
      rintro rfl; exact pkZ_s_In_nc hin (pkZ_s_cross_symm.1 hc)
    have hpin := pkZ_s_In_of_cross (pkZ_s_lt (pkZ_s_mem_S.1 hpN).1) hin hc (hT.2.1 _ hp _ hC) hne'
    obtain ⟨p', hp', rfl⟩ := pkZ_s_surjLQ hi hij hjN hne hpN hpin
    refine ⟨p', mem_filter.2 ⟨hp', hp⟩, ?_⟩
    rwa [← pkZ_s_cross (N := N) (b := i) (n := j - i + 1) (by omega) (by omega) (by omega)
      (pkZ_s_mem_S.1 hp').1 (pkZ_s_mem_S.1 hd).1]

lemma pkZ_s_right_max {Q : ℕ → Prop} [DecidablePred Q] {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N)
    (hne : ¬ (i = 1 ∧ j = N)) (hE : N % 2 = 0) {T : Finset (ℕ × ℕ)} (hT : pkZ_s_IsMax (pkZ_s_S Q N) T)
    (hC : (i, j) ∈ T) :
    pkZ_s_IsMax (pkZ_s_S Q (N - j + i + 1)) ((pkZ_s_S Q (N - j + i + 1)).filter (fun d => pkZ_relab N j d ∈ T)) := by
  refine ⟨filter_subset _ _, ?_, ?_⟩
  · intro p hp q hq
    rw [mem_filter] at hp hq
    rw [← pkZ_s_cross (N := N) (b := j) (n := N - j + i + 1) (by omega) (by omega) (by omega)
      (pkZ_s_mem_S.1 hp.1).1 (pkZ_s_mem_S.1 hq.1).1]
    exact hT.2.1 _ hp.2 _ hq.2
  · intro d hd hnot
    have hnT : pkZ_relab N j d ∉ T := fun h => hnot (mem_filter.2 ⟨hd, h⟩)
    obtain ⟨hdN, hout⟩ := pkZ_s_mapRQ hi hij hjN hne hE hd
    obtain ⟨p, hp, hc⟩ := hT.2.2 _ hdN hnT
    have hpN := hT.1 hp
    have hne' : p ≠ (i, j) := by
      rintro rfl; exact pkZ_s_Out_nc hout (pkZ_s_cross_symm.1 hc)
    have hpout := pkZ_s_Out_of_cross (pkZ_s_lt (pkZ_s_mem_S.1 hpN).1) hout hc (hT.2.1 _ hp _ hC) hne'
    obtain ⟨p', hp', rfl⟩ := pkZ_s_surjRQ hi hij hjN hne hE hpN hpout
    refine ⟨p', mem_filter.2 ⟨hp', hp⟩, ?_⟩
    rwa [← pkZ_s_cross (N := N) (b := j) (n := N - j + i + 1) (by omega) (by omega) (by omega)
      (pkZ_s_mem_S.1 hp').1 (pkZ_s_mem_S.1 hd).1]

/-- A maximal set through the chord is the glue of its two restrictions. -/
lemma pkZ_s_glue_split {Q : ℕ → Prop} [DecidablePred Q] {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N)
    (hne : ¬ (i = 1 ∧ j = N)) (hE : N % 2 = 0) {T : Finset (ℕ × ℕ)} (hT : pkZ_s_IsMax (pkZ_s_S Q N) T)
    (hC : (i, j) ∈ T) :
    pkZ_s_glue N i j ((pkZ_s_S Q (j - i + 1)).filter (fun d => pkZ_relab N i d ∈ T))
      ((pkZ_s_S Q (N - j + i + 1)).filter (fun d => pkZ_relab N j d ∈ T)) = T := by
  ext p
  rw [pkZ_s_glue, mem_insert, mem_union, mem_image, mem_image]
  constructor
  · rintro (rfl | ⟨p', hp', rfl⟩ | ⟨p', hp', rfl⟩)
    · exact hC
    · exact (mem_filter.1 hp').2
    · exact (mem_filter.1 hp').2
  · intro hp
    have hpN := hT.1 hp
    rcases pkZ_s_part (i := i) (j := j) (pkZ_s_mem_S.1 hpN).1 with h | hc | hin | hout
    · exact Or.inl h
    · exact absurd hc (hT.2.1 _ hp _ hC)
    · obtain ⟨p', hp', rfl⟩ := pkZ_s_surjLQ hi hij hjN hne hpN hin
      exact Or.inr (Or.inl ⟨p', mem_filter.2 ⟨hp', hp⟩, rfl⟩)
    · obtain ⟨p', hp', rfl⟩ := pkZ_s_surjRQ hi hij hjN hne hE hpN hout
      exact Or.inr (Or.inr ⟨p', mem_filter.2 ⟨hp', hp⟩, rfl⟩)

/-- **The chord-split bijection, generic** (R12-P3c §5 C5 item 4): for any family `tr n` of the maximal
non-crossing subsets of a parity class of diagonals (triangulations, quadrangulations), sets through the chord
`(i, j)` are the glued pairs of sets of the two children `P_L = i..j`, `P_R = j..N,1..i`. -/
theorem pkZ_s_sum_split {M : Type*} [AddCommMonoid M] {Q : ℕ → Prop} [DecidablePred Q]
    (tr : ℕ → Finset (Finset (ℕ × ℕ))) (htr : ∀ n T, T ∈ tr n ↔ pkZ_s_IsMax (pkZ_s_S Q n) T)
    {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N) (hne : ¬ (i = 1 ∧ j = N)) (hE : N % 2 = 0)
    (hQC : (i, j) ∈ pkZ_s_S Q N) (g : Finset (ℕ × ℕ) → M) :
    ∑ T ∈ (tr N).filter (fun T => (i, j) ∈ T), g T =
      ∑ x ∈ tr (j - i + 1) ×ˢ tr (N - j + i + 1), g (pkZ_s_glue N i j x.1 x.2) := by
  refine (sum_nbij' (fun x => pkZ_s_glue N i j x.1 x.2)
    (fun T => ((pkZ_s_S Q (j - i + 1)).filter (fun d => pkZ_relab N i d ∈ T),
      (pkZ_s_S Q (N - j + i + 1)).filter (fun d => pkZ_relab N j d ∈ T))) ?_ ?_ ?_ ?_ ?_).symm
  · rintro ⟨T1, T2⟩ hx
    simp only [coe_product, Set.mem_prod, mem_coe, coe_filter, Set.mem_setOf_eq, mem_filter, mem_product,
      htr] at hx ⊢
    exact ⟨pkZ_s_glue_max hi hij hjN hne hE hQC hx.1 hx.2, mem_insert_self _ _⟩
  · intro T hT
    simp only [coe_product, Set.mem_prod, mem_coe, coe_filter, Set.mem_setOf_eq, mem_filter, mem_product,
      htr] at hT ⊢
    exact ⟨pkZ_s_left_max hi hij hjN hne hT.1 hT.2, pkZ_s_right_max hi hij hjN hne hE hT.1 hT.2⟩
  · rintro ⟨T1, T2⟩ hx
    simp only [coe_product, Set.mem_prod, mem_coe, mem_product, htr] at hx
    have hL : T1 ⊆ diagonals (j - i + 1) := fun d hd => (pkZ_s_mem_S.1 (hx.1.1 hd)).1
    have hR : T2 ⊆ diagonals (N - j + i + 1) := fun d hd => (pkZ_s_mem_S.1 (hx.2.1 hd)).1
    simp only [Prod.mk.injEq]
    constructor
    · ext d
      rw [mem_filter]
      constructor
      · rintro ⟨hd, h⟩
        exact (pkZ_s_mem_glue_L hi hij hjN hne hE hL hR (pkZ_s_mem_S.1 hd).1).1 h
      · intro h
        exact ⟨hx.1.1 h, (pkZ_s_mem_glue_L hi hij hjN hne hE hL hR (hL h)).2 h⟩
    · ext d
      rw [mem_filter]
      constructor
      · rintro ⟨hd, h⟩
        exact (pkZ_s_mem_glue_R hi hij hjN hne hE hL hR (pkZ_s_mem_S.1 hd).1).1 h
      · intro h
        exact ⟨hx.2.1 h, (pkZ_s_mem_glue_R hi hij hjN hne hE hL hR (hR h)).2 h⟩
  · intro T hT
    simp only [coe_filter, Set.mem_setOf_eq, mem_coe, mem_filter, htr] at hT
    exact pkZ_s_glue_split hi hij hjN hne hE hT.1 hT.2
  · intro _ _; rfl

lemma pkZ_s_tri_iff (n : ℕ) (T : Finset (ℕ × ℕ)) :
    T ∈ triangulations n ↔ pkZ_s_IsMax (pkZ_s_S (fun _ => True) n) T := by
  have h : pkZ_s_S (fun _ => True) n = diagonals n := filter_true_of_mem fun _ _ => trivial
  rw [h, mem_triangulations]
  exact Iff.rfl

lemma pkZ_s_odd_eq (n : ℕ) : oddDiagonals n = pkZ_s_S (fun r => r = 1) n := rfl

/-- The summand of `pkZ_AP`. -/
noncomputable def pkZ_s_F (R : Type*) [CommRing R] (n : ℕ) (T : Finset (ℕ × ℕ)) :
    PowerSeries (MvPolynomial (ℕ × ℕ) R) :=
  PowerSeries.C (∏ d ∈ oddDiagonals n \ T, MvPolynomial.X d) *
    ∏ d ∈ T.filter (fun d => shiftSign d ≠ 0), pkZ_sP R d

lemma pkZ_s_shiftSign_odd {d : ℕ × ℕ} (hd : d.1 ≤ d.2) (h : (d.2 - d.1) % 2 = 1) : shiftSign d = 0 := by
  unfold shiftSign; split_ifs <;> omega

lemma pkZ_s_sign_relab {N b n : ℕ} (hE : N % 2 = 0) (hb : 1 ≤ b) (hn : n + b - 1 ≤ 2 * N) (hnN : n ≤ N)
    {d : ℕ × ℕ} (hd : d ∈ diagonals n) : shiftSign (pkZ_relab N b d) = (-1) ^ (b + 1) * shiftSign d := by
  obtain ⟨a, c⟩ := d
  rw [mem_diagonals] at hd; dsimp only at hd
  have h := pkZ_s_spec2 (N := N) (b := b) (a := a) (c := c) (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨k, hk | hk⟩ : ∃ k, b = 2 * k ∨ b = 2 * k + 1 := ⟨b / 2, by omega⟩
  · have hp : ((-1 : ℤ)) ^ (b + 1) = -1 := by
      rw [hk]; exact Odd.neg_one_pow ⟨k, rfl⟩
    rw [hp]; unfold shiftSign; dsimp only; split_ifs <;> omega
  · have hp : ((-1 : ℤ)) ^ (b + 1) = 1 := by
      rw [hk]; exact Even.neg_one_pow ⟨k + 1, by ring⟩
    rw [hp]; unfold shiftSign; dsimp only; split_ifs <;> omega

lemma pkZ_s_rescale_C {R : Type*} [CommRing R] (a b : MvPolynomial (ℕ × ℕ) R) :
    PowerSeries.rescale a (PowerSeries.C b) = PowerSeries.C b := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  split_ifs with h <;> simp [h]

lemma pkZ_s_map_sP {R : Type*} [CommRing R] (f : MvPolynomial (ℕ × ℕ) R →+* MvPolynomial (ℕ × ℕ) R) (d : ℕ × ℕ) (h : f (MvPolynomial.X d) = MvPolynomial.X d) :
    PowerSeries.map f (pkZ_sP R d) = pkZ_sP R d := by
  ext n
  rw [PowerSeries.coeff_map]
  rcases n with _ | n
  · simp [pkZ_sP]
  · simp only [pkZ_sP, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]
    simp [map_mul, map_pow, map_neg, h]

lemma pkZ_s_sP_relab {R : Type*} [CommRing R] (ρ : ℕ × ℕ → ℕ × ℕ) (σ : ℤ) (d : ℕ × ℕ) (h : shiftSign (ρ d) = σ * shiftSign d) :
    PowerSeries.rescale ((σ : ℤ) : MvPolynomial (ℕ × ℕ) R)
      (PowerSeries.map (MvPolynomial.rename ρ).toRingHom (pkZ_sP R d)) = pkZ_sP R (ρ d) := by
  ext n
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_map]
  rcases n with _ | n
  · simp [pkZ_sP]
  · simp only [pkZ_sP, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, h]
    simp [map_mul, map_pow, map_neg, MvPolynomial.rename_X, mul_pow]
    ring

lemma pkZ_s_resc_F {R : Type*} [CommRing R] (n : ℕ) (ρ : ℕ × ℕ → ℕ × ℕ) (σ : ℤ) (T : Finset (ℕ × ℕ))
    (hs : ∀ d ∈ T, shiftSign (ρ d) = σ * shiftSign d) :
    PowerSeries.rescale ((σ : ℤ) : MvPolynomial (ℕ × ℕ) R)
        (PowerSeries.map (MvPolynomial.rename ρ).toRingHom (pkZ_s_F R n T)) =
      PowerSeries.C (∏ d ∈ oddDiagonals n \ T, MvPolynomial.X (ρ d)) *
        ∏ d ∈ T.filter (fun d => shiftSign d ≠ 0), pkZ_sP R (ρ d) := by
  rw [pkZ_s_F, map_mul, map_mul, PowerSeries.map_C, pkZ_s_rescale_C]
  congr 1
  · congr 1
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_prod, MvPolynomial.rename_X]
  · rw [map_prod (PowerSeries.map _), map_prod (PowerSeries.rescale _)]
    exact prod_congr rfl fun d hd => pkZ_s_sP_relab ρ σ d (hs d (mem_filter.1 hd).1)

/-- Setting `X_C = 0` keeps exactly the triangulations through `C`. -/
lemma pkZ_s_zeroAt_AP {R : Type*} [CommRing R] {N m : ℕ} {C : ℕ × ℕ} (hC : C ∈ oddDiagonals N) :
    pkZ_zeroAt R C (pkZ_AP R N m) =
      PowerSeries.coeff m (∑ T ∈ (triangulations N).filter (fun T => C ∈ T), pkZ_s_F R N T) := by
  have hsC : shiftSign C = 0 := by
    have h := mem_filter.1 hC
    have h1 := mem_diagonals.1 h.1
    exact pkZ_s_shiftSign_odd (by omega) h.2
  have hmap : ∀ f : PowerSeries (MvPolynomial (ℕ × ℕ) R),
      pkZ_zeroAt R C (PowerSeries.coeff m f) = PowerSeries.coeff m (PowerSeries.map (pkZ_zeroAt R C).toRingHom f) := by
    intro f; rw [PowerSeries.coeff_map]; rfl
  rw [sum_filter, pkZ_AP, hmap, map_sum]
  congr 1
  refine sum_congr rfl fun T _ => ?_
  rw [map_mul, PowerSeries.map_C, map_prod (PowerSeries.map _)]
  have hs : ∀ d ∈ T.filter (fun d => shiftSign d ≠ 0),
      PowerSeries.map (pkZ_zeroAt R C).toRingHom (pkZ_sP R d) = pkZ_sP R d := by
    intro d hd
    have hdC : d ≠ C := fun h => (mem_filter.1 hd).2 (by rw [h]; exact hsC)
    exact pkZ_s_map_sP _ d (by simp [pkZ_zeroAt, hdC])
  rw [prod_congr rfl hs]
  split_ifs with hCT
  · rw [pkZ_s_F]
    congr 2
    rw [map_prod]
    refine prod_congr rfl fun d hd => ?_
    have hdC : d ≠ C := fun h => (mem_sdiff.1 hd).2 (by rw [h]; exact hCT)
    simp [pkZ_zeroAt, hdC]
  · rw [map_prod, prod_eq_zero (mem_sdiff.2 ⟨hC, hCT⟩) (by simp [pkZ_zeroAt]), map_zero, zero_mul]

/-- The summand at a glued triangulation factors over the two children. -/
lemma pkZ_s_F_glue {R : Type*} [CommRing R] {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N) (hne : ¬ (i = 1 ∧ j = N))
    (hE : N % 2 = 0) (hodd : (j - i) % 2 = 1) {T1 T2 : Finset (ℕ × ℕ)} (h1 : T1 ⊆ diagonals (j - i + 1))
    (h2 : T2 ⊆ diagonals (N - j + i + 1)) :
    pkZ_s_F R N (pkZ_s_glue N i j T1 T2) =
      PowerSeries.C (pkZ_cross R N (i, j)) *
        (PowerSeries.rescale ((((-1) ^ (i + 1) : ℤ)) : MvPolynomial (ℕ × ℕ) R)
            (PowerSeries.map (MvPolynomial.rename (pkZ_relab N i)).toRingHom (pkZ_s_F R (j - i + 1) T1)) *
          PowerSeries.rescale ((((-1) ^ (j + 1) : ℤ)) : MvPolynomial (ℕ × ℕ) R)
            (PowerSeries.map (MvPolynomial.rename (pkZ_relab N j)).toRingHom (pkZ_s_F R (N - j + i + 1) T2))) := by
  have hsL : ∀ d ∈ T1, shiftSign (pkZ_relab N i d) = (-1) ^ (i + 1) * shiftSign d := fun d hd =>
    pkZ_s_sign_relab hE (by omega) (by omega) (by omega) (h1 hd)
  have hsR : ∀ d ∈ T2, shiftSign (pkZ_relab N j d) = (-1) ^ (j + 1) * shiftSign d := fun d hd =>
    pkZ_s_sign_relab hE (by omega) (by omega) (by omega) (h2 hd)
  rw [pkZ_s_resc_F _ _ _ _ hsL, pkZ_s_resc_F _ _ _ _ hsR]
  have injL : Set.InjOn (pkZ_relab N i) (diagonals (j - i + 1) : Set (ℕ × ℕ)) := fun x hx y hy h =>
    pkZ_s_inj (N := N) (b := i) (n := j - i + 1) (by omega) (by omega) (by omega) hx hy h
  have injR : Set.InjOn (pkZ_relab N j) (diagonals (N - j + i + 1) : Set (ℕ × ℕ)) := fun x hx y hy h =>
    pkZ_s_inj (N := N) (b := j) (n := N - j + i + 1) (by omega) (by omega) (by omega) hx hy h
  have hoddL : ∀ d ∈ oddDiagonals (j - i + 1), d ∈ diagonals (j - i + 1) := fun d hd => (mem_filter.1 hd).1
  have hoddR : ∀ d ∈ oddDiagonals (N - j + i + 1), d ∈ diagonals (N - j + i + 1) :=
    fun d hd => (mem_filter.1 hd).1
  -- the odd diagonals missing from the glued set
  have hodd_set : oddDiagonals N \ pkZ_s_glue N i j T1 T2 =
      (oddDiagonals N).filter (fun d => Crosses d (i, j)) ∪
        ((oddDiagonals (j - i + 1) \ T1).image (pkZ_relab N i) ∪
          (oddDiagonals (N - j + i + 1) \ T2).image (pkZ_relab N j)) := by
    ext d
    rw [mem_sdiff, mem_union, mem_union, mem_filter, mem_image, mem_image]
    constructor
    · rintro ⟨hd, hnot⟩
      rcases pkZ_s_part (i := i) (j := j) (mem_filter.1 hd).1 with rfl | hc | hin | hout
      · exact absurd (mem_insert_self _ _) hnot
      · exact Or.inl ⟨hd, hc⟩
      · rw [pkZ_s_odd_eq] at hd
        obtain ⟨d', hd', rfl⟩ := pkZ_s_surjLQ hi hij hjN hne hd hin
        rw [← pkZ_s_odd_eq] at hd'
        refine Or.inr (Or.inl ⟨d', mem_sdiff.2 ⟨hd', fun h => hnot ?_⟩, rfl⟩)
        exact (pkZ_s_mem_glue_L hi hij hjN hne hE h1 h2 (hoddL _ hd')).2 h
      · rw [pkZ_s_odd_eq] at hd
        obtain ⟨d', hd', rfl⟩ := pkZ_s_surjRQ hi hij hjN hne hE hd hout
        rw [← pkZ_s_odd_eq] at hd'
        refine Or.inr (Or.inr ⟨d', mem_sdiff.2 ⟨hd', fun h => hnot ?_⟩, rfl⟩)
        exact (pkZ_s_mem_glue_R hi hij hjN hne hE h1 h2 (hoddR _ hd')).2 h
    · rintro (⟨hd, hc⟩ | ⟨d', hd', rfl⟩ | ⟨d', hd', rfl⟩)
      · exact ⟨hd, fun h => pkZ_s_glue_nc hi hij hjN hne hE h1 h2 h hc⟩
      · obtain ⟨hd'o, hnT⟩ := mem_sdiff.1 hd'
        rw [pkZ_s_odd_eq] at hd'o
        refine ⟨by rw [pkZ_s_odd_eq]; exact (pkZ_s_mapLQ hi hij hjN hne hd'o).1, fun h => hnT ?_⟩
        exact (pkZ_s_mem_glue_L hi hij hjN hne hE h1 h2 (pkZ_s_mem_S.1 hd'o).1).1 h
      · obtain ⟨hd'o, hnT⟩ := mem_sdiff.1 hd'
        rw [pkZ_s_odd_eq] at hd'o
        refine ⟨by rw [pkZ_s_odd_eq]; exact (pkZ_s_mapRQ hi hij hjN hne hE hd'o).1, fun h => hnT ?_⟩
        exact (pkZ_s_mem_glue_R hi hij hjN hne hE h1 h2 (pkZ_s_mem_S.1 hd'o).1).1 h
  have hdisj1 : Disjoint ((oddDiagonals N).filter (fun d => Crosses d (i, j)))
      ((oddDiagonals (j - i + 1) \ T1).image (pkZ_relab N i) ∪
        (oddDiagonals (N - j + i + 1) \ T2).image (pkZ_relab N j)) := by
    rw [disjoint_left]
    intro d hd hd'
    have hc := (mem_filter.1 hd).2
    rw [mem_union, mem_image, mem_image] at hd'
    rcases hd' with ⟨d', hd', rfl⟩ | ⟨d', hd', rfl⟩
    · exact pkZ_s_In_nc (pkZ_s_mapL hi hij hjN hne (hoddL _ (mem_sdiff.1 hd').1)).2.1 hc
    · exact pkZ_s_Out_nc (pkZ_s_mapR hi hij hjN hne hE (hoddR _ (mem_sdiff.1 hd').1)).2.1 hc
  have hdisjLR : ∀ (A B : Finset (ℕ × ℕ)), A ⊆ diagonals (j - i + 1) → B ⊆ diagonals (N - j + i + 1) →
      Disjoint (A.image (pkZ_relab N i)) (B.image (pkZ_relab N j)) := by
    intro A B hA hB
    rw [disjoint_left]
    intro d hd hd'
    rw [mem_image] at hd hd'
    obtain ⟨a, ha, rfl⟩ := hd
    obtain ⟨b, hb, hba⟩ := hd'
    obtain ⟨haN, hin, -⟩ := pkZ_s_mapL hi hij hjN hne (hA ha)
    obtain ⟨-, hout, -⟩ := pkZ_s_mapR hi hij hjN hne hE (hB hb)
    rw [hba] at hout
    exact pkZ_s_In_not_Out (pkZ_s_lt haN) hin hout
  have hsC : shiftSign (i, j) = 0 := pkZ_s_shiftSign_odd (by dsimp only; omega) hodd
  have hfilt : (pkZ_s_glue N i j T1 T2).filter (fun d => shiftSign d ≠ 0) =
      (T1.filter (fun d => shiftSign d ≠ 0)).image (pkZ_relab N i) ∪
        (T2.filter (fun d => shiftSign d ≠ 0)).image (pkZ_relab N j) := by
    ext d
    simp only [pkZ_s_glue, mem_filter, mem_union, mem_image, mem_insert]
    constructor
    · rintro ⟨rfl | ⟨d', hd', rfl⟩ | ⟨d', hd', rfl⟩, hs⟩
      · exact absurd hsC hs
      · rw [hsL d' hd'] at hs
        exact Or.inl ⟨d', ⟨hd', right_ne_zero_of_mul hs⟩, rfl⟩
      · rw [hsR d' hd'] at hs
        exact Or.inr ⟨d', ⟨hd', right_ne_zero_of_mul hs⟩, rfl⟩
    · rintro (⟨d', ⟨hd', hs⟩, rfl⟩ | ⟨d', ⟨hd', hs⟩, rfl⟩)
      · refine ⟨Or.inr (Or.inl ⟨d', hd', rfl⟩), ?_⟩
        rw [hsL d' hd']; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hs
      · refine ⟨Or.inr (Or.inr ⟨d', hd', rfl⟩), ?_⟩
        rw [hsR d' hd']; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hs
  rw [pkZ_s_F, hodd_set, hfilt, prod_union hdisj1,
    prod_union (hdisjLR _ _ (fun d hd => hoddL _ (mem_sdiff.1 hd).1) (fun d hd => hoddR _ (mem_sdiff.1 hd).1)),
    prod_union (hdisjLR _ _ (fun d hd => h1 (mem_filter.1 hd).1) (fun d hd => h2 (mem_filter.1 hd).1)),
    prod_image (injL.mono fun d hd => hoddL _ (mem_sdiff.1 hd).1),
    prod_image (injR.mono fun d hd => hoddR _ (mem_sdiff.1 hd).1),
    prod_image (injL.mono fun d hd => h1 (mem_filter.1 hd).1),
    prod_image (injR.mono fun d hd => h2 (mem_filter.1 hd).1), pkZ_cross, map_mul, map_mul]
  ring

/-- `AP_residue` in the frozen variable names, proved from the pieces above. -/
theorem pkZ_s_AP_residue {R : Type*} [CommRing R] {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {C : ℕ × ℕ} (hC : C ∈ oddDiagonals N) (m : ℕ) :
    pkZ_zeroAt R C (pkZ_AP R N m) =
      (∑ p ∈ antidiagonal m, ((-1 : MvPolynomial (ℕ × ℕ) R) ^ ((C.1 + 1) * p.1 + (C.2 + 1) * p.2)) *
        (MvPolynomial.rename (pkZ_relab N C.1) (pkZ_AP R (C.2 - C.1 + 1) p.1) *
          MvPolynomial.rename (pkZ_relab N C.2) (pkZ_AP R (N - C.2 + C.1 + 1) p.2))) * pkZ_cross R N C := by
  rw [pkZ_s_zeroAt_AP hC]
  obtain ⟨i, j⟩ := C
  have hC1 := mem_filter.1 hC
  have hC2 := mem_diagonals.1 hC1.1
  dsimp only at hC1 hC2 ⊢
  obtain ⟨hi, hjN, hij, hne⟩ := hC2
  have hodd := hC1.2
  have hQC : (i, j) ∈ pkZ_s_S (fun _ => True) N := pkZ_s_mem_S.2 ⟨(mem_filter.1 hC).1, trivial⟩
  rw [pkZ_s_sum_split triangulations pkZ_s_tri_iff hi hij hjN hne hE hQC (pkZ_s_F R N)]
  have hsub : ∀ n T, T ∈ triangulations n → T ⊆ diagonals n := fun n T hT =>
    (mem_triangulations.1 hT).1
  have hsum : ∑ x ∈ triangulations (j - i + 1) ×ˢ triangulations (N - j + i + 1),
      pkZ_s_F R N (pkZ_s_glue N i j x.1 x.2) =
      ∑ x ∈ triangulations (j - i + 1) ×ˢ triangulations (N - j + i + 1),
        PowerSeries.C (pkZ_cross R N (i, j)) *
          (PowerSeries.rescale (((-1) ^ (i + 1) : ℤ) : MvPolynomial (ℕ × ℕ) R) (PowerSeries.map (MvPolynomial.rename (pkZ_relab N i)).toRingHom (pkZ_s_F R (j - i + 1) x.1)) *
            PowerSeries.rescale (((-1) ^ (j + 1) : ℤ) : MvPolynomial (ℕ × ℕ) R)
              (PowerSeries.map (MvPolynomial.rename (pkZ_relab N j)).toRingHom (pkZ_s_F R (N - j + i + 1) x.2))) :=
    sum_congr rfl fun x hx => pkZ_s_F_glue hi hij hjN hne hE hodd (hsub _ _ (mem_product.1 hx).1)
      (hsub _ _ (mem_product.1 hx).2)
  have hprod : ∀ (A B : Finset (Finset (ℕ × ℕ))) (c : PowerSeries (MvPolynomial (ℕ × ℕ) R))
      (f g : Finset (ℕ × ℕ) → PowerSeries (MvPolynomial (ℕ × ℕ) R)),
      ∑ x ∈ A ×ˢ B, c * (f x.1 * g x.2) = c * ((∑ T ∈ A, f T) * ∑ T ∈ B, g T) := by
    intro A B c f g
    rw [sum_mul_sum, mul_sum, sum_product]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum]
  have hfac : ∑ x ∈ triangulations (j - i + 1) ×ˢ triangulations (N - j + i + 1),
      pkZ_s_F R N (pkZ_s_glue N i j x.1 x.2) =
      PowerSeries.C (pkZ_cross R N (i, j)) *
        (PowerSeries.rescale (((-1) ^ (i + 1) : ℤ) : MvPolynomial (ℕ × ℕ) R) (PowerSeries.map (MvPolynomial.rename (pkZ_relab N i)).toRingHom
            (∑ T ∈ triangulations (j - i + 1), pkZ_s_F R (j - i + 1) T)) *
          PowerSeries.rescale (((-1) ^ (j + 1) : ℤ) : MvPolynomial (ℕ × ℕ) R) (PowerSeries.map (MvPolynomial.rename (pkZ_relab N j)).toRingHom
            (∑ T ∈ triangulations (N - j + i + 1), pkZ_s_F R (N - j + i + 1) T))) := by
    rw [hsum, map_sum (PowerSeries.map _), map_sum (PowerSeries.rescale _), map_sum (PowerSeries.map _),
      map_sum (PowerSeries.rescale _)]
    exact hprod _ _ _
      (fun T => PowerSeries.rescale (((-1) ^ (i + 1) : ℤ) : MvPolynomial (ℕ × ℕ) R) (PowerSeries.map (MvPolynomial.rename (pkZ_relab N i)).toRingHom (pkZ_s_F R (j - i + 1) T)))
      (fun T => PowerSeries.rescale (((-1) ^ (j + 1) : ℤ) : MvPolynomial (ℕ × ℕ) R)
        (PowerSeries.map (MvPolynomial.rename (pkZ_relab N j)).toRingHom (pkZ_s_F R (N - j + i + 1) T)))
  rw [hfac]
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul, mul_sum, sum_mul]
  refine sum_congr rfl fun p _ => ?_
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_rescale, PowerSeries.coeff_map, PowerSeries.coeff_map]
  have eL : PowerSeries.coeff p.1 (∑ T ∈ triangulations (j - i + 1), pkZ_s_F R (j - i + 1) T) =
      pkZ_AP R (j - i + 1) p.1 := rfl
  have eR : PowerSeries.coeff p.2 (∑ T ∈ triangulations (N - j + i + 1), pkZ_s_F R (N - j + i + 1) T) =
      pkZ_AP R (N - j + i + 1) p.2 := rfl
  rw [eL, eR]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  push_cast
  ring

/-! The pointwise δ-order fact needs the numerator machinery before this point of the file, where the base's `AP`,
`AP_residue`, … are not yet declared: the block above is a renamed copy (`pkZ_AP` = `AP` by definition) of the
pkgInf / pkgDeg / pkgSplit proofs it needs, and the lemmas below repeat `AP_eq_zero`'s proof on the copy. -/

lemma pkZ_c_res_zero {R : Type*} [CommRing R] {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0)
    (ih : ∀ n, n < N → 4 ≤ n → n % 2 = 0 → ∀ k, k < n - 2 → pkZ_AP R n k = 0)
    {m : ℕ} (hm : m < N - 2) {C : ℕ × ℕ} (hC : C ∈ oddDiagonals N) : pkZ_zeroAt R C (pkZ_AP R N m) = 0 := by
  rw [pkZ_s_AP_residue hN hE hC m]
  have hc := pkZ_child hE hC
  rw [sum_eq_zero, zero_mul]
  intro p hp
  have hp' := mem_antidiagonal.1 hp
  by_cases h1 : p.1 < C.2 - C.1 + 1 - 2
  · rw [ih (C.2 - C.1 + 1) hc.2.2.1 hc.1 hc.2.1 p.1 h1, map_zero, zero_mul, mul_zero]
  · rw [ih (N - C.2 + C.1 + 1) hc.2.2.2.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 p.2 (by omega), map_zero, mul_zero,
      mul_zero]

lemma pkZ_c_const_zero {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (m : ℕ) (c : ℤ)
    (h : pkZ_AP ℤ N m = (∏ C ∈ oddDiagonals N, (MvPolynomial.X C : MvPolynomial (ℕ × ℕ) ℤ)) * MvPolynomial.C c) :
    c = 0 := by
  obtain ⟨x, hx, hR⟩ := onRect_inhabited (n := N) (k := 1) (m := 1) le_rfl (by omega) le_rfl (by omega)
  have hxo : ∀ d ∈ oddDiagonals N, x d ≠ 0 := fun d hd => hx d (mem_filter.1 hd).1
  have e1 := pkZ_APeval N m x hxo
  rw [shiftCoeff_row_zero hN hE ⟨le_rfl, by omega⟩ x hxo hR (m : ℤ), zero_mul, ← pkZ_APmap (Int.castRingHom ℚ), h]
    at e1
  have e2 : MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℚ)
      ((∏ C ∈ oddDiagonals N, (MvPolynomial.X C : MvPolynomial (ℕ × ℕ) ℤ)) * MvPolynomial.C c)) =
      (∏ d ∈ oddDiagonals N, x d) * (c : ℚ) := by
    simp [map_prod]
  rw [e2] at e1
  have hp : (∏ d ∈ oddDiagonals N, x d) ≠ 0 := prod_ne_zero_iff.2 hxo
  exact Int.cast_eq_zero.1 ((mul_eq_zero.1 e1).resolve_left hp)

lemma pkZ_c_eq_zero_int : ∀ N : ℕ, 4 ≤ N → N % 2 = 0 → ∀ m, m < N - 2 → pkZ_AP ℤ N m = 0 := by
  intro N
  refine Nat.strong_induction_on N ?_
  intro N ih hN hE m hm
  by_cases hs : (oddDiagonals N).card + m < N - 3
  · exact pkZ_APsmall hN m hs
  obtain ⟨Q, hQ⟩ := pkZ_dvd (oddDiagonals N) (pkZ_AP ℤ N m)
    (fun C hC => pkZ_c_res_zero hN hE (fun n hn h4 h2 k hk => ih n hn h4 h2 k hk) hm hC)
  by_contra hne
  have hQ0 : Q ≠ 0 := fun h0 => hne (by rw [hQ, h0, mul_zero])
  have t1 := (pkZ_APhom (R := ℤ) hN m (by omega)).totalDegree hne
  rw [hQ, MvPolynomial.totalDegree_mul_of_isDomain (pkZ_prod_ne _) hQ0, pkZ_prod_deg] at t1
  have t2 : Q.totalDegree = 0 := by omega
  have hc := pkZ_c_const_zero hN hE m (Q.coeff 0) (by rw [hQ, ← MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 t2])
  exact hQ0 (by rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 t2, hc, map_zero])

/-- `sorry` (3c-b). **Lemma 4.1 of Z26: the naive orders cancel.** `A_N(X + δv₀) = O(δ^{−(N−2)})`.
[mirror D3: numerator form, every `m < N − 2`, N ≤ 10; E2] -/
theorem shiftCoeff_eq_zero_of_lt {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (X : ℕ × ℕ → K)
    (hX : ∀ d ∈ oddDiagonals N, X d ≠ 0) {m : ℤ} (hm : m < (N : ℤ) - 2) : shiftCoeff N m X = 0 := by
  rcases lt_or_ge m 0 with h | h
  · exact shiftCoeff_neg N X h
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
  have e := pkZ_APeval N n X hX
  rw [← pkZ_APmap (Int.castRingHom K), pkZ_c_eq_zero_int N hN hE n (by omega), map_zero, map_zero] at e
  exact (mul_eq_zero.1 e.symm).resolve_right (prod_ne_zero_iff.2 hX)

/-- On diagonals of an even polygon, rotation by one flips `v₀`. -/
theorem pkRt_sign_rot {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {d : ℕ × ℕ} (hd : d ∈ diagonals N) :
    shiftSign (rot N d) = - shiftSign d := by
  obtain ⟨a, b⟩ := d
  rw [mem_diagonals] at hd
  dsimp only at hd
  rw [rot_eq (by omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)
    (by dsimp only; omega)]
  have e : ∀ p : ℕ × ℕ, shiftSign p =
      if p.1 % 2 = 0 ∧ p.2 % 2 = 0 then 1 else if p.1 % 2 = 1 ∧ p.2 % 2 = 1 then -1 else 0 := fun p => rfl
  have en : ∀ u, nxt N u = if u = N then 1 else u + 1 := fun u => rfl
  rw [e, e, en, en]
  dsimp only
  split_ifs <;> omega

theorem pkRt_rescale_shift (s : ℤ) (x : K) :
    PowerSeries.rescale (-1 : K) (shiftSeries (-s) x) = shiftSeries s x := by
  have e : ∀ t : ℤ, shiftSeries t x =
      PowerSeries.X * PowerSeries.mk (fun k => (t : K) ^ (k + 1) * (-x) ^ k) := fun t => rfl
  rw [e, e]
  ext n
  rw [PowerSeries.coeff_rescale]
  rcases n with _ | n
  · simp
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk,
      PowerSeries.coeff_mk]
    have h1 : ((-1 : K)) ^ (n + 1) * (-1) ^ (n + 1) = 1 := by
      rw [← mul_pow]
      norm_num
    push_cast
    rw [neg_pow (s : K)]
    linear_combination ((s : K) ^ (n + 1) * (-x) ^ n) * h1

theorem pkRt_rescale_C (a : K) : PowerSeries.rescale (-1 : K) (PowerSeries.C a) = PowerSeries.C a := by
  ext n
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  split_ifs with hn
  · rw [hn, pow_zero, one_mul]
  · rw [mul_zero]

theorem pkRt_phi_rot {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (X : ℕ × ℕ → K) {d : ℕ × ℕ}
    (hd : d ∈ diagonals N) : phi (X ∘ rot N) d = PowerSeries.rescale (-1 : K) (phi X (rot N d)) := by
  have e : ∀ (Y : ℕ × ℕ → K) (p : ℕ × ℕ), phi Y p =
      if shiftSign p = 0 then PowerSeries.C (Y p)⁻¹ else shiftSeries (shiftSign p) (Y p) := fun Y p => rfl
  rw [e, e, pkRt_sign_rot hN hE hd, Function.comp_apply]
  by_cases h : shiftSign d = 0
  · rw [ite_eq_left h, ite_eq_left (show -shiftSign d = 0 by omega), pkRt_rescale_C]
  · rw [ite_eq_right h, ite_eq_right (show ¬ -shiftSign d = 0 by omega), pkRt_rescale_shift]

theorem pkRt_sum_rot {N : ℕ} (hN : 3 ≤ N) (ψ : ℕ × ℕ → PowerSeries K) :
    Finset.sum (triangulations N) (fun T => ∏ d ∈ T, ψ (rot N d)) =
      Finset.sum (triangulations N) (fun T => ∏ d ∈ T, ψ d) := by
  apply (HahnSeries.ofPowerSeries_injective : Function.Injective (HahnSeries.ofPowerSeries ℤ K))
  have h := amp_rot N hN (fun d => (HahnSeries.ofPowerSeries ℤ K (ψ d))⁻¹)
  have e : ∀ Y : ℕ × ℕ → LaurentSeries K,
      amp N Y = Finset.sum (triangulations N) (fun T => ∏ d ∈ T, (Y d)⁻¹) := fun Y => rfl
  rw [e, e] at h
  simp only [Function.comp_apply, inv_inv] at h
  rw [map_sum, map_sum]
  simp only [map_prod]
  exact h

/-- `sorry` (3c-b). NLSM is even in the δ-direction: flipping `v₀ → −v₀` leaves the order `N − 2` unchanged (used to
identify the child's `v₀` in residues; PROOFS §0 "invariant under v₀ → −v₀"). Stated through rotation by one, which
flips `v₀` (C0). -/
theorem NLSM_rot {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (X : ℕ × ℕ → K) : NLSM N (X ∘ rot N) = NLSM N X := by
  rw [NLSM_eq_ps (by omega), NLSM_eq_ps (by omega)]
  have h1 : Finset.sum (triangulations N) (fun T => ∏ d ∈ T, phi (X ∘ rot N) d) =
      Finset.sum (triangulations N)
        (fun T => ∏ d ∈ T, PowerSeries.rescale (-1 : K) (phi X (rot N d))) :=
    Finset.sum_congr rfl (fun T hT => Finset.prod_congr rfl
      (fun d hd => pkRt_phi_rot hN hE X ((mem_triangulations.1 hT).1 hd)))
  have h2 := pkRt_sum_rot (K := K) (N := N) (by omega) (fun d => PowerSeries.rescale (-1 : K) (phi X d))
  have h3 : Finset.sum (triangulations N) (fun T => ∏ d ∈ T, PowerSeries.rescale (-1 : K) (phi X d)) =
      PowerSeries.rescale (-1 : K) (Finset.sum (triangulations N) (fun T => ∏ d ∈ T, phi X d)) := by
    rw [map_sum]
    simp only [map_prod]
  rw [h1, h2, h3, PowerSeries.coeff_rescale,
    (show Even (N - 2) from ⟨(N - 2) / 2, by omega⟩).neg_one_pow, one_mul]

end NLSMside

/-! ## 3. Polynomial numerators and residues (the rational-function layer, part (i)) -/

section Poly

open MvPolynomial

variable (R : Type*) [CommRing R]

/-- A cyclic chord read as a polynomial variable (`0` on edges): the polynomial twin of Phase 1's `planar`. -/
noncomputable def planarP (N i j : ℕ) : MvPolynomial (ℕ × ℕ) R :=
  if npair N i j ∈ diagonals N then X (npair N i j) else 0

/-- The polynomial twin of Phase 3's `vnumX` (PROOFS §0 identity (R)). -/
noncomputable def vnumP (N π : ℕ) (q : Quad) : MvPolynomial (ℕ × ℕ) R :=
  planarP R N q.u1 q.u3 + planarP R N q.u2 q.u4 -
    (if q.u1 % 2 = π then planarP R N q.u2 q.u3 + planarP R N q.u4 q.u1
     else planarP R N q.u1 q.u2 + planarP R N q.u3 q.u4)

/-- The common denominator `∏_{odd C} X_C`. -/
noncomputable def oddDen (N : ℕ) : MvPolynomial (ℕ × ℕ) R := ∏ d ∈ oddDiagonals N, X d

/-- Numerator of `Q_N^π`: `Q_N^π · oddDen = QP` (`QP_eval`). -/
noncomputable def QP (N π : ℕ) : MvPolynomial (ℕ × ℕ) R :=
  ∑ G ∈ quadrangulations N, (∏ q ∈ quads N G, vnumP R N π q) * ∏ d ∈ oddDiagonals N \ G, X d

/-- `shiftSeries` with a polynomial variable. -/
noncomputable def shiftSeriesP (d : ℕ × ℕ) : PowerSeries (MvPolynomial (ℕ × ℕ) R) :=
  PowerSeries.X * PowerSeries.mk (fun k => ((shiftSign d : ℤ) : MvPolynomial (ℕ × ℕ) R) ^ (k + 1) * (-X d) ^ k)

/-- Numerator of the order-`m` coefficient: `shiftCoeff N m · oddDen = AP N m` (`AP_eval`). -/
noncomputable def AP (N m : ℕ) : MvPolynomial (ℕ × ℕ) R :=
  PowerSeries.coeff m (∑ T ∈ triangulations N,
    PowerSeries.C (∏ d ∈ oddDiagonals N \ T, X d) *
      ∏ d ∈ T.filter (fun d => shiftSign d ≠ 0), shiftSeriesP R d)

/-- Numerator of `NLSM_N`. -/
noncomputable def NP (N : ℕ) : MvPolynomial (ℕ × ℕ) R := AP R N (N - 2)

/-- Set the variable `C` to `0` (the residue operation on numerators). -/
noncomputable def zeroAt (C : ℕ × ℕ) : MvPolynomial (ℕ × ℕ) R →ₐ[R] MvPolynomial (ℕ × ℕ) R :=
  aeval (fun d => if d = C then 0 else X d)

/-- Child-to-parent relabelling: child vertex `a` ↦ parent vertex `a + b − 1` read mod `N` (PROOFS Lemma B.2: `P_L`
has `b = i`, `P_R` has `b = j`). -/
def relab (N b : ℕ) (d : ℕ × ℕ) : ℕ × ℕ := npair N (d.1 + b - 1) (d.2 + b - 1)

/-- The odd diagonals crossing `C` (in neither sub-polygon). -/
noncomputable def crossProd (N : ℕ) (C : ℕ × ℕ) : MvPolynomial (ℕ × ℕ) R :=
  ∏ d ∈ (oddDiagonals N).filter (fun d => Crosses d C), X d

variable {R}

lemma planarP_hom {K : Type*} [Field K] (f : MvPolynomial (ℕ × ℕ) R →+* K) (N i j : ℕ) :
    f (planarP R N i j) = planar N (fun d => f (X d)) i j := by
  unfold planarP planar npair
  split_ifs <;> simp

lemma vnumP_hom {K : Type*} [Field K] (f : MvPolynomial (ℕ × ℕ) R →+* K) (N π : ℕ) (q : Quad) :
    f (vnumP R N π q) = vnumX N π (fun d => f (X d)) q := by
  unfold vnumP vnumX
  split_ifs <;> simp [planarP_hom]

/-- PROVED. **Numerator lemma for `Q`, for every ring map into a field** (the pointwise and the generic bridge at
once): `f(QP) = Q_N^π(f ∘ X) · f(oddDen)` wherever no odd diagonal maps to `0`. -/
theorem QP_hom {K : Type*} [Field K] (f : MvPolynomial (ℕ × ℕ) R →+* K) (N π : ℕ)
    (hX : ∀ d ∈ oddDiagonals N, f (X d) ≠ 0) :
    f (QP R N π) = Qpi N π (fun d => f (X d)) * f (oddDen R N) := by
  rw [QP, Qpi, map_sum, sum_mul]
  refine sum_congr rfl fun G hG => ?_
  have hGs : G ⊆ oddDiagonals N := (mem_filter.1 hG).2.1
  rw [map_mul, map_prod, map_prod, diagram, oddDen, map_prod, ← prod_sdiff hGs]
  have hq : ∀ q ∈ quads N G, f (vnumP R N π q) = vnum N π (fun d => f (X d)) q := fun q hq => by
    rw [vnumP_hom, vnum_eq_vnumX π _ (mem_filter.1 hq).1]
  rw [prod_congr rfl hq]
  have hinv : (∏ d ∈ G, (f (X d))⁻¹) * ∏ d ∈ G, f (X d) = 1 := by
    rw [← prod_mul_distrib]
    exact prod_eq_one fun d hd => inv_mul_cancel₀ (hX d (hGs hd))
  calc (∏ q ∈ quads N G, vnum N π (fun d => f (X d)) q) * (∏ d ∈ oddDiagonals N \ G, f (X d))
      = (∏ q ∈ quads N G, vnum N π (fun d => f (X d)) q) * (∏ d ∈ oddDiagonals N \ G, f (X d)) *
          ((∏ d ∈ G, (f (X d))⁻¹) * ∏ d ∈ G, f (X d)) := by rw [hinv, mul_one]
    _ = _ := by ring

/-- PROVED. Numerator lemma for `Q` (pointwise). -/
theorem QP_eval {K : Type*} [Field K] (N π : ℕ) (X : ℕ × ℕ → K) (hX : ∀ d ∈ oddDiagonals N, X d ≠ 0) :
    eval X (QP K N π) = Qpi N π X * ∏ d ∈ oddDiagonals N, X d := by
  have h := QP_hom (eval X) N π (by simpa using hX)
  simp only [eval_X, oddDen, map_prod] at h
  exact h

lemma pkI_map_mk {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (g : ℕ → A) :
    PowerSeries.map f (PowerSeries.mk g) = PowerSeries.mk (fun k => f (g k)) := by
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk]

lemma pkI_evalShift {K : Type*} [Field K] (X : ℕ × ℕ → K) (d : ℕ × ℕ) :
    PowerSeries.map (eval X) (shiftSeriesP K d) = shiftSeries (shiftSign d) (X d) := by
  rw [shiftSeriesP, shiftSeries, map_mul, PowerSeries.map_X, pkI_map_mk]
  simp

lemma pkI_mapShiftP {S : Type*} [CommRing S] (f : R →+* S) (d : ℕ × ℕ) :
    PowerSeries.map (MvPolynomial.map f) (shiftSeriesP R d) = shiftSeriesP S d := by
  rw [shiftSeriesP, shiftSeriesP, map_mul, PowerSeries.map_X, pkI_map_mk]
  simp

lemma pkI_odd_sign {N : ℕ} {d : ℕ × ℕ} (hd : d ∈ oddDiagonals N) : shiftSign d = 0 := by
  have h1 := mem_filter.1 hd
  have h2 := mem_diagonals.1 h1.1
  have h3 := h1.2
  unfold shiftSign
  rcases Nat.mod_two_eq_zero_or_one d.1 with a | a <;> rcases Nat.mod_two_eq_zero_or_one d.2 with b | b <;>
    simp [a, b] <;> omega

lemma pkI_sign_zero {N : ℕ} {d : ℕ × ℕ} (hd : d ∈ diagonals N) (hs : shiftSign d = 0) : d ∈ oddDiagonals N := by
  refine mem_filter.2 ⟨hd, ?_⟩
  have h1 := mem_diagonals.1 hd
  unfold shiftSign at hs
  rcases Nat.mod_two_eq_zero_or_one d.1 with a | a <;> rcases Nat.mod_two_eq_zero_or_one d.2 with b | b <;>
    simp [a, b] at hs <;> omega

lemma pkI_ring_aux {A : Type*} [CommRing A] (a p i z : A) (h : i * z = 1) : a * p = (i * p) * (a * z) := by
  calc a * p = a * p * (i * z) := by rw [h, mul_one]
    _ = _ := by ring

/-- `sorry` (3c-b). Numerator lemma for the δ-coefficients. -/
theorem AP_eval {K : Type*} [Field K] (N m : ℕ) (X : ℕ × ℕ → K) (hX : ∀ d ∈ oddDiagonals N, X d ≠ 0) :
    eval X (AP K N m) = shiftCoeff N m X * ∏ d ∈ oddDiagonals N, X d := by
  have hT : ∀ T ∈ triangulations N, PowerSeries.C (∏ d ∈ oddDiagonals N \ T, X d) *
        ∏ d ∈ T.filter (fun d => shiftSign d ≠ 0), shiftSeries (shiftSign d) (X d) =
      (∏ d ∈ T, phi X d) * PowerSeries.C (∏ d ∈ oddDiagonals N, X d) := by
    intro T hT
    have hTd : T ⊆ diagonals N := (mem_triangulations.1 hT).1
    have hsub : T.filter (fun d => shiftSign d = 0) ⊆ oddDiagonals N := fun d hd =>
      pkI_sign_zero (hTd (mem_filter.1 hd).1) (mem_filter.1 hd).2
    have hsd : oddDiagonals N \ T = oddDiagonals N \ T.filter (fun d => shiftSign d = 0) := by
      ext d
      simp only [mem_sdiff, mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun h => h2 h.1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun h => h2 ⟨h, pkI_odd_sign h1⟩⟩
    have h0 : ∏ d ∈ T.filter (fun d => shiftSign d = 0), phi X d =
        PowerSeries.C (∏ d ∈ T.filter (fun d => shiftSign d = 0), (X d)⁻¹) := by
      rw [map_prod]
      exact prod_congr rfl fun d hd => by unfold phi; rw [if_pos (mem_filter.1 hd).2]
    have h1 : ∏ d ∈ T.filter (fun d => ¬ shiftSign d = 0), phi X d =
        ∏ d ∈ T.filter (fun d => shiftSign d ≠ 0), shiftSeries (shiftSign d) (X d) :=
      prod_congr rfl fun d hd => by unfold phi; rw [if_neg (mem_filter.1 hd).2]
    have hinv : (∏ d ∈ T.filter (fun d => shiftSign d = 0), (X d)⁻¹) *
        ∏ d ∈ T.filter (fun d => shiftSign d = 0), X d = 1 := by
      rw [← prod_mul_distrib]
      exact prod_eq_one fun d hd => inv_mul_cancel₀ (hX d (hsub hd))
    rw [← prod_sdiff hsub, ← hsd, ← prod_filter_mul_prod_filter_not T (fun d => shiftSign d = 0), h0, h1]
    have hc : PowerSeries.C ((∏ d ∈ oddDiagonals N \ T, X d) * ∏ d ∈ T.filter (fun d => shiftSign d = 0), X d) =
        PowerSeries.C (∏ d ∈ oddDiagonals N \ T, X d) *
          PowerSeries.C (∏ d ∈ T.filter (fun d => shiftSign d = 0), X d) := map_mul _ _ _
    rw [hc]
    exact pkI_ring_aux _ _ _ _ (by rw [← map_mul, hinv, map_one])
  rw [AP, ← PowerSeries.coeff_map (eval X), map_sum, shiftCoeff_eq_ps, ← PowerSeries.coeff_mul_C, sum_mul]
  refine congrArg _ (sum_congr rfl fun T hT' => ?_)
  have e1 : PowerSeries.map (eval X) (PowerSeries.C (∏ d ∈ oddDiagonals N \ T, (MvPolynomial.X d : MvPolynomial (ℕ × ℕ) K))) =
      PowerSeries.C (∏ d ∈ oddDiagonals N \ T, X d) := by
    rw [PowerSeries.map_C, map_prod]
    simp only [eval_X]
  have e2 : PowerSeries.map (eval X) (∏ d ∈ T.filter (fun d => shiftSign d ≠ 0), shiftSeriesP K d) =
      ∏ d ∈ T.filter (fun d => shiftSign d ≠ 0), shiftSeries (shiftSign d) (X d) := by
    rw [map_prod]
    exact prod_congr rfl fun d _ => pkI_evalShift X d
  rw [map_mul, e1, e2, hT T hT']

/-- `sorry` (3c-b). Base change of the numerators. -/
theorem QP_map {S : Type*} [CommRing S] (f : R →+* S) (N π : ℕ) : map f (QP R N π) = QP S N π := by
  have hp : ∀ i j, MvPolynomial.map f (planarP R N i j) = planarP S N i j := by
    intro i j
    unfold planarP
    split_ifs <;> simp
  have hv : ∀ q, MvPolynomial.map f (vnumP R N π q) = vnumP S N π q := by
    intro q
    unfold vnumP
    split_ifs <;> simp [hp]
  simp only [QP, map_sum, map_mul, map_prod, hv, map_X]

theorem AP_map {S : Type*} [CommRing S] (f : R →+* S) (N m : ℕ) : map f (AP R N m) = AP S N m := by
  rw [AP, AP, ← PowerSeries.coeff_map (MvPolynomial.map f), map_sum]
  refine congrArg _ (sum_congr rfl fun T _ => ?_)
  simp only [map_mul, map_prod, PowerSeries.map_C, map_X, pkI_mapShiftP]

lemma pkDg_sign_zero {N : ℕ} {d : ℕ × ℕ} (hd : d ∈ diagonals N) (hs : shiftSign d = 0) : d ∈ oddDiagonals N := by
  refine mem_filter.2 ⟨hd, ?_⟩
  have h1 := mem_diagonals.1 hd
  unfold shiftSign at hs
  rcases Nat.mod_two_eq_zero_or_one d.1 with a | a <;> rcases Nat.mod_two_eq_zero_or_one d.2 with b | b <;>
    simp [a, b] at hs <;> omega

lemma pkDg_sign_ne {N : ℕ} {d : ℕ × ℕ} (hd : d ∈ oddDiagonals N) : ¬ shiftSign d ≠ 0 := by
  have h1 := mem_diagonals.1 (mem_filter.1 hd).1
  have h2 := (mem_filter.1 hd).2
  unfold shiftSign
  rcases Nat.mod_two_eq_zero_or_one d.1 with a | a <;> rcases Nat.mod_two_eq_zero_or_one d.2 with b | b <;>
    simp [a, b] <;> omega

lemma pkDg_card_glue {a b k : ℕ} {T1 T2 : Finset (ℕ × ℕ)} (hak : a < k) (hkb : k < b)
    (h1 : T1 ⊆ sdiag a k) (h2 : T2 ⊆ sdiag k b) :
    (glue a b k T1 T2).card =
      T1.card + T2.card + (if a + 1 < k then 1 else 0) + (if k + 1 < b then 1 else 0) := by
  have hA : ∀ d ∈ (if a + 1 < k then {(a, k)} else ∅ : Finset (ℕ × ℕ)), d = (a, k) := by
    intro d hd; split_ifs at hd <;> simp only [mem_singleton, notMem_empty] at hd <;> exact hd
  have hB : ∀ d ∈ (if k + 1 < b then {(k, b)} else ∅ : Finset (ℕ × ℕ)), d = (k, b) := by
    intro d hd; split_ifs at hd <;> simp only [mem_singleton, notMem_empty] at hd <;> exact hd
  have d12 : Disjoint T1 T2 := by
    rw [disjoint_left]
    intro d hd1 hd2
    have := mem_sdiag.1 (h1 hd1); have := mem_sdiag.1 (h2 hd2); omega
  have dAB : Disjoint (if a + 1 < k then {(a, k)} else ∅ : Finset (ℕ × ℕ))
      (if k + 1 < b then {(k, b)} else ∅) := by
    rw [disjoint_left]
    intro d hd1 hd2
    have e1 := hA d hd1; have e2 := hB d hd2
    rw [e1] at e2; simp only [Prod.mk.injEq] at e2; omega
  have dTAB : Disjoint (T1 ∪ T2) ((if a + 1 < k then {(a, k)} else ∅ : Finset (ℕ × ℕ)) ∪
      (if k + 1 < b then {(k, b)} else ∅)) := by
    rw [disjoint_left]
    intro d hd hd'
    rw [mem_union] at hd hd'
    rcases hd' with hd' | hd'
    · have e := hA d hd'; subst e
      rcases hd with hd | hd
      · have := mem_sdiag.1 (h1 hd); dsimp only at this; omega
      · have := mem_sdiag.1 (h2 hd); dsimp only at this; omega
    · have e := hB d hd'; subst e
      rcases hd with hd | hd
      · have := mem_sdiag.1 (h1 hd); dsimp only at this; omega
      · have := mem_sdiag.1 (h2 hd); dsimp only at this; omega
  show (T1 ∪ T2 ∪ ((if a + 1 < k then {(a, k)} else ∅) ∪ (if k + 1 < b then {(k, b)} else ∅))).card = _
  rw [card_union_of_disjoint dTAB, card_union_of_disjoint d12, card_union_of_disjoint dAB]
  split_ifs <;> simp only [card_singleton, card_empty] <;> omega

lemma pkDg_card_tri : ∀ n a b : ℕ, b - a ≤ n → a < b → ∀ T : Finset (ℕ × ℕ), IsTri a b T →
    T.card = b - a - 2 := by
  intro n
  induction n with
  | zero => intro a b h1 h2; omega
  | succ n ih =>
    intro a b h1 h2 T hT
    by_cases hab : a + 1 < b
    · obtain ⟨k, hak, hkb, hA, hB⟩ := exists_apex hab hT
      have e := glue_split hT hak hkb hA hB
      have hL := left_isTri hT hak hkb hA hB
      have hR := right_isTri hT hak hkb hA hB
      have c1 := ih a k (by omega) hak _ hL
      have c2 := ih k b (by omega) hkb _ hR
      rw [← e, pkDg_card_glue hak hkb hL.1 hR.1, c1, c2]
      split_ifs <;> omega
    · have hs : T = ∅ := by
        refine eq_empty_of_forall_notMem fun d hd => ?_
        have := mem_sdiag.1 (hT.1 hd)
        omega
      rw [hs, card_empty]
      omega

lemma pkDg_card_quads {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {G : Finset (ℕ × ℕ)} (hQ : IsQuadrangulation N G) :
    (quads N G).card = G.card + 1 := by
  have hnd : ∀ x ∈ G, x ∈ diagonals N := fun x hx => (mem_filter.1 (hQ.1 hx)).1
  have hinj : Set.InjOn (fun q : Quad => (q.u1, q.u4)) (quads N G) := by
    intro q hq q' hq' h
    simp only [Prod.mk.injEq] at h
    exact p3b_eq_of_base hQ hq hq' h.1 h.2
  have himg : (quads N G).image (fun q : Quad => (q.u1, q.u4)) = insert (1, N) G := by
    ext x
    rw [mem_image, mem_insert]
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨-, -, -, -, hB, -⟩ := p3b_qf hQ.1 hq
      rcases hB with hB | hB
      · exact Or.inr hB
      · left; rw [hB.1, hB.2]
    · rintro (rfl | hx)
      · obtain ⟨q, hq, h1, h4⟩ := p3b_face_quad hN hE hQ (Or.inr ⟨rfl, rfl⟩)
        exact ⟨q, hq, by rw [h1, h4]⟩
      · obtain ⟨c, e⟩ := x
        obtain ⟨q, hq, h1, h4⟩ := p3b_face_quad hN hE hQ (Or.inl hx)
        exact ⟨q, hq, by rw [h1, h4]⟩
  have h1N : (1, N) ∉ G := fun h => by
    have := mem_diagonals.1 (hnd _ h); dsimp only at this; omega
  rw [← card_image_of_injOn hinj, himg, card_insert_of_notMem h1N]

lemma pkDg_planarP (N i j : ℕ) : (planarP R N i j).IsHomogeneous 1 := by
  show (if npair N i j ∈ diagonals N then X (npair N i j) else 0 : MvPolynomial (ℕ × ℕ) R).IsHomogeneous 1
  split_ifs
  · exact isHomogeneous_X R _
  · exact isHomogeneous_zero _ _ _

lemma pkDg_vnumP (N π : ℕ) (q : Quad) : (vnumP R N π q).IsHomogeneous 1 := by
  show (planarP R N q.u1 q.u3 + planarP R N q.u2 q.u4 -
    (if q.u1 % 2 = π then planarP R N q.u2 q.u3 + planarP R N q.u4 q.u1
     else planarP R N q.u1 q.u2 + planarP R N q.u3 q.u4)).IsHomogeneous 1
  refine ((pkDg_planarP N _ _).add (pkDg_planarP N _ _)).sub ?_
  split_ifs
  · exact (pkDg_planarP N _ _).add (pkDg_planarP N _ _)
  · exact (pkDg_planarP N _ _).add (pkDg_planarP N _ _)

lemma pkDg_prodX (s : Finset (ℕ × ℕ)) :
    (Finset.prod s (fun d => (X d : MvPolynomial (ℕ × ℕ) R))).IsHomogeneous s.card := by
  have h := IsHomogeneous.prod s (fun d => (X d : MvPolynomial (ℕ × ℕ) R)) (fun _ => 1)
    (fun d _ => isHomogeneous_X R d)
  rwa [sum_const, smul_eq_mul, mul_one] at h

lemma pkDg_mul {f g : PowerSeries (MvPolynomial (ℕ × ℕ) R)} {r s : ℕ}
    (hf : ∀ k, (PowerSeries.coeff k f).IsHomogeneous (k - r) ∧ (k < r → PowerSeries.coeff k f = 0))
    (hg : ∀ k, (PowerSeries.coeff k g).IsHomogeneous (k - s) ∧ (k < s → PowerSeries.coeff k g = 0)) (k : ℕ) :
    (PowerSeries.coeff k (f * g)).IsHomogeneous (k - (r + s)) ∧
      (k < r + s → PowerSeries.coeff k (f * g) = 0) := by
  rw [PowerSeries.coeff_mul]
  constructor
  · refine IsHomogeneous.sum _ _ _ fun p hp => ?_
    have hk := mem_antidiagonal.1 hp
    by_cases h1 : p.1 < r
    · rw [(hf p.1).2 h1, zero_mul]; exact isHomogeneous_zero _ _ _
    by_cases h2 : p.2 < s
    · rw [(hg p.2).2 h2, mul_zero]; exact isHomogeneous_zero _ _ _
    have h := (hf p.1).1.mul (hg p.2).1
    rwa [show p.1 - r + (p.2 - s) = k - (r + s) by omega] at h
  · intro hk
    refine sum_eq_zero fun p hp => ?_
    have hk' := mem_antidiagonal.1 hp
    by_cases h1 : p.1 < r
    · rw [(hf p.1).2 h1, zero_mul]
    · rw [(hg p.2).2 (by omega), mul_zero]

lemma pkDg_prod (s : Finset (ℕ × ℕ)) (f : ℕ × ℕ → PowerSeries (MvPolynomial (ℕ × ℕ) R))
    (hf : ∀ d ∈ s, ∀ k, (PowerSeries.coeff k (f d)).IsHomogeneous (k - 1) ∧
      (k < 1 → PowerSeries.coeff k (f d) = 0)) :
    ∀ k, (PowerSeries.coeff k (Finset.prod s f)).IsHomogeneous (k - s.card) ∧
      (k < s.card → PowerSeries.coeff k (Finset.prod s f) = 0) := by
  induction s using Finset.induction_on with
  | empty =>
    intro k
    rw [prod_empty, card_empty, PowerSeries.coeff_one]
    refine ⟨?_, fun h => absurd h (Nat.not_lt_zero _)⟩
    split_ifs with h
    · subst h; exact isHomogeneous_one _ _
    · exact isHomogeneous_zero _ _ _
  | insert a s ha ih =>
    intro k
    rw [prod_insert ha, card_insert_of_notMem ha]
    have h := pkDg_mul (hf a (mem_insert_self a s)) (ih fun d hd => hf d (mem_insert_of_mem hd)) k
    rwa [show 1 + s.card = s.card + 1 by omega] at h

lemma pkDg_shift (d : ℕ × ℕ) (k : ℕ) :
    (PowerSeries.coeff k (shiftSeriesP R d)).IsHomogeneous (k - 1) ∧
      (k < 1 → PowerSeries.coeff k (shiftSeriesP R d) = 0) := by
  have e : shiftSeriesP R d = PowerSeries.X * PowerSeries.mk
      (fun k => ((shiftSign d : ℤ) : MvPolynomial (ℕ × ℕ) R) ^ (k + 1) * (-X d) ^ k) := rfl
  rw [e]
  rcases k with _ | k
  · rw [PowerSeries.coeff_zero_X_mul]; exact ⟨isHomogeneous_zero _ _ _, fun _ => rfl⟩
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]
    refine ⟨?_, fun h => absurd h (by omega)⟩
    have h1 : (((shiftSign d : ℤ) : MvPolynomial (ℕ × ℕ) R) ^ (k + 1)).IsHomogeneous (0 * (k + 1)) := by
      rw [← map_intCast (C : R →+* MvPolynomial (ℕ × ℕ) R)]
      exact (isHomogeneous_C _ _).pow _
    have h2 := h1.mul ((isHomogeneous_X R d).neg.pow k)
    rwa [show 0 * (k + 1) + 1 * k = k + 1 - 1 by omega] at h2

/-- `sorry` (3c-b). PROOFS Lemma B.1 (degree): `QP` is homogeneous of degree `#odd + 1`. [mirror D4, N ≤ 10] -/
theorem QP_isHomogeneous {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (π : ℕ) :
    (QP R N π).IsHomogeneous ((oddDiagonals N).card + 1) := by
  show (Finset.sum (quadrangulations N) (fun G => (Finset.prod (quads N G) (fun q => vnumP R N π q)) *
    Finset.prod (oddDiagonals N \ G) (fun d => X d))).IsHomogeneous _
  refine IsHomogeneous.sum _ _ _ fun G hG => ?_
  have hGq := (mem_filter.1 hG).2
  have hc := pkDg_card_quads hN hE hGq
  have hsub : G ⊆ oddDiagonals N := hGq.1
  have hd := card_sdiff_of_subset hsub
  have hle := card_le_card hsub
  have h := (IsHomogeneous.prod (quads N G) (fun q => vnumP R N π q) (fun _ => 1)
    (fun q _ => pkDg_vnumP N π q)).mul (pkDg_prodX (oddDiagonals N \ G))
  rw [sum_const, smul_eq_mul, mul_one] at h
  rwa [show (quads N G).card + (oddDiagonals N \ G).card = (oddDiagonals N).card + 1 by omega] at h

/-- `sorry` (3c-b). Z26 Lemma 4.1 (degree): `AP N m` is homogeneous of degree `#odd + m − (N − 3)`. [mirror D4] -/
theorem AP_isHomogeneous {N : ℕ} (hN : 4 ≤ N) (m : ℕ) (hm : N - 3 ≤ (oddDiagonals N).card + m) :
    (AP R N m).IsHomogeneous ((oddDiagonals N).card + m - (N - 3)) := by
  show (PowerSeries.coeff m (Finset.sum (triangulations N) (fun T =>
    PowerSeries.C (Finset.prod (oddDiagonals N \ T) (fun d => X d)) *
      Finset.prod (T.filter (fun d => shiftSign d ≠ 0)) (fun d => shiftSeriesP R d)))).IsHomogeneous _
  rw [map_sum]
  refine IsHomogeneous.sum _ _ _ fun T hT => ?_
  rw [PowerSeries.coeff_C_mul]
  have hTd : T ⊆ diagonals N := (mem_triangulations.1 hT).1
  have hcard : T.card = N - 3 := by
    have h := pkDg_card_tri N 1 N (by omega) (by omega) T
      (mem_tri.1 (by rw [← triangulations_eq_tri]; exact hT))
    omega
  have hsplit : (T.filter (fun d => shiftSign d ≠ 0)).card + (T.filter (fun d => ¬ shiftSign d ≠ 0)).card =
      T.card := card_filter_add_card_filter_not _
  have heq : T.filter (fun d => ¬ shiftSign d ≠ 0) = T ∩ oddDiagonals N := by
    ext d
    rw [mem_filter, mem_inter]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, pkDg_sign_zero (hTd h1) (not_not.1 h2)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, pkDg_sign_ne h2⟩
  have hsd : (oddDiagonals N \ T).card = (oddDiagonals N).card - (T ∩ oddDiagonals N).card := card_sdiff
  have hle : (T ∩ oddDiagonals N).card ≤ (oddDiagonals N).card := card_le_card inter_subset_right
  rw [heq] at hsplit
  have hP := pkDg_prod (T.filter (fun d => shiftSign d ≠ 0)) (fun d => shiftSeriesP R d)
    (fun d _ k => pkDg_shift d k) m
  by_cases hr : m < (T.filter (fun d => shiftSign d ≠ 0)).card
  · rw [hP.2 hr, mul_zero]
    exact isHomogeneous_zero _ _ _
  · have h := (pkDg_prodX (oddDiagonals N \ T)).mul hP.1
    rwa [show (oddDiagonals N \ T).card + (m - (T.filter (fun d => shiftSign d ≠ 0)).card) =
      (oddDiagonals N).card + m - (N - 3) by omega] at h

lemma pkI_card_glue {a b k : ℕ} {T1 T2 : Finset (ℕ × ℕ)} (hak : a < k) (hkb : k < b)
    (h1 : T1 ⊆ sdiag a k) (h2 : T2 ⊆ sdiag k b) :
    (glue a b k T1 T2).card =
      T1.card + T2.card + (if a + 1 < k then 1 else 0) + (if k + 1 < b then 1 else 0) := by
  have hA : ∀ d ∈ (if a + 1 < k then {(a, k)} else ∅ : Finset (ℕ × ℕ)), d = (a, k) := by
    intro d hd; split_ifs at hd <;> simp only [mem_singleton, notMem_empty] at hd <;> exact hd
  have hB : ∀ d ∈ (if k + 1 < b then {(k, b)} else ∅ : Finset (ℕ × ℕ)), d = (k, b) := by
    intro d hd; split_ifs at hd <;> simp only [mem_singleton, notMem_empty] at hd <;> exact hd
  have d12 : Disjoint T1 T2 := by
    rw [disjoint_left]
    intro d hd1 hd2
    have := mem_sdiag.1 (h1 hd1); have := mem_sdiag.1 (h2 hd2); omega
  have dAB : Disjoint (if a + 1 < k then {(a, k)} else ∅ : Finset (ℕ × ℕ))
      (if k + 1 < b then {(k, b)} else ∅) := by
    rw [disjoint_left]
    intro d hd1 hd2
    have e1 := hA d hd1; have e2 := hB d hd2
    rw [e1] at e2; simp only [Prod.mk.injEq] at e2; omega
  have dTAB : Disjoint (T1 ∪ T2) ((if a + 1 < k then {(a, k)} else ∅ : Finset (ℕ × ℕ)) ∪
      (if k + 1 < b then {(k, b)} else ∅)) := by
    rw [disjoint_left]
    intro d hd hd'
    rw [mem_union] at hd hd'
    rcases hd' with hd' | hd'
    · have e := hA d hd'; subst e
      rcases hd with hd | hd
      · have := mem_sdiag.1 (h1 hd); dsimp only at this; omega
      · have := mem_sdiag.1 (h2 hd); dsimp only at this; omega
    · have e := hB d hd'; subst e
      rcases hd with hd | hd
      · have := mem_sdiag.1 (h1 hd); dsimp only at this; omega
      · have := mem_sdiag.1 (h2 hd); dsimp only at this; omega
  show (T1 ∪ T2 ∪ ((if a + 1 < k then {(a, k)} else ∅) ∪ (if k + 1 < b then {(k, b)} else ∅))).card = _
  rw [card_union_of_disjoint dTAB, card_union_of_disjoint d12, card_union_of_disjoint dAB]
  split_ifs <;> simp only [card_singleton, card_empty] <;> omega

lemma pkI_card_tri : ∀ n a b : ℕ, b - a ≤ n → a < b → ∀ T : Finset (ℕ × ℕ), IsTri a b T →
    T.card = b - a - 2 := by
  intro n
  induction n with
  | zero => intro a b h1 h2; omega
  | succ n ih =>
    intro a b h1 h2 T hT
    by_cases hab : a + 1 < b
    · obtain ⟨k, hak, hkb, hA, hB⟩ := exists_apex hab hT
      have e := glue_split hT hak hkb hA hB
      have hL := left_isTri hT hak hkb hA hB
      have hR := right_isTri hT hak hkb hA hB
      have c1 := ih a k (by omega) hak _ hL
      have c2 := ih k b (by omega) hkb _ hR
      rw [← e, pkI_card_glue hak hkb hL.1 hR.1, c1, c2]
      split_ifs <;> omega
    · have hs : T = ∅ := by
        refine eq_empty_of_forall_notMem fun d hd => ?_
        have := mem_sdiag.1 (hT.1 hd)
        omega
      rw [hs, card_empty]
      omega

/-- `sorry` (3c-b). Orders below `#shifted` vanish identically (each shifted diagonal contributes `e^{≥1}`). -/
theorem AP_eq_zero_of_small {N : ℕ} (hN : 4 ≤ N) (m : ℕ) (hm : (oddDiagonals N).card + m < N - 3) :
    AP R N m = 0 := by
  rw [AP, map_sum]
  refine sum_eq_zero fun T hT => ?_
  have hTd : T ⊆ diagonals N := (mem_triangulations.1 hT).1
  have hcard : T.card = N - 3 := by
    have h := pkI_card_tri N 1 N (by omega) (by omega) T
      (mem_tri.1 (by rw [← triangulations_eq_tri]; exact hT))
    omega
  have hsub : T.filter (fun d => ¬ shiftSign d ≠ 0) ⊆ oddDiagonals N := fun d hd =>
    pkI_sign_zero (hTd (mem_filter.1 hd).1) (not_not.1 (mem_filter.1 hd).2)
  have hsplit : (T.filter (fun d => shiftSign d ≠ 0)).card + (T.filter (fun d => ¬ shiftSign d ≠ 0)).card =
      T.card := card_filter_add_card_filter_not _
  have hle := card_le_card hsub
  have hprod : ∏ d ∈ T.filter (fun d => shiftSign d ≠ 0), shiftSeriesP R d =
      PowerSeries.X ^ (T.filter (fun d => shiftSign d ≠ 0)).card *
        ∏ d ∈ T.filter (fun d => shiftSign d ≠ 0),
          PowerSeries.mk (fun k => ((shiftSign d : ℤ) : MvPolynomial (ℕ × ℕ) R) ^ (k + 1) * (-X d) ^ k) := by
    rw [← prod_const, ← prod_mul_distrib]
    rfl
  rw [hprod, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_neg (by omega), mul_zero]

lemma pkI_zeroAt_X (c d : ℕ × ℕ) : zeroAt R c (X d) = if d = c then 0 else X d := by
  rw [zeroAt, aeval_X]

lemma pkI_sub_zeroAt (c : ℕ × ℕ) (P : MvPolynomial (ℕ × ℕ) R) : X c ∣ P - zeroAt R c P := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [zeroAt, aeval_C, algebraMap_eq, sub_self]
    exact dvd_zero _
  | add p q hp hq =>
    rw [map_add, add_sub_add_comm]
    exact dvd_add hp hq
  | mul_X p n hp =>
    rw [map_mul, pkI_zeroAt_X]
    split_ifs with h
    · rw [mul_zero, sub_zero, h]
      exact dvd_mul_left _ _
    · rw [← sub_mul]
      exact dvd_mul_of_dvd_left hp _

/-- `sorry` (3c-b). **Z26 Lemma 3.1, numerator form**: a polynomial with `zeroAt C P = 0` for every `C ∈ S` is
divisible by `∏_{C∈S} X_C` (distinct variables are pairwise non-associated primes). -/
theorem prod_X_dvd_of_zeroAt [IsDomain R] (S : Finset (ℕ × ℕ)) (P : MvPolynomial (ℕ × ℕ) R)
    (h : ∀ C ∈ S, zeroAt R C P = 0) : (∏ C ∈ S, X C) ∣ P := by
  induction S using Finset.induction_on generalizing P with
  | empty =>
    rw [prod_empty]
    exact one_dvd _
  | insert a s ha ih =>
    obtain ⟨Q, hQ⟩ := ih P (fun c hc => h c (mem_insert_of_mem hc))
    have hz : zeroAt R a Q = 0 := by
      have h1 := h a (mem_insert_self a s)
      rw [hQ, map_mul, map_prod] at h1
      have h2 : ∏ c ∈ s, zeroAt R a (X c) = ∏ c ∈ s, X c := prod_congr rfl fun c hc => by
        rw [pkI_zeroAt_X, if_neg (fun e : c = a => ha (e ▸ hc))]
      rw [h2] at h1
      exact (mul_eq_zero.1 h1).resolve_left (prod_ne_zero_iff.2 fun c _ => X_ne_zero c)
    obtain ⟨Q', hQ'⟩ : X a ∣ Q := by
      have h3 := pkI_sub_zeroAt a Q
      rwa [hz, sub_zero] at h3
    rw [prod_insert ha, hQ, hQ']
    exact ⟨Q', by ring⟩

/-! ### pkgSplit helpers: the chord-split bijection (generic over a parity class of diagonals) -/

lemma pkSp_vtx {N x : ℕ} (h1 : 1 ≤ x) (h2 : x ≤ 2 * N) : vtx N x = if x ≤ N then x else x - N := by
  split_ifs with h
  · exact vtx_of_mem h1 h
  · exact vtx_of_gt (by omega) h2

/-- `relab` in coordinates: no wrap, one endpoint wraps, both wrap. -/
lemma pkSp_spec {N b a c x y : ℕ} (hb : 1 ≤ b) (ha : 1 ≤ a) (hac : a < c) (hca : c < a + N)
    (hc : c + b - 1 ≤ 2 * N) (he : relab N b (a, c) = (x, y)) :
    (c + b - 1 ≤ N ∧ x = a + b - 1 ∧ y = c + b - 1) ∨
    (a + b - 1 ≤ N ∧ N < c + b - 1 ∧ x = c + b - 1 - N ∧ y = a + b - 1) ∨
    (N < a + b - 1 ∧ x = a + b - 1 - N ∧ y = c + b - 1 - N) := by
  unfold relab npair at he
  dsimp only at he
  by_cases h1 : c + b - 1 ≤ N
  · rw [vtx_of_mem (by omega) (by omega), vtx_of_mem (by omega) h1] at he
    simp only [Prod.mk.injEq, min_def, max_def] at he
    split_ifs at he <;> omega
  · by_cases h2 : a + b - 1 ≤ N
    · rw [vtx_of_mem (by omega) h2, vtx_of_gt (by omega) hc] at he
      simp only [Prod.mk.injEq, min_def, max_def] at he
      split_ifs at he <;> omega
    · rw [vtx_of_gt (by omega) (by omega), vtx_of_gt (by omega) hc] at he
      simp only [Prod.mk.injEq, min_def, max_def] at he
      split_ifs at he <;> omega

/-- `pkSp_spec` read on the components of `relab`. -/
lemma pkSp_spec2 {N b a c : ℕ} (hb : 1 ≤ b) (ha : 1 ≤ a) (hac : a < c) (hca : c < a + N)
    (hc : c + b - 1 ≤ 2 * N) :
    (c + b - 1 ≤ N ∧ (relab N b (a, c)).1 = a + b - 1 ∧ (relab N b (a, c)).2 = c + b - 1) ∨
    (a + b - 1 ≤ N ∧ N < c + b - 1 ∧ (relab N b (a, c)).1 = c + b - 1 - N ∧
      (relab N b (a, c)).2 = a + b - 1) ∨
    (N < a + b - 1 ∧ (relab N b (a, c)).1 = a + b - 1 - N ∧ (relab N b (a, c)).2 = c + b - 1 - N) :=
  pkSp_spec hb ha hac hca hc rfl

/-- Diagonals of the `n`-gon whose length parity satisfies `Q` (all: `Q = True`; odd: `Q = (· = 1)`). -/
def pkSp_S (Q : ℕ → Prop) [DecidablePred Q] (n : ℕ) : Finset (ℕ × ℕ) :=
  (diagonals n).filter (fun d => Q ((d.2 - d.1) % 2))

lemma pkSp_mem_S {Q : ℕ → Prop} [DecidablePred Q] {n : ℕ} {d : ℕ × ℕ} :
    d ∈ pkSp_S Q n ↔ d ∈ diagonals n ∧ Q ((d.2 - d.1) % 2) := by
  unfold pkSp_S; rw [mem_filter]

/-- Maximal pairwise non-crossing subsets of `S` (`IsTriangulation n = pkSp_IsMax (diagonals n)`,
`IsQuadrangulation N = pkSp_IsMax (oddDiagonals N)`, both by definition). -/
def pkSp_IsMax (S T : Finset (ℕ × ℕ)) : Prop :=
  T ⊆ S ∧ (∀ p ∈ T, ∀ q ∈ T, ¬ Crosses p q) ∧ ∀ d ∈ S, d ∉ T → ∃ p ∈ T, Crosses p d

/-- Strictly inside the chord `(i, j)`. -/
def pkSp_In (i j : ℕ) (d : ℕ × ℕ) : Prop := i ≤ d.1 ∧ d.2 ≤ j ∧ ¬ (d.1 = i ∧ d.2 = j)

/-- On the other side of the chord `(i, j)`. -/
def pkSp_Out (i j : ℕ) (d : ℕ × ℕ) : Prop :=
  (d.2 ≤ i ∨ j ≤ d.1 ∨ (d.1 ≤ i ∧ j ≤ d.2)) ∧ ¬ (d.1 = i ∧ d.2 = j)

lemma pkSp_mapL {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N) (hne : ¬ (i = 1 ∧ j = N))
    {d : ℕ × ℕ} (hd : d ∈ diagonals (j - i + 1)) :
    relab N i d ∈ diagonals N ∧ pkSp_In i j (relab N i d) ∧
      ((relab N i d).2 - (relab N i d).1) % 2 = (d.2 - d.1) % 2 := by
  obtain ⟨a, c⟩ := d
  rw [mem_diagonals] at hd; dsimp only at hd
  have h := pkSp_spec2 (N := N) (b := i) (a := a) (c := c) (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [mem_diagonals]; unfold pkSp_In; try dsimp only
  omega

lemma pkSp_mapR {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N) (hne : ¬ (i = 1 ∧ j = N))
    (hE : N % 2 = 0) {d : ℕ × ℕ} (hd : d ∈ diagonals (N - j + i + 1)) :
    relab N j d ∈ diagonals N ∧ pkSp_Out i j (relab N j d) ∧
      ((relab N j d).2 - (relab N j d).1) % 2 = (d.2 - d.1) % 2 := by
  obtain ⟨a, c⟩ := d
  rw [mem_diagonals] at hd; dsimp only at hd
  have h := pkSp_spec2 (N := N) (b := j) (a := a) (c := c) (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [mem_diagonals]; unfold pkSp_Out; try dsimp only
  omega

lemma pkSp_surjL {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N)
    {d : ℕ × ℕ} (hd : d ∈ diagonals N) (hin : pkSp_In i j d) :
    ∃ d' ∈ diagonals (j - i + 1), relab N i d' = d := by
  obtain ⟨c, e⟩ := d
  rw [mem_diagonals] at hd; unfold pkSp_In at hin; dsimp only at hd hin
  refine ⟨(c - i + 1, e - i + 1), ?_, ?_⟩
  · rw [mem_diagonals]; dsimp only; omega
  · have h := pkSp_spec2 (N := N) (b := i) (a := c - i + 1) (c := e - i + 1) (by omega) (by omega) (by omega)
      (by omega) (by omega)
    exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)

lemma pkSp_surjR {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N)
    {d : ℕ × ℕ} (hd : d ∈ diagonals N) (hout : pkSp_Out i j d) :
    ∃ d' ∈ diagonals (N - j + i + 1), relab N j d' = d := by
  obtain ⟨c, e⟩ := d
  rw [mem_diagonals] at hd; unfold pkSp_Out at hout; dsimp only at hd hout
  by_cases h1 : j ≤ c
  · refine ⟨(c - j + 1, e - j + 1), ?_, ?_⟩
    · rw [mem_diagonals]; dsimp only; omega
    · have h := pkSp_spec2 (N := N) (b := j) (a := c - j + 1) (c := e - j + 1) (by omega) (by omega) (by omega)
        (by omega) (by omega)
      exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)
  · by_cases h2 : e ≤ i
    · refine ⟨(c + N - j + 1, e + N - j + 1), ?_, ?_⟩
      · rw [mem_diagonals]; dsimp only; omega
      · have h := pkSp_spec2 (N := N) (b := j) (a := c + N - j + 1) (c := e + N - j + 1) (by omega) (by omega) (by omega)
          (by omega) (by omega)
        exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)
    · refine ⟨(e - j + 1, c + N - j + 1), ?_, ?_⟩
      · rw [mem_diagonals]; dsimp only; omega
      · have h := pkSp_spec2 (N := N) (b := j) (a := e - j + 1) (c := c + N - j + 1) (by omega) (by omega) (by omega)
          (by omega) (by omega)
        exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)

/-- Injectivity and crossing, for any relabelling `b ≥ 1` of the diagonals of an `n`-gon with `n + b − 1 ≤ 2N`. -/
lemma pkSp_inj {N b n : ℕ} (hb : 1 ≤ b) (hn : n + b - 1 ≤ 2 * N) (hnN : n ≤ N) {d d' : ℕ × ℕ} (hd : d ∈ diagonals n)
    (hd' : d' ∈ diagonals n) (h : relab N b d = relab N b d') : d = d' := by
  obtain ⟨a, c⟩ := d
  obtain ⟨a', c'⟩ := d'
  rw [mem_diagonals] at hd hd'; dsimp only at hd hd'
  have h1 := pkSp_spec2 (N := N) (b := b) (a := a) (c := c) (by omega) (by omega) (by omega) (by omega) (by omega)
  have h2 := pkSp_spec2 (N := N) (b := b) (a := a') (c := c') (by omega) (by omega) (by omega) (by omega)
    (by omega)
  have e1 := congrArg Prod.fst h
  have e2 := congrArg Prod.snd h
  exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)

lemma pkSp_cross {N b n : ℕ} (hb : 1 ≤ b) (hn : n + b - 1 ≤ 2 * N) (hnN : n ≤ N) {d d' : ℕ × ℕ}
    (hd : d ∈ diagonals n) (hd' : d' ∈ diagonals n) :
    Crosses (relab N b d) (relab N b d') ↔ Crosses d d' := by
  obtain ⟨a, c⟩ := d
  obtain ⟨a', c'⟩ := d'
  rw [mem_diagonals] at hd hd'; dsimp only at hd hd'
  have h1 := pkSp_spec2 (N := N) (b := b) (a := a) (c := c) (by omega) (by omega) (by omega) (by omega) (by omega)
  have h2 := pkSp_spec2 (N := N) (b := b) (a := a') (c := c') (by omega) (by omega) (by omega) (by omega)
    (by omega)
  simp only [Crosses]
  omega

lemma pkSp_cross_symm {p q : ℕ × ℕ} : Crosses p q ↔ Crosses q p := by
  simp only [Crosses]; omega

/-- Every diagonal is the chord, crosses it, or lies on one side. -/
lemma pkSp_part {N i j : ℕ} {d : ℕ × ℕ} (hd : d ∈ diagonals N) :
    d = (i, j) ∨ Crosses d (i, j) ∨ pkSp_In i j d ∨ pkSp_Out i j d := by
  obtain ⟨c, e⟩ := d
  rw [mem_diagonals] at hd
  simp only [Prod.mk.injEq, Crosses, pkSp_In, pkSp_Out]
  omega

lemma pkSp_In_nc {i j : ℕ} {d : ℕ × ℕ} (h : pkSp_In i j d) : ¬ Crosses d (i, j) := by
  unfold pkSp_In at h; simp only [Crosses]; omega

lemma pkSp_Out_nc {i j : ℕ} {d : ℕ × ℕ} (h : pkSp_Out i j d) : ¬ Crosses d (i, j) := by
  unfold pkSp_Out at h; simp only [Crosses]; omega

lemma pkSp_In_Out_nc {i j : ℕ} {d q : ℕ × ℕ} (hd : d.1 < d.2) (hq : q.1 < q.2) (h : pkSp_In i j d)
    (h' : pkSp_Out i j q) : ¬ Crosses d q := by
  unfold pkSp_In at h; unfold pkSp_Out at h'; simp only [Crosses]; omega

lemma pkSp_In_ne {i j : ℕ} {d : ℕ × ℕ} (h : pkSp_In i j d) : d ≠ (i, j) := by
  rintro rfl; exact h.2.2 ⟨rfl, rfl⟩

lemma pkSp_Out_ne {i j : ℕ} {d : ℕ × ℕ} (h : pkSp_Out i j d) : d ≠ (i, j) := by
  rintro rfl; exact h.2 ⟨rfl, rfl⟩

lemma pkSp_In_not_Out {i j : ℕ} {d : ℕ × ℕ} (hd : d.1 < d.2) (h : pkSp_In i j d) : ¬ pkSp_Out i j d := by
  unfold pkSp_In at h; unfold pkSp_Out; omega

/-- A diagonal crossing one on a side, but not the chord, lies on that side. -/
lemma pkSp_In_of_cross {i j : ℕ} {p d : ℕ × ℕ} (hp : p.1 < p.2) (hd : pkSp_In i j d) (hc : Crosses p d)
    (hpC : ¬ Crosses p (i, j)) (hne : p ≠ (i, j)) : pkSp_In i j p := by
  obtain ⟨c, e⟩ := p
  simp only [ne_eq, Prod.mk.injEq] at hne
  unfold pkSp_In at hd ⊢; simp only [Crosses] at hc hpC; dsimp only at *
  omega

lemma pkSp_Out_of_cross {i j : ℕ} {p d : ℕ × ℕ} (hp : p.1 < p.2) (hd : pkSp_Out i j d) (hc : Crosses p d)
    (hpC : ¬ Crosses p (i, j)) (hne : p ≠ (i, j)) : pkSp_Out i j p := by
  obtain ⟨c, e⟩ := p
  simp only [ne_eq, Prod.mk.injEq] at hne
  unfold pkSp_Out at hd ⊢; simp only [Crosses] at hc hpC; dsimp only at *
  omega

lemma pkSp_lt {n : ℕ} {d : ℕ × ℕ} (hd : d ∈ diagonals n) : d.1 < d.2 := by
  rw [mem_diagonals] at hd; omega

lemma pkSp_mapLQ {Q : ℕ → Prop} [DecidablePred Q] {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N)
    (hne : ¬ (i = 1 ∧ j = N)) {d : ℕ × ℕ} (hd : d ∈ pkSp_S Q (j - i + 1)) :
    relab N i d ∈ pkSp_S Q N ∧ pkSp_In i j (relab N i d) := by
  rw [pkSp_mem_S] at hd ⊢
  obtain ⟨h1, h2, h3⟩ := pkSp_mapL hi hij hjN hne hd.1
  exact ⟨⟨h1, by rw [h3]; exact hd.2⟩, h2⟩

lemma pkSp_mapRQ {Q : ℕ → Prop} [DecidablePred Q] {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N)
    (hne : ¬ (i = 1 ∧ j = N)) (hE : N % 2 = 0) {d : ℕ × ℕ} (hd : d ∈ pkSp_S Q (N - j + i + 1)) :
    relab N j d ∈ pkSp_S Q N ∧ pkSp_Out i j (relab N j d) := by
  rw [pkSp_mem_S] at hd ⊢
  obtain ⟨h1, h2, h3⟩ := pkSp_mapR hi hij hjN hne hE hd.1
  exact ⟨⟨h1, by rw [h3]; exact hd.2⟩, h2⟩

lemma pkSp_surjLQ {Q : ℕ → Prop} [DecidablePred Q] {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N)
    (hne : ¬ (i = 1 ∧ j = N)) {d : ℕ × ℕ} (hd : d ∈ pkSp_S Q N) (hin : pkSp_In i j d) :
    ∃ d' ∈ pkSp_S Q (j - i + 1), relab N i d' = d := by
  rw [pkSp_mem_S] at hd
  obtain ⟨d', hd', rfl⟩ := pkSp_surjL hi hij hjN hd.1 hin
  obtain ⟨-, -, h3⟩ := pkSp_mapL (N := N) hi hij hjN hne hd'
  exact ⟨d', pkSp_mem_S.2 ⟨hd', by rw [← h3]; exact hd.2⟩, rfl⟩

lemma pkSp_surjRQ {Q : ℕ → Prop} [DecidablePred Q] {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N)
    (hne : ¬ (i = 1 ∧ j = N)) (hE : N % 2 = 0) {d : ℕ × ℕ} (hd : d ∈ pkSp_S Q N) (hout : pkSp_Out i j d) :
    ∃ d' ∈ pkSp_S Q (N - j + i + 1), relab N j d' = d := by
  rw [pkSp_mem_S] at hd
  obtain ⟨d', hd', rfl⟩ := pkSp_surjR hi hij hjN hd.1 hout
  obtain ⟨-, -, h3⟩ := pkSp_mapR (N := N) hi hij hjN hne hE hd'
  exact ⟨d', pkSp_mem_S.2 ⟨hd', by rw [← h3]; exact hd.2⟩, rfl⟩

/-- The glued set: the chord, the left child relabelled by `relab N i`, the right child by `relab N j`. -/
def pkSp_glue (N i j : ℕ) (T1 T2 : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  insert (i, j) (T1.image (relab N i) ∪ T2.image (relab N j))

lemma pkSp_mem_glue_L {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N) (hne : ¬ (i = 1 ∧ j = N))
    (hE : N % 2 = 0) {T1 T2 : Finset (ℕ × ℕ)} (h1 : T1 ⊆ diagonals (j - i + 1))
    (h2 : T2 ⊆ diagonals (N - j + i + 1)) {d : ℕ × ℕ} (hd : d ∈ diagonals (j - i + 1)) :
    relab N i d ∈ pkSp_glue N i j T1 T2 ↔ d ∈ T1 := by
  obtain ⟨hdN, hin, -⟩ := pkSp_mapL hi hij hjN hne hd
  rw [pkSp_glue, mem_insert, mem_union, mem_image, mem_image]
  constructor
  · rintro (h | ⟨d', hd', he⟩ | ⟨d', hd', he⟩)
    · exact absurd h (pkSp_In_ne hin)
    · rwa [← pkSp_inj (N := N) (b := i) (n := j - i + 1) (by omega) (by omega) (by omega) (h1 hd') hd he]
    · exfalso
      obtain ⟨-, hout, -⟩ := pkSp_mapR hi hij hjN hne hE (h2 hd')
      rw [he] at hout
      exact pkSp_In_not_Out (pkSp_lt hdN) hin hout
  · intro h; exact Or.inr (Or.inl ⟨d, h, rfl⟩)

lemma pkSp_mem_glue_R {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N) (hne : ¬ (i = 1 ∧ j = N))
    (hE : N % 2 = 0) {T1 T2 : Finset (ℕ × ℕ)} (h1 : T1 ⊆ diagonals (j - i + 1))
    (h2 : T2 ⊆ diagonals (N - j + i + 1)) {d : ℕ × ℕ} (hd : d ∈ diagonals (N - j + i + 1)) :
    relab N j d ∈ pkSp_glue N i j T1 T2 ↔ d ∈ T2 := by
  obtain ⟨hdN, hout, -⟩ := pkSp_mapR hi hij hjN hne hE hd
  rw [pkSp_glue, mem_insert, mem_union, mem_image, mem_image]
  constructor
  · rintro (h | ⟨d', hd', he⟩ | ⟨d', hd', he⟩)
    · exact absurd h (pkSp_Out_ne hout)
    · exfalso
      obtain ⟨-, hin, -⟩ := pkSp_mapL hi hij hjN hne (h1 hd')
      rw [he] at hin
      exact pkSp_In_not_Out (pkSp_lt hdN) hin hout
    · rwa [← pkSp_inj (N := N) (b := j) (n := N - j + i + 1) (by omega) (by omega) (by omega) (h2 hd') hd he]
  · intro h; exact Or.inr (Or.inr ⟨d, h, rfl⟩)

/-- Nothing in a glued set crosses the chord. -/
lemma pkSp_glue_nc {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N) (hne : ¬ (i = 1 ∧ j = N))
    (hE : N % 2 = 0) {T1 T2 : Finset (ℕ × ℕ)} (h1 : T1 ⊆ diagonals (j - i + 1))
    (h2 : T2 ⊆ diagonals (N - j + i + 1)) {p : ℕ × ℕ} (hp : p ∈ pkSp_glue N i j T1 T2) :
    ¬ Crosses p (i, j) := by
  rw [pkSp_glue, mem_insert, mem_union, mem_image, mem_image] at hp
  rcases hp with rfl | ⟨p', hp', rfl⟩ | ⟨p', hp', rfl⟩
  · simp only [Crosses]; omega
  · exact pkSp_In_nc (pkSp_mapL hi hij hjN hne (h1 hp')).2.1
  · exact pkSp_Out_nc (pkSp_mapR hi hij hjN hne hE (h2 hp')).2.1

/-- Gluing maximal sets of the two children gives a maximal set through the chord. -/
lemma pkSp_glue_max {Q : ℕ → Prop} [DecidablePred Q] {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N)
    (hne : ¬ (i = 1 ∧ j = N)) (hE : N % 2 = 0) (hQC : (i, j) ∈ pkSp_S Q N) {T1 T2 : Finset (ℕ × ℕ)}
    (h1 : pkSp_IsMax (pkSp_S Q (j - i + 1)) T1) (h2 : pkSp_IsMax (pkSp_S Q (N - j + i + 1)) T2) :
    pkSp_IsMax (pkSp_S Q N) (pkSp_glue N i j T1 T2) := by
  have hL : T1 ⊆ diagonals (j - i + 1) := fun d hd => (pkSp_mem_S.1 (h1.1 hd)).1
  have hR : T2 ⊆ diagonals (N - j + i + 1) := fun d hd => (pkSp_mem_S.1 (h2.1 hd)).1
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    rw [pkSp_glue, mem_insert, mem_union, mem_image, mem_image] at hd
    rcases hd with rfl | ⟨d', hd', rfl⟩ | ⟨d', hd', rfl⟩
    · exact hQC
    · exact (pkSp_mapLQ hi hij hjN hne (h1.1 hd')).1
    · exact (pkSp_mapRQ hi hij hjN hne hE (h2.1 hd')).1
  · intro p hp q hq
    have hpc := pkSp_glue_nc hi hij hjN hne hE hL hR hp
    have hqc := pkSp_glue_nc hi hij hjN hne hE hL hR hq
    rw [pkSp_glue, mem_insert, mem_union, mem_image, mem_image] at hp hq
    rcases hp with rfl | ⟨p', hp', rfl⟩ | ⟨p', hp', rfl⟩
    · exact fun h => hqc (pkSp_cross_symm.1 h)
    · rcases hq with rfl | ⟨q', hq', rfl⟩ | ⟨q', hq', rfl⟩
      · exact hpc
      · rw [pkSp_cross (N := N) (b := i) (n := j - i + 1) (by omega) (by omega) (by omega) (hL hp') (hL hq')]
        exact h1.2.1 _ hp' _ hq'
      · obtain ⟨hpN, hin, -⟩ := pkSp_mapL hi hij hjN hne (hL hp')
        obtain ⟨hqN, hout, -⟩ := pkSp_mapR hi hij hjN hne hE (hR hq')
        exact pkSp_In_Out_nc (pkSp_lt hpN) (pkSp_lt hqN) hin hout
    · rcases hq with rfl | ⟨q', hq', rfl⟩ | ⟨q', hq', rfl⟩
      · exact hpc
      · obtain ⟨hqN, hin, -⟩ := pkSp_mapL hi hij hjN hne (hL hq')
        obtain ⟨hpN, hout, -⟩ := pkSp_mapR hi hij hjN hne hE (hR hp')
        exact fun h => pkSp_In_Out_nc (pkSp_lt hqN) (pkSp_lt hpN) hin hout (pkSp_cross_symm.1 h)
      · rw [pkSp_cross (N := N) (b := j) (n := N - j + i + 1) (by omega) (by omega) (by omega) (hR hp') (hR hq')]
        exact h2.2.1 _ hp' _ hq'
  · intro d hd hnot
    have hdN := (pkSp_mem_S.1 hd).1
    rcases pkSp_part (i := i) (j := j) hdN with rfl | hc | hin | hout
    · exact absurd (mem_insert_self _ _) hnot
    · exact ⟨(i, j), mem_insert_self _ _, pkSp_cross_symm.1 hc⟩
    · obtain ⟨d', hd', rfl⟩ := pkSp_surjLQ hi hij hjN hne hd hin
      have hd'L := (pkSp_mem_S.1 hd').1
      have hn1 : d' ∉ T1 := fun h => hnot ((pkSp_mem_glue_L hi hij hjN hne hE hL hR hd'L).2 h)
      obtain ⟨p', hp', hc⟩ := h1.2.2 d' hd' hn1
      refine ⟨relab N i p', (pkSp_mem_glue_L hi hij hjN hne hE hL hR (hL hp')).2 hp', ?_⟩
      rwa [pkSp_cross (N := N) (b := i) (n := j - i + 1) (by omega) (by omega) (by omega) (hL hp') hd'L]
    · obtain ⟨d', hd', rfl⟩ := pkSp_surjRQ hi hij hjN hne hE hd hout
      have hd'R := (pkSp_mem_S.1 hd').1
      have hn2 : d' ∉ T2 := fun h => hnot ((pkSp_mem_glue_R hi hij hjN hne hE hL hR hd'R).2 h)
      obtain ⟨p', hp', hc⟩ := h2.2.2 d' hd' hn2
      refine ⟨relab N j p', (pkSp_mem_glue_R hi hij hjN hne hE hL hR (hR hp')).2 hp', ?_⟩
      rwa [pkSp_cross (N := N) (b := j) (n := N - j + i + 1) (by omega) (by omega) (by omega) (hR hp') hd'R]

/-- The left restriction of a maximal set through the chord is maximal. -/
lemma pkSp_left_max {Q : ℕ → Prop} [DecidablePred Q] {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N)
    (hne : ¬ (i = 1 ∧ j = N)) {T : Finset (ℕ × ℕ)} (hT : pkSp_IsMax (pkSp_S Q N) T) (hC : (i, j) ∈ T) :
    pkSp_IsMax (pkSp_S Q (j - i + 1)) ((pkSp_S Q (j - i + 1)).filter (fun d => relab N i d ∈ T)) := by
  refine ⟨filter_subset _ _, ?_, ?_⟩
  · intro p hp q hq
    rw [mem_filter] at hp hq
    rw [← pkSp_cross (N := N) (b := i) (n := j - i + 1) (by omega) (by omega) (by omega)
      (pkSp_mem_S.1 hp.1).1 (pkSp_mem_S.1 hq.1).1]
    exact hT.2.1 _ hp.2 _ hq.2
  · intro d hd hnot
    have hnT : relab N i d ∉ T := fun h => hnot (mem_filter.2 ⟨hd, h⟩)
    obtain ⟨hdN, hin⟩ := pkSp_mapLQ hi hij hjN hne hd
    obtain ⟨p, hp, hc⟩ := hT.2.2 _ hdN hnT
    have hpN := hT.1 hp
    have hne' : p ≠ (i, j) := by
      rintro rfl; exact pkSp_In_nc hin (pkSp_cross_symm.1 hc)
    have hpin := pkSp_In_of_cross (pkSp_lt (pkSp_mem_S.1 hpN).1) hin hc (hT.2.1 _ hp _ hC) hne'
    obtain ⟨p', hp', rfl⟩ := pkSp_surjLQ hi hij hjN hne hpN hpin
    refine ⟨p', mem_filter.2 ⟨hp', hp⟩, ?_⟩
    rwa [← pkSp_cross (N := N) (b := i) (n := j - i + 1) (by omega) (by omega) (by omega)
      (pkSp_mem_S.1 hp').1 (pkSp_mem_S.1 hd).1]

lemma pkSp_right_max {Q : ℕ → Prop} [DecidablePred Q] {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N)
    (hne : ¬ (i = 1 ∧ j = N)) (hE : N % 2 = 0) {T : Finset (ℕ × ℕ)} (hT : pkSp_IsMax (pkSp_S Q N) T)
    (hC : (i, j) ∈ T) :
    pkSp_IsMax (pkSp_S Q (N - j + i + 1)) ((pkSp_S Q (N - j + i + 1)).filter (fun d => relab N j d ∈ T)) := by
  refine ⟨filter_subset _ _, ?_, ?_⟩
  · intro p hp q hq
    rw [mem_filter] at hp hq
    rw [← pkSp_cross (N := N) (b := j) (n := N - j + i + 1) (by omega) (by omega) (by omega)
      (pkSp_mem_S.1 hp.1).1 (pkSp_mem_S.1 hq.1).1]
    exact hT.2.1 _ hp.2 _ hq.2
  · intro d hd hnot
    have hnT : relab N j d ∉ T := fun h => hnot (mem_filter.2 ⟨hd, h⟩)
    obtain ⟨hdN, hout⟩ := pkSp_mapRQ hi hij hjN hne hE hd
    obtain ⟨p, hp, hc⟩ := hT.2.2 _ hdN hnT
    have hpN := hT.1 hp
    have hne' : p ≠ (i, j) := by
      rintro rfl; exact pkSp_Out_nc hout (pkSp_cross_symm.1 hc)
    have hpout := pkSp_Out_of_cross (pkSp_lt (pkSp_mem_S.1 hpN).1) hout hc (hT.2.1 _ hp _ hC) hne'
    obtain ⟨p', hp', rfl⟩ := pkSp_surjRQ hi hij hjN hne hE hpN hpout
    refine ⟨p', mem_filter.2 ⟨hp', hp⟩, ?_⟩
    rwa [← pkSp_cross (N := N) (b := j) (n := N - j + i + 1) (by omega) (by omega) (by omega)
      (pkSp_mem_S.1 hp').1 (pkSp_mem_S.1 hd).1]

/-- A maximal set through the chord is the glue of its two restrictions. -/
lemma pkSp_glue_split {Q : ℕ → Prop} [DecidablePred Q] {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N)
    (hne : ¬ (i = 1 ∧ j = N)) (hE : N % 2 = 0) {T : Finset (ℕ × ℕ)} (hT : pkSp_IsMax (pkSp_S Q N) T)
    (hC : (i, j) ∈ T) :
    pkSp_glue N i j ((pkSp_S Q (j - i + 1)).filter (fun d => relab N i d ∈ T))
      ((pkSp_S Q (N - j + i + 1)).filter (fun d => relab N j d ∈ T)) = T := by
  ext p
  rw [pkSp_glue, mem_insert, mem_union, mem_image, mem_image]
  constructor
  · rintro (rfl | ⟨p', hp', rfl⟩ | ⟨p', hp', rfl⟩)
    · exact hC
    · exact (mem_filter.1 hp').2
    · exact (mem_filter.1 hp').2
  · intro hp
    have hpN := hT.1 hp
    rcases pkSp_part (i := i) (j := j) (pkSp_mem_S.1 hpN).1 with h | hc | hin | hout
    · exact Or.inl h
    · exact absurd hc (hT.2.1 _ hp _ hC)
    · obtain ⟨p', hp', rfl⟩ := pkSp_surjLQ hi hij hjN hne hpN hin
      exact Or.inr (Or.inl ⟨p', mem_filter.2 ⟨hp', hp⟩, rfl⟩)
    · obtain ⟨p', hp', rfl⟩ := pkSp_surjRQ hi hij hjN hne hE hpN hout
      exact Or.inr (Or.inr ⟨p', mem_filter.2 ⟨hp', hp⟩, rfl⟩)

/-- **The chord-split bijection, generic** (R12-P3c §5 C5 item 4): for any family `tr n` of the maximal
non-crossing subsets of a parity class of diagonals (triangulations, quadrangulations), sets through the chord
`(i, j)` are the glued pairs of sets of the two children `P_L = i..j`, `P_R = j..N,1..i`. -/
theorem pkSp_sum_split {M : Type*} [AddCommMonoid M] {Q : ℕ → Prop} [DecidablePred Q]
    (tr : ℕ → Finset (Finset (ℕ × ℕ))) (htr : ∀ n T, T ∈ tr n ↔ pkSp_IsMax (pkSp_S Q n) T)
    {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N) (hne : ¬ (i = 1 ∧ j = N)) (hE : N % 2 = 0)
    (hQC : (i, j) ∈ pkSp_S Q N) (g : Finset (ℕ × ℕ) → M) :
    ∑ T ∈ (tr N).filter (fun T => (i, j) ∈ T), g T =
      ∑ x ∈ tr (j - i + 1) ×ˢ tr (N - j + i + 1), g (pkSp_glue N i j x.1 x.2) := by
  refine (sum_nbij' (fun x => pkSp_glue N i j x.1 x.2)
    (fun T => ((pkSp_S Q (j - i + 1)).filter (fun d => relab N i d ∈ T),
      (pkSp_S Q (N - j + i + 1)).filter (fun d => relab N j d ∈ T))) ?_ ?_ ?_ ?_ ?_).symm
  · rintro ⟨T1, T2⟩ hx
    simp only [coe_product, Set.mem_prod, mem_coe, coe_filter, Set.mem_setOf_eq, mem_filter, mem_product,
      htr] at hx ⊢
    exact ⟨pkSp_glue_max hi hij hjN hne hE hQC hx.1 hx.2, mem_insert_self _ _⟩
  · intro T hT
    simp only [coe_product, Set.mem_prod, mem_coe, coe_filter, Set.mem_setOf_eq, mem_filter, mem_product,
      htr] at hT ⊢
    exact ⟨pkSp_left_max hi hij hjN hne hT.1 hT.2, pkSp_right_max hi hij hjN hne hE hT.1 hT.2⟩
  · rintro ⟨T1, T2⟩ hx
    simp only [coe_product, Set.mem_prod, mem_coe, mem_product, htr] at hx
    have hL : T1 ⊆ diagonals (j - i + 1) := fun d hd => (pkSp_mem_S.1 (hx.1.1 hd)).1
    have hR : T2 ⊆ diagonals (N - j + i + 1) := fun d hd => (pkSp_mem_S.1 (hx.2.1 hd)).1
    simp only [Prod.mk.injEq]
    constructor
    · ext d
      rw [mem_filter]
      constructor
      · rintro ⟨hd, h⟩
        exact (pkSp_mem_glue_L hi hij hjN hne hE hL hR (pkSp_mem_S.1 hd).1).1 h
      · intro h
        exact ⟨hx.1.1 h, (pkSp_mem_glue_L hi hij hjN hne hE hL hR (hL h)).2 h⟩
    · ext d
      rw [mem_filter]
      constructor
      · rintro ⟨hd, h⟩
        exact (pkSp_mem_glue_R hi hij hjN hne hE hL hR (pkSp_mem_S.1 hd).1).1 h
      · intro h
        exact ⟨hx.2.1 h, (pkSp_mem_glue_R hi hij hjN hne hE hL hR (hR h)).2 h⟩
  · intro T hT
    simp only [coe_filter, Set.mem_setOf_eq, mem_coe, mem_filter, htr] at hT
    exact pkSp_glue_split hi hij hjN hne hE hT.1 hT.2
  · intro _ _; rfl

lemma pkSp_tri_iff (n : ℕ) (T : Finset (ℕ × ℕ)) :
    T ∈ triangulations n ↔ pkSp_IsMax (pkSp_S (fun _ => True) n) T := by
  have h : pkSp_S (fun _ => True) n = diagonals n := filter_true_of_mem fun _ _ => trivial
  rw [h, mem_triangulations]
  exact Iff.rfl

lemma pkSp_odd_eq (n : ℕ) : oddDiagonals n = pkSp_S (fun r => r = 1) n := rfl

/-! ### pkgSplit helpers: the power-series side of `AP_residue` -/

/-- The summand of `AP`. -/
noncomputable def pkSp_F (R : Type*) [CommRing R] (n : ℕ) (T : Finset (ℕ × ℕ)) :
    PowerSeries (MvPolynomial (ℕ × ℕ) R) :=
  PowerSeries.C (∏ d ∈ oddDiagonals n \ T, X d) *
    ∏ d ∈ T.filter (fun d => shiftSign d ≠ 0), shiftSeriesP R d

lemma pkSp_shiftSign_odd {d : ℕ × ℕ} (hd : d.1 ≤ d.2) (h : (d.2 - d.1) % 2 = 1) : shiftSign d = 0 := by
  unfold shiftSign; split_ifs <;> omega

lemma pkSp_sign_relab {N b n : ℕ} (hE : N % 2 = 0) (hb : 1 ≤ b) (hn : n + b - 1 ≤ 2 * N) (hnN : n ≤ N)
    {d : ℕ × ℕ} (hd : d ∈ diagonals n) : shiftSign (relab N b d) = (-1) ^ (b + 1) * shiftSign d := by
  obtain ⟨a, c⟩ := d
  rw [mem_diagonals] at hd; dsimp only at hd
  have h := pkSp_spec2 (N := N) (b := b) (a := a) (c := c) (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨k, hk | hk⟩ : ∃ k, b = 2 * k ∨ b = 2 * k + 1 := ⟨b / 2, by omega⟩
  · have hp : ((-1 : ℤ)) ^ (b + 1) = -1 := by
      rw [hk]; exact Odd.neg_one_pow ⟨k, rfl⟩
    rw [hp]; unfold shiftSign; dsimp only; split_ifs <;> omega
  · have hp : ((-1 : ℤ)) ^ (b + 1) = 1 := by
      rw [hk]; exact Even.neg_one_pow ⟨k + 1, by ring⟩
    rw [hp]; unfold shiftSign; dsimp only; split_ifs <;> omega

lemma pkSp_rescale_C (a b : MvPolynomial (ℕ × ℕ) R) :
    PowerSeries.rescale a (PowerSeries.C b) = PowerSeries.C b := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  split_ifs with h <;> simp [h]

lemma pkSp_map_sP (f : MvPolynomial (ℕ × ℕ) R →+* MvPolynomial (ℕ × ℕ) R) (d : ℕ × ℕ) (h : f (X d) = X d) :
    PowerSeries.map f (shiftSeriesP R d) = shiftSeriesP R d := by
  ext n
  rw [PowerSeries.coeff_map]
  rcases n with _ | n
  · simp [shiftSeriesP]
  · simp only [shiftSeriesP, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]
    simp [map_mul, map_pow, map_neg, h]

lemma pkSp_sP_relab (ρ : ℕ × ℕ → ℕ × ℕ) (σ : ℤ) (d : ℕ × ℕ) (h : shiftSign (ρ d) = σ * shiftSign d) :
    PowerSeries.rescale ((σ : ℤ) : MvPolynomial (ℕ × ℕ) R)
      (PowerSeries.map (rename ρ).toRingHom (shiftSeriesP R d)) = shiftSeriesP R (ρ d) := by
  ext n
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_map]
  rcases n with _ | n
  · simp [shiftSeriesP]
  · simp only [shiftSeriesP, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, h]
    simp [map_mul, map_pow, map_neg, rename_X, mul_pow]
    ring

lemma pkSp_resc_F (n : ℕ) (ρ : ℕ × ℕ → ℕ × ℕ) (σ : ℤ) (T : Finset (ℕ × ℕ))
    (hs : ∀ d ∈ T, shiftSign (ρ d) = σ * shiftSign d) :
    PowerSeries.rescale ((σ : ℤ) : MvPolynomial (ℕ × ℕ) R)
        (PowerSeries.map (rename ρ).toRingHom (pkSp_F R n T)) =
      PowerSeries.C (∏ d ∈ oddDiagonals n \ T, X (ρ d)) *
        ∏ d ∈ T.filter (fun d => shiftSign d ≠ 0), shiftSeriesP R (ρ d) := by
  rw [pkSp_F, map_mul, map_mul, PowerSeries.map_C, pkSp_rescale_C]
  congr 1
  · congr 1
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_prod, rename_X]
  · rw [map_prod (PowerSeries.map _), map_prod (PowerSeries.rescale _)]
    exact prod_congr rfl fun d hd => pkSp_sP_relab ρ σ d (hs d (mem_filter.1 hd).1)

/-- Setting `X_C = 0` keeps exactly the triangulations through `C`. -/
lemma pkSp_zeroAt_AP {N m : ℕ} {C : ℕ × ℕ} (hC : C ∈ oddDiagonals N) :
    zeroAt R C (AP R N m) =
      PowerSeries.coeff m (∑ T ∈ (triangulations N).filter (fun T => C ∈ T), pkSp_F R N T) := by
  have hsC : shiftSign C = 0 := by
    have h := mem_filter.1 hC
    have h1 := mem_diagonals.1 h.1
    exact pkSp_shiftSign_odd (by omega) h.2
  have hmap : ∀ f : PowerSeries (MvPolynomial (ℕ × ℕ) R),
      zeroAt R C (PowerSeries.coeff m f) = PowerSeries.coeff m (PowerSeries.map (zeroAt R C).toRingHom f) := by
    intro f; rw [PowerSeries.coeff_map]; rfl
  rw [sum_filter, AP, hmap, map_sum]
  congr 1
  refine sum_congr rfl fun T _ => ?_
  rw [map_mul, PowerSeries.map_C, map_prod (PowerSeries.map _)]
  have hs : ∀ d ∈ T.filter (fun d => shiftSign d ≠ 0),
      PowerSeries.map (zeroAt R C).toRingHom (shiftSeriesP R d) = shiftSeriesP R d := by
    intro d hd
    have hdC : d ≠ C := fun h => (mem_filter.1 hd).2 (by rw [h]; exact hsC)
    exact pkSp_map_sP _ d (by simp [zeroAt, hdC])
  rw [prod_congr rfl hs]
  split_ifs with hCT
  · rw [pkSp_F]
    congr 2
    rw [map_prod]
    refine prod_congr rfl fun d hd => ?_
    have hdC : d ≠ C := fun h => (mem_sdiff.1 hd).2 (by rw [h]; exact hCT)
    simp [zeroAt, hdC]
  · rw [map_prod, prod_eq_zero (mem_sdiff.2 ⟨hC, hCT⟩) (by simp [zeroAt]), map_zero, zero_mul]

/-- The summand at a glued triangulation factors over the two children. -/
lemma pkSp_F_glue {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N) (hne : ¬ (i = 1 ∧ j = N))
    (hE : N % 2 = 0) (hodd : (j - i) % 2 = 1) {T1 T2 : Finset (ℕ × ℕ)} (h1 : T1 ⊆ diagonals (j - i + 1))
    (h2 : T2 ⊆ diagonals (N - j + i + 1)) :
    pkSp_F R N (pkSp_glue N i j T1 T2) =
      PowerSeries.C (crossProd R N (i, j)) *
        (PowerSeries.rescale ((((-1) ^ (i + 1) : ℤ)) : MvPolynomial (ℕ × ℕ) R)
            (PowerSeries.map (rename (relab N i)).toRingHom (pkSp_F R (j - i + 1) T1)) *
          PowerSeries.rescale ((((-1) ^ (j + 1) : ℤ)) : MvPolynomial (ℕ × ℕ) R)
            (PowerSeries.map (rename (relab N j)).toRingHom (pkSp_F R (N - j + i + 1) T2))) := by
  have hsL : ∀ d ∈ T1, shiftSign (relab N i d) = (-1) ^ (i + 1) * shiftSign d := fun d hd =>
    pkSp_sign_relab hE (by omega) (by omega) (by omega) (h1 hd)
  have hsR : ∀ d ∈ T2, shiftSign (relab N j d) = (-1) ^ (j + 1) * shiftSign d := fun d hd =>
    pkSp_sign_relab hE (by omega) (by omega) (by omega) (h2 hd)
  rw [pkSp_resc_F _ _ _ _ hsL, pkSp_resc_F _ _ _ _ hsR]
  have injL : Set.InjOn (relab N i) (diagonals (j - i + 1) : Set (ℕ × ℕ)) := fun x hx y hy h =>
    pkSp_inj (N := N) (b := i) (n := j - i + 1) (by omega) (by omega) (by omega) hx hy h
  have injR : Set.InjOn (relab N j) (diagonals (N - j + i + 1) : Set (ℕ × ℕ)) := fun x hx y hy h =>
    pkSp_inj (N := N) (b := j) (n := N - j + i + 1) (by omega) (by omega) (by omega) hx hy h
  have hoddL : ∀ d ∈ oddDiagonals (j - i + 1), d ∈ diagonals (j - i + 1) := fun d hd => (mem_filter.1 hd).1
  have hoddR : ∀ d ∈ oddDiagonals (N - j + i + 1), d ∈ diagonals (N - j + i + 1) :=
    fun d hd => (mem_filter.1 hd).1
  -- the odd diagonals missing from the glued set
  have hodd_set : oddDiagonals N \ pkSp_glue N i j T1 T2 =
      (oddDiagonals N).filter (fun d => Crosses d (i, j)) ∪
        ((oddDiagonals (j - i + 1) \ T1).image (relab N i) ∪
          (oddDiagonals (N - j + i + 1) \ T2).image (relab N j)) := by
    ext d
    rw [mem_sdiff, mem_union, mem_union, mem_filter, mem_image, mem_image]
    constructor
    · rintro ⟨hd, hnot⟩
      rcases pkSp_part (i := i) (j := j) (mem_filter.1 hd).1 with rfl | hc | hin | hout
      · exact absurd (mem_insert_self _ _) hnot
      · exact Or.inl ⟨hd, hc⟩
      · rw [pkSp_odd_eq] at hd
        obtain ⟨d', hd', rfl⟩ := pkSp_surjLQ hi hij hjN hne hd hin
        rw [← pkSp_odd_eq] at hd'
        refine Or.inr (Or.inl ⟨d', mem_sdiff.2 ⟨hd', fun h => hnot ?_⟩, rfl⟩)
        exact (pkSp_mem_glue_L hi hij hjN hne hE h1 h2 (hoddL _ hd')).2 h
      · rw [pkSp_odd_eq] at hd
        obtain ⟨d', hd', rfl⟩ := pkSp_surjRQ hi hij hjN hne hE hd hout
        rw [← pkSp_odd_eq] at hd'
        refine Or.inr (Or.inr ⟨d', mem_sdiff.2 ⟨hd', fun h => hnot ?_⟩, rfl⟩)
        exact (pkSp_mem_glue_R hi hij hjN hne hE h1 h2 (hoddR _ hd')).2 h
    · rintro (⟨hd, hc⟩ | ⟨d', hd', rfl⟩ | ⟨d', hd', rfl⟩)
      · exact ⟨hd, fun h => pkSp_glue_nc hi hij hjN hne hE h1 h2 h hc⟩
      · obtain ⟨hd'o, hnT⟩ := mem_sdiff.1 hd'
        rw [pkSp_odd_eq] at hd'o
        refine ⟨by rw [pkSp_odd_eq]; exact (pkSp_mapLQ hi hij hjN hne hd'o).1, fun h => hnT ?_⟩
        exact (pkSp_mem_glue_L hi hij hjN hne hE h1 h2 (pkSp_mem_S.1 hd'o).1).1 h
      · obtain ⟨hd'o, hnT⟩ := mem_sdiff.1 hd'
        rw [pkSp_odd_eq] at hd'o
        refine ⟨by rw [pkSp_odd_eq]; exact (pkSp_mapRQ hi hij hjN hne hE hd'o).1, fun h => hnT ?_⟩
        exact (pkSp_mem_glue_R hi hij hjN hne hE h1 h2 (pkSp_mem_S.1 hd'o).1).1 h
  have hdisj1 : Disjoint ((oddDiagonals N).filter (fun d => Crosses d (i, j)))
      ((oddDiagonals (j - i + 1) \ T1).image (relab N i) ∪
        (oddDiagonals (N - j + i + 1) \ T2).image (relab N j)) := by
    rw [disjoint_left]
    intro d hd hd'
    have hc := (mem_filter.1 hd).2
    rw [mem_union, mem_image, mem_image] at hd'
    rcases hd' with ⟨d', hd', rfl⟩ | ⟨d', hd', rfl⟩
    · exact pkSp_In_nc (pkSp_mapL hi hij hjN hne (hoddL _ (mem_sdiff.1 hd').1)).2.1 hc
    · exact pkSp_Out_nc (pkSp_mapR hi hij hjN hne hE (hoddR _ (mem_sdiff.1 hd').1)).2.1 hc
  have hdisjLR : ∀ (A B : Finset (ℕ × ℕ)), A ⊆ diagonals (j - i + 1) → B ⊆ diagonals (N - j + i + 1) →
      Disjoint (A.image (relab N i)) (B.image (relab N j)) := by
    intro A B hA hB
    rw [disjoint_left]
    intro d hd hd'
    rw [mem_image] at hd hd'
    obtain ⟨a, ha, rfl⟩ := hd
    obtain ⟨b, hb, hba⟩ := hd'
    obtain ⟨haN, hin, -⟩ := pkSp_mapL hi hij hjN hne (hA ha)
    obtain ⟨-, hout, -⟩ := pkSp_mapR hi hij hjN hne hE (hB hb)
    rw [hba] at hout
    exact pkSp_In_not_Out (pkSp_lt haN) hin hout
  have hsC : shiftSign (i, j) = 0 := pkSp_shiftSign_odd (by dsimp only; omega) hodd
  have hfilt : (pkSp_glue N i j T1 T2).filter (fun d => shiftSign d ≠ 0) =
      (T1.filter (fun d => shiftSign d ≠ 0)).image (relab N i) ∪
        (T2.filter (fun d => shiftSign d ≠ 0)).image (relab N j) := by
    ext d
    simp only [pkSp_glue, mem_filter, mem_union, mem_image, mem_insert]
    constructor
    · rintro ⟨rfl | ⟨d', hd', rfl⟩ | ⟨d', hd', rfl⟩, hs⟩
      · exact absurd hsC hs
      · rw [hsL d' hd'] at hs
        exact Or.inl ⟨d', ⟨hd', right_ne_zero_of_mul hs⟩, rfl⟩
      · rw [hsR d' hd'] at hs
        exact Or.inr ⟨d', ⟨hd', right_ne_zero_of_mul hs⟩, rfl⟩
    · rintro (⟨d', ⟨hd', hs⟩, rfl⟩ | ⟨d', ⟨hd', hs⟩, rfl⟩)
      · refine ⟨Or.inr (Or.inl ⟨d', hd', rfl⟩), ?_⟩
        rw [hsL d' hd']; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hs
      · refine ⟨Or.inr (Or.inr ⟨d', hd', rfl⟩), ?_⟩
        rw [hsR d' hd']; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hs
  rw [pkSp_F, hodd_set, hfilt, prod_union hdisj1,
    prod_union (hdisjLR _ _ (fun d hd => hoddL _ (mem_sdiff.1 hd).1) (fun d hd => hoddR _ (mem_sdiff.1 hd).1)),
    prod_union (hdisjLR _ _ (fun d hd => h1 (mem_filter.1 hd).1) (fun d hd => h2 (mem_filter.1 hd).1)),
    prod_image (injL.mono fun d hd => hoddL _ (mem_sdiff.1 hd).1),
    prod_image (injR.mono fun d hd => hoddR _ (mem_sdiff.1 hd).1),
    prod_image (injL.mono fun d hd => h1 (mem_filter.1 hd).1),
    prod_image (injR.mono fun d hd => h2 (mem_filter.1 hd).1), crossProd, map_mul, map_mul]
  ring

/-- `AP_residue` in the frozen variable names, proved from the pieces above. -/
theorem pkSp_AP_residue {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {C : ℕ × ℕ} (hC : C ∈ oddDiagonals N) (m : ℕ) :
    zeroAt R C (AP R N m) =
      (∑ p ∈ antidiagonal m, ((-1 : MvPolynomial (ℕ × ℕ) R) ^ ((C.1 + 1) * p.1 + (C.2 + 1) * p.2)) *
        (rename (relab N C.1) (AP R (C.2 - C.1 + 1) p.1) *
          rename (relab N C.2) (AP R (N - C.2 + C.1 + 1) p.2))) * crossProd R N C := by
  rw [pkSp_zeroAt_AP hC]
  obtain ⟨i, j⟩ := C
  have hC1 := mem_filter.1 hC
  have hC2 := mem_diagonals.1 hC1.1
  dsimp only at hC1 hC2 ⊢
  obtain ⟨hi, hjN, hij, hne⟩ := hC2
  have hodd := hC1.2
  have hQC : (i, j) ∈ pkSp_S (fun _ => True) N := pkSp_mem_S.2 ⟨(mem_filter.1 hC).1, trivial⟩
  rw [pkSp_sum_split triangulations pkSp_tri_iff hi hij hjN hne hE hQC (pkSp_F R N)]
  have hsub : ∀ n T, T ∈ triangulations n → T ⊆ diagonals n := fun n T hT =>
    (mem_triangulations.1 hT).1
  have hsum : ∑ x ∈ triangulations (j - i + 1) ×ˢ triangulations (N - j + i + 1),
      pkSp_F R N (pkSp_glue N i j x.1 x.2) =
      ∑ x ∈ triangulations (j - i + 1) ×ˢ triangulations (N - j + i + 1),
        PowerSeries.C (crossProd R N (i, j)) *
          (PowerSeries.rescale (((-1) ^ (i + 1) : ℤ) : MvPolynomial (ℕ × ℕ) R) (PowerSeries.map (rename (relab N i)).toRingHom (pkSp_F R (j - i + 1) x.1)) *
            PowerSeries.rescale (((-1) ^ (j + 1) : ℤ) : MvPolynomial (ℕ × ℕ) R)
              (PowerSeries.map (rename (relab N j)).toRingHom (pkSp_F R (N - j + i + 1) x.2))) :=
    sum_congr rfl fun x hx => pkSp_F_glue hi hij hjN hne hE hodd (hsub _ _ (mem_product.1 hx).1)
      (hsub _ _ (mem_product.1 hx).2)
  have hprod : ∀ (A B : Finset (Finset (ℕ × ℕ))) (c : PowerSeries (MvPolynomial (ℕ × ℕ) R))
      (f g : Finset (ℕ × ℕ) → PowerSeries (MvPolynomial (ℕ × ℕ) R)),
      ∑ x ∈ A ×ˢ B, c * (f x.1 * g x.2) = c * ((∑ T ∈ A, f T) * ∑ T ∈ B, g T) := by
    intro A B c f g
    rw [sum_mul_sum, mul_sum, sum_product]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum]
  have hfac : ∑ x ∈ triangulations (j - i + 1) ×ˢ triangulations (N - j + i + 1),
      pkSp_F R N (pkSp_glue N i j x.1 x.2) =
      PowerSeries.C (crossProd R N (i, j)) *
        (PowerSeries.rescale (((-1) ^ (i + 1) : ℤ) : MvPolynomial (ℕ × ℕ) R) (PowerSeries.map (rename (relab N i)).toRingHom
            (∑ T ∈ triangulations (j - i + 1), pkSp_F R (j - i + 1) T)) *
          PowerSeries.rescale (((-1) ^ (j + 1) : ℤ) : MvPolynomial (ℕ × ℕ) R) (PowerSeries.map (rename (relab N j)).toRingHom
            (∑ T ∈ triangulations (N - j + i + 1), pkSp_F R (N - j + i + 1) T))) := by
    rw [hsum, map_sum (PowerSeries.map _), map_sum (PowerSeries.rescale _), map_sum (PowerSeries.map _),
      map_sum (PowerSeries.rescale _)]
    exact hprod _ _ _
      (fun T => PowerSeries.rescale (((-1) ^ (i + 1) : ℤ) : MvPolynomial (ℕ × ℕ) R) (PowerSeries.map (rename (relab N i)).toRingHom (pkSp_F R (j - i + 1) T)))
      (fun T => PowerSeries.rescale (((-1) ^ (j + 1) : ℤ) : MvPolynomial (ℕ × ℕ) R)
        (PowerSeries.map (rename (relab N j)).toRingHom (pkSp_F R (N - j + i + 1) T)))
  rw [hfac]
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul, mul_sum, sum_mul]
  refine sum_congr rfl fun p _ => ?_
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_rescale, PowerSeries.coeff_map, PowerSeries.coeff_map]
  have eL : PowerSeries.coeff p.1 (∑ T ∈ triangulations (j - i + 1), pkSp_F R (j - i + 1) T) =
      AP R (j - i + 1) p.1 := rfl
  have eR : PowerSeries.coeff p.2 (∑ T ∈ triangulations (N - j + i + 1), pkSp_F R (N - j + i + 1) T) =
      AP R (N - j + i + 1) p.2 := rfl
  rw [eL, eR]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  push_cast
  ring

/-- `sorry` (3c-b). **Residues of the shifted amplitude, every δ-order (Z26 Lemma 4.1, residue formula)**:
triangulations through `C` = pairs of triangulations of `P_L` and `P_R`; the child's `v₀` is `(−1)^{b+1}` times the
parent's restriction, whence the sign. [mirror D5: every odd chord, `m ≤ N − 2`, N = 6, 8, 10] -/
theorem AP_residue {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {C : ℕ × ℕ} (hC : C ∈ oddDiagonals N) (m : ℕ) :
    zeroAt R C (AP R N m) =
      (∑ p ∈ antidiagonal m, ((-1 : MvPolynomial (ℕ × ℕ) R) ^ ((C.1 + 1) * p.1 + (C.2 + 1) * p.2)) *
        (rename (relab N C.1) (AP R (C.2 - C.1 + 1) p.1) *
          rename (relab N C.2) (AP R (N - C.2 + C.1 + 1) p.2))) * crossProd R N C :=
  pkSp_AP_residue hN hE hC m

/-- Every residue of `AP N m` vanishes below the NLSM order, given the statement for the smaller polygons. -/
lemma pkZ_res_zero {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0)
    (ih : ∀ n, n < N → 4 ≤ n → n % 2 = 0 → ∀ k, k < n - 2 → AP R n k = 0)
    {m : ℕ} (hm : m < N - 2) {C : ℕ × ℕ} (hC : C ∈ oddDiagonals N) : zeroAt R C (AP R N m) = 0 := by
  rw [AP_residue hN hE hC m]
  have hc := pkZ_child hE hC
  rw [sum_eq_zero, zero_mul]
  intro p hp
  have hp' := mem_antidiagonal.1 hp
  by_cases h1 : p.1 < C.2 - C.1 + 1 - 2
  · rw [ih (C.2 - C.1 + 1) hc.2.2.1 hc.1 hc.2.1 p.1 h1, map_zero, zero_mul, mul_zero]
  · rw [ih (N - C.2 + C.1 + 1) hc.2.2.2.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 p.2 (by omega), map_zero, mul_zero,
      mul_zero]

/-- A constant multiple of `oddDen` that is also the numerator of an order below `N − 2` is zero: evaluate at a point
of the row `R_{1,1}` with every diagonal non-zero (row zero of the shifted amplitude). -/
lemma pkZ_const_zero {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (m : ℕ) (c : ℤ)
    (h : AP ℤ N m = (∏ C ∈ oddDiagonals N, (X C : MvPolynomial (ℕ × ℕ) ℤ)) * MvPolynomial.C c) : c = 0 := by
  obtain ⟨x, hx, hR⟩ := onRect_inhabited (n := N) (k := 1) (m := 1) le_rfl (by omega) le_rfl (by omega)
  have hxo : ∀ d ∈ oddDiagonals N, x d ≠ 0 := fun d hd => hx d (mem_filter.1 hd).1
  have e1 := AP_eval N m x hxo
  rw [shiftCoeff_row_zero hN hE ⟨le_rfl, by omega⟩ x hxo hR (m : ℤ), zero_mul, ← AP_map (Int.castRingHom ℚ), h]
    at e1
  have e2 : eval x (MvPolynomial.map (Int.castRingHom ℚ)
      ((∏ C ∈ oddDiagonals N, (X C : MvPolynomial (ℕ × ℕ) ℤ)) * MvPolynomial.C c)) =
      (∏ d ∈ oddDiagonals N, x d) * (c : ℚ) := by
    simp [map_prod]
  rw [e2] at e1
  have hp : (∏ d ∈ oddDiagonals N, x d) ≠ 0 := prod_ne_zero_iff.2 hxo
  exact Int.cast_eq_zero.1 ((mul_eq_zero.1 e1).resolve_left hp)

/-- `AP_eq_zero` over `ℤ`, by strong induction on `N`. -/
lemma pkZ_eq_zero_int : ∀ N : ℕ, 4 ≤ N → N % 2 = 0 → ∀ m, m < N - 2 → AP ℤ N m = 0 := by
  intro N
  refine Nat.strong_induction_on N ?_
  intro N ih hN hE m hm
  by_cases hs : (oddDiagonals N).card + m < N - 3
  · exact AP_eq_zero_of_small hN m hs
  obtain ⟨Q, hQ⟩ := prod_X_dvd_of_zeroAt (oddDiagonals N) (AP ℤ N m)
    (fun C hC => pkZ_res_zero hN hE (fun n hn h4 h2 k hk => ih n hn h4 h2 k hk) hm hC)
  by_contra hne
  have hQ0 : Q ≠ 0 := fun h0 => hne (by rw [hQ, h0, mul_zero])
  have t1 := (AP_isHomogeneous (R := ℤ) hN m (by omega)).totalDegree hne
  rw [hQ, totalDegree_mul_of_isDomain (pkZ_prod_ne _) hQ0, pkZ_prod_deg] at t1
  have t2 : Q.totalDegree = 0 := by omega
  have hc := pkZ_const_zero hN hE m (Q.coeff 0) (by rw [hQ, ← totalDegree_eq_zero_iff_eq_C.1 t2])
  exact hQ0 (by rw [totalDegree_eq_zero_iff_eq_C.1 t2, hc, map_zero])

/-- `sorry` (3c-b). **Lemma 4.1 of Z26, numerator form** (all rings, via `ℤ`). -/
theorem AP_eq_zero {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {m : ℕ} (hm : m < N - 2) : AP R N m = 0 := by
  rw [← AP_map (Int.castRingHom R), pkZ_eq_zero_int N hN hE m hm, map_zero]

lemma pkZ_sign_even {N : ℕ} {C : ℕ × ℕ} (h1 : (C.2 - C.1 + 1) % 2 = 0) (h2 : (N - C.2 + C.1 + 1) % 2 = 0)
    (h3 : 4 ≤ C.2 - C.1 + 1) (h4 : 4 ≤ N - C.2 + C.1 + 1) :
    Even ((C.1 + 1) * (C.2 - C.1 + 1 - 2) + (C.2 + 1) * (N - C.2 + C.1 + 1 - 2)) := by
  obtain ⟨a, ha⟩ : ∃ a, C.2 - C.1 + 1 - 2 = 2 * a := ⟨(C.2 - C.1 + 1 - 2) / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, N - C.2 + C.1 + 1 - 2 = 2 * b := ⟨(N - C.2 + C.1 + 1 - 2) / 2, by omega⟩
  rw [ha, hb]
  exact ⟨(C.1 + 1) * a + (C.2 + 1) * b, by ring⟩

/-- `sorry` (3c-b; from `AP_residue` at `m = N − 2` and `AP_eq_zero` for the children: only `p = (L−2, R−2)` survives,
with sign `+1` since `L`, `R` are even). **PROOFS Lemma B.3 = Z26 Lemma 4.2, numerator form**:
`Res_C NLSM_N = NLSM_L · NLSM_R`. -/
theorem NP_residue {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {C : ℕ × ℕ} (hC : C ∈ oddDiagonals N) :
    zeroAt R C (NP R N) =
      rename (relab N C.1) (NP R (C.2 - C.1 + 1)) * rename (relab N C.2) (NP R (N - C.2 + C.1 + 1)) *
        crossProd R N C := by
  have hc := pkZ_child hE hC
  have e0 : NP R N = AP R N (N - 2) := rfl
  rw [e0, AP_residue hN hE hC (N - 2),
    sum_eq_single (C.2 - C.1 + 1 - 2, N - C.2 + C.1 + 1 - 2)]
  · rw [Even.neg_one_pow (pkZ_sign_even hc.2.1 hc.2.2.2.2.1 hc.1 hc.2.2.2.1), one_mul]
    rfl
  · intro p hp hne
    have hp' := mem_antidiagonal.1 hp
    by_cases h1 : p.1 < C.2 - C.1 + 1 - 2
    · rw [AP_eq_zero hc.1 hc.2.1 h1, map_zero, zero_mul, mul_zero]
    by_cases h2 : p.2 < N - C.2 + C.1 + 1 - 2
    · rw [AP_eq_zero hc.2.2.2.1 hc.2.2.2.2.1 h2, map_zero, mul_zero, mul_zero]
    exfalso
    exact hne (Prod.ext (by omega) (by omega))
  · intro h
    exact absurd (mem_antidiagonal.2 hc.2.2.2.2.2.2) h

/-! ### pkgQres helpers: the quads of a glued quadrangulation and `QP_residue` -/

lemma pkQ_npair_comm (N x y : ℕ) : npair N x y = npair N y x := by
  unfold npair; rw [min_comm, max_comm]

lemma pkQ_npair_vtx {N x y x' y' : ℕ} (hx : vtx N x = vtx N x') (hy : vtx N y = vtx N y') :
    npair N x y = npair N x' y' := by
  unfold npair; rw [hx, hy]

lemma pkQ_vtx_sub {N x : ℕ} (h : N < x) : vtx N (x - N) = vtx N x := by
  have e := vtx_add_n N (x - N)
  rw [Nat.sub_add_cancel h.le] at e
  exact e.symm

lemma pkQ_pl_eq {N x y x' y' : ℕ} (h : npair N x y = npair N x' y') :
    planarP R N x y = planarP R N x' y' := by
  unfold planarP; rw [h]

/-- The vertex numerator with explicit corners. -/
noncomputable def pkQ_V (R : Type*) [CommRing R] (N π a b c d : ℕ) : MvPolynomial (ℕ × ℕ) R :=
  planarP R N a c + planarP R N b d -
    (if a % 2 = π then planarP R N b c + planarP R N d a else planarP R N a b + planarP R N c d)

lemma pkQ_vnumP (N π : ℕ) (q : Quad) : vnumP R N π q = pkQ_V R N π q.u1 q.u2 q.u3 q.u4 := rfl

lemma pkQ_V_rot {N π a b c d : ℕ} (hπ : π < 2) (hab : (a + b) % 2 = 1) :
    pkQ_V R N π a b c d = pkQ_V R N π b c d a := by
  unfold pkQ_V
  rw [pkQ_pl_eq (R := R) (pkQ_npair_comm N c a)]
  by_cases h : a % 2 = π
  · rw [if_pos h, if_neg (show ¬ b % 2 = π by omega)]; ring
  · rw [if_neg h, if_pos (show b % 2 = π by omega)]; ring

lemma pkQ_V_vtx {N π a b c d a' b' c' d' : ℕ} (ha : vtx N a = vtx N a') (hb : vtx N b = vtx N b')
    (hc : vtx N c = vtx N c') (hd : vtx N d = vtx N d') (hp : a % 2 = a' % 2) :
    pkQ_V R N π a b c d = pkQ_V R N π a' b' c' d' := by
  unfold pkQ_V
  rw [hp, pkQ_pl_eq (R := R) (pkQ_npair_vtx ha hc), pkQ_pl_eq (R := R) (pkQ_npair_vtx hb hd),
    pkQ_pl_eq (R := R) (pkQ_npair_vtx hb hc), pkQ_pl_eq (R := R) (pkQ_npair_vtx hd ha),
    pkQ_pl_eq (R := R) (pkQ_npair_vtx ha hb), pkQ_pl_eq (R := R) (pkQ_npair_vtx hc hd)]

/-- Child quad to parent quad: shift the corners by `b − 1`, wrap past `N`, re-sort (a cyclic rotation). -/
def pkQ_lift (N b : ℕ) (q : Quad) : Quad :=
  if q.u4 + b - 1 ≤ N then ⟨q.u1 + b - 1, q.u2 + b - 1, q.u3 + b - 1, q.u4 + b - 1⟩
  else if q.u3 + b - 1 ≤ N then ⟨q.u4 + b - 1 - N, q.u1 + b - 1, q.u2 + b - 1, q.u3 + b - 1⟩
  else if q.u2 + b - 1 ≤ N then ⟨q.u3 + b - 1 - N, q.u4 + b - 1 - N, q.u1 + b - 1, q.u2 + b - 1⟩
  else if q.u1 + b - 1 ≤ N then ⟨q.u2 + b - 1 - N, q.u3 + b - 1 - N, q.u4 + b - 1 - N, q.u1 + b - 1⟩
  else ⟨q.u1 + b - 1 - N, q.u2 + b - 1 - N, q.u3 + b - 1 - N, q.u4 + b - 1 - N⟩

/-- Parent quad to child quad (inverse of `pkQ_lift`). -/
def pkQ_unlift (N b : ℕ) (q : Quad) : Quad :=
  if b ≤ q.u1 then ⟨q.u1 + 1 - b, q.u2 + 1 - b, q.u3 + 1 - b, q.u4 + 1 - b⟩
  else if b ≤ q.u2 then ⟨q.u2 + 1 - b, q.u3 + 1 - b, q.u4 + 1 - b, q.u1 + N + 1 - b⟩
  else if b ≤ q.u3 then ⟨q.u3 + 1 - b, q.u4 + 1 - b, q.u1 + N + 1 - b, q.u2 + N + 1 - b⟩
  else if b ≤ q.u4 then ⟨q.u4 + 1 - b, q.u1 + N + 1 - b, q.u2 + N + 1 - b, q.u3 + N + 1 - b⟩
  else ⟨q.u1 + N + 1 - b, q.u2 + N + 1 - b, q.u3 + N + 1 - b, q.u4 + N + 1 - b⟩

lemma pkQ_lift_spec (N b : ℕ) (q : Quad) :
    (q.u4 + b - 1 ≤ N ∧ pkQ_lift N b q = ⟨q.u1 + b - 1, q.u2 + b - 1, q.u3 + b - 1, q.u4 + b - 1⟩) ∨
    ((N < q.u4 + b - 1 ∧ q.u3 + b - 1 ≤ N) ∧
      pkQ_lift N b q = ⟨q.u4 + b - 1 - N, q.u1 + b - 1, q.u2 + b - 1, q.u3 + b - 1⟩) ∨
    ((N < q.u3 + b - 1 ∧ q.u2 + b - 1 ≤ N) ∧
      pkQ_lift N b q = ⟨q.u3 + b - 1 - N, q.u4 + b - 1 - N, q.u1 + b - 1, q.u2 + b - 1⟩) ∨
    ((N < q.u2 + b - 1 ∧ q.u1 + b - 1 ≤ N) ∧
      pkQ_lift N b q = ⟨q.u2 + b - 1 - N, q.u3 + b - 1 - N, q.u4 + b - 1 - N, q.u1 + b - 1⟩) ∨
    (N < q.u1 + b - 1 ∧
      pkQ_lift N b q = ⟨q.u1 + b - 1 - N, q.u2 + b - 1 - N, q.u3 + b - 1 - N, q.u4 + b - 1 - N⟩) := by
  unfold pkQ_lift
  split_ifs with c1 c2 c3 c4
  · exact Or.inl ⟨c1, rfl⟩
  · exact Or.inr (Or.inl ⟨⟨by omega, c2⟩, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨⟨by omega, c3⟩, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨by omega, c4⟩, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, rfl⟩)))

lemma pkQ_unlift_spec (N b : ℕ) (q : Quad) :
    (b ≤ q.u1 ∧ pkQ_unlift N b q = ⟨q.u1 + 1 - b, q.u2 + 1 - b, q.u3 + 1 - b, q.u4 + 1 - b⟩) ∨
    ((q.u1 < b ∧ b ≤ q.u2) ∧
      pkQ_unlift N b q = ⟨q.u2 + 1 - b, q.u3 + 1 - b, q.u4 + 1 - b, q.u1 + N + 1 - b⟩) ∨
    ((q.u2 < b ∧ b ≤ q.u3) ∧
      pkQ_unlift N b q = ⟨q.u3 + 1 - b, q.u4 + 1 - b, q.u1 + N + 1 - b, q.u2 + N + 1 - b⟩) ∨
    ((q.u3 < b ∧ b ≤ q.u4) ∧
      pkQ_unlift N b q = ⟨q.u4 + 1 - b, q.u1 + N + 1 - b, q.u2 + N + 1 - b, q.u3 + N + 1 - b⟩) ∨
    (q.u4 < b ∧
      pkQ_unlift N b q = ⟨q.u1 + N + 1 - b, q.u2 + N + 1 - b, q.u3 + N + 1 - b, q.u4 + N + 1 - b⟩) := by
  unfold pkQ_unlift
  split_ifs with c1 c2 c3 c4
  · exact Or.inl ⟨c1, rfl⟩
  · exact Or.inr (Or.inl ⟨⟨by omega, c2⟩, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨⟨by omega, c3⟩, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨by omega, c4⟩, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, rfl⟩)))

lemma pkQ_lift_unlift {N b : ℕ} (hb : 1 ≤ b) (hbN : b ≤ N) {q : Quad} (hq : q ∈ quadIdx N) :
    pkQ_lift N b (pkQ_unlift N b q) = q := by
  obtain ⟨a1, a2, a3, a4⟩ := q
  rw [p3b_mem_quadIdx] at hq
  have hl := pkQ_lift_spec N b (pkQ_unlift N b ⟨a1, a2, a3, a4⟩)
  rcases pkQ_unlift_spec N b ⟨a1, a2, a3, a4⟩ with ⟨c, e⟩ | ⟨c, e⟩ | ⟨c, e⟩ | ⟨c, e⟩ | ⟨c, e⟩ <;>
    rw [e] at hl ⊢ <;> dsimp only at c hl hq <;>
    rcases hl with ⟨c', e'⟩ | ⟨c', e'⟩ | ⟨c', e'⟩ | ⟨c', e'⟩ | ⟨c', e'⟩ <;> rw [e'] <;>
    simp only [Quad.mk.injEq] <;> omega

lemma pkQ_unlift_lift {N b n : ℕ} (hb : 1 ≤ b) (hn : n ≤ N) {q : Quad} (hq : q ∈ quadIdx n) :
    pkQ_unlift N b (pkQ_lift N b q) = q := by
  obtain ⟨a1, a2, a3, a4⟩ := q
  rw [p3b_mem_quadIdx] at hq
  have hl := pkQ_unlift_spec N b (pkQ_lift N b ⟨a1, a2, a3, a4⟩)
  rcases pkQ_lift_spec N b ⟨a1, a2, a3, a4⟩ with ⟨c, e⟩ | ⟨c, e⟩ | ⟨c, e⟩ | ⟨c, e⟩ | ⟨c, e⟩ <;>
    rw [e] at hl ⊢ <;> dsimp only at c hl hq <;>
    rcases hl with ⟨c', e'⟩ | ⟨c', e'⟩ | ⟨c', e'⟩ | ⟨c', e'⟩ | ⟨c', e'⟩ <;> rw [e'] <;>
    simp only [Quad.mk.injEq] <;> omega

lemma pkQ_lift_idx {N b n : ℕ} (hb : 1 ≤ b) (hn : n ≤ N) (hnb : n + b - 1 ≤ 2 * N) {q : Quad}
    (hq : q ∈ quadIdx n) : pkQ_lift N b q ∈ quadIdx N := by
  obtain ⟨a1, a2, a3, a4⟩ := q
  rw [p3b_mem_quadIdx] at hq
  rcases pkQ_lift_spec N b ⟨a1, a2, a3, a4⟩ with ⟨c, e⟩ | ⟨c, e⟩ | ⟨c, e⟩ | ⟨c, e⟩ | ⟨c, e⟩ <;>
    rw [e, p3b_mem_quadIdx] <;> dsimp only at c hq ⊢ <;> omega

/-- The four sides of a quad, as a conjunction (the closing side read as `(a, d)`). -/
def pkQ_Ok (N : ℕ) (G : Finset (ℕ × ℕ)) (a b c d : ℕ) : Prop :=
  SideOK N G (a, b) ∧ SideOK N G (b, c) ∧ SideOK N G (c, d) ∧ SideOK N G (a, d)

lemma pkQ_so_eq {N : ℕ} {G : Finset (ℕ × ℕ)} {x y x' y' : ℕ} (h : npair N x y = npair N x' y') :
    SideOK N G (x, y) ↔ SideOK N G (x', y') := by
  show npair N x y ∈ G ∨ npair N x y ∉ diagonals N ↔ npair N x' y' ∈ G ∨ npair N x' y' ∉ diagonals N
  rw [h]

lemma pkQ_Ok_rot {N : ℕ} {G : Finset (ℕ × ℕ)} {a b c d : ℕ} :
    pkQ_Ok N G a b c d ↔ pkQ_Ok N G b c d a := by
  unfold pkQ_Ok
  rw [pkQ_so_eq (G := G) (pkQ_npair_comm N b a), pkQ_so_eq (G := G) (pkQ_npair_comm N d a)]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h2, h3, h4, h1⟩
  · rintro ⟨h2, h3, h4, h1⟩; exact ⟨h1, h2, h3, h4⟩

lemma pkQ_Ok_vtx {N : ℕ} {G : Finset (ℕ × ℕ)} {a b c d a' b' c' d' : ℕ} (ha : vtx N a = vtx N a')
    (hb : vtx N b = vtx N b') (hc : vtx N c = vtx N c') (hd : vtx N d = vtx N d') :
    pkQ_Ok N G a b c d ↔ pkQ_Ok N G a' b' c' d' := by
  unfold pkQ_Ok
  rw [pkQ_so_eq (G := G) (pkQ_npair_vtx ha hb), pkQ_so_eq (G := G) (pkQ_npair_vtx hb hc),
    pkQ_so_eq (G := G) (pkQ_npair_vtx hc hd), pkQ_so_eq (G := G) (pkQ_npair_vtx ha hd)]

lemma pkQ_mem_quads {N : ℕ} {G : Finset (ℕ × ℕ)} {q : Quad} :
    q ∈ quads N G ↔ q ∈ quadIdx N ∧ pkQ_Ok N G q.u1 q.u2 q.u3 q.u4 := by
  constructor
  · intro hq
    obtain ⟨-, s1, s2, s3⟩ := p3b_sides_of_mem hq
    have s4 : SideOK N G (q.u4, q.u1 + N) := (mem_filter.1 hq).2 _ (by simp [Quad.sides])
    rw [pkQ_so_eq (pkQ_npair_comm N q.u4 (q.u1 + N)), pkQ_so_eq (pkQ_npair_vtx (vtx_add_n N q.u1) rfl)] at s4
    exact ⟨(mem_filter.1 hq).1, s1, s2, s3, s4⟩
  · intro h
    obtain ⟨a, b, c, d⟩ := q
    obtain ⟨hi, s1, s2, s3, s4⟩ := h
    refine p3b_mem_quads (p3b_mem_quadIdx.1 hi) s1 s2 s3 ?_
    rw [pkQ_so_eq (pkQ_npair_comm N d (a + N)), pkQ_so_eq (pkQ_npair_vtx (vtx_add_n N a) rfl)]
    exact s4

lemma pkQ_lift_Ok {N b n : ℕ} {G : Finset (ℕ × ℕ)} (hn : n ≤ N) {q : Quad} (hq : q ∈ quadIdx n) :
    pkQ_Ok N G (pkQ_lift N b q).u1 (pkQ_lift N b q).u2 (pkQ_lift N b q).u3 (pkQ_lift N b q).u4 ↔
      pkQ_Ok N G (q.u1 + b - 1) (q.u2 + b - 1) (q.u3 + b - 1) (q.u4 + b - 1) := by
  rw [p3b_mem_quadIdx] at hq
  rcases pkQ_lift_spec N b q with ⟨c, e⟩ | ⟨c, e⟩ | ⟨c, e⟩ | ⟨c, e⟩ | ⟨c, e⟩ <;> rw [e] <;> dsimp only
  · rw [pkQ_Ok_vtx (a' := q.u4 + b - 1) (b' := q.u1 + b - 1) (c' := q.u2 + b - 1) (d' := q.u3 + b - 1)
      (pkQ_vtx_sub (by omega)) rfl rfl rfl, pkQ_Ok_rot]
  · rw [pkQ_Ok_vtx (a' := q.u3 + b - 1) (b' := q.u4 + b - 1) (c' := q.u1 + b - 1) (d' := q.u2 + b - 1)
      (pkQ_vtx_sub (by omega)) (pkQ_vtx_sub (by omega)) rfl rfl, pkQ_Ok_rot, pkQ_Ok_rot]
  · rw [pkQ_Ok_vtx (a' := q.u2 + b - 1) (b' := q.u3 + b - 1) (c' := q.u4 + b - 1) (d' := q.u1 + b - 1)
      (pkQ_vtx_sub (by omega)) (pkQ_vtx_sub (by omega)) (pkQ_vtx_sub (by omega)) rfl, pkQ_Ok_rot, pkQ_Ok_rot,
      pkQ_Ok_rot]
  · rw [pkQ_Ok_vtx (a' := q.u1 + b - 1) (b' := q.u2 + b - 1) (c' := q.u3 + b - 1) (d' := q.u4 + b - 1)
      (pkQ_vtx_sub (by omega)) (pkQ_vtx_sub (by omega)) (pkQ_vtx_sub (by omega)) (pkQ_vtx_sub (by omega))]

lemma pkQ_V_lift {N b n π : ℕ} (hπ : π < 2) (hE : N % 2 = 0) (hn : n ≤ N) {q : Quad} (hq : q ∈ quadIdx n)
    (halt : q.Alternating) :
    vnumP R N π (pkQ_lift N b q) =
      pkQ_V R N π (q.u1 + b - 1) (q.u2 + b - 1) (q.u3 + b - 1) (q.u4 + b - 1) := by
  rw [p3b_mem_quadIdx] at hq
  obtain ⟨p1, p2, p3⟩ := halt
  have r41 := pkQ_V_rot (R := R) (N := N) (a := q.u4 + b - 1) (b := q.u1 + b - 1) (c := q.u2 + b - 1)
    (d := q.u3 + b - 1) hπ (by omega)
  have r34 := pkQ_V_rot (R := R) (N := N) (a := q.u3 + b - 1) (b := q.u4 + b - 1) (c := q.u1 + b - 1)
    (d := q.u2 + b - 1) hπ (by omega)
  have r23 := pkQ_V_rot (R := R) (N := N) (a := q.u2 + b - 1) (b := q.u3 + b - 1) (c := q.u4 + b - 1)
    (d := q.u1 + b - 1) hπ (by omega)
  rcases pkQ_lift_spec N b q with ⟨c, e⟩ | ⟨c, e⟩ | ⟨c, e⟩ | ⟨c, e⟩ | ⟨c, e⟩ <;> rw [e, pkQ_vnumP] <;>
    dsimp only
  · rw [pkQ_V_vtx (a' := q.u4 + b - 1) (b' := q.u1 + b - 1) (c' := q.u2 + b - 1) (d' := q.u3 + b - 1)
      (pkQ_vtx_sub (by omega)) rfl rfl rfl (by omega), r41]
  · rw [pkQ_V_vtx (a' := q.u3 + b - 1) (b' := q.u4 + b - 1) (c' := q.u1 + b - 1) (d' := q.u2 + b - 1)
      (pkQ_vtx_sub (by omega)) (pkQ_vtx_sub (by omega)) rfl rfl (by omega), r34, r41]
  · rw [pkQ_V_vtx (a' := q.u2 + b - 1) (b' := q.u3 + b - 1) (c' := q.u4 + b - 1) (d' := q.u1 + b - 1)
      (pkQ_vtx_sub (by omega)) (pkQ_vtx_sub (by omega)) (pkQ_vtx_sub (by omega)) rfl (by omega), r23, r34, r41]
  · rw [pkQ_V_vtx (a' := q.u1 + b - 1) (b' := q.u2 + b - 1) (c' := q.u3 + b - 1) (d' := q.u4 + b - 1)
      (pkQ_vtx_sub (by omega)) (pkQ_vtx_sub (by omega)) (pkQ_vtx_sub (by omega)) (pkQ_vtx_sub (by omega))
      (by omega)]

/-- A child chord relabels to a parent chord other than `C`; a child edge relabels to a parent edge or to `C`. -/
lemma pkQ_pl {N b n : ℕ} {C : ℕ × ℕ}
    (hA : ∀ d ∈ diagonals n, relab N b d ∈ diagonals N ∧ relab N b d ≠ C)
    (hB : ∀ x y, 1 ≤ x → x < y → y ≤ n → (x, y) ∉ diagonals n →
      relab N b (x, y) ∉ diagonals N ∨ relab N b (x, y) = C)
    {x y : ℕ} (hx : 1 ≤ x) (hxy : x < y) (hy : y ≤ n) :
    zeroAt R C (planarP R N (x + b - 1) (y + b - 1)) = rename (relab N b) (planarP R n x y) := by
  have e1 : planarP R N (x + b - 1) (y + b - 1) =
      if relab N b (x, y) ∈ diagonals N then X (relab N b (x, y)) else 0 := rfl
  have e2 : planarP R n x y = if (x, y) ∈ diagonals n then X (x, y) else 0 := by
    unfold planarP; rw [p3b_npair hx hxy.le hy]
  rw [e1, e2]
  by_cases hd : (x, y) ∈ diagonals n
  · obtain ⟨h1, h2⟩ := hA _ hd
    rw [if_pos h1, if_pos hd, pkI_zeroAt_X, if_neg h2, rename_X]
  · rw [if_neg hd, map_zero]
    rcases hB x y hx hxy hy hd with h | h
    · rw [if_neg h, map_zero]
    · split_ifs
      · rw [h, pkI_zeroAt_X, if_pos rfl]
      · rw [map_zero]

lemma pkQ_side {N b n : ℕ} {C : ℕ × ℕ} {G G' : Finset (ℕ × ℕ)}
    (hA : ∀ d ∈ diagonals n, relab N b d ∈ diagonals N ∧ relab N b d ≠ C)
    (hB : ∀ x y, 1 ≤ x → x < y → y ≤ n → (x, y) ∉ diagonals n →
      relab N b (x, y) ∉ diagonals N ∨ relab N b (x, y) = C)
    (hG : ∀ d ∈ diagonals n, (relab N b d ∈ G' ↔ d ∈ G)) (hCG : C ∈ G')
    {x y : ℕ} (hx : 1 ≤ x) (hxy : x < y) (hy : y ≤ n) :
    SideOK n G (x, y) ↔ SideOK N G' (x + b - 1, y + b - 1) := by
  show npair n x y ∈ G ∨ npair n x y ∉ diagonals n ↔ relab N b (x, y) ∈ G' ∨ relab N b (x, y) ∉ diagonals N
  rw [p3b_npair hx hxy.le hy]
  by_cases hd : (x, y) ∈ diagonals n
  · rw [hG _ hd]
    have h1 := (hA _ hd).1
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact absurd hd h
    · rintro (h | h)
      · exact Or.inl h
      · exact absurd h1 h
  · constructor
    · intro _
      rcases hB x y hx hxy hy hd with h | h
      · exact Or.inr h
      · rw [h]; exact Or.inl hCG
    · intro _; exact Or.inr hd

lemma pkQ_V_rel {N b n π : ℕ} {C : ℕ × ℕ} (hπ : π < 2) (hb : 1 ≤ b)
    (hA : ∀ d ∈ diagonals n, relab N b d ∈ diagonals N ∧ relab N b d ≠ C)
    (hB : ∀ x y, 1 ≤ x → x < y → y ≤ n → (x, y) ∉ diagonals n →
      relab N b (x, y) ∉ diagonals N ∨ relab N b (x, y) = C)
    {a1 a2 a3 a4 : ℕ} (h : 1 ≤ a1 ∧ a1 < a2 ∧ a2 < a3 ∧ a3 < a4 ∧ a4 ≤ n) :
    zeroAt R C (pkQ_V R N π (a1 + b - 1) (a2 + b - 1) (a3 + b - 1) (a4 + b - 1)) =
      rename (relab N b) (pkQ_V R n ((π + b + 1) % 2) a1 a2 a3 a4) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  unfold pkQ_V
  rw [pkQ_pl_eq (R := R) (pkQ_npair_comm N (a4 + b - 1) (a1 + b - 1)),
    pkQ_pl_eq (R := R) (pkQ_npair_comm n a4 a1)]
  by_cases hp : a1 % 2 = (π + b + 1) % 2
  · rw [if_pos (show (a1 + b - 1) % 2 = π by omega), if_pos hp]
    simp only [map_sub, map_add]
    rw [pkQ_pl hA hB (x := a1) (y := a3) (by omega) (by omega) (by omega),
      pkQ_pl hA hB (x := a2) (y := a4) (by omega) (by omega) (by omega),
      pkQ_pl hA hB (x := a2) (y := a3) (by omega) (by omega) (by omega),
      pkQ_pl hA hB (x := a1) (y := a4) (by omega) (by omega) (by omega)]
  · rw [if_neg (show ¬ (a1 + b - 1) % 2 = π by omega), if_neg hp]
    simp only [map_sub, map_add]
    rw [pkQ_pl hA hB (x := a1) (y := a3) (by omega) (by omega) (by omega),
      pkQ_pl hA hB (x := a2) (y := a4) (by omega) (by omega) (by omega),
      pkQ_pl hA hB (x := a1) (y := a2) (by omega) (by omega) (by omega),
      pkQ_pl hA hB (x := a3) (y := a4) (by omega) (by omega) (by omega)]

lemma pkQ_hL {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N) (hne : ¬ (i = 1 ∧ j = N)) :
    (∀ d ∈ diagonals (j - i + 1), relab N i d ∈ diagonals N ∧ relab N i d ≠ (i, j)) ∧
    (∀ x y, 1 ≤ x → x < y → y ≤ j - i + 1 → (x, y) ∉ diagonals (j - i + 1) →
      relab N i (x, y) ∉ diagonals N ∨ relab N i (x, y) = (i, j)) := by
  refine ⟨fun d hd => ?_, fun x y hx hxy hy hd => ?_⟩
  · obtain ⟨h1, h2, -⟩ := pkSp_mapL hi hij hjN hne hd
    exact ⟨h1, pkSp_In_ne h2⟩
  · rw [mem_diagonals] at hd; dsimp only at hd
    have h := pkSp_spec2 (N := N) (b := i) (a := x) (c := y) (by omega) hx hxy (by omega) (by omega)
    by_cases hy1 : y = x + 1
    · left; rw [mem_diagonals]; omega
    · right; exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)

lemma pkQ_hR {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N) (hne : ¬ (i = 1 ∧ j = N))
    (hE : N % 2 = 0) :
    (∀ d ∈ diagonals (N - j + i + 1), relab N j d ∈ diagonals N ∧ relab N j d ≠ (i, j)) ∧
    (∀ x y, 1 ≤ x → x < y → y ≤ N - j + i + 1 → (x, y) ∉ diagonals (N - j + i + 1) →
      relab N j (x, y) ∉ diagonals N ∨ relab N j (x, y) = (i, j)) := by
  refine ⟨fun d hd => ?_, fun x y hx hxy hy hd => ?_⟩
  · obtain ⟨h1, h2, -⟩ := pkSp_mapR hi hij hjN hne hE hd
    exact ⟨h1, pkSp_Out_ne h2⟩
  · rw [mem_diagonals] at hd; dsimp only at hd
    have h := pkSp_spec2 (N := N) (b := j) (a := x) (c := y) (by omega) hx hxy (by omega) (by omega)
    by_cases hy1 : y = x + 1
    · left; rw [mem_diagonals]; omega
    · right; exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)

lemma pkQ_nc {N i j : ℕ} {G' : Finset (ℕ × ℕ)} (hi : 1 ≤ i) (hjN : j ≤ N)
    (hG' : ∀ p ∈ G', ¬ Crosses p (i, j)) {x y : ℕ} (hx : 1 ≤ x) (hxy : x < y) (hy : y ≤ N)
    (h : SideOK N G' (x, y)) : ¬ Crosses (x, y) (i, j) := by
  have h' : npair N x y ∈ G' ∨ npair N x y ∉ diagonals N := h
  rw [p3b_npair hx hxy.le hy] at h'
  rcases h' with h' | h'
  · exact hG' _ h'
  · rw [mem_diagonals] at h'; dsimp only at h'; simp only [Crosses]; omega

/-- A quad of the glued quadrangulation not inside `i..j` has no corner strictly inside `i..j` (parity: `C` is odd,
opposite corners of a quad have equal parity). -/
lemma pkQ_out {N i j : ℕ} {G' : Finset (ℕ × ℕ)} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N)
    (hodd : (j - i) % 2 = 1) (hGo : G' ⊆ oddDiagonals N) (hG' : ∀ p ∈ G', ¬ Crosses p (i, j))
    {q : Quad} (hq : q ∈ quads N G') (hL : ¬ (i ≤ q.u1 ∧ q.u4 ≤ j)) :
    (q.u1 ≤ i ∨ j ≤ q.u1) ∧ (q.u2 ≤ i ∨ j ≤ q.u2) ∧ (q.u3 ≤ i ∨ j ≤ q.u3) ∧ (q.u4 ≤ i ∨ j ≤ q.u4) := by
  obtain ⟨p1, p2, p3⟩ := p3b_quads_alternating hGo hq
  obtain ⟨hI, s1, s2, s3, s4⟩ := pkQ_mem_quads.1 hq
  rw [p3b_mem_quadIdx] at hI
  have c1 := pkQ_nc hi hjN hG' (by omega) (by omega) (by omega) s1
  have c2 := pkQ_nc hi hjN hG' (by omega) (by omega) (by omega) s2
  have c3 := pkQ_nc hi hjN hG' (by omega) (by omega) (by omega) s3
  have c4 := pkQ_nc hi hjN hG' (by omega) (by omega) (by omega) s4
  simp only [Crosses] at c1 c2 c3 c4
  omega

lemma pkQ_quad_iff {N b n : ℕ} {G G' : Finset (ℕ × ℕ)} (hb : 1 ≤ b) (hn : n ≤ N) (hnb : n + b - 1 ≤ 2 * N)
    (hS : ∀ x y, 1 ≤ x → x < y → y ≤ n → (SideOK n G (x, y) ↔ SideOK N G' (x + b - 1, y + b - 1)))
    {q : Quad} (hq : q ∈ quadIdx n) : q ∈ quads n G ↔ pkQ_lift N b q ∈ quads N G' := by
  have hr := p3b_mem_quadIdx.1 hq
  rw [pkQ_mem_quads, pkQ_mem_quads, pkQ_lift_Ok hn hq]
  unfold pkQ_Ok
  rw [hS q.u1 q.u2 (by omega) (by omega) (by omega), hS q.u2 q.u3 (by omega) (by omega) (by omega),
    hS q.u3 q.u4 (by omega) (by omega) (by omega), hS q.u1 q.u4 (by omega) (by omega) (by omega)]
  constructor
  · intro h; exact ⟨pkQ_lift_idx hb hn hnb hq, h.2⟩
  · intro h; exact ⟨hq, h.2⟩

lemma pkQ_lift_inL {N i j : ℕ} (hi : 1 ≤ i) (hjN : j ≤ N) {q : Quad} (hq : q ∈ quadIdx (j - i + 1)) :
    i ≤ (pkQ_lift N i q).u1 ∧ (pkQ_lift N i q).u4 ≤ j := by
  rw [p3b_mem_quadIdx] at hq
  rcases pkQ_lift_spec N i q with ⟨c, e⟩ | ⟨c, e⟩ | ⟨c, e⟩ | ⟨c, e⟩ | ⟨c, e⟩ <;> rw [e] <;> dsimp only <;> omega

lemma pkQ_lift_outL {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N) {q : Quad}
    (hq : q ∈ quadIdx (N - j + i + 1)) : ¬ (i ≤ (pkQ_lift N j q).u1 ∧ (pkQ_lift N j q).u4 ≤ j) := by
  rw [p3b_mem_quadIdx] at hq
  rcases pkQ_lift_spec N j q with ⟨c, e⟩ | ⟨c, e⟩ | ⟨c, e⟩ | ⟨c, e⟩ | ⟨c, e⟩ <;> rw [e] <;> dsimp only <;> omega

lemma pkQ_unlift_idxL {N i j : ℕ} (hi : 1 ≤ i) {q : Quad} (hq : q ∈ quadIdx N) (h : i ≤ q.u1 ∧ q.u4 ≤ j) :
    pkQ_unlift N i q ∈ quadIdx (j - i + 1) := by
  rw [p3b_mem_quadIdx] at hq
  rcases pkQ_unlift_spec N i q with ⟨c, e⟩ | ⟨c, e⟩ | ⟨c, e⟩ | ⟨c, e⟩ | ⟨c, e⟩ <;> rw [e, p3b_mem_quadIdx] <;>
    dsimp only <;> omega

lemma pkQ_unlift_idxR {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N) {q : Quad} (hq : q ∈ quadIdx N)
    (h : (q.u1 ≤ i ∨ j ≤ q.u1) ∧ (q.u2 ≤ i ∨ j ≤ q.u2) ∧ (q.u3 ≤ i ∨ j ≤ q.u3) ∧ (q.u4 ≤ i ∨ j ≤ q.u4)) :
    pkQ_unlift N j q ∈ quadIdx (N - j + i + 1) := by
  rw [p3b_mem_quadIdx] at hq
  rcases pkQ_unlift_spec N j q with ⟨c, e⟩ | ⟨c, e⟩ | ⟨c, e⟩ | ⟨c, e⟩ | ⟨c, e⟩ <;> rw [e, p3b_mem_quadIdx] <;>
    dsimp only <;> omega

/-- **Per-quadrangulation B.2**: the vertex factors of a glued quadrangulation, with `X_C = 0`, are the relabelled
vertex factors of the two children with the induced polarities `(π + b + 1) % 2`. -/
lemma pkQ_prod_quads {N i j π : ℕ} (hπ : π < 2) (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N)
    (hne : ¬ (i = 1 ∧ j = N)) (hE : N % 2 = 0) (hodd : (j - i) % 2 = 1) (hC : (i, j) ∈ oddDiagonals N)
    {G1 G2 : Finset (ℕ × ℕ)}
    (h1 : pkSp_IsMax (pkSp_S (fun r => r = 1) (j - i + 1)) G1)
    (h2 : pkSp_IsMax (pkSp_S (fun r => r = 1) (N - j + i + 1)) G2) :
    zeroAt R (i, j) (∏ q ∈ quads N (pkSp_glue N i j G1 G2), vnumP R N π q) =
      (∏ q ∈ quads (j - i + 1) G1, rename (relab N i) (vnumP R (j - i + 1) ((π + i + 1) % 2) q)) *
        ∏ q ∈ quads (N - j + i + 1) G2, rename (relab N j) (vnumP R (N - j + i + 1) ((π + j + 1) % 2) q) := by
  have hmax := pkSp_glue_max (Q := fun r => r = 1) hi hij hjN hne hE hC h1 h2
  have hGo : pkSp_glue N i j G1 G2 ⊆ oddDiagonals N := hmax.1
  have hL : G1 ⊆ diagonals (j - i + 1) := fun d hd => (pkSp_mem_S.1 (h1.1 hd)).1
  have hR : G2 ⊆ diagonals (N - j + i + 1) := fun d hd => (pkSp_mem_S.1 (h2.1 hd)).1
  have hGoL : G1 ⊆ oddDiagonals (j - i + 1) := h1.1
  have hGoR : G2 ⊆ oddDiagonals (N - j + i + 1) := h2.1
  have hCG : (i, j) ∈ pkSp_glue N i j G1 G2 := mem_insert_self _ _
  have hnc : ∀ p ∈ pkSp_glue N i j G1 G2, ¬ Crosses p (i, j) := fun p hp =>
    pkSp_glue_nc hi hij hjN hne hE hL hR hp
  obtain ⟨hAL, hBL⟩ := pkQ_hL hi hij hjN hne
  obtain ⟨hAR, hBR⟩ := pkQ_hR hi hij hjN hne hE
  have hSL : ∀ x y, 1 ≤ x → x < y → y ≤ j - i + 1 →
      (SideOK (j - i + 1) G1 (x, y) ↔ SideOK N (pkSp_glue N i j G1 G2) (x + i - 1, y + i - 1)) :=
    fun x y hx hxy hy =>
      pkQ_side hAL hBL (fun d hd => pkSp_mem_glue_L hi hij hjN hne hE hL hR hd) hCG hx hxy hy
  have hSR : ∀ x y, 1 ≤ x → x < y → y ≤ N - j + i + 1 →
      (SideOK (N - j + i + 1) G2 (x, y) ↔ SideOK N (pkSp_glue N i j G1 G2) (x + j - 1, y + j - 1)) :=
    fun x y hx hxy hy =>
      pkQ_side hAR hBR (fun d hd => pkSp_mem_glue_R hi hij hjN hne hE hL hR hd) hCG hx hxy hy
  rw [map_prod, ← prod_filter_mul_prod_filter_not (quads N (pkSp_glue N i j G1 G2))
    (fun q => i ≤ q.u1 ∧ q.u4 ≤ j)]
  congr 1
  · refine (prod_nbij' (pkQ_lift N i) (pkQ_unlift N i) ?_ ?_ ?_ ?_ ?_).symm
    · intro q hq
      have hq' : q ∈ quads (j - i + 1) G1 := hq
      have hqI := (pkQ_mem_quads.1 hq').1
      exact mem_filter.2 ⟨(pkQ_quad_iff (by omega) (by omega) (by omega) hSL hqI).1 hq',
        pkQ_lift_inL hi hjN hqI⟩
    · intro q hq
      have hq' := mem_filter.1 hq
      have hqI := (pkQ_mem_quads.1 hq'.1).1
      have hu := pkQ_unlift_idxL hi hqI hq'.2
      refine (pkQ_quad_iff (by omega) (by omega) (by omega) hSL hu).2 ?_
      rw [pkQ_lift_unlift hi (by omega) hqI]
      exact hq'.1
    · intro q hq
      exact pkQ_unlift_lift hi (by omega) (pkQ_mem_quads.1 hq).1
    · intro q hq
      exact pkQ_lift_unlift hi (by omega) (pkQ_mem_quads.1 (mem_filter.1 hq).1).1
    · intro q hq
      have hqI := (pkQ_mem_quads.1 hq).1
      rw [pkQ_V_lift (b := i) hπ hE (by omega) hqI (p3b_quads_alternating hGoL hq),
        pkQ_V_rel hπ hi hAL hBL (p3b_mem_quadIdx.1 hqI)]
      (try rfl)
  · refine (prod_nbij' (pkQ_lift N j) (pkQ_unlift N j) ?_ ?_ ?_ ?_ ?_).symm
    · intro q hq
      have hq' : q ∈ quads (N - j + i + 1) G2 := hq
      have hqI := (pkQ_mem_quads.1 hq').1
      exact mem_filter.2 ⟨(pkQ_quad_iff (by omega) (by omega) (by omega) hSR hqI).1 hq',
        pkQ_lift_outL hi hij hjN hqI⟩
    · intro q hq
      have hq' := mem_filter.1 hq
      have hqI := (pkQ_mem_quads.1 hq'.1).1
      have hu := pkQ_unlift_idxR hi hij hjN hqI (pkQ_out hi hij hjN hodd hGo hnc hq'.1 hq'.2)
      refine (pkQ_quad_iff (by omega) (by omega) (by omega) hSR hu).2 ?_
      rw [pkQ_lift_unlift (by omega) hjN hqI]
      exact hq'.1
    · intro q hq
      exact pkQ_unlift_lift (by omega) (by omega) (pkQ_mem_quads.1 hq).1
    · intro q hq
      exact pkQ_lift_unlift (by omega) hjN (pkQ_mem_quads.1 (mem_filter.1 hq).1).1
    · intro q hq
      have hqI := (pkQ_mem_quads.1 hq).1
      rw [pkQ_V_lift (b := j) hπ hE (by omega) hqI (p3b_quads_alternating hGoR hq),
        pkQ_V_rel hπ (by omega) hAR hBR (p3b_mem_quadIdx.1 hqI)]
      (try rfl)

/-- The odd diagonals missing from a glued quadrangulation: those crossing the chord and the children's. -/
lemma pkQ_odd_prod {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N) (hne : ¬ (i = 1 ∧ j = N))
    (hE : N % 2 = 0) {T1 T2 : Finset (ℕ × ℕ)} (h1 : T1 ⊆ diagonals (j - i + 1))
    (h2 : T2 ⊆ diagonals (N - j + i + 1)) :
    ∏ d ∈ oddDiagonals N \ pkSp_glue N i j T1 T2, (X d : MvPolynomial (ℕ × ℕ) R) =
      crossProd R N (i, j) * rename (relab N i) (∏ d ∈ oddDiagonals (j - i + 1) \ T1, X d) *
        rename (relab N j) (∏ d ∈ oddDiagonals (N - j + i + 1) \ T2, X d) := by
  have injL : Set.InjOn (relab N i) (diagonals (j - i + 1) : Set (ℕ × ℕ)) := fun x hx y hy h =>
    pkSp_inj (N := N) (b := i) (n := j - i + 1) (by omega) (by omega) (by omega) hx hy h
  have injR : Set.InjOn (relab N j) (diagonals (N - j + i + 1) : Set (ℕ × ℕ)) := fun x hx y hy h =>
    pkSp_inj (N := N) (b := j) (n := N - j + i + 1) (by omega) (by omega) (by omega) hx hy h
  have hoddL : ∀ d ∈ oddDiagonals (j - i + 1), d ∈ diagonals (j - i + 1) := fun d hd => (mem_filter.1 hd).1
  have hoddR : ∀ d ∈ oddDiagonals (N - j + i + 1), d ∈ diagonals (N - j + i + 1) :=
    fun d hd => (mem_filter.1 hd).1
  have hodd_set : oddDiagonals N \ pkSp_glue N i j T1 T2 =
      (oddDiagonals N).filter (fun d => Crosses d (i, j)) ∪
        ((oddDiagonals (j - i + 1) \ T1).image (relab N i) ∪
          (oddDiagonals (N - j + i + 1) \ T2).image (relab N j)) := by
    ext d
    rw [mem_sdiff, mem_union, mem_union, mem_filter, mem_image, mem_image]
    constructor
    · rintro ⟨hd, hnot⟩
      rcases pkSp_part (i := i) (j := j) (mem_filter.1 hd).1 with rfl | hc | hin | hout
      · exact absurd (mem_insert_self _ _) hnot
      · exact Or.inl ⟨hd, hc⟩
      · rw [pkSp_odd_eq] at hd
        obtain ⟨d', hd', rfl⟩ := pkSp_surjLQ hi hij hjN hne hd hin
        rw [← pkSp_odd_eq] at hd'
        refine Or.inr (Or.inl ⟨d', mem_sdiff.2 ⟨hd', fun h => hnot ?_⟩, rfl⟩)
        exact (pkSp_mem_glue_L hi hij hjN hne hE h1 h2 (hoddL _ hd')).2 h
      · rw [pkSp_odd_eq] at hd
        obtain ⟨d', hd', rfl⟩ := pkSp_surjRQ hi hij hjN hne hE hd hout
        rw [← pkSp_odd_eq] at hd'
        refine Or.inr (Or.inr ⟨d', mem_sdiff.2 ⟨hd', fun h => hnot ?_⟩, rfl⟩)
        exact (pkSp_mem_glue_R hi hij hjN hne hE h1 h2 (hoddR _ hd')).2 h
    · rintro (⟨hd, hc⟩ | ⟨d', hd', rfl⟩ | ⟨d', hd', rfl⟩)
      · exact ⟨hd, fun h => pkSp_glue_nc hi hij hjN hne hE h1 h2 h hc⟩
      · obtain ⟨hd'o, hnT⟩ := mem_sdiff.1 hd'
        rw [pkSp_odd_eq] at hd'o
        refine ⟨by rw [pkSp_odd_eq]; exact (pkSp_mapLQ hi hij hjN hne hd'o).1, fun h => hnT ?_⟩
        exact (pkSp_mem_glue_L hi hij hjN hne hE h1 h2 (pkSp_mem_S.1 hd'o).1).1 h
      · obtain ⟨hd'o, hnT⟩ := mem_sdiff.1 hd'
        rw [pkSp_odd_eq] at hd'o
        refine ⟨by rw [pkSp_odd_eq]; exact (pkSp_mapRQ hi hij hjN hne hE hd'o).1, fun h => hnT ?_⟩
        exact (pkSp_mem_glue_R hi hij hjN hne hE h1 h2 (pkSp_mem_S.1 hd'o).1).1 h
  have hdisj1 : Disjoint ((oddDiagonals N).filter (fun d => Crosses d (i, j)))
      ((oddDiagonals (j - i + 1) \ T1).image (relab N i) ∪
        (oddDiagonals (N - j + i + 1) \ T2).image (relab N j)) := by
    rw [disjoint_left]
    intro d hd hd'
    have hc := (mem_filter.1 hd).2
    rw [mem_union, mem_image, mem_image] at hd'
    rcases hd' with ⟨d', hd', rfl⟩ | ⟨d', hd', rfl⟩
    · exact pkSp_In_nc (pkSp_mapL hi hij hjN hne (hoddL _ (mem_sdiff.1 hd').1)).2.1 hc
    · exact pkSp_Out_nc (pkSp_mapR hi hij hjN hne hE (hoddR _ (mem_sdiff.1 hd').1)).2.1 hc
  have hdisjLR : ∀ (A B : Finset (ℕ × ℕ)), A ⊆ diagonals (j - i + 1) → B ⊆ diagonals (N - j + i + 1) →
      Disjoint (A.image (relab N i)) (B.image (relab N j)) := by
    intro A B hA hB
    rw [disjoint_left]
    intro d hd hd'
    rw [mem_image] at hd hd'
    obtain ⟨a, ha, rfl⟩ := hd
    obtain ⟨b, hb, hba⟩ := hd'
    obtain ⟨haN, hin, -⟩ := pkSp_mapL hi hij hjN hne (hA ha)
    obtain ⟨-, hout, -⟩ := pkSp_mapR hi hij hjN hne hE (hB hb)
    rw [hba] at hout
    exact pkSp_In_not_Out (pkSp_lt haN) hin hout
  rw [hodd_set, prod_union hdisj1,
    prod_union (hdisjLR _ _ (fun d hd => hoddL _ (mem_sdiff.1 hd).1) (fun d hd => hoddR _ (mem_sdiff.1 hd).1)),
    prod_image (injL.mono fun d hd => hoddL _ (mem_sdiff.1 hd).1),
    prod_image (injR.mono fun d hd => hoddR _ (mem_sdiff.1 hd).1), crossProd, map_prod, map_prod]
  simp only [rename_X]
  ring

lemma pkQ_tr (n : ℕ) (T : Finset (ℕ × ℕ)) :
    T ∈ quadrangulations n ↔ pkSp_IsMax (pkSp_S (fun r => r = 1) n) T := by
  show T ∈ (oddDiagonals n).powerset.filter (IsQuadrangulation n) ↔ _
  rw [mem_filter, mem_powerset]
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨h.1, h⟩

/-- Setting `X_C = 0` keeps exactly the quadrangulations through `C`. -/
lemma pkQ_zeroAt_QP {N π : ℕ} {C : ℕ × ℕ} (hC : C ∈ oddDiagonals N) :
    zeroAt R C (QP R N π) = ∑ G ∈ (quadrangulations N).filter (fun G => C ∈ G),
      zeroAt R C (∏ q ∈ quads N G, vnumP R N π q) * ∏ d ∈ oddDiagonals N \ G, X d := by
  rw [QP, map_sum, sum_filter]
  refine sum_congr rfl fun G _ => ?_
  rw [map_mul]
  split_ifs with hCG
  · congr 1
    rw [map_prod]
    refine prod_congr rfl fun d hd => ?_
    have hdC : d ≠ C := fun h => (mem_sdiff.1 hd).2 (by rw [h]; exact hCG)
    rw [pkI_zeroAt_X, if_neg hdC]
  · have h0 : ∏ d ∈ oddDiagonals N \ G, zeroAt R C (X d) = 0 :=
      prod_eq_zero (mem_sdiff.2 ⟨hC, hCG⟩) (by rw [pkI_zeroAt_X, if_pos rfl])
    have h0' : zeroAt R C (∏ d ∈ oddDiagonals N \ G, (X d : MvPolynomial (ℕ × ℕ) R)) = 0 := by
      rw [map_prod]; exact h0
    rw [h0', mul_zero]

/-- `QP_residue` in the frozen variable names (PROOFS Lemma B.2, numerator form). -/
theorem pkQ_QP_residue {N π : ℕ} (hE : N % 2 = 0) (hπ : π < 2) {C : ℕ × ℕ} (hC : C ∈ oddDiagonals N) :
    zeroAt R C (QP R N π) =
      rename (relab N C.1) (QP R (C.2 - C.1 + 1) ((π + C.1 + 1) % 2)) *
        rename (relab N C.2) (QP R (N - C.2 + C.1 + 1) ((π + C.2 + 1) % 2)) * crossProd R N C := by
  rw [pkQ_zeroAt_QP hC]
  obtain ⟨i, j⟩ := C
  have hC1 := mem_filter.1 hC
  have hC2 := mem_diagonals.1 hC1.1
  dsimp only at hC1 hC2 ⊢
  obtain ⟨hi, hjN, hij, hne⟩ := hC2
  have hodd := hC1.2
  have hQC : (i, j) ∈ pkSp_S (fun r => r = 1) N := hC
  rw [pkSp_sum_split quadrangulations pkQ_tr hi hij hjN hne hE hQC]
  have hsum : ∀ x ∈ quadrangulations (j - i + 1) ×ˢ quadrangulations (N - j + i + 1),
      zeroAt R (i, j) (∏ q ∈ quads N (pkSp_glue N i j x.1 x.2), vnumP R N π q) *
        ∏ d ∈ oddDiagonals N \ pkSp_glue N i j x.1 x.2, X d =
      rename (relab N i) ((∏ q ∈ quads (j - i + 1) x.1, vnumP R (j - i + 1) ((π + i + 1) % 2) q) *
          ∏ d ∈ oddDiagonals (j - i + 1) \ x.1, X d) *
        rename (relab N j) ((∏ q ∈ quads (N - j + i + 1) x.2, vnumP R (N - j + i + 1) ((π + j + 1) % 2) q) *
          ∏ d ∈ oddDiagonals (N - j + i + 1) \ x.2, X d) * crossProd R N (i, j) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := mem_product.1 hx
    have m1 := (pkQ_tr _ _).1 hx1
    have m2 := (pkQ_tr _ _).1 hx2
    have hL : x.1 ⊆ diagonals (j - i + 1) := fun d hd => (pkSp_mem_S.1 (m1.1 hd)).1
    have hR : x.2 ⊆ diagonals (N - j + i + 1) := fun d hd => (pkSp_mem_S.1 (m2.1 hd)).1
    rw [pkQ_prod_quads hπ hi hij hjN hne hE hodd hC m1 m2, pkQ_odd_prod hi hij hjN hne hE hL hR]
    simp only [map_mul, map_prod]
    ring
  rw [sum_congr rfl hsum, ← sum_mul, QP, QP, map_sum, map_sum, sum_mul_sum, sum_product]

/-- `sorry` (3c-b). **PROOFS Lemma B.2 (factorisation of Q), numerator form**, with the quadrangulation bijection and
the induced polarities `π_L ≡ π − (i − 1)`, `π_R ≡ π − (j − 1)`. [mirror D5: every odd chord, both π, N = 6, 8, 10] -/
theorem QP_residue {N π : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (hπ : π < 2) {C : ℕ × ℕ} (hC : C ∈ oddDiagonals N) :
    zeroAt R C (QP R N π) =
      rename (relab N C.1) (QP R (C.2 - C.1 + 1) ((π + C.1 + 1) % 2)) *
        rename (relab N C.2) (QP R (N - C.2 + C.1 + 1) ((π + C.2 + 1) % 2)) * crossProd R N C :=
  pkQ_QP_residue hE hπ hC

end Poly

/-! ## 4. The row loci and Lemma B.5 -/

section Rows

open MvPolynomial

variable {K : Type*} [Field K]

lemma pkI_planar_addR (N : ℕ) (X : ℕ × ℕ → K) (a b : ℕ) : planar N X a (b + N) = planar N X a b := by
  unfold planar
  rw [vtx_add_n]

lemma pkI_mesh_addR (N : ℕ) (X : ℕ × ℕ → K) (a b : ℕ) : mesh N X a (b + N) = mesh N X a b := by
  unfold mesh
  rw [show b + N + 1 = (b + 1) + N by omega, pkI_planar_addR, pkI_planar_addR, pkI_planar_addR,
    pkI_planar_addR]

lemma pkI_planar_symm (N : ℕ) (X : ℕ × ℕ → K) (u v : ℕ) : planar N X u v = planar N X v u := by
  unfold planar
  rw [min_comm, max_comm]

lemma pkI_mesh_symm (N : ℕ) (X : ℕ × ℕ → K) (u v : ℕ) : mesh N X u v = mesh N X v u := by
  unfold mesh
  rw [pkI_planar_symm N X u v, pkI_planar_symm N X (u + 1) (v + 1), pkI_planar_symm N X u (v + 1),
    pkI_planar_symm N X (u + 1) v]
  ring

lemma pkI_row_vtx {N i : ℕ} (hN : 4 ≤ N) (hi : 1 ≤ i ∧ i ≤ N) :
    ((2 ≤ i ∧ vtx N (i + N - 1) = i - 1) ∨ (i = 1 ∧ vtx N (i + N - 1) = N)) ∧
      ((i < N ∧ vtx N (i + 1) = i + 1) ∨ (i = N ∧ vtx N (i + 1) = 1)) := by
  rw [pkI_vtx (N := N) (x := i + N - 1) (by omega) (by omega), pkI_vtx (N := N) (x := i + 1) (by omega) (by omega)]
  constructor <;> split_ifs <;> omega

/-- `sorry` (3c-b). Phase 3's `Z_{{i−1,i+1}}` and Phase 1's skinny rectangle `R_{1,i}` are the same locus (the
row-`i` tiles; PROOFS Lemma B.4 "R_i = Z_{{i−1,i+1}}"). [mirror D9, N ≤ 12, every i] -/
theorem onZT_row_iff {N i : ℕ} (hN : 4 ≤ N) (hi : 1 ≤ i ∧ i ≤ N) (X : ℕ × ℕ → K) :
    OnZT N {vtx N (i + N - 1), vtx N (i + 1)} X ↔ OnRect N 1 i X := by
  obtain ⟨ht1, ht2⟩ := pkI_row_vtx hN hi
  constructor
  · intro hZ a ha j hj
    simp only [mem_Ico, mem_Icc] at ha hj
    rw [show a = i by omega]
    by_cases hjN : j ≤ N
    · refine hZ i (mem_Icc.2 (by omega)) j (mem_Icc.2 (by omega)) ?_
      show i ∉ _ ∧ j ∉ _ ∧ (∃ t ∈ _, min i j < t ∧ t < max i j) ∧ (∃ t ∈ _, t < min i j ∨ max i j < t)
      rw [min_eq_left (by omega : i ≤ j), max_eq_right (by omega : i ≤ j)]
      simp only [mem_insert, mem_singleton]
      exact ⟨by omega, by omega, ⟨vtx N (i + 1), Or.inr rfl, by omega⟩, ⟨vtx N (i + N - 1), Or.inl rfl, by omega⟩⟩
    · obtain ⟨b, rfl⟩ : ∃ b, j = b + N := ⟨j - N, by omega⟩
      rw [pkI_mesh_addR, pkI_mesh_symm]
      refine hZ b (mem_Icc.2 (by omega)) i (mem_Icc.2 (by omega)) ?_
      show b ∉ _ ∧ i ∉ _ ∧ (∃ t ∈ _, min b i < t ∧ t < max b i) ∧ (∃ t ∈ _, t < min b i ∨ max b i < t)
      rw [min_eq_left (by omega : b ≤ i), max_eq_right (by omega : b ≤ i)]
      simp only [mem_insert, mem_singleton]
      exact ⟨by omega, by omega, ⟨vtx N (i + N - 1), Or.inl rfl, by omega⟩, ⟨vtx N (i + 1), Or.inr rfl, by omega⟩⟩
  · intro hR
    have row : ∀ c, 1 ≤ c → c ≤ N → c ≠ vtx N (i + N - 1) → c ≠ vtx N (i + 1) → c ≠ i → mesh N X i c = 0 := by
      intro c hc1 hc2 hc3 hc4 hc5
      by_cases hci : i < c
      · exact hR i (mem_Ico.2 ⟨le_rfl, by omega⟩) c (mem_Icc.2 ⟨by omega, by omega⟩)
      · rw [← pkI_mesh_addR]
        exact hR i (mem_Ico.2 ⟨le_rfl, by omega⟩) (c + N) (mem_Icc.2 ⟨by omega, by omega⟩)
    intro a ha b hb hST
    obtain ⟨haT, hbT, ⟨t, htT, h1, h2⟩, ⟨t', htT', h3⟩⟩ := hST
    simp only [mem_insert, mem_singleton] at haT hbT htT htT'
    simp only [mem_Icc] at ha hb
    simp only [min_def, max_def] at h1 h2 h3
    have key : a = i ∨ b = i := by
      split_ifs at h1 h2 h3 <;> omega
    rcases key with h | h
    · rw [h]
      exact row b hb.1 hb.2 (fun e => hbT (Or.inl e)) (fun e => hbT (Or.inr e)) (by split_ifs at h1 h2 <;> omega)
    · rw [pkI_mesh_symm, h]
      exact row a ha.1 ha.2 (fun e => haT (Or.inl e)) (fun e => haT (Or.inr e)) (by split_ifs at h1 h2 <;> omega)

/-- `sorry` (3c-b). `{i − 1, i + 1}` is admissible, of parity `i + 1`. -/
theorem admissible_row {N i : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (hi : 1 ≤ i ∧ i ≤ N) :
    Admissible N ((i + 1) % 2) {vtx N (i + N - 1), vtx N (i + 1)} := by
  obtain ⟨ht1, ht2⟩ := pkI_row_vtx hN hi
  refine And.intro ?_ (And.intro ?_ ?_)
  · intro t ht
    simp only [mem_insert, mem_singleton] at ht
    rw [mem_Icc]
    omega
  · exact (card_pair_eq_two_iff.2 (by omega)).ge
  · intro t ht
    simp only [mem_insert, mem_singleton] at ht
    omega

theorem pkRw_mono (m : Finsupp (ℕ × ℕ) ℕ) (hm : (m.sum fun _ e => e) ≤ 1) :
    m = 0 ∨ ∃ v, m = Finsupp.single v 1 := by
  have hc : Multiset.card (Finsupp.toMultiset m) ≤ 1 := by
    rw [Finsupp.card_toMultiset]; exact hm
  have hm' : m = Multiset.toFinsupp (Finsupp.toMultiset m) := (Multiset.toFinsupp_eq_iff.2 rfl).symm
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hc with h | h
  · left
    rw [hm', Multiset.card_eq_zero.1 h, Multiset.toFinsupp_zero]
  · right
    obtain ⟨v, hv⟩ := Multiset.card_eq_one.1 h
    exact ⟨v, by rw [hm', hv, Multiset.toFinsupp_singleton]⟩

theorem pkRw_add (L : MvPolynomial (ℕ × ℕ) ℚ) (hL : L.totalDegree ≤ 1) (x y : ℕ × ℕ → ℚ) :
    eval (x + y) L + eval 0 L = eval x L + eval y L := by
  simp only [eval_eq]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rcases pkRw_mono m ((le_totalDegree hm).trans hL) with h | ⟨v, h⟩
  · subst h; simp
  · subst h; simp; ring

theorem pkRw_planar {N r j : ℕ} (x : ℕ × ℕ → ℚ)
    (h : ∀ p : ℕ × ℕ, (p.1 = vtx N r ∨ p.2 = vtx N r) → x p = 0) : planar N x r j = 0 := by
  show (if (min (vtx N r) (vtx N j), max (vtx N r) (vtx N j)) ∈ diagonals N then
    x (min (vtx N r) (vtx N j), max (vtx N r) (vtx N j)) else 0) = 0
  split_ifs
  · apply h
    rcases le_total (vtx N r) (vtx N j) with hle | hle
    · left; exact min_eq_left hle
    · right; exact max_eq_left hle
  · rfl

theorem pkRw_row {N r : ℕ} (x : ℕ × ℕ → ℚ)
    (h : ∀ p : ℕ × ℕ, (p.1 = vtx N r ∨ p.2 = vtx N r ∨ p.1 = vtx N (r + 1) ∨ p.2 = vtx N (r + 1)) →
      x p = 0) : OnRect N 1 r x := by
  intro i hi j _
  have hir : i = r := by have := Finset.mem_Ico.1 hi; omega
  rw [hir]
  have h1 : ∀ k, planar N x r k = 0 := fun k => pkRw_planar x (fun p hp =>
    h p (hp.elim (fun e => Or.inl e) (fun e => Or.inr (Or.inl e))))
  have h2 : ∀ k, planar N x (r + 1) k = 0 := fun k => pkRw_planar x (fun p hp =>
    h p (hp.elim (fun e => Or.inr (Or.inr (Or.inl e))) (fun e => Or.inr (Or.inr (Or.inr e)))))
  show planar N x r j + planar N x (r + 1) (j + 1) - planar N x r (j + 1) - planar N x (r + 1) j = 0
  rw [h1 j, h2 (j + 1), h1 (j + 1), h2 j]
  ring

theorem pkRw_decomp (L : MvPolynomial (ℕ × ℕ) ℚ) (hL : L.totalDegree ≤ 1) (A B C : ℕ × ℕ → Prop)
    [DecidablePred A] [DecidablePred B] (hABC : ∀ p, A p → B p → C p → False)
    (hA : ∀ y : ℕ × ℕ → ℚ, (∀ p, A p → y p = 0) → eval y L = 0)
    (hB : ∀ y : ℕ × ℕ → ℚ, (∀ p, B p → y p = 0) → eval y L = 0)
    (hC : ∀ y : ℕ × ℕ → ℚ, (∀ p, C p → y p = 0) → eval y L = 0) (x : ℕ × ℕ → ℚ) :
    eval x L = 0 := by
  have h0 : eval 0 L = 0 := hA 0 (fun _ _ => rfl)
  have hu := hA (fun p => if A p then 0 else x p) (fun p hp => if_pos hp)
  have hv := hB (fun p => if A p ∧ ¬ B p then x p else 0) (fun p hp => if_neg (fun hc => hc.2 hp))
  have hw := hC (fun p => if A p ∧ B p then x p else 0) (fun p hp => if_neg (fun hc => hABC p hc.1 hc.2 hp))
  have hx : x = (fun p => if A p then 0 else x p) +
      ((fun p => if A p ∧ ¬ B p then x p else 0) + (fun p => if A p ∧ B p then x p else 0)) := by
    ext p
    show x p = (if A p then 0 else x p) + ((if A p ∧ ¬ B p then x p else 0) + (if A p ∧ B p then x p else 0))
    by_cases ha : A p <;> by_cases hb : B p <;> simp [ha, hb]
  have e1 := pkRw_add L hL (fun p => if A p then 0 else x p)
    ((fun p => if A p ∧ ¬ B p then x p else 0) + (fun p => if A p ∧ B p then x p else 0))
  have e2 := pkRw_add L hL (fun p => if A p ∧ ¬ B p then x p else 0) (fun p => if A p ∧ B p then x p else 0)
  rw [hx]
  linarith

/-- `sorry` (3c-b). **PROOFS Lemma B.5: three same-parity rows kill an affine form** (`N ≥ 6`). The constant term is
included: every row locus contains `0`. [mirror D10: full rank for rows a, a+2, a+4, a = 1, 2, N = 6…12] -/
theorem three_rows {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {a : ℕ} (ha : 1 ≤ a ∧ a ≤ 2)
    (L : MvPolynomial (ℕ × ℕ) ℚ) (hL : L.totalDegree ≤ 1)
    (h : ∀ x : ℕ × ℕ → ℚ, (OnRect N 1 a x ∨ OnRect N 1 (a + 2) x ∨ OnRect N 1 (a + 4) x) → eval x L = 0) :
    L = 0 := by
  have v0 : vtx N a = a := vtx_of_mem (by omega) (by omega)
  have v1 : vtx N (a + 1) = a + 1 := vtx_of_mem (by omega) (by omega)
  have v2 : vtx N (a + 2) = a + 2 := vtx_of_mem (by omega) (by omega)
  have v3 : vtx N (a + 2 + 1) = a + 2 + 1 := vtx_of_mem (by omega) (by omega)
  have v4 : vtx N (a + 4) = a + 4 := vtx_of_mem (by omega) (by omega)
  have v5 : vtx N (a + 4 + 1) = a + 4 + 1 ∨ (vtx N (a + 4 + 1) = 1 ∧ a + 4 + 1 = N + 1) := by
    by_cases hc : a + 4 + 1 ≤ N
    · exact Or.inl (vtx_of_mem (by omega) hc)
    · right
      rw [show a + 4 + 1 = 1 + N by omega, vtx_add_n, vtx_of_mem le_rfl (by omega)]
      exact ⟨rfl, by omega⟩
  apply MvPolynomial.funext
  intro x
  rw [map_zero]
  exact pkRw_decomp L hL
    (fun p => p.1 = vtx N a ∨ p.2 = vtx N a ∨ p.1 = vtx N (a + 1) ∨ p.2 = vtx N (a + 1))
    (fun p => p.1 = vtx N (a + 2) ∨ p.2 = vtx N (a + 2) ∨ p.1 = vtx N (a + 2 + 1) ∨ p.2 = vtx N (a + 2 + 1))
    (fun p => p.1 = vtx N (a + 4) ∨ p.2 = vtx N (a + 4) ∨ p.1 = vtx N (a + 4 + 1) ∨ p.2 = vtx N (a + 4 + 1))
    (fun p hA hB hC => by omega)
    (fun y hy => h y (Or.inl (pkRw_row y hy)))
    (fun y hy => h y (Or.inr (Or.inl (pkRw_row y hy))))
    (fun y hy => h y (Or.inr (Or.inr (pkRw_row y hy)))) x

end Rows

/-! ## 5. The rational-function layer, parts (ii)–(iii): generic point, `RatZeroOn`, the line bridge (L-3) -/

section Rational

open MvPolynomial

/-- The field of rational functions in the planar variables. -/
abbrev RF := FractionRing (MvPolynomial (ℕ × ℕ) ℚ)

/-- The generic point: every planar variable is its own indeterminate. -/
noncomputable def gen : ℕ × ℕ → RF := fun d => algebraMap (MvPolynomial (ℕ × ℕ) ℚ) RF (X d)

/-- PROVED. The generic point has no vanishing coordinate, so no `X ≠ 0` side condition survives there. -/
theorem gen_ne_zero (d : ℕ × ℕ) : gen d ≠ 0 := by
  unfold gen
  rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (MvPolynomial (ℕ × ℕ) ℚ) RF)]
  exact X_ne_zero d

/-- `F` restricts to the zero rational function on the set of ℚ-points `V`: `F = P/Q` with `Q` not identically zero on
`V` and `P` identically zero on `V`. For `V` a linear subspace (irreducible) this does not depend on the choice of
`P, Q`. -/
def RatZeroOn (V : Set (ℕ × ℕ → ℚ)) (F : RF) : Prop :=
  ∃ P Q : MvPolynomial (ℕ × ℕ) ℚ, F * algebraMap _ RF Q = algebraMap _ RF P ∧
    (∃ w ∈ V, eval w Q ≠ 0) ∧ ∀ x ∈ V, eval x P = 0

/-- PROVED (the IDEAS L-3 bridge). A polynomial vanishing on a line-closed set `V` wherever `Q ≠ 0`, with `Q`
not identically zero on `V`, vanishes on all of `V`: restrict to the line through `x` and a witness `w`, where
`t ↦ P·Q` is a one-variable polynomial with infinitely many zeros. (Phase 2's `generic_bridge`, abstracted.) -/
theorem line_bridge {σ : Type*} (V : Set (σ → ℚ)) (hV : ∀ x ∈ V, ∀ y ∈ V, ∀ t : ℚ, x + t • (y - x) ∈ V)
    (P Q : MvPolynomial σ ℚ) {w : σ → ℚ} (hw : w ∈ V) (hQw : eval w Q ≠ 0)
    (h : ∀ x ∈ V, eval x Q ≠ 0 → eval x P = 0) : ∀ x ∈ V, eval x P = 0 := by
  intro x hx
  let ℓ : σ → Polynomial ℚ := fun i => Polynomial.C (x i) + Polynomial.X * Polynomial.C (w i - x i)
  have hev : ∀ (F : MvPolynomial σ ℚ) (t : ℚ), (aeval ℓ F).eval t = eval (x + t • (w - x)) F := by
    intro F t
    have hfun : (fun i => Polynomial.aeval t (ℓ i)) = x + t • (w - x) := by
      funext i
      simp [ℓ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Polynomial.coe_aeval_eq_eval, ← AlgHom.comp_apply, comp_aeval, hfun]
    rw [aeval_def, eval]; rfl
  have hq : aeval ℓ Q ≠ 0 := by
    intro h0
    apply hQw
    have := hev Q 1
    rw [h0, Polynomial.eval_zero, one_smul, add_sub_cancel] at this
    exact this.symm
  have hpq : aeval ℓ P * aeval ℓ Q = 0 := by
    apply Polynomial.funext
    intro t
    rw [Polynomial.eval_mul, Polynomial.eval_zero, hev, hev]
    by_cases hQ : eval (x + t • (w - x)) Q = 0
    · rw [hQ, mul_zero]
    · rw [h _ (hV x hx w hw t) hQ, zero_mul]
  have hp := (mul_eq_zero.1 hpq).resolve_right hq
  have := hev P 0
  rw [hp, Polynomial.eval_zero, zero_smul, add_zero] at this
  exact this.symm

/-- The numerator and denominator of Phase 1's `A_n`. -/
noncomputable def ampNum (n : ℕ) : MvPolynomial (ℕ × ℕ) ℚ := ∑ T ∈ triangulations n, ∏ d ∈ diagonals n \ T, X d

noncomputable def diagDen (n : ℕ) : MvPolynomial (ℕ × ℕ) ℚ := ∏ d ∈ diagonals n, X d

/-- PROVED. Numerator lemma for `A_n`, for every ring map into a field. -/
theorem amp_hom {K : Type*} [Field K] (f : MvPolynomial (ℕ × ℕ) ℚ →+* K) (n : ℕ)
    (hX : ∀ d ∈ diagonals n, f (X d) ≠ 0) :
    f (ampNum n) = amp n (fun d => f (X d)) * f (diagDen n) := by
  rw [ampNum, amp, map_sum, sum_mul]
  refine sum_congr rfl fun T hT => ?_
  have hTs : T ⊆ diagonals n := (mem_filter.1 hT).2.1
  rw [map_prod, diagDen, map_prod, ← prod_sdiff hTs]
  have hinv : (∏ d ∈ T, (f (X d))⁻¹) * ∏ d ∈ T, f (X d) = 1 := by
    rw [← prod_mul_distrib]
    exact prod_eq_one fun d hd => inv_mul_cancel₀ (hX d (hTs hd))
  calc (∏ d ∈ diagonals n \ T, f (X d))
      = (∏ d ∈ diagonals n \ T, f (X d)) * ((∏ d ∈ T, (f (X d))⁻¹) * ∏ d ∈ T, f (X d)) := by rw [hinv, mul_one]
    _ = _ := by ring

lemma onRect_line {n k m : ℕ} {x y : ℕ × ℕ → ℚ} (hx : OnRect n k m x) (hy : OnRect n k m y) (t : ℚ) :
    OnRect n k m (x + t • (y - x)) := by
  intro i hi j hj
  have e : mesh n (x + t • (y - x)) i j = mesh n x i j + t * (mesh n y i j - mesh n x i j) := by
    have hf : (x + t • (y - x)) = fun d => x d + t * (fun d => y d + (-1) * x d) d := by
      funext d; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
    rw [hf]; unfold mesh; simp only [p3b_planar_lin]; ring
  rw [e, hx i hi j hj, hy i hi j hj]; ring

lemma onZT_line {N : ℕ} {T : Finset ℕ} {x y : ℕ × ℕ → ℚ} (hx : OnZT N T x) (hy : OnZT N T y) (t : ℚ) :
    OnZT N T (x + t • (y - x)) := by
  have hf : (x + t • (y - x)) = fun d => x d + t * (fun d => y d + (-1) * x d) d := by
    funext d; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  rw [hf]
  exact p3b_onZT_lin t hx (p3b_onZT_lin (-1) hy hx)

/-- PROVED. **Phase 1 in rational form (L-3)**: `A_n` restricts to the zero rational function on every
rectangle locus. From `amp_eq_zero_of_onRect`, `onRect_inhabited`, the numerator of `amp`, and `line_bridge`. -/
theorem amp_ratZero_onRect {n k m : ℕ} (hk : 1 ≤ k) (hkn : k + 3 ≤ n) (hm : 1 ≤ m) (hmn : m ≤ n) :
    RatZeroOn {x | OnRect n k m x} (amp n gen) := by
  obtain ⟨w, hw0, hwR⟩ := onRect_inhabited hk hkn hm hmn
  have hQw : eval w (diagDen n) ≠ 0 := by
    rw [diagDen, map_prod]; simpa using prod_ne_zero_iff.2 hw0
  refine ⟨ampNum n, diagDen n, ?_, ⟨w, hwR, hQw⟩, ?_⟩
  · rw [amp_hom (algebraMap _ RF) n (fun d _ => gen_ne_zero d)]; rfl
  · refine line_bridge _ (fun x hx y hy t => by
      simp only [Set.mem_setOf_eq] at hx hy ⊢; exact onRect_line hx hy t) _ _ hwR hQw fun x hx hQ => ?_
    have hx0 : ∀ d ∈ diagonals n, x d ≠ 0 := by
      rw [diagDen, map_prod] at hQ; simpa using prod_ne_zero_iff.1 hQ
    rw [amp_hom (eval x) n (by simpa using hx0)]
    simp only [eval_X]
    rw [amp_eq_zero_of_onRect hk hkn hm hmn x hx0 hx, zero_mul]

/-- PROVED. **Phase 3 Theorem A in rational form (L-3)**. From `theoremA`, `ZT_inhabited`, `QP_hom`,
`line_bridge`. -/
theorem theoremA_rat {N r : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (hr : r < 2) {T : Finset ℕ} (hT : Admissible N r T) :
    RatZeroOn {x | OnZT N T x} (Qpi N (1 - r) gen) := by
  obtain ⟨w, hwZ, hw0⟩ := ZT_inhabited hN hE hr hT
  have hodd : ∀ d ∈ oddDiagonals N, d ∈ diagonals N := fun d hd => (mem_filter.1 hd).1
  have hQw : eval w (oddDen ℚ N) ≠ 0 := by
    rw [oddDen, map_prod]; simpa using prod_ne_zero_iff.2 fun d hd => hw0 d (hodd d hd)
  refine ⟨QP ℚ N (1 - r), oddDen ℚ N, ?_, ⟨w, hwZ, hQw⟩, ?_⟩
  · rw [QP_hom (algebraMap _ RF) N (1 - r) (fun d _ => gen_ne_zero d)]; rfl
  · refine line_bridge _ (fun x hx y hy t => by
      simp only [Set.mem_setOf_eq] at hx hy ⊢; exact onZT_line hx hy t) _ _ hwZ hQw fun x hx hQ => ?_
    have hx0 : ∀ d ∈ oddDiagonals N, x d ≠ 0 := by
      rw [oddDen, map_prod] at hQ; simpa using prod_ne_zero_iff.1 hQ
    rw [QP_hom (eval x) N (1 - r) (by simpa using hx0)]
    simp only [eval_X]
    rw [((theoremA hN hE hr hT).2 x hx).2, zero_mul]

end Rational

/-! ## 6. Theorem B -/

section TheoremB

open MvPolynomial

theorem pkM_diag4 : diagonals 4 = {(1, 3), (2, 4)} := by decide

theorem pkM_tri4 : triangulations 4 = {{(1, 3)}, {(2, 4)}} := by decide

theorem pkM_quad4 : quadrangulations 4 = {∅} := by decide

theorem pkM_quads4 : quads 4 ∅ = {⟨1, 2, 3, 4⟩} := by decide

/-- Copy of `NLSM_four` (declared after the target). -/
theorem pkM_NLSM4 {K : Type*} [Field K] (x : ℕ × ℕ → K) : NLSM 4 x = -(x (1, 3) + x (2, 4)) := by
  rw [NLSM_eq_ps (by norm_num), pkM_tri4, sum_insert (by decide), sum_singleton,
    prod_singleton, prod_singleton]
  simp [phi, shiftSign, shiftSeries, PowerSeries.coeff_succ_X_mul]
  ring

/-- Copy of `Qpi_four` (declared after the target). -/
theorem pkM_Qpi4 {K : Type*} [Field K] (π : ℕ) (x : ℕ × ℕ → K) : Qpi 4 π x = x (1, 3) + x (2, 4) := by
  rw [Qpi, pkM_quad4, sum_singleton, diagram, pkM_quads4, prod_singleton, prod_empty, mul_one,
    vnum_eq_vnumX π x (by decide : (⟨1, 2, 3, 4⟩ : Quad) ∈ quadIdx 4)]
  unfold vnumX
  split_ifs <;> simp [planar, vtx, pkM_diag4]

theorem pkM_oddDen (N : ℕ) : oddDen ℚ N = ∏ d ∈ oddDiagonals N, (X d : MvPolynomial (ℕ × ℕ) ℚ) := rfl

theorem pkM_evalD {N π : ℕ} (hN : 2 ≤ N) (x : ℕ × ℕ → ℚ) (hX : ∀ d ∈ oddDiagonals N, x d ≠ 0) (s : ℤ) :
    eval x (QP ℚ N π - (s : MvPolynomial (ℕ × ℕ) ℚ) * NP ℚ N) =
      (Qpi N π x - (s : ℚ) * NLSM N x) * ∏ d ∈ oddDiagonals N, x d := by
  have e1 : NP ℚ N = AP ℚ N (N - 2) := rfl
  have e2 : NLSM N x = shiftCoeff N ((N : ℤ) - 2) x := rfl
  have e3 : ((N : ℤ) - 2) = ((N - 2 : ℕ) : ℤ) := by omega
  rw [map_sub, map_mul, map_intCast, e1, QP_eval N π x hX, AP_eval N (N - 2) x hX, e2, e3]
  ring

theorem pkM_eq_of_eval {N : ℕ} (P Q : MvPolynomial (ℕ × ℕ) ℚ)
    (h : ∀ x : ℕ × ℕ → ℚ, (∀ d ∈ oddDiagonals N, x d ≠ 0) → eval x P = eval x Q) : P = Q := by
  have hden : oddDen ℚ N ≠ 0 := prod_ne_zero_iff.2 fun d _ => X_ne_zero d
  have h0 : (P - Q) * oddDen ℚ N = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_sub, map_zero, pkM_oddDen, map_prod]
    by_cases hx : ∏ d ∈ oddDiagonals N, eval x (X d : MvPolynomial (ℕ × ℕ) ℚ) = 0
    · rw [hx, mul_zero]
    · have hx' : ∀ d ∈ oddDiagonals N, x d ≠ 0 := by
        intro d hd
        have := prod_ne_zero_iff.1 hx d hd
        simpa using this
      rw [h x hx', sub_self, zero_mul]
  exact sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_right hden)

theorem pkM_four (π : ℕ) : QP ℚ 4 π = ((sigma 4 : ℤ) : MvPolynomial (ℕ × ℕ) ℚ) * NP ℚ 4 := by
  rw [← sub_eq_zero]
  refine pkM_eq_of_eval (N := 4) _ 0 (fun x hx => ?_)
  rw [pkM_evalD (by norm_num) x hx, pkM_Qpi4, pkM_NLSM4, map_zero]
  have e : sigma 4 = -1 := by
    show (-1 : ℤ) ^ (4 / 2 + 1) = -1
    norm_num
  rw [e]
  push_cast
  ring

theorem pkM_sig {L M N : ℕ} (hL : L % 2 = 0) (hM : M % 2 = 0) (h4L : 4 ≤ L) (h4M : 4 ≤ M)
    (h : (L - 2) + (M - 2) = N - 2) : sigma L * sigma M = sigma N := by
  show (-1 : ℤ) ^ (L / 2 + 1) * (-1) ^ (M / 2 + 1) = (-1) ^ (N / 2 + 1)
  rw [← pow_add, show L / 2 + 1 + (M / 2 + 1) = (N / 2 + 1) + 2 by omega, pow_add]
  norm_num

theorem pkM_res {N π : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (hπ : π < 2)
    (ih : ∀ M : ℕ, M < N → 4 ≤ M → M % 2 = 0 → ∀ ρ : ℕ, ρ < 2 →
      QP ℚ M ρ = ((sigma M : ℤ) : MvPolynomial (ℕ × ℕ) ℚ) * NP ℚ M)
    {c : ℕ × ℕ} (hc : c ∈ oddDiagonals N) :
    zeroAt ℚ c (QP ℚ N π - ((sigma N : ℤ) : MvPolynomial (ℕ × ℕ) ℚ) * NP ℚ N) = 0 := by
  have hk := pkZ_child hE hc
  rw [map_sub, map_mul, map_intCast, QP_residue hN hE hπ hc, NP_residue hN hE hc,
    ih _ hk.2.2.1 hk.1 hk.2.1 ((π + c.1 + 1) % 2) (Nat.mod_lt _ (by norm_num)),
    ih _ hk.2.2.2.2.2.1 hk.2.2.2.1 hk.2.2.2.2.1 ((π + c.2 + 1) % 2) (Nat.mod_lt _ (by norm_num))]
  simp only [map_mul, map_intCast]
  rw [← pkM_sig hk.2.1 hk.2.2.2.2.1 hk.1 hk.2.2.2.1 hk.2.2.2.2.2.2, Int.cast_mul]
  ring

theorem pkM_deg {N π : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (L : MvPolynomial (ℕ × ℕ) ℚ)
    (hL : QP ℚ N π - ((sigma N : ℤ) : MvPolynomial (ℕ × ℕ) ℚ) * NP ℚ N = oddDen ℚ N * L) :
    L.totalDegree ≤ 1 := by
  by_cases h0 : L = 0
  · rw [h0, totalDegree_zero]
    omega
  have hden : oddDen ℚ N ≠ 0 := prod_ne_zero_iff.2 fun d _ => X_ne_zero d
  have hdenH : (oddDen ℚ N).IsHomogeneous (oddDiagonals N).card := by
    have h := IsHomogeneous.prod (oddDiagonals N) (fun d => (X d : MvPolynomial (ℕ × ℕ) ℚ)) (fun _ => 1)
      (fun d _ => isHomogeneous_X ℚ d)
    rw [sum_const, smul_eq_mul, mul_one] at h
    exact h
  have hQ := QP_isHomogeneous (R := ℚ) hN hE π
  have hA := AP_isHomogeneous (R := ℚ) hN (N - 2) (by omega)
  rw [show (oddDiagonals N).card + (N - 2) - (N - 3) = (oddDiagonals N).card + 1 by omega] at hA
  have hC := (isHomogeneous_C (ℕ × ℕ) ((sigma N : ℤ) : ℚ)).mul hA
  rw [zero_add, map_intCast] at hC
  have hD := hQ.sub hC
  have e : NP ℚ N = AP ℚ N (N - 2) := rfl
  rw [← e, hL] at hD
  have h1 := hD.totalDegree (mul_ne_zero hden h0)
  rw [totalDegree_mul_of_isDomain hden h0, hdenH.totalDegree hden] at h1
  omega

theorem pkM_row {N π i : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (hi : 1 ≤ i ∧ i ≤ N) (hπ : i % 2 = π)
    (L : MvPolynomial (ℕ × ℕ) ℚ)
    (hL : QP ℚ N π - ((sigma N : ℤ) : MvPolynomial (ℕ × ℕ) ℚ) * NP ℚ N = oddDen ℚ N * L)
    (x : ℕ × ℕ → ℚ) (hx : OnRect N 1 i x) : eval x L = 0 := by
  obtain ⟨w, hw0, hwR⟩ := onRect_inhabited (n := N) (k := 1) (m := i) le_rfl (by omega) hi.1 hi.2
  have hodd : ∀ d ∈ oddDiagonals N, d ∈ diagonals N := fun d hd => (mem_filter.1 hd).1
  have hQw : eval w (oddDen ℚ N) ≠ 0 := by
    rw [pkM_oddDen, map_prod]
    simpa using prod_ne_zero_iff.2 fun d hd => hw0 d (hodd d hd)
  refine line_bridge {x | OnRect N 1 i x} (fun x hx y hy t => by
      simp only [Set.mem_setOf_eq] at hx hy ⊢
      exact onRect_line hx hy t) L (oddDen ℚ N) hwR hQw (fun y hy hQ => ?_) x hx
  have hQ' := hQ
  have hy0 : ∀ d ∈ oddDiagonals N, y d ≠ 0 := by
    rw [pkM_oddDen, map_prod] at hQ'
    simpa using prod_ne_zero_iff.1 hQ'
  have hD := congrArg (eval y) hL
  rw [pkM_evalD (by omega) y hy0, map_mul] at hD
  have hA := ((theoremA hN hE (Nat.mod_lt (i + 1) (by norm_num)) (admissible_row hN hE hi) (K := ℚ)).2 y
    ((onZT_row_iff hN hi y).2 hy)).2
  rw [show 1 - (i + 1) % 2 = π by omega] at hA
  rw [hA, NLSM_row_zero hN hE hi y hy0 hy, mul_zero, sub_zero, zero_mul] at hD
  exact (mul_eq_zero.1 hD.symm).resolve_left hQ

theorem pkM_step {N π : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) (hπ : π < 2)
    (hz : ∀ c ∈ oddDiagonals N,
      zeroAt ℚ c (QP ℚ N π - ((sigma N : ℤ) : MvPolynomial (ℕ × ℕ) ℚ) * NP ℚ N) = 0) :
    QP ℚ N π = ((sigma N : ℤ) : MvPolynomial (ℕ × ℕ) ℚ) * NP ℚ N := by
  obtain ⟨L, hL⟩ := prod_X_dvd_of_zeroAt (oddDiagonals N) _ hz
  have hL' : QP ℚ N π - ((sigma N : ℤ) : MvPolynomial (ℕ × ℕ) ℚ) * NP ℚ N = oddDen ℚ N * L := hL
  have h4 : 4 ≤ N := by omega
  have hdeg := pkM_deg h4 hE L hL'
  have hL0 : L = 0 := three_rows hN hE (a := 2 - π) (by omega) L hdeg (fun x hx => by
    rcases hx with h | h | h
    · exact pkM_row h4 hE (by omega) (by omega) L hL' x h
    · exact pkM_row h4 hE (by omega) (by omega) L hL' x h
    · exact pkM_row h4 hE (by omega) (by omega) L hL' x h)
  rw [hL0, mul_zero] at hL'
  exact sub_eq_zero.1 hL'

theorem pkM_rat (N : ℕ) : 4 ≤ N → N % 2 = 0 → ∀ π : ℕ, π < 2 →
    QP ℚ N π = ((sigma N : ℤ) : MvPolynomial (ℕ × ℕ) ℚ) * NP ℚ N := by
  refine Nat.strong_induction_on N ?_
  intro N ih hN hE π hπ
  by_cases h4 : N = 4
  · subst h4
    exact pkM_four π
  · exact pkM_step (by omega) hE hπ (fun c hc => pkM_res hN hE hπ ih hc)

theorem pkM_int {N π : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (hπ : π < 2) :
    QP ℤ N π = ((sigma N : ℤ) : MvPolynomial (ℕ × ℕ) ℤ) * NP ℤ N := by
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) (Int.castRingHom ℚ).injective_int
  have e1 : NP ℤ N = AP ℤ N (N - 2) := rfl
  have e2 : NP ℚ N = AP ℚ N (N - 2) := rfl
  rw [map_mul, map_intCast, QP_map, e1, AP_map, ← e2]
  exact pkM_rat N hN hE π hπ

/-- `sorry` (3c-b). **Theorem B, numerator form**: `QP_N^π = σ_N · NP_N` over every commutative ring. Proof
(PROOFS §2): induction on `N`; `D = QP − σ NP` has `zeroAt C D = 0` for every odd `C` (`QP_residue`, `NP_residue`,
induction, `σ_L σ_R = σ_N`), so `oddDen ∣ D` (`prod_X_dvd_of_zeroAt`), `D = oddDen · L` with `L` affine
(homogeneity); `L` vanishes on the three rows `i ≡ π` (Theorem A via `onZT_row_iff`; `NLSM_row_zero`; `line_bridge`
with `onRect_inhabited`), so `L = 0` (`three_rows`). Base `N = 4`. [mirror D6, N ≤ 12] -/
theorem theoremB_poly {R : Type*} [CommRing R] {N π : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (hπ : π < 2) :
    QP R N π = ((sigma N : ℤ) : MvPolynomial (ℕ × ℕ) R) * NP R N := by
  have e : NP R N = AP R N (N - 2) := rfl
  have e2 : NP ℤ N = AP ℤ N (N - 2) := rfl
  rw [e, ← QP_map (Int.castRingHom R), ← AP_map (Int.castRingHom R), pkM_int hN hE hπ, e2, map_mul, map_intCast]

variable {K : Type*} [Field K]

/-- ASSEMBLED. **Theorem B (PROOFS §2), pointwise**: for every even `N ≥ 4`, both polarities, over any field, at every
point where no odd diagonal vanishes: `Q_N^π = σ_N · NLSM_N`, `σ_N = (−1)^{N/2+1}`. The hypothesis `hX` is necessary
(`negctl_poles_six`), and so is `π < 2` (`negctl_pi_two_six`). -/
theorem theoremB {N π : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (hπ : π < 2) (X : ℕ × ℕ → K)
    (hX : ∀ d ∈ oddDiagonals N, X d ≠ 0) : Qpi N π X = (sigma N : K) * NLSM N X := by
  have h := congrArg (eval X) (theoremB_poly (R := K) hN hE hπ)
  rw [QP_eval N π X hX, map_mul, NP, AP_eval N (N - 2) X hX, map_intCast] at h
  have hd : ∏ d ∈ oddDiagonals N, X d ≠ 0 := prod_ne_zero_iff.2 hX
  rw [NLSM, show ((N : ℤ) - 2) = ((N - 2 : ℕ) : ℤ) by omega]
  apply mul_right_cancel₀ hd
  rw [h]; ring

/-- ASSEMBLED. Theorem B at the generic point: an identity in `RF`, with no side condition. -/
theorem theoremB_rat {N π : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (hπ : π < 2) :
    Qpi N π gen = (sigma N : RF) * NLSM N gen :=
  theoremB hN hE hπ gen (fun d _ => gen_ne_zero d)

/-- ASSEMBLED. The two polarities agree (where they must): a corollary of Theorem B. Single diagrams do not
(`negctl_polarity_diagram_six`). -/
theorem Qpi_polarity {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (X : ℕ × ℕ → K)
    (hX : ∀ d ∈ oddDiagonals N, X d ≠ 0) : Qpi N 0 X = Qpi N 1 X := by
  rw [theoremB hN hE (by norm_num) X hX, theoremB hN hE (by norm_num) X hX]

/-- ASSEMBLED. **The Main Theorem of R2-Z30 (the S_T family of NLSM zeros)**, pointwise: for every even `N ≥ 4` and every
admissible `T`, `Z_T` has a point with every diagonal non-zero, and `NLSM_N = 0` at every point of `Z_T` where no odd
diagonal vanishes. -/
theorem nlsm_zero_on_ZT {N r : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (hr : r < 2) {T : Finset ℕ}
    (hT : Admissible N r T) :
    (∃ X : ℕ × ℕ → ℚ, OnZT N T X ∧ ∀ d ∈ diagonals N, X d ≠ 0) ∧
    ∀ X : ℕ × ℕ → K, OnZT N T X → (∀ d ∈ oddDiagonals N, X d ≠ 0) → NLSM N X = 0 := by
  refine ⟨(theoremA hN hE hr hT (K := ℚ)).1, fun X hZ hX => ?_⟩
  have hA := ((theoremA hN hE hr hT (K := K)).2 X hZ).2
  rw [theoremB hN hE (by omega) X hX] at hA
  have hs : (sigma N : K) ≠ 0 := by
    unfold sigma; push_cast
    exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  exact (mul_eq_zero.1 hA).resolve_left hs

/-- ASSEMBLED. The Main Theorem in rational form (from `theoremB_rat` and `theoremA_rat`). -/
theorem nlsm_ratZero_ZT {N r : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (hr : r < 2) {T : Finset ℕ}
    (hT : Admissible N r T) : RatZeroOn {x | OnZT N T x} (NLSM N gen) := by
  obtain ⟨P, Q, hPQ, hw, hP⟩ := theoremA_rat hN hE hr hT
  have hs2 : (sigma N : RF) * (sigma N : RF) = 1 := by
    unfold sigma; push_cast; rw [← mul_pow]; norm_num
  have hN' : NLSM N gen = (sigma N : RF) * Qpi N (1 - r) gen := by
    rw [theoremB_rat hN hE (by omega), ← mul_assoc, hs2, one_mul]
  refine ⟨(sigma N : MvPolynomial (ℕ × ℕ) ℚ) * P, Q, ?_, hw, fun x hx => ?_⟩
  · rw [hN', mul_assoc, hPQ, map_mul, map_intCast]
  · rw [map_mul, hP x hx, mul_zero]

end TheoremB

/-! ## 7. Small cases end to end, witnesses, negative controls -/

section Small

variable {K : Type*} [Field K]

theorem diagonals_four : diagonals 4 = {(1, 3), (2, 4)} := by decide

theorem triangulations_four : triangulations 4 = {{(1, 3)}, {(2, 4)}} := by decide

theorem quadrangulations_four : quadrangulations 4 = {∅} := by decide

theorem quads_four : quads 4 ∅ = {⟨1, 2, 3, 4⟩} := by decide

theorem oddDiagonals_six : oddDiagonals 6 = {(1, 4), (2, 5), (3, 6)} := by decide

lemma phi_of_sign {X : ℕ × ℕ → K} {d : ℕ × ℕ} {s : ℤ} (h : shiftSign d = s) (hs : s ≠ 0) :
    phi X d = shiftSeries s (X d) := by
  rw [phi, h, if_neg hs]

lemma phi_of_zero {X : ℕ × ℕ → K} {d : ℕ × ℕ} (h : shiftSign d = 0) : phi X d = PowerSeries.C (X d)⁻¹ := by
  rw [phi, if_pos h]

/-- `shiftSeries = X · gser`. -/
noncomputable def gser (s : ℤ) (x : K) : PowerSeries K := PowerSeries.mk (fun k => (s : K) ^ (k + 1) * (-x) ^ k)

lemma sh_eq (s : ℤ) (x : K) : shiftSeries s x = PowerSeries.X * gser s x := rfl

/-- PROVED. The first coefficients of `1/(x ± δ)` at `δ = ∞`. -/
lemma coeff_shiftSeries (s : ℤ) (x : K) (k : ℕ) :
    PowerSeries.coeff (k + 1) (shiftSeries s x) = (s : K) ^ (k + 1) * (-x) ^ k := by
  rw [sh_eq, PowerSeries.coeff_succ_X_mul, gser, PowerSeries.coeff_mk]

/-! ### N = 4 -/

/-- PROVED. **NLSM_4 from the definition**: `NLSM_4 = −(X₁₃ + X₂₄)`, i.e. `−A_4^NLSM` of arXiv:2312.16282 eq. (4.4)
(C0: sign `(−1)^{n−1}`, `n = 2`). -/
theorem NLSM_four (X : ℕ × ℕ → K) : NLSM 4 X = -(X (1, 3) + X (2, 4)) := by
  rw [NLSM_eq_ps (by norm_num), triangulations_four, sum_insert (by decide), sum_singleton,
    prod_singleton, prod_singleton]
  simp [phi, shiftSign, shiftSeries, PowerSeries.coeff_succ_X_mul]
  ring

/-- PROVED. The other δ-orders at N = 4: order `N − 3 = 1` vanishes (Lemma 4.1), order `N − 1 = 3` is not NLSM. -/
theorem shiftCoeff_four (X : ℕ × ℕ → K) :
    shiftCoeff 4 1 X = 0 ∧ shiftCoeff 4 3 X = X (2, 4) ^ 2 - X (1, 3) ^ 2 := by
  have h1 : ((1 : ℤ)) = ((1 : ℕ) : ℤ) := rfl
  have h3 : ((3 : ℤ)) = ((3 : ℕ) : ℤ) := rfl
  rw [h1, h3, shiftCoeff_eq_ps, shiftCoeff_eq_ps, triangulations_four, sum_insert (by decide), sum_singleton,
    prod_singleton, prod_singleton]
  have p13 := phi_of_sign (X := X) (show shiftSign (1, 3) = -1 by decide) (by decide)
  have p24 := phi_of_sign (X := X) (show shiftSign (2, 4) = 1 by decide) (by decide)
  rw [p13, p24, map_add, map_add, show (1 : ℕ) = 0 + 1 from rfl, show (3 : ℕ) = 2 + 1 from rfl,
    coeff_shiftSeries, coeff_shiftSeries, coeff_shiftSeries, coeff_shiftSeries]
  constructor <;> push_cast <;> ring

/-- PROVED. `Q_4^π = X₁₃ + X₂₄` for every `π` (the single quad's `−` sides are polygon edges). -/
theorem Qpi_four (π : ℕ) (X : ℕ × ℕ → K) : Qpi 4 π X = X (1, 3) + X (2, 4) := by
  rw [Qpi, quadrangulations_four, sum_singleton, diagram, quads_four, prod_singleton, prod_empty, mul_one,
    vnum_eq_vnumX π X (by decide : (⟨1, 2, 3, 4⟩ : Quad) ∈ quadIdx 4)]
  unfold vnumX
  split_ifs <;> simp [planar, vtx, diagonals_four]

/-- PROVED. **Theorem B at N = 4, end to end from the definitions** (no side condition: no odd diagonals). -/
theorem theoremB_four (π : ℕ) (X : ℕ × ℕ → K) : Qpi 4 π X = (sigma 4 : K) * NLSM 4 X := by
  rw [Qpi_four, NLSM_four, sigma]; push_cast; ring

/-! ### N = 6 -/

theorem triangulations_six : triangulations 6 =
    {{(1, 3), (1, 4), (1, 5)}, {(1, 3), (1, 4), (4, 6)}, {(1, 3), (1, 5), (3, 5)}, {(1, 3), (3, 5), (3, 6)},
     {(1, 3), (3, 6), (4, 6)}, {(1, 4), (1, 5), (2, 4)}, {(1, 4), (2, 4), (4, 6)}, {(1, 5), (2, 4), (2, 5)},
     {(1, 5), (2, 5), (3, 5)}, {(2, 4), (2, 5), (2, 6)}, {(2, 4), (2, 6), (4, 6)}, {(2, 5), (2, 6), (3, 5)},
     {(2, 6), (3, 5), (3, 6)}, {(2, 6), (3, 6), (4, 6)}} := by
  decide

lemma coeff_gg (t u : ℤ) (y z : K) (n : ℕ) (hn : n ≤ 2) :
    PowerSeries.coeff n (gser t y * gser u z) =
      if n = 0 then (t : K) * u else if n = 1 then (t : K) ^ 2 * (-y) * u + t * (u ^ 2 * (-z))
      else (t : K) ^ 3 * (-y) ^ 2 * u + t ^ 2 * (-y) * (u ^ 2 * (-z)) + t * (u ^ 3 * (-z) ^ 2) := by
  interval_cases n <;>
  simp only [gser, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_zero, PowerSeries.coeff_mk] <;> norm_num <;> ring

lemma coeff_ggg (s t u : ℤ) (x y z : K) (n : ℕ) (hn : n ≤ 1) :
    PowerSeries.coeff n (gser s x * (gser t y * gser u z)) =
      if n = 0 then (s : K) * t * u else (s : K) ^ 2 * (-x) * t * u + s * (t ^ 2 * (-y)) * u + s * t * (u ^ 2 * (-z)) := by
  interval_cases n <;>
  simp only [gser, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_zero, PowerSeries.coeff_mk] <;> norm_num <;> ring

/-- Coefficient `n + 3` of three shifted factors. -/
lemma c_sss (s t u : ℤ) (x y z : K) (n : ℕ) :
    PowerSeries.coeff (n + 3) (shiftSeries s x * (shiftSeries t y * shiftSeries u z)) =
      PowerSeries.coeff n (gser s x * (gser t y * gser u z)) := by
  rw [sh_eq, sh_eq, sh_eq,
    show PowerSeries.X * gser s x * (PowerSeries.X * gser t y * (PowerSeries.X * gser u z)) =
      PowerSeries.X ^ 3 * (gser s x * (gser t y * gser u z)) by ring, PowerSeries.coeff_X_pow_mul']
  simp

/-- Coefficient `n + 2` of one unshifted and two shifted factors, in the three positions `prod_insert` produces. -/
lemma c_css (w : K) (t u : ℤ) (y z : K) (n : ℕ) :
    PowerSeries.coeff (n + 2) (PowerSeries.C w * (shiftSeries t y * shiftSeries u z)) =
      w * PowerSeries.coeff n (gser t y * gser u z) := by
  rw [PowerSeries.coeff_C_mul, sh_eq, sh_eq,
    show PowerSeries.X * gser t y * (PowerSeries.X * gser u z) = PowerSeries.X ^ 2 * (gser t y * gser u z) by ring,
    PowerSeries.coeff_X_pow_mul']
  simp

lemma c_scs (w : K) (t u : ℤ) (y z : K) (n : ℕ) :
    PowerSeries.coeff (n + 2) (shiftSeries t y * (PowerSeries.C w * shiftSeries u z)) =
      w * PowerSeries.coeff n (gser t y * gser u z) := by
  rw [← c_css]; congr 1; ring

lemma c_ssc (w : K) (t u : ℤ) (y z : K) (n : ℕ) :
    PowerSeries.coeff (n + 2) (shiftSeries t y * (shiftSeries u z * PowerSeries.C w)) =
      w * PowerSeries.coeff n (gser t y * gser u z) := by
  rw [← c_css]; congr 1; ring

/-- The expansion of the hexagon's shifted amplitude, one line per triangulation (the order of `triangulations_six`). -/
lemma hex_expand (X : ℕ × ℕ → K) (n : ℕ) :
    PowerSeries.coeff n (∑ T ∈ triangulations 6, ∏ d ∈ T, phi X d) =
      PowerSeries.coeff n (
        shiftSeries (-1) (X (1, 3)) * (PowerSeries.C (X (1, 4))⁻¹ * shiftSeries (-1) (X (1, 5))) +
        (shiftSeries (-1) (X (1, 3)) * (PowerSeries.C (X (1, 4))⁻¹ * shiftSeries 1 (X (4, 6))) +
        (shiftSeries (-1) (X (1, 3)) * (shiftSeries (-1) (X (1, 5)) * shiftSeries (-1) (X (3, 5))) +
        (shiftSeries (-1) (X (1, 3)) * (shiftSeries (-1) (X (3, 5)) * PowerSeries.C (X (3, 6))⁻¹) +
        (shiftSeries (-1) (X (1, 3)) * (PowerSeries.C (X (3, 6))⁻¹ * shiftSeries 1 (X (4, 6))) +
        (PowerSeries.C (X (1, 4))⁻¹ * (shiftSeries (-1) (X (1, 5)) * shiftSeries 1 (X (2, 4))) +
        (PowerSeries.C (X (1, 4))⁻¹ * (shiftSeries 1 (X (2, 4)) * shiftSeries 1 (X (4, 6))) +
        (shiftSeries (-1) (X (1, 5)) * (shiftSeries 1 (X (2, 4)) * PowerSeries.C (X (2, 5))⁻¹) +
        (shiftSeries (-1) (X (1, 5)) * (PowerSeries.C (X (2, 5))⁻¹ * shiftSeries (-1) (X (3, 5))) +
        (shiftSeries 1 (X (2, 4)) * (PowerSeries.C (X (2, 5))⁻¹ * shiftSeries 1 (X (2, 6))) +
        (shiftSeries 1 (X (2, 4)) * (shiftSeries 1 (X (2, 6)) * shiftSeries 1 (X (4, 6))) +
        (PowerSeries.C (X (2, 5))⁻¹ * (shiftSeries 1 (X (2, 6)) * shiftSeries (-1) (X (3, 5))) +
        (shiftSeries 1 (X (2, 6)) * (shiftSeries (-1) (X (3, 5)) * PowerSeries.C (X (3, 6))⁻¹) +
        shiftSeries 1 (X (2, 6)) * (PowerSeries.C (X (3, 6))⁻¹ * shiftSeries 1 (X (4, 6)))))))))))))))) := by
  rw [triangulations_six]
  simp (config := {decide := true}) only [sum_insert, sum_singleton, mem_insert, mem_singleton, prod_insert,
    prod_singleton, not_false_eq_true]
  rw [phi_of_sign (X := X) (show shiftSign (1, 3) = -1 by decide) (by decide),
    phi_of_sign (X := X) (show shiftSign (1, 5) = -1 by decide) (by decide),
    phi_of_sign (X := X) (show shiftSign (3, 5) = -1 by decide) (by decide),
    phi_of_sign (X := X) (show shiftSign (2, 4) = 1 by decide) (by decide),
    phi_of_sign (X := X) (show shiftSign (2, 6) = 1 by decide) (by decide),
    phi_of_sign (X := X) (show shiftSign (4, 6) = 1 by decide) (by decide),
    phi_of_zero (X := X) (show shiftSign (1, 4) = 0 by decide),
    phi_of_zero (X := X) (show shiftSign (2, 5) = 0 by decide),
    phi_of_zero (X := X) (show shiftSign (3, 6) = 0 by decide)]

/-- arXiv:2312.16282 eq. (4.3), transcribed: `(X₁₃+X₂₄)(X₁₅+X₄₆)/X₁₄ − X₁₃ − X₂₄ + (cyclic, i → i+2)`. -/
noncomputable def paper43 (X : ℕ × ℕ → K) : K :=
  ((X (1, 3) + X (2, 4)) * (X (1, 5) + X (4, 6)) * (X (1, 4))⁻¹ - X (1, 3) - X (2, 4)) +
  ((X (3, 5) + X (4, 6)) * (X (1, 3) + X (2, 6)) * (X (3, 6))⁻¹ - X (3, 5) - X (4, 6)) +
  ((X (1, 5) + X (2, 6)) * (X (3, 5) + X (2, 4)) * (X (2, 5))⁻¹ - X (1, 5) - X (2, 6))

/-- PROVED. **NLSM_6 from the definition equals the paper's printed six-point amplitude** arXiv:2312.16282 eq. (4.3)
(C0: sign `(−1)^{n−1} = +1`, `n = 3`). No side condition: both sides use the same `x⁻¹` atoms. -/
theorem NLSM_six (X : ℕ × ℕ → K) : NLSM 6 X = paper43 X := by
  rw [NLSM_eq_ps (by norm_num), hex_expand, show (6 : ℕ) - 2 = 1 + 3 from rfl]
  simp only [map_add, c_sss]
  rw [show (1 : ℕ) + 3 = 2 + 2 from rfl]
  simp only [c_css, c_scs, c_ssc, coeff_gg _ _ _ _ 2 le_rfl, coeff_ggg _ _ _ _ _ _ 1 le_rfl]
  unfold paper43
  norm_num
  ring

/-- PROVED. **Lemma 4.1 at N = 6**: the order `δ^{−3} = δ^{−(N−3)}` cancels identically. -/
theorem shiftCoeff_six_three (X : ℕ × ℕ → K) : shiftCoeff 6 3 X = 0 := by
  rw [show ((3 : ℤ)) = ((0 + 3 : ℕ) : ℤ) from rfl, shiftCoeff_eq_ps, hex_expand]
  simp only [map_add, c_sss]
  rw [show (0 : ℕ) + 3 = 1 + 2 from rfl]
  simp only [c_css, c_scs, c_ssc, coeff_gg _ _ _ _ 1 (by norm_num), coeff_ggg _ _ _ _ _ _ 0 (by norm_num)]
  norm_num
  ring

/-- PROVED. **Theorem B at N = 6, end to end from the definitions**, both polarities (`σ₆ = +1`). -/
theorem theoremB_six {π : ℕ} (hπ : π < 2) (X : ℕ × ℕ → K) (hX : ∀ d ∈ oddDiagonals 6, X d ≠ 0) :
    Qpi 6 π X = (sigma 6 : K) * NLSM 6 X := by
  rw [oddDiagonals_six] at hX
  have h14 := hX (1, 4) (by simp)
  have h25 := hX (2, 5) (by simp)
  have h36 := hX (3, 6) (by simp)
  rw [Qpi_six, NLSM_six, paper43, sigma]
  interval_cases π <;>
  · simp [vnumX, planar, vtx, diagonals_six]
    field_simp
    ring

/-! ### Witnesses (non-vacuity) -/

/-- PROVED. NLSM_4 and NLSM_6 are not identically zero (so `theoremB_four/six` are not `0 = 0`), at the all-ones
point, which satisfies every side condition. -/
theorem NLSM_ne_zero_small : NLSM 4 (fun _ => (1 : ℚ)) = -2 ∧ NLSM 6 (fun _ => (1 : ℚ)) = 6 := by
  rw [NLSM_four, NLSM_six, paper43]; norm_num

/-- PROVED. The side condition of `theoremB` is satisfiable at every `N` (non-vacuity of the pointwise form). -/
theorem theoremB_hyp_inhabited (N : ℕ) : ∀ d ∈ oddDiagonals N, (fun _ => (1 : ℚ)) d ≠ 0 := by
  intro d _; norm_num

/-- `sorry` (3c-b, optional). NLSM_N is not identically zero for any even `N ≥ 4` (from `NP_residue` by induction:
a non-zero residue). -/
theorem NLSM_ne_zero {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) : ∃ X : ℕ × ℕ → ℚ, NLSM N X ≠ 0 := sorry

/-! ### Negative controls -/

/-- PROVED. Control (wrong sign): `−σ_N` fails at N = 4 and N = 6. -/
theorem negctl_sign :
    Qpi 4 0 (fun _ => (1 : ℚ)) ≠ (-(sigma 4 : ℚ)) * NLSM 4 (fun _ => (1 : ℚ)) ∧
    Qpi 6 0 (fun _ => (1 : ℚ)) ≠ (-(sigma 6 : ℚ)) * NLSM 6 (fun _ => (1 : ℚ)) := by
  rw [Qpi_four, NLSM_four, (theoremB_six (by norm_num) _ (by intro d _; norm_num)), NLSM_six, paper43, sigma, sigma]
  norm_num

/-- PROVED. Control (wrong δ order): with the order `N − 3` Theorem B would read `Q = 0` (false); with `N − 1` it fails
at N = 4. -/
theorem negctl_order :
    Qpi 4 0 (fun _ => (1 : ℚ)) ≠ (sigma 4 : ℚ) * shiftCoeff 4 1 (fun _ => (1 : ℚ)) ∧
    Qpi 4 0 (fun _ => (1 : ℚ)) ≠ (sigma 4 : ℚ) * shiftCoeff 4 3 (fun _ => (1 : ℚ)) ∧
    Qpi 6 0 (fun _ => (1 : ℚ)) ≠ (sigma 6 : ℚ) * shiftCoeff 6 3 (fun _ => (1 : ℚ)) := by
  rw [Qpi_four, (shiftCoeff_four _).1, (shiftCoeff_four _).2, shiftCoeff_six_three,
    theoremB_six (by norm_num) _ (by intro d _; norm_num), NLSM_six, paper43]
  norm_num [sigma]

/-- PROVED. Control (the side condition `X_C ≠ 0` is needed): at `X₁₄ = 0`, all other diagonals `1`, Lean's `0⁻¹ = 0`
gives `Q_6 = 4` but `NLSM_6 = 2`. -/
theorem negctl_poles_six :
    Qpi 6 0 (fun d => if d = (1, 4) then (0 : ℚ) else 1) ≠
      (sigma 6 : ℚ) * NLSM 6 (fun d => if d = (1, 4) then (0 : ℚ) else 1) := by
  rw [Qpi_six, NLSM_six, paper43, sigma]
  simp [vnumX, planar, vtx, diagonals_six]
  norm_num

/-- PROVED. Control (`π < 2` is needed): with `π = 2` no side is ever `+` first, and `Q_6 = 8 ≠ 6 = NLSM_6` at the
all-ones point. -/
theorem negctl_pi_two_six : Qpi 6 2 (fun _ => (1 : ℚ)) ≠ (sigma 6 : ℚ) * NLSM 6 (fun _ => (1 : ℚ)) := by
  rw [Qpi_six, NLSM_six, paper43, sigma]
  simp [vnumX, planar, vtx, diagonals_six]
  norm_num

theorem diagram_six_14 (π : ℕ) (X : ℕ × ℕ → K) : diagram 6 π X {(1, 4)} =
    vnumX 6 π X ⟨1, 2, 3, 4⟩ * vnumX 6 π X ⟨1, 4, 5, 6⟩ * (X (1, 4))⁻¹ := by
  rw [diagram, quads_6_0, prod_insert (by decide), prod_singleton, prod_singleton,
    vnum_eq_vnumX π X (by decide : (⟨1, 2, 3, 4⟩ : Quad) ∈ quadIdx 6),
    vnum_eq_vnumX π X (by decide : (⟨1, 4, 5, 6⟩ : Quad) ∈ quadIdx 6)]

/-- PROVED. Control (polarity): the two polarities' sums agree (`Qpi_polarity`, here from `theoremB_six`), but single
diagrams differ: at `X = (1,…,9)` (order of `diagonals_six`) the diagram `{(1,4)}` is `25` for `π = 0` and `18` for
`π = 1`. -/
theorem negctl_polarity_diagram_six :
    diagram 6 0 (hexPt 1 2 3 4 5 6 7 8 9) {(1, 4)} = 25 ∧ diagram 6 1 (hexPt 1 2 3 4 5 6 7 8 9) {(1, 4)} = 18 ∧
    Qpi 6 0 (hexPt 1 2 3 4 5 6 7 8 9) = Qpi 6 1 (hexPt 1 2 3 4 5 6 7 8 9) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [diagram_six_14]; norm_num [vnumX, planar, vtx, diagonals_six, hexPt]
  · rw [diagram_six_14]; norm_num [vnumX, planar, vtx, diagonals_six, hexPt]
  · have h : ∀ d ∈ oddDiagonals 6, hexPt 1 2 3 4 5 6 7 8 9 d ≠ 0 := by
      rw [oddDiagonals_six]; intro d hd
      simp only [mem_insert, mem_singleton] at hd
      rcases hd with rfl | rfl | rfl <;> norm_num [hexPt]
    rw [theoremB_six (by norm_num) _ h, theoremB_six (by norm_num) _ h]

end Small

/-! ## Axiom audit -/

#print axioms NLSM_eq_ps
#print axioms shiftCoeff_neg
#print axioms gen_ne_zero
#print axioms NLSM_four
#print axioms shiftCoeff_four
#print axioms Qpi_four
#print axioms theoremB_four
#print axioms NLSM_six
#print axioms shiftCoeff_six_three
#print axioms theoremB_six
#print axioms NLSM_ne_zero_small
#print axioms theoremB_hyp_inhabited
#print axioms negctl_sign
#print axioms negctl_order
#print axioms negctl_poles_six
#print axioms negctl_pi_two_six
#print axioms negctl_polarity_diagram_six
#print axioms line_bridge
#print axioms QP_eval
#print axioms amp_ratZero_onRect
#print axioms theoremA_rat
#print axioms theoremB
#print axioms nlsm_ratZero_ZT
#print axioms nlsm_zero_on_ZT

end R12P3C
