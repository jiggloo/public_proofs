import PionCompleteness.C6

namespace PiZ

open Finset R12P1 R12P4A R12P3 R12P3C

/-- `ψ_K` on a product of variables removes the banned ones. -/
theorem pkR_b_psi_prod {R : Type*} [CommRing R] (K s : Finset (ℕ × ℕ)) :
    pkR_b_psi R (fun d => d ∈ K) (Finset.prod s (fun d => MvPolynomial.X d)) =
      Finset.prod (s \ K) (fun d => (MvPolynomial.X d : MvPolynomial (ℕ × ℕ) R)) := by
  rw [map_prod]
  have e : ∀ d ∈ s, pkR_b_psi R (fun d => d ∈ K) (MvPolynomial.X d) =
      if d ∈ K then 1 else MvPolynomial.X d := fun d _ => pkR_b_psi_X _ d
  rw [prod_congr rfl e, prod_ite, prod_const_one, one_mul]
  refine prod_congr ?_ (fun _ _ => rfl)
  ext d; simp only [mem_filter, mem_sdiff]

/-- `ψ` commutes with `rename`: banning `K` in the parent is banning its preimage in the child. -/
theorem pkR_b_psi_rename {R : Type*} [CommRing R] (ρ : ℕ × ℕ → ℕ × ℕ) (K : Finset (ℕ × ℕ))
    (q : MvPolynomial (ℕ × ℕ) R) :
    pkR_b_psi R (fun d => d ∈ K) (MvPolynomial.rename ρ q) =
      MvPolynomial.rename ρ (pkR_b_psi R (fun d => ρ d ∈ K) q) := by
  have h : (pkR_b_psi R (fun d => d ∈ K)).comp (MvPolynomial.rename ρ) =
      (MvPolynomial.rename ρ).comp (pkR_b_psi R (fun d => ρ d ∈ K)) := by
    refine MvPolynomial.algHom_ext fun d => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, MvPolynomial.rename_X, pkR_b_psi_X, pkR_b_psi_X]
    by_cases hd : ρ d ∈ K
    · rw [if_pos hd, if_pos hd, map_one]
    · rw [if_neg hd, if_neg hd, MvPolynomial.rename_X]
  exact AlgHom.congr_fun h q

theorem pkR_b_map_rescale {A B : Type*} [CommRing A] [CommRing B] (f : RingHom A B) (a : A)
    (p : PowerSeries A) :
    PowerSeries.map f (PowerSeries.rescale a p) = PowerSeries.rescale (f a) (PowerSeries.map f p) := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_map, PowerSeries.coeff_rescale, PowerSeries.coeff_rescale, PowerSeries.coeff_map, map_mul,
    map_pow]

theorem pkR_b_map_map {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] (f : RingHom B C) (g : RingHom A B)
    (p : PowerSeries A) :
    PowerSeries.map f (PowerSeries.map g p) = PowerSeries.map (f.comp g) p := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_map]
  rfl

/-- `map ψ_K ∘ map (rename ρ) = map (rename ρ) ∘ map ψ_{ρ⁻¹ K}` on power series. -/
theorem pkR_b_map_psi_ren {R : Type*} [CommRing R] (ρ : ℕ × ℕ → ℕ × ℕ) (K : Finset (ℕ × ℕ))
    (p : PowerSeries (MvPolynomial (ℕ × ℕ) R)) :
    PowerSeries.map (pkR_b_psi R (fun d => d ∈ K)).toRingHom (PowerSeries.map (MvPolynomial.rename ρ).toRingHom p) =
      PowerSeries.map (MvPolynomial.rename ρ).toRingHom
        (PowerSeries.map (pkR_b_psi R (fun d => ρ d ∈ K)).toRingHom p) := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_map]
  exact pkR_b_psi_rename ρ K _

/-- Disjointness from an image = disjointness from the pull-back. -/
theorem pkR_b_disj_image (f : ℕ × ℕ → ℕ × ℕ) {s U : Finset (ℕ × ℕ)} (t : Finset (ℕ × ℕ)) (hs : s ⊆ U) :
    Disjoint (s.image f) t ↔ Disjoint s (U.filter (fun d => f d ∈ t)) := by
  rw [disjoint_left, disjoint_left]
  constructor
  · intro h d hd hd'
    exact h (mem_image.2 ⟨d, hd, rfl⟩) (mem_filter.1 hd').2
  · intro h a ha hat
    obtain ⟨d, hd, rfl⟩ := mem_image.1 ha
    exact h hd (mem_filter.2 ⟨hs hd, hat⟩)

/-- A glued triangulation avoids `K` iff both children avoid the pulled-back sets (the chord is not banned). -/
theorem pkR_b_disj_glue {N i j : ℕ} {K T1 T2 : Finset (ℕ × ℕ)} (hCK : (i, j) ∉ K)
    (h1 : T1 ⊆ diagonals (j - i + 1)) (h2 : T2 ⊆ diagonals (N - j + i + 1)) :
    Disjoint (pkSp_glue N i j T1 T2) K ↔
      Disjoint T1 (pkR_b_pull N i (j - i + 1) K) ∧ Disjoint T2 (pkR_b_pull N j (N - j + i + 1) K) := by
  have e : pkSp_glue N i j T1 T2 = insert (i, j) (T1.image (relab N i) ∪ T2.image (relab N j)) := rfl
  rw [e, disjoint_insert_left, disjoint_union_left, pkR_b_disj_image (relab N i) K h1,
    pkR_b_disj_image (relab N j) K h2]
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨hCK, h⟩

/-- An odd diagonal has sign 0. -/
theorem pkR_b_sign_odd {N : ℕ} {d : ℕ × ℕ} (hd : d ∈ oddDiagonals N) : shiftSign d = 0 := by
  have h := mem_filter.1 hd
  have h1 := mem_diagonals.1 h.1
  exact pkSp_shiftSign_odd (by omega) h.2

/-- **The glued ¬K summand factors** (`pkSp_F_glue` with a banned set of odd diagonals not containing the chord). -/
theorem pkR_b_F_glue {R : Type*} [CommRing R] {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N)
    (hne : ¬ (i = 1 ∧ j = N)) (hE : N % 2 = 0) (hodd : (j - i) % 2 = 1) {K T1 T2 : Finset (ℕ × ℕ)}
    (hK : K ⊆ oddDiagonals N) (h1 : T1 ⊆ diagonals (j - i + 1)) (h2 : T2 ⊆ diagonals (N - j + i + 1)) :
    pkR_b_F R N K (pkSp_glue N i j T1 T2) =
      PowerSeries.C (pkR_b_cross R N K (i, j)) *
        (PowerSeries.rescale ((((-1) ^ (i + 1) : ℤ)) : MvPolynomial (ℕ × ℕ) R)
            (PowerSeries.map (MvPolynomial.rename (relab N i)).toRingHom
              (pkR_b_F R (j - i + 1) (pkR_b_pull N i (j - i + 1) K) T1)) *
          PowerSeries.rescale ((((-1) ^ (j + 1) : ℤ)) : MvPolynomial (ℕ × ℕ) R)
            (PowerSeries.map (MvPolynomial.rename (relab N j)).toRingHom
              (pkR_b_F R (N - j + i + 1) (pkR_b_pull N j (N - j + i + 1) K) T2))) := by
  have hTg : ∀ d ∈ pkSp_glue N i j T1 T2, shiftSign d ≠ 0 → ¬ (d ∈ K) :=
    fun d _ hs hdK => hs (pkR_b_sign_odd (hK hdK))
  rw [← pkR_b_F_psi N K _ (fun d => d ∈ K) (fun d _ => Iff.rfl) hTg, pkSp_F_glue hi hij hjN hne hE hodd h1 h2,
    map_mul, PowerSeries.map_C, map_mul, pkR_b_map_rescale, pkR_b_map_rescale, pkR_b_map_psi_ren,
    pkR_b_map_psi_ren]
  have hc : (pkR_b_psi R (fun d => d ∈ K)).toRingHom (crossProd R N (i, j)) = pkR_b_cross R N K (i, j) :=
    pkR_b_psi_prod K _
  have hs : ∀ k : ℕ, (pkR_b_psi R (fun d => d ∈ K)).toRingHom ((((-1) ^ k : ℤ)) : MvPolynomial (ℕ × ℕ) R) =
      ((((-1) ^ k : ℤ)) : MvPolynomial (ℕ × ℕ) R) := fun k => map_intCast _ _
  have hL : PowerSeries.map (pkR_b_psi R (fun d => relab N i d ∈ K)).toRingHom (pkSp_F R (j - i + 1) T1) =
      pkR_b_F R (j - i + 1) (pkR_b_pull N i (j - i + 1) K) T1 := by
    refine pkR_b_F_psi _ _ _ _ (fun d hd => ?_) (fun d hd hs hdK => ?_)
    · have hd' := (mem_filter.1 hd).1
      constructor
      · intro h; exact mem_filter.2 ⟨hd', h⟩
      · intro h; exact (mem_filter.1 h).2
    · have hpar := (pkSp_mapL (N := N) hi hij hjN hne (h1 hd)).2.2
      have hodd' := (mem_filter.1 (hK hdK)).2
      have hdd := mem_diagonals.1 (h1 hd)
      exact hs (pkSp_shiftSign_odd (by omega) (by omega))
  have hR : PowerSeries.map (pkR_b_psi R (fun d => relab N j d ∈ K)).toRingHom (pkSp_F R (N - j + i + 1) T2) =
      pkR_b_F R (N - j + i + 1) (pkR_b_pull N j (N - j + i + 1) K) T2 := by
    refine pkR_b_F_psi _ _ _ _ (fun d hd => ?_) (fun d hd hs hdK => ?_)
    · have hd' := (mem_filter.1 hd).1
      constructor
      · intro h; exact mem_filter.2 ⟨hd', h⟩
      · intro h; exact (mem_filter.1 h).2
    · have hpar := (pkSp_mapR (N := N) hi hij hjN hne hE (h2 hd)).2.2
      have hodd' := (mem_filter.1 (hK hdK)).2
      have hdd := mem_diagonals.1 (h2 hd)
      exact hs (pkSp_shiftSign_odd (by omega) (by omega))
  rw [hc, hs, hs, hL, hR]

/-- Off the chord, banning `C` multiplies the summand by `X_C`. -/
theorem pkR_b_F_erase {R : Type*} [CommRing R] {n : ℕ} {K T : Finset (ℕ × ℕ)} {C : ℕ × ℕ}
    (hCo : C ∈ oddDiagonals n) (hCK : C ∈ K) (hCT : C ∉ T) :
    pkR_b_F R n (K.erase C) T = PowerSeries.C (MvPolynomial.X C) * pkR_b_F R n K T := by
  have e : (oddDiagonals n \ T) \ K.erase C = insert C ((oddDiagonals n \ T) \ K) := by
    ext d
    simp only [mem_insert, mem_sdiff, mem_erase]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      by_cases hd : d = C
      · exact Or.inl hd
      · exact Or.inr ⟨⟨h1, h2⟩, fun h => h3 ⟨hd, h⟩⟩
    · rintro (rfl | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨⟨hCo, hCT⟩, fun h => h.1 rfl⟩
      · exact ⟨⟨h1, h2⟩, fun h => h3 h.2⟩
  have hn : C ∉ (oddDiagonals n \ T) \ K := fun h => (mem_sdiff.1 h).2 hCK
  show PowerSeries.C (Finset.prod ((oddDiagonals n \ T) \ K.erase C) (fun d => (MvPolynomial.X d : MvPolynomial (ℕ × ℕ) R))) *
      Finset.prod (T.filter (fun d => shiftSign d ≠ 0)) (fun d => shiftSeriesP R d) =
    PowerSeries.C (MvPolynomial.X C) * (PowerSeries.C (Finset.prod ((oddDiagonals n \ T) \ K)
      (fun d => (MvPolynomial.X d : MvPolynomial (ℕ × ℕ) R))) *
      Finset.prod (T.filter (fun d => shiftSign d ≠ 0)) (fun d => shiftSeriesP R d))
  rw [e, prod_insert hn, map_mul, mul_assoc]

theorem pkR_b_disj_erase {K T : Finset (ℕ × ℕ)} {C : ℕ × ℕ} (hCT : C ∉ T) :
    Disjoint T (K.erase C) ↔ Disjoint T K := by
  constructor
  · intro h
    rw [disjoint_left] at h ⊢
    intro a ha haK
    exact h ha (mem_erase.2 ⟨fun e => hCT (e ▸ ha), haK⟩)
  · intro h; exact disjoint_of_subset_right (erase_subset C K) h

/-- **Single-chord recursion of the ¬K numerators, every δ-order** (PREFORM-Res §5.7, numerator form): for `C ∈ K ⊆`
odd diagonals, `K′ = K ∖ {C}`, the triangulations avoiding `K′` split by whether they contain `C`:
`AP^{¬K′}_N = X_C · AP^{¬K}_N + (Σ_{p} ± ren(AP^{¬K′_L}_L) · ren(AP^{¬K′_R}_R)) · crossProd^{¬K′}_C`. At `K = {C}` this
is `AP_residue` plus the `X_C`-part. -/
theorem pkR_b_split {R : Type*} [CommRing R] {N : ℕ} (hE : N % 2 = 0) {K : Finset (ℕ × ℕ)}
    (hK : K ⊆ oddDiagonals N) {C : ℕ × ℕ} (hC : C ∈ K) (m : ℕ) :
    pkR_b_AP R N m (K.erase C) = MvPolynomial.X C * pkR_b_AP R N m K +
      Finset.sum (antidiagonal m) (fun p => (-1 : MvPolynomial (ℕ × ℕ) R) ^ ((C.1 + 1) * p.1 + (C.2 + 1) * p.2) *
        (MvPolynomial.rename (relab N C.1)
            (pkR_b_AP R (C.2 - C.1 + 1) p.1 (pkR_b_pull N C.1 (C.2 - C.1 + 1) (K.erase C))) *
          MvPolynomial.rename (relab N C.2)
            (pkR_b_AP R (N - C.2 + C.1 + 1) p.2 (pkR_b_pull N C.2 (N - C.2 + C.1 + 1) (K.erase C))))) *
        pkR_b_cross R N (K.erase C) C := by
  have hCo : C ∈ oddDiagonals N := hK hC
  have hK' : K.erase C ⊆ oddDiagonals N := (erase_subset C K).trans hK
  have hCK' : C ∉ K.erase C := fun h => (mem_erase.1 h).1 rfl
  obtain ⟨i, j⟩ := C
  have hC1 := mem_filter.1 hCo
  have hC2 := mem_diagonals.1 hC1.1
  dsimp only at hC1 hC2 hCK' ⊢
  obtain ⟨hi, hjN, hij, hne⟩ := hC2
  have hodd := hC1.2
  have hQC : (i, j) ∈ pkSp_S (fun _ => True) N := pkSp_mem_S.2 ⟨hC1.1, trivial⟩
  -- the sums as sums over all triangulations
  have eA : ∀ (K0 : Finset (ℕ × ℕ)), pkR_b_AP R N m K0 = PowerSeries.coeff m (Finset.sum (triangulations N)
      (fun T => if Disjoint T K0 then pkR_b_F R N K0 T else 0)) := by
    intro K0
    rw [← sum_filter]; rfl
  rw [eA, eA]
  -- split by `C ∈ T`
  rw [← sum_filter_add_sum_filter_not (triangulations N) (fun T => (i, j) ∈ T)
    (fun T => if Disjoint T (K.erase (i, j)) then pkR_b_F R N (K.erase (i, j)) T else 0)]
  have hoff : Finset.sum ((triangulations N).filter (fun T => ¬ (i, j) ∈ T))
      (fun T => if Disjoint T (K.erase (i, j)) then pkR_b_F R N (K.erase (i, j)) T else 0) =
      PowerSeries.C (MvPolynomial.X (i, j)) * Finset.sum (triangulations N)
        (fun T => if Disjoint T K then pkR_b_F R N K T else 0) := by
    rw [mul_sum, ← sum_filter_add_sum_filter_not (triangulations N) (fun T => (i, j) ∈ T)]
    have z : Finset.sum ((triangulations N).filter (fun T => (i, j) ∈ T))
        (fun T => PowerSeries.C (MvPolynomial.X (i, j)) * (if Disjoint T K then pkR_b_F R N K T else 0)) = 0 := by
      refine sum_eq_zero fun T hT => ?_
      have hT' := (mem_filter.1 hT).2
      have hnd : ¬ Disjoint T K := fun h => disjoint_left.1 h hT' hC
      rw [if_neg hnd, mul_zero]
    rw [z, zero_add]
    refine sum_congr rfl fun T hT => ?_
    have hT' := (mem_filter.1 hT).2
    by_cases hd : Disjoint T K
    · rw [if_pos hd, if_pos ((pkR_b_disj_erase hT').2 hd), pkR_b_F_erase hCo hC hT']
    · rw [if_neg hd, if_neg (fun h => hd ((pkR_b_disj_erase hT').1 h)), mul_zero]
  rw [hoff]
  -- the chord part: glue
  rw [pkSp_sum_split triangulations pkSp_tri_iff hi hij hjN hne hE hQC]
  have hsub : ∀ n T, T ∈ triangulations n → T ⊆ diagonals n := fun n T hT => (mem_triangulations.1 hT).1
  have hg : ∀ x ∈ triangulations (j - i + 1) ×ˢ triangulations (N - j + i + 1),
      (if Disjoint (pkSp_glue N i j x.1 x.2) (K.erase (i, j))
        then pkR_b_F R N (K.erase (i, j)) (pkSp_glue N i j x.1 x.2) else 0) =
      PowerSeries.C (pkR_b_cross R N (K.erase (i, j)) (i, j)) *
        ((if Disjoint x.1 (pkR_b_pull N i (j - i + 1) (K.erase (i, j))) then
            PowerSeries.rescale ((((-1) ^ (i + 1) : ℤ)) : MvPolynomial (ℕ × ℕ) R)
              (PowerSeries.map (MvPolynomial.rename (relab N i)).toRingHom
                (pkR_b_F R (j - i + 1) (pkR_b_pull N i (j - i + 1) (K.erase (i, j))) x.1)) else 0) *
          (if Disjoint x.2 (pkR_b_pull N j (N - j + i + 1) (K.erase (i, j))) then
            PowerSeries.rescale ((((-1) ^ (j + 1) : ℤ)) : MvPolynomial (ℕ × ℕ) R)
              (PowerSeries.map (MvPolynomial.rename (relab N j)).toRingHom
                (pkR_b_F R (N - j + i + 1) (pkR_b_pull N j (N - j + i + 1) (K.erase (i, j))) x.2)) else 0)) := by
    intro x hx
    have h1 := hsub _ _ (mem_product.1 hx).1
    have h2 := hsub _ _ (mem_product.1 hx).2
    rw [pkR_b_F_glue hi hij hjN hne hE hodd hK' h1 h2]
    by_cases d1 : Disjoint x.1 (pkR_b_pull N i (j - i + 1) (K.erase (i, j)))
    · by_cases d2 : Disjoint x.2 (pkR_b_pull N j (N - j + i + 1) (K.erase (i, j)))
      · rw [if_pos ((pkR_b_disj_glue hCK' h1 h2).2 ⟨d1, d2⟩), if_pos d1, if_pos d2]
      · rw [if_neg (fun h => d2 ((pkR_b_disj_glue hCK' h1 h2).1 h).2), if_neg d2, mul_zero, mul_zero]
    · rw [if_neg (fun h => d1 ((pkR_b_disj_glue hCK' h1 h2).1 h).1), if_neg d1, zero_mul, mul_zero]
  rw [sum_congr rfl hg]
  have hprod : ∀ (A B : Finset (Finset (ℕ × ℕ))) (c : PowerSeries (MvPolynomial (ℕ × ℕ) R))
      (f g : Finset (ℕ × ℕ) → PowerSeries (MvPolynomial (ℕ × ℕ) R)),
      Finset.sum (A ×ˢ B) (fun x => c * (f x.1 * g x.2)) =
        c * (Finset.sum A (fun T => f T) * Finset.sum B (fun T => g T)) := by
    intro A B c f g
    rw [sum_mul_sum, mul_sum, sum_product]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum]
  rw [hprod _ _ _ (fun T => if Disjoint T (pkR_b_pull N i (j - i + 1) (K.erase (i, j))) then
        PowerSeries.rescale ((((-1) ^ (i + 1) : ℤ)) : MvPolynomial (ℕ × ℕ) R)
          (PowerSeries.map (MvPolynomial.rename (relab N i)).toRingHom
            (pkR_b_F R (j - i + 1) (pkR_b_pull N i (j - i + 1) (K.erase (i, j))) T)) else 0)
    (fun T => if Disjoint T (pkR_b_pull N j (N - j + i + 1) (K.erase (i, j))) then
        PowerSeries.rescale ((((-1) ^ (j + 1) : ℤ)) : MvPolynomial (ℕ × ℕ) R)
          (PowerSeries.map (MvPolynomial.rename (relab N j)).toRingHom
            (pkR_b_F R (N - j + i + 1) (pkR_b_pull N j (N - j + i + 1) (K.erase (i, j))) T)) else 0)]
  have eL : Finset.sum (triangulations (j - i + 1)) (fun T =>
      if Disjoint T (pkR_b_pull N i (j - i + 1) (K.erase (i, j))) then
        PowerSeries.rescale ((((-1) ^ (i + 1) : ℤ)) : MvPolynomial (ℕ × ℕ) R)
          (PowerSeries.map (MvPolynomial.rename (relab N i)).toRingHom
            (pkR_b_F R (j - i + 1) (pkR_b_pull N i (j - i + 1) (K.erase (i, j))) T)) else 0) =
      PowerSeries.rescale ((((-1) ^ (i + 1) : ℤ)) : MvPolynomial (ℕ × ℕ) R)
        (PowerSeries.map (MvPolynomial.rename (relab N i)).toRingHom
          (Finset.sum ((triangulations (j - i + 1)).filter
            (fun T => Disjoint T (pkR_b_pull N i (j - i + 1) (K.erase (i, j)))))
            (fun T => pkR_b_F R (j - i + 1) (pkR_b_pull N i (j - i + 1) (K.erase (i, j))) T))) := by
    rw [map_sum (PowerSeries.map _), map_sum (PowerSeries.rescale _), sum_filter]
  have eR : Finset.sum (triangulations (N - j + i + 1)) (fun T =>
      if Disjoint T (pkR_b_pull N j (N - j + i + 1) (K.erase (i, j))) then
        PowerSeries.rescale ((((-1) ^ (j + 1) : ℤ)) : MvPolynomial (ℕ × ℕ) R)
          (PowerSeries.map (MvPolynomial.rename (relab N j)).toRingHom
            (pkR_b_F R (N - j + i + 1) (pkR_b_pull N j (N - j + i + 1) (K.erase (i, j))) T)) else 0) =
      PowerSeries.rescale ((((-1) ^ (j + 1) : ℤ)) : MvPolynomial (ℕ × ℕ) R)
        (PowerSeries.map (MvPolynomial.rename (relab N j)).toRingHom
          (Finset.sum ((triangulations (N - j + i + 1)).filter
            (fun T => Disjoint T (pkR_b_pull N j (N - j + i + 1) (K.erase (i, j)))))
            (fun T => pkR_b_F R (N - j + i + 1) (pkR_b_pull N j (N - j + i + 1) (K.erase (i, j))) T))) := by
    rw [map_sum (PowerSeries.map _), map_sum (PowerSeries.rescale _), sum_filter]
  rw [eL, eR, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul, mul_sum, sum_mul,
    add_comm]
  refine (add_right_inj _).2 (sum_congr rfl fun p _ => ?_)
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_rescale, PowerSeries.coeff_map, PowerSeries.coeff_map]
  have e1 : PowerSeries.coeff p.1 (Finset.sum ((triangulations (j - i + 1)).filter
      (fun T => Disjoint T (pkR_b_pull N i (j - i + 1) (K.erase (i, j)))))
        (fun T => pkR_b_F R (j - i + 1) (pkR_b_pull N i (j - i + 1) (K.erase (i, j))) T)) =
      pkR_b_AP R (j - i + 1) p.1 (pkR_b_pull N i (j - i + 1) (K.erase (i, j))) := rfl
  have e2 : PowerSeries.coeff p.2 (Finset.sum ((triangulations (N - j + i + 1)).filter
      (fun T => Disjoint T (pkR_b_pull N j (N - j + i + 1) (K.erase (i, j)))))
        (fun T => pkR_b_F R (N - j + i + 1) (pkR_b_pull N j (N - j + i + 1) (K.erase (i, j))) T)) =
      pkR_b_AP R (N - j + i + 1) p.2 (pkR_b_pull N j (N - j + i + 1) (K.erase (i, j))) := rfl
  rw [e1, e2]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  push_cast
  ring

/-- The pull-back of odd diagonals consists of odd diagonals. -/
theorem pkR_b_pull_odd {N i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hjN : j ≤ N) (hne : ¬ (i = 1 ∧ j = N))
    (hE : N % 2 = 0) {K : Finset (ℕ × ℕ)} (hK : K ⊆ oddDiagonals N) :
    pkR_b_pull N i (j - i + 1) K ⊆ oddDiagonals (j - i + 1) ∧
      pkR_b_pull N j (N - j + i + 1) K ⊆ oddDiagonals (N - j + i + 1) := by
  constructor
  · intro d hd
    have hd1 := mem_filter.1 hd
    have hpar := (pkSp_mapL (N := N) hi hij hjN hne hd1.1).2.2
    have ho := (mem_filter.1 (hK hd1.2)).2
    exact mem_filter.2 ⟨hd1.1, by omega⟩
  · intro d hd
    have hd1 := mem_filter.1 hd
    have hpar := (pkSp_mapR (N := N) hi hij hjN hne hE hd1.1).2.2
    have ho := (mem_filter.1 (hK hd1.2)).2
    exact mem_filter.2 ⟨hd1.1, by omega⟩

/-- **δ-order bound for the ¬K numerators** (PREFORM-Res §8.3 g2, numerator form; the input of §5.7): for every even
`N ≥ 4` and every set `K` of odd (mixed) diagonals, the ¬K amplitude has no order below `N − 2`. Induction on `N`, then
on `K`, through `pkR_b_split` (base `K = ∅`: `AP_eq_zero`). Over a domain (the `X_C` factor is cancelled). -/
theorem pkR_b_low {R : Type*} [CommRing R] [IsDomain R] :
    ∀ N : ℕ, 4 ≤ N → N % 2 = 0 → ∀ K : Finset (ℕ × ℕ), K ⊆ oddDiagonals N → ∀ m : ℕ, m < N - 2 →
      pkR_b_AP R N m K = 0 := by
  intro N
  refine Nat.strong_induction_on N ?_
  intro N ih hN hE K
  refine Finset.induction_on K ?_ ?_
  · intro _ m hm
    rw [pkR_b_AP_empty]
    exact AP_eq_zero hN hE hm
  · intro C K' hCK' ihK hsub m hm
    have hK : insert C K' ⊆ oddDiagonals N := hsub
    have hC : C ∈ insert C K' := mem_insert_self C K'
    have hs := pkR_b_split (R := R) hE hK hC m
    rw [erase_insert hCK', ihK ((subset_insert C K').trans hK) m hm] at hs
    have hCo : C ∈ oddDiagonals N := hK hC
    have hc := pkZ_child hE hCo
    have hC1 := mem_filter.1 hCo
    have hC2 := mem_diagonals.1 hC1.1
    obtain ⟨hi, hjN, hij, hne⟩ := hC2
    have hp := pkR_b_pull_odd (N := N) (i := C.1) (j := C.2) hi hij hjN hne hE ((subset_insert C K').trans hK)
    have z : Finset.sum (antidiagonal m) (fun p => (-1 : MvPolynomial (ℕ × ℕ) R) ^ ((C.1 + 1) * p.1 + (C.2 + 1) * p.2) *
        (MvPolynomial.rename (relab N C.1) (pkR_b_AP R (C.2 - C.1 + 1) p.1 (pkR_b_pull N C.1 (C.2 - C.1 + 1) K')) *
          MvPolynomial.rename (relab N C.2)
            (pkR_b_AP R (N - C.2 + C.1 + 1) p.2 (pkR_b_pull N C.2 (N - C.2 + C.1 + 1) K')))) = 0 := by
      refine sum_eq_zero fun p hp' => ?_
      have hp'' := HasAntidiagonal.mem_antidiagonal.1 hp'
      by_cases h1 : p.1 < C.2 - C.1 + 1 - 2
      · rw [ih (C.2 - C.1 + 1) hc.2.2.1 hc.1 hc.2.1 _ hp.1 p.1 h1, map_zero, zero_mul, mul_zero]
      · rw [ih (N - C.2 + C.1 + 1) hc.2.2.2.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 _ hp.2 p.2 (by omega), map_zero,
          mul_zero, mul_zero]
    rw [z, zero_mul, add_zero] at hs
    exact (mul_eq_zero.1 hs.symm).resolve_left (MvPolynomial.X_ne_zero C)

/-- **I3, numerator form** (`pkR_b_I3num`; PREFORM-Res §5.7 / §8.3 g2 — its first Lean statement, frozen here). Source:
BLUEPRINT App. B I3 (grouping identity (★), R2-Z188 R1 M3), recast in PREFORM §5.7 as the single-chord recursion with a
banned set `K′ = K ∖ {C}`: `A^{¬K′}_N = A^{¬K}_N + A^{¬K′_L}_L · A^{¬K′_R}_R / X_C`. Numerator form over the denominators
`∏_{odd d ∉ K′}` (`pkR_b_NP`): the children are the base's `relab` sides of `C` (the `NP_residue` labelling) with the
pulled-back banned sets. At `K = {C}` it is `NP_residue` together with the `X_C`-part; iterating it inside a child reaches
the non-contiguous vertex lists of §5.7. -/
theorem pkR_b_I3num {R : Type*} [CommRing R] [IsDomain R] {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0)
    {K : Finset (ℕ × ℕ)} (hK : K ⊆ oddDiagonals N) {C : ℕ × ℕ} (hC : C ∈ K) :
    pkR_b_NP R N (K.erase C) = MvPolynomial.X C * pkR_b_NP R N K +
      MvPolynomial.rename (relab N C.1) (pkR_b_NP R (C.2 - C.1 + 1) (pkR_b_pull N C.1 (C.2 - C.1 + 1) (K.erase C))) *
        MvPolynomial.rename (relab N C.2)
          (pkR_b_NP R (N - C.2 + C.1 + 1) (pkR_b_pull N C.2 (N - C.2 + C.1 + 1) (K.erase C))) *
        pkR_b_cross R N (K.erase C) C := by
  have hCo : C ∈ oddDiagonals N := hK hC
  have hc := pkZ_child hE hCo
  have hC1 := mem_filter.1 hCo
  have hC2 := mem_diagonals.1 hC1.1
  obtain ⟨hi, hjN, hij, hne⟩ := hC2
  have hp := pkR_b_pull_odd (N := N) (i := C.1) (j := C.2) hi hij hjN hne hE ((erase_subset C K).trans hK)
  have e0 : ∀ K0 : Finset (ℕ × ℕ), pkR_b_NP R N K0 = pkR_b_AP R N (N - 2) K0 := fun K0 => rfl
  rw [e0, e0, pkR_b_split hE hK hC (N - 2),
    sum_eq_single (C.2 - C.1 + 1 - 2, N - C.2 + C.1 + 1 - 2)]
  · rw [Even.neg_one_pow (pkZ_sign_even hc.2.1 hc.2.2.2.2.1 hc.1 hc.2.2.2.1), one_mul]
    rfl
  · intro p hp' hne'
    have hp'' := HasAntidiagonal.mem_antidiagonal.1 hp'
    by_cases h1 : p.1 < C.2 - C.1 + 1 - 2
    · rw [pkR_b_low (C.2 - C.1 + 1) hc.1 hc.2.1 _ hp.1 p.1 h1, map_zero, zero_mul, mul_zero]
    · by_cases h2 : p.2 < N - C.2 + C.1 + 1 - 2
      · rw [pkR_b_low (N - C.2 + C.1 + 1) hc.2.2.2.1 hc.2.2.2.2.1 _ hp.2 p.2 h2, map_zero, mul_zero, mul_zero]
      · exfalso
        apply hne'
        refine Prod.ext ?_ ?_ <;> dsimp only <;> omega
  · intro h
    exact absurd (HasAntidiagonal.mem_antidiagonal.2
      (show (C.2 - C.1 + 1 - 2) + (N - C.2 + C.1 + 1 - 2) = N - 2 by omega)) h

/-! ### R1 (chain lemma, BLUEPRINT App. B R1 = R2-Z188 C1 + R1; PREFORM-Res §5.1) -/

/-- Membership in the head of a chord `(q1, q2)`, arithmetically. -/
theorem pkR_b_mem_head {N m q1 q2 : ℕ} :
    m ∈ oddSide N (q1, q2) ↔ (q1 % 2 = 1 ∧ q1 ≤ m ∧ m ≤ q2 - 1) ∨
      (q1 % 2 = 0 ∧ 1 ≤ m ∧ m ≤ N ∧ ¬ (q1 ≤ m ∧ m ≤ q2 - 1)) := by
  show m ∈ (if q1 % 2 = 1 then Icc q1 (q2 - 1) else Icc 1 N \ Icc q1 (q2 - 1)) ↔ _
  split_ifs with h
  · rw [mem_Icc]
    constructor
    · intro h'; exact Or.inl ⟨h, h'⟩
    · intro h'; omega
  · rw [mem_sdiff, mem_Icc, mem_Icc]
    constructor
    · intro h'; omega
    · intro h'; omega

theorem pkR_b_headO {N m q1 q2 : ℕ} (hq : q1 % 2 = 1) :
    m ∈ oddSide N (q1, q2) ↔ q1 ≤ m ∧ m ≤ q2 - 1 := by
  rw [pkR_b_mem_head]
  constructor
  · intro h; omega
  · intro h; omega

theorem pkR_b_headE {N m q1 q2 : ℕ} (hq : q1 % 2 = 0) :
    m ∈ oddSide N (q1, q2) ↔ 1 ≤ m ∧ m ≤ N ∧ (m < q1 ∨ q2 - 1 < m) := by
  rw [pkR_b_mem_head]
  constructor
  · intro h; omega
  · intro h; omega

theorem pkR_b_odd_iff {N q1 q2 : ℕ} : (q1, q2) ∈ oddDiagonals N ↔
    1 ≤ q1 ∧ q2 ≤ N ∧ q1 + 2 ≤ q2 ∧ ¬ (q1 = 1 ∧ q2 = N) ∧ (q2 - q1) % 2 = 1 := by
  constructor
  · intro h
    have h1 := mem_filter.1 h
    have h2 := mem_diagonals.1 h1.1
    dsimp only at h1 h2
    omega
  · intro h
    refine mem_filter.2 ⟨mem_diagonals.2 ?_, ?_⟩ <;> dsimp only <;> omega

/-- Crossing chords have incomparable heads. -/
theorem pkR_b_cross_not_sub {N q1 q2 r1 r2 : ℕ} (hQ : (q1, q2) ∈ oddDiagonals N)
    (hQ' : (r1, r2) ∈ oddDiagonals N) (hc : Crosses (q1, q2) (r1, r2)) :
    ¬ oddSide N (q1, q2) ⊆ oddSide N (r1, r2) := by
  have a := pkR_b_odd_iff.1 hQ
  have b := pkR_b_odd_iff.1 hQ'
  have c : (q1 < r1 ∧ r1 < q2 ∧ q2 < r2) ∨ (r1 < q1 ∧ q1 < r2 ∧ r2 < q2) := hc
  intro hs
  have t1 := @hs q1
  have t2 := @hs r1
  have t3 := @hs N
  have t4 := @hs (r2 - 1)
  have t5 := @hs (q2 - 1)
  rcases Nat.mod_two_eq_zero_or_one q1 with hq | hq <;> rcases Nat.mod_two_eq_zero_or_one r1 with hr | hr
  · rw [pkR_b_headE hq, pkR_b_headE hr] at t4 t2
    rcases c with c | c
    · exact absurd (t4 (by omega)) (by omega)
    · exact absurd (t2 (by omega)) (by omega)
  · rw [pkR_b_headE hq, pkR_b_headO hr] at t3
    exact absurd (t3 (by omega)) (by omega)
  · rw [pkR_b_headO hq, pkR_b_headE hr] at t2 t1
    rcases c with c | c
    · exact absurd (t2 (by omega)) (by omega)
    · exact absurd (t1 (by omega)) (by omega)
  · rw [pkR_b_headO hq, pkR_b_headO hr] at t1 t5
    rcases c with c | c
    · exact absurd (t1 (by omega)) (by omega)
    · exact absurd (t5 (by omega)) (by omega)

/-- **R1, pairwise form.** Two mixed chords whose heads share a leg `x` and both miss a leg `y` cross iff their heads are
incomparable. -/
theorem pkR_b_R1 {N q1 q2 r1 r2 x y : ℕ} (hQ : (q1, q2) ∈ oddDiagonals N) (hQ' : (r1, r2) ∈ oddDiagonals N)
    (hx1 : x ∈ oddSide N (q1, q2)) (hx2 : x ∈ oddSide N (r1, r2)) (hy : 1 ≤ y ∧ y ≤ N)
    (hy1 : y ∉ oddSide N (q1, q2)) (hy2 : y ∉ oddSide N (r1, r2)) :
    ¬ Crosses (q1, q2) (r1, r2) ↔
      (oddSide N (q1, q2) ⊆ oddSide N (r1, r2) ∨ oddSide N (r1, r2) ⊆ oddSide N (q1, q2)) := by
  constructor
  · intro hc
    have a := pkR_b_odd_iff.1 hQ
    have b := pkR_b_odd_iff.1 hQ'
    have c : ¬ ((q1 < r1 ∧ r1 < q2 ∧ q2 < r2) ∨ (r1 < q1 ∧ q1 < r2 ∧ r2 < q2)) := hc
    have g : (q1 ≤ r1 ∧ r2 ≤ q2) ∨ (r1 ≤ q1 ∧ q2 ≤ r2) ∨ q2 ≤ r1 ∨ r2 ≤ q1 := by omega
    rcases Nat.mod_two_eq_zero_or_one q1 with hq | hq <;> rcases Nat.mod_two_eq_zero_or_one r1 with hr | hr
    · rw [pkR_b_headE hq] at hx1 hy1
      rw [pkR_b_headE hr] at hx2 hy2
      rcases g with g | g | g | g
      · left; intro m hm; rw [pkR_b_headE hr]; rw [pkR_b_headE hq] at hm; omega
      · right; intro m hm; rw [pkR_b_headE hq]; rw [pkR_b_headE hr] at hm; omega
      · exfalso; omega
      · exfalso; omega
    · rw [pkR_b_headE hq] at hx1 hy1
      rw [pkR_b_headO hr] at hx2 hy2
      rcases g with g | g | g | g
      · exfalso; omega
      · exfalso; omega
      · right; intro m hm; rw [pkR_b_headE hq]; rw [pkR_b_headO hr] at hm; omega
      · right; intro m hm; rw [pkR_b_headE hq]; rw [pkR_b_headO hr] at hm; omega
    · rw [pkR_b_headO hq] at hx1 hy1
      rw [pkR_b_headE hr] at hx2 hy2
      rcases g with g | g | g | g
      · exfalso; omega
      · exfalso; omega
      · left; intro m hm; rw [pkR_b_headE hr]; rw [pkR_b_headO hq] at hm; omega
      · left; intro m hm; rw [pkR_b_headE hr]; rw [pkR_b_headO hq] at hm; omega
    · rw [pkR_b_headO hq] at hx1 hy1
      rw [pkR_b_headO hr] at hx2 hy2
      rcases g with g | g | g | g
      · right; intro m hm; rw [pkR_b_headO hq]; rw [pkR_b_headO hr] at hm; omega
      · left; intro m hm; rw [pkR_b_headO hr]; rw [pkR_b_headO hq] at hm; omega
      · exfalso; omega
      · exfalso; omega
  · rintro (h | h) hc
    · exact pkR_b_cross_not_sub hQ hQ' hc h
    · exact pkR_b_cross_not_sub hQ' hQ (pkSp_cross_symm.1 hc) h

/-- A mixed chord is determined by its head. -/
theorem pkR_b_head_inj {N q1 q2 r1 r2 : ℕ} (hQ : (q1, q2) ∈ oddDiagonals N) (hQ' : (r1, r2) ∈ oddDiagonals N)
    (h : oddSide N (q1, q2) = oddSide N (r1, r2)) : q1 = r1 ∧ q2 = r2 := by
  have a := pkR_b_odd_iff.1 hQ
  have b := pkR_b_odd_iff.1 hQ'
  have t1 := Finset.ext_iff.1 h q1
  have t2 := Finset.ext_iff.1 h r1
  have t3 := Finset.ext_iff.1 h (q2 - 1)
  have t4 := Finset.ext_iff.1 h (r2 - 1)
  have t5 := Finset.ext_iff.1 h N
  rcases Nat.mod_two_eq_zero_or_one q1 with hq | hq <;> rcases Nat.mod_two_eq_zero_or_one r1 with hr | hr
  · rw [pkR_b_headE hq, pkR_b_headE hr] at t1 t2 t3 t4
    have e1 := t1.2
    have e2 := t2.1
    have e3 := t3.2
    have e4 := t4.1
    omega
  · rw [pkR_b_headE hq, pkR_b_headO hr] at t5
    exact absurd (t5.1 (by omega)) (by omega)
  · rw [pkR_b_headO hq, pkR_b_headE hr] at t5
    exact absurd (t5.2 (by omega)) (by omega)
  · rw [pkR_b_headO hq, pkR_b_headO hr] at t1 t2 t3 t4
    have e1 := t1.1
    have e2 := t2.2
    have e3 := t3.1
    have e4 := t4.2
    omega

/-- A leg of the head (its odd end leg). -/
theorem pkR_b_head_ne {N q1 q2 : ℕ} (hQ : (q1, q2) ∈ oddDiagonals N) :
    (if q1 % 2 = 1 then q1 else q2) ∈ oddSide N (q1, q2) := by
  have a := pkR_b_odd_iff.1 hQ
  rw [pkR_b_mem_head]
  split_ifs with h <;> omega

/-- A leg outside the head (its even end leg on the tail side). -/
theorem pkR_b_tail_ne {N q1 q2 : ℕ} (hQ : (q1, q2) ∈ oddDiagonals N) :
    (if q1 % 2 = 1 then q2 else q1) ∉ oddSide N (q1, q2) := by
  have a := pkR_b_odd_iff.1 hQ
  rw [pkR_b_mem_head]
  split_ifs with h <;> omega

/-- **R1 (chain lemma), class form.** In a set of mixed chords with a bottom `b` and a top `t` (every head between
`A_b` and `A_t`), two chords do not cross iff their heads are nested; distinct members have strictly nested heads
(`pkR_b_head_inj`). -/
theorem pkR_b_chain {N : ℕ} {b t Q Q' : ℕ × ℕ} (hb : b ∈ oddDiagonals N) (ht : t ∈ oddDiagonals N)
    (hQ : Q ∈ oddDiagonals N) (hQ' : Q' ∈ oddDiagonals N)
    (h1 : oddSide N b ⊆ oddSide N Q) (h2 : oddSide N Q ⊆ oddSide N t)
    (h3 : oddSide N b ⊆ oddSide N Q') (h4 : oddSide N Q' ⊆ oddSide N t) :
    ¬ Crosses Q Q' ↔ (oddSide N Q ⊆ oddSide N Q' ∨ oddSide N Q' ⊆ oddSide N Q) := by
  obtain ⟨b1, b2⟩ := b
  obtain ⟨t1, t2⟩ := t
  obtain ⟨q1, q2⟩ := Q
  obtain ⟨r1, r2⟩ := Q'
  have hx := pkR_b_head_ne hb
  have hy := pkR_b_tail_ne ht
  have ta := pkR_b_odd_iff.1 ht
  refine pkR_b_R1 hQ hQ' (h1 hx) (h3 hx) (by split_ifs <;> omega) (fun h => hy (h2 h)) (fun h => hy (h4 h))

theorem pkR_b_NP_empty {R : Type*} [CommRing R] (n : ℕ) : pkR_b_NP R n ∅ = NP R n := by
  show pkR_b_AP R n (n - 2) ∅ = AP R n (n - 2)
  exact pkR_b_AP_empty n (n - 2)

theorem pkR_b_pull_empty (N b n : ℕ) : pkR_b_pull N b n ∅ = ∅ := by
  show (diagonals n).filter (fun d => relab N b d ∈ (∅ : Finset (ℕ × ℕ))) = ∅
  exact filter_false_of_mem fun d _ h => by simp at h

theorem pkR_b_cross_empty {R : Type*} [CommRing R] (N : ℕ) (C : ℕ × ℕ) :
    pkR_b_cross R N ∅ C = crossProd R N C := by
  show Finset.prod (((oddDiagonals N).filter (fun d => Crosses d C)) \ ∅) (fun d => MvPolynomial.X d) = crossProd R N C
  rw [sdiff_empty]; rfl

/-- **I3 at `K = {C}`** (the `[ResNum]` identity with its explicit `X_C`-part): `NP_N = X_C · NP^{¬C}_N + NP_L · NP_R ·
crossProd_C`, children in the `NP_residue` labelling. -/
theorem pkR_b_res1 {R : Type*} [CommRing R] [IsDomain R] {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {C : ℕ × ℕ}
    (hC : C ∈ oddDiagonals N) :
    NP R N = MvPolynomial.X C * pkR_b_NP R N {C} +
      MvPolynomial.rename (relab N C.1) (NP R (C.2 - C.1 + 1)) *
        MvPolynomial.rename (relab N C.2) (NP R (N - C.2 + C.1 + 1)) * crossProd R N C := by
  have h := pkR_b_I3num (R := R) hN hE (K := {C}) (fun d hd => by rw [mem_singleton.1 hd]; exact hC)
    (mem_singleton_self C)
  rw [erase_singleton, pkR_b_NP_empty, pkR_b_pull_empty, pkR_b_pull_empty, pkR_b_NP_empty, pkR_b_NP_empty,
    pkR_b_cross_empty] at h
  exact h

/-! ### R17 (BLUEPRINT App. B §2 "¬K = full"; review R12-P7f-Res-R1 S1)

No chord of the class `K` (heads between `A_b` and `A_t`) is a diagonal of the tail child of the top `t` or of the head
child of the bottom `b`: the pull-back of `K` to those children is empty, so their ¬K numerators are the full child
numerators (`pkR_b_NP_empty`). Children in the `relab` labelling with the frozen starts and sizes (`tailStart` /
`tailLen`, `headStart` / `headLen`), i.e. the sides `NP_residue` / `pkR_b_I3num` produce. (The frozen `childSetB`
labelling is this one rotated by one leg; that is review M1, handled by `NLSM_rot` where the child loci are compared.) -/

/-- `vtx` on `1..2N`, as an omega-friendly disjunction. -/
theorem pkR_b_vtx2 {N u : ℕ} (h1 : 1 ≤ u) (h2 : u ≤ 2 * N) :
    (u ≤ N ∧ vtx N u = u) ∨ (N < u ∧ vtx N u = u - N) := by
  by_cases h : u ≤ N
  · exact Or.inl ⟨h, vtx_of_mem h1 h⟩
  · exact Or.inr ⟨by omega, vtx_of_gt (by omega) h2⟩

/-- Tail core: a mixed chord with head inside `A_t` and both end points among the dual points of the tail of `t` is `t`. -/
theorem pkR_b_R17_tcore {N q1 q2 t1 t2 : ℕ} (hQ : (q1, q2) ∈ oddDiagonals N) (ht : (t1, t2) ∈ oddDiagonals N)
    (hsub : oddSide N (q1, q2) ⊆ oddSide N (t1, t2))
    (hD : (t1 % 2 = 1 ∧ (t2 ≤ q1 ∨ q1 ≤ t1) ∧ (t2 ≤ q2 ∨ q2 ≤ t1)) ∨ (t1 % 2 = 0 ∧ t1 ≤ q1 ∧ q2 ≤ t2)) :
    q1 = t1 ∧ q2 = t2 := by
  have a := pkR_b_odd_iff.1 hQ
  have b := pkR_b_odd_iff.1 ht
  have s1 := @hsub q1
  have s2 := @hsub (q2 - 1)
  have s3 := @hsub N
  have s4 := @hsub t1
  have s5 := @hsub (t2 - 1)
  rcases Nat.mod_two_eq_zero_or_one q1 with hq | hq <;> rcases Nat.mod_two_eq_zero_or_one t1 with hr | hr
  · rw [pkR_b_headE hq, pkR_b_headE hr] at s1 s2 s3 s4 s5
    omega
  · rw [pkR_b_headE hq, pkR_b_headO hr] at s3
    omega
  · rw [pkR_b_headO hq, pkR_b_headE hr] at s1
    omega
  · rw [pkR_b_headO hq, pkR_b_headO hr] at s1 s2
    omega

/-- Head core: a mixed chord with head containing `A_b` and both end points among the dual points of the head of `b`
is `b`. -/
theorem pkR_b_R17_hcore {N q1 q2 b1 b2 : ℕ} (hQ : (q1, q2) ∈ oddDiagonals N) (hb : (b1, b2) ∈ oddDiagonals N)
    (hsub : oddSide N (b1, b2) ⊆ oddSide N (q1, q2))
    (hD : (b1 % 2 = 1 ∧ b1 ≤ q1 ∧ q2 ≤ b2) ∨ (b1 % 2 = 0 ∧ (b2 ≤ q1 ∨ q1 ≤ b1) ∧ (b2 ≤ q2 ∨ q2 ≤ b1))) :
    q1 = b1 ∧ q2 = b2 := by
  have a := pkR_b_odd_iff.1 hQ
  have b := pkR_b_odd_iff.1 hb
  have s1 := @hsub b1
  have s2 := @hsub (b2 - 1)
  have s3 := @hsub q1
  have s4 := @hsub (q2 - 1)
  have s5 := @hsub 1
  have s6 := @hsub N
  rcases Nat.mod_two_eq_zero_or_one q1 with hq | hq <;> rcases Nat.mod_two_eq_zero_or_one b1 with hr | hr
  · rw [pkR_b_headE hq, pkR_b_headE hr] at s1 s2 s3 s4 s5 s6
    omega
  · rw [pkR_b_headE hq, pkR_b_headO hr] at s3
    omega
  · rw [pkR_b_headO hq, pkR_b_headE hr] at s5 s6
    omega
  · rw [pkR_b_headO hq, pkR_b_headO hr] at s1 s2
    omega

/-- The start and size of the tail child of a mixed chord, unfolded. -/
theorem pkR_b_tail_data {N : ℕ} {t : ℕ × ℕ} (ht : t ∈ oddDiagonals N) :
    (t.1 % 2 = 1 ∧ tailStart t = t.2 ∧ tailLen N t = N - (t.2 - t.1)) ∨
      (t.1 % 2 = 0 ∧ tailStart t = t.1 ∧ tailLen N t = t.2 - t.1) := by
  have b := pkR_b_odd_iff.1 ht
  have eS : tailStart t = if t.1 % 2 = 1 then t.2 else t.1 := rfl
  have eL : tailLen N t = N - (if t.1 % 2 = 1 then t.2 - t.1 else N - (t.2 - t.1)) := rfl
  rw [eS, eL]
  split_ifs with h <;> omega

/-- The start and size of the head child of a mixed chord, unfolded. -/
theorem pkR_b_head_data {N : ℕ} {t : ℕ × ℕ} (ht : t ∈ oddDiagonals N) :
    (t.1 % 2 = 1 ∧ headStart t = t.1 ∧ headLen N t = t.2 - t.1) ∨
      (t.1 % 2 = 0 ∧ headStart t = t.2 ∧ headLen N t = N - (t.2 - t.1)) := by
  have b := pkR_b_odd_iff.1 ht
  have eS : headStart t = if t.1 % 2 = 1 then t.1 else t.2 := rfl
  have eL : headLen N t = if t.1 % 2 = 1 then t.2 - t.1 else N - (t.2 - t.1) := rfl
  rw [eS, eL]
  split_ifs with h <;> omega

/-- The parent chord of a child diagonal under `relab N s` (child of size `n`, `s ≥ 1`, `s + n − 1 ≤ 2N`). -/
theorem pkR_b_relab_eq {N s n : ℕ} {d : ℕ × ℕ} (hs : 1 ≤ s) (hn : s + n ≤ 2 * N + 1) (hd : d ∈ diagonals n) :
    ∃ p1 p2 : ℕ, relab N s d = (min p1 p2, max p1 p2) ∧
      ((d.1 + s - 1 ≤ N ∧ p1 = d.1 + s - 1) ∨ (N < d.1 + s - 1 ∧ p1 = d.1 + s - 1 - N)) ∧
      ((d.2 + s - 1 ≤ N ∧ p2 = d.2 + s - 1) ∨ (N < d.2 + s - 1 ∧ p2 = d.2 + s - 1 - N)) := by
  have hd' := mem_diagonals.1 hd
  refine ⟨vtx N (d.1 + s - 1), vtx N (d.2 + s - 1), rfl, ?_, ?_⟩
  · rcases pkR_b_vtx2 (N := N) (u := d.1 + s - 1) (by omega) (by omega) with h | h
    · exact Or.inl ⟨h.1, h.2⟩
    · exact Or.inr ⟨h.1, h.2⟩
  · rcases pkR_b_vtx2 (N := N) (u := d.2 + s - 1) (by omega) (by omega) with h | h
    · exact Or.inl ⟨h.1, h.2⟩
    · exact Or.inr ⟨h.1, h.2⟩

/-- **R17, tail side.** If every chord of `K` is mixed with head inside `A_t`, no chord of `K` pulls back to a diagonal of
the tail child of `t`. -/
theorem pkR_b_R17_tail {N : ℕ} {t : ℕ × ℕ} (ht : t ∈ oddDiagonals N) {K : Finset (ℕ × ℕ)}
    (hK : K ⊆ oddDiagonals N) (hKt : ∀ Q ∈ K, oddSide N Q ⊆ oddSide N t) :
    pkR_b_pull N (tailStart t) (tailLen N t + 1) K = ∅ := by
  refine filter_false_of_mem fun d hd hQ => ?_
  have hd' := mem_diagonals.1 hd
  have b := pkR_b_odd_iff.1 ht
  have hT := pkR_b_tail_data ht
  obtain ⟨p1, p2, e, h1, h2⟩ := pkR_b_relab_eq (N := N) (s := tailStart t) (n := tailLen N t + 1)
    (by omega) (by omega) hd
  rw [e] at hQ
  have hQo := hK hQ
  have hsub := hKt _ hQ
  obtain ⟨t1, t2⟩ := t
  dsimp only at hT hd' b h1 h2
  have c := pkR_b_R17_tcore hQo ht hsub (by omega)
  omega

/-- **R17, head side.** If every chord of `K` is mixed with head containing `A_b`, no chord of `K` pulls back to a
diagonal of the head child of `b`. -/
theorem pkR_b_R17_head {N : ℕ} {b : ℕ × ℕ} (hb : b ∈ oddDiagonals N) {K : Finset (ℕ × ℕ)}
    (hK : K ⊆ oddDiagonals N) (hKb : ∀ Q ∈ K, oddSide N b ⊆ oddSide N Q) :
    pkR_b_pull N (headStart b) (headLen N b + 1) K = ∅ := by
  refine filter_false_of_mem fun d hd hQ => ?_
  have hd' := mem_diagonals.1 hd
  have bb := pkR_b_odd_iff.1 hb
  have hH := pkR_b_head_data hb
  obtain ⟨p1, p2, e, h1, h2⟩ := pkR_b_relab_eq (N := N) (s := headStart b) (n := headLen N b + 1)
    (by omega) (by omega) hd
  rw [e] at hQ
  have hQo := hK hQ
  have hsub := hKb _ hQ
  obtain ⟨b1, b2⟩ := b
  dsimp only at hH hd' bb h1 h2
  have c := pkR_b_R17_hcore hQo hb hsub (by omega)
  omega

/-- **R17 for the ¬K side numerators**: with `K` the class (heads between `A_b` and `A_t`), the ¬K numerators of the tail
child of `t` and of the head child of `b` are the full child numerators. -/
theorem pkR_b_R17 {R : Type*} [CommRing R] {N : ℕ} {b t : ℕ × ℕ} (hb : b ∈ oddDiagonals N)
    (ht : t ∈ oddDiagonals N) {K : Finset (ℕ × ℕ)} (hK : K ⊆ oddDiagonals N)
    (hKbt : ∀ Q ∈ K, oddSide N b ⊆ oddSide N Q ∧ oddSide N Q ⊆ oddSide N t) :
    pkR_b_NP R (tailLen N t + 1) (pkR_b_pull N (tailStart t) (tailLen N t + 1) K) = NP R (tailLen N t + 1) ∧
      pkR_b_NP R (headLen N b + 1) (pkR_b_pull N (headStart b) (headLen N b + 1) K) = NP R (headLen N b + 1) := by
  rw [pkR_b_R17_tail ht hK (fun Q hQ => (hKbt Q hQ).2), pkR_b_R17_head hb hK (fun Q hQ => (hKbt Q hQ).1),
    pkR_b_NP_empty, pkR_b_NP_empty]
  exact ⟨rfl, rfl⟩

/-! ### [OmegaHyp] (PREFORM-Res §5.3, combinatorial half of R3; R2-Z188 C3 (1)–(4) + R2-Z182 C1(c))

For nested mixed chords `Q ≻ Q′` (`A_{Q′} ⊆ A_Q`), `μ := A_Q ∖ A_{Q′}` and `T(Q, Q′)` = {same-parity pairs inside `μ`} ∪
{odd `u ∈ μ` with `w ∈ A_{Q′}`} ∪ {even `u ∈ μ` with `w ∈ B_Q`}. (H3a) clean `Q`, `Q′` and (H3b) equal inner sets put
every diagonal of `T(Q, Q′)` into `S`. -/

/-- `T(Q, Q′)` as a predicate on a pair of legs (either order). -/
def pkR_b_TP (N : ℕ) (Q Q' : ℕ × ℕ) (a b : ℕ) : Prop :=
  (a % 2 = b % 2 ∧ a ∈ oddSide N Q ∧ a ∉ oddSide N Q' ∧ b ∈ oddSide N Q ∧ b ∉ oddSide N Q') ∨
  (a % 2 = 1 ∧ a ∈ oddSide N Q ∧ a ∉ oddSide N Q' ∧ b ∈ oddSide N Q') ∨
  (b % 2 = 1 ∧ b ∈ oddSide N Q ∧ b ∉ oddSide N Q' ∧ a ∈ oddSide N Q') ∨
  (a % 2 = 0 ∧ a ∈ oddSide N Q ∧ a ∉ oddSide N Q' ∧ b ∈ evenSide N Q) ∨
  (b % 2 = 0 ∧ b ∈ oddSide N Q ∧ b ∉ oddSide N Q' ∧ a ∈ evenSide N Q)

theorem pkR_b_TP_iff (N : ℕ) (Q Q' : ℕ × ℕ) (a b : ℕ) : pkR_b_TP N Q Q' a b ↔
    ((a % 2 = b % 2 ∧ a ∈ oddSide N Q ∧ a ∉ oddSide N Q' ∧ b ∈ oddSide N Q ∧ b ∉ oddSide N Q') ∨
    (a % 2 = 1 ∧ a ∈ oddSide N Q ∧ a ∉ oddSide N Q' ∧ b ∈ oddSide N Q') ∨
    (b % 2 = 1 ∧ b ∈ oddSide N Q ∧ b ∉ oddSide N Q' ∧ a ∈ oddSide N Q') ∨
    (a % 2 = 0 ∧ a ∈ oddSide N Q ∧ a ∉ oddSide N Q' ∧ b ∈ evenSide N Q) ∨
    (b % 2 = 0 ∧ b ∈ oddSide N Q ∧ b ∉ oddSide N Q' ∧ a ∈ evenSide N Q)) := Iff.rfl

theorem pkR_b_mem_even {N : ℕ} {P : ℕ × ℕ} {x : ℕ} (hx : 1 ≤ x ∧ x ≤ N) (h : x ∉ oddSide N P) :
    x ∈ evenSide N P := mem_sdiff.2 ⟨mem_Icc.2 hx, h⟩

theorem pkR_b_not_odd {N : ℕ} {P : ℕ × ℕ} {x : ℕ} (h : x ∈ evenSide N P) : x ∉ oddSide N P :=
  (mem_sdiff.1 h).2

theorem pkR_b_rect {N : ℕ} {P : ℕ × ℕ} {x y : ℕ} (hx : x ∈ oddSide N P) (hx2 : x % 2 = 0)
    (hy : y ∈ evenSide N P) (hy2 : y % 2 = 1) : (min x y, max x y) ∈ minRect N P :=
  mem_image.2 ⟨(x, y), mem_product.2 ⟨mem_filter.2 ⟨hx, hx2⟩, mem_filter.2 ⟨hy, hy2⟩⟩, rfl⟩

theorem pkR_b_inOO {N : ℕ} {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ} {a b : ℕ} (hm : (a, b) ∈ missing N S)
    (ha : a % 2 = 1) (hb : b % 2 = 1) (ha' : a ∈ oddSide N P) (hb' : b ∈ oddSide N P) :
    (a, b) ∈ innerOO N S P :=
  mem_filter.2 ⟨mem_filter.2 ⟨hm, ⟨ha, hb⟩⟩, ⟨ha', hb'⟩⟩

theorem pkR_b_inEE {N : ℕ} {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ} {a b : ℕ} (hm : (a, b) ∈ missing N S)
    (ha : a % 2 = 0) (hb : b % 2 = 0) (ha' : a ∈ evenSide N P) (hb' : b ∈ evenSide N P) :
    (a, b) ∈ innerEE N S P :=
  mem_filter.2 ⟨mem_filter.2 ⟨hm, ⟨ha, hb⟩⟩, ⟨ha', hb'⟩⟩

/-- **[OmegaHyp]** (H3a) + (H3b) ⇒ `T(Q, Q′) ⊆ S`. -/
theorem pkR_b_omegaHyp {N : ℕ} {S : Finset (ℕ × ℕ)} {Q Q' : ℕ × ℕ}
    (hsub : oddSide N Q' ⊆ oddSide N Q)
    (hmQ : Disjoint (minRect N Q) (missing N S)) (hmQ' : Disjoint (minRect N Q') (missing N S))
    (hee : innerEE N S Q = innerEE N S Q') (hoo : innerOO N S Q = innerOO N S Q')
    {a b : ℕ} (hab : (a, b) ∈ diagonals N) (hT : pkR_b_TP N Q Q' a b) : (a, b) ∈ S := by
  by_contra hS
  have hm : (a, b) ∈ missing N S := mem_sdiff.2 ⟨hab, hS⟩
  have hd := mem_diagonals.1 hab
  dsimp only at hd
  have ea : min a b = a := min_eq_left (show a ≤ b by omega)
  have eb : max a b = b := max_eq_right (show a ≤ b by omega)
  have ea' : min b a = a := min_eq_right (show a ≤ b by omega)
  have eb' : max b a = b := max_eq_left (show a ≤ b by omega)
  rcases (pkR_b_TP_iff N Q Q' a b).1 hT with h | h | h | h | h
  · obtain ⟨hp, ha, ha', hb, hb'⟩ := h
    rcases Nat.mod_two_eq_zero_or_one a with h2 | h2
    · have e : (a, b) ∈ innerEE N S Q' :=
        pkR_b_inEE hm h2 (by omega) (pkR_b_mem_even (by omega) ha') (pkR_b_mem_even (by omega) hb')
      rw [← hee] at e
      exact pkR_b_not_odd (mem_filter.1 e).2.1 ha
    · have e : (a, b) ∈ innerOO N S Q := pkR_b_inOO hm h2 (by omega) ha hb
      rw [hoo] at e
      exact ha' (mem_filter.1 e).2.1
  · obtain ⟨h2, ha, ha', hb⟩ := h
    rcases Nat.mod_two_eq_zero_or_one b with h3 | h3
    · have e := pkR_b_rect hb h3 (pkR_b_mem_even (by omega) ha') h2
      rw [ea', eb'] at e
      exact disjoint_left.1 hmQ' e hm
    · have e : (a, b) ∈ innerOO N S Q := pkR_b_inOO hm h2 h3 ha (hsub hb)
      rw [hoo] at e
      exact ha' (mem_filter.1 e).2.1
  · obtain ⟨h2, hb, hb', ha⟩ := h
    rcases Nat.mod_two_eq_zero_or_one a with h3 | h3
    · have e := pkR_b_rect ha h3 (pkR_b_mem_even (by omega) hb') h2
      rw [ea, eb] at e
      exact disjoint_left.1 hmQ' e hm
    · have e : (a, b) ∈ innerOO N S Q := pkR_b_inOO hm h3 h2 (hsub ha) hb
      rw [hoo] at e
      exact hb' (mem_filter.1 e).2.2
  · obtain ⟨h2, ha, ha', hb⟩ := h
    rcases Nat.mod_two_eq_zero_or_one b with h3 | h3
    · have e : (a, b) ∈ innerEE N S Q' := pkR_b_inEE hm h2 h3 (pkR_b_mem_even (by omega) ha')
        (pkR_b_mem_even (by omega) (fun h => pkR_b_not_odd hb (hsub h)))
      rw [← hee] at e
      exact pkR_b_not_odd (mem_filter.1 e).2.1 ha
    · have e := pkR_b_rect ha h2 hb h3
      rw [ea, eb] at e
      exact disjoint_left.1 hmQ e hm
  · obtain ⟨h2, hb, hb', ha⟩ := h
    rcases Nat.mod_two_eq_zero_or_one a with h3 | h3
    · have e : (a, b) ∈ innerEE N S Q' := pkR_b_inEE hm h3 h2
        (pkR_b_mem_even (by omega) (fun h => pkR_b_not_odd ha (hsub h))) (pkR_b_mem_even (by omega) hb')
      rw [← hee] at e
      exact pkR_b_not_odd (mem_filter.1 e).2.2 hb
    · have e := pkR_b_rect hb h2 ha h3
      rw [ea', eb'] at e
      exact disjoint_left.1 hmQ e hm

/-- (H3a) for a class member: a chord of `hitClass N S t` is a clean mixed chord (`poleChords ⊆ cleanChords`). -/
theorem pkR_b_H3a {N : ℕ} {S : Finset (ℕ × ℕ)} {t Q : ℕ × ℕ} (hQ : Q ∈ hitClass N S t) :
    Q ∈ oddDiagonals N ∧ Disjoint (minRect N Q) (missing N S) := by
  have h1 := (mem_filter.1 hQ).1
  have h2 := (mem_filter.1 h1).1
  exact mem_filter.1 h2

-- R12-P7b-pkgRes-b3 (claude-opus-5-5, 2026-09-28): [OmegaTiles] (positional core + chord form + member part) and the
-- rotation bridge. Appended; everything above is byte-identical to md5 d8a09369. Uses `lemma65` (frozen, pkgLin) and
-- the sub-wave a helpers `pkR_subTile`, `pkR_lam`, `pkR_minrect`, `pkR_mesh_comm`, `pkR_planar_*` of the snapshot.

/-! ### [OmegaTiles] (PREFORM-Res §5.3, X-level half of R3; R12-P7b-pkgRes-b3, claude-opus-5-5)

For nested mixed chords `Q ≻ Q′`, the region `Ω(Q, Q′)` is the cyclic vertex list
`f_{Q,Q′} = [a, a+1, …, c] ++ [c′+1, …, a′+1]` (read with `vtx N`). Here it is written in *positions* relative to the first
leg `a` of `A_Q` (so heads that wrap around `N` need no rotation): `A_Q` = positions `[0, L)`, `A_{Q′}` = positions
`[p, p + L′)`, `μ = A_Q ∖ A_{Q′}` = positions `[0, p) ∪ [p + L′, L)`, `B_Q` = positions `[L, N)`; the leg at position `i`
is `vtx N (a + i)`. Child dual point `k` is the parent dual point before position `pkR_b_olo p L' k`; child leg `p + 1`
is `A_{Q′}` (`r′`), child leg `m = L − L′ + 2` is `B_Q` (`s′`), all other child legs are single parent legs of `μ`.
If every tile of `T(Q, Q′)` vanishes, the child point lies on `Λ` of the standard polygon `(m, p/2)`, `x′ = X_Q` and
`X_Q = X_{Q′}` (the last from the child's Lemma 6.5 relation). -/

/-- An inner `vtx` is absorbed. -/
theorem pkR_b_vtx_add {N : ℕ} (hN : 1 ≤ N) (u e : ℕ) : vtx N (vtx N u + e) = vtx N (u + e) := by
  induction e with
  | zero => rw [add_zero, add_zero]; exact pkR_vtx_vtx hN u
  | succ e ih =>
    rw [← add_assoc, ← add_assoc, vtx_succ hN (vtx N u + e), vtx_succ hN (u + e), ih]

/-- The extended mesh reads its labels through `vtx`. -/
theorem pkR_b_mesh_congr {K : Type*} [Field K] {N : ℕ} (hN : 1 ≤ N) (X : ℕ × ℕ → K) {x y x' y' : ℕ}
    (hx : vtx N x = vtx N x') (hy : vtx N y = vtx N y') : mesh N X x y = mesh N X x' y' := by
  have hx1 : vtx N (x + 1) = vtx N (x' + 1) := by rw [vtx_succ hN x, hx, ← vtx_succ hN x']
  have hy1 : vtx N (y + 1) = vtx N (y' + 1) := by rw [vtx_succ hN y, hy, ← vtx_succ hN y']
  rw [pkR_mesh_def N X x y, pkR_mesh_def N X x' y', pkR_planar_congr hN X hx hy, pkR_planar_congr hN X hx1 hy1,
    pkR_planar_congr hN X hx hy1, pkR_planar_congr hN X hx1 hy]

theorem pkR_b_mod2 {N z : ℕ} (h : z < 2 * N) : (z < N ∧ z % N = z) ∨ (N ≤ z ∧ z % N = z - N) := by
  by_cases hz : z < N
  · exact Or.inl ⟨hz, Nat.mod_eq_of_lt hz⟩
  · refine Or.inr ⟨by omega, ?_⟩
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- A block of a sub-polygon whose end dual points sit at positions `lo < hi` from leg `a` consists of the legs at the
positions `[lo, hi)`. -/
theorem pkR_b_blk_pos {N m a lo hi k x : ℕ} {f : ℕ → ℕ} (ha : 1 ≤ a ∧ a ≤ N) (hlo : lo < hi) (hhi : hi ≤ N)
    (hlh : hi - lo < N) (e1 : f (vtx m k) = vtx N (a + lo)) (e2 : f (vtx m (k + 1)) = vtx N (a + hi))
    (hx : x ∈ pkR_blk N m f k) : ∃ i, lo ≤ i ∧ i < hi ∧ vtx N x = vtx N (a + i) := by
  have eb : pkR_blk N m f k =
      Icc (f (vtx m k)) (f (vtx m k) + (f (vtx m (k + 1)) + N - f (vtx m k)) % N - 1) := rfl
  rw [eb, e1, e2, mem_Icc] at hx
  have vb1 := vtx_bounds N (a + lo) (by omega)
  have vb2 := vtx_bounds N (a + hi) (by omega)
  have b1 := pkR_b_vtx2 (N := N) (u := a + lo) (by omega) (by omega)
  have b2 := pkR_b_vtx2 (N := N) (u := a + hi) (by omega) (by omega)
  have m2 := pkR_b_mod2 (N := N) (z := vtx N (a + hi) + N - vtx N (a + lo)) (by omega)
  refine ⟨lo + (x - vtx N (a + lo)), by omega, by omega, ?_⟩
  have b3 := pkR_b_vtx2 (N := N) (u := x) (by omega) (by omega)
  have b4 := pkR_b_vtx2 (N := N) (u := a + (lo + (x - vtx N (a + lo)))) (by omega) (by omega)
  omega

/-- Position (from leg `a`) of the parent dual point before child dual point `k` of `Ω(Q, Q′)`. -/
def pkR_b_olo (p L' k : ℕ) : ℕ := if k ≤ p + 1 then k - 1 else k - 2 + L'

/-- Position of the parent dual point after child leg `k` (`N` = back to `a` for the last leg). -/
def pkR_b_ohi (N L L' p k : ℕ) : ℕ := if k = L - L' + 2 then N else pkR_b_olo p L' (k + 1)

/-- The region list `f_{Q,Q′}` (PREFORM-Res §5.3) in positions from leg `a`. -/
def pkR_b_omL (N a p L' : ℕ) (k : ℕ) : ℕ := vtx N (a + pkR_b_olo p L' k)

theorem pkR_b_olo_eq (p L' k : ℕ) :
    (k ≤ p + 1 ∧ pkR_b_olo p L' k = k - 1) ∨ (p + 1 < k ∧ pkR_b_olo p L' k = k - 2 + L') := by
  have e : pkR_b_olo p L' k = if k ≤ p + 1 then k - 1 else k - 2 + L' := rfl
  rw [e]
  split_ifs with h <;> omega

theorem pkR_b_ohi_eq (N L L' p k : ℕ) :
    (k = L - L' + 2 ∧ pkR_b_ohi N L L' p k = N) ∨
      (k ≠ L - L' + 2 ∧ pkR_b_ohi N L L' p k = pkR_b_olo p L' (k + 1)) := by
  have e : pkR_b_ohi N L L' p k = if k = L - L' + 2 then N else pkR_b_olo p L' (k + 1) := rfl
  rw [e]
  split_ifs with h
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr ⟨h, rfl⟩

theorem pkR_b_omL_def (N a p L' k : ℕ) : pkR_b_omL N a p L' k = vtx N (a + pkR_b_olo p L' k) := rfl

/-- The dual point after child leg `k`. -/
theorem pkR_b_om_next {N a p L L' k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ L - L' + 2) :
    pkR_b_omL N a p L' (vtx (L - L' + 2) (k + 1)) = vtx N (a + pkR_b_ohi N L L' p k) := by
  rcases pkR_b_ohi_eq N L L' p k with h | h
  · rw [h.2, h.1, show L - L' + 2 + 1 = 1 + (L - L' + 2) by omega, vtx_add_n (L - L' + 2) 1,
      vtx_of_mem le_rfl (by omega), pkR_b_omL_def, vtx_add_n N a]
    have o := pkR_b_olo_eq p L' 1
    rw [show pkR_b_olo p L' 1 = 0 by omega, add_zero]
  · rw [h.2, vtx_of_mem (by omega) (by omega), pkR_b_omL_def]

theorem pkR_b_om_cyc {N a p L L' : ℕ} (hN : 1 ≤ N) (ha : 1 ≤ a ∧ a ≤ N) (hL' : 1 ≤ L') (hpL : p + L' ≤ L)
    (hLL : L' + 2 ≤ L) (hLN : L < N) : pkR_CycList N (L - L' + 2) (pkR_b_omL N a p L') := by
  intro k hk
  have hk' := mem_Icc.1 hk
  refine ⟨mem_Icc.2 (vtx_bounds N _ hN), ?_⟩
  rw [pkR_b_om_next hk'.1 hk'.2, pkR_b_omL_def]
  have o1 := pkR_b_olo_eq p L' k
  have o2 := pkR_b_olo_eq p L' (k + 1)
  have h2 := pkR_b_ohi_eq N L L' p k
  have b1 := pkR_b_vtx2 (N := N) (u := a + pkR_b_olo p L' k) (by omega) (by omega)
  have b2 := pkR_b_vtx2 (N := N) (u := a + pkR_b_ohi N L L' p k) (by omega) (by omega)
  omega

/-- The legs of child leg `k` of `Ω(Q, Q′)` are the parent legs at positions `[olo k, ohi k)`. -/
theorem pkR_b_om_blk {N a p L L' : ℕ} (ha : 1 ≤ a ∧ a ≤ N) (hL' : 1 ≤ L') (hpL : p + L' ≤ L)
    (hLL : L' + 2 ≤ L) (hLN : L < N) {k x : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ L - L' + 2)
    (hx : x ∈ pkR_blk N (L - L' + 2) (pkR_b_omL N a p L') k) :
    ∃ i, pkR_b_olo p L' k ≤ i ∧ i < pkR_b_ohi N L L' p k ∧ vtx N x = vtx N (a + i) := by
  have o1 := pkR_b_olo_eq p L' k
  have o2 := pkR_b_olo_eq p L' (k + 1)
  have h2 := pkR_b_ohi_eq N L L' p k
  refine pkR_b_blk_pos ha (by omega) (by omega) (by omega) ?_ (pkR_b_om_next hk1 hk2) hx
  rw [vtx_of_mem hk1 hk2]
  rfl

/-- A single-leg child edge has zero planar variable. -/
theorem pkR_b_om_single {N a p L' j : ℕ} (hN : 1 ≤ N) (X : ℕ × ℕ → ℚ) (hj1 : 1 ≤ j) (hj3 : j ≠ p + 1) :
    planar N X (pkR_b_omL N a p L' j) (pkR_b_omL N a p L' (j + 1)) = 0 := by
  have o1 := pkR_b_olo_eq p L' j
  have o2 := pkR_b_olo_eq p L' (j + 1)
  rw [pkR_b_omL_def, pkR_b_omL_def, show a + pkR_b_olo p L' (j + 1) = a + pkR_b_olo p L' j + 1 by omega,
    ← pkR_planar_vtx hN X]
  exact pkR_planar_succ hN X _

theorem pkR_b_cstp_ne {m p k l : ℕ} (hp : p % 2 = 0) (h : (k, l) ≠ pkR_cstp m (p / 2)) :
    ¬ (k = 2 ∧ l = m ∧ p = 0) ∧ ¬ (k = p ∧ l = p + 2 ∧ 2 ≤ p) := by
  have e : pkR_cstp m (p / 2) = if p / 2 = 0 then (2, m) else (2 * (p / 2), 2 * (p / 2) + 2) := rfl
  constructor
  · rintro ⟨h1, h2, h3⟩
    apply h
    rw [e, if_pos (by omega)]
    exact Prod.ext h1 h2
  · rintro ⟨h1, h2, h3⟩
    apply h
    rw [e, if_neg (by omega)]
    exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)

theorem pkR_b_cstp_eq {m p : ℕ} (hp : p % 2 = 0) :
    (p = 0 ∧ pkR_cstp m (p / 2) = (2, m)) ∨ (2 ≤ p ∧ pkR_cstp m (p / 2) = (p, p + 2)) := by
  have e : pkR_cstp m (p / 2) = if p / 2 = 0 then (2, m) else (2 * (p / 2), 2 * (p / 2) + 2) := rfl
  rw [e]
  by_cases h : p = 0
  · exact Or.inl ⟨h, by rw [if_pos (by omega)]⟩
  · refine Or.inr ⟨by omega, ?_⟩
    rw [if_neg (by omega)]
    exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)

theorem pkR_b_om_single' {N a p L' j j' : ℕ} (hN : 1 ≤ N) (X : ℕ × ℕ → ℚ) (hj' : j' = j + 1) (hj1 : 1 ≤ j)
    (hj3 : j ≠ p + 1) : planar N X (pkR_b_omL N a p L' j) (pkR_b_omL N a p L' j') = 0 := by
  subst hj'
  exact pkR_b_om_single hN X hj1 hj3

theorem pkR_b_bsum_zero {N m : ℕ} {f : ℕ → ℕ} (X : ℕ × ℕ → ℚ) {k l : ℕ}
    (h : ∀ x ∈ pkR_blk N m f k, ∀ y ∈ pkR_blk N m f l, mesh N X x y = 0) :
    Finset.sum (pkR_blk N m f k) (fun x => Finset.sum (pkR_blk N m f l) (fun y => mesh N X x y)) = 0 :=
  sum_eq_zero fun x hx => sum_eq_zero fun y hy => h x hx y hy

/-- `T(Q, Q′)` in positions from leg `a` (`μ` = positions `[0, p) ∪ [p + L′, L)`): same-parity pairs of `μ`; (odd leg of
`μ` = even position) × `A_{Q′}`; (even leg of `μ` = odd position) × `B_Q`. -/
def pkR_b_OT (N a p L L' : ℕ) (X : ℕ × ℕ → ℚ) : Prop :=
  (∀ i j, (i < p ∨ (p + L' ≤ i ∧ i < L)) → (j < p ∨ (p + L' ≤ j ∧ j < L)) → i % 2 = j % 2 → i ≠ j →
      mesh N X (vtx N (a + i)) (vtx N (a + j)) = 0) ∧
  (∀ i j, (i < p ∨ (p + L' ≤ i ∧ i < L)) → i % 2 = 0 → p ≤ j → j < p + L' →
      mesh N X (vtx N (a + i)) (vtx N (a + j)) = 0) ∧
  (∀ i j, (i < p ∨ (p + L' ≤ i ∧ i < L)) → i % 2 = 1 → L ≤ j → j < N →
      mesh N X (vtx N (a + i)) (vtx N (a + j)) = 0)

theorem pkR_b_OT_iff (N a p L L' : ℕ) (X : ℕ × ℕ → ℚ) : pkR_b_OT N a p L L' X ↔
    ((∀ i j, (i < p ∨ (p + L' ≤ i ∧ i < L)) → (j < p ∨ (p + L' ≤ j ∧ j < L)) → i % 2 = j % 2 → i ≠ j →
      mesh N X (vtx N (a + i)) (vtx N (a + j)) = 0) ∧
    (∀ i j, (i < p ∨ (p + L' ≤ i ∧ i < L)) → i % 2 = 0 → p ≤ j → j < p + L' →
      mesh N X (vtx N (a + i)) (vtx N (a + j)) = 0) ∧
    (∀ i j, (i < p ∨ (p + L' ≤ i ∧ i < L)) → i % 2 = 1 → L ≤ j → j < N →
      mesh N X (vtx N (a + i)) (vtx N (a + j)) = 0)) := Iff.rfl

theorem pkR_b_om_posS {N a p L L' : ℕ} (hN : 1 ≤ N) (ha : 1 ≤ a ∧ a ≤ N) (hL' : 1 ≤ L') (hpL : p + L' ≤ L)
    (hLL : L' + 2 ≤ L) (hLN : L < N) {k x : ℕ} (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ L - L' + 2) (hkp : k ≠ p + 1)
    (hx : x ∈ pkR_blk N (L - L' + 2) (pkR_b_omL N a p L') k) :
    ∃ i, ((k ≤ p ∧ i = k - 1) ∨ (p + 2 ≤ k ∧ i = k - 2 + L')) ∧ vtx N x = vtx N (vtx N (a + i)) := by
  obtain ⟨i, h1, h2, h3⟩ := pkR_b_om_blk ha hL' hpL hLL hLN hk1 (by omega) hx
  have o1 := pkR_b_olo_eq p L' k
  have o2 := pkR_b_olo_eq p L' (k + 1)
  have o3 := pkR_b_ohi_eq N L L' p k
  exact ⟨i, by omega, h3.trans (pkR_vtx_vtx hN _).symm⟩

theorem pkR_b_om_posR {N a p L L' : ℕ} (hN : 1 ≤ N) (ha : 1 ≤ a ∧ a ≤ N) (hL' : 1 ≤ L') (hpL : p + L' ≤ L)
    (hLL : L' + 2 ≤ L) (hLN : L < N) {x : ℕ} (hx : x ∈ pkR_blk N (L - L' + 2) (pkR_b_omL N a p L') (p + 1)) :
    ∃ i, p ≤ i ∧ i < p + L' ∧ vtx N x = vtx N (vtx N (a + i)) := by
  obtain ⟨i, h1, h2, h3⟩ := pkR_b_om_blk ha hL' hpL hLL hLN (by omega) (by omega) hx
  have o1 := pkR_b_olo_eq p L' (p + 1)
  have o2 := pkR_b_olo_eq p L' (p + 1 + 1)
  have o3 := pkR_b_ohi_eq N L L' p (p + 1)
  exact ⟨i, by omega, by omega, h3.trans (pkR_vtx_vtx hN _).symm⟩

theorem pkR_b_om_posM {N a p L L' : ℕ} (hN : 1 ≤ N) (ha : 1 ≤ a ∧ a ≤ N) (hL' : 1 ≤ L') (hpL : p + L' ≤ L)
    (hLL : L' + 2 ≤ L) (hLN : L < N) {x : ℕ}
    (hx : x ∈ pkR_blk N (L - L' + 2) (pkR_b_omL N a p L') (L - L' + 2)) :
    ∃ i, L ≤ i ∧ i < N ∧ vtx N x = vtx N (vtx N (a + i)) := by
  obtain ⟨i, h1, h2, h3⟩ := pkR_b_om_blk ha hL' hpL hLL hLN (by omega) le_rfl hx
  have o1 := pkR_b_olo_eq p L' (L - L' + 2)
  have o3 := pkR_b_ohi_eq N L L' p (L - L' + 2)
  exact ⟨i, by omega, by omega, h3.trans (pkR_vtx_vtx hN _).symm⟩

/-- The block sum of every same-parity pair of child legs of `Ω(Q, Q′)` vanishes on `T(Q, Q′)`. -/
theorem pkR_b_omBlk {N a p L L' : ℕ} (hN : 1 ≤ N) (ha : 1 ≤ a ∧ a ≤ N) (hp : p % 2 = 0) (hL' : L' % 2 = 1)
    (hL : L % 2 = 1) (hpL : p + L' ≤ L) (hLL : L' + 2 ≤ L) (hLN : L < N) {X : ℕ × ℕ → ℚ}
    (hT : pkR_b_OT N a p L L' X) {k l : ℕ} (hk : 1 ≤ k) (hkl : k + 2 ≤ l) (hl : l ≤ L - L' + 2)
    (hpar : k % 2 = l % 2) :
    Finset.sum (pkR_blk N (L - L' + 2) (pkR_b_omL N a p L') k) (fun x =>
      Finset.sum (pkR_blk N (L - L' + 2) (pkR_b_omL N a p L') l) (fun y => mesh N X x y)) = 0 := by
  obtain ⟨HT1, HT2, HT3⟩ := (pkR_b_OT_iff N a p L L' X).1 hT
  have hL1 : 1 ≤ L' := by omega
  refine pkR_b_bsum_zero X fun x hx y hy => ?_
  rcases (show k = p + 1 ∨ l = p + 1 ∨ l = L - L' + 2 ∨ (k ≠ p + 1 ∧ l ≠ p + 1 ∧ l + 1 ≤ L - L' + 2) by omega)
    with h | h | h | h
  · subst h
    obtain ⟨i, hi1, hi2, hi3⟩ := pkR_b_om_posR hN ha hL1 hpL hLL hLN hx
    obtain ⟨j, hj, hj3⟩ := pkR_b_om_posS hN ha hL1 hpL hLL hLN (k := l) (by omega) (by omega) (by omega) hy
    rw [pkR_b_mesh_congr hN X hi3 hj3, pkR_mesh_comm]
    exact HT2 j i (by omega) (by omega) hi1 hi2
  · subst h
    obtain ⟨i, hi, hi3⟩ := pkR_b_om_posS hN ha hL1 hpL hLL hLN (k := k) hk (by omega) (by omega) hx
    obtain ⟨j, hj1, hj2, hj3⟩ := pkR_b_om_posR hN ha hL1 hpL hLL hLN hy
    rw [pkR_b_mesh_congr hN X hi3 hj3]
    exact HT2 i j (by omega) (by omega) hj1 hj2
  · subst h
    obtain ⟨i, hi, hi3⟩ := pkR_b_om_posS hN ha hL1 hpL hLL hLN (k := k) hk (by omega) (by omega) hx
    obtain ⟨j, hj1, hj2, hj3⟩ := pkR_b_om_posM hN ha hL1 hpL hLL hLN hy
    rw [pkR_b_mesh_congr hN X hi3 hj3]
    exact HT3 i j (by omega) (by omega) hj1 hj2
  · obtain ⟨i, hi, hi3⟩ := pkR_b_om_posS hN ha hL1 hpL hLL hLN (k := k) hk (by omega) h.1 hx
    obtain ⟨j, hj, hj3⟩ := pkR_b_om_posS hN ha hL1 hpL hLL hLN (k := l) (by omega) h.2.2 h.2.1 hy
    rw [pkR_b_mesh_congr hN X hi3 hj3]
    exact HT1 i j (by omega) (by omega) (by omega) (by omega)

set_option maxHeartbeats 1000000 in
/-- Every same-parity child tile of `Ω(Q, Q′)` other than `c⋆ = (1, m − 1)` and `c⋆′` vanishes on `T(Q, Q′)`. -/
theorem pkR_b_omZero {N a p L L' : ℕ} (hN : 1 ≤ N) (ha : 1 ≤ a ∧ a ≤ N) (hp : p % 2 = 0) (hL' : L' % 2 = 1)
    (hL : L % 2 = 1) (hpL : p + L' ≤ L) (hLL : L' + 2 ≤ L) (hLN : L < N) {X : ℕ × ℕ → ℚ}
    (hT : pkR_b_OT N a p L L' X) {k l : ℕ} (hk : 1 ≤ k) (hkl : k + 2 ≤ l) (hl : l ≤ L - L' + 2)
    (hpar : k % 2 = l % 2) (hs : (k, l) ≠ (1, L - L' + 2 - 1)) (hc : (k, l) ≠ pkR_cstp (L - L' + 2) (p / 2)) :
    mesh (L - L' + 2) (pkR_subX N (pkR_b_omL N a p L') X) k l = 0 := by
  obtain ⟨HT1, HT2, HT3⟩ := (pkR_b_OT_iff N a p L L' X).1 hT
  have hs' : ¬ (k = 1 ∧ l + 1 = L - L' + 2) := by
    rintro ⟨h1, h2⟩
    exact hs (Prod.ext h1 (by dsimp only; omega))
  obtain ⟨hc1, hc2⟩ := pkR_b_cstp_ne hp hc
  have hL1 : 1 ≤ L' := by omega
  rw [pkR_subTile hN (by omega) (pkR_b_om_cyc hN ha hL1 hpL hLL hLN) X (mem_Icc.2 ⟨hk, by omega⟩)
    (mem_Icc.2 ⟨by omega, hl⟩) (mem_diagonals.2 (by dsimp only; omega))]
  have vl : vtx (L - L' + 2) l = l := vtx_of_mem (by omega) hl
  have vk2 : vtx (L - L' + 2) (k + 2) = k + 2 := vtx_of_mem (by omega) (by omega)
  have vk1 : vtx (L - L' + 2) (k + 1) = k + 1 := vtx_of_mem (by omega) (by omega)
  have vk : vtx (L - L' + 2) k = k := vtx_of_mem hk (by omega)
  rw [vl, vk2, vk1, vk]
  have c1 : (if l = k + 2 then planar N X (pkR_b_omL N a p L' (k + 1)) (pkR_b_omL N a p L' (k + 2)) else 0) = 0 := by
    split_ifs with h
    · exact pkR_b_om_single' hN X rfl (by omega) (by omega)
    · rfl
  have c2 : (if k = vtx (L - L' + 2) (l + 2) then planar N X (pkR_b_omL N a p L' (vtx (L - L' + 2) (l + 1)))
      (pkR_b_omL N a p L' (vtx (L - L' + 2) (l + 2))) else 0) = 0 := by
    have v1 := pkR_b_vtx2 (N := L - L' + 2) (u := l + 1) (by omega) (by omega)
    have v2 := pkR_b_vtx2 (N := L - L' + 2) (u := l + 2) (by omega) (by omega)
    split_ifs with h
    · rw [show vtx (L - L' + 2) (l + 1) = 1 by omega, show vtx (L - L' + 2) (l + 2) = 1 + 1 by omega]
      exact pkR_b_om_single' hN X rfl le_rfl (by omega)
    · rfl
  rw [c1, c2, add_zero, add_zero]
  exact pkR_b_omBlk hN ha hp hL' hL hpL hLL hLN hT hk hkl hl hpar

set_option maxHeartbeats 1000000 in
/-- `c⋆` of `Ω(Q, Q′)` (child tile `(1, m − 1)`, straddling `s′ = B_Q`) is `X_Q` on `T(Q, Q′)`. -/
theorem pkR_b_omStar {N a p L L' : ℕ} (hN : 1 ≤ N) (ha : 1 ≤ a ∧ a ≤ N) (hp : p % 2 = 0) (hL' : L' % 2 = 1)
    (hL : L % 2 = 1) (hpL : p + L' ≤ L) (hLL : L' + 2 ≤ L) (hLN : L < N) {X : ℕ × ℕ → ℚ}
    (hT : pkR_b_OT N a p L L' X) :
    mesh (L - L' + 2) (pkR_subX N (pkR_b_omL N a p L') X) 1 (L - L' + 2 - 1) = planar N X a (a + L) := by
  obtain ⟨HT1, HT2, HT3⟩ := (pkR_b_OT_iff N a p L L' X).1 hT
  have hL1 : 1 ≤ L' := by omega
  rw [pkR_subTile hN (by omega) (pkR_b_om_cyc hN ha hL1 hpL hLL hLN) X (mem_Icc.2 ⟨le_rfl, by omega⟩)
    (mem_Icc.2 ⟨by omega, by omega⟩) (mem_diagonals.2 (by dsimp only; omega))]
  rw [show vtx (L - L' + 2) (L - L' + 2 - 1) = L - L' + 2 - 1 from vtx_of_mem (by omega) (by omega),
    show vtx (L - L' + 2) (1 + 2) = 1 + 2 from vtx_of_mem (by omega) (by omega),
    show vtx (L - L' + 2) (1 + 1) = 1 + 1 from vtx_of_mem (by omega) (by omega),
    show vtx (L - L' + 2) 1 = 1 from vtx_of_mem le_rfl (by omega),
    show vtx (L - L' + 2) (L - L' + 2 - 1 + 1) = L - L' + 2 from vtx_of_mem (by omega) (by omega),
    show vtx (L - L' + 2) (L - L' + 2 - 1 + 2) = 1 by
      have v := pkR_b_vtx2 (N := L - L' + 2) (u := L - L' + 2 - 1 + 2) (by omega) (by omega)
      omega]
  have e0 : Finset.sum (pkR_blk N (L - L' + 2) (pkR_b_omL N a p L') 1) (fun x =>
      Finset.sum (pkR_blk N (L - L' + 2) (pkR_b_omL N a p L') (L - L' + 2 - 1)) (fun y => mesh N X x y)) = 0 := by
    refine pkR_b_bsum_zero X fun x hx y hy => ?_
    obtain ⟨i, hi1, hi2, hi3⟩ := pkR_b_om_blk ha hL1 hpL hLL hLN le_rfl (by omega) hx
    obtain ⟨j, hj1, hj2, hj3⟩ := pkR_b_om_blk ha hL1 hpL hLL hLN (by omega) (by omega) hy
    rw [pkR_b_mesh_congr hN X (hi3.trans (pkR_vtx_vtx hN _).symm) (hj3.trans (pkR_vtx_vtx hN _).symm)]
    have o1 := pkR_b_olo_eq p L' 1
    have o2 := pkR_b_olo_eq p L' (1 + 1)
    have o3 := pkR_b_ohi_eq N L L' p 1
    have o4 := pkR_b_olo_eq p L' (L - L' + 2 - 1)
    have o5 := pkR_b_olo_eq p L' (L - L' + 2 - 1 + 1)
    have o6 := pkR_b_ohi_eq N L L' p (L - L' + 2 - 1)
    rcases (show p = 0 ∨ (2 ≤ p ∧ L - L' + 2 - 1 = p + 1) ∨ (2 ≤ p ∧ L - L' + 2 - 1 ≠ p + 1) by omega)
      with h | h | h
    · rw [pkR_mesh_comm]
      exact HT2 j i (by omega) (by omega) (by omega) (by omega)
    · exact HT2 i j (by omega) (by omega) (by omega) (by omega)
    · exact HT1 i j (by omega) (by omega) (by omega) (by omega)
  have e1 : (if L - L' + 2 - 1 = 1 + 2 then planar N X (pkR_b_omL N a p L' (1 + 1)) (pkR_b_omL N a p L' (1 + 2))
      else 0) = 0 := by
    split_ifs
    · exact pkR_b_om_single' hN X rfl (by omega) (by omega)
    · rfl
  rw [e0, e1, if_pos rfl, zero_add, zero_add, pkR_b_omL_def, pkR_b_omL_def,
    show pkR_b_olo p L' (L - L' + 2) = L by have o := pkR_b_olo_eq p L' (L - L' + 2); omega,
    show pkR_b_olo p L' 1 = 0 by have o := pkR_b_olo_eq p L' 1; omega, add_zero,
    pkR_planar_comm N X (vtx N (a + L)) (vtx N a), ← pkR_planar_vtx hN X a (a + L)]

set_option maxHeartbeats 1000000 in
/-- `c⋆′` of `Ω(Q, Q′)` for `p = 0` (child tile `(2, m)`) is `X_{Q′}` on `T(Q, Q′)`. -/
theorem pkR_b_omStarP0 {N a L L' : ℕ} (hN : 1 ≤ N) (ha : 1 ≤ a ∧ a ≤ N) (hL' : L' % 2 = 1)
    (hL : L % 2 = 1) (hLL : L' + 2 ≤ L) (hLN : L < N) {X : ℕ × ℕ → ℚ}
    (hT : pkR_b_OT N a 0 L L' X) :
    mesh (L - L' + 2) (pkR_subX N (pkR_b_omL N a 0 L') X) 2 (L - L' + 2) = planar N X a (a + L') := by
  obtain ⟨HT1, HT2, HT3⟩ := (pkR_b_OT_iff N a 0 L L' X).1 hT
  have hL1 : 1 ≤ L' := by omega
  have hpL : 0 + L' ≤ L := by omega
  rw [pkR_subTile hN (by omega) (pkR_b_om_cyc hN ha hL1 hpL hLL hLN) X (mem_Icc.2 ⟨by omega, by omega⟩)
    (mem_Icc.2 ⟨by omega, le_rfl⟩) (mem_diagonals.2 (by dsimp only; omega))]
  rw [show vtx (L - L' + 2) (L - L' + 2) = L - L' + 2 from vtx_of_mem (by omega) le_rfl,
    show vtx (L - L' + 2) (2 + 2) = 2 + 2 from vtx_of_mem (by omega) (by omega),
    show vtx (L - L' + 2) (2 + 1) = 2 + 1 from vtx_of_mem (by omega) (by omega),
    show vtx (L - L' + 2) 2 = 2 from vtx_of_mem (by omega) (by omega),
    show vtx (L - L' + 2) (L - L' + 2 + 1) = 1 by
      have v := pkR_b_vtx2 (N := L - L' + 2) (u := L - L' + 2 + 1) (by omega) (by omega)
      omega,
    show vtx (L - L' + 2) (L - L' + 2 + 2) = 2 by
      have v := pkR_b_vtx2 (N := L - L' + 2) (u := L - L' + 2 + 2) (by omega) (by omega)
      omega]
  have e0 : Finset.sum (pkR_blk N (L - L' + 2) (pkR_b_omL N a 0 L') 2) (fun x =>
      Finset.sum (pkR_blk N (L - L' + 2) (pkR_b_omL N a 0 L') (L - L' + 2)) (fun y => mesh N X x y)) = 0 := by
    refine pkR_b_bsum_zero X fun x hx y hy => ?_
    obtain ⟨i, hi1, hi2, hi3⟩ := pkR_b_om_blk ha hL1 hpL hLL hLN (by omega) (by omega) hx
    obtain ⟨j, hj1, hj2, hj3⟩ := pkR_b_om_blk ha hL1 hpL hLL hLN (by omega) le_rfl hy
    rw [pkR_b_mesh_congr hN X (hi3.trans (pkR_vtx_vtx hN _).symm) (hj3.trans (pkR_vtx_vtx hN _).symm)]
    have o1 := pkR_b_olo_eq 0 L' 2
    have o2 := pkR_b_olo_eq 0 L' (2 + 1)
    have o3 := pkR_b_ohi_eq N L L' 0 2
    have o4 := pkR_b_olo_eq 0 L' (L - L' + 2)
    have o6 := pkR_b_ohi_eq N L L' 0 (L - L' + 2)
    exact HT3 i j (by omega) (by omega) (by omega) (by omega)
  have e1 : (if L - L' + 2 = 2 + 2 then planar N X (pkR_b_omL N a 0 L' (2 + 1)) (pkR_b_omL N a 0 L' (2 + 2))
      else 0) = 0 := by
    split_ifs
    · exact pkR_b_om_single' hN X rfl (by omega) (by omega)
    · rfl
  rw [e0, e1, if_pos rfl, zero_add, zero_add, pkR_b_omL_def, pkR_b_omL_def,
    show pkR_b_olo 0 L' 2 = L' by have o := pkR_b_olo_eq 0 L' 2; omega,
    show pkR_b_olo 0 L' 1 = 0 by have o := pkR_b_olo_eq 0 L' 1; omega, add_zero,
    ← pkR_planar_vtx hN X a (a + L')]

set_option maxHeartbeats 1000000 in
/-- `c⋆′` of `Ω(Q, Q′)` for `p ≥ 2` (child tile `(p, p + 2)`, straddling `r′ = A_{Q′}`) is `X_{Q′}` on `T(Q, Q′)`. -/
theorem pkR_b_omStarP {N a p L L' : ℕ} (hN : 1 ≤ N) (ha : 1 ≤ a ∧ a ≤ N) (hp : p % 2 = 0) (hp2 : 2 ≤ p)
    (hL' : L' % 2 = 1) (hL : L % 2 = 1) (hpL : p + L' ≤ L) (hLL : L' + 2 ≤ L) (hLN : L < N)
    {X : ℕ × ℕ → ℚ} (hT : pkR_b_OT N a p L L' X) :
    mesh (L - L' + 2) (pkR_subX N (pkR_b_omL N a p L') X) p (p + 2) = planar N X (a + p) (a + p + L') := by
  obtain ⟨HT1, HT2, HT3⟩ := (pkR_b_OT_iff N a p L L' X).1 hT
  have hL1 : 1 ≤ L' := by omega
  rw [pkR_subTile hN (by omega) (pkR_b_om_cyc hN ha hL1 hpL hLL hLN) X (mem_Icc.2 ⟨by omega, by omega⟩)
    (mem_Icc.2 ⟨by omega, by omega⟩) (mem_diagonals.2 (by dsimp only; omega))]
  rw [show vtx (L - L' + 2) (p + 2) = p + 2 from vtx_of_mem (by omega) (by omega),
    show vtx (L - L' + 2) (p + 1) = p + 1 from vtx_of_mem (by omega) (by omega),
    show vtx (L - L' + 2) p = p from vtx_of_mem (by omega) (by omega)]
  have e0 : Finset.sum (pkR_blk N (L - L' + 2) (pkR_b_omL N a p L') p) (fun x =>
      Finset.sum (pkR_blk N (L - L' + 2) (pkR_b_omL N a p L') (p + 2)) (fun y => mesh N X x y)) = 0 := by
    refine pkR_b_bsum_zero X fun x hx y hy => ?_
    obtain ⟨i, hi1, hi2, hi3⟩ := pkR_b_om_blk ha hL1 hpL hLL hLN (by omega) (by omega) hx
    obtain ⟨j, hj1, hj2, hj3⟩ := pkR_b_om_blk ha hL1 hpL hLL hLN (by omega) (by omega) hy
    rw [pkR_b_mesh_congr hN X (hi3.trans (pkR_vtx_vtx hN _).symm) (hj3.trans (pkR_vtx_vtx hN _).symm)]
    have o1 := pkR_b_olo_eq p L' p
    have o2 := pkR_b_olo_eq p L' (p + 1)
    have o3 := pkR_b_ohi_eq N L L' p p
    have o4 := pkR_b_olo_eq p L' (p + 2)
    have o5 := pkR_b_olo_eq p L' (p + 2 + 1)
    have o6 := pkR_b_ohi_eq N L L' p (p + 2)
    rcases (show p + 2 = L - L' + 2 ∨ p + 2 ≠ L - L' + 2 by omega) with h | h
    · exact HT3 i j (by omega) (by omega) (by omega) (by omega)
    · exact HT1 i j (by omega) (by omega) (by omega) (by omega)
  have e2 : (if p = vtx (L - L' + 2) (p + 2 + 2) then planar N X (pkR_b_omL N a p L' (vtx (L - L' + 2) (p + 2 + 1)))
      (pkR_b_omL N a p L' (vtx (L - L' + 2) (p + 2 + 2))) else 0) = 0 := by
    have v1 := pkR_b_vtx2 (N := L - L' + 2) (u := p + 2 + 1) (by omega) (by omega)
    have v2 := pkR_b_vtx2 (N := L - L' + 2) (u := p + 2 + 2) (by omega) (by omega)
    split_ifs with h
    · rw [show vtx (L - L' + 2) (p + 2 + 1) = 1 by omega, show vtx (L - L' + 2) (p + 2 + 2) = 1 + 1 by omega]
      exact pkR_b_om_single' hN X rfl le_rfl (by omega)
    · rfl
  rw [e0, e2, if_pos rfl, zero_add, add_zero, pkR_b_omL_def, pkR_b_omL_def,
    show pkR_b_olo p L' (p + 1) = p by have o := pkR_b_olo_eq p L' (p + 1); omega,
    show pkR_b_olo p L' (p + 2) = p + L' by have o := pkR_b_olo_eq p L' (p + 2); omega,
    ← add_assoc, ← pkR_planar_vtx hN X (a + p) (a + p + L')]

set_option maxHeartbeats 1000000 in
/-- **[OmegaTiles], linear core in positions** (PREFORM-Res §5.3; R2-Z188 C3): if every tile of `T(Q, Q′)` vanishes,
the region point `subX f_{Q,Q′} X` lies on `Λ` of the standard polygon `(m, p/2)` (`m = L − L′ + 2`), its `x′` is
`X_Q` (the parent planar variable at the dual points `a`, `a + L` of `Q`), and `X_Q = X_{Q′}` (dual points `a + p`,
`a + p + L′`). The last two come from [SubTile] (`c⋆ = X_Q`, `c⋆′ = X_{Q′}` on `T`) and the child's Lemma 6.5
relation. -/
theorem pkR_b_omCore {N a p L L' : ℕ} (hN : 1 ≤ N) (ha : 1 ≤ a ∧ a ≤ N) (hp : p % 2 = 0) (hL' : L' % 2 = 1)
    (hL : L % 2 = 1) (hpL : p + L' ≤ L) (hLL : L' + 2 ≤ L) (hLN : L < N) {X : ℕ × ℕ → ℚ}
    (hT : pkR_b_OT N a p L L' X) :
    pkR_lam (L - L' + 2) (p / 2) ∅ (pkR_subX N (pkR_b_omL N a p L') X) ∧
      mesh (L - L' + 2) (pkR_subX N (pkR_b_omL N a p L') X) 1 (L - L' + 2 - 1) = planar N X a (a + L) ∧
      planar N X a (a + L) = planar N X (a + p) (a + p + L') := by
  have hstar := pkR_b_omStar hN ha hp hL' hL hpL hLL hLN hT
  have hsp : mesh (L - L' + 2) (pkR_subX N (pkR_b_omL N a p L') X) (pkR_cstp (L - L' + 2) (p / 2)).1
      (pkR_cstp (L - L' + 2) (p / 2)).2 = planar N X (a + p) (a + p + L') := by
    rcases pkR_b_cstp_eq (m := L - L' + 2) hp with h | h
    · rw [h.2]
      obtain ⟨h0, -⟩ := h
      subst h0
      rw [add_zero]
      exact pkR_b_omStarP0 hN ha hL' hL hLL hLN hT
    · rw [h.2]
      exact pkR_b_omStarP hN ha hp h.1 hL' hL hpL hLL hLN hT
  have hee : Finset.sum ((diagonals (L - L' + 2)).filter (fun t => t.1 % 2 = 0 ∧ t.2 % 2 = 0))
      (fun t => mesh (L - L' + 2) (pkR_subX N (pkR_b_omL N a p L') X) t.1 t.2) =
      mesh (L - L' + 2) (pkR_subX N (pkR_b_omL N a p L') X) (pkR_cstp (L - L' + 2) (p / 2)).1
        (pkR_cstp (L - L' + 2) (p / 2)).2 := by
    refine sum_eq_single_of_mem _ ?_ ?_
    · rcases pkR_b_cstp_eq (m := L - L' + 2) hp with h | h <;> rw [h.2] <;>
        refine mem_filter.2 ⟨mem_diagonals.2 ?_, ?_⟩ <;> dsimp only <;> omega
    · rintro ⟨k, l⟩ ht hne
      have ht' := mem_filter.1 ht
      have ht'' := mem_diagonals.1 ht'.1
      dsimp only at ht' ht''
      exact pkR_b_omZero hN ha hp hL' hL hpL hLL hLN hT ht''.1 ht''.2.2.1 ht''.2.1 (by omega)
        (fun e => by have e1 := congrArg Prod.fst e; dsimp only at e1; omega) hne
  have hoo : Finset.sum ((diagonals (L - L' + 2)).filter (fun t => t.1 % 2 = 1 ∧ t.2 % 2 = 1))
      (fun t => mesh (L - L' + 2) (pkR_subX N (pkR_b_omL N a p L') X) t.1 t.2) =
      mesh (L - L' + 2) (pkR_subX N (pkR_b_omL N a p L') X) 1 (L - L' + 2 - 1) := by
    refine sum_eq_single_of_mem (1, L - L' + 2 - 1) ?_ ?_
    · refine mem_filter.2 ⟨mem_diagonals.2 ?_, ?_⟩ <;> dsimp only <;> omega
    · rintro ⟨k, l⟩ ht hne
      have ht' := mem_filter.1 ht
      have ht'' := mem_diagonals.1 ht'.1
      dsimp only at ht' ht''
      refine pkR_b_omZero hN ha hp hL' hL hpL hLL hLN hT ht''.1 ht''.2.2.1 ht''.2.1 (by omega) hne ?_
      intro e
      rcases pkR_b_cstp_eq (m := L - L' + 2) hp with h | h <;> rw [h.2] at e <;>
        have e1 := congrArg Prod.fst e <;> dsimp only at e1 <;> omega
  have h65 := lemma65 (N := L - L' + 2) (by omega) ⟨(L - L' + 2) / 2, by omega⟩
    (pkR_subX N (pkR_b_omL N a p L') X)
  rw [hee, hoo] at h65
  refine ⟨(pkR_lam_iff _ _ _ _).2 ⟨fun k hk l hl hkl hpar hs hc => ?_, h65.symm, fun Q hQ => by simp at hQ⟩,
    hstar, ?_⟩
  · exact pkR_b_omZero hN ha hp hL' hL hpL hLL hLN hT (mem_Icc.1 hk).1 hkl (mem_Icc.1 hl).2 hpar hs hc
  · rw [← hstar, ← hsp]
    exact h65.symm

/-! #### [OmegaTiles] for chords: the positions of `A_Q`, `A_{Q′}`, `B_Q` from the first leg `a = headStart Q` -/

/-- Head membership through the cyclic position from `headStart`. -/
theorem pkR_b_head_pos {N x : ℕ} {Q : ℕ × ℕ} (hQ : Q ∈ oddDiagonals N) (hx : 1 ≤ x ∧ x ≤ N) :
    x ∈ oddSide N Q ↔ cycPos N (headStart Q) x < headLen N Q := by
  have b := pkR_b_odd_iff.1 hQ
  have hH := pkR_b_head_data hQ
  have e : cycPos N (headStart Q) x = (x + N - headStart Q) % N := rfl
  rw [e]
  obtain ⟨q1, q2⟩ := Q
  dsimp only at b hH
  have m2 := pkR_b_mod2 (N := N) (z := x + N - headStart (q1, q2)) (by omega)
  rw [pkR_b_mem_head]
  constructor
  · intro h; omega
  · intro h; omega

/-- The start of a head is an odd leg in `1..N`, and the head has an odd number `≥ 3` of legs, the tail `≥ 3`. -/
theorem pkR_b_head_facts {N : ℕ} (hE : N % 2 = 0) {Q : ℕ × ℕ} (hQ : Q ∈ oddDiagonals N) :
    1 ≤ headStart Q ∧ headStart Q ≤ N ∧ headStart Q % 2 = 1 ∧ headLen N Q % 2 = 1 ∧ 3 ≤ headLen N Q ∧
      headLen N Q + 3 ≤ N := by
  have b := pkR_b_odd_iff.1 hQ
  have hH := pkR_b_head_data hQ
  obtain ⟨q1, q2⟩ := Q
  dsimp only at b hH
  omega

/-- The planar variable at the dual points `headStart Q`, `headStart Q + headLen N Q` is `X_Q`. -/
theorem pkR_b_planarQ {N : ℕ} {Q : ℕ × ℕ} (hQ : Q ∈ oddDiagonals N) (X : ℕ × ℕ → ℚ) :
    planar N X (headStart Q) (headStart Q + headLen N Q) = X Q := by
  have b := pkR_b_odd_iff.1 hQ
  have hH := pkR_b_head_data hQ
  obtain ⟨q1, q2⟩ := Q
  dsimp only at b hH
  rcases hH with h | h
  · rw [h.2.1, h.2.2, show q1 + (q2 - q1) = q2 by omega]
    exact planar_eq_X X b.1 b.2.2.1 b.2.1 b.2.2.2.1
  · rw [h.2.1, h.2.2, show q2 + (N - (q2 - q1)) = q1 + N by omega,
      pkR_planar_congr (by omega) X (rfl : vtx N q2 = vtx N q2) (vtx_add_n N q1), pkR_planar_comm]
    exact planar_eq_X X b.1 b.2.2.1 b.2.1 b.2.2.2.1

/-- `T(Q, Q′)` is symmetric. -/
theorem pkR_b_TP_symm {N : ℕ} {Q Q' : ℕ × ℕ} {a b : ℕ} (h : pkR_b_TP N Q Q' a b) : pkR_b_TP N Q Q' b a := by
  rcases (pkR_b_TP_iff N Q Q' a b).1 h with h | h | h | h | h
  · exact (pkR_b_TP_iff N Q Q' b a).2 (Or.inl ⟨h.1.symm, h.2.2.2.1, h.2.2.2.2, h.2.1, h.2.2.1⟩)
  · exact (pkR_b_TP_iff N Q Q' b a).2 (Or.inr (Or.inr (Or.inl h)))
  · exact (pkR_b_TP_iff N Q Q' b a).2 (Or.inr (Or.inl h))
  · exact (pkR_b_TP_iff N Q Q' b a).2 (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · exact (pkR_b_TP_iff N Q Q' b a).2 (Or.inr (Or.inr (Or.inr (Or.inl h))))

/-- A `T(Q, Q′)` tile in either order. -/
theorem pkR_b_TP_mesh {N : ℕ} {Q Q' : ℕ × ℕ} {X : ℕ × ℕ → ℚ}
    (hT : ∀ a b, (a, b) ∈ diagonals N → pkR_b_TP N Q Q' a b → mesh N X a b = 0) {x y : ℕ}
    (hd : (min x y, max x y) ∈ diagonals N) (h : pkR_b_TP N Q Q' x y) : mesh N X x y = 0 := by
  have hd' := mem_diagonals.1 hd
  dsimp only at hd'
  rcases (show x < y ∨ y < x by omega) with c | c
  · rw [min_eq_left (show x ≤ y by omega), max_eq_right (show x ≤ y by omega)] at hd
    exact hT x y hd h
  · rw [min_eq_right (show y ≤ x by omega), max_eq_left (show y ≤ x by omega)] at hd
    rw [pkR_mesh_comm]
    exact hT y x hd (pkR_b_TP_symm h)

/-- The data of a nested pair in positions from `a = headStart Q`: `A_{Q′}` = positions `[p, p + L′)` with
`p + L′ ≤ L`, `p` even, `L′ + 2 ≤ L`. -/
theorem pkR_b_nest_pos {N : ℕ} (hE : N % 2 = 0) {Q Q' : ℕ × ℕ} (hQ : Q ∈ oddDiagonals N)
    (hQ' : Q' ∈ oddDiagonals N) (hsub : oddSide N Q' ⊆ oddSide N Q) (hne : Q ≠ Q') :
    cycPos N (headStart Q) (headStart Q') % 2 = 0 ∧
      cycPos N (headStart Q) (headStart Q') + headLen N Q' ≤ headLen N Q ∧ headLen N Q' + 2 ≤ headLen N Q ∧
      ∀ i, i < N → (vtx N (headStart Q + i) ∈ oddSide N Q' ↔
        cycPos N (headStart Q) (headStart Q') ≤ i ∧ i < cycPos N (headStart Q) (headStart Q') + headLen N Q') := by
  have f1 := pkR_b_head_facts hE hQ
  have f2 := pkR_b_head_facts hE hQ'
  have ep : cycPos N (headStart Q) (headStart Q') = (headStart Q' + N - headStart Q) % N := rfl
  have m1 := pkR_b_mod2 (N := N) (z := headStart Q' + N - headStart Q) (by omega)
  -- membership of the leg at position `i` in `A_{Q′}`, through the position from `headStart Q′`
  have key : ∀ i, i < N → (vtx N (headStart Q + i) ∈ oddSide N Q' ↔
      (vtx N (headStart Q + i) + N - headStart Q') % N < headLen N Q') := by
    intro i hi
    have v := vtx_bounds N (headStart Q + i) (by omega)
    exact pkR_b_head_pos hQ' v
  have keyQ : ∀ i, i < N → (vtx N (headStart Q + i) ∈ oddSide N Q ↔ i < headLen N Q) := by
    intro i hi
    have v := vtx_bounds N (headStart Q + i) (by omega)
    rw [pkR_b_head_pos hQ v]
    have e : cycPos N (headStart Q) (vtx N (headStart Q + i)) = (vtx N (headStart Q + i) + N - headStart Q) % N := rfl
    rw [e]
    have b1 := pkR_b_vtx2 (N := N) (u := headStart Q + i) (by omega) (by omega)
    have m3 := pkR_b_mod2 (N := N) (z := vtx N (headStart Q + i) + N - headStart Q) (by omega)
    omega
  have gen : ∀ i, i < N → (vtx N (headStart Q + i) ∈ oddSide N Q' ↔
      ((i + N - cycPos N (headStart Q) (headStart Q')) % N < headLen N Q')) := by
    intro i hi
    rw [key i hi]
    have b1 := pkR_b_vtx2 (N := N) (u := headStart Q + i) (by omega) (by omega)
    have m3 := pkR_b_mod2 (N := N) (z := vtx N (headStart Q + i) + N - headStart Q') (by omega)
    have m4 := pkR_b_mod2 (N := N) (z := i + N - cycPos N (headStart Q) (headStart Q')) (by omega)
    omega
  -- `p < L`: the start of `A_{Q′}` lies in `A_Q`
  have hpL : cycPos N (headStart Q) (headStart Q') < headLen N Q := by
    have h0 := (gen (cycPos N (headStart Q) (headStart Q')) (by omega)).2
    have m5 := pkR_b_mod2 (N := N) (z := cycPos N (headStart Q) (headStart Q') + N -
      cycPos N (headStart Q) (headStart Q')) (by omega)
    have h1 := h0 (by omega)
    exact (keyQ _ (by omega)).1 (hsub h1)
  -- `p + L′ ≤ L`: otherwise the first leg of `B_Q` would lie in `A_{Q′}`
  have hpL' : cycPos N (headStart Q) (headStart Q') + headLen N Q' ≤ headLen N Q := by
    by_contra hc
    have m5 := pkR_b_mod2 (N := N) (z := headLen N Q + N - cycPos N (headStart Q) (headStart Q')) (by omega)
    have h1 := (gen (headLen N Q) (by omega)).2 (by omega)
    have h2 := (keyQ (headLen N Q) (by omega)).1 (hsub h1)
    omega
  have hpos : ∀ i, i < N → (vtx N (headStart Q + i) ∈ oddSide N Q' ↔
      cycPos N (headStart Q) (headStart Q') ≤ i ∧ i < cycPos N (headStart Q) (headStart Q') + headLen N Q') := by
    intro i hi
    rw [gen i hi]
    have m4 := pkR_b_mod2 (N := N) (z := i + N - cycPos N (headStart Q) (headStart Q')) (by omega)
    omega
  -- the start of `A_{Q′}` has odd parity, so `p` is even
  have hpar : cycPos N (headStart Q) (headStart Q') % 2 = 0 := by omega
  refine ⟨hpar, hpL', ?_, hpos⟩
  -- `L′ ≠ L`, else `p = 0` and the heads have the same start and length, so `Q = Q′`
  by_contra hc
  apply hne
  have hH := pkR_b_head_data hQ
  have hH' := pkR_b_head_data hQ'
  have b1 := pkR_b_odd_iff.1 hQ
  have b2 := pkR_b_odd_iff.1 hQ'
  obtain ⟨q1, q2⟩ := Q
  obtain ⟨r1, r2⟩ := Q'
  dsimp only at hH hH' b1 b2
  exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)

theorem pkR_b_posQ {N : ℕ} (hE : N % 2 = 0) {Q : ℕ × ℕ} (hQ : Q ∈ oddDiagonals N) {i : ℕ} (hi : i < N) :
    (vtx N (headStart Q + i) ∈ oddSide N Q ↔ i < headLen N Q) ∧
      (vtx N (headStart Q + i) ∈ evenSide N Q ↔ headLen N Q ≤ i) ∧
      ((headStart Q + i ≤ N ∧ vtx N (headStart Q + i) = headStart Q + i) ∨
        (N < headStart Q + i ∧ vtx N (headStart Q + i) = headStart Q + i - N)) := by
  have f1 := pkR_b_head_facts hE hQ
  have v := vtx_bounds N (headStart Q + i) (by omega)
  have b1 := pkR_b_vtx2 (N := N) (u := headStart Q + i) (by omega) (by omega)
  have hA : vtx N (headStart Q + i) ∈ oddSide N Q ↔ i < headLen N Q := by
    rw [pkR_b_head_pos hQ v]
    have e : cycPos N (headStart Q) (vtx N (headStart Q + i)) =
        (vtx N (headStart Q + i) + N - headStart Q) % N := rfl
    rw [e]
    have m3 := pkR_b_mod2 (N := N) (z := vtx N (headStart Q + i) + N - headStart Q) (by omega)
    omega
  refine ⟨hA, ?_, b1⟩
  have e : evenSide N Q = Icc 1 N \ oddSide N Q := rfl
  rw [e, mem_sdiff, mem_Icc, hA]
  omega

/-- The region point `subX f_{Q,Q′} X` of `Ω(Q, Q′)` and its size and `d₁′`. -/
def pkR_b_omX (N : ℕ) (Q Q' : ℕ × ℕ) (X : ℕ × ℕ → ℚ) : ℕ × ℕ → ℚ :=
  pkR_subX N (pkR_b_omL N (headStart Q) (cycPos N (headStart Q) (headStart Q')) (headLen N Q')) X

def pkR_b_omM (N : ℕ) (Q Q' : ℕ × ℕ) : ℕ := headLen N Q - headLen N Q' + 2

def pkR_b_omD (N : ℕ) (Q Q' : ℕ × ℕ) : ℕ := cycPos N (headStart Q) (headStart Q') / 2

set_option maxHeartbeats 1000000 in
/-- **[OmegaTiles]** (PREFORM-Res §5.3, the X-level half of R3; R2-Z188 C3). For nested mixed chords `Q ≠ Q′`
(`A_{Q′} ⊆ A_Q`), if every diagonal tile of `T(Q, Q′)` vanishes, the region point of `Ω(Q, Q′)` (list
`f_{Q,Q′} = [a, …, c] ++ [c′+1, …, a′+1]` read with `vtx N`, heads may wrap) lies on `Λ` of the standard polygon
`(m, d₁′)`, its `x′ = c⋆` is `X_Q`, and `X_Q = X_{Q′}`. With [OmegaHyp] (`pkR_b_omegaHyp`) the hypothesis holds on
`L_S` for (H3a) + (H3b). (The minrect conditions of members strictly between are not included here.) -/
theorem pkR_b_omegaTiles {N : ℕ} (hE : N % 2 = 0) {Q Q' : ℕ × ℕ} (hQ : Q ∈ oddDiagonals N)
    (hQ' : Q' ∈ oddDiagonals N) (hsub : oddSide N Q' ⊆ oddSide N Q) (hne : Q ≠ Q') {X : ℕ × ℕ → ℚ}
    (hT : ∀ a b, (a, b) ∈ diagonals N → pkR_b_TP N Q Q' a b → mesh N X a b = 0) :
    pkR_lam (pkR_b_omM N Q Q') (pkR_b_omD N Q Q') ∅ (pkR_b_omX N Q Q' X) ∧
      mesh (pkR_b_omM N Q Q') (pkR_b_omX N Q Q' X) 1 (pkR_b_omM N Q Q' - 1) = X Q ∧ X Q = X Q' := by
  have f1 := pkR_b_head_facts hE hQ
  have f2 := pkR_b_head_facts hE hQ'
  obtain ⟨hp, hpL, hLL, hpos⟩ := pkR_b_nest_pos hE hQ hQ' hsub hne
  have hXQ := pkR_b_planarQ hQ X
  have hXQ' := pkR_b_planarQ hQ' X
  -- the vtx-reading of `Q′`'s dual points from `a`
  have ep : cycPos N (headStart Q) (headStart Q') = (headStart Q' + N - headStart Q) % N := rfl
  have m1 := pkR_b_mod2 (N := N) (z := headStart Q' + N - headStart Q) (by omega)
  have c1 : vtx N (headStart Q + cycPos N (headStart Q) (headStart Q')) = vtx N (headStart Q') := by
    have b1 := pkR_b_vtx2 (N := N) (u := headStart Q + cycPos N (headStart Q) (headStart Q')) (by omega) (by omega)
    have b2 := pkR_b_vtx2 (N := N) (u := headStart Q') (by omega) (by omega)
    omega
  have c2 : vtx N (headStart Q + cycPos N (headStart Q) (headStart Q') + headLen N Q') =
      vtx N (headStart Q' + headLen N Q') := by
    have b1 := pkR_b_vtx2 (N := N) (u := headStart Q + cycPos N (headStart Q) (headStart Q') + headLen N Q')
      (by omega) (by omega)
    have b2 := pkR_b_vtx2 (N := N) (u := headStart Q' + headLen N Q') (by omega) (by omega)
    omega
  rw [← pkR_planar_congr (by omega) X c1 c2] at hXQ'
  have eX : pkR_b_omX N Q Q' X =
      pkR_subX N (pkR_b_omL N (headStart Q) (cycPos N (headStart Q) (headStart Q')) (headLen N Q')) X := rfl
  have eM : pkR_b_omM N Q Q' = headLen N Q - headLen N Q' + 2 := rfl
  have eD : pkR_b_omD N Q Q' = cycPos N (headStart Q) (headStart Q') / 2 := rfl
  rw [eX, eM, eD, ← hXQ, ← hXQ']
  refine pkR_b_omCore (by omega) ⟨by omega, by omega⟩ hp (by omega) (by omega) hpL hLL (by omega)
    ((pkR_b_OT_iff _ _ _ _ _ X).2 ⟨?_, ?_, ?_⟩)
  · intro i j hi hj hij hne'
    obtain ⟨A1, -, V1⟩ := pkR_b_posQ hE hQ (i := i) (by omega)
    obtain ⟨A2, -, V2⟩ := pkR_b_posQ hE hQ (i := j) (by omega)
    have B1 := hpos i (by omega)
    have B2 := hpos j (by omega)
    refine pkR_b_TP_mesh hT (mem_diagonals.2 (by dsimp only; omega)) ((pkR_b_TP_iff N Q Q' _ _).2 (Or.inl ?_))
    exact ⟨by omega, A1.2 (by omega), fun h => by have := B1.1 h; omega, A2.2 (by omega),
      fun h => by have := B2.1 h; omega⟩
  · intro i j hi hi2 hj1 hj2
    obtain ⟨A1, -, V1⟩ := pkR_b_posQ hE hQ (i := i) (by omega)
    obtain ⟨A2, -, V2⟩ := pkR_b_posQ hE hQ (i := j) (by omega)
    have B1 := hpos i (by omega)
    have B2 := hpos j (by omega)
    refine pkR_b_TP_mesh hT (mem_diagonals.2 (by dsimp only; omega))
      ((pkR_b_TP_iff N Q Q' _ _).2 (Or.inr (Or.inl ?_)))
    exact ⟨by omega, A1.2 (by omega), fun h => by have := B1.1 h; omega, B2.2 ⟨hj1, hj2⟩⟩
  · intro i j hi hi2 hj1 hj2
    obtain ⟨A1, -, V1⟩ := pkR_b_posQ hE hQ (i := i) (by omega)
    obtain ⟨-, E2, V2⟩ := pkR_b_posQ hE hQ (i := j) (by omega)
    have B1 := hpos i (by omega)
    refine pkR_b_TP_mesh hT (mem_diagonals.2 (by dsimp only; omega))
      ((pkR_b_TP_iff N Q Q' _ _).2 (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
    exact ⟨by omega, A1.2 (by omega), fun h => by have := B1.1 h; omega, E2.2 hj1⟩

/-! ### Rotation bridge (review R12-P7f-Res-R1 M1; 3c-b `NLSM_rot`)

The frozen `childSetB` labels the B-child of a chord with the massive leg first (child leg `j ≥ 2` ↦ parent leg
`tailStart + j − 2`), whereas `relab` (hence `NP_residue`, `pkR_b_I3num`, `pkR_b_R17`) puts the massive leg last (child
leg `k ≤ n − 1` ↦ parent leg `tailStart + k − 1`): the same cyclic order rotated by one leg, B-leg `k + 1` = relab-leg `k`.
Non-vanishing on a child locus survives this relabelling (witness `y ∘ rot n`, `mesh_rot`, `NLSM_rot`). -/

/-- The extended mesh at arbitrary labels is the mesh at the sorted `npair`. -/
theorem pkR_b_mesh_npair {K : Type*} [Field K] {n : ℕ} (hn : 1 ≤ n) (Y : ℕ × ℕ → K) (u v : ℕ) :
    mesh n Y u v = mesh n Y (npair n u v).1 (npair n u v).2 := by
  have e : npair n u v = (min (vtx n u) (vtx n v), max (vtx n u) (vtx n v)) := rfl
  rw [e, pkR_b_mesh_congr hn Y (pkR_vtx_vtx hn u).symm (pkR_vtx_vtx hn v).symm]
  rcases le_total (vtx n u) (vtx n v) with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, pkR_mesh_comm]

/-- **Rotation bridge**: `NonzeroOn n S` gives `NonzeroOn n S′` for the rotated set
`S′ = {d : npair n (d.1 + 1) (d.2 + 1) ∈ S}` (legs relabelled `k ↦ k + 1`), witnessed by `y ∘ rot n`. For
`S = childSetB N S₀ t` this is the B-child locus in the `relab N (tailStart t)` labelling that `pkR_b_I3num` and
`pkR_b_R17` produce. -/
theorem pkR_b_nonzero_rot {n : ℕ} (hn : 4 ≤ n) (hE : n % 2 = 0) {S : Finset (ℕ × ℕ)} (h : NonzeroOn n S) :
    NonzeroOn n ((diagonals n).filter (fun d => npair n (d.1 + 1) (d.2 + 1) ∈ S)) := by
  obtain ⟨y, hy, hpole, hne⟩ := h
  have hn1 : 1 ≤ n := by omega
  refine (show NonzeroOn n ((diagonals n).filter (fun d => npair n (d.1 + 1) (d.2 + 1) ∈ S)) ↔
      ∃ X : ℕ × ℕ → ℚ, OnLocus n ((diagonals n).filter (fun d => npair n (d.1 + 1) (d.2 + 1) ∈ S)) X ∧
        (∀ d ∈ oddDiagonals n, X d ≠ 0) ∧ NLSM n X ≠ 0 from Iff.rfl).2
    ⟨Function.comp y (rot n), fun t ht => ?_, fun d hd => ?_, ?_⟩
  · rw [mesh_rot hn1, pkR_b_mesh_npair hn1]
    exact hy _ (mem_filter.1 ht).2
  · have hd' := mem_filter.1 hd
    have hdd := mem_diagonals.1 hd'.1
    have e : rot n d = (min (vtx n (d.1 + 1)) (vtx n (d.2 + 1)), max (vtx n (d.1 + 1)) (vtx n (d.2 + 1))) := rfl
    have v1 := pkR_b_vtx2 (N := n) (u := d.1 + 1) (by omega) (by omega)
    have v2 := pkR_b_vtx2 (N := n) (u := d.2 + 1) (by omega) (by omega)
    have hodd := hd'.2
    refine hpole _ (mem_filter.2 ⟨rot_mem hn1 hd'.1, ?_⟩)
    rw [e]
    dsimp only
    omega
  · rw [NLSM_rot hn hE]
    exact hne

set_option maxHeartbeats 1000000 in
/-- [OmegaTiles], member part (PREFORM-Res §5.3 "ι maps into `Λ^I`"), in positions: for a chord `Q″` with
`A_{Q′} ⊆ A_{Q″} ⊆ A_Q` (positions `[p″, p″ + L″)`), vanishing of the parent tiles `minRect(Q″)` (even leg of `A_{Q″}` ×
odd leg of `B_{Q″}`) gives vanishing of the child `minrect` of the standard member `(p″/2, (p″ + L″ − L′ − p)/2)`. -/
theorem pkR_b_omMem {N a p L L' p'' L'' : ℕ} (hN : 1 ≤ N) (ha : 1 ≤ a ∧ a ≤ N) (hp : p % 2 = 0)
    (hL' : L' % 2 = 1) (hL : L % 2 = 1) (hpL : p + L' ≤ L) (hLL : L' + 2 ≤ L) (hLN : L < N) (hp'' : p'' % 2 = 0)
    (hL'' : L'' % 2 = 1) (h1 : p'' ≤ p) (h2 : p + L' ≤ p'' + L'') (h3 : p'' + L'' ≤ L) {X : ℕ × ℕ → ℚ}
    (hM : ∀ i j, p'' ≤ i → i < p'' + L'' → i % 2 = 1 → (j < p'' ∨ p'' + L'' ≤ j) → j < N → j % 2 = 0 →
      mesh N X (vtx N (a + i)) (vtx N (a + j)) = 0) :
    ∀ t ∈ pkR_minrect (L - L' + 2) (p / 2) (p'' / 2, (p'' + L'' - L' - p) / 2),
      mesh (L - L' + 2) (pkR_subX N (pkR_b_omL N a p L') X) t.1 t.2 = 0 := by
  rintro ⟨w, c⟩ ht
  obtain ⟨⟨hw1, hw2, hw3, hw4⟩, ⟨hc1, hc2, hc3, hc4⟩⟩ := (pkR_mem_minrect _ _ _ _).1 ht
  rw [pkR_mem_head] at hw4 hc4
  rw [mem_Icc] at hw1 hc1
  dsimp only at hw1 hw2 hw3 hw4 hc1 hc2 hc3 hc4 ⊢
  have hL1 : 1 ≤ L' := by omega
  have hd : (min w c, max w c) ∈ diagonals (L - L' + 2) := mem_diagonals.2 (by dsimp only; omega)
  rw [pkR_subTile hN (by omega) (pkR_b_om_cyc hN ha hL1 hpL hLL hLN) X (mem_Icc.2 hw1) (mem_Icc.2 hc1) hd]
  have v1 := pkR_b_vtx2 (N := L - L' + 2) (u := c) (by omega) (by omega)
  have v2 := pkR_b_vtx2 (N := L - L' + 2) (u := w + 2) (by omega) (by omega)
  have v3 := pkR_b_vtx2 (N := L - L' + 2) (u := w) (by omega) (by omega)
  have v4 := pkR_b_vtx2 (N := L - L' + 2) (u := c + 2) (by omega) (by omega)
  rw [if_neg (show ¬ vtx (L - L' + 2) c = vtx (L - L' + 2) (w + 2) by omega),
    if_neg (show ¬ vtx (L - L' + 2) w = vtx (L - L' + 2) (c + 2) by omega), add_zero, add_zero]
  refine pkR_b_bsum_zero X fun x hx y hy => ?_
  obtain ⟨i, hi, hi3⟩ := pkR_b_om_posS hN ha hL1 hpL hLL hLN (k := w) (by omega) (by omega) (by omega) hx
  obtain ⟨j, hj, hj3⟩ := pkR_b_om_posS hN ha hL1 hpL hLL hLN (k := c) (by omega) (by omega) (by omega) hy
  rw [pkR_b_mesh_congr hN X hi3 hj3, pkR_mesh_comm]
  exact hM j i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- [OmegaTiles], member part for chords: `A_{Q′} ⊆ A_{Q″} ⊆ A_Q` (`Q″ ≠ Q`) and `minRect(Q″) = 0` give the child
`minrect` of the standard member of `Q″` (`pkR_b_omI`). -/
def pkR_b_omI (N : ℕ) (Q Q' Q'' : ℕ × ℕ) : ℕ × ℕ :=
  (cycPos N (headStart Q) (headStart Q'') / 2,
    (cycPos N (headStart Q) (headStart Q'') + headLen N Q'' - headLen N Q' - cycPos N (headStart Q) (headStart Q')) / 2)

set_option maxHeartbeats 1000000 in
theorem pkR_b_omegaMem {N : ℕ} (hE : N % 2 = 0) {Q Q' Q'' : ℕ × ℕ} (hQ : Q ∈ oddDiagonals N)
    (hQ' : Q' ∈ oddDiagonals N) (hQ'' : Q'' ∈ oddDiagonals N) (hsub : oddSide N Q' ⊆ oddSide N Q)
    (hne : Q ≠ Q') (hsub1 : oddSide N Q' ⊆ oddSide N Q'') (hsub2 : oddSide N Q'' ⊆ oddSide N Q) (hne'' : Q ≠ Q'')
    {X : ℕ × ℕ → ℚ} (hR : ∀ t ∈ minRect N Q'', mesh N X t.1 t.2 = 0) :
    ∀ t ∈ pkR_minrect (pkR_b_omM N Q Q') (pkR_b_omD N Q Q') (pkR_b_omI N Q Q' Q''),
      mesh (pkR_b_omM N Q Q') (pkR_b_omX N Q Q' X) t.1 t.2 = 0 := by
  have f1 := pkR_b_head_facts hE hQ
  have f2 := pkR_b_head_facts hE hQ'
  have f3 := pkR_b_head_facts hE hQ''
  obtain ⟨hp, hpL, hLL, hpos⟩ := pkR_b_nest_pos hE hQ hQ' hsub hne
  obtain ⟨hp3, hpL3, hLL3, hpos3⟩ := pkR_b_nest_pos hE hQ hQ'' hsub2 hne''
  -- `A_{Q′} ⊆ A_{Q″}` in positions
  have t1 := (hpos3 (cycPos N (headStart Q) (headStart Q')) (by omega)).1
    (hsub1 ((hpos _ (by omega)).2 ⟨le_rfl, by omega⟩))
  have t2 := (hpos3 (cycPos N (headStart Q) (headStart Q') + headLen N Q' - 1) (by omega)).1
    (hsub1 ((hpos _ (by omega)).2 ⟨by omega, by omega⟩))
  have eX : pkR_b_omX N Q Q' X =
      pkR_subX N (pkR_b_omL N (headStart Q) (cycPos N (headStart Q) (headStart Q')) (headLen N Q')) X := rfl
  have eM : pkR_b_omM N Q Q' = headLen N Q - headLen N Q' + 2 := rfl
  have eD : pkR_b_omD N Q Q' = cycPos N (headStart Q) (headStart Q') / 2 := rfl
  have eI : pkR_b_omI N Q Q' Q'' = (cycPos N (headStart Q) (headStart Q'') / 2,
      (cycPos N (headStart Q) (headStart Q'') + headLen N Q'' - headLen N Q' - cycPos N (headStart Q) (headStart Q')) / 2)
    := rfl
  rw [eX, eM, eD, eI]
  refine pkR_b_omMem (by omega) ⟨by omega, by omega⟩ hp (by omega) (by omega) hpL hLL (by omega) hp3 (by omega)
    (by omega) (by omega) hpL3 fun i j hi1 hi2 hi3 hj1 hj2 hj3 => ?_
  obtain ⟨-, -, V1⟩ := pkR_b_posQ hE hQ (i := i) (by omega)
  obtain ⟨-, -, V2⟩ := pkR_b_posQ hE hQ (i := j) (by omega)
  have A1 := (hpos3 i (by omega)).2 ⟨hi1, hi2⟩
  have A2 : vtx N (headStart Q + j) ∉ oddSide N Q'' := fun h => by have := (hpos3 j hj2).1 h; omega
  have hv := vtx_bounds N (headStart Q + j) (by omega)
  have hr := pkR_b_rect A1 (by omega) (pkR_b_mem_even hv A2) (by omega)
  have e := hR _ hr
  rcases le_total (vtx N (headStart Q + i)) (vtx N (headStart Q + j)) with h | h
  · rw [min_eq_left h, max_eq_right h] at e
    exact e
  · rw [min_eq_right h, max_eq_left h] at e
    rw [pkR_mesh_comm]
    exact e

/-! ### R6 (Theorem E), X-level, b-side instance (PREFORM-Res §5.6; R2-Z195 C3) — (z1), (z2)

The A-child of `Q` in the frozen `childSetA` / `relab N (headStart Q)` labelling is `Ω` with the degenerate inner
block `L′ = 1` at `p = L − 1`: list `[a, a+1, …, a+L]` (`pkR_b_omL N a (L − 1) 1`), child legs `1..L` = the legs of `A_Q`
(positions `0..L−1`), child leg `L + 1` = `B_Q`. Its single-leg tiles are parent tiles, plus `X_Q` at the straddle
`(1, L)`; so the (z1), (z2) conditions of the ear lemma for `b_Q` hold on `T(Q, b) ∩ {X_Q = 0}`. -/

/-- A child leg that is a single parent leg has a one-element block. -/
theorem pkR_b_om_blk1 {N a p L L' k : ℕ} (ha : 1 ≤ a ∧ a ≤ N) (hL' : 1 ≤ L') (hpL : p + L' ≤ L)
    (hLL : L' + 2 ≤ L) (hLN : L < N) (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ L - L' + 2) (hkp : k ≠ p + 1 ∨ L' = 1) :
    pkR_blk N (L - L' + 2) (pkR_b_omL N a p L') k = {pkR_b_omL N a p L' k} := by
  have eb : pkR_blk N (L - L' + 2) (pkR_b_omL N a p L') k =
      Icc (pkR_b_omL N a p L' (vtx (L - L' + 2) k)) (pkR_b_omL N a p L' (vtx (L - L' + 2) k) +
        (pkR_b_omL N a p L' (vtx (L - L' + 2) (k + 1)) + N - pkR_b_omL N a p L' (vtx (L - L' + 2) k)) % N - 1) := rfl
  rw [eb, pkR_b_om_next hk1 (by omega), vtx_of_mem hk1 (by omega), pkR_b_omL_def]
  have o1 := pkR_b_olo_eq p L' k
  have o2 := pkR_b_olo_eq p L' (k + 1)
  have o3 := pkR_b_ohi_eq N L L' p k
  have b1 := pkR_b_vtx2 (N := N) (u := a + pkR_b_olo p L' k) (by omega) (by omega)
  have b2 := pkR_b_vtx2 (N := N) (u := a + pkR_b_ohi N L L' p k) (by omega) (by omega)
  have m2 := pkR_b_mod2 (N := N)
    (z := vtx N (a + pkR_b_ohi N L L' p k) + N - vtx N (a + pkR_b_olo p L' k)) (by omega)
  rw [show vtx N (a + pkR_b_olo p L' k) + (vtx N (a + pkR_b_ohi N L L' p k) + N - vtx N (a + pkR_b_olo p L' k)) % N
    - 1 = vtx N (a + pkR_b_olo p L' k) by omega, Icc_self]

set_option maxHeartbeats 1000000 in
/-- **A-child tiles** (R6 building block): tiles of two legs of `A_Q` in the A-child of `Q` are the parent tiles, plus
`X_Q` (the planar variable at the dual points `a`, `a + L` of `Q`) at the straddle `(1, L)`. -/
theorem pkR_b_Atile {N a L : ℕ} (hN : 1 ≤ N) (ha : 1 ≤ a ∧ a ≤ N) (hL : L % 2 = 1) (hL3 : 3 ≤ L) (hLN : L < N)
    (X : ℕ × ℕ → ℚ) {k l : ℕ} (hk : 1 ≤ k) (hkl : k + 2 ≤ l) (hl : l ≤ L) :
    mesh (L - 1 + 2) (pkR_subX N (pkR_b_omL N a (L - 1) 1) X) k l =
      mesh N X (vtx N (a + (k - 1))) (vtx N (a + (l - 1))) + (if k = 1 ∧ l = L then planar N X a (a + L) else 0) := by
  have hpL : L - 1 + 1 ≤ L := by omega
  have hLL : 1 + 2 ≤ L := by omega
  rw [pkR_subTile hN (by omega) (pkR_b_om_cyc hN ha le_rfl hpL hLL hLN) X (mem_Icc.2 ⟨hk, by omega⟩)
    (mem_Icc.2 ⟨by omega, by omega⟩) (mem_diagonals.2 (by dsimp only; omega))]
  have vl : vtx (L - 1 + 2) l = l := vtx_of_mem (by omega) (by omega)
  have vk2 : vtx (L - 1 + 2) (k + 2) = k + 2 := vtx_of_mem (by omega) (by omega)
  have vk1 : vtx (L - 1 + 2) (k + 1) = k + 1 := vtx_of_mem (by omega) (by omega)
  have vk : vtx (L - 1 + 2) k = k := vtx_of_mem hk (by omega)
  rw [vl, vk2, vk1, vk]
  have c1 : (if l = k + 2 then planar N X (pkR_b_omL N a (L - 1) 1 (k + 1)) (pkR_b_omL N a (L - 1) 1 (k + 2))
      else 0) = 0 := by
    split_ifs with h
    · exact pkR_b_om_single' hN X rfl (by omega) (by omega)
    · rfl
  have c2 : (if k = vtx (L - 1 + 2) (l + 2) then planar N X (pkR_b_omL N a (L - 1) 1 (vtx (L - 1 + 2) (l + 1)))
      (pkR_b_omL N a (L - 1) 1 (vtx (L - 1 + 2) (l + 2))) else 0) =
      (if k = 1 ∧ l = L then planar N X a (a + L) else 0) := by
    have v1 := pkR_b_vtx2 (N := L - 1 + 2) (u := l + 1) (by omega) (by omega)
    have v2 := pkR_b_vtx2 (N := L - 1 + 2) (u := l + 2) (by omega) (by omega)
    by_cases h : k = 1 ∧ l = L
    · rw [if_pos (show k = vtx (L - 1 + 2) (l + 2) by omega), if_pos h,
        show vtx (L - 1 + 2) (l + 1) = L - 1 + 2 by omega, show vtx (L - 1 + 2) (l + 2) = 1 by omega,
        pkR_b_omL_def, pkR_b_omL_def,
        show pkR_b_olo (L - 1) 1 (L - 1 + 2) = L by have o := pkR_b_olo_eq (L - 1) 1 (L - 1 + 2); omega,
        show pkR_b_olo (L - 1) 1 1 = 0 by have o := pkR_b_olo_eq (L - 1) 1 1; omega, add_zero,
        pkR_planar_comm N X (vtx N (a + L)) (vtx N a), ← pkR_planar_vtx hN X a (a + L)]
    · rw [if_neg (show ¬ k = vtx (L - 1 + 2) (l + 2) by omega), if_neg h]
  rw [c1, c2, add_zero, pkR_b_om_blk1 (k := k) ha le_rfl hpL hLL hLN hk (by omega) (Or.inr rfl),
    pkR_b_om_blk1 (k := l) ha le_rfl hpL hLL hLN (by omega) (by omega) (Or.inr rfl), sum_singleton, sum_singleton,
    pkR_b_omL_def, pkR_b_omL_def,
    show pkR_b_olo (L - 1) 1 k = k - 1 by have o := pkR_b_olo_eq (L - 1) 1 k; omega,
    show pkR_b_olo (L - 1) 1 l = l - 1 by have o := pkR_b_olo_eq (L - 1) 1 l; omega]

/-- **R6, (z1) and (z2) for `b_Q`** (PREFORM-Res §5.6 claim "(z1), (z2) ∈ span(T(Q, b), X_Q)"): with `A_b` = positions
`[p, p + L′)` of `A_Q`, on `T(Q, b) ∩ {X_Q = 0}` every tile of the A-child of `Q` between two odd legs of
`μ = A_Q ∖ A_b` (z1), or between an odd leg of `μ` and a leg of `A_b` (z2), vanishes. (Odd legs = even positions.) -/
theorem pkR_b_R6z {N a p L L' : ℕ} (hN : 1 ≤ N) (ha : 1 ≤ a ∧ a ≤ N) (hL : L % 2 = 1) (hpL : p + L' ≤ L)
    (hLL : L' + 2 ≤ L) (hLN : L < N) {X : ℕ × ℕ → ℚ} (hT : pkR_b_OT N a p L L' X)
    (hXQ : planar N X a (a + L) = 0) {k l : ℕ} (hk : 1 ≤ k) (hkl : k + 2 ≤ l) (hl : l ≤ L)
    (hz : (((k - 1 < p ∨ (p + L' ≤ k - 1 ∧ k - 1 < L)) ∧ (k - 1) % 2 = 0) ∧
        (((l - 1 < p ∨ (p + L' ≤ l - 1 ∧ l - 1 < L)) ∧ (l - 1) % 2 = 0) ∨ (p ≤ l - 1 ∧ l - 1 < p + L'))) ∨
      (((l - 1 < p ∨ (p + L' ≤ l - 1 ∧ l - 1 < L)) ∧ (l - 1) % 2 = 0) ∧ p ≤ k - 1 ∧ k - 1 < p + L')) :
    mesh (L - 1 + 2) (pkR_subX N (pkR_b_omL N a (L - 1) 1) X) k l = 0 := by
  obtain ⟨HT1, HT2, -⟩ := (pkR_b_OT_iff N a p L L' X).1 hT
  rw [pkR_b_Atile hN ha hL (by omega) hLN X hk hkl hl, hXQ, ite_self, add_zero]
  rcases hz with ⟨hk', hl' | hl'⟩ | ⟨hl', hk'⟩
  · exact HT1 (k - 1) (l - 1) hk'.1 hl'.1 (by omega) (by omega)
  · exact HT2 (k - 1) (l - 1) hk'.1 hk'.2 hl'.1 hl'.2
  · rw [pkR_mesh_comm]
    exact HT2 (l - 1) (k - 1) hl'.1 hl'.2 hk'.1 hk'.2

-- R12-P7b-pkgRes-c2 (claude-opus-5-5, 2026-09-28, second dispatch): sub-wave c2 — R9 [Const9] on the simple route
-- (thread §3 'c2'), then R14(d), R15, R10. Every name prefixed `pkR_` (no `pkR_b_`).

/-! ### pkgRes sub-wave c2 (R12-P7b-pkgRes-c2, claude-opus-5-5): R9 [Const9] -/

/-- Planar variables of a combination `a·X + b·Y`. -/
theorem pkR_planar_comb (n : ℕ) (X Y : ℕ × ℕ → ℚ) (a b : ℚ) (i j : ℕ) :
    planar n (fun p => a * X p + b * Y p) i j = a * planar n X i j + b * planar n Y i j := by
  rw [pkR_planar_def, pkR_planar_def n X, pkR_planar_def n Y]
  split_ifs
  · rfl
  · ring

/-- Tiles of a combination `a·X + b·Y`. -/
theorem pkR_mesh_comb (n : ℕ) (X Y : ℕ × ℕ → ℚ) (a b : ℚ) (u v : ℕ) :
    mesh n (fun p => a * X p + b * Y p) u v = a * mesh n X u v + b * mesh n Y u v := by
  rw [pkR_mesh_def, pkR_mesh_def n X, pkR_mesh_def n Y, pkR_planar_comb, pkR_planar_comb, pkR_planar_comb,
    pkR_planar_comb]
  ring

/-- Tiles of the zero point. -/
theorem pkR_mesh_zero (n u v : ℕ) : mesh n (fun _ => (0 : ℚ)) u v = 0 := by
  rw [pkR_mesh_def]
  simp only [pkR_planar_def, ite_self, add_zero, sub_zero]

/-- `Λ^I` is a linear subspace. -/
theorem pkR_lam_sub (n d₁ : ℕ) (I : Finset (ℕ × ℕ)) : pkR_Sub {X | pkR_lam n d₁ I X} := by
  refine (pkR_Sub_iff _).2 ⟨?_, ?_⟩
  · show pkR_lam n d₁ I (fun _ => (0 : ℚ))
    refine (pkR_lam_iff _ _ _ _).2 ⟨fun a _ b _ _ _ _ _ => pkR_mesh_zero n a b, ?_, fun Q _ t _ => pkR_mesh_zero n t.1 t.2⟩
    rw [pkR_mesh_zero, pkR_mesh_zero]
  · intro X hX Y hY a b
    have hX' : pkR_lam n d₁ I X := hX
    have hY' : pkR_lam n d₁ I Y := hY
    obtain ⟨h1, h2, h3⟩ := (pkR_lam_iff _ _ _ _).1 hX'
    obtain ⟨k1, k2, k3⟩ := (pkR_lam_iff _ _ _ _).1 hY'
    show pkR_lam n d₁ I (fun i => a * X i + b * Y i)
    refine (pkR_lam_iff _ _ _ _).2 ⟨fun u hu v hv e1 e2 e3 e4 => ?_, ?_, fun Q hQ t ht => ?_⟩
    · rw [pkR_mesh_comb, h1 u hu v hv e1 e2 e3 e4, k1 u hu v hv e1 e2 e3 e4]
      ring
    · rw [pkR_mesh_comb, pkR_mesh_comb, h2, k2]
    · rw [pkR_mesh_comb, h3 Q hQ t ht, k3 Q hQ t ht]
      ring

/-- A tile as a polynomial (so `x = c⋆` is a linear form for the §6 algebra layer). -/
noncomputable def pkR_meshP (n a b : ℕ) : MvPolynomial (ℕ × ℕ) ℚ :=
  planarP ℚ n a b + planarP ℚ n (a + 1) (b + 1) - planarP ℚ n a (b + 1) - planarP ℚ n (a + 1) b

theorem pkR_meshP_eval (n a b : ℕ) (X : ℕ × ℕ → ℚ) :
    MvPolynomial.eval X (pkR_meshP n a b) = mesh n X a b := by
  have h : ∀ i j : ℕ, MvPolynomial.eval X (planarP ℚ n i j) = planar n X i j := by
    intro i j
    rw [planarP_hom (MvPolynomial.eval X) n i j]
    simp only [MvPolynomial.eval_X]
  rw [show pkR_meshP n a b = planarP ℚ n a b + planarP ℚ n (a + 1) (b + 1) - planarP ℚ n a (b + 1) -
      planarP ℚ n (a + 1) b from rfl, map_sub, map_sub, map_add, h, h, h, h, pkR_mesh_def]

theorem pkR_meshP_lin (n a b : ℕ) : pkR_Lin (pkR_meshP n a b) := by
  intro x y s t
  rw [pkR_meshP_eval, pkR_meshP_eval, pkR_meshP_eval, pkR_mesh_comb]

/-- End points of an odd diagonal. -/
theorem pkR_odd_bd {n : ℕ} {Q : ℕ × ℕ} (hQ : Q ∈ oddDiagonals n) : 1 ≤ Q.1 ∧ Q.1 + 2 ≤ Q.2 ∧ Q.2 ≤ n := by
  have hQd := (mem_filter.1 hQ).1
  rw [mem_diagonals] at hQd
  omega

/-- A linear form scales. -/
theorem pkR_lin_scale {σ : Type*} {ℓ : MvPolynomial σ ℚ} (h : pkR_Lin ℓ) (x : σ → ℚ) (t : ℚ) :
    MvPolynomial.eval (fun i => t * x i) ℓ = t * MvPolynomial.eval x ℓ := by
  have e := h x x t 0
  have e2 : (fun i => t * x i + 0 * x i) = fun i => t * x i := by
    ext i; ring
  rw [e2] at e
  rw [e]; ring

/-- A homogeneous polynomial scales. -/
theorem pkR_hom_eval {σ : Type*} {P : MvPolynomial σ ℚ} {m : ℕ} (h : P.IsHomogeneous m) (x : σ → ℚ) (t : ℚ) :
    MvPolynomial.eval (fun i => t * x i) P = t ^ m * MvPolynomial.eval x P := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  rw [h.degree_eq_sum_deg_support hs]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

/-- Scaling substitution. -/
theorem pkR_eval_scale {σ : Type*} (F : MvPolynomial σ ℚ) (y : σ → ℚ) (t : ℚ) :
    MvPolynomial.eval y (MvPolynomial.aeval (fun i => (MvPolynomial.C t * MvPolynomial.X i : MvPolynomial σ ℚ)) F) =
      MvPolynomial.eval (fun i => t * y i) F := by
  rw [pkR_eval_aeval]
  simp only [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]

/-- The ray through `x` is a subspace. -/
theorem pkR_ray_sub {σ : Type*} (x : σ → ℚ) : pkR_Sub {y : σ → ℚ | ∃ t : ℚ, y = fun i => t * x i} := by
  refine (pkR_Sub_iff _).2 ⟨⟨0, by ext i; ring⟩, ?_⟩
  rintro y ⟨t1, rfl⟩ z ⟨t2, rfl⟩ a b
  exact ⟨a * t1 + b * t2, by ext i; ring⟩

/-- **Homogeneity of a quotient** (R9 step 6): if `N = ℓ·F` on `V` with `N` homogeneous of degree `k + 1` and `ℓ` a
linear form not identically zero on `V`, then `F` scales with degree `k` on `V` (all `t`, `t = 0` included). -/
theorem pkR_homQuot {σ : Type*} {V : Set (σ → ℚ)} (hV : pkR_Sub V) {ℓ N F : MvPolynomial σ ℚ} {k : ℕ}
    (hℓ : pkR_Lin ℓ) (hw : ∃ w ∈ V, MvPolynomial.eval w ℓ ≠ 0)
    (hN : ∀ x : σ → ℚ, ∀ t : ℚ, MvPolynomial.eval (fun i => t * x i) N = t ^ (k + 1) * MvPolynomial.eval x N)
    (hF : ∀ x ∈ V, MvPolynomial.eval x N = MvPolynomial.eval x ℓ * MvPolynomial.eval x F) :
    ∀ x ∈ V, ∀ t : ℚ, MvPolynomial.eval (fun i => t * x i) F = t ^ k * MvPolynomial.eval x F := by
  -- t ≠ 0, ℓ(y) ≠ 0
  have h1 : ∀ y ∈ V, MvPolynomial.eval y ℓ ≠ 0 → ∀ t : ℚ, t ≠ 0 →
      MvPolynomial.eval (fun i => t * y i) F = t ^ k * MvPolynomial.eval y F := by
    intro y hy hly t ht
    have e := hF _ (pkR_smul_mem hV hy t)
    rw [hN y t, hF y hy, pkR_lin_scale hℓ y t] at e
    have hne : t * MvPolynomial.eval y ℓ ≠ 0 := mul_ne_zero ht hly
    refine mul_left_cancel₀ hne ?_
    rw [← e]
    ring
  -- any t, ℓ(y) ≠ 0 (t = 0 by the ray)
  have h2 : ∀ y ∈ V, MvPolynomial.eval y ℓ ≠ 0 → ∀ t : ℚ,
      MvPolynomial.eval (fun i => t * y i) F = t ^ k * MvPolynomial.eval y F := by
    intro y hy hly t
    by_cases ht : t = 0
    · have hl := line_bridge {z : σ → ℚ | ∃ s : ℚ, z = fun i => s * y i} (pkR_line (pkR_ray_sub y))
        (F - MvPolynomial.C (MvPolynomial.eval y F / MvPolynomial.eval y ℓ ^ k) * ℓ ^ k) ℓ (w := y)
        ⟨1, by ext i; ring⟩ hly ?_ (fun i => t * y i) ⟨t, rfl⟩
      · rw [map_sub, map_mul, map_pow, MvPolynomial.eval_C, pkR_lin_scale hℓ y t, sub_eq_zero] at hl
        rw [hl, mul_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero k hly)]
        ring
      · rintro z ⟨s, rfl⟩ hz
        rw [pkR_lin_scale hℓ y s] at hz
        have hs : s ≠ 0 := fun h0 => hz (by rw [h0, zero_mul])
        rw [map_sub, map_mul, map_pow, MvPolynomial.eval_C, pkR_lin_scale hℓ y s, h1 y hy hly s hs, mul_pow,
          sub_eq_zero, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero k hly)]
        ring
    · exact h1 y hy hly t ht
  intro x hx t
  obtain ⟨w, hwV, hwl⟩ := hw
  have hl := line_bridge V (pkR_line hV)
    (MvPolynomial.aeval (fun i => (MvPolynomial.C t * MvPolynomial.X i : MvPolynomial σ ℚ)) F -
      MvPolynomial.C (t ^ k) * F) ℓ hwV hwl (fun y hy hly => by
        rw [map_sub, map_mul, MvPolynomial.eval_C, pkR_eval_scale, h2 y hy hly t, sub_self]) x hx
  rw [map_sub, map_mul, MvPolynomial.eval_C, pkR_eval_scale, sub_eq_zero] at hl
  exact hl

/-- R9 step 1a: `NP_n = 0` on `Λ^I₀` (every same-parity tile is `0` there, so `Λ^I₀ ⊆ Z_{evens}`; [STnum]). -/
theorem pkR_c9_zero {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ : ℕ} (hd : 2 * d₁ + 2 ≤ n) {I : Finset (ℕ × ℕ)}
    {X : ℕ × ℕ → ℚ} (hX : pkR_lam n d₁ I X) (hx : mesh n X 1 (n - 1) = 0) :
    MvPolynomial.eval X (NP ℚ n) = 0 := by
  refine pkR_STnum hn hE (show (0 : ℕ) < 2 by norm_num) (pkR_adm_evens hn) X ?_
  refine pkR_ZT_evens hE (fun a b ha hab hb hao hbo => ?_)
  exact pkR_lam0_sp hE hn hd hX hx a (mem_Icc.2 ⟨ha, by omega⟩) b (mem_Icc.2 ⟨by omega, by omega⟩) hab (by omega)

/-- R9 step 1b ([Div]): `NP_n = x·F₁` on `Λ`. -/
theorem pkR_c9_F1 {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ : ℕ} (hd : 2 * d₁ + 2 ≤ n) :
    ∃ F₁ : MvPolynomial (ℕ × ℕ) ℚ, ∀ X : ℕ × ℕ → ℚ, pkR_lam n d₁ ∅ X →
      MvPolynomial.eval X (NP ℚ n) = mesh n X 1 (n - 1) * MvPolynomial.eval X F₁ := by
  obtain ⟨F, hF⟩ := pkR_div (pkR_lam_sub n d₁ ∅) (pkR_meshP_lin n 1 (n - 1))
    ⟨pkR_chA n d₁, (pkR_xwit hE hn d₁ hd).1, by rw [pkR_meshP_eval, (pkR_xwit hE hn d₁ hd).2]; norm_num⟩ (NP ℚ n)
    (fun X hX hx => pkR_c9_zero hE hn hd (I := ∅) hX (by rwa [pkR_meshP_eval] at hx))
  exact ⟨F, fun X hX => by rw [hF X hX, pkR_meshP_eval]⟩

/-- R9 witness: a point of `Λ ∩ {X_Q = 0}` with `x = 1` (`chA` minus a multiple of the (G) witness). -/
theorem pkR_c9_wit {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ : ℕ} (hd : 2 * d₁ + 2 ≤ n) {Q : ℕ × ℕ}
    (hQ : Q ∈ oddDiagonals n) :
    ∃ w : ℕ × ℕ → ℚ, pkR_lam n d₁ ∅ w ∧ w Q = 0 ∧ mesh n w 1 (n - 1) = 1 := by
  obtain ⟨Y, hY, hYx, hYQ⟩ := pkR_G hE hn d₁ hd hQ
  obtain ⟨hc, hcx⟩ := pkR_xwit hE hn d₁ hd
  refine ⟨fun i => 1 * pkR_chA n d₁ i + (-(pkR_chA n d₁ Q / Y Q)) * Y i,
    ((pkR_Sub_iff _).1 (pkR_lam_sub n d₁ ∅)).2 _ hc _ hY 1 (-(pkR_chA n d₁ Q / Y Q)), ?_, ?_⟩
  · show 1 * pkR_chA n d₁ Q + -(pkR_chA n d₁ Q / Y Q) * Y Q = 0
    rw [neg_mul, ← sub_eq_add_neg, one_mul]
    exact pkR_elim hYQ
  · rw [pkR_mesh_comb, hcx, hYx]
    ring

/-- R9 steps 2–4 (simple route, thread §3 'c2'): for every mixed diagonal `Q`, `F₁ = 0` on `Λ₀ ∩ {X_Q = 0}`. Both
child numerators of [ResNum] vanish on `Λ₀ ∩ {X_Q = 0}` (every same-parity tile is `0` on `Λ₀`), so [Div] on
`Λ ∩ {X_Q = 0}` gives `L = x·α`, `R = x·γ` there, hence `x·F₁ = x²·α·γ·cross` and [Prime] cancels `x`. -/
theorem pkR_c9_vanQ {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ : ℕ} (hd : 2 * d₁ + 2 ≤ n)
    {F₁ : MvPolynomial (ℕ × ℕ) ℚ}
    (hF : ∀ X : ℕ × ℕ → ℚ, pkR_lam n d₁ ∅ X →
      MvPolynomial.eval X (NP ℚ n) = mesh n X 1 (n - 1) * MvPolynomial.eval X F₁)
    {Q : ℕ × ℕ} (hQ : Q ∈ oddDiagonals n) :
    ∀ X : ℕ × ℕ → ℚ, pkR_lam n d₁ ∅ X → mesh n X 1 (n - 1) = 0 → X Q = 0 → MvPolynomial.eval X F₁ = 0 := by
  have hb := pkR_odd_bd hQ
  have hV' := pkR_sub_inter (pkR_lam_sub n d₁ ∅) (pkR_lin_X (σ := ℕ × ℕ) Q)
  obtain ⟨w, hw, hwQ, hwx⟩ := pkR_c9_wit hE hn hd hQ
  have hwV' : w ∈ {X | X ∈ {X | pkR_lam n d₁ ∅ X} ∧ MvPolynomial.eval X (MvPolynomial.X Q) = 0} :=
    ⟨hw, by rw [MvPolynomial.eval_X]; exact hwQ⟩
  have hwit : ∃ w ∈ {X | X ∈ {X | pkR_lam n d₁ ∅ X} ∧ MvPolynomial.eval X (MvPolynomial.X Q) = 0},
      MvPolynomial.eval w (pkR_meshP n 1 (n - 1)) ≠ 0 :=
    ⟨w, hwV', by rw [pkR_meshP_eval, hwx]; norm_num⟩
  obtain ⟨α, hα⟩ := pkR_div hV' (pkR_meshP_lin n 1 (n - 1)) hwit
    (MvPolynomial.rename (relab n Q.1) (NP ℚ (Q.2 - Q.1 + 1))) (fun X hX hx => by
      have hX1 : pkR_lam n d₁ ∅ X := hX.1
      have hXQ : X Q = 0 := by have h2 := hX.2; rwa [MvPolynomial.eval_X] at h2
      rw [pkR_meshP_eval] at hx
      exact pkR_side1_NP (p := Q.1) (q := Q.2) hE hn hQ (fun a b h1 h2 h3 h4 h5 =>
        pkR_lam0_sp hE hn hd hX1 hx a (mem_Icc.2 ⟨by omega, by omega⟩) b (mem_Icc.2 ⟨by omega, by omega⟩) h2
          (by omega)) hXQ)
  obtain ⟨γ, hγ⟩ := pkR_div hV' (pkR_meshP_lin n 1 (n - 1)) hwit
    (MvPolynomial.rename (relab n Q.2) (NP ℚ (n - Q.2 + Q.1 + 1))) (fun X hX hx => by
      have hX1 : pkR_lam n d₁ ∅ X := hX.1
      have hXQ : X Q = 0 := by have h2 := hX.2; rwa [MvPolynomial.eval_X] at h2
      rw [pkR_meshP_eval] at hx
      exact pkR_side2_NP (p := Q.1) (q := Q.2) hE hn hQ (fun a ha b hb' h1 _ _ h4 h5 =>
        pkR_lam0_sp hE hn hd hX1 hx a ha b hb' h1 (by omega)) hXQ)
  obtain ⟨E, hEq⟩ := pkR_resNum (R := ℚ) hn hE hQ
  have hz := pkR_prime hV' hwit (G := F₁ - pkR_meshP n 1 (n - 1) * α * γ * crossProd ℚ n Q) (fun X hX => by
    have hX1 : pkR_lam n d₁ ∅ X := hX.1
    have hXQ : X Q = 0 := by have h2 := hX.2; rwa [MvPolynomial.eval_X] at h2
    have e := congrArg (MvPolynomial.eval X) hEq
    rw [map_add, map_mul, map_mul, map_mul, MvPolynomial.eval_X, hXQ, zero_mul, zero_add, hα X hX, hγ X hX,
      hF X hX1, pkR_meshP_eval] at e
    rw [map_sub, map_mul, map_mul, map_mul, pkR_meshP_eval, mul_sub, e]
    ring)
  intro X hX hx hXQ
  have h0 := hz X ⟨hX, by rw [MvPolynomial.eval_X]; exact hXQ⟩
  rw [map_sub, map_mul, map_mul, map_mul, pkR_meshP_eval, hx, sub_eq_zero] at h0
  rw [h0]
  ring

/-- **R9 [Const9]** (PREFORM-Res §4.3; simple route of thread §3 'c2', no side-type table): on the standard polygon
(`n` even ≥ 4, any gap `d₁`), `NP_n = x·F₁` on `Λ` and `F₁ = c·oddDen_n` on `Λ₀` for one constant `c`. -/
theorem pkR_const9 {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) (d₁ : ℕ) (hd : 2 * d₁ + 2 ≤ n) :
    ∃ (F₁ : MvPolynomial (ℕ × ℕ) ℚ) (c : ℚ),
      (∀ X : ℕ × ℕ → ℚ, pkR_lam n d₁ ∅ X →
        MvPolynomial.eval X (NP ℚ n) = mesh n X 1 (n - 1) * MvPolynomial.eval X F₁) ∧
      ∀ X : ℕ × ℕ → ℚ, pkR_lam n d₁ ∅ X → mesh n X 1 (n - 1) = 0 →
        MvPolynomial.eval X F₁ = c * MvPolynomial.eval X (oddDen ℚ n) := by
  obtain ⟨F₁, hF⟩ := pkR_c9_F1 hE hn hd
  have hV := pkR_lam_sub n d₁ ∅
  have hV0 := pkR_sub_inter hV (pkR_meshP_lin n 1 (n - 1))
  -- [ProdDiv] on Λ₀ with the forms X_Q, Q mixed
  obtain ⟨G, hG⟩ := pkR_prodDiv hV0 (fun Q => (MvPolynomial.X Q : MvPolynomial (ℕ × ℕ) ℚ)) (oddDiagonals n)
    (fun Q _ => pkR_lin_X Q)
    (fun Q hQ => by
      obtain ⟨Y, hY, hYx, hYQ⟩ := pkR_G hE hn d₁ hd hQ
      exact ⟨Y, ⟨hY, by rw [pkR_meshP_eval]; exact hYx⟩, by simp only [MvPolynomial.eval_X]; exact hYQ⟩)
    (fun Q hQ Q' hQ' hne => by
      obtain ⟨Y, hY, hYx, hYQ, hYQ'⟩ := pkR_G2 hE hn d₁ hd hQ hQ' hne
      exact ⟨Y, ⟨hY, by rw [pkR_meshP_eval]; exact hYx⟩, by simp only [MvPolynomial.eval_X]; exact hYQ,
        by simp only [MvPolynomial.eval_X]; exact hYQ'⟩)
    F₁ (fun Q hQ X hX hXQ => by
      have hX1 : pkR_lam n d₁ ∅ X := hX.1
      have hx : mesh n X 1 (n - 1) = 0 := by have h2 := hX.2; rwa [pkR_meshP_eval] at h2
      simp only [MvPolynomial.eval_X] at hXQ
      exact pkR_c9_vanQ hE hn hd hF hQ X hX1 hx hXQ)
  have hPD : Finset.prod (oddDiagonals n) (fun Q => (MvPolynomial.X Q : MvPolynomial (ℕ × ℕ) ℚ)) = oddDen ℚ n := rfl
  rw [hPD] at hG
  -- homogeneity of F₁ and oddDen, then [Const]
  have hN : ∀ x : ℕ × ℕ → ℚ, ∀ t : ℚ, MvPolynomial.eval (fun i => t * x i) (NP ℚ n) =
      t ^ ((oddDiagonals n).card + 1) * MvPolynomial.eval x (NP ℚ n) :=
    fun x t => pkR_hom_eval (pkR_NP_hom hn) x t
  have hF' : ∀ x ∈ {X | pkR_lam n d₁ ∅ X}, MvPolynomial.eval x (NP ℚ n) =
      MvPolynomial.eval x (pkR_meshP n 1 (n - 1)) * MvPolynomial.eval x F₁ :=
    fun x hx => by rw [pkR_meshP_eval]; exact hF x hx
  have hH := pkR_homQuot hV (pkR_meshP_lin n 1 (n - 1))
    ⟨pkR_chA n d₁, (pkR_xwit hE hn d₁ hd).1, by rw [pkR_meshP_eval, (pkR_xwit hE hn d₁ hd).2]; norm_num⟩ hN hF'
  have hD : ∀ x ∈ {X | X ∈ {X | pkR_lam n d₁ ∅ X} ∧ MvPolynomial.eval X (pkR_meshP n 1 (n - 1)) = 0}, ∀ t : ℚ,
      MvPolynomial.eval (fun i => t * x i) (oddDen ℚ n) = t ^ (oddDiagonals n).card * MvPolynomial.eval x (oddDen ℚ n) := by
    intro x _ t
    rw [pkR_eval_oddDen, pkR_eval_oddDen, Finset.prod_mul_distrib, Finset.prod_const]
  obtain ⟨w, hwV, hw⟩ := pkR_avoid_aux hV0 (fun Q => (MvPolynomial.X Q : MvPolynomial (ℕ × ℕ) ℚ)) (oddDiagonals n)
    (fun Q hQ => by
      obtain ⟨Y, hY, hYx, hYQ⟩ := pkR_G hE hn d₁ hd hQ
      exact ⟨Y, ⟨hY, by rw [pkR_meshP_eval]; exact hYx⟩, by simp only [MvPolynomial.eval_X]; exact hYQ⟩)
  rw [hPD] at hw
  have hc := pkR_const hV0 (P := F₁) (D := oddDen ℚ n) (G := G) (k := (oddDiagonals n).card)
    (fun x hx t => hH x hx.1 t) hD hG ⟨w, hwV, hw⟩
  refine ⟨F₁, MvPolynomial.eval (fun _ => (0 : ℚ)) G, hF, fun X hX hx => ?_⟩
  have hX0 : X ∈ {X | X ∈ {X | pkR_lam n d₁ ∅ X} ∧ MvPolynomial.eval X (pkR_meshP n 1 (n - 1)) = 0} :=
    ⟨hX, by rw [pkR_meshP_eval]; exact hx⟩
  rw [hG X hX0, hc X hX0]
  ring

/-! ### pkgRes sub-wave c2: R14(d) and the ¬q [ResNum] form -/

/-- `W_q` is a linear subspace. -/
theorem pkR_W_sub (n d₁ : ℕ) (q : ℕ × ℕ) : pkR_Sub {X | pkR_W n d₁ q X} := by
  refine (pkR_Sub_iff _).2 ⟨?_, ?_⟩
  · show pkR_W n d₁ q (fun _ => (0 : ℚ))
    exact (pkR_W_iff _ _ _ _).2 ⟨fun a _ b _ _ _ _ _ _ => pkR_mesh_zero n a b, fun t _ => pkR_mesh_zero n t.1 t.2⟩
  · intro X hX Y hY a b
    have hX' : pkR_W n d₁ q X := hX
    have hY' : pkR_W n d₁ q Y := hY
    obtain ⟨h1, h3⟩ := (pkR_W_iff _ _ _ _).1 hX'
    obtain ⟨k1, k3⟩ := (pkR_W_iff _ _ _ _).1 hY'
    show pkR_W n d₁ q (fun i => a * X i + b * Y i)
    refine (pkR_W_iff _ _ _ _).2 ⟨fun u hu v hv e1 e2 e3 e4 e5 => ?_, fun t ht => ?_⟩
    · rw [pkR_mesh_comb, h1 u hu v hv e1 e2 e3 e4 e5, k1 u hu v hv e1 e2 e3 e4 e5]
      ring
    · rw [pkR_mesh_comb, h3 t ht, k3 t ht]
      ring

/-- The member chord map is injective. -/
theorem pkR_mchord_inj {d₁ : ℕ} {Q Q' : ℕ × ℕ} (h : pkR_mchord d₁ Q = pkR_mchord d₁ Q') : Q = Q' := by
  have h1 : 2 * Q.1 + 1 = 2 * Q'.1 + 1 := congrArg Prod.fst h
  have h2 : 2 * d₁ + 2 * Q.2 + 2 = 2 * d₁ + 2 * Q'.2 + 2 := congrArg Prod.snd h
  exact Prod.ext (by omega) (by omega)

/-- A standard member other than `a`, `b` (the hypotheses of `pkR_mchord_mem`). -/
def pkR_isMem (n d₁ : ℕ) (Q : ℕ × ℕ) : Prop :=
  Q.1 ≤ d₁ ∧ 2 * d₁ + 2 * Q.2 + 2 ≤ n ∧ ¬ (Q.1 = d₁ ∧ Q.2 = 0) ∧ ¬ (Q.1 = 0 ∧ 2 * d₁ + 2 * Q.2 + 2 = n)

theorem pkR_isMem_iff (n d₁ : ℕ) (Q : ℕ × ℕ) : pkR_isMem n d₁ Q ↔
    (Q.1 ≤ d₁ ∧ 2 * d₁ + 2 * Q.2 + 2 ≤ n ∧ ¬ (Q.1 = d₁ ∧ Q.2 = 0) ∧ ¬ (Q.1 = 0 ∧ 2 * d₁ + 2 * Q.2 + 2 = n)) :=
  Iff.rfl

/-- The forms of R14(d), indexed by `ℕ × ℕ`: the sentinels `(d₁+1, 0)` ↦ `c⋆ = x`, `(d₁+2, 0)` ↦ `c⋆′`, a member `Q` ↦
`X_Q` (its chord). -/
noncomputable def pkR_r14f (n d₁ : ℕ) (Q : ℕ × ℕ) : MvPolynomial (ℕ × ℕ) ℚ :=
  if Q = (d₁ + 1, 0) then pkR_meshP n 1 (n - 1) else
    if Q = (d₁ + 2, 0) then pkR_meshP n (pkR_cstp n d₁).1 (pkR_cstp n d₁).2 else MvPolynomial.X (pkR_mchord d₁ Q)

theorem pkR_r14f_s1 (n d₁ : ℕ) (X : ℕ × ℕ → ℚ) :
    MvPolynomial.eval X (pkR_r14f n d₁ (d₁ + 1, 0)) = mesh n X 1 (n - 1) := by
  rw [pkR_r14f, ite_eq_left rfl, pkR_meshP_eval]

theorem pkR_r14f_s2 (n d₁ : ℕ) (X : ℕ × ℕ → ℚ) :
    MvPolynomial.eval X (pkR_r14f n d₁ (d₁ + 2, 0)) = mesh n X (pkR_cstp n d₁).1 (pkR_cstp n d₁).2 := by
  have h : ((d₁ + 2, 0) : ℕ × ℕ) ≠ (d₁ + 1, 0) := fun h => by
    have e : d₁ + 2 = d₁ + 1 := congrArg Prod.fst h
    omega
  rw [pkR_r14f, ite_eq_right h, ite_eq_left rfl, pkR_meshP_eval]

theorem pkR_r14f_mem (n d₁ : ℕ) {Q : ℕ × ℕ} (hQ : Q.1 ≤ d₁) (X : ℕ × ℕ → ℚ) :
    MvPolynomial.eval X (pkR_r14f n d₁ Q) = X (pkR_mchord d₁ Q) := by
  have h1 : Q ≠ (d₁ + 1, 0) := fun h => by
    have e : Q.1 = d₁ + 1 := congrArg Prod.fst h
    omega
  have h2 : Q ≠ (d₁ + 2, 0) := fun h => by
    have e : Q.1 = d₁ + 2 := congrArg Prod.fst h
    omega
  rw [pkR_r14f, ite_eq_right h1, ite_eq_right h2, MvPolynomial.eval_X]

theorem pkR_r14f_lin (n d₁ : ℕ) (Q : ℕ × ℕ) : pkR_Lin (pkR_r14f n d₁ Q) := by
  rw [pkR_r14f]
  split_ifs
  · exact pkR_meshP_lin _ _ _
  · exact pkR_meshP_lin _ _ _
  · exact pkR_lin_X _

/-- **R14(d)** (PREFORM-Res §4.5 (d)): [ProdDiv] on `W_q` with the forms `c⋆`, `c⋆′` and `X_Q` (`Q ∈ J`, members other
than `q`), pairwise non-proportional by (W-ind) and (G_W) (`pkR_Wind1/2`, `pkR_GW_Q`, `pkR_GW_star`, `pkR_GW_starp`,
`pkR_GW_pair`). A polynomial vanishing on each `W_q ∩ {form = 0}` is `c⋆ · c⋆′ · ∏_{Q ∈ J} X_Q · G` on `W_q`. -/
theorem pkR_R14d {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ i j : ℕ} (hi : i ≤ d₁) (hj : 2 * d₁ + 2 * j + 2 ≤ n)
    (hb : ¬ (i = d₁ ∧ j = 0)) (ha : ¬ (i = 0 ∧ 2 * d₁ + 2 * j + 2 = n)) (J : Finset (ℕ × ℕ))
    (hJ : ∀ Q ∈ J, pkR_isMem n d₁ Q ∧ Q ≠ (i, j)) (P : MvPolynomial (ℕ × ℕ) ℚ)
    (h1 : ∀ X : ℕ × ℕ → ℚ, pkR_W n d₁ (i, j) X → mesh n X 1 (n - 1) = 0 → MvPolynomial.eval X P = 0)
    (h2 : ∀ X : ℕ × ℕ → ℚ, pkR_W n d₁ (i, j) X → mesh n X (pkR_cstp n d₁).1 (pkR_cstp n d₁).2 = 0 →
      MvPolynomial.eval X P = 0)
    (h3 : ∀ Q ∈ J, ∀ X : ℕ × ℕ → ℚ, pkR_W n d₁ (i, j) X → X (pkR_mchord d₁ Q) = 0 → MvPolynomial.eval X P = 0) :
    ∃ G : MvPolynomial (ℕ × ℕ) ℚ, ∀ X : ℕ × ℕ → ℚ, pkR_W n d₁ (i, j) X →
      MvPolynomial.eval X P = mesh n X 1 (n - 1) * mesh n X (pkR_cstp n d₁).1 (pkR_cstp n d₁).2 *
        Finset.prod J (fun Q => X (pkR_mchord d₁ Q)) * MvPolynomial.eval X G := by
  have hJ1 : ∀ Q ∈ J, Q.1 ≤ d₁ := fun Q hQ => ((pkR_isMem_iff _ _ _).1 (hJ Q hQ).1).1
  have hs1 : ((d₁ + 1, 0) : ℕ × ℕ) ∉ insert ((d₁ + 2, 0) : ℕ × ℕ) J := by
    intro h
    rcases mem_insert.1 h with h | h
    · have e : d₁ + 1 = d₁ + 2 := congrArg Prod.fst h
      omega
    · have e : d₁ + 1 ≤ d₁ := hJ1 _ h
      omega
  have hs2 : ((d₁ + 2, 0) : ℕ × ℕ) ∉ J := by
    intro h
    have e : d₁ + 2 ≤ d₁ := hJ1 _ h
    omega
  -- the non-vanishing and non-proportionality witnesses
  have hmem : ∀ Q ∈ J, pkR_mchord d₁ Q ∈ oddDiagonals n ∧ pkR_mchord d₁ Q ≠ pkR_mchord d₁ (i, j) := by
    intro Q hQ
    obtain ⟨hm, hne⟩ := hJ Q hQ
    obtain ⟨m1, m2, m3, m4⟩ := (pkR_isMem_iff _ _ _).1 hm
    exact ⟨pkR_mchord_mem (i := Q.1) (j := Q.2) m1 m2 m3 m4, fun h => hne (pkR_mchord_inj h)⟩
  have wQ : ∀ Q ∈ J, ∃ X : ℕ × ℕ → ℚ, pkR_W n d₁ (i, j) X ∧ mesh n X 1 (n - 1) = 0 ∧
      mesh n X (pkR_cstp n d₁).1 (pkR_cstp n d₁).2 = 0 ∧ X (pkR_mchord d₁ Q) ≠ 0 :=
    fun Q hQ => pkR_GW_Q hE hn hi hj hb (hmem Q hQ).1 (hmem Q hQ).2
  obtain ⟨G, hG⟩ := pkR_prodDiv (pkR_W_sub n d₁ (i, j)) (pkR_r14f n d₁) (insert (d₁ + 1, 0) (insert (d₁ + 2, 0) J))
    (fun Q _ => pkR_r14f_lin n d₁ Q)
    (fun Q hQ => by
      rcases mem_insert.1 hQ with rfl | hQ'
      · obtain ⟨Y, hY, hY1, _⟩ := pkR_Wind2 hE hn hi hj hb ha
        exact ⟨Y, hY, by rw [pkR_r14f_s1]; exact hY1⟩
      · rcases mem_insert.1 hQ' with rfl | hQ''
        · obtain ⟨Y, hY, _, hY2⟩ := pkR_Wind1 hE hn hi hj hb ha
          exact ⟨Y, hY, by rw [pkR_r14f_s2]; exact hY2⟩
        · obtain ⟨Y, hY, _, _, hY3⟩ := wQ Q hQ''
          exact ⟨Y, hY, by rw [pkR_r14f_mem n d₁ (hJ1 Q hQ'')]; exact hY3⟩)
    (fun Q hQ Q' hQ' hne => by
      rcases mem_insert.1 hQ with rfl | hQa
      · rcases mem_insert.1 hQ' with rfl | hQb
        · exact absurd rfl hne
        · rcases mem_insert.1 hQb with rfl | hQc
          · obtain ⟨Y, hY, hY1, hY2⟩ := pkR_Wind1 hE hn hi hj hb ha
            exact ⟨Y, hY, by rw [pkR_r14f_s1]; exact hY1, by rw [pkR_r14f_s2]; exact hY2⟩
          · obtain ⟨Y, hY, hY1, _, hY3⟩ := wQ Q' hQc
            exact ⟨Y, hY, by rw [pkR_r14f_s1]; exact hY1, by rw [pkR_r14f_mem n d₁ (hJ1 Q' hQc)]; exact hY3⟩
      · rcases mem_insert.1 hQa with rfl | hQb
        · rcases mem_insert.1 hQ' with rfl | hQc
          · obtain ⟨Y, hY, hY1, hY2⟩ := pkR_Wind2 hE hn hi hj hb ha
            exact ⟨Y, hY, by rw [pkR_r14f_s2]; exact hY2, by rw [pkR_r14f_s1]; exact hY1⟩
          · rcases mem_insert.1 hQc with rfl | hQd
            · exact absurd rfl hne
            · obtain ⟨Y, hY, _, hY2, hY3⟩ := wQ Q' hQd
              exact ⟨Y, hY, by rw [pkR_r14f_s2]; exact hY2, by rw [pkR_r14f_mem n d₁ (hJ1 Q' hQd)]; exact hY3⟩
        · obtain ⟨m, hne1⟩ := hJ Q hQb
          obtain ⟨m1, m2, m3, m4⟩ := (pkR_isMem_iff _ _ _).1 m
          rcases mem_insert.1 hQ' with rfl | hQc
          · obtain ⟨Y, hY, hY1, hY2⟩ := pkR_GW_star hE hn hi hj hb ha (hmem Q hQb).1 (hmem Q hQb).2
            exact ⟨Y, hY, by rw [pkR_r14f_mem n d₁ m1]; exact hY1, by rw [pkR_r14f_s1]; exact hY2⟩
          · rcases mem_insert.1 hQc with rfl | hQd
            · obtain ⟨Y, hY, hY1, hY2⟩ := pkR_GW_starp hE hn hi hj hb ha (hmem Q hQb).1 (hmem Q hQb).2
              exact ⟨Y, hY, by rw [pkR_r14f_mem n d₁ m1]; exact hY1, by rw [pkR_r14f_s2]; exact hY2⟩
            · obtain ⟨m', hne2⟩ := hJ Q' hQd
              obtain ⟨k1, k2, k3, k4⟩ := (pkR_isMem_iff _ _ _).1 m'
              obtain ⟨Y, hY, hY1, hY2⟩ := pkR_GW_pair (i := Q.1) (j := Q.2) (k := Q'.1) (l := Q'.2) hE hn hi hj hb ha
                m1 m2 m3 m4 k1 k2 k3 k4 hne1 hne2 (fun h => hne (Prod.ext (congrArg Prod.fst h).symm
                  (congrArg Prod.snd h).symm))
              exact ⟨Y, hY, by rw [pkR_r14f_mem n d₁ m1]; exact hY1, by rw [pkR_r14f_mem n d₁ k1]; exact hY2⟩)
    P (fun Q hQ X hX hXQ => by
      have hX' : pkR_W n d₁ (i, j) X := hX
      rcases mem_insert.1 hQ with rfl | hQa
      · rw [pkR_r14f_s1] at hXQ
        exact h1 X hX' hXQ
      · rcases mem_insert.1 hQa with rfl | hQb
        · rw [pkR_r14f_s2] at hXQ
          exact h2 X hX' hXQ
        · rw [pkR_r14f_mem n d₁ (hJ1 Q hQb)] at hXQ
          exact h3 Q hQb X hX' hXQ)
  refine ⟨G, fun X hX => ?_⟩
  rw [hG X hX, prod_insert hs1, prod_insert hs2, map_mul, map_mul, map_prod, pkR_r14f_s1, pkR_r14f_s2,
    prod_congr rfl (fun Q hQ => pkR_r14f_mem n d₁ (hJ1 Q hQ) X)]
  ring

/-- **The ¬q [ResNum] form** (PREFORM-Res §4.5, R14(c) in numerator form; I3 at `K = {q, Q}`): for distinct mixed `q`,
`Q`, the ¬q numerator is `X_Q · E + (child ¬q numerators) · cross^{¬q}_Q`, the children in the `NP_residue`
labelling with the pulled-back banned sets. -/
theorem pkR_resNumK {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {q Q : ℕ × ℕ} (hq : q ∈ oddDiagonals N)
    (hQ : Q ∈ oddDiagonals N) (hne : q ≠ Q) :
    ∃ E : MvPolynomial (ℕ × ℕ) ℚ, pkR_b_NP ℚ N {q} = MvPolynomial.X Q * E +
      MvPolynomial.rename (relab N Q.1) (pkR_b_NP ℚ (Q.2 - Q.1 + 1) (pkR_b_pull N Q.1 (Q.2 - Q.1 + 1) {q})) *
        MvPolynomial.rename (relab N Q.2)
          (pkR_b_NP ℚ (N - Q.2 + Q.1 + 1) (pkR_b_pull N Q.2 (N - Q.2 + Q.1 + 1) {q})) *
        pkR_b_cross ℚ N {q} Q := by
  have hK : ({q, Q} : Finset (ℕ × ℕ)).erase Q = {q} := by
    ext x
    simp only [mem_erase, mem_insert, mem_singleton]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact h2
      · exact absurd h2 h1
    · intro h
      exact ⟨by rw [h]; exact hne, Or.inl h⟩
  have hsub : ({q, Q} : Finset (ℕ × ℕ)) ⊆ oddDiagonals N := by
    intro x hx
    rcases mem_insert.1 hx with rfl | hx'
    · exact hq
    · rw [mem_singleton.1 hx']
      exact hQ
  have h := pkR_b_I3num (R := ℚ) hN hE hsub (C := Q) (mem_insert_of_mem (mem_singleton_self Q))
  rw [hK] at h
  exact ⟨_, h⟩

/-! ### pkgRes sub-wave c2: R10 Ψ — the W-trick (iii) and the polynomial core of (iv) -/

/-- `Λ^{q} ⊆ W_q`. -/
theorem pkR_lam_W {n d₁ : ℕ} {q : ℕ × ℕ} {X : ℕ × ℕ → ℚ} (hX : pkR_lam n d₁ {q} X) : pkR_W n d₁ q X := by
  obtain ⟨h1, _, h3⟩ := (pkR_lam_iff _ _ _ _).1 hX
  exact (pkR_W_iff _ _ _ _).2 ⟨fun a ha b hb e1 e2 e3 e4 _ => h1 a ha b hb e1 e2 e3 e4,
    fun t ht => h3 q (mem_singleton_self q) t ht⟩

/-- **R10(iii) / the W-trick** (PREFORM-Res §4.4 (iii)): a polynomial vanishing on `W_q ∩ {c⋆ = 0}` and on
`W_q ∩ {c⋆′ = 0}` (for the ¬q numerator: R14(a)/(b) + R5) is `x² · F₃` on `Λ^{q}` (`R14(d)` with `J = ∅`, then
`c⋆ = c⋆′ = x` on `Λ`). -/
theorem pkR_R10iii {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ i j : ℕ} (hi : i ≤ d₁) (hj : 2 * d₁ + 2 * j + 2 ≤ n)
    (hb : ¬ (i = d₁ ∧ j = 0)) (ha : ¬ (i = 0 ∧ 2 * d₁ + 2 * j + 2 = n)) (P : MvPolynomial (ℕ × ℕ) ℚ)
    (h1 : ∀ X : ℕ × ℕ → ℚ, pkR_W n d₁ (i, j) X → mesh n X 1 (n - 1) = 0 → MvPolynomial.eval X P = 0)
    (h2 : ∀ X : ℕ × ℕ → ℚ, pkR_W n d₁ (i, j) X → mesh n X (pkR_cstp n d₁).1 (pkR_cstp n d₁).2 = 0 →
      MvPolynomial.eval X P = 0) :
    ∃ F₃ : MvPolynomial (ℕ × ℕ) ℚ, ∀ X : ℕ × ℕ → ℚ, pkR_lam n d₁ {(i, j)} X →
      MvPolynomial.eval X P = mesh n X 1 (n - 1) * mesh n X 1 (n - 1) * MvPolynomial.eval X F₃ := by
  obtain ⟨G, hG⟩ := pkR_R14d hE hn hi hj hb ha ∅ (fun Q hQ => by simp at hQ) P h1 h2
    (fun Q hQ => by simp at hQ)
  refine ⟨G, fun X hX => ?_⟩
  rw [hG X (pkR_lam_W hX), prod_empty, mul_one, ← ((pkR_lam_iff _ _ _ _).1 hX).2.1]

/-- **R10(iv), polynomial core** (the step "combine with [Const9]" of PREFORM-Res §4.4, done without rational functions).
`V = Λ`, `V₂ = Λ^{q} ⊆ V`, `x` the tile `c⋆`, `ℓ = X_C` (C the chord of `q`). Inputs: the C-split `NP_n = X_C · M` on `Λ`
(I3 at `K = {C}` with the A-child `= −X_C`, R10(i)); [Const9] at `n` (`NP_n = x·F₁` on `Λ`, `F₁ = c·X_C·D` on `Λ₀`,
`oddDen = X_C · D`); on `Λ^{q}`: `M = x·(x·F₃ − F₁′·cr)` (R10(iii) for the ¬C part, [Region](ii) + [Const9] at `n − 2` for
the B-child, `cr = crossProd_C`) and `F₁′ = c′·D′` on `Λ^{q}₀`. Output: `c·D = −c′·D′·cr` on `Λ^{q}₀`. The division
steps: `M = 0` on `Λ₀` ([Prime], `X_C ≢ 0` on `Λ₀`), so `M = x·M′` ([Div]), `F₁ = X_C·M′` ([Prime]), `M′ = c·D` on `Λ₀`
([Prime]); on `Λ^{q}`, `M′ = x·F₃ − F₁′·cr` ([Prime]). -/
theorem pkR_psi_core {σ : Type*} {V V₂ : Set (σ → ℚ)} (hV : pkR_Sub V) (hV₂ : pkR_Sub V₂) (h21 : V₂ ⊆ V)
    {x ℓ : MvPolynomial σ ℚ} (hx : pkR_Lin x)
    {NPn F₁ M D F₃ F₁' D' cr : MvPolynomial σ ℚ} {c c' : ℚ}
    (hsplit : ∀ X ∈ V, MvPolynomial.eval X NPn = MvPolynomial.eval X ℓ * MvPolynomial.eval X M)
    (hF₁ : ∀ X ∈ V, MvPolynomial.eval X NPn = MvPolynomial.eval X x * MvPolynomial.eval X F₁)
    (hc : ∀ X ∈ V, MvPolynomial.eval X x = 0 →
      MvPolynomial.eval X F₁ = c * (MvPolynomial.eval X ℓ * MvPolynomial.eval X D))
    (hM₂ : ∀ X ∈ V₂, MvPolynomial.eval X M = MvPolynomial.eval X x *
      (MvPolynomial.eval X x * MvPolynomial.eval X F₃ - MvPolynomial.eval X F₁' * MvPolynomial.eval X cr))
    (hc' : ∀ X ∈ V₂, MvPolynomial.eval X x = 0 → MvPolynomial.eval X F₁' = c' * MvPolynomial.eval X D')
    (wx : ∃ w ∈ V₂, MvPolynomial.eval w x ≠ 0)
    (wℓ : ∃ w ∈ V, MvPolynomial.eval w x = 0 ∧ MvPolynomial.eval w ℓ ≠ 0) :
    ∀ X ∈ V₂, MvPolynomial.eval X x = 0 →
      c * MvPolynomial.eval X D = -(c' * MvPolynomial.eval X D' * MvPolynomial.eval X cr) := by
  have hV0 := pkR_sub_inter hV hx
  obtain ⟨w₂, hw₂, hw₂x⟩ := wx
  obtain ⟨wl, hwl, hwlx, hwlℓ⟩ := wℓ
  have hwV : ∃ w ∈ V, MvPolynomial.eval w x ≠ 0 := ⟨w₂, h21 hw₂, hw₂x⟩
  have hwl0 : ∃ w ∈ {X | X ∈ V ∧ MvPolynomial.eval X x = 0}, MvPolynomial.eval w ℓ ≠ 0 := ⟨wl, ⟨hwl, hwlx⟩, hwlℓ⟩
  -- M = 0 on Λ₀
  have hM0 := pkR_prime hV0 hwl0 (G := M) (fun X hX => by
    rw [← hsplit X hX.1, hF₁ X hX.1, hX.2, zero_mul])
  -- M = x·M′ on Λ
  obtain ⟨M', hM'⟩ := pkR_div hV hx hwV M (fun X hX hx0 => hM0 X ⟨hX, hx0⟩)
  -- F₁ = X_C·M′ on Λ
  have hF := pkR_prime hV hwV (G := F₁ - ℓ * M') (fun X hX => by
    rw [map_sub, map_mul, mul_sub, ← hF₁ X hX, hsplit X hX, hM' X hX]
    ring)
  -- M′ = c·D on Λ₀
  have hMc := pkR_prime hV0 hwl0 (G := M' - MvPolynomial.C c * D) (fun X hX => by
    have e := hF X hX.1
    rw [map_sub, map_mul, sub_eq_zero, hc X hX.1 hX.2] at e
    rw [map_sub, map_mul, MvPolynomial.eval_C, mul_sub, ← e]
    ring)
  -- M′ = x·F₃ − F₁′·cr on Λ^{q}
  have hM2' := pkR_prime hV₂ ⟨w₂, hw₂, hw₂x⟩ (G := M' - (x * F₃ - F₁' * cr)) (fun X hX => by
    have e := hM₂ X hX
    rw [hM' X (h21 hX)] at e
    rw [map_sub, map_sub, map_mul, map_mul, mul_sub, e]
    ring)
  intro X hX hx0
  have e1 := hMc X ⟨h21 hX, hx0⟩
  have e2 := hM2' X hX
  rw [map_sub, map_mul, MvPolynomial.eval_C, sub_eq_zero] at e1
  rw [map_sub, map_sub, map_mul, map_mul, hx0, sub_eq_zero, e1, hc' X hX hx0] at e2
  rw [e2]
  ring

/-- **R10(iv), non-vanishing**: with a point of `Λ^{q}₀` where `D′·cr ≠ 0` ([Avoid] with (G^I)), `c′ ≠ 0 ⇒ c ≠ 0`. -/
theorem pkR_psi_ne {σ : Type*} {V₂ : Set (σ → ℚ)} {x D D' cr : MvPolynomial σ ℚ} {c c' : ℚ}
    (h : ∀ X ∈ V₂, MvPolynomial.eval X x = 0 →
      c * MvPolynomial.eval X D = -(c' * MvPolynomial.eval X D' * MvPolynomial.eval X cr))
    (wp : ∃ w ∈ V₂, MvPolynomial.eval w x = 0 ∧ MvPolynomial.eval w D' * MvPolynomial.eval w cr ≠ 0)
    (hc' : c' ≠ 0) : c ≠ 0 := by
  intro h0
  obtain ⟨w, hw, hwx, hwne⟩ := wp
  have e := h w hw hwx
  rw [h0, zero_mul, eq_comm, neg_eq_zero, mul_assoc] at e
  exact hwne ((mul_eq_zero.1 e).resolve_left hc')

/-- `NP_4 = −(X₁₃ + X₂₄)` (no odd diagonals at `n = 4`; base `NLSM_four`). -/
theorem pkR_NP4 (Y : ℕ × ℕ → ℚ) : MvPolynomial.eval Y (NP ℚ 4) = -(Y (1, 3) + Y (2, 4)) := by
  have h0 : oddDiagonals 4 = ∅ := by decide
  have hY : ∀ d ∈ oddDiagonals 4, Y d ≠ 0 := by
    rw [h0]
    intro d hd
    simp at hd
  rw [show NP ℚ 4 = AP ℚ 4 (4 - 2) from rfl, AP_eval 4 (4 - 2) Y hY, h0, prod_empty, mul_one]
  have e : shiftCoeff 4 ((4 - 2 : ℕ) : ℤ) Y = NLSM 4 Y := by
    rw [show ((4 - 2 : ℕ) : ℤ) = ((4 : ℕ) : ℤ) - 2 by norm_num]
    rfl
  rw [e, NLSM_four]

/-- The chord `C = (2d₁ − 1, 2d₁ + 2)` of `b′ = (d₁ − 1, 0)` is mixed. -/
theorem pkR_R10_C {n d₁ : ℕ} (hn : 6 ≤ n) (hd1 : 1 ≤ d₁) (hd : 2 * d₁ + 2 ≤ n) :
    ((2 * d₁ - 1, 2 * d₁ + 2) : ℕ × ℕ) ∈ oddDiagonals n := by
  refine mem_filter.2 ⟨mem_diagonals.2 ⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> (try dsimp only) <;> omega

/-- **R10(i), numerator form on all of `Λ^I`**: the A-child of `C` (the 4-gon `[2d₁−1 .. 2d₁+2]`) has numerator `−X_C`. -/
theorem pkR_R10_A {n : ℕ} (hn : 6 ≤ n) {d₁ : ℕ} (hd1 : 1 ≤ d₁) (hd : 2 * d₁ + 2 ≤ n) {I : Finset (ℕ × ℕ)}
    {X : ℕ × ℕ → ℚ} (hX : pkR_lam n d₁ I X) :
    MvPolynomial.eval X (MvPolynomial.rename (relab n (2 * d₁ - 1)) (NP ℚ (2 * d₁ + 2 - (2 * d₁ - 1) + 1))) =
      -X (2 * d₁ - 1, 2 * d₁ + 2) := by
  have hQ := pkR_R10_C hn hd1 hd
  have h4 : 2 * d₁ + 2 - (2 * d₁ - 1) + 1 = 4 := by omega
  have e1 : X (relab n (2 * d₁ - 1) (1, 3)) = planar n X (2 * d₁ - 1) (2 * d₁ + 1) := by
    rw [← pkR_relab1 hQ X (1, 3) (by rw [h4]; decide)]
    show planar n X (1 + (2 * d₁ - 1) - 1) (3 + (2 * d₁ - 1) - 1) = _
    rw [show 1 + (2 * d₁ - 1) - 1 = 2 * d₁ - 1 by omega, show 3 + (2 * d₁ - 1) - 1 = 2 * d₁ + 1 by omega]
  have e2 : X (relab n (2 * d₁ - 1) (2, 4)) = planar n X (2 * d₁) (2 * d₁ + 2) := by
    rw [← pkR_relab1 hQ X (2, 4) (by rw [h4]; decide)]
    show planar n X (2 + (2 * d₁ - 1) - 1) (4 + (2 * d₁ - 1) - 1) = _
    rw [show 2 + (2 * d₁ - 1) - 1 = 2 * d₁ by omega, show 4 + (2 * d₁ - 1) - 1 = 2 * d₁ + 2 by omega]
  have eC : planar n X (2 * d₁ - 1) (2 * d₁ + 2) = X (2 * d₁ - 1, 2 * d₁ + 2) := by
    rw [pkR_planar_def, vtx_of_mem (n := n) (i := 2 * d₁ - 1) (by omega) (by omega),
      vtx_of_mem (n := n) (i := 2 * d₁ + 2) (by omega) (by omega), min_eq_left (show 2 * d₁ - 1 ≤ 2 * d₁ + 2 by omega),
      max_eq_right (show 2 * d₁ - 1 ≤ 2 * d₁ + 2 by omega)]
    exact ite_eq_left (mem_filter.1 hQ).1
  rw [h4, MvPolynomial.eval_rename, pkR_NP4, Function.comp_apply, Function.comp_apply, e1, e2,
    pkR_R10i hn hd1 hd hX, eC]

/-- **The C-split on all of `Λ^I`** (I3 at `K = {C}` = `pkR_b_res1`, with R10(i)): `NP_n = X_C · M`,
`M = NP^{¬C} − NP_B · cross_C` (the input `hsplit` of `pkR_psi_core`). -/
theorem pkR_R10_split {n : ℕ} (hn : 6 ≤ n) (hE : n % 2 = 0) {d₁ : ℕ} (hd1 : 1 ≤ d₁) (hd : 2 * d₁ + 2 ≤ n)
    {I : Finset (ℕ × ℕ)} {X : ℕ × ℕ → ℚ} (hX : pkR_lam n d₁ I X) :
    MvPolynomial.eval X (NP ℚ n) = X (2 * d₁ - 1, 2 * d₁ + 2) *
      MvPolynomial.eval X (pkR_b_NP ℚ n {(2 * d₁ - 1, 2 * d₁ + 2)} -
        MvPolynomial.rename (relab n (2 * d₁ + 2)) (NP ℚ (n - (2 * d₁ + 2) + (2 * d₁ - 1) + 1)) *
          crossProd ℚ n (2 * d₁ - 1, 2 * d₁ + 2)) := by
  have hQ := pkR_R10_C hn hd1 hd
  have e := congrArg (MvPolynomial.eval X) (pkR_b_res1 (R := ℚ) (show 4 ≤ n by omega) hE hQ)
  dsimp only at e
  rw [map_add, map_mul, map_mul, map_mul, MvPolynomial.eval_X, pkR_R10_A hn hd1 hd hX] at e
  rw [e, map_sub, map_mul]
  ring

theorem pkR_mesh4 (X : ℕ × ℕ → ℚ) : mesh 4 X 1 (4 - 1) = X (1, 3) + X (2, 4) := by
  have p13 : planar 4 X 1 3 = X (1, 3) := by rw [pkR_planar_def]; exact ite_eq_left (by decide)
  have p24 : planar 4 X 2 4 = X (2, 4) := by rw [pkR_planar_def]; exact ite_eq_left (by decide)
  have p14 : planar 4 X 1 4 = 0 := by rw [pkR_planar_def]; exact ite_eq_right (by decide)
  have p23 : planar 4 X 2 3 = 0 := by rw [pkR_planar_def]; exact ite_eq_right (by decide)
  rw [pkR_mesh_def, show 4 - 1 = 3 from rfl, show 1 + 1 = 2 from rfl, show 3 + 1 = 4 from rfl, p13, p24, p14, p23]
  ring

/-- **R10 base** `c(4) = −1`: any [Const9] data at `n = 4` has constant `−1`. -/
theorem pkR_psi_four {F₁ : MvPolynomial (ℕ × ℕ) ℚ} {c : ℚ}
    (hF : ∀ X : ℕ × ℕ → ℚ, pkR_lam 4 0 ∅ X →
      MvPolynomial.eval X (NP ℚ 4) = mesh 4 X 1 (4 - 1) * MvPolynomial.eval X F₁)
    (hc : ∀ X : ℕ × ℕ → ℚ, pkR_lam 4 0 ∅ X → mesh 4 X 1 (4 - 1) = 0 →
      MvPolynomial.eval X F₁ = c * MvPolynomial.eval X (oddDen ℚ 4)) : c = -1 := by
  have hV := pkR_lam_sub 4 0 ∅
  obtain ⟨hw, hwx⟩ := pkR_xwit (n := 4) rfl le_rfl 0 (by norm_num)
  have hG := pkR_prime hV ⟨pkR_chA 4 0, hw, by rw [pkR_meshP_eval, hwx]; norm_num⟩ (G := F₁ + 1) (fun X hX => by
    have e := hF X hX
    rw [pkR_NP4, pkR_mesh4] at e
    rw [pkR_meshP_eval, map_add, map_one, pkR_mesh4, mul_add, ← e]
    ring)
  have h0 : pkR_lam 4 0 ∅ (fun _ => (0 : ℚ)) := hV.1
  have e1 := hG _ hV.1
  have e2 := hc _ h0 (pkR_mesh_zero 4 1 (4 - 1))
  have hod : oddDiagonals 4 = ∅ := by decide
  rw [pkR_eval_oddDen, hod, prod_empty, mul_one] at e2
  rw [map_add, map_one, e2] at e1
  linarith

/-! ### pkgRes sub-wave c2, third dispatch (c2c): the B-child rotation bridge

The B-child of the chord `C = (p, p + 3)` in the `relab n (p + 3)` labelling (the list `[p+3, …, n, 1, …, p]`) is the
region list `f = [1, …, p] ++ [p+3, …, n]` of [Region](ii) rotated by `n − 2 − p` legs. `NP` is rotation invariant
(3c-b `NLSM_rot`), so the child numerator can be read at the rotated point `X ∘ (relab n (p+3) ∘ rot^[n−2−p])`, which
agrees with the region point `pkR_subX n f X` on every child diagonal. -/

/-- `vtx` absorbs an inner `vtx`. -/
theorem pkR_vtx_add {m : ℕ} (hm : 1 ≤ m) (u k : ℕ) : vtx m (vtx m u + k) = vtx m (u + k) := by
  unfold vtx
  congr 1
  have e1 : (u + m - 1) % m + 1 + k + m - 1 = (u + m - 1) % m + (k + m) := by omega
  have e2 : u + k + m - 1 = (u + m - 1) + k := by omega
  rw [e1, e2, Nat.add_mod ((u + m - 1) % m) (k + m) m, Nat.mod_mod, Nat.add_mod_right, ← Nat.add_mod]

theorem pkR_npair_comm (m u v : ℕ) : npair m u v = npair m v u := by
  show (min (vtx m u) (vtx m v), max (vtx m u) (vtx m v)) = (min (vtx m v) (vtx m u), max (vtx m v) (vtx m u))
  rw [min_comm, max_comm]

theorem pkR_npair_vtx {m : ℕ} (hm : 1 ≤ m) (u v k : ℕ) :
    npair m (vtx m u + k) (vtx m v + k) = npair m (u + k) (v + k) := by
  show (min (vtx m (vtx m u + k)) (vtx m (vtx m v + k)), max (vtx m (vtx m u + k)) (vtx m (vtx m v + k))) =
    (min (vtx m (u + k)) (vtx m (v + k)), max (vtx m (u + k)) (vtx m (v + k)))
  rw [pkR_vtx_add hm, pkR_vtx_add hm]

/-- The `k`-fold rotation of a diagonal shifts both labels by `k`. -/
theorem pkR_rot_iter {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    ∀ d ∈ diagonals m, (rot m)^[k] d = npair m (d.1 + k) (d.2 + k) := by
  induction k with
  | zero =>
    intro d hd
    rw [mem_diagonals] at hd
    show d = (min (vtx m (d.1 + 0)) (vtx m (d.2 + 0)), max (vtx m (d.1 + 0)) (vtx m (d.2 + 0)))
    rw [add_zero, add_zero, vtx_of_mem (by omega) (by omega), vtx_of_mem (by omega) (by omega),
      min_eq_left (by omega), max_eq_right (by omega)]
  | succ k ih =>
    intro d hd
    rw [Function.iterate_succ_apply, ih (rot m d) (rot_mem hm hd)]
    show npair m (min (vtx m (d.1 + 1)) (vtx m (d.2 + 1)) + k) (max (vtx m (d.1 + 1)) (vtx m (d.2 + 1)) + k) = _
    rw [show d.1 + (k + 1) = d.1 + 1 + k by omega, show d.2 + (k + 1) = d.2 + 1 + k by omega]
    rcases le_total (vtx m (d.1 + 1)) (vtx m (d.2 + 1)) with h | h
    · rw [min_eq_left h, max_eq_right h, pkR_npair_vtx hm]
    · rw [min_eq_right h, max_eq_left h, pkR_npair_comm, pkR_npair_vtx hm]

/-- Rotation keeps the parity class of a diagonal (`m` even). -/
theorem pkR_rot_par {m : ℕ} (hm : 4 ≤ m) (hE : m % 2 = 0) {d : ℕ × ℕ} (hd : d ∈ diagonals m) :
    (rot m d ∈ oddDiagonals m ↔ d ∈ oddDiagonals m) := by
  have hdd := mem_diagonals.1 hd
  have e : rot m d = (min (vtx m (d.1 + 1)) (vtx m (d.2 + 1)), max (vtx m (d.1 + 1)) (vtx m (d.2 + 1))) := rfl
  have v1 := pkR_b_vtx2 (N := m) (u := d.1 + 1) (by omega) (by omega)
  have v2 := pkR_b_vtx2 (N := m) (u := d.2 + 1) (by omega) (by omega)
  have hr := rot_mem (show 1 ≤ m by omega) hd
  constructor
  · intro h
    refine mem_filter.2 ⟨hd, ?_⟩
    have h2 := (mem_filter.1 h).2
    rw [e] at h2
    dsimp only at h2
    omega
  · intro h
    refine mem_filter.2 ⟨hr, ?_⟩
    have h2 := (mem_filter.1 h).2
    rw [e]
    dsimp only
    omega

/-- **`NP` is invariant under the one-step rotation** (3c-b `NLSM_rot` and `AP_eval` where every odd diagonal is
non-zero, then `line_bridge` across the poles). -/
theorem pkR_NP_rot {m : ℕ} (hm : 4 ≤ m) (hE : m % 2 = 0) (Y : ℕ × ℕ → ℚ) :
    MvPolynomial.eval (Y ∘ rot m) (NP ℚ m) = MvPolynomial.eval Y (NP ℚ m) := by
  have eS : ∀ y : ℕ × ℕ → ℚ, shiftCoeff m ((m - 2 : ℕ) : ℤ) y = NLSM m y := fun y => by
    rw [show ((m - 2 : ℕ) : ℤ) = (m : ℤ) - 2 by omega]
    rfl
  have key : ∀ x ∈ (Set.univ : Set (ℕ × ℕ → ℚ)), MvPolynomial.eval x (oddDen ℚ m) ≠ 0 →
      MvPolynomial.eval x (MvPolynomial.rename (rot m) (NP ℚ m) - NP ℚ m) = 0 := by
    intro x _ hx
    rw [pkR_eval_oddDen] at hx
    have hx' : ∀ d ∈ oddDiagonals m, x d ≠ 0 := fun d hd => (Finset.prod_ne_zero_iff.1 hx) d hd
    have hr : ∀ d ∈ oddDiagonals m, (x ∘ rot m) d ≠ 0 := fun d hd =>
      hx' _ ((pkR_rot_par hm hE (mem_filter.1 hd).1).2 hd)
    have hp : Finset.prod (oddDiagonals m) (fun d => (x ∘ rot m) d) = Finset.prod (oddDiagonals m) (fun d => x d) :=
      Finset.prod_bij (fun d _ => rot m d) (fun d hd => (pkR_rot_par hm hE (mem_filter.1 hd).1).2 hd)
        (fun a ha b hb h => rot_inj (by omega) (mem_filter.1 ha).1 (mem_filter.1 hb).1 h)
        (fun d hd => by
          obtain ⟨d0, hd0, h⟩ := rot_surj (show 1 ≤ m by omega) (mem_filter.1 hd).1
          exact ⟨d0, (pkR_rot_par hm hE hd0).1 (h ▸ hd), h⟩)
        (fun d _ => rfl)
    rw [map_sub, MvPolynomial.eval_rename, show NP ℚ m = AP ℚ m (m - 2) from rfl,
      AP_eval m (m - 2) (x ∘ rot m) hr, AP_eval m (m - 2) x hx', eS, eS, NLSM_rot hm hE, hp, sub_self]
  have hz := line_bridge (Set.univ : Set (ℕ × ℕ → ℚ)) (fun _ _ _ _ _ => Set.mem_univ _)
    (MvPolynomial.rename (rot m) (NP ℚ m) - NP ℚ m) (oddDen ℚ m) (w := fun _ => (1 : ℚ)) (Set.mem_univ _)
    (by rw [pkR_eval_oddDen, prod_const_one]; exact one_ne_zero) key Y (Set.mem_univ _)
  rw [map_sub, MvPolynomial.eval_rename, sub_eq_zero] at hz
  exact hz

/-- `NP` is invariant under every iterated rotation. -/
theorem pkR_NP_rotk {m : ℕ} (hm : 4 ≤ m) (hE : m % 2 = 0) (k : ℕ) (Y : ℕ × ℕ → ℚ) :
    MvPolynomial.eval (Y ∘ (rot m)^[k]) (NP ℚ m) = MvPolynomial.eval Y (NP ℚ m) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ, ← Function.comp_assoc, pkR_NP_rot hm hE, ih]

/-- **The rotation bridge, on labels**: on a child diagonal `(a, b)` of the `(n − 2)`-gon, the `relab n (p + 3)`
chord of the `(n − 2 − p)`-rotated diagonal is the region chord `(f a, f b)`, `f k = k` (`k ≤ p`), `k + 2` (`k > p`). -/
theorem pkR_rotB_pair {n p : ℕ} (hp : 1 ≤ p) (hpn : p + 3 ≤ n) {a b : ℕ} (hd : (a, b) ∈ diagonals (n - 2)) :
    relab n (p + 3) (npair (n - 2) (a + (n - 2 - p)) (b + (n - 2 - p))) =
      (if a ≤ p then a else a + 2, if b ≤ p then b else b + 2) := by
  rw [mem_diagonals] at hd
  dsimp only at hd
  obtain ⟨u, hu⟩ : ∃ u, u = vtx (n - 2) (a + (n - 2 - p)) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = vtx (n - 2) (b + (n - 2 - p)) := ⟨_, rfl⟩
  have hu' := pkR_b_vtx2 (N := n - 2) (u := a + (n - 2 - p)) (by omega) (by omega)
  have hv' := pkR_b_vtx2 (N := n - 2) (u := b + (n - 2 - p)) (by omega) (by omega)
  rw [← hu] at hu'
  rw [← hv] at hv'
  have e : npair (n - 2) (a + (n - 2 - p)) (b + (n - 2 - p)) = (min u v, max u v) := by rw [hu, hv]; rfl
  rw [e]
  obtain ⟨fa, hfa⟩ : ∃ fa, fa = (if a ≤ p then a else a + 2) := ⟨_, rfl⟩
  obtain ⟨fb, hfb⟩ : ∃ fb, fb = (if b ≤ p then b else b + 2) := ⟨_, rfl⟩
  have hfa' : (a ≤ p ∧ fa = a) ∨ (p < a ∧ fa = a + 2) := by rw [hfa]; split_ifs <;> omega
  have hfb' : (b ≤ p ∧ fb = b) ∨ (p < b ∧ fb = b + 2) := by rw [hfb]; split_ifs <;> omega
  rw [← hfa, ← hfb]
  have eU : vtx n (u + (p + 3) - 1) = fa := by
    have w := pkR_b_vtx2 (N := n) (u := u + (p + 3) - 1) (by omega) (by omega)
    omega
  have eV : vtx n (v + (p + 3) - 1) = fb := by
    have w := pkR_b_vtx2 (N := n) (u := v + (p + 3) - 1) (by omega) (by omega)
    omega
  show (min (vtx n (min u v + (p + 3) - 1)) (vtx n (max u v + (p + 3) - 1)),
    max (vtx n (min u v + (p + 3) - 1)) (vtx n (max u v + (p + 3) - 1))) = (fa, fb)
  rcases le_total u v with h | h
  · rw [min_eq_left h, max_eq_right h, eU, eV, min_eq_left (by omega), max_eq_right (by omega)]
  · rw [min_eq_right h, max_eq_left h, eU, eV, min_eq_right (by omega), max_eq_left (by omega)]

/-- The rotated B-child point agrees with the region point on every child diagonal. -/
theorem pkR_rotB_eval {n p : ℕ} (hp : 1 ≤ p) (hpn : p + 3 ≤ n) (X : ℕ × ℕ → ℚ) :
    ∀ d ∈ diagonals (n - 2), (X ∘ (relab n (p + 3) ∘ (rot (n - 2))^[n - 2 - p])) d =
      pkR_subX n (fun k => if k ≤ p then k else k + 2) X d := by
  rintro ⟨a, b⟩ hd
  have hdd := mem_diagonals.1 hd
  dsimp only at hdd
  show X (relab n (p + 3) ((rot (n - 2))^[n - 2 - p] (a, b))) =
    planar n X (if a ≤ p then a else a + 2) (if b ≤ p then b else b + 2)
  rw [pkR_rot_iter (by omega) _ (a, b) hd]
  dsimp only
  rw [pkR_rotB_pair hp hpn hd]
  obtain ⟨fa, hfa⟩ : ∃ fa, fa = (if a ≤ p then a else a + 2) := ⟨_, rfl⟩
  obtain ⟨fb, hfb⟩ : ∃ fb, fb = (if b ≤ p then b else b + 2) := ⟨_, rfl⟩
  have hfa' : (a ≤ p ∧ fa = a) ∨ (p < a ∧ fa = a + 2) := by rw [hfa]; split_ifs <;> omega
  have hfb' : (b ≤ p ∧ fb = b) ∨ (p < b ∧ fb = b + 2) := by rw [hfb]; split_ifs <;> omega
  rw [← hfa, ← hfb, planar_of_mem X (by omega) (by omega) (by omega),
    ite_eq_left (by rw [mem_diagonals]; dsimp only; omega)]


end PiZ
