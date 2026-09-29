import PionCompleteness.C9

namespace PiZ

open Finset R12P1 R12P4A R12P3 R12P3C

/-! ### G3: R5 (d) and R6 for a general banned set (crossing members allowed) -/

/-- Iterated [Prime] over a finset of forms. -/
theorem pkR_d2_primeFin {σ ι : Type*} [DecidableEq ι] {V : Set (σ → ℚ)} (hV : pkR_Sub V)
    (ℓ : ι → MvPolynomial σ ℚ) (s : Finset ι) (hw : ∀ j ∈ s, ∃ w ∈ V, MvPolynomial.eval w (ℓ j) ≠ 0)
    {G : MvPolynomial σ ℚ} (h : ∀ x ∈ V, (∏ j ∈ s, MvPolynomial.eval x (ℓ j)) * MvPolynomial.eval x G = 0) :
    ∀ x ∈ V, MvPolynomial.eval x G = 0 := by
  induction s using Finset.induction_on generalizing G with
  | empty =>
    intro x hx
    have e := h x hx
    rw [prod_empty, one_mul] at e
    exact e
  | insert a s ha ih =>
    have h2 : ∀ x ∈ V, MvPolynomial.eval x (ℓ a * G) = 0 :=
      ih (fun j hj => hw j (mem_insert_of_mem hj)) (fun x hx => by
        have e := h x hx
        rw [prod_insert ha] at e
        rw [map_mul]
        linear_combination e)
    exact pkR_prime hV (hw a (mem_insert_self a s)) (fun x hx => by rw [← map_mul]; exact h2 x hx)

/-- **R5 (d) peeling on `Z′`, general banned set**: for an up-closed `R′ ⊆ K`, peeling a smallest head leaves the full
tail child, which vanishes on `Z′` (R5 (b), `pkR_b_R5bT`); so `NP^{¬(K∖R′)} = (Π_{R′} X_Q) · NP^{¬K}` on `Z′`. -/
theorem pkR_d2_R5peel {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {K : Finset (ℕ × ℕ)} (hK : K ⊆ oddDiagonals n)
    (hnc : ∀ Q ∈ K, ∀ Q' ∈ K, ¬ Crosses Q' Q → oddSide n Q ⊆ oddSide n Q' ∨ oddSide n Q' ⊆ oddSide n Q)
    {R : Finset ℕ} (hRA : ∀ C ∈ K, R ⊆ oddSide n C) {X : ℕ × ℕ → ℚ} (hZ : pkR_b_Z5 n 1 R K X)
    (R' : Finset (ℕ × ℕ)) (hRK : R' ⊆ K) (hup : ∀ Q ∈ R', ∀ Q' ∈ K, oddSide n Q ⊆ oddSide n Q' → Q' ∈ R') :
    MvPolynomial.eval X (pkR_b_NP ℚ n (K \ R')) = (∏ Q ∈ R', X Q) * MvPolynomial.eval X (pkR_b_NP ℚ n K) := by
  induction R' using Finset.strongInduction with
  | H R ih =>
  rcases R.eq_empty_or_nonempty with hR | hR
  · subst hR
    rw [sdiff_empty, prod_empty, one_mul]
  obtain ⟨Q, hQR, hmin⟩ := exists_min_image R (fun Q => (oddSide n Q).card) hR
  have hQK := hRK hQR
  have hQo := hK hQK
  have hsame : ∀ Q' ∈ R, oddSide n Q' ⊆ oddSide n Q → Q' = Q := fun Q' hQ' hs =>
    pkR_d2_eq_of_head (hK (hRK hQ')) hQo (eq_of_subset_of_card_le hs (hmin Q' hQ'))
  have hR'K : R.erase Q ⊆ K := (erase_subset Q R).trans hRK
  have hup' : ∀ Q₁ ∈ R.erase Q, ∀ Q' ∈ K, oddSide n Q₁ ⊆ oddSide n Q' → Q' ∈ R.erase Q := by
    intro Q₁ hQ₁ Q' hQ' hs
    have hQ₁R := mem_of_mem_erase hQ₁
    refine mem_erase.2 ⟨fun h => ?_, hup Q₁ hQ₁R Q' hQ' hs⟩
    rw [h] at hs
    exact ne_of_mem_erase hQ₁ (hsame Q₁ hQ₁R hs)
  have ih' := ih (R.erase Q) (erase_ssubset hQR) hR'K hup'
  have hQn : Q ∉ K \ R := fun h => (mem_sdiff.1 h).2 hQR
  have hins : insert Q (K \ R) ⊆ oddDiagonals n := by
    intro d hd
    rcases mem_insert.1 hd with h | h
    · rw [h]
      exact hQo
    · exact hK (mem_sdiff.1 h).1
  have hstep := pkR_b_step (R := ℚ) hn hE hins hQn
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
  rw [heq] at hstep
  have hpullT : pkR_b_pull n (tailStart Q) (tailLen n Q + 1) (K \ R) = ∅ := by
    refine pkR_d2_pull_tail hQo (fun d hd => hK (mem_sdiff.1 hd).1) fun Q' hQ' => ?_
    obtain ⟨hQ'K, hQ'R⟩ := mem_sdiff.1 hQ'
    by_cases hc : Crosses Q' Q
    · exact Or.inr hc
    · rcases hnc Q hQK Q' hQ'K hc with h | h
      · exact absurd (hup Q hQR Q' hQ'K h) hQ'R
      · exact Or.inl h
  have hterm : MvPolynomial.eval X (pkR_b_term ℚ n (K \ R) Q) = 0 := by
    unfold pkR_b_term
    rw [hpullT, pkR_b_NP_empty, map_mul, map_mul, pkR_b_R5bT hE hn hQo (hRA Q hQK) hQK hZ, mul_zero, zero_mul]
  rw [hstep, map_add, map_mul, MvPolynomial.eval_X, ih', hterm, add_zero, ← mul_prod_erase R _ hQR]
  ring

/-- **R5 (d) for a general banned set** (the chain hypothesis of `pkR_b_R5d` dropped): if every member's head contains
the run `R` (odd leg `r₀`; two legs of `T`), then `N^{¬K}_n ≡ 0` on `Z′`. -/
theorem pkR_d2_R5d {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {K : Finset (ℕ × ℕ)} (hK : K ⊆ oddDiagonals n)
    (hnc : ∀ Q ∈ K, ∀ Q' ∈ K, ¬ Crosses Q' Q → oddSide n Q ⊆ oddSide n Q' ∨ oddSide n Q' ⊆ oddSide n Q)
    {R : Finset ℕ} (hRn : R ⊆ Icc 1 n) (hRA : ∀ C ∈ K, R ⊆ oddSide n C) {r₀ : ℕ} (hr₀ : r₀ ∈ R)
    (hr₀o : r₀ % 2 = 1) (hRR : ∀ a ∈ R, ∀ b ∈ R, ¬ InST (pkR_b_T5 n 1 R) a b) {t₁ t₂ : ℕ}
    (h1 : t₁ ∈ pkR_b_T5 n 1 R) (h2 : t₂ ∈ pkR_b_T5 n 1 R) (h12 : t₁ ≠ t₂) :
    ∀ X ∈ {X : ℕ × ℕ → ℚ | pkR_b_Z5 n 1 R K X}, MvPolynomial.eval X (pkR_b_NP ℚ n K) = 0 := by
  refine pkR_d2_primeFin (pkR_b_Z5_sub n 1 R K) (fun Q => MvPolynomial.X Q) K ?_ ?_
  · intro j hj
    obtain ⟨w, hw, hne⟩ := pkR_b_R5cT hE (hK hj) hRn (hRA j hj) hr₀ hr₀o K
    exact ⟨w, hw, by rw [MvPolynomial.eval_X]; exact hne⟩
  · intro x hx
    have hx' : pkR_b_Z5 n 1 R K x := hx
    have hN0 := pkR_b_R5a_NP hE hn (by omega) hx' hRR h1 h2 h12
    have e := pkR_d2_R5peel hE hn hK hnc hRA hx' K subset_rfl (fun _ _ _ h _ => h)
    rw [Finset.sdiff_self, pkR_b_NP_empty, hN0] at e
    simp only [MvPolynomial.eval_X]
    exact e.symm

/-- **R6 ⇒ `b_Q ≡ 0` for a general member set** (`pkR_b_R6van` without the chain hypothesis): positional members `J`
(each head containing `A_b`), crossing allowed. -/
theorem pkR_d2_R6van {N a p L L' : ℕ} (hN : 1 ≤ N) (ha : 1 ≤ a ∧ a ≤ N) (hL : L % 2 = 1) (hp : p % 2 = 0)
    (hL' : L' % 2 = 1) (hL3 : 3 ≤ L') (hpL : p + L' ≤ L) (hLL : L' + 2 ≤ L) (hLN : L < N) {X : ℕ × ℕ → ℚ}
    (hT : pkR_b_OT N a p L L' X) (hXQ : planar N X a (a + L) = 0) (J : Finset (ℕ × ℕ))
    (hc : ∀ c ∈ J, c.1 % 2 = 0 ∧ c.2 % 2 = 1 ∧ c.1 ≤ p ∧ p + L' ≤ c.1 + c.2 ∧
      c.1 + c.2 ≤ L ∧ ¬ (c.1 = 0 ∧ c.2 = L) ∧
      ∀ i' j, c.1 ≤ i' → i' < c.1 + c.2 → i' % 2 = 1 → (j < c.1 ∨ c.1 + c.2 ≤ j) → j < L →
        j % 2 = 0 → mesh N X (vtx N (a + i')) (vtx N (a + j)) = 0) :
    MvPolynomial.eval (pkR_subX N (pkR_b_omL N a (L - 1) 1) X)
      (pkR_b_NP ℚ (L - 1 + 2) (J.image (fun c => (c.1 + 1, c.1 + c.2 + 1)))) = 0 := by
  have hZ := pkR_b_R6Z5 hN ha hL hp hL' hpL hLL hLN hT hXQ (J := J) (fun cc hcc => by
    obtain ⟨a1, a2, a3, a4, a5, -, a7⟩ := hc cc hcc
    exact ⟨a1, a2, a3, a4, a5, a7⟩)
  have hC' : J.image (fun c => (c.1 + 1, c.1 + c.2 + 1)) ⊆ oddDiagonals (L - 1 + 2) := by
    intro d hd
    obtain ⟨c, hcJ, rfl⟩ := mem_image.1 hd
    obtain ⟨a1, a2, a3, a4, a5, a6, -⟩ := hc c hcJ
    exact mem_filter.2 ⟨mem_diagonals.2 (by dsimp only; omega), by dsimp only; omega⟩
  have hRA : ∀ d ∈ J.image (fun c => (c.1 + 1, c.1 + c.2 + 1)),
      Icc (p + 1) (p + L') ⊆ oddSide (L - 1 + 2) d := by
    intro d hd
    obtain ⟨c, hcJ, rfl⟩ := mem_image.1 hd
    rw [pkR_b_oS1 (hc c hcJ).1]
    intro x hx
    rw [mem_Icc] at hx ⊢
    have := hc c hcJ
    omega
  have hnc' : ∀ d ∈ J.image (fun c => (c.1 + 1, c.1 + c.2 + 1)),
      ∀ d' ∈ J.image (fun c => (c.1 + 1, c.1 + c.2 + 1)), ¬ Crosses d' d →
        oddSide (L - 1 + 2) d ⊆ oddSide (L - 1 + 2) d' ∨ oddSide (L - 1 + 2) d' ⊆ oddSide (L - 1 + 2) d := by
    intro d hd d' hd' hcr
    obtain ⟨c, hcJ, rfl⟩ := mem_image.1 hd
    obtain ⟨c', hcJ', rfl⟩ := mem_image.1 hd'
    have k1 := hc c hcJ
    have k2 := hc c' hcJ'
    rw [pkR_b_oS1 k1.1, pkR_b_oS1 k2.1]
    unfold Crosses at hcr
    dsimp only at hcr
    by_cases h : c'.1 ≤ c.1 ∧ c.1 + c.2 ≤ c'.1 + c'.2
    · exact Or.inl (Icc_subset_Icc (by omega) (by omega))
    · exact Or.inr (Icc_subset_Icc (by omega) (by omega))
  have hRn : Icc (p + 1) (p + L') ⊆ Icc 1 (L - 1 + 2) := by
    intro x hx
    rw [mem_Icc] at hx ⊢
    omega
  have ht1 : L - 1 + 2 ∈ pkR_b_T5 (L - 1 + 2) 1 (Icc (p + 1) (p + L')) :=
    mem_filter.2 ⟨mem_Icc.2 ⟨by omega, le_rfl⟩, by omega, fun h => by rw [mem_Icc] at h; omega⟩
  obtain ⟨t₂, ht2, h12⟩ : ∃ t₂, t₂ ∈ pkR_b_T5 (L - 1 + 2) 1 (Icc (p + 1) (p + L')) ∧ L - 1 + 2 ≠ t₂ := by
    by_cases hp0 : p = 0
    · exact ⟨L' + 1, mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega, fun h => by rw [mem_Icc] at h; omega⟩,
        by omega⟩
    · exact ⟨p, mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega, fun h => by rw [mem_Icc] at h; omega⟩,
        by omega⟩
  exact pkR_d2_R5d (n := L - 1 + 2) (by omega) (by omega) hC' hnc' hRn hRA (r₀ := p + 1)
    (mem_Icc.2 ⟨le_rfl, by omega⟩) (by omega) pkR_b_ivl_RR ht1 ht2 h12 _ hZ

set_option maxHeartbeats 1000000 in
/-- **T(Q, Q′) on `L_S` in positions** (the `pkR_b_OT` input of R6): two class members `Q′ ⊊ Q` (heads) — [OmegaHyp]
(`pkR_b_omegaHyp` with (H3a), (H3b) = `pkR_d_H3b`) read from `a = headStart Q` (the conversion of `pkR_b_omegaTiles`). -/
theorem pkR_d2_OT {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} {t Q Q' : ℕ × ℕ}
    (hQc : Q ∈ hitClass N S t) (hQc' : Q' ∈ hitClass N S t) (hsub : oddSide N Q' ⊆ oddSide N Q) (hne : Q ≠ Q')
    {X : ℕ × ℕ → ℚ} (hX : OnLocus N S X) :
    pkR_b_OT N (headStart Q) (cycPos N (headStart Q) (headStart Q')) (headLen N Q) (headLen N Q') X := by
  have hQ := (pkR_b_H3a hQc).1
  have hQ' := (pkR_b_H3a hQc').1
  have f1 := pkR_b_head_facts hE hQ
  have f2 := pkR_b_head_facts hE hQ'
  obtain ⟨hp, hpL, hLL, hpos⟩ := pkR_b_nest_pos hE hQ hQ' hsub hne
  have hT : ∀ a b, (a, b) ∈ diagonals N → pkR_b_TP N Q Q' a b → mesh N X a b = 0 := fun a b hab hTP =>
    hX _ (pkR_b_omegaHyp hsub (pkR_b_H3a hQc).2 (pkR_b_H3a hQc').2 (pkR_d_H3b hN hE hQc hQc').1
      (pkR_d_H3b hN hE hQc hQc').2 hab hTP)
  refine (pkR_b_OT_iff _ _ _ _ _ X).2 ⟨?_, ?_, ?_⟩
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

/-- The members strictly below `c` pull back to the head child of `c` as positional chords `(u + 1, u + v + 1)`
(`u` = position of `A_Q`, `v = |A_Q|`); crossing and higher members do not pull back. -/
theorem pkR_d2_pull_below {N : ℕ} (hE : N % 2 = 0) {K : Finset (ℕ × ℕ)} (hK : K ⊆ oddDiagonals N)
    (hnc : ∀ Q ∈ K, ∀ Q' ∈ K, ¬ Crosses Q' Q → oddSide N Q ⊆ oddSide N Q' ∨ oddSide N Q' ⊆ oddSide N Q)
    {c : ℕ × ℕ} (hcK : c ∈ K) :
    pkR_b_pull N (headStart c) (headLen N c + 1) K =
      ((pkR_d2_below N K c).image (fun Q => (cycPos N (headStart c) (headStart Q), headLen N Q))).image
        (fun d => (d.1 + 1, d.1 + d.2 + 1)) := by
  have hco := hK hcK
  have hKQK : pkR_d2_below N K c ⊆ K := filter_subset _ _
  have h1 : pkR_b_pull N (headStart c) (headLen N c + 1) K =
      pkR_b_pull N (headStart c) (headLen N c + 1) (pkR_d2_below N K c) := by
    refine pkR_b_pull_mono hKQK (pkR_d2_pull_head hco (fun d hd => hK (mem_sdiff.1 hd).1) fun Q' hQ' => ?_)
    obtain ⟨hQ'K, hQ'n⟩ := mem_sdiff.1 hQ'
    by_cases hc : Crosses Q' c
    · exact Or.inr hc
    · rcases hnc c hcK Q' hQ'K hc with h | h
      · exact Or.inl h
      · by_cases he : Q' = c
        · rw [he]
          exact Or.inl subset_rfl
        · exact absurd (mem_filter.2 ⟨hQ'K, he, h⟩) hQ'n
  rw [h1, pkR_b_pull_head hE hco (fun d hd => hK (hKQK hd)) (fun d hd => (mem_filter.1 hd).2.2),
    erase_eq_self.2 (fun h => (mem_filter.1 h).2.1 rfl), image_image]
  rfl

/-- The `minRect(Q)` tiles in positions from `headStart c` (`A_Q` = positions `[u, u + v)` inside `A_c`): (odd position in
`A_Q`) × (even position of `A_c` outside `A_Q`) vanish on `L_S` for a clean chord `Q` (the (z3) input of R6). -/
theorem pkR_d2_mrpos {N : ℕ} (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} {c Q : ℕ × ℕ} (hco : c ∈ oddDiagonals N)
    (hQo : Q ∈ oddDiagonals N) (hQsub : oddSide N Q ⊆ oddSide N c) (hQc : c ≠ Q)
    (hcl : Disjoint (minRect N Q) (missing N S)) {X : ℕ × ℕ → ℚ} (hX : OnLocus N S X) (i' j : ℕ)
    (hi1 : cycPos N (headStart c) (headStart Q) ≤ i') (hi2 : i' < cycPos N (headStart c) (headStart Q) + headLen N Q)
    (hi3 : i' % 2 = 1)
    (hj1 : j < cycPos N (headStart c) (headStart Q) ∨ cycPos N (headStart c) (headStart Q) + headLen N Q ≤ j)
    (hj2 : j < headLen N c) (hj3 : j % 2 = 0) :
    mesh N X (vtx N (headStart c + i')) (vtx N (headStart c + j)) = 0 := by
  have f1 := pkR_b_head_facts hE hco
  obtain ⟨-, q1, -, qpos⟩ := pkR_b_nest_pos hE hco hQo hQsub hQc
  obtain ⟨-, -, V1⟩ := pkR_b_posQ hE hco (i := i') (by omega)
  obtain ⟨-, -, V2⟩ := pkR_b_posQ hE hco (i := j) (by omega)
  have hx := (qpos i' (by omega)).2 ⟨hi1, hi2⟩
  have hy : vtx N (headStart c + j) ∉ oddSide N Q := fun h => by
    have := (qpos j (by omega)).1 h
    omega
  have hxe : vtx N (headStart c + i') % 2 = 0 := by omega
  have hyo : vtx N (headStart c + j) % 2 = 1 := by omega
  have hyB : vtx N (headStart c + j) ∈ evenSide N Q :=
    mem_sdiff.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, hy⟩
  have hmR : (min (vtx N (headStart c + i')) (vtx N (headStart c + j)),
      max (vtx N (headStart c + i')) (vtx N (headStart c + j))) ∈ minRect N Q :=
    pkCh_mem_minRect.2 ⟨_, mem_filter.2 ⟨hx, hxe⟩, _, mem_filter.2 ⟨hyB, hyo⟩, rfl⟩
  have hmS : (min (vtx N (headStart c + i')) (vtx N (headStart c + j)),
      max (vtx N (headStart c + i')) (vtx N (headStart c + j))) ∈ S := by
    by_contra hns
    exact disjoint_left.1 hcl hmR (mem_sdiff.2 ⟨pkR_d2_minRect_diag hQo hmR, hns⟩)
  have hm := hX _ hmS
  dsimp only at hm
  rcases le_total (vtx N (headStart c + i')) (vtx N (headStart c + j)) with h | h
  · rwa [min_eq_left h, max_eq_right h] at hm
  · rw [min_eq_right h, max_eq_left h] at hm
    rw [pkR_mesh_comm]
    exact hm

/-- **(E) for `b_c`** (gap G3, general class): on `H` (`X_c = 0` on `L_S`), the ¬K numerator of the head child of a class
member `c ≠ b` vanishes (`pkR_d2_R6van` with `T(c, b)` from `pkR_d2_OT` and the members below `c` as `J`). -/
theorem pkR_d2_bvan {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} {t b c : ℕ × ℕ}
    (hb : b ∈ hitClass N S t) (hc : c ∈ hitClass N S t) (hbc : oddSide N b ⊆ oddSide N c) (hcb : c ≠ b)
    (hbK : ∀ Q ∈ hitClass N S t, oddSide N b ⊆ oddSide N Q)
    (hnc : ∀ Q ∈ hitClass N S t, ∀ Q' ∈ hitClass N S t, ¬ Crosses Q' Q →
      oddSide N Q ⊆ oddSide N Q' ∨ oddSide N Q' ⊆ oddSide N Q)
    {X : ℕ × ℕ → ℚ} (hX : OnLocus N S X) (hXc : X c = 0) :
    MvPolynomial.eval X (MvPolynomial.rename (relab N (headStart c))
      (pkR_b_NP ℚ (headLen N c + 1) (pkR_b_pull N (headStart c) (headLen N c + 1) (hitClass N S t)))) = 0 := by
  have hco := (pkR_b_H3a hc).1
  have hbo := (pkR_b_H3a hb).1
  have f1 := pkR_b_head_facts hE hco
  have fb := pkR_b_head_facts hE hbo
  obtain ⟨hp, hpL, hLL, -⟩ := pkR_b_nest_pos hE hco hbo hbc hcb
  have hK : hitClass N S t ⊆ oddDiagonals N := fun Q hQ => (pkR_b_H3a hQ).1
  have hXQ : planar N X (headStart c) (headStart c + headLen N c) = 0 := by
    rw [pkR_b_planarQ hco X]
    exact hXc
  have hOT := pkR_d2_OT hN hE hc hb hbc hcb hX
  have hJ : ∀ d ∈ (pkR_d2_below N (hitClass N S t) c).image
      (fun Q => (cycPos N (headStart c) (headStart Q), headLen N Q)),
      d.1 % 2 = 0 ∧ d.2 % 2 = 1 ∧ d.1 ≤ cycPos N (headStart c) (headStart b) ∧
        cycPos N (headStart c) (headStart b) + headLen N b ≤ d.1 + d.2 ∧ d.1 + d.2 ≤ headLen N c ∧
        ¬ (d.1 = 0 ∧ d.2 = headLen N c) ∧
        ∀ i' j, d.1 ≤ i' → i' < d.1 + d.2 → i' % 2 = 1 → (j < d.1 ∨ d.1 + d.2 ≤ j) → j < headLen N c →
          j % 2 = 0 → mesh N X (vtx N (headStart c + i')) (vtx N (headStart c + j)) = 0 := by
    intro d hd
    obtain ⟨Q, hQ, rfl⟩ := mem_image.1 hd
    obtain ⟨hQK, hQc, hQsub⟩ := mem_filter.1 hQ
    have hQo := hK hQK
    have fQ := pkR_b_head_facts hE hQo
    obtain ⟨q0, q1, q2, -⟩ := pkR_b_nest_pos hE hco hQo hQsub (fun e => hQc e.symm)
    have hn := (pkR_d2_nest_iff hE hco hbo hQo hbc hQsub hcb (fun e => hQc e.symm)).1 (hbK Q hQK)
    exact ⟨q0, fQ.2.2.2.1, hn.1, hn.2, q1, fun h => by omega,
      pkR_d2_mrpos hE hco hQo hQsub (fun e => hQc e.symm) (pkR_b_H3a hQK).2 hX⟩
  rw [pkR_d2_pull_below hE hK hnc hc, pkR_b_child_omL ⟨f1.1, f1.2.1⟩ (by omega) (by omega)]
  exact pkR_d2_R6van (N := N) (by omega) ⟨f1.1, f1.2.1⟩ f1.2.2.2.1 hp fb.2.2.2.1 fb.2.2.2.2.1 hpL hLL (by omega)
    hOT hXQ _ hJ

/-! ### G3, tail side: `a_Q ≡ 0` on `H` for a general class -/

/-- An (even head leg, odd tail leg) pair of a clean chord is a vanishing tile on `L_S` (a `minRect` tile). -/
theorem pkR_d2_mr_leg {N : ℕ} {S : Finset (ℕ × ℕ)} {Q : ℕ × ℕ} (hQo : Q ∈ oddDiagonals N)
    (hcl : Disjoint (minRect N Q) (missing N S)) {X : ℕ × ℕ → ℚ} (hX : OnLocus N S X) {e o : ℕ}
    (he : e ∈ oddSide N Q) (he2 : e % 2 = 0) (ho : 1 ≤ o ∧ o ≤ N) (ho1 : o ∉ oddSide N Q) (ho2 : o % 2 = 1) :
    mesh N X e o = 0 := by
  have hmR : (min e o, max e o) ∈ minRect N Q :=
    pkCh_mem_minRect.2 ⟨_, mem_filter.2 ⟨he, he2⟩, _, mem_filter.2 ⟨mem_sdiff.2 ⟨mem_Icc.2 ho, ho1⟩, ho2⟩, rfl⟩
  have hmS : (min e o, max e o) ∈ S := by
    by_contra hns
    exact disjoint_left.1 hcl hmR (mem_sdiff.2 ⟨pkR_d2_minRect_diag hQo hmR, hns⟩)
  have hm := hX _ hmS
  dsimp only at hm
  rcases le_total e o with h | h
  · rwa [min_eq_left h, max_eq_right h] at hm
  · rw [min_eq_right h, max_eq_left h] at hm
    rw [pkR_mesh_comm]
    exact hm

/-- The head of a mixed chord ends at its tail start. -/
theorem pkR_d2_vtx_ts {N : ℕ} {Q : ℕ × ℕ} (hQ : Q ∈ oddDiagonals N) :
    vtx N (headStart Q + headLen N Q) = tailStart Q := by
  have b := pkR_b_odd_iff.1 hQ
  have hH := pkR_b_head_data hQ
  have hT := pkR_b_tail_data hQ
  obtain ⟨q1, q2⟩ := Q
  dsimp only at b hH hT
  rcases hH with h | h <;> rcases hT with h' | h'
  · rw [h.2.1, h.2.2, h'.2.1, show q1 + (q2 - q1) = q2 by omega]
    exact vtx_of_mem (by omega) (by omega)
  · omega
  · omega
  · rw [h.2.1, h.2.2, h'.2.1, show q2 + (N - (q2 - q1)) = q1 + N by omega, vtx_add_n]
    exact vtx_of_mem (by omega) (by omega)

/-- `X_Q` read from the tail start of `Q`. -/
theorem pkR_d2_planarT {N : ℕ} {Q : ℕ × ℕ} (hQ : Q ∈ oddDiagonals N) (X : ℕ × ℕ → ℚ) :
    planar N X (tailStart Q) (tailStart Q + tailLen N Q) = X Q := by
  have b := pkR_b_odd_iff.1 hQ
  have hT := pkR_b_tail_data hQ
  obtain ⟨q1, q2⟩ := Q
  dsimp only at b hT
  rcases hT with h | h
  · rw [h.2.1, h.2.2, show q2 + (N - (q2 - q1)) = q1 + N by omega,
      pkR_planar_congr (by omega) X (rfl : vtx N q2 = vtx N q2) (vtx_add_n N q1), pkR_planar_comm]
    exact planar_eq_X X b.1 b.2.2.1 b.2.1 b.2.2.2.1
  · rw [h.2.1, h.2.2, show q1 + (q2 - q1) = q2 by omega]
    exact planar_eq_X X b.1 b.2.2.1 b.2.1 b.2.2.2.1

/-- Position facts of a chord `Q` with head inside `A_t` (`Q = t` allowed), from `a = headStart t`. -/
theorem pkR_d2_npos {N : ℕ} (hE : N % 2 = 0) {t Q : ℕ × ℕ} (ht : t ∈ oddDiagonals N) (hQ : Q ∈ oddDiagonals N)
    (hsub : oddSide N Q ⊆ oddSide N t) :
    cycPos N (headStart t) (headStart Q) % 2 = 0 ∧ cycPos N (headStart t) (headStart Q) + headLen N Q ≤ headLen N t ∧
      (∀ i, i < N → (vtx N (headStart t + i) ∈ oddSide N Q ↔
        cycPos N (headStart t) (headStart Q) ≤ i ∧ i < cycPos N (headStart t) (headStart Q) + headLen N Q)) ∧
      vtx N (headStart t + cycPos N (headStart t) (headStart Q)) = headStart Q ∧
      vtx N (headStart t + (cycPos N (headStart t) (headStart Q) + headLen N Q)) = tailStart Q := by
  have f1 := pkR_b_head_facts hE ht
  have fQ := pkR_b_head_facts hE hQ
  have hv := pkR_b_vtx_cyc (N := N) (s := headStart t) (x := headStart Q) ⟨f1.1, f1.2.1⟩ ⟨fQ.1, fQ.2.1⟩
  have hA : cycPos N (headStart t) (headStart Q) % 2 = 0 ∧
      cycPos N (headStart t) (headStart Q) + headLen N Q ≤ headLen N t ∧
      (∀ i, i < N → (vtx N (headStart t + i) ∈ oddSide N Q ↔
        cycPos N (headStart t) (headStart Q) ≤ i ∧ i < cycPos N (headStart t) (headStart Q) + headLen N Q)) := by
    by_cases hQt : t = Q
    · subst hQt
      have e0 : cycPos N (headStart t) (headStart t) = 0 := by
        show (headStart t + N - headStart t) % N = 0
        rw [show headStart t + N - headStart t = N by omega, Nat.mod_self]
      rw [e0]
      refine ⟨rfl, by omega, fun i hi => ?_⟩
      rw [(pkR_b_posQ hE ht hi).1]
      omega
    · obtain ⟨a1, a2, -, a4⟩ := pkR_b_nest_pos hE ht hQ hsub hQt
      exact ⟨a1, a2, a4⟩
  refine ⟨hA.1, hA.2.1, hA.2.2, hv, ?_⟩
  have e1 := pkR_b_vtx_sh (N := N) (a := headStart t) (s := cycPos N (headStart t) (headStart Q))
    (i := headLen N Q) (by omega) ⟨f1.1, f1.2.1⟩ (by omega) (by omega)
  rw [hv, Nat.mod_eq_of_lt (by omega), pkR_d2_vtx_ts hQ] at e1
  exact e1.symm

/-- The chord `Q″ ⊇ Q` read as a child chord of the tail child of `Q` (base `tailStart Q`), in positions from
`headStart t`: `(u + 1, u + v + 1)` with `u = p″ + L″ − p − L′`, `v = N − L″`. -/
theorem pkR_d2_relab_tail {N : ℕ} (hE : N % 2 = 0) {t Q Q'' : ℕ × ℕ} (ht : t ∈ oddDiagonals N)
    (hQ : Q ∈ oddDiagonals N) (hQ'' : Q'' ∈ oddDiagonals N) (hsQ : oddSide N Q ⊆ oddSide N t)
    (hs'' : oddSide N Q'' ⊆ oddSide N t) (hle : cycPos N (headStart t) (headStart Q'') ≤ cycPos N (headStart t) (headStart Q))
    (hge : cycPos N (headStart t) (headStart Q) + headLen N Q ≤
      cycPos N (headStart t) (headStart Q'') + headLen N Q'') :
    relab N (tailStart Q)
      (cycPos N (headStart t) (headStart Q'') + headLen N Q'' - cycPos N (headStart t) (headStart Q) - headLen N Q + 1,
        cycPos N (headStart t) (headStart Q'') + headLen N Q'' - cycPos N (headStart t) (headStart Q) - headLen N Q +
          (N - headLen N Q'') + 1) = Q'' := by
  have f1 := pkR_b_head_facts hE ht
  have fQ := pkR_b_head_facts hE hQ
  have fQ'' := pkR_b_head_facts hE hQ''
  obtain ⟨-, a2, -, -, a5⟩ := pkR_d2_npos hE ht hQ hsQ
  obtain ⟨-, b2, -, b4, b5⟩ := pkR_d2_npos hE ht hQ'' hs''
  have hts := pkR_b_tail_data hQ
  have hQb := pkR_b_odd_iff.1 hQ
  have hts1 : 1 ≤ tailStart Q ∧ tailStart Q ≤ N := by
    rcases hts with h | h <;> omega
  have e1 := pkR_b_vtx_sh (N := N) (a := headStart t) (s := cycPos N (headStart t) (headStart Q) + headLen N Q)
    (i := cycPos N (headStart t) (headStart Q'') + headLen N Q'' - cycPos N (headStart t) (headStart Q) -
      headLen N Q) (by omega) ⟨f1.1, f1.2.1⟩ (by omega) (by omega)
  have e2 := pkR_b_vtx_sh (N := N) (a := headStart t) (s := cycPos N (headStart t) (headStart Q) + headLen N Q)
    (i := cycPos N (headStart t) (headStart Q'') + headLen N Q'' - cycPos N (headStart t) (headStart Q) -
      headLen N Q + (N - headLen N Q'')) (by omega) ⟨f1.1, f1.2.1⟩ (by omega) (by omega)
  rw [a5, show cycPos N (headStart t) (headStart Q) + headLen N Q + (cycPos N (headStart t) (headStart Q'') +
      headLen N Q'' - cycPos N (headStart t) (headStart Q) - headLen N Q) =
      cycPos N (headStart t) (headStart Q'') + headLen N Q'' by omega, Nat.mod_eq_of_lt (by omega), b5] at e1
  rw [a5, show cycPos N (headStart t) (headStart Q) + headLen N Q + (cycPos N (headStart t) (headStart Q'') +
      headLen N Q'' - cycPos N (headStart t) (headStart Q) - headLen N Q + (N - headLen N Q'')) =
      cycPos N (headStart t) (headStart Q'') + N by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (show cycPos N (headStart t) (headStart Q'') < N by omega), b4] at e2
  show (min (vtx N (_ + tailStart Q - 1)) (vtx N (_ + tailStart Q - 1)),
    max (vtx N (_ + tailStart Q - 1)) (vtx N (_ + tailStart Q - 1))) = Q''
  rw [show cycPos N (headStart t) (headStart Q'') + headLen N Q'' - cycPos N (headStart t) (headStart Q) -
      headLen N Q + 1 + tailStart Q - 1 = tailStart Q + (cycPos N (headStart t) (headStart Q'') + headLen N Q'' -
        cycPos N (headStart t) (headStart Q) - headLen N Q) by omega,
    show cycPos N (headStart t) (headStart Q'') + headLen N Q'' - cycPos N (headStart t) (headStart Q) -
      headLen N Q + (N - headLen N Q'') + 1 + tailStart Q - 1 = tailStart Q + (cycPos N (headStart t) (headStart Q'') +
        headLen N Q'' - cycPos N (headStart t) (headStart Q) - headLen N Q + (N - headLen N Q'')) by omega, e1, e2]
  have b := pkR_b_odd_iff.1 hQ''
  have hH := pkR_b_head_data hQ''
  have hT := pkR_b_tail_data hQ''
  obtain ⟨q1, q2⟩ := Q''
  dsimp only at b hH hT
  rcases hH with h | h <;> rcases hT with h' | h'
  · rw [h.2.1, h'.2.1]
    exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)
  · omega
  · omega
  · rw [h.2.1, h'.2.1]
    exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)

/-- Head inclusion inside `A_t` in positions from `headStart t` (forward direction; `Q″ = t` allowed). -/
theorem pkR_d2_nest_fwd {N : ℕ} (hE : N % 2 = 0) {t Q Q'' : ℕ × ℕ} (ht : t ∈ oddDiagonals N)
    (hQ : Q ∈ oddDiagonals N) (hQ'' : Q'' ∈ oddDiagonals N) (hsQ : oddSide N Q ⊆ oddSide N t)
    (hs'' : oddSide N Q'' ⊆ oddSide N t) (h : oddSide N Q ⊆ oddSide N Q'') :
    cycPos N (headStart t) (headStart Q'') ≤ cycPos N (headStart t) (headStart Q) ∧
      cycPos N (headStart t) (headStart Q) + headLen N Q ≤
        cycPos N (headStart t) (headStart Q'') + headLen N Q'' := by
  have f1 := pkR_b_head_facts hE ht
  have fQ := pkR_b_head_facts hE hQ
  obtain ⟨-, a2, a3, -, -⟩ := pkR_d2_npos hE ht hQ hsQ
  obtain ⟨-, b2, b3, -, -⟩ := pkR_d2_npos hE ht hQ'' hs''
  have m1 := (b3 _ (by omega)).1 (h ((a3 (cycPos N (headStart t) (headStart Q)) (by omega)).2 ⟨le_rfl, by omega⟩))
  have m2 := (b3 _ (by omega)).1 (h ((a3 (cycPos N (headStart t) (headStart Q) + headLen N Q - 1) (by omega)).2
    ⟨by omega, by omega⟩))
  omega

/-- **The pull-back of the class to the tail child of `Q`** (base `tailStart Q`): the members strictly above `Q`, as
positional chords `(u + 1, u + v + 1)`, `u = p″ + L″ − p − L′`, `v = N − L″` (positions from `headStart t`). -/
theorem pkR_d2_pull_above {N : ℕ} (hE : N % 2 = 0) {K : Finset (ℕ × ℕ)} (hK : K ⊆ oddDiagonals N)
    (hnc : ∀ Q ∈ K, ∀ Q' ∈ K, ¬ Crosses Q' Q → oddSide N Q ⊆ oddSide N Q' ∨ oddSide N Q' ⊆ oddSide N Q)
    {t Q : ℕ × ℕ} (ht : t ∈ oddDiagonals N) (hKt : ∀ Q' ∈ K, oddSide N Q' ⊆ oddSide N t) (hQK : Q ∈ K)
    (hQt : Q ≠ t) :
    pkR_b_pull N (tailStart Q) (tailLen N Q + 1) K =
      ((pkR_d2_above N K Q).image (fun Q'' => (cycPos N (headStart t) (headStart Q'') + headLen N Q'' -
        cycPos N (headStart t) (headStart Q) - headLen N Q, N - headLen N Q''))).image
        (fun d => (d.1 + 1, d.1 + d.2 + 1)) := by
  have hQo := hK hQK
  have f1 := pkR_b_head_facts hE ht
  have fQ := pkR_b_head_facts hE hQo
  obtain ⟨-, -, hLL, -⟩ := pkR_b_nest_pos hE ht hQo (hKt Q hQK) (Ne.symm hQt)
  obtain ⟨-, a2, -, -, -⟩ := pkR_d2_npos hE ht hQo (hKt Q hQK)
  have hts := pkR_b_tail_data hQo
  have hQb := pkR_b_odd_iff.1 hQo
  have hts1 : 1 ≤ tailStart Q ∧ tailStart Q ≤ N := by
    rcases hts with h | h <;> omega
  have htl : tailLen N Q = N - headLen N Q := rfl
  -- the positional chord of a member above `Q` is a child diagonal, relabelled to that member
  have hfwd : ∀ Q'' ∈ pkR_d2_above N K Q,
      (cycPos N (headStart t) (headStart Q'') + headLen N Q'' - cycPos N (headStart t) (headStart Q) - headLen N Q + 1,
        cycPos N (headStart t) (headStart Q'') + headLen N Q'' - cycPos N (headStart t) (headStart Q) - headLen N Q +
          (N - headLen N Q'') + 1) ∈ diagonals (tailLen N Q + 1) ∧
      relab N (tailStart Q)
        (cycPos N (headStart t) (headStart Q'') + headLen N Q'' - cycPos N (headStart t) (headStart Q) - headLen N Q + 1,
          cycPos N (headStart t) (headStart Q'') + headLen N Q'' - cycPos N (headStart t) (headStart Q) - headLen N Q +
            (N - headLen N Q'') + 1) = Q'' := by
    intro Q'' h
    obtain ⟨hQ''K, hne, hsub⟩ := mem_filter.1 h
    have hQ''o := hK hQ''K
    have fQ'' := pkR_b_head_facts hE hQ''o
    obtain ⟨-, b2, -, -, -⟩ := pkR_d2_npos hE ht hQ''o (hKt Q'' hQ''K)
    have hn := pkR_d2_nest_fwd hE ht hQo hQ''o (hKt Q hQK) (hKt Q'' hQ''K) hsub
    have hne' : ¬ (cycPos N (headStart t) (headStart Q'') = cycPos N (headStart t) (headStart Q) ∧
        headLen N Q'' = headLen N Q) := by
      rintro ⟨e1, e2⟩
      by_cases h't : Q'' = t
      · rw [h't] at e2
        omega
      · exact hne (pkR_d2_pos_eq hE ht hQ''o hQo (hKt Q'' hQ''K) (hKt Q hQK) (Ne.symm h't) (Ne.symm hQt) e1 e2)
    exact ⟨mem_diagonals.2 (by dsimp only; omega),
      pkR_d2_relab_tail hE ht hQo hQ''o (hKt Q hQK) (hKt Q'' hQ''K) hn.1 hn.2⟩
  ext d
  constructor
  · intro hd
    obtain ⟨hdd, hdK⟩ := mem_filter.1 hd
    have hdd' := mem_diagonals.1 hdd
    obtain ⟨Q'', hQ''⟩ : ∃ Q'', relab N (tailStart Q) d = Q'' := ⟨_, rfl⟩
    rw [hQ''] at hdK
    have hQ''o := hK hdK
    have hnot : ¬ (oddSide N Q'' ⊆ oddSide N Q ∨ Crosses Q'' Q) := by
      intro hc
      have e := pkR_d2_pull_tail hQo (K := {Q''}) (by simpa using hQ''o) (by simpa using hc)
      have hm : d ∈ pkR_b_pull N (tailStart Q) (tailLen N Q + 1) {Q''} :=
        mem_filter.2 ⟨hdd, by rw [hQ'']; exact mem_singleton_self _⟩
      rw [e] at hm
      simp at hm
    have hsub : oddSide N Q ⊆ oddSide N Q'' := by
      rcases hnc Q hQK Q'' hdK (fun h => hnot (Or.inr h)) with h | h
      · exact h
      · exact absurd (Or.inl h) hnot
    have hne : Q'' ≠ Q := fun e => hnot (Or.inl (by rw [e]))
    have hmem : Q'' ∈ pkR_d2_above N K Q := mem_filter.2 ⟨hdK, hne, hsub⟩
    obtain ⟨hdg, hrel⟩ := hfwd Q'' hmem
    have hdg' := mem_diagonals.1 hdg
    have e := pkR_b_relab_inj hts1 (show tailLen N Q + 1 ≤ N by omega) ⟨by omega, by omega, by omega⟩
      ⟨by dsimp only at hdg' ⊢; omega, by dsimp only at hdg' ⊢; omega, by dsimp only at hdg' ⊢; omega⟩
      (hQ''.trans hrel.symm)
    exact mem_image.2 ⟨_, mem_image.2 ⟨Q'', hmem, rfl⟩, e.symm⟩
  · intro hd
    obtain ⟨d', hd', rfl⟩ := mem_image.1 hd
    obtain ⟨Q'', hQ'', rfl⟩ := mem_image.1 hd'
    obtain ⟨hdg, hrel⟩ := hfwd Q'' hQ''
    refine mem_filter.2 ⟨hdg, ?_⟩
    show relab N (tailStart Q) _ ∈ K
    rw [hrel]
    exact (mem_filter.1 hQ'').1

set_option maxHeartbeats 1000000 in
/-- **(E) for `a_Q`** (gap G3, general class): on `H` (`X_Q = 0` on `L_S`), the ¬K numerator of the tail child of a class
member `Q ≠ t` vanishes (`pkR_d2_R6van` at the tail start of `Q` with `T(t, Q)` swapped, `pkR_b_OT_swap`, and the members
above `Q` as `J`). -/
theorem pkR_d2_avan {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} {t Q : ℕ × ℕ}
    (htK : t ∈ hitClass N S t) (hQ : Q ∈ hitClass N S t) (hQt : Q ≠ t)
    (hKt : ∀ Q' ∈ hitClass N S t, oddSide N Q' ⊆ oddSide N t)
    (hnc : ∀ Q ∈ hitClass N S t, ∀ Q' ∈ hitClass N S t, ¬ Crosses Q' Q →
      oddSide N Q ⊆ oddSide N Q' ∨ oddSide N Q' ⊆ oddSide N Q)
    {X : ℕ × ℕ → ℚ} (hX : OnLocus N S X) (hXQ : X Q = 0) :
    MvPolynomial.eval X (MvPolynomial.rename (relab N (tailStart Q))
      (pkR_b_NP ℚ (tailLen N Q + 1) (pkR_b_pull N (tailStart Q) (tailLen N Q + 1) (hitClass N S t)))) = 0 := by
  have hto := (pkR_b_H3a htK).1
  have hQo := (pkR_b_H3a hQ).1
  have hK : hitClass N S t ⊆ oddDiagonals N := fun Q hQ => (pkR_b_H3a hQ).1
  have f1 := pkR_b_head_facts hE hto
  have fQ := pkR_b_head_facts hE hQo
  obtain ⟨hp, hpL, hLL, -⟩ := pkR_b_nest_pos hE hto hQo (hKt Q hQ) (Ne.symm hQt)
  obtain ⟨-, -, -, -, a5⟩ := pkR_d2_npos hE hto hQo (hKt Q hQ)
  have hts := pkR_b_tail_data hQo
  have hQb := pkR_b_odd_iff.1 hQo
  have hts1 : 1 ≤ tailStart Q ∧ tailStart Q ≤ N := by
    rcases hts with h | h <;> omega
  have htl : tailLen N Q = N - headLen N Q := rfl
  have hOT := pkR_b_OT_swap (by omega) hE ⟨f1.1, f1.2.1⟩ hp fQ.2.2.2.1 hpL (by omega)
    (pkR_d2_OT hN hE htK hQ (hKt Q hQ) (Ne.symm hQt) hX)
  have hXQ' : planar N X (vtx N (headStart t + (cycPos N (headStart t) (headStart Q) + headLen N Q)))
      (vtx N (headStart t + (cycPos N (headStart t) (headStart Q) + headLen N Q)) + (N - headLen N Q)) = 0 := by
    rw [a5]
    exact (pkR_d2_planarT hQo X).trans hXQ
  have ha' : 1 ≤ vtx N (headStart t + (cycPos N (headStart t) (headStart Q) + headLen N Q)) ∧
      vtx N (headStart t + (cycPos N (headStart t) (headStart Q) + headLen N Q)) ≤ N := by
    rw [a5]
    exact hts1
  have hsh := fun k (hk : k < N) => pkR_b_vtx_sh (N := N) (a := headStart t)
    (s := cycPos N (headStart t) (headStart Q) + headLen N Q) (i := k) (by omega) ⟨f1.1, f1.2.1⟩ (by omega) hk
  have hJ : ∀ c ∈ (pkR_d2_above N (hitClass N S t) Q).image (fun Q'' => (cycPos N (headStart t) (headStart Q'') +
      headLen N Q'' - cycPos N (headStart t) (headStart Q) - headLen N Q, N - headLen N Q'')),
      c.1 % 2 = 0 ∧ c.2 % 2 = 1 ∧ c.1 ≤ headLen N t - cycPos N (headStart t) (headStart Q) - headLen N Q ∧
        headLen N t - cycPos N (headStart t) (headStart Q) - headLen N Q + (N - headLen N t) ≤ c.1 + c.2 ∧
        c.1 + c.2 ≤ N - headLen N Q ∧ ¬ (c.1 = 0 ∧ c.2 = N - headLen N Q) ∧
        ∀ i' j, c.1 ≤ i' → i' < c.1 + c.2 → i' % 2 = 1 → (j < c.1 ∨ c.1 + c.2 ≤ j) → j < N - headLen N Q →
          j % 2 = 0 → mesh N X (vtx N (vtx N (headStart t + (cycPos N (headStart t) (headStart Q) + headLen N Q)) + i'))
            (vtx N (vtx N (headStart t + (cycPos N (headStart t) (headStart Q) + headLen N Q)) + j)) = 0 := by
    intro c hc
    obtain ⟨Q'', hQ'', rfl⟩ := mem_image.1 hc
    obtain ⟨hQ''K, hne, hsub⟩ := mem_filter.1 hQ''
    have hQ''o := hK hQ''K
    have fQ'' := pkR_b_head_facts hE hQ''o
    obtain ⟨b1, b2, b3, -, -⟩ := pkR_d2_npos hE hto hQ''o (hKt Q'' hQ''K)
    have hn := pkR_d2_nest_fwd hE hto hQo hQ''o (hKt Q hQ) (hKt Q'' hQ''K) hsub
    have hne' : ¬ (cycPos N (headStart t) (headStart Q'') = cycPos N (headStart t) (headStart Q) ∧
        headLen N Q'' = headLen N Q) := by
      rintro ⟨e1, e2⟩
      by_cases h't : Q'' = t
      · rw [h't] at e2
        omega
      · exact hne (pkR_d2_pos_eq hE hto hQ''o hQo (hKt Q'' hQ''K) (hKt Q hQ) (Ne.symm h't) (Ne.symm hQt) e1 e2)
    refine ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, by dsimp only; omega,
      by dsimp only; omega, fun h => by dsimp only at h; omega, ?_⟩
    dsimp only
    intro i' j hi1 hi2 hi3 hj1 hj2 hj3
    have hzi := pkR_b_mod2 (N := N) (z := cycPos N (headStart t) (headStart Q) + headLen N Q + i') (by omega)
    have hzj := pkR_b_mod2 (N := N) (z := cycPos N (headStart t) (headStart Q) + headLen N Q + j) (by omega)
    rw [hsh i' (by omega), hsh j (by omega), pkR_mesh_comm]
    have Zi : (cycPos N (headStart t) (headStart Q) + headLen N Q + i') % N < N := Nat.mod_lt _ (by omega)
    have Zj : (cycPos N (headStart t) (headStart Q) + headLen N Q + j) % N < N := Nat.mod_lt _ (by omega)
    obtain ⟨-, -, Vi⟩ := pkR_b_posQ hE hto Zi
    obtain ⟨-, -, Vj⟩ := pkR_b_posQ hE hto Zj
    have Mi := b3 _ Zi
    have Mj := b3 _ Zj
    refine pkR_d2_mr_leg hQ''o (pkR_b_H3a hQ''K).2 hX (Mj.2 ?_) ?_ ?_ (fun h => ?_) ?_
    · omega
    · omega
    · omega
    · have := Mi.1 h
      omega
    · omega
  rw [pkR_d2_pull_above hE hK hnc hto hKt hQ hQt, pkR_b_child_omL hts1 (by omega) (by omega), ← a5, htl]
  exact pkR_d2_R6van (N := N) (a := vtx N (headStart t + (cycPos N (headStart t) (headStart Q) + headLen N Q)))
    (p := headLen N t - cycPos N (headStart t) (headStart Q) - headLen N Q) (L := N - headLen N Q)
    (L' := N - headLen N t) (by omega) ha' (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) hOT hXQ' _ hJ

/-! ### Step 2 assembled (G1–G4 + G5 part 1): `NP_N = X_t^{κ−1}·G` on `L_S`, `G|_H = ε·a_t·b_b·W` -/

theorem pkR_d2_hs_mem {N : ℕ} {Q : ℕ × ℕ} (hQ : Q ∈ oddDiagonals N) : headStart Q ∈ oddSide N Q := by
  obtain ⟨q1, q2⟩ := Q
  exact pkR_b_head_ne hQ

/-- A coordinate of the point `pkR_subX N f X` as a polynomial in `X`. -/
noncomputable def pkR_d2_subP (N : ℕ) (f : ℕ → ℕ) (d : ℕ × ℕ) : MvPolynomial (ℕ × ℕ) ℚ :=
  planarP ℚ N (f d.1) (f d.2)

theorem pkR_d2_subP_eval (N : ℕ) (f : ℕ → ℕ) (X : ℕ × ℕ → ℚ) (d : ℕ × ℕ) :
    MvPolynomial.eval X (pkR_d2_subP N f d) = pkR_subX N f X d := by
  show MvPolynomial.eval X (planarP ℚ N (f d.1) (f d.2)) = planar N X (f d.1) (f d.2)
  rw [planarP_hom (MvPolynomial.eval X) N (f d.1) (f d.2)]
  simp only [MvPolynomial.eval_X]

/-- A polynomial read at a `pkR_subX` point is a polynomial in `X`. -/
theorem pkR_d2_eval_sub (N : ℕ) (f : ℕ → ℕ) (X : ℕ × ℕ → ℚ) (P : MvPolynomial (ℕ × ℕ) ℚ) :
    MvPolynomial.eval (pkR_subX N f X) P = MvPolynomial.eval X (MvPolynomial.aeval (pkR_d2_subP N f) P) := by
  rw [pkR_eval_aeval]
  exact congrArg (fun Y => MvPolynomial.eval Y P) (funext fun d => (pkR_d2_subP_eval N f X d).symm)

/-- R15's `D′` at the Ω point of `(Q, c)`, as a polynomial in `X` (product over the non-member odd diagonals of `Ω`). -/
noncomputable def pkR_d2_Dp (N : ℕ) (K : Finset (ℕ × ℕ)) (Q c : ℕ × ℕ) : MvPolynomial (ℕ × ℕ) ℚ :=
  Finset.prod ((oddDiagonals (pkR_b_omM N Q c)).filter (fun Q' => Q' ∉
      ((pkR_d2_above N (pkR_d2_below N K Q) c).image (pkR_b_omI N Q c)).image (pkR_mchord (pkR_b_omD N Q c))))
    (fun Q' => pkR_d2_subP N (pkR_b_omL N (headStart Q) (cycPos N (headStart Q) (headStart c)) (headLen N c)) Q')

theorem pkR_d2_Dp_eval (N : ℕ) (K : Finset (ℕ × ℕ)) (Q c : ℕ × ℕ) (X : ℕ × ℕ → ℚ) :
    MvPolynomial.eval X (pkR_d2_Dp N K Q c) =
      Finset.prod ((oddDiagonals (pkR_b_omM N Q c)).filter (fun Q' => Q' ∉
        ((pkR_d2_above N (pkR_d2_below N K Q) c).image (pkR_b_omI N Q c)).image (pkR_mchord (pkR_b_omD N Q c))))
      (fun Q' => pkR_b_omX N Q c X Q') := by
  unfold pkR_d2_Dp
  rw [map_prod]
  exact prod_congr rfl fun Q' _ => pkR_d2_subP_eval _ _ _ _

/-- The non-member product of [Res] on `H` (before its identification as `∏_{Q ∈ J} X_Q`, gap G5 part 2): the crossing
chords of `t`, R15's `D′` at `Ω(t, b)`, and the crossing chords of `b` inside the head child of `t`. -/
noncomputable def pkR_d2_W (N : ℕ) (K : Finset (ℕ × ℕ)) (t b : ℕ × ℕ) : MvPolynomial (ℕ × ℕ) ℚ :=
  if t = b then pkR_b_cross ℚ N K t else
    pkR_b_cross ℚ N K t * pkR_d2_Dp N K t b * MvPolynomial.rename (relab N (headStart t))
      (pkR_b_cross ℚ (headLen N t + 1) (pkR_b_pull N (headStart t) (headLen N t + 1) K) (pkR_b_cc N t b))

/-- The polynomial `G` of [Res] (`pkR_d2_main`): top-down terms (R2′), A-side terms (R2A′) with R15's constants `ε` and
remainders `F` (read through `pkR_d2_subP`), and the ¬K remainder. -/
noncomputable def pkR_d2_G (N : ℕ) (K : Finset (ℕ × ℕ)) (t : ℕ × ℕ) (ε : ℕ × ℕ → ℕ × ℕ → ℚ)
    (F : ℕ × ℕ → ℕ × ℕ → MvPolynomial (ℕ × ℕ) ℚ) : MvPolynomial (ℕ × ℕ) ℚ :=
  ∑ Q ∈ K, MvPolynomial.rename (relab N (tailStart Q))
      (pkR_b_NP ℚ (tailLen N Q + 1) (pkR_b_pull N (tailStart Q) (tailLen N Q + 1) K)) *
    pkR_b_cross ℚ N K Q *
    (∑ c ∈ pkR_d2_below N K Q, MvPolynomial.rename (relab N (headStart c))
        (pkR_b_NP ℚ (headLen N c + 1) (pkR_b_pull N (headStart c) (headLen N c + 1) K)) *
      (MvPolynomial.C (ε Q c) * pkR_d2_Dp N K Q c + MvPolynomial.X t *
        MvPolynomial.aeval (pkR_d2_subP N (pkR_b_omL N (headStart Q) (cycPos N (headStart Q) (headStart c))
          (headLen N c))) (F Q c)) *
      MvPolynomial.rename (relab N (headStart Q))
        (pkR_b_cross ℚ (headLen N Q + 1) (pkR_b_pull N (headStart Q) (headLen N Q + 1) K) (pkR_b_cc N Q c)) +
      MvPolynomial.rename (relab N (headStart Q))
        (pkR_b_NP ℚ (headLen N Q + 1) (pkR_b_pull N (headStart Q) (headLen N Q + 1) K))) +
  MvPolynomial.X t * pkR_b_NP ℚ N K

set_option maxHeartbeats 2000000 in
/-- **[Res] in numerator form for every `ResChildInput` instance, up to the non-member product** (PREFORM-Res §7 step 2;
G1–G4 of §3 'd' and the polynomial half of G5): with `K` the class of `t` (crossing members allowed),
`NP_N = X_t^{κ−1} · G` on `L_S`, and on `H = L_S ∩ {X_t = 0}`, `G = ε · a_t · b_b · W` with `ε ≠ 0` (R15's constant of
`Ω(t, b)`, or `1` when `t = b`) and `W = pkR_d2_W` (crossing chords of `t`, `D′` of `Ω(t, b)`, crossing chords of `b`
inside `A(t)`). What `pkR_d_ResNum` still needs is `W = ∏_{Q ∈ J} X_Q` with `J ⊆ odd ∖ K` (gap G5 part 2). -/
theorem pkR_d2_main {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} {t b : ℕ × ℕ}
    (ht : t ∈ poleChords N S) (hb : b ∈ hitClass N S t)
    (hint : ∀ Q ∈ hitClass N S t, oddSide N b ⊆ oddSide N Q ∧ oddSide N Q ⊆ oddSide N t)
    (hH2' : ∀ Q ∈ hitClass N S t, ∀ X : ℕ × ℕ → ℚ, OnLocus N S X → X Q = X t) :
    ∃ (G : MvPolynomial (ℕ × ℕ) ℚ) (ε : ℚ), ε ≠ 0 ∧
      (∀ X : ℕ × ℕ → ℚ, OnLocus N S X →
        MvPolynomial.eval X (NP ℚ N) = X t ^ ((hitClass N S t).card - 1) * MvPolynomial.eval X G) ∧
      ∀ X : ℕ × ℕ → ℚ, OnLocus N S X → X t = 0 → MvPolynomial.eval X G =
        ε * MvPolynomial.eval (X ∘ relab N (tailStart t)) (NP ℚ (tailLen N t + 1)) *
          MvPolynomial.eval (X ∘ relab N (headStart b)) (NP ℚ (headLen N b + 1)) *
          MvPolynomial.eval X (pkR_d2_W N (hitClass N S t) t b) := by
  classical
  have htK : t ∈ hitClass N S t := mem_filter.2 ⟨ht, rfl⟩
  have hK : hitClass N S t ⊆ oddDiagonals N := fun Q hQ => (pkR_b_H3a hQ).1
  have hto := hK htK
  have hbo := hK hb
  have hnc : ∀ Q ∈ hitClass N S t, ∀ Q' ∈ hitClass N S t, ¬ Crosses Q' Q →
      oddSide N Q ⊆ oddSide N Q' ∨ oddSide N Q' ⊆ oddSide N Q := by
    intro Q hQ Q' hQ' hc
    rcases (pkR_b_chain hbo hto (hK hQ') (hK hQ) (hint Q' hQ').1 (hint Q' hQ').2 (hint Q hQ).1
      (hint Q hQ).2).1 hc with e | e
    · exact Or.inr e
    · exact Or.inl e
  have hℓ : ∀ c ∈ hitClass N S t, headStart b ∈ oddSide N c := fun c hc => (hint c hc).1 (pkR_d2_hs_mem hbo)
  have hKt : ∀ Q ∈ hitClass N S t, oddSide N Q ⊆ oddSide N t := fun Q hQ => (hint Q hQ).2
  have hbK : ∀ Q ∈ hitClass N S t, oddSide N b ⊆ oddSide N Q := fun Q hQ => (hint Q hQ).1
  have hΩ : ∀ Q c : ℕ × ℕ, ∃ (ε : ℚ) (F : MvPolynomial (ℕ × ℕ) ℚ), Q ∈ hitClass N S t →
      c ∈ pkR_d2_below N (hitClass N S t) Q → ε ≠ 0 ∧ ∀ X : ℕ × ℕ → ℚ, OnLocus N S X →
        MvPolynomial.eval (pkR_b_omX N Q c X) (NP ℚ (pkR_b_omM N Q c)) =
          X Q ^ (pkR_d2_above N (pkR_d2_below N (hitClass N S t) Q) c).card *
            (ε * X Q * MvPolynomial.eval X (pkR_d2_Dp N (hitClass N S t) Q c) +
              X Q ^ 2 * MvPolynomial.eval (pkR_b_omX N Q c X) F) := by
    intro Q c
    by_cases h : Q ∈ hitClass N S t ∧ c ∈ pkR_d2_below N (hitClass N S t) Q
    · obtain ⟨hQ, hc⟩ := h
      obtain ⟨hcK, hcQ, hcs⟩ := mem_filter.1 hc
      obtain ⟨ε, F, hε, hF⟩ := pkR_d2_omegaQ hN hE hQ hcK hcs (fun e => hcQ e.symm)
      exact ⟨ε, F, fun _ _ => ⟨hε, fun X hX => by rw [hF X hX, pkR_d2_Dp_eval]⟩⟩
    · exact ⟨1, 0, fun hQ hc => absurd ⟨hQ, hc⟩ h⟩
  choose εf Ff hεF using hΩ
  -- the value of `G` at a point of `L_S`
  have hval : ∀ X : ℕ × ℕ → ℚ, OnLocus N S X →
      MvPolynomial.eval X (NP ℚ N) = X t ^ ((hitClass N S t).card - 1) *
        MvPolynomial.eval X (pkR_d2_G N (hitClass N S t) t εf Ff) := by
    intro X hX
    have hx : ∀ Q ∈ hitClass N S t, X Q = X t := fun Q hQ => hH2' Q hQ X hX
    have htop := pkR_d2_top_ind (by omega) hE hK hnc hx (hitClass N S t) subset_rfl (fun _ _ _ h _ => h)
    rw [Finset.sdiff_self, pkR_b_NP_empty] at htop
    have key := pkR_d2_count (hitClass N S t) (card_pos.2 ⟨t, htK⟩) (X t)
      (MvPolynomial.eval X (pkR_b_NP ℚ N (hitClass N S t))) (MvPolynomial.eval X (NP ℚ N))
      (fun Q => (pkR_d2_above N (hitClass N S t) Q).card + (pkR_d2_crs (hitClass N S t) Q).card)
      (fun Q => (pkR_d2_below N (hitClass N S t) Q).card)
      (fun Q => MvPolynomial.eval X (MvPolynomial.rename (relab N (headStart Q)) (NP ℚ (headLen N Q + 1))))
      (fun Q => MvPolynomial.eval X (MvPolynomial.rename (relab N (tailStart Q))
        (pkR_b_NP ℚ (tailLen N Q + 1) (pkR_b_pull N (tailStart Q) (tailLen N Q + 1) (hitClass N S t)))))
      (fun Q => MvPolynomial.eval X (pkR_b_cross ℚ N (hitClass N S t) Q))
      (fun Q => MvPolynomial.eval X (MvPolynomial.rename (relab N (headStart Q))
        (pkR_b_NP ℚ (headLen N Q + 1) (pkR_b_pull N (headStart Q) (headLen N Q + 1) (hitClass N S t)))))
      (fun Q => pkR_d2_below N (hitClass N S t) Q)
      (fun Q c => (pkR_d2_above N (pkR_d2_below N (hitClass N S t) Q) c).card)
      (fun _ c => MvPolynomial.eval X (MvPolynomial.rename (relab N (headStart c))
        (pkR_b_NP ℚ (headLen N c + 1) (pkR_b_pull N (headStart c) (headLen N c + 1) (hitClass N S t)))))
      (fun Q c => MvPolynomial.eval (pkR_b_omX N Q c X) (NP ℚ (pkR_b_omM N Q c)))
      (fun Q c => MvPolynomial.eval X (MvPolynomial.rename (relab N (headStart Q))
        (pkR_b_cross ℚ (headLen N Q + 1) (pkR_b_pull N (headStart Q) (headLen N Q + 1) (hitClass N S t))
          (pkR_b_cc N Q c))))
      εf (fun Q c => MvPolynomial.eval X (pkR_d2_Dp N (hitClass N S t) Q c))
      (fun Q c => MvPolynomial.eval X (MvPolynomial.aeval (pkR_d2_subP N (pkR_b_omL N (headStart Q)
        (cycPos N (headStart Q) (headStart c)) (headLen N c))) (Ff Q c)))
      htop (fun Q hQ => pkR_d2_part hK hnc hQ) (fun Q hQ => pkR_d2_Aside hE hK hnc hℓ hQ hx)
      (fun Q hQ c hc => by
        have hsub : pkR_d2_above N (pkR_d2_below N (hitClass N S t) Q) c ⊆ (pkR_d2_below N (hitClass N S t) Q).erase c :=
          fun y hy => mem_erase.2 ⟨(mem_filter.1 hy).2.1, (mem_filter.1 hy).1⟩
        have h1 := card_le_card hsub
        rw [card_erase_of_mem hc] at h1
        have h2 := card_pos.2 ⟨c, hc⟩
        omega)
      (fun Q hQ c hc => by
        rw [(hεF Q c hQ hc).2 X hX, hx Q hQ,
          show MvPolynomial.eval (pkR_b_omX N Q c X) (Ff Q c) = _ from pkR_d2_eval_sub _ _ X (Ff Q c)])
    rw [key]
    congr 1
    unfold pkR_d2_G
    simp only [map_add, map_mul, map_sum, MvPolynomial.eval_C, MvPolynomial.eval_X]
  refine ⟨pkR_d2_G N (hitClass N S t) t εf Ff, if t = b then 1 else εf t b, ?_, hval, ?_⟩
  · split_ifs with htb
    · exact one_ne_zero
    · exact (hεF t b htK (mem_filter.2 ⟨hb, fun e => htb e.symm, hbK t htK⟩)).1
  · intro X hX hXt
    have hx : ∀ Q ∈ hitClass N S t, X Q = X t := fun Q hQ => hH2' Q hQ X hX
    have hR17t : pkR_b_pull N (tailStart t) (tailLen N t + 1) (hitClass N S t) = ∅ :=
      pkR_b_R17_tail hto hK hKt
    have hR17b : pkR_b_pull N (headStart b) (headLen N b + 1) (hitClass N S t) = ∅ :=
      pkR_b_R17_head hbo hK hbK
    have hat : MvPolynomial.eval X (MvPolynomial.rename (relab N (tailStart t))
        (pkR_b_NP ℚ (tailLen N t + 1) (pkR_b_pull N (tailStart t) (tailLen N t + 1) (hitClass N S t)))) =
        MvPolynomial.eval (X ∘ relab N (tailStart t)) (NP ℚ (tailLen N t + 1)) := by
      rw [hR17t, pkR_b_NP_empty, MvPolynomial.eval_rename]
    have hbb : MvPolynomial.eval X (MvPolynomial.rename (relab N (headStart b))
        (pkR_b_NP ℚ (headLen N b + 1) (pkR_b_pull N (headStart b) (headLen N b + 1) (hitClass N S t)))) =
        MvPolynomial.eval (X ∘ relab N (headStart b)) (NP ℚ (headLen N b + 1)) := by
      rw [hR17b, pkR_b_NP_empty, MvPolynomial.eval_rename]
    have ha : ∀ Q ∈ hitClass N S t, Q ≠ t → MvPolynomial.eval X (MvPolynomial.rename (relab N (tailStart Q))
        (pkR_b_NP ℚ (tailLen N Q + 1) (pkR_b_pull N (tailStart Q) (tailLen N Q + 1) (hitClass N S t)))) = 0 :=
      fun Q hQ hQt => pkR_d2_avan hN hE htK hQ hQt hKt hnc hX (by rw [hx Q hQ, hXt])
    unfold pkR_d2_G pkR_d2_W
    simp only [map_add, map_mul, map_sum, MvPolynomial.eval_C, MvPolynomial.eval_X, hXt, zero_mul, add_zero]
    by_cases htb : t = b
    · subst htb
      have hS : pkR_d2_below N (hitClass N S t) t = ∅ := by
        refine filter_eq_empty_iff.2 fun Q hQ h => h.1 ?_
        exact pkR_d2_eq_of_head (hK hQ) hto (Subset.antisymm h.2 (hbK Q hQ))
      rw [ite_eq_left_of_eq_true _ _ (eq_self t), ite_eq_left_of_eq_true _ _ (eq_self t), sum_eq_single_of_mem t htK (fun Q hQ hQt => by rw [ha Q hQ hQt, zero_mul, zero_mul]),
        hS, sum_empty, zero_add, hat, hbb]
      ring
    · have hbS : b ∈ pkR_d2_below N (hitClass N S t) t := mem_filter.2 ⟨hb, fun e => htb e.symm, hbK t htK⟩
      have hbv : ∀ c ∈ pkR_d2_below N (hitClass N S t) t, c ≠ b →
          MvPolynomial.eval X (MvPolynomial.rename (relab N (headStart c))
            (pkR_b_NP ℚ (headLen N c + 1) (pkR_b_pull N (headStart c) (headLen N c + 1) (hitClass N S t)))) = 0 :=
        fun c hc hcb => pkR_d2_bvan hN hE hb (mem_filter.1 hc).1 (hbK c (mem_filter.1 hc).1) hcb hbK hnc hX
          (by rw [hx c (mem_filter.1 hc).1, hXt])
      have hB : MvPolynomial.eval X (MvPolynomial.rename (relab N (headStart t))
          (pkR_b_NP ℚ (headLen N t + 1) (pkR_b_pull N (headStart t) (headLen N t + 1) (hitClass N S t)))) = 0 :=
        pkR_d2_bvan hN hE hb htK (hbK t htK) htb hbK hnc hX hXt
      rw [ite_eq_right_of_eq_false _ _ (eq_false htb), ite_eq_right_of_eq_false _ _ (eq_false htb),
        sum_eq_single_of_mem t htK (fun Q hQ hQt => by rw [ha Q hQ hQt, zero_mul, zero_mul]),
        sum_eq_single_of_mem b hbS (fun c hc hcb => by rw [hbv c hc hcb, zero_mul, zero_mul]), hB, add_zero, hat, hbb,
        map_mul, map_mul]
      ring

/-- The non-member product of a single-member class (`t = b`): the crossing chords of `t` that are not members. -/
theorem pkR_d2_W_self (N : ℕ) (K : Finset (ℕ × ℕ)) (t : ℕ × ℕ) :
    ((oddDiagonals N).filter (fun d => Crosses d t)) \ K ⊆ oddDiagonals N \ K ∧
      ∀ X : ℕ × ℕ → ℚ, MvPolynomial.eval X (pkR_d2_W N K t t) =
        ∏ Q ∈ ((oddDiagonals N).filter (fun d => Crosses d t)) \ K, X Q := by
  refine ⟨fun d hd => mem_sdiff.2 ⟨(mem_filter.1 (mem_sdiff.1 hd).1).1, (mem_sdiff.1 hd).2⟩, fun X => ?_⟩
  unfold pkR_d2_W pkR_b_cross
  rw [ite_eq_left_of_eq_true _ _ (eq_self t), map_prod]
  simp only [MvPolynomial.eval_X]

/-- **`pkR_d_ResNum` for every `ResChildInput` instance, given the identification of the non-member product**
(gap G5 part 2 as the single hypothesis `hW`: `W = ∏_{Q ∈ J} X_Q` with `J` odd non-members; it holds for `t = b` by
`pkR_d2_W_self`). This is the form `pkR_d_reduce`'s `hRes` consumes. -/
theorem pkR_d2_ResNum_holds {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    (hW : ∀ (S : Finset (ℕ × ℕ)) (t b : ℕ × ℕ), InFpi N S → t ∈ poleChords N S → b ∈ hitClass N S t →
      (∀ Q ∈ hitClass N S t, oddSide N b ⊆ oddSide N Q ∧ oddSide N Q ⊆ oddSide N t) → t ≠ b →
      ∃ J : Finset (ℕ × ℕ), J ⊆ oddDiagonals N \ hitClass N S t ∧
        ∀ X : ℕ × ℕ → ℚ, OnLocus N S X → X t = 0 →
          MvPolynomial.eval X (pkR_d2_W N (hitClass N S t) t b) = ∏ Q ∈ J, X Q) :
    ∀ (S : Finset (ℕ × ℕ)) (t b : ℕ × ℕ), InFpi N S → t ∈ poleChords N S → b ∈ hitClass N S t →
      (∀ Q ∈ hitClass N S t, oddSide N b ⊆ oddSide N Q ∧ oddSide N Q ⊆ oddSide N t) →
      (∀ Q ∈ oddDiagonals N,
        (∃ c : ℚ, c ≠ 0 ∧ ∀ X : ℕ × ℕ → ℚ, OnLocus N S X → X Q = c * X t) ↔ Q ∈ hitClass N S t) →
      (∀ Q ∈ hitClass N S t, ∀ X : ℕ × ℕ → ℚ, OnLocus N S X → X Q = X t) → pkR_d_ResNum N S t b := by
  intro S t b hF ht hb hint _ hH2'
  have hEN : N % 2 = 0 := Nat.even_iff.1 hE
  obtain ⟨G, ε, hε, hNP, hH⟩ := pkR_d2_main hN hEN ht hb hint hH2'
  by_cases htb : t = b
  · subst htb
    obtain ⟨hJ, hWJ⟩ := pkR_d2_W_self N (hitClass N S t) t
    exact ⟨G, _, ε, _, hε, hJ, hNP, fun X hX hXt => by rw [hH X hX hXt, hWJ X]⟩
  · obtain ⟨J, hJ, hWJ⟩ := hW S t b hF ht hb hint htb
    exact ⟨G, _, ε, J, hε, hJ, hNP, fun X hX hXt => by rw [hH X hX hXt, hWJ X hX hXt]⟩

/-- **`resChild_input` modulo gap G5 part 2** (the non-member product `W = ∏_{Q∈J} X_Q`, hypothesis `hW`): d's reduction
`pkR_d_reduce` with [Res] from `pkR_d2_ResNum_holds` and [Child](1) from pkgRes-ch (`pkR_ch_childB`, `pkR_ch_childA`). -/
theorem pkR_d2_final {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    (hW : ∀ (S : Finset (ℕ × ℕ)) (t b : ℕ × ℕ), InFpi N S → t ∈ poleChords N S → b ∈ hitClass N S t →
      (∀ Q ∈ hitClass N S t, oddSide N b ⊆ oddSide N Q ∧ oddSide N Q ⊆ oddSide N t) → t ≠ b →
      ∃ J : Finset (ℕ × ℕ), J ⊆ oddDiagonals N \ hitClass N S t ∧
        ∀ X : ℕ × ℕ → ℚ, OnLocus N S X → X t = 0 →
          MvPolynomial.eval X (pkR_d2_W N (hitClass N S t) t b) = ∏ Q ∈ J, X Q) :
    ResChildInput N :=
  pkR_d_reduce hN hE (pkR_d2_ResNum_holds hN hE hW) (pkR_ch_childB hN hE) (pkR_ch_childA hN hE)


-- pkgRes-w (R12-P7b-pkgRes-w, claude-opus-5-5): the last gap `hW` of `pkR_d2_final` (G5 part 2, thread §3 'd2'):
-- the non-member product `pkR_d2_W` is `∏_{Q ∈ J} X_Q` with `J ⊆ odd ∖ K`, then the body of `resChild_input`.

/-- The Ω(t, b) diagonals read as child diagonals of the head child of `t` (positions `olo + 1`). -/
def pkR_w_om (p L' : ℕ) (d : ℕ × ℕ) : ℕ × ℕ := (pkR_b_olo p L' d.1 + 1, pkR_b_olo p L' d.2 + 1)

/-- An Ω diagonal is an odd diagonal of the head child of `t` that does not cross the child chord of `b`. -/
theorem pkR_w_om_mem {p L L' : ℕ} (h3 : 3 ≤ L') (hL' : L' % 2 = 1) (hpL : p + L' ≤ L) {d : ℕ × ℕ}
    (hd : d ∈ oddDiagonals (L - L' + 2)) :
    pkR_w_om p L' d ∈ oddDiagonals (L + 1) ∧ ¬ Crosses (pkR_w_om p L' d) (p + 1, p + L' + 1) := by
  obtain ⟨i, j⟩ := d
  have h := pkR_b_odd_iff.1 hd
  have e1 := pkR_b_olo_eq p L' i
  have e2 := pkR_b_olo_eq p L' j
  show (pkR_b_olo p L' i + 1, pkR_b_olo p L' j + 1) ∈ oddDiagonals (L + 1) ∧
    ¬ Crosses (pkR_b_olo p L' i + 1, pkR_b_olo p L' j + 1) (p + 1, p + L' + 1)
  refine ⟨pkR_b_odd_iff.2 ?_, ?_⟩
  · omega
  · unfold Crosses
    dsimp only
    omega

/-- `pkR_w_om` is injective on pairs of positive legs. -/
theorem pkR_w_om_inj {p L' : ℕ} (h1 : 1 ≤ L') {d d' : ℕ × ℕ} (hd : 1 ≤ d.1 ∧ 1 ≤ d.2) (hd' : 1 ≤ d'.1 ∧ 1 ≤ d'.2)
    (h : pkR_w_om p L' d = pkR_w_om p L' d') : d = d' := by
  obtain ⟨i, j⟩ := d
  obtain ⟨i', j'⟩ := d'
  have a1 := congrArg Prod.fst h
  have a2 := congrArg Prod.snd h
  change pkR_b_olo p L' i + 1 = pkR_b_olo p L' i' + 1 at a1
  change pkR_b_olo p L' j + 1 = pkR_b_olo p L' j' + 1 at a2
  dsimp only at hd hd'
  have e1 := pkR_b_olo_eq p L' i
  have e2 := pkR_b_olo_eq p L' j
  have e3 := pkR_b_olo_eq p L' i'
  have e4 := pkR_b_olo_eq p L' j'
  exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)

/-- `relab` of an odd child diagonal is an odd parent diagonal. -/
theorem pkR_w_relab_odd {N s n : ℕ} (hE : N % 2 = 0) (hs : 1 ≤ s ∧ s ≤ N) (hn : n ≤ N) {d : ℕ × ℕ}
    (hd : d ∈ oddDiagonals n) : relab N s d ∈ oddDiagonals N := by
  have hdd := mem_filter.1 hd
  refine mem_filter.2 ⟨pkR_b_relab_mem hs hn hdd.1, ?_⟩
  obtain ⟨p1, p2, e, h1, h2⟩ := pkR_b_relab_eq (N := N) (s := s) (n := n) (by omega) (by omega) hdd.1
  have hd' := mem_diagonals.1 hdd.1
  have hpar := hdd.2
  rw [e]
  dsimp only
  omega

/-- `relab N s` is injective on a set of odd child diagonals. -/
theorem pkR_w_relab_injOn {N s n : ℕ} (hs : 1 ≤ s ∧ s ≤ N) (hn : n ≤ N) {A : Finset (ℕ × ℕ)}
    (hA : A ⊆ oddDiagonals n) : Set.InjOn (relab N s) ↑A := by
  intro a ha a' ha' e
  have h1 := mem_diagonals.1 (mem_filter.1 (hA ha)).1
  have h2 := mem_diagonals.1 (mem_filter.1 (hA ha')).1
  exact pkR_b_relab_inj hs hn ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩ e

/-- The Ω point at an Ω diagonal is the relabelled child variable. -/
theorem pkR_w_omX {N : ℕ} {t b : ℕ × ℕ} (hs : 1 ≤ headStart t ∧ headStart t ≤ N) (hn : headLen N t + 1 ≤ N)
    (X : ℕ × ℕ → ℚ) {d : ℕ × ℕ}
    (hd : pkR_w_om (cycPos N (headStart t) (headStart b)) (headLen N b) d ∈ diagonals (headLen N t + 1)) :
    pkR_b_omX N t b X d =
      X (relab N (headStart t) (pkR_w_om (cycPos N (headStart t) (headStart b)) (headLen N b) d)) := by
  rw [pkR_b_relab_subX hs hn X hd]
  unfold pkR_b_omX pkR_subX pkR_b_omL pkR_w_om
  dsimp only
  simp only [show ∀ a, a + 1 + headStart t - 1 = headStart t + a from fun a => by omega]

/-- An Ω diagonal of `(t, b)` that is not the standard image of a member strictly between is not a member. -/
theorem pkR_w_notK {N : ℕ} (hE : N % 2 = 0) {K : Finset (ℕ × ℕ)} {t b Q' : ℕ × ℕ} (hto : t ∈ oddDiagonals N)
    (hbo : b ∈ oddDiagonals N) (hbt : oddSide N b ⊆ oddSide N t) (htb : t ≠ b) (hK : K ⊆ oddDiagonals N)
    (hint : ∀ c ∈ K, oddSide N b ⊆ oddSide N c ∧ oddSide N c ⊆ oddSide N t)
    (hQ' : Q' ∈ oddDiagonals (pkR_b_omM N t b))
    (hex : Q' ∉ ((pkR_d2_above N (pkR_d2_below N K t) b).image (pkR_b_omI N t b)).image
      (pkR_mchord (pkR_b_omD N t b))) :
    relab N (headStart t) (pkR_w_om (cycPos N (headStart t) (headStart b)) (headLen N b) Q') ∉ K := by
  intro hc
  generalize hcd : relab N (headStart t) (pkR_w_om (cycPos N (headStart t) (headStart b)) (headLen N b) Q') = c
    at hc
  have f1 := pkR_b_head_facts hE hto
  have fb := pkR_b_head_facts hE hbo
  obtain ⟨p0, p1, p2, -⟩ := pkR_b_nest_pos hE hto hbo hbt htb
  have hco := hK hc
  have fc := pkR_b_head_facts hE hco
  obtain ⟨hbc, hct⟩ := hint c hc
  obtain ⟨q0, q1, -, q3, -⟩ := pkR_d2_npos hE hto hco hct
  have hrc : relab N (headStart t) (cycPos N (headStart t) (headStart c) + 1,
      cycPos N (headStart t) (headStart c) + headLen N c + 1) = c :=
    pkR_b_relab_head hco ⟨f1.1, f1.2.1⟩ (by omega) q3
  obtain ⟨i, j⟩ := Q'
  have hij := pkR_b_odd_iff.1 hQ'
  have hm : pkR_b_omM N t b = headLen N t - headLen N b + 2 := rfl
  rw [hm] at hij
  have e1 := pkR_b_olo_eq (cycPos N (headStart t) (headStart b)) (headLen N b) i
  have e2 := pkR_b_olo_eq (cycPos N (headStart t) (headStart b)) (headLen N b) j
  have hω := pkR_b_relab_inj (N := N) (s := headStart t) (n := headLen N t + 1) ⟨f1.1, f1.2.1⟩ (by omega)
    (d := pkR_w_om (cycPos N (headStart t) (headStart b)) (headLen N b) (i, j))
    (d' := (cycPos N (headStart t) (headStart c) + 1, cycPos N (headStart t) (headStart c) + headLen N c + 1))
    (by
      show 1 ≤ pkR_b_olo (cycPos N (headStart t) (headStart b)) (headLen N b) i + 1 ∧
        pkR_b_olo (cycPos N (headStart t) (headStart b)) (headLen N b) i + 1 <
          pkR_b_olo (cycPos N (headStart t) (headStart b)) (headLen N b) j + 1 ∧
        pkR_b_olo (cycPos N (headStart t) (headStart b)) (headLen N b) j + 1 ≤ headLen N t + 1
      omega) (by dsimp only; omega) (by rw [hcd, hrc])
  have w1 := congrArg Prod.fst hω
  have w2 := congrArg Prod.snd hω
  change pkR_b_olo (cycPos N (headStart t) (headStart b)) (headLen N b) i + 1 =
    cycPos N (headStart t) (headStart c) + 1 at w1
  change pkR_b_olo (cycPos N (headStart t) (headStart b)) (headLen N b) j + 1 =
    cycPos N (headStart t) (headStart c) + headLen N c + 1 at w2
  by_cases hct' : c = t
  · subst hct'
    omega
  by_cases hcb : c = b
  · subst hcb
    omega
  have hn := (pkR_d2_nest_iff hE hto hbo hco hbt hct htb (fun e => hct' e.symm)).1 hbc
  have hmem : c ∈ pkR_d2_above N (pkR_d2_below N K t) b :=
    mem_filter.2 ⟨mem_filter.2 ⟨hc, hct', hct⟩, hcb, hbc⟩
  refine hex (mem_image.2 ⟨pkR_b_omI N t b c, mem_image.2 ⟨c, hmem, rfl⟩, ?_⟩)
  unfold pkR_mchord pkR_b_omD pkR_b_omI
  exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)

set_option maxHeartbeats 1000000 in
/-- **The non-member product is a product of odd non-member variables** (gap G5 part 2 for `t ≠ b`): with
`J = J₁ ∪ relab(ω(D) ∪ C₃)` — `J₁` the non-member odd chords crossing `t`, `D` the index set of R15's `D′` at `Ω(t, b)`
(read in the head child of `t` by `pkR_w_om`), `C₃` the non-member odd child chords crossing the child chord of `b`. -/
theorem pkR_w_core {N : ℕ} (hE : N % 2 = 0) {K : Finset (ℕ × ℕ)} {t b : ℕ × ℕ} (hto : t ∈ oddDiagonals N)
    (hbo : b ∈ oddDiagonals N) (hbt : oddSide N b ⊆ oddSide N t) (htb : t ≠ b) (hK : K ⊆ oddDiagonals N)
    (hint : ∀ c ∈ K, oddSide N b ⊆ oddSide N c ∧ oddSide N c ⊆ oddSide N t) :
    ∃ J : Finset (ℕ × ℕ), J ⊆ oddDiagonals N \ K ∧
      ∀ X : ℕ × ℕ → ℚ, MvPolynomial.eval X (pkR_d2_W N K t b) = ∏ Q ∈ J, X Q := by
  classical
  have f1 := pkR_b_head_facts hE hto
  have fb := pkR_b_head_facts hE hbo
  obtain ⟨p0, p1, p2, -⟩ := pkR_b_nest_pos hE hto hbo hbt htb
  have hs : 1 ≤ headStart t ∧ headStart t ≤ N := ⟨f1.1, f1.2.1⟩
  have hn : headLen N t + 1 ≤ N := by omega
  have hm : pkR_b_omM N t b = headLen N t - headLen N b + 2 := rfl
  have hcc : pkR_b_cc N t b = (cycPos N (headStart t) (headStart b) + 1,
      cycPos N (headStart t) (headStart b) + headLen N b + 1) := rfl
  -- the three index sets
  set D := (oddDiagonals (pkR_b_omM N t b)).filter (fun Q' => Q' ∉
      ((pkR_d2_above N (pkR_d2_below N K t) b).image (pkR_b_omI N t b)).image (pkR_mchord (pkR_b_omD N t b)))
    with hD
  set C3 := ((oddDiagonals (headLen N t + 1)).filter (fun d => Crosses d (pkR_b_cc N t b))) \
      pkR_b_pull N (headStart t) (headLen N t + 1) K with hC3
  set J1 := ((oddDiagonals N).filter (fun d => Crosses d t)) \ K with hJ1
  set ω := pkR_w_om (cycPos N (headStart t) (headStart b)) (headLen N b) with hωd
  have hDm : ∀ Q' ∈ D, ω Q' ∈ oddDiagonals (headLen N t + 1) ∧ ¬ Crosses (ω Q') (pkR_b_cc N t b) := by
    intro Q' hQ'
    have h := (mem_filter.1 hQ').1
    rw [hm] at h
    rw [hcc]
    exact pkR_w_om_mem fb.2.2.2.2.1 fb.2.2.2.1 p1 h
  have hA : D.image ω ∪ C3 ⊆ oddDiagonals (headLen N t + 1) := by
    intro a ha
    rcases mem_union.1 ha with h | h
    · obtain ⟨Q', hQ', rfl⟩ := mem_image.1 h
      exact (hDm Q' hQ').1
    · exact (mem_filter.1 (mem_sdiff.1 h).1).1
  have hdisj2 : Disjoint (D.image ω) C3 := by
    refine disjoint_left.2 fun a ha hC => ?_
    obtain ⟨Q', hQ', rfl⟩ := mem_image.1 ha
    exact (hDm Q' hQ').2 (mem_filter.1 (mem_sdiff.1 hC).1).2
  have hdisj1 : Disjoint J1 ((D.image ω ∪ C3).image (relab N (headStart t))) := by
    refine disjoint_left.2 fun x hx hy => ?_
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hy
    have hx' := mem_filter.1 (mem_sdiff.1 hx).1
    have hpull := pkR_d2_pull_head hto (K := {relab N (headStart t) a})
      (fun Q hQ => by rw [mem_singleton.1 hQ]; exact hx'.1)
      (fun Q hQ => Or.inr (by rw [mem_singleton.1 hQ]; exact hx'.2))
    have hmem : a ∈ pkR_b_pull N (headStart t) (headLen N t + 1) {relab N (headStart t) a} :=
      mem_filter.2 ⟨(mem_filter.1 (hA ha)).1, mem_singleton_self _⟩
    rw [hpull] at hmem
    simp at hmem
  have hinjR := pkR_w_relab_injOn hs hn hA
  have hinjω : Set.InjOn ω ↑D := by
    intro Q₁ h₁ Q₂ h₂ e
    have a1 := mem_diagonals.1 (mem_filter.1 (mem_filter.1 h₁).1).1
    have a2 := mem_diagonals.1 (mem_filter.1 (mem_filter.1 h₂).1).1
    exact pkR_w_om_inj (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ e
  refine ⟨J1 ∪ (D.image ω ∪ C3).image (relab N (headStart t)), ?_, fun X => ?_⟩
  · intro x hx
    rcases mem_union.1 hx with h | h
    · exact mem_sdiff.2 ⟨(mem_filter.1 (mem_sdiff.1 h).1).1, (mem_sdiff.1 h).2⟩
    · obtain ⟨a, ha, rfl⟩ := mem_image.1 h
      refine mem_sdiff.2 ⟨pkR_w_relab_odd hE hs hn (hA ha), ?_⟩
      rcases mem_union.1 ha with h' | h'
      · obtain ⟨Q', hQ', rfl⟩ := mem_image.1 h'
        exact pkR_w_notK hE hto hbo hbt htb hK hint (mem_filter.1 hQ').1 (mem_filter.1 hQ').2
      · intro hK'
        exact (mem_sdiff.1 h').2 (mem_filter.2 ⟨(mem_filter.1 (mem_filter.1 (mem_sdiff.1 h').1).1).1, hK'⟩)
  · rw [prod_union hdisj1, prod_image hinjR, prod_union hdisj2, prod_image hinjω]
    unfold pkR_d2_W
    rw [ite_eq_right_of_eq_false _ _ (eq_false htb), map_mul, map_mul, pkR_d2_Dp_eval, MvPolynomial.eval_rename]
    unfold pkR_b_cross
    rw [map_prod, map_prod]
    simp only [MvPolynomial.eval_X, Function.comp_apply]
    rw [mul_assoc]
    congr 2
    refine prod_congr rfl fun Q' hQ' => ?_
    exact pkR_w_omX hs hn X (mem_filter.1 (hDm Q' hQ').1).1

/-- **Gap G5 part 2 (`hW` of `pkR_d2_final`)**, in exactly the form `pkR_d2_ResNum_holds` takes. -/
theorem pkR_w_hW {N : ℕ} (hE : Even N) :
    ∀ (S : Finset (ℕ × ℕ)) (t b : ℕ × ℕ), InFpi N S → t ∈ poleChords N S → b ∈ hitClass N S t →
      (∀ Q ∈ hitClass N S t, oddSide N b ⊆ oddSide N Q ∧ oddSide N Q ⊆ oddSide N t) → t ≠ b →
      ∃ J : Finset (ℕ × ℕ), J ⊆ oddDiagonals N \ hitClass N S t ∧
        ∀ X : ℕ × ℕ → ℚ, OnLocus N S X → X t = 0 →
          MvPolynomial.eval X (pkR_d2_W N (hitClass N S t) t b) = ∏ Q ∈ J, X Q := by
  intro S t b _ ht hb hint htb
  have hEN : N % 2 = 0 := Nat.even_iff.1 hE
  have htK : t ∈ hitClass N S t := mem_filter.2 ⟨ht, rfl⟩
  have hK : hitClass N S t ⊆ oddDiagonals N := fun Q hQ => (pkR_b_H3a hQ).1
  obtain ⟨J, hJ, hWJ⟩ := pkR_w_core hEN (hK htK) (hK hb) (hint b hb).2 htb hK hint
  exact ⟨J, hJ, fun X _ _ => hWJ X⟩

/-- **`resChild_input`, fully assembled** (the target body of `pkgRes/target.lean`): `pkR_d2_final` with
`hW := pkR_w_hW`. -/
theorem pkR_w_target_check {N : ℕ} (hN : 6 ≤ N) (hE : Even N) : ResChildInput N :=
  pkR_d2_final hN hE (pkR_w_hW hE)

/-- `sorry` (pkgRes, M3; uses pkgChild) · the [Res] + [Child](1) input at every even `N ≥ 6`. -/
theorem resChild_input {N : ℕ} (hN : 6 ≤ N) (hE : Even N) : ResChildInput N :=
  pkR_d2_final hN hE (pkR_w_hW hE)

/-- Helper (pkgST): a sorted pair `a ≤ b` of legs of `1..N` separated by `G ⊆ 1..N` is a member of `S_G`. -/
theorem pkS_mem_sep {N : ℕ} {G : Finset ℕ} (hG : G ⊆ Icc 1 N) {a b : ℕ} (ha : a ∈ Icc 1 N) (hb : b ∈ Icc 1 N)
    (hab : a ≤ b) (h : InST G a b) : (a, b) ∈ sepPairs N G := by
  obtain ⟨haG, hbG, ⟨t, htG, ht1, ht2⟩, ⟨s, hsG, hs⟩⟩ := h
  have hs' := mem_Icc.1 (hG hsG)
  have ha' := mem_Icc.1 ha
  have hb' := mem_Icc.1 hb
  refine mem_filter.2 ⟨?_, ⟨haG, hbG, ⟨t, htG, ht1, ht2⟩, ⟨s, hsG, hs⟩⟩⟩
  show (a, b) ∈ (Icc 1 N ×ˢ Icc 1 N).filter (fun p => p.1 + 2 ≤ p.2 ∧ ¬ (p.1 = 1 ∧ p.2 = N))
  refine mem_filter.2 ⟨mem_product.2 ⟨ha, hb⟩, ?_⟩
  show a + 2 ≤ b ∧ ¬ (a = 1 ∧ b = N)
  omega

/-- Helper (pkgST): the label bridge `L_{S_G} ⊆ Z_G` (every tile of `S_G`, in either order, vanishes on `L_{S_G}`). -/
theorem pkS_onZT {N : ℕ} {G : Finset ℕ} (hG : G ⊆ Icc 1 N) {X : ℕ × ℕ → ℚ} (hX : OnLocus N (sepPairs N G) X) :
    OnZT N G X := by
  intro a ha b hb h
  rcases le_total a b with hab | hab
  · exact hX (a, b) (pkS_mem_sep hG ha hb hab h)
  · obtain ⟨haG, hbG, ⟨t, htG, ht1, ht2⟩, ⟨s, hsG, hs⟩⟩ := h
    have h' : InST G b a := ⟨hbG, haG, ⟨t, htG, by omega, by omega⟩, ⟨s, hsG, by omega⟩⟩
    rw [pkI_mesh_symm]
    exact hX (b, a) (pkS_mem_sep hG hb ha hab h')

/-- Helper (pkgST): the leg set of an admissible `G` lies in `1..N`. -/
theorem pkS_sub {N r : ℕ} {G : Finset ℕ} (h : Admissible N r G) : G ⊆ Icc 1 N := by
  obtain ⟨hs, -, -⟩ := h
  exact hs

/-- `sorry` (pkgST, M3; from 3c-b's `nlsm_zero_on_ZT`) · the S_T zero at every even `N ≥ 6`. -/
theorem stZero_input {N : ℕ} (hN : 6 ≤ N) (hE : Even N) : STZeroInput N := by
  intro G hG
  rw [ampZeroOn_iff_nlsmZeroOn]
  intro X hL hX
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  rcases hG with h | h
  · exact (nlsm_zero_on_ZT (by omega) hE' (by norm_num) h).2 X (pkS_onZT (pkS_sub h) hL) hX
  · exact (nlsm_zero_on_ZT (by omega) hE' (by norm_num) h).2 X (pkS_onZT (pkS_sub h) hL) hX

/-- ASSEMBLED · **Theorem Π, clause 1 (completeness)** [v3 §14.1]: for even `N ≥ 6`, every non-degenerate coordinate
zero of `𝒜_N` contains a member of `𝒢_N`. -/
theorem pi_clause1 {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {S : Finset (ℕ × ℕ)} (hS : IsNDZero N S) : ContainsGMember N S :=
  pi_clause1_M2 hN hE (fun _ h6 _ he => germ_input h6 he) (fun _ h6 _ he => resChild_input h6 he) hS

/-- ASSEMBLED · **[Cl2](a)** [v3 §14.4 Prop. 14.7 (a), §14.5]: every member of `𝒢_N` is a non-degenerate zero. -/
theorem cl2a {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {Z : Finset (ℕ × ℕ)} (hZ : Z ∈ gFamily N) :
    NonDegPt N Z ∧ AmpZeroOn N Z :=
  cl2a_M2 hN hE (stZero_input hN hE) hZ

/-- ASSEMBLED · **Theorem Π, clause 2 (minimality)** [v3 §14.1]. -/
theorem pi_clause2 {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {Z : Finset (ℕ × ℕ)} (hZ : Z ∈ gFamily N) :
    NonDegPt N Z ∧ IsMinimalZero N Z :=
  pi_clause2_M2 hN hE (fun _ h6 _ he => germ_input h6 he) (fun _ h6 _ he => resChild_input h6 he)
    (stZero_input hN hE) hZ

/-- ASSEMBLED · **"Hence"** [v3 §14.1]: the minimal non-degenerate coordinate zeros of `𝒜_N` are exactly the members of
`𝒢_N`. -/
theorem pi_minimal_iff {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {Z : Finset (ℕ × ℕ)} :
    IsMinimalZero N Z ↔ Z ∈ gFamily N :=
  pi_minimal_iff_M2 hN hE (fun _ h6 _ he => germ_input h6 he) (fun _ h6 _ he => resChild_input h6 he)
    (stZero_input hN hE)

/-! ## 9. Controls (PROVED; R12-P7a, renamed): inhabitation witnesses and negative controls at N = 6 (generated by `gen_controls.py`;
witness points from `mirror.py`, exact ℚ, fixed seeds) -/

theorem oddDiagonals_sub {N : ℕ} {d : ℕ × ℕ} (h : d ∈ oddDiagonals N) : d ∈ diagonals N := (mem_filter.1 h).1

/-! ### `S_{1,3,5}` at N = 6 -/

theorem SG6_ST135 : sepPairs 6 {1, 3, 5} = {(2, 4), (2, 6), (4, 6)} := by decide

/-- PROVED. `S_{1, 3, 5}` is a member of `𝒢_6`. -/
theorem mem_ST135 : sepPairs 6 {1, 3, 5} ∈ gFamily 6 := mem_image.2 ⟨{1, 3, 5}, by decide, rfl⟩

def w_ST135 : ℕ × ℕ → ℚ := fun d =>
  if d = (1, 3) then (-4) else if d = (1, 4) then (-4) else if d = (1, 5) then (-1) else if d = (2, 4) then 6 else
  if d = (2, 5) then 3 else if d = (2, 6) then 1 else if d = (3, 5) then (-3) else if d = (3, 6) then (-3) else
  if d = (4, 6) then (-3) else 0

theorem w_ST135_ne : ∀ d ∈ diagonals 6, w_ST135 d ≠ 0 := by decide

/-- PROVED. Inhabitation: `L_S` has a rational point with every chord non-zero. -/
theorem nd_ST135 : NonDegPt 6 (sepPairs 6 {1, 3, 5}) :=
  ⟨w_ST135, by rw [SG6_ST135]; intro t ht; fin_cases ht <;> simp [mesh, planar, vtx, diagonals, w_ST135] <;> norm_num,
    w_ST135_ne⟩

/-- PROVED. `𝒜_6 ≡ 0` on `L_S` (pointwise, off the poles): pivots solved from the tile equations, then
`field_simp; ring` on (4.3). -/
theorem zero_ST135 : AmpZeroOn 6 (sepPairs 6 {1, 3, 5}) := by
  intro X hL hX
  rw [SG6_ST135] at hL
  have h0 : X (2, 4) - X (2, 5) + X (3, 5) = 0 := by
    have h := hL (2, 4) (by decide)
    simp only [mesh, planar] at h; norm_num [vtx, diagonals] at h; linarith
  have h1 : X (1, 3) + X (2, 6) - X (3, 6) = 0 := by
    have h := hL (2, 6) (by decide)
    simp only [mesh, planar] at h; norm_num [vtx, diagonals] at h; linarith
  have h2 : -X (1, 4) + X (1, 5) + X (4, 6) = 0 := by
    have h := hL (4, 6) (by decide)
    simp only [mesh, planar] at h; norm_num [vtx, diagonals] at h; linarith
  have n14 : X (1, 4) ≠ 0 := hX (1, 4) (by decide)
  have n25 : X (2, 5) ≠ 0 := hX (2, 5) (by decide)
  have n36 : X (3, 6) ≠ 0 := hX (3, 6) (by decide)
  have e0 : X (1, 3) = -X (2, 6) + X (3, 6) := by linarith [h0, h1, h2]
  have e1 : X (1, 5) = X (1, 4) - X (4, 6) := by linarith [h0, h1, h2]
  have e2 : X (2, 4) = X (2, 5) - X (3, 5) := by linarith [h0, h1, h2]
  rw [calA_six, paper43, e0, e1, e2]
  field_simp
  ring

def w_ST135_24 : ℕ × ℕ → ℚ := fun d =>
  if d = (1, 3) then (-6) else if d = (1, 4) then (-5) else if d = (1, 5) then (-1) else if d = (2, 4) then 2 else
  if d = (2, 5) then (-3) else if d = (2, 6) then 2 else if d = (3, 5) then (-3) else if d = (3, 6) then (-4) else
  if d = (4, 6) then (-4) else 0

theorem w_ST135_24_ne : ∀ d ∈ diagonals 6, w_ST135_24 d ≠ 0 := by decide

theorem SG6_ST135_24 : (sepPairs 6 {1, 3, 5}).erase (2, 4) = {(2, 6), (4, 6)} := by decide

/-- PROVED. `𝒜_6 = -2/3` at `w_ST135_24`, a point of the locus with no chord zero. -/
theorem min_ST135_24 : ¬ AmpZeroOn 6 ((sepPairs 6 {1, 3, 5}).erase (2, 4)) := by
  intro h
  have hv := h w_ST135_24 (by rw [SG6_ST135_24]; intro t ht; fin_cases ht <;> simp [mesh, planar, vtx, diagonals, w_ST135_24] <;> norm_num)
    (by intro d hd; exact w_ST135_24_ne d (oddDiagonals_sub hd))
  rw [calA_six] at hv
  norm_num [paper43, w_ST135_24] at hv

def w_ST135_26 : ℕ × ℕ → ℚ := fun d =>
  if d = (1, 3) then 3 else if d = (1, 4) then (-6) else if d = (1, 5) then (-2) else if d = (2, 4) then 1 else
  if d = (2, 5) then (-2) else if d = (2, 6) then (-2) else if d = (3, 5) then (-3) else if d = (3, 6) then (-1) else
  if d = (4, 6) then (-4) else 0

theorem w_ST135_26_ne : ∀ d ∈ diagonals 6, w_ST135_26 d ≠ 0 := by decide

theorem SG6_ST135_26 : (sepPairs 6 {1, 3, 5}).erase (2, 6) = {(2, 4), (4, 6)} := by decide

/-- PROVED. `𝒜_6 = 14` at `w_ST135_26`, a point of the locus with no chord zero. -/
theorem min_ST135_26 : ¬ AmpZeroOn 6 ((sepPairs 6 {1, 3, 5}).erase (2, 6)) := by
  intro h
  have hv := h w_ST135_26 (by rw [SG6_ST135_26]; intro t ht; fin_cases ht <;> simp [mesh, planar, vtx, diagonals, w_ST135_26] <;> norm_num)
    (by intro d hd; exact w_ST135_26_ne d (oddDiagonals_sub hd))
  rw [calA_six] at hv
  norm_num [paper43, w_ST135_26] at hv

def w_ST135_46 : ℕ × ℕ → ℚ := fun d =>
  if d = (1, 3) then 6 else if d = (1, 4) then (-4) else if d = (1, 5) then (-2) else if d = (2, 4) then 8 else
  if d = (2, 5) then 4 else if d = (2, 6) then (-3) else if d = (3, 5) then (-4) else if d = (3, 6) then 3 else
  if d = (4, 6) then (-3) else 0

theorem w_ST135_46_ne : ∀ d ∈ diagonals 6, w_ST135_46 d ≠ 0 := by decide

theorem SG6_ST135_46 : (sepPairs 6 {1, 3, 5}).erase (4, 6) = {(2, 4), (2, 6)} := by decide

/-- PROVED. `𝒜_6 = 7/2` at `w_ST135_46`, a point of the locus with no chord zero. -/
theorem min_ST135_46 : ¬ AmpZeroOn 6 ((sepPairs 6 {1, 3, 5}).erase (4, 6)) := by
  intro h
  have hv := h w_ST135_46 (by rw [SG6_ST135_46]; intro t ht; fin_cases ht <;> simp [mesh, planar, vtx, diagonals, w_ST135_46] <;> norm_num)
    (by intro d hd; exact w_ST135_46_ne d (oddDiagonals_sub hd))
  rw [calA_six] at hv
  norm_num [paper43, w_ST135_46] at hv

/-! ### `S_{1,3}` at N = 6 -/

theorem SG6_ST13 : sepPairs 6 {1, 3} = {(2, 4), (2, 5), (2, 6)} := by decide

/-- PROVED. `S_{1, 3}` is a member of `𝒢_6`. -/
theorem mem_ST13 : sepPairs 6 {1, 3} ∈ gFamily 6 := mem_image.2 ⟨{1, 3}, by decide, rfl⟩

def w_ST13 : ℕ × ℕ → ℚ := fun d =>
  if d = (1, 3) then 3 else if d = (1, 4) then 4 else if d = (1, 5) then (-3) else if d = (2, 4) then (-3) else
  if d = (2, 5) then 1 else if d = (2, 6) then (-4) else if d = (3, 5) then 4 else if d = (3, 6) then (-1) else
  if d = (4, 6) then (-1) else 0

theorem w_ST13_ne : ∀ d ∈ diagonals 6, w_ST13 d ≠ 0 := by decide

/-- PROVED. Inhabitation: `L_S` has a rational point with every chord non-zero. -/
theorem nd_ST13 : NonDegPt 6 (sepPairs 6 {1, 3}) :=
  ⟨w_ST13, by rw [SG6_ST13]; intro t ht; fin_cases ht <;> simp [mesh, planar, vtx, diagonals, w_ST13] <;> norm_num,
    w_ST13_ne⟩

/-- PROVED. `𝒜_6 ≡ 0` on `L_S` (pointwise, off the poles): pivots solved from the tile equations, then
`field_simp; ring` on (4.3). -/
theorem zero_ST13 : AmpZeroOn 6 (sepPairs 6 {1, 3}) := by
  intro X hL hX
  rw [SG6_ST13] at hL
  have h0 : X (2, 4) - X (2, 5) + X (3, 5) = 0 := by
    have h := hL (2, 4) (by decide)
    simp only [mesh, planar] at h; norm_num [vtx, diagonals] at h; linarith
  have h1 : X (2, 5) - X (2, 6) - X (3, 5) + X (3, 6) = 0 := by
    have h := hL (2, 5) (by decide)
    simp only [mesh, planar] at h; norm_num [vtx, diagonals] at h; linarith
  have h2 : X (1, 3) + X (2, 6) - X (3, 6) = 0 := by
    have h := hL (2, 6) (by decide)
    simp only [mesh, planar] at h; norm_num [vtx, diagonals] at h; linarith
  have n14 : X (1, 4) ≠ 0 := hX (1, 4) (by decide)
  have n25 : X (2, 5) ≠ 0 := hX (2, 5) (by decide)
  have n36 : X (3, 6) ≠ 0 := hX (3, 6) (by decide)
  have e0 : X (1, 3) = -X (2, 5) + X (3, 5) := by linarith [h0, h1, h2]
  have e1 : X (2, 4) = X (2, 5) - X (3, 5) := by linarith [h0, h1, h2]
  have e2 : X (2, 6) = X (2, 5) - X (3, 5) + X (3, 6) := by linarith [h0, h1, h2]
  rw [calA_six, paper43, e0, e1, e2]
  field_simp
  ring

def w_ST13_24 : ℕ × ℕ → ℚ := fun d =>
  if d = (1, 3) then (-2) else if d = (1, 4) then (-3) else if d = (1, 5) then (-3) else if d = (2, 4) then 1 else
  if d = (2, 5) then 4 else if d = (2, 6) then 3 else if d = (3, 5) then 2 else if d = (3, 6) then 1 else
  if d = (4, 6) then 3 else 0

theorem w_ST13_24_ne : ∀ d ∈ diagonals 6, w_ST13_24 d ≠ 0 := by decide

theorem SG6_ST13_24 : (sepPairs 6 {1, 3}).erase (2, 4) = {(2, 5), (2, 6)} := by decide

/-- PROVED. `𝒜_6 = 1` at `w_ST13_24`, a point of the locus with no chord zero. -/
theorem min_ST13_24 : ¬ AmpZeroOn 6 ((sepPairs 6 {1, 3}).erase (2, 4)) := by
  intro h
  have hv := h w_ST13_24 (by rw [SG6_ST13_24]; intro t ht; fin_cases ht <;> simp [mesh, planar, vtx, diagonals, w_ST13_24] <;> norm_num)
    (by intro d hd; exact w_ST13_24_ne d (oddDiagonals_sub hd))
  rw [calA_six] at hv
  norm_num [paper43, w_ST13_24] at hv

def w_ST13_25 : ℕ × ℕ → ℚ := fun d =>
  if d = (1, 3) then (-2) else if d = (1, 4) then 1 else if d = (1, 5) then 2 else if d = (2, 4) then 3 else
  if d = (2, 5) then 2 else if d = (2, 6) then 4 else if d = (3, 5) then (-1) else if d = (3, 6) then 2 else
  if d = (4, 6) then 4 else 0

theorem w_ST13_25_ne : ∀ d ∈ diagonals 6, w_ST13_25 d ≠ 0 := by decide

theorem SG6_ST13_25 : (sepPairs 6 {1, 3}).erase (2, 5) = {(2, 4), (2, 6)} := by decide

/-- PROVED. `𝒜_6 = 5` at `w_ST13_25`, a point of the locus with no chord zero. -/
theorem min_ST13_25 : ¬ AmpZeroOn 6 ((sepPairs 6 {1, 3}).erase (2, 5)) := by
  intro h
  have hv := h w_ST13_25 (by rw [SG6_ST13_25]; intro t ht; fin_cases ht <;> simp [mesh, planar, vtx, diagonals, w_ST13_25] <;> norm_num)
    (by intro d hd; exact w_ST13_25_ne d (oddDiagonals_sub hd))
  rw [calA_six] at hv
  norm_num [paper43, w_ST13_25] at hv

def w_ST13_26 : ℕ × ℕ → ℚ := fun d =>
  if d = (1, 3) then (-2) else if d = (1, 4) then (-3) else if d = (1, 5) then 3 else if d = (2, 4) then 3 else
  if d = (2, 5) then 6 else if d = (2, 6) then 1 else if d = (3, 5) then 3 else if d = (3, 6) then (-2) else
  if d = (4, 6) then (-3) else 0

theorem w_ST13_26_ne : ∀ d ∈ diagonals 6, w_ST13_26 d ≠ 0 := by decide

theorem SG6_ST13_26 : (sepPairs 6 {1, 3}).erase (2, 6) = {(2, 4), (2, 5)} := by decide

/-- PROVED. `𝒜_6 = -1` at `w_ST13_26`, a point of the locus with no chord zero. -/
theorem min_ST13_26 : ¬ AmpZeroOn 6 ((sepPairs 6 {1, 3}).erase (2, 6)) := by
  intro h
  have hv := h w_ST13_26 (by rw [SG6_ST13_26]; intro t ht; fin_cases ht <;> simp [mesh, planar, vtx, diagonals, w_ST13_26] <;> norm_num)
    (by intro d hd; exact w_ST13_26_ne d (oddDiagonals_sub hd))
  rw [calA_six] at hv
  norm_num [paper43, w_ST13_26] at hv

/-! ### `S_{1,4}` at N = 6 -/

theorem SG6_D14 : sepPairs 6 {1, 4} = {(2, 5), (2, 6), (3, 5), (3, 6)} := by decide

/-- PROVED. `S_{1, 4}` is a member of `𝒢_6`. -/
theorem mem_D14 : sepPairs 6 {1, 4} ∈ gFamily 6 := mem_image.2 ⟨{1, 4}, by decide, rfl⟩

def w_D14 : ℕ × ℕ → ℚ := fun d =>
  if d = (1, 3) then (-2) else if d = (1, 4) then (-1) else if d = (1, 5) then 2 else if d = (2, 4) then 4 else
  if d = (2, 5) then 1 else if d = (2, 6) then 4 else if d = (3, 5) then (-1) else if d = (3, 6) then 2 else
  if d = (4, 6) then 3 else 0

theorem w_D14_ne : ∀ d ∈ diagonals 6, w_D14 d ≠ 0 := by decide

/-- PROVED. Inhabitation: `L_S` has a rational point with every chord non-zero. -/
theorem nd_D14 : NonDegPt 6 (sepPairs 6 {1, 4}) :=
  ⟨w_D14, by rw [SG6_D14]; intro t ht; fin_cases ht <;> simp [mesh, planar, vtx, diagonals, w_D14] <;> norm_num,
    w_D14_ne⟩

/-- PROVED. `𝒜_6 ≡ 0` on `L_S` (pointwise, off the poles): pivots solved from the tile equations, then
`field_simp; ring` on (4.3). -/
theorem zero_D14 : AmpZeroOn 6 (sepPairs 6 {1, 4}) := by
  intro X hL hX
  rw [SG6_D14] at hL
  have h0 : X (2, 5) - X (2, 6) - X (3, 5) + X (3, 6) = 0 := by
    have h := hL (2, 5) (by decide)
    simp only [mesh, planar] at h; norm_num [vtx, diagonals] at h; linarith
  have h1 : X (1, 3) + X (2, 6) - X (3, 6) = 0 := by
    have h := hL (2, 6) (by decide)
    simp only [mesh, planar] at h; norm_num [vtx, diagonals] at h; linarith
  have h2 : X (3, 5) - X (3, 6) + X (4, 6) = 0 := by
    have h := hL (3, 5) (by decide)
    simp only [mesh, planar] at h; norm_num [vtx, diagonals] at h; linarith
  have h3 : -X (1, 3) + X (1, 4) + X (3, 6) - X (4, 6) = 0 := by
    have h := hL (3, 6) (by decide)
    simp only [mesh, planar] at h; norm_num [vtx, diagonals] at h; linarith
  have n14 : X (1, 4) ≠ 0 := hX (1, 4) (by decide)
  have n25 : X (2, 5) ≠ 0 := hX (2, 5) (by decide)
  have n36 : X (3, 6) ≠ 0 := hX (3, 6) (by decide)
  have e0 : X (1, 3) = -X (2, 5) + X (3, 6) - X (4, 6) := by linarith [h0, h1, h2, h3]
  have e1 : X (2, 6) = X (2, 5) + X (4, 6) := by linarith [h0, h1, h2, h3]
  have e2 : X (3, 5) = X (3, 6) - X (4, 6) := by linarith [h0, h1, h2, h3]
  have e3 : X (1, 4) = -X (2, 5) := by linarith [h0, h1, h2, h3]
  rw [e3] at n14
  rw [calA_six, paper43, e0, e1, e2, e3]
  field_simp
  ring

def w_D14_25 : ℕ × ℕ → ℚ := fun d =>
  if d = (1, 3) then (-5) else if d = (1, 4) then (-2) else if d = (1, 5) then (-2) else if d = (2, 4) then (-2) else
  if d = (2, 5) then 4 else if d = (2, 6) then 1 else if d = (3, 5) then (-3) else if d = (3, 6) then (-4) else
  if d = (4, 6) then (-1) else 0

theorem w_D14_25_ne : ∀ d ∈ diagonals 6, w_D14_25 d ≠ 0 := by decide

theorem SG6_D14_25 : (sepPairs 6 {1, 4}).erase (2, 5) = {(2, 6), (3, 5), (3, 6)} := by decide

/-- PROVED. `𝒜_6 = -5/4` at `w_D14_25`, a point of the locus with no chord zero. -/
theorem min_D14_25 : ¬ AmpZeroOn 6 ((sepPairs 6 {1, 4}).erase (2, 5)) := by
  intro h
  have hv := h w_D14_25 (by rw [SG6_D14_25]; intro t ht; fin_cases ht <;> simp [mesh, planar, vtx, diagonals, w_D14_25] <;> norm_num)
    (by intro d hd; exact w_D14_25_ne d (oddDiagonals_sub hd))
  rw [calA_six] at hv
  norm_num [paper43, w_D14_25] at hv

def w_D14_26 : ℕ × ℕ → ℚ := fun d =>
  if d = (1, 3) then (-2) else if d = (1, 4) then (-3) else if d = (1, 5) then (-2) else if d = (2, 4) then (-4) else
  if d = (2, 5) then (-2) else if d = (2, 6) then (-4) else if d = (3, 5) then 1 else if d = (3, 6) then (-1) else
  if d = (4, 6) then (-2) else 0

theorem w_D14_26_ne : ∀ d ∈ diagonals 6, w_D14_26 d ≠ 0 := by decide

theorem SG6_D14_26 : (sepPairs 6 {1, 4}).erase (2, 6) = {(2, 5), (3, 5), (3, 6)} := by decide

/-- PROVED. `𝒜_6 = -10` at `w_D14_26`, a point of the locus with no chord zero. -/
theorem min_D14_26 : ¬ AmpZeroOn 6 ((sepPairs 6 {1, 4}).erase (2, 6)) := by
  intro h
  have hv := h w_D14_26 (by rw [SG6_D14_26]; intro t ht; fin_cases ht <;> simp [mesh, planar, vtx, diagonals, w_D14_26] <;> norm_num)
    (by intro d hd; exact w_D14_26_ne d (oddDiagonals_sub hd))
  rw [calA_six] at hv
  norm_num [paper43, w_D14_26] at hv

def w_D14_35 : ℕ × ℕ → ℚ := fun d =>
  if d = (1, 3) then (-6) else if d = (1, 4) then (-5) else if d = (1, 5) then (-1) else if d = (2, 4) then (-1) else
  if d = (2, 5) then 8 else if d = (2, 6) then 2 else if d = (3, 5) then 2 else if d = (3, 6) then (-4) else
  if d = (4, 6) then (-3) else 0

theorem w_D14_35_ne : ∀ d ∈ diagonals 6, w_D14_35 d ≠ 0 := by decide

theorem SG6_D14_35 : (sepPairs 6 {1, 4}).erase (3, 5) = {(2, 5), (2, 6), (3, 6)} := by decide

/-- PROVED. `𝒜_6 = 21/40` at `w_D14_35`, a point of the locus with no chord zero. -/
theorem min_D14_35 : ¬ AmpZeroOn 6 ((sepPairs 6 {1, 4}).erase (3, 5)) := by
  intro h
  have hv := h w_D14_35 (by rw [SG6_D14_35]; intro t ht; fin_cases ht <;> simp [mesh, planar, vtx, diagonals, w_D14_35] <;> norm_num)
    (by intro d hd; exact w_D14_35_ne d (oddDiagonals_sub hd))
  rw [calA_six] at hv
  norm_num [paper43, w_D14_35] at hv

def w_D14_36 : ℕ × ℕ → ℚ := fun d =>
  if d = (1, 3) then (-1) else if d = (1, 4) then (-1) else if d = (1, 5) then (-1) else if d = (2, 4) then 3 else
  if d = (2, 5) then (-6) else if d = (2, 6) then (-2) else if d = (3, 5) then (-7) else if d = (3, 6) then (-3) else
  if d = (4, 6) then 4 else 0

theorem w_D14_36_ne : ∀ d ∈ diagonals 6, w_D14_36 d ≠ 0 := by decide

theorem SG6_D14_36 : (sepPairs 6 {1, 4}).erase (3, 6) = {(2, 5), (2, 6), (3, 5)} := by decide

/-- PROVED. `𝒜_6 = -7` at `w_D14_36`, a point of the locus with no chord zero. -/
theorem min_D14_36 : ¬ AmpZeroOn 6 ((sepPairs 6 {1, 4}).erase (3, 6)) := by
  intro h
  have hv := h w_D14_36 (by rw [SG6_D14_36]; intro t ht; fin_cases ht <;> simp [mesh, planar, vtx, diagonals, w_D14_36] <;> norm_num)
    (by intro d hd; exact w_D14_36_ne d (oddDiagonals_sub hd))
  rw [calA_six] at hv
  norm_num [paper43, w_D14_36] at hv

/-! ### Negative controls at N = 6 -/

def w_empty : ℕ × ℕ → ℚ := fun d =>
  if d = (1, 3) then (-2) else if d = (1, 4) then (-4) else if d = (1, 5) then 2 else if d = (2, 4) then (-1) else
  if d = (2, 5) then 4 else if d = (2, 6) then 4 else if d = (3, 5) then (-2) else if d = (3, 6) then (-3) else
  if d = (4, 6) then (-1) else 0

theorem w_empty_ne : ∀ d ∈ diagonals 6, w_empty d ≠ 0 := by decide

/-- PROVED. `𝒜_6 = -7/4` at `w_empty`, a point of the locus with no chord zero. -/
theorem notZero_empty : ¬ AmpZeroOn 6 (∅) := by
  intro h
  have hv := h w_empty (by intro t ht; simp at ht)
    (by intro d hd; exact w_empty_ne d (oddDiagonals_sub hd))
  rw [calA_six] at hv
  norm_num [paper43, w_empty] at hv

/-- PROVED. The pattern-free set `∅` is non-degenerate and not a zero (so clause 1 is not vacuous at `∅`). -/
theorem control_empty : IsNDZero 6 ∅ → False := fun h => notZero_empty h.2.2

theorem nd_empty : NonDegPt 6 ∅ := ⟨w_empty, by intro t ht; simp at ht, w_empty_ne⟩

/-- PROVED. `|T| = 1` is not a pattern: `S_{1} = ∅` (a single leg cuts no pair) and `{1} ∉` the leg sets of `𝒢_6`. -/
theorem control_T1 : sepPairs 6 {1} = ∅ ∧ ({1} : Finset ℕ) ∉ gLegSets 6 := by decide

theorem SG6_mixed124 : sepPairs 6 {1, 2, 4} = {(3, 5), (3, 6)} := by decide

def w_mixed124 : ℕ × ℕ → ℚ := fun d =>
  if d = (1, 3) then 3 else if d = (1, 4) then (-1) else if d = (1, 5) then (-4) else if d = (2, 4) then (-2) else
  if d = (2, 5) then 1 else if d = (2, 6) then 4 else if d = (3, 5) then 4 else if d = (3, 6) then 1 else
  if d = (4, 6) then (-3) else 0

theorem w_mixed124_ne : ∀ d ∈ diagonals 6, w_mixed124 d ≠ 0 := by decide

/-- PROVED. `𝒜_6 = 12` at `w_mixed124`, a point of the locus with no chord zero. -/
theorem notZero_mixed124 : ¬ AmpZeroOn 6 (sepPairs 6 {1, 2, 4}) := by
  intro h
  have hv := h w_mixed124 (by rw [SG6_mixed124]; intro t ht; fin_cases ht <;> simp [mesh, planar, vtx, diagonals, w_mixed124] <;> norm_num)
    (by intro d hd; exact w_mixed124_ne d (oddDiagonals_sub hd))
  rw [calA_six] at hv
  norm_num [paper43, w_mixed124] at hv

/-- PROVED. A mixed triple is neither a pattern nor a diamond, and its `S_T` is not a zero. -/
theorem control_mixed124 : ({1, 2, 4} : Finset ℕ) ∉ gLegSets 6 ∧ ¬ AmpZeroOn 6 (sepPairs 6 {1, 2, 4}) :=
  ⟨by decide, notZero_mixed124⟩

/-- PROVED. **Degenerate sets make `AmpZeroOn` vacuous**: on `L_S` for `S` = all pairs every chord vanishes, so no
point avoids the poles and `AmpZeroOn` holds trivially, while `S` is degenerate. This is why `IsNDZero` carries
`Nondeg` and why clause 2 concludes `NonDegPt`. -/
theorem degenerate_full : ¬ Nondeg 6 (diagonals 6) ∧ AmpZeroOn 6 (diagonals 6) := by
  have key : ∀ X : ℕ × ℕ → ℚ, OnLocus 6 (diagonals 6) X → X (1, 4) = 0 := by
    intro X hL
    have h0 : X (1, 3) - X (1, 4) + X (2, 4) = 0 := by
      have h := hL (1, 3) (by decide)
      simp only [mesh, planar] at h; norm_num [vtx, diagonals] at h; linarith
    have h1 : X (1, 4) - X (1, 5) - X (2, 4) + X (2, 5) = 0 := by
      have h := hL (1, 4) (by decide)
      simp only [mesh, planar] at h; norm_num [vtx, diagonals] at h; linarith
    have h2 : X (1, 5) - X (2, 5) + X (2, 6) = 0 := by
      have h := hL (1, 5) (by decide)
      simp only [mesh, planar] at h; norm_num [vtx, diagonals] at h; linarith
    have h3 : X (2, 4) - X (2, 5) + X (3, 5) = 0 := by
      have h := hL (2, 4) (by decide)
      simp only [mesh, planar] at h; norm_num [vtx, diagonals] at h; linarith
    have h4 : X (2, 5) - X (2, 6) - X (3, 5) + X (3, 6) = 0 := by
      have h := hL (2, 5) (by decide)
      simp only [mesh, planar] at h; norm_num [vtx, diagonals] at h; linarith
    have h5 : X (1, 3) + X (2, 6) - X (3, 6) = 0 := by
      have h := hL (2, 6) (by decide)
      simp only [mesh, planar] at h; norm_num [vtx, diagonals] at h; linarith
    have h6 : X (3, 5) - X (3, 6) + X (4, 6) = 0 := by
      have h := hL (3, 5) (by decide)
      simp only [mesh, planar] at h; norm_num [vtx, diagonals] at h; linarith
    have h7 : -X (1, 3) + X (1, 4) + X (3, 6) - X (4, 6) = 0 := by
      have h := hL (3, 6) (by decide)
      simp only [mesh, planar] at h; norm_num [vtx, diagonals] at h; linarith
    have h8 : -X (1, 4) + X (1, 5) + X (4, 6) = 0 := by
      have h := hL (4, 6) (by decide)
      simp only [mesh, planar] at h; norm_num [vtx, diagonals] at h; linarith
    linarith [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  refine ⟨fun h => ?_, fun X hL hX => absurd (key X hL) (hX (1, 4) (by decide))⟩
  obtain ⟨X, hL, hX⟩ := h (1, 4) (by decide)
  exact hX (key X hL)

/-! ### Inhabitation at N = 8 (non-degeneracy witnesses PROVED; the zero itself is `cl2a`, `sorry`: no Lean
evaluator of `𝒜_8` exists yet, see thread §5) -/

theorem SG8_ST135 : sepPairs 8 {1, 3, 5} = {(2, 4), (2, 6), (2, 7), (2, 8), (4, 6), (4, 7), (4, 8)} := by decide

theorem mem8_ST135 : sepPairs 8 {1, 3, 5} ∈ gFamily 8 := mem_image.2 ⟨{1, 3, 5}, by decide, rfl⟩

def w8_ST135 : ℕ × ℕ → ℚ := fun d =>
  if d = (1, 3) then 5 else if d = (1, 4) then (-7) else if d = (1, 5) then (-3) else if d = (1, 6) then 3 else
  if d = (1, 7) then 4 else if d = (2, 4) then 2 else if d = (2, 5) then (-1) else if d = (2, 6) then (-1) else
  if d = (2, 7) then (-9) else if d = (2, 8) then (-2) else if d = (3, 5) then (-3) else if d = (3, 6) then 4 else
  if d = (3, 7) then (-4) else if d = (3, 8) then 3 else if d = (4, 6) then (-4) else if d = (4, 7) then (-6) else
  if d = (4, 8) then (-1) else if d = (5, 7) then (-2) else if d = (5, 8) then 3 else if d = (6, 8) then 3 else 0

theorem w8_ST135_ne : ∀ d ∈ diagonals 8, w8_ST135 d ≠ 0 := by decide

theorem nd8_ST135 : NonDegPt 8 (sepPairs 8 {1, 3, 5}) :=
  ⟨w8_ST135, by rw [SG8_ST135]; intro t ht; fin_cases ht <;> simp [mesh, planar, vtx, diagonals, w8_ST135] <;> norm_num,
    w8_ST135_ne⟩

theorem SG8_D14 : sepPairs 8 {1, 4} = {(2, 5), (2, 6), (2, 7), (2, 8), (3, 5), (3, 6), (3, 7), (3, 8)} := by decide

theorem mem8_D14 : sepPairs 8 {1, 4} ∈ gFamily 8 := mem_image.2 ⟨{1, 4}, by decide, rfl⟩

def w8_D14 : ℕ × ℕ → ℚ := fun d =>
  if d = (1, 3) then (-3) else if d = (1, 4) then (-1) else if d = (1, 5) then (-4) else if d = (1, 6) then (-3) else
  if d = (1, 7) then (-3) else if d = (2, 4) then 4 else if d = (2, 5) then 1 else if d = (2, 6) then (-1) else
  if d = (2, 7) then 5 else if d = (2, 8) then 4 else if d = (3, 5) then (-2) else if d = (3, 6) then (-4) else
  if d = (3, 7) then 2 else if d = (3, 8) then 1 else if d = (4, 6) then (-2) else if d = (4, 7) then 4 else
  if d = (4, 8) then 3 else if d = (5, 7) then (-2) else if d = (5, 8) then (-3) else if d = (6, 8) then (-1) else 0

theorem w8_D14_ne : ∀ d ∈ diagonals 8, w8_D14 d ≠ 0 := by decide

theorem nd8_D14 : NonDegPt 8 (sepPairs 8 {1, 4}) :=
  ⟨w8_D14, by rw [SG8_D14]; intro t ht; fin_cases ht <;> simp [mesh, planar, vtx, diagonals, w8_D14] <;> norm_num,
    w8_D14_ne⟩

/-- A maximal pattern-free set at N = 8 with `𝒫₁ = {(2, 7)}` (regime B; `n8-data.json`, first such entry). -/
def S8B : Finset (ℕ × ℕ) := {(1, 6), (2, 4), (2, 5), (2, 7), (3, 5), (3, 6), (3, 7), (3, 8), (4, 6), (4, 7), (4, 8), (5, 7), (5, 8), (6, 8)}

def w8B : ℕ × ℕ → ℚ := fun d =>
  if d = (1, 3) then (-5) else if d = (1, 4) then (-8) else if d = (1, 5) then (-1) else if d = (1, 6) then (-3) else
  if d = (1, 7) then (-4) else if d = (2, 4) then 3 else if d = (2, 5) then 6 else if d = (2, 6) then (-1) else
  if d = (2, 7) then (-2) else if d = (2, 8) then (-1) else if d = (3, 5) then 3 else if d = (3, 6) then (-4) else
  if d = (3, 7) then (-2) else if d = (3, 8) then (-1) else if d = (4, 6) then (-7) else if d = (4, 7) then (-5) else
  if d = (4, 8) then (-4) else if d = (5, 7) then 2 else if d = (5, 8) then 3 else if d = (6, 8) then 1 else 0

theorem w8B_ne : ∀ d ∈ diagonals 8, w8B d ≠ 0 := by decide

/-- PROVED. **The hypotheses of `lemma14_6` (and of `chain_interval`) are satisfiable**: `S8B ∈ F^π_8` and `(2, 7) ∈ 𝒫₁(S8B)`. -/
theorem lemma14_6_hyp_inhabited : InFpi 8 S8B ∧ (2, 7) ∈ poleChords 8 S8B := by
  refine ⟨⟨by decide, nonDeg_of_pt ⟨w8B, ?_, w8B_ne⟩, by unfold ContainsGMember; decide⟩, by decide⟩
  intro t ht; simp only [S8B] at ht; fin_cases ht <;> simp [mesh, planar, vtx, diagonals, w8B] <;> norm_num

/-! ### Clause 1 and clause 2 at N = 6, instances (PROVED, independent of the `sorry`s) -/

/-- PROVED. The hypotheses of `pi_clause1` are satisfiable (a non-degenerate zero exists), and its conclusion holds there. -/
theorem clause1_hyp_inhabited : IsNDZero 6 (sepPairs 6 {1, 3, 5}) ∧ ContainsGMember 6 (sepPairs 6 {1, 3, 5}) :=
  ⟨⟨gFamily_sub mem_ST135, nonDeg_of_pt nd_ST135, zero_ST135⟩, ⟨_, mem_ST135, subset_refl _⟩⟩

/-- PROVED. **Clause 2 at N = 6 for three members** (an odd pattern `S_{1,3,5}`, the single-leg locus `S_{1,3}`, the
mixed-anchored diamond `S_{1,4}`): each is a minimal non-degenerate coordinate zero, directly from the definitions. -/
theorem clause2_six_instances :
    IsMinimalZero 6 (sepPairs 6 {1, 3, 5}) ∧ IsMinimalZero 6 (sepPairs 6 {1, 3}) ∧ IsMinimalZero 6 (sepPairs 6 {1, 4}) := by
  refine ⟨⟨⟨gFamily_sub mem_ST135, nonDeg_of_pt nd_ST135, zero_ST135⟩, ?_⟩,
    ⟨⟨gFamily_sub mem_ST13, nonDeg_of_pt nd_ST13, zero_ST13⟩, ?_⟩, ⟨⟨gFamily_sub mem_D14, nonDeg_of_pt nd_D14, zero_D14⟩, ?_⟩⟩
  · intro t ht; rw [SG6_ST135] at ht; fin_cases ht
    · exact min_ST135_24
    · exact min_ST135_26
    · exact min_ST135_46
  · intro t ht; rw [SG6_ST13] at ht; fin_cases ht
    · exact min_ST13_24
    · exact min_ST13_25
    · exact min_ST13_26
  · intro t ht; rw [SG6_D14] at ht; fin_cases ht
    · exact min_D14_25
    · exact min_D14_26
    · exact min_D14_35
    · exact min_D14_36

/-- PROVED. **Negative control: the diamonds are needed.** `S_{1,4}` is a non-degenerate zero at N = 6 that contains no
`S_T` (|T| ≥ 2, one parity); a list `𝒢_N` without the mixed-anchored diamonds would make clause 1 false. -/
theorem control_diamonds_needed :
    IsNDZero 6 (sepPairs 6 {1, 4}) ∧ ∀ G ∈ (Icc 1 6).powerset, IsSameParitySet 6 G → ¬ sepPairs 6 G ⊆ sepPairs 6 {1, 4} :=
  ⟨⟨gFamily_sub mem_D14, nonDeg_of_pt nd_D14, zero_D14⟩, by decide⟩

/-- PROVED. **Negative control: minimality is not automatic.** `S_{1,3,5} ∪ {(1,4)}` is a non-degenerate zero at N = 6
(it contains `S_{1,3,5}`) that is not minimal: removing `(1,4)` leaves a zero. -/
theorem control_not_minimal : ¬ IsMinimalZero 6 (insert (1, 4) (sepPairs 6 {1, 3, 5})) := by
  rintro ⟨-, hmin⟩
  apply hmin (1, 4) (mem_insert_self _ _)
  rw [erase_insert (by decide)]
  exact zero_ST135

/-! ### (Tri) at N = 10: the setting is inhabited, a witness of `F_U` is checked, a non-witness is rejected -/

/-- PROVED. The configuration of v3 §14.3 Remark (ii) (N = 10, Θ = {4}, τ = {5, 7}, σ = {1, 3}) with `ω = 7`,
`X = [1, 3]`, `Y = [5, 7]` satisfies every clause of `ThreeSepSetting` (non-vacuity of `threeSep_consecWit`). -/
theorem threeSep_setting_ten : ThreeSepSetting 10 7 1 3 5 7 {4} {5, 7} {1, 3} := by decide

/-- PROVED. `G = {1, 3}` (two consecutive odd trace legs, `F_U`) is a witness there: `S_G ⊆ C₀`. -/
theorem threeSep_witness_ten : ConsecWit 10 {4} {5, 7} {1, 3} {1, 3} ∧ sepPairs 10 {1, 3} ⊆ threeSepCut 10 7 1 3 5 7 {4} {5, 7} {1, 3} := by
  decide

/-- PROVED. Negative control: `S_{2,4,6}` is not inside `C₀` there (the inclusion is not trivially true). -/
theorem threeSep_nonwitness_ten : ¬ sepPairs 10 {2, 4, 6} ⊆ threeSepCut 10 7 1 3 5 7 {4} {5, 7} {1, 3} := by decide

/-- PROVED. Negative control on the setting: the same data with `τ = {1}` (not admissible: leg 1 lies in `X`) is
rejected. -/
theorem threeSep_setting_reject : ¬ ThreeSepSetting 10 7 1 3 5 7 {4} {1} {1, 3} := by decide

/-! ### Stage-0 controls (R12-P7b0; PROVED): P7a R1 S1, the reviewer's probes, the new predicates and route objects

Data from `../mirror_b.py` (thread §6 E2) and the P7a mirror; every `decide` is kernel evaluation (no `native_decide`). -/

/-- PROVED. The witness form is not vacuous: `NLSM_6 ≢ 0` on `L_∅` (from P7a's `notZero_empty`). -/
theorem nonzero_empty6 : NonzeroOn 6 ∅ := nonzeroOn_iff_not_ampZeroOn.2 notZero_empty

/-- PROVED. **P7a R1 S1, genuine mixed triple**: `T = {1, 3, 6}` at N = 8 (arcs `{2}`, `{4, 5}`, `{7, 8}`, all
non-empty) is not a leg set of `𝒢_8`, and `S_T` contains no member of `𝒢_8` (reviewer probe `rev_mixed136`). -/
theorem control_mixed136 : ({1, 3, 6} : Finset ℕ) ∉ gLegSets 8 ∧ ¬ ContainsGMember 8 (sepPairs 8 {1, 3, 6}) := by
  refine ⟨by decide, ?_⟩; unfold ContainsGMember; decide

theorem sepPairs8_136 : sepPairs 8 {1, 3, 6} = {(2, 4), (2, 5), (2, 7), (2, 8), (4, 7), (4, 8), (5, 7), (5, 8)} := by
  decide

def w8_136 : ℕ × ℕ → ℚ := fun d =>
  if d = (1, 3) then 5 else if d = (1, 4) then 9 else if d = (1, 5) then 4 else if d = (1, 6) then 1 else
  if d = (1, 7) then (-2) else if d = (2, 4) then (-2) else if d = (2, 5) then (-5) else if d = (2, 6) then 2 else
  if d = (2, 7) then (-8) else if d = (2, 8) then (-4) else if d = (3, 5) then (-3) else if d = (3, 6) then 4 else
  if d = (3, 7) then (-3) else if d = (3, 8) then 1 else if d = (4, 6) then (-4) else if d = (4, 7) then 8 else
  if d = (4, 8) then 4 else if d = (5, 7) then 3 else if d = (5, 8) then (-1) else if d = (6, 8) then (-4) else 0

theorem w8_136_ne : ∀ d ∈ diagonals 8, w8_136 d ≠ 0 := by decide

/-- PROVED. **S1, continued**: `S_{1,3,6} ∈ F^π_8` (non-degenerate, witness point with every chord non-zero; contains no
member of `𝒢_8`). So clause 1 claims `𝒜_8 ≢ 0` on its locus; the Python value at this point is `𝒜_8 = 1725/32 ≠ 0`
(thread §6 E2; a Lean evaluator of `𝒜_8` is a stage-0 TODO, thread §5). -/
theorem fpi8_mixed136 : InFpi 8 (sepPairs 8 {1, 3, 6}) := by
  refine ⟨by decide, nonDeg_of_pt ⟨w8_136, ?_, w8_136_ne⟩, control_mixed136.2⟩
  rw [sepPairs8_136]; intro t ht; fin_cases ht <;> simp [mesh, planar, vtx, diagonals, w8_136] <;> norm_num

/-- PROVED. Reviewer probes (P7a R1, `r12p7arev/RevCheck.lean`), renamed: `|𝒢_6| = 11`, `|𝒢_8| = 30`, no empty member,
the wrap-around pair `{1, 8}` is not an anchor. -/
theorem rev_card6 : (gFamily 6).card = 11 := by decide
theorem rev_card8 : (gFamily 8).card = 30 := by decide
theorem rev_nonempty8 : ∀ Z ∈ gFamily 8, Z.Nonempty := by decide
theorem rev_wrap18 : sepPairs 8 {1, 8} = ∅ ∧ ¬ IsMixedAnchor 8 {1, 8} ∧ ({1, 8} : Finset ℕ) ∉ gLegSets 8 := by decide

/-- PROVED. Heads and tails (reviewer probe `rev_head`), and the cyclic-arc form of the sides. -/
theorem rev_head : oddSide 8 (2, 7) = {1, 7, 8} ∧ evenSide 8 (2, 7) = {2, 3, 4, 5, 6} ∧ oddSide 8 (1, 4) = {1, 2, 3} := by
  decide
theorem sides8_27 : oddSide 8 (2, 7) = cycArc 8 (headStart (2, 7)) (headLen 8 (2, 7)) ∧
    evenSide 8 (2, 7) = cycArc 8 (tailStart (2, 7)) (tailLen 8 (2, 7)) := by decide

/-- PROVED. The (Tri) example of v3 §14.3 at N = 12 (reviewer probes `rev_tri12`, `_w`, `_nw`). -/
theorem rev_tri12 : ThreeSepSetting 12 9 3 5 7 9 {2, 6} {7} {12} := by decide
theorem rev_tri12_w : ConsecWit 12 {2, 6} {7} {12} {2, 12} ∧
    sepPairs 12 {2, 12} ⊆ threeSepCut 12 9 3 5 7 9 {2, 6} {7} {12} := by decide
theorem rev_tri12_nw : ¬ sepPairs 12 {2, 6} ⊆ threeSepCut 12 9 3 5 7 9 {2, 6} {7} {12} := by decide

/-- PROVED. **Route objects at N = 8 on `S8B`** (the `lemma14_6` inhabitant, regime B): `(2, 7)` is the only `𝒫₁` chord;
it is in `𝒮_B`, canonical, satisfies (Even-top′), is its own class, and both its sides satisfy `Sep_all`; its A-child
(size 4) has coordinate set `∅` and its B-child (size 6) the set below, which contains no member of `𝒢_6` (the true side
of `childF`). -/
theorem ctl8_route : poleChords 8 S8B = {(2, 7)} ∧ goodTail 8 S8B = {(2, 7)} ∧ IsMinimalChord 8 S8B (2, 7) ∧
    EvenTopP 8 S8B (2, 7) ∧ hitClass 8 S8B (2, 7) = {(2, 7)} ∧
    NoFreeSep 8 S8B (headStart (2, 7)) (headLen 8 (2, 7)) 0 ∧ NoFreeSep 8 S8B (tailStart (2, 7)) (tailLen 8 (2, 7)) 1 := by
  decide
theorem ctl8_children : childSetA 8 S8B (2, 7) = ∅ ∧
    childSetB 8 S8B (2, 7) = {(2, 4), (2, 5), (3, 5), (3, 6), (4, 6)} ∧
    headLen 8 (2, 7) + 1 = 4 ∧ tailLen 8 (2, 7) + 1 = 6 ∧ ¬ ContainsGMember 6 (childSetB 8 S8B (2, 7)) := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩; unfold ContainsGMember; decide

/-- A set in `F^π_8` (transversal form checked by the mirror) whose `𝒫₁` chord `(2, 5)` fails `Sep_all` of its head. -/
def S8N : Finset (ℕ × ℕ) := {(1, 5), (1, 6), (1, 7), (2, 5), (2, 6), (2, 8), (3, 6), (3, 8)}

/-- PROVED. **Negative control for `NoFreeSep` / `childSetA`** (the false side of `childF`): `(2, 5) ∈ 𝒫₁(S8N)`, its head
has a failing separator, and its A-child set `{(1,5), (2,5), (3,5)}` is `S_{4,6} ∈ 𝒢_6`. -/
theorem ctl8_neg : ¬ ContainsGMember 8 S8N ∧ (2, 5) ∈ poleChords 8 S8N ∧
    ¬ NoFreeSep 8 S8N (headStart (2, 5)) (headLen 8 (2, 5)) 0 ∧
    childSetA 8 S8N (2, 5) = {(1, 5), (2, 5), (3, 5)} ∧ ContainsGMember 6 (childSetA 8 S8N (2, 5)) := by
  refine ⟨?_, by decide, by decide, by decide, ?_⟩
  · unfold ContainsGMember; decide
  · unfold ContainsGMember; decide

/-- A set at N = 10 (mirror, F^π transversal form) with a `𝒫₁` chord `(1, 8)` whose head has a spread failing even
trace `{4}`. -/
def S10E : Finset (ℕ × ℕ) := {(1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 4), (2, 5), (2, 6), (2, 7), (2, 9),
  (2, 10), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (4, 7), (4, 8), (4, 9), (4, 10), (5, 8), (5, 10), (6, 8),
  (6, 9), (6, 10), (7, 9), (7, 10)}

/-- PROVED. **Negative control for `EvenTopP`**: (Even-top′) is not automatic; it fails at a (non-canonical) `𝒫₁` chord. -/
theorem ctl10_evenTop_fails : (1, 8) ∈ poleChords 10 S10E ∧ ¬ EvenTopP 10 S10E (1, 8) ∧
    ¬ IsMinimalChord 10 S10E (1, 8) := by
  decide

end PiZ

/-! ## 10. Axiom report (PROVED items: [propext, Classical.choice, Quot.sound]; ASSEMBLED: + sorryAx) -/

#print axioms PiZ.calA_four
#print axioms PiZ.calA_six
#print axioms PiZ.nonDeg_mono
#print axioms PiZ.ampZeroOn_mono
#print axioms PiZ.gFamily_sub
#print axioms PiZ.zero_ST135
#print axioms PiZ.zero_ST13
#print axioms PiZ.zero_D14
#print axioms PiZ.clause1_hyp_inhabited
#print axioms PiZ.clause2_six_instances
#print axioms PiZ.control_empty
#print axioms PiZ.nd_empty
#print axioms PiZ.control_T1
#print axioms PiZ.control_mixed124
#print axioms PiZ.degenerate_full
#print axioms PiZ.control_diamonds_needed
#print axioms PiZ.control_not_minimal
#print axioms PiZ.nd8_ST135
#print axioms PiZ.nd8_D14
#print axioms PiZ.mem8_ST135
#print axioms PiZ.mem8_D14
#print axioms PiZ.threeSep_setting_ten
#print axioms PiZ.threeSep_witness_ten
#print axioms PiZ.threeSep_nonwitness_ten
#print axioms PiZ.threeSep_setting_reject
#print axioms PiZ.lemma14_6_hyp_inhabited
#print axioms PiZ.calA_eq_zero_iff
#print axioms PiZ.ampZeroOn_iff_nlsmZeroOn
#print axioms PiZ.nonzeroOn_iff_not_nlsmZeroOn
#print axioms PiZ.nonzeroOn_iff_not_ampZeroOn
#print axioms PiZ.nonzero_empty6
#print axioms PiZ.control_mixed136
#print axioms PiZ.fpi8_mixed136
#print axioms PiZ.rev_card6
#print axioms PiZ.rev_card8
#print axioms PiZ.rev_nonempty8
#print axioms PiZ.rev_wrap18
#print axioms PiZ.rev_head
#print axioms PiZ.sides8_27
#print axioms PiZ.rev_tri12
#print axioms PiZ.rev_tri12_w
#print axioms PiZ.rev_tri12_nw
#print axioms PiZ.ctl8_route
#print axioms PiZ.ctl8_children
#print axioms PiZ.ctl8_neg
#print axioms PiZ.ctl10_evenTop_fails
#print axioms PiZ.threeSep
#print axioms PiZ.chain_interval
#print axioms PiZ.cl2a_M2
#print axioms PiZ.prop14_7
#print axioms PiZ.minimal_iff_of
#print axioms PiZ.pi_clause2_M2
#print axioms PiZ.pi_minimal_iff_M2
#print axioms PiZ.pi_clause1
#print axioms PiZ.cl2a
#print axioms PiZ.pi_clause2
#print axioms PiZ.pi_minimal_iff
