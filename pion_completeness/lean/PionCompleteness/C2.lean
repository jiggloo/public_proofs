import PionCompleteness.C1

namespace PiZ

open Finset R12P1 R12P4A R12P3 R12P3C

/-! [Child](3) helpers: `InST` read through positions, the child's legs as positions, the two directions. -/

theorem pkCh_transversal_iff {m : ℕ} {M : Finset (ℕ × ℕ)} :
    Transversal m M ↔ ∀ Z ∈ gFamily m, (Z ∩ M).Nonempty := Iff.rfl

theorem pkCh_mem_gLeg {m : ℕ} {T : Finset ℕ} : T ∈ gLegSets m ↔ T ⊆ Icc 1 m ∧ IsGSet m T := by
  show T ∈ (Icc 1 m).powerset.filter (IsGSet m) ↔ _
  rw [mem_filter, mem_powerset]

theorem pkCh_isG_iff {m : ℕ} {T : Finset ℕ} :
    IsGSet m T ↔ (Admissible m 0 T ∨ Admissible m 1 T) ∨ IsMixedAnchor m T := Iff.rfl

theorem pkCh_adm_iff {m r : ℕ} {T : Finset ℕ} :
    Admissible m r T ↔ T ⊆ Icc 1 m ∧ 2 ≤ T.card ∧ ∀ t ∈ T, t % 2 = r := Iff.rfl

theorem pkCh_mixed_iff {m : ℕ} {T : Finset ℕ} :
    IsMixedAnchor m T ↔ ∃ a ∈ Icc 1 m, ∃ b ∈ Icc 1 m, T = {a, b} ∧ a + 2 ≤ b ∧ ¬ (a = 1 ∧ b = m) ∧ a % 2 ≠ b % 2 :=
  Iff.rfl

theorem pkCh_fpi_iff {N : ℕ} {S : Finset (ℕ × ℕ)} :
    InFpi N S ↔ S ⊆ diagonals N ∧ Nondeg N S ∧ ¬ ContainsGMember N S := Iff.rfl

/-- A one-parity leg set with at least two legs is a same-parity set. -/
theorem pkCh_sameParity {m r : ℕ} {T : Finset ℕ} (hT : T ⊆ Icc 1 m) (hc : 2 ≤ T.card) (hp : ∀ t ∈ T, t % 2 = r) :
    IsGSet m T := by
  obtain ⟨t, ht⟩ := card_pos.1 (show 0 < T.card by omega)
  have h0 := hp t ht
  rw [pkCh_isG_iff]
  left
  rcases Nat.mod_two_eq_zero_or_one t with h | h
  · left
    exact pkCh_adm_iff.2 ⟨hT, hc, fun x hx => by rw [hp x hx]; omega⟩
  · right
    exact pkCh_adm_iff.2 ⟨hT, hc, fun x hx => by rw [hp x hx]; omega⟩

/-- A sorted non-adjacent mixed pair is a mixed anchor. -/
theorem pkCh_mixed_of {m a b : ℕ} (hd : (min a b, max a b) ∈ diagonals m) (hp : a % 2 ≠ b % 2) :
    IsGSet m {a, b} := by
  rw [pkCh_isG_iff]
  right
  have h := mem_diagonals.1 hd
  dsimp only at h
  rw [pkCh_mixed_iff]
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab, max_eq_right hab] at h
    exact ⟨a, mem_Icc.2 ⟨by omega, by omega⟩, b, mem_Icc.2 ⟨by omega, by omega⟩, rfl, h.2.2.1, h.2.2.2, hp⟩
  · rw [min_eq_right hab, max_eq_left hab] at h
    exact ⟨b, mem_Icc.2 ⟨by omega, by omega⟩, a, mem_Icc.2 ⟨by omega, by omega⟩, pair_comm a b, h.2.2.1, h.2.2.2,
      fun e => hp e.symm⟩

/-- Linear "between" against positional "between" (swapped when the start `s` lies in `(min, max]`). -/
theorem pkCh_btw {N s a b t : ℕ} (hs : s ∈ Icc 1 N) (ha : a ∈ Icc 1 N) (hb : b ∈ Icc 1 N) (ht : t ∈ Icc 1 N)
    (hta : t ≠ a) (htb : t ≠ b) :
    ((min a b < s ∧ s ≤ max a b) → ((min a b < t ∧ t < max a b) ↔
      ¬ (min (cycPos N s a) (cycPos N s b) < cycPos N s t ∧ cycPos N s t < max (cycPos N s a) (cycPos N s b)))) ∧
    (¬ (min a b < s ∧ s ≤ max a b) → ((min a b < t ∧ t < max a b) ↔
      (min (cycPos N s a) (cycPos N s b) < cycPos N s t ∧ cycPos N s t < max (cycPos N s a) (cycPos N s b)))) := by
  rw [mem_Icc] at hs ha hb ht
  rw [pkCo_cycPos_eq hs.1 hs.2 ha.1 ha.2, pkCo_cycPos_eq hs.1 hs.2 hb.1 hb.2, pkCo_cycPos_eq hs.1 hs.2 ht.1 ht.2]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> (split_ifs <;> omega)

/-- **`InST` through positions** from any start `s`: different arcs of `C_N ∖ T` = one leg of `T` strictly between the
positions and one not. -/
theorem pkCh_inST_pos {N s a b : ℕ} {T : Finset ℕ} (hs : s ∈ Icc 1 N) (hT : T ⊆ Icc 1 N) (ha : a ∈ Icc 1 N)
    (hb : b ∈ Icc 1 N) :
    InST T a b ↔ a ∉ T ∧ b ∉ T ∧
      (∃ t ∈ T, min (cycPos N s a) (cycPos N s b) < cycPos N s t ∧ cycPos N s t < max (cycPos N s a) (cycPos N s b)) ∧
      (∃ t ∈ T, ¬ (min (cycPos N s a) (cycPos N s b) < cycPos N s t ∧
        cycPos N s t < max (cycPos N s a) (cycPos N s b))) := by
  rw [pkCo_inST_iff]
  have hout : ∀ t ∈ T, a ∉ T → b ∉ T → ((t < min a b ∨ max a b < t) ↔ ¬ (min a b < t ∧ t < max a b)) := by
    intro t ht ha' hb'
    have h1 : t ≠ a := fun h => ha' (h ▸ ht)
    have h2 : t ≠ b := fun h => hb' (h ▸ ht)
    omega
  constructor
  · rintro ⟨ha', hb', ⟨t, ht, h1⟩, ⟨t', ht', h2⟩⟩
    have e1 := pkCh_btw hs ha hb (hT ht) (fun h => ha' (h ▸ ht)) (fun h => hb' (h ▸ ht))
    have e2 := pkCh_btw hs ha hb (hT ht') (fun h => ha' (h ▸ ht')) (fun h => hb' (h ▸ ht'))
    have h2' := (hout t' ht' ha' hb').1 h2
    by_cases hc : min a b < s ∧ s ≤ max a b
    · exact ⟨ha', hb', ⟨t', ht', not_not.1 (mt (e2.1 hc).2 h2')⟩, ⟨t, ht, (e1.1 hc).1 h1⟩⟩
    · exact ⟨ha', hb', ⟨t, ht, (e1.2 hc).1 h1⟩, ⟨t', ht', mt (e2.2 hc).2 h2'⟩⟩
  · rintro ⟨ha', hb', ⟨t, ht, h1⟩, ⟨t', ht', h2⟩⟩
    have e1 := pkCh_btw hs ha hb (hT ht) (fun h => ha' (h ▸ ht)) (fun h => hb' (h ▸ ht))
    have e2 := pkCh_btw hs ha hb (hT ht') (fun h => ha' (h ▸ ht')) (fun h => hb' (h ▸ ht'))
    by_cases hc : min a b < s ∧ s ≤ max a b
    · exact ⟨ha', hb', ⟨t', ht', (e2.1 hc).2 h2⟩, ⟨t, ht, (hout t ht ha' hb').2 (fun h => (e1.1 hc).1 h h1)⟩⟩
    · exact ⟨ha', hb', ⟨t, ht, (e1.2 hc).2 h1⟩, ⟨t', ht', (hout t' ht' ha' hb').2 (fun h => h2 ((e2.2 hc).1 h))⟩⟩

theorem pkCh_inST_minmax {T : Finset ℕ} {a b : ℕ} : InST T (min a b) (max a b) ↔ InST T a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h]
    exact pkCo_inST_comm

theorem pkCh_minmax_map (f : ℕ → ℕ) (a b : ℕ) :
    (min (f (min a b)) (f (max a b)), max (f (min a b)) (f (max a b))) = (min (f a) (f b), max (f a) (f b)) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, min_comm (f b), max_comm (f b)]

/-- The side data and the child labelling of [Child] (BP App. C §C-2): the side `L = (s, k)`, the child `(k+1)`-gon
read from the child leg `c` (child position `i` ↔ parent position `i` from `s`, `i < k`), the new leg `hat` at child
position `k`, and `f` = child leg ↦ parent leg. -/
def pkCh_CH (N s k c hat : ℕ) (f : ℕ → ℕ) : Prop :=
  s ∈ Icc 1 N ∧ 3 ≤ k ∧ k + 3 ≤ N ∧ k % 2 = 1 ∧ N % 2 = 0 ∧ c ∈ Icc 1 (k + 1) ∧ c % 2 = s % 2 ∧
    hat ∈ Icc 1 (k + 1) ∧ cycPos (k + 1) c hat = k ∧ ∀ y ∈ Icc 1 (k + 1), y ≠ hat → f y = vtx N (s + cycPos (k + 1) c y)

theorem pkCh_CH_iff {N s k c hat : ℕ} {f : ℕ → ℕ} :
    pkCh_CH N s k c hat f ↔ s ∈ Icc 1 N ∧ 3 ≤ k ∧ k + 3 ≤ N ∧ k % 2 = 1 ∧ N % 2 = 0 ∧ c ∈ Icc 1 (k + 1) ∧
      c % 2 = s % 2 ∧ hat ∈ Icc 1 (k + 1) ∧ cycPos (k + 1) c hat = k ∧
      ∀ y ∈ Icc 1 (k + 1), y ≠ hat → f y = vtx N (s + cycPos (k + 1) c y) := Iff.rfl

/-- A child leg other than `hat`: its position, its parent leg, parities. -/
theorem pkCh_ch_y {N s k c hat : ℕ} {f : ℕ → ℕ} (H : pkCh_CH N s k c hat f) {y : ℕ} (hy : y ∈ Icc 1 (k + 1))
    (hyh : y ≠ hat) : cycPos (k + 1) c y < k ∧ f y ∈ Icc 1 N ∧ cycPos N s (f y) = cycPos (k + 1) c y ∧
      f y % 2 = y % 2 := by
  obtain ⟨hs, hk3, hkN, hk1, hE, hc, hcs, hhat, hhp, hf⟩ := pkCh_CH_iff.1 H
  have hlt := pkCo_cycPos_lt (show 1 ≤ k + 1 by omega) c y
  have hne : cycPos (k + 1) c y ≠ k := fun h => hyh (pkCo_cycPos_inj hc hy hhat (by rw [h, hhp]))
  have hN1 : 1 ≤ N := by omega
  rw [hf y hy hyh]
  have hmy := pkCo_cycPos_mod_two (show (k + 1) % 2 = 0 by omega) hc hy
  have hv := pkCo_vtx_mod_two hN1 hE (s + cycPos (k + 1) c y)
  refine ⟨by omega, mem_Icc.2 (vtx_bounds N _ hN1), pkCo_cycPos_vtx hs (by omega), by omega⟩

/-- A leg of the side `L` is `f` of a child leg with the same position. -/
theorem pkCh_ch_x {N s k c hat : ℕ} {f : ℕ → ℕ} (H : pkCh_CH N s k c hat f) {x : ℕ} (hx : x ∈ Icc 1 N)
    (hxk : cycPos N s x < k) : ∃ y ∈ Icc 1 (k + 1), y ≠ hat ∧ cycPos (k + 1) c y = cycPos N s x ∧ f y = x := by
  obtain ⟨hs, hk3, hkN, hk1, hE, hc, hcs, hhat, hhp, hf⟩ := pkCh_CH_iff.1 H
  have hy := mem_Icc.2 (vtx_bounds (k + 1) (c + cycPos N s x) (by omega))
  have hp : cycPos (k + 1) c (vtx (k + 1) (c + cycPos N s x)) = cycPos N s x := pkCo_cycPos_vtx hc (by omega)
  have hyh : vtx (k + 1) (c + cycPos N s x) ≠ hat := fun h => by
    rw [h, hhp] at hp
    omega
  refine ⟨_, hy, hyh, hp, ?_⟩
  rw [hf _ hy hyh, hp]
  exact pkCo_vtx_cycPos hs hx

theorem pkCh_ch_hat {N s k c hat : ℕ} {f : ℕ → ℕ} (H : pkCh_CH N s k c hat f) : hat % 2 = (s + 1) % 2 := by
  obtain ⟨hs, hk3, hkN, hk1, hE, hc, hcs, hhat, hhp, hf⟩ := pkCh_CH_iff.1 H
  have := pkCo_cycPos_mod_two (show (k + 1) % 2 = 0 by omega) hc hhat
  omega

theorem pkCh_cpi_nn {N s k hat : ℕ} {S : Finset (ℕ × ℕ)} {f : ℕ → ℕ} {j l : ℕ} (hj : j ≠ hat) (hl : l ≠ hat) :
    ChildPairIn N S s k hat f j l ↔ (min (f j) (f l), max (f j) (f l)) ∈ S := by
  unfold ChildPairIn
  rw [if_neg hj, if_neg hl]

theorem pkCh_cpi_l {N s k hat : ℕ} {S : Finset (ℕ × ℕ)} {f : ℕ → ℕ} {j l : ℕ} (hj : j = hat) :
    ChildPairIn N S s k hat f j l ↔ ∀ w ∈ Icc 1 N, w ∉ cycArc N s k → (min (f l) w, max (f l) w) ∈ S := by
  unfold ChildPairIn
  rw [if_pos hj]

theorem pkCh_cpi_r {N s k hat : ℕ} {S : Finset (ℕ × ℕ)} {f : ℕ → ℕ} {j l : ℕ} (hj : j ≠ hat) (hl : l = hat) :
    ChildPairIn N S s k hat f j l ↔ ∀ w ∈ Icc 1 N, w ∉ cycArc N s k → (min (f j) w, max (f j) w) ∈ S := by
  unfold ChildPairIn
  rw [if_neg hj, if_pos hl]

theorem pkCh_mem_childMiss {N s k hat m : ℕ} {S : Finset (ℕ × ℕ)} {f : ℕ → ℕ} {σ : ℕ × ℕ} :
    σ ∈ missing m ((diagonals m).filter (fun σ => ChildPairIn N S s k hat f σ.1 σ.2)) ↔
      σ ∈ diagonals m ∧ ¬ ChildPairIn N S s k hat f σ.1 σ.2 := by
  rw [pkCh_mem_missing, mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h => h2 ⟨h1, h⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h => h2 h.2⟩


theorem pkCh_cgm_iff {N : ℕ} {S : Finset (ℕ × ℕ)} : ContainsGMember N S ↔ ∃ Z ∈ gFamily N, Z ⊆ S := Iff.rfl

/-- [Child](3) "⇒" (BP App. C §C-2 (3)(b)): a failing trace `Θ` of `L` gives the child leg set `Θ ∪ {P̂}` of `𝒢_m`
whose `S_T` misses the child's missing set. No hypothesis on `S`. -/
theorem pkCh_child_nf {N s k c hat : ℕ} {f : ℕ → ℕ} {S : Finset (ℕ × ℕ)} (H : pkCh_CH N s k c hat f)
    (hT : Transversal (k + 1) (missing (k + 1) ((diagonals (k + 1)).filter
      (fun σ => ChildPairIn N S s k hat f σ.1 σ.2)))) :
    NoFreeSep N S s k ((s + 1) % 2) := by
  obtain ⟨hs, hk3, hkN, hk1, hE, hc, hcs, hhat, hhp, hf⟩ := pkCh_CH_iff.1 H
  have hhq := pkCh_ch_hat H
  have hm2 : (k + 1) % 2 = 0 := by omega
  rw [pkCh_noFree_iff]
  intro Θ hΘ hdis
  obtain ⟨hΘsub, hΘc⟩ := pkCo_mem_admSeps.1 hΘ
  have hθ : ∀ θ ∈ Θ, θ ∈ Icc 1 N ∧ 1 ≤ cycPos N s θ ∧ cycPos N s θ + 2 ≤ k :=
    fun θ h => (pkCo_mem_intArc hs (by omega)).1 (hΘsub h)
  have hg : ∀ θ ∈ Θ, vtx (k + 1) (c + cycPos N s θ) ∈ Icc 1 (k + 1) ∧
      cycPos (k + 1) c (vtx (k + 1) (c + cycPos N s θ)) = cycPos N s θ ∧
      vtx (k + 1) (c + cycPos N s θ) % 2 = θ % 2 := by
    intro θ h
    obtain ⟨h1, h2, h3⟩ := hθ θ h
    have := pkCo_vtx_mod_two (show 1 ≤ k + 1 by omega) hm2 (c + cycPos N s θ)
    have := pkCo_cycPos_mod_two hE hs h1
    exact ⟨mem_Icc.2 (vtx_bounds _ _ (by omega)), pkCo_cycPos_vtx hc (by omega), by omega⟩
  obtain ⟨T, hTdef⟩ : ∃ T : Finset ℕ, T = Θ.image (fun θ => vtx (k + 1) (c + cycPos N s θ)) ∪ {hat} := ⟨_, rfl⟩
  have hTmem : ∀ t, t ∈ T ↔ (∃ θ ∈ Θ, vtx (k + 1) (c + cycPos N s θ) = t) ∨ t = hat := by
    intro t
    rw [hTdef, mem_union, mem_image, mem_singleton]
  have hTsub : T ⊆ Icc 1 (k + 1) := by
    intro t ht
    rcases (hTmem t).1 ht with ⟨θ, h, rfl⟩ | h
    · exact (hg θ h).1
    · rw [h]
      exact hhat
  have hΘne : Θ.Nonempty := card_pos.1 (by omega)
  have hTG : IsGSet (k + 1) T := by
    by_cases hq : ∀ θ ∈ Θ, θ % 2 = (s + 1) % 2
    · obtain ⟨θ₀, h0⟩ := hΘne
      have hne : vtx (k + 1) (c + cycPos N s θ₀) ≠ hat := fun h => by
        have e := (hg θ₀ h0).2.1
        rw [h, hhp] at e
        have := (hθ θ₀ h0).2.2
        omega
      have h2 := one_lt_card.2 ⟨_, (hTmem _).2 (Or.inl ⟨θ₀, h0, rfl⟩), hat, (hTmem hat).2 (Or.inr rfl), hne⟩
      refine pkCh_sameParity hTsub (by omega) (r := (s + 1) % 2) ?_
      intro t ht
      rcases (hTmem t).1 ht with ⟨θ, h, rfl⟩ | h
      · rw [(hg θ h).2.2]
        exact hq θ h
      · rw [h]
        exact hhq
    · have hc1 : Θ.card = 1 := by
        rcases hΘc with h | ⟨-, h⟩
        · exact h
        · exact absurd h hq
      obtain ⟨x, rfl⟩ := card_eq_one.1 hc1
      have hxq : x % 2 ≠ (s + 1) % 2 := fun h => hq fun θ hθ => by
        rw [mem_singleton.1 hθ]
        exact h
      have hTx : T = {vtx (k + 1) (c + cycPos N s x), hat} := by
        rw [hTdef, image_singleton, ← insert_eq]
      obtain ⟨hgx, hpx, hrx⟩ := hg x (mem_singleton_self x)
      obtain ⟨-, hx1, hx2⟩ := hθ x (mem_singleton_self x)
      rw [hTx]
      refine pkCh_mixed_of (pkCh_diag_pos hc hgx hhat ?_ ?_) (by rw [hrx, hhq]; exact hxq)
      · rw [hpx, hhp]
        omega
      · rw [hpx, hhp]
        omega
  have hZ : sepPairs (k + 1) T ∈ gFamily (k + 1) := mem_image.2 ⟨T, pkCh_mem_gLeg.2 ⟨hTsub, hTG⟩, rfl⟩
  obtain ⟨⟨y1, y2⟩, hσ⟩ := (pkCh_transversal_iff.1 hT) _ hZ
  obtain ⟨hσ1, hσ2⟩ := mem_inter.1 hσ
  obtain ⟨hy1, hy2, hy12, hin⟩ := (pkCo_mem_sepPairs hTsub).1 hσ1
  obtain ⟨-, hnc⟩ := pkCh_mem_childMiss.1 hσ2
  dsimp only at hy1 hy2 hy12 hin hnc
  obtain ⟨hy1T, hy2T, ⟨t, htT, hbt⟩, -⟩ := (pkCh_inST_pos hc hTsub hy1 hy2).1 hin
  have hy1h : y1 ≠ hat := fun h => hy1T ((hTmem y1).2 (Or.inr h))
  have hy2h : y2 ≠ hat := fun h => hy2T ((hTmem y2).2 (Or.inr h))
  obtain ⟨hp1, hx1, hq1, -⟩ := pkCh_ch_y H hy1 hy1h
  obtain ⟨hp2, hx2, hq2, -⟩ := pkCh_ch_y H hy2 hy2h
  rw [pkCh_cpi_nn hy1h hy2h] at hnc
  have hx1Θ : f y1 ∉ Θ := fun h => hy1T ((hTmem y1).2 (Or.inl ⟨f y1, h, by rw [hq1]; exact pkCo_vtx_cycPos hc hy1⟩))
  have hx2Θ : f y2 ∉ Θ := fun h => hy2T ((hTmem y2).2 (Or.inl ⟨f y2, h, by rw [hq2]; exact pkCo_vtx_cycPos hc hy2⟩))
  rcases (hTmem t).1 htT with ⟨θ, hθΘ, rfl⟩ | h
  · have e := (hg θ hθΘ).2.1
    rw [e] at hbt
    have hτ := pkCh_sepIn_of hs (show k + 1 ≤ N by omega) hx1 hx2 (by omega) (by omega) hx1Θ hx2Θ hθΘ
      (by omega) (by omega)
    exact disjoint_left.1 hdis hτ (pkCh_mem_missing.2 ⟨(pkCo_mem_sepIn.1 hτ).1, hnc⟩)
  · rw [h, hhp] at hbt
    omega

/-- [Child](3) "⇐", `P̂ ∈ T` (BP App. C §C-2 (3)(b)): `T ∖ {P̂}` is an admissible trace of `L`; a missing runcut pair
lifts to a missing child pair in `S_T`. -/
theorem pkCh_tr_hat {N s k c hat : ℕ} {f : ℕ → ℕ} {S : Finset (ℕ × ℕ)} (H : pkCh_CH N s k c hat f)
    (hNF : NoFreeSep N S s k ((s + 1) % 2)) {T : Finset ℕ} (hTsub : T ⊆ Icc 1 (k + 1)) (hTG : IsGSet (k + 1) T)
    (hh : hat ∈ T) :
    (sepPairs (k + 1) T ∩ missing (k + 1) ((diagonals (k + 1)).filter
      (fun σ => ChildPairIn N S s k hat f σ.1 σ.2))).Nonempty := by
  obtain ⟨hs, hk3, hkN, hk1, hE, hc, hcs, hhat, hhp, hf⟩ := pkCh_CH_iff.1 H
  have hhq := pkCh_ch_hat H
  have hm2 : (k + 1) % 2 = 0 := by omega
  have hint : ∀ y ∈ T, y ≠ hat → 1 ≤ cycPos (k + 1) c y ∧ cycPos (k + 1) c y + 2 ≤ k := by
    intro y hy hyh
    have hyI := hTsub hy
    have hlt := (pkCh_ch_y H hyI hyh).1
    rcases pkCh_isG_iff.1 hTG with hA | hM
    · have hpy := pkCo_cycPos_mod_two hm2 hc hyI
      have hpar : y % 2 = hat % 2 := by
        rcases hA with hA | hA
        · obtain ⟨-, -, hp⟩ := pkCh_adm_iff.1 hA
          rw [hp y hy, hp hat hh]
        · obtain ⟨-, -, hp⟩ := pkCh_adm_iff.1 hA
          rw [hp y hy, hp hat hh]
      omega
    · obtain ⟨a, ha, b, hb, hab, h1, h2, -⟩ := pkCh_mixed_iff.1 hM
      have hy' := hy
      rw [hab, mem_insert, mem_singleton] at hy'
      have hh' := hh
      rw [hab, mem_insert, mem_singleton] at hh'
      have ha' := mem_Icc.1 ha
      have hb' := mem_Icc.1 hb
      have hd : (min y hat, max y hat) ∈ diagonals (k + 1) := by
        rw [mem_diagonals]
        dsimp only
        omega
      have := pkCh_pos_of_diag hc hyI hhat hd
      rw [hhp] at this
      omega
  have hshape : (T.erase hat).Nonempty ∧ ((∀ y ∈ T, y % 2 = hat % 2) ∨ ∃ y, T.erase hat = {y}) := by
    rcases pkCh_isG_iff.1 hTG with hA | hM
    · have hA' : ∃ r, Admissible (k + 1) r T := by
        rcases hA with h | h
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
      obtain ⟨r, hr⟩ := hA'
      obtain ⟨-, hc2, hp⟩ := pkCh_adm_iff.1 hr
      have := card_erase_of_mem hh
      refine ⟨card_pos.1 (by omega), Or.inl fun y hy => by rw [hp y hy, hp hat hh]⟩
    · obtain ⟨a, ha, b, hb, hab, h1, h2, -⟩ := pkCh_mixed_iff.1 hM
      have hh' := hh
      rw [hab, mem_insert, mem_singleton] at hh'
      rcases hh' with e | e
      · have he : T.erase hat = {b} := by
          rw [hab, e, erase_insert (fun h => by rw [mem_singleton] at h; omega)]
        exact ⟨by rw [he]; exact singleton_nonempty b, Or.inr ⟨b, he⟩⟩
      · have he : T.erase hat = {a} := by
          rw [hab, e, pair_comm, erase_insert (fun h => by rw [mem_singleton] at h; omega)]
        exact ⟨by rw [he]; exact singleton_nonempty a, Or.inr ⟨a, he⟩⟩
  have hΘ : (T.erase hat).image f ∈ admSeps N s k ((s + 1) % 2) := by
    rw [pkCo_mem_admSeps]
    refine ⟨fun θ hθ => ?_, ?_⟩
    · obtain ⟨y, hy, rfl⟩ := mem_image.1 hθ
      obtain ⟨hyh, hyT⟩ := mem_erase.1 hy
      obtain ⟨-, hfy, hq, -⟩ := pkCh_ch_y H (hTsub hyT) hyh
      have := hint y hyT hyh
      exact (pkCo_mem_intArc hs (by omega)).2 ⟨hfy, by omega, by omega⟩
    · rcases hshape.2 with hp | ⟨y, he⟩
      · have hne := hshape.1.image f
        have := card_pos.2 hne
        rcases Nat.lt_or_ge ((T.erase hat).image f).card 2 with h | h
        · left
          omega
        · right
          refine ⟨h, fun θ hθ => ?_⟩
          obtain ⟨y, hy, rfl⟩ := mem_image.1 hθ
          obtain ⟨hyh, hyT⟩ := mem_erase.1 hy
          rw [(pkCh_ch_y H (hTsub hyT) hyh).2.2.2, hp y hyT, hhq]
      · left
        rw [he, image_singleton, card_singleton]
  obtain ⟨⟨x1, x2⟩, hτ1, hτ2⟩ := not_disjoint_iff.1 (pkCh_noFree_iff.1 hNF _ hΘ)
  obtain ⟨hd, hx1a, hx2a, hx1Θ, hx2Θ, θ, hθΘ, hb1, hb2⟩ := pkCo_mem_sepIn.1 hτ1
  obtain ⟨-, hτS⟩ := pkCh_mem_missing.1 hτ2
  dsimp only at hd hx1a hx2a hx1Θ hx2Θ hb1 hb2
  have hd' := mem_diagonals.1 hd
  dsimp only at hd'
  obtain ⟨hx1, hp1⟩ := (pkCo_mem_cycArc_pos hs (by omega)).1 hx1a
  obtain ⟨hx2, hp2⟩ := (pkCo_mem_cycArc_pos hs (by omega)).1 hx2a
  obtain ⟨y1, hy1, hy1h, hq1, hf1⟩ := pkCh_ch_x H hx1 hp1
  obtain ⟨y2, hy2, hy2h, hq2, hf2⟩ := pkCh_ch_x H hx2 hp2
  obtain ⟨y0, hy0, rfl⟩ := mem_image.1 hθΘ
  obtain ⟨hy0h, hy0T⟩ := mem_erase.1 hy0
  have hq0 := (pkCh_ch_y H (hTsub hy0T) hy0h).2.2.1
  have hy1T : y1 ∉ T := fun h => hx1Θ (by rw [← hf1]; exact mem_image_of_mem f (mem_erase.2 ⟨hy1h, h⟩))
  have hy2T : y2 ∉ T := fun h => hx2Θ (by rw [← hf2]; exact mem_image_of_mem f (mem_erase.2 ⟨hy2h, h⟩))
  have hin : InST T y1 y2 := (pkCh_inST_pos hc hTsub hy1 hy2).2
    ⟨hy1T, hy2T, ⟨y0, hy0T, by omega⟩, ⟨hat, hh, by omega⟩⟩
  have hne : y1 ≠ y2 := fun h => by
    rw [h] at hq1
    omega
  have hy1' := mem_Icc.1 hy1
  have hy2' := mem_Icc.1 hy2
  have hmin : min y1 y2 ≠ hat := by
    rcases min_choice y1 y2 with e | e <;> rw [e]
    · exact hy1h
    · exact hy2h
  have hmax : max y1 y2 ≠ hat := by
    rcases max_choice y1 y2 with e | e <;> rw [e]
    · exact hy1h
    · exact hy2h
  have hin' := pkCh_inST_minmax.2 hin
  have hI1 : min y1 y2 ∈ Icc 1 (k + 1) := mem_Icc.2 ⟨by omega, by omega⟩
  have hI2 : max y1 y2 ∈ Icc 1 (k + 1) := mem_Icc.2 ⟨by omega, by omega⟩
  have hlt : min y1 y2 < max y1 y2 := by omega
  refine ⟨(min y1 y2, max y1 y2), mem_inter.2 ⟨(pkCo_mem_sepPairs hTsub).2 ⟨hI1, hI2, hlt, hin'⟩,
    pkCh_mem_childMiss.2 ⟨pkCo_diag_of_inST hTsub hI1 hI2 hlt hin', ?_⟩⟩⟩
  show ¬ ChildPairIn N S s k hat f (min y1 y2) (max y1 y2)
  rw [pkCh_cpi_nn hmin hmax, pkCh_minmax_map f y1 y2, hf1, hf2, min_eq_left (by omega), max_eq_right (by omega)]
  exact hτS

/-- [Child](3) "⇐", `P̂ ∉ T`, a separated pair with one leg in `L` and one outside: the child pair `{x, P̂}`. -/
theorem pkCh_tr_mixed {N s k c hat : ℕ} {f : ℕ → ℕ} {S : Finset (ℕ × ℕ)} (H : pkCh_CH N s k c hat f)
    {T : Finset ℕ} (hTsub : T ⊆ Icc 1 (k + 1)) (hh : hat ∉ T) {xa xb : ℕ} (hxa : xa ∈ Icc 1 N)
    (hxb : xb ∈ Icc 1 N) (hia : cycPos N s xa < k) (hib : k ≤ cycPos N s xb) (hxaT : xa ∉ T.image f)
    (hτS : (min xa xb, max xa xb) ∉ S) {yt yt' : ℕ} (hyt : yt ∈ T) (hyt' : yt' ∈ T)
    (hbt : cycPos N s xa < cycPos (k + 1) c yt) (hnbt : cycPos (k + 1) c yt' < cycPos N s xa) :
    (sepPairs (k + 1) T ∩ missing (k + 1) ((diagonals (k + 1)).filter
      (fun σ => ChildPairIn N S s k hat f σ.1 σ.2))).Nonempty := by
  obtain ⟨hs, hk3, hkN, hk1, hE, hc, hcs, hhat, hhp, hf⟩ := pkCh_CH_iff.1 H
  have hyth : yt ≠ hat := fun h => hh (h ▸ hyt)
  have hpt := (pkCh_ch_y H (hTsub hyt) hyth).1
  obtain ⟨ya, hya, hyah, hqa, hfa⟩ := pkCh_ch_x H hxa hia
  have hyaT : ya ∉ T := fun h => hxaT (by rw [← hfa]; exact mem_image_of_mem f h)
  have hin : InST T ya hat := (pkCh_inST_pos hc hTsub hya hhat).2
    ⟨hyaT, hh, ⟨yt, hyt, by omega⟩, ⟨yt', hyt', by omega⟩⟩
  have hin' := pkCh_inST_minmax.2 hin
  have hya' := mem_Icc.1 hya
  have hhat' := mem_Icc.1 hhat
  have hI1 : min ya hat ∈ Icc 1 (k + 1) := mem_Icc.2 ⟨by omega, by omega⟩
  have hI2 : max ya hat ∈ Icc 1 (k + 1) := mem_Icc.2 ⟨by omega, by omega⟩
  have hlt : min ya hat < max ya hat := by omega
  have hxbL : xb ∉ cycArc N s k := fun h => by
    have := ((pkCo_mem_cycArc_pos hs (by omega)).1 h).2
    omega
  refine ⟨(min ya hat, max ya hat), mem_inter.2 ⟨(pkCo_mem_sepPairs hTsub).2 ⟨hI1, hI2, hlt, hin'⟩,
    pkCh_mem_childMiss.2 ⟨pkCo_diag_of_inST hTsub hI1 hI2 hlt hin', ?_⟩⟩⟩
  show ¬ ChildPairIn N S s k hat f (min ya hat) (max ya hat)
  rcases le_total ya hat with hle | hle
  · rw [min_eq_left hle, max_eq_right hle, pkCh_cpi_r hyah rfl]
    intro hall
    have := hall xb hxb hxbL
    rw [hfa] at this
    exact hτS this
  · rw [min_eq_right hle, max_eq_left hle, pkCh_cpi_l rfl]
    intro hall
    have := hall xb hxb hxbL
    rw [hfa] at this
    exact hτS this

/-- [Child](3) "⇐", `P̂ ∉ T`, a separated pair with both legs in `L`. -/
theorem pkCh_tr_in {N s k c hat : ℕ} {f : ℕ → ℕ} {S : Finset (ℕ × ℕ)} (H : pkCh_CH N s k c hat f)
    {T : Finset ℕ} (hTsub : T ⊆ Icc 1 (k + 1)) (hh : hat ∉ T) {x1 x2 : ℕ} (hx1 : x1 ∈ Icc 1 N)
    (hx2 : x2 ∈ Icc 1 N) (hi1 : cycPos N s x1 < k) (hi2 : cycPos N s x2 < k) (hx1T : x1 ∉ T.image f)
    (hx2T : x2 ∉ T.image f) (hτS : (min x1 x2, max x1 x2) ∉ S) {yt yt' : ℕ} (hyt : yt ∈ T) (hyt' : yt' ∈ T)
    (hbt : min (cycPos N s x1) (cycPos N s x2) < cycPos (k + 1) c yt ∧
      cycPos (k + 1) c yt < max (cycPos N s x1) (cycPos N s x2))
    (hnbt : ¬ (min (cycPos N s x1) (cycPos N s x2) < cycPos (k + 1) c yt' ∧
      cycPos (k + 1) c yt' < max (cycPos N s x1) (cycPos N s x2))) :
    (sepPairs (k + 1) T ∩ missing (k + 1) ((diagonals (k + 1)).filter
      (fun σ => ChildPairIn N S s k hat f σ.1 σ.2))).Nonempty := by
  obtain ⟨hs, hk3, hkN, hk1, hE, hc, hcs, hhat, hhp, hf⟩ := pkCh_CH_iff.1 H
  obtain ⟨y1, hy1, hy1h, hq1, hf1⟩ := pkCh_ch_x H hx1 hi1
  obtain ⟨y2, hy2, hy2h, hq2, hf2⟩ := pkCh_ch_x H hx2 hi2
  have hy1T : y1 ∉ T := fun h => hx1T (by rw [← hf1]; exact mem_image_of_mem f h)
  have hy2T : y2 ∉ T := fun h => hx2T (by rw [← hf2]; exact mem_image_of_mem f h)
  rw [← hq1, ← hq2] at hbt hnbt
  have hin : InST T y1 y2 := (pkCh_inST_pos hc hTsub hy1 hy2).2 ⟨hy1T, hy2T, ⟨yt, hyt, hbt⟩, ⟨yt', hyt', hnbt⟩⟩
  have hne : y1 ≠ y2 := fun h => by
    rw [h] at hbt
    omega
  have hy1' := mem_Icc.1 hy1
  have hy2' := mem_Icc.1 hy2
  have hmin : min y1 y2 ≠ hat := by
    rcases min_choice y1 y2 with e | e <;> rw [e]
    · exact hy1h
    · exact hy2h
  have hmax : max y1 y2 ≠ hat := by
    rcases max_choice y1 y2 with e | e <;> rw [e]
    · exact hy1h
    · exact hy2h
  have hin' := pkCh_inST_minmax.2 hin
  have hI1 : min y1 y2 ∈ Icc 1 (k + 1) := mem_Icc.2 ⟨by omega, by omega⟩
  have hI2 : max y1 y2 ∈ Icc 1 (k + 1) := mem_Icc.2 ⟨by omega, by omega⟩
  have hlt : min y1 y2 < max y1 y2 := by omega
  refine ⟨(min y1 y2, max y1 y2), mem_inter.2 ⟨(pkCo_mem_sepPairs hTsub).2 ⟨hI1, hI2, hlt, hin'⟩,
    pkCh_mem_childMiss.2 ⟨pkCo_diag_of_inST hTsub hI1 hI2 hlt hin', ?_⟩⟩⟩
  show ¬ ChildPairIn N S s k hat f (min y1 y2) (max y1 y2)
  rw [pkCh_cpi_nn hmin hmax, pkCh_minmax_map f y1 y2, hf1, hf2]
  exact hτS

/-- [Child](3) "⇐", `P̂ ∉ T` (BP App. C §C-2 (3)(a)): `T ⊆ L` is a member of `𝒢_N`, which `S ∈ F^π` does not contain;
its missing pair maps to a missing child pair in `S_T`. -/
theorem pkCh_tr_nohat {N s k c hat : ℕ} {f : ℕ → ℕ} {S : Finset (ℕ × ℕ)} (H : pkCh_CH N s k c hat f)
    (hG : ¬ ContainsGMember N S) {T : Finset ℕ} (hTsub : T ⊆ Icc 1 (k + 1)) (hTG : IsGSet (k + 1) T)
    (hh : hat ∉ T) :
    (sepPairs (k + 1) T ∩ missing (k + 1) ((diagonals (k + 1)).filter
      (fun σ => ChildPairIn N S s k hat f σ.1 σ.2))).Nonempty := by
  obtain ⟨hs, hk3, hkN, hk1, hE, hc, hcs, hhat, hhp, hf⟩ := pkCh_CH_iff.1 H
  have hyT : ∀ y ∈ T, y ≠ hat := fun y hy h => hh (h ▸ hy)
  have hT'sub : T.image f ⊆ Icc 1 N := fun t ht => by
    obtain ⟨y, hy, rfl⟩ := mem_image.1 ht
    exact (pkCh_ch_y H (hTsub hy) (hyT y hy)).2.1
  have hT'G : IsGSet N (T.image f) := by
    rcases pkCh_isG_iff.1 hTG with hA | hM
    · have hA' : ∃ r, Admissible (k + 1) r T := by
        rcases hA with h | h
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
      obtain ⟨r, hr⟩ := hA'
      obtain ⟨-, hc2, hp⟩ := pkCh_adm_iff.1 hr
      obtain ⟨y1, hy1, y2, hy2, hne⟩ := one_lt_card.1 (show 1 < T.card by omega)
      have hfne : f y1 ≠ f y2 := fun h => hne (pkCo_cycPos_inj hc (hTsub hy1) (hTsub hy2) (by
        have e1 := (pkCh_ch_y H (hTsub hy1) (hyT y1 hy1)).2.2.1
        have e2 := (pkCh_ch_y H (hTsub hy2) (hyT y2 hy2)).2.2.1
        rw [h] at e1
        omega))
      have h2 := one_lt_card.2 ⟨f y1, mem_image_of_mem f hy1, f y2, mem_image_of_mem f hy2, hfne⟩
      refine pkCh_sameParity hT'sub (by omega) (r := r) ?_
      intro t ht
      obtain ⟨y, hy, rfl⟩ := mem_image.1 ht
      rw [(pkCh_ch_y H (hTsub hy) (hyT y hy)).2.2.2]
      exact hp y hy
    · obtain ⟨a, ha, b, hb, hab, h1, h2, h3⟩ := pkCh_mixed_iff.1 hM
      have haT : a ∈ T := by
        rw [hab]
        exact mem_insert_self a {b}
      have hbT : b ∈ T := by
        rw [hab]
        exact mem_insert_of_mem (mem_singleton_self b)
      obtain ⟨hpa, hfa, hqa, hra⟩ := pkCh_ch_y H ha (hyT a haT)
      obtain ⟨hpb, hfb, hqb, hrb⟩ := pkCh_ch_y H hb (hyT b hbT)
      have hdab : (min a b, max a b) ∈ diagonals (k + 1) := by
        rw [min_eq_left (by omega), max_eq_right (by omega), mem_diagonals]
        exact ⟨(mem_Icc.1 ha).1, (mem_Icc.1 hb).2, h1, h2⟩
      have hpos := pkCh_pos_of_diag hc ha hb hdab
      have hd := pkCh_diag_pos hs hfa hfb (by rw [hqa, hqb]; omega) (by rw [hqa, hqb]; omega)
      rw [hab, image_insert, image_singleton]
      exact pkCh_mixed_of hd (by rw [hra, hrb]; exact h3)
  have hnot : ¬ sepPairs N (T.image f) ⊆ S := fun hsub =>
    hG (pkCh_cgm_iff.2 ⟨_, mem_image.2 ⟨T.image f, pkCh_mem_gLeg.2 ⟨hT'sub, hT'G⟩, rfl⟩, hsub⟩)
  obtain ⟨⟨x1, x2⟩, hτ, hτS⟩ := not_subset.1 hnot
  obtain ⟨hx1, hx2, hx12, hin⟩ := (pkCo_mem_sepPairs hT'sub).1 hτ
  dsimp only at hx1 hx2 hx12 hin
  obtain ⟨hx1T, hx2T, ⟨t, htT, hbt⟩, ⟨t', ht'T, hnbt⟩⟩ := (pkCh_inST_pos hs hT'sub hx1 hx2).1 hin
  obtain ⟨yt, hyt, rfl⟩ := mem_image.1 htT
  obtain ⟨yt', hyt', rfl⟩ := mem_image.1 ht'T
  obtain ⟨hpt, hft, hqt, -⟩ := pkCh_ch_y H (hTsub hyt) (hyT yt hyt)
  obtain ⟨hpt', hft', hqt', -⟩ := pkCh_ch_y H (hTsub hyt') (hyT yt' hyt')
  rw [hqt] at hbt
  rw [hqt'] at hnbt
  have hS12 : (min x1 x2, max x1 x2) ∉ S := by
    rw [min_eq_left hx12.le, max_eq_right hx12.le]
    exact hτS
  have hS21 : (min x2 x1, max x2 x1) ∉ S := by
    rw [min_eq_right hx12.le, max_eq_left hx12.le]
    exact hτS
  by_cases h1 : cycPos N s x1 < k
  · by_cases h2 : cycPos N s x2 < k
    · exact pkCh_tr_in H hTsub hh hx1 hx2 h1 h2 hx1T hx2T hS12 hyt hyt' hbt hnbt
    · have hneq : cycPos (k + 1) c yt' ≠ cycPos N s x1 := fun h => hx1T (by
        rw [← pkCo_cycPos_inj hs hft' hx1 (by rw [hqt']; exact h)]
        exact mem_image_of_mem f hyt')
      exact pkCh_tr_mixed H hTsub hh hx1 hx2 h1 (by omega) hx1T hS12 hyt hyt' (by omega) (by omega)
  · by_cases h2 : cycPos N s x2 < k
    · have hneq : cycPos (k + 1) c yt' ≠ cycPos N s x2 := fun h => hx2T (by
        rw [← pkCo_cycPos_inj hs hft' hx2 (by rw [hqt']; exact h)]
        exact mem_image_of_mem f hyt')
      exact pkCh_tr_mixed H hTsub hh hx2 hx1 h2 (by omega) hx2T hS21 hyt hyt' (by omega) (by omega)
    · omega

theorem pkCh_child_tr {N s k c hat : ℕ} {f : ℕ → ℕ} {S : Finset (ℕ × ℕ)} (H : pkCh_CH N s k c hat f)
    (hG : ¬ ContainsGMember N S) (hNF : NoFreeSep N S s k ((s + 1) % 2)) :
    Transversal (k + 1) (missing (k + 1) ((diagonals (k + 1)).filter
      (fun σ => ChildPairIn N S s k hat f σ.1 σ.2))) := by
  rw [pkCh_transversal_iff]
  intro Z hZ
  obtain ⟨T, hT, rfl⟩ := mem_image.1 hZ
  obtain ⟨hTsub, hTG⟩ := pkCh_mem_gLeg.1 hT
  by_cases hh : hat ∈ T
  · exact pkCh_tr_hat H hNF hTsub hTG hh
  · exact pkCh_tr_nohat H hG hTsub hTG hh

/-- **[Child](3), generic side** (R2-Z182 Theorem 1; BP App. C §C-2): for `S ∈ F^π_N` the child set of the side is in
`F^π_{k+1}` iff the side satisfies `Sep_all` with hub parity `(s + 1) % 2`. -/
theorem pkCh_childGen {N s k c hat : ℕ} {f : ℕ → ℕ} {S : Finset (ℕ × ℕ)} (H : pkCh_CH N s k c hat f)
    (hF : InFpi N S) :
    InFpi (k + 1) ((diagonals (k + 1)).filter (fun σ => ChildPairIn N S s k hat f σ.1 σ.2)) ↔
      NoFreeSep N S s k ((s + 1) % 2) := by
  obtain ⟨hs, hk3, hkN, hk1, hE, -⟩ := pkCh_CH_iff.1 H
  obtain ⟨-, -, hG⟩ := pkCh_fpi_iff.1 hF
  rw [fpi_iff (by omega) (Nat.even_iff.2 (by omega)) (filter_subset _ _)]
  exact ⟨pkCh_child_nf H, pkCh_child_tr H hG⟩


/-! [Int] helpers: neighbours through positions, the cut dictionary, Lemma 5′ (one generic side form). -/

theorem pkCh_pos_next {N s x : ℕ} (hs : s ∈ Icc 1 N) (hx : x ∈ Icc 1 N) (h : cycPos N s x + 1 < N) :
    cycPos N s (vtx N (x + 1)) = cycPos N s x + 1 := by
  have hN : 1 ≤ N := by have := mem_Icc.1 hs; omega
  have hv := vtx_bounds N (x + 1) hN
  rw [mem_Icc] at hs hx
  rw [pkCo_cycPos_eq hs.1 hs.2 hx.1 hx.2] at h
  rw [pkCo_cycPos_eq hs.1 hs.2 hv.1 hv.2, pkCo_cycPos_eq hs.1 hs.2 hx.1 hx.2, pkCo_vtx_eq hx.1 hx.2 hN]
  split_ifs at h ⊢ <;> omega

theorem pkCh_pos_prev {N s x : ℕ} (hs : s ∈ Icc 1 N) (hx : x ∈ Icc 1 N) (h : 1 ≤ cycPos N s x) :
    cycPos N s (vtx N (x + (N - 1))) = cycPos N s x - 1 := by
  have hN : 1 ≤ N := by have := mem_Icc.1 hs; omega
  have hv := vtx_bounds N (x + (N - 1)) hN
  rw [mem_Icc] at hs hx
  rw [pkCo_cycPos_eq hs.1 hs.2 hx.1 hx.2] at h
  rw [pkCo_cycPos_eq hs.1 hs.2 hv.1 hv.2, pkCo_cycPos_eq hs.1 hs.2 hx.1 hx.2, pkCo_vtx_eq hx.1 hx.2 (by omega)]
  split_ifs at h ⊢ <;> omega

/-- All legs outside an arc `Y ∋ u, v` lie on one side of `{u, v}`, read through positions from any start. -/
theorem pkCh_out_side {N s sY kY u v θ t : ℕ} (hs : s ∈ Icc 1 N) (hsY : sY ∈ Icc 1 N) (hkY : kY ≤ N)
    (hu : u ∈ cycArc N sY kY) (hv : v ∈ cycArc N sY kY) (hθI : θ ∈ Icc 1 N) (hθ : θ ∉ cycArc N sY kY)
    (htI : t ∈ Icc 1 N) (ht : t ∉ cycArc N sY kY)
    (hb : min (cycPos N s u) (cycPos N s v) < cycPos N s θ ∧ cycPos N s θ < max (cycPos N s u) (cycPos N s v)) :
    min (cycPos N s u) (cycPos N s v) < cycPos N s t ∧ cycPos N s t < max (cycPos N s u) (cycPos N s v) := by
  obtain ⟨huI, hup⟩ := (pkCo_mem_cycArc_pos hsY hkY).1 hu
  obtain ⟨hvI, hvp⟩ := (pkCo_mem_cycArc_pos hsY hkY).1 hv
  have hθp : kY ≤ cycPos N sY θ := by
    by_contra h
    exact hθ ((pkCo_mem_cycArc_pos hsY hkY).2 ⟨hθI, by omega⟩)
  have htp : kY ≤ cycPos N sY t := by
    by_contra h
    exact ht ((pkCo_mem_cycArc_pos hsY hkY).2 ⟨htI, by omega⟩)
  have hθu : θ ≠ u := fun h => hθ (h ▸ hu)
  have hθv : θ ≠ v := fun h => hθ (h ▸ hv)
  have htu : t ≠ u := fun h => ht (h ▸ hu)
  have htv : t ≠ v := fun h => ht (h ▸ hv)
  have e1 := pkCh_btw hsY huI hvI hθI hθu hθv
  have e2 := pkCh_btw hsY huI hvI htI htu htv
  have e3 := pkCh_btw hs huI hvI hθI hθu hθv
  have e4 := pkCh_btw hs huI hvI htI htu htv
  have nY1 : ¬ (min (cycPos N sY u) (cycPos N sY v) < cycPos N sY θ ∧
      cycPos N sY θ < max (cycPos N sY u) (cycPos N sY v)) := by omega
  have nY2 : ¬ (min (cycPos N sY u) (cycPos N sY v) < cycPos N sY t ∧
      cycPos N sY t < max (cycPos N sY u) (cycPos N sY v)) := by omega
  by_cases cY : min u v < sY ∧ sY ≤ max u v
  · by_cases cs : min u v < s ∧ s ≤ max u v
    · exact absurd hb ((e3.1 cs).1 ((e1.1 cY).2 nY1))
    · exact (e4.2 cs).1 ((e2.1 cY).2 nY2)
  · by_cases cs : min u v < s ∧ s ≤ max u v
    · by_contra h
      exact nY2 ((e2.2 cY).1 ((e4.1 cs).2 h))
    · exact absurd ((e3.2 cs).2 hb) (fun h => nY1 ((e1.2 cY).1 h))

/-- **Lemma 5′, generic side form** [BP App. D §3a; R2-Z189 C1] (both the main form and its mirror): `L = (sL, kL)` a
side of a chord with `Sep_all(L)`, `X = (sX, kX)` / `Y = (sY, kY)` the two sides of a `𝒫₀` chord (`X`'s ends have the hub
parity of `L`), the `minrect` of the second chord clean between `X` and `Y`, the missing pairs of `L`'s end parity inside
`L` lying inside `Y`, and `X` meeting the complement of `L`: then `X` misses `L`. -/
theorem pkCh_lem5 {N sL kL sX kX sY kY : ℕ} {S : Finset (ℕ × ℕ)} (hE : N % 2 = 0)
    (hsL : sL ∈ Icc 1 N) (hkL1 : kL % 2 = 1) (hkL3 : 3 ≤ kL) (hkLN : kL + 3 ≤ N)
    (hsX : sX ∈ Icc 1 N) (hsXp : sX % 2 = (sL + 1) % 2) (hkX1 : kX % 2 = 1) (hkXN : kX ≤ N)
    (hsY : sY ∈ Icc 1 N) (hkYN : kY ≤ N)
    (hXY : ∀ x ∈ Icc 1 N, x ∈ cycArc N sX kX ↔ x ∉ cycArc N sY kY)
    (hNF : NoFreeSep N S sL kL ((sL + 1) % 2))
    (hmin : ∀ e ∈ cycArc N sX kX, ∀ y ∈ cycArc N sY kY, e % 2 = sL % 2 → y % 2 = (sL + 1) % 2 →
      (min e y, max e y) ∉ missing N S)
    (hin : ∀ u v, (u, v) ∈ missing N S → u % 2 = sL % 2 → v % 2 = sL % 2 → u ∈ cycArc N sL kL →
      v ∈ cycArc N sL kL → u ∈ cycArc N sY kY ∧ v ∈ cycArc N sY kY)
    {t : ℕ} (htI : t ∈ Icc 1 N) (htL : t ∉ cycArc N sL kL) (htX : t ∈ cycArc N sX kX) :
    ∀ x ∈ cycArc N sX kX, x ∉ cycArc N sL kL := by
  intro x hxX hxL
  have hN1 : 1 ≤ N := by omega
  have hkLN' : kL ≤ N := by omega
  obtain ⟨hxI, hpx⟩ := (pkCo_mem_cycArc_pos hsL hkLN').1 hxL
  obtain ⟨-, hpxX⟩ := (pkCo_mem_cycArc_pos hsX hkXN).1 hxX
  obtain ⟨Θ, hΘdef⟩ : ∃ Θ : Finset ℕ,
      Θ = (cycArc N sL kL).filter (fun y => y ∈ cycArc N sX kX ∧ y % 2 = (sL + 1) % 2) := ⟨_, rfl⟩
  have hΘmem : ∀ y, y ∈ Θ ↔ y ∈ cycArc N sL kL ∧ y ∈ cycArc N sX kX ∧ y % 2 = (sL + 1) % 2 := by
    intro y
    rw [hΘdef, mem_filter]
  have hΘne : Θ.Nonempty := by
    by_cases hxp : x % 2 = (sL + 1) % 2
    · exact ⟨x, (hΘmem x).2 ⟨hxL, hxX, hxp⟩⟩
    · have hqX := pkCo_cycPos_mod_two hE hsX hxI
      have hqL := pkCo_cycPos_mod_two hE hsL hxI
      have hX1 : 1 ≤ cycPos N sX x := by omega
      have hX2 : cycPos N sX x + 2 ≤ kX := by omega
      have hnI := mem_Icc.2 (vtx_bounds N (x + 1) hN1)
      have hpI := mem_Icc.2 (vtx_bounds N (x + (N - 1)) hN1)
      by_cases hnx : cycPos N sL x + 1 < kL
      · have e1 := pkCh_pos_next hsL hxI (by omega)
        have e2 := pkCh_pos_next hsX hxI (by omega)
        have e3 := pkCo_vtx_mod_two hN1 hE (x + 1)
        refine ⟨vtx N (x + 1), (hΘmem _).2 ⟨(pkCo_mem_cycArc_pos hsL hkLN').2 ⟨hnI, by omega⟩,
          (pkCo_mem_cycArc_pos hsX hkXN).2 ⟨hnI, by omega⟩, by omega⟩⟩
      · have e1 := pkCh_pos_prev hsL hxI (by omega)
        have e2 := pkCh_pos_prev hsX hxI hX1
        have e3 := pkCo_vtx_mod_two hN1 hE (x + (N - 1))
        refine ⟨vtx N (x + (N - 1)), (hΘmem _).2 ⟨(pkCo_mem_cycArc_pos hsL hkLN').2 ⟨hpI, by omega⟩,
          (pkCo_mem_cycArc_pos hsX hkXN).2 ⟨hpI, by omega⟩, by omega⟩⟩
  have hΘadm : Θ ∈ admSeps N sL kL ((sL + 1) % 2) := by
    rw [pkCo_mem_admSeps]
    refine ⟨fun y hy => ?_, ?_⟩
    · obtain ⟨hyL, -, hyp⟩ := (hΘmem y).1 hy
      obtain ⟨hyI, hyk⟩ := (pkCo_mem_cycArc_pos hsL hkLN').1 hyL
      have := pkCo_cycPos_mod_two hE hsL hyI
      exact (pkCo_mem_intArc hsL hkLN').2 ⟨hyI, by omega, by omega⟩
    · have := card_pos.2 hΘne
      rcases Nat.lt_or_ge Θ.card 2 with h | h
      · left
        omega
      · right
        exact ⟨h, fun y hy => ((hΘmem y).1 hy).2.2⟩
  obtain ⟨⟨u, v⟩, hτ1, hτ2⟩ := not_disjoint_iff.1 (pkCh_noFree_iff.1 hNF Θ hΘadm)
  obtain ⟨hd, huL, hvL, huΘ, hvΘ, θ, hθΘ, hb1, hb2⟩ := pkCo_mem_sepIn.1 hτ1
  dsimp only at hd huL hvL huΘ hvΘ hb1 hb2
  obtain ⟨huI, hup⟩ := (pkCo_mem_cycArc_pos hsL hkLN').1 huL
  obtain ⟨hvI, hvp⟩ := (pkCo_mem_cycArc_pos hsL hkLN').1 hvL
  obtain ⟨hθL, hθX, -⟩ := (hΘmem θ).1 hθΘ
  have hθI := ((pkCo_mem_cycArc_pos hsL hkLN').1 hθL).1
  have hone : u ∈ cycArc N sX kX ∨ v ∈ cycArc N sX kX := by
    by_contra hc
    obtain ⟨hu', hv'⟩ := not_or.1 hc
    have huY : u ∈ cycArc N sY kY := by
      by_contra h
      exact hu' ((hXY u huI).2 h)
    have hvY : v ∈ cycArc N sY kY := by
      by_contra h
      exact hv' ((hXY v hvI).2 h)
    have hb := pkCh_out_side hsL hsY hkYN huY hvY hθI ((hXY θ hθI).1 hθX) htI ((hXY t htI).1 htX) ⟨hb1, hb2⟩
    have htp : kL ≤ cycPos N sL t := by
      by_contra h
      exact htL ((pkCo_mem_cycArc_pos hsL hkLN').2 ⟨htI, by omega⟩)
    omega
  have hd' := mem_diagonals.1 hd
  dsimp only at hd'
  rcases hone with huX | hvX
  · have hup2 : u % 2 = sL % 2 := by
      by_contra h
      exact huΘ ((hΘmem u).2 ⟨huL, huX, by omega⟩)
    by_cases hvq : v % 2 = (sL + 1) % 2
    · have hvX : v ∉ cycArc N sX kX := fun h => hvΘ ((hΘmem v).2 ⟨hvL, h, hvq⟩)
      have hvY : v ∈ cycArc N sY kY := by
        by_contra h
        exact hvX ((hXY v hvI).2 h)
      have := hmin u huX v hvY hup2 hvq
      rw [min_eq_left (by omega), max_eq_right (by omega)] at this
      exact this hτ2
    · exact (hXY u huI).1 huX (hin u v hτ2 hup2 (by omega) huL hvL).1
  · have hvp2 : v % 2 = sL % 2 := by
      by_contra h
      exact hvΘ ((hΘmem v).2 ⟨hvL, hvX, by omega⟩)
    by_cases huq : u % 2 = (sL + 1) % 2
    · have huX : u ∉ cycArc N sX kX := fun h => huΘ ((hΘmem u).2 ⟨huL, h, huq⟩)
      have huY : u ∈ cycArc N sY kY := by
        by_contra h
        exact huX ((hXY u huI).2 h)
      have := hmin v hvX u huY hvp2 huq
      rw [min_eq_right (by omega), max_eq_left (by omega)] at this
      exact this hτ2
    · exact (hXY v hvI).1 hvX (hin u v hτ2 (by omega) hvp2 huL hvL).2

/-- Cut dictionary, separated case: a leg of an arc of the other parity than the arc's ends is cut off by the legs of
the end parity (its two neighbours) from every non-adjacent leg outside that set. -/
theorem pkCh_cut_sep {N s k : ℕ} {G : Finset ℕ} (hE : N % 2 = 0) (hs : s ∈ Icc 1 N) (hk1 : k % 2 = 1)
    (hkN : k + 1 ≤ N) (hG : ∀ t, t ∈ G ↔ t ∈ cycArc N s k ∧ t % 2 = s % 2) (hGsub : G ⊆ Icc 1 N)
    {x w : ℕ} (hx : x ∈ cycArc N s k) (hxp : x % 2 ≠ s % 2) (hw : w ∈ Icc 1 N) (hwG : w ∉ G)
    (hd : (min x w, max x w) ∈ diagonals N) : InST G x w := by
  have hN1 : 1 ≤ N := by omega
  obtain ⟨hxI, hpx⟩ := (pkCo_mem_cycArc_pos hs (by omega)).1 hx
  have hq := pkCo_cycPos_mod_two hE hs hxI
  have h1 : 1 ≤ cycPos N s x := by omega
  have h2 : cycPos N s x + 2 ≤ k := by omega
  have hpos := pkCh_pos_of_diag hs hxI hw hd
  have hnI := mem_Icc.2 (vtx_bounds N (x + 1) hN1)
  have hpI := mem_Icc.2 (vtx_bounds N (x + (N - 1)) hN1)
  have hn := pkCh_pos_next hs hxI (by omega)
  have hp := pkCh_pos_prev hs hxI h1
  have hn2 := pkCo_vtx_mod_two hN1 hE (x + 1)
  have hp2 := pkCo_vtx_mod_two hN1 hE (x + (N - 1))
  have hnG : vtx N (x + 1) ∈ G := (hG _).2 ⟨(pkCo_mem_cycArc_pos hs (by omega)).2 ⟨hnI, by omega⟩, by omega⟩
  have hpG : vtx N (x + (N - 1)) ∈ G := (hG _).2 ⟨(pkCo_mem_cycArc_pos hs (by omega)).2 ⟨hpI, by omega⟩, by omega⟩
  have hxG : x ∉ G := fun h => hxp ((hG x).1 h).2
  rw [pkCh_inST_pos hs hGsub hxI hw]
  rcases Nat.lt_or_ge (cycPos N s x) (cycPos N s w) with hlt | hge
  · exact ⟨hxG, hwG, ⟨_, hnG, by omega⟩, ⟨_, hpG, by omega⟩⟩
  · exact ⟨hxG, hwG, ⟨_, hpG, by omega⟩, ⟨_, hnG, by omega⟩⟩

/-- Cut dictionary, unseparated case: two legs outside an arc are not separated by legs of the arc. -/
theorem pkCh_cut_nosep {N s k : ℕ} {G : Finset ℕ} (hs : s ∈ Icc 1 N) (hkN : k ≤ N) (hGL : G ⊆ cycArc N s k)
    (hGsub : G ⊆ Icc 1 N) {x w : ℕ} (hx : x ∈ Icc 1 N) (hw : w ∈ Icc 1 N) (hxL : x ∉ cycArc N s k)
    (hwL : w ∉ cycArc N s k) : ¬ InST G x w := by
  rw [pkCh_inST_pos hs hGsub hx hw]
  rintro ⟨-, -, ⟨t, ht, h1, h2⟩, -⟩
  have := ((pkCo_mem_cycArc_pos hs hkN).1 (hGL ht)).2
  have hx' : k ≤ cycPos N s x := by
    by_contra h
    exact hxL ((pkCo_mem_cycArc_pos hs hkN).2 ⟨hx, by omega⟩)
  have hw' : k ≤ cycPos N s w := by
    by_contra h
    exact hwL ((pkCo_mem_cycArc_pos hs hkN).2 ⟨hw, by omega⟩)
  omega

theorem pkCh_mem_hitSet {N : ℕ} {S : Finset (ℕ × ℕ)} {P p : ℕ × ℕ} :
    p ∈ hitSet N S P ↔ p ∈ missing N S ∧ (p ∈ oddSideSplit N P ∨ p ∈ evenSideSplit N P) := by
  show p ∈ missing N S ∩ (oddSideSplit N P ∪ evenSideSplit N P) ↔ _
  rw [mem_inter, mem_union]

theorem pkCh_mem_hitClass {N : ℕ} {S : Finset (ℕ × ℕ)} {P Q : ℕ × ℕ} :
    Q ∈ hitClass N S P ↔ Q ∈ poleChords N S ∧ hitSet N S Q = hitSet N S P := by
  show Q ∈ (poleChords N S).filter (fun Q => hitSet N S Q = hitSet N S P) ↔ _
  rw [mem_filter]

/-- Head and tail arcs of a mixed chord, and the parity legs of each. -/
theorem pkCh_arcs {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {P : ℕ × ℕ} (hP : P ∈ oddDiagonals N) :
    (∀ x, x ∈ oddSide N P ↔ x ∈ cycArc N (headStart P) (headLen N P)) ∧
    (∀ x, x ∈ evenSide N P ↔ x ∈ cycArc N (tailStart P) (tailLen N P)) ∧
    (∀ x ∈ Icc 1 N, x ∈ cycArc N (headStart P) (headLen N P) ↔ x ∉ cycArc N (tailStart P) (tailLen N P)) ∧
    (∀ t, t ∈ odds (oddSide N P) ↔ t ∈ cycArc N (headStart P) (headLen N P) ∧ t % 2 = headStart P % 2) ∧
    (∀ t, t ∈ evens (evenSide N P) ↔ t ∈ cycArc N (tailStart P) (tailLen N P) ∧ t % 2 = tailStart P % 2) ∧
    odds (oddSide N P) ⊆ Icc 1 N ∧ evens (evenSide N P) ⊆ Icc 1 N := by
  obtain ⟨-, hs2, -, -, -, -, hh2, -⟩ := pkCh_sides hE hP
  obtain ⟨eA, eB⟩ := sides_eq_cycArc hN (Nat.even_iff.2 hE) hP
  have hsub : ∀ x, x ∈ cycArc N (headStart P) (headLen N P) → x ∈ Icc 1 N := fun x h =>
    pkCo_cycArc_sub (by omega) h
  have hsubB : ∀ x, x ∈ cycArc N (tailStart P) (tailLen N P) → x ∈ Icc 1 N := fun x h =>
    pkCo_cycArc_sub (by omega) h
  have hB : ∀ x, x ∈ evenSide N P ↔ x ∈ Icc 1 N ∧ x ∉ oddSide N P := by
    intro x
    show x ∈ Icc 1 N \ oddSide N P ↔ _
    rw [mem_sdiff]
  refine ⟨fun x => by rw [eA], fun x => by rw [eB], fun x hx => ?_, fun t => ?_, fun t => ?_, ?_, ?_⟩
  · rw [← eA, ← eB, hB]
    exact ⟨fun h h' => h'.2 h, fun h => by
      by_contra h'
      exact h ⟨hx, h'⟩⟩
  · rw [pkCh_mem_odds, eA, hh2]
  · rw [pkCh_mem_evens, eB, hs2]
  · intro t ht
    rw [pkCh_mem_odds, eA] at ht
    exact hsub t ht.1
  · intro t ht
    rw [pkCh_mem_evens, eB] at ht
    exact hsubB t ht.1

/-- Cut dictionary for a missing pair `(u, v)` of one parity: it is in the hit set of `P` iff it is not inside the side
whose ends have that parity (tail for ee, head for oo) [BP App. D §0 D2; R2-Z182 C1]. -/
theorem pkCh_hit_iff {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ}
    (hP : P ∈ oddDiagonals N) {u v : ℕ} (hm : (u, v) ∈ missing N S) (huv : u % 2 = v % 2) :
    (u % 2 = 0 → ((u, v) ∈ hitSet N S P ↔ ¬ (u ∈ evenSide N P ∧ v ∈ evenSide N P))) ∧
    (u % 2 = 1 → ((u, v) ∈ hitSet N S P ↔ ¬ (u ∈ oddSide N P ∧ v ∈ oddSide N P))) := by
  obtain ⟨hts, hts2, htl1, htl3, htlN, hhs, hhs2, hhl1, hhl3, hhlN⟩ := pkCh_sides hE hP
  obtain ⟨mA, mB, mAB, mOA, mEB, sOA, sEB⟩ := pkCh_arcs (by omega) hE hP
  obtain ⟨hd, -⟩ := pkCh_mem_missing.1 hm
  have hd' := mem_diagonals.1 hd
  dsimp only at hd'
  have huI : u ∈ Icc 1 N := mem_Icc.2 ⟨by omega, by omega⟩
  have hvI : v ∈ Icc 1 N := mem_Icc.2 ⟨by omega, by omega⟩
  have hdd : (min u v, max u v) ∈ diagonals N := by
    rw [min_eq_left (by omega), max_eq_right (by omega)]
    exact hd
  have hdd' : (min v u, max v u) ∈ diagonals N := by
    rw [min_eq_right (by omega), max_eq_left (by omega)]
    exact hd
  have hlt : u < v := by omega
  have sepA : ∀ G, G ⊆ Icc 1 N → (InST G u v → (u, v) ∈ sepPairs N G) := fun G hG h =>
    (pkCo_mem_sepPairs hG).2 ⟨huI, hvI, hlt, h⟩
  have sepA' : ∀ G, G ⊆ Icc 1 N → ((u, v) ∈ sepPairs N G → InST G u v) := fun G hG h =>
    ((pkCo_mem_sepPairs hG).1 h).2.2.2
  refine ⟨fun h0 => ?_, fun h1 => ?_⟩
  · rw [pkCh_mem_hitSet]
    constructor
    · rintro ⟨-, hA | hB⟩ ⟨huB, hvB⟩
      · refine pkCh_cut_nosep (G := odds (oddSide N P)) (by exact hhs) (by omega) (fun t ht => ((mOA t).1 ht).1)
          sOA huI hvI (fun h => ?_) (fun h => ?_) (sepA' _ sOA hA)
        · exact (mAB u huI).1 h ((mB u).1 huB)
        · exact (mAB v hvI).1 h ((mB v).1 hvB)
      · exact ((sepA' _ sEB hB).1) (pkCh_mem_evens.2 ⟨huB, h0⟩)
    · intro hn
      refine ⟨hm, Or.inl (sepA _ sOA ?_)⟩
      by_cases huB : u ∈ evenSide N P
      · have hvB : v ∉ evenSide N P := fun h => hn ⟨huB, h⟩
        have hvA : v ∈ cycArc N (headStart P) (headLen N P) := by
          by_contra h
          exact hvB ((mB v).2 (by by_contra h'; exact h ((mAB v hvI).2 h')))
        exact pkCo_inST_comm.1 (pkCh_cut_sep hE hhs hhl1 (by omega) mOA sOA hvA (by omega) huI
          (fun h => by have := ((mOA u).1 h).2; omega) hdd')
      · have huA : u ∈ cycArc N (headStart P) (headLen N P) := by
          by_contra h
          exact huB ((mB u).2 (by by_contra h'; exact h ((mAB u huI).2 h')))
        exact pkCh_cut_sep hE hhs hhl1 (by omega) mOA sOA huA (by omega) hvI
          (fun h => by have := ((mOA v).1 h).2; omega) hdd
  · rw [pkCh_mem_hitSet]
    constructor
    · rintro ⟨-, hA | hB⟩ ⟨huA, hvA⟩
      · exact ((sepA' _ sOA hA).1) (pkCh_mem_odds.2 ⟨huA, h1⟩)
      · refine pkCh_cut_nosep (G := evens (evenSide N P)) (by exact hts) (by omega) (fun t ht => ((mEB t).1 ht).1)
          sEB huI hvI (fun h => ?_) (fun h => ?_) (sepA' _ sEB hB)
        · exact (mAB u huI).1 ((mA u).1 huA) h
        · exact (mAB v hvI).1 ((mA v).1 hvA) h
    · intro hn
      refine ⟨hm, Or.inr (sepA _ sEB ?_)⟩
      by_cases huA : u ∈ oddSide N P
      · have hvA : v ∉ oddSide N P := fun h => hn ⟨huA, h⟩
        have hvB : v ∈ cycArc N (tailStart P) (tailLen N P) := by
          by_contra h
          exact hvA ((mA v).2 ((mAB v hvI).2 h))
        exact pkCo_inST_comm.1 (pkCh_cut_sep hE hts htl1 (by omega) mEB sEB hvB (by omega) huI
          (fun h => by have := ((mEB u).1 h).2; omega) hdd')
      · have huB : u ∈ cycArc N (tailStart P) (tailLen N P) := by
          by_contra h
          exact huA ((mA u).2 ((mAB u huI).2 h))
        exact pkCh_cut_sep hE hts htl1 (by omega) mEB sEB huB (by omega) hvI
          (fun h => by have := ((mEB v).1 h).2; omega) hdd

/-- [Int](a): every class member's head lies in the head of a `𝒮_B` chord (Lemma 5′, main form). -/
theorem pkCh_int_top {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} {P Q : ℕ × ℕ}
    (hP : P ∈ poleChords N S) (hPB : NoFreeSep N S (tailStart P) (tailLen N P) 1) (hQ : Q ∈ poleChords N S)
    (hh : hitSet N S Q = hitSet N S P) : oddSide N Q ⊆ oddSide N P := by
  obtain ⟨hPo, -, -, ⟨⟨f1, f2⟩, hf⟩⟩ := pkCh_mem_pole.1 hP
  obtain ⟨hQo, hQr, -, -⟩ := pkCh_mem_pole.1 hQ
  obtain ⟨hts, hts2, htl1, htl3, htlN, hhs, hhs2, hhl1, hhl3, hhlN⟩ := pkCh_sides hE hPo
  obtain ⟨qts, qts2, qtl1, qtl3, qtlN, qhs, qhs2, qhl1, qhl3, qhlN⟩ := pkCh_sides hE hQo
  obtain ⟨mA, mB, mAB, -, -, -, -⟩ := pkCh_arcs (by omega) hE hPo
  obtain ⟨qA, qB, qAB, -, -, -, -⟩ := pkCh_arcs (by omega) hE hQo
  obtain ⟨hfM, hf1, hf2⟩ := pkCh_mem_innerOO.1 hf
  obtain ⟨hfm, hfp1, hfp2⟩ := pkCh_mem_Moo.1 hfM
  dsimp only at hf1 hf2 hfp1 hfp2
  have hfnP := mt ((pkCh_hit_iff hN hE hPo hfm (by omega)).2 hfp1).1 (fun h => h ⟨hf1, hf2⟩)
  rw [← hh] at hfnP
  have hfQ : f1 ∈ oddSide N Q ∧ f2 ∈ oddSide N Q := by
    by_contra h
    exact hfnP (((pkCh_hit_iff hN hE hQo hfm (by omega)).2 hfp1).2 h)
  have hfI : f1 ∈ Icc 1 N := pkCo_cycArc_sub (by omega) ((mA f1).1 hf1)
  have key := pkCh_lem5 (S := S) hE hts htl1 htl3 htlN qhs (by omega) qhl1 (by omega) qts (by omega) qAB
    (by rw [show (tailStart P + 1) % 2 = 1 by omega]; exact hPB)
    (fun e he y hy he2 hy2 => fun hm => disjoint_left.1 hQr (pkCh_mem_minRect.2 ⟨e,
      pkCh_mem_evens.2 ⟨(qA e).2 he, by omega⟩, y, pkCh_mem_odds.2 ⟨(qB y).2 hy, by omega⟩, rfl⟩) hm)
    (fun u v hm hu hv huL hvL => by
      have hn := mt ((pkCh_hit_iff hN hE hPo hm (by omega)).1 (by omega)).1 (fun h => h ⟨(mB u).2 huL, (mB v).2 hvL⟩)
      rw [← hh] at hn
      have hQB : u ∈ evenSide N Q ∧ v ∈ evenSide N Q := by
        by_contra h
        exact hn (((pkCh_hit_iff hN hE hQo hm (by omega)).1 (by omega)).2 h)
      exact ⟨(qB u).1 hQB.1, (qB v).1 hQB.2⟩)
    hfI (fun h => (mAB f1 hfI).1 ((mA f1).1 hf1) h) ((qA f1).1 hfQ.1)
  intro x hx
  have hxI : x ∈ Icc 1 N := pkCo_cycArc_sub (by omega) ((qA x).1 hx)
  have hxB := key x ((qA x).1 hx)
  exact (mA x).2 ((mAB x hxI).2 hxB)

/-- [Int](b): a class member with `Sep_all` on its head has its head inside every class member's head (Lemma 5′,
mirror form, from the same generic lemma with the sides exchanged). -/
theorem pkCh_int_bot {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} {b Q : ℕ × ℕ}
    (hb : b ∈ poleChords N S) (hbA : NoFreeSep N S (headStart b) (headLen N b) 0) (hQ : Q ∈ poleChords N S)
    (hh : hitSet N S Q = hitSet N S b) : oddSide N b ⊆ oddSide N Q := by
  obtain ⟨hbo, -, ⟨⟨g1, g2⟩, hg⟩, -⟩ := pkCh_mem_pole.1 hb
  obtain ⟨hQo, hQr, -, -⟩ := pkCh_mem_pole.1 hQ
  obtain ⟨hts, hts2, htl1, htl3, htlN, hhs, hhs2, hhl1, hhl3, hhlN⟩ := pkCh_sides hE hbo
  obtain ⟨qts, qts2, qtl1, qtl3, qtlN, qhs, qhs2, qhl1, qhl3, qhlN⟩ := pkCh_sides hE hQo
  obtain ⟨mA, mB, mAB, -, -, -, -⟩ := pkCh_arcs (by omega) hE hbo
  obtain ⟨qA, qB, qAB, -, -, -, -⟩ := pkCh_arcs (by omega) hE hQo
  have qBA : ∀ x ∈ Icc 1 N, x ∈ cycArc N (tailStart Q) (tailLen N Q) ↔
      x ∉ cycArc N (headStart Q) (headLen N Q) := fun x hx => by
    rw [qAB x hx]
    exact ⟨fun h h' => h' h, fun h => by by_contra h'; exact h h'⟩
  obtain ⟨hgM, hg1, hg2⟩ := pkCh_mem_innerEE.1 hg
  obtain ⟨hgm, hgp1, hgp2⟩ := pkCh_mem_Mee.1 hgM
  dsimp only at hg1 hg2 hgp1 hgp2
  have hgnb := mt ((pkCh_hit_iff hN hE hbo hgm (by omega)).1 hgp1).1 (fun h => h ⟨hg1, hg2⟩)
  rw [← hh] at hgnb
  have hgQ : g1 ∈ evenSide N Q ∧ g2 ∈ evenSide N Q := by
    by_contra h
    exact hgnb (((pkCh_hit_iff hN hE hQo hgm (by omega)).1 hgp1).2 h)
  have hgI : g1 ∈ Icc 1 N := pkCo_cycArc_sub (by omega) ((mB g1).1 hg1)
  have key := pkCh_lem5 (S := S) hE hhs hhl1 hhl3 hhlN qts (by omega) qtl1 (by omega) qhs (by omega) qBA
    (by rw [show (headStart b + 1) % 2 = 0 by omega]; exact hbA)
    (fun e he y hy he2 hy2 => by
      rw [min_comm, max_comm]
      exact fun hm => disjoint_left.1 hQr (pkCh_mem_minRect.2 ⟨y,
        pkCh_mem_evens.2 ⟨(qA y).2 hy, by omega⟩, e, pkCh_mem_odds.2 ⟨(qB e).2 he, by omega⟩, rfl⟩) hm)
    (fun u v hm hu hv huL hvL => by
      have hn := mt ((pkCh_hit_iff hN hE hbo hm (by omega)).2 (by omega)).1 (fun h => h ⟨(mA u).2 huL, (mA v).2 hvL⟩)
      rw [← hh] at hn
      have hQA : u ∈ oddSide N Q ∧ v ∈ oddSide N Q := by
        by_contra h
        exact hn (((pkCh_hit_iff hN hE hQo hm (by omega)).2 (by omega)).2 h)
      exact ⟨(qA u).1 hQA.1, (qA v).1 hQA.2⟩)
    hgI (fun h => (mAB g1 hgI).1 h ((mB g1).1 hg1)) ((qB g1).1 hgQ.1)
  intro z hz
  have hzA := (mA z).1 hz
  have hzI : z ∈ Icc 1 N := pkCo_cycArc_sub (by omega) hzA
  by_contra hzQ
  have hzB : z ∈ cycArc N (tailStart Q) (tailLen N Q) := by
    by_contra h
    exact hzQ ((qA z).2 (by by_contra h'; exact h ((qBA z hzI).2 h')))
  exact key z hzB hzA

/-- `sorry` (pkgChain) · **[Can]** (Lemma X_all) [v3 §14.2 route step 3; BP App. C §C-3]: if `𝒫₁ ≠ ∅` a canonical chord
exists. (BP: holds for every `S`; frozen with v3's F^π.) -/
theorem can_exists {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {S : Finset (ℕ × ℕ)} (hF : InFpi N S)
    (hP : (poleChords N S).Nonempty) : ∃ P, IsMinimalChord N S P := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  obtain ⟨P0, hP0, hmin⟩ := exists_min_image (poleChords N S) (fun P => tailLen N P) hP
  have hG : P0 ∈ goodTail N S := by
    refine pkCh_mem_goodTail.2 ⟨hP0, ?_⟩
    by_contra hc
    obtain ⟨Q, hQ, hlt⟩ := pkCh_Xall_B hN hE' hP0 hc
    have := hmin Q hQ
    omega
  obtain ⟨P1, hP1, hmin1⟩ := exists_min_image (goodTail N S) (fun P => (oddSide N P).card) ⟨P0, hG⟩
  refine ⟨P1, pkCh_minChord_iff.2 ⟨hP1, fun Q hQ hss => ?_⟩⟩
  have h1 := hmin1 Q hQ
  have h2 := card_lt_card hss
  omega

/-! ### Sub-wave b: [D] Lemma 14.5 through a linear core (labels `1..N`, head `[1, ω]`) -/

theorem pkCh_isRun_iff {ω : ℕ} {Θ : Finset ℕ} {a b : ℕ} :
    IsRun ω Θ a b ↔ 1 ≤ a ∧ a ≤ b ∧ b ≤ ω ∧ (a = 1 ∨ a - 1 ∈ Θ) ∧ (b = ω ∨ b + 1 ∈ Θ) ∧ ∀ w ∈ Icc a b, w ∉ Θ :=
  Iff.rfl

theorem pkCh_asc_iff {N a b : ℕ} {τ : Finset ℕ} :
    AdmSepCompl N a b τ ↔ (∃ t ∈ intCompl N a b, τ = {t}) ∨
      (2 ≤ τ.card ∧ τ ⊆ intCompl N a b ∧ ∀ t ∈ τ, t % 2 = 1) := Iff.rfl

theorem pkCh_ta_iff {N ω : ℕ} {τ : Finset ℕ} :
    TailAvoiding N ω τ ↔ Disjoint τ (Icc (ω + 2) (N - 1)) ∧ ((∀ t ∈ τ, t % 2 = 1) → Disjoint τ (Icc (ω + 1) N)) :=
  Iff.rfl

theorem pkCh_tss_iff {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} :
    ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ ↔ N % 2 = 0 ∧ ω % 2 = 1 ∧ ω + 3 ≤ N ∧ Θ.Nonempty ∧ Θ ⊆ Icc 2 (ω - 1) ∧
      (∀ θ ∈ Θ, θ % 2 = 0) ∧ IsRun ω Θ x0 x1 ∧ IsRun ω Θ y0 y1 ∧ x1 < y0 ∧ x0 + 2 ≤ x1 ∧ y0 + 2 ≤ y1 ∧
      AdmSepCompl N x0 x1 τ ∧ AdmSepCompl N y0 y1 σ ∧ TailAvoiding N ω τ ∧ TailAvoiding N ω σ ∧
      (y0 ∈ τ ∨ InST (Icc x0 x1 ∪ τ) y0 (ω + 2)) ∧ (x1 ∈ σ ∨ InST (Icc y0 y1 ∪ σ) x1 (ω + 2)) := Iff.rfl

theorem pkCh_mem_intCompl {N a b x : ℕ} :
    x ∈ intCompl N a b ↔ (1 ≤ x ∧ x ≤ N) ∧ ¬ (a ≤ x ∧ x ≤ b) ∧ x ≠ b + 1 ∧
      x ≠ (if a = 1 then N else a - 1) := by
  show x ∈ Icc 1 N \ (Icc a b ∪ {b + 1, prevLeg N a}) ↔ _
  have e : prevLeg N a = if a = 1 then N else a - 1 := rfl
  rw [mem_sdiff, mem_union, mem_insert, mem_singleton, mem_Icc, mem_Icc, e]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h => h2 (Or.inl h), fun h => h2 (Or.inr (Or.inl h)), fun h => h2 (Or.inr (Or.inr h))⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, ?_⟩
    rintro (h | h | h)
    · exact h2 h
    · exact h3 h
    · exact h4 h

/-- An admissible trace of a complement: its legs lie in `intCompl`, and an even leg makes it a singleton. -/
theorem pkCh_asc_facts {N a b : ℕ} {τ : Finset ℕ} (h : AdmSepCompl N a b τ) :
    τ.Nonempty ∧ τ ⊆ intCompl N a b ∧ ∀ t ∈ τ, t % 2 = 0 → τ = {t} := by
  rcases pkCh_asc_iff.1 h with ⟨t, ht, rfl⟩ | ⟨hc, hs, ho⟩
  · refine ⟨⟨t, mem_singleton_self t⟩, singleton_subset_iff.2 ht, fun t' ht' _ => ?_⟩
    rw [mem_singleton.1 ht']
  · refine ⟨card_pos.1 (by omega), hs, fun t ht he => ?_⟩
    have := ho t ht
    omega

/-- Transitivity of "same piece" through a reference leg `R`. -/
theorem pkCh_inST_trans {T : Finset ℕ} {w z R : ℕ} (h1 : InST T w R) (hz : z ∉ T) (h2 : ¬ InST T z R) :
    InST T w z := by
  rw [pkCo_inST_iff] at h1 h2 ⊢
  obtain ⟨hw, hR, ⟨g1, hg1, a1⟩, ⟨g2, hg2, a2⟩⟩ := h1
  have e1 : g1 ≠ z := fun e => hz (e ▸ hg1)
  have e2 : g2 ≠ z := fun e => hz (e ▸ hg2)
  have f1 : g1 ≠ R := fun e => hR (e ▸ hg1)
  have f2 : g2 ≠ R := fun e => hR (e ▸ hg2)
  have d1 : g1 ≠ w := fun e => hw (e ▸ hg1)
  have d2 : g2 ≠ w := fun e => hw (e ▸ hg2)
  refine ⟨hw, hz, ?_, ?_⟩
  · by_cases hb : ∃ t ∈ T, min z R < t ∧ t < max z R
    · have n1 : ¬ (g1 < min z R ∨ max z R < g1) := fun h => h2 ⟨hz, hR, hb, ⟨g1, hg1, h⟩⟩
      have n2 : ¬ (g2 < min z R ∨ max z R < g2) := fun h => h2 ⟨hz, hR, hb, ⟨g2, hg2, h⟩⟩
      by_cases c : min w z < g1 ∧ g1 < max w z
      · exact ⟨g1, hg1, c⟩
      · exact ⟨g2, hg2, by omega⟩
    · have n1 : ¬ (min z R < g1 ∧ g1 < max z R) := fun h => hb ⟨g1, hg1, h⟩
      have n2 : ¬ (min z R < g2 ∧ g2 < max z R) := fun h => hb ⟨g2, hg2, h⟩
      by_cases c : min w z < g1 ∧ g1 < max w z
      · exact ⟨g1, hg1, c⟩
      · exact ⟨g2, hg2, by omega⟩
  · by_cases hb : ∃ t ∈ T, min z R < t ∧ t < max z R
    · have n1 : ¬ (g1 < min z R ∨ max z R < g1) := fun h => h2 ⟨hz, hR, hb, ⟨g1, hg1, h⟩⟩
      have n2 : ¬ (g2 < min z R ∨ max z R < g2) := fun h => h2 ⟨hz, hR, hb, ⟨g2, hg2, h⟩⟩
      by_cases c : g1 < min w z ∨ max w z < g1
      · exact ⟨g1, hg1, c⟩
      · exact ⟨g2, hg2, by omega⟩
    · have n1 : ¬ (min z R < g1 ∧ g1 < max z R) := fun h => hb ⟨g1, hg1, h⟩
      have n2 : ¬ (min z R < g2 ∧ g2 < max z R) := fun h => hb ⟨g2, hg2, h⟩
      by_cases c : g1 < min w z ∨ max w z < g1
      · exact ⟨g1, hg1, c⟩
      · exact ⟨g2, hg2, by omega⟩

/-- The run of `A′ ∖ Θ` (`A′ = [1, ω]`) through a leg `u ∉ Θ`. -/
theorem pkCh_runOf {ω u : ℕ} {Θ : Finset ℕ} (hΘ : Θ ⊆ Icc 2 (ω - 1)) (hu : u ∈ Icc 1 ω) (huΘ : u ∉ Θ) :
    ∃ a b, IsRun ω Θ a b ∧ a ≤ u ∧ u ≤ b := by
  rw [mem_Icc] at hu
  obtain ⟨a, ha1, hau, haΘ, hA⟩ : ∃ a, 1 ≤ a ∧ a ≤ u ∧ (a = 1 ∨ a - 1 ∈ Θ) ∧ ∀ θ ∈ Θ, θ < u → θ < a := by
    by_cases hL : (Θ.filter (fun x => x < u)).Nonempty
    · have hm := mem_filter.1 ((Θ.filter (fun x => x < u)).max'_mem hL)
      refine ⟨(Θ.filter (fun x => x < u)).max' hL + 1, by omega, by omega, Or.inr ?_, fun θ hθ hθu => ?_⟩
      · rw [Nat.add_sub_cancel]; exact hm.1
      · have := (Θ.filter (fun x => x < u)).le_max' θ (mem_filter.2 ⟨hθ, hθu⟩); omega
    · refine ⟨1, le_refl _, hu.1, Or.inl rfl, fun θ hθ hθu => ?_⟩
      exact absurd ⟨θ, mem_filter.2 ⟨hθ, hθu⟩⟩ hL
  obtain ⟨b, hbω, hub, hbΘ, hB⟩ : ∃ b, b ≤ ω ∧ u ≤ b ∧ (b = ω ∨ b + 1 ∈ Θ) ∧ ∀ θ ∈ Θ, u < θ → b < θ := by
    by_cases hR : (Θ.filter (fun x => u < x)).Nonempty
    · have hm := mem_filter.1 ((Θ.filter (fun x => u < x)).min'_mem hR)
      have hmI := mem_Icc.1 (hΘ hm.1)
      refine ⟨(Θ.filter (fun x => u < x)).min' hR - 1, by omega, by omega, Or.inr ?_, fun θ hθ hθu => ?_⟩
      · rw [Nat.sub_add_cancel (by omega)]; exact hm.1
      · have := (Θ.filter (fun x => u < x)).min'_le θ (mem_filter.2 ⟨hθ, hθu⟩); omega
    · refine ⟨ω, le_refl _, hu.2, Or.inl rfl, fun θ hθ hθu => ?_⟩
      exact absurd ⟨θ, mem_filter.2 ⟨hθ, hθu⟩⟩ hR
  refine ⟨a, b, pkCh_isRun_iff.2 ⟨ha1, by omega, hbω, haΘ, hbΘ, fun w hw hwΘ => ?_⟩, hau, hub⟩
  rw [mem_Icc] at hw
  rcases lt_trichotomy w u with h | h | h
  · have := hA w hwΘ h; omega
  · exact huΘ (h ▸ hwΘ)
  · have := hB w hwΘ h; omega

/-- A clean-pair predicate read through `min`/`max`. -/
theorem pkCh_C_minmax {C : ℕ → ℕ → Prop} (hC : ∀ u v, C u v → C v u) {u v : ℕ} (h : C (min u v) (max u v)) :
    C u v := by
  rcases le_total u v with huv | huv
  · rw [min_eq_left huv, max_eq_right huv] at h; exact h
  · rw [min_eq_right huv, max_eq_left huv] at h; exact hC _ _ h

/-- **[b0]** in the linear setting (BP App. D §2): a failing admissible trace of `C_N ∖ [a, b]` (`[a, b] ⊆ A′`) is
(b0)-shaped, given `Sep_all(W)` for the tail `W = [ω+1, N]`. -/
theorem pkCh_b0 {N ω a b : ℕ} {τ : Finset ℕ} {C : ℕ → ℕ → Prop} (hN : N % 2 = 0) (hω : ω % 2 = 1)
    (hωN : ω + 3 ≤ N) (hab : a ≤ b) (hbω : b ≤ ω)
    (HW : ∀ τ0 : Finset ℕ, τ0.Nonempty → τ0 ⊆ Icc (ω + 2) (N - 1) → (τ0.card = 1 ∨ ∀ t ∈ τ0, t % 2 = 1) →
      ∃ u v, u ∈ Icc (ω + 1) N ∧ v ∈ Icc (ω + 1) N ∧ u ∉ τ0 ∧ v ∉ τ0 ∧
        (∃ t ∈ τ0, min u v < t ∧ t < max u v) ∧ ¬ C u v)
    (hτ : AdmSepCompl N a b τ) (hf : ∀ u v, InST (Icc a b ∪ τ) u v → C u v) : TailAvoiding N ω τ := by
  obtain ⟨-, -, hev⟩ := pkCh_asc_facts hτ
  have part1 : Disjoint τ (Icc (ω + 2) (N - 1)) := by
    by_contra hnd
    obtain ⟨t0, ht0τ, ht0I⟩ := not_disjoint_iff.1 hnd
    have hne : (τ.filter (fun t => ω + 2 ≤ t ∧ t ≤ N - 1)).Nonempty := ⟨t0, mem_filter.2 ⟨ht0τ, mem_Icc.1 ht0I⟩⟩
    have hsub : τ.filter (fun t => ω + 2 ≤ t ∧ t ≤ N - 1) ⊆ Icc (ω + 2) (N - 1) := fun t ht =>
      mem_Icc.2 (mem_filter.1 ht).2
    have hadm : (τ.filter (fun t => ω + 2 ≤ t ∧ t ≤ N - 1)).card = 1 ∨
        ∀ t ∈ τ.filter (fun t => ω + 2 ≤ t ∧ t ≤ N - 1), t % 2 = 1 := by
      by_cases ho : ∀ t ∈ τ, t % 2 = 1
      · exact Or.inr fun t ht => ho t (mem_filter.1 ht).1
      · left
        obtain ⟨t1, ht1, ht1e⟩ : ∃ t1 ∈ τ, ¬ t1 % 2 = 1 := by
          by_contra hc
          apply ho
          intro t ht
          by_contra h
          exact hc ⟨t, ht, h⟩
        have e := hev t1 ht1 (by omega)
        have : τ.filter (fun t => ω + 2 ≤ t ∧ t ≤ N - 1) = {t1} := by
          apply (hne.subset_singleton_iff).1
          rw [← e]; exact filter_subset _ _
        rw [this, card_singleton]
    obtain ⟨u, v, hu, hv, hu0, hv0, ⟨t, ht, hb1, hb2⟩, hc⟩ := HW _ hne hsub hadm
    have htτ := (mem_filter.1 ht).1
    have hnot : ∀ x ∈ Icc (ω + 1) N, x ∉ τ.filter (fun t => ω + 2 ≤ t ∧ t ≤ N - 1) → x ∉ Icc a b ∪ τ := by
      intro x hx hx0 hxT
      rw [mem_Icc] at hx
      rcases mem_union.1 hxT with h | h
      · have := mem_Icc.1 h; omega
      · have hx' : ¬ (ω + 2 ≤ x ∧ x ≤ N - 1) := fun h' => hx0 (mem_filter.2 ⟨h, h'⟩)
        have hxe : x % 2 = 0 := by omega
        have e := hev x h hxe
        rw [e] at htτ
        rw [mem_singleton.1 htτ] at ht
        exact hx0 ht
    apply hc
    apply hf
    rw [pkCo_inST_iff]
    refine ⟨hnot u hu hu0, hnot v hv hv0, ⟨t, mem_union_right _ htτ, hb1, hb2⟩,
      ⟨a, mem_union_left _ (mem_Icc.2 ⟨le_refl _, hab⟩), ?_⟩⟩
    rw [mem_Icc] at hu hv
    omega
  refine pkCh_ta_iff.2 ⟨part1, fun ho => disjoint_left.2 fun t ht htI => ?_⟩
  have h1 := ho t ht
  have h2 : t ∉ Icc (ω + 2) (N - 1) := disjoint_left.1 part1 ht
  rw [mem_Icc] at htI h2
  omega

/-- [St1] key step (BP App. D §8 (4)), linear: `w ∈ H(τ)` (separated from `R` by `Z ∪ τ`), a leg `θ′` of `R_τ` (or the
adjoined even singleton trace) strictly between `w` and `z` inside `A′ = [1, ω]` ⇒ `w`, `z` are in different pieces. -/
theorem pkCh_st1_key {ω R z0 z1 w z θ' : ℕ} {τ : Finset ℕ} (hRω : ω < R) (hz1 : z1 ≤ ω)
    (hτe : ∀ t ∈ τ, t % 2 = 0 → τ = {t}) (hθ'e : θ' % 2 = 0) (hθ'Z : θ' ∉ Icc z0 z1) (hθ'ω : θ' ≤ ω)
    (hzω : z ≤ ω) (hwω : w ≤ ω) (hw : InST (Icc z0 z1 ∪ τ) w R) (hθ' : ¬ InST (Icc z0 z1 ∪ τ) θ' R)
    (hb : min w z < θ' ∧ θ' < max w z) : InST (Icc z0 z1 ∪ τ) w z := by
  have hw' := hw
  rw [pkCo_inST_iff] at hw'
  obtain ⟨hwT, hRT, ⟨g1, hg1, a1⟩, ⟨g2, hg2, a2⟩⟩ := hw'
  have hmem : ∀ t, t ∈ Icc z0 z1 ∪ τ ↔ (z0 ≤ t ∧ t ≤ z1) ∨ t ∈ τ := fun t => by rw [mem_union, mem_Icc]
  have hθ'Z' : ¬ (z0 ≤ θ' ∧ θ' ≤ z1) := fun h => hθ'Z (mem_Icc.2 h)
  by_cases hθτ : θ' ∈ τ
  · have e := hτe θ' hθτ hθ'e
    have hT : ∀ t, t ∈ Icc z0 z1 ∪ τ ↔ (z0 ≤ t ∧ t ≤ z1) ∨ t = θ' := fun t => by rw [hmem, e, mem_singleton]
    have hwZ : ¬ (z0 ≤ w ∧ w ≤ z1) ∧ w ≠ θ' := by
      rw [hT] at hwT
      exact ⟨fun h => hwT (Or.inl h), fun h => hwT (Or.inr h)⟩
    have c1 := (hT g1).1 hg1
    have c2 := (hT g2).1 hg2
    refine pkCh_inST_trans hw ?_ ?_
    · rw [hT]
      rintro (h | h) <;> omega
    · rw [pkCo_inST_iff]
      rintro ⟨-, -, ⟨g, hg, bg⟩, ⟨g', hg', bg'⟩⟩
      have c3 := (hT g).1 hg
      have c4 := (hT g').1 hg'
      omega
  · have hθT : θ' ∉ Icc z0 z1 ∪ τ := by
      rw [hmem]
      rintro (h | h)
      · exact hθ'Z' h
      · exact hθτ h
    have hθ2 : ¬ ((∃ t ∈ Icc z0 z1 ∪ τ, min θ' R < t ∧ t < max θ' R) ∧
        ∃ t ∈ Icc z0 z1 ∪ τ, t < min θ' R ∨ max θ' R < t) := fun h => hθ' ⟨hθT, hRT, h.1, h.2⟩
    have hg1θ : g1 ≠ θ' := fun e => hθT (e ▸ hg1)
    have hg2θ : g2 ≠ θ' := fun e => hθT (e ▸ hg2)
    by_cases hbt : ∃ t ∈ Icc z0 z1 ∪ τ, min θ' R < t ∧ t < max θ' R
    · have hno : ∀ t ∈ Icc z0 z1 ∪ τ, ¬ (t < min θ' R ∨ max θ' R < t) := fun t ht h => hθ2 ⟨hbt, ⟨t, ht, h⟩⟩
      have n2 := hno g2 hg2
      have hz : z < θ' := by omega
      refine pkCh_inST_trans hw ?_ ?_
      · intro hzT
        have := hno z hzT
        omega
      · rw [pkCo_inST_iff]
        rintro ⟨-, -, -, ⟨g', hg', bg'⟩⟩
        have := hno g' hg'
        omega
    · have hno : ∀ t ∈ Icc z0 z1 ∪ τ, ¬ (min θ' R < t ∧ t < max θ' R) := fun t ht h => hbt ⟨t, ht, h⟩
      have n1 := hno g1 hg1
      have hz : θ' < z := by omega
      refine pkCh_inST_trans hw ?_ ?_
      · intro hzT
        have := hno z hzT
        omega
      · rw [pkCo_inST_iff]
        rintro ⟨-, -, ⟨g', hg', bg'⟩, -⟩
        have := hno g' hg'
        omega

/-- **[St1] (4)**, linear: `Θ′ := Θ ∖ H(τ)` is failing. -/
theorem pkCh_st1_fail {ω R z0 z1 : ℕ} {Θ τ : Finset ℕ} {C : ℕ → ℕ → Prop} (hC : ∀ u v, C u v → C v u)
    (hRω : ω < R) (hz1 : z1 ≤ ω) (hτe : ∀ t ∈ τ, t % 2 = 0 → τ = {t}) (hΘe : ∀ θ ∈ Θ, θ % 2 = 0)
    (hZΘ : ∀ θ ∈ Θ, θ ∉ Icc z0 z1) (hΘω : ∀ θ ∈ Θ, θ ≤ ω)
    (hΘf : ∀ u v, runSepA ω Θ u v → C u v) (hτf : ∀ u v, InST (Icc z0 z1 ∪ τ) u v → C u v) :
    ∀ u v, runSepA ω (Θ.filter (fun θ => ¬ InST (Icc z0 z1 ∪ τ) θ R)) u v → C u v := by
  intro u v h
  obtain ⟨hu, hv, huΘ', hvΘ', θ', hθ', b1, b2⟩ := pkT_runSepA_iff.1 h
  obtain ⟨hθΘ, hθn⟩ := mem_filter.1 hθ'
  have hu' := mem_Icc.1 hu
  have hv' := mem_Icc.1 hv
  by_cases huΘ : u ∈ Θ
  · have hwu : InST (Icc z0 z1 ∪ τ) u R := by
      by_contra hc
      exact huΘ' (mem_filter.2 ⟨huΘ, hc⟩)
    exact hτf u v (pkCh_st1_key hRω hz1 hτe (hΘe θ' hθΘ) (hZΘ θ' hθΘ) (hΘω θ' hθΘ) hv'.2 hu'.2 hwu hθn ⟨b1, b2⟩)
  · by_cases hvΘ : v ∈ Θ
    · have hwv : InST (Icc z0 z1 ∪ τ) v R := by
        by_contra hc
        exact hvΘ' (mem_filter.2 ⟨hvΘ, hc⟩)
      rw [min_comm] at b1
      rw [max_comm] at b2
      exact hC _ _ (hτf v u (pkCh_st1_key hRω hz1 hτe (hΘe θ' hθΘ) (hZΘ θ' hθΘ) (hΘω θ' hθΘ) hu'.2 hv'.2 hwv hθn
        ⟨b1, b2⟩))
    · exact hΘf u v (pkT_runSepA_iff.2 ⟨hu, hv, huΘ, hvΘ, θ', hθΘ, b1, b2⟩)

/-- **[St1] (1)–(3)** for `X` (before `Y`), linear: a short failing trace `τ` of `B_X` gives `Θ′ ⊊ Θ` keeping `y₀ − 1`. -/
theorem pkCh_st1X {N ω x0 x1 y0 : ℕ} {Θ τ : Finset ℕ} (hωN : ω + 3 ≤ N) (hΘ : Θ ⊆ Icc 2 (ω - 1))
    (hX : IsRun ω Θ x0 x1) (hy : y0 - 1 ∈ Θ) (hxy : x1 < y0) (hy0ω : y0 ≤ ω) (hτ : AdmSepCompl N x0 x1 τ)
    (hTA : TailAvoiding N ω τ) (hs : ¬ (y0 ∈ τ ∨ InST (Icc x0 x1 ∪ τ) y0 (ω + 2))) :
    (Θ.filter (fun θ => ¬ InST (Icc x0 x1 ∪ τ) θ (ω + 2))).card < Θ.card ∧
      y0 - 1 ∈ Θ.filter (fun θ => ¬ InST (Icc x0 x1 ∪ τ) θ (ω + 2)) := by
  obtain ⟨hx0, hx01, hx1ω, hxa, hxb, -⟩ := pkCh_isRun_iff.1 hX
  obtain ⟨⟨t, ht⟩, hτI, -⟩ := pkCh_asc_facts hτ
  obtain ⟨hTA1, -⟩ := pkCh_ta_iff.1 hTA
  have hmem : ∀ g, g ∈ Icc x0 x1 ∪ τ ↔ (x0 ≤ g ∧ g ≤ x1) ∨ g ∈ τ := fun g => by rw [mem_union, mem_Icc]
  have hτW : ∀ g ∈ τ, ¬ (ω + 2 ≤ g ∧ g ≤ N - 1) := fun g hg h => disjoint_left.1 hTA1 hg (mem_Icc.2 h)
  have hy0τ : y0 ∉ τ := fun h => hs (Or.inl h)
  have hωT : ω + 2 ∉ Icc x0 x1 ∪ τ := by
    rw [hmem]
    rintro (h | h)
    · omega
    · exact hτW _ h ⟨le_refl _, by omega⟩
  have hy0T : y0 ∉ Icc x0 x1 ∪ τ := by
    rw [hmem]
    rintro (h | h)
    · omega
    · exact hy0τ h
  have hno : ∀ g ∈ Icc x0 x1 ∪ τ, ¬ (y0 < g ∧ g < ω + 2) := by
    intro g hg hgb
    apply hs
    right
    rw [pkCo_inST_iff]
    refine ⟨hy0T, hωT, ⟨g, hg, by omega⟩, ⟨x0, (hmem x0).2 (Or.inl ⟨le_refl _, hx01⟩), by omega⟩⟩
  have htI := pkCh_mem_intCompl.1 (hτI ht)
  have hΘy := mem_Icc.1 (hΘ hy)
  refine ⟨card_lt_card (filter_ssubset.2 ?_), mem_filter.2 ⟨hy, ?_⟩⟩
  · by_cases h1 : x1 + 1 < t ∧ t < ω + 2
    · have hx1Θ : x1 + 1 ∈ Θ := by
        rcases hxb with h | h
        · omega
        · exact h
      refine ⟨x1 + 1, hx1Θ, not_not.2 ?_⟩
      rw [pkCo_inST_iff]
      refine ⟨?_, hωT, ⟨t, mem_union_right _ ht, by omega⟩, ⟨x0, (hmem x0).2 (Or.inl ⟨le_refl _, hx01⟩), by omega⟩⟩
      rw [hmem]
      rintro (h | h)
      · omega
      · exact (pkCh_mem_intCompl.1 (hτI h)).2.2.1 rfl
    · have htN := hτW t ht
      have hx0' : x0 ≠ 1 := by
        intro e
        rw [if_pos e] at htI
        omega
      have hx0Θ : x0 - 1 ∈ Θ := by
        rcases hxa with h | h
        · exact absurd h hx0'
        · exact h
      rw [if_neg hx0'] at htI
      refine ⟨x0 - 1, hx0Θ, not_not.2 ?_⟩
      rw [pkCo_inST_iff]
      refine ⟨?_, hωT, ⟨x0, (hmem x0).2 (Or.inl ⟨le_refl _, hx01⟩), by omega⟩, ⟨t, mem_union_right _ ht, by omega⟩⟩
      rw [hmem]
      rintro (h | h)
      · omega
      · have := (pkCh_mem_intCompl.1 (hτI h)).2.2.2
        rw [if_neg hx0'] at this
        exact this rfl
  · rw [pkCo_inST_iff]
    rintro ⟨-, -, ⟨g, hg, bg⟩, -⟩
    by_cases e : g = y0
    · exact hy0T (e ▸ hg)
    · exact hno g hg (by omega)

/-- **[St1] (1)–(3)**, mirror for `Y` (after `X`), linear: a short failing trace `σ` of `B_Y` gives `Θ′ ⊊ Θ` keeping
`x₁ + 1`. -/
theorem pkCh_st1Y {N ω x1 y0 y1 : ℕ} {Θ σ : Finset ℕ} (hωN : ω + 3 ≤ N) (hΘ : Θ ⊆ Icc 2 (ω - 1))
    (hY : IsRun ω Θ y0 y1) (hx : x1 + 1 ∈ Θ) (hxy : x1 < y0) (hx1 : 1 ≤ x1) (hσ : AdmSepCompl N y0 y1 σ)
    (hTA : TailAvoiding N ω σ) (hs : ¬ (x1 ∈ σ ∨ InST (Icc y0 y1 ∪ σ) x1 (ω + 2))) :
    (Θ.filter (fun θ => ¬ InST (Icc y0 y1 ∪ σ) θ (ω + 2))).card < Θ.card ∧
      x1 + 1 ∈ Θ.filter (fun θ => ¬ InST (Icc y0 y1 ∪ σ) θ (ω + 2)) := by
  obtain ⟨hy0, hy01, hy1ω, hya, hyb, -⟩ := pkCh_isRun_iff.1 hY
  obtain ⟨⟨t, ht⟩, hσI, -⟩ := pkCh_asc_facts hσ
  obtain ⟨hTA1, -⟩ := pkCh_ta_iff.1 hTA
  have hmem : ∀ g, g ∈ Icc y0 y1 ∪ σ ↔ (y0 ≤ g ∧ g ≤ y1) ∨ g ∈ σ := fun g => by rw [mem_union, mem_Icc]
  have hσW : ∀ g ∈ σ, ¬ (ω + 2 ≤ g ∧ g ≤ N - 1) := fun g hg h => disjoint_left.1 hTA1 hg (mem_Icc.2 h)
  have hx1σ : x1 ∉ σ := fun h => hs (Or.inl h)
  have hωT : ω + 2 ∉ Icc y0 y1 ∪ σ := by
    rw [hmem]
    rintro (h | h)
    · omega
    · exact hσW _ h ⟨le_refl _, by omega⟩
  have hx1T : x1 ∉ Icc y0 y1 ∪ σ := by
    rw [hmem]
    rintro (h | h)
    · omega
    · exact hx1σ h
  have hno : ∀ g ∈ Icc y0 y1 ∪ σ, ¬ (g < x1 ∨ ω + 2 < g) := by
    intro g hg hgb
    apply hs
    right
    rw [pkCo_inST_iff]
    refine ⟨hx1T, hωT, ⟨y0, (hmem y0).2 (Or.inl ⟨le_refl _, hy01⟩), by omega⟩, ⟨g, hg, by omega⟩⟩
  have htI := pkCh_mem_intCompl.1 (hσI ht)
  have hy0' : y0 ≠ 1 := by omega
  rw [if_neg hy0'] at htI
  have htn := hno t (mem_union_right _ ht)
  have htx : t ≠ x1 := fun e => hx1σ (e ▸ ht)
  have htN := hσW t ht
  refine ⟨card_lt_card (filter_ssubset.2 ?_), mem_filter.2 ⟨hx, ?_⟩⟩
  · by_cases h1 : t < y0 - 1
    · have hy0Θ : y0 - 1 ∈ Θ := by
        rcases hya with h | h
        · exact absurd h hy0'
        · exact h
      refine ⟨y0 - 1, hy0Θ, not_not.2 ?_⟩
      rw [pkCo_inST_iff]
      refine ⟨?_, hωT, ⟨y0, (hmem y0).2 (Or.inl ⟨le_refl _, hy01⟩), by omega⟩, ⟨t, mem_union_right _ ht, by omega⟩⟩
      rw [hmem]
      rintro (h | h)
      · omega
      · have := (pkCh_mem_intCompl.1 (hσI h)).2.2.2
        rw [if_neg hy0'] at this
        exact this rfl
    · have hy1Θ : y1 + 1 ∈ Θ := by
        rcases hyb with h | h
        · omega
        · exact h
      refine ⟨y1 + 1, hy1Θ, not_not.2 ?_⟩
      rw [pkCo_inST_iff]
      refine ⟨?_, hωT, ⟨t, mem_union_right _ ht, by omega⟩, ⟨y0, (hmem y0).2 (Or.inl ⟨le_refl _, hy01⟩), by omega⟩⟩
      rw [hmem]
      rintro (h | h)
      · omega
      · exact (pkCh_mem_intCompl.1 (hσI h)).2.2.1 rfl
  · rw [pkCo_inST_iff]
    rintro ⟨-, -, -, ⟨g, hg, bg⟩⟩
    have := hno g hg
    by_cases e : g = x1
    · exact hx1T (e ▸ hg)
    · omega

/-- **Lemma 14.5, linear core** (BP §3.3): head `A′ = [1, ω]`, tail `W = [ω+1, N]`; `C u v` reads "the pair `{u, v}` is
not missing". Hypotheses: `Sep_all(W)` (`HW`), [L0] + head-minimality (`Hfail`: every O-run of a failing even trace
has a failing admissible trace of its complement), F^π (`HG`: no one-parity leg set has `S_G` clean). Conclusion: no
failing even trace `Θ` is spread (by strong induction on `|Θ|`, [St1] giving a smaller one when a trace is short). -/
theorem pkCh_core {N ω : ℕ} {C : ℕ → ℕ → Prop} (hC : ∀ u v, C u v → C v u) (hN : N % 2 = 0) (hω : ω % 2 = 1)
    (hωN : ω + 3 ≤ N)
    (HW : ∀ τ0 : Finset ℕ, τ0.Nonempty → τ0 ⊆ Icc (ω + 2) (N - 1) → (τ0.card = 1 ∨ ∀ t ∈ τ0, t % 2 = 1) →
      ∃ u v, u ∈ Icc (ω + 1) N ∧ v ∈ Icc (ω + 1) N ∧ u ∉ τ0 ∧ v ∉ τ0 ∧
        (∃ t ∈ τ0, min u v < t ∧ t < max u v) ∧ ¬ C u v)
    (Hfail : ∀ Θ : Finset ℕ, Θ.Nonempty → Θ ⊆ Icc 2 (ω - 1) → (∀ θ ∈ Θ, θ % 2 = 0) →
      (∀ u v, runSepA ω Θ u v → C u v) → ∀ a b, IsRun ω Θ a b →
      (∃ u v, a ≤ u ∧ u < v ∧ v ≤ b ∧ u % 2 = 1 ∧ v % 2 = 1 ∧ ¬ C u v) →
      ∃ τ, AdmSepCompl N a b τ ∧ ∀ u v, InST (Icc a b ∪ τ) u v → C u v)
    (HG : ∀ G : Finset ℕ, G ⊆ Icc 1 N → 2 ≤ G.card → ((∀ g ∈ G, g % 2 = 0) ∨ (∀ g ∈ G, g % 2 = 1)) →
      ∃ u v, (min u v, max u v) ∈ diagonals N ∧ InST G u v ∧ ¬ C u v) :
    ∀ n (Θ : Finset ℕ), Θ.card = n → Θ ⊆ Icc 2 (ω - 1) → (∀ θ ∈ Θ, θ % 2 = 0) →
      (∀ u v, runSepA ω Θ u v → C u v) → ∀ u1 v1 u2 v2 : ℕ, 1 ≤ u1 → u1 < v1 → v1 < u2 → u2 < v2 → v2 ≤ ω →
      u1 % 2 = 1 → v1 % 2 = 1 → u2 % 2 = 1 → v2 % 2 = 1 → ¬ C u1 v1 → ¬ C u2 v2 →
      (∃ θ ∈ Θ, v1 < θ ∧ θ < u2) → False := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih Θ hn hΘ hΘe hΘf u1 v1 u2 v2 h1 h12 h23 h34 h4 p1 p2 p3 p4 c1 c2 hθ
  obtain ⟨θ0, hθ0, hθ0a, hθ0b⟩ := hθ
  have hθ0I := mem_Icc.1 (hΘ hθ0)
  have hnΘ : ∀ x, x % 2 = 1 → x ∉ Θ := fun x hx h => by have := hΘe x h; omega
  obtain ⟨x0, x1, hX, hx0, hx1⟩ := pkCh_runOf hΘ (mem_Icc.2 ⟨h1, by omega⟩) (hnΘ u1 p1)
  obtain ⟨y0, y1, hY, hy0, hy1⟩ := pkCh_runOf hΘ (mem_Icc.2 ⟨by omega, by omega⟩) (hnΘ u2 p3)
  obtain ⟨hxa0, hx01, hx1ω, hxa, hxb, hXΘ⟩ := pkCh_isRun_iff.1 hX
  obtain ⟨hya0, hy01, hy1ω, hya, hyb, hYΘ⟩ := pkCh_isRun_iff.1 hY
  have hθX : ¬ (x0 ≤ θ0 ∧ θ0 ≤ x1) := fun h => hXΘ θ0 (mem_Icc.2 h) hθ0
  have hθY : ¬ (y0 ≤ θ0 ∧ θ0 ≤ y1) := fun h => hYΘ θ0 (mem_Icc.2 h) hθ0
  have hv1 : v1 ≤ x1 := by
    by_contra hc
    have hx1Θ : x1 + 1 ∈ Θ := by
      rcases hxb with h | h
      · omega
      · exact h
    have := hΘe _ hx1Θ
    exact c1 (hΘf u1 v1 (pkT_runSepA_iff.2 ⟨mem_Icc.2 ⟨h1, by omega⟩, mem_Icc.2 ⟨by omega, by omega⟩, hnΘ u1 p1,
      hnΘ v1 p2, x1 + 1, hx1Θ, by omega, by omega⟩))
  have hv2 : v2 ≤ y1 := by
    by_contra hc
    have hy1Θ : y1 + 1 ∈ Θ := by
      rcases hyb with h | h
      · omega
      · exact h
    have := hΘe _ hy1Θ
    exact c2 (hΘf u2 v2 (pkT_runSepA_iff.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, mem_Icc.2 ⟨by omega, by omega⟩,
      hnΘ u2 p3, hnΘ v2 p4, y1 + 1, hy1Θ, by omega, by omega⟩))
  have hxθ : x1 < θ0 := by omega
  have hθy : θ0 < y0 := by omega
  have hx1Θ : x1 + 1 ∈ Θ := by
    rcases hxb with h | h
    · omega
    · exact h
  have hy0Θ : y0 - 1 ∈ Θ := by
    rcases hya with h | h
    · omega
    · exact h
  have hx1e := hΘe _ hx1Θ
  have hy0e := hΘe _ hy0Θ
  have hne : Θ.Nonempty := ⟨θ0, hθ0⟩
  obtain ⟨τ, hτ, hτf⟩ := Hfail Θ hne hΘ hΘe hΘf x0 x1 hX ⟨u1, v1, hx0, h12, hv1, p1, p2, c1⟩
  obtain ⟨σ, hσ, hσf⟩ := Hfail Θ hne hΘ hΘe hΘf y0 y1 hY ⟨u2, v2, hy0, h34, hv2, p3, p4, c2⟩
  have hTAτ := pkCh_b0 hN hω hωN hx01 hx1ω HW hτ hτf
  have hTAσ := pkCh_b0 hN hω hωN hy01 hy1ω HW hσ hσf
  have hΘω : ∀ θ ∈ Θ, θ ≤ ω := fun θ hθ => by have := mem_Icc.1 (hΘ hθ); omega
  have hLτ : y0 ∈ τ ∨ InST (Icc x0 x1 ∪ τ) y0 (ω + 2) := by
    by_contra hs
    obtain ⟨hcard, hmem⟩ := pkCh_st1X hωN hΘ hX hy0Θ (by omega) (by omega) hτ hTAτ hs
    exact ih _ (hn ▸ hcard) _ rfl (subset_trans (filter_subset _ _) hΘ) (fun θ hθ => hΘe θ (mem_filter.1 hθ).1)
      (pkCh_st1_fail hC (by omega) hx1ω (pkCh_asc_facts hτ).2.2 hΘe (fun θ hθ hI => hXΘ θ hI hθ) hΘω hΘf hτf)
      u1 v1 u2 v2 h1 h12 h23 h34 h4 p1 p2 p3 p4 c1 c2 ⟨y0 - 1, hmem, by omega, by omega⟩
  have hLσ : x1 ∈ σ ∨ InST (Icc y0 y1 ∪ σ) x1 (ω + 2) := by
    by_contra hs
    obtain ⟨hcard, hmem⟩ := pkCh_st1Y hωN hΘ hY hx1Θ (by omega) (by omega) hσ hTAσ hs
    exact ih _ (hn ▸ hcard) _ rfl (subset_trans (filter_subset _ _) hΘ) (fun θ hθ => hΘe θ (mem_filter.1 hθ).1)
      (pkCh_st1_fail hC (by omega) hy1ω (pkCh_asc_facts hσ).2.2 hΘe (fun θ hθ hI => hYΘ θ hI hθ) hΘω hΘf hσf)
      u1 v1 u2 v2 h1 h12 h23 h34 h4 p1 p2 p3 p4 c1 c2 ⟨x1 + 1, hmem, by omega, by omega⟩
  have hset : ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ :=
    pkCh_tss_iff.2 ⟨hN, hω, hωN, hne, hΘ, hΘe, hX, hY, by omega, by omega, by omega, hτ, hσ, hTAτ, hTAσ, hLτ, hLσ⟩
  obtain ⟨G, hGc, hGs⟩ := threeSep_consecWit hset
  obtain ⟨hcard, a, -, len, -, hG⟩ := pkT_consecWit_iff.1 hGc
  have hN1 : 1 ≤ N := by omega
  have hGsub : G ⊆ Icc 1 N := by
    intro g hg
    rcases hG with e | e <;> rw [e] at hg <;> exact pkCo_cycArc_sub hN1 (mem_inter.1 hg).2
  have hpar : (∀ g ∈ G, g % 2 = 0) ∨ (∀ g ∈ G, g % 2 = 1) := by
    rcases hG with e | e
    · left
      intro g hg
      rw [e] at hg
      exact (pkCh_mem_evens.1 (mem_inter.1 hg).1).2
    · right
      intro g hg
      rw [e] at hg
      exact (pkCh_mem_odds.1 (mem_inter.1 hg).1).2
  obtain ⟨u, v, hd, hst, hc⟩ := HG G hGsub hcard hpar
  have hmem := hGs (pkT_mem_sepPairs.2 ⟨hd, pkCh_inST_minmax.2 hst⟩)
  obtain ⟨-, h | h | h⟩ := pkT_mem_threeSepCut.1 hmem
  · exact hc (pkCh_C_minmax hC (hΘf _ _ h))
  · exact hc (pkCh_C_minmax hC (hτf _ _ h))
  · exact hc (pkCh_C_minmax hC (hσf _ _ h))

/-! #### Rotation to the linear setting: `φ = rotLeg N (N + 1 − s)` (`φ x = cycPos N s x + 1`), inverse `ψ = rotLeg N (s − 1)` -/

theorem pkCh_phi_eq {N s : ℕ} (hs : s ∈ Icc 1 N) (x : ℕ) : rotLeg N (N + 1 - s) x = cycPos N s x + 1 := by
  have hs' := mem_Icc.1 hs
  show (x + (N + 1 - s) + N - 1) % N + 1 = (x + N - s) % N + 1
  rw [show x + (N + 1 - s) + N - 1 = (x + N - s) + N by omega, Nat.add_mod_right]

theorem pkCh_psi_phi {N s x : ℕ} (hs : s ∈ Icc 1 N) (hx : x ∈ Icc 1 N) :
    rotLeg N (s - 1) (rotLeg N (N + 1 - s) x) = x := by
  have hs' := mem_Icc.1 hs
  have hx' := mem_Icc.1 hx
  show vtx N (vtx N (x + (N + 1 - s)) + (s - 1)) = x
  rw [pkCo_vtx_vtx_add (by omega), show x + (N + 1 - s) + (s - 1) = x + N by omega, vtx_add_n,
    vtx_of_mem hx'.1 hx'.2]

theorem pkCh_phi_psi {N s y : ℕ} (hs : s ∈ Icc 1 N) (hy : y ∈ Icc 1 N) :
    rotLeg N (N + 1 - s) (rotLeg N (s - 1) y) = y := by
  have hs' := mem_Icc.1 hs
  have hy' := mem_Icc.1 hy
  show vtx N (vtx N (y + (s - 1)) + (N + 1 - s)) = y
  rw [pkCo_vtx_vtx_add (by omega), show y + (s - 1) + (N + 1 - s) = y + N by omega, vtx_add_n,
    vtx_of_mem hy'.1 hy'.2]

theorem pkCh_psi_mem {N s : ℕ} (hN : 1 ≤ N) (y : ℕ) : rotLeg N (s - 1) y ∈ Icc 1 N := by
  show vtx N (y + (s - 1)) ∈ Icc 1 N
  exact mem_Icc.2 (vtx_bounds N _ hN)

theorem pkCh_psi_pos {N s y : ℕ} (hs : s ∈ Icc 1 N) (hy : y ∈ Icc 1 N) : cycPos N s (rotLeg N (s - 1) y) = y - 1 := by
  have h := pkCh_phi_eq hs (rotLeg N (s - 1) y)
  rw [pkCh_phi_psi hs hy] at h
  omega

theorem pkCh_psi_mod {N s : ℕ} (hN : 1 ≤ N) (hE : N % 2 = 0) (hs1 : 1 ≤ s) (hs2 : s % 2 = 1) (y : ℕ) :
    rotLeg N (s - 1) y % 2 = y % 2 := by
  show vtx N (y + (s - 1)) % 2 = y % 2
  rw [pkCo_vtx_mod_two hN hE]
  omega

theorem pkCh_pos_mod {N s x : ℕ} (hE : N % 2 = 0) (hs : s ∈ Icc 1 N) (hs2 : s % 2 = 1) (hx : x ∈ Icc 1 N) :
    (cycPos N s x + 1) % 2 = x % 2 := by
  have := pkCo_cycPos_mod_two hE hs hx
  omega

/-- The clean-pair predicate of the linear setting (legs read through `ψ`). -/
def pkCh_Cl (N s : ℕ) (S : Finset (ℕ × ℕ)) (u v : ℕ) : Prop :=
  ¬ (u ∈ Icc 1 N ∧ v ∈ Icc 1 N ∧ ((rotLeg N (s - 1) u, rotLeg N (s - 1) v) ∈ missing N S ∨
    (rotLeg N (s - 1) v, rotLeg N (s - 1) u) ∈ missing N S))

theorem pkCh_Cl_iff {N s : ℕ} {S : Finset (ℕ × ℕ)} {u v : ℕ} :
    pkCh_Cl N s S u v ↔ ¬ (u ∈ Icc 1 N ∧ v ∈ Icc 1 N ∧ ((rotLeg N (s - 1) u, rotLeg N (s - 1) v) ∈ missing N S ∨
      (rotLeg N (s - 1) v, rotLeg N (s - 1) u) ∈ missing N S)) := Iff.rfl

theorem pkCh_Cl_symm {N s : ℕ} {S : Finset (ℕ × ℕ)} (u v : ℕ) (h : pkCh_Cl N s S u v) : pkCh_Cl N s S v u := by
  rw [pkCh_Cl_iff] at h ⊢
  rintro ⟨h1, h2, h3 | h3⟩
  · exact h ⟨h2, h1, Or.inr h3⟩
  · exact h ⟨h2, h1, Or.inl h3⟩

/-- A missing pair of legs gives a non-clean pair of linear labels. -/
theorem pkCh_notCl {N s : ℕ} {S : Finset (ℕ × ℕ)} (hs : s ∈ Icc 1 N) {x y : ℕ} (hx : x ∈ Icc 1 N)
    (hy : y ∈ Icc 1 N) (hm : (x, y) ∈ missing N S) :
    ¬ pkCh_Cl N s S (rotLeg N (N + 1 - s) x) (rotLeg N (N + 1 - s) y) := by
  have hN : 1 ≤ N := by have := mem_Icc.1 hs; omega
  rw [pkCh_Cl_iff, not_not, pkCh_psi_phi hs hx, pkCh_psi_phi hs hy]
  refine ⟨?_, ?_, Or.inl hm⟩
  · rw [pkCh_phi_eq hs, mem_Icc]
    exact ⟨by omega, Nat.succ_le_of_lt (pkCo_cycPos_lt hN s _)⟩
  · rw [pkCh_phi_eq hs, mem_Icc]
    exact ⟨by omega, Nat.succ_le_of_lt (pkCo_cycPos_lt hN s _)⟩

/-- The tail of a mixed chord follows its head. -/
theorem pkCh_tail_eq {N : ℕ} {P : ℕ × ℕ} (hP : P ∈ oddDiagonals N) :
    tailStart P = vtx N (headStart P + headLen N P) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := pkCo_mem_oddDiagonals.1 hP
  show (if P.1 % 2 = 1 then P.2 else P.1) =
    vtx N ((if P.1 % 2 = 1 then P.1 else P.2) + (if P.1 % 2 = 1 then P.2 - P.1 else N - (P.2 - P.1)))
  split_ifs with h
  · rw [show P.1 + (P.2 - P.1) = P.2 by omega, vtx_of_mem (by omega) h2]
  · rw [show P.2 + (N - (P.2 - P.1)) = P.1 + N by omega, vtx_add_n, vtx_of_mem h1 (by omega)]

/-- Tail legs through head positions. -/
theorem pkCh_tailpos {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {P : ℕ × ℕ} (hP : P ∈ oddDiagonals N) {x : ℕ}
    (hx : x ∈ Icc 1 N) :
    (x ∈ cycArc N (tailStart P) (tailLen N P) ↔ headLen N P ≤ cycPos N (headStart P) x) ∧
      (headLen N P ≤ cycPos N (headStart P) x →
        cycPos N (tailStart P) x = cycPos N (headStart P) x - headLen N P) := by
  obtain ⟨hts, -, -, -, -, hs, -, -, hk3, hkN⟩ := pkCh_sides hE hP
  have e : tailStart P = vtx N (headStart P + headLen N P) := pkCh_tail_eq hP
  have hp := pkCh_pos_shift hs hx (show headLen N P < N by omega)
  have hlt := pkCo_cycPos_lt (show 1 ≤ N by omega) (headStart P) x
  rw [← e] at hp
  have htl : tailLen N P = N - headLen N P := rfl
  rw [htl, pkCo_mem_cycArc_pos hts (by omega), hp]
  refine ⟨?_, fun h => by rw [if_pos h]⟩
  constructor
  · rintro ⟨-, h⟩
    split_ifs at h with h' <;> omega
  · intro h
    exact ⟨hx, by rw [if_pos h]; omega⟩

/-- Head legs through head positions. -/
theorem pkCh_headpos {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {P : ℕ × ℕ} (hP : P ∈ oddDiagonals N) {x : ℕ} :
    x ∈ oddSide N P ↔ x ∈ Icc 1 N ∧ cycPos N (headStart P) x < headLen N P := by
  obtain ⟨-, -, -, -, -, hs, -, -, -, hkN⟩ := pkCh_sides hE hP
  rw [(pkCh_arcs (by omega) hE hP).1 x, pkCo_mem_cycArc_pos hs (by omega)]

theorem pkCh_evenpos {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {P : ℕ × ℕ} (hP : P ∈ oddDiagonals N) {x : ℕ} :
    x ∈ evenSide N P ↔ x ∈ Icc 1 N ∧ headLen N P ≤ cycPos N (headStart P) x := by
  show x ∈ Icc 1 N \ oddSide N P ↔ _
  rw [mem_sdiff, pkCh_headpos hN hE hP]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by by_contra h; exact h2 ⟨h1, by omega⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h => by omega⟩

/-- `HW` of the linear core: `Sep_all` of the tail of `P`. -/
theorem pkCh_HW {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ}
    (hPo : P ∈ oddDiagonals N) (hPB : NoFreeSep N S (tailStart P) (tailLen N P) 1) :
    ∀ τ0 : Finset ℕ, τ0.Nonempty → τ0 ⊆ Icc (headLen N P + 2) (N - 1) → (τ0.card = 1 ∨ ∀ t ∈ τ0, t % 2 = 1) →
      ∃ u v, u ∈ Icc (headLen N P + 1) N ∧ v ∈ Icc (headLen N P + 1) N ∧ u ∉ τ0 ∧ v ∉ τ0 ∧
        (∃ t ∈ τ0, min u v < t ∧ t < max u v) ∧ ¬ pkCh_Cl N (headStart P) S u v := by
  obtain ⟨hts, -, -, htl3, -, hs, hs2, hk1, hk3, hkN⟩ := pkCh_sides hE hPo
  have hN1 : 1 ≤ N := by omega
  have hsI := mem_Icc.1 hs
  have htl : tailLen N P = N - headLen N P := rfl
  intro τ0 hne hsub hadm
  have hτ0I : ∀ y ∈ τ0, y ∈ Icc 1 N := fun y hy => by
    have := mem_Icc.1 (hsub hy)
    exact mem_Icc.2 ⟨by omega, by omega⟩
  have hinj : Set.InjOn (rotLeg N (headStart P - 1)) τ0 := fun x hx y hy h =>
    pkCo_rotLeg_inj hN1 (hτ0I x (mem_coe.1 hx)) (hτ0I y (mem_coe.1 hy)) h
  have hψt : ∀ y ∈ τ0, rotLeg N (headStart P - 1) y ∈ cycArc N (tailStart P) (tailLen N P) ∧
      cycPos N (tailStart P) (rotLeg N (headStart P - 1) y) = y - 1 - headLen N P := by
    intro y hy
    have hyI := mem_Icc.1 (hsub hy)
    have hψ := pkCh_psi_mem (s := headStart P) hN1 y
    have hp := pkCh_psi_pos hs (hτ0I y hy)
    obtain ⟨t1, t2⟩ := pkCh_tailpos hN hE hPo hψ
    rw [hp] at t1 t2
    exact ⟨t1.2 (by omega), by rw [t2 (by omega)]⟩
  have hadm' : τ0.image (rotLeg N (headStart P - 1)) ∈ admSeps N (tailStart P) (tailLen N P) 1 := by
    rw [pkCo_mem_admSeps]
    refine ⟨fun x hx => ?_, ?_⟩
    · obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
      have hyI := mem_Icc.1 (hsub hy)
      rw [pkCo_mem_intArc hts (by rw [htl]; omega), (hψt y hy).2, htl]
      exact ⟨pkCh_psi_mem hN1 y, by omega, by omega⟩
    · rw [card_image_of_injOn hinj]
      by_cases hc : τ0.card = 1
      · exact Or.inl hc
      · right
        refine ⟨?_, fun x hx => ?_⟩
        · have := card_pos.2 hne; omega
        · obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
          rcases hadm with h | h
          · exact absurd h hc
          · rw [pkCh_psi_mod hN1 hE hsI.1 hs2]; exact h y hy
  have hnd := pkCh_noFree_iff.1 hPB _ hadm'
  obtain ⟨⟨p1, p2⟩, hpS, hpM⟩ := not_disjoint_iff.1 hnd
  obtain ⟨-, hp1, hp2, hp1τ, hp2τ, θ, hθ, b1, b2⟩ := pkCo_mem_sepIn.1 hpS
  obtain ⟨t, ht, rfl⟩ := mem_image.1 hθ
  simp only at hp1 hp2 hp1τ hp2τ b1 b2
  have hp1I := pkCo_cycArc_sub hN1 hp1
  have hp2I := pkCo_cycArc_sub hN1 hp2
  obtain ⟨q1, q1'⟩ := pkCh_tailpos hN hE hPo hp1I
  obtain ⟨q2, q2'⟩ := pkCh_tailpos hN hE hPo hp2I
  have k1 := q1.1 hp1
  have k2 := q2.1 hp2
  rw [q1' k1, q2' k2, (hψt t ht).2] at b1 b2
  have hl1 := pkCo_cycPos_lt hN1 (headStart P) p1
  have hl2 := pkCo_cycPos_lt hN1 (headStart P) p2
  have htI := mem_Icc.1 (hsub ht)
  refine ⟨rotLeg N (N + 1 - headStart P) p1, rotLeg N (N + 1 - headStart P) p2, ?_, ?_, ?_, ?_,
    ⟨t, ht, ?_, ?_⟩, pkCh_notCl hs hp1I hp2I hpM⟩
  · rw [pkCh_phi_eq hs, mem_Icc]; omega
  · rw [pkCh_phi_eq hs, mem_Icc]; omega
  · intro h
    apply hp1τ
    rw [← pkCh_psi_phi hs hp1I]
    exact mem_image_of_mem _ h
  · intro h
    apply hp2τ
    rw [← pkCh_psi_phi hs hp2I]
    exact mem_image_of_mem _ h
  · rw [pkCh_phi_eq hs, pkCh_phi_eq hs]; omega
  · rw [pkCh_phi_eq hs, pkCh_phi_eq hs]; omega

/-- `HG` of the linear core: F^π (no one-parity `S_G` is clean). -/
theorem pkCh_HG {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} (hF : InFpi N S) {s : ℕ}
    (hs : s ∈ Icc 1 N) (hs2 : s % 2 = 1) :
    ∀ G : Finset ℕ, G ⊆ Icc 1 N → 2 ≤ G.card → ((∀ g ∈ G, g % 2 = 0) ∨ (∀ g ∈ G, g % 2 = 1)) →
      ∃ u v, (min u v, max u v) ∈ diagonals N ∧ InST G u v ∧ ¬ pkCh_Cl N s S u v := by
  intro G hG hc hp
  have hN1 : 1 ≤ N := by omega
  have hsI := mem_Icc.1 hs
  obtain ⟨-, -, hnG⟩ := pkCh_fpi_iff.1 hF
  have hsubψ : G.image (rotLeg N (s - 1)) ⊆ Icc 1 N := fun x hx => by
    obtain ⟨y, -, rfl⟩ := mem_image.1 hx
    exact pkCh_psi_mem hN1 y
  have hinj : Set.InjOn (rotLeg N (s - 1)) G := fun x hx y hy h =>
    pkCo_rotLeg_inj hN1 (hG (mem_coe.1 hx)) (hG (mem_coe.1 hy)) h
  have hcard : 2 ≤ (G.image (rotLeg N (s - 1))).card := by rw [card_image_of_injOn hinj]; exact hc
  have hGs : IsGSet N (G.image (rotLeg N (s - 1))) := by
    rcases hp with h | h
    · refine pkCh_sameParity hsubψ hcard (r := 0) fun x hx => ?_
      obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
      rw [pkCh_psi_mod hN1 hE hsI.1 hs2]; exact h y hy
    · refine pkCh_sameParity hsubψ hcard (r := 1) fun x hx => ?_
      obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
      rw [pkCh_psi_mod hN1 hE hsI.1 hs2]; exact h y hy
  have hmemF : sepPairs N (G.image (rotLeg N (s - 1))) ∈ gFamily N :=
    mem_image.2 ⟨_, pkCh_mem_gLeg.2 ⟨hsubψ, hGs⟩, rfl⟩
  obtain ⟨⟨q1, q2⟩, hq, hqS⟩ := not_subset.1 (fun h => hnG (pkCh_cgm_iff.2 ⟨_, hmemF, h⟩))
  obtain ⟨hqd, hqst⟩ := pkT_mem_sepPairs.1 hq
  have hqd' := mem_diagonals.1 hqd
  simp only at hqd' hqst
  have hq1 : q1 ∈ Icc 1 N := mem_Icc.2 ⟨by omega, by omega⟩
  have hq2 : q2 ∈ Icc 1 N := mem_Icc.2 ⟨by omega, by omega⟩
  have hqM : (q1, q2) ∈ missing N S := pkCh_mem_missing.2 ⟨hqd, hqS⟩
  have hφ1 : rotLeg N (N + 1 - s) q1 ∈ Icc 1 N := by
    rw [pkCh_phi_eq hs, mem_Icc]
    exact ⟨by omega, Nat.succ_le_of_lt (pkCo_cycPos_lt hN1 s _)⟩
  have hφ2 : rotLeg N (N + 1 - s) q2 ∈ Icc 1 N := by
    rw [pkCh_phi_eq hs, mem_Icc]
    exact ⟨by omega, Nat.succ_le_of_lt (pkCo_cycPos_lt hN1 s _)⟩
  have hst : InST G (rotLeg N (N + 1 - s) q1) (rotLeg N (N + 1 - s) q2) := by
    rw [← inST_rotLeg hN1 (s - 1) hG hφ1 hφ2, pkCh_psi_phi hs hq1, pkCh_psi_phi hs hq2]
    exact hqst
  refine ⟨_, _, ?_, hst, pkCh_notCl hs hq1 hq2 hqM⟩
  have hne : rotLeg N (N + 1 - s) q1 ≠ rotLeg N (N + 1 - s) q2 := by
    intro e
    have := congrArg (rotLeg N (s - 1)) e
    rw [pkCh_psi_phi hs hq1, pkCh_psi_phi hs hq2] at this
    omega
  have hst' := pkCh_inST_minmax.2 hst
  rcases lt_or_gt_of_ne hne with h | h
  · rw [min_eq_left h.le, max_eq_right h.le] at hst' ⊢
    exact pkCo_diag_of_inST hG hφ1 hφ2 h hst'
  · rw [min_eq_right h.le, max_eq_left h.le] at hst' ⊢
    exact pkCo_diag_of_inST hG hφ2 hφ1 h hst'

/-- A missing pair in either order is not clean in the linear setting. -/
theorem pkCh_notCl_mm {N s : ℕ} {S : Finset (ℕ × ℕ)} (hs : s ∈ Icc 1 N) {x y : ℕ} (hx : x ∈ Icc 1 N)
    (hy : y ∈ Icc 1 N) (hm : (min x y, max x y) ∈ missing N S) :
    ¬ pkCh_Cl N s S (rotLeg N (N + 1 - s) x) (rotLeg N (N + 1 - s) y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, max_eq_right h] at hm
    exact pkCh_notCl hs hx hy hm
  · rw [min_eq_right h, max_eq_left h] at hm
    exact fun hc => pkCh_notCl hs hy hx hm (pkCh_Cl_symm _ _ hc)

set_option maxHeartbeats 1000000 in
/-- `Hfail` of the linear core: **[L0]** (the run chord `Q_Z` of an O-run is in `𝒫₁`, BP App. D §7) and head-minimality
of the canonical chord give a failing admissible trace of `B_{Q_Z}`, read in the linear setting. -/
theorem pkCh_Hfail {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ}
    (hP : IsMinimalChord N S P) :
    ∀ Θ : Finset ℕ, Θ.Nonempty → Θ ⊆ Icc 2 (headLen N P - 1) → (∀ θ ∈ Θ, θ % 2 = 0) →
      (∀ u v, runSepA (headLen N P) Θ u v → pkCh_Cl N (headStart P) S u v) → ∀ a b, IsRun (headLen N P) Θ a b →
      (∃ u v, a ≤ u ∧ u < v ∧ v ≤ b ∧ u % 2 = 1 ∧ v % 2 = 1 ∧ ¬ pkCh_Cl N (headStart P) S u v) →
      ∃ τ, AdmSepCompl N a b τ ∧ ∀ u v, InST (Icc a b ∪ τ) u v → pkCh_Cl N (headStart P) S u v := by
  intro Θ hne hΘ hΘe hΘf a b hR huv
  obtain ⟨u, v, hau, huv, hvb, hu2, hv2, huvC⟩ := huv
  obtain ⟨hPg, hmin⟩ := pkCh_minChord_iff.1 hP
  obtain ⟨hPp, -⟩ := pkCh_mem_goodTail.1 hPg
  obtain ⟨hPo, hPclean, hPee, -⟩ := pkCh_mem_pole.1 hPp
  obtain ⟨-, -, -, -, -, hs, hs2, hk1, hk3, hkN⟩ := pkCh_sides hE hPo
  obtain ⟨ha1, hab, hbk, haΘ, hbΘ, hRΘ⟩ := pkCh_isRun_iff.1 hR
  have hN1 : 1 ≤ N := by omega
  have hsI := mem_Icc.1 hs
  have hΘI : ∀ θ ∈ Θ, 2 ≤ θ ∧ θ ≤ headLen N P - 1 := fun θ h => mem_Icc.1 (hΘ h)
  have ha2 : a % 2 = 1 := by
    rcases haΘ with h | h
    · omega
    · have := hΘe _ h; have := hΘI _ h; omega
  have hb2 : b % 2 = 1 := by
    rcases hbΘ with h | h
    · omega
    · have := hΘe _ h; omega
  have hr2 : rotLeg N (headStart P - 1) (b + 1) % 2 = 0 := by
    rw [pkCh_psi_mod hN1 hE hsI.1 hs2]; omega
  obtain ⟨Q, hQo, hQts, hQtl⟩ := pkCh_mkTail (l := N - (b + 1 - a)) hE (pkCh_psi_mem hN1 (b + 1)) hr2
    (by omega) (by omega) (by omega)
  have hQtsI : tailStart Q ∈ Icc 1 N := by rw [hQts]; exact pkCh_psi_mem hN1 _
  have hQts' : tailStart Q = vtx N (headStart P + b) := by
    rw [hQts]
    show vtx N (b + 1 + (headStart P - 1)) = vtx N (headStart P + b)
    rw [show b + 1 + (headStart P - 1) = headStart P + b by omega]
  have hposQ : ∀ x ∈ Icc 1 N, cycPos N (tailStart Q) x = if b ≤ cycPos N (headStart P) x then
      cycPos N (headStart P) x - b else cycPos N (headStart P) x + N - b := fun x hx => by
    rw [hQts']; exact pkCh_pos_shift hs hx (by omega)
  have hevQ : ∀ x, x ∈ evenSide N Q ↔ x ∈ Icc 1 N ∧
      (cycPos N (headStart P) x + 1 < a ∨ b < cycPos N (headStart P) x + 1) := by
    intro x
    rw [pkCh_mem_even (by omega) hE hQo, hQtl]
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
  have hodQ : ∀ x, x ∈ oddSide N Q ↔ x ∈ Icc 1 N ∧
      a ≤ cycPos N (headStart P) x + 1 ∧ cycPos N (headStart P) x + 1 ≤ b := by
    intro x
    rw [pkCh_mem_odd (by omega) hE hQo, hQtl]
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
  -- [L0]: `Q ∈ 𝒫₁`
  have hQpole : Q ∈ poleChords N S := by
    refine pkCh_mem_pole.2 ⟨hQo, disjoint_left.2 fun p hp hpm => ?_, ?_, ?_⟩
    · obtain ⟨e, he, o, ho, rfl⟩ := pkCh_mem_minRect.1 hp
      obtain ⟨heQ, he2⟩ := pkCh_mem_evens.1 he
      obtain ⟨hoQ, ho2⟩ := pkCh_mem_odds.1 ho
      obtain ⟨heI, hea, heb⟩ := (hodQ e).1 heQ
      obtain ⟨hoI, hob⟩ := (hevQ o).1 hoQ
      have hepos := pkCh_pos_mod hE hs hs2 heI
      have hopos := pkCh_pos_mod hE hs hs2 hoI
      by_cases hok : headLen N P ≤ cycPos N (headStart P) o
      · apply disjoint_left.1 hPclean _ hpm
        exact pkCh_mem_minRect.2 ⟨e, pkCh_mem_evens.2 ⟨(pkCh_headpos hN hE hPo).2 ⟨heI, by omega⟩, he2⟩, o,
          pkCh_mem_odds.2 ⟨(pkCh_evenpos hN hE hPo).2 ⟨hoI, hok⟩, ho2⟩, rfl⟩
      · apply pkCh_notCl_mm hs heI hoI hpm
        apply hΘf
        rw [pkCh_phi_eq hs, pkCh_phi_eq hs, pkT_runSepA_iff]
        have hoΘ : cycPos N (headStart P) o + 1 ∉ Θ := fun h => by have := hΘe _ h; omega
        have heΘ : cycPos N (headStart P) e + 1 ∉ Θ := fun h => hRΘ _ (mem_Icc.2 ⟨hea, heb⟩) h
        refine ⟨mem_Icc.2 ⟨by omega, by omega⟩, mem_Icc.2 ⟨by omega, by omega⟩, heΘ, hoΘ, ?_⟩
        rcases hob with h | h
        · have ha' : a - 1 ∈ Θ := by
            rcases haΘ with h' | h'
            · omega
            · exact h'
          have := hΘe _ ha'
          exact ⟨a - 1, ha', by omega, by omega⟩
        · have hb' : b + 1 ∈ Θ := by
            rcases hbΘ with h' | h'
            · omega
            · exact h'
          have := hΘe _ hb'
          exact ⟨b + 1, hb', by omega, by omega⟩
    · obtain ⟨⟨g1, g2⟩, hg⟩ := hPee
      obtain ⟨hgM, hg1, hg2⟩ := pkCh_mem_innerEE.1 hg
      have h1 := (pkCh_evenpos hN hE hPo).1 hg1
      have h2 := (pkCh_evenpos hN hE hPo).1 hg2
      exact ⟨(g1, g2), pkCh_mem_innerEE.2 ⟨hgM, (hevQ _).2 ⟨h1.1, Or.inr (by omega)⟩,
        (hevQ _).2 ⟨h2.1, Or.inr (by omega)⟩⟩⟩
    · rw [pkCh_Cl_iff, not_not] at huvC
      obtain ⟨huI, hvI, hm⟩ := huvC
      have hψu := pkCh_psi_pos hs huI
      have hψv := pkCh_psi_pos hs hvI
      have hmu := pkCh_psi_mod hN1 hE hsI.1 hs2 u
      have hmv := pkCh_psi_mod hN1 hE hsI.1 hs2 v
      have hoU : rotLeg N (headStart P - 1) u ∈ oddSide N Q :=
        (hodQ _).2 ⟨pkCh_psi_mem hN1 u, by omega, by omega⟩
      have hoV : rotLeg N (headStart P - 1) v ∈ oddSide N Q :=
        (hodQ _).2 ⟨pkCh_psi_mem hN1 v, by omega, by omega⟩
      rcases hm with hm | hm
      · exact ⟨_, pkCh_mem_innerOO.2 ⟨pkCh_mem_Moo.2 ⟨hm, (by omega : rotLeg N (headStart P - 1) u % 2 = 1),
          (by omega : rotLeg N (headStart P - 1) v % 2 = 1)⟩, hoU, hoV⟩⟩
      · exact ⟨_, pkCh_mem_innerOO.2 ⟨pkCh_mem_Moo.2 ⟨hm, (by omega : rotLeg N (headStart P - 1) v % 2 = 1),
          (by omega : rotLeg N (headStart P - 1) u % 2 = 1)⟩, hoV, hoU⟩⟩
  -- head-minimality: `A_Q ⊊ A_P`, so `Q ∉ 𝒮_B`
  have hsub' : oddSide N Q ⊆ oddSide N P := fun x hx => by
    obtain ⟨hxI, h1, h2⟩ := (hodQ x).1 hx
    exact (pkCh_headpos hN hE hPo).2 ⟨hxI, by omega⟩
  have hsub : oddSide N Q ⊂ oddSide N P := by
    obtain ⟨θ, hθ⟩ := hne
    have hθI := hΘI θ hθ
    have hθN : θ ∈ Icc 1 N := mem_Icc.2 ⟨by omega, by omega⟩
    have hp := pkCh_psi_pos hs hθN
    refine (ssubset_iff_of_subset hsub').2 ⟨rotLeg N (headStart P - 1) θ,
      (pkCh_headpos hN hE hPo).2 ⟨pkCh_psi_mem hN1 θ, by omega⟩, fun h => ?_⟩
    obtain ⟨-, h1, h2⟩ := (hodQ _).1 h
    exact hRΘ θ (mem_Icc.2 ⟨by omega, by omega⟩) hθ
  have hQng : Q ∉ goodTail N S := fun h => hmin Q h hsub
  obtain ⟨τ0, hτ0, hτ0d⟩ : ∃ τ0 ∈ admSeps N (tailStart Q) (tailLen N Q) 1,
      Disjoint (sepIn N (tailStart Q) (tailLen N Q) τ0) (missing N S) := by
    by_contra hc
    exact hQng (pkCh_mem_goodTail.2 ⟨hQpole, pkCh_noFree_iff.2 fun τ0 hτ0 hd => hc ⟨τ0, hτ0, hd⟩⟩)
  obtain ⟨hτ0sub, hτ0c⟩ := pkCo_mem_admSeps.1 hτ0
  have hτ0I : ∀ x ∈ τ0, x ∈ Icc 1 N ∧ 1 ≤ cycPos N (tailStart Q) x ∧
      cycPos N (tailStart Q) x + 2 ≤ tailLen N Q := fun x hx =>
    (pkCo_mem_intArc hQtsI (by rw [hQtl]; omega)).1 (hτ0sub hx)
  have hint : ∀ x ∈ τ0, rotLeg N (N + 1 - headStart P) x ∈ intCompl N a b := by
    intro x hx
    obtain ⟨hxI, h1, h2⟩ := hτ0I x hx
    rw [hposQ x hxI] at h1 h2
    rw [hQtl] at h2
    have hlt := pkCo_cycPos_lt hN1 (headStart P) x
    rw [pkCh_mem_intCompl, pkCh_phi_eq hs]
    split_ifs at h1 h2 ⊢ <;> omega
  have hinj : Set.InjOn (rotLeg N (N + 1 - headStart P)) τ0 := fun x hx y hy h =>
    pkCo_rotLeg_inj hN1 (hτ0I x (mem_coe.1 hx)).1 (hτ0I y (mem_coe.1 hy)).1 h
  refine ⟨τ0.image (rotLeg N (N + 1 - headStart P)), ?_, ?_⟩
  · rw [pkCh_asc_iff]
    rcases hτ0c with hc1 | ⟨hc2, hodd⟩
    · left
      obtain ⟨x, rfl⟩ := card_eq_one.1 hc1
      exact ⟨_, hint x (mem_singleton_self x), by rw [image_singleton]⟩
    · right
      refine ⟨by rw [card_image_of_injOn hinj]; exact hc2, fun y hy => ?_, fun y hy => ?_⟩
      · obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
        exact hint x hx
      · obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
        rw [pkCh_phi_eq hs, pkCh_pos_mod hE hs hs2 (hτ0I x hx).1]
        exact hodd x hx
  · intro x y hin
    rw [pkCh_Cl_iff]
    rintro ⟨hxI, hyI, hm⟩
    have hpx := pkCh_psi_pos hs hxI
    have hpy := pkCh_psi_pos hs hyI
    have hx' := mem_Icc.1 hxI
    have hy' := mem_Icc.1 hyI
    rw [pkCo_inST_iff] at hin
    obtain ⟨hxT, hyT, ⟨g, hg, bg⟩, ⟨g', hg', og⟩⟩ := hin
    have hxab : ¬ (a ≤ x ∧ x ≤ b) := fun h => hxT (mem_union_left _ (mem_Icc.2 h))
    have hyab : ¬ (a ≤ y ∧ y ≤ b) := fun h => hyT (mem_union_left _ (mem_Icc.2 h))
    have hQx : cycPos N (tailStart Q) (rotLeg N (headStart P - 1) x) =
        if b ≤ x - 1 then x - 1 - b else x - 1 + N - b := by
      rw [hposQ _ (pkCh_psi_mem hN1 x), hpx]
    have hQy : cycPos N (tailStart Q) (rotLeg N (headStart P - 1) y) =
        if b ≤ y - 1 then y - 1 - b else y - 1 + N - b := by
      rw [hposQ _ (pkCh_psi_mem hN1 y), hpy]
    have hxA : rotLeg N (headStart P - 1) x ∈ cycArc N (tailStart Q) (tailLen N Q) := by
      rw [← (pkCh_arcs (by omega) hE hQo).2.1, hevQ, hpx]
      exact ⟨pkCh_psi_mem hN1 x, by omega⟩
    have hyA : rotLeg N (headStart P - 1) y ∈ cycArc N (tailStart Q) (tailLen N Q) := by
      rw [← (pkCh_arcs (by omega) hE hQo).2.1, hevQ, hpy]
      exact ⟨pkCh_psi_mem hN1 y, by omega⟩
    have hxτ : rotLeg N (headStart P - 1) x ∉ τ0 := fun h => by
      have := mem_image_of_mem (rotLeg N (N + 1 - headStart P)) h
      rw [pkCh_phi_psi hs hxI] at this
      exact hxT (mem_union_right _ this)
    have hyτ : rotLeg N (headStart P - 1) y ∉ τ0 := fun h => by
      have := mem_image_of_mem (rotLeg N (N + 1 - headStart P)) h
      rw [pkCh_phi_psi hs hyI] at this
      exact hyT (mem_union_right _ this)
    have hθc : ∃ θ ∈ τ0, min (cycPos N (tailStart Q) (rotLeg N (headStart P - 1) x))
        (cycPos N (tailStart Q) (rotLeg N (headStart P - 1) y)) < cycPos N (tailStart Q) θ ∧
        cycPos N (tailStart Q) θ < max (cycPos N (tailStart Q) (rotLeg N (headStart P - 1) x))
        (cycPos N (tailStart Q) (rotLeg N (headStart P - 1) y)) := by
      rw [hQx, hQy]
      rcases mem_union.1 hg with hg1 | hg1 <;> rcases mem_union.1 hg' with hg2 | hg2
      · rw [mem_Icc] at hg1 hg2
        exfalso
        omega
      · obtain ⟨θ, hθ, rfl⟩ := mem_image.1 hg2
        obtain ⟨i1, i2, -, -⟩ := pkCh_mem_intCompl.1 (hint θ hθ)
        have hθI := (hτ0I θ hθ).1
        simp only [pkCh_phi_eq hs] at og i1 i2
        rw [mem_Icc] at hg1
        refine ⟨θ, hθ, ?_⟩
        rw [hposQ θ hθI]
        split_ifs <;> omega
      · obtain ⟨θ, hθ, rfl⟩ := mem_image.1 hg1
        obtain ⟨i1, i2, -, -⟩ := pkCh_mem_intCompl.1 (hint θ hθ)
        have hθI := (hτ0I θ hθ).1
        simp only [pkCh_phi_eq hs] at bg i1 i2
        rw [mem_Icc] at hg2
        refine ⟨θ, hθ, ?_⟩
        rw [hposQ θ hθI]
        split_ifs <;> omega
      · obtain ⟨θ, hθ, rfl⟩ := mem_image.1 hg1
        obtain ⟨θ', hθ', rfl⟩ := mem_image.1 hg2
        obtain ⟨i1, i2, -, -⟩ := pkCh_mem_intCompl.1 (hint θ hθ)
        obtain ⟨j1, j2, -, -⟩ := pkCh_mem_intCompl.1 (hint θ' hθ')
        simp only [pkCh_phi_eq hs] at bg og i1 i2 j1 j2
        by_cases hside : (x < a ∧ y < a) ∨ (b < x ∧ b < y)
        · refine ⟨θ, hθ, ?_⟩
          rw [hposQ θ (hτ0I θ hθ).1]
          split_ifs <;> omega
        · refine ⟨θ', hθ', ?_⟩
          rw [hposQ θ' (hτ0I θ' hθ').1]
          split_ifs <;> omega
    rcases hm with hm | hm
    · exact disjoint_left.1 hτ0d (pkCo_mem_sepIn.2 ⟨(pkCh_mem_missing.1 hm).1, hxA, hyA, hxτ, hyτ, hθc⟩) hm
    · obtain ⟨θ, hθ, c1, c2⟩ := hθc
      rw [min_comm] at c1
      rw [max_comm] at c2
      exact disjoint_left.1 hτ0d (pkCo_mem_sepIn.2 ⟨(pkCh_mem_missing.1 hm).1, hyA, hxA, hyτ, hxτ, θ, hθ, c1, c2⟩) hm

theorem pkCh_evenTop_iff {N : ℕ} {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ} :
    EvenTopP N S P ↔ ∀ Θ ∈ admSeps N (headStart P) (headLen N P) 0, (∀ θ ∈ Θ, θ % 2 = 0) →
      Disjoint (sepIn N (headStart P) (headLen N P) Θ) (missing N S) → ¬ Spread N S (headStart P) (headLen N P) Θ :=
  Iff.rfl

/-- **[D] Lemma 14.5** at a canonical chord, from the linear core: a spread failing even trace of the head gives a
contradiction. -/
theorem pkCh_evenTop_gen {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} (hF : InFpi N S)
    {P : ℕ × ℕ} (hP : IsMinimalChord N S P) {Θ : Finset ℕ} (hΘ : Θ ∈ admSeps N (headStart P) (headLen N P) 0)
    (hΘe : ∀ θ ∈ Θ, θ % 2 = 0) (hΘd : Disjoint (sepIn N (headStart P) (headLen N P) Θ) (missing N S))
    (hsp : Spread N S (headStart P) (headLen N P) Θ) : False := by
  obtain ⟨hPg, -⟩ := pkCh_minChord_iff.1 hP
  obtain ⟨hPp, hPB⟩ := pkCh_mem_goodTail.1 hPg
  have hPo := (pkCh_mem_pole.1 hPp).1
  obtain ⟨-, -, -, -, -, hs, hs2, hk1, hk3, hkN⟩ := pkCh_sides hE hPo
  have hN1 : 1 ≤ N := by omega
  obtain ⟨hΘsub, -⟩ := pkCo_mem_admSeps.1 hΘ
  have hΘI : ∀ θ ∈ Θ, θ ∈ Icc 1 N ∧ 1 ≤ cycPos N (headStart P) θ ∧
      cycPos N (headStart P) θ + 2 ≤ headLen N P := fun θ h => (pkCo_mem_intArc hs (by omega)).1 (hΘsub h)
  have hΘl : Θ.image (rotLeg N (N + 1 - headStart P)) ⊆ Icc 2 (headLen N P - 1) := fun y hy => by
    obtain ⟨θ, hθ, rfl⟩ := mem_image.1 hy
    have := hΘI θ hθ
    rw [pkCh_phi_eq hs, mem_Icc]
    omega
  have hΘle : ∀ t ∈ Θ.image (rotLeg N (N + 1 - headStart P)), t % 2 = 0 := fun y hy => by
    obtain ⟨θ, hθ, rfl⟩ := mem_image.1 hy
    rw [pkCh_phi_eq hs, pkCh_pos_mod hE hs hs2 (hΘI θ hθ).1]
    exact hΘe θ hθ
  have hΘlf : ∀ u v, runSepA (headLen N P) (Θ.image (rotLeg N (N + 1 - headStart P))) u v →
      pkCh_Cl N (headStart P) S u v := by
    intro u v h
    obtain ⟨hu, hv, huΘ, hvΘ, t, ht, b1, b2⟩ := pkT_runSepA_iff.1 h
    obtain ⟨θ, hθ, rfl⟩ := mem_image.1 ht
    rw [pkCh_Cl_iff]
    rintro ⟨huI, hvI, hm⟩
    have hu' := mem_Icc.1 hu
    have hv' := mem_Icc.1 hv
    have hpu := pkCh_psi_pos hs huI
    have hpv := pkCh_psi_pos hs hvI
    have hψuA : rotLeg N (headStart P - 1) u ∈ cycArc N (headStart P) (headLen N P) :=
      (pkCo_mem_cycArc_pos hs (by omega)).2 ⟨pkCh_psi_mem hN1 u, by omega⟩
    have hψvA : rotLeg N (headStart P - 1) v ∈ cycArc N (headStart P) (headLen N P) :=
      (pkCo_mem_cycArc_pos hs (by omega)).2 ⟨pkCh_psi_mem hN1 v, by omega⟩
    have hψuΘ : rotLeg N (headStart P - 1) u ∉ Θ := fun h => huΘ (by
      rw [← pkCh_phi_psi hs huI]; exact mem_image_of_mem _ h)
    have hψvΘ : rotLeg N (headStart P - 1) v ∉ Θ := fun h => hvΘ (by
      rw [← pkCh_phi_psi hs hvI]; exact mem_image_of_mem _ h)
    rw [pkCh_phi_eq hs] at b1 b2
    have hθb : min (cycPos N (headStart P) (rotLeg N (headStart P - 1) u))
        (cycPos N (headStart P) (rotLeg N (headStart P - 1) v)) < cycPos N (headStart P) θ ∧
        cycPos N (headStart P) θ < max (cycPos N (headStart P) (rotLeg N (headStart P - 1) u))
        (cycPos N (headStart P) (rotLeg N (headStart P - 1) v)) := by
      rw [hpu, hpv]; omega
    rcases hm with hm | hm
    · exact disjoint_left.1 hΘd (pkCo_mem_sepIn.2 ⟨(pkCh_mem_missing.1 hm).1, hψuA, hψvA, hψuΘ, hψvΘ, θ, hθ,
        hθb⟩) hm
    · rw [min_comm, max_comm] at hθb
      exact disjoint_left.1 hΘd (pkCo_mem_sepIn.2 ⟨(pkCh_mem_missing.1 hm).1, hψvA, hψuA, hψvΘ, hψuΘ, θ, hθ,
        hθb⟩) hm
  -- the two O-runs
  obtain ⟨⟨p1, p2⟩, hp, ⟨q1, q2⟩, hq, ⟨hp1, hp2, -, -, hpR⟩, ⟨hq1, hq2, -, -, hqR⟩, hpq⟩ := hsp
  have hp1' : p1 ∈ cycArc N (headStart P) (headLen N P) := hp1
  have hp2' : p2 ∈ cycArc N (headStart P) (headLen N P) := hp2
  have hq1' : q1 ∈ cycArc N (headStart P) (headLen N P) := hq1
  have hq2' : q2 ∈ cycArc N (headStart P) (headLen N P) := hq2
  have hpR' : ¬ ∃ θ ∈ Θ, min (cycPos N (headStart P) p1) (cycPos N (headStart P) p2) < cycPos N (headStart P) θ ∧
      cycPos N (headStart P) θ < max (cycPos N (headStart P) p1) (cycPos N (headStart P) p2) := hpR
  have hqR' : ¬ ∃ θ ∈ Θ, min (cycPos N (headStart P) q1) (cycPos N (headStart P) q2) < cycPos N (headStart P) θ ∧
      cycPos N (headStart P) θ < max (cycPos N (headStart P) q1) (cycPos N (headStart P) q2) := hqR
  obtain ⟨θ, hθ, c1, c2⟩ : ∃ θ ∈ Θ, min (cycPos N (headStart P) p1) (cycPos N (headStart P) q1) <
      cycPos N (headStart P) θ ∧
      cycPos N (headStart P) θ < max (cycPos N (headStart P) p1) (cycPos N (headStart P) q1) := by
    by_contra hc
    exact hpq hc
  obtain ⟨hpM, hp1o, hp2o⟩ := pkCh_mem_Moo.1 hp
  obtain ⟨hqM, hq1o, hq2o⟩ := pkCh_mem_Moo.1 hq
  have hp1o' : p1 % 2 = 1 := hp1o
  have hp2o' : p2 % 2 = 1 := hp2o
  have hq1o' : q1 % 2 = 1 := hq1o
  have hq2o' : q2 % 2 = 1 := hq2o
  have hpd := mem_diagonals.1 (pkCh_mem_missing.1 hpM).1
  have hqd := mem_diagonals.1 (pkCh_mem_missing.1 hqM).1
  simp only at hpd hqd
  have hA := fun x (hx : x ∈ cycArc N (headStart P) (headLen N P)) =>
    (pkCo_mem_cycArc_pos hs (show headLen N P ≤ N by omega)).1 hx
  obtain ⟨hp1I, hp1k⟩ := hA p1 hp1'
  obtain ⟨hp2I, hp2k⟩ := hA p2 hp2'
  obtain ⟨hq1I, hq1k⟩ := hA q1 hq1'
  obtain ⟨hq2I, hq2k⟩ := hA q2 hq2'
  have hθI := hΘI θ hθ
  have m1 := pkCh_pos_mod hE hs hs2 hp1I
  have m2 := pkCh_pos_mod hE hs hs2 hp2I
  have m3 := pkCh_pos_mod hE hs hs2 hq1I
  have m4 := pkCh_pos_mod hE hs hs2 hq2I
  have m5 := pkCh_pos_mod hE hs hs2 hθI.1
  have e5 := hΘe θ hθ
  have np : ¬ (min (cycPos N (headStart P) p1) (cycPos N (headStart P) p2) < cycPos N (headStart P) θ ∧
      cycPos N (headStart P) θ < max (cycPos N (headStart P) p1) (cycPos N (headStart P) p2)) :=
    fun h => hpR' ⟨θ, hθ, h⟩
  have nq : ¬ (min (cycPos N (headStart P) q1) (cycPos N (headStart P) q2) < cycPos N (headStart P) θ ∧
      cycPos N (headStart P) θ < max (cycPos N (headStart P) q1) (cycPos N (headStart P) q2)) :=
    fun h => hqR' ⟨θ, hθ, h⟩
  have hpne : cycPos N (headStart P) p1 ≠ cycPos N (headStart P) p2 := fun h => by
    have := pkCo_cycPos_inj hs hp1I hp2I h; omega
  have hqne : cycPos N (headStart P) q1 ≠ cycPos N (headStart P) q2 := fun h => by
    have := pkCo_cycPos_inj hs hq1I hq2I h; omega
  have cp : ¬ pkCh_Cl N (headStart P) S (cycPos N (headStart P) p1 + 1) (cycPos N (headStart P) p2 + 1) := by
    have := pkCh_notCl hs hp1I hp2I hpM
    rw [pkCh_phi_eq hs, pkCh_phi_eq hs] at this
    exact this
  have cq : ¬ pkCh_Cl N (headStart P) S (cycPos N (headStart P) q1 + 1) (cycPos N (headStart P) q2 + 1) := by
    have := pkCh_notCl hs hq1I hq2I hqM
    rw [pkCh_phi_eq hs, pkCh_phi_eq hs] at this
    exact this
  have cp' := fun h => cp (pkCh_C_minmax pkCh_Cl_symm h)
  have cq' := fun h => cq (pkCh_C_minmax pkCh_Cl_symm h)
  have hθl : cycPos N (headStart P) θ + 1 ∈ Θ.image (rotLeg N (N + 1 - headStart P)) := by
    rw [← pkCh_phi_eq hs]; exact mem_image_of_mem _ hθ
  have core := pkCh_core (C := pkCh_Cl N (headStart P) S) pkCh_Cl_symm hE hk1 hkN (pkCh_HW hN hE hPo hPB)
    (pkCh_Hfail hN hE hP) (pkCh_HG hN hE hF hs hs2) _ (Θ.image (rotLeg N (N + 1 - headStart P))) rfl hΘl
    hΘle hΘlf
  rcases (show (max (cycPos N (headStart P) p1) (cycPos N (headStart P) p2) < cycPos N (headStart P) θ ∧
      cycPos N (headStart P) θ < min (cycPos N (headStart P) q1) (cycPos N (headStart P) q2)) ∨
      (max (cycPos N (headStart P) q1) (cycPos N (headStart P) q2) < cycPos N (headStart P) θ ∧
      cycPos N (headStart P) θ < min (cycPos N (headStart P) p1) (cycPos N (headStart P) p2)) by omega) with h | h
  · exact core (min (cycPos N (headStart P) p1 + 1) (cycPos N (headStart P) p2 + 1))
      (max (cycPos N (headStart P) p1 + 1) (cycPos N (headStart P) p2 + 1))
      (min (cycPos N (headStart P) q1 + 1) (cycPos N (headStart P) q2 + 1))
      (max (cycPos N (headStart P) q1 + 1) (cycPos N (headStart P) q2 + 1))
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      cp' cq' ⟨_, hθl, by omega, by omega⟩
  · exact core (min (cycPos N (headStart P) q1 + 1) (cycPos N (headStart P) q2 + 1))
      (max (cycPos N (headStart P) q1 + 1) (cycPos N (headStart P) q2 + 1))
      (min (cycPos N (headStart P) p1 + 1) (cycPos N (headStart P) p2 + 1))
      (max (cycPos N (headStart P) p1 + 1) (cycPos N (headStart P) p2 + 1))
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      cq' cp' ⟨_, hθl, by omega, by omega⟩

/-- `sorry` (pkgChain; consumes `threeSep_consecWit`) · **[D] Lemma 14.5** [v3 §14.3; BP §3.3]: a canonical chord
satisfies (Even-top′). -/
theorem evenTop {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {S : Finset (ℕ × ℕ)} (hF : InFpi N S) {P : ℕ × ℕ}
    (hP : IsMinimalChord N S P) : EvenTopP N S P := by
  rw [pkCh_evenTop_iff]
  intro Θ hΘ hΘe hΘd hsp
  exact pkCh_evenTop_gen hN (Nat.even_iff.1 hE) hF hP hΘ hΘe hΘd hsp

/-! ### Sub-wave b (start of [Bot]): the lift of BP App. D §6c -/

theorem pkCh_sameRun_iff {N s : ℕ} {Θ : Finset ℕ} {u v : ℕ} :
    SameRun N s Θ u v ↔ ¬ ∃ θ ∈ Θ, min (cycPos N s u) (cycPos N s v) < cycPos N s θ ∧
      cycPos N s θ < max (cycPos N s u) (cycPos N s v) := Iff.rfl

theorem pkCh_inOneRun_iff {N s k : ℕ} {Θ : Finset ℕ} {p : ℕ × ℕ} :
    InOneRun N s k Θ p ↔ p.1 ∈ cycArc N s k ∧ p.2 ∈ cycArc N s k ∧ p.1 ∉ Θ ∧ p.2 ∉ Θ ∧ SameRun N s Θ p.1 p.2 :=
  Iff.rfl

theorem pkCh_spread_iff {N : ℕ} {S : Finset (ℕ × ℕ)} {s k : ℕ} {Θ : Finset ℕ} :
    Spread N S s k Θ ↔ ∃ p ∈ Moo N S, ∃ p' ∈ Moo N S, InOneRun N s k Θ p ∧ InOneRun N s k Θ p' ∧
      ¬ SameRun N s Θ p.1 p'.1 := Iff.rfl

/-- A head inside another head is a position interval `[a, a + k)` of the bigger head. -/
theorem pkCh_subHead {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {P Ps : ℕ × ℕ} (hPo : P ∈ oddDiagonals N)
    (hPso : Ps ∈ oddDiagonals N) (hsub : oddSide N P ⊆ oddSide N Ps) :
    cycPos N (headStart Ps) (headStart P) + headLen N P ≤ headLen N Ps ∧
      cycPos N (headStart Ps) (headStart P) % 2 = 0 ∧
      (∀ x ∈ Icc 1 N, x ∈ oddSide N P ↔ cycPos N (headStart Ps) (headStart P) ≤ cycPos N (headStart Ps) x ∧
        cycPos N (headStart Ps) x < cycPos N (headStart Ps) (headStart P) + headLen N P) ∧
      (∀ x ∈ Icc 1 N, cycPos N (headStart Ps) (headStart P) ≤ cycPos N (headStart Ps) x →
        cycPos N (headStart P) x = cycPos N (headStart Ps) x - cycPos N (headStart Ps) (headStart P)) := by
  obtain ⟨-, -, -, -, -, hs, hs2, hk1, hk3, hkN⟩ := pkCh_sides hE hPo
  obtain ⟨-, -, -, -, -, hss, hss2, hks1, hks3, hksN⟩ := pkCh_sides hE hPso
  have hN1 : 1 ≤ N := by omega
  have ha := pkCo_cycPos_lt hN1 (headStart Ps) (headStart P)
  have hpar := pkCo_cycPos_mod_two hE hss hs
  have hv : vtx N (headStart Ps + cycPos N (headStart Ps) (headStart P)) = headStart P := pkCo_vtx_cycPos hss hs
  have hshift : ∀ x ∈ Icc 1 N, cycPos N (headStart P) x =
      if cycPos N (headStart Ps) (headStart P) ≤ cycPos N (headStart Ps) x then
        cycPos N (headStart Ps) x - cycPos N (headStart Ps) (headStart P)
      else cycPos N (headStart Ps) x + N - cycPos N (headStart Ps) (headStart P) := fun x hx => by
    rw [← pkCh_pos_shift hss hx ha, hv]
  -- the leg at position `N − 1` is not in the big head
  have hbound : cycPos N (headStart Ps) (headStart P) + headLen N P ≤ headLen N Ps := by
    by_contra hc
    -- a leg of `A_P` with big position `≥ headLen Ps`
    have hm : cycPos N (headStart Ps) (headStart P) + headLen N P - 1 < N ∨
        N ≤ cycPos N (headStart Ps) (headStart P) + headLen N P - 1 := by omega
    rcases hm with hm | hm
    · have hxI := mem_Icc.2 (vtx_bounds N (headStart Ps + (cycPos N (headStart Ps) (headStart P) + headLen N P - 1)) hN1)
      have hp := pkCo_cycPos_vtx hss hm
      have hin : vtx N (headStart Ps + (cycPos N (headStart Ps) (headStart P) + headLen N P - 1)) ∈ oddSide N P := by
        rw [pkCh_headpos hN hE hPo, hshift _ hxI, hp]
        exact ⟨hxI, by split_ifs <;> omega⟩
      have := (pkCh_headpos hN hE hPso).1 (hsub hin)
      rw [hp] at this
      omega
    · have hxI := mem_Icc.2 (vtx_bounds N (headStart Ps + (N - 1)) hN1)
      have hp := pkCo_cycPos_vtx hss (show N - 1 < N by omega)
      have hin : vtx N (headStart Ps + (N - 1)) ∈ oddSide N P := by
        rw [pkCh_headpos hN hE hPo, hshift _ hxI, hp]
        exact ⟨hxI, by split_ifs <;> omega⟩
      have := (pkCh_headpos hN hE hPso).1 (hsub hin)
      rw [hp] at this
      omega
  refine ⟨hbound, by omega, fun x hx => ?_, fun x hx h => by rw [hshift x hx, if_pos h]⟩
  rw [pkCh_headpos hN hE hPo, hshift x hx]
  have := pkCo_cycPos_lt hN1 (headStart Ps) x
  constructor
  · rintro ⟨-, h⟩
    split_ifs at h with h' <;> omega
  · rintro ⟨h1, h2⟩
    exact ⟨hx, by rw [if_pos h1]; omega⟩

/-- **The lift** (BP App. D §6c): a spread failing even trace `Θ` of the head of `P` (inside the head of `P*`, with
`o_in(P*) ⊆ o_in(P)`, `P ∈ 𝒫₀`) gives the spread failing even trace `Θ ∪ evens(A* ∖ A_P)` of the head of `P*`. No F^π. -/
theorem pkCh_lift {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} {P Ps : ℕ × ℕ}
    (hP : P ∈ cleanChords N S) (hPso : Ps ∈ oddDiagonals N) (hsub : oddSide N P ⊆ oddSide N Ps)
    (hoo : innerOO N S Ps ⊆ innerOO N S P) {Θ : Finset ℕ} (hΘ : Θ ∈ admSeps N (headStart P) (headLen N P) 0)
    (hΘe : ∀ θ ∈ Θ, θ % 2 = 0) (hΘd : Disjoint (sepIn N (headStart P) (headLen N P) Θ) (missing N S))
    (hsp : Spread N S (headStart P) (headLen N P) Θ) :
    ∃ Θ' ∈ admSeps N (headStart Ps) (headLen N Ps) 0, (∀ θ ∈ Θ', θ % 2 = 0) ∧
      Disjoint (sepIn N (headStart Ps) (headLen N Ps) Θ') (missing N S) ∧
      Spread N S (headStart Ps) (headLen N Ps) Θ' := by
  have hPo : P ∈ oddDiagonals N := (mem_filter.1 hP).1
  have hPc : Disjoint (minRect N P) (missing N S) := (mem_filter.1 hP).2
  obtain ⟨-, -, -, -, -, hs, hs2, hk1, hk3, hkN⟩ := pkCh_sides hE hPo
  obtain ⟨-, -, -, -, -, hss, hss2, hks1, hks3, hksN⟩ := pkCh_sides hE hPso
  have hN1 : 1 ≤ N := by omega
  obtain ⟨hab, ha2, hmemP, hposP⟩ := pkCh_subHead hN hE hPo hPso hsub
  obtain ⟨hΘsub, hΘc⟩ := pkCo_mem_admSeps.1 hΘ
  have hΘI : ∀ θ ∈ Θ, θ ∈ Icc 1 N ∧ 1 ≤ cycPos N (headStart P) θ ∧ cycPos N (headStart P) θ + 2 ≤ headLen N P :=
    fun θ h => (pkCo_mem_intArc hs (by omega)).1 (hΘsub h)
  -- positions of `Θ` in the big head
  have hΘpos : ∀ θ ∈ Θ, cycPos N (headStart Ps) (headStart P) + 1 ≤ cycPos N (headStart Ps) θ ∧
      cycPos N (headStart Ps) θ + 2 ≤ cycPos N (headStart Ps) (headStart P) + headLen N P ∧
      cycPos N (headStart P) θ = cycPos N (headStart Ps) θ - cycPos N (headStart Ps) (headStart P) := by
    intro θ hθ
    obtain ⟨hθI, h1, h2⟩ := hΘI θ hθ
    have hin : θ ∈ oddSide N P := (pkCh_headpos hN hE hPo).2 ⟨hθI, by omega⟩
    obtain ⟨g1, g2⟩ := (hmemP θ hθI).1 hin
    have e := hposP θ hθI g1
    rw [e] at h1 h2
    exact ⟨by omega, by omega, e⟩
  -- the added legs
  have hbig : ∀ x, x ∈ oddSide N Ps ↔ x ∈ Icc 1 N ∧ cycPos N (headStart Ps) x < headLen N Ps :=
    fun x => pkCh_headpos hN hE hPso
  have hmemU : ∀ x, x ∈ Θ ∪ (Icc 1 N).filter (fun x => cycPos N (headStart Ps) x < headLen N Ps ∧
      ¬ (cycPos N (headStart Ps) (headStart P) ≤ cycPos N (headStart Ps) x ∧
        cycPos N (headStart Ps) x < cycPos N (headStart Ps) (headStart P) + headLen N P) ∧ x % 2 = 0) ↔
      x ∈ Θ ∨ (x ∈ Icc 1 N ∧ cycPos N (headStart Ps) x < headLen N Ps ∧
        ¬ (cycPos N (headStart Ps) (headStart P) ≤ cycPos N (headStart Ps) x ∧
          cycPos N (headStart Ps) x < cycPos N (headStart Ps) (headStart P) + headLen N P) ∧ x % 2 = 0) := by
    intro x; rw [mem_union, mem_filter]
  have hparS : ∀ x ∈ Icc 1 N, cycPos N (headStart Ps) x % 2 = (x + headStart Ps) % 2 :=
    fun x hx => pkCo_cycPos_mod_two hE hss hx
  have hΘin : ∀ θ ∈ Θ, θ ∈ oddSide N P := fun θ hθ => by
    obtain ⟨hθI, h1, h2⟩ := hΘI θ hθ
    exact (pkCh_headpos hN hE hPo).2 ⟨hθI, by omega⟩
  have hbigA : ∀ x, x ∈ cycArc N (headStart Ps) (headLen N Ps) ↔ x ∈ Icc 1 N ∧ cycPos N (headStart Ps) x < headLen N Ps :=
    fun x => pkCo_mem_cycArc_pos hss (by omega)
  have hsmA : ∀ x, x ∈ cycArc N (headStart P) (headLen N P) ↔ x ∈ oddSide N P :=
    fun x => ((pkCh_arcs (by omega) hE hPo).1 x).symm
  -- the key claim for pairs with a leg outside `A_P`
  have hout : ∀ x y, x ∈ Icc 1 N → y ∈ Icc 1 N → cycPos N (headStart Ps) x < headLen N Ps →
      cycPos N (headStart Ps) y < headLen N Ps → x ∉ oddSide N P →
      x ∉ Θ ∪ (Icc 1 N).filter (fun x => cycPos N (headStart Ps) x < headLen N Ps ∧
        ¬ (cycPos N (headStart Ps) (headStart P) ≤ cycPos N (headStart Ps) x ∧
          cycPos N (headStart Ps) x < cycPos N (headStart Ps) (headStart P) + headLen N P) ∧ x % 2 = 0) →
      y ∉ Θ ∪ (Icc 1 N).filter (fun x => cycPos N (headStart Ps) x < headLen N Ps ∧
        ¬ (cycPos N (headStart Ps) (headStart P) ≤ cycPos N (headStart Ps) x ∧
          cycPos N (headStart Ps) x < cycPos N (headStart Ps) (headStart P) + headLen N P) ∧ x % 2 = 0) →
      (min x y, max x y) ∉ missing N S := by
    intro x y hx hy hxK hyK hxP hxU hyU hm
    rw [hmemU] at hxU hyU
    have hxin : ¬ (cycPos N (headStart Ps) (headStart P) ≤ cycPos N (headStart Ps) x ∧
        cycPos N (headStart Ps) x < cycPos N (headStart Ps) (headStart P) + headLen N P) :=
      fun h => hxP ((hmemP x hx).2 h)
    have hx2 : x % 2 = 1 := by
      by_contra h
      exact hxU (Or.inr ⟨hx, hxK, hxin, by omega⟩)
    by_cases hy2 : y % 2 = 1
    · have hmoo : (min x y, max x y) ∈ innerOO N S Ps := by
        refine pkCh_mem_innerOO.2 ⟨pkCh_mem_Moo.2 ⟨hm, ?_, ?_⟩, ?_, ?_⟩
        · show min x y % 2 = 1
          rcases le_total x y with h | h
          · rw [min_eq_left h]; exact hx2
          · rw [min_eq_right h]; exact hy2
        · show max x y % 2 = 1
          rcases le_total x y with h | h
          · rw [max_eq_right h]; exact hy2
          · rw [max_eq_left h]; exact hx2
        · show min x y ∈ oddSide N Ps
          rcases le_total x y with h | h
          · rw [min_eq_left h]; exact (hbig x).2 ⟨hx, hxK⟩
          · rw [min_eq_right h]; exact (hbig y).2 ⟨hy, hyK⟩
        · show max x y ∈ oddSide N Ps
          rcases le_total x y with h | h
          · rw [max_eq_right h]; exact (hbig y).2 ⟨hy, hyK⟩
          · rw [max_eq_left h]; exact (hbig x).2 ⟨hx, hxK⟩
      obtain ⟨-, h1, h2⟩ := pkCh_mem_innerOO.1 (hoo hmoo)
      rcases le_total x y with h | h
      · rw [min_eq_left h] at h1; exact hxP h1
      · rw [max_eq_left h] at h2; exact hxP h2
    · have hyin : cycPos N (headStart Ps) (headStart P) ≤ cycPos N (headStart Ps) y ∧
          cycPos N (headStart Ps) y < cycPos N (headStart Ps) (headStart P) + headLen N P := by
        by_contra h
        exact hyU (Or.inr ⟨hy, hyK, h, by omega⟩)
      have hyP := (hmemP y hy).2 hyin
      have hxB : x ∈ evenSide N P := by
        show x ∈ Icc 1 N \ oddSide N P
        exact mem_sdiff.2 ⟨hx, hxP⟩
      apply disjoint_left.1 hPc _ hm
      refine pkCh_mem_minRect.2 ⟨y, pkCh_mem_evens.2 ⟨hyP, by omega⟩, x, pkCh_mem_odds.2 ⟨hxB, hx2⟩, ?_⟩
      rw [min_comm, max_comm]
  refine ⟨Θ ∪ (Icc 1 N).filter (fun x => cycPos N (headStart Ps) x < headLen N Ps ∧
      ¬ (cycPos N (headStart Ps) (headStart P) ≤ cycPos N (headStart Ps) x ∧
        cycPos N (headStart Ps) x < cycPos N (headStart Ps) (headStart P) + headLen N P) ∧ x % 2 = 0), ?_, ?_, ?_, ?_⟩
  · rw [pkCo_mem_admSeps]
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [pkCo_mem_intArc hss (by omega)]
      rcases (hmemU x).1 hx with h | ⟨hxI, h1, h2, h3⟩
      · obtain ⟨g1, g2, -⟩ := hΘpos x h
        exact ⟨(hΘI x h).1, by omega, by omega⟩
      · have := hparS x hxI
        exact ⟨hxI, by omega, by omega⟩
    · by_cases hEne : ((Icc 1 N).filter (fun x => cycPos N (headStart Ps) x < headLen N Ps ∧
          ¬ (cycPos N (headStart Ps) (headStart P) ≤ cycPos N (headStart Ps) x ∧
            cycPos N (headStart Ps) x < cycPos N (headStart Ps) (headStart P) + headLen N P) ∧ x % 2 = 0)).Nonempty
      · right
        obtain ⟨e, he⟩ := hEne
        obtain ⟨θ, hθ⟩ : Θ.Nonempty := by
          rcases hΘc with h | h
          · exact card_pos.1 (by omega)
          · exact card_pos.1 (by omega)
        refine ⟨one_lt_card.2 ⟨θ, mem_union_left _ hθ, e, mem_union_right _ he, fun h => ?_⟩, fun x hx => ?_⟩
        · rw [← h] at he
          obtain ⟨-, -, h2, -⟩ := mem_filter.1 he
          obtain ⟨g1, g2, -⟩ := hΘpos θ hθ
          exact h2 ⟨by omega, by omega⟩
        · rcases (hmemU x).1 hx with h | ⟨-, -, -, h3⟩
          · exact hΘe x h
          · exact h3
      · rw [not_nonempty_iff_eq_empty.1 hEne, union_empty]
        exact hΘc
  · intro x hx
    rcases (hmemU x).1 hx with h | ⟨-, -, -, h3⟩
    · exact hΘe x h
    · exact h3
  · refine disjoint_left.2 fun p hp hpm => ?_
    obtain ⟨p1, p2⟩ := p
    obtain ⟨hpd, hp1, hp2, hp1U, hp2U, θ, hθ, b1, b2⟩ := pkCo_mem_sepIn.1 hp
    simp only at hp1 hp2 hp1U hp2U b1 b2
    have hpd' := mem_diagonals.1 hpd
    simp only at hpd'
    obtain ⟨hp1I, hp1K⟩ := (hbigA p1).1 hp1
    obtain ⟨hp2I, hp2K⟩ := (hbigA p2).1 hp2
    have e12 : (min p1 p2, max p1 p2) = (p1, p2) := by rw [min_eq_left (by omega), max_eq_right (by omega)]
    by_cases hin1 : p1 ∈ oddSide N P
    · by_cases hin2 : p2 ∈ oddSide N P
      · obtain ⟨i1, i1'⟩ := (hmemP p1 hp1I).1 hin1
        obtain ⟨i2, i2'⟩ := (hmemP p2 hp2I).1 hin2
        have hθΘ : θ ∈ Θ := by
          rcases (hmemU θ).1 hθ with h | ⟨-, -, h2, -⟩
          · exact h
          · exact absurd ⟨by omega, by omega⟩ h2
        obtain ⟨g1, g2, g3⟩ := hΘpos θ hθΘ
        apply disjoint_left.1 hΘd _ hpm
        refine pkCo_mem_sepIn.2 ⟨hpd, (hsmA p1).2 hin1, (hsmA p2).2 hin2, fun h => hp1U (mem_union_left _ h),
          fun h => hp2U (mem_union_left _ h), θ, hθΘ, ?_, ?_⟩ <;>
          simp only <;> rw [hposP p1 hp1I i1, hposP p2 hp2I i2, g3] <;> omega
      · rw [← e12] at hpm
        rw [min_comm, max_comm] at hpm
        exact hout p2 p1 hp2I hp1I hp2K hp1K hin2 hp2U hp1U hpm
    · rw [← e12] at hpm
      exact hout p1 p2 hp1I hp2I hp1K hp2K hin1 hp1U hp2U hpm
  · obtain ⟨⟨p1, p2⟩, hp, ⟨q1, q2⟩, hq, hpr, hqr, hpq⟩ := pkCh_spread_iff.1 hsp
    obtain ⟨hp1, hp2, hp1Θ, hp2Θ, hpR⟩ := pkCh_inOneRun_iff.1 hpr
    obtain ⟨hq1, hq2, hq1Θ, hq2Θ, hqR⟩ := pkCh_inOneRun_iff.1 hqr
    simp only at hp1 hp2 hp1Θ hp2Θ hpR hq1 hq2 hq1Θ hq2Θ hqR hpq
    have lift1 : ∀ x ∈ cycArc N (headStart P) (headLen N P), x ∉ Θ →
        x ∈ cycArc N (headStart Ps) (headLen N Ps) ∧ x ∉ Θ ∪ (Icc 1 N).filter (fun x =>
          cycPos N (headStart Ps) x < headLen N Ps ∧
          ¬ (cycPos N (headStart Ps) (headStart P) ≤ cycPos N (headStart Ps) x ∧
            cycPos N (headStart Ps) x < cycPos N (headStart Ps) (headStart P) + headLen N P) ∧ x % 2 = 0) ∧
          x ∈ Icc 1 N ∧ cycPos N (headStart Ps) (headStart P) ≤ cycPos N (headStart Ps) x ∧
          cycPos N (headStart Ps) x < cycPos N (headStart Ps) (headStart P) + headLen N P := by
      intro x hx hxΘ
      have hxP := (hsmA x).1 hx
      have hxI := ((pkCh_headpos hN hE hPo).1 hxP).1
      obtain ⟨i1, i2⟩ := (hmemP x hxI).1 hxP
      refine ⟨((pkCh_arcs (by omega) hE hPso).1 x).1 (hsub hxP), fun h => ?_, hxI, i1, i2⟩
      rcases (hmemU x).1 h with h | ⟨-, -, h2, -⟩
      · exact hxΘ h
      · exact h2 ⟨i1, i2⟩
    obtain ⟨a1, a1U, a1I, a1a, a1b⟩ := lift1 p1 hp1 hp1Θ
    obtain ⟨a2, a2U, a2I, a2a, a2b⟩ := lift1 p2 hp2 hp2Θ
    obtain ⟨c1, c1U, c1I, c1a, c1b⟩ := lift1 q1 hq1 hq1Θ
    obtain ⟨c2, c2U, c2I, c2a, c2b⟩ := lift1 q2 hq2 hq2Θ
    have sr : ∀ u v, u ∈ Icc 1 N → v ∈ Icc 1 N → cycPos N (headStart Ps) (headStart P) ≤ cycPos N (headStart Ps) u →
        cycPos N (headStart Ps) u < cycPos N (headStart Ps) (headStart P) + headLen N P →
        cycPos N (headStart Ps) (headStart P) ≤ cycPos N (headStart Ps) v →
        cycPos N (headStart Ps) v < cycPos N (headStart Ps) (headStart P) + headLen N P →
        SameRun N (headStart P) Θ u v → SameRun N (headStart Ps) (Θ ∪ (Icc 1 N).filter (fun x =>
          cycPos N (headStart Ps) x < headLen N Ps ∧
          ¬ (cycPos N (headStart Ps) (headStart P) ≤ cycPos N (headStart Ps) x ∧
            cycPos N (headStart Ps) x < cycPos N (headStart Ps) (headStart P) + headLen N P) ∧ x % 2 = 0)) u v := by
      intro u v hu hv u1 u2 v1 v2 h
      rw [pkCh_sameRun_iff] at h ⊢
      rintro ⟨θ, hθ, b1, b2⟩
      rcases (hmemU θ).1 hθ with h' | ⟨-, -, h2, -⟩
      · obtain ⟨g1, g2, g3⟩ := hΘpos θ h'
        refine h ⟨θ, h', ?_, ?_⟩ <;> rw [hposP u hu u1, hposP v hv v1, g3] <;> omega
      · exact h2 ⟨by omega, by omega⟩
    refine pkCh_spread_iff.2 ⟨(p1, p2), hp, (q1, q2), hq, pkCh_inOneRun_iff.2 ⟨a1, a2, a1U, a2U,
      sr p1 p2 a1I a2I a1a a1b a2a a2b hpR⟩, pkCh_inOneRun_iff.2 ⟨c1, c2, c1U, c2U,
      sr q1 q2 c1I c2I c1a c1b c2a c2b hqR⟩, ?_⟩
    simp only
    rw [pkCh_sameRun_iff, not_not]
    rw [pkCh_sameRun_iff, not_not] at hpq
    obtain ⟨θ, hθ, b1, b2⟩ := hpq
    obtain ⟨g1, g2, g3⟩ := hΘpos θ hθ
    rw [hposP p1 a1I a1a, hposP q1 c1I c1a, g3] at b1 b2
    exact ⟨θ, mem_union_left _ hθ, by omega, by omega⟩

/-! ### Sub-wave c: [Bot] (BP App. D §6d) -/

/-- A failing even head trace read in the linear setting of the head (labels `cycPos + 1`). -/
theorem pkCh_toLin {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ}
    (hPo : P ∈ oddDiagonals N) {Θ : Finset ℕ} (hΘ : Θ ∈ admSeps N (headStart P) (headLen N P) 0)
    (hΘe : ∀ θ ∈ Θ, θ % 2 = 0) (hΘd : Disjoint (sepIn N (headStart P) (headLen N P) Θ) (missing N S)) :
    Θ.image (rotLeg N (N + 1 - headStart P)) ⊆ Icc 2 (headLen N P - 1) ∧
      (∀ t ∈ Θ.image (rotLeg N (N + 1 - headStart P)), t % 2 = 0) ∧
      (∀ u v, runSepA (headLen N P) (Θ.image (rotLeg N (N + 1 - headStart P))) u v →
        pkCh_Cl N (headStart P) S u v) := by
  obtain ⟨-, -, -, -, -, hs, hs2, hk1, hk3, hkN⟩ := pkCh_sides hE hPo
  have hN1 : 1 ≤ N := by omega
  obtain ⟨hΘsub, -⟩ := pkCo_mem_admSeps.1 hΘ
  have hΘI : ∀ θ ∈ Θ, θ ∈ Icc 1 N ∧ 1 ≤ cycPos N (headStart P) θ ∧
      cycPos N (headStart P) θ + 2 ≤ headLen N P := fun θ h => (pkCo_mem_intArc hs (by omega)).1 (hΘsub h)
  have hΘl : Θ.image (rotLeg N (N + 1 - headStart P)) ⊆ Icc 2 (headLen N P - 1) := fun y hy => by
    obtain ⟨θ, hθ, rfl⟩ := mem_image.1 hy
    have := hΘI θ hθ
    rw [pkCh_phi_eq hs, mem_Icc]
    omega
  have hΘle : ∀ t ∈ Θ.image (rotLeg N (N + 1 - headStart P)), t % 2 = 0 := fun y hy => by
    obtain ⟨θ, hθ, rfl⟩ := mem_image.1 hy
    rw [pkCh_phi_eq hs, pkCh_pos_mod hE hs hs2 (hΘI θ hθ).1]
    exact hΘe θ hθ
  have hΘlf : ∀ u v, runSepA (headLen N P) (Θ.image (rotLeg N (N + 1 - headStart P))) u v →
      pkCh_Cl N (headStart P) S u v := by
    intro u v h
    obtain ⟨hu, hv, huΘ, hvΘ, t, ht, b1, b2⟩ := pkT_runSepA_iff.1 h
    obtain ⟨θ, hθ, rfl⟩ := mem_image.1 ht
    rw [pkCh_Cl_iff]
    rintro ⟨huI, hvI, hm⟩
    have hu' := mem_Icc.1 hu
    have hv' := mem_Icc.1 hv
    have hpu := pkCh_psi_pos hs huI
    have hpv := pkCh_psi_pos hs hvI
    have hψuA : rotLeg N (headStart P - 1) u ∈ cycArc N (headStart P) (headLen N P) :=
      (pkCo_mem_cycArc_pos hs (by omega)).2 ⟨pkCh_psi_mem hN1 u, by omega⟩
    have hψvA : rotLeg N (headStart P - 1) v ∈ cycArc N (headStart P) (headLen N P) :=
      (pkCo_mem_cycArc_pos hs (by omega)).2 ⟨pkCh_psi_mem hN1 v, by omega⟩
    have hψuΘ : rotLeg N (headStart P - 1) u ∉ Θ := fun h => huΘ (by
      rw [← pkCh_phi_psi hs huI]; exact mem_image_of_mem _ h)
    have hψvΘ : rotLeg N (headStart P - 1) v ∉ Θ := fun h => hvΘ (by
      rw [← pkCh_phi_psi hs hvI]; exact mem_image_of_mem _ h)
    rw [pkCh_phi_eq hs] at b1 b2
    have hθb : min (cycPos N (headStart P) (rotLeg N (headStart P - 1) u))
        (cycPos N (headStart P) (rotLeg N (headStart P - 1) v)) < cycPos N (headStart P) θ ∧
        cycPos N (headStart P) θ < max (cycPos N (headStart P) (rotLeg N (headStart P - 1) u))
        (cycPos N (headStart P) (rotLeg N (headStart P - 1) v)) := by
      rw [hpu, hpv]; omega
    rcases hm with hm | hm
    · exact disjoint_left.1 hΘd (pkCo_mem_sepIn.2 ⟨(pkCh_mem_missing.1 hm).1, hψuA, hψvA, hψuΘ, hψvΘ, θ, hθ,
        hθb⟩) hm
    · rw [min_comm, max_comm] at hθb
      exact disjoint_left.1 hΘd (pkCo_mem_sepIn.2 ⟨(pkCh_mem_missing.1 hm).1, hψvA, hψuA, hψvΘ, hψuΘ, θ, hθ,
        hθb⟩) hm
  exact ⟨hΘl, hΘle, hΘlf⟩

/-- **[L0]** (BP App. D §7) for any `P ∈ 𝒫₁`, linear setting of its head: the run chord of an O-run `[a, b]` of a
failing even trace is in `𝒫₁`; its head is the label interval `[a, b]`. -/
theorem pkCh_L0 {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ}
    (hPp : P ∈ poleChords N S) {Θ : Finset ℕ} (hΘ : Θ ⊆ Icc 2 (headLen N P - 1)) (hΘe : ∀ θ ∈ Θ, θ % 2 = 0)
    (hΘf : ∀ u v, runSepA (headLen N P) Θ u v → pkCh_Cl N (headStart P) S u v) {a b : ℕ}
    (hR : IsRun (headLen N P) Θ a b)
    (huv : ∃ u v, a ≤ u ∧ u < v ∧ v ≤ b ∧ u % 2 = 1 ∧ v % 2 = 1 ∧ ¬ pkCh_Cl N (headStart P) S u v) :
    ∃ Q ∈ poleChords N S, ∀ x, x ∈ oddSide N Q ↔ x ∈ Icc 1 N ∧
      a ≤ cycPos N (headStart P) x + 1 ∧ cycPos N (headStart P) x + 1 ≤ b := by
  obtain ⟨u, v, hau, huv, hvb, hu2, hv2, huvC⟩ := huv
  obtain ⟨hPo, hPclean, hPee, -⟩ := pkCh_mem_pole.1 hPp
  obtain ⟨-, -, -, -, -, hs, hs2, hk1, hk3, hkN⟩ := pkCh_sides hE hPo
  obtain ⟨ha1, hab, hbk, haΘ, hbΘ, hRΘ⟩ := pkCh_isRun_iff.1 hR
  have hN1 : 1 ≤ N := by omega
  have hsI := mem_Icc.1 hs
  have hΘI : ∀ θ ∈ Θ, 2 ≤ θ ∧ θ ≤ headLen N P - 1 := fun θ h => mem_Icc.1 (hΘ h)
  have ha2 : a % 2 = 1 := by
    rcases haΘ with h | h
    · omega
    · have := hΘe _ h; have := hΘI _ h; omega
  have hb2 : b % 2 = 1 := by
    rcases hbΘ with h | h
    · omega
    · have := hΘe _ h; omega
  have hr2 : rotLeg N (headStart P - 1) (b + 1) % 2 = 0 := by
    rw [pkCh_psi_mod hN1 hE hsI.1 hs2]; omega
  obtain ⟨Q, hQo, hQts, hQtl⟩ := pkCh_mkTail (l := N - (b + 1 - a)) hE (pkCh_psi_mem hN1 (b + 1)) hr2
    (by omega) (by omega) (by omega)
  have hQtsI : tailStart Q ∈ Icc 1 N := by rw [hQts]; exact pkCh_psi_mem hN1 _
  have hQts' : tailStart Q = vtx N (headStart P + b) := by
    rw [hQts]
    show vtx N (b + 1 + (headStart P - 1)) = vtx N (headStart P + b)
    rw [show b + 1 + (headStart P - 1) = headStart P + b by omega]
  have hposQ : ∀ x ∈ Icc 1 N, cycPos N (tailStart Q) x = if b ≤ cycPos N (headStart P) x then
      cycPos N (headStart P) x - b else cycPos N (headStart P) x + N - b := fun x hx => by
    rw [hQts']; exact pkCh_pos_shift hs hx (by omega)
  have hevQ : ∀ x, x ∈ evenSide N Q ↔ x ∈ Icc 1 N ∧
      (cycPos N (headStart P) x + 1 < a ∨ b < cycPos N (headStart P) x + 1) := by
    intro x
    rw [pkCh_mem_even (by omega) hE hQo, hQtl]
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
  have hodQ : ∀ x, x ∈ oddSide N Q ↔ x ∈ Icc 1 N ∧
      a ≤ cycPos N (headStart P) x + 1 ∧ cycPos N (headStart P) x + 1 ≤ b := by
    intro x
    rw [pkCh_mem_odd (by omega) hE hQo, hQtl]
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
  -- [L0]: `Q ∈ 𝒫₁`
  have hQpole : Q ∈ poleChords N S := by
    refine pkCh_mem_pole.2 ⟨hQo, disjoint_left.2 fun p hp hpm => ?_, ?_, ?_⟩
    · obtain ⟨e, he, o, ho, rfl⟩ := pkCh_mem_minRect.1 hp
      obtain ⟨heQ, he2⟩ := pkCh_mem_evens.1 he
      obtain ⟨hoQ, ho2⟩ := pkCh_mem_odds.1 ho
      obtain ⟨heI, hea, heb⟩ := (hodQ e).1 heQ
      obtain ⟨hoI, hob⟩ := (hevQ o).1 hoQ
      have hepos := pkCh_pos_mod hE hs hs2 heI
      have hopos := pkCh_pos_mod hE hs hs2 hoI
      by_cases hok : headLen N P ≤ cycPos N (headStart P) o
      · apply disjoint_left.1 hPclean _ hpm
        exact pkCh_mem_minRect.2 ⟨e, pkCh_mem_evens.2 ⟨(pkCh_headpos hN hE hPo).2 ⟨heI, by omega⟩, he2⟩, o,
          pkCh_mem_odds.2 ⟨(pkCh_evenpos hN hE hPo).2 ⟨hoI, hok⟩, ho2⟩, rfl⟩
      · apply pkCh_notCl_mm hs heI hoI hpm
        apply hΘf
        rw [pkCh_phi_eq hs, pkCh_phi_eq hs, pkT_runSepA_iff]
        have hoΘ : cycPos N (headStart P) o + 1 ∉ Θ := fun h => by have := hΘe _ h; omega
        have heΘ : cycPos N (headStart P) e + 1 ∉ Θ := fun h => hRΘ _ (mem_Icc.2 ⟨hea, heb⟩) h
        refine ⟨mem_Icc.2 ⟨by omega, by omega⟩, mem_Icc.2 ⟨by omega, by omega⟩, heΘ, hoΘ, ?_⟩
        rcases hob with h | h
        · have ha' : a - 1 ∈ Θ := by
            rcases haΘ with h' | h'
            · omega
            · exact h'
          have := hΘe _ ha'
          exact ⟨a - 1, ha', by omega, by omega⟩
        · have hb' : b + 1 ∈ Θ := by
            rcases hbΘ with h' | h'
            · omega
            · exact h'
          have := hΘe _ hb'
          exact ⟨b + 1, hb', by omega, by omega⟩
    · obtain ⟨⟨g1, g2⟩, hg⟩ := hPee
      obtain ⟨hgM, hg1, hg2⟩ := pkCh_mem_innerEE.1 hg
      have h1 := (pkCh_evenpos hN hE hPo).1 hg1
      have h2 := (pkCh_evenpos hN hE hPo).1 hg2
      exact ⟨(g1, g2), pkCh_mem_innerEE.2 ⟨hgM, (hevQ _).2 ⟨h1.1, Or.inr (by omega)⟩,
        (hevQ _).2 ⟨h2.1, Or.inr (by omega)⟩⟩⟩
    · rw [pkCh_Cl_iff, not_not] at huvC
      obtain ⟨huI, hvI, hm⟩ := huvC
      have hψu := pkCh_psi_pos hs huI
      have hψv := pkCh_psi_pos hs hvI
      have hmu := pkCh_psi_mod hN1 hE hsI.1 hs2 u
      have hmv := pkCh_psi_mod hN1 hE hsI.1 hs2 v
      have hoU : rotLeg N (headStart P - 1) u ∈ oddSide N Q :=
        (hodQ _).2 ⟨pkCh_psi_mem hN1 u, by omega, by omega⟩
      have hoV : rotLeg N (headStart P - 1) v ∈ oddSide N Q :=
        (hodQ _).2 ⟨pkCh_psi_mem hN1 v, by omega, by omega⟩
      rcases hm with hm | hm
      · exact ⟨_, pkCh_mem_innerOO.2 ⟨pkCh_mem_Moo.2 ⟨hm, (by omega : rotLeg N (headStart P - 1) u % 2 = 1),
          (by omega : rotLeg N (headStart P - 1) v % 2 = 1)⟩, hoU, hoV⟩⟩
      · exact ⟨_, pkCh_mem_innerOO.2 ⟨pkCh_mem_Moo.2 ⟨hm, (by omega : rotLeg N (headStart P - 1) v % 2 = 1),
          (by omega : rotLeg N (headStart P - 1) u % 2 = 1)⟩, hoV, hoU⟩⟩
  exact ⟨Q, hQpole, hodQ⟩


end PiZ
