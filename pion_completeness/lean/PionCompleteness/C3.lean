import PionCompleteness.C2

namespace PiZ

open Finset R12P1 R12P4A R12P3 R12P3C

/-- Class members have the same `o_in` (cut dictionary). -/
theorem pkCh_class_oo {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} {P Q : ℕ × ℕ}
    (hPo : P ∈ oddDiagonals N) (hQo : Q ∈ oddDiagonals N) (hh : hitSet N S Q = hitSet N S P) :
    innerOO N S Q = innerOO N S P := by
  ext ⟨u, v⟩
  rw [pkCh_mem_innerOO, pkCh_mem_innerOO]
  constructor
  · rintro ⟨hm, h1, h2⟩
    obtain ⟨hmm, hu, hv⟩ := pkCh_mem_Moo.1 hm
    dsimp only at hu hv h1 h2 ⊢
    refine ⟨hm, ?_⟩
    have hq := mt ((pkCh_hit_iff hN hE hQo hmm (by omega)).2 hu).1 (fun h => h ⟨h1, h2⟩)
    rw [hh] at hq
    by_contra hc
    exact hq (((pkCh_hit_iff hN hE hPo hmm (by omega)).2 hu).2 hc)
  · rintro ⟨hm, h1, h2⟩
    obtain ⟨hmm, hu, hv⟩ := pkCh_mem_Moo.1 hm
    dsimp only at hu hv h1 h2 ⊢
    refine ⟨hm, ?_⟩
    have hq := mt ((pkCh_hit_iff hN hE hPo hmm (by omega)).2 hu).1 (fun h => h ⟨h1, h2⟩)
    rw [← hh] at hq
    by_contra hc
    exact hq (((pkCh_hit_iff hN hE hQo hmm (by omega)).2 hu).2 hc)

/-- The class member `Q_k` and a failing even trace of its head that is not spread: the run chord of the O-run gives
a `𝒫₁` chord with a strictly smaller head and the same `o_in` (BP App. D §6d, third bullet, via [L0]). -/
theorem pkCh_runChord {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} {Q : ℕ × ℕ}
    (hQp : Q ∈ poleChords N S) {Θ : Finset ℕ} (hΘ : Θ ∈ admSeps N (headStart Q) (headLen N Q) 0)
    (hΘe : ∀ θ ∈ Θ, θ % 2 = 0) (hΘd : Disjoint (sepIn N (headStart Q) (headLen N Q) Θ) (missing N S))
    (hns : ¬ Spread N S (headStart Q) (headLen N Q) Θ) :
    ∃ R ∈ poleChords N S, oddSide N R ⊂ oddSide N Q ∧ innerOO N S R = innerOO N S Q := by
  obtain ⟨hQo, -, -, ⟨⟨f1, f2⟩, hf⟩⟩ := pkCh_mem_pole.1 hQp
  obtain ⟨-, -, -, -, -, hs, hs2, hk1, hk3, hkN⟩ := pkCh_sides hE hQo
  have hN1 : 1 ≤ N := by omega
  obtain ⟨hΘl, hΘle, hΘlf⟩ := pkCh_toLin hN hE hQo hΘ hΘe hΘd
  obtain ⟨hΘsub, hΘc⟩ := pkCo_mem_admSeps.1 hΘ
  have hΘI : ∀ θ ∈ Θ, θ ∈ Icc 1 N ∧ 1 ≤ cycPos N (headStart Q) θ ∧
      cycPos N (headStart Q) θ + 2 ≤ headLen N Q := fun θ h => (pkCo_mem_intArc hs (by omega)).1 (hΘsub h)
  have hθl : ∀ θ ∈ Θ, cycPos N (headStart Q) θ + 1 ∈ Θ.image (rotLeg N (N + 1 - headStart Q)) := fun θ hθ => by
    rw [← pkCh_phi_eq hs]; exact mem_image_of_mem _ hθ
  have hlθ : ∀ t ∈ Θ.image (rotLeg N (N + 1 - headStart Q)), ∃ θ ∈ Θ, t = cycPos N (headStart Q) θ + 1 :=
    fun t ht => by
      obtain ⟨θ, hθ, rfl⟩ := mem_image.1 ht
      exact ⟨θ, hθ, pkCh_phi_eq hs θ⟩
  -- facts on inner oo pairs of `Q`
  have hoo : ∀ p1 p2, (p1, p2) ∈ innerOO N S Q → p1 ∈ Icc 1 N ∧ p2 ∈ Icc 1 N ∧
      cycPos N (headStart Q) p1 < headLen N Q ∧ cycPos N (headStart Q) p2 < headLen N Q ∧
      p1 ∉ Θ ∧ p2 ∉ Θ ∧ (p1, p2) ∈ Moo N S ∧ p1 % 2 = 1 ∧ p2 % 2 = 1 ∧ p1 < p2 := by
    intro p1 p2 hp
    obtain ⟨hpM, hp1, hp2⟩ := pkCh_mem_innerOO.1 hp
    obtain ⟨hpm, hp1o, hp2o⟩ := pkCh_mem_Moo.1 hpM
    dsimp only at hp1 hp2 hp1o hp2o
    have hpd := mem_diagonals.1 (pkCh_mem_missing.1 hpm).1
    dsimp only at hpd
    obtain ⟨i1, k1⟩ := (pkCh_headpos hN hE hQo).1 hp1
    obtain ⟨i2, k2⟩ := (pkCh_headpos hN hE hQo).1 hp2
    exact ⟨i1, i2, k1, k2, fun h => by have := hΘe _ h; omega, fun h => by have := hΘe _ h; omega, hpM,
      hp1o, hp2o, by omega⟩
  have hInOne : ∀ p1 p2, (p1, p2) ∈ innerOO N S Q → InOneRun N (headStart Q) (headLen N Q) Θ (p1, p2) := by
    intro p1 p2 hp
    obtain ⟨i1, i2, k1, k2, t1, t2, hpM, -, -, -⟩ := hoo p1 p2 hp
    obtain ⟨-, hp1, hp2⟩ := pkCh_mem_innerOO.1 hp
    have a1 := ((pkCh_arcs (by omega) hE hQo).1 p1).1 hp1
    have a2 := ((pkCh_arcs (by omega) hE hQo).1 p2).1 hp2
    refine pkCh_inOneRun_iff.2 ⟨a1, a2, t1, t2, ?_⟩
    rw [pkCh_sameRun_iff]
    rintro ⟨θ, hθ, b1, b2⟩
    have hm := (pkCh_mem_Moo.1 hpM).1
    exact disjoint_left.1 hΘd (pkCo_mem_sepIn.2 ⟨(pkCh_mem_missing.1 hm).1, a1, a2, t1, t2, θ, hθ, b1, b2⟩) hm
  have hsame : ∀ p1 p2, (p1, p2) ∈ innerOO N S Q → SameRun N (headStart Q) Θ p1 f1 := by
    intro p1 p2 hp
    by_contra hc
    exact hns (pkCh_spread_iff.2 ⟨(p1, p2), (hoo p1 p2 hp).2.2.2.2.2.2.1, (f1, f2), (hoo f1 f2 hf).2.2.2.2.2.2.1,
      hInOne p1 p2 hp, hInOne f1 f2 hf, hc⟩)
  obtain ⟨g1, g2, gk1, gk2, gt1, gt2, gM, go1, go2, glt⟩ := hoo f1 f2 hf
  have gm1 := pkCh_pos_mod hE hs hs2 g1
  have gm2 := pkCh_pos_mod hE hs hs2 g2
  have hf1Θ : cycPos N (headStart Q) f1 + 1 ∉ Θ.image (rotLeg N (N + 1 - headStart Q)) := fun h => by
    have := hΘle _ h; omega
  obtain ⟨a, b, hR, hau, hub⟩ := pkCh_runOf hΘl (mem_Icc.2 ⟨by omega, by omega⟩) hf1Θ
  obtain ⟨ha1, hab, hbk, haΘ, hbΘ, hRΘ⟩ := pkCh_isRun_iff.1 hR
  -- a pair of `o_in(Q)` whose first leg is in the run lies in the run
  have inrun : ∀ x y, x ∈ Icc 1 N → y ∈ Icc 1 N → cycPos N (headStart Q) x < headLen N Q →
      cycPos N (headStart Q) y < headLen N Q →
      a ≤ cycPos N (headStart Q) y + 1 → cycPos N (headStart Q) y + 1 ≤ b →
      (cycPos N (headStart Q) x + 1) % 2 = 1 →
      SameRun N (headStart Q) Θ x y → a ≤ cycPos N (headStart Q) x + 1 ∧ cycPos N (headStart Q) x + 1 ≤ b := by
    intro x y hx hy hxk hyk h1 h2 hx2 hxy
    rw [pkCh_sameRun_iff] at hxy
    by_contra hc
    rcases (show cycPos N (headStart Q) x + 1 < a ∨ b < cycPos N (headStart Q) x + 1 by omega) with h | h
    · have ha' : a - 1 ∈ Θ.image (rotLeg N (N + 1 - headStart Q)) := by
        rcases haΘ with h' | h'
        · omega
        · exact h'
      have := hΘle _ ha'
      obtain ⟨θ, hθ, e⟩ := hlθ _ ha'
      exact hxy ⟨θ, hθ, by omega, by omega⟩
    · have hb' : b + 1 ∈ Θ.image (rotLeg N (N + 1 - headStart Q)) := by
        rcases hbΘ with h' | h'
        · omega
        · exact h'
      have := hΘle _ hb'
      obtain ⟨θ, hθ, e⟩ := hlθ _ hb'
      exact hxy ⟨θ, hθ, by omega, by omega⟩
  have hsr : ∀ x y, SameRun N (headStart Q) Θ x y → SameRun N (headStart Q) Θ y x := by
    intro x y h
    rw [pkCh_sameRun_iff] at h ⊢
    rintro ⟨θ, hθ, b1, b2⟩
    exact h ⟨θ, hθ, by rw [min_comm]; exact b1, by rw [max_comm]; exact b2⟩
  have hin : ∀ p1 p2, (p1, p2) ∈ innerOO N S Q →
      (a ≤ cycPos N (headStart Q) p1 + 1 ∧ cycPos N (headStart Q) p1 + 1 ≤ b) ∧
      (a ≤ cycPos N (headStart Q) p2 + 1 ∧ cycPos N (headStart Q) p2 + 1 ≤ b) := by
    intro p1 p2 hp
    obtain ⟨i1, i2, k1, k2, -, -, -, o1, o2, -⟩ := hoo p1 p2 hp
    have m1 := pkCh_pos_mod hE hs hs2 i1
    have m2 := pkCh_pos_mod hE hs hs2 i2
    have r1 := inrun p1 f1 i1 g1 k1 gk1 hau hub (by omega) (hsame p1 p2 hp)
    have hr := (pkCh_inOneRun_iff.1 (hInOne p1 p2 hp)).2.2.2.2
    exact ⟨r1, inrun p2 p1 i2 i1 k2 k1 r1.1 r1.2 (by omega) (hsr _ _ hr)⟩
  obtain ⟨hf1r, hf2r⟩ := hin f1 f2 hf
  have hC : ¬ pkCh_Cl N (headStart Q) S (cycPos N (headStart Q) f1 + 1) (cycPos N (headStart Q) f2 + 1) := by
    have := pkCh_notCl hs g1 g2 (pkCh_mem_Moo.1 gM).1
    rw [pkCh_phi_eq hs, pkCh_phi_eq hs] at this
    exact this
  have hfne : cycPos N (headStart Q) f1 ≠ cycPos N (headStart Q) f2 := fun h => by
    have := pkCo_cycPos_inj hs g1 g2 h; omega
  have hC' := fun h => hC (pkCh_C_minmax pkCh_Cl_symm h)
  obtain ⟨R, hRp, hRodd⟩ := pkCh_L0 hN hE hQp hΘl hΘle hΘlf hR
    ⟨min (cycPos N (headStart Q) f1 + 1) (cycPos N (headStart Q) f2 + 1),
      max (cycPos N (headStart Q) f1 + 1) (cycPos N (headStart Q) f2 + 1),
      by omega, by omega, by omega, by omega, by omega, hC'⟩
  have hsub : oddSide N R ⊆ oddSide N Q := fun x hx => by
    obtain ⟨hxI, h1, h2⟩ := (hRodd x).1 hx
    exact (pkCh_headpos hN hE hQo).2 ⟨hxI, by omega⟩
  refine ⟨R, hRp, (ssubset_iff_of_subset hsub).2 ?_, ?_⟩
  · obtain ⟨θ, hθ⟩ : Θ.Nonempty := by
      rcases hΘc with h | h
      · exact card_pos.1 (by omega)
      · exact card_pos.1 (by omega)
    obtain ⟨hθI, h1, h2⟩ := hΘI θ hθ
    refine ⟨θ, (pkCh_headpos hN hE hQo).2 ⟨hθI, by omega⟩, fun h => ?_⟩
    obtain ⟨-, c1, c2⟩ := (hRodd θ).1 h
    exact hRΘ _ (mem_Icc.2 ⟨c1, c2⟩) (hθl θ hθ)
  · ext ⟨p1, p2⟩
    rw [pkCh_mem_innerOO, pkCh_mem_innerOO]
    constructor
    · rintro ⟨hm, h1, h2⟩
      exact ⟨hm, hsub h1, hsub h2⟩
    · intro h'
      have h := pkCh_mem_innerOO.2 h'
      obtain ⟨i1, i2, -⟩ := hoo p1 p2 h
      obtain ⟨r1, r2⟩ := hin p1 p2 h
      exact ⟨h'.1, (hRodd p1).2 ⟨i1, r1⟩, (hRodd p2).2 ⟨i2, r2⟩⟩

/-- **[Bot] reduction** (BP App. D §6d): strong induction on the head size of a class member. -/
theorem pkCh_bot_red {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ}
    (hP : IsMinimalChord N S P) (hT : EvenTopP N S P)
    (hOB : ∀ Q ∈ hitClass N S P, ∀ x, {x} ∈ admSeps N (headStart Q) (headLen N Q) 0 → x % 2 = 1 →
      Disjoint (sepIn N (headStart Q) (headLen N Q) {x}) (missing N S) → False)
    (hNB : ∀ R ∈ poleChords N S, oddSide N R ⊆ oddSide N P → innerOO N S R = innerOO N S P → R ∈ hitClass N S P) :
    ∀ n, ∀ Q ∈ hitClass N S P, (oddSide N Q).card = n →
      ∃ b ∈ hitClass N S P, NoFreeSep N S (headStart b) (headLen N b) 0 := by
  obtain ⟨hPg, -⟩ := pkCh_minChord_iff.1 hP
  obtain ⟨hPp, hPB⟩ := pkCh_mem_goodTail.1 hPg
  have hPo := (pkCh_mem_pole.1 hPp).1
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih Q hQ hn
  by_cases hA : NoFreeSep N S (headStart Q) (headLen N Q) 0
  · exact ⟨Q, hQ, hA⟩
  obtain ⟨Θ, hΘ, hΘd⟩ : ∃ Θ ∈ admSeps N (headStart Q) (headLen N Q) 0,
      Disjoint (sepIn N (headStart Q) (headLen N Q) Θ) (missing N S) := by
    by_contra hc
    exact hA (pkCh_noFree_iff.2 fun Θ hΘ hd => hc ⟨Θ, hΘ, hd⟩)
  obtain ⟨hQp, hQh⟩ := pkCh_mem_hitClass.1 hQ
  have hQo := (pkCh_mem_pole.1 hQp).1
  obtain ⟨hΘsub, hΘc⟩ := pkCo_mem_admSeps.1 hΘ
  have hΘe : ∀ θ ∈ Θ, θ % 2 = 0 := by
    rcases hΘc with h1 | ⟨-, h2⟩
    · obtain ⟨x, rfl⟩ := card_eq_one.1 h1
      intro θ hθ
      rw [mem_singleton] at hθ
      subst hθ
      by_contra hx
      exact hOB Q hQ θ hΘ (by omega) hΘd
    · exact h2
  have hQsub := pkCh_int_top hN hE hPp hPB hQp hQh
  have hoo := pkCh_class_oo hN hE hPo hQo hQh
  by_cases hsp : Spread N S (headStart Q) (headLen N Q) Θ
  · exfalso
    obtain ⟨Θ', h1, h2, h3, h4⟩ := pkCh_lift hN hE (mem_filter.1 hQp).1 hPo hQsub (fun x hx => by rw [hoo]; exact hx) hΘ hΘe hΘd hsp
    exact pkCh_evenTop_iff.1 hT Θ' h1 h2 h3 h4
  · obtain ⟨R, hRp, hRQ, hRoo⟩ := pkCh_runChord hN hE hQp hΘ hΘe hΘd hsp
    have hRc := hNB R hRp (hRQ.subset.trans hQsub) (hRoo.trans hoo)
    exact ih _ (hn ▸ card_lt_card hRQ) R hRc rfl
/-- `S_G` for `G` = the even legs of `[x0, x1]`: a separated pair has an odd leg strictly inside. -/
theorem pkCh_evG {x0 x1 u v : ℕ} (h : InST ((Icc x0 x1).filter (fun x => x % 2 = 0)) u v) :
    (x0 < u ∧ u < x1 ∧ u % 2 = 1) ∨ (x0 < v ∧ v < x1 ∧ v % 2 = 1) := by
  obtain ⟨hu, hv, ⟨g, hg, b1⟩, ⟨g', hg', b2⟩⟩ := pkCo_inST_iff.1 h
  rw [mem_filter, mem_Icc] at hu hv hg hg'
  omega

/-- `S_G` for `G = {N} ∪` the even legs of `[2, a − 1]` (`a` odd). -/
theorem pkCh_evGN {N a u v : ℕ} (ha : a % 2 = 1) (hu1 : 1 ≤ u) (hv1 : 1 ≤ v) (huN : u ≤ N) (hvN : v ≤ N)
    (h : InST (insert N ((Icc 2 (a - 1)).filter (fun x => x % 2 = 0))) u v) :
    (u + 1 < a ∧ u % 2 = 1) ∨ (v + 1 < a ∧ v % 2 = 1) := by
  obtain ⟨hu, hv, ⟨g, hg, b1⟩, ⟨g', hg', b2⟩⟩ := pkCo_inST_iff.1 h
  rw [mem_insert, mem_filter, mem_Icc] at hu hv hg hg'
  omega

/-- A run with anchors on both sides. -/
theorem pkCh_runAnch {T : Finset ℕ} {L H u : ℕ} (hL : L ∈ T) (hH : H ∈ T) (hLu : L < u) (huH : u < H)
    (hu : u ∉ T) :
    ∃ x0 x1, x0 - 1 ∈ T ∧ x1 + 1 ∈ T ∧ 1 ≤ x0 ∧ x0 ≤ u ∧ u ≤ x1 ∧ ∀ w, x0 ≤ w → w ≤ x1 → w ∉ T := by
  have hl : (T.filter (fun x => x < u)).Nonempty := ⟨L, mem_filter.2 ⟨hL, hLu⟩⟩
  have hr : (T.filter (fun x => u < x)).Nonempty := ⟨H, mem_filter.2 ⟨hH, huH⟩⟩
  have hm := mem_filter.1 ((T.filter (fun x => x < u)).max'_mem hl)
  have hM := mem_filter.1 ((T.filter (fun x => u < x)).min'_mem hr)
  refine ⟨(T.filter (fun x => x < u)).max' hl + 1, (T.filter (fun x => u < x)).min' hr - 1, ?_, ?_, by omega,
    by omega, by omega, fun w h1 h2 hw => ?_⟩
  · rw [Nat.add_sub_cancel]; exact hm.1
  · rw [Nat.sub_add_cancel (by omega)]; exact hM.1
  · rcases lt_trichotomy w u with h | h | h
    · have := (T.filter (fun x => x < u)).le_max' w (mem_filter.2 ⟨hw, h⟩); omega
    · exact hu (h ▸ hw)
    · have := (T.filter (fun x => u < x)).min'_le w (mem_filter.2 ⟨hw, h⟩); omega

/-- **(Thin)** core, one run (BP App. D §6a): in the linear setting of `P′` (head `[1, ω]`), a run `[x0, x1]` of
`C_N ∖ ([a, b] ∪ τ)` (or a piece with its trace leg adjoined) with two even end legs, `≥ 3` legs, inside `D`, has
`S_G` clean for `G` = its even legs (o-clean, `minrect(W)`, runcut), against F^π. -/
theorem pkCh_thinInt {N ω a b x0 x1 : ℕ} {τ : Finset ℕ} {C : ℕ → ℕ → Prop} (hC : ∀ u v, C u v → C v u)
    (HG : ∀ G : Finset ℕ, G ⊆ Icc 1 N → 2 ≤ G.card → ((∀ g ∈ G, g % 2 = 0) ∨ (∀ g ∈ G, g % 2 = 1)) →
      ∃ u v, (min u v, max u v) ∈ diagonals N ∧ InST G u v ∧ ¬ C u v)
    (Hmr : ∀ e o, e ∈ Icc 1 N → o ∈ Icc 1 N → e % 2 = 0 → o % 2 = 1 → a ≤ e → e ≤ b → ¬ (a ≤ o ∧ o ≤ b) → C e o)
    (Hoc : ∀ u v, u % 2 = 1 → v % 2 = 1 → 1 ≤ u → u ≤ ω → 1 ≤ v → v ≤ ω → ¬ (a ≤ u ∧ u ≤ b) → C u v)
    (hf : ∀ u v, InST (Icc a b ∪ τ) u v → C u v)
    (hωN : ω + 1 ≤ N) (hbω : b ≤ ω) (hx0 : 1 ≤ x0) (h0 : x0 % 2 = 0) (h1 : x1 % 2 = 0) (h01 : x0 + 2 ≤ x1) (hx1 : x1 ≤ ω + 1)
    (hdis : x1 < a ∨ b < x0)
    (hL : x0 - 1 ∈ Icc a b ∪ τ ∨ x0 ∈ τ) (hR : x1 + 1 ∈ Icc a b ∪ τ ∨ x1 ∈ τ)
    (hint : ∀ t ∈ τ, ¬ (x0 < t ∧ t < x1)) (hτ : ∀ t ∈ τ, t = x0 ∨ t = x1 ∨ (t % 2 = 1 ∧ t ≤ ω)) : False := by
  have hGsub : (Icc x0 x1).filter (fun x => x % 2 = 0) ⊆ Icc 1 N := fun x hx => by
    rw [mem_filter, mem_Icc] at hx; rw [mem_Icc]; omega
  have hGc : 2 ≤ ((Icc x0 x1).filter (fun x => x % 2 = 0)).card :=
    one_lt_card.2 ⟨x0, mem_filter.2 ⟨mem_Icc.2 ⟨le_refl _, by omega⟩, h0⟩, x1,
      mem_filter.2 ⟨mem_Icc.2 ⟨by omega, le_refl _⟩, h1⟩, by omega⟩
  obtain ⟨bL, hbL, bL1, bL2⟩ : ∃ t ∈ Icc a b ∪ τ, x0 - 1 ≤ t ∧ t ≤ x0 := by
    rcases hL with h | h
    · exact ⟨_, h, le_refl _, by omega⟩
    · exact ⟨x0, mem_union_right _ h, by omega, le_refl _⟩
  obtain ⟨bR, hbR, bR1, bR2⟩ : ∃ t ∈ Icc a b ∪ τ, x1 ≤ t ∧ t ≤ x1 + 1 := by
    rcases hR with h | h
    · exact ⟨_, h, by omega, le_refl _⟩
    · exact ⟨x1, mem_union_right _ h, le_refl _, by omega⟩
  have key : ∀ u v, x0 < u → u < x1 → u % 2 = 1 → 1 ≤ v → v ≤ N →
      v ∉ (Icc x0 x1).filter (fun x => x % 2 = 0) → C u v := by
    intro u v hu1 hu2 hu3 hv1 hv2 hvG
    rw [mem_filter, mem_Icc] at hvG
    have huab : ¬ (a ≤ u ∧ u ≤ b) := by omega
    by_cases hvab : a ≤ v ∧ v ≤ b
    · by_cases hv2' : v % 2 = 0
      · exact hC _ _ (Hmr v u (mem_Icc.2 ⟨by omega, by omega⟩) (mem_Icc.2 ⟨by omega, by omega⟩) hv2' hu3 hvab.1
          hvab.2 huab)
      · exact Hoc u v hu3 (by omega) (by omega) (by omega) (by omega) (by omega) huab
    · by_cases hvτ : v ∈ τ
      · rcases hτ v hvτ with h | h | h
        · exact absurd ⟨⟨by omega, by omega⟩, by omega⟩ hvG
        · exact absurd ⟨⟨by omega, by omega⟩, by omega⟩ hvG
        · exact Hoc u v hu3 h.1 (by omega) (by omega) (by omega) h.2 huab
      · by_cases hvX : x0 ≤ v ∧ v ≤ x1
        · exact Hoc u v hu3 (by omega) (by omega) (by omega) (by omega) (by omega) huab
        · apply hf
          have huT : u ∉ Icc a b ∪ τ := by
            rw [mem_union, mem_Icc]
            rintro (h | h)
            · exact huab h
            · exact hint u h ⟨hu1, hu2⟩
          have hvT : v ∉ Icc a b ∪ τ := by
            rw [mem_union, mem_Icc]
            rintro (h | h)
            · exact hvab h
            · exact hvτ h
          have nL : v ≠ bL := fun h => hvT (h ▸ hbL)
          have nR : v ≠ bR := fun h => hvT (h ▸ hbR)
          rw [pkCo_inST_iff]
          refine ⟨huT, hvT, ?_, ?_⟩
          · rcases (show v < x0 ∨ x1 < v by omega) with h | h
            · exact ⟨bL, hbL, by omega, by omega⟩
            · exact ⟨bR, hbR, by omega, by omega⟩
          · rcases (show v < x0 ∨ x1 < v by omega) with h | h
            · exact ⟨bR, hbR, Or.inr (by omega)⟩
            · exact ⟨bL, hbL, Or.inl (by omega)⟩
  obtain ⟨u, v, hd, hst, hc⟩ := HG _ hGsub hGc (Or.inl fun g hg => (mem_filter.1 hg).2)
  have hd' := mem_diagonals.1 hd
  simp only at hd'
  have hvG := (pkCo_inST_iff.1 hst).2.1
  have huG := (pkCo_inST_iff.1 hst).1
  rcases pkCh_evG hst with h | h
  · exact hc (key u v h.1 h.2.1 h.2.2 (by omega) (by omega) hvG)
  · exact hc (hC _ _ (key v u h.1 h.2.1 h.2.2 (by omega) (by omega) huG))

/-- **(Thin)** core, the piece through leg `1` when the even singleton trace is `{N}`. -/
theorem pkCh_thinN {N ω a b : ℕ} {C : ℕ → ℕ → Prop} (hC : ∀ u v, C u v → C v u) (hN : N % 2 = 0)
    (HG : ∀ G : Finset ℕ, G ⊆ Icc 1 N → 2 ≤ G.card → ((∀ g ∈ G, g % 2 = 0) ∨ (∀ g ∈ G, g % 2 = 1)) →
      ∃ u v, (min u v, max u v) ∈ diagonals N ∧ InST G u v ∧ ¬ C u v)
    (Hmr : ∀ e o, e ∈ Icc 1 N → o ∈ Icc 1 N → e % 2 = 0 → o % 2 = 1 → a ≤ e → e ≤ b → ¬ (a ≤ o ∧ o ≤ b) → C e o)
    (Hoc : ∀ u v, u % 2 = 1 → v % 2 = 1 → 1 ≤ u → u ≤ ω → 1 ≤ v → v ≤ ω → ¬ (a ≤ u ∧ u ≤ b) → C u v)
    (hf : ∀ u v, InST (Icc a b ∪ {N}) u v → C u v)
    (hωN : ω + 3 ≤ N) (ha : 3 ≤ a) (ha2 : a % 2 = 1) (hab : a ≤ b) (hbω : b ≤ ω) : False := by
  have hGsub : insert N ((Icc 2 (a - 1)).filter (fun x => x % 2 = 0)) ⊆ Icc 1 N := fun x hx => by
    rw [mem_insert, mem_filter, mem_Icc] at hx; rw [mem_Icc]; omega
  have hGc : 2 ≤ (insert N ((Icc 2 (a - 1)).filter (fun x => x % 2 = 0))).card :=
    one_lt_card.2 ⟨N, mem_insert_self _ _, 2, mem_insert_of_mem (mem_filter.2 ⟨mem_Icc.2 ⟨le_refl _, by omega⟩,
      rfl⟩), by omega⟩
  have hGp : ∀ g ∈ insert N ((Icc 2 (a - 1)).filter (fun x => x % 2 = 0)), g % 2 = 0 := fun g hg => by
    rw [mem_insert, mem_filter] at hg
    rcases hg with h | h
    · rw [h]; exact hN
    · exact h.2
  have key : ∀ u v, 1 ≤ u → u + 1 < a → u % 2 = 1 → 1 ≤ v → v ≤ N →
      v ∉ insert N ((Icc 2 (a - 1)).filter (fun x => x % 2 = 0)) → C u v := by
    intro u v hu1 hu2 hu3 hv1 hv2 hvG
    rw [mem_insert, mem_filter, mem_Icc] at hvG
    have huab : ¬ (a ≤ u ∧ u ≤ b) := by omega
    by_cases hvab : a ≤ v ∧ v ≤ b
    · by_cases hv2' : v % 2 = 0
      · exact hC _ _ (Hmr v u (mem_Icc.2 ⟨by omega, by omega⟩) (mem_Icc.2 ⟨by omega, by omega⟩) hv2' hu3 hvab.1
          hvab.2 huab)
      · exact Hoc u v hu3 (by omega) (by omega) (by omega) (by omega) (by omega) huab
    · by_cases hva : v < a
      · exact Hoc u v hu3 (by omega) (by omega) (by omega) (by omega) (by omega) huab
      · apply hf
        rw [pkCo_inST_iff, mem_union, mem_union, mem_Icc, mem_Icc, mem_singleton, mem_singleton]
        refine ⟨by omega, by omega, ⟨a, mem_union_left _ (mem_Icc.2 ⟨le_refl _, hab⟩), by omega, by omega⟩,
          ⟨N, mem_union_right _ (mem_singleton_self _), Or.inr (by omega)⟩⟩
  obtain ⟨u, v, hd, hst, hc⟩ := HG _ hGsub hGc (Or.inl hGp)
  have hd' := mem_diagonals.1 hd
  simp only at hd'
  have hvG := (pkCo_inST_iff.1 hst).2.1
  have huG := (pkCo_inST_iff.1 hst).1
  rcases pkCh_evGN ha2 (by omega) (by omega) (by omega) (by omega) hst with h | h
  · exact hc (key u v (by omega) h.1 h.2 (by omega) (by omega) hvG)
  · exact hc (hC _ _ (key v u (by omega) h.1 h.2 (by omega) (by omega) huG))

/-- **(Thin)** in the linear setting of `P′` (BP App. D §6a): `W` with head `[a, b] ⊊ [1, ω]`, o-clean, in `𝒫₀`; a failing
(b0)-shaped trace `τ` of `B_W` is odd, and with `hi`/`lo` its extreme legs right of `b` / left of `a` (else `b` / `a`),
`R* = [hi+1, N] ∪ [1, lo−1]`: even legs of `B_W ∖ R*` are runcut-separated from odd legs of `R*`, and every missing ee
pair of `B_W` lies in `R*` (the other runs are single legs). -/
theorem pkCh_thinLin {N ω a b : ℕ} {τ : Finset ℕ} {C : ℕ → ℕ → Prop} (hC : ∀ u v, C u v → C v u)
    (hN : N % 2 = 0) (hωN : ω + 3 ≤ N) (ha1 : 1 ≤ a) (ha2 : a % 2 = 1) (hb2 : b % 2 = 1) (hab : a + 2 ≤ b)
    (hbω : b ≤ ω) (hτ : AdmSepCompl N a b τ) (hTA : TailAvoiding N ω τ)
    (hf : ∀ u v, InST (Icc a b ∪ τ) u v → C u v)
    (HG : ∀ G : Finset ℕ, G ⊆ Icc 1 N → 2 ≤ G.card → ((∀ g ∈ G, g % 2 = 0) ∨ (∀ g ∈ G, g % 2 = 1)) →
      ∃ u v, (min u v, max u v) ∈ diagonals N ∧ InST G u v ∧ ¬ C u v)
    (Hmr : ∀ e o, e ∈ Icc 1 N → o ∈ Icc 1 N → e % 2 = 0 → o % 2 = 1 → a ≤ e → e ≤ b → ¬ (a ≤ o ∧ o ≤ b) → C e o)
    (Hoc : ∀ u v, u % 2 = 1 → v % 2 = 1 → 1 ≤ u → u ≤ ω → 1 ≤ v → v ≤ ω → ¬ (a ≤ u ∧ u ≤ b) → C u v) :
    ∃ lo hi, lo ≤ a ∧ b ≤ hi ∧ hi ≤ ω ∧ 1 ≤ lo ∧ lo % 2 = 1 ∧ hi % 2 = 1 ∧ (lo < a ∨ b < hi) ∧
      (∀ e o, e ∈ Icc 1 N → o ∈ Icc 1 N → e % 2 = 0 → o % 2 = 1 → lo ≤ e → e ≤ hi → ¬ (a ≤ e ∧ e ≤ b) →
        (o < lo ∨ hi < o) → C e o) ∧
      (∀ e1 e2, e1 ∈ Icc 1 N → e2 ∈ Icc 1 N → e1 % 2 = 0 → e2 % 2 = 0 → ¬ (a ≤ e1 ∧ e1 ≤ b) →
        ¬ (a ≤ e2 ∧ e2 ≤ b) → e1 ≠ e2 → ¬ C e1 e2 → (e1 < lo ∨ hi < e1)) := by
  obtain ⟨hne, hsubτ, hsing⟩ := pkCh_asc_facts hτ
  have hτI : ∀ t ∈ τ, (1 ≤ t ∧ t ≤ N) ∧ ¬ (a ≤ t ∧ t ≤ b) ∧ t ≠ b + 1 ∧ t ≠ (if a = 1 then N else a - 1) :=
    fun t ht => pkCh_mem_intCompl.1 (hsubτ ht)
  obtain ⟨hTA1, hTA2⟩ := pkCh_ta_iff.1 hTA
  -- (Thin) Case A: an even singleton trace is impossible
  have hodd : ∀ t ∈ τ, t % 2 = 1 := by
    intro y hy
    by_contra hy2
    have hτy : τ = {y} := hsing y hy (by omega)
    obtain ⟨⟨hy1, hyN⟩, hyab, hyb1, hya1⟩ := hτI y hy
    have hyW : ¬ (ω + 2 ≤ y ∧ y ≤ N - 1) := fun h => disjoint_left.1 hTA1 hy (mem_Icc.2 h)
    rw [hτy] at hf
    rcases (show (b + 1 < y ∧ y ≤ ω + 1) ∨ y < a ∨ y = N by omega) with h | h | h
    · refine pkCh_thinInt (x0 := b + 1) (x1 := y) (τ := {y}) hC HG Hmr Hoc hf (by omega) hbω (by omega) (by omega)
        (by omega) (by omega) (by omega) (Or.inr (by omega)) (Or.inl ?_) (Or.inr (mem_singleton_self _)) ?_ ?_
      · rw [show b + 1 - 1 = b by omega]; exact mem_union_left _ (mem_Icc.2 ⟨by omega, le_refl _⟩)
      · intro t ht; rw [mem_singleton] at ht; omega
      · intro t ht; rw [mem_singleton] at ht; exact Or.inr (Or.inl ht)
    · have ha' : a ≠ 1 := by omega
      rw [if_neg ha'] at hya1
      refine pkCh_thinInt (x0 := y) (x1 := a - 1) (τ := {y}) hC HG Hmr Hoc hf (by omega) hbω (by omega) (by omega)
        (by omega) (by omega) (by omega) (Or.inl (by omega)) (Or.inr (mem_singleton_self _)) (Or.inl ?_) ?_ ?_
      · rw [show a - 1 + 1 = a by omega]; exact mem_union_left _ (mem_Icc.2 ⟨le_refl _, by omega⟩)
      · intro t ht; rw [mem_singleton] at ht; omega
      · intro t ht; rw [mem_singleton] at ht; exact Or.inl ht
    · have ha' : a ≠ 1 := fun h' => by rw [if_pos h'] at hya1; exact hya1 h
      rw [h] at hf
      exact pkCh_thinN hC hN HG Hmr Hoc hf hωN (by omega) ha2 (by omega) hbω
  have hτω : ∀ t ∈ τ, t ≤ ω := fun t ht => by
    by_contra h
    exact disjoint_left.1 (hTA2 hodd) ht (mem_Icc.2 ⟨by omega, (hτI t ht).1.2⟩)
  obtain ⟨hi, hhiT, hhib, hhiω, hhi⟩ : ∃ hi, (hi ∈ τ ∨ hi = b) ∧ b ≤ hi ∧ hi ≤ ω ∧ ∀ t ∈ τ, b < t → t ≤ hi := by
    by_cases hR : (τ.filter (fun x => b < x)).Nonempty
    · have hm := mem_filter.1 ((τ.filter (fun x => b < x)).max'_mem hR)
      exact ⟨_, Or.inl hm.1, by omega, hτω _ hm.1, fun t ht htb =>
        (τ.filter (fun x => b < x)).le_max' t (mem_filter.2 ⟨ht, htb⟩)⟩
    · exact ⟨b, Or.inr rfl, le_refl _, hbω, fun t ht htb => absurd ⟨t, mem_filter.2 ⟨ht, htb⟩⟩ hR⟩
  obtain ⟨lo, hloT, hloa, hlo1, hlo⟩ : ∃ lo, (lo ∈ τ ∨ lo = a) ∧ lo ≤ a ∧ 1 ≤ lo ∧ ∀ t ∈ τ, t < a → lo ≤ t := by
    by_cases hL : (τ.filter (fun x => x < a)).Nonempty
    · have hm := mem_filter.1 ((τ.filter (fun x => x < a)).min'_mem hL)
      exact ⟨_, Or.inl hm.1, by omega, (hτI _ hm.1).1.1, fun t ht hta =>
        (τ.filter (fun x => x < a)).min'_le t (mem_filter.2 ⟨ht, hta⟩)⟩
    · exact ⟨a, Or.inr rfl, le_refl _, ha1, fun t ht hta => absurd ⟨t, mem_filter.2 ⟨ht, hta⟩⟩ hL⟩
  have hhi2 : hi % 2 = 1 := by rcases hhiT with h | h; exact hodd _ h; omega
  have hlo2 : lo % 2 = 1 := by rcases hloT with h | h; exact hodd _ h; omega
  have hside : lo < a ∨ b < hi := by
    obtain ⟨t, ht⟩ := hne
    have := (hτI t ht).2.1
    rcases (show t < a ∨ b < t by omega) with h | h
    · have := hlo t ht h; omega
    · have := hhi t ht h; omega
  have haT : a ∈ Icc a b ∪ τ := mem_union_left _ (mem_Icc.2 ⟨le_refl _, by omega⟩)
  have hbT : b ∈ Icc a b ∪ τ := mem_union_left _ (mem_Icc.2 ⟨by omega, le_refl _⟩)
  have hTodd : ∀ t ∈ Icc a b ∪ τ, (t < a ∨ b < t ∨ t = a ∨ t = b) → t % 2 = 1 := by
    intro t ht h
    rcases mem_union.1 ht with h' | h'
    · rw [mem_Icc] at h'; omega
    · exact hodd t h'
  have hnotT : ∀ x, x % 2 = 0 → ¬ (a ≤ x ∧ x ≤ b) → x ∉ Icc a b ∪ τ := by
    intro x hx hxab h
    rcases mem_union.1 h with h' | h'
    · exact hxab (mem_Icc.1 h')
    · have := hodd x h'; omega
  refine ⟨lo, hi, hloa, hhib, hhiω, hlo1, hlo2, hhi2, hside, ?_, ?_⟩
  · intro e o he ho he2 ho2 h1 h2 heab ho'
    apply hf
    have hoT : o ∉ Icc a b ∪ τ := by
      intro h
      rcases mem_union.1 h with h' | h'
      · rw [mem_Icc] at h'; omega
      · rcases (show o < a ∨ b < o by have := (hτI o h').2.1; omega) with h'' | h''
        · have := hlo o h' h''; omega
        · have := hhi o h' h''; omega
    rw [pkCo_inST_iff]
    refine ⟨hnotT e he2 heab, hoT, ?_⟩
    rcases (show b < e ∨ e < a by omega) with hr | hl
    · have hiT : hi ∈ Icc a b ∪ τ := by
        rcases hhiT with h | h
        · exact mem_union_right _ h
        · omega
      rcases ho' with h | h
      · exact ⟨⟨a, haT, by omega, by omega⟩, ⟨hi, hiT, Or.inr (by omega)⟩⟩
      · exact ⟨⟨hi, hiT, by omega, by omega⟩, ⟨a, haT, Or.inl (by omega)⟩⟩
    · have loT : lo ∈ Icc a b ∪ τ := by
        rcases hloT with h | h
        · exact mem_union_right _ h
        · omega
      rcases ho' with h | h
      · exact ⟨⟨lo, loT, by omega, by omega⟩, ⟨a, haT, Or.inr (by omega)⟩⟩
      · exact ⟨⟨a, haT, by omega, by omega⟩, ⟨lo, loT, Or.inl (by omega)⟩⟩
  · intro e1 e2 h1 h2 he1 he2 hab1 hab2 hne12 hc
    by_contra hin
    have h1T := hnotT e1 he1 hab1
    have h2T := hnotT e2 he2 hab2
    -- the run of `e1` and its anchors
    obtain ⟨L, H, hL, hH, hLe, heH, hHω⟩ : ∃ L H, L ∈ Icc a b ∪ τ ∧ H ∈ Icc a b ∪ τ ∧ L < e1 ∧ e1 < H ∧
        H ≤ ω := by
      rcases (show b < e1 ∨ e1 < a by omega) with hr | hl
      · have hiT : hi ∈ Icc a b ∪ τ := by
          rcases hhiT with h | h
          · exact mem_union_right _ h
          · omega
        exact ⟨b, hi, hbT, hiT, hr, by omega, hhiω⟩
      · have loT : lo ∈ Icc a b ∪ τ := by
          rcases hloT with h | h
          · exact mem_union_right _ h
          · omega
        exact ⟨lo, a, loT, haT, by omega, hl, by omega⟩
    obtain ⟨x0, x1, hx0T, hx1T, hx01, hx0e, hex1, hfree⟩ := pkCh_runAnch hL hH hLe heH h1T
    have hLx : L < x0 := by
      by_contra h
      exact hfree L (by omega) (by omega) hL
    have hHx : x1 < H := by
      by_contra h
      exact hfree H (by omega) (by omega) hH
    have hsame : x0 ≤ e2 ∧ e2 ≤ x1 := by
      by_contra hc2
      apply hc
      apply hf
      rw [pkCo_inST_iff]
      refine ⟨h1T, h2T, ?_⟩
      have n0 : e2 ≠ x0 - 1 := fun h => h2T (h ▸ hx0T)
      have n1 : e2 ≠ x1 + 1 := fun h => h2T (h ▸ hx1T)
      rcases (show e2 < x0 ∨ x1 < e2 by omega) with h | h
      · exact ⟨⟨x0 - 1, hx0T, by omega, by omega⟩, ⟨x1 + 1, hx1T, Or.inr (by omega)⟩⟩
      · exact ⟨⟨x1 + 1, hx1T, by omega, by omega⟩, ⟨x0 - 1, hx0T, Or.inl (by omega)⟩⟩
    have ha' : ¬ (x0 ≤ a ∧ a ≤ x1) := fun h => hfree a h.1 h.2 haT
    have hb' : ¬ (x0 ≤ b ∧ b ≤ x1) := fun h => hfree b h.1 h.2 hbT
    have hp0 := hTodd _ hx0T (by omega)
    have hp1 := hTodd _ hx1T (by omega)
    refine pkCh_thinInt (x0 := x0) (x1 := x1) hC HG Hmr Hoc hf (by omega) hbω hx01 (by omega) (by omega) (by omega)
      (by omega) (by omega) (Or.inl hx0T) (Or.inl hx1T) (fun t ht h => hfree t (by omega) (by omega)
      (mem_union_right _ ht)) (fun t ht => Or.inr (Or.inr ⟨hodd t ht, hτω t ht⟩))
/-- The chord whose head is the label interval `[a, b]` of the linear setting of `P` (labels `cycPos + 1`). -/
theorem pkCh_mkHead {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {P : ℕ × ℕ} (hPo : P ∈ oddDiagonals N) {a b : ℕ}
    (ha1 : 1 ≤ a) (hab : a + 2 ≤ b) (hbk : b ≤ headLen N P) (ha2 : a % 2 = 1) (hb2 : b % 2 = 1) :
    ∃ Q ∈ oddDiagonals N, tailStart Q = vtx N (headStart P + b) ∧ tailLen N Q = N - (b + 1 - a) ∧
      (∀ x, x ∈ evenSide N Q ↔ x ∈ Icc 1 N ∧
        (cycPos N (headStart P) x + 1 < a ∨ b < cycPos N (headStart P) x + 1)) ∧
      (∀ x, x ∈ oddSide N Q ↔ x ∈ Icc 1 N ∧
        a ≤ cycPos N (headStart P) x + 1 ∧ cycPos N (headStart P) x + 1 ≤ b) := by
  obtain ⟨-, -, -, -, -, hs, hs2, hk1, hk3, hkN⟩ := pkCh_sides hE hPo
  have hN1 : 1 ≤ N := by omega
  have hsI := mem_Icc.1 hs
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
  exact ⟨Q, hQo, hQts', hQtl, hevQ, hodQ⟩

set_option maxHeartbeats 1000000 in
/-- A failing admissible trace of the tail of a chord with head `[a, b]` (linear setting of `P`), read as a failing
(Tri)-style trace `τ` of `C_N ∖ [a, b]` (moved out of `pkCh_Hfail`). -/
theorem pkCh_tailLin {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} {P Q : ℕ × ℕ}
    (hPo : P ∈ oddDiagonals N) (hQo : Q ∈ oddDiagonals N) {a b : ℕ} (ha1 : 1 ≤ a) (hab : a ≤ b)
    (hbk : b ≤ headLen N P) (hQts' : tailStart Q = vtx N (headStart P + b)) (hQtl : tailLen N Q = N - (b + 1 - a))
    {τ0 : Finset ℕ} (hτ0 : τ0 ∈ admSeps N (tailStart Q) (tailLen N Q) 1)
    (hτ0d : Disjoint (sepIn N (tailStart Q) (tailLen N Q) τ0) (missing N S)) :
    ∃ τ, AdmSepCompl N a b τ ∧ ∀ u v, InST (Icc a b ∪ τ) u v → pkCh_Cl N (headStart P) S u v := by
  obtain ⟨-, -, -, -, -, hs, hs2, hk1, hk3, hkN⟩ := pkCh_sides hE hPo
  have hN1 : 1 ≤ N := by omega
  have hsI := mem_Icc.1 hs
  have hQtsI : tailStart Q ∈ Icc 1 N := (pkCh_sides hE hQo).1
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

/-- On `𝒫₀` the hit set is determined by `e_in` and `o_in` (BP App. D §0 D3; mixed pairs are hit only in `minrect`). -/
theorem pkCh_class_of {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} {P Q : ℕ × ℕ}
    (hP : P ∈ cleanChords N S) (hQ : Q ∈ cleanChords N S) (hee : innerEE N S P = innerEE N S Q)
    (hoo : innerOO N S P = innerOO N S Q) : hitSet N S P = hitSet N S Q := by
  have hmix : ∀ R : ℕ × ℕ, R ∈ oddDiagonals N → Disjoint (minRect N R) (missing N S) → ∀ u v,
      (u, v) ∈ missing N S → u % 2 ≠ v % 2 → (u, v) ∉ hitSet N S R := by
    rintro ⟨i, j⟩ hRo hRc u v hm hp hh
    have hd := mem_diagonals.1 (pkCh_mem_missing.1 hm).1
    dsimp only at hd
    obtain ⟨r1, r2, -⟩ := pkCo_mem_oddDiagonals.1 hRo
    dsimp only at r1 r2
    have hps := pkL_H_to hRo (by omega) (mem_union.2 (pkCh_mem_hitSet.1 hh).2)
    exact disjoint_left.1 hRc (pkL_Psi_minRect r1 r2 (by omega) (by omega) (by omega) hp hps) hm
  have dir : ∀ R R' : ℕ × ℕ, R ∈ cleanChords N S → R' ∈ cleanChords N S → innerEE N S R = innerEE N S R' →
      innerOO N S R = innerOO N S R' → ∀ u v, (u, v) ∈ hitSet N S R → (u, v) ∈ hitSet N S R' := by
    intro R R' hR hR' he ho u v hh
    have hRo : R ∈ oddDiagonals N := (mem_filter.1 hR).1
    have hR'o : R' ∈ oddDiagonals N := (mem_filter.1 hR').1
    have hm := (pkCh_mem_hitSet.1 hh).1
    by_cases hp : u % 2 = v % 2
    · by_cases h0 : u % 2 = 0
      · rw [(pkCh_hit_iff hN hE hR'o hm hp).1 h0]
        rw [(pkCh_hit_iff hN hE hRo hm hp).1 h0] at hh
        intro hin
        apply hh
        have hx : (u, v) ∈ innerEE N S R' := pkCh_mem_innerEE.2 ⟨pkCh_mem_Mee.2 ⟨hm, h0, by omega⟩, hin.1, hin.2⟩
        rw [← he] at hx
        obtain ⟨-, a1, a2⟩ := pkCh_mem_innerEE.1 hx
        exact ⟨a1, a2⟩
      · have h1 : u % 2 = 1 := by omega
        rw [(pkCh_hit_iff hN hE hR'o hm hp).2 h1]
        rw [(pkCh_hit_iff hN hE hRo hm hp).2 h1] at hh
        intro hin
        apply hh
        have hx : (u, v) ∈ innerOO N S R' := pkCh_mem_innerOO.2 ⟨pkCh_mem_Moo.2 ⟨hm, h1, by omega⟩, hin.1, hin.2⟩
        rw [← ho] at hx
        obtain ⟨-, a1, a2⟩ := pkCh_mem_innerOO.1 hx
        exact ⟨a1, a2⟩
    · exact absurd hh (hmix R hRo (mem_filter.1 hR).2 u v hm hp)
  ext ⟨u, v⟩
  exact ⟨dir P Q hP hQ hee hoo u v, dir Q P hQ hP hee.symm hoo.symm u v⟩

/-- **(Thin) + Corollary** (BP App. D §6a) at the chord level: an o-clean `W ∈ 𝒫₁` with head inside the head of
`P′ ∈ 𝒮_B`, failing `Sep_all(B_W)`, has a class-preserving B-step `V` (tail `R*`). F^π. -/
theorem pkCh_noB1_step {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} (hF : InFpi N S)
    {P W : ℕ × ℕ} (hPg : P ∈ goodTail N S) (hWp : W ∈ poleChords N S) (hsub : oddSide N W ⊆ oddSide N P)
    (hoo : innerOO N S W = innerOO N S P) {τ0 : Finset ℕ} (hτ0 : τ0 ∈ admSeps N (tailStart W) (tailLen N W) 1)
    (hτ0d : Disjoint (sepIn N (tailStart W) (tailLen N W) τ0) (missing N S)) :
    ∃ V ∈ poleChords N S, evenSide N V ⊂ evenSide N W ∧ oddSide N V ⊆ oddSide N P ∧
      innerOO N S V = innerOO N S P ∧ hitSet N S V = hitSet N S W := by
  obtain ⟨hPp, hPB⟩ := pkCh_mem_goodTail.1 hPg
  have hPo := (pkCh_mem_pole.1 hPp).1
  obtain ⟨hWo, hWc, ⟨⟨g1, g2⟩, hg⟩, -⟩ := pkCh_mem_pole.1 hWp
  obtain ⟨-, -, -, -, -, hs, hs2, hk1, hk3, hkN⟩ := pkCh_sides hE hPo
  obtain ⟨-, -, -, -, -, hws, hws2, hwk1, hwk3, hwkN⟩ := pkCh_sides hE hWo
  have hN1 : 1 ≤ N := by omega
  have hsI := mem_Icc.1 hs
  obtain ⟨hcb, hc2, hmemP, -⟩ := pkCh_subHead hN hE hWo hPo hsub
  obtain ⟨c, hc⟩ : ∃ c, cycPos N (headStart P) (headStart W) = c := ⟨_, rfl⟩
  rw [hc] at hcb hc2 hmemP
  have hWts : tailStart W = vtx N (headStart P + (c + headLen N W)) := by
    rw [pkCh_tail_eq hWo]
    rw [← pkCo_vtx_cycPos hs hws, hc, pkCo_vtx_vtx_add hN1, add_assoc]
  have hWtl : tailLen N W = N - (c + headLen N W + 1 - (c + 1)) := by
    rw [show c + headLen N W + 1 - (c + 1) = headLen N W by omega]
    rfl
  obtain ⟨τ, hτ, hτf⟩ := pkCh_tailLin hN hE (S := S) hPo hWo (a := c + 1) (b := c + headLen N W) (by omega)
    (by omega) hcb hWts hWtl hτ0 hτ0d
  have hTA := pkCh_b0 hE hk1 hkN (by omega : c + 1 ≤ c + headLen N W) hcb (pkCh_HW hN hE hPo hPB) hτ hτf
  have HG := pkCh_HG hN hE hF hs hs2
  have Hmr : ∀ e o, e ∈ Icc 1 N → o ∈ Icc 1 N → e % 2 = 0 → o % 2 = 1 → c + 1 ≤ e → e ≤ c + headLen N W →
      ¬ (c + 1 ≤ o ∧ o ≤ c + headLen N W) → pkCh_Cl N (headStart P) S e o := by
    intro e o he ho he2 ho2 h1 h2 ho'
    rw [pkCh_Cl_iff]
    rintro ⟨-, -, hm⟩
    have pe := pkCh_psi_pos hs he
    have po := pkCh_psi_pos hs ho
    have eW : rotLeg N (headStart P - 1) e ∈ oddSide N W :=
      (hmemP _ (pkCh_psi_mem hN1 e)).2 (by rw [pe]; omega)
    have oW : rotLeg N (headStart P - 1) o ∈ evenSide N W := by
      show rotLeg N (headStart P - 1) o ∈ Icc 1 N \ oddSide N W
      refine mem_sdiff.2 ⟨pkCh_psi_mem hN1 o, fun h => ?_⟩
      have := (hmemP _ (pkCh_psi_mem hN1 o)).1 h
      rw [po] at this
      omega
    have me := pkCh_psi_mod hN1 hE hsI.1 hs2 e
    have mo := pkCh_psi_mod hN1 hE hsI.1 hs2 o
    have hr : (min (rotLeg N (headStart P - 1) e) (rotLeg N (headStart P - 1) o),
        max (rotLeg N (headStart P - 1) e) (rotLeg N (headStart P - 1) o)) ∈ minRect N W :=
      pkCh_mem_minRect.2 ⟨_, pkCh_mem_evens.2 ⟨eW, by omega⟩, _, pkCh_mem_odds.2 ⟨oW, by omega⟩, rfl⟩
    rcases hm with hm | hm
    · have hd := mem_diagonals.1 (pkCh_mem_missing.1 hm).1
      dsimp only at hd
      rw [min_eq_left (by omega), max_eq_right (by omega)] at hr
      exact disjoint_left.1 hWc hr hm
    · have hd := mem_diagonals.1 (pkCh_mem_missing.1 hm).1
      dsimp only at hd
      rw [min_eq_right (by omega), max_eq_left (by omega)] at hr
      exact disjoint_left.1 hWc hr hm
  have Hoc : ∀ u v, u % 2 = 1 → v % 2 = 1 → 1 ≤ u → u ≤ headLen N P → 1 ≤ v → v ≤ headLen N P →
      ¬ (c + 1 ≤ u ∧ u ≤ c + headLen N W) → pkCh_Cl N (headStart P) S u v := by
    intro u v hu hv u1 u2 v1 v2 hu'
    rw [pkCh_Cl_iff]
    rintro ⟨huI, hvI, hm⟩
    have pu := pkCh_psi_pos hs huI
    have pv := pkCh_psi_pos hs hvI
    have mu := pkCh_psi_mod hN1 hE hsI.1 hs2 u
    have mv := pkCh_psi_mod hN1 hE hsI.1 hs2 v
    have uP : rotLeg N (headStart P - 1) u ∈ oddSide N P :=
      (pkCh_headpos hN hE hPo).2 ⟨pkCh_psi_mem hN1 u, by rw [pu]; omega⟩
    have vP : rotLeg N (headStart P - 1) v ∈ oddSide N P :=
      (pkCh_headpos hN hE hPo).2 ⟨pkCh_psi_mem hN1 v, by rw [pv]; omega⟩
    have key : ∀ x y, (x, y) ∈ missing N S → x % 2 = 1 → y % 2 = 1 → x ∈ oddSide N P → y ∈ oddSide N P →
        x ∈ oddSide N W ∧ y ∈ oddSide N W := by
      intro x y hm hx hy hxP hyP
      have hin : (x, y) ∈ innerOO N S P := pkCh_mem_innerOO.2 ⟨pkCh_mem_Moo.2 ⟨hm, hx, hy⟩, hxP, hyP⟩
      rw [← hoo] at hin
      exact ⟨(pkCh_mem_innerOO.1 hin).2.1, (pkCh_mem_innerOO.1 hin).2.2⟩
    have uW : rotLeg N (headStart P - 1) u ∉ oddSide N W := fun h => by
      have := (hmemP _ (pkCh_psi_mem hN1 u)).1 h
      rw [pu] at this
      omega
    rcases hm with hm | hm
    · exact uW (key _ _ hm (by omega) (by omega) uP vP).1
    · exact uW (key _ _ hm (by omega) (by omega) vP uP).2
  obtain ⟨lo, hi, hloa, hhib, hhiω, hlo1, hlo2, hhi2, hside, T2, T3⟩ :=
    pkCh_thinLin pkCh_Cl_symm hE hkN (by omega) (by omega) (by omega) (by omega) hcb hτ hTA hτf HG Hmr Hoc
  obtain ⟨V, hVo, -, -, hevV, hodV⟩ := pkCh_mkHead hN hE hPo (a := lo) (b := hi) hlo1 (by omega) hhiω hlo2 hhi2
  have hodW : ∀ x, x ∈ oddSide N W ↔ x ∈ Icc 1 N ∧ c + 1 ≤ cycPos N (headStart P) x + 1 ∧
      cycPos N (headStart P) x + 1 ≤ c + headLen N W := by
    intro x
    constructor
    · intro h
      have hx : x ∈ Icc 1 N := ((pkCh_headpos hN hE hWo).1 h).1
      have := (hmemP x hx).1 h
      exact ⟨hx, by omega, by omega⟩
    · rintro ⟨hx, h1, h2⟩
      exact (hmemP x hx).2 ⟨by omega, by omega⟩
  have hevW : ∀ x, x ∈ evenSide N W ↔ x ∈ Icc 1 N ∧ ¬ (c + 1 ≤ cycPos N (headStart P) x + 1 ∧
      cycPos N (headStart P) x + 1 ≤ c + headLen N W) := by
    intro x
    show x ∈ Icc 1 N \ oddSide N W ↔ _
    rw [mem_sdiff, hodW]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h => h2 ⟨h1, h⟩⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h => h2 h.2⟩
  have hEE : innerEE N S W ⊆ innerEE N S V := by
    rintro ⟨x, y⟩ h
    obtain ⟨hM, hx, hy⟩ := pkCh_mem_innerEE.1 h
    obtain ⟨hm, hx2, hy2⟩ := pkCh_mem_Mee.1 hM
    dsimp only at hx hy hx2 hy2
    obtain ⟨hxI, hxW⟩ := (hevW x).1 hx
    obtain ⟨hyI, hyW⟩ := (hevW y).1 hy
    have hd := mem_diagonals.1 (pkCh_mem_missing.1 hm).1
    dsimp only at hd
    have mx := pkCh_pos_mod hE hs hs2 hxI
    have my := pkCh_pos_mod hE hs hs2 hyI
    have hne : cycPos N (headStart P) x + 1 ≠ cycPos N (headStart P) y + 1 := fun h => by
      have := pkCo_cycPos_inj hs hxI hyI (by omega)
      omega
    have nC := pkCh_notCl hs hxI hyI hm
    rw [pkCh_phi_eq hs, pkCh_phi_eq hs] at nC
    have lx := pkCo_cycPos_lt hN1 (headStart P) x
    have ly := pkCo_cycPos_lt hN1 (headStart P) y
    have r1 := T3 _ _ (mem_Icc.2 ⟨by omega, by omega⟩) (mem_Icc.2 ⟨by omega, by omega⟩) (by omega) (by omega)
      hxW hyW hne nC
    have r2 := T3 _ _ (mem_Icc.2 ⟨by omega, by omega⟩) (mem_Icc.2 ⟨by omega, by omega⟩) (by omega) (by omega)
      hyW hxW (Ne.symm hne) (fun h => nC (pkCh_Cl_symm _ _ h))
    exact pkCh_mem_innerEE.2 ⟨hM, (hevV x).2 ⟨hxI, r1⟩, (hevV y).2 ⟨hyI, r2⟩⟩
  have hsubWV : oddSide N W ⊆ oddSide N V := fun x h => by
    obtain ⟨hx, h1, h2⟩ := (hodW x).1 h
    exact (hodV x).2 ⟨hx, by omega, by omega⟩
  have hsubVP : oddSide N V ⊆ oddSide N P := fun x h => by
    obtain ⟨hx, h1, h2⟩ := (hodV x).1 h
    exact (pkCh_headpos hN hE hPo).2 ⟨hx, by omega⟩
  have hevVW : evenSide N V ⊆ evenSide N W := fun x h => by
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
  have hEEeq : innerEE N S V = innerEE N S W := by
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
    have me := pkCh_pos_mod hE hs hs2 heI
    have mo := pkCh_pos_mod hE hs hs2 hoI
    have le := pkCo_cycPos_lt hN1 (headStart P) e
    have lo' := pkCo_cycPos_lt hN1 (headStart P) o
    apply pkCh_notCl_mm hs heI hoI hpm
    rw [pkCh_phi_eq hs, pkCh_phi_eq hs]
    by_cases hin : c + 1 ≤ cycPos N (headStart P) e + 1 ∧ cycPos N (headStart P) e + 1 ≤ c + headLen N W
    · exact Hmr _ _ (mem_Icc.2 ⟨by omega, by omega⟩) (mem_Icc.2 ⟨by omega, by omega⟩) (by omega) (by omega)
        hin.1 hin.2 (by omega)
    · exact T2 _ _ (mem_Icc.2 ⟨by omega, by omega⟩) (mem_Icc.2 ⟨by omega, by omega⟩) (by omega) (by omega)
        e1 e2 hin o1
  have hVp : V ∈ poleChords N S := by
    refine pkCh_mem_pole.2 ⟨hVo, hVc, ⟨(g1, g2), hEE hg⟩, ?_⟩
    obtain ⟨q, hq⟩ := (pkCh_mem_pole.1 hWp).2.2.2
    refine ⟨q, ?_⟩
    rw [hOOV, ← hoo]
    exact hq
  have hVcl : V ∈ cleanChords N S := mem_filter.2 ⟨hVo, hVc⟩
  have hWcl : W ∈ cleanChords N S := mem_filter.2 ⟨hWo, hWc⟩
  refine ⟨V, hVp, (ssubset_iff_of_subset hevVW).2 ?_, hsubVP, hOOV,
    pkCh_class_of hN hE hVcl hWcl hEEeq (hOOV.trans hoo.symm)⟩
  rcases hside with h | h
  · have hx := pkCh_psi_mem (s := headStart P) hN1 lo
    have px := pkCh_psi_pos hs (mem_Icc.2 ⟨hlo1, by omega⟩)
    refine ⟨rotLeg N (headStart P - 1) lo, (hevW _).2 ⟨hx, by rw [px]; omega⟩, fun hv => ?_⟩
    obtain ⟨-, h1⟩ := (hevV _).1 hv
    rw [px] at h1
    omega
  · have hx := pkCh_psi_mem (s := headStart P) hN1 hi
    have px := pkCh_psi_pos (y := hi) hs (mem_Icc.2 ⟨by omega, by omega⟩)
    refine ⟨rotLeg N (headStart P - 1) hi, (hevW _).2 ⟨hx, by rw [px]; omega⟩, fun hv => ?_⟩
    obtain ⟨-, h1⟩ := (hevV _).1 hv
    rw [px] at h1
    omega

/-- **(NoB1)** (BP App. D §6b): every o-clean `W ∈ 𝒫₁` with head inside the head of a canonical chord is in its class
(iterate the class-preserving B-step; tails shrink; head-minimality at the end). -/
theorem pkCh_noB1 {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} (hF : InFpi N S) {P : ℕ × ℕ}
    (hP : IsMinimalChord N S P) :
    ∀ n, ∀ W ∈ poleChords N S, (evenSide N W).card = n → oddSide N W ⊆ oddSide N P →
      innerOO N S W = innerOO N S P → W ∈ hitClass N S P := by
  obtain ⟨hPg, hmin⟩ := pkCh_minChord_iff.1 hP
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih W hW hn hsub hoo
  by_cases hB : NoFreeSep N S (tailStart W) (tailLen N W) 1
  · have hWg : W ∈ goodTail N S := pkCh_mem_goodTail.2 ⟨hW, hB⟩
    have heq : oddSide N W = oddSide N P := by
      by_contra hne
      exact hmin W hWg (Finset.ssubset_iff_subset_ne.2 ⟨hsub, hne⟩)
    refine pkCh_mem_hitClass.2 ⟨hW, ?_⟩
    show missing N S ∩ (sepPairs N (odds (oddSide N W)) ∪ sepPairs N (evens (Icc 1 N \ oddSide N W))) =
      missing N S ∩ (sepPairs N (odds (oddSide N P)) ∪ sepPairs N (evens (Icc 1 N \ oddSide N P)))
    rw [heq]
  · obtain ⟨τ0, hτ0, hτ0d⟩ : ∃ τ0 ∈ admSeps N (tailStart W) (tailLen N W) 1,
        Disjoint (sepIn N (tailStart W) (tailLen N W) τ0) (missing N S) := by
      by_contra hc
      exact hB (pkCh_noFree_iff.2 fun τ0 h hd => hc ⟨τ0, h, hd⟩)
    obtain ⟨V, hVp, hVW, hVP, hVoo, hVh⟩ := pkCh_noB1_step hN hE hF hPg hW hsub hoo hτ0 hτ0d
    have hV := ih _ (hn ▸ card_lt_card hVW) V hVp rfl hVP hVoo
    exact pkCh_mem_hitClass.2 ⟨hW, hVh.symm.trans (pkCh_mem_hitClass.1 hV).2⟩

/-- `S_G` transfers to a larger leg set that avoids both legs. -/
theorem pkCh_stTrans {G T : Finset ℕ} {u v : ℕ} (h : InST G u v) (hG : G ⊆ T) (hu : u ∉ T) (hv : v ∉ T) :
    InST T u v := by
  obtain ⟨-, -, ⟨g, hg, b1⟩, ⟨g', hg', b2⟩⟩ := pkCo_inST_iff.1 h
  exact pkCo_inST_iff.2 ⟨hu, hv, ⟨g, hG hg, b1⟩, ⟨g', hG hg', b2⟩⟩

/-- **Zone lemma** of the Side lemma (BP App. D §5a, cases A(a), A(b), B, C, D), linear setting of `P*` (head
`[1, ω]`): `Q` has head `[a, a1]` and fails at the odd leg `x`; the descent chord `W` has head `[x, w]`, is in `𝒫₀`
(`MW`) and carries the history fact (`F6`). A failing (b0)-shaped trace `T` of `B_W` avoids the zone `{N} ∪ [1, x − 2]`. -/
theorem pkCh_zone {N ω a a1 x w : ℕ} {T : Finset ℕ} {C : ℕ → ℕ → Prop} (hC : ∀ u v, C u v → C v u)
    (hN : N % 2 = 0) (hωN : ω + 3 ≤ N) (ha1 : 1 ≤ a) (ha : a % 2 = 1) (hx : x % 2 = 1) (hax : a < x)
    (hxa1 : x < a1) (ha1w : a1 ≤ w) (hwω : w ≤ ω)
    (HG : ∀ G : Finset ℕ, G ⊆ Icc 1 N → 2 ≤ G.card → ((∀ g ∈ G, g % 2 = 0) ∨ (∀ g ∈ G, g % 2 = 1)) →
      ∃ u v, (min u v, max u v) ∈ diagonals N ∧ InST G u v ∧ ¬ C u v)
    (HGm : ∀ p q, 1 ≤ p → p + 2 ≤ q → q ≤ N → ¬ (p = 1 ∧ q = N) → p % 2 ≠ q % 2 →
      ∃ u v, (min u v, max u v) ∈ diagonals N ∧ InST {p, q} u v ∧ ¬ C u v)
    (F1 : ∀ s r, a ≤ s → s + 1 ≤ x → x + 1 ≤ r → r ≤ a1 → C s r)
    (F2 : ∀ e o, 1 ≤ o → o ≤ N → e % 2 = 0 → o % 2 = 1 → a ≤ e → e ≤ a1 → ¬ (a ≤ o ∧ o ≤ a1) → C e o)
    (F3 : ∀ u v, u % 2 = 1 → v % 2 = 1 → 1 ≤ u → u ≤ ω → 1 ≤ v → v ≤ ω → ¬ (a ≤ u ∧ u ≤ a1) → C u v)
    (MW : ∀ e o, 1 ≤ o → o ≤ N → e % 2 = 0 → o % 2 = 1 → x ≤ e → e ≤ w → ¬ (x ≤ o ∧ o ≤ w) → C e o)
    (F6 : ∀ r s, r % 2 = 0 → a1 + 1 ≤ r → r ≤ w → 1 ≤ s → s + 1 ≤ x → C r s)
    (hT : AdmSepCompl N x w T) (hTA : TailAvoiding N ω T) (hf : ∀ u v, InST (Icc x w ∪ T) u v → C u v) :
    ∀ t ∈ T, ¬ (t = N ∨ t + 2 ≤ x) := by
  obtain ⟨hne, hsubT, hsing⟩ := pkCh_asc_facts hT
  have hTI : ∀ t ∈ T, (1 ≤ t ∧ t ≤ N) ∧ ¬ (x ≤ t ∧ t ≤ w) ∧ t ≠ w + 1 ∧ t ≠ (if x = 1 then N else x - 1) :=
    fun t ht => pkCh_mem_intCompl.1 (hsubT ht)
  have hx1 : x ≠ 1 := by omega
  obtain ⟨hTA1, hTA2⟩ := pkCh_ta_iff.1 hTA
  have hTW : ∀ t ∈ T, ¬ (ω + 2 ≤ t ∧ t ≤ N - 1) := fun t ht h => disjoint_left.1 hTA1 ht (mem_Icc.2 h)
  -- (X) and (Y)
  have hX : ∀ s r, a ≤ s → s + 1 ≤ x → x + 1 ≤ r → r ≤ w → C s r := by
    intro s r h1 h2 h3 h4
    by_cases hr : r ≤ a1
    · exact F1 s r h1 h2 h3 hr
    · rcases Nat.mod_two_eq_zero_or_one s with hs | hs <;> rcases Nat.mod_two_eq_zero_or_one r with hr' | hr'
      · exact hC _ _ (F6 r s hr' (by omega) h4 (by omega) h2)
      · exact F2 s r (by omega) (by omega) hs hr' h1 (by omega) (by omega)
      · exact hC _ _ (MW r s (by omega) (by omega) hr' hs (by omega) h4 (by omega))
      · exact hC _ _ (F3 r s hr' hs (by omega) (by omega) (by omega) (by omega) (by omega))
  have hY : ∀ o u, o % 2 = 1 → 1 ≤ o → o + 1 ≤ a → a ≤ u → u ≤ w → C o u := by
    intro o u h1 h2 h3 h4 h5
    rcases Nat.mod_two_eq_zero_or_one u with hu | hu
    · by_cases hua : u ≤ a1
      · exact hC _ _ (F2 u o h2 (by omega) hu h1 h4 hua (by omega))
      · exact hC _ _ (MW u o h2 (by omega) hu h1 (by omega) h5 (by omega))
    · exact F3 o u h1 hu h2 (by omega) (by omega) (by omega) (by omega)
  -- the other leg: odd traces are odd legs of `D`
  have hsmall : ∀ t ∈ T, ¬ (w + 2 ≤ t ∧ t ≤ ω + 1) → t = N ∨ t + 2 ≤ x := by
    intro t ht h
    obtain ⟨⟨t1, tN⟩, txw, tw1, tx1⟩ := hTI t ht
    rw [if_neg hx1] at tx1
    have := hTW t ht
    omega
  intro t ht hz
  by_cases hev : ∃ y ∈ T, y % 2 = 0
  · -- an even singleton `{y}`: cases A(a), C (and their wrap at `N`)
    obtain ⟨y, hy, hy2⟩ := hev
    have hTy : T = {y} := hsing y hy hy2
    rw [hTy] at hf
    rw [hTy, mem_singleton] at ht
    subst ht
    obtain ⟨⟨y1, yN⟩, yxw, yw1, yx1⟩ := hTI t hy
    rw [if_neg hx1] at yx1
    have hyT : ∀ z, z ∈ Icc x w ∪ {t} ↔ (x ≤ z ∧ z ≤ w) ∨ z = t := by
      intro z; rw [mem_union, mem_Icc, mem_singleton]
    by_cases hyN : t = N
    · by_cases ha3 : a = 1
      · -- G = {x, N}: A(a) at `y = N = α − 1 = a − 1`
        obtain ⟨u, v, hd, hst, hc⟩ := HGm x N (by omega) (by omega) (le_refl _) (by omega) (by omega)
        have hd' := mem_diagonals.1 hd
        simp only at hd'
        obtain ⟨hu, hv, ⟨g, hg, b1⟩, ⟨g', hg', b2⟩⟩ := pkCo_inST_iff.1 hst
        rw [mem_insert, mem_singleton] at hu hv hg hg'
        have key : ∀ s v, 1 ≤ s → s + 1 ≤ x → x + 1 ≤ v → v + 1 ≤ N → C s v := by
          intro s v h1 h2 h3 h4
          by_cases hvw : v ≤ w
          · exact hX s v (by omega) h2 h3 hvw
          · apply hf
            rw [pkCo_inST_iff, hyT, hyT]
            exact ⟨by omega, by omega, ⟨x, (hyT x).2 (Or.inl ⟨le_refl _, by omega⟩), by omega, by omega⟩,
              ⟨t, (hyT t).2 (Or.inr rfl), Or.inr (by omega)⟩⟩
        rcases (show (u + 1 ≤ x ∧ x + 1 ≤ v ∧ v + 1 ≤ N) ∨ (v + 1 ≤ x ∧ x + 1 ≤ u ∧ u + 1 ≤ N) by omega) with h | h
        · exact hc (key u v (by omega) h.1 h.2.1 h.2.2)
        · exact hc (hC _ _ (key v u (by omega) h.1 h.2.1 h.2.2))
      · -- C at the wrap: G = {N} ∪ evens [2, a − 1]
        have hGsub : insert N ((Icc 2 (a - 1)).filter (fun z => z % 2 = 0)) ⊆ Icc 1 N := fun z hz => by
          rw [mem_insert, mem_filter, mem_Icc] at hz; rw [mem_Icc]; omega
        have hGc : 2 ≤ (insert N ((Icc 2 (a - 1)).filter (fun z => z % 2 = 0))).card :=
          one_lt_card.2 ⟨N, mem_insert_self _ _, 2, mem_insert_of_mem (mem_filter.2 ⟨mem_Icc.2 ⟨le_refl _,
            by omega⟩, rfl⟩), by omega⟩
        have hGp : ∀ g ∈ insert N ((Icc 2 (a - 1)).filter (fun z => z % 2 = 0)), g % 2 = 0 := fun g hg => by
          rw [mem_insert, mem_filter] at hg
          rcases hg with h | h
          · rw [h]; exact hN
          · exact h.2
        obtain ⟨u, v, hd, hst, hc⟩ := HG _ hGsub hGc (Or.inl hGp)
        have hd' := mem_diagonals.1 hd
        simp only at hd'
        have hvG := (pkCo_inST_iff.1 hst).2.1
        have huG := (pkCo_inST_iff.1 hst).1
        have key : ∀ o v, 1 ≤ o → o + 1 < a → o % 2 = 1 → 1 ≤ v → v ≤ N →
            v ∉ insert N ((Icc 2 (a - 1)).filter (fun z => z % 2 = 0)) → C o v := by
          intro o v h1 h2 h3 h4 h5 hvG
          rw [mem_insert, mem_filter, mem_Icc] at hvG
          by_cases hva : v < a
          · exact F3 o v h3 (by omega) h1 (by omega) h4 (by omega) (by omega)
          · by_cases hvw : v ≤ w
            · exact hY o v h3 h1 (by omega) (by omega) hvw
            · apply hf
              rw [pkCo_inST_iff, hyT, hyT]
              exact ⟨by omega, by omega, ⟨x, (hyT x).2 (Or.inl ⟨le_refl _, by omega⟩), by omega, by omega⟩,
                ⟨t, (hyT t).2 (Or.inr rfl), Or.inr (by omega)⟩⟩
        rcases pkCh_evGN ha (by omega) (by omega) (by omega) (by omega) hst with h | h
        · exact hc (key u v (by omega) h.1 h.2 (by omega) (by omega) hvG)
        · exact hc (hC _ _ (key v u (by omega) h.1 h.2 (by omega) (by omega) huG))
    · have hyx : t + 3 ≤ x := by omega
      by_cases hya : a ≤ t + 1
      · -- A(a): G = {y, x}
        obtain ⟨u, v, hd, hst, hc⟩ := HGm t x (by omega) (by omega) (by omega) (by omega) (by omega)
        have hd' := mem_diagonals.1 hd
        simp only at hd'
        obtain ⟨hu, hv, ⟨g, hg, b1⟩, ⟨g', hg', b2⟩⟩ := pkCo_inST_iff.1 hst
        rw [mem_insert, mem_singleton] at hu hv hg hg'
        have key : ∀ s v, t < s → s + 1 ≤ x → 1 ≤ v → v ≤ N → (v < t ∨ x < v) → C s v := by
          intro s v h1 h2 h3 h4 h5
          by_cases hvw : x < v ∧ v ≤ w
          · exact hX s v (by omega) h2 (by omega) hvw.2
          · apply hf
            rw [pkCo_inST_iff, hyT, hyT]
            rcases h5 with h5 | h5
            · exact ⟨by omega, by omega, ⟨t, (hyT t).2 (Or.inr rfl), by omega, by omega⟩,
                ⟨x, (hyT x).2 (Or.inl ⟨le_refl _, by omega⟩), Or.inr (by omega)⟩⟩
            · exact ⟨by omega, by omega, ⟨x, (hyT x).2 (Or.inl ⟨le_refl _, by omega⟩), by omega, by omega⟩,
                ⟨t, (hyT t).2 (Or.inr rfl), Or.inl (by omega)⟩⟩
        rcases (show (t < u ∧ u + 1 ≤ x ∧ (v < t ∨ x < v)) ∨ (t < v ∧ v + 1 ≤ x ∧ (u < t ∨ x < u)) by omega)
          with h | h
        · exact hc (key u v h.1 h.2.1 (by omega) (by omega) h.2.2)
        · exact hc (hC _ _ (key v u h.1 h.2.1 (by omega) (by omega) h.2.2))
      · -- C: G = evens [y, a − 1]
        have hGsub : (Icc t (a - 1)).filter (fun z => z % 2 = 0) ⊆ Icc 1 N := fun z hz => by
          rw [mem_filter, mem_Icc] at hz; rw [mem_Icc]; omega
        have hGc : 2 ≤ ((Icc t (a - 1)).filter (fun z => z % 2 = 0)).card :=
          one_lt_card.2 ⟨t, mem_filter.2 ⟨mem_Icc.2 ⟨le_refl _, by omega⟩, hy2⟩, a - 1,
            mem_filter.2 ⟨mem_Icc.2 ⟨by omega, le_refl _⟩, by omega⟩, by omega⟩
        obtain ⟨u, v, hd, hst, hc⟩ := HG _ hGsub hGc (Or.inl fun g hg => (mem_filter.1 hg).2)
        have hd' := mem_diagonals.1 hd
        simp only at hd'
        have hvG := (pkCo_inST_iff.1 hst).2.1
        have huG := (pkCo_inST_iff.1 hst).1
        have key : ∀ o v, t < o → o < a - 1 → o % 2 = 1 → 1 ≤ v → v ≤ N →
            v ∉ (Icc t (a - 1)).filter (fun z => z % 2 = 0) → C o v := by
          intro o v h1 h2 h3 h4 h5 hvG
          rw [mem_filter, mem_Icc] at hvG
          by_cases hvo : v % 2 = 1 ∧ v ≤ ω
          · exact F3 o v h3 hvo.1 (by omega) (by omega) h4 hvo.2 (by omega)
          · by_cases hvw : a ≤ v ∧ v ≤ w
            · exact hY o v h3 (by omega) (by omega) hvw.1 hvw.2
            · apply hf
              rw [pkCo_inST_iff, hyT, hyT]
              rcases (show v < t ∨ w < v by omega) with h6 | h6
              · exact ⟨by omega, by omega, ⟨t, (hyT t).2 (Or.inr rfl), by omega, by omega⟩,
                  ⟨x, (hyT x).2 (Or.inl ⟨le_refl _, by omega⟩), Or.inr (by omega)⟩⟩
              · exact ⟨by omega, by omega, ⟨x, (hyT x).2 (Or.inl ⟨le_refl _, by omega⟩), by omega, by omega⟩,
                  ⟨t, (hyT t).2 (Or.inr rfl), Or.inl (by omega)⟩⟩
        rcases pkCh_evG hst with h | h
        · exact hc (key u v h.1 h.2.1 h.2.2 (by omega) (by omega) hvG)
        · exact hc (hC _ _ (key v u h.1 h.2.1 h.2.2 (by omega) (by omega) huG))
  · -- an odd trace: cases A(b), B, D
    have hodd : ∀ z ∈ T, z % 2 = 1 := fun z hz => by
      by_contra h
      exact hev ⟨z, hz, by omega⟩
    have hTω : ∀ z ∈ T, ¬ (ω + 1 ≤ z ∧ z ≤ N) := fun z hz h =>
      disjoint_left.1 (hTA2 hodd) hz (mem_Icc.2 h)
    have hTpos : ∀ z ∈ T, (1 ≤ z ∧ z + 2 ≤ x) ∨ (w + 2 ≤ z ∧ z ≤ ω) := by
      intro z hz
      obtain ⟨⟨z1, zN⟩, zxw, zw1, zx1⟩ := hTI z hz
      rw [if_neg hx1] at zx1
      have := hTω z hz
      have := hodd z hz
      omega
    have hTT : ∀ z, z ∈ Icc x w ∪ T ↔ (x ≤ z ∧ z ≤ w) ∨ z ∈ T := by
      intro z; rw [mem_union, mem_Icc]
    -- a trace leg other than `x`-side legs is an odd leg of `D`
    have hDleg : ∀ s z, z ∈ T → a ≤ s → s + 1 ≤ x → ¬ (a ≤ z ∧ z + 2 ≤ x) → C s z := by
      intro s z hz h1 h2 h3
      have hz2 := hodd z hz
      have hzp := hTpos z hz
      rcases Nat.mod_two_eq_zero_or_one s with hs | hs
      · exact F2 s z (by omega) (by omega) hs hz2 h1 (by omega) (by omega)
      · exact hC _ _ (F3 z s hz2 hs (by omega) (by omega) (by omega) (by omega) (by omega))
    have ht2 := hodd t ht
    by_cases hA : ∃ z ∈ T, a ≤ z ∧ z + 2 ≤ x
    · -- A(b): G = T_A ∪ {x}
      obtain ⟨z0, hz0, hz0a, hz0x⟩ := hA
      have hGsub : insert x (T.filter (fun z => a ≤ z ∧ z + 2 ≤ x)) ⊆ Icc x w ∪ T := fun z hz => by
        rw [mem_insert, mem_filter] at hz
        rcases hz with h | h
        · exact (hTT z).2 (Or.inl ⟨by omega, by omega⟩)
        · exact mem_union_right _ h.1
      have hGI : insert x (T.filter (fun z => a ≤ z ∧ z + 2 ≤ x)) ⊆ Icc 1 N := fun z hz => by
        rw [mem_insert, mem_filter] at hz
        rcases hz with h | h
        · rw [mem_Icc]; omega
        · exact mem_Icc.2 (hTI z h.1).1
      have hGc : 2 ≤ (insert x (T.filter (fun z => a ≤ z ∧ z + 2 ≤ x))).card :=
        one_lt_card.2 ⟨x, mem_insert_self _ _, z0, mem_insert_of_mem (mem_filter.2 ⟨hz0, hz0a, hz0x⟩), by omega⟩
      have hGp : ∀ g ∈ insert x (T.filter (fun z => a ≤ z ∧ z + 2 ≤ x)), g % 2 = 1 := fun g hg => by
        rw [mem_insert, mem_filter] at hg
        rcases hg with h | h
        · rw [h]; exact hx
        · exact hodd g h.1
      obtain ⟨u, v, hd, hst, hc⟩ := HG _ hGI hGc (Or.inr hGp)
      have hd' := mem_diagonals.1 hd
      simp only at hd'
      obtain ⟨hu, hv, ⟨g, hg, b1⟩, ⟨g', hg', b2⟩⟩ := pkCo_inST_iff.1 hst
      have hgr : ∀ g ∈ insert x (T.filter (fun z => a ≤ z ∧ z + 2 ≤ x)), a ≤ g ∧ g ≤ x := fun g hg => by
        rw [mem_insert, mem_filter] at hg
        rcases hg with h | h
        · omega
        · omega
      have gg := hgr g hg
      have gg' := hgr g' hg'
      have key : ∀ s v, a ≤ s → s + 1 ≤ x → 1 ≤ v → v ≤ N →
          s ∉ insert x (T.filter (fun z => a ≤ z ∧ z + 2 ≤ x)) →
          v ∉ insert x (T.filter (fun z => a ≤ z ∧ z + 2 ≤ x)) →
          InST (insert x (T.filter (fun z => a ≤ z ∧ z + 2 ≤ x))) s v → C s v := by
        intro s v h1 h2 h3 h4 hsG hvG hsv
        have hsT : s ∉ T := fun h => hsG (mem_insert_of_mem (mem_filter.2 ⟨h, h1, by
          have := hodd s h
          obtain ⟨-, -, -, h'⟩ := hTI s h
          rw [if_neg hx1] at h'
          omega⟩))
        by_cases hvw : x ≤ v ∧ v ≤ w
        · have hvx : v ≠ x := fun h => hvG (h ▸ mem_insert_self _ _)
          exact hX s v h1 h2 (by omega) hvw.2
        · by_cases hvT : v ∈ T
          · refine hDleg s v hvT h1 h2 fun h => hvG (mem_insert_of_mem (mem_filter.2 ⟨hvT, h⟩))
          · exact hf _ _ (pkCh_stTrans hsv hGsub (fun h => by
              rw [hTT] at h
              rcases h with h | h
              · omega
              · exact hsT h) (fun h => by
              rw [hTT] at h
              rcases h with h | h
              · exact hvw h
              · exact hvT h))
      rcases (show (a ≤ u ∧ u + 1 ≤ x) ∨ (a ≤ v ∧ v + 1 ≤ x) by
        by_contra hcon
        have hux : u ≠ x := fun h => hu (h ▸ mem_insert_self _ _)
        have hvx : v ≠ x := fun h => hv (h ▸ mem_insert_self _ _)
        omega) with h | h
      · exact hc (key u v h.1 h.2 (by omega) (by omega) hu hv hst)
      · exact hc (hC _ _ (key v u h.1 h.2 (by omega) (by omega) hv hu (pkCo_inST_comm.1 hst)))
    · have hA' : ∀ z ∈ T, ¬ (a ≤ z ∧ z + 2 ≤ x) := fun z hz h => hA ⟨z, hz, h⟩
      by_cases hB : 3 ≤ a ∧ a - 2 ∈ T
      · -- B: G = {a − 1, x}
        obtain ⟨u, v, hd, hst, hc⟩ := HGm (a - 1) x (by omega) (by omega) (by omega) (by omega) (by omega)
        have hd' := mem_diagonals.1 hd
        simp only at hd'
        obtain ⟨hu, hv, ⟨g, hg, b1⟩, ⟨g', hg', b2⟩⟩ := pkCo_inST_iff.1 hst
        rw [mem_insert, mem_singleton] at hu hv hg hg'
        have key : ∀ s v, a ≤ s → s + 1 ≤ x → 1 ≤ v → v ≤ N → (v + 1 < a ∨ x < v) → C s v := by
          intro s v h1 h2 h3 h4 h5
          have hsT : s ∉ T := fun h => by
            have := hodd s h
            obtain ⟨-, -, -, h'⟩ := hTI s h
            rw [if_neg hx1] at h'
            exact hA' s h ⟨h1, by omega⟩
          by_cases hvw : x ≤ v ∧ v ≤ w
          · exact hX s v h1 h2 (by omega) hvw.2
          · by_cases hvT : v ∈ T
            · exact hDleg s v hvT h1 h2 (hA' v hvT)
            · apply hf
              rw [pkCo_inST_iff, hTT, hTT]
              refine ⟨fun h => by rcases h with h | h; omega; exact hsT h,
                fun h => by rcases h with h | h; exact hvw h; exact hvT h, ?_⟩
              have hxT : x ∈ Icc x w ∪ T := (hTT x).2 (Or.inl ⟨le_refl _, by omega⟩)
              rcases h5 with h5 | h5
              · have hva : v ≠ a - 2 := fun h => hvT (h ▸ hB.2)
                exact ⟨⟨a - 2, mem_union_right _ hB.2, by omega, by omega⟩, ⟨x, hxT, Or.inr (by omega)⟩⟩
              · exact ⟨⟨x, hxT, by omega, by omega⟩, ⟨a - 2, mem_union_right _ hB.2, Or.inl (by omega)⟩⟩
        rcases (show (a ≤ u ∧ u + 1 ≤ x ∧ (v + 1 < a ∨ x < v)) ∨ (a ≤ v ∧ v + 1 ≤ x ∧ (u + 1 < a ∨ x < u)) by
          omega) with h | h
        · exact hc (key u v h.1 h.2.1 (by omega) (by omega) h.2.2)
        · exact hc (hC _ _ (key v u h.1 h.2.1 (by omega) (by omega) h.2.2))
      · -- D: G = evens [t* + 1, a − 1], t* the last trace leg below `a`
        have hL : (T.filter (fun z => z < a)).Nonempty := ⟨t, mem_filter.2 ⟨ht, by
          have := hA' t ht
          omega⟩⟩
        have hm := mem_filter.1 ((T.filter (fun z => z < a)).max'_mem hL)
        obtain ⟨ts, hts⟩ : ∃ ts, (T.filter (fun z => z < a)).max' hL = ts := ⟨_, rfl⟩
        rw [hts] at hm
        have hmax : ∀ z ∈ T, z < a → z ≤ ts := fun z hz hza => by
          rw [← hts]; exact (T.filter (fun z => z < a)).le_max' z (mem_filter.2 ⟨hz, hza⟩)
        have hts2 := hodd ts hm.1
        have hts4 : ts + 4 ≤ a := by
          have : ts ≠ a - 2 := fun h => hB ⟨by omega, h ▸ hm.1⟩
          omega
        have hGsub : (Icc (ts + 1) (a - 1)).filter (fun z => z % 2 = 0) ⊆ Icc 1 N := fun z hz => by
          rw [mem_filter, mem_Icc] at hz; rw [mem_Icc]; omega
        have hGc : 2 ≤ ((Icc (ts + 1) (a - 1)).filter (fun z => z % 2 = 0)).card :=
          one_lt_card.2 ⟨ts + 1, mem_filter.2 ⟨mem_Icc.2 ⟨le_refl _, by omega⟩, by omega⟩, a - 1,
            mem_filter.2 ⟨mem_Icc.2 ⟨by omega, le_refl _⟩, by omega⟩, by omega⟩
        obtain ⟨u, v, hd, hst, hc⟩ := HG _ hGsub hGc (Or.inl fun g hg => (mem_filter.1 hg).2)
        have hd' := mem_diagonals.1 hd
        simp only at hd'
        have hvG := (pkCo_inST_iff.1 hst).2.1
        have huG := (pkCo_inST_iff.1 hst).1
        have key : ∀ o v, ts + 1 < o → o < a - 1 → o % 2 = 1 → 1 ≤ v → v ≤ N →
            v ∉ (Icc (ts + 1) (a - 1)).filter (fun z => z % 2 = 0) → C o v := by
          intro o v h1 h2 h3 h4 h5 hvG
          rw [mem_filter, mem_Icc] at hvG
          by_cases hvo : v % 2 = 1 ∧ v ≤ ω
          · exact F3 o v h3 hvo.1 (by omega) (by omega) h4 hvo.2 (by omega)
          · by_cases hvw : a ≤ v ∧ v ≤ w
            · exact hY o v h3 (by omega) (by omega) hvw.1 hvw.2
            · have hoT : o ∉ T := fun h => by
                have := hmax o h (by omega)
                omega
              have hvT : v ∉ T := fun h => hvo ⟨hodd v h, by have := hTpos v h; omega⟩
              apply hf
              rw [pkCo_inST_iff, hTT, hTT]
              refine ⟨fun h => by rcases h with h | h; omega; exact hoT h,
                fun h => by rcases h with h | h; omega; exact hvT h, ?_⟩
              have hxT : x ∈ Icc x w ∪ T := (hTT x).2 (Or.inl ⟨le_refl _, by omega⟩)
              rcases (show v < ts ∨ w < v by
                have : v ≠ ts := fun h => hvT (h ▸ hm.1)
                omega) with h6 | h6
              · exact ⟨⟨ts, mem_union_right _ hm.1, by omega, by omega⟩, ⟨x, hxT, Or.inr (by omega)⟩⟩
              · exact ⟨⟨x, hxT, by omega, by omega⟩, ⟨ts, mem_union_right _ hm.1, Or.inl (by omega)⟩⟩
        rcases pkCh_evG hst with h | h
        · exact hc (key u v h.1 h.2.1 h.2.2 (by omega) (by omega) hvG)
        · exact hc (hC _ _ (key v u h.1 h.2.1 h.2.2 (by omega) (by omega) huG))
/-- **Side lemma, linear core** (BP App. D §5a, right piece `R = [x, a1]`): along every B′-keeping descent from `Q_R`
the head stays `[x, w]`; stated as: no chord with head `[x, w]` (`a1 ≤ w ≤ ω`) in `𝒫₀` carrying the history fact
(F6) exists, given that each such chord fails `Sep_all` of its tail (`Hstep`: head-minimality of `P*`). Strong
induction on the tail size `N − w`; the zone lemma keeps the next head `[x, w⁺]`. -/
theorem pkCh_sideCore {N ω a a1 x : ℕ} {C : ℕ → ℕ → Prop} (hC : ∀ u v, C u v → C v u)
    (hN : N % 2 = 0) (hω : ω % 2 = 1) (hωN : ω + 3 ≤ N) (ha1 : 1 ≤ a) (ha : a % 2 = 1) (hx : x % 2 = 1)
    (hax : a < x) (hxa1 : x < a1)
    (HW : ∀ τ0 : Finset ℕ, τ0.Nonempty → τ0 ⊆ Icc (ω + 2) (N - 1) → (τ0.card = 1 ∨ ∀ t ∈ τ0, t % 2 = 1) →
      ∃ u v, u ∈ Icc (ω + 1) N ∧ v ∈ Icc (ω + 1) N ∧ u ∉ τ0 ∧ v ∉ τ0 ∧
        (∃ t ∈ τ0, min u v < t ∧ t < max u v) ∧ ¬ C u v)
    (HG : ∀ G : Finset ℕ, G ⊆ Icc 1 N → 2 ≤ G.card → ((∀ g ∈ G, g % 2 = 0) ∨ (∀ g ∈ G, g % 2 = 1)) →
      ∃ u v, (min u v, max u v) ∈ diagonals N ∧ InST G u v ∧ ¬ C u v)
    (HGm : ∀ p q, 1 ≤ p → p + 2 ≤ q → q ≤ N → ¬ (p = 1 ∧ q = N) → p % 2 ≠ q % 2 →
      ∃ u v, (min u v, max u v) ∈ diagonals N ∧ InST {p, q} u v ∧ ¬ C u v)
    (F1 : ∀ s r, a ≤ s → s + 1 ≤ x → x + 1 ≤ r → r ≤ a1 → C s r)
    (F2 : ∀ e o, 1 ≤ o → o ≤ N → e % 2 = 0 → o % 2 = 1 → a ≤ e → e ≤ a1 → ¬ (a ≤ o ∧ o ≤ a1) → C e o)
    (F3 : ∀ u v, u % 2 = 1 → v % 2 = 1 → 1 ≤ u → u ≤ ω → 1 ≤ v → v ≤ ω → ¬ (a ≤ u ∧ u ≤ a1) → C u v)
    (Hstep : ∀ w, a1 ≤ w → w ≤ ω → w % 2 = 1 →
      (∀ e o, 1 ≤ o → o ≤ N → e % 2 = 0 → o % 2 = 1 → x ≤ e → e ≤ w → ¬ (x ≤ o ∧ o ≤ w) → C e o) →
      ∃ T, AdmSepCompl N x w T ∧ ∀ u v, InST (Icc x w ∪ T) u v → C u v) :
    ∀ n w, n = N - w → a1 ≤ w → w ≤ ω → w % 2 = 1 →
      (∀ e o, 1 ≤ o → o ≤ N → e % 2 = 0 → o % 2 = 1 → x ≤ e → e ≤ w → ¬ (x ≤ o ∧ o ≤ w) → C e o) →
      (∀ r s, r % 2 = 0 → a1 + 1 ≤ r → r ≤ w → 1 ≤ s → s + 1 ≤ x → C r s) → False := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih w hn h1 h2 h3 hMW hF6
  obtain ⟨T, hT, hf⟩ := Hstep w h1 h2 h3 hMW
  have hTA := pkCh_b0 hN hω hωN (a := x) (b := w) (by omega) h2 HW hT hf
  have hz := pkCh_zone hC hN hωN ha1 ha hx hax hxa1 h1 h2 HG HGm F1 F2 F3 hMW hF6 hT hTA hf
  obtain ⟨hne, hsubT, hsing⟩ := pkCh_asc_facts hT
  have hx1 : x ≠ 1 := by omega
  obtain ⟨hTA1, -⟩ := pkCh_ta_iff.1 hTA
  have hTr : ∀ t ∈ T, w + 2 ≤ t ∧ t ≤ ω + 1 := by
    intro t ht
    obtain ⟨⟨t1, tN⟩, txw, tw1, tx1⟩ := pkCh_mem_intCompl.1 (hsubT ht)
    rw [if_neg hx1] at tx1
    have hW : ¬ (ω + 2 ≤ t ∧ t ≤ N - 1) := fun h => disjoint_left.1 hTA1 ht (mem_Icc.2 h)
    have := hz t ht
    omega
  obtain ⟨w', hw1, hw2, hw3, hwT, hwm⟩ : ∃ w', w < w' ∧ w' ≤ ω ∧ w' % 2 = 1 ∧ (∀ t ∈ T, t ≤ w' + 1) ∧
      ((w' ∈ T ∧ ∀ t ∈ T, t % 2 = 1) ∨ T = {w' + 1}) := by
    by_cases hev : ∃ y ∈ T, y % 2 = 0
    · obtain ⟨y, hy, hy2⟩ := hev
      have hTy := hsing y hy hy2
      obtain ⟨-, -, yw1, -⟩ := pkCh_mem_intCompl.1 (hsubT hy)
      have := hTr y hy
      refine ⟨y - 1, by omega, by omega, by omega, fun t ht => ?_, Or.inr ?_⟩
      · rw [hTy, mem_singleton] at ht; omega
      · rw [Nat.sub_add_cancel (by omega)]; exact hTy
    · have hodd : ∀ t ∈ T, t % 2 = 1 := fun t ht => by
        by_contra h
        exact hev ⟨t, ht, by omega⟩
      have hm := T.max'_mem hne
      have := hTr _ hm
      have := hodd _ hm
      refine ⟨T.max' hne, by omega, by omega, by omega, fun t ht => ?_, Or.inl ⟨hm, hodd⟩⟩
      have := T.le_max' t ht
      omega
  have hTop : ∃ tT ∈ T, w' ≤ tT ∧ tT ≤ w' + 1 ∧ ∀ e, e % 2 = 0 → e ≤ w' → e ∉ T := by
    rcases hwm with ⟨hm, hodd⟩ | hTy
    · exact ⟨w', hm, le_refl _, by omega, fun e he _ h => by have := hodd e h; omega⟩
    · refine ⟨w' + 1, by rw [hTy]; exact mem_singleton_self _, by omega, le_refl _, fun e he hew h => ?_⟩
      rw [hTy, mem_singleton] at h
      omega
  obtain ⟨tT, htT, htT1, htT2, hnoE⟩ := hTop
  have hxT : x ∈ Icc x w ∪ T := mem_union_left _ (mem_Icc.2 ⟨le_refl _, by omega⟩)
  have hsep : ∀ e o, e % 2 = 0 → w + 1 ≤ e → e ≤ w' → 1 ≤ o → o ≤ N → ¬ (x ≤ o ∧ o ≤ w') →
      (o % 2 = 1 ∨ o < x) → C e o := by
    intro e o he h1 h2 h3 h4 h5 h6
    apply hf
    have heT : e ∉ Icc x w ∪ T := by
      rw [mem_union, mem_Icc]
      rintro (h | h)
      · omega
      · exact hnoE e he h2 h
    have hoT : o ∉ Icc x w ∪ T := by
      rw [mem_union, mem_Icc]
      rintro (h | h)
      · omega
      · have := hTr o h
        have := hwT o h
        omega
    rw [pkCo_inST_iff]
    refine ⟨heT, hoT, ?_⟩
    rcases (show o < x ∨ w' < o by omega) with h | h
    · exact ⟨⟨x, hxT, by omega, by omega⟩, ⟨tT, mem_union_right _ htT, Or.inr (by omega)⟩⟩
    · have : tT < o := by
        have : o ≠ tT := fun h' => hoT (h' ▸ mem_union_right _ htT)
        omega
      exact ⟨⟨tT, mem_union_right _ htT, by omega, by omega⟩, ⟨x, hxT, Or.inl (by omega)⟩⟩
  refine ih (N - w') (by omega) w' rfl (by omega) hw2 hw3 ?_ ?_
  · intro e o h1 h2 he ho h3 h4 h5
    by_cases hew : e ≤ w
    · exact hMW e o h1 h2 he ho h3 hew (by omega)
    · exact hsep e o he (by omega) h4 h1 h2 h5 (Or.inl ho)
  · intro r s hr h1 h2 h3 h4
    by_cases hrw : r ≤ w
    · exact hF6 r s hr h1 hrw h3 h4
    · exact hsep r s hr (by omega) h2 h3 (by omega) (by omega) (Or.inr (by omega))
/-- `HGm` of the linear setting: F^π for the mixed-anchored diamonds. -/
theorem pkCh_HGm {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} (hF : InFpi N S) {s : ℕ}
    (hs : s ∈ Icc 1 N) (hs2 : s % 2 = 1) :
    ∀ p q, 1 ≤ p → p + 2 ≤ q → q ≤ N → ¬ (p = 1 ∧ q = N) → p % 2 ≠ q % 2 →
      ∃ u v, (min u v, max u v) ∈ diagonals N ∧ InST {p, q} u v ∧ ¬ pkCh_Cl N s S u v := by
  intro p q h1 h2 h3 h4 h5
  have hN1 : 1 ≤ N := by omega
  have hsI := mem_Icc.1 hs
  obtain ⟨-, -, hnG⟩ := pkCh_fpi_iff.1 hF
  have hG : ({p, q} : Finset ℕ) ⊆ Icc 1 N := fun z hz => by
    rw [mem_insert, mem_singleton] at hz; rw [mem_Icc]; omega
  have hpI : p ∈ Icc 1 N := mem_Icc.2 ⟨h1, by omega⟩
  have hqI : q ∈ Icc 1 N := mem_Icc.2 ⟨by omega, h3⟩
  have hsubψ : ({p, q} : Finset ℕ).image (rotLeg N (s - 1)) ⊆ Icc 1 N := fun z hz => by
    obtain ⟨y, -, rfl⟩ := mem_image.1 hz
    exact pkCh_psi_mem hN1 y
  have hGs : IsGSet N (({p, q} : Finset ℕ).image (rotLeg N (s - 1))) := by
    rw [image_insert, image_singleton]
    have pp := pkCh_psi_pos hs hpI
    have pq := pkCh_psi_pos hs hqI
    refine pkCh_mixed_of (pkCh_diag_pos hs (pkCh_psi_mem hN1 p) (pkCh_psi_mem hN1 q) ?_ ?_) ?_
    · rw [pp, pq]; omega
    · rw [pp, pq]; omega
    · rw [pkCh_psi_mod hN1 hE hsI.1 hs2, pkCh_psi_mod hN1 hE hsI.1 hs2]; exact h5
  have hmemF : sepPairs N (({p, q} : Finset ℕ).image (rotLeg N (s - 1))) ∈ gFamily N :=
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
  have hst : InST {p, q} (rotLeg N (N + 1 - s) q1) (rotLeg N (N + 1 - s) q2) := by
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

/-- **(Odd-below), right piece** (BP App. D §5b with the Side lemma §5a): a class member `Q` of the canonical `P*`
failing `Sep_all(A_Q)` at an odd singleton `{x0}` with an `O_in` pair on the far side of `x0` gives a `𝒮_B` chord
with head `⊊ A*`. -/
theorem pkCh_oddBelowR {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} (hF : InFpi N S) {P Q : ℕ × ℕ}
    (hP : IsMinimalChord N S P) (hQ : Q ∈ hitClass N S P) {x0 : ℕ}
    (hx0 : {x0} ∈ admSeps N (headStart Q) (headLen N Q) 0) (hx02 : x0 % 2 = 1)
    (hx0d : Disjoint (sepIn N (headStart Q) (headLen N Q) {x0}) (missing N S))
    (hR : ∃ f1 f2, (f1, f2) ∈ innerOO N S P ∧
      cycPos N (headStart P) x0 ≤ cycPos N (headStart P) f1 ∧ cycPos N (headStart P) x0 ≤ cycPos N (headStart P) f2) :
    False := by
  obtain ⟨hPg, hmin⟩ := pkCh_minChord_iff.1 hP
  obtain ⟨hPp, hPB⟩ := pkCh_mem_goodTail.1 hPg
  obtain ⟨hPo, -, ⟨⟨g1, g2⟩, hgP⟩, -⟩ := pkCh_mem_pole.1 hPp
  obtain ⟨hQp, hQh⟩ := pkCh_mem_hitClass.1 hQ
  obtain ⟨hQo, hQc, -, -⟩ := pkCh_mem_pole.1 hQp
  obtain ⟨-, -, -, -, -, hs, hs2, hk1, hk3, hkN⟩ := pkCh_sides hE hPo
  obtain ⟨-, -, -, -, -, hqs, hqs2, hqk1, hqk3, hqkN⟩ := pkCh_sides hE hQo
  have hN1 : 1 ≤ N := by omega
  have hsI := mem_Icc.1 hs
  have hsub := pkCh_int_top hN hE hPp hPB hQp hQh
  have hoo := pkCh_class_oo hN hE hPo hQo hQh
  obtain ⟨hcb, hc2, hmemP, hposP⟩ := pkCh_subHead hN hE hQo hPo hsub
  obtain ⟨c, hc⟩ : ∃ c, cycPos N (headStart P) (headStart Q) = c := ⟨_, rfl⟩
  rw [hc] at hcb hc2 hmemP hposP
  -- the failing leg `x0`, label `x`
  obtain ⟨hx0sub, -⟩ := pkCo_mem_admSeps.1 hx0
  obtain ⟨hx0I, hx01, hx02'⟩ := (pkCo_mem_intArc hqs (by omega)).1 (hx0sub (mem_singleton_self _))
  have hx0Q : x0 ∈ oddSide N Q := (pkCh_headpos hN hE hQo).2 ⟨hx0I, by omega⟩
  have hx0P := (hmemP x0 hx0I).1 hx0Q
  have hx0pos := hposP x0 hx0I hx0P.1
  obtain ⟨x, hxd⟩ : ∃ x, cycPos N (headStart P) x0 + 1 = x := ⟨_, rfl⟩
  have hxm := pkCh_pos_mod hE hs hs2 hx0I
  rw [hxd] at hxm
  have hlx := pkCo_cycPos_lt hN1 (headStart P) x0
  -- label facts for legs
  have hψ : ∀ y, y ∈ Icc 1 N → cycPos N (headStart P) (rotLeg N (headStart P - 1) y) = y - 1 :=
    fun y hy => pkCh_psi_pos hs hy
  have HG := pkCh_HG hN hE hF hs hs2
  have HGm := pkCh_HGm hN hE hF hs hs2
  have HW := pkCh_HW hN hE hPo hPB
  -- (F2) `minrect(Q)` clean
  have F2 : ∀ e o, 1 ≤ o → o ≤ N → e % 2 = 0 → o % 2 = 1 → c + 1 ≤ e → e ≤ c + headLen N Q →
      ¬ (c + 1 ≤ o ∧ o ≤ c + headLen N Q) → pkCh_Cl N (headStart P) S e o := by
    intro e o ho1 hoN he2 ho2 h1 h2 ho'
    have he : e ∈ Icc 1 N := mem_Icc.2 ⟨by omega, by omega⟩
    have ho : o ∈ Icc 1 N := mem_Icc.2 ⟨ho1, hoN⟩
    rw [pkCh_Cl_iff]
    rintro ⟨-, -, hm⟩
    have pe := hψ e he
    have po := hψ o ho
    have eW : rotLeg N (headStart P - 1) e ∈ oddSide N Q :=
      (hmemP _ (pkCh_psi_mem hN1 e)).2 (by rw [pe]; omega)
    have oW : rotLeg N (headStart P - 1) o ∈ evenSide N Q := by
      show rotLeg N (headStart P - 1) o ∈ Icc 1 N \ oddSide N Q
      refine mem_sdiff.2 ⟨pkCh_psi_mem hN1 o, fun h => ?_⟩
      have := (hmemP _ (pkCh_psi_mem hN1 o)).1 h
      rw [po] at this
      omega
    have me := pkCh_psi_mod hN1 hE hsI.1 hs2 e
    have mo := pkCh_psi_mod hN1 hE hsI.1 hs2 o
    have hr : (min (rotLeg N (headStart P - 1) e) (rotLeg N (headStart P - 1) o),
        max (rotLeg N (headStart P - 1) e) (rotLeg N (headStart P - 1) o)) ∈ minRect N Q :=
      pkCh_mem_minRect.2 ⟨_, pkCh_mem_evens.2 ⟨eW, by omega⟩, _, pkCh_mem_odds.2 ⟨oW, by omega⟩, rfl⟩
    rcases hm with hm | hm
    · have hd := mem_diagonals.1 (pkCh_mem_missing.1 hm).1
      dsimp only at hd
      rw [min_eq_left (by omega), max_eq_right (by omega)] at hr
      exact disjoint_left.1 hQc hr hm
    · have hd := mem_diagonals.1 (pkCh_mem_missing.1 hm).1
      dsimp only at hd
      rw [min_eq_right (by omega), max_eq_left (by omega)] at hr
      exact disjoint_left.1 hQc hr hm
  -- (F3) o-clean
  have F3 : ∀ u v, u % 2 = 1 → v % 2 = 1 → 1 ≤ u → u ≤ headLen N P → 1 ≤ v → v ≤ headLen N P →
      ¬ (c + 1 ≤ u ∧ u ≤ c + headLen N Q) → pkCh_Cl N (headStart P) S u v := by
    intro u v hu hv u1 u2 v1 v2 hu'
    rw [pkCh_Cl_iff]
    rintro ⟨huI, hvI, hm⟩
    have pu := hψ u huI
    have pv := hψ v hvI
    have mu := pkCh_psi_mod hN1 hE hsI.1 hs2 u
    have mv := pkCh_psi_mod hN1 hE hsI.1 hs2 v
    have uP : rotLeg N (headStart P - 1) u ∈ oddSide N P :=
      (pkCh_headpos hN hE hPo).2 ⟨pkCh_psi_mem hN1 u, by rw [pu]; omega⟩
    have vP : rotLeg N (headStart P - 1) v ∈ oddSide N P :=
      (pkCh_headpos hN hE hPo).2 ⟨pkCh_psi_mem hN1 v, by rw [pv]; omega⟩
    have key : ∀ x y, (x, y) ∈ missing N S → x % 2 = 1 → y % 2 = 1 → x ∈ oddSide N P → y ∈ oddSide N P →
        x ∈ oddSide N Q ∧ y ∈ oddSide N Q := by
      intro x y hm hx hy hxP hyP
      have hin : (x, y) ∈ innerOO N S P := pkCh_mem_innerOO.2 ⟨pkCh_mem_Moo.2 ⟨hm, hx, hy⟩, hxP, hyP⟩
      rw [← hoo] at hin
      exact ⟨(pkCh_mem_innerOO.1 hin).2.1, (pkCh_mem_innerOO.1 hin).2.2⟩
    have uW : rotLeg N (headStart P - 1) u ∉ oddSide N Q := fun h => by
      have := (hmemP _ (pkCh_psi_mem hN1 u)).1 h
      rw [pu] at this
      omega
    rcases hm with hm | hm
    · exact uW (key _ _ hm (by omega) (by omega) uP vP).1
    · exact uW (key _ _ hm (by omega) (by omega) vP uP).2
  -- (F1) `Q` fails at `{x0}`
  have F1 : ∀ s r, c + 1 ≤ s → s + 1 ≤ x → x + 1 ≤ r → r ≤ c + headLen N Q → pkCh_Cl N (headStart P) S s r := by
    intro s r h1 h2 h3 h4
    have hsI' : s ∈ Icc 1 N := mem_Icc.2 ⟨by omega, by omega⟩
    have hrI : r ∈ Icc 1 N := mem_Icc.2 ⟨by omega, by omega⟩
    rw [pkCh_Cl_iff]
    rintro ⟨-, -, hm⟩
    have ps := hψ s hsI'
    have pr := hψ r hrI
    have qs := hposP _ (pkCh_psi_mem hN1 s) (by rw [ps]; omega)
    have qr := hposP _ (pkCh_psi_mem hN1 r) (by rw [pr]; omega)
    rw [ps] at qs
    rw [pr] at qr
    have aS : rotLeg N (headStart P - 1) s ∈ cycArc N (headStart Q) (headLen N Q) :=
      (pkCo_mem_cycArc_pos hqs (by omega)).2 ⟨pkCh_psi_mem hN1 s, by rw [qs]; omega⟩
    have aR : rotLeg N (headStart P - 1) r ∈ cycArc N (headStart Q) (headLen N Q) :=
      (pkCo_mem_cycArc_pos hqs (by omega)).2 ⟨pkCh_psi_mem hN1 r, by rw [qr]; omega⟩
    have nS : rotLeg N (headStart P - 1) s ∉ ({x0} : Finset ℕ) := fun h => by
      rw [mem_singleton] at h
      have := congrArg (cycPos N (headStart P)) h
      rw [ps] at this
      omega
    have nR : rotLeg N (headStart P - 1) r ∉ ({x0} : Finset ℕ) := fun h => by
      rw [mem_singleton] at h
      have := congrArg (cycPos N (headStart P)) h
      rw [pr] at this
      omega
    rcases hm with hm | hm
    · exact disjoint_left.1 hx0d (pkCo_mem_sepIn.2 ⟨(pkCh_mem_missing.1 hm).1, aS, aR, nS, nR, x0,
        mem_singleton_self _, by rw [qs, qr, hx0pos]; omega, by rw [qs, qr, hx0pos]; omega⟩) hm
    · exact disjoint_left.1 hx0d (pkCo_mem_sepIn.2 ⟨(pkCh_mem_missing.1 hm).1, aR, aS, nR, nS, x0,
        mem_singleton_self _, by rw [qs, qr, hx0pos]; omega, by rw [qs, qr, hx0pos]; omega⟩) hm
  -- the `O_in` pair in `[x, a1]`
  obtain ⟨f1, f2, hf, hf1, hf2⟩ := hR
  have hfQ : (f1, f2) ∈ innerOO N S Q := by rw [hoo]; exact hf
  obtain ⟨hfM, hf1Q, hf2Q⟩ := pkCh_mem_innerOO.1 hfQ
  obtain ⟨hfm, hf1o, hf2o⟩ := pkCh_mem_Moo.1 hfM
  dsimp only at hf1Q hf2Q hf1o hf2o
  have hf1I := ((pkCh_headpos hN hE hQo).1 hf1Q).1
  have hf2I := ((pkCh_headpos hN hE hQo).1 hf2Q).1
  have hf1P := (hmemP f1 hf1I).1 hf1Q
  have hf2P := (hmemP f2 hf2I).1 hf2Q
  -- `Hstep`: a chord with head `[x, w]` in `𝒫₀` is in `𝒫₁`, not in `𝒮_B` (head-minimality), so its tail fails
  have Hstep : ∀ w, c + headLen N Q ≤ w → w ≤ headLen N P → w % 2 = 1 →
      (∀ e o, 1 ≤ o → o ≤ N → e % 2 = 0 → o % 2 = 1 → x ≤ e → e ≤ w → ¬ (x ≤ o ∧ o ≤ w) →
        pkCh_Cl N (headStart P) S e o) →
      ∃ T, AdmSepCompl N x w T ∧ ∀ u v, InST (Icc x w ∪ T) u v → pkCh_Cl N (headStart P) S u v := by
    intro w h1 h2 h3 hMW
    obtain ⟨V, hVo, hVts, hVtl, hevV, hodV⟩ := pkCh_mkHead hN hE hPo (a := x) (b := w) (by omega) (by omega) h2
      (by omega) h3
    have hVc : Disjoint (minRect N V) (missing N S) := by
      refine disjoint_left.2 fun p hp hpm => ?_
      obtain ⟨e, he, o, ho, rfl⟩ := pkCh_mem_minRect.1 hp
      obtain ⟨heV, he2⟩ := pkCh_mem_evens.1 he
      obtain ⟨hoV, ho2⟩ := pkCh_mem_odds.1 ho
      obtain ⟨heI, e1, e2⟩ := (hodV e).1 heV
      obtain ⟨hoI, o1⟩ := (hevV o).1 hoV
      have me := pkCh_pos_mod hE hs hs2 heI
      have mo := pkCh_pos_mod hE hs hs2 hoI
      have le := pkCo_cycPos_lt hN1 (headStart P) e
      have lo := pkCo_cycPos_lt hN1 (headStart P) o
      apply pkCh_notCl_mm hs heI hoI hpm
      rw [pkCh_phi_eq hs, pkCh_phi_eq hs]
      exact hMW _ _ (by omega) (by omega) (by omega) (by omega) e1 e2 (by omega)
    have hVp : V ∈ poleChords N S := by
      refine pkCh_mem_pole.2 ⟨hVo, hVc, ?_, ⟨(f1, f2), pkCh_mem_innerOO.2 ⟨hfM, (hodV f1).2 ⟨hf1I, by omega, by omega⟩,
        (hodV f2).2 ⟨hf2I, by omega, by omega⟩⟩⟩⟩
      obtain ⟨⟨e1, e2⟩, he⟩ := (pkCh_mem_pole.1 hPp).2.2.1
      obtain ⟨heM, he1, he2⟩ := pkCh_mem_innerEE.1 he
      dsimp only at he1 he2
      obtain ⟨k1, k1'⟩ := (pkCh_evenpos hN hE hPo).1 he1
      obtain ⟨k2, k2'⟩ := (pkCh_evenpos hN hE hPo).1 he2
      exact ⟨(e1, e2), pkCh_mem_innerEE.2 ⟨heM, (hevV e1).2 ⟨k1, Or.inr (by omega)⟩,
        (hevV e2).2 ⟨k2, Or.inr (by omega)⟩⟩⟩
    have hVs : oddSide N V ⊂ oddSide N P := by
      have hsub' : oddSide N V ⊆ oddSide N P := fun y hy => by
        obtain ⟨hyI, y1, y2⟩ := (hodV y).1 hy
        exact (pkCh_headpos hN hE hPo).2 ⟨hyI, by omega⟩
      refine (ssubset_iff_of_subset hsub').2 ⟨headStart P, (pkCh_headpos hN hE hPo).2 ⟨hs, by
        rw [pkCo_cycPos_self hs]; omega⟩, fun h => ?_⟩
      obtain ⟨-, y1, -⟩ := (hodV _).1 h
      rw [pkCo_cycPos_self hs] at y1
      omega
    have hVng : V ∉ goodTail N S := fun h => hmin V h hVs
    obtain ⟨τ0, hτ0, hτ0d⟩ : ∃ τ0 ∈ admSeps N (tailStart V) (tailLen N V) 1,
        Disjoint (sepIn N (tailStart V) (tailLen N V) τ0) (missing N S) := by
      by_contra hcon
      exact hVng (pkCh_mem_goodTail.2 ⟨hVp, pkCh_noFree_iff.2 fun τ0 h hd => hcon ⟨τ0, h, hd⟩⟩)
    exact pkCh_tailLin hN hE hPo hVo (by omega) (by omega) h2 hVts hVtl hτ0 hτ0d
  refine pkCh_sideCore (a := c + 1) (a1 := c + headLen N Q) (x := x) pkCh_Cl_symm hE hk1 hkN (by omega) (by omega)
    (by omega) (by omega) (by omega) HW HG HGm F1 (fun e o h1 h2 h3 h4 h5 h6 h7 => F2 e o h1 h2 h3 h4 h5 h6 h7) F3
    Hstep _ (c + headLen N Q) rfl (le_refl _) hcb (by omega) ?_ ?_
  · intro e o h1 h2 he ho h3 h4 h5
    by_cases hoa : c + 1 ≤ o ∧ o ≤ c + headLen N Q
    · exact pkCh_Cl_symm _ _ (F1 o e hoa.1 (by omega) (by omega) h4)
    · exact F2 e o h1 h2 he ho (by omega) h4 hoa
  · intro r s hr h1 h2
    omega
/-- **Zone lemma, mirror piece** (BP App. D §5a mirror): descent heads `[w, x]` (`w ≤ a`), zone `[x + 2, ω + 1]`. -/
theorem pkCh_zoneL {N ω a a1 x w : ℕ} {T : Finset ℕ} {C : ℕ → ℕ → Prop} (hC : ∀ u v, C u v → C v u)
    (hN : N % 2 = 0) (hωN : ω + 3 ≤ N) (hw1 : 1 ≤ w) (hwa : w ≤ a) (ha1o : a1 % 2 = 1) (hx : x % 2 = 1)
    (hax : a < x) (hxa1 : x < a1) (ha1ω : a1 ≤ ω)
    (HG : ∀ G : Finset ℕ, G ⊆ Icc 1 N → 2 ≤ G.card → ((∀ g ∈ G, g % 2 = 0) ∨ (∀ g ∈ G, g % 2 = 1)) →
      ∃ u v, (min u v, max u v) ∈ diagonals N ∧ InST G u v ∧ ¬ C u v)
    (HGm : ∀ p q, 1 ≤ p → p + 2 ≤ q → q ≤ N → ¬ (p = 1 ∧ q = N) → p % 2 ≠ q % 2 →
      ∃ u v, (min u v, max u v) ∈ diagonals N ∧ InST {p, q} u v ∧ ¬ C u v)
    (F1 : ∀ s r, a ≤ s → s + 1 ≤ x → x + 1 ≤ r → r ≤ a1 → C s r)
    (F2 : ∀ e o, 1 ≤ o → o ≤ N → e % 2 = 0 → o % 2 = 1 → a ≤ e → e ≤ a1 → ¬ (a ≤ o ∧ o ≤ a1) → C e o)
    (F3 : ∀ u v, u % 2 = 1 → v % 2 = 1 → 1 ≤ u → u ≤ ω → 1 ≤ v → v ≤ ω → ¬ (a ≤ u ∧ u ≤ a1) → C u v)
    (MW : ∀ e o, 1 ≤ o → o ≤ N → e % 2 = 0 → o % 2 = 1 → w ≤ e → e ≤ x → ¬ (w ≤ o ∧ o ≤ x) → C e o)
    (F6 : ∀ r s, r % 2 = 0 → w ≤ r → r + 1 ≤ a → x + 1 ≤ s → s ≤ ω → C r s)
    (hT : AdmSepCompl N w x T) (hTA : TailAvoiding N ω T) (hf : ∀ u v, InST (Icc w x ∪ T) u v → C u v) :
    ∀ t ∈ T, ¬ (x + 2 ≤ t ∧ t ≤ ω + 1) := by
  obtain ⟨hne, hsubT, hsing⟩ := pkCh_asc_facts hT
  have hTI : ∀ t ∈ T, (1 ≤ t ∧ t ≤ N) ∧ ¬ (w ≤ t ∧ t ≤ x) ∧ t ≠ x + 1 ∧ t ≠ (if w = 1 then N else w - 1) :=
    fun t ht => pkCh_mem_intCompl.1 (hsubT ht)
  obtain ⟨hTA1, hTA2⟩ := pkCh_ta_iff.1 hTA
  have hX : ∀ s r, x + 1 ≤ s → s ≤ a1 → w ≤ r → r + 1 ≤ x → C s r := by
    intro s r h1 h2 h3 h4
    by_cases hr : a ≤ r
    · exact hC _ _ (F1 r s hr h4 h1 h2)
    · rcases Nat.mod_two_eq_zero_or_one s with hs | hs <;> rcases Nat.mod_two_eq_zero_or_one r with hr' | hr'
      · exact hC _ _ (F6 r s hr' h3 (by omega) h1 (by omega))
      · exact F2 s r (by omega) (by omega) hs hr' (by omega) h2 (by omega)
      · exact hC _ _ (MW r s (by omega) (by omega) hr' hs h3 (by omega) (by omega))
      · exact hC _ _ (F3 r s hr' hs (by omega) (by omega) (by omega) (by omega) (by omega))
  have hY : ∀ o u, o % 2 = 1 → a1 + 1 ≤ o → o ≤ ω → w ≤ u → u ≤ a1 → C o u := by
    intro o u h1 h2 h3 h4 h5
    rcases Nat.mod_two_eq_zero_or_one u with hu | hu
    · by_cases hua : a ≤ u
      · exact hC _ _ (F2 u o (by omega) (by omega) hu h1 hua h5 (by omega))
      · exact hC _ _ (MW u o (by omega) (by omega) hu h1 h4 (by omega) (by omega))
    · exact F3 o u h1 hu (by omega) h3 (by omega) (by omega) (by omega)
  intro t ht hz
  by_cases hev : ∃ y ∈ T, y % 2 = 0
  · obtain ⟨y, hy, hy2⟩ := hev
    have hTy : T = {y} := hsing y hy hy2
    rw [hTy] at hf
    rw [hTy, mem_singleton] at ht
    subst ht
    obtain ⟨⟨y1, yN⟩, yxw, yx1, -⟩ := hTI t hy
    have hyT : ∀ z, z ∈ Icc w x ∪ {t} ↔ (w ≤ z ∧ z ≤ x) ∨ z = t := by
      intro z; rw [mem_union, mem_Icc, mem_singleton]
    have hxT : x ∈ Icc w x ∪ {t} := (hyT x).2 (Or.inl ⟨by omega, le_refl _⟩)
    have htT : t ∈ Icc w x ∪ {t} := (hyT t).2 (Or.inr rfl)
    by_cases hya : t ≤ a1 + 1
    · -- A(a)': G = {x, y}
      obtain ⟨u, v, hd, hst, hc⟩ := HGm x t (by omega) (by omega) (by omega) (by omega) (by omega)
      have hd' := mem_diagonals.1 hd
      simp only at hd'
      obtain ⟨hu, hv, ⟨g, hg, b1⟩, ⟨g', hg', b2⟩⟩ := pkCo_inST_iff.1 hst
      rw [mem_insert, mem_singleton] at hu hv hg hg'
      have key : ∀ s v, x < s → s < t → 1 ≤ v → v ≤ N → (v < x ∨ t < v) → C s v := by
        intro s v h1 h2 h3 h4 h5
        by_cases hvw : w ≤ v ∧ v < x
        · exact hX s v (by omega) (by omega) hvw.1 (by omega)
        · apply hf
          rw [pkCo_inST_iff, hyT, hyT]
          rcases h5 with h5 | h5
          · exact ⟨by omega, by omega, ⟨x, hxT, by omega, by omega⟩, ⟨t, htT, Or.inr (by omega)⟩⟩
          · exact ⟨by omega, by omega, ⟨t, htT, by omega, by omega⟩, ⟨x, hxT, Or.inl (by omega)⟩⟩
      rcases (show (x < u ∧ u < t ∧ (v < x ∨ t < v)) ∨ (x < v ∧ v < t ∧ (u < x ∨ t < u)) by omega) with h | h
      · exact hc (key u v h.1 h.2.1 (by omega) (by omega) h.2.2)
      · exact hc (hC _ _ (key v u h.1 h.2.1 (by omega) (by omega) h.2.2))
    · -- C': G = evens [a1 + 1, y]
      have hGsub : (Icc (a1 + 1) t).filter (fun z => z % 2 = 0) ⊆ Icc 1 N := fun z hz => by
        rw [mem_filter, mem_Icc] at hz; rw [mem_Icc]; omega
      have hGc : 2 ≤ ((Icc (a1 + 1) t).filter (fun z => z % 2 = 0)).card :=
        one_lt_card.2 ⟨a1 + 1, mem_filter.2 ⟨mem_Icc.2 ⟨le_refl _, by omega⟩, by omega⟩, t,
          mem_filter.2 ⟨mem_Icc.2 ⟨by omega, le_refl _⟩, hy2⟩, by omega⟩
      obtain ⟨u, v, hd, hst, hc⟩ := HG _ hGsub hGc (Or.inl fun g hg => (mem_filter.1 hg).2)
      have hd' := mem_diagonals.1 hd
      simp only at hd'
      have hvG := (pkCo_inST_iff.1 hst).2.1
      have huG := (pkCo_inST_iff.1 hst).1
      have key : ∀ o v, a1 + 1 < o → o < t → o % 2 = 1 → 1 ≤ v → v ≤ N →
          v ∉ (Icc (a1 + 1) t).filter (fun z => z % 2 = 0) → C o v := by
        intro o v h1 h2 h3 h4 h5 hvG
        rw [mem_filter, mem_Icc] at hvG
        by_cases hvo : v % 2 = 1 ∧ v ≤ ω
        · exact F3 o v h3 hvo.1 (by omega) (by omega) h4 hvo.2 (by omega)
        · by_cases hvw : w ≤ v ∧ v ≤ a1
          · exact hY o v h3 (by omega) (by omega) hvw.1 hvw.2
          · apply hf
            rw [pkCo_inST_iff, hyT, hyT]
            rcases (show v < w ∨ t < v by omega) with h6 | h6
            · exact ⟨by omega, by omega, ⟨x, hxT, by omega, by omega⟩, ⟨t, htT, Or.inr (by omega)⟩⟩
            · exact ⟨by omega, by omega, ⟨t, htT, by omega, by omega⟩, ⟨x, hxT, Or.inl (by omega)⟩⟩
      rcases pkCh_evG hst with h | h
      · exact hc (key u v h.1 h.2.1 h.2.2 (by omega) (by omega) hvG)
      · exact hc (hC _ _ (key v u h.1 h.2.1 h.2.2 (by omega) (by omega) huG))
  · have hodd : ∀ z ∈ T, z % 2 = 1 := fun z hz => by
      by_contra h
      exact hev ⟨z, hz, by omega⟩
    have hTω : ∀ z ∈ T, ¬ (ω + 1 ≤ z ∧ z ≤ N) := fun z hz h =>
      disjoint_left.1 (hTA2 hodd) hz (mem_Icc.2 h)
    have hTpos : ∀ z ∈ T, (1 ≤ z ∧ z + 2 ≤ w) ∨ (x + 2 ≤ z ∧ z ≤ ω) := by
      intro z hz
      obtain ⟨⟨z1, zN⟩, zxw, zw1, zx1⟩ := hTI z hz
      have := hTω z hz
      have := hodd z hz
      split_ifs at zx1 <;> omega
    have hTT : ∀ z, z ∈ Icc w x ∪ T ↔ (w ≤ z ∧ z ≤ x) ∨ z ∈ T := by
      intro z; rw [mem_union, mem_Icc]
    have hxT : x ∈ Icc w x ∪ T := (hTT x).2 (Or.inl ⟨by omega, le_refl _⟩)
    have hDleg : ∀ s z, z ∈ T → x + 1 ≤ s → s ≤ a1 → ¬ (x + 2 ≤ z ∧ z ≤ a1) → C s z := by
      intro s z hz h1 h2 h3
      have hz2 := hodd z hz
      have hzp := hTpos z hz
      rcases Nat.mod_two_eq_zero_or_one s with hs | hs
      · exact F2 s z (by omega) (by omega) hs hz2 (by omega) h2 (by omega)
      · exact hC _ _ (F3 z s hz2 hs (by omega) (by omega) (by omega) (by omega) (by omega))
    have ht2 := hodd t ht
    by_cases hA : ∃ z ∈ T, x + 2 ≤ z ∧ z ≤ a1
    · -- A(b)'
      obtain ⟨z0, hz0, hz0a, hz0x⟩ := hA
      have hGsub : insert x (T.filter (fun z => x + 2 ≤ z ∧ z ≤ a1)) ⊆ Icc w x ∪ T := fun z hz => by
        rw [mem_insert, mem_filter] at hz
        rcases hz with h | h
        · rw [h]; exact hxT
        · exact mem_union_right _ h.1
      have hGI : insert x (T.filter (fun z => x + 2 ≤ z ∧ z ≤ a1)) ⊆ Icc 1 N := fun z hz => by
        rw [mem_insert, mem_filter] at hz
        rcases hz with h | h
        · rw [mem_Icc]; omega
        · exact mem_Icc.2 (hTI z h.1).1
      have hGc : 2 ≤ (insert x (T.filter (fun z => x + 2 ≤ z ∧ z ≤ a1))).card :=
        one_lt_card.2 ⟨x, mem_insert_self _ _, z0, mem_insert_of_mem (mem_filter.2 ⟨hz0, hz0a, hz0x⟩), by omega⟩
      have hGp : ∀ g ∈ insert x (T.filter (fun z => x + 2 ≤ z ∧ z ≤ a1)), g % 2 = 1 := fun g hg => by
        rw [mem_insert, mem_filter] at hg
        rcases hg with h | h
        · rw [h]; exact hx
        · exact hodd g h.1
      obtain ⟨u, v, hd, hst, hc⟩ := HG _ hGI hGc (Or.inr hGp)
      have hd' := mem_diagonals.1 hd
      simp only at hd'
      obtain ⟨hu, hv, ⟨g, hg, b1⟩, ⟨g', hg', b2⟩⟩ := pkCo_inST_iff.1 hst
      have hgr : ∀ g ∈ insert x (T.filter (fun z => x + 2 ≤ z ∧ z ≤ a1)), x ≤ g ∧ g ≤ a1 := fun g hg => by
        rw [mem_insert, mem_filter] at hg
        rcases hg with h | h
        · omega
        · omega
      have gg := hgr g hg
      have gg' := hgr g' hg'
      have key : ∀ s v, x + 1 ≤ s → s ≤ a1 → 1 ≤ v → v ≤ N →
          v ∉ insert x (T.filter (fun z => x + 2 ≤ z ∧ z ≤ a1)) →
          InST (insert x (T.filter (fun z => x + 2 ≤ z ∧ z ≤ a1))) s v → C s v := by
        intro s v h1 h2 h3 h4 hvG hsv
        have hsG := (pkCo_inST_iff.1 hsv).1
        have hsT : s ∉ T := fun h => by
          obtain ⟨-, -, h', -⟩ := hTI s h
          exact hsG (mem_insert_of_mem (mem_filter.2 ⟨h, by omega, h2⟩))
        by_cases hvw : w ≤ v ∧ v ≤ x
        · have hvx : v ≠ x := fun h => hvG (h ▸ mem_insert_self _ _)
          exact hX s v h1 h2 hvw.1 (by omega)
        · by_cases hvT : v ∈ T
          · exact hDleg s v hvT h1 h2 fun h => hvG (mem_insert_of_mem (mem_filter.2 ⟨hvT, h⟩))
          · exact hf _ _ (pkCh_stTrans hsv hGsub (fun h => by
              rw [hTT] at h
              rcases h with h | h
              · omega
              · exact hsT h) (fun h => by
              rw [hTT] at h
              rcases h with h | h
              · exact hvw h
              · exact hvT h))
      rcases (show (x + 1 ≤ u ∧ u ≤ a1) ∨ (x + 1 ≤ v ∧ v ≤ a1) by
        by_contra hcon
        have hux : u ≠ x := fun h => hu (h ▸ mem_insert_self _ _)
        have hvx : v ≠ x := fun h => hv (h ▸ mem_insert_self _ _)
        omega) with h | h
      · exact hc (key u v h.1 h.2 (by omega) (by omega) hv hst)
      · exact hc (hC _ _ (key v u h.1 h.2 (by omega) (by omega) hu (pkCo_inST_comm.1 hst)))
    · have hA' : ∀ z ∈ T, ¬ (x + 2 ≤ z ∧ z ≤ a1) := fun z hz h => hA ⟨z, hz, h⟩
      by_cases hB : a1 + 2 ∈ T
      · -- B': G = {x, a1 + 1}
        have hB2 := hTpos _ hB
        obtain ⟨u, v, hd, hst, hc⟩ := HGm x (a1 + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
        have hd' := mem_diagonals.1 hd
        simp only at hd'
        obtain ⟨hu, hv, ⟨g, hg, b1⟩, ⟨g', hg', b2⟩⟩ := pkCo_inST_iff.1 hst
        rw [mem_insert, mem_singleton] at hu hv hg hg'
        have key : ∀ s v, x + 1 ≤ s → s ≤ a1 → 1 ≤ v → v ≤ N → (v < x ∨ a1 + 1 < v) → C s v := by
          intro s v h1 h2 h3 h4 h5
          have hsT : s ∉ T := fun h => by
            obtain ⟨-, -, h', -⟩ := hTI s h
            exact hA' s h ⟨by omega, h2⟩
          by_cases hvw : w ≤ v ∧ v ≤ x
          · exact hX s v h1 h2 hvw.1 (by omega)
          · by_cases hvT : v ∈ T
            · exact hDleg s v hvT h1 h2 (hA' v hvT)
            · apply hf
              rw [pkCo_inST_iff, hTT, hTT]
              refine ⟨fun h => by rcases h with h | h; omega; exact hsT h,
                fun h => by rcases h with h | h; exact hvw h; exact hvT h, ?_⟩
              rcases h5 with h5 | h5
              · exact ⟨⟨x, hxT, by omega, by omega⟩, ⟨a1 + 2, mem_union_right _ hB, Or.inr (by omega)⟩⟩
              · have hva : v ≠ a1 + 2 := fun h => hvT (h ▸ hB)
                exact ⟨⟨a1 + 2, mem_union_right _ hB, by omega, by omega⟩, ⟨x, hxT, Or.inl (by omega)⟩⟩
        rcases (show (x + 1 ≤ u ∧ u ≤ a1 ∧ (v < x ∨ a1 + 1 < v)) ∨ (x + 1 ≤ v ∧ v ≤ a1 ∧ (u < x ∨ a1 + 1 < u)) by
          omega) with h | h
        · exact hc (key u v h.1 h.2.1 (by omega) (by omega) h.2.2)
        · exact hc (hC _ _ (key v u h.1 h.2.1 (by omega) (by omega) h.2.2))
      · -- D': G = evens [a1 + 1, t* − 1], t* the first trace leg after `x`
        have hR : (T.filter (fun z => x < z)).Nonempty := ⟨t, mem_filter.2 ⟨ht, by omega⟩⟩
        have hm := mem_filter.1 ((T.filter (fun z => x < z)).min'_mem hR)
        obtain ⟨ts, hts⟩ : ∃ ts, (T.filter (fun z => x < z)).min' hR = ts := ⟨_, rfl⟩
        rw [hts] at hm
        have hmin : ∀ z ∈ T, x < z → ts ≤ z := fun z hz hza => by
          rw [← hts]; exact (T.filter (fun z => x < z)).min'_le z (mem_filter.2 ⟨hz, hza⟩)
        have hts2 := hodd ts hm.1
        have htsp := hTpos ts hm.1
        have hts4 : a1 + 4 ≤ ts := by
          have : ts ≠ a1 + 2 := fun h => hB (h ▸ hm.1)
          have := hA' ts hm.1
          omega
        have hGsub : (Icc (a1 + 1) (ts - 1)).filter (fun z => z % 2 = 0) ⊆ Icc 1 N := fun z hz => by
          rw [mem_filter, mem_Icc] at hz; rw [mem_Icc]; omega
        have hGc : 2 ≤ ((Icc (a1 + 1) (ts - 1)).filter (fun z => z % 2 = 0)).card :=
          one_lt_card.2 ⟨a1 + 1, mem_filter.2 ⟨mem_Icc.2 ⟨le_refl _, by omega⟩, by omega⟩, ts - 1,
            mem_filter.2 ⟨mem_Icc.2 ⟨by omega, le_refl _⟩, by omega⟩, by omega⟩
        obtain ⟨u, v, hd, hst, hc⟩ := HG _ hGsub hGc (Or.inl fun g hg => (mem_filter.1 hg).2)
        have hd' := mem_diagonals.1 hd
        simp only at hd'
        have hvG := (pkCo_inST_iff.1 hst).2.1
        have huG := (pkCo_inST_iff.1 hst).1
        have key : ∀ o v, a1 + 1 < o → o < ts - 1 → o % 2 = 1 → 1 ≤ v → v ≤ N →
            v ∉ (Icc (a1 + 1) (ts - 1)).filter (fun z => z % 2 = 0) → C o v := by
          intro o v h1 h2 h3 h4 h5 hvG
          rw [mem_filter, mem_Icc] at hvG
          by_cases hvo : v % 2 = 1 ∧ v ≤ ω
          · exact F3 o v h3 hvo.1 (by omega) (by omega) h4 hvo.2 (by omega)
          · by_cases hvw : w ≤ v ∧ v ≤ a1
            · exact hY o v h3 (by omega) (by omega) hvw.1 hvw.2
            · have hoT : o ∉ T := fun h => by
                have := hmin o h (by omega)
                omega
              have hvT : v ∉ T := fun h => hvo ⟨hodd v h, by have := hTpos v h; omega⟩
              apply hf
              rw [pkCo_inST_iff, hTT, hTT]
              refine ⟨fun h => by rcases h with h | h; omega; exact hoT h,
                fun h => by rcases h with h | h; omega; exact hvT h, ?_⟩
              rcases (show v < w ∨ ts < v by
                have : v ≠ ts := fun h => hvT (h ▸ hm.1)
                omega) with h6 | h6
              · exact ⟨⟨x, hxT, by omega, by omega⟩, ⟨ts, mem_union_right _ hm.1, Or.inr (by omega)⟩⟩
              · exact ⟨⟨ts, mem_union_right _ hm.1, by omega, by omega⟩, ⟨x, hxT, Or.inl (by omega)⟩⟩
        rcases pkCh_evG hst with h | h
        · exact hc (key u v h.1 h.2.1 h.2.2 (by omega) (by omega) hvG)
        · exact hc (hC _ _ (key v u h.1 h.2.1 h.2.2 (by omega) (by omega) huG))
/-- **Side lemma, linear core, mirror piece** `F = [a, x]`: descent heads `[w, x]`, strong induction on `w`. -/
theorem pkCh_sideCoreL {N ω a a1 x : ℕ} {C : ℕ → ℕ → Prop} (hC : ∀ u v, C u v → C v u)
    (hN : N % 2 = 0) (hω : ω % 2 = 1) (hωN : ω + 3 ≤ N) (ha1o : a1 % 2 = 1) (hx : x % 2 = 1)
    (hax : a < x) (hxa1 : x < a1) (ha1ω : a1 ≤ ω)
    (HW : ∀ τ0 : Finset ℕ, τ0.Nonempty → τ0 ⊆ Icc (ω + 2) (N - 1) → (τ0.card = 1 ∨ ∀ t ∈ τ0, t % 2 = 1) →
      ∃ u v, u ∈ Icc (ω + 1) N ∧ v ∈ Icc (ω + 1) N ∧ u ∉ τ0 ∧ v ∉ τ0 ∧
        (∃ t ∈ τ0, min u v < t ∧ t < max u v) ∧ ¬ C u v)
    (HG : ∀ G : Finset ℕ, G ⊆ Icc 1 N → 2 ≤ G.card → ((∀ g ∈ G, g % 2 = 0) ∨ (∀ g ∈ G, g % 2 = 1)) →
      ∃ u v, (min u v, max u v) ∈ diagonals N ∧ InST G u v ∧ ¬ C u v)
    (HGm : ∀ p q, 1 ≤ p → p + 2 ≤ q → q ≤ N → ¬ (p = 1 ∧ q = N) → p % 2 ≠ q % 2 →
      ∃ u v, (min u v, max u v) ∈ diagonals N ∧ InST {p, q} u v ∧ ¬ C u v)
    (F1 : ∀ s r, a ≤ s → s + 1 ≤ x → x + 1 ≤ r → r ≤ a1 → C s r)
    (F2 : ∀ e o, 1 ≤ o → o ≤ N → e % 2 = 0 → o % 2 = 1 → a ≤ e → e ≤ a1 → ¬ (a ≤ o ∧ o ≤ a1) → C e o)
    (F3 : ∀ u v, u % 2 = 1 → v % 2 = 1 → 1 ≤ u → u ≤ ω → 1 ≤ v → v ≤ ω → ¬ (a ≤ u ∧ u ≤ a1) → C u v)
    (Hstep : ∀ w, 1 ≤ w → w ≤ a → w % 2 = 1 →
      (∀ e o, 1 ≤ o → o ≤ N → e % 2 = 0 → o % 2 = 1 → w ≤ e → e ≤ x → ¬ (w ≤ o ∧ o ≤ x) → C e o) →
      ∃ T, AdmSepCompl N w x T ∧ ∀ u v, InST (Icc w x ∪ T) u v → C u v) :
    ∀ n w, n = w → 1 ≤ w → w ≤ a → w % 2 = 1 →
      (∀ e o, 1 ≤ o → o ≤ N → e % 2 = 0 → o % 2 = 1 → w ≤ e → e ≤ x → ¬ (w ≤ o ∧ o ≤ x) → C e o) →
      (∀ r s, r % 2 = 0 → w ≤ r → r + 1 ≤ a → x + 1 ≤ s → s ≤ ω → C r s) → False := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih w hn h1 h2 h3 hMW hF6
  obtain ⟨T, hT, hf⟩ := Hstep w h1 h2 h3 hMW
  have hTA := pkCh_b0 hN hω hωN (a := w) (b := x) (by omega) (by omega) HW hT hf
  have hz := pkCh_zoneL hC hN hωN h1 h2 ha1o hx hax hxa1 ha1ω HG HGm F1 F2 F3 hMW hF6 hT hTA hf
  obtain ⟨hne, hsubT, hsing⟩ := pkCh_asc_facts hT
  obtain ⟨hTA1, -⟩ := pkCh_ta_iff.1 hTA
  have hTr : ∀ t ∈ T, (t = N ∧ w ≠ 1) ∨ (1 ≤ t ∧ t + 2 ≤ w) := by
    intro t ht
    obtain ⟨⟨t1, tN⟩, txw, tx1, tw1⟩ := pkCh_mem_intCompl.1 (hsubT ht)
    have hW : ¬ (ω + 2 ≤ t ∧ t ≤ N - 1) := fun h => disjoint_left.1 hTA1 ht (mem_Icc.2 h)
    have := hz t ht
    split_ifs at tw1 <;> omega
  obtain ⟨w', hw1, hw2, hw3, tT, htT, htT1, hlow, hnoE⟩ : ∃ w', w' < w ∧ 1 ≤ w' ∧ w' % 2 = 1 ∧ ∃ tT ∈ T,
      ((tT = N ∧ w' = 1) ∨ (tT + 1 = w' ∨ tT = w')) ∧ (∀ z ∈ T, z = N ∨ w' ≤ z + 1) ∧
      (∀ e, e % 2 = 0 → w' ≤ e → e + 1 ≤ w → e ∉ T) := by
    by_cases hev : ∃ y ∈ T, y % 2 = 0
    · obtain ⟨y, hy, hy2⟩ := hev
      have hTy := hsing y hy hy2
      rcases hTr y hy with h | h
      · refine ⟨1, by omega, le_refl _, rfl, y, hy, Or.inl ⟨h.1, rfl⟩, fun z _ => by omega, fun e he h1 h2 hz => ?_⟩
        rw [hTy, mem_singleton] at hz
        omega
      · refine ⟨y + 1, by omega, by omega, by omega, y, hy, Or.inr (Or.inl rfl), fun z hz => ?_,
          fun e he h1 h2 hz => ?_⟩
        · rw [hTy, mem_singleton] at hz; omega
        · rw [hTy, mem_singleton] at hz; omega
    · have hodd : ∀ t ∈ T, t % 2 = 1 := fun t ht => by
        by_contra h
        exact hev ⟨t, ht, by omega⟩
      have hm := T.min'_mem hne
      have hmo := hodd _ hm
      have hmr := hTr _ hm
      refine ⟨T.min' hne, by omega, by omega, hmo, T.min' hne, hm, Or.inr (Or.inr rfl), fun z hz => ?_,
        fun e he h1 h2 hz => by have := hodd e hz; omega⟩
      have := T.min'_le z hz
      omega
  have hxT : x ∈ Icc w x ∪ T := mem_union_left _ (mem_Icc.2 ⟨by omega, le_refl _⟩)
  have htTT : tT ∈ Icc w x ∪ T := mem_union_right _ htT
  have hsep : ∀ e o, e % 2 = 0 → w' ≤ e → e + 1 ≤ w → 1 ≤ o → o + 1 ≤ N → ¬ (w' ≤ o ∧ o ≤ x) →
      (o % 2 = 1 ∨ x < o) → C e o := by
    intro e o he h1 h2 h3 h4 h5 h6
    apply hf
    have heT : e ∉ Icc w x ∪ T := by
      rw [mem_union, mem_Icc]
      rintro (h | h)
      · omega
      · exact hnoE e he h1 h2 h
    have hoT : o ∉ Icc w x ∪ T := by
      rw [mem_union, mem_Icc]
      rintro (h | h)
      · omega
      · rcases hlow o h with h' | h'
        · omega
        · rcases hTr o h with h'' | h''
          · omega
          · omega
    rw [pkCo_inST_iff]
    refine ⟨heT, hoT, ?_⟩
    rcases (show o < w' ∨ x < o by omega) with h | h
    · rcases htT1 with ⟨-, h'⟩ | h'
      · omega
      · exact ⟨⟨tT, htTT, by omega, by omega⟩, ⟨x, hxT, Or.inr (by omega)⟩⟩
    · rcases htT1 with ⟨h', -⟩ | h'
      · exact ⟨⟨x, hxT, by omega, by omega⟩, ⟨tT, htTT, Or.inr (by omega)⟩⟩
      · exact ⟨⟨x, hxT, by omega, by omega⟩, ⟨tT, htTT, Or.inl (by omega)⟩⟩
  refine ih w' (by omega) w' rfl hw2 (by omega) hw3 ?_ ?_
  · intro e o h1 h2 he ho h3 h4 h5
    by_cases hew : w ≤ e
    · exact hMW e o h1 h2 he ho hew h4 (by omega)
    · exact hsep e o he h3 (by omega) h1 (by omega) h5 (Or.inl ho)
  · intro r s hr h1 h2 h3 h4
    by_cases hrw : w ≤ r
    · exact hF6 r s hr hrw h2 h3 h4
    · exact hsep r s hr h1 (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))
/-- **(Odd-below), mirror piece**: as `pkCh_oddBelowR` with the `O_in` pair on the near side of `x0`. -/
theorem pkCh_oddBelowL {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} (hF : InFpi N S) {P Q : ℕ × ℕ}
    (hP : IsMinimalChord N S P) (hQ : Q ∈ hitClass N S P) {x0 : ℕ}
    (hx0 : {x0} ∈ admSeps N (headStart Q) (headLen N Q) 0) (hx02 : x0 % 2 = 1)
    (hx0d : Disjoint (sepIn N (headStart Q) (headLen N Q) {x0}) (missing N S))
    (hR : ∃ f1 f2, (f1, f2) ∈ innerOO N S P ∧
      cycPos N (headStart P) f1 ≤ cycPos N (headStart P) x0 ∧ cycPos N (headStart P) f2 ≤ cycPos N (headStart P) x0) :
    False := by
  obtain ⟨hPg, hmin⟩ := pkCh_minChord_iff.1 hP
  obtain ⟨hPp, hPB⟩ := pkCh_mem_goodTail.1 hPg
  obtain ⟨hPo, -, ⟨⟨g1, g2⟩, hgP⟩, -⟩ := pkCh_mem_pole.1 hPp
  obtain ⟨hQp, hQh⟩ := pkCh_mem_hitClass.1 hQ
  obtain ⟨hQo, hQc, -, -⟩ := pkCh_mem_pole.1 hQp
  obtain ⟨-, -, -, -, -, hs, hs2, hk1, hk3, hkN⟩ := pkCh_sides hE hPo
  obtain ⟨-, -, -, -, -, hqs, hqs2, hqk1, hqk3, hqkN⟩ := pkCh_sides hE hQo
  have hN1 : 1 ≤ N := by omega
  have hsI := mem_Icc.1 hs
  have hsub := pkCh_int_top hN hE hPp hPB hQp hQh
  have hoo := pkCh_class_oo hN hE hPo hQo hQh
  obtain ⟨hcb, hc2, hmemP, hposP⟩ := pkCh_subHead hN hE hQo hPo hsub
  obtain ⟨c, hc⟩ : ∃ c, cycPos N (headStart P) (headStart Q) = c := ⟨_, rfl⟩
  rw [hc] at hcb hc2 hmemP hposP
  -- the failing leg `x0`, label `x`
  obtain ⟨hx0sub, -⟩ := pkCo_mem_admSeps.1 hx0
  obtain ⟨hx0I, hx01, hx02'⟩ := (pkCo_mem_intArc hqs (by omega)).1 (hx0sub (mem_singleton_self _))
  have hx0Q : x0 ∈ oddSide N Q := (pkCh_headpos hN hE hQo).2 ⟨hx0I, by omega⟩
  have hx0P := (hmemP x0 hx0I).1 hx0Q
  have hx0pos := hposP x0 hx0I hx0P.1
  obtain ⟨x, hxd⟩ : ∃ x, cycPos N (headStart P) x0 + 1 = x := ⟨_, rfl⟩
  have hxm := pkCh_pos_mod hE hs hs2 hx0I
  rw [hxd] at hxm
  have hlx := pkCo_cycPos_lt hN1 (headStart P) x0
  -- label facts for legs
  have hψ : ∀ y, y ∈ Icc 1 N → cycPos N (headStart P) (rotLeg N (headStart P - 1) y) = y - 1 :=
    fun y hy => pkCh_psi_pos hs hy
  have HG := pkCh_HG hN hE hF hs hs2
  have HGm := pkCh_HGm hN hE hF hs hs2
  have HW := pkCh_HW hN hE hPo hPB
  -- (F2) `minrect(Q)` clean
  have F2 : ∀ e o, 1 ≤ o → o ≤ N → e % 2 = 0 → o % 2 = 1 → c + 1 ≤ e → e ≤ c + headLen N Q →
      ¬ (c + 1 ≤ o ∧ o ≤ c + headLen N Q) → pkCh_Cl N (headStart P) S e o := by
    intro e o ho1 hoN he2 ho2 h1 h2 ho'
    have he : e ∈ Icc 1 N := mem_Icc.2 ⟨by omega, by omega⟩
    have ho : o ∈ Icc 1 N := mem_Icc.2 ⟨ho1, hoN⟩
    rw [pkCh_Cl_iff]
    rintro ⟨-, -, hm⟩
    have pe := hψ e he
    have po := hψ o ho
    have eW : rotLeg N (headStart P - 1) e ∈ oddSide N Q :=
      (hmemP _ (pkCh_psi_mem hN1 e)).2 (by rw [pe]; omega)
    have oW : rotLeg N (headStart P - 1) o ∈ evenSide N Q := by
      show rotLeg N (headStart P - 1) o ∈ Icc 1 N \ oddSide N Q
      refine mem_sdiff.2 ⟨pkCh_psi_mem hN1 o, fun h => ?_⟩
      have := (hmemP _ (pkCh_psi_mem hN1 o)).1 h
      rw [po] at this
      omega
    have me := pkCh_psi_mod hN1 hE hsI.1 hs2 e
    have mo := pkCh_psi_mod hN1 hE hsI.1 hs2 o
    have hr : (min (rotLeg N (headStart P - 1) e) (rotLeg N (headStart P - 1) o),
        max (rotLeg N (headStart P - 1) e) (rotLeg N (headStart P - 1) o)) ∈ minRect N Q :=
      pkCh_mem_minRect.2 ⟨_, pkCh_mem_evens.2 ⟨eW, by omega⟩, _, pkCh_mem_odds.2 ⟨oW, by omega⟩, rfl⟩
    rcases hm with hm | hm
    · have hd := mem_diagonals.1 (pkCh_mem_missing.1 hm).1
      dsimp only at hd
      rw [min_eq_left (by omega), max_eq_right (by omega)] at hr
      exact disjoint_left.1 hQc hr hm
    · have hd := mem_diagonals.1 (pkCh_mem_missing.1 hm).1
      dsimp only at hd
      rw [min_eq_right (by omega), max_eq_left (by omega)] at hr
      exact disjoint_left.1 hQc hr hm
  -- (F3) o-clean
  have F3 : ∀ u v, u % 2 = 1 → v % 2 = 1 → 1 ≤ u → u ≤ headLen N P → 1 ≤ v → v ≤ headLen N P →
      ¬ (c + 1 ≤ u ∧ u ≤ c + headLen N Q) → pkCh_Cl N (headStart P) S u v := by
    intro u v hu hv u1 u2 v1 v2 hu'
    rw [pkCh_Cl_iff]
    rintro ⟨huI, hvI, hm⟩
    have pu := hψ u huI
    have pv := hψ v hvI
    have mu := pkCh_psi_mod hN1 hE hsI.1 hs2 u
    have mv := pkCh_psi_mod hN1 hE hsI.1 hs2 v
    have uP : rotLeg N (headStart P - 1) u ∈ oddSide N P :=
      (pkCh_headpos hN hE hPo).2 ⟨pkCh_psi_mem hN1 u, by rw [pu]; omega⟩
    have vP : rotLeg N (headStart P - 1) v ∈ oddSide N P :=
      (pkCh_headpos hN hE hPo).2 ⟨pkCh_psi_mem hN1 v, by rw [pv]; omega⟩
    have key : ∀ x y, (x, y) ∈ missing N S → x % 2 = 1 → y % 2 = 1 → x ∈ oddSide N P → y ∈ oddSide N P →
        x ∈ oddSide N Q ∧ y ∈ oddSide N Q := by
      intro x y hm hx hy hxP hyP
      have hin : (x, y) ∈ innerOO N S P := pkCh_mem_innerOO.2 ⟨pkCh_mem_Moo.2 ⟨hm, hx, hy⟩, hxP, hyP⟩
      rw [← hoo] at hin
      exact ⟨(pkCh_mem_innerOO.1 hin).2.1, (pkCh_mem_innerOO.1 hin).2.2⟩
    have uW : rotLeg N (headStart P - 1) u ∉ oddSide N Q := fun h => by
      have := (hmemP _ (pkCh_psi_mem hN1 u)).1 h
      rw [pu] at this
      omega
    rcases hm with hm | hm
    · exact uW (key _ _ hm (by omega) (by omega) uP vP).1
    · exact uW (key _ _ hm (by omega) (by omega) vP uP).2
  -- (F1) `Q` fails at `{x0}`
  have F1 : ∀ s r, c + 1 ≤ s → s + 1 ≤ x → x + 1 ≤ r → r ≤ c + headLen N Q → pkCh_Cl N (headStart P) S s r := by
    intro s r h1 h2 h3 h4
    have hsI' : s ∈ Icc 1 N := mem_Icc.2 ⟨by omega, by omega⟩
    have hrI : r ∈ Icc 1 N := mem_Icc.2 ⟨by omega, by omega⟩
    rw [pkCh_Cl_iff]
    rintro ⟨-, -, hm⟩
    have ps := hψ s hsI'
    have pr := hψ r hrI
    have qs := hposP _ (pkCh_psi_mem hN1 s) (by rw [ps]; omega)
    have qr := hposP _ (pkCh_psi_mem hN1 r) (by rw [pr]; omega)
    rw [ps] at qs
    rw [pr] at qr
    have aS : rotLeg N (headStart P - 1) s ∈ cycArc N (headStart Q) (headLen N Q) :=
      (pkCo_mem_cycArc_pos hqs (by omega)).2 ⟨pkCh_psi_mem hN1 s, by rw [qs]; omega⟩
    have aR : rotLeg N (headStart P - 1) r ∈ cycArc N (headStart Q) (headLen N Q) :=
      (pkCo_mem_cycArc_pos hqs (by omega)).2 ⟨pkCh_psi_mem hN1 r, by rw [qr]; omega⟩
    have nS : rotLeg N (headStart P - 1) s ∉ ({x0} : Finset ℕ) := fun h => by
      rw [mem_singleton] at h
      have := congrArg (cycPos N (headStart P)) h
      rw [ps] at this
      omega
    have nR : rotLeg N (headStart P - 1) r ∉ ({x0} : Finset ℕ) := fun h => by
      rw [mem_singleton] at h
      have := congrArg (cycPos N (headStart P)) h
      rw [pr] at this
      omega
    rcases hm with hm | hm
    · exact disjoint_left.1 hx0d (pkCo_mem_sepIn.2 ⟨(pkCh_mem_missing.1 hm).1, aS, aR, nS, nR, x0,
        mem_singleton_self _, by rw [qs, qr, hx0pos]; omega, by rw [qs, qr, hx0pos]; omega⟩) hm
    · exact disjoint_left.1 hx0d (pkCo_mem_sepIn.2 ⟨(pkCh_mem_missing.1 hm).1, aR, aS, nR, nS, x0,
        mem_singleton_self _, by rw [qs, qr, hx0pos]; omega, by rw [qs, qr, hx0pos]; omega⟩) hm
  -- the `O_in` pair in `[x, a1]`
  obtain ⟨f1, f2, hf, hf1, hf2⟩ := hR
  have hfQ : (f1, f2) ∈ innerOO N S Q := by rw [hoo]; exact hf
  obtain ⟨hfM, hf1Q, hf2Q⟩ := pkCh_mem_innerOO.1 hfQ
  obtain ⟨hfm, hf1o, hf2o⟩ := pkCh_mem_Moo.1 hfM
  dsimp only at hf1Q hf2Q hf1o hf2o
  have hf1I := ((pkCh_headpos hN hE hQo).1 hf1Q).1
  have hf2I := ((pkCh_headpos hN hE hQo).1 hf2Q).1
  have hf1P := (hmemP f1 hf1I).1 hf1Q
  have hf2P := (hmemP f2 hf2I).1 hf2Q
  -- `Hstep`: a chord with head `[w, x]` in `𝒫₀` is in `𝒫₁`, not in `𝒮_B` (head-minimality), so its tail fails
  have Hstep : ∀ w, 1 ≤ w → w ≤ c + 1 → w % 2 = 1 →
      (∀ e o, 1 ≤ o → o ≤ N → e % 2 = 0 → o % 2 = 1 → w ≤ e → e ≤ x → ¬ (w ≤ o ∧ o ≤ x) →
        pkCh_Cl N (headStart P) S e o) →
      ∃ T, AdmSepCompl N w x T ∧ ∀ u v, InST (Icc w x ∪ T) u v → pkCh_Cl N (headStart P) S u v := by
    intro w h1 h2 h3 hMW
    obtain ⟨V, hVo, hVts, hVtl, hevV, hodV⟩ := pkCh_mkHead hN hE hPo (a := w) (b := x) h1 (by omega) (by omega)
      h3 (by omega)
    have hVc : Disjoint (minRect N V) (missing N S) := by
      refine disjoint_left.2 fun p hp hpm => ?_
      obtain ⟨e, he, o, ho, rfl⟩ := pkCh_mem_minRect.1 hp
      obtain ⟨heV, he2⟩ := pkCh_mem_evens.1 he
      obtain ⟨hoV, ho2⟩ := pkCh_mem_odds.1 ho
      obtain ⟨heI, e1, e2⟩ := (hodV e).1 heV
      obtain ⟨hoI, o1⟩ := (hevV o).1 hoV
      have me := pkCh_pos_mod hE hs hs2 heI
      have mo := pkCh_pos_mod hE hs hs2 hoI
      have le := pkCo_cycPos_lt hN1 (headStart P) e
      have lo := pkCo_cycPos_lt hN1 (headStart P) o
      apply pkCh_notCl_mm hs heI hoI hpm
      rw [pkCh_phi_eq hs, pkCh_phi_eq hs]
      exact hMW _ _ (by omega) (by omega) (by omega) (by omega) e1 e2 (by omega)
    have hVp : V ∈ poleChords N S := by
      refine pkCh_mem_pole.2 ⟨hVo, hVc, ?_, ⟨(f1, f2), pkCh_mem_innerOO.2 ⟨hfM, (hodV f1).2 ⟨hf1I, by omega, by omega⟩,
        (hodV f2).2 ⟨hf2I, by omega, by omega⟩⟩⟩⟩
      obtain ⟨⟨e1, e2⟩, he⟩ := (pkCh_mem_pole.1 hPp).2.2.1
      obtain ⟨heM, he1, he2⟩ := pkCh_mem_innerEE.1 he
      dsimp only at he1 he2
      obtain ⟨k1, k1'⟩ := (pkCh_evenpos hN hE hPo).1 he1
      obtain ⟨k2, k2'⟩ := (pkCh_evenpos hN hE hPo).1 he2
      exact ⟨(e1, e2), pkCh_mem_innerEE.2 ⟨heM, (hevV e1).2 ⟨k1, Or.inr (by omega)⟩,
        (hevV e2).2 ⟨k2, Or.inr (by omega)⟩⟩⟩
    have hVs : oddSide N V ⊂ oddSide N P := by
      have hsub' : oddSide N V ⊆ oddSide N P := fun y hy => by
        obtain ⟨hyI, y1, y2⟩ := (hodV y).1 hy
        exact (pkCh_headpos hN hE hPo).2 ⟨hyI, by omega⟩
      have hωI : headLen N P ∈ Icc 1 N := mem_Icc.2 ⟨by omega, by omega⟩
      have pω := hψ _ hωI
      refine (ssubset_iff_of_subset hsub').2 ⟨rotLeg N (headStart P - 1) (headLen N P),
        (pkCh_headpos hN hE hPo).2 ⟨pkCh_psi_mem hN1 _, by rw [pω]; omega⟩, fun h => ?_⟩
      obtain ⟨-, -, y2⟩ := (hodV _).1 h
      rw [pω] at y2
      omega
    have hVng : V ∉ goodTail N S := fun h => hmin V h hVs
    obtain ⟨τ0, hτ0, hτ0d⟩ : ∃ τ0 ∈ admSeps N (tailStart V) (tailLen N V) 1,
        Disjoint (sepIn N (tailStart V) (tailLen N V) τ0) (missing N S) := by
      by_contra hcon
      exact hVng (pkCh_mem_goodTail.2 ⟨hVp, pkCh_noFree_iff.2 fun τ0 h hd => hcon ⟨τ0, h, hd⟩⟩)
    exact pkCh_tailLin hN hE hPo hVo h1 (by omega) (by omega) hVts hVtl hτ0 hτ0d
  refine pkCh_sideCoreL (a := c + 1) (a1 := c + headLen N Q) (x := x) pkCh_Cl_symm hE hk1 hkN (by omega)
    (by omega) (by omega) (by omega) hcb HW HG HGm F1 (fun e o h1 h2 h3 h4 h5 h6 h7 => F2 e o h1 h2 h3 h4 h5 h6 h7) F3
    Hstep _ (c + 1) rfl (by omega) (le_refl _) (by omega) ?_ ?_
  · intro e o h1 h2 he ho h3 h4 h5
    by_cases hoa : x + 1 ≤ o ∧ o ≤ c + headLen N Q
    · exact F1 e o h3 (by omega) hoa.1 hoa.2
    · exact F2 e o h1 h2 he ho h3 (by omega) (by omega)
  · intro r s hr h1 h2
    omega

/-- **(Odd-below)** (BP App. D §5b): no class member of the canonical `P*` fails `Sep_all` of its head at an odd
singleton. The `O_in` pairs lie on one side of the failing leg; the Side lemma (right piece or mirror) gives a `𝒮_B`
chord with a smaller head. -/
theorem pkCh_oddBelow {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} (hF : InFpi N S) {P Q : ℕ × ℕ}
    (hP : IsMinimalChord N S P) (hQ : Q ∈ hitClass N S P) {x0 : ℕ}
    (hx0 : {x0} ∈ admSeps N (headStart Q) (headLen N Q) 0) (hx02 : x0 % 2 = 1)
    (hx0d : Disjoint (sepIn N (headStart Q) (headLen N Q) {x0}) (missing N S)) : False := by
  obtain ⟨hPg, -⟩ := pkCh_minChord_iff.1 hP
  obtain ⟨hPp, hPB⟩ := pkCh_mem_goodTail.1 hPg
  obtain ⟨hPo, -, -, ⟨⟨f1, f2⟩, hf⟩⟩ := pkCh_mem_pole.1 hPp
  obtain ⟨hQp, hQh⟩ := pkCh_mem_hitClass.1 hQ
  have hQo := (pkCh_mem_pole.1 hQp).1
  obtain ⟨-, -, -, -, -, hs, hs2, hk1, hk3, hkN⟩ := pkCh_sides hE hPo
  obtain ⟨-, -, -, -, -, hqs, hqs2, hqk1, hqk3, hqkN⟩ := pkCh_sides hE hQo
  have hsub := pkCh_int_top hN hE hPp hPB hQp hQh
  have hoo := pkCh_class_oo hN hE hPo hQo hQh
  obtain ⟨hcb, hc2, hmemP, hposP⟩ := pkCh_subHead hN hE hQo hPo hsub
  have hfQ : (f1, f2) ∈ innerOO N S Q := by rw [hoo]; exact hf
  obtain ⟨hfM, hf1Q, hf2Q⟩ := pkCh_mem_innerOO.1 hfQ
  dsimp only at hf1Q hf2Q
  have hf1I := ((pkCh_headpos hN hE hQo).1 hf1Q).1
  have hf2I := ((pkCh_headpos hN hE hQo).1 hf2Q).1
  obtain ⟨hx0sub, -⟩ := pkCo_mem_admSeps.1 hx0
  obtain ⟨hx0I, hx01, hx02'⟩ := (pkCo_mem_intArc hqs (by omega)).1 (hx0sub (mem_singleton_self _))
  have hx0Q : x0 ∈ oddSide N Q := (pkCh_headpos hN hE hQo).2 ⟨hx0I, by omega⟩
  have p1 := (hmemP f1 hf1I).1 hf1Q
  have p2 := (hmemP f2 hf2I).1 hf2Q
  have p0 := (hmemP x0 hx0I).1 hx0Q
  have q1 := hposP f1 hf1I p1.1
  have q2 := hposP f2 hf2I p2.1
  have q0 := hposP x0 hx0I p0.1
  by_cases hRt : cycPos N (headStart P) x0 ≤ cycPos N (headStart P) f1 ∧
      cycPos N (headStart P) x0 ≤ cycPos N (headStart P) f2
  · exact pkCh_oddBelowR hN hE hF hP hQ hx0 hx02 hx0d ⟨f1, f2, hf, hRt.1, hRt.2⟩
  · by_cases hLt : cycPos N (headStart P) f1 ≤ cycPos N (headStart P) x0 ∧
        cycPos N (headStart P) f2 ≤ cycPos N (headStart P) x0
    · exact pkCh_oddBelowL hN hE hF hP hQ hx0 hx02 hx0d ⟨f1, f2, hf, hLt.1, hLt.2⟩
    · have hm := (pkCh_mem_Moo.1 hfM).1
      have a1 : f1 ∈ cycArc N (headStart Q) (headLen N Q) := ((pkCh_arcs (by omega) hE hQo).1 f1).1 hf1Q
      have a2 : f2 ∈ cycArc N (headStart Q) (headLen N Q) := ((pkCh_arcs (by omega) hE hQo).1 f2).1 hf2Q
      have n1 : f1 ∉ ({x0} : Finset ℕ) := fun h => by rw [mem_singleton] at h; subst h; omega
      have n2 : f2 ∉ ({x0} : Finset ℕ) := fun h => by rw [mem_singleton] at h; subst h; omega
      exact disjoint_left.1 hx0d (pkCo_mem_sepIn.2 ⟨(pkCh_mem_missing.1 hm).1, a1, a2, n1, n2, x0,
        mem_singleton_self _, by rw [q1, q2, q0]; omega, by rw [q1, q2, q0]; omega⟩) hm

/-- `sorry` (pkgChain) · **[Bot]** [v3 §14.2 route step 4; BP App. D §6d]: (Even-top′) at a canonical chord gives a
member `b` of its class with `Sep_all(A_b)`. -/
theorem bot_of_evenTop {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {S : Finset (ℕ × ℕ)} (hF : InFpi N S) {P : ℕ × ℕ}
    (hP : IsMinimalChord N S P) (hT : EvenTopP N S P) :
    ∃ b ∈ hitClass N S P, NoFreeSep N S (headStart b) (headLen N b) 0 := by
  have hE' := Nat.even_iff.1 hE
  obtain ⟨hPg, -⟩ := pkCh_minChord_iff.1 hP
  obtain ⟨hPp, -⟩ := pkCh_mem_goodTail.1 hPg
  refine pkCh_bot_red hN hE' hP hT ?_ ?_ _ P (pkCh_mem_hitClass.2 ⟨hPp, rfl⟩) rfl
  · intro Q hQ x hx hx2 hxd
    exact pkCh_oddBelow hN hE' hF hP hQ hx hx2 hxd
  · intro R hR hRP hRoo
    exact pkCh_noB1 hN hE' hF hP _ R hR rfl hRP hRoo

/-- `sorry` (pkgChain) · **[Int]** [v3 §14.2 route step 5; BP App. D §3b]: at a canonical chord `P` with a class member
`b` satisfying `Sep_all(A_b)`, the class is the interval `[b, P]` under head inclusion. -/
theorem int_of_bot {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {S : Finset (ℕ × ℕ)} (hF : InFpi N S) {P b : ℕ × ℕ}
    (hP : IsMinimalChord N S P) (hb : b ∈ hitClass N S P) (hbA : NoFreeSep N S (headStart b) (headLen N b) 0) :
    ∀ Q ∈ hitClass N S P, oddSide N b ⊆ oddSide N Q ∧ oddSide N Q ⊆ oddSide N P := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  obtain ⟨hPg, -⟩ := pkCh_minChord_iff.1 hP
  obtain ⟨hPp, hPB⟩ := pkCh_mem_goodTail.1 hPg
  obtain ⟨hbp, hbh⟩ := pkCh_mem_hitClass.1 hb
  intro Q hQ
  obtain ⟨hQp, hQh⟩ := pkCh_mem_hitClass.1 hQ
  exact ⟨pkCh_int_bot hN hE' hbp hbA hQp (hQh.trans hbh.symm), pkCh_int_top hN hE' hPp hPB hQp hQh⟩

/-- `sorry` (pkgChain) · **[Child](3)** (R2-Z182 Theorem 1) [v3 §14.2 route step 8; BP App. C §C-2]: for `S ∈ F^π` and
`P ∈ 𝒫₁`, each child set is in `F^π` of its size exactly when that side satisfies `Sep_all`. -/
theorem childF {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {S : Finset (ℕ × ℕ)} (hF : InFpi N S) {P : ℕ × ℕ}
    (hP : P ∈ poleChords N S) :
    (InFpi (headLen N P + 1) (childSetA N S P) ↔ NoFreeSep N S (headStart P) (headLen N P) 0) ∧
    (InFpi (tailLen N P + 1) (childSetB N S P) ↔ NoFreeSep N S (tailStart P) (tailLen N P) 1) := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  have hPo : P ∈ oddDiagonals N := (pkCh_mem_pole.1 hP).1
  obtain ⟨hts, hts2, htl1, htl3, htlN, hhs, hhs2, hhl1, hhl3, hhlN⟩ := pkCh_sides hE' hPo
  refine ⟨?_, ?_⟩
  · have H : pkCh_CH N (headStart P) (headLen N P) 1 (headLen N P + 1)
        (fun j => vtx N (headStart P + j - 1)) := by
      refine pkCh_CH_iff.2 ⟨hhs, hhl3, hhlN, hhl1, hE', mem_Icc.2 ⟨le_refl 1, by omega⟩, by omega,
        mem_Icc.2 ⟨by omega, le_refl _⟩, ?_, ?_⟩
      · rw [pkCo_cycPos_eq (le_refl 1) (by omega) (by omega) (le_refl _), if_pos (by omega)]
        omega
      · intro y hy hyh
        have hy' := mem_Icc.1 hy
        show vtx N (headStart P + y - 1) = vtx N (headStart P + cycPos (headLen N P + 1) 1 y)
        rw [pkCo_cycPos_eq (le_refl 1) (by omega) hy'.1 hy'.2, if_pos hy'.1,
          show headStart P + y - 1 = headStart P + (y - 1) by omega]
    have e := pkCh_childGen H hF
    rw [show (headStart P + 1) % 2 = 0 by omega] at e
    exact e
  · have H : pkCh_CH N (tailStart P) (tailLen N P) 2 1 (fun j => vtx N (tailStart P + j - 2)) := by
      refine pkCh_CH_iff.2 ⟨hts, htl3, htlN, htl1, hE', mem_Icc.2 ⟨by omega, by omega⟩, by omega,
        mem_Icc.2 ⟨le_refl 1, by omega⟩, ?_, ?_⟩
      · rw [pkCo_cycPos_eq (by omega) (by omega) (le_refl 1) (by omega), if_neg (by omega)]
        omega
      · intro y hy hyh
        have hy' := mem_Icc.1 hy
        show vtx N (tailStart P + y - 2) = vtx N (tailStart P + cycPos (tailLen N P + 1) 2 y)
        rw [pkCo_cycPos_eq (by omega) (by omega) hy'.1 hy'.2, if_pos (show 2 ≤ y by omega),
          show tailStart P + y - 2 = tailStart P + (y - 2) by omega]
    have e := pkCh_childGen H hF
    rw [show (tailStart P + 1) % 2 = 1 by omega] at e
    exact e

/-- `sorry` (pkgLin) · **𝒢_N is an antichain** [v3 Prop. 14.7 (b); BP [Anti]]. -/
theorem gFamily_antichain {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {Z Z' : Finset (ℕ × ℕ)} (hZ : Z ∈ gFamily N)
    (hZ' : Z' ∈ gFamily N) (h : Z ⊆ Z') : Z = Z' := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  obtain ⟨G, hG, rfl⟩ := mem_image.1 hZ
  obtain ⟨G', hG', rfl⟩ := mem_image.1 hZ'
  have hG'sub := (pkL_gprops hE' hG').1
  have hGG : G = G' := by
    apply Subset.antisymm
    · intro t ht
      by_contra ht'
      obtain ⟨p, hp, hp'⟩ := pkL_sep_step hN hE' hG hG'sub ht ht'
      exact hp' (h hp)
    · intro x hx
      by_contra hxG
      obtain ⟨p, hp, hpx⟩ := pkL_supp hE' hG (hG'sub hx) hxG
      have hst := (mem_filter.1 (h hp)).2
      rcases hpx with e | e
      · exact hst.1 (by rw [e]; exact hx)
      · exact hst.2.1 (by rw [e]; exact hx)
  rw [hGG]

/-- `sorry` (pkgLin) · **[Cl2a], non-degeneracy part** [v3 Prop. 14.7 (a); BP App. A §8.2 (R2-Z117 Lemma 1)]: every
member of `𝒢_N` has a rational point with every chord non-zero. -/
theorem cl2a_nondeg {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {Z : Finset (ℕ × ℕ)} (hZ : Z ∈ gFamily N) : NonDegPt N Z := by
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  obtain ⟨G, hG, rfl⟩ := mem_image.1 hZ
  rcases (mem_filter.1 hG).2 with hS | hM
  · have hT : ∃ r, r < 2 ∧ Admissible N r G := by
      rcases hS with h0 | h1
      · exact ⟨0, by omega, h0⟩
      · exact ⟨1, by omega, h1⟩
    obtain ⟨r, hr, hT⟩ := hT
    obtain ⟨X, hX, hX0⟩ := ZT_inhabited (by omega) hE' hr hT
    refine ⟨X, fun p hp => ?_, hX0⟩
    obtain ⟨hd, hst⟩ := mem_filter.1 hp
    have hd' := mem_diagonals.1 hd
    exact hX p.1 (mem_Icc.2 ⟨by omega, by omega⟩) p.2 (mem_Icc.2 ⟨by omega, by omega⟩) hst
  · obtain ⟨a, ha, b, hb, rfl, hab, hne, -⟩ := hM
    rw [mem_Icc] at ha hb
    obtain ⟨X, hX0, hR⟩ := onRect_inhabited (n := N) (k := b - a - 1) (m := a + 1) (by omega) (by omega)
      (by omega) (by omega)
    exact ⟨X, pkL_onLocus_anchor (by omega) ha.1 hab hb.2 hR, hX0⟩

/-- The parity sign `τ` of a pair of distinct labels: `+1` both even, `−1` both odd, `0` mixed. -/
def pkBr_tau (x y : ℕ) : ℚ := if x % 2 = y % 2 then (if x % 2 = 0 then 1 else -1) else 0

theorem pkBr_planar_sign {N x y : ℕ} (hE : N % 2 = 0) (hx1 : 1 ≤ x) (hxN : x ≤ N) (hy1 : 1 ≤ y) (hyN : y ≤ N)
    (hxy : x ≠ y) :
    planar N (fun d => ((shiftSign d : ℤ) : ℚ)) x y = pkBr_tau x y := by
  unfold planar
  rw [vtx_of_mem hx1 hxN, vtx_of_mem hy1 hyN]
  rcases lt_or_gt_of_ne hxy with h | h
  · rw [min_eq_left h.le, max_eq_right h.le]
    split_ifs with hd
    · rw [mem_diagonals] at hd
      unfold shiftSign pkBr_tau
      dsimp only
      split_ifs <;> (try omega) <;> norm_num
    · rw [mem_diagonals] at hd
      dsimp only at hd
      unfold pkBr_tau
      simp [show ¬ (x % 2 = y % 2) by omega]
  · rw [min_eq_right h.le, max_eq_left h.le]
    split_ifs with hd
    · rw [mem_diagonals] at hd
      unfold shiftSign pkBr_tau
      dsimp only
      split_ifs <;> (try omega) <;> norm_num
    · rw [mem_diagonals] at hd
      dsimp only at hd
      unfold pkBr_tau
      simp [show ¬ (x % 2 = y % 2) by omega]

/-- `c(v₀) = 0` on every tile `(u, v) ∈ diagonals N`, `N` even (Z26 Lemma 3.2; reproved here). -/
theorem pkBr_mesh_sign {N : ℕ} (hE : N % 2 = 0) {u v : ℕ} (huv : (u, v) ∈ diagonals N) :
    mesh N (fun d => ((shiftSign d : ℤ) : ℚ)) u v = 0 := by
  rw [mem_diagonals] at huv
  dsimp only at huv
  obtain ⟨h1, h2, h3, h4⟩ := huv
  unfold mesh
  rcases lt_or_eq_of_le h2 with hv | hv
  · rw [pkBr_planar_sign hE h1 (by omega) (by omega) h2 (by omega),
      pkBr_planar_sign hE (by omega) (by omega) (by omega) (by omega) (by omega),
      pkBr_planar_sign hE h1 (by omega) (by omega) (by omega) (by omega),
      pkBr_planar_sign hE (by omega) (by omega) (by omega) h2 (by omega)]
    unfold pkBr_tau
    split_ifs <;> (try omega) <;> norm_num
  · rw [hv]
    have hw : ∀ x, planar N (fun d => ((shiftSign d : ℤ) : ℚ)) x (N + 1) =
        planar N (fun d => ((shiftSign d : ℤ) : ℚ)) x 1 := by
      intro x
      unfold planar
      rw [show N + 1 = 1 + N by omega, vtx_add_n]
    rw [hw, hw, pkBr_planar_sign hE h1 (by omega) (by omega) le_rfl (by omega),
      pkBr_planar_sign hE (by omega) (by omega) (by omega) (by omega) (by omega),
      pkBr_planar_sign hE h1 (by omega) le_rfl (by omega) (by omega),
      pkBr_planar_sign hE (by omega) (by omega) (by omega) le_rfl (by omega)]
    unfold pkBr_tau
    split_ifs <;> (try omega) <;> norm_num

/-- The shifted point, written through `HahnSeries.C`. -/
theorem pkBr_shifted_eq (X : ℕ × ℕ → ℚ) (d : ℕ × ℕ) :
    shifted X d = HahnSeries.C (X d) + HahnSeries.C (((shiftSign d : ℤ) : ℚ)) * delta := by
  show HahnSeries.C (X d) + ((shiftSign d : ℤ) : LaurentSeries ℚ) * delta = _
  rw [map_intCast]

theorem pkBr_planar_shifted (N : ℕ) (X : ℕ × ℕ → ℚ) (x y : ℕ) :
    planar N (shifted X) x y = HahnSeries.C (planar N X x y) +
      HahnSeries.C (planar N (fun d => ((shiftSign d : ℤ) : ℚ)) x y) * delta := by
  unfold planar
  split_ifs
  · exact pkBr_shifted_eq X _
  · simp

theorem pkBr_mesh_shifted (N : ℕ) (X : ℕ × ℕ → ℚ) (x y : ℕ) :
    mesh N (shifted X) x y = HahnSeries.C (mesh N X x y) +
      HahnSeries.C (mesh N (fun d => ((shiftSign d : ℤ) : ℚ)) x y) * delta := by
  unfold mesh
  simp only [pkBr_planar_shifted, map_add, map_sub]
  ring

/-- Every shifted diagonal is non-zero when every odd diagonal is. -/
theorem pkBr_shifted_ne {N : ℕ} {X : ℕ × ℕ → ℚ} (hX : ∀ d ∈ oddDiagonals N, X d ≠ 0) {d : ℕ × ℕ}
    (hd : d ∈ diagonals N) : shifted X d ≠ 0 := by
  rw [pkBr_shifted_eq]
  by_cases hs : shiftSign d = 0
  · have hodd : d ∈ oddDiagonals N := by
      show d ∈ (diagonals N).filter (fun d => (d.2 - d.1) % 2 = 1)
      rw [mem_filter]
      refine ⟨hd, ?_⟩
      rw [mem_diagonals] at hd
      unfold shiftSign at hs
      split_ifs at hs <;> omega
    rw [hs, Int.cast_zero, map_zero, zero_mul, add_zero]
    exact HahnSeries.C_ne_zero (hX d hodd)
  · intro h0
    have := congrArg (fun f : LaurentSeries ℚ => f.coeff (-1)) h0
    simp only [HahnSeries.C_apply, delta, HahnSeries.single_mul_single, HahnSeries.coeff_add,
      HahnSeries.coeff_single, HahnSeries.coeff_zero] at this
    norm_num at this
    exact hs (by exact_mod_cast this)

/-- The diamond anchored just past the legs `a < b` lies in `S_{{a,b}}` (for `b = N` it is `D(1, a+1)`). -/
theorem pkBr_diamond_sub {N a b : ℕ} (ha : 1 ≤ a) (hab : a + 2 ≤ b) (hbN : b ≤ N) (hne : ¬ (a = 1 ∧ b = N)) :
    ContainsDiamond N (sepPairs N {a, b}) := by
  rcases lt_or_eq_of_le hbN with hb | hb
  · have hd : (a + 1, b + 1) ∈ diagonals N := mem_diagonals.2 ⟨by omega, by omega, by omega, by omega⟩
    refine ⟨(a + 1, b + 1), hd, ?_⟩
    intro p hp
    have hpd := diamond_subset_diagonals hd hp
    dsimp only at hp
    rw [pkA_mem_diamond (by omega) (by omega) (by omega)] at hp
    have hlt : p.1 < p.2 := by rw [mem_diagonals] at hpd; omega
    rw [sepPairs, mem_filter]
    refine ⟨hpd, ?_⟩
    unfold InST
    rw [min_eq_left hlt.le, max_eq_right hlt.le]
    simp only [mem_insert, mem_singleton]
    rcases hp with h | h
    · exact ⟨by omega, by omega, ⟨b, Or.inr rfl, by omega, by omega⟩, ⟨a, Or.inl rfl, Or.inl (by omega)⟩⟩
    · exact ⟨by omega, by omega, ⟨a, Or.inl rfl, by omega, by omega⟩, ⟨b, Or.inr rfl, Or.inr (by omega)⟩⟩
  · have hd : (1, a + 1) ∈ diagonals N := mem_diagonals.2 ⟨le_rfl, by omega, by omega, by omega⟩
    refine ⟨(1, a + 1), hd, ?_⟩
    intro p hp
    have hpd := diamond_subset_diagonals hd hp
    dsimp only at hp
    rw [pkA_mem_diamond le_rfl (by omega) (by omega)] at hp
    have hlt : p.1 < p.2 := by rw [mem_diagonals] at hpd; omega
    rw [sepPairs, mem_filter]
    refine ⟨hpd, ?_⟩
    unfold InST
    rw [min_eq_left hlt.le, max_eq_right hlt.le]
    simp only [mem_insert, mem_singleton]
    rcases hp with h | h
    · exact ⟨by omega, by omega, ⟨a, Or.inl rfl, by omega, by omega⟩, ⟨b, Or.inr rfl, Or.inr (by omega)⟩⟩
    · omega

/-- `sorry` (pkgBridge) · **[Cl2a], diamond part** [v3 §14.5 [Cl2](a); BP §3.A "diamonds via `lemmaZ`"]: a mixed-anchored
diamond is a zero of `𝒜_N` (the Tr φ³ rectangle zero `R12P4A.amp_zero_of_diamond` at the δ-shifted point, which stays on
the locus because `c(v₀) = 0`). No 3c-b input. -/
theorem cl2a_diamond {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {G : Finset ℕ} (hG : IsMixedAnchor N G) :
    AmpZeroOn N (sepPairs N G) := by
  obtain ⟨a, ha, b, hb, rfl, hab, hne, -⟩ := hG
  rw [mem_Icc] at ha hb
  have hE2 : N % 2 = 0 := Nat.even_iff.1 hE
  have hD := pkBr_diamond_sub ha.1 hab hb.2 hne
  intro X hL hX
  have hL' : OnLocus N (sepPairs N {a, b}) (shifted X) := by
    intro t ht
    rw [pkBr_mesh_shifted, hL t ht, pkBr_mesh_sign hE2 (mem_filter.1 ht).1]
    simp
  have h0 := amp_zero_of_diamond hD hL' (fun d hd => pkBr_shifted_ne hX hd)
  rw [calA, NLSM, shiftCoeff, h0]
  simp

/-- ASSEMBLED · **the chain's output** [v3 §14.2 route steps 3–5]: for `S ∈ F^π` with `𝒫₁ ≠ ∅` there are `t ∈ 𝒫₁`
with `Sep_all(B_t)` and `b` in the class of `t` with `Sep_all(A_b)`, and the class is the interval `[b, t]`. -/
theorem chain_interval {N : ℕ} (hN : 6 ≤ N) (hE : Even N) {S : Finset (ℕ × ℕ)} (hF : InFpi N S)
    (hP : (poleChords N S).Nonempty) :
    ∃ t ∈ poleChords N S, ∃ b ∈ hitClass N S t, NoFreeSep N S (tailStart t) (tailLen N t) 1 ∧
      NoFreeSep N S (headStart b) (headLen N b) 0 ∧
      ∀ Q ∈ hitClass N S t, oddSide N b ⊆ oddSide N Q ∧ oddSide N Q ⊆ oddSide N t := by
  obtain ⟨P, hPm⟩ := can_exists hN hE hF hP
  obtain ⟨b, hb, hbA⟩ := bot_of_evenTop hN hE hF hPm (evenTop hN hE hF hPm)
  have hPg := hPm.1
  exact ⟨P, (mem_filter.1 hPg).1, b, hb, (mem_filter.1 hPg).2, hbA, int_of_bot hN hE hF hPm hb hbA⟩

/-! ## 8. Theorem Π [v3 §14.1]: the M2 form (analytic inputs as hypotheses) and the M3 form

**The analytic inputs** (BP §5 M2; owner decision 2026-09-27) are frozen `Prop` definitions, passed as explicit
hypotheses of the M2 theorems (no `axiom`), and are the M3 targets. Each is stated with every hypothesis the route has at
the point of use (so it is as weak as the route allows), and each is a *consequence of clause 1 itself* on its domain
(its conclusion `NonzeroOn N S` for `S ∈ F^π` is clause 1's claim; `STZeroInput` is Theorem 1 of the note), so no input
can be false while Π is true: the M2 theorems cannot be vacuous through a false hypothesis.
* `GermInput N` = [Germ] with [LemE] and Theorem I inside (v3 route step 2; BP App. A §3.6): `S ∈ F^π`, `𝒫₁ = ∅` ⇒
  `NonzeroOn`. BP §5 lists `hThmI` separately; here Theorem I is internal to pkgGerm, because the M2 assembly never calls
  it outside [Germ] (thread §4 C2).
* `ResChildInput N` = [Res] + [Child](1) (surjectivity) + the domain step of route step 8 (BP App. B §2, App. C §C-2
  (1), (4)): for `S ∈ F^π`, an interval class `[b, t]` of `𝒫₁` chords that is the full proportionality class of `X_t`
  with every member at `+X_t`, non-vanishing of the two child amplitudes on their loci gives `NonzeroOn N S`.
* `STZeroInput N` = the S_T zero (Theorem 1 of the note; base `nlsm_zero_on_ZT`, a 3c-b target), the analytic half of
  [Cl2a]; the diamond half is `cl2a_diamond` (pkgBridge, no 3c-b input). -/


end PiZ
