import PionCompleteness.C0

namespace PiZ

open Finset R12P1 R12P4A R12P3 R12P3C

theorem pkT_runSepA_iff {ω : ℕ} {Θ : Finset ℕ} {u v : ℕ} :
    runSepA ω Θ u v ↔ u ∈ Icc 1 ω ∧ v ∈ Icc 1 ω ∧ u ∉ Θ ∧ v ∉ Θ ∧ ∃ θ ∈ Θ, min u v < θ ∧ θ < max u v :=
  Iff.rfl

theorem pkT_runSepA_comm {ω : ℕ} {Θ : Finset ℕ} {u v : ℕ} : runSepA ω Θ u v ↔ runSepA ω Θ v u := by
  rw [pkT_runSepA_iff, pkT_runSepA_iff, min_comm, max_comm]
  exact ⟨fun ⟨h1, h2, h3, h4, h5⟩ => ⟨h2, h1, h4, h3, h5⟩, fun ⟨h1, h2, h3, h4, h5⟩ => ⟨h2, h1, h4, h3, h5⟩⟩

theorem pkT_mem_evens {L : Finset ℕ} {x : ℕ} : x ∈ evens L ↔ x ∈ L ∧ x % 2 = 0 := by
  show x ∈ L.filter (fun a => a % 2 = 0) ↔ _
  exact mem_filter

theorem pkT_mem_odds {L : Finset ℕ} {x : ℕ} : x ∈ odds L ↔ x ∈ L ∧ x % 2 = 1 := by
  show x ∈ L.filter (fun a => a % 2 = 1) ↔ _
  exact mem_filter

theorem pkT_consecWit_iff {N : ℕ} {Θ τ σ G : Finset ℕ} :
    ConsecWit N Θ τ σ G ↔ 2 ≤ G.card ∧ ∃ a ∈ Icc 1 N, ∃ len ∈ range (N + 1),
      G = evens (Θ ∪ τ ∪ σ) ∩ cycArc N a len ∨ G = odds (τ ∪ σ) ∩ cycArc N a len :=
  Iff.rfl

theorem pkT_mem_sepPairs {N : ℕ} {G : Finset ℕ} {p : ℕ × ℕ} :
    p ∈ sepPairs N G ↔ p ∈ diagonals N ∧ InST G p.1 p.2 := by
  show p ∈ (diagonals N).filter (fun p => InST G p.1 p.2) ↔ _
  exact mem_filter

theorem pkT_mem_threeSepCut {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} {p : ℕ × ℕ} :
    p ∈ threeSepCut N ω x0 x1 y0 y1 Θ τ σ ↔ p ∈ diagonals N ∧
      (runSepA ω Θ p.1 p.2 ∨ InST (Icc x0 x1 ∪ τ) p.1 p.2 ∨ InST (Icc y0 y1 ∪ σ) p.1 p.2) := by
  show p ∈ (diagonals N).filter _ ↔ _
  exact mem_filter

/-- Core of the block lemma: `w` inside the block `(a, b)`, `z` anywhere, a leg of `G` strictly between them. -/
theorem pkT_block_core {ω : ℕ} {Θ K G : Finset ℕ} {a b w z g : ℕ}
    (haK : a ∈ K) (hbK : b ∈ K)
    (hGab : ∀ g ∈ G, a ≤ g ∧ g ≤ b)
    (hGΘ : ∀ x, a < x → x < b → (x ∈ G ↔ x ∈ Θ))
    (hK : ∀ k ∈ K, ¬ (a < k ∧ k < b))
    (hbω : b ≤ ω + 1)
    (hKA : ∀ k ∈ K, k ∉ G → 1 ≤ k ∧ k ≤ ω ∧ k ∉ Θ)
    (hb7 : b ∈ G → b ∉ Θ → ∀ k ∈ K, k ≤ b)
    (ha7 : a ∈ G → a ∉ Θ → ∀ k ∈ K, a ≤ k)
    (hw1 : a < w) (hw2 : w < b) (hwG : w ∉ G) (hzG : z ∉ G)
    (hg : g ∈ G) (hgw : min w z < g ∧ g < max w z) :
    runSepA ω Θ w z ∨ InST K w z := by
  have hwΘ : w ∉ Θ := fun h => hwG ((hGΘ w hw1 hw2).2 h)
  have hwK : w ∉ K := fun h => hK w h ⟨hw1, hw2⟩
  by_cases hz : a < z ∧ z < b
  · left
    have hzΘ : z ∉ Θ := fun h => hzG ((hGΘ z hz.1 hz.2).2 h)
    have hg1 : a < g ∧ g < b := by omega
    exact pkT_runSepA_iff.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, mem_Icc.2 ⟨by omega, by omega⟩, hwΘ, hzΘ, g,
      (hGΘ g hg1.1 hg1.2).1 hg, hgw⟩
  · by_cases hzK : z ∈ K
    · left
      obtain ⟨hz1, hz2, hzΘ⟩ := hKA z hzK hzG
      refine pkT_runSepA_iff.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, mem_Icc.2 ⟨hz1, hz2⟩, hwΘ, hzΘ, ?_⟩
      by_cases hgΘ : g ∈ Θ
      · exact ⟨g, hgΘ, hgw⟩
      · exfalso
        have hgab := hGab g hg
        have hg' : g = a ∨ g = b := by
          by_contra hne
          have h2 : a < g ∧ g < b := by omega
          exact hgΘ ((hGΘ g h2.1 h2.2).1 hg)
        rcases hg' with rfl | rfl
        · have := ha7 hg hgΘ z hzK
          omega
        · have := hb7 hg hgΘ z hzK
          omega
    · right
      have hza : z ≠ a := fun h => hzK (h ▸ haK)
      have hzb : z ≠ b := fun h => hzK (h ▸ hbK)
      refine pkT_inST_iff.2 ⟨hwK, hzK, ?_, ?_⟩
      · by_cases hza' : z ≤ a
        · exact ⟨a, haK, by omega⟩
        · exact ⟨b, hbK, by omega⟩
      · by_cases hza' : z ≤ a
        · exact ⟨b, hbK, by omega⟩
        · exact ⟨a, haK, by omega⟩

/-- **Block lemma** (PL-type, one cut): `G ⊆ [a, b]` agrees with `Θ` strictly inside the `K`-free block `(a, b)`,
`a, b ∈ K`; then every pair separated by `G` is separated by the runs of `A′ ∖ Θ` or by `K`. -/
theorem pkT_block {ω : ℕ} {Θ K G : Finset ℕ} {a b u v : ℕ}
    (haK : a ∈ K) (hbK : b ∈ K)
    (hGab : ∀ g ∈ G, a ≤ g ∧ g ≤ b)
    (hGΘ : ∀ x, a < x → x < b → (x ∈ G ↔ x ∈ Θ))
    (hK : ∀ k ∈ K, ¬ (a < k ∧ k < b))
    (hbω : b ≤ ω + 1)
    (hKA : ∀ k ∈ K, k ∉ G → 1 ≤ k ∧ k ≤ ω ∧ k ∉ Θ)
    (hb7 : b ∈ G → b ∉ Θ → ∀ k ∈ K, k ≤ b)
    (ha7 : a ∈ G → a ∉ Θ → ∀ k ∈ K, a ≤ k)
    (huv : u < v) (h : InST G u v) : runSepA ω Θ u v ∨ InST K u v := by
  rw [pkT_inST_iff, min_eq_left huv.le, max_eq_right huv.le] at h
  obtain ⟨huG, hvG, ⟨g1, hg1, h1⟩, ⟨g2, hg2, h2⟩⟩ := h
  have hb1 := hGab g1 hg1
  have hb2 := hGab g2 hg2
  rcases h2 with h2 | h2
  · exact pkT_block_core haK hbK hGab hGΘ hK hbω hKA hb7 ha7 (w := u) (z := v) (by omega) (by omega) huG hvG hg1
      (by rw [min_eq_left huv.le, max_eq_right huv.le]; exact h1)
  · rcases pkT_block_core haK hbK hGab hGΘ hK hbω hKA hb7 ha7 (w := v) (z := u) (by omega) (by omega) hvG huG hg1
      (by rw [min_eq_right huv.le, max_eq_left huv.le]; exact h1) with h | h
    · exact Or.inl (pkT_runSepA_comm.1 h)
    · exact Or.inr (pkT_inST_comm.1 h)

theorem pkT_gamma {ω x0 x1 y0 y1 : ℕ} {Θ : Finset ℕ} (hX : IsRun ω Θ x0 x1) (hY : IsRun ω Θ y0 y1)
    (hxy : x1 < y0) : x1 + 1 ∈ Θ ∧ y0 - 1 ∈ Θ := by
  obtain ⟨hx0, hx01, hx1ω, -, hx1Θ, -⟩ := hX
  obtain ⟨hy0, hy01, hy1ω, hy0Θ, -, -⟩ := hY
  exact ⟨hx1Θ.resolve_left (by omega), hy0Θ.resolve_left (by omega)⟩

/-- The arc of length `len` starting at leg `N`: `N` itself, then `1, …, len − 1`. -/
theorem pkT_mem_cycArc_N {N len x : ℕ} (hN : 1 ≤ N) (hl : len ≤ N) :
    x ∈ cycArc N N len ↔ (1 ≤ len ∧ x = N) ∨ (1 ≤ x ∧ x < len) := by
  rw [pkT_mem_cycArc]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · left
      rw [Nat.add_zero, vtx_of_mem hN le_rfl]
      exact ⟨by omega, rfl⟩
    · right
      rw [vtx_of_gt (by omega) (by omega)]
      omega
  · rintro (⟨h1, rfl⟩ | ⟨h1, h2⟩)
    · exact ⟨0, by omega, by rw [Nat.add_zero, vtx_of_mem hN le_rfl]⟩
    · exact ⟨x, h2, by rw [vtx_of_gt (by omega) (by omega)]; omega⟩

/-- A trace that is not an even singleton is odd (from admissibility). -/
theorem pkT_odd_of_adm {N a b : ℕ} {τ : Finset ℕ} (hτ : AdmSepCompl N a b τ) (hA : ¬ ∃ t, τ = {t} ∧ t % 2 = 0) :
    ∀ t ∈ τ, t % 2 = 1 := by
  rcases hτ with ⟨t, -, rfl⟩ | ⟨-, -, hodd⟩
  · intro s hs
    rw [mem_singleton] at hs
    subst hs
    by_contra hc
    exact hA ⟨s, rfl, by omega⟩
  · exact hodd

/-- **Case A** (`τ = {t}` even; v3 Lemma 14.2 (A), BP App. E §4 with `V = [γ, t − 1]`): the even witness
`U_e ∩ [x₁ + 1, t]`. -/
theorem pkT_caseA {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} (h : ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ)
    {t : ℕ} (ht : τ = {t}) (hte : t % 2 = 0) :
    ∃ G, ConsecWit N Θ τ σ G ∧ sepPairs N G ⊆ threeSepCut N ω x0 x1 y0 y1 Θ τ σ := by
  obtain ⟨hNe, hωo, hωN, -, hΘsub, hΘev, hX, hY, hxy, hX3, hY3, -, hσ, -, -, hτL, hσL⟩ := h
  obtain ⟨hγ, hγ'⟩ := pkT_gamma hX hY hxy
  obtain ⟨hx0, hx01, hx1ω, -, -, hXΘ⟩ := hX
  obtain ⟨hy0, hy01, hy1ω, -, -, hYΘ⟩ := hY
  have hx1o : x1 % 2 = 1 := by have := hΘev _ hγ; omega
  have hy0o : y0 % 2 = 1 := by have := hΘev _ hγ'; omega
  subst ht
  have htpos : y0 < t ∧ t ≤ ω + 1 := by
    rcases hτL with h1 | h1
    · rw [mem_singleton] at h1; omega
    · rw [pkT_inST_iff, min_eq_left (show y0 ≤ ω + 2 by omega), max_eq_right (show y0 ≤ ω + 2 by omega)] at h1
      obtain ⟨-, -, ⟨k, hk, hk1⟩, -⟩ := h1
      rw [mem_union, mem_Icc, mem_singleton] at hk
      rcases hk with hk | rfl <;> omega
  have hσe : ∀ s ∈ σ, s % 2 = 0 → s < x1 ∨ ω + 2 < s := by
    intro s hs hse
    have hσs : σ = {s} := by
      rcases hσ with ⟨s', -, rfl⟩ | ⟨-, -, hodd⟩
      · rw [mem_singleton] at hs; rw [hs]
      · have := hodd s hs; omega
    rw [hσs] at hσL
    rcases hσL with h1 | h1
    · rw [mem_singleton] at h1; omega
    · rw [pkT_inST_iff, min_eq_left (show x1 ≤ ω + 2 by omega), max_eq_right (show x1 ≤ ω + 2 by omega)] at h1
      obtain ⟨-, -, -, ⟨k, hk, hk1⟩⟩ := h1
      rw [mem_union, mem_Icc, mem_singleton] at hk
      rcases hk with hk | rfl <;> omega
  have hmem : ∀ x, x ∈ evens (Θ ∪ {t} ∪ σ) ∩ cycArc N (x1 + 1) (t - x1) ↔
      x1 + 1 ≤ x ∧ x ≤ t ∧ (x ∈ Θ ∨ x = t) := by
    intro x
    rw [mem_inter, pkT_mem_evens, pkT_mem_cycArc_lin (N := N) (a := x1 + 1) (len := t - x1) (x := x) (by omega)
      (by omega), mem_union, mem_union, mem_singleton]
    constructor
    · rintro ⟨⟨(hx | hx) | hx, hxe⟩, h1, h2⟩
      · exact ⟨h1, by omega, Or.inl hx⟩
      · exact ⟨h1, by omega, Or.inr hx⟩
      · have := hσe x hx hxe; omega
    · rintro ⟨h1, h2, hx | hx⟩
      · exact ⟨⟨Or.inl (Or.inl hx), hΘev x hx⟩, h1, by omega⟩
      · exact ⟨⟨Or.inl (Or.inr hx), by omega⟩, h1, by omega⟩
  refine ⟨evens (Θ ∪ {t} ∪ σ) ∩ cycArc N (x1 + 1) (t - x1), pkT_consecWit_iff.2 ⟨?_, x1 + 1,
    mem_Icc.2 ⟨by omega, by omega⟩, t - x1, mem_range.2 (by omega), Or.inl rfl⟩, ?_⟩
  · have hsub : ({x1 + 1, t} : Finset ℕ) ⊆ evens (Θ ∪ {t} ∪ σ) ∩ cycArc N (x1 + 1) (t - x1) := by
      intro x hx
      rw [mem_insert, mem_singleton] at hx
      rcases hx with hx | hx
      · exact (hmem x).2 ⟨by omega, by omega, Or.inl (hx ▸ hγ)⟩
      · exact (hmem x).2 ⟨by omega, by omega, Or.inr hx⟩
    have := card_le_card hsub
    rw [card_pair (by omega)] at this
    exact this
  · intro p hp
    obtain ⟨hd, hpG⟩ := pkT_mem_sepPairs.1 hp
    have hd' := mem_diagonals.1 hd
    refine pkT_mem_threeSepCut.2 ⟨hd, ?_⟩
    have hres := pkT_block (ω := ω) (Θ := Θ) (K := Icc x0 x1 ∪ {t}) (a := x1) (b := t)
      (mem_union.2 (Or.inl (mem_Icc.2 ⟨hx01, le_refl _⟩))) (mem_union.2 (Or.inr (mem_singleton_self t)))
      (fun g hg => by have := (hmem g).1 hg; omega)
      (fun x h1 h2 => by
        rw [hmem]
        constructor
        · rintro ⟨-, -, hx | hx⟩
          · exact hx
          · omega
        · intro hx
          exact ⟨by omega, by omega, Or.inl hx⟩)
      (fun k hk hk2 => by rw [mem_union, mem_Icc, mem_singleton] at hk; omega)
      htpos.2
      (fun k hk hkG => by
        rw [mem_union, mem_Icc, mem_singleton] at hk
        rcases hk with hk | hk
        · exact ⟨by omega, by omega, hXΘ k (mem_Icc.2 hk)⟩
        · exact absurd ((hmem k).2 ⟨by omega, by omega, Or.inr hk⟩) hkG)
      (fun _ _ k hk => by rw [mem_union, mem_Icc, mem_singleton] at hk; omega)
      (fun hx1G => by have := (hmem x1).1 hx1G; omega)
      (by omega) hpG
    rcases hres with hr | hr
    · exact Or.inl hr
    · exact Or.inr (Or.inl hr)

/-- The position of an even singleton `σ = {g}` ((F2) for `σ`, (b0)): `g < x₁` or `g = N`. -/
theorem pkT_sigma_even_pos {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} (h : ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ)
    {g : ℕ} (hg : σ = {g}) (hge : g % 2 = 0) : (1 ≤ g ∧ g < x1) ∨ g = N := by
  obtain ⟨hNe, hωo, hωN, -, hΘsub, hΘev, hX, hY, hxy, hX3, hY3, -, hσ, -, hσb, -, hσL⟩ := h
  obtain ⟨hγ, hγ'⟩ := pkT_gamma hX hY hxy
  obtain ⟨hx0, hx01, hx1ω, -, -, hXΘ⟩ := hX
  obtain ⟨hy0, hy01, hy1ω, -, -, hYΘ⟩ := hY
  have hx1o : x1 % 2 = 1 := by have := hΘev _ hγ; omega
  subst hg
  have hgN : 1 ≤ g ∧ g ≤ N := by
    rcases hσ with ⟨s, hs, hgs⟩ | ⟨hc, -, -⟩
    · rw [singleton_inj] at hgs
      subst hgs
      have := (mem_sdiff.1 hs).1
      rw [mem_Icc] at this
      exact this
    · rw [card_singleton] at hc; omega
  have hgb : g ∉ Icc (ω + 2) (N - 1) := disjoint_singleton_left.1 hσb.1
  rw [mem_Icc] at hgb
  rcases hσL with h1 | h1
  · rw [mem_singleton] at h1; omega
  · rw [pkT_inST_iff, min_eq_left (show x1 ≤ ω + 2 by omega), max_eq_right (show x1 ≤ ω + 2 by omega)] at h1
    obtain ⟨-, -, -, ⟨k, hk, hk1⟩⟩ := h1
    rw [mem_union, mem_Icc, mem_singleton] at hk
    rcases hk with hk | rfl <;> omega

/-- **Case B, linear** (`σ = {g}` even, `g < x₁`, `τ` odd): the even witness `U_e ∩ [g, y₀ − 1]`. -/
theorem pkT_caseB_lin {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} (h : ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ)
    (hτo : ∀ t ∈ τ, t % 2 = 1) {g : ℕ} (hg : σ = {g}) (hge : g % 2 = 0) (hg1 : 1 ≤ g) (hgx : g < x1) :
    ∃ G, ConsecWit N Θ τ σ G ∧ sepPairs N G ⊆ threeSepCut N ω x0 x1 y0 y1 Θ τ σ := by
  obtain ⟨hNe, hωo, hωN, -, hΘsub, hΘev, hX, hY, hxy, hX3, hY3, -, -, -, -, -, -⟩ := h
  obtain ⟨hγ, hγ'⟩ := pkT_gamma hX hY hxy
  obtain ⟨hx0, hx01, hx1ω, -, -, hXΘ⟩ := hX
  obtain ⟨hy0, hy01, hy1ω, -, -, hYΘ⟩ := hY
  have hx1o : x1 % 2 = 1 := by have := hΘev _ hγ; omega
  have hy0o : y0 % 2 = 1 := by have := hΘev _ hγ'; omega
  subst hg
  have hmem : ∀ x, x ∈ evens (Θ ∪ τ ∪ {g}) ∩ cycArc N g (y0 - g) ↔ g ≤ x ∧ x < y0 ∧ (x ∈ Θ ∨ x = g) := by
    intro x
    rw [mem_inter, pkT_mem_evens, pkT_mem_cycArc_lin (N := N) (a := g) (len := y0 - g) (x := x) hg1
      (by omega), mem_union, mem_union, mem_singleton]
    constructor
    · rintro ⟨⟨(hx | hx) | hx, hxe⟩, h1, h2⟩
      · exact ⟨h1, by omega, Or.inl hx⟩
      · have := hτo x hx; omega
      · exact ⟨h1, by omega, Or.inr hx⟩
    · rintro ⟨h1, h2, hx | hx⟩
      · exact ⟨⟨Or.inl (Or.inl hx), hΘev x hx⟩, h1, by omega⟩
      · exact ⟨⟨Or.inr hx, by omega⟩, h1, by omega⟩
  refine ⟨evens (Θ ∪ τ ∪ {g}) ∩ cycArc N g (y0 - g), pkT_consecWit_iff.2 ⟨?_, g,
    mem_Icc.2 ⟨hg1, by omega⟩, y0 - g, mem_range.2 (by omega), Or.inl rfl⟩, ?_⟩
  · have hsub : ({g, y0 - 1} : Finset ℕ) ⊆ evens (Θ ∪ τ ∪ {g}) ∩ cycArc N g (y0 - g) := by
      intro x hx
      rw [mem_insert, mem_singleton] at hx
      rcases hx with hx | hx
      · exact (hmem x).2 ⟨by omega, by omega, Or.inr hx⟩
      · exact (hmem x).2 ⟨by omega, by omega, Or.inl (hx ▸ hγ')⟩
    have := card_le_card hsub
    rw [card_pair (by omega)] at this
    exact this
  · intro p hp
    obtain ⟨hd, hpG⟩ := pkT_mem_sepPairs.1 hp
    have hd' := mem_diagonals.1 hd
    refine pkT_mem_threeSepCut.2 ⟨hd, ?_⟩
    have hres := pkT_block (ω := ω) (Θ := Θ) (K := Icc y0 y1 ∪ {g}) (a := g) (b := y0)
      (mem_union.2 (Or.inr (mem_singleton_self g))) (mem_union.2 (Or.inl (mem_Icc.2 ⟨le_refl _, hy01⟩)))
      (fun x hx => by have := (hmem x).1 hx; omega)
      (fun x h1 h2 => by
        rw [hmem]
        constructor
        · rintro ⟨-, -, hx | hx⟩
          · exact hx
          · omega
        · intro hx
          exact ⟨by omega, by omega, Or.inl hx⟩)
      (fun k hk hk2 => by rw [mem_union, mem_Icc, mem_singleton] at hk; omega)
      (by omega)
      (fun k hk hkG => by
        rw [mem_union, mem_Icc, mem_singleton] at hk
        rcases hk with hk | hk
        · exact ⟨by omega, by omega, hYΘ k (mem_Icc.2 hk)⟩
        · exact absurd ((hmem k).2 ⟨by omega, by omega, Or.inr hk⟩) hkG)
      (fun hy0G => by have := (hmem y0).1 hy0G; omega)
      (fun _ _ k hk => by rw [mem_union, mem_Icc, mem_singleton] at hk; omega)
      (by omega) hpG
    rcases hres with hr | hr
    · exact Or.inl hr
    · exact Or.inr (Or.inr hr)

/-- **Case B, wrapping** (`σ = {N}`, `τ` odd): the even witness `U_e ∩ [N, y₀ − 1]` (through `N`, `1`). -/
theorem pkT_caseB_wrap {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} (h : ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ)
    (hτo : ∀ t ∈ τ, t % 2 = 1) (hg : σ = {N}) :
    ∃ G, ConsecWit N Θ τ σ G ∧ sepPairs N G ⊆ threeSepCut N ω x0 x1 y0 y1 Θ τ σ := by
  obtain ⟨hNe, hωo, hωN, -, hΘsub, hΘev, hX, hY, hxy, hX3, hY3, -, -, -, -, -, -⟩ := h
  obtain ⟨hγ, hγ'⟩ := pkT_gamma hX hY hxy
  obtain ⟨hx0, hx01, hx1ω, -, -, hXΘ⟩ := hX
  obtain ⟨hy0, hy01, hy1ω, -, -, hYΘ⟩ := hY
  have hΘω : ∀ x ∈ Θ, 2 ≤ x ∧ x ≤ ω - 1 := fun x hx => mem_Icc.1 (hΘsub hx)
  subst hg
  have hmem : ∀ x, x ∈ evens (Θ ∪ τ ∪ {N}) ∩ cycArc N N y0 ↔ x = N ∨ (x < y0 ∧ x ∈ Θ) := by
    intro x
    rw [mem_inter, pkT_mem_evens, pkT_mem_cycArc_N (by omega) (by omega), mem_union, mem_union, mem_singleton]
    constructor
    · rintro ⟨⟨(hx | hx) | hx, hxe⟩, h1⟩
      · rcases h1 with h1 | h1
        · exact Or.inl h1.2
        · exact Or.inr ⟨h1.2, hx⟩
      · have := hτo x hx; omega
      · exact Or.inl hx
    · rintro (hx | ⟨h1, hx⟩)
      · exact ⟨⟨Or.inr hx, by omega⟩, Or.inl ⟨by omega, hx⟩⟩
      · have := hΘω x hx
        exact ⟨⟨Or.inl (Or.inl hx), hΘev x hx⟩, Or.inr ⟨by omega, h1⟩⟩
  refine ⟨evens (Θ ∪ τ ∪ {N}) ∩ cycArc N N y0, pkT_consecWit_iff.2 ⟨?_, N,
    mem_Icc.2 ⟨by omega, le_refl _⟩, y0, mem_range.2 (by omega), Or.inl rfl⟩, ?_⟩
  · have hsub : ({N, y0 - 1} : Finset ℕ) ⊆ evens (Θ ∪ τ ∪ {N}) ∩ cycArc N N y0 := by
      intro x hx
      rw [mem_insert, mem_singleton] at hx
      rcases hx with hx | hx
      · exact (hmem x).2 (Or.inl hx)
      · exact (hmem x).2 (Or.inr ⟨by omega, hx ▸ hγ'⟩)
    have := card_le_card hsub
    rw [card_pair (by omega)] at this
    exact this
  · intro p hp
    obtain ⟨hd, hpG⟩ := pkT_mem_sepPairs.1 hp
    have hd' := mem_diagonals.1 hd
    refine pkT_mem_threeSepCut.2 ⟨hd, ?_⟩
    have huv : p.1 < p.2 := by omega
    rw [pkT_inST_iff, min_eq_left huv.le, max_eq_right huv.le] at hpG
    obtain ⟨huG, hvG, ⟨g1, hg1, h1⟩, -⟩ := hpG
    have hg1' : g1 < y0 ∧ g1 ∈ Θ := by
      rcases (hmem g1).1 hg1 with hx | hx
      · omega
      · exact hx
    have hg1ω := hΘω g1 hg1'.2
    have huΘ : p.1 ∉ Θ := fun hu => huG ((hmem _).2 (Or.inr ⟨by omega, hu⟩))
    have hvN : p.2 ≠ N := fun hv => hvG ((hmem _).2 (Or.inl hv))
    by_cases hv : p.2 ∈ Θ ∨ ω < p.2
    · right; right
      have hvy : y1 < p.2 := by
        rcases hv with hv | hv
        · have hvy0 : y0 ≤ p.2 := by
            by_contra hc
            exact hvG ((hmem _).2 (Or.inr ⟨by omega, hv⟩))
          by_contra hc
          exact hYΘ _ (mem_Icc.2 ⟨hvy0, by omega⟩) hv
        · omega
      refine pkT_inST_iff.2 ⟨?_, ?_, ⟨y0, mem_union.2 (Or.inl (mem_Icc.2 ⟨le_refl _, hy01⟩)), ?_⟩,
        ⟨N, mem_union.2 (Or.inr (mem_singleton_self N)), ?_⟩⟩
      · rw [mem_union, mem_Icc, mem_singleton]; omega
      · rw [mem_union, mem_Icc, mem_singleton]; omega
      · rw [min_eq_left huv.le, max_eq_right huv.le]; omega
      · rw [min_eq_left huv.le, max_eq_right huv.le]; omega
    · left
      have hvΘ : p.2 ∉ Θ := fun h' => hv (Or.inl h')
      refine pkT_runSepA_iff.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, mem_Icc.2 ⟨by omega, by omega⟩, huΘ, hvΘ, g1,
        hg1'.2, ?_⟩
      rw [min_eq_left huv.le, max_eq_right huv.le]; exact h1

/-- For odd traces every leg of `X ∪ τ` and of `Y ∪ σ` lies in `A′ ∖ Θ` ((P), (b0)). -/
theorem pkT_K_facts {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} (h : ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ)
    (hτo : ∀ t ∈ τ, t % 2 = 1) (hσo : ∀ t ∈ σ, t % 2 = 1) :
    (∀ k ∈ Icc x0 x1 ∪ τ, 1 ≤ k ∧ k ≤ ω ∧ k ∉ Θ) ∧ (∀ k ∈ Icc y0 y1 ∪ σ, 1 ≤ k ∧ k ≤ ω ∧ k ∉ Θ) := by
  obtain ⟨hNe, hωo, hωN, -, hΘsub, hΘev, hX, hY, hxy, hX3, hY3, hτ, hσ, hτb, hσb, -, -⟩ := h
  obtain ⟨hx0, hx01, hx1ω, -, -, hXΘ⟩ := hX
  obtain ⟨hy0, hy01, hy1ω, -, -, hYΘ⟩ := hY
  have htr : ∀ {a b : ℕ} {D : Finset ℕ}, AdmSepCompl N a b D → TailAvoiding N ω D → (∀ t ∈ D, t % 2 = 1) →
      ∀ k ∈ D, 1 ≤ k ∧ k ≤ ω ∧ k ∉ Θ := by
    intro a b D hD hDb hDo k hk
    have hk1 : k ∈ Icc 1 N := by
      rcases hD with ⟨s, hs, rfl⟩ | ⟨-, hsub, -⟩
      · rw [mem_singleton] at hk
        subst hk
        exact (mem_sdiff.1 hs).1
      · exact (mem_sdiff.1 (hsub hk)).1
    have hkW : k ∉ Icc (ω + 1) N := disjoint_left.1 (hDb.2 hDo) hk
    rw [mem_Icc] at hk1 hkW
    refine ⟨hk1.1, by omega, fun hkΘ => ?_⟩
    have := hΘev k hkΘ
    have := hDo k hk
    omega
  constructor
  · intro k hk
    rcases mem_union.1 hk with hk | hk
    · have := mem_Icc.1 hk
      exact ⟨by omega, by omega, hXΘ k hk⟩
    · exact htr hτ hτb hτo k hk
  · intro k hk
    rcases mem_union.1 hk with hk | hk
    · have := mem_Icc.1 hk
      exact ⟨by omega, by omega, hYΘ k hk⟩
    · exact htr hσ hσb hσo k hk

/-- **Case EP** (both traces odd; a non-`R` piece `(a, b)` of `X ∪ τ` or `Y ∪ σ` holds two Θ-legs; PL* = BP App. E §4
for odd traces): the even witness `Θ ∩ (a, b) = U_e ∩ [a + 1, b − 1]`. -/
theorem pkT_caseEP {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ K : Finset ℕ} (h : ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ)
    (hτo : ∀ t ∈ τ, t % 2 = 1) (hσo : ∀ t ∈ σ, t % 2 = 1)
    (hK : K = Icc x0 x1 ∪ τ ∨ K = Icc y0 y1 ∪ σ)
    {a b : ℕ} (ha : a ∈ K) (hb : b ∈ K) (hab : a < b) (hgap : ∀ k ∈ K, ¬ (a < k ∧ k < b))
    (h2 : 2 ≤ (Θ.filter (fun x => a < x ∧ x < b)).card) :
    ∃ G, ConsecWit N Θ τ σ G ∧ sepPairs N G ⊆ threeSepCut N ω x0 x1 y0 y1 Θ τ σ := by
  obtain ⟨hKX, hKY⟩ := pkT_K_facts h hτo hσo
  have hKA : ∀ k ∈ K, 1 ≤ k ∧ k ≤ ω ∧ k ∉ Θ := by
    rcases hK with hK | hK
    · rw [hK]; exact hKX
    · rw [hK]; exact hKY
  obtain ⟨hNe, hωo, hωN, -, hΘsub, hΘev, -⟩ := h
  obtain ⟨hb1, hbω, -⟩ := hKA b hb
  obtain ⟨ha1, haω, -⟩ := hKA a ha
  have hmem : ∀ x, x ∈ evens (Θ ∪ τ ∪ σ) ∩ cycArc N (a + 1) (b - a - 1) ↔ a < x ∧ x < b ∧ x ∈ Θ := by
    intro x
    rw [mem_inter, pkT_mem_evens, pkT_mem_cycArc_lin (N := N) (a := a + 1) (len := b - a - 1) (x := x)
      (by omega) (by omega), mem_union, mem_union]
    constructor
    · rintro ⟨⟨(hx | hx) | hx, hxe⟩, h1, h2⟩
      · exact ⟨by omega, by omega, hx⟩
      · have := hτo x hx; omega
      · have := hσo x hx; omega
    · rintro ⟨h1, h2, hx⟩
      exact ⟨⟨Or.inl (Or.inl hx), hΘev x hx⟩, by omega, by omega⟩
  refine ⟨evens (Θ ∪ τ ∪ σ) ∩ cycArc N (a + 1) (b - a - 1), pkT_consecWit_iff.2 ⟨?_, a + 1,
    mem_Icc.2 ⟨by omega, by omega⟩, b - a - 1, mem_range.2 (by omega), Or.inl rfl⟩, ?_⟩
  · refine le_trans h2 (card_le_card fun x hx => (hmem x).2 ?_)
    have := mem_filter.1 hx
    exact ⟨this.2.1, this.2.2, this.1⟩
  · intro p hp
    obtain ⟨hd, hpG⟩ := pkT_mem_sepPairs.1 hp
    have hd' := mem_diagonals.1 hd
    refine pkT_mem_threeSepCut.2 ⟨hd, ?_⟩
    have hres := pkT_block (ω := ω) (Θ := Θ) (K := K) (a := a) (b := b) ha hb
      (fun x hx => by have := (hmem x).1 hx; omega)
      (fun x h1 h2 => by rw [hmem]; exact ⟨fun h' => h'.2.2, fun h' => ⟨h1, h2, h'⟩⟩)
      hgap (by omega)
      (fun k hk _ => hKA k hk)
      (fun hbG => absurd ((hmem b).1 hbG).2.1 (lt_irrefl b))
      (fun haG => absurd ((hmem a).1 haG).1 (lt_irrefl a))
      (by omega) hpG
    rcases hres with hr | hr
    · exact Or.inl hr
    · rcases hK with hK | hK
      · rw [hK] at hr; exact Or.inr (Or.inl hr)
      · rw [hK] at hr; exact Or.inr (Or.inr hr)

/-! ### Zone case (pkgTri, both traces odd, ¬EP): the zone set `G′` and its three properties

Walk-free linear form of the end-blocked zones (BP App. E §2) for odd traces. Checked equal to the walk definition on
every zone-case configuration N = 10–18 (`zone_pred.py`: 9 / 132 / 1 405 / 13 078 / 112 896), with |G′| ≥ 2, G′ a
linear `U_o`-block and `S_{G′} ⊆ C₀` in every case (`zone_lin.py` N ≤ 16, `zone_pred.py` N = 18). -/

/-- `t ∈ τ` lies in `Z_X^L`: (A) `t ∈ Λ`, no σ-leg in `[t, x₀]`, and σ misses `[1, x₀]` or a Θ-leg `θ < t` has no
σ-leg in `[θ, x₀]`; (B) `t ∈ Ρ`, σ misses `[1, x₀]`, and a Θ-leg `θ ∈ (y₁, t)` has no σ-leg in `[θ, ω]`. -/
def pkT_remT (ω x0 y1 : ℕ) (Θ σ : Finset ℕ) (t : ℕ) : Prop :=
  (t < x0 ∧ (∀ s ∈ σ, ¬ (t ≤ s ∧ s ≤ x0)) ∧
    ((∀ s ∈ σ, ¬ s ≤ x0) ∨ ∃ θ ∈ Θ, θ < t ∧ ∀ s ∈ σ, ¬ (θ ≤ s ∧ s ≤ x0))) ∨
  (y1 < t ∧ (∀ s ∈ σ, ¬ s ≤ x0) ∧ ∃ θ ∈ Θ, y1 < θ ∧ θ < t ∧ ∀ s ∈ σ, ¬ (θ ≤ s ∧ s ≤ ω))

/-- `s ∈ σ` lies in `Z_Y^R` (mirror of `pkT_remT`). -/
def pkT_remS (ω x0 y1 : ℕ) (Θ τ : Finset ℕ) (s : ℕ) : Prop :=
  (y1 < s ∧ (∀ t ∈ τ, ¬ (y1 ≤ t ∧ t ≤ s)) ∧
    ((∀ t ∈ τ, ¬ (y1 ≤ t ∧ t ≤ ω)) ∨ ∃ θ ∈ Θ, s < θ ∧ ∀ t ∈ τ, ¬ (y1 ≤ t ∧ t ≤ θ))) ∨
  (s < x0 ∧ (∀ t ∈ τ, ¬ (y1 ≤ t ∧ t ≤ ω)) ∧ ∃ θ ∈ Θ, s < θ ∧ θ < x0 ∧ ∀ t ∈ τ, ¬ t ≤ θ)

/-- The zone set `G′ = (τ ∖ Z_X) ∪ (σ ∖ Z_Y)` (odd traces). -/
def pkT_zoneSet (ω x0 y1 : ℕ) (Θ τ σ : Finset ℕ) : Finset ℕ :=
  τ.filter (fun t => ¬ ((t < x0 ∧ (∀ s ∈ σ, ¬ (t ≤ s ∧ s ≤ x0)) ∧
            ((∀ s ∈ σ, ¬ s ≤ x0) ∨ ∃ θ ∈ Θ, θ < t ∧ ∀ s ∈ σ, ¬ (θ ≤ s ∧ s ≤ x0))) ∨
          (y1 < t ∧ (∀ s ∈ σ, ¬ s ≤ x0) ∧ ∃ θ ∈ Θ, y1 < θ ∧ θ < t ∧ ∀ s ∈ σ, ¬ (θ ≤ s ∧ s ≤ ω)))) ∪
    σ.filter (fun s => ¬ ((y1 < s ∧ (∀ t ∈ τ, ¬ (y1 ≤ t ∧ t ≤ s)) ∧
            ((∀ t ∈ τ, ¬ (y1 ≤ t ∧ t ≤ ω)) ∨ ∃ θ ∈ Θ, s < θ ∧ ∀ t ∈ τ, ¬ (y1 ≤ t ∧ t ≤ θ))) ∨
          (s < x0 ∧ (∀ t ∈ τ, ¬ (y1 ≤ t ∧ t ≤ ω)) ∧ ∃ θ ∈ Θ, s < θ ∧ θ < x0 ∧ ∀ t ∈ τ, ¬ t ≤ θ)))


theorem pkT_remT_iff {ω x0 y1 : ℕ} {Θ σ : Finset ℕ} {t : ℕ} :
    pkT_remT ω x0 y1 Θ σ t ↔ (t < x0 ∧ (∀ s ∈ σ, ¬ (t ≤ s ∧ s ≤ x0)) ∧
        ((∀ s ∈ σ, ¬ s ≤ x0) ∨ ∃ θ ∈ Θ, θ < t ∧ ∀ s ∈ σ, ¬ (θ ≤ s ∧ s ≤ x0))) ∨
      (y1 < t ∧ (∀ s ∈ σ, ¬ s ≤ x0) ∧ ∃ θ ∈ Θ, y1 < θ ∧ θ < t ∧ ∀ s ∈ σ, ¬ (θ ≤ s ∧ s ≤ ω)) :=
  Iff.rfl

theorem pkT_remS_iff {ω x0 y1 : ℕ} {Θ τ : Finset ℕ} {s : ℕ} :
    pkT_remS ω x0 y1 Θ τ s ↔ (y1 < s ∧ (∀ t ∈ τ, ¬ (y1 ≤ t ∧ t ≤ s)) ∧
        ((∀ t ∈ τ, ¬ (y1 ≤ t ∧ t ≤ ω)) ∨ ∃ θ ∈ Θ, s < θ ∧ ∀ t ∈ τ, ¬ (y1 ≤ t ∧ t ≤ θ))) ∨
      (s < x0 ∧ (∀ t ∈ τ, ¬ (y1 ≤ t ∧ t ≤ ω)) ∧ ∃ θ ∈ Θ, s < θ ∧ θ < x0 ∧ ∀ t ∈ τ, ¬ t ≤ θ) :=
  Iff.rfl


/-! ### Zone case, linear proof (pkgTri-2). Hypotheses of the zone case bundled; ¬EP enters only through `pkT_gap`. -/

/-- The zone-case hypotheses: the setting, odd traces, and no `X ∪ τ`- or `Y ∪ σ`-gap with two Θ-legs (¬EP). -/
def pkT_ZH (N ω x0 x1 y0 y1 : ℕ) (Θ τ σ : Finset ℕ) : Prop :=
  ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ ∧ (∀ t ∈ τ, t % 2 = 1) ∧ (∀ t ∈ σ, t % 2 = 1) ∧
  (∀ a ∈ Icc x0 x1 ∪ τ, ∀ b ∈ Icc x0 x1 ∪ τ, a < b → (∀ k ∈ Icc x0 x1 ∪ τ, ¬ (a < k ∧ k < b)) →
      (Θ.filter (fun x => a < x ∧ x < b)).card ≤ 1) ∧
  (∀ a ∈ Icc y0 y1 ∪ σ, ∀ b ∈ Icc y0 y1 ∪ σ, a < b → (∀ k ∈ Icc y0 y1 ∪ σ, ¬ (a < k ∧ k < b)) →
      (Θ.filter (fun x => a < x ∧ x < b)).card ≤ 1)

theorem pkT_ZH_iff {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} :
    pkT_ZH N ω x0 x1 y0 y1 Θ τ σ ↔
  ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ ∧ (∀ t ∈ τ, t % 2 = 1) ∧ (∀ t ∈ σ, t % 2 = 1) ∧
    (∀ a ∈ Icc x0 x1 ∪ τ, ∀ b ∈ Icc x0 x1 ∪ τ, a < b → (∀ k ∈ Icc x0 x1 ∪ τ, ¬ (a < k ∧ k < b)) →
        (Θ.filter (fun x => a < x ∧ x < b)).card ≤ 1) ∧
    (∀ a ∈ Icc y0 y1 ∪ σ, ∀ b ∈ Icc y0 y1 ∪ σ, a < b → (∀ k ∈ Icc y0 y1 ∪ σ, ¬ (a < k ∧ k < b)) →
        (Θ.filter (fun x => a < x ∧ x < b)).card ≤ 1) :=
  Iff.rfl

theorem pkT_ZH_nX {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} (H : pkT_ZH N ω x0 x1 y0 y1 Θ τ σ) :
    ∀ a ∈ Icc x0 x1 ∪ τ, ∀ b ∈ Icc x0 x1 ∪ τ, a < b → (∀ k ∈ Icc x0 x1 ∪ τ, ¬ (a < k ∧ k < b)) →
      (Θ.filter (fun x => a < x ∧ x < b)).card ≤ 1 :=
  (pkT_ZH_iff.1 H).2.2.2.1

theorem pkT_ZH_nY {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} (H : pkT_ZH N ω x0 x1 y0 y1 Θ τ σ) :
    ∀ a ∈ Icc y0 y1 ∪ σ, ∀ b ∈ Icc y0 y1 ∪ σ, a < b → (∀ k ∈ Icc y0 y1 ∪ σ, ¬ (a < k ∧ k < b)) →
      (Θ.filter (fun x => a < x ∧ x < b)).card ≤ 1 :=
  (pkT_ZH_iff.1 H).2.2.2.2

/-- Linear facts of the zone case ((F1), (P), (F2) = Long). -/
theorem pkT_zf {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} (H : pkT_ZH N ω x0 x1 y0 y1 Θ τ σ) :
    (1 ≤ x0 ∧ x0 + 2 ≤ x1 ∧ x1 < y0 ∧ y0 + 2 ≤ y1 ∧ y1 ≤ ω ∧ ω + 3 ≤ N) ∧
    (x1 + 1 ∈ Θ ∧ y0 - 1 ∈ Θ ∧ (1 < x0 → x0 - 1 ∈ Θ) ∧ (y1 < ω → y1 + 1 ∈ Θ)) ∧
    (∀ θ ∈ Θ, 2 ≤ θ ∧ θ < ω ∧ (θ < x0 ∨ x1 < θ) ∧ (θ < y0 ∨ y1 < θ)) ∧
    (∀ t ∈ τ, 1 ≤ t ∧ t ≤ ω ∧ t ∉ Θ ∧ (t < x0 ∨ x1 < t)) ∧
    (∀ s ∈ σ, 1 ≤ s ∧ s ≤ ω ∧ s ∉ Θ ∧ (s < y0 ∨ y1 < s)) ∧
    (∃ t ∈ τ, y0 ≤ t) ∧ (∃ s ∈ σ, s ≤ x1) := by
  obtain ⟨h, hτo, hσo, -, -⟩ := H
  obtain ⟨hKX, hKY⟩ := pkT_K_facts h hτo hσo
  obtain ⟨hNe, hωo, hωN, -, hΘsub, hΘev, hX, hY, hxy, hX3, hY3, hτA, hσA, -, -, hτL, hσL⟩ := h
  obtain ⟨hγ, hγ'⟩ := pkT_gamma hX hY hxy
  obtain ⟨hx0, hx01, hx1ω, hx0Θ, -, hXΘ⟩ := hX
  obtain ⟨hy0, hy01, hy1ω, -, hy1Θ, hYΘ⟩ := hY
  have hτc : ∀ t ∈ τ, t ∉ Icc x0 x1 := by
    intro t ht
    have hi : t ∈ intCompl N x0 x1 := by
      rcases hτA with ⟨s, hs, rfl⟩ | ⟨-, hsub, -⟩
      · rw [mem_singleton] at ht
        rw [ht]
        exact hs
      · exact hsub ht
    have := (mem_sdiff.1 hi).2
    exact fun h' => this (mem_union.2 (Or.inl h'))
  have hσc : ∀ s ∈ σ, s ∉ Icc y0 y1 := by
    intro s hs
    have hi : s ∈ intCompl N y0 y1 := by
      rcases hσA with ⟨s', hs', rfl⟩ | ⟨-, hsub, -⟩
      · rw [mem_singleton] at hs
        rw [hs]
        exact hs'
      · exact hsub hs
    have := (mem_sdiff.1 hi).2
    exact fun h' => this (mem_union.2 (Or.inl h'))
  refine ⟨⟨hx0, hX3, hxy, hY3, hy1ω, hωN⟩, ⟨hγ, hγ', fun h1 => hx0Θ.resolve_left (by omega),
    fun h1 => hy1Θ.resolve_left (by omega)⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro θ hθ
    have h1 := mem_Icc.1 (hΘsub hθ)
    have h2 := hΘev θ hθ
    refine ⟨h1.1, by omega, ?_, ?_⟩
    · by_contra hc
      exact hXΘ θ (mem_Icc.2 ⟨by omega, by omega⟩) hθ
    · by_contra hc
      exact hYΘ θ (mem_Icc.2 ⟨by omega, by omega⟩) hθ
  · intro t ht
    obtain ⟨h1, h2, h3⟩ := hKX t (mem_union.2 (Or.inr ht))
    refine ⟨h1, h2, h3, ?_⟩
    by_contra hc
    exact hτc t ht (mem_Icc.2 ⟨by omega, by omega⟩)
  · intro s hs
    obtain ⟨h1, h2, h3⟩ := hKY s (mem_union.2 (Or.inr hs))
    refine ⟨h1, h2, h3, ?_⟩
    by_contra hc
    exact hσc s hs (mem_Icc.2 ⟨by omega, by omega⟩)
  · rcases hτL with h1 | h1
    · exact ⟨y0, h1, le_refl _⟩
    · rw [pkT_inST_iff, min_eq_left (show y0 ≤ ω + 2 by omega), max_eq_right (show y0 ≤ ω + 2 by omega)] at h1
      obtain ⟨-, -, ⟨k, hk, hk1⟩, -⟩ := h1
      rcases mem_union.1 hk with hk' | hk'
      · have := mem_Icc.1 hk'
        omega
      · exact ⟨k, hk', by omega⟩
  · rcases hσL with h1 | h1
    · exact ⟨x1, h1, le_refl _⟩
    · rw [pkT_inST_iff, min_eq_left (show x1 ≤ ω + 2 by omega), max_eq_right (show x1 ≤ ω + 2 by omega)] at h1
      obtain ⟨-, -, -, ⟨k, hk, hk1⟩⟩ := h1
      rcases mem_union.1 hk with hk' | hk'
      · have := mem_Icc.1 hk'
        omega
      · have := hKY k (mem_union.2 (Or.inr hk'))
        exact ⟨k, hk', by omega⟩

/-- **Gap lemma** (the one use of ¬EP): two Θ-legs `p < q` with `K`-legs below `p` and above `q` have a `K`-leg in
`[p, q]`. -/
theorem pkT_gap {K Θ : Finset ℕ}
    (hn : ∀ a ∈ K, ∀ b ∈ K, a < b → (∀ k ∈ K, ¬ (a < k ∧ k < b)) → (Θ.filter (fun x => a < x ∧ x < b)).card ≤ 1)
    {p q a0 b0 : ℕ} (hp : p ∈ Θ) (hq : q ∈ Θ) (hpq : p < q) (ha0 : a0 ∈ K) (h1 : a0 < p) (hb0 : b0 ∈ K)
    (h2 : q < b0) : ∃ k ∈ K, p ≤ k ∧ k ≤ q := by
  by_contra hc
  have hL : (K.filter (fun k => k < p)).Nonempty := ⟨a0, mem_filter.2 ⟨ha0, h1⟩⟩
  have hR : (K.filter (fun k => q < k)).Nonempty := ⟨b0, mem_filter.2 ⟨hb0, h2⟩⟩
  obtain ⟨a, haK, hap, hamax⟩ : ∃ a ∈ K, a < p ∧ ∀ k ∈ K, k < p → k ≤ a :=
    ⟨(K.filter (fun k => k < p)).max' hL, (mem_filter.1 ((K.filter (fun k => k < p)).max'_mem hL)).1,
      (mem_filter.1 ((K.filter (fun k => k < p)).max'_mem hL)).2,
      fun k hk hkp => (K.filter (fun k => k < p)).le_max' k (mem_filter.2 ⟨hk, hkp⟩)⟩
  obtain ⟨b, hbK, hqb, hbmin⟩ : ∃ b ∈ K, q < b ∧ ∀ k ∈ K, q < k → b ≤ k :=
    ⟨(K.filter (fun k => q < k)).min' hR, (mem_filter.1 ((K.filter (fun k => q < k)).min'_mem hR)).1,
      (mem_filter.1 ((K.filter (fun k => q < k)).min'_mem hR)).2,
      fun k hk hkq => (K.filter (fun k => q < k)).min'_le k (mem_filter.2 ⟨hk, hkq⟩)⟩
  have hgap : ∀ k ∈ K, ¬ (a < k ∧ k < b) := by
    intro k hk hk2
    by_cases hkp : k < p
    · have := hamax k hk hkp
      omega
    · by_cases hkq : q < k
      · have := hbmin k hk hkq
        omega
      · exact hc ⟨k, hk, by omega, by omega⟩
  have h3 := hn a haK b hbK (by omega) hgap
  have hsub : ({p, q} : Finset ℕ) ⊆ Θ.filter (fun x => a < x ∧ x < b) := by
    intro x hx
    rw [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact mem_filter.2 ⟨hp, by omega, by omega⟩
    · exact mem_filter.2 ⟨hq, by omega, by omega⟩
  have := card_le_card hsub
  rw [card_pair (by omega)] at this
  omega

theorem pkT_two {G : Finset ℕ} {a b : ℕ} (ha : a ∈ G) (hb : b ∈ G) (hab : a < b) : 2 ≤ G.card := by
  have hsub : ({a, b} : Finset ℕ) ⊆ G := by
    intro x hx
    rw [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  have := card_le_card hsub
  rw [card_pair (by omega)] at this
  exact this

theorem pkT_mem_zoneSet {ω x0 y1 : ℕ} {Θ τ σ : Finset ℕ} {g : ℕ} :
    g ∈ pkT_zoneSet ω x0 y1 Θ τ σ ↔
      (g ∈ τ ∧ ¬ pkT_remT ω x0 y1 Θ σ g) ∨ (g ∈ σ ∧ ¬ pkT_remS ω x0 y1 Θ τ g) :=
  mem_union.trans (or_congr mem_filter mem_filter)

theorem pkT_remT_side {ω x0 y1 : ℕ} {Θ σ : Finset ℕ} {t : ℕ} (hr : pkT_remT ω x0 y1 Θ σ t) : t < x0 ∨ y1 < t := by
  rcases hr with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact Or.inl h1
  · exact Or.inr h1

theorem pkT_remS_side {ω x0 y1 : ℕ} {Θ τ : Finset ℕ} {s : ℕ} (hr : pkT_remS ω x0 y1 Θ τ s) : y1 < s ∨ s < x0 := by
  rcases hr with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact Or.inl h1
  · exact Or.inr h1

theorem pkT_remT_B {ω x0 y1 : ℕ} {Θ σ : Finset ℕ} {t : ℕ} (hr : pkT_remT ω x0 y1 Θ σ t) (ht : y1 < t)
    (hxy : x0 ≤ y1) : ∃ θ ∈ Θ, y1 < θ ∧ θ < t ∧ ∀ s ∈ σ, ¬ (θ ≤ s ∧ s ≤ ω) := by
  rcases hr with ⟨h1, -⟩ | ⟨-, -, θ, hθ, h1, h2, h3⟩
  · omega
  · exact ⟨θ, hθ, h1, h2, h3⟩

theorem pkT_remS_B {ω x0 y1 : ℕ} {Θ τ : Finset ℕ} {s : ℕ} (hr : pkT_remS ω x0 y1 Θ τ s) (hs : s < x0)
    (hxy : x0 ≤ y1) : ∃ θ ∈ Θ, s < θ ∧ θ < x0 ∧ ∀ t ∈ τ, ¬ t ≤ θ := by
  rcases hr with ⟨h1, -⟩ | ⟨-, -, θ, hθ, h1, h2, h3⟩
  · omega
  · exact ⟨θ, hθ, h1, h2, h3⟩

theorem pkT_remT_of_A {ω x0 y1 : ℕ} {Θ σ : Finset ℕ} {t : ℕ} (ht : t < x0) (hPX : ∀ s ∈ σ, ¬ s ≤ x0) :
    pkT_remT ω x0 y1 Θ σ t :=
  pkT_remT_iff.2 (Or.inl ⟨ht, fun s hs h' => hPX s hs h'.2, Or.inl hPX⟩)

theorem pkT_remT_of_B {ω x0 y1 : ℕ} {Θ σ : Finset ℕ} {t θ : ℕ} (ht : y1 < t) (hPX : ∀ s ∈ σ, ¬ s ≤ x0)
    (hθ : θ ∈ Θ) (h1 : y1 < θ) (h2 : θ < t) (hfree : ∀ s ∈ σ, ¬ (θ ≤ s ∧ s ≤ ω)) : pkT_remT ω x0 y1 Θ σ t :=
  pkT_remT_iff.2 (Or.inr ⟨ht, hPX, θ, hθ, h1, h2, hfree⟩)

theorem pkT_remS_of_A {ω x0 y1 : ℕ} {Θ τ : Finset ℕ} {s : ℕ} (hs : y1 < s) (hsω : s ≤ ω)
    (hPY : ∀ t ∈ τ, ¬ (y1 ≤ t ∧ t ≤ ω)) : pkT_remS ω x0 y1 Θ τ s :=
  pkT_remS_iff.2 (Or.inl ⟨hs, fun t ht h' => hPY t ht ⟨h'.1, le_trans h'.2 hsω⟩, Or.inl hPY⟩)

theorem pkT_remS_of_B {ω x0 y1 : ℕ} {Θ τ : Finset ℕ} {s θ : ℕ} (hs : s < x0) (hPY : ∀ t ∈ τ, ¬ (y1 ≤ t ∧ t ≤ ω))
    (hθ : θ ∈ Θ) (h1 : s < θ) (h2 : θ < x0) (hfree : ∀ t ∈ τ, ¬ t ≤ θ) : pkT_remS ω x0 y1 Θ τ s :=
  pkT_remS_iff.2 (Or.inr ⟨hs, hPY, θ, hθ, h1, h2, hfree⟩)

/-- Global form of a τ-removal (Lemma B (ii) under ¬EP): a removed τ-leg forces σ ∩ [1, x₀] = ∅. -/
theorem pkT_remT_PX {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} (H : pkT_ZH N ω x0 x1 y0 y1 Θ τ σ) {t : ℕ}
    (hr : pkT_remT ω x0 y1 Θ σ t) : ∀ s ∈ σ, ¬ s ≤ x0 := by
  obtain ⟨⟨hx0, hx01, hxy, hy01, hy1ω, hωN⟩, ⟨-, -, hx0Θ, -⟩, -, -, -, -, -⟩ := pkT_zf H
  rcases hr with ⟨htx, -, hP | ⟨θ, hθ, hθt, hfree⟩⟩ | ⟨-, hP, -⟩
  · exact hP
  · intro s hs hsx
    have hsθ : s < θ := by
      by_contra hc
      exact hfree s hs ⟨by omega, hsx⟩
    obtain ⟨k, hk, hk1, hk2⟩ := pkT_gap (pkT_ZH_nY H) hθ (hx0Θ (by omega)) (show θ < x0 - 1 by omega)
      (mem_union.2 (Or.inr hs)) hsθ (mem_union.2 (Or.inl (mem_Icc.2 ⟨le_refl y0, by omega⟩)))
      (show x0 - 1 < y0 by omega)
    rcases mem_union.1 hk with hk' | hk'
    · have := mem_Icc.1 hk'
      omega
    · exact hfree k hk' ⟨hk1, by omega⟩
  · exact hP

/-- Global form of a σ-removal (Lemma B (iii) under ¬EP): a removed σ-leg forces τ ∩ [y₁, ω] = ∅. -/
theorem pkT_remS_PY {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} (H : pkT_ZH N ω x0 x1 y0 y1 Θ τ σ) {s : ℕ}
    (hr : pkT_remS ω x0 y1 Θ τ s) : ∀ t ∈ τ, ¬ (y1 ≤ t ∧ t ≤ ω) := by
  obtain ⟨⟨hx0, hx01, hxy, hy01, hy1ω, hωN⟩, ⟨-, -, -, hy1Θ⟩, hΘf, -, -, -, -⟩ := pkT_zf H
  rcases hr with ⟨hsy, -, hP | ⟨θ, hθ, hsθ, hfree⟩⟩ | ⟨-, hP, -⟩
  · exact hP
  · intro t ht hty
    have hθω := (hΘf θ hθ).2.1
    have htθ : θ < t := by
      by_contra hc
      exact hfree t ht ⟨hty.1, by omega⟩
    obtain ⟨k, hk, hk1, hk2⟩ := pkT_gap (pkT_ZH_nX H) (hy1Θ (by omega)) hθ (show y1 + 1 < θ by omega)
      (mem_union.2 (Or.inl (mem_Icc.2 ⟨by omega, le_refl x1⟩))) (show x1 < y1 + 1 by omega)
      (mem_union.2 (Or.inr ht)) htθ
    rcases mem_union.1 hk with hk' | hk'
    · have := mem_Icc.1 hk'
      omega
    · exact hfree k hk' ⟨by omega, hk2⟩
  · exact hP

/-- Legs of `τ ∪ σ` in `[x₀, y₁]` are never removed. -/
theorem pkT_mid_G {ω x0 y1 : ℕ} {Θ τ σ : Finset ℕ} {g : ℕ} (hg : g ∈ τ ∨ g ∈ σ) (h1 : x0 ≤ g) (h2 : g ≤ y1) :
    g ∈ pkT_zoneSet ω x0 y1 Θ τ σ := by
  rcases hg with hg | hg
  · refine pkT_mem_zoneSet.2 (Or.inl ⟨hg, fun hr => ?_⟩)
    rcases pkT_remT_side hr with h | h <;> omega
  · refine pkT_mem_zoneSet.2 (Or.inr ⟨hg, fun hr => ?_⟩)
    rcases pkT_remS_side hr with h | h <;> omega

theorem pkT_notG_T {ω x0 y1 : ℕ} {Θ τ σ : Finset ℕ} {w : ℕ} (hw : w ∈ τ)
    (hG : w ∉ pkT_zoneSet ω x0 y1 Θ τ σ) : pkT_remT ω x0 y1 Θ σ w := by
  by_contra hc
  exact hG (pkT_mem_zoneSet.2 (Or.inl ⟨hw, hc⟩))

theorem pkT_notG_S {ω x0 y1 : ℕ} {Θ τ σ : Finset ℕ} {w : ℕ} (hw : w ∈ σ)
    (hG : w ∉ pkT_zoneSet ω x0 y1 Θ τ σ) : pkT_remS ω x0 y1 Θ τ w := by
  by_contra hc
  exact hG (pkT_mem_zoneSet.2 (Or.inr ⟨hw, hc⟩))

/-- A removed leg is not in both traces (Lemma R (d)). -/
theorem pkT_notBoth {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} (H : pkT_ZH N ω x0 x1 y0 y1 Θ τ σ) {w : ℕ}
    (hwτ : w ∈ τ) (hwσ : w ∈ σ) (hG : w ∉ pkT_zoneSet ω x0 y1 Θ τ σ) : False := by
  obtain ⟨-, -, -, hτf, -, -, -⟩ := pkT_zf H
  have hrT := pkT_notG_T hwτ hG
  have hPX := pkT_remT_PX H hrT
  have hPY := pkT_remS_PY H (pkT_notG_S hwσ hG)
  rcases pkT_remT_side hrT with h | h
  · exact hPX w hwσ (by omega)
  · exact hPY w hwτ ⟨by omega, (hτf w hwτ).2.1⟩

/-- **Convexity** of `G′` in `τ ∪ σ` (Lemma B, linear form). -/
theorem pkT_zone_conv {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} (H : pkT_ZH N ω x0 x1 y0 y1 Θ τ σ) {b : ℕ}
    (hb : b ∈ τ ∨ b ∈ σ) (hbG : b ∉ pkT_zoneSet ω x0 y1 Θ τ σ) :
    (∀ a ∈ pkT_zoneSet ω x0 y1 Θ τ σ, ¬ a < b) ∨ (∀ c ∈ pkT_zoneSet ω x0 y1 Θ τ σ, ¬ b < c) := by
  obtain ⟨⟨hx0, hx01, hxy, hy01, hy1ω, hωN⟩, -, hΘf, hτf, hσf, -, -⟩ := pkT_zf H
  by_cases hbτ : b ∈ τ
  · have hr := pkT_notG_T hbτ hbG
    have hPX := pkT_remT_PX H hr
    rcases pkT_remT_side hr with hbx | hby
    · left
      intro a ha hab
      rcases pkT_mem_zoneSet.1 ha with ⟨haτ, hna⟩ | ⟨haσ, -⟩
      · exact hna (pkT_remT_of_A (by omega) hPX)
      · exact hPX a haσ (by omega)
    · obtain ⟨θ, hθ, h1, h2, hfree⟩ := pkT_remT_B hr hby (by omega)
      right
      intro c hc hbc
      rcases pkT_mem_zoneSet.1 hc with ⟨hcτ, hnc⟩ | ⟨hcσ, -⟩
      · exact hnc (pkT_remT_of_B (by omega) hPX hθ h1 (by omega) hfree)
      · exact hfree c hcσ ⟨by omega, (hσf c hcσ).2.1⟩
  · have hbσ : b ∈ σ := hb.resolve_left hbτ
    have hr := pkT_notG_S hbσ hbG
    have hPY := pkT_remS_PY H hr
    rcases pkT_remS_side hr with hby | hbx
    · right
      intro c hc hbc
      rcases pkT_mem_zoneSet.1 hc with ⟨hcτ, -⟩ | ⟨hcσ, hnc⟩
      · exact hPY c hcτ ⟨by omega, (hτf c hcτ).2.1⟩
      · exact hnc (pkT_remS_of_A (by omega) (hσf c hcσ).2.1 hPY)
    · obtain ⟨θ, hθ, h1, h2, hfree⟩ := pkT_remS_B hr hbx (by omega)
      left
      intro a ha hab
      rcases pkT_mem_zoneSet.1 ha with ⟨haτ, -⟩ | ⟨haσ, hna⟩
      · exact hfree a haτ (by omega)
      · exact hna (pkT_remS_of_B (by omega) hPY hθ (by omega) h2 hfree)

/-- **LR*** (zone-set form): `|G′| ≥ 2`. -/
theorem pkT_zone_card' {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} (H : pkT_ZH N ω x0 x1 y0 y1 Θ τ σ) :
    2 ≤ (pkT_zoneSet ω x0 y1 Θ τ σ).card := by
  obtain ⟨⟨hx0, hx01, hxy, hy01, hy1ω, hωN⟩, ⟨hγ, hγ', hx0Θ, hy1Θ⟩, hΘf, hτf, hσf, ⟨tl, htl, htl1⟩,
    ⟨sl, hsl, hsl1⟩⟩ := pkT_zf H
  have he : ∃ e ∈ τ, x1 < e ∧ e ≤ y1 := by
    by_contra hc
    have htly : y1 < tl := by
      by_contra h'
      exact hc ⟨tl, htl, by omega, by omega⟩
    have htlω := (hτf tl htl).2.1
    have htlΘ := (hτf tl htl).2.2.1
    have hne : tl ≠ y1 + 1 := fun h' => htlΘ (by rw [h']; exact hy1Θ (by omega))
    obtain ⟨k, hk, hk1, hk2⟩ := pkT_gap (pkT_ZH_nX H) hγ (hy1Θ (by omega)) (show x1 + 1 < y1 + 1 by omega)
      (mem_union.2 (Or.inl (mem_Icc.2 ⟨by omega, le_refl x1⟩))) (show x1 < x1 + 1 by omega)
      (mem_union.2 (Or.inr htl)) (show y1 + 1 < tl by omega)
    rcases mem_union.1 hk with hk' | hk'
    · have := mem_Icc.1 hk'
      omega
    · have hkΘ := (hτf k hk').2.2.1
      have hk3 : k ≠ y1 + 1 := fun h' => hkΘ (by rw [h']; exact hy1Θ (by omega))
      exact hc ⟨k, hk', by omega, by omega⟩
  have hf : ∃ f ∈ σ, x0 ≤ f ∧ f < y0 := by
    by_contra hc
    have hslx : sl < x0 := by
      by_contra h'
      exact hc ⟨sl, hsl, by omega, by omega⟩
    have hslΘ := (hσf sl hsl).2.2.1
    have hsl0 := (hσf sl hsl).1
    have hne : sl ≠ x0 - 1 := fun h' => hslΘ (by rw [h']; exact hx0Θ (by omega))
    obtain ⟨k, hk, hk1, hk2⟩ := pkT_gap (pkT_ZH_nY H) (hx0Θ (by omega)) hγ' (show x0 - 1 < y0 - 1 by omega)
      (mem_union.2 (Or.inr hsl)) (show sl < x0 - 1 by omega)
      (mem_union.2 (Or.inl (mem_Icc.2 ⟨le_refl y0, by omega⟩))) (show y0 - 1 < y0 by omega)
    rcases mem_union.1 hk with hk' | hk'
    · have := mem_Icc.1 hk'
      omega
    · have hkΘ := (hσf k hk').2.2.1
      have hk3 : k ≠ x0 - 1 := fun h' => hkΘ (by rw [h']; exact hx0Θ (by omega))
      have hk4 : k ≠ y0 - 1 := fun h' => hkΘ (by rw [h']; exact hγ')
      exact hc ⟨k, hk', by omega, by omega⟩
  obtain ⟨e, he, he1, he2⟩ := he
  obtain ⟨f, hf, hf1, hf2⟩ := hf
  have heG : e ∈ pkT_zoneSet ω x0 y1 Θ τ σ := pkT_mid_G (Or.inl he) (by omega) he2
  have hfG : f ∈ pkT_zoneSet ω x0 y1 Θ τ σ := pkT_mid_G (Or.inr hf) hf1 (by omega)
  by_cases hslG : sl ∈ pkT_zoneSet ω x0 y1 Θ τ σ
  · exact pkT_two hslG heG (by omega)
  · have htlG : tl ∈ pkT_zoneSet ω x0 y1 Θ τ σ := by
      by_contra htlG
      have hPX := pkT_remT_PX H (pkT_notG_T htl htlG)
      by_cases hslx : x0 ≤ sl
      · exact hslG (pkT_mid_G (Or.inr hsl) hslx (by omega))
      · exact hPX sl hsl (by omega)
    exact pkT_two hfG htlG (by omega)

/-- A convex subset of `U` inside `[1, ω]` is `U ∩ [α, β]`. -/
theorem pkT_block_of_conv {N ω : ℕ} {U G : Finset ℕ} (hGU : ∀ g ∈ G, g ∈ U ∧ 1 ≤ g ∧ g ≤ ω) (hωN : ω ≤ N)
    (hne : G.Nonempty) (hconv : ∀ b ∈ U, b ∉ G → (∀ a ∈ G, ¬ a < b) ∨ (∀ c ∈ G, ¬ b < c)) :
    ∃ α β, 1 ≤ α ∧ α ≤ β ∧ β ≤ ω ∧ G = U ∩ cycArc N α (β + 1 - α) := by
  have hα := hGU _ (G.min'_mem hne)
  have hβ := hGU _ (G.max'_mem hne)
  have hαβ := G.min'_le _ (G.max'_mem hne)
  refine ⟨G.min' hne, G.max' hne, hα.2.1, hαβ, hβ.2.2, ?_⟩
  ext x
  rw [mem_inter, pkT_mem_cycArc_lin hα.2.1 (by omega)]
  constructor
  · intro hx
    have h1 := G.min'_le x hx
    have h2 := G.le_max' x hx
    exact ⟨(hGU x hx).1, h1, by omega⟩
  · rintro ⟨hxU, hx2, hx3⟩
    by_contra hxG
    rcases hconv x hxU hxG with hL | hR
    · by_cases heq : x = G.min' hne
      · rw [heq] at hxG
        exact hxG (G.min'_mem hne)
      · exact hL _ (G.min'_mem hne) (by omega)
    · by_cases heq : x = G.max' hne
      · rw [heq] at hxG
        exact hxG (G.max'_mem hne)
      · exact hR _ (G.max'_mem hne) (by omega)

/-- **Lemma B** (linear form). -/
theorem pkT_zone_block' {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} (H : pkT_ZH N ω x0 x1 y0 y1 Θ τ σ) :
    ∃ α β, 1 ≤ α ∧ α ≤ β ∧ β ≤ ω ∧ pkT_zoneSet ω x0 y1 Θ τ σ = odds (τ ∪ σ) ∩ cycArc N α (β + 1 - α) := by
  obtain ⟨⟨hx0, hx01, hxy, hy01, hy1ω, hωN⟩, -, -, hτf, hσf, -, -⟩ := pkT_zf H
  have hc := pkT_zone_card' H
  refine pkT_block_of_conv ?_ (by omega) (card_pos.1 (by omega)) ?_
  · intro g hg
    rcases pkT_mem_zoneSet.1 hg with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact ⟨pkT_mem_odds.2 ⟨mem_union.2 (Or.inl h1), (pkT_ZH_iff.1 H).2.1 g h1⟩, (hτf g h1).1, (hτf g h1).2.1⟩
    · exact ⟨pkT_mem_odds.2 ⟨mem_union.2 (Or.inr h1), (pkT_ZH_iff.1 H).2.2.1 g h1⟩, (hσf g h1).1, (hσf g h1).2.1⟩
  · intro b hb hbG
    exact pkT_zone_conv H (mem_union.1 (pkT_mem_odds.1 hb).1) hbG

/-! ### Zone lemma (linear proof): every pair separated by `G′` lies in `C₀`. -/

theorem pkT_inST_lt {T : Finset ℕ} {u v : ℕ} (huv : u < v) :
    InST T u v ↔ u ∉ T ∧ v ∉ T ∧ (∃ t ∈ T, u < t ∧ t < v) ∧ (∃ t ∈ T, t < u ∨ v < t) := by
  rw [pkT_inST_iff, min_eq_left huv.le, max_eq_right huv.le]

/-- An unseparated pair off `T` has a `T`-free arc. -/
theorem pkT_free {T : Finset ℕ} {u v : ℕ} (huv : u < v) (hK : ¬ InST T u v) (hu : u ∉ T) (hv : v ∉ T) :
    (∀ t ∈ T, ¬ (u < t ∧ t < v)) ∨ (∀ t ∈ T, ¬ (t < u ∨ v < t)) := by
  by_cases hI : ∃ t ∈ T, u < t ∧ t < v
  · right
    intro t ht hO
    exact hK ((pkT_inST_lt huv).2 ⟨hu, hv, hI, t, ht, hO⟩)
  · left
    intro t ht h'
    exact hI ⟨t, ht, h'⟩

theorem pkT_inF {T : Finset ℕ} {u v k : ℕ} (hF : ∀ t ∈ T, ¬ (u < t ∧ t < v)) (hk : k ∈ T) (hu : u ∉ T)
    (hv : v ∉ T) (h1 : u ≤ k) (h2 : k ≤ v) : False := by
  have h3 : k ≠ u := fun h' => hu (by rw [← h']; exact hk)
  have h4 : k ≠ v := fun h' => hv (by rw [← h']; exact hk)
  exact hF k hk ⟨by omega, by omega⟩

theorem pkT_outF {T : Finset ℕ} {u v k : ℕ} (hF : ∀ t ∈ T, ¬ (t < u ∨ v < t)) (hk : k ∈ T) (hu : u ∉ T)
    (hv : v ∉ T) (h : k ≤ u ∨ v ≤ k) : False := by
  have h3 : k ≠ u := fun h' => hu (by rw [← h']; exact hk)
  have h4 : k ≠ v := fun h' => hv (by rw [← h']; exact hk)
  exact hF k hk (by omega)

theorem pkT_D_notKX {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} (H : pkT_ZH N ω x0 x1 y0 y1 Θ τ σ) {d : ℕ}
    (hd : d ∈ Θ ∨ ω < d) : d ∉ Icc x0 x1 ∪ τ := by
  obtain ⟨⟨hx0, hx01, hxy, hy01, hy1ω, hωN⟩, -, hΘf, hτf, hσf, -, -⟩ := pkT_zf H
  intro hk
  rcases mem_union.1 hk with hk | hk
  · have := mem_Icc.1 hk
    rcases hd with hd | hd
    · rcases (hΘf d hd).2.2.1 with h' | h' <;> omega
    · omega
  · have := hτf d hk
    rcases hd with hd | hd
    · exact this.2.2.1 hd
    · omega

theorem pkT_D_notKY {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} (H : pkT_ZH N ω x0 x1 y0 y1 Θ τ σ) {d : ℕ}
    (hd : d ∈ Θ ∨ ω < d) : d ∉ Icc y0 y1 ∪ σ := by
  obtain ⟨⟨hx0, hx01, hxy, hy01, hy1ω, hωN⟩, -, hΘf, hτf, hσf, -, -⟩ := pkT_zf H
  intro hk
  rcases mem_union.1 hk with hk | hk
  · have := mem_Icc.1 hk
    rcases hd with hd | hd
    · rcases (hΘf d hd).2.2.2 with h' | h' <;> omega
    · omega
  · have := hσf d hk
    rcases hd with hd | hd
    · exact this.2.2.1 hd
    · omega

/-- The two `K`-free arcs cannot be opposite (Long), and cannot coincide (`G′ ⊆ τ ∪ σ`): an endpoint lies in
`X ∪ τ ∪ Y ∪ σ` (v3 (1a)). -/
theorem pkT_zs_step1 {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} (H : pkT_ZH N ω x0 x1 y0 y1 Θ τ σ) {u v : ℕ}
    (huv : u < v)
    (hIn : ∃ g ∈ pkT_zoneSet ω x0 y1 Θ τ σ, u < g ∧ g < v)
    (hOut : ∃ g ∈ pkT_zoneSet ω x0 y1 Θ τ σ, g < u ∨ v < g)
    (hKX : ¬ InST (Icc x0 x1 ∪ τ) u v) (hKY : ¬ InST (Icc y0 y1 ∪ σ) u v)
    (huX : u ∉ Icc x0 x1 ∪ τ) (huY : u ∉ Icc y0 y1 ∪ σ) (hvX : v ∉ Icc x0 x1 ∪ τ) (hvY : v ∉ Icc y0 y1 ∪ σ) :
    False := by
  obtain ⟨⟨hx0, hx01, hxy, hy01, hy1ω, hωN⟩, -, hΘf, hτf, hσf, ⟨tl, htl, htl1⟩, ⟨sl, hsl, hsl1⟩⟩ := pkT_zf H
  obtain ⟨g1, hg1, hg11, hg12⟩ := hIn
  obtain ⟨g2, hg2, hg2o⟩ := hOut
  rcases pkT_free huv hKX huX hvX with hFX | hFX <;> rcases pkT_free huv hKY huY hvY with hFY | hFY
  · rcases pkT_mem_zoneSet.1 hg1 with ⟨h, -⟩ | ⟨h, -⟩
    · exact hFX g1 (mem_union_right _ h) ⟨hg11, hg12⟩
    · exact hFY g1 (mem_union_right _ h) ⟨hg11, hg12⟩
  · -- In free of X ∪ τ, Out free of Y ∪ σ
    have h1 := hFY sl (mem_union_right _ hsl)
    have h2 := hFY y1 (mem_union_left _ (mem_Icc.2 ⟨by omega, le_refl _⟩))
    have h3 := hFX x1 (mem_union_left _ (mem_Icc.2 ⟨by omega, le_refl _⟩))
    have hux : u = x1 := by omega
    have hus : sl = u := by omega
    exact huY (by rw [← hus]; exact mem_union_right _ hsl)
  · -- Out free of X ∪ τ, In free of Y ∪ σ
    have h1 := hFX tl (mem_union_right _ htl)
    have h2 := hFX x0 (mem_union_left _ (mem_Icc.2 ⟨le_refl _, by omega⟩))
    have h3 := hFY y0 (mem_union_left _ (mem_Icc.2 ⟨le_refl _, by omega⟩))
    have hvt : tl = v := by omega
    exact hvX (by rw [← hvt]; exact mem_union_right _ htl)
  · rcases pkT_mem_zoneSet.1 hg2 with ⟨h, -⟩ | ⟨h, -⟩
    · exact hFX g2 (mem_union_right _ h) hg2o
    · exact hFY g2 (mem_union_right _ h) hg2o

/-- Both endpoints in one run of `A′ ∖ Θ` (R2-Z240 I.b). -/
theorem pkT_zs_run {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} (H : pkT_ZH N ω x0 x1 y0 y1 Θ τ σ) {u v : ℕ}
    (huv : u < v) (hu1 : 1 ≤ u) (hu : u ≤ ω ∧ u ∉ Θ) (hv : v ≤ ω ∧ v ∉ Θ) (hno : ∀ θ ∈ Θ, ¬ (u < θ ∧ θ < v))
    (hGu : u ∉ pkT_zoneSet ω x0 y1 Θ τ σ) (hGv : v ∉ pkT_zoneSet ω x0 y1 Θ τ σ)
    (hIn : ∃ g ∈ pkT_zoneSet ω x0 y1 Θ τ σ, u < g ∧ g < v)
    (hKX : ¬ InST (Icc x0 x1 ∪ τ) u v) (hKY : ¬ InST (Icc y0 y1 ∪ σ) u v) : False := by
  obtain ⟨⟨hx0, hx01, hxy, hy01, hy1ω, hωN⟩, ⟨hγ, hγ', hx0Θ, hy1Θ⟩, hΘf, hτf, hσf, ⟨tl, htl, htl1⟩,
    ⟨sl, hsl, hsl1⟩⟩ := pkT_zf H
  obtain ⟨g, hg, hg1, hg2⟩ := hIn
  -- no Θ-leg in [u, v]
  have hnoΘ : ∀ θ ∈ Θ, θ < u ∨ v < θ := by
    intro θ hθ
    have h1 : θ ≠ u := fun h' => hu.2 (by rw [← h']; exact hθ)
    have h2 : θ ≠ v := fun h' => hv.2 (by rw [← h']; exact hθ)
    have := hno θ hθ
    omega
  by_cases huX : x0 ≤ u ∧ u ≤ x1
  · have hvx : v ≤ x1 := by
      have := hnoΘ _ hγ
      omega
    apply hKY
    rw [pkT_inST_lt huv]
    have huσ : u ∉ σ := fun h' => hGu (pkT_mid_G (Or.inr h') huX.1 (by omega))
    have hvσ : v ∉ σ := fun h' => hGv (pkT_mid_G (Or.inr h') (by omega) (by omega))
    refine ⟨fun h' => ?_, fun h' => ?_, ⟨g, ?_, hg1, hg2⟩, ⟨y0, mem_union_left _ (mem_Icc.2 ⟨le_refl _, by omega⟩),
      Or.inr (by omega)⟩⟩
    · rcases mem_union.1 h' with h' | h'
      · have := mem_Icc.1 h'
        omega
      · exact huσ h'
    · rcases mem_union.1 h' with h' | h'
      · have := mem_Icc.1 h'
        omega
      · exact hvσ h'
    · rcases pkT_mem_zoneSet.1 hg with ⟨h', -⟩ | ⟨h', -⟩
      · have := hτf g h'
        omega
      · exact mem_union_right _ h'
  by_cases huY : y0 ≤ u ∧ u ≤ y1
  · have hvy : v ≤ y1 := by
      by_contra hc
      have := hnoΘ _ (hy1Θ (by omega))
      omega
    apply hKX
    rw [pkT_inST_lt huv]
    have huτ : u ∉ τ := fun h' => hGu (pkT_mid_G (Or.inl h') (by omega) huY.2)
    have hvτ : v ∉ τ := fun h' => hGv (pkT_mid_G (Or.inl h') (by omega) hvy)
    refine ⟨fun h' => ?_, fun h' => ?_, ⟨g, ?_, hg1, hg2⟩, ⟨x0, mem_union_left _ (mem_Icc.2 ⟨le_refl _, by omega⟩),
      Or.inl (by omega)⟩⟩
    · rcases mem_union.1 h' with h' | h'
      · have := mem_Icc.1 h'
        omega
      · exact huτ h'
    · rcases mem_union.1 h' with h' | h'
      · have := mem_Icc.1 h'
        omega
      · exact hvτ h'
    · rcases pkT_mem_zoneSet.1 hg with ⟨h', -⟩ | ⟨h', -⟩
      · exact mem_union_right _ h'
      · have := hσf g h'
        omega
  -- u off X ∪ Y: [u, v] lies in Λ, Γ or Ρ
  have hreg : v < x0 ∨ (x1 < u ∧ v < y0) ∨ y1 < u := by
    by_cases h1 : u < x0
    · left
      have := hnoΘ _ (hx0Θ (by omega))
      omega
    · by_cases h2 : u < y0
      · right; left
        have := hnoΘ _ hγ'
        omega
      · right; right
        omega
  rcases pkT_mem_zoneSet.1 hg with ⟨hgτ, hng⟩ | ⟨hgσ, hng⟩
  · apply hKX
    rw [pkT_inST_lt huv]
    have huτ : u ∉ τ := by
      intro huτ
      have hr := pkT_notG_T huτ hGu
      have hPX := pkT_remT_PX H hr
      rcases pkT_remT_side hr with h | h
      · exact hng (pkT_remT_of_A (by omega) hPX)
      · obtain ⟨θ, hθ, h1, h2, hfree⟩ := pkT_remT_B hr h (by omega)
        exact hng (pkT_remT_of_B (by omega) hPX hθ h1 (by omega) hfree)
    have hvτ : v ∉ τ := by
      intro hvτ
      have hr := pkT_notG_T hvτ hGv
      have hPX := pkT_remT_PX H hr
      rcases pkT_remT_side hr with h | h
      · exact hng (pkT_remT_of_A (by omega) hPX)
      · obtain ⟨θ, hθ, h1, h2, hfree⟩ := pkT_remT_B hr h (by omega)
        have := hnoΘ θ hθ
        exact hng (pkT_remT_of_B (by omega) hPX hθ h1 (by omega) hfree)
    refine ⟨fun h' => ?_, fun h' => ?_, ⟨g, mem_union_right _ hgτ, hg1, hg2⟩,
      ⟨x0, mem_union_left _ (mem_Icc.2 ⟨le_refl _, by omega⟩), by omega⟩⟩
    · rcases mem_union.1 h' with h' | h'
      · have := mem_Icc.1 h'
        omega
      · exact huτ h'
    · rcases mem_union.1 h' with h' | h'
      · have := mem_Icc.1 h'
        omega
      · exact hvτ h'
  · apply hKY
    rw [pkT_inST_lt huv]
    have huσ : u ∉ σ := by
      intro huσ
      have hr := pkT_notG_S huσ hGu
      have hPY := pkT_remS_PY H hr
      rcases pkT_remS_side hr with h | h
      · exact hng (pkT_remS_of_A (by omega) (hσf g hgσ).2.1 hPY)
      · obtain ⟨θ, hθ, h1, h2, hfree⟩ := pkT_remS_B hr h (by omega)
        have := hnoΘ θ hθ
        exact hng (pkT_remS_of_B (by omega) hPY hθ (by omega) h2 hfree)
    have hvσ : v ∉ σ := by
      intro hvσ
      have hr := pkT_notG_S hvσ hGv
      have hPY := pkT_remS_PY H hr
      rcases pkT_remS_side hr with h | h
      · exact hng (pkT_remS_of_A (by omega) (hσf g hgσ).2.1 hPY)
      · obtain ⟨θ, hθ, h1, h2, hfree⟩ := pkT_remS_B hr h (by omega)
        exact hng (pkT_remS_of_B (by omega) hPY hθ (by omega) h2 hfree)
    refine ⟨fun h' => ?_, fun h' => ?_, ⟨g, mem_union_right _ hgσ, hg1, hg2⟩,
      ⟨y0, mem_union_left _ (mem_Icc.2 ⟨le_refl _, by omega⟩), by omega⟩⟩
    · rcases mem_union.1 h' with h' | h'
      · have := mem_Icc.1 h'
        omega
      · exact huσ h'
    · rcases mem_union.1 h' with h' | h'
      · have := mem_Icc.1 h'
        omega
      · exact hvσ h'

/-- The Γ-gap of `Y ∪ σ` from `x₁` (¬EP): a Θ-leg `q ∈ (x₁ + 1, y₀)` has a σ-leg in `(x₁ + 1, q)`. -/
theorem pkT_WgY {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} (H : pkT_ZH N ω x0 x1 y0 y1 Θ τ σ) {q : ℕ}
    (hq : q ∈ Θ) (h1 : x1 + 1 < q) (h2 : q < y0) : ∃ k ∈ σ, x1 + 1 < k ∧ k < q := by
  obtain ⟨⟨hx0, hx01, hxy, hy01, hy1ω, hωN⟩, ⟨hγ, hγ', hx0Θ, hy1Θ⟩, hΘf, hτf, hσf, -, ⟨sl, hsl, hsl1⟩⟩ :=
    pkT_zf H
  obtain ⟨k, hk, hk1, hk2⟩ := pkT_gap (pkT_ZH_nY H) hγ hq h1 (mem_union_right _ hsl) (show sl < x1 + 1 by omega)
    (mem_union_left _ (mem_Icc.2 ⟨le_refl y0, by omega⟩)) h2
  rcases mem_union.1 hk with hk' | hk'
  · have := mem_Icc.1 hk'
    omega
  · have hkΘ := (hσf k hk').2.2.1
    have h3 : k ≠ x1 + 1 := fun h' => hkΘ (by rw [h']; exact hγ)
    have h4 : k ≠ q := fun h' => hkΘ (by rw [h']; exact hq)
    exact ⟨k, hk', by omega, by omega⟩

/-- The Γ-gap of `X ∪ τ` towards `y₀` (¬EP): a Θ-leg `p ∈ (x₁, y₀ − 1)` has a τ-leg in `(p, y₀ − 1)`. -/
theorem pkT_WgX {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} (H : pkT_ZH N ω x0 x1 y0 y1 Θ τ σ) {p : ℕ}
    (hp : p ∈ Θ) (h1 : x1 < p) (h2 : p < y0 - 1) : ∃ k ∈ τ, p < k ∧ k < y0 - 1 := by
  obtain ⟨⟨hx0, hx01, hxy, hy01, hy1ω, hωN⟩, ⟨hγ, hγ', hx0Θ, hy1Θ⟩, hΘf, hτf, hσf, ⟨tl, htl, htl1⟩, -⟩ :=
    pkT_zf H
  obtain ⟨k, hk, hk1, hk2⟩ := pkT_gap (pkT_ZH_nX H) hp hγ' h2 (mem_union_left _ (mem_Icc.2 ⟨by omega, le_refl x1⟩))
    h1 (mem_union_right _ htl) (show y0 - 1 < tl by omega)
  rcases mem_union.1 hk with hk' | hk'
  · have := mem_Icc.1 hk'
    omega
  · have hkΘ := (hτf k hk').2.2.1
    have h3 : k ≠ p := fun h' => hkΘ (by rw [h']; exact hp)
    have h4 : k ≠ y0 - 1 := fun h' => hkΘ (by rw [h']; exact hγ')
    exact ⟨k, hk', by omega, by omega⟩

/-- The Λ-gap of `Y ∪ σ` (¬EP): a Θ-leg `p < x₀ − 1` with a σ-leg below has a σ-leg in `(p, x₀ − 1)`. -/
theorem pkT_WlY {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} (H : pkT_ZH N ω x0 x1 y0 y1 Θ τ σ) {p s : ℕ}
    (hp : p ∈ Θ) (h1 : p + 1 < x0) (hs : s ∈ σ) (hsp : s < p) : ∃ k ∈ σ, p < k ∧ k < x0 - 1 := by
  obtain ⟨⟨hx0, hx01, hxy, hy01, hy1ω, hωN⟩, ⟨hγ, hγ', hx0Θ, hy1Θ⟩, hΘf, hτf, hσf, -, -⟩ := pkT_zf H
  obtain ⟨k, hk, hk1, hk2⟩ := pkT_gap (pkT_ZH_nY H) hp (hx0Θ (by omega)) (show p < x0 - 1 by omega)
    (mem_union_right _ hs) hsp (mem_union_left _ (mem_Icc.2 ⟨le_refl y0, by omega⟩)) (show x0 - 1 < y0 by omega)
  rcases mem_union.1 hk with hk' | hk'
  · have := mem_Icc.1 hk'
    omega
  · have hkΘ := (hσf k hk').2.2.1
    have h3 : k ≠ p := fun h' => hkΘ (by rw [h']; exact hp)
    have h4 : k ≠ x0 - 1 := fun h' => hkΘ (by rw [h']; exact hx0Θ (by omega))
    exact ⟨k, hk', by omega, by omega⟩

/-- The Ρ-gap of `X ∪ τ` (¬EP): a Θ-leg `q > y₁ + 1` with a τ-leg above has a τ-leg in `(y₁ + 1, q)`. -/
theorem pkT_WrX {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} (H : pkT_ZH N ω x0 x1 y0 y1 Θ τ σ) {q t : ℕ}
    (hq : q ∈ Θ) (h1 : y1 + 1 < q) (ht : t ∈ τ) (htq : q < t) : ∃ k ∈ τ, y1 + 1 < k ∧ k < q := by
  obtain ⟨⟨hx0, hx01, hxy, hy01, hy1ω, hωN⟩, ⟨hγ, hγ', hx0Θ, hy1Θ⟩, hΘf, hτf, hσf, -, -⟩ := pkT_zf H
  have hqω := (hΘf q hq).2.1
  obtain ⟨k, hk, hk1, hk2⟩ := pkT_gap (pkT_ZH_nX H) (hy1Θ (by omega)) hq h1
    (mem_union_left _ (mem_Icc.2 ⟨by omega, le_refl x1⟩)) (show x1 < y1 + 1 by omega) (mem_union_right _ ht) htq
  rcases mem_union.1 hk with hk' | hk'
  · have := mem_Icc.1 hk'
    omega
  · have hkΘ := (hτf k hk').2.2.1
    have h3 : k ≠ y1 + 1 := fun h' => hkΘ (by rw [h']; exact hy1Θ (by omega))
    have h4 : k ≠ q := fun h' => hkΘ (by rw [h']; exact hq)
    exact ⟨k, hk', by omega, by omega⟩

/-- Up case: `u ∈ X ∪ τ ∪ Y ∪ σ`, `v ∈ Θ ∪ W` (R2-Z240 III with the run leg first). -/
theorem pkT_zs_up {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} (H : pkT_ZH N ω x0 x1 y0 y1 Θ τ σ) {u v : ℕ}
    (huv : u < v) (hd : v ∈ Θ ∨ ω < v) (huK : u ∈ Icc x0 x1 ∪ τ ∨ u ∈ Icc y0 y1 ∪ σ)
    (hGu : u ∉ pkT_zoneSet ω x0 y1 Θ τ σ)
    (hIn : ∃ g ∈ pkT_zoneSet ω x0 y1 Θ τ σ, u < g ∧ g < v)
    (hOut : ∃ g ∈ pkT_zoneSet ω x0 y1 Θ τ σ, g < u ∨ v < g)
    (hKX : ¬ InST (Icc x0 x1 ∪ τ) u v) (hKY : ¬ InST (Icc y0 y1 ∪ σ) u v) : False := by
  obtain ⟨⟨hx0, hx01, hxy, hy01, hy1ω, hωN⟩, ⟨hγ, hγ', hx0Θ, hy1Θ⟩, hΘf, hτf, hσf, ⟨tl, htl, htl1⟩,
    ⟨sl, hsl, hsl1⟩⟩ := pkT_zf H
  have hvX := pkT_D_notKX H hd
  have hvY := pkT_D_notKY H hd
  obtain ⟨g1, hg1, hg11, hg12⟩ := hIn
  obtain ⟨g2, hg2, hg2o⟩ := hOut
  have hy0Y : y0 ∈ Icc y0 y1 ∪ σ := mem_union_left _ (mem_Icc.2 ⟨le_refl _, by omega⟩)
  have hy1Y : y1 ∈ Icc y0 y1 ∪ σ := mem_union_left _ (mem_Icc.2 ⟨by omega, le_refl _⟩)
  have hx0X : x0 ∈ Icc x0 x1 ∪ τ := mem_union_left _ (mem_Icc.2 ⟨le_refl _, by omega⟩)
  -- the Γ-argument (In free of Y ∪ σ, a τ-leg of G′ in (x₁, v), u ≤ x₁)
  have hΓ : ∀ (hF : ∀ t ∈ Icc y0 y1 ∪ σ, ¬ (u < t ∧ t < v)), u ∉ Icc y0 y1 ∪ σ → u ≤ x1 → g1 ∈ τ → x1 < g1 →
      False := by
    intro hF huY hux hg1τ hg1x
    have hvy : v < y0 := by
      by_contra hc
      exact pkT_inF hF hy0Y huY hvY (by omega) (by omega)
    have hvΘ : v ∈ Θ := hd.resolve_right (by omega)
    have hne : g1 ≠ x1 + 1 := fun h' => (hτf g1 hg1τ).2.2.1 (by rw [h']; exact hγ)
    obtain ⟨k, hk, hk1, hk2⟩ := pkT_WgY H hvΘ (show x1 + 1 < v by omega) hvy
    exact pkT_inF hF (mem_union_right _ hk) huY hvY (by omega) (by omega)
  -- the Out argument (Out free of Y ∪ σ, σ ∩ [1, x₀] = ∅)
  have hO : ∀ (hF : ∀ t ∈ Icc y0 y1 ∪ σ, ¬ (t < u ∨ v < t)), u ∉ Icc y0 y1 ∪ σ → u ≤ x1 →
      (∀ s ∈ σ, ¬ s ≤ x0) → False := by
    intro hF huY hux hPX
    have hvy : y1 < v := by
      by_contra hc
      exact pkT_outF hF hy1Y huY hvY (by omega)
    rcases pkT_mem_zoneSet.1 hg2 with ⟨hg2τ, hng⟩ | ⟨hg2σ, -⟩
    · rcases hg2o with h | h
      · rcases (hτf g2 hg2τ).2.2.2 with h' | h'
        · exact hng (pkT_remT_of_A h' hPX)
        · omega
      · have hvΘ : v ∈ Θ := hd.resolve_right (by have := (hτf g2 hg2τ).2.1; omega)
        refine hng (pkT_remT_of_B (by omega) hPX hvΘ (by omega) h (fun s hs hs' => ?_))
        have hne : s ≠ v := fun h' => (hσf s hs).2.2.1 (by rw [h']; exact hvΘ)
        exact hF s (mem_union_right _ hs) (Or.inr (by omega))
    · exact hF g2 (mem_union_right _ hg2σ) hg2o
  rcases huK with huK | huK
  · rcases mem_union.1 huK with huX | huτ
    · -- u ∈ X
      have huX' := mem_Icc.1 huX
      have huσ : u ∉ σ := fun h' => hGu (pkT_mid_G (Or.inr h') huX'.1 (by omega))
      have huY : u ∉ Icc y0 y1 ∪ σ := by
        intro h'
        rcases mem_union.1 h' with h' | h'
        · have := mem_Icc.1 h'
          omega
        · exact huσ h'
      rcases pkT_free huv hKY huY hvY with hF | hF
      · rcases pkT_mem_zoneSet.1 hg1 with ⟨hg1τ, -⟩ | ⟨hg1σ, -⟩
        · refine hΓ hF huY huX'.2 hg1τ ?_
          rcases (hτf g1 hg1τ).2.2.2 with h' | h' <;> omega
        · exact hF g1 (mem_union_right _ hg1σ) ⟨hg11, hg12⟩
      · refine hO hF huY huX'.2 (fun s hs hsx => ?_)
        have hne : s ≠ u := fun h' => huσ (by rw [← h']; exact hs)
        exact hF s (mem_union_right _ hs) (Or.inl (by omega))
    · -- u ∈ τ ∖ G′
      have hr := pkT_notG_T huτ hGu
      have hPX := pkT_remT_PX H hr
      have huσ : u ∉ σ := fun h' => pkT_notBoth H huτ h' hGu
      have huY : u ∉ Icc y0 y1 ∪ σ := by
        intro h'
        rcases mem_union.1 h' with h' | h'
        · have := mem_Icc.1 h'
          rcases pkT_remT_side hr with h'' | h'' <;> omega
        · exact huσ h'
      rcases pkT_remT_side hr with hux | huy
      · rcases pkT_free huv hKY huY hvY with hF | hF
        · rcases pkT_mem_zoneSet.1 hg1 with ⟨hg1τ, hng⟩ | ⟨hg1σ, -⟩
          · rcases (hτf g1 hg1τ).2.2.2 with h' | h'
            · exact hng (pkT_remT_of_A h' hPX)
            · exact hΓ hF huY (by omega) hg1τ h'
          · exact hF g1 (mem_union_right _ hg1σ) ⟨hg11, hg12⟩
        · exact hO hF huY (by omega) hPX
      · obtain ⟨θ, hθ, h1, h2, hfree⟩ := pkT_remT_B hr huy (by omega)
        rcases pkT_free huv hKY huY hvY with hF | hF
        · rcases pkT_mem_zoneSet.1 hg1 with ⟨hg1τ, hng⟩ | ⟨hg1σ, -⟩
          · exact hng (pkT_remT_of_B (by omega) hPX hθ h1 (by omega) hfree)
          · exact hF g1 (mem_union_right _ hg1σ) ⟨hg11, hg12⟩
        · exact pkT_outF hF hy0Y huY hvY (Or.inl (by omega))
  · rcases mem_union.1 huK with huY' | huσ
    · -- u ∈ Y
      have huY := mem_Icc.1 huY'
      have huτ : u ∉ τ := fun h' => hGu (pkT_mid_G (Or.inl h') (by omega) huY.2)
      have huX : u ∉ Icc x0 x1 ∪ τ := by
        intro h'
        rcases mem_union.1 h' with h' | h'
        · have := mem_Icc.1 h'
          omega
        · exact huτ h'
      rcases pkT_free huv hKX huX hvX with hF | hF
      · rcases pkT_mem_zoneSet.1 hg1 with ⟨hg1τ, -⟩ | ⟨hg1σ, hng⟩
        · exact hF g1 (mem_union_right _ hg1τ) ⟨hg11, hg12⟩
        · have hg1y : y1 < g1 := by
            rcases (hσf g1 hg1σ).2.2.2 with h' | h' <;> omega
          obtain ⟨t, ht, hty⟩ : ∃ t ∈ τ, y1 ≤ t ∧ t ≤ ω := by
            by_contra hc
            exact hng (pkT_remS_of_A hg1y (hσf g1 hg1σ).2.1 (fun t ht h' => hc ⟨t, ht, h'⟩))
          have htv : v < t := by
            by_contra hc
            exact pkT_inF hF (mem_union_right _ ht) huX hvX (by omega) (by omega)
          have hvΘ : v ∈ Θ := hd.resolve_right (by omega)
          have hne : g1 ≠ y1 + 1 := fun h' => (hσf g1 hg1σ).2.2.1 (by rw [h']; exact hy1Θ (by omega))
          obtain ⟨k, hk, hk1, hk2⟩ := pkT_WrX H hvΘ (show y1 + 1 < v by omega) ht htv
          exact pkT_inF hF (mem_union_right _ hk) huX hvX (by omega) (by omega)
      · exact pkT_outF hF hx0X huX hvX (Or.inl (by omega))
    · -- u ∈ σ ∖ G′
      have hr := pkT_notG_S huσ hGu
      have hPY := pkT_remS_PY H hr
      have huτ : u ∉ τ := fun h' => pkT_notBoth H h' huσ hGu
      have huX : u ∉ Icc x0 x1 ∪ τ := by
        intro h'
        rcases mem_union.1 h' with h' | h'
        · have := mem_Icc.1 h'
          exact hGu (pkT_mid_G (Or.inr huσ) this.1 (by omega))
        · exact huτ h'
      rcases pkT_remS_side hr with huy | hux
      · rcases pkT_free huv hKX huX hvX with hF | hF
        · rcases pkT_mem_zoneSet.1 hg1 with ⟨hg1τ, -⟩ | ⟨hg1σ, hng⟩
          · exact hF g1 (mem_union_right _ hg1τ) ⟨hg11, hg12⟩
          · exact hng (pkT_remS_of_A (by omega) (hσf g1 hg1σ).2.1 hPY)
        · exact pkT_outF hF hx0X huX hvX (Or.inl (by omega))
      · obtain ⟨θ, hθ, h1, h2, hfree⟩ := pkT_remS_B hr hux (by omega)
        rcases pkT_free huv hKX huX hvX with hF | hF
        · have hvx : v < x0 := by
            by_contra hc
            exact pkT_inF hF hx0X huX hvX (by omega) (by omega)
          have hvΘ : v ∈ Θ := hd.resolve_right (by omega)
          rcases pkT_mem_zoneSet.1 hg1 with ⟨hg1τ, -⟩ | ⟨hg1σ, hng⟩
          · exact hF g1 (mem_union_right _ hg1τ) ⟨hg11, hg12⟩
          · refine hng (pkT_remS_of_B (by omega) hPY hvΘ hg12 hvx (fun t ht htv => ?_))
            by_cases htθ : t ≤ θ
            · exact hfree t ht htθ
            · exact pkT_inF hF (mem_union_right _ ht) huX hvX (by omega) htv
        · have htlv : tl ≤ v := by
            by_contra hc
            exact pkT_outF hF (mem_union_right _ htl) huX hvX (Or.inr (by omega))
          have hvy : y1 < v := by
            rcases hd with hd | hd
            · rcases (hΘf v hd).2.2.2 with h' | h' <;> omega
            · omega
          rcases pkT_mem_zoneSet.1 hg2 with ⟨hg2τ, -⟩ | ⟨hg2σ, hng⟩
          · exact hF g2 (mem_union_right _ hg2τ) hg2o
          · rcases hg2o with h' | h'
            · exact hng (pkT_remS_of_B (by omega) hPY hθ (by omega) h2 hfree)
            · exact hng (pkT_remS_of_A (by omega) (hσf g2 hg2σ).2.1 hPY)

/-- Down case: `u ∈ Θ`, `v ∈ X ∪ τ ∪ Y ∪ σ`. -/
theorem pkT_zs_down {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} (H : pkT_ZH N ω x0 x1 y0 y1 Θ τ σ) {u v : ℕ}
    (huv : u < v) (huΘ : u ∈ Θ) (hvK : v ∈ Icc x0 x1 ∪ τ ∨ v ∈ Icc y0 y1 ∪ σ)
    (hGv : v ∉ pkT_zoneSet ω x0 y1 Θ τ σ)
    (hIn : ∃ g ∈ pkT_zoneSet ω x0 y1 Θ τ σ, u < g ∧ g < v)
    (hOut : ∃ g ∈ pkT_zoneSet ω x0 y1 Θ τ σ, g < u ∨ v < g)
    (hKX : ¬ InST (Icc x0 x1 ∪ τ) u v) (hKY : ¬ InST (Icc y0 y1 ∪ σ) u v) : False := by
  obtain ⟨⟨hx0, hx01, hxy, hy01, hy1ω, hωN⟩, ⟨hγ, hγ', hx0Θ, hy1Θ⟩, hΘf, hτf, hσf, ⟨tl, htl, htl1⟩,
    ⟨sl, hsl, hsl1⟩⟩ := pkT_zf H
  have huX := pkT_D_notKX H (Or.inl huΘ)
  have huY := pkT_D_notKY H (Or.inl huΘ)
  have huf := hΘf u huΘ
  obtain ⟨g1, hg1, hg11, hg12⟩ := hIn
  obtain ⟨g2, hg2, hg2o⟩ := hOut
  have hy0Y : y0 ∈ Icc y0 y1 ∪ σ := mem_union_left _ (mem_Icc.2 ⟨le_refl _, by omega⟩)
  have hx0X : x0 ∈ Icc x0 x1 ∪ τ := mem_union_left _ (mem_Icc.2 ⟨le_refl _, by omega⟩)
  rcases hvK with hvK | hvK
  · rcases mem_union.1 hvK with hvX' | hvτ
    · -- v ∈ X
      have hvX := mem_Icc.1 hvX'
      have hvσ : v ∉ σ := fun h' => hGv (pkT_mid_G (Or.inr h') hvX.1 (by omega))
      have hvY : v ∉ Icc y0 y1 ∪ σ := by
        intro h'
        rcases mem_union.1 h' with h' | h'
        · have := mem_Icc.1 h'
          omega
        · exact hvσ h'
      rcases pkT_free huv hKY huY hvY with hF | hF
      · rcases pkT_mem_zoneSet.1 hg1 with ⟨hg1τ, hng⟩ | ⟨hg1σ, -⟩
        · have hg1x : g1 < x0 := by
            rcases (hτf g1 hg1τ).2.2.2 with h' | h' <;> omega
          obtain ⟨s, hs, hsx⟩ : ∃ s ∈ σ, s ≤ x0 := by
            by_contra hc
            exact hng (pkT_remT_of_A hg1x (fun s hs h' => hc ⟨s, hs, h'⟩))
          have hsu : s < u := by
            by_contra hc
            have hne : s ≠ u := fun h' => (hσf s hs).2.2.1 (by rw [h']; exact huΘ)
            exact pkT_inF hF (mem_union_right _ hs) huY hvY (by omega) (by omega)
          have hne : g1 ≠ x0 - 1 := fun h' => (hτf g1 hg1τ).2.2.1 (by rw [h']; exact hx0Θ (by omega))
          obtain ⟨k, hk, hk1, hk2⟩ := pkT_WlY H huΘ (show u + 1 < x0 by omega) hs hsu
          exact pkT_inF hF (mem_union_right _ hk) huY hvY (by omega) (by omega)
        · exact hF g1 (mem_union_right _ hg1σ) ⟨hg11, hg12⟩
      · exact pkT_outF hF hy0Y huY hvY (Or.inr (by omega))
    · -- v ∈ τ ∖ G′
      have hr := pkT_notG_T hvτ hGv
      have hPX := pkT_remT_PX H hr
      have hvσ : v ∉ σ := fun h' => pkT_notBoth H hvτ h' hGv
      have hvY : v ∉ Icc y0 y1 ∪ σ := by
        intro h'
        rcases mem_union.1 h' with h' | h'
        · have := mem_Icc.1 h'
          rcases pkT_remT_side hr with h'' | h'' <;> omega
        · exact hvσ h'
      rcases pkT_remT_side hr with hvx | hvy
      · rcases pkT_free huv hKY huY hvY with hF | hF
        · rcases pkT_mem_zoneSet.1 hg1 with ⟨hg1τ, hng⟩ | ⟨hg1σ, -⟩
          · exact hng (pkT_remT_of_A (by omega) hPX)
          · exact hF g1 (mem_union_right _ hg1σ) ⟨hg11, hg12⟩
        · exact pkT_outF hF hy0Y huY hvY (Or.inr (by omega))
      · obtain ⟨θ, hθ, h1, h2, hfree⟩ := pkT_remT_B hr hvy (by omega)
        by_cases huy : y1 < u
        · rcases pkT_free huv hKY huY hvY with hF | hF
          · rcases pkT_mem_zoneSet.1 hg1 with ⟨hg1τ, hng⟩ | ⟨hg1σ, -⟩
            · refine hng (pkT_remT_of_B (by omega) hPX huΘ huy hg11 (fun s hs hs' => ?_))
              have hne : s ≠ u := fun h' => (hσf s hs).2.2.1 (by rw [h']; exact huΘ)
              by_cases hsv : s ≤ v
              · exact pkT_inF hF (mem_union_right _ hs) huY hvY (by omega) hsv
              · exact hfree s hs ⟨by omega, hs'.2⟩
            · exact hF g1 (mem_union_right _ hg1σ) ⟨hg11, hg12⟩
          · exact pkT_outF hF hy0Y huY hvY (Or.inl (by omega))
        · have huy0 : u < y0 := by
            rcases huf.2.2.2 with h' | h' <;> omega
          rcases pkT_free huv hKY huY hvY with hF | hF
          · exact pkT_inF hF hy0Y huY hvY (by omega) (by omega)
          · rcases pkT_mem_zoneSet.1 hg2 with ⟨hg2τ, hng⟩ | ⟨hg2σ, -⟩
            · rcases hg2o with h' | h'
              · rcases (hτf g2 hg2τ).2.2.2 with h'' | h''
                · exact hng (pkT_remT_of_A h'' hPX)
                · exact pkT_outF hF (mem_union_right _ hsl) huY hvY (Or.inl (by omega))
              · exact hng (pkT_remT_of_B (by omega) hPX hθ h1 (by omega) hfree)
            · exact hF g2 (mem_union_right _ hg2σ) hg2o
  · rcases mem_union.1 hvK with hvY' | hvσ
    · -- v ∈ Y
      have hvY := mem_Icc.1 hvY'
      have hvτ : v ∉ τ := fun h' => hGv (pkT_mid_G (Or.inl h') (by omega) hvY.2)
      have hvX : v ∉ Icc x0 x1 ∪ τ := by
        intro h'
        rcases mem_union.1 h' with h' | h'
        · have := mem_Icc.1 h'
          omega
        · exact hvτ h'
      rcases huf.2.2.1 with hux | hux
      · rcases pkT_free huv hKX huX hvX with hF | hF
        · exact pkT_inF hF hx0X huX hvX (by omega) (by omega)
        · have hPY : ∀ t ∈ τ, ¬ (y1 ≤ t ∧ t ≤ ω) := by
            intro t ht hty
            exact pkT_outF hF (mem_union_right _ ht) huX hvX (Or.inr (by omega))
          rcases pkT_mem_zoneSet.1 hg2 with ⟨hg2τ, -⟩ | ⟨hg2σ, hng⟩
          · exact hF g2 (mem_union_right _ hg2τ) hg2o
          · rcases hg2o with h' | h'
            · refine hng (pkT_remS_of_B (by omega) hPY huΘ h' hux (fun t ht htu => ?_))
              exact pkT_outF hF (mem_union_right _ ht) huX hvX (Or.inl htu)
            · have hg2y : y1 < g2 := by
                rcases (hσf g2 hg2σ).2.2.2 with h'' | h'' <;> omega
              exact hng (pkT_remS_of_A hg2y (hσf g2 hg2σ).2.1 hPY)
      · rcases pkT_free huv hKX huX hvX with hF | hF
        · rcases pkT_mem_zoneSet.1 hg1 with ⟨hg1τ, -⟩ | ⟨hg1σ, -⟩
          · exact hF g1 (mem_union_right _ hg1τ) ⟨hg11, hg12⟩
          · have hg1y : g1 < y0 := by
              rcases (hσf g1 hg1σ).2.2.2 with h' | h' <;> omega
            have hne : g1 ≠ y0 - 1 := fun h' => (hσf g1 hg1σ).2.2.1 (by rw [h']; exact hγ')
            obtain ⟨k, hk, hk1, hk2⟩ := pkT_WgX H huΘ hux (show u < y0 - 1 by omega)
            exact pkT_inF hF (mem_union_right _ hk) huX hvX (by omega) (by omega)
        · exact pkT_outF hF hx0X huX hvX (Or.inl (by omega))
    · -- v ∈ σ ∖ G′
      have hr := pkT_notG_S hvσ hGv
      have hPY := pkT_remS_PY H hr
      have hvτ : v ∉ τ := fun h' => pkT_notBoth H h' hvσ hGv
      have hvX : v ∉ Icc x0 x1 ∪ τ := by
        intro h'
        rcases mem_union.1 h' with h' | h'
        · have := mem_Icc.1 h'
          exact hGv (pkT_mid_G (Or.inr hvσ) this.1 (by omega))
        · exact hvτ h'
      rcases pkT_remS_side hr with hvy | hvx
      · rcases huf.2.2.1 with hux | hux
        · rcases pkT_free huv hKX huX hvX with hF | hF
          · exact pkT_inF hF hx0X huX hvX (by omega) (by omega)
          · rcases pkT_mem_zoneSet.1 hg2 with ⟨hg2τ, -⟩ | ⟨hg2σ, hng⟩
            · exact hF g2 (mem_union_right _ hg2τ) hg2o
            · rcases hg2o with h' | h'
              · refine hng (pkT_remS_of_B (by omega) hPY huΘ h' hux (fun t ht htu => ?_))
                exact pkT_outF hF (mem_union_right _ ht) huX hvX (Or.inl htu)
              · exact hng (pkT_remS_of_A (by omega) (hσf g2 hg2σ).2.1 hPY)
        · rcases pkT_free huv hKX huX hvX with hF | hF
          · by_cases huy : y1 < u
            · rcases pkT_mem_zoneSet.1 hg1 with ⟨hg1τ, -⟩ | ⟨hg1σ, hng⟩
              · exact hF g1 (mem_union_right _ hg1τ) ⟨hg11, hg12⟩
              · exact hng (pkT_remS_of_A (by omega) (hσf g1 hg1σ).2.1 hPY)
            · have huy0 : u < y0 := by
                rcases huf.2.2.2 with h' | h' <;> omega
              have htv : tl ≤ v := by
                by_contra hc
                exact hPY tl htl ⟨by omega, (hτf tl htl).2.1⟩
              exact pkT_inF hF (mem_union_right _ htl) huX hvX (by omega) htv
          · exact pkT_outF hF hx0X huX hvX (Or.inl (by omega))
      · obtain ⟨θ, hθ, h1, h2, hfree⟩ := pkT_remS_B hr hvx (by omega)
        rcases pkT_free huv hKX huX hvX with hF | hF
        · rcases pkT_mem_zoneSet.1 hg1 with ⟨hg1τ, -⟩ | ⟨hg1σ, hng⟩
          · exact hF g1 (mem_union_right _ hg1τ) ⟨hg11, hg12⟩
          · exact hng (pkT_remS_of_B (by omega) hPY hθ (by omega) h2 hfree)
        · exact pkT_outF hF hx0X huX hvX (Or.inr (by omega))

/-- **Zone lemma** (linear proof): `S_{G′} ⊆ C₀`. -/
theorem pkT_zone_sep' {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} (H : pkT_ZH N ω x0 x1 y0 y1 Θ τ σ) :
    sepPairs N (pkT_zoneSet ω x0 y1 Θ τ σ) ⊆ threeSepCut N ω x0 x1 y0 y1 Θ τ σ := by
  obtain ⟨-, -, -, hτf, hσf, -, -⟩ := pkT_zf H
  have hKA : ∀ w, (w ∈ Icc x0 x1 ∪ τ ∨ w ∈ Icc y0 y1 ∪ σ) → w ≤ ω ∧ w ∉ Θ := by
    intro w hw
    obtain ⟨-, -, -, -, -, -, hX, hY, -⟩ := (pkT_ZH_iff.1 H).1
    obtain ⟨-, -, hx1ω, -, -, hXΘ⟩ := hX
    obtain ⟨-, -, hy1ω, -, -, hYΘ⟩ := hY
    rcases hw with hw | hw
    · rcases mem_union.1 hw with hw | hw
      · exact ⟨by have := mem_Icc.1 hw; omega, hXΘ w hw⟩
      · exact ⟨(hτf w hw).2.1, (hτf w hw).2.2.1⟩
    · rcases mem_union.1 hw with hw | hw
      · exact ⟨by have := mem_Icc.1 hw; omega, hYΘ w hw⟩
      · exact ⟨(hσf w hw).2.1, (hσf w hw).2.2.1⟩
  intro p hp
  obtain ⟨hd, hpG⟩ := pkT_mem_sepPairs.1 hp
  have hd' := mem_diagonals.1 hd
  refine pkT_mem_threeSepCut.2 ⟨hd, ?_⟩
  by_cases hA : runSepA ω Θ p.1 p.2
  · exact Or.inl hA
  by_cases hX : InST (Icc x0 x1 ∪ τ) p.1 p.2
  · exact Or.inr (Or.inl hX)
  by_cases hY : InST (Icc y0 y1 ∪ σ) p.1 p.2
  · exact Or.inr (Or.inr hY)
  exfalso
  have huv : p.1 < p.2 := by omega
  have hu1 : 1 ≤ p.1 := hd'.1
  rw [pkT_inST_lt huv] at hpG
  obtain ⟨hGu, hGv, hIn, hOut⟩ := hpG
  have hK : (p.1 ∈ Icc x0 x1 ∪ τ ∨ p.1 ∈ Icc y0 y1 ∪ σ) ∨ (p.2 ∈ Icc x0 x1 ∪ τ ∨ p.2 ∈ Icc y0 y1 ∪ σ) := by
    by_contra hc
    exact pkT_zs_step1 H huv hIn hOut hX hY (fun h' => hc (Or.inl (Or.inl h'))) (fun h' => hc (Or.inl (Or.inr h')))
      (fun h' => hc (Or.inr (Or.inl h'))) (fun h' => hc (Or.inr (Or.inr h')))
  by_cases hu : p.1 ≤ ω ∧ p.1 ∉ Θ
  · by_cases hv : p.2 ≤ ω ∧ p.2 ∉ Θ
    · have hno : ∀ θ ∈ Θ, ¬ (p.1 < θ ∧ θ < p.2) := by
        intro θ hθ h'
        apply hA
        rw [pkT_runSepA_iff, min_eq_left huv.le, max_eq_right huv.le]
        exact ⟨mem_Icc.2 ⟨hu1, hu.1⟩, mem_Icc.2 ⟨by omega, hv.1⟩, hu.2, hv.2, θ, hθ, h'⟩
      exact pkT_zs_run H huv hu1 hu hv hno hGu hGv hIn hX hY
    · have hvD : p.2 ∈ Θ ∨ ω < p.2 := by
        by_cases h' : p.2 ∈ Θ
        · exact Or.inl h'
        · right
          by_contra h''
          exact hv ⟨by omega, h'⟩
      have hvK : ¬ (p.2 ∈ Icc x0 x1 ∪ τ ∨ p.2 ∈ Icc y0 y1 ∪ σ) := fun h' => hv (hKA _ h')
      exact pkT_zs_up H huv hvD (hK.resolve_right hvK) hGu hIn hOut hX hY
  · have huK : ¬ (p.1 ∈ Icc x0 x1 ∪ τ ∨ p.1 ∈ Icc y0 y1 ∪ σ) := fun h' => hu (hKA _ h')
    have hvK := hK.resolve_left huK
    have hvω := (hKA _ hvK).1
    have huΘ : p.1 ∈ Θ := by
      by_contra h'
      exact hu ⟨by omega, h'⟩
    exact pkT_zs_down H huv huΘ hvK hGv hIn hOut hX hY

/-- **LR*** (BP App. E §5) in zone-set form: `|G′| ≥ 2`. -/
theorem pkT_zone_card {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} (h : ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ)
    (hτo : ∀ t ∈ τ, t % 2 = 1) (hσo : ∀ t ∈ σ, t % 2 = 1)
    (hnX : ∀ a ∈ Icc x0 x1 ∪ τ, ∀ b ∈ Icc x0 x1 ∪ τ, a < b → (∀ k ∈ Icc x0 x1 ∪ τ, ¬ (a < k ∧ k < b)) →
      (Θ.filter (fun x => a < x ∧ x < b)).card ≤ 1)
    (hnY : ∀ a ∈ Icc y0 y1 ∪ σ, ∀ b ∈ Icc y0 y1 ∪ σ, a < b → (∀ k ∈ Icc y0 y1 ∪ σ, ¬ (a < k ∧ k < b)) →
      (Θ.filter (fun x => a < x ∧ x < b)).card ≤ 1) :
    2 ≤ (pkT_zoneSet ω x0 y1 Θ τ σ).card :=
  pkT_zone_card' (pkT_ZH_iff.2 ⟨h, hτo, hσo, hnX, hnY⟩)

/-- **Lemma B** (BP App. E §6), linear form: `G′ = U_o ∩ [α, β]` with `1 ≤ α ≤ β ≤ ω`. -/
theorem pkT_zone_block {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} (h : ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ)
    (hτo : ∀ t ∈ τ, t % 2 = 1) (hσo : ∀ t ∈ σ, t % 2 = 1)
    (hnX : ∀ a ∈ Icc x0 x1 ∪ τ, ∀ b ∈ Icc x0 x1 ∪ τ, a < b → (∀ k ∈ Icc x0 x1 ∪ τ, ¬ (a < k ∧ k < b)) →
      (Θ.filter (fun x => a < x ∧ x < b)).card ≤ 1)
    (hnY : ∀ a ∈ Icc y0 y1 ∪ σ, ∀ b ∈ Icc y0 y1 ∪ σ, a < b → (∀ k ∈ Icc y0 y1 ∪ σ, ¬ (a < k ∧ k < b)) →
      (Θ.filter (fun x => a < x ∧ x < b)).card ≤ 1) :
    ∃ α β, 1 ≤ α ∧ α ≤ β ∧ β ≤ ω ∧ pkT_zoneSet ω x0 y1 Θ τ σ = odds (τ ∪ σ) ∩ cycArc N α (β + 1 - α) :=
  pkT_zone_block' (pkT_ZH_iff.2 ⟨h, hτo, hσo, hnX, hnY⟩)

/-- **Zone lemma** (BP App. E §7 / §7a, R2-Z240 route): `S_{G′} ⊆ C₀`. -/
theorem pkT_zone_sep {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} (h : ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ)
    (hτo : ∀ t ∈ τ, t % 2 = 1) (hσo : ∀ t ∈ σ, t % 2 = 1)
    (hnX : ∀ a ∈ Icc x0 x1 ∪ τ, ∀ b ∈ Icc x0 x1 ∪ τ, a < b → (∀ k ∈ Icc x0 x1 ∪ τ, ¬ (a < k ∧ k < b)) →
      (Θ.filter (fun x => a < x ∧ x < b)).card ≤ 1)
    (hnY : ∀ a ∈ Icc y0 y1 ∪ σ, ∀ b ∈ Icc y0 y1 ∪ σ, a < b → (∀ k ∈ Icc y0 y1 ∪ σ, ¬ (a < k ∧ k < b)) →
      (Θ.filter (fun x => a < x ∧ x < b)).card ≤ 1) :
    sepPairs N (pkT_zoneSet ω x0 y1 Θ τ σ) ⊆ threeSepCut N ω x0 x1 y0 y1 Θ τ σ :=
  pkT_zone_sep' (pkT_ZH_iff.2 ⟨h, hτo, hσo, hnX, hnY⟩)

theorem pkT_zoneCase {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} (h : ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ)
    (hτo : ∀ t ∈ τ, t % 2 = 1) (hσo : ∀ t ∈ σ, t % 2 = 1)
    (hnX : ∀ a ∈ Icc x0 x1 ∪ τ, ∀ b ∈ Icc x0 x1 ∪ τ, a < b → (∀ k ∈ Icc x0 x1 ∪ τ, ¬ (a < k ∧ k < b)) →
      (Θ.filter (fun x => a < x ∧ x < b)).card ≤ 1)
    (hnY : ∀ a ∈ Icc y0 y1 ∪ σ, ∀ b ∈ Icc y0 y1 ∪ σ, a < b → (∀ k ∈ Icc y0 y1 ∪ σ, ¬ (a < k ∧ k < b)) →
      (Θ.filter (fun x => a < x ∧ x < b)).card ≤ 1) :
    ∃ G, ConsecWit N Θ τ σ G ∧ sepPairs N G ⊆ threeSepCut N ω x0 x1 y0 y1 Θ τ σ := by
  have hωN : ω + 3 ≤ N := by
    obtain ⟨-, -, h3, -⟩ := h
    exact h3
  obtain ⟨α, β, hα, hαβ, hβ, hG⟩ := pkT_zone_block h hτo hσo hnX hnY
  refine ⟨pkT_zoneSet ω x0 y1 Θ τ σ, pkT_consecWit_iff.2 ⟨pkT_zone_card h hτo hσo hnX hnY, α,
    mem_Icc.2 ⟨hα, by omega⟩, β + 1 - α, mem_range.2 (by omega), Or.inr ?_⟩, pkT_zone_sep h hτo hσo hnX hnY⟩
  rw [hG]

/-- `sorry` (pkgTri) · **(Tri), single-witness-family form** [v3 §14.3 Remark (ii); R2-Z235]: some `G ∈ F_U` has
`S_G ⊆ C₀`. (Mirror: every configuration of this encoding at N = 10 (25) and N = 12 (349) has an F_U witness, §6.) -/
theorem threeSep_consecWit {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} (h : ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ) :
    ∃ G, ConsecWit N Θ τ σ G ∧ sepPairs N G ⊆ threeSepCut N ω x0 x1 y0 y1 Θ τ σ := by
  have hτA : AdmSepCompl N x0 x1 τ := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h12, -⟩ := h
    exact h12
  have hσA : AdmSepCompl N y0 y1 σ := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h13, -⟩ := h
    exact h13
  by_cases hA : ∃ t, τ = {t} ∧ t % 2 = 0
  · obtain ⟨t, ht, hte⟩ := hA
    exact pkT_caseA h ht hte
  have hτo : ∀ t ∈ τ, t % 2 = 1 := pkT_odd_of_adm hτA hA
  by_cases hB : ∃ g, σ = {g} ∧ g % 2 = 0
  · obtain ⟨g, hg, hge⟩ := hB
    rcases pkT_sigma_even_pos h hg hge with hpos | hpos
    · exact pkT_caseB_lin h hτo hg hge hpos.1 hpos.2
    · rw [hpos] at hg
      exact pkT_caseB_wrap h hτo hg
  have hσo : ∀ t ∈ σ, t % 2 = 1 := pkT_odd_of_adm hσA hB
  by_cases hEX : ∃ a ∈ Icc x0 x1 ∪ τ, ∃ b ∈ Icc x0 x1 ∪ τ, a < b ∧ (∀ k ∈ Icc x0 x1 ∪ τ, ¬ (a < k ∧ k < b)) ∧
      2 ≤ (Θ.filter (fun x => a < x ∧ x < b)).card
  · obtain ⟨a, ha, b, hb, hab, hgap, h2⟩ := hEX
    exact pkT_caseEP h hτo hσo (Or.inl rfl) ha hb hab hgap h2
  by_cases hEY : ∃ a ∈ Icc y0 y1 ∪ σ, ∃ b ∈ Icc y0 y1 ∪ σ, a < b ∧ (∀ k ∈ Icc y0 y1 ∪ σ, ¬ (a < k ∧ k < b)) ∧
      2 ≤ (Θ.filter (fun x => a < x ∧ x < b)).card
  · obtain ⟨a, ha, b, hb, hab, hgap, h2⟩ := hEY
    exact pkT_caseEP h hτo hσo (Or.inr rfl) ha hb hab hgap h2
  -- Zone case (both traces odd, no gap of X ∪ τ or Y ∪ σ with two Θ-legs): the odd witness G′ of BP App. E §5–§7
  -- (LR*, Lemma B, zone lemma), proved linearly in `pkT_zone_card'`, `pkT_zone_block'`, `pkT_zone_sep'`.
  have hnX : ∀ a ∈ Icc x0 x1 ∪ τ, ∀ b ∈ Icc x0 x1 ∪ τ, a < b → (∀ k ∈ Icc x0 x1 ∪ τ, ¬ (a < k ∧ k < b)) →
      (Θ.filter (fun x => a < x ∧ x < b)).card ≤ 1 := fun a ha b hb hab hgap => by
    by_contra hc
    exact hEX ⟨a, ha, b, hb, hab, hgap, by omega⟩
  have hnY : ∀ a ∈ Icc y0 y1 ∪ σ, ∀ b ∈ Icc y0 y1 ∪ σ, a < b → (∀ k ∈ Icc y0 y1 ∪ σ, ¬ (a < k ∧ k < b)) →
      (Θ.filter (fun x => a < x ∧ x < b)).card ≤ 1 := fun a ha b hb hab hgap => by
    by_contra hc
    exact hEY ⟨a, ha, b, hb, hab, hgap, by omega⟩
  exact pkT_zoneCase h hτo hσo hnX hnY

/-- ASSEMBLED · **(Tri)** [v3 §14.3]: some `G ∈ 𝒯` (≥ 2 legs of `1..N`, one parity) has `S_G ⊆ C₀`. From `threeSep_consecWit`. -/
theorem threeSep {N ω x0 x1 y0 y1 : ℕ} {Θ τ σ : Finset ℕ} (h : ThreeSepSetting N ω x0 x1 y0 y1 Θ τ σ) :
    ∃ G, IsSameParitySet N G ∧ sepPairs N G ⊆ threeSepCut N ω x0 x1 y0 y1 Θ τ σ := by
  obtain ⟨G, ⟨hc, a, -, len, -, hG⟩, hsub⟩ := threeSep_consecWit h
  refine ⟨G, ?_, hsub⟩
  have hN0 : 0 < N := by obtain ⟨-, -, h3, -⟩ := h; omega
  have hArc : ∀ x ∈ cycArc N a len, x ∈ Icc 1 N := by
    intro x hx
    obtain ⟨k, -, rfl⟩ := mem_image.1 hx
    rw [mem_Icc, vtx]
    exact ⟨Nat.succ_le_succ (Nat.zero_le _), Nat.succ_le_of_lt (Nat.mod_lt _ hN0)⟩
  rcases hG with hG | hG
  · left
    refine ⟨fun x hx => ?_, hc, fun x hx => ?_⟩
    · rw [hG] at hx; exact hArc x (mem_inter.1 hx).2
    · rw [hG] at hx; exact (mem_filter.1 (mem_inter.1 hx).1).2
  · right
    refine ⟨fun x hx => ?_, hc, fun x hx => ?_⟩
    · rw [hG] at hx; exact hArc x (mem_inter.1 hx).2
    · rw [hG] at hx; exact (mem_filter.1 (mem_inter.1 hx).1).2

/-! ## 7. M1 interface statements (combinatorial core; frozen, `sorry` = package targets) [BP §3.A, §4, §5]

Only the statements another package or the M2 assembly consumes are frozen here; the chain's internal lemmas ([b0],
[L0], [St1], [Lem5′], [Side], (Odd-below), [Thin], [NoB1], [Lift], [Sub], [ORun], zone lemmas, …) are package helpers
(prefixed) and are listed in the package READMEs. Hypotheses follow v3's statements (F^π where v3 has it) even where
BP G-4 says a weaker one suffices: a package may prove a stronger helper, the frozen interface stays the reviewed one.
Truth at small N: `../mirror_b.py` (N = 6 all 242 F^π sets, N = 8 all 797 maximal + 40 000 random of 806 448,
N = 10 3 000 random): 0 failures of every statement of this section (thread §6 E2). -/

theorem pkCo_mem_oddDiagonals {N : ℕ} {P : ℕ × ℕ} :
    P ∈ oddDiagonals N ↔
      1 ≤ P.1 ∧ P.2 ≤ N ∧ P.1 + 2 ≤ P.2 ∧ ¬ (P.1 = 1 ∧ P.2 = N) ∧ (P.2 - P.1) % 2 = 1 := by
  show P ∈ (diagonals N).filter (fun d => (d.2 - d.1) % 2 = 1) ↔ _
  rw [mem_filter, mem_diagonals]
  exact ⟨fun ⟨⟨a, b, c, d⟩, e⟩ => ⟨a, b, c, d, e⟩, fun ⟨a, b, c, d, e⟩ => ⟨⟨a, b, c, d⟩, e⟩⟩

theorem pkCo_mem_cycArc {N a len x : ℕ} : x ∈ cycArc N a len ↔ ∃ k, k < len ∧ vtx N (a + k) = x := by
  show x ∈ (range len).image (fun k => vtx N (a + k)) ↔ _
  rw [mem_image]
  simp only [mem_range]

/-- An arc that does not wrap is an interval. -/
theorem pkCo_mem_cycArc_lin {N a len x : ℕ} (ha : 1 ≤ a) (hl : a + len ≤ N + 1) :
    x ∈ cycArc N a len ↔ a ≤ x ∧ x < a + len := by
  rw [pkCo_mem_cycArc]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [vtx_of_mem (by omega) (by omega)]
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨x - a, by omega, by rw [vtx_of_mem (by omega) (by omega)]; omega⟩

/-- The arc from `j` of length `N − (j − i)` is the complement of `[i, j)`. -/
theorem pkCo_mem_cycArc_wrap {N i j x : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ N) :
    x ∈ cycArc N j (N - (j - i)) ↔ (1 ≤ x ∧ x ≤ N) ∧ ¬ (i ≤ x ∧ x < j) := by
  rw [pkCo_mem_cycArc]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rcases le_or_gt (j + k) N with h | h
    · rw [vtx_of_mem (by omega) h]; omega
    · rw [vtx_of_gt h (by omega)]; omega
  · rintro ⟨⟨h1, h2⟩, h3⟩
    rcases le_or_gt j x with h | h
    · exact ⟨x - j, by omega, by rw [vtx_of_mem (by omega) (by omega)]; omega⟩
    · refine ⟨x + N - j, by omega, ?_⟩
      rw [vtx_of_gt (by omega) (by omega)]; omega

theorem pkCo_vtx_eq {N s k : ℕ} (hs1 : 1 ≤ s) (hsN : s ≤ N) (hk : k ≤ N) :
    vtx N (s + k) = if s + k ≤ N then s + k else s + k - N := by
  split_ifs with h
  · exact vtx_of_mem (by omega) h
  · exact vtx_of_gt (by omega) (by omega)

theorem pkCo_cycPos_eq {N s x : ℕ} (hs1 : 1 ≤ s) (hsN : s ≤ N) (hx1 : 1 ≤ x) (hxN : x ≤ N) :
    cycPos N s x = if s ≤ x then x - s else x + N - s := by
  show (x + N - s) % N = _
  split_ifs with h
  · rw [show x + N - s = (x - s) + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

theorem pkCo_vtx_vtx_add {N : ℕ} (hN : 1 ≤ N) (m j : ℕ) : vtx N (vtx N m + j) = vtx N (m + j) := by
  show ((m + N - 1) % N + 1 + j + N - 1) % N + 1 = (m + j + N - 1) % N + 1
  rw [show (m + N - 1) % N + 1 + j + N - 1 = (m + N - 1) % N + (j + N) by omega, Nat.mod_add_mod,
    show m + N - 1 + (j + N) = (m + j + N - 1) + N by omega, Nat.add_mod_right]

/-- Membership in an arc through the position. -/
theorem pkCo_mem_cycArc_pos {N s len x : ℕ} (hs : s ∈ Icc 1 N) (hl : len ≤ N) :
    x ∈ cycArc N s len ↔ x ∈ Icc 1 N ∧ cycPos N s x < len := by
  rw [mem_Icc] at hs ⊢
  rw [pkCo_mem_cycArc]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [pkCo_vtx_eq hs.1 hs.2 (by omega)]
    split_ifs with h
    · rw [pkCo_cycPos_eq hs.1 hs.2 (by omega) h]; split_ifs <;> omega
    · rw [pkCo_cycPos_eq hs.1 hs.2 (by omega) (by omega)]; split_ifs <;> omega
  · rintro ⟨⟨h1, h2⟩, h3⟩
    rw [pkCo_cycPos_eq hs.1 hs.2 h1 h2] at h3
    refine ⟨cycPos N s x, ?_, ?_⟩ <;> rw [pkCo_cycPos_eq hs.1 hs.2 h1 h2]
    · split_ifs at h3 ⊢ <;> omega
    · split_ifs with h
      · rw [pkCo_vtx_eq hs.1 hs.2 (by omega)]; split_ifs <;> omega
      · rw [pkCo_vtx_eq hs.1 hs.2 (by omega)]; split_ifs <;> omega

theorem pkCo_cycArc_sub {N s len : ℕ} (hN : 1 ≤ N) : cycArc N s len ⊆ Icc 1 N := by
  intro x hx
  obtain ⟨k, -, rfl⟩ := pkCo_mem_cycArc.1 hx
  exact mem_Icc.2 (vtx_bounds N _ hN)

theorem pkCo_cycPos_vtx {N s k : ℕ} (hs : s ∈ Icc 1 N) (hk : k < N) : cycPos N s (vtx N (s + k)) = k := by
  rw [mem_Icc] at hs
  rw [pkCo_vtx_eq hs.1 hs.2 hk.le]
  split_ifs with h
  · rw [pkCo_cycPos_eq hs.1 hs.2 (by omega) h]; split_ifs <;> omega
  · rw [pkCo_cycPos_eq hs.1 hs.2 (by omega) (by omega)]; split_ifs <;> omega

theorem pkCo_card_cycArc {N s len : ℕ} (hs : s ∈ Icc 1 N) (hl : len ≤ N) : (cycArc N s len).card = len := by
  show ((range len).image (fun k => vtx N (s + k))).card = len
  rw [card_image_of_injOn, card_range]
  intro k hk k' hk' h
  have hk1 : k < len := mem_range.1 hk
  have hk2 : k' < len := mem_range.1 hk'
  have e1 := pkCo_cycPos_vtx hs (show k < N by omega)
  have e2 := pkCo_cycPos_vtx hs (show k' < N by omega)
  simp only at h
  rw [h] at e1
  omega

/-- The complement of an arc is the arc that follows it. -/
theorem pkCo_cycArc_compl {N s len : ℕ} (hs : s ∈ Icc 1 N) (hl : len ≤ N) :
    Icc 1 N \ cycArc N s len = cycArc N (vtx N (s + len)) (N - len) := by
  have hN : 1 ≤ N := by have := mem_Icc.1 hs; omega
  have hv := vtx_bounds N (s + len) hN
  ext x
  rw [mem_sdiff, pkCo_mem_cycArc_pos hs hl, pkCo_mem_cycArc_pos (mem_Icc.2 hv) (by omega)]
  rw [mem_Icc] at hs
  by_cases hx : x ∈ Icc 1 N
  · have hx' := mem_Icc.1 hx
    simp only [hx, true_and]
    rw [pkCo_cycPos_eq hs.1 hs.2 hx'.1 hx'.2, pkCo_cycPos_eq hv.1 hv.2 hx'.1 hx'.2, pkCo_vtx_eq hs.1 hs.2 hl]
    split_ifs <;> omega
  · simp only [hx, false_and, and_false]

/-- Sub-arcs. -/
theorem pkCo_cycArc_subarc {N s i m len : ℕ} (hN : 1 ≤ N) (him : i + m ≤ len) :
    cycArc N (vtx N (s + i)) m ⊆ cycArc N s len := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := pkCo_mem_cycArc.1 hx
  rw [pkCo_vtx_vtx_add hN, Nat.add_assoc]
  exact pkCo_mem_cycArc.2 ⟨i + k, by omega, rfl⟩

/-- Rotation transports arcs. -/
theorem pkCo_image_rotLeg_cycArc {N : ℕ} (hN : 1 ≤ N) (r s len : ℕ) :
    (cycArc N s len).image (rotLeg N r) = cycArc N (rotLeg N r s) len := by
  ext x
  rw [mem_image, pkCo_mem_cycArc]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨k, hk, rfl⟩ := pkCo_mem_cycArc.1 hy
    refine ⟨k, hk, ?_⟩
    show vtx N (vtx N (s + r) + k) = vtx N (vtx N (s + k) + r)
    rw [pkCo_vtx_vtx_add hN, pkCo_vtx_vtx_add hN, Nat.add_right_comm]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨vtx N (s + k), pkCo_mem_cycArc.2 ⟨k, hk, rfl⟩, ?_⟩
    show vtx N (vtx N (s + k) + r) = vtx N (vtx N (s + r) + k)
    rw [pkCo_vtx_vtx_add hN, pkCo_vtx_vtx_add hN, Nat.add_right_comm]

/-- Rotation preserves positions. -/
theorem pkCo_cycPos_rotLeg {N r s x : ℕ} (hN : 1 ≤ N) (hs : s ∈ Icc 1 N) (hx : x ∈ Icc 1 N) :
    cycPos N (rotLeg N r s) (rotLeg N r x) = cycPos N s x := by
  have hs' := pkCo_rotLeg_mem (r := r) hN hs
  have hx' := pkCo_rotLeg_mem (r := r) hN hx
  rw [mem_Icc] at hs hx hs' hx'
  have hc := Nat.mod_lt r (by omega : 0 < N)
  rw [pkCo_cycPos_eq hs'.1 hs'.2 hx'.1 hx'.2, pkCo_cycPos_eq hs.1 hs.2 hx.1 hx.2]
  rw [pkCo_rotLeg_eq hN hs.1 hs.2, pkCo_rotLeg_eq hN hx.1 hx.2]
  split_ifs <;> omega

/-- Positions are `< N`. -/
theorem pkCo_cycPos_lt {N : ℕ} (hN : 1 ≤ N) (s x : ℕ) : cycPos N s x < N := Nat.mod_lt _ (by omega)

/-- The leg at the position of `x` is `x`. -/
theorem pkCo_vtx_cycPos {N s x : ℕ} (hs : s ∈ Icc 1 N) (hx : x ∈ Icc 1 N) : vtx N (s + cycPos N s x) = x := by
  rw [mem_Icc] at hs hx
  rw [pkCo_cycPos_eq hs.1 hs.2 hx.1 hx.2]
  split_ifs with h
  · rw [pkCo_vtx_eq hs.1 hs.2 (by omega)]; split_ifs <;> omega
  · rw [pkCo_vtx_eq hs.1 hs.2 (by omega)]; split_ifs <;> omega

/-- Positions are injective on legs. -/
theorem pkCo_cycPos_inj {N s x y : ℕ} (hs : s ∈ Icc 1 N) (hx : x ∈ Icc 1 N) (hy : y ∈ Icc 1 N)
    (h : cycPos N s x = cycPos N s y) : x = y := by
  rw [← pkCo_vtx_cycPos hs hx, ← pkCo_vtx_cycPos hs hy, h]

/-- The start of an arc has position `0`. -/
theorem pkCo_cycPos_self {N s : ℕ} (hs : s ∈ Icc 1 N) : cycPos N s s = 0 := by
  rw [mem_Icc] at hs
  rw [pkCo_cycPos_eq hs.1 hs.2 hs.1 hs.2]
  split_ifs <;> omega

/-- Positions from a later start: `pos_{s+i} x = pos_s x − i` when `i ≤ pos_s x`. -/
theorem pkCo_cycPos_vtx_add {N s i x : ℕ} (hs : s ∈ Icc 1 N) (hx : x ∈ Icc 1 N) (hi : i ≤ cycPos N s x) :
    cycPos N (vtx N (s + i)) x = cycPos N s x - i := by
  have hN : 1 ≤ N := by have := mem_Icc.1 hs; omega
  have hlt := pkCo_cycPos_lt hN s x
  have hv := vtx_bounds N (s + i) hN
  rw [mem_Icc] at hs hx
  rw [pkCo_cycPos_eq hv.1 hv.2 hx.1 hx.2]
  rw [pkCo_cycPos_eq hs.1 hs.2 hx.1 hx.2] at hi hlt ⊢
  rw [pkCo_vtx_eq hs.1 hs.2 (by omega)]
  split_ifs at hi hlt ⊢ <;> omega

/-- For even `N`, `vtx` preserves parity. -/
theorem pkCo_vtx_mod_two {N : ℕ} (hN : 1 ≤ N) (hE : N % 2 = 0) (m : ℕ) : vtx N m % 2 = m % 2 := by
  have h := Nat.mod_mod_of_dvd (m + N - 1) (Nat.dvd_of_mod_eq_zero hE)
  show ((m + N - 1) % N + 1) % 2 = m % 2
  omega

/-- For even `N`, the parity of a position is the parity of `x + s`. -/
theorem pkCo_cycPos_mod_two {N s x : ℕ} (hE : N % 2 = 0) (hs : s ∈ Icc 1 N) (hx : x ∈ Icc 1 N) :
    cycPos N s x % 2 = (x + s) % 2 := by
  rw [mem_Icc] at hs hx
  rw [pkCo_cycPos_eq hs.1 hs.2 hx.1 hx.2]
  split_ifs <;> omega

/-- Membership in `int L` through positions. -/
theorem pkCo_mem_intArc {N s k x : ℕ} (hs : s ∈ Icc 1 N) (hk : k ≤ N) :
    x ∈ intArc N s k ↔ x ∈ Icc 1 N ∧ 1 ≤ cycPos N s x ∧ cycPos N s x + 2 ≤ k := by
  show x ∈ (cycArc N s k).filter (fun x => 1 ≤ cycPos N s x ∧ cycPos N s x + 2 ≤ k) ↔ _
  rw [mem_filter, pkCo_mem_cycArc_pos hs hk]
  constructor
  · rintro ⟨⟨h1, -⟩, h2, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, by omega⟩, h2, h3⟩

/-- `int L` is the arc from the second leg with `k − 2` legs. -/
theorem pkCo_intArc_eq {N s k : ℕ} (hs : s ∈ Icc 1 N) (hk : 2 ≤ k) (hkN : k ≤ N) :
    intArc N s k = cycArc N (vtx N (s + 1)) (k - 2) := by
  have hN : 1 ≤ N := by have := mem_Icc.1 hs; omega
  have hv := mem_Icc.2 (vtx_bounds N (s + 1) hN)
  ext x
  rw [pkCo_mem_intArc hs hkN, pkCo_mem_cycArc_pos hv (by omega)]
  constructor
  · rintro ⟨hx, h1, h2⟩
    rw [pkCo_cycPos_vtx_add hs hx h1]
    exact ⟨hx, by omega⟩
  · rintro ⟨hx, h⟩
    by_cases h0 : 1 ≤ cycPos N s x
    · rw [pkCo_cycPos_vtx_add hs hx h0] at h
      exact ⟨hx, h0, by omega⟩
    · have e : cycPos N s x = 0 := by omega
      have hxs : x = s := by
        have := pkCo_cycPos_self hs
        exact pkCo_cycPos_inj hs hx hs (by omega)
      rw [hxs] at h
      have hlt := pkCo_cycPos_lt hN (vtx N (s + 1)) s
      have hs' := mem_Icc.1 hs
      have hv' := mem_Icc.1 hv
      rw [pkCo_cycPos_eq hv'.1 hv'.2 hs'.1 hs'.2, pkCo_vtx_eq hs'.1 hs'.2 (by omega)] at h
      split_ifs at h <;> omega

/-- Membership in the admissible separators. -/
theorem pkCo_mem_admSeps {N s k q : ℕ} {Θ : Finset ℕ} :
    Θ ∈ admSeps N s k q ↔ Θ ⊆ intArc N s k ∧ (Θ.card = 1 ∨ (2 ≤ Θ.card ∧ ∀ θ ∈ Θ, θ % 2 = q)) := by
  show Θ ∈ (intArc N s k).powerset.filter (fun Θ => Θ.card = 1 ∨ (2 ≤ Θ.card ∧ ∀ θ ∈ Θ, θ % 2 = q)) ↔ _
  rw [mem_filter, mem_powerset]

/-- Membership in `runcut_L(Θ)`. -/
theorem pkCo_mem_sepIn {N s k : ℕ} {Θ : Finset ℕ} {p : ℕ × ℕ} :
    p ∈ sepIn N s k Θ ↔ p ∈ diagonals N ∧ p.1 ∈ cycArc N s k ∧ p.2 ∈ cycArc N s k ∧ p.1 ∉ Θ ∧ p.2 ∉ Θ ∧
      ∃ θ ∈ Θ, min (cycPos N s p.1) (cycPos N s p.2) < cycPos N s θ ∧
        cycPos N s θ < max (cycPos N s p.1) (cycPos N s p.2) := by
  show p ∈ (diagonals N).filter (fun p => p.1 ∈ cycArc N s k ∧ p.2 ∈ cycArc N s k ∧ p.1 ∉ Θ ∧ p.2 ∉ Θ ∧
    ∃ θ ∈ Θ, min (cycPos N s p.1) (cycPos N s p.2) < cycPos N s θ ∧
      cycPos N s θ < max (cycPos N s p.1) (cycPos N s p.2)) ↔ _
  rw [mem_filter]

/-- **First hit**: a non-empty set of legs has a leg of least position along the arc from `s`. -/
theorem pkCo_exists_first (N s : ℕ) {Θ : Finset ℕ} (hΘ : Θ.Nonempty) :
    ∃ θ ∈ Θ, ∀ θ' ∈ Θ, cycPos N s θ ≤ cycPos N s θ' :=
  exists_min_image Θ (cycPos N s) hΘ

/-- **Last hit**. -/
theorem pkCo_exists_last (N s : ℕ) {Θ : Finset ℕ} (hΘ : Θ.Nonempty) :
    ∃ θ ∈ Θ, ∀ θ' ∈ Θ, cycPos N s θ' ≤ cycPos N s θ :=
  exists_max_image Θ (cycPos N s) hΘ

/-- Runs: `SameRun` is reflexive. -/
theorem pkCo_sameRun_refl (N s : ℕ) (Θ : Finset ℕ) (u : ℕ) : SameRun N s Θ u u := by
  rintro ⟨θ, -, h1, h2⟩
  rw [min_self] at h1
  rw [max_self] at h2
  omega

/-- Runs: `SameRun` is symmetric. -/
theorem pkCo_sameRun_comm {N s : ℕ} {Θ : Finset ℕ} {u v : ℕ} : SameRun N s Θ u v ↔ SameRun N s Θ v u := by
  show (¬ ∃ θ ∈ Θ, min (cycPos N s u) (cycPos N s v) < cycPos N s θ ∧ cycPos N s θ < max (cycPos N s u) (cycPos N s v)) ↔
    ¬ ∃ θ ∈ Θ, min (cycPos N s v) (cycPos N s u) < cycPos N s θ ∧ cycPos N s θ < max (cycPos N s v) (cycPos N s u)
  rw [min_comm, max_comm]

/-- Runs: `SameRun` is transitive through a leg `v ∉ Θ` (legs in `1..N`). -/
theorem pkCo_sameRun_trans {N s : ℕ} {Θ : Finset ℕ} {u v w : ℕ} (hs : s ∈ Icc 1 N) (hΘ : Θ ⊆ Icc 1 N)
    (hv : v ∈ Icc 1 N) (hvΘ : v ∉ Θ) (h1 : SameRun N s Θ u v) (h2 : SameRun N s Θ v w) : SameRun N s Θ u w := by
  rintro ⟨θ, hθ, a, b⟩
  have hne : cycPos N s θ ≠ cycPos N s v := fun e => by
    rw [pkCo_cycPos_inj hs (hΘ hθ) hv e] at hθ
    exact hvΘ hθ
  by_cases c1 : min (cycPos N s u) (cycPos N s v) < cycPos N s θ ∧ cycPos N s θ < max (cycPos N s u) (cycPos N s v)
  · exact h1 ⟨θ, hθ, c1⟩
  · refine h2 ⟨θ, hθ, ?_⟩
    omega

theorem pkCo_exists_image {G : Finset ℕ} (f : ℕ → ℕ) (p : ℕ → Prop) :
    (∃ t ∈ G.image f, p t) ↔ ∃ t ∈ G, p (f t) := by
  constructor
  · rintro ⟨y, ht, h⟩
    obtain ⟨t, ht', rfl⟩ := mem_image.1 ht
    exact ⟨t, ht', h⟩
  · rintro ⟨t, ht, h⟩
    exact ⟨f t, mem_image_of_mem _ ht, h⟩

/-- Reflection of legs `x ↦ N + 1 − x`. -/
def pkCo_refLeg (N x : ℕ) : ℕ := N + 1 - x

theorem pkCo_refLeg_mem {N x : ℕ} (hx : x ∈ Icc 1 N) : pkCo_refLeg N x ∈ Icc 1 N := by
  rw [mem_Icc] at hx ⊢
  show 1 ≤ N + 1 - x ∧ N + 1 - x ≤ N
  omega

theorem pkCo_refLeg_refLeg {N x : ℕ} (hx : x ∈ Icc 1 N) : pkCo_refLeg N (pkCo_refLeg N x) = x := by
  rw [mem_Icc] at hx
  show N + 1 - (N + 1 - x) = x
  omega

theorem pkCo_refLeg_inj {N x y : ℕ} (hx : x ∈ Icc 1 N) (hy : y ∈ Icc 1 N) (h : pkCo_refLeg N x = pkCo_refLeg N y) :
    x = y := by
  rw [← pkCo_refLeg_refLeg hx, ← pkCo_refLeg_refLeg hy, h]

/-- For even `N`, reflection flips parity. -/
theorem pkCo_refLeg_mod_two {N x : ℕ} (hE : N % 2 = 0) (hx : x ∈ Icc 1 N) : pkCo_refLeg N x % 2 = 1 - x % 2 := by
  rw [mem_Icc] at hx
  show (N + 1 - x) % 2 = 1 - x % 2
  omega

/-- Reflection transport of "different arcs". -/
theorem pkCo_inST_refLeg {N : ℕ} {G : Finset ℕ} (hG : G ⊆ Icc 1 N) {u v : ℕ} (hu : u ∈ Icc 1 N)
    (hv : v ∈ Icc 1 N) : InST (G.image (pkCo_refLeg N)) (pkCo_refLeg N u) (pkCo_refLeg N v) ↔ InST G u v := by
  have mem : ∀ x ∈ Icc 1 N, pkCo_refLeg N x ∈ G.image (pkCo_refLeg N) ↔ x ∈ G := fun x hx => by
    rw [mem_image]
    constructor
    · rintro ⟨y, hy, h⟩
      rw [← pkCo_refLeg_inj (hG hy) hx h]
      exact hy
    · intro h
      exact ⟨x, h, rfl⟩
  rw [pkCo_inST_iff, pkCo_inST_iff, mem u hu, mem v hv,
    pkCo_exists_image (pkCo_refLeg N) (fun t => min (pkCo_refLeg N u) (pkCo_refLeg N v) < t ∧ t < max (pkCo_refLeg N u) (pkCo_refLeg N v)),
    pkCo_exists_image (pkCo_refLeg N) (fun t => t < min (pkCo_refLeg N u) (pkCo_refLeg N v) ∨ max (pkCo_refLeg N u) (pkCo_refLeg N v) < t)]
  rw [mem_Icc] at hu hv
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr ?_ ?_
  · refine exists_congr fun t => and_congr_right fun ht => ?_
    have := mem_Icc.1 (hG ht)
    show (min (N + 1 - u) (N + 1 - v) < N + 1 - t ∧ N + 1 - t < max (N + 1 - u) (N + 1 - v)) ↔ _
    omega
  · refine exists_congr fun t => and_congr_right fun ht => ?_
    have := mem_Icc.1 (hG ht)
    show (N + 1 - t < min (N + 1 - u) (N + 1 - v) ∨ max (N + 1 - u) (N + 1 - v) < N + 1 - t) ↔ _
    omega

/-- Reflection of a sorted pair (re-sorted). -/
def pkCo_refPair (N : ℕ) (p : ℕ × ℕ) : ℕ × ℕ := (pkCo_refLeg N p.2, pkCo_refLeg N p.1)

/-- Reflection transport of `S_G`. -/
theorem pkCo_sepPairs_refLeg {N : ℕ} {G : Finset ℕ} (hG : G ⊆ Icc 1 N) :
    sepPairs N (G.image (pkCo_refLeg N)) = (sepPairs N G).image (pkCo_refPair N) := by
  have hG' : G.image (pkCo_refLeg N) ⊆ Icc 1 N := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
    exact pkCo_refLeg_mem (hG hx)
  ext ⟨a, b⟩
  rw [pkCo_mem_sepPairs hG', mem_image]
  constructor
  · rintro ⟨hq1, hq2, hq, h⟩
    dsimp only at hq1 hq2 hq h
    refine ⟨(pkCo_refLeg N b, pkCo_refLeg N a), ?_, ?_⟩
    · rw [pkCo_mem_sepPairs hG]
      have hb := pkCo_refLeg_mem hq2
      have ha := pkCo_refLeg_mem hq1
      refine ⟨hb, ha, ?_, ?_⟩
      · rw [mem_Icc] at hq1 hq2
        show N + 1 - b < N + 1 - a
        omega
      · have h' := (pkCo_inST_refLeg hG ha hb).1 (by
          rw [pkCo_refLeg_refLeg hq1, pkCo_refLeg_refLeg hq2]
          exact h)
        exact pkCo_inST_comm.1 h'
    · show (pkCo_refLeg N (pkCo_refLeg N a), pkCo_refLeg N (pkCo_refLeg N b)) = (a, b)
      rw [pkCo_refLeg_refLeg hq1, pkCo_refLeg_refLeg hq2]
  · rintro ⟨p, hp, hpq⟩
    rw [← hpq]
    rw [pkCo_mem_sepPairs hG] at hp
    obtain ⟨h1, h2, h3, h⟩ := hp
    refine ⟨pkCo_refLeg_mem h2, pkCo_refLeg_mem h1, ?_, ?_⟩
    · rw [mem_Icc] at h1 h2
      show N + 1 - p.2 < N + 1 - p.1
      omega
    · exact pkCo_inST_comm.1 ((pkCo_inST_refLeg hG h1 h2).2 h)

/-- `sorry` (pkgComb) · the P7a sides are the cyclic arcs `(headStart, headLen)`, `(tailStart, tailLen)` of a mixed
chord (mirror: every odd chord, N = 6, 8, 10). -/
theorem sides_eq_cycArc {N : ℕ} (hN : 4 ≤ N) (hE : Even N) {P : ℕ × ℕ} (hP : P ∈ oddDiagonals N) :
    oddSide N P = cycArc N (headStart P) (headLen N P) ∧ evenSide N P = cycArc N (tailStart P) (tailLen N P) := by
  obtain ⟨h1, h2, h3, -, -⟩ := pkCo_mem_oddDiagonals.1 hP
  unfold evenSide tailLen
  by_cases hp : P.1 % 2 = 1
  · simp only [oddSide, headStart, headLen, tailStart, hp, if_true]
    constructor
    · ext x; rw [pkCo_mem_cycArc_lin h1 (by omega), mem_Icc]; omega
    · ext x; rw [pkCo_mem_cycArc_wrap h1 (by omega) h2, mem_sdiff, mem_Icc, mem_Icc]; omega
  · simp only [oddSide, headStart, headLen, tailStart, hp, if_false]
    rw [show N - (N - (P.2 - P.1)) = P.2 - P.1 by omega]
    constructor
    · ext x; rw [pkCo_mem_cycArc_wrap h1 (by omega) h2, mem_sdiff, mem_Icc, mem_Icc]; omega
    · ext x; rw [pkCo_mem_cycArc_lin h1 (by omega), mem_sdiff, mem_sdiff, mem_Icc, mem_Icc]; omega

/-- `sorry` (pkgComb) · **child sizes** [v3 §14.2 route step 8; BP [Child](2)]: both sides of a mixed chord have odd
length `≥ 3`, so both children have even size between `4` and `N − 2`. -/
theorem childSize_bounds {N : ℕ} (hN : 4 ≤ N) (hE : Even N) {P : ℕ × ℕ} (hP : P ∈ oddDiagonals N) :
    Even (headLen N P + 1) ∧ 4 ≤ headLen N P + 1 ∧ headLen N P + 1 ≤ N - 2 ∧
    Even (tailLen N P + 1) ∧ 4 ≤ tailLen N P + 1 ∧ tailLen N P + 1 ≤ N - 2 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := pkCo_mem_oddDiagonals.1 hP
  have hN2 : N % 2 = 0 := Nat.even_iff.1 hE
  unfold tailLen headLen
  simp only [Nat.even_iff]
  split_ifs <;> omega

/-! pkgChain helpers (R12-P7b-pkgChain-a): positional arc API, [Can] (Lemma X_all, tail side) and [Child](3). -/

theorem pkCh_mem_evens {L : Finset ℕ} {x : ℕ} : x ∈ evens L ↔ x ∈ L ∧ x % 2 = 0 := by
  show x ∈ L.filter (fun a => a % 2 = 0) ↔ _
  rw [mem_filter]

theorem pkCh_mem_odds {L : Finset ℕ} {x : ℕ} : x ∈ odds L ↔ x ∈ L ∧ x % 2 = 1 := by
  show x ∈ L.filter (fun a => a % 2 = 1) ↔ _
  rw [mem_filter]

theorem pkCh_mem_missing {N : ℕ} {S : Finset (ℕ × ℕ)} {p : ℕ × ℕ} :
    p ∈ missing N S ↔ p ∈ diagonals N ∧ p ∉ S := by
  show p ∈ diagonals N \ S ↔ _
  rw [mem_sdiff]

theorem pkCh_mem_Mee {N : ℕ} {S : Finset (ℕ × ℕ)} {p : ℕ × ℕ} :
    p ∈ Mee N S ↔ p ∈ missing N S ∧ p.1 % 2 = 0 ∧ p.2 % 2 = 0 := by
  show p ∈ (missing N S).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0) ↔ _
  rw [mem_filter]

theorem pkCh_mem_Moo {N : ℕ} {S : Finset (ℕ × ℕ)} {p : ℕ × ℕ} :
    p ∈ Moo N S ↔ p ∈ missing N S ∧ p.1 % 2 = 1 ∧ p.2 % 2 = 1 := by
  show p ∈ (missing N S).filter (fun p => p.1 % 2 = 1 ∧ p.2 % 2 = 1) ↔ _
  rw [mem_filter]

theorem pkCh_mem_innerEE {N : ℕ} {S : Finset (ℕ × ℕ)} {P p : ℕ × ℕ} :
    p ∈ innerEE N S P ↔ p ∈ Mee N S ∧ p.1 ∈ evenSide N P ∧ p.2 ∈ evenSide N P := by
  show p ∈ (Mee N S).filter (fun p => p.1 ∈ evenSide N P ∧ p.2 ∈ evenSide N P) ↔ _
  rw [mem_filter]

theorem pkCh_mem_innerOO {N : ℕ} {S : Finset (ℕ × ℕ)} {P p : ℕ × ℕ} :
    p ∈ innerOO N S P ↔ p ∈ Moo N S ∧ p.1 ∈ oddSide N P ∧ p.2 ∈ oddSide N P := by
  show p ∈ (Moo N S).filter (fun p => p.1 ∈ oddSide N P ∧ p.2 ∈ oddSide N P) ↔ _
  rw [mem_filter]

theorem pkCh_mem_pole {N : ℕ} {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ} :
    P ∈ poleChords N S ↔ P ∈ oddDiagonals N ∧ Disjoint (minRect N P) (missing N S) ∧
      (innerEE N S P).Nonempty ∧ (innerOO N S P).Nonempty := by
  show P ∈ ((oddDiagonals N).filter (fun P => Disjoint (minRect N P) (missing N S))).filter
    (fun P => (innerEE N S P).Nonempty ∧ (innerOO N S P).Nonempty) ↔ _
  rw [mem_filter, mem_filter, and_assoc]

theorem pkCh_mem_minRect {N : ℕ} {P p : ℕ × ℕ} :
    p ∈ minRect N P ↔ ∃ e ∈ evens (oddSide N P), ∃ o ∈ odds (evenSide N P), p = (min e o, max e o) := by
  show p ∈ (evens (oddSide N P) ×ˢ odds (evenSide N P)).image (fun q => (min q.1 q.2, max q.1 q.2)) ↔ _
  rw [mem_image]
  constructor
  · rintro ⟨⟨e, o⟩, hq, h⟩
    rw [mem_product] at hq
    exact ⟨e, hq.1, o, hq.2, h.symm⟩
  · rintro ⟨e, he, o, ho, h⟩
    exact ⟨(e, o), mem_product.2 ⟨he, ho⟩, h.symm⟩

theorem pkCh_mem_goodTail {N : ℕ} {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ} :
    P ∈ goodTail N S ↔ P ∈ poleChords N S ∧ NoFreeSep N S (tailStart P) (tailLen N P) 1 := by
  show P ∈ (poleChords N S).filter (fun P => NoFreeSep N S (tailStart P) (tailLen N P) 1) ↔ _
  rw [mem_filter]

theorem pkCh_noFree_iff {N : ℕ} {S : Finset (ℕ × ℕ)} {s k q : ℕ} :
    NoFreeSep N S s k q ↔ ∀ Θ ∈ admSeps N s k q, ¬ Disjoint (sepIn N s k Θ) (missing N S) := Iff.rfl

theorem pkCh_minChord_iff {N : ℕ} {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ} :
    IsMinimalChord N S P ↔ P ∈ goodTail N S ∧ ∀ Q ∈ goodTail N S, ¬ oddSide N Q ⊂ oddSide N P := Iff.rfl

/-- Positions from the leg at position `a`. -/
theorem pkCh_pos_shift {N s a x : ℕ} (hs : s ∈ Icc 1 N) (hx : x ∈ Icc 1 N) (ha : a < N) :
    cycPos N (vtx N (s + a)) x = if a ≤ cycPos N s x then cycPos N s x - a else cycPos N s x + N - a := by
  have hN : 1 ≤ N := by have := mem_Icc.1 hs; omega
  have hv := vtx_bounds N (s + a) hN
  rw [mem_Icc] at hs hx
  rw [pkCo_cycPos_eq hv.1 hv.2 hx.1 hx.2, pkCo_cycPos_eq hs.1 hs.2 hx.1 hx.2, pkCo_vtx_eq hs.1 hs.2 ha.le]
  split_ifs <;> omega

/-- A sub-arc through positions. -/
theorem pkCh_mem_sub {N s a l x : ℕ} (hs : s ∈ Icc 1 N) (hal : a + l ≤ N) (hl : 1 ≤ l) :
    x ∈ cycArc N (vtx N (s + a)) l ↔ x ∈ Icc 1 N ∧ a ≤ cycPos N s x ∧ cycPos N s x < a + l := by
  have hN : 1 ≤ N := by have := mem_Icc.1 hs; omega
  rw [pkCo_mem_cycArc_pos (mem_Icc.2 (vtx_bounds N (s + a) hN)) (by omega)]
  constructor
  · rintro ⟨hx, h⟩
    rw [pkCh_pos_shift hs hx (by omega)] at h
    have := pkCo_cycPos_lt hN s x
    refine ⟨hx, ?_⟩
    split_ifs at h with h1 <;> omega
  · rintro ⟨hx, h1, h2⟩
    refine ⟨hx, ?_⟩
    rw [pkCh_pos_shift hs hx (by omega), if_pos h1]
    omega

/-- Two legs whose positions differ by `2 … N − 2` form a (sorted) diagonal. -/
theorem pkCh_diag_pos {N s x y : ℕ} (hs : s ∈ Icc 1 N) (hx : x ∈ Icc 1 N) (hy : y ∈ Icc 1 N)
    (h1 : min (cycPos N s x) (cycPos N s y) + 2 ≤ max (cycPos N s x) (cycPos N s y))
    (h2 : max (cycPos N s x) (cycPos N s y) + 2 ≤ N + min (cycPos N s x) (cycPos N s y)) :
    (min x y, max x y) ∈ diagonals N := by
  rw [mem_Icc] at hs hx hy
  rw [pkCo_cycPos_eq hs.1 hs.2 hx.1 hx.2, pkCo_cycPos_eq hs.1 hs.2 hy.1 hy.2] at h1 h2
  rw [mem_diagonals]
  dsimp only
  split_ifs at h1 h2 <;> omega

/-- Conversely, a diagonal has positions differing by `2 … N − 2`. -/
theorem pkCh_pos_of_diag {N s x y : ℕ} (hs : s ∈ Icc 1 N) (hx : x ∈ Icc 1 N) (hy : y ∈ Icc 1 N)
    (hd : (min x y, max x y) ∈ diagonals N) :
    min (cycPos N s x) (cycPos N s y) + 2 ≤ max (cycPos N s x) (cycPos N s y) ∧
      max (cycPos N s x) (cycPos N s y) + 2 ≤ N + min (cycPos N s x) (cycPos N s y) := by
  rw [mem_Icc] at hs hx hy
  rw [pkCo_cycPos_eq hs.1 hs.2 hx.1 hx.2, pkCo_cycPos_eq hs.1 hs.2 hy.1 hy.2]
  rw [mem_diagonals] at hd
  dsimp only at hd
  split_ifs <;> omega

/-- A pair of arc legs separated (by position) by a leg of `Θ` lies in `runcut`. -/
theorem pkCh_sepIn_of {N s k θ x y : ℕ} {Θ : Finset ℕ} (hs : s ∈ Icc 1 N) (hk : k + 1 ≤ N)
    (hx : x ∈ Icc 1 N) (hy : y ∈ Icc 1 N) (hxk : cycPos N s x < k) (hyk : cycPos N s y < k)
    (hxT : x ∉ Θ) (hyT : y ∉ Θ) (hθ : θ ∈ Θ)
    (h1 : min (cycPos N s x) (cycPos N s y) < cycPos N s θ)
    (h2 : cycPos N s θ < max (cycPos N s x) (cycPos N s y)) :
    (min x y, max x y) ∈ sepIn N s k Θ := by
  have hkN : k ≤ N := by omega
  have hd := pkCh_diag_pos hs hx hy (by omega) (by omega)
  have hxa := (pkCo_mem_cycArc_pos hs hkN).2 ⟨hx, hxk⟩
  have hya := (pkCo_mem_cycArc_pos hs hkN).2 ⟨hy, hyk⟩
  rw [pkCo_mem_sepIn]
  rcases le_total x y with h | h
  · rw [min_eq_left h, max_eq_right h] at hd ⊢
    exact ⟨hd, hxa, hya, hxT, hyT, θ, hθ, h1, h2⟩
  · rw [min_eq_right h, max_eq_left h] at hd ⊢
    refine ⟨hd, hya, hxa, hyT, hxT, θ, hθ, ?_, ?_⟩
    · rw [min_comm]; exact h1
    · rw [max_comm]; exact h2

/-- Side data of a mixed chord. -/
theorem pkCh_sides {N : ℕ} (hE : N % 2 = 0) {P : ℕ × ℕ} (hP : P ∈ oddDiagonals N) :
    tailStart P ∈ Icc 1 N ∧ tailStart P % 2 = 0 ∧ tailLen N P % 2 = 1 ∧ 3 ≤ tailLen N P ∧ tailLen N P + 3 ≤ N ∧
    headStart P ∈ Icc 1 N ∧ headStart P % 2 = 1 ∧ headLen N P % 2 = 1 ∧ 3 ≤ headLen N P ∧ headLen N P + 3 ≤ N := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := pkCo_mem_oddDiagonals.1 hP
  rw [mem_Icc, mem_Icc]
  unfold tailStart tailLen headStart headLen
  split_ifs <;> omega

/-- Tail membership through positions. -/
theorem pkCh_mem_even {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {P : ℕ × ℕ} (hP : P ∈ oddDiagonals N) {x : ℕ} :
    x ∈ evenSide N P ↔ x ∈ Icc 1 N ∧ cycPos N (tailStart P) x < tailLen N P := by
  obtain ⟨hs, -, -, -, hk, -⟩ := pkCh_sides hE hP
  rw [(sides_eq_cycArc hN (Nat.even_iff.2 hE) hP).2, pkCo_mem_cycArc_pos hs (by omega)]

theorem pkCh_mem_odd {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {P : ℕ × ℕ} (hP : P ∈ oddDiagonals N) {x : ℕ} :
    x ∈ oddSide N P ↔ x ∈ Icc 1 N ∧ tailLen N P ≤ cycPos N (tailStart P) x := by
  have hsub : oddSide N P ⊆ Icc 1 N := by
    rw [(sides_eq_cycArc hN (Nat.even_iff.2 hE) hP).1]
    exact pkCo_cycArc_sub (by omega)
  have he : x ∈ evenSide N P ↔ x ∈ Icc 1 N ∧ x ∉ oddSide N P := by
    show x ∈ Icc 1 N \ oddSide N P ↔ _
    rw [mem_sdiff]
  constructor
  · intro h
    refine ⟨hsub h, ?_⟩
    by_contra hc
    exact ((he.1 ((pkCh_mem_even hN hE hP).2 ⟨hsub h, by omega⟩)).2 h)
  · rintro ⟨hx, h⟩
    by_contra hc
    have := ((pkCh_mem_even hN hE hP).1 (he.2 ⟨hx, hc⟩)).2
    omega

/-- The mixed chord with a given tail (even start `r`, odd length `l`). -/
theorem pkCh_mkTail {N r l : ℕ} (hE : N % 2 = 0) (hr : r ∈ Icc 1 N) (hr2 : r % 2 = 0) (hl : l % 2 = 1)
    (hl3 : 3 ≤ l) (hlN : l + 3 ≤ N) : ∃ Q ∈ oddDiagonals N, tailStart Q = r ∧ tailLen N Q = l := by
  rw [mem_Icc] at hr
  by_cases h : r + l ≤ N
  · refine ⟨(r, r + l), ?_, ?_, ?_⟩
    · rw [pkCo_mem_oddDiagonals]; dsimp only; omega
    · show (if r % 2 = 1 then r + l else r) = r
      rw [if_neg (by omega)]
    · show N - (if r % 2 = 1 then r + l - r else N - (r + l - r)) = l
      rw [if_neg (by omega)]; omega
  · refine ⟨(r + l - N, r), ?_, ?_, ?_⟩
    · rw [pkCo_mem_oddDiagonals]; dsimp only; omega
    · show (if (r + l - N) % 2 = 1 then r else r + l - N) = r
      rw [if_pos (by omega)]
    · show N - (if (r + l - N) % 2 = 1 then r - (r + l - N) else N - (r - (r + l - N))) = l
      rw [if_pos (by omega)]; omega

/-- **[Can] core** (BP App. C §C-3 (B), both cases merged): a sub-run `[a, b]` of the tail (positions, even ends) that
contains an `e_in` pair and whose `minrect` second block is covered gives a `𝒫₁` chord with a shorter tail. -/
theorem pkCh_tailQ {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ}
    (hP : P ∈ poleChords N S) {a b : ℕ} (ha : a % 2 = 0) (hb : b % 2 = 0) (hab : a + 2 ≤ b)
    (hbk : b < tailLen N P) (hne : 0 < a ∨ b + 1 < tailLen N P) {g1 g2 : ℕ} (hg : (g1, g2) ∈ innerEE N S P)
    (hg1 : a ≤ cycPos N (tailStart P) g1 ∧ cycPos N (tailStart P) g1 ≤ b)
    (hg2 : a ≤ cycPos N (tailStart P) g2 ∧ cycPos N (tailStart P) g2 ≤ b)
    (hsep : ∀ e ∈ Icc 1 N, ∀ o ∈ Icc 1 N, e % 2 = 0 → o % 2 = 1 → cycPos N (tailStart P) e < tailLen N P →
      ¬ (a ≤ cycPos N (tailStart P) e ∧ cycPos N (tailStart P) e ≤ b) → a < cycPos N (tailStart P) o →
      cycPos N (tailStart P) o < b → (min e o, max e o) ∉ missing N S) :
    ∃ Q ∈ poleChords N S, tailLen N Q < tailLen N P := by
  obtain ⟨hPo, hPr, -, ⟨f, hf⟩⟩ := pkCh_mem_pole.1 hP
  obtain ⟨hs, hs2, hk1, hk3, hkN, -⟩ := pkCh_sides hE hPo
  have hN1 : 1 ≤ N := by omega
  have hr := vtx_bounds N (tailStart P + a) hN1
  have hr2 : vtx N (tailStart P + a) % 2 = 0 := by
    rw [pkCo_vtx_mod_two hN1 hE]; omega
  obtain ⟨Q, hQ, hQs, hQl⟩ := pkCh_mkTail hE (mem_Icc.2 hr) hr2 (show (b - a + 1) % 2 = 1 by omega)
    (by omega) (by omega)
  have memQ : ∀ x, x ∈ evenSide N Q ↔ x ∈ Icc 1 N ∧ a ≤ cycPos N (tailStart P) x ∧
      cycPos N (tailStart P) x ≤ b := by
    intro x
    rw [(sides_eq_cycArc (by omega) (Nat.even_iff.2 hE) hQ).2, hQs, hQl, pkCh_mem_sub hs (by omega) (by omega)]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, by omega⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, by omega⟩
  refine ⟨Q, pkCh_mem_pole.2 ⟨hQ, ?_, ?_, ?_⟩, by omega⟩
  · rw [disjoint_left]
    intro p hp hpm
    obtain ⟨e, he, o, ho, rfl⟩ := pkCh_mem_minRect.1 hp
    obtain ⟨he1, he2⟩ := pkCh_mem_evens.1 he
    obtain ⟨ho1, ho2⟩ := pkCh_mem_odds.1 ho
    obtain ⟨hoI, hoa, hob⟩ := (memQ o).1 ho1
    have heI : e ∈ Icc 1 N := ((pkCh_mem_odd (by omega) hE hQ).1 he1).1
    have heQ : e ∉ evenSide N Q := fun h => by
      have e1 := (pkCh_mem_odd (by omega) hE hQ).1 he1
      have e2 := (pkCh_mem_even (by omega) hE hQ).1 h
      omega
    have hop := pkCo_cycPos_mod_two hE hs hoI
    by_cases hek : cycPos N (tailStart P) e < tailLen N P
    · refine hsep e heI o hoI he2 ho2 hek (fun h => heQ ((memQ e).2 ⟨heI, h⟩)) ?_ ?_ hpm
      · rcases Nat.lt_or_ge a (cycPos N (tailStart P) o) with h | h
        · exact h
        · omega
      · rcases Nat.lt_or_ge (cycPos N (tailStart P) o) b with h | h
        · exact h
        · omega
    · have heP : e ∈ oddSide N P := (pkCh_mem_odd (by omega) hE hPo).2 ⟨heI, by omega⟩
      have hoP : o ∈ evenSide N P := (pkCh_mem_even (by omega) hE hPo).2 ⟨hoI, by omega⟩
      exact disjoint_left.1 hPr (pkCh_mem_minRect.2 ⟨e, pkCh_mem_evens.2 ⟨heP, he2⟩, o,
        pkCh_mem_odds.2 ⟨hoP, ho2⟩, rfl⟩) hpm
  · obtain ⟨hgM, hg1P, hg2P⟩ := pkCh_mem_innerEE.1 hg
    have h1 := ((pkCh_mem_even (by omega) hE hPo).1 hg1P).1
    have h2 := ((pkCh_mem_even (by omega) hE hPo).1 hg2P).1
    exact ⟨(g1, g2), pkCh_mem_innerEE.2 ⟨hgM, (memQ g1).2 ⟨h1, hg1⟩, (memQ g2).2 ⟨h2, hg2⟩⟩⟩
  · obtain ⟨hfM, hf1, hf2⟩ := pkCh_mem_innerOO.1 hf
    have h1 := (pkCh_mem_odd (by omega) hE hPo).1 hf1
    have h2 := (pkCh_mem_odd (by omega) hE hPo).1 hf2
    refine ⟨f, pkCh_mem_innerOO.2 ⟨hfM, (pkCh_mem_odd (by omega) hE hQ).2 ⟨h1.1, ?_⟩,
      (pkCh_mem_odd (by omega) hE hQ).2 ⟨h2.1, ?_⟩⟩⟩
    · by_contra hc
      have := (memQ f.1).1 ((pkCh_mem_even (by omega) hE hQ).2 ⟨h1.1, by omega⟩)
      omega
    · by_contra hc
      have := (memQ f.2).1 ((pkCh_mem_even (by omega) hE hQ).2 ⟨h2.1, by omega⟩)
      omega


/-- Run ends around `[lo, hi]` for a set of odd positions (abstract form, used by [Can] case 1). -/
theorem pkCh_runEnds (pos : ℕ → ℕ) (Θ : Finset ℕ) {lo hi k : ℕ} (hodd : ∀ θ ∈ Θ, pos θ % 2 = 1)
    (hlo : lo % 2 = 0) (hhi : hi % 2 = 0) (hk : k % 2 = 1) (hθk : ∀ θ ∈ Θ, pos θ + 2 ≤ k) (hhik : hi < k)
    (hlh : lo ≤ hi) :
    ∃ a b, a % 2 = 0 ∧ b % 2 = 0 ∧ a ≤ lo ∧ hi ≤ b ∧ b < k ∧ (a = 0 ∨ ∃ θ ∈ Θ, pos θ + 1 = a) ∧
      (b + 1 = k ∨ ∃ θ ∈ Θ, pos θ = b + 1) ∧ (∀ θ ∈ Θ, pos θ < lo → pos θ < a) ∧
      (∀ θ ∈ Θ, hi < pos θ → b < pos θ) := by
  obtain ⟨a, ha2, hal, ha0, haθ⟩ : ∃ a, a % 2 = 0 ∧ a ≤ lo ∧ (a = 0 ∨ ∃ θ ∈ Θ, pos θ + 1 = a) ∧
      ∀ θ ∈ Θ, pos θ < lo → pos θ < a := by
    by_cases hL : (Θ.filter (fun θ => pos θ < lo)).Nonempty
    · obtain ⟨θ₁, hθ₁, hmax⟩ := exists_max_image _ pos hL
      obtain ⟨hθ₁Θ, hθ₁lt⟩ := mem_filter.1 hθ₁
      have h1 := hodd _ hθ₁Θ
      refine ⟨pos θ₁ + 1, by omega, by omega, Or.inr ⟨θ₁, hθ₁Θ, rfl⟩, fun θ hθΘ hlt => ?_⟩
      have := hmax θ (mem_filter.2 ⟨hθΘ, hlt⟩)
      omega
    · exact ⟨0, rfl, Nat.zero_le _, Or.inl rfl, fun θ hθΘ hlt => (hL ⟨θ, mem_filter.2 ⟨hθΘ, hlt⟩⟩).elim⟩
  obtain ⟨b, hb2, hbh, hbk, hb0, hbθ⟩ : ∃ b, b % 2 = 0 ∧ hi ≤ b ∧ b < k ∧ (b + 1 = k ∨ ∃ θ ∈ Θ, pos θ = b + 1) ∧
      ∀ θ ∈ Θ, hi < pos θ → b < pos θ := by
    by_cases hR : (Θ.filter (fun θ => hi < pos θ)).Nonempty
    · obtain ⟨θ₂, hθ₂, hmin⟩ := exists_min_image _ pos hR
      obtain ⟨hθ₂Θ, hθ₂lt⟩ := mem_filter.1 hθ₂
      have h1 := hodd _ hθ₂Θ
      have h2 := hθk _ hθ₂Θ
      refine ⟨pos θ₂ - 1, by omega, by omega, by omega, Or.inr ⟨θ₂, hθ₂Θ, by omega⟩, fun θ hθΘ hlt => ?_⟩
      have := hmin θ (mem_filter.2 ⟨hθΘ, hlt⟩)
      omega
    · exact ⟨k - 1, by omega, by omega, by omega, Or.inl (by omega),
        fun θ hθΘ hlt => (hR ⟨θ, mem_filter.2 ⟨hθΘ, hlt⟩⟩).elim⟩
  exact ⟨a, b, ha2, hb2, hal, hbh, hbk, ha0, hb0, haθ, hbθ⟩

/-- [Can] case 1 (the failing trace consists of odd legs): the run of `B ∖ Θ` around an `e_in` pair. -/
theorem pkCh_Xodd {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ}
    (hP : P ∈ poleChords N S) {Θ : Finset ℕ}
    (hdis : Disjoint (sepIn N (tailStart P) (tailLen N P) Θ) (missing N S)) (hΘne : Θ.Nonempty)
    (hθ : ∀ θ ∈ Θ, θ ∈ Icc 1 N ∧ 1 ≤ cycPos N (tailStart P) θ ∧ cycPos N (tailStart P) θ + 2 ≤ tailLen N P ∧
      cycPos N (tailStart P) θ % 2 = 1 ∧ θ % 2 = 1)
    {g1 g2 : ℕ} (hg : (g1, g2) ∈ innerEE N S P) {lo hi : ℕ} (hlo : lo % 2 = 0) (hhi : hi % 2 = 0)
    (hlh : lo < hi) (hhik : hi < tailLen N P)
    (hgpos : (cycPos N (tailStart P) g1 = lo ∧ cycPos N (tailStart P) g2 = hi) ∨
      (cycPos N (tailStart P) g1 = hi ∧ cycPos N (tailStart P) g2 = lo))
    (hnb : ∀ θ ∈ Θ, ¬ (lo < cycPos N (tailStart P) θ ∧ cycPos N (tailStart P) θ < hi)) :
    ∃ Q ∈ poleChords N S, tailLen N Q < tailLen N P := by
  obtain ⟨hPo, -, -, -⟩ := pkCh_mem_pole.1 hP
  obtain ⟨hs, hs2, hk1, hk3, hkN, -⟩ := pkCh_sides hE hPo
  have hk' : tailLen N P + 1 ≤ N := by omega
  obtain ⟨a, b, ha2, hb2, hal, hbh, hbk, ha0, hb0, haθ, hbθ⟩ := pkCh_runEnds (cycPos N (tailStart P)) Θ
    (lo := lo) (hi := hi) (k := tailLen N P) (fun θ h => (hθ θ h).2.2.2.1) hlo hhi hk1
    (fun θ h => (hθ θ h).2.2.1) hhik hlh.le
  obtain ⟨θ₀, hθ₀⟩ := hΘne
  have h0 := hθ θ₀ hθ₀
  have h0' := hnb θ₀ hθ₀
  have hlh2 : lo + 2 ≤ hi := by omega
  have hne : 0 < a ∨ b + 1 < tailLen N P := by
    rcases Nat.lt_or_ge (cycPos N (tailStart P) θ₀) lo with h | h
    · left
      have := haθ θ₀ hθ₀ h
      omega
    · right
      have := hbθ θ₀ hθ₀ (by omega)
      omega
  have hg1 : a ≤ cycPos N (tailStart P) g1 ∧ cycPos N (tailStart P) g1 ≤ b := by
    rcases hgpos with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
  have hg2 : a ≤ cycPos N (tailStart P) g2 ∧ cycPos N (tailStart P) g2 ≤ b := by
    rcases hgpos with ⟨-, h1⟩ | ⟨-, h1⟩ <;> omega
  refine pkCh_tailQ hN hE hP ha2 hb2 (by omega) hbk hne hg hg1 hg2 ?_
  intro e he o ho he2 ho2 hek hout hoa hob hm
  have hpe := pkCo_cycPos_mod_two hE hs he
  have hpo := pkCo_cycPos_mod_two hE hs ho
  have heΘ : e ∉ Θ := fun h => by
    have := (hθ e h).2.2.2.2
    omega
  have hoΘ : o ∉ Θ := fun h => by
    have h2 := hnb o h
    have h3 := (hθ o h).2.2.2.1
    by_cases c1 : cycPos N (tailStart P) o < lo
    · have := haθ o h c1
      omega
    · by_cases c2 : hi < cycPos N (tailStart P) o
      · have := hbθ o h c2
        omega
      · omega
  rcases Nat.lt_or_ge (cycPos N (tailStart P) e) a with h | h
  · rcases ha0 with h0 | ⟨θ₁, hθ₁, hθ₁a⟩
    · omega
    · have := (hθ θ₁ hθ₁).2.2.2.1
      exact disjoint_left.1 hdis
        (pkCh_sepIn_of hs hk' he ho hek (by omega) heΘ hoΘ hθ₁ (by omega) (by omega)) hm
  · rcases hb0 with h0 | ⟨θ₂, hθ₂, hθ₂b⟩
    · omega
    · have := (hθ θ₂ hθ₂).2.2.2.1
      exact disjoint_left.1 hdis
        (pkCh_sepIn_of hs hk' he ho hek (by omega) heΘ hoΘ hθ₂ (by omega) (by omega)) hm

/-- [Can] case 2 (the failing trace is one even leg `x`): the piece of `B` on the side of `x` holding the `e_in` pair. -/
theorem pkCh_Xeven {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ}
    (hP : P ∈ poleChords N S) {x : ℕ}
    (hdis : Disjoint (sepIn N (tailStart P) (tailLen N P) {x}) (missing N S))
    (hx : x ∈ Icc 1 N ∧ 1 ≤ cycPos N (tailStart P) x ∧ cycPos N (tailStart P) x + 2 ≤ tailLen N P ∧
      cycPos N (tailStart P) x % 2 = 0)
    {g1 g2 : ℕ} (hg : (g1, g2) ∈ innerEE N S P) {lo hi : ℕ} (hlh : lo < hi) (hhik : hi < tailLen N P)
    (hgpos : (cycPos N (tailStart P) g1 = lo ∧ cycPos N (tailStart P) g2 = hi) ∨
      (cycPos N (tailStart P) g1 = hi ∧ cycPos N (tailStart P) g2 = lo))
    (hside : hi ≤ cycPos N (tailStart P) x ∨ cycPos N (tailStart P) x ≤ lo) :
    ∃ Q ∈ poleChords N S, tailLen N Q < tailLen N P := by
  obtain ⟨hPo, -, -, -⟩ := pkCh_mem_pole.1 hP
  obtain ⟨hs, hs2, hk1, hk3, hkN, -⟩ := pkCh_sides hE hPo
  have hk' : tailLen N P + 1 ≤ N := by omega
  obtain ⟨hxI, hx1, hx2, hx3⟩ := hx
  rcases hside with hs1 | hs1
  · have hg1 : 0 ≤ cycPos N (tailStart P) g1 ∧ cycPos N (tailStart P) g1 ≤ cycPos N (tailStart P) x := by
      rcases hgpos with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
    have hg2 : 0 ≤ cycPos N (tailStart P) g2 ∧ cycPos N (tailStart P) g2 ≤ cycPos N (tailStart P) x := by
      rcases hgpos with ⟨-, h1⟩ | ⟨-, h1⟩ <;> omega
    refine pkCh_tailQ hN hE hP (a := 0) (b := cycPos N (tailStart P) x) (by omega) hx3 (by omega) (by omega)
      (Or.inr (by omega)) hg hg1 hg2 ?_
    intro e he o ho he2 ho2 hek hout hoa hob hm
    have heΘ : e ∉ ({x} : Finset ℕ) := fun h => by
      rw [mem_singleton.1 h] at hout
      omega
    have hoΘ : o ∉ ({x} : Finset ℕ) := fun h => by
      rw [mem_singleton.1 h] at hob
      omega
    exact disjoint_left.1 hdis
      (pkCh_sepIn_of hs hk' he ho hek (by omega) heΘ hoΘ (mem_singleton_self x) (by omega) (by omega)) hm
  · have hg1 : cycPos N (tailStart P) x ≤ cycPos N (tailStart P) g1 ∧
        cycPos N (tailStart P) g1 ≤ tailLen N P - 1 := by
      rcases hgpos with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
    have hg2 : cycPos N (tailStart P) x ≤ cycPos N (tailStart P) g2 ∧
        cycPos N (tailStart P) g2 ≤ tailLen N P - 1 := by
      rcases hgpos with ⟨-, h1⟩ | ⟨-, h1⟩ <;> omega
    refine pkCh_tailQ hN hE hP (a := cycPos N (tailStart P) x) (b := tailLen N P - 1) hx3 (by omega)
      (by omega) (by omega) (Or.inl (by omega)) hg hg1 hg2 ?_
    intro e he o ho he2 ho2 hek hout hoa hob hm
    have heΘ : e ∉ ({x} : Finset ℕ) := fun h => by
      rw [mem_singleton.1 h] at hout
      omega
    have hoΘ : o ∉ ({x} : Finset ℕ) := fun h => by
      rw [mem_singleton.1 h] at hoa
      omega
    exact disjoint_left.1 hdis
      (pkCh_sepIn_of hs hk' he ho hek (by omega) heΘ hoΘ (mem_singleton_self x) (by omega) (by omega)) hm

/-- **Lemma X_all (B)** [BP App. C §C-3; R2-Z158 C1 + R2-Z179 C3]: if `Sep_all(B_P)` fails for `P ∈ 𝒫₁`, some `𝒫₁`
chord has a strictly shorter tail. -/
theorem pkCh_Xall_B {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ}
    (hP : P ∈ poleChords N S) (hc : ¬ NoFreeSep N S (tailStart P) (tailLen N P) 1) :
    ∃ Q ∈ poleChords N S, tailLen N Q < tailLen N P := by
  obtain ⟨hPo, -, ⟨⟨g1, g2⟩, hg⟩, -⟩ := pkCh_mem_pole.1 hP
  obtain ⟨hs, hs2, hk1, hk3, hkN, -⟩ := pkCh_sides hE hPo
  have hkN' : tailLen N P ≤ N := by omega
  obtain ⟨Θ, hΘ, hdis⟩ : ∃ Θ ∈ admSeps N (tailStart P) (tailLen N P) 1,
      Disjoint (sepIn N (tailStart P) (tailLen N P) Θ) (missing N S) := by
    by_contra h
    exact hc (pkCh_noFree_iff.2 fun Θ hΘ hd => h ⟨Θ, hΘ, hd⟩)
  obtain ⟨hΘsub, hΘc⟩ := pkCo_mem_admSeps.1 hΘ
  have hθ : ∀ θ ∈ Θ, θ ∈ Icc 1 N ∧ 1 ≤ cycPos N (tailStart P) θ ∧ cycPos N (tailStart P) θ + 2 ≤ tailLen N P ∧
      cycPos N (tailStart P) θ % 2 = θ % 2 := by
    intro θ h
    obtain ⟨h1, h2, h3⟩ := (pkCo_mem_intArc hs hkN').1 (hΘsub h)
    have := pkCo_cycPos_mod_two hE hs h1
    exact ⟨h1, h2, h3, by omega⟩
  obtain ⟨hgM, hg1P, hg2P⟩ := pkCh_mem_innerEE.1 hg
  obtain ⟨hgm, hge1, hge2⟩ := pkCh_mem_Mee.1 hgM
  obtain ⟨hgd, -⟩ := pkCh_mem_missing.1 hgm
  have hgd' := mem_diagonals.1 hgd
  dsimp only at hg1P hg2P hge1 hge2 hgd'
  obtain ⟨hg1I, hp1⟩ := (pkCh_mem_even (by omega) hE hPo).1 hg1P
  obtain ⟨hg2I, hp2⟩ := (pkCh_mem_even (by omega) hE hPo).1 hg2P
  have hq1 : cycPos N (tailStart P) g1 % 2 = 0 := by
    have := pkCo_cycPos_mod_two hE hs hg1I
    omega
  have hq2 : cycPos N (tailStart P) g2 % 2 = 0 := by
    have := pkCo_cycPos_mod_two hE hs hg2I
    omega
  have hne12 : cycPos N (tailStart P) g1 ≠ cycPos N (tailStart P) g2 := fun h => by
    have := pkCo_cycPos_inj hs hg1I hg2I h
    omega
  have hnb : ∀ θ ∈ Θ, g1 ∉ Θ → g2 ∉ Θ →
      ¬ (min (cycPos N (tailStart P) g1) (cycPos N (tailStart P) g2) < cycPos N (tailStart P) θ ∧
        cycPos N (tailStart P) θ < max (cycPos N (tailStart P) g1) (cycPos N (tailStart P) g2)) := by
    intro θ hθΘ h1 h2 hbt
    have hmem : (g1, g2) ∈ sepIn N (tailStart P) (tailLen N P) Θ := by
      rw [pkCo_mem_sepIn]
      exact ⟨hgd, (pkCo_mem_cycArc_pos hs hkN').2 ⟨hg1I, hp1⟩, (pkCo_mem_cycArc_pos hs hkN').2 ⟨hg2I, hp2⟩,
        h1, h2, θ, hθΘ, hbt⟩
    exact disjoint_left.1 hdis hmem hgm
  obtain ⟨lo, hi, hlo, hhi, hlh, hhik, hgpos, hmin, hmax⟩ : ∃ lo hi, lo % 2 = 0 ∧ hi % 2 = 0 ∧ lo < hi ∧
      hi < tailLen N P ∧ ((cycPos N (tailStart P) g1 = lo ∧ cycPos N (tailStart P) g2 = hi) ∨
        (cycPos N (tailStart P) g1 = hi ∧ cycPos N (tailStart P) g2 = lo)) ∧
      min (cycPos N (tailStart P) g1) (cycPos N (tailStart P) g2) = lo ∧
      max (cycPos N (tailStart P) g1) (cycPos N (tailStart P) g2) = hi := by
    rcases Nat.lt_or_gt_of_ne hne12 with h | h
    · exact ⟨_, _, hq1, hq2, h, hp2, Or.inl ⟨rfl, rfl⟩, min_eq_left h.le, max_eq_right h.le⟩
    · exact ⟨_, _, hq2, hq1, h, hp1, Or.inr ⟨rfl, rfl⟩, min_eq_right h.le, max_eq_left h.le⟩
  rw [hmin, hmax] at hnb
  by_cases hodd : ∀ θ ∈ Θ, θ % 2 = 1
  · have hg1Θ : g1 ∉ Θ := fun h => by
      have := hodd _ h
      omega
    have hg2Θ : g2 ∉ Θ := fun h => by
      have := hodd _ h
      omega
    refine pkCh_Xodd hN hE hP hdis ?_ (fun θ h => ?_) hg hlo hhi hlh hhik hgpos (fun θ h => hnb θ h hg1Θ hg2Θ)
    · exact card_pos.1 (show 0 < Θ.card by omega)
    · obtain ⟨h1, h2, h3, h4⟩ := hθ θ h
      have h5 := hodd θ h
      exact ⟨h1, h2, h3, by omega, h5⟩
  · obtain ⟨x, hxΘ, hx2⟩ : ∃ x ∈ Θ, x % 2 = 0 := by
      by_contra h
      exact hodd fun θ hθ => by
        by_contra h'
        exact h ⟨θ, hθ, by omega⟩
    have hc1 : Θ.card = 1 := by
      rcases hΘc with h | ⟨-, h⟩
      · exact h
      · have := h x hxΘ
        omega
    obtain ⟨x', rfl⟩ := card_eq_one.1 hc1
    rw [mem_singleton] at hxΘ
    rw [hxΘ] at hx2
    have hx := hθ x' (mem_singleton_self x')
    refine pkCh_Xeven hN hE hP hdis ⟨hx.1, hx.2.1, hx.2.2.1, by omega⟩ hg hlh hhik hgpos ?_
    by_contra hbad
    have h1 : g1 ∉ ({x'} : Finset ℕ) := fun h => by
      rw [mem_singleton.1 h] at hgpos
      omega
    have h2 : g2 ∉ ({x'} : Finset ℕ) := fun h => by
      rw [mem_singleton.1 h] at hgpos
      omega
    exact hnb x' (mem_singleton_self x') h1 h2 (by omega)



end PiZ
