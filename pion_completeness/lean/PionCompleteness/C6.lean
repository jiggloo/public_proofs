import PionCompleteness.C5

namespace PiZ

open Finset R12P1 R12P4A R12P3 R12P3C

/-- The point of the planar variables defined by a Gram matrix `C` via [ArcX]. -/
def pkR_gramPt {K : Type*} [Field K] (C : ℕ → ℕ → K) : ℕ × ℕ → K := fun p => pkR_arcX C p.1 p.2

theorem pkR_arcX_def {K : Type*} [Field K] (C : ℕ → ℕ → K) (i j : ℕ) :
    pkR_arcX C i j = -(Finset.sum (Ico i j) (fun d => Finset.sum (Ico i d) (fun c => C c d))) := rfl

theorem pkR_arcX_self {K : Type*} [Field K] (C : ℕ → ℕ → K) (i : ℕ) : pkR_arcX C i i = 0 := by
  rw [pkR_arcX_def, Ico_self, sum_empty, neg_zero]

theorem pkR_arcX_succ {K : Type*} [Field K] (C : ℕ → ℕ → K) {i j : ℕ} (hij : i ≤ j) :
    pkR_arcX C i (j + 1) = pkR_arcX C i j - Finset.sum (Ico i j) (fun c => C c j) := by
  rw [pkR_arcX_def, pkR_arcX_def, sum_Ico_succ_top hij]
  ring

theorem pkR_arcX_edge {K : Type*} [Field K] (C : ℕ → ℕ → K) (i : ℕ) : pkR_arcX C i (i + 1) = 0 := by
  rw [pkR_arcX_succ C le_rfl, pkR_arcX_self, Ico_self, sum_empty, sub_zero]

theorem pkR_arcX_first {K : Type*} [Field K] (C : ℕ → ℕ → K) {i j : ℕ} (hij : i < j) :
    pkR_arcX C i j = pkR_arcX C (i + 1) j - Finset.sum (Ico (i + 1) j) (fun d => C i d) := by
  refine Nat.le_induction (m := i + 1)
    (P := fun j _ => pkR_arcX C i j = pkR_arcX C (i + 1) j - Finset.sum (Ico (i + 1) j) (fun d => C i d))
    ?_ ?_ j hij
  · rw [pkR_arcX_edge, pkR_arcX_self, Ico_self, sum_empty, sub_zero]
  · intro j hj ih
    rw [pkR_arcX_succ C (by omega : i ≤ j), pkR_arcX_succ C hj, ih, sum_eq_sum_Ico_succ_bot (by omega : i < j),
      sum_Ico_succ_top hj]
    ring

/-- Reindexing a sum over an integer range along an increasing enumeration `g` of the legs outside `Z`. -/
theorem pkR_reindex {K : Type*} [Field K] (F : ℕ → K) (Z : Finset ℕ) (g : ℕ → ℕ) (hg : StrictMono g)
    (hgZ : ∀ k, g k ∉ Z) {i j : ℕ} (hs : ∀ a ∈ Ico (g i) (g j), a ∉ Z → ∃ k ∈ Ico i j, g k = a)
    (hF : ∀ a ∈ Z, F a = 0) : Finset.sum (Ico (g i) (g j)) F = Finset.sum (Ico i j) (fun k => F (g k)) := by
  rw [← sum_filter_of_ne (p := fun a => a ∉ Z) (fun a _ ha hz => ha (hF a hz))]
  have e : (Ico (g i) (g j)).filter (fun a => a ∉ Z) = (Ico i j).image g := by
    ext a
    rw [mem_filter, mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      exact hs a h1 h2
    · rintro ⟨k, hk, rfl⟩
      exact ⟨mem_Ico.2 ⟨hg.monotone (mem_Ico.1 hk).1, hg (mem_Ico.1 hk).2⟩, hgZ k⟩
  rw [e, sum_image (fun x _ y _ h => hg.injective h)]

/-- **[Collapse]** (PREFORM-Res §2): a Gram matrix with zero rows on the leg set `Z` gives, on every arc, the planar
value of the collapsed polygon (legs `∉ Z` enumerated in order by `g`, collapsed matrix `C (g k) (g l)`). -/
theorem pkR_collapse {K : Type*} [Field K] (C : ℕ → ℕ → K) (Z : Finset ℕ)
    (hZ : ∀ a b, (a ∈ Z ∨ b ∈ Z) → C a b = 0) (g : ℕ → ℕ) (hg : StrictMono g) (hgZ : ∀ k, g k ∉ Z) {i j : ℕ}
    (hs : ∀ a ∈ Ico (g i) (g j), a ∉ Z → ∃ k ∈ Ico i j, g k = a) :
    pkR_arcX C (g i) (g j) = pkR_arcX (fun k l => C (g k) (g l)) i j := by
  rw [pkR_arcX_def, pkR_arcX_def,
    pkR_reindex (fun d => Finset.sum (Ico (g i) d) (fun c => C c d)) Z g hg hgZ hs
      (fun a ha => sum_eq_zero (fun c _ => hZ c a (Or.inr ha)))]
  refine congrArg (fun t => -t) (sum_congr rfl (fun k hk => ?_))
  refine pkR_reindex (fun c => C c (g k)) Z g hg hgZ ?_ (fun a ha => hZ a (g k) (Or.inl ha))
  intro a ha haZ
  have hk' := mem_Ico.1 hk
  have ha' := mem_Ico.1 ha
  obtain ⟨c, hc, rfl⟩ := hs a (mem_Ico.2 ⟨ha'.1, lt_trans ha'.2 (hg hk'.2)⟩) haZ
  exact ⟨c, mem_Ico.2 ⟨(mem_Ico.1 hc).1, hg.lt_iff_lt.1 ha'.2⟩, rfl⟩

/-- A symmetric, zero-diagonal matrix with zero row sums on `1..n` has vanishing [ArcX] value on the full arc
`[1, n)` (the non-diagonal pair `(1, n)`). -/
theorem pkR_arcX_1n {n : ℕ} (hn : 1 ≤ n) (C : ℕ → ℕ → ℚ) (hs : ∀ a b, C a b = C b a) (hd : ∀ a, C a a = 0)
    (hr : ∀ a ∈ Icc 1 n, Finset.sum (Icc 1 n) (fun b => C a b) = 0) : pkR_arcX C 1 n = 0 := by
  have hI : Icc 1 n = Ico 1 (n + 1) := by
    ext x
    rw [mem_Icc, mem_Ico]
    omega
  -- the lower-triangle sum equals the upper-triangle sum
  have hswap : Finset.sum (Ico 1 n) (fun d => Finset.sum (Ico 1 d) (fun c => C c d)) =
      Finset.sum (Ico 1 n) (fun c => Finset.sum (Ioo c n) (fun d => C c d)) := by
    refine sum_comm' (fun d c => ?_)
    rw [mem_Ico, mem_Ico, mem_Ico, mem_Ioo]
    omega
  -- full square sum over Ico 1 n is zero
  have hrow : ∀ d ∈ Ico 1 n, Finset.sum (Ico 1 n) (fun c => C d c) = - C d n := by
    intro d hd'
    have h := hr d (by rw [mem_Icc]; rw [mem_Ico] at hd'; omega)
    rw [hI, sum_Ico_succ_top hn] at h
    linarith
  have hsq : Finset.sum (Ico 1 n) (fun d => Finset.sum (Ico 1 n) (fun c => C d c)) = 0 := by
    rw [sum_congr rfl hrow, sum_neg_distrib]
    have h := hr n (by rw [mem_Icc]; omega)
    rw [hI, sum_Ico_succ_top hn] at h
    simp only [hd] at h
    have e : Finset.sum (Ico 1 n) (fun d => C d n) = Finset.sum (Ico 1 n) (fun b => C n b) :=
      sum_congr rfl (fun d _ => hs d n)
    rw [e]
    linarith
  -- split each row at the diagonal
  have hsplit : ∀ d ∈ Ico 1 n, Finset.sum (Ico 1 n) (fun c => C d c) =
      Finset.sum (Ico 1 d) (fun c => C c d) + Finset.sum (Ioo d n) (fun c => C d c) := by
    intro d hd'
    have hd1 := mem_Ico.1 hd'
    rw [← sum_Ico_consecutive _ hd1.1 (le_of_lt hd1.2), sum_eq_sum_Ico_succ_bot hd1.2, hd d, zero_add]
    have e1 : Ioo d n = Ico (d + 1) n := by
      ext x
      rw [mem_Ioo, mem_Ico]
      omega
    rw [e1, sum_congr rfl (fun c _ => hs d c : ∀ c ∈ Ico 1 d, C d c = C c d)]
  rw [sum_congr rfl hsplit, sum_add_distrib, ← hswap] at hsq
  rw [pkR_arcX_def]
  linarith

/-- On `1 ≤ i ≤ j ≤ n` the planar variable of the Gram point is its [ArcX] value (non-diagonal pairs included). -/
theorem pkR_planar_gram {n : ℕ} (hn : 1 ≤ n) (C : ℕ → ℕ → ℚ) (hs : ∀ a b, C a b = C b a) (hd : ∀ a, C a a = 0)
    (hr : ∀ a ∈ Icc 1 n, Finset.sum (Icc 1 n) (fun b => C a b) = 0) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j)
    (hj : j ≤ n) : planar n (pkR_gramPt C) i j = pkR_arcX C i j := by
  rw [planar_of_mem _ hi hij hj]
  by_cases hD : (i, j) ∈ diagonals n
  · exact (ite_eq_left hD).trans rfl
  · rw [ite_eq_right hD]
    rw [mem_diagonals] at hD
    dsimp only at hD
    rcases (show j = i ∨ j = i + 1 ∨ (i = 1 ∧ j = n) by omega) with h | h | h
    · rw [h, pkR_arcX_self]
    · rw [h, pkR_arcX_edge]
    · rw [h.1, h.2, pkR_arcX_1n hn C hs hd hr]

theorem pkR_gram_lt {n : ℕ} (hn : 1 ≤ n) (C : ℕ → ℕ → ℚ) (hs : ∀ a b, C a b = C b a) (hd : ∀ a, C a a = 0)
    (hr : ∀ a ∈ Icc 1 n, Finset.sum (Icc 1 n) (fun b => C a b) = 0) {a b : ℕ} (ha : 1 ≤ a) (hab : a < b)
    (hb : b ≤ n) : mesh n (pkR_gramPt C) a b = C a b := by
  rw [pkR_mesh_def]
  rcases (show b < n ∨ b = n by omega) with hb' | hb'
  · rw [pkR_planar_gram hn C hs hd hr (i := a) (j := b) ha (by omega) hb,
      pkR_planar_gram hn C hs hd hr (i := a + 1) (j := b + 1) (by omega) (by omega) (by omega),
      pkR_planar_gram hn C hs hd hr (i := a) (j := b + 1) ha (by omega) (by omega),
      pkR_planar_gram hn C hs hd hr (i := a + 1) (j := b) (by omega) (by omega) hb,
      pkR_arcX_succ C (by omega : a ≤ b), pkR_arcX_succ C (by omega : a + 1 ≤ b), sum_eq_sum_Ico_succ_bot hab]
    ring
  · subst hb'
    have v1 : vtx b (b + 1) = vtx b 1 := by rw [add_comm, vtx_add_n]
    rw [pkR_planar_congr hn _ (rfl : vtx b (a + 1) = vtx b (a + 1)) v1,
      pkR_planar_congr hn _ (rfl : vtx b a = vtx b a) v1, pkR_planar_comm b _ (a + 1) 1, pkR_planar_comm b _ a 1,
      pkR_planar_gram hn C hs hd hr (i := a) (j := b) ha (by omega) le_rfl,
      pkR_planar_gram hn C hs hd hr (i := 1) (j := a + 1) le_rfl (by omega) (by omega),
      pkR_planar_gram hn C hs hd hr (i := 1) (j := a) le_rfl ha (by omega),
      pkR_planar_gram hn C hs hd hr (i := a + 1) (j := b) (by omega) (by omega) le_rfl,
      pkR_arcX_succ C ha, pkR_arcX_first C hab]
    have hI : Icc 1 b = Ico 1 (b + 1) := by
      ext x
      rw [mem_Icc, mem_Ico]
      omega
    have h := hr a (by rw [mem_Icc]; omega)
    rw [hI, sum_Ico_succ_top hn, ← sum_Ico_consecutive _ ha (le_of_lt hab), sum_eq_sum_Ico_succ_bot hab] at h
    simp only [hd] at h
    have e : Finset.sum (Ico 1 a) (fun c => C c a) = Finset.sum (Ico 1 a) (fun c => C a c) :=
      sum_congr rfl (fun c _ => hs c a)
    rw [e]
    linarith

/-- **Gram inverse** (PREFORM-Res §3.4, K2b): the point defined by a symmetric, zero-diagonal Gram matrix with zero row
sums on `1..n` has extended mesh `C` at every pair of distinct legs. -/
theorem pkR_gram {n : ℕ} (hn : 1 ≤ n) (C : ℕ → ℕ → ℚ) (hs : ∀ a b, C a b = C b a) (hd : ∀ a, C a a = 0)
    (hr : ∀ a ∈ Icc 1 n, Finset.sum (Icc 1 n) (fun b => C a b) = 0) {a b : ℕ} (ha : a ∈ Icc 1 n)
    (hb : b ∈ Icc 1 n) (hab : a ≠ b) : mesh n (pkR_gramPt C) a b = C a b := by
  rw [mem_Icc] at ha hb
  rcases lt_or_gt_of_ne hab with h | h
  · exact pkR_gram_lt hn C hs hd hr ha.1 h hb.2
  · rw [pkR_mesh_comm, pkR_gram_lt hn C hs hd hr hb.1 h ha.2, hs]

-- c1 (R12-P7b-pkgRes-c1): mixed-only witness points, the standard polygon, (G), (G′₂)

/-- **Two-level witness point** (c1). With `F x = f (x / 2)` and `H x = h ((x + 1) / 2)`,
`X(p, q) = 2 (F q − F p) (H q − H p)`. Its extended mesh is `−2 (u_a v_b + u_b v_a)` with `u` supported on odd legs and `v`
on even legs (`pkR_fh_mesh`), so every same-parity tile vanishes (`pkR_fh_sp`); it is PREFORM-Res §3.4's four-entry witness
written through prefix sums. -/
def pkR_fhPt (f h : ℕ → ℚ) : ℕ × ℕ → ℚ :=
  fun p => 2 * (f (p.2 / 2) - f (p.1 / 2)) * (h ((p.2 + 1) / 2) - h ((p.1 + 1) / 2))

theorem pkR_fhPt_def (f h : ℕ → ℚ) (p q : ℕ) :
    pkR_fhPt f h (p, q) = 2 * (f (q / 2) - f (p / 2)) * (h ((q + 1) / 2) - h ((p + 1) / 2)) := rfl

theorem pkR_fh_zero1 (f h : ℕ → ℚ) {p q : ℕ} (e : q / 2 = p / 2) : pkR_fhPt f h (p, q) = 0 := by
  rw [pkR_fhPt_def, e]
  ring

theorem pkR_fh_zero2 (f h : ℕ → ℚ) {p q : ℕ} (e : (q + 1) / 2 = (p + 1) / 2) : pkR_fhPt f h (p, q) = 0 := by
  rw [pkR_fhPt_def, e]
  ring

/-- On `1 ≤ i ≤ j ≤ n` the planar variable of the witness point is its formula (edges and `(1, n)` included). -/
theorem pkR_fh_planar {n : ℕ} (f h : ℕ → ℚ) (hf : f 0 = f (n / 2)) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j)
    (hj : j ≤ n) : planar n (pkR_fhPt f h) i j = pkR_fhPt f h (i, j) := by
  rw [planar_of_mem _ hi hij hj]
  by_cases hD : (i, j) ∈ diagonals n
  · exact ite_eq_left hD
  · rw [ite_eq_right hD]
    rw [mem_diagonals] at hD
    dsimp only at hD
    rcases (show j / 2 = i / 2 ∨ (j + 1) / 2 = (i + 1) / 2 ∨ (i = 1 ∧ j = n) by omega) with e | e | e
    · rw [pkR_fh_zero1 f h e]
    · rw [pkR_fh_zero2 f h e]
    · rw [e.1, e.2, pkR_fhPt_def, show 1 / 2 = 0 from rfl, hf]
      ring

/-- The extended mesh of the witness point at `a < b` (all legs in `1..n`, `n` even, the wrap `b = n` included). -/
theorem pkR_fh_mesh {n : ℕ} (hE : n % 2 = 0) (f h : ℕ → ℚ) (hf : f 0 = f (n / 2)) (hh : h 1 = h (n / 2 + 1))
    {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ n) :
    mesh n (pkR_fhPt f h) a b =
      -2 * ((f ((a + 1) / 2) - f (a / 2)) * (h ((b + 1 + 1) / 2) - h ((b + 1) / 2)) +
        (f ((b + 1) / 2) - f (b / 2)) * (h ((a + 1 + 1) / 2) - h ((a + 1) / 2))) := by
  rw [pkR_mesh_def]
  rcases (show b < n ∨ b = n by omega) with hb' | hb'
  · rw [pkR_fh_planar f h hf ha (le_of_lt hab) hb,
      pkR_fh_planar f h hf (i := a + 1) (j := b + 1) (by omega) (by omega) (by omega),
      pkR_fh_planar f h hf (i := a) (j := b + 1) ha (by omega) (by omega),
      pkR_fh_planar f h hf (i := a + 1) (j := b) (by omega) (by omega) hb,
      pkR_fhPt_def, pkR_fhPt_def, pkR_fhPt_def, pkR_fhPt_def]
    ring
  · subst hb'
    have hn1 : 1 ≤ b := by omega
    have v1 : vtx b (b + 1) = vtx b 1 := by rw [add_comm, vtx_add_n]
    have e1 : (b + 1) / 2 = b / 2 := by omega
    have e2 : (b + 1 + 1) / 2 = b / 2 + 1 := by omega
    rw [pkR_planar_congr hn1 _ (rfl : vtx b (a + 1) = vtx b (a + 1)) v1,
      pkR_planar_congr hn1 _ (rfl : vtx b a = vtx b a) v1, pkR_planar_comm b _ (a + 1) 1, pkR_planar_comm b _ a 1,
      pkR_fh_planar f h hf ha (le_of_lt hab) le_rfl,
      pkR_fh_planar f h hf (i := 1) (j := a + 1) le_rfl (by omega) (by omega),
      pkR_fh_planar f h hf (i := 1) (j := a) le_rfl ha (by omega),
      pkR_fh_planar f h hf (i := a + 1) (j := b) (by omega) (by omega) le_rfl,
      pkR_fhPt_def, pkR_fhPt_def, pkR_fhPt_def, pkR_fhPt_def, e1, e2, show 1 / 2 = 0 from rfl,
      show (1 + 1) / 2 = 1 from rfl, hf, hh]
    ring

/-- Every same-parity tile of the witness point vanishes (`a, b ∈ 1..n`, `n` even). -/
theorem pkR_fh_sp {n : ℕ} (hE : n % 2 = 0) (f h : ℕ → ℚ) (hf : f 0 = f (n / 2)) (hh : h 1 = h (n / 2 + 1))
    {a b : ℕ} (ha : a ∈ Icc 1 n) (hb : b ∈ Icc 1 n) (hp : a % 2 = b % 2) : mesh n (pkR_fhPt f h) a b = 0 := by
  rw [mem_Icc] at ha hb
  have key : ∀ a b : ℕ, 1 ≤ a → a < b → b ≤ n → a % 2 = b % 2 → mesh n (pkR_fhPt f h) a b = 0 := by
    intro a b ha hab hb hp
    rw [pkR_fh_mesh hE f h hf hh ha hab hb]
    rcases (show a % 2 = 0 ∨ a % 2 = 1 by omega) with h0 | h0
    · rw [show (a + 1) / 2 = a / 2 by omega, show (b + 1) / 2 = b / 2 by omega]
      ring
    · rw [show (a + 1 + 1) / 2 = (a + 1) / 2 by omega, show (b + 1 + 1) / 2 = (b + 1) / 2 by omega]
      ring
  rcases (show a < b ∨ a = b ∨ b < a by omega) with h1 | h1 | h1
  · exact key a b ha.1 h1 hb.2 hp
  · rw [h1, pkR_mesh_self (by omega : 1 ≤ n)]
  · rw [pkR_mesh_comm]
    exact key b a hb.1 h1 ha.2 hp.symm

/-- The straddling tile `c⋆′` of the standard polygon `(n, d₁)` (legs `2d₁, 2d₁ + 2` around `r = 2d₁ + 1`, read with
`vtx`: `(2, n)` when `d₁ = 0`). PREFORM-Res §3.1. -/
def pkR_cstp (n d₁ : ℕ) : ℕ × ℕ := if d₁ = 0 then (2, n) else (2 * d₁, 2 * d₁ + 2)

/-- The head `A_Q = [2i + 1, 2d₁ + 2j + 1]` of the standard member `Q = (i, j)` (PREFORM-Res §3.1). -/
def pkR_head (d₁ : ℕ) (Q : ℕ × ℕ) : Finset ℕ := Icc (2 * Q.1 + 1) (2 * d₁ + 2 * Q.2 + 1)

/-- The member chord `(2i + 1, 2d₁ + 2j + 2)` of the index pair `Q = (i, j)`. -/
def pkR_mchord (d₁ : ℕ) (Q : ℕ × ℕ) : ℕ × ℕ := (2 * Q.1 + 1, 2 * d₁ + 2 * Q.2 + 2)

/-- `minrect(Q)` of the standard polygon: (odd strip leg `∉ A_Q`, even strip leg `∈ A_Q`); strip legs are all legs but
`s = n` and `r = 2d₁ + 1`. PREFORM-Res §3.1. -/
def pkR_minrect (n d₁ : ℕ) (Q : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 n).filter (fun w => w % 2 = 1 ∧ w ≠ 2 * d₁ + 1 ∧ w ∉ pkR_head d₁ Q)) ×ˢ
    ((Icc 1 n).filter (fun c => c % 2 = 0 ∧ c ≠ n ∧ c ∈ pkR_head d₁ Q))

/-- **Λ^I** of the standard polygon `(n, d₁)` (PREFORM-Res §3.1): same-parity tiles vanish except `c⋆ = c_{1,n−1}` and
`c⋆′`, `c⋆ = c⋆′`, and the `minrect` tiles of every member of `I` vanish. `x := c⋆ = mesh n X 1 (n − 1)`. -/
def pkR_lam (n d₁ : ℕ) (I : Finset (ℕ × ℕ)) (X : ℕ × ℕ → ℚ) : Prop :=
  (∀ a ∈ Icc 1 n, ∀ b ∈ Icc 1 n, a + 2 ≤ b → a % 2 = b % 2 → (a, b) ≠ (1, n - 1) → (a, b) ≠ pkR_cstp n d₁ →
      mesh n X a b = 0) ∧ mesh n X 1 (n - 1) = mesh n X (pkR_cstp n d₁).1 (pkR_cstp n d₁).2 ∧
  ∀ Q ∈ I, ∀ t ∈ pkR_minrect n d₁ Q, mesh n X t.1 t.2 = 0

theorem pkR_lam_iff (n d₁ : ℕ) (I : Finset (ℕ × ℕ)) (X : ℕ × ℕ → ℚ) : pkR_lam n d₁ I X ↔
    (∀ a ∈ Icc 1 n, ∀ b ∈ Icc 1 n, a + 2 ≤ b → a % 2 = b % 2 → (a, b) ≠ (1, n - 1) → (a, b) ≠ pkR_cstp n d₁ →
      mesh n X a b = 0) ∧ mesh n X 1 (n - 1) = mesh n X (pkR_cstp n d₁).1 (pkR_cstp n d₁).2 ∧
    ∀ Q ∈ I, ∀ t ∈ pkR_minrect n d₁ Q, mesh n X t.1 t.2 = 0 := Iff.rfl

/-- A point whose same-parity tiles all vanish lies on `Λ₀ = Λ ∩ {x = 0}` of every standard polygon. -/
theorem pkR_lam_of_sp {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) (d₁ : ℕ) (hd : 2 * d₁ + 2 ≤ n) {X : ℕ × ℕ → ℚ}
    (hX : ∀ a ∈ Icc 1 n, ∀ b ∈ Icc 1 n, a % 2 = b % 2 → mesh n X a b = 0) :
    pkR_lam n d₁ ∅ X ∧ mesh n X 1 (n - 1) = 0 := by
  have hx : mesh n X 1 (n - 1) = 0 := hX 1 (mem_Icc.2 ⟨le_rfl, by omega⟩) (n - 1) (mem_Icc.2 ⟨by omega, by omega⟩)
    (by omega)
  refine ⟨⟨fun a ha b hb _ hp _ _ => hX a ha b hb hp, ?_, fun Q hQ => by simp at hQ⟩, hx⟩
  rw [hx]
  have e : pkR_cstp n d₁ = if d₁ = 0 then (2, n) else (2 * d₁, 2 * d₁ + 2) := rfl
  rw [e]
  split_ifs with h0
  · exact (hX 2 (mem_Icc.2 ⟨by omega, by omega⟩) n (mem_Icc.2 ⟨by omega, le_rfl⟩) (by omega)).symm
  · exact (hX (2 * d₁) (mem_Icc.2 ⟨by omega, by omega⟩) (2 * d₁ + 2) (mem_Icc.2 ⟨by omega, hd⟩) (by omega)).symm

/-- Witness functions for one mixed diagonal `(p', q')`: the two levels jump across it. -/
theorem pkR_fh_ne {n p' q' : ℕ} (hQ' : (p', q') ∈ oddDiagonals n) (f h : ℕ → ℚ)
    (hfv : f (q' / 2) - f (p' / 2) ≠ 0) (hhv : h ((q' + 1) / 2) - h ((p' + 1) / 2) ≠ 0) :
    pkR_fhPt f h (p', q') ≠ 0 := by
  rw [pkR_fhPt_def]
  exact mul_ne_zero (mul_ne_zero two_ne_zero hfv) hhv

/-- A two-step level function: `+1` at `b` (unless `b = hi`), `−1` at `a` (unless `a = lo`). -/
def pkR_lev (a b lo hi : ℕ) : ℕ → ℚ := fun k => (if k = b ∧ k ≠ hi then 1 else 0) - (if k = a ∧ k ≠ lo then 1 else 0)

theorem pkR_lev_def (a b lo hi k : ℕ) :
    pkR_lev a b lo hi k = (if k = b ∧ k ≠ hi then 1 else 0) - (if k = a ∧ k ≠ lo then 1 else 0) := rfl

/-- The indicator of `a`, glued to `hi` when `a = lo` (so that it takes equal values at `lo` and `hi`). -/
def pkR_dlt (a lo hi : ℕ) : ℕ → ℚ := fun k => if k = a ∨ (a = lo ∧ k = hi) then 1 else 0

theorem pkR_dlt_def (a lo hi k : ℕ) : pkR_dlt a lo hi k = if k = a ∨ (a = lo ∧ k = hi) then 1 else 0 := rfl

/-- **(G)** (PREFORM-Res §3.4, R2-Z201 C1): every mixed diagonal is non-zero somewhere on `Λ₀` of every standard
polygon; the witness is a two-level point (mixed tiles only). -/
theorem pkR_G {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) (d₁ : ℕ) (hd : 2 * d₁ + 2 ≤ n) {Q : ℕ × ℕ}
    (hQ : Q ∈ oddDiagonals n) : ∃ X : ℕ × ℕ → ℚ, pkR_lam n d₁ ∅ X ∧ mesh n X 1 (n - 1) = 0 ∧ X Q ≠ 0 := by
  obtain ⟨p, q⟩ := Q
  have hQd := mem_filter.1 hQ
  rw [mem_diagonals] at hQd
  dsimp only at hQd
  have hf : pkR_lev (p / 2) (q / 2) 0 (n / 2) 0 = pkR_lev (p / 2) (q / 2) 0 (n / 2) (n / 2) := by
    rw [pkR_lev_def, pkR_lev_def]
    split_ifs <;> (try omega) <;> norm_num
  have hh : pkR_lev ((p + 1) / 2) ((q + 1) / 2) 1 (n / 2 + 1) 1 =
      pkR_lev ((p + 1) / 2) ((q + 1) / 2) 1 (n / 2 + 1) (n / 2 + 1) := by
    rw [pkR_lev_def, pkR_lev_def]
    split_ifs <;> (try omega) <;> norm_num
  refine ⟨pkR_fhPt (pkR_lev (p / 2) (q / 2) 0 (n / 2)) (pkR_lev ((p + 1) / 2) ((q + 1) / 2) 1 (n / 2 + 1)), ?_⟩
  obtain ⟨h1, h2⟩ := pkR_lam_of_sp hE hn d₁ hd (fun a ha b hb hp => pkR_fh_sp hE _ _ hf hh ha hb hp)
  refine ⟨h1, h2, pkR_fh_ne hQ _ _ ?_ ?_⟩
  · rw [pkR_lev_def, pkR_lev_def]
    split_ifs <;> (try omega) <;> norm_num
  · rw [pkR_lev_def, pkR_lev_def]
    split_ifs <;> (try omega) <;> norm_num

/-- **(G′₂)** (PREFORM-Res §3.4, R2-Z201 C2): for distinct mixed diagonals `Q ≠ Q'` there is a point of `Λ₀` (of every
standard polygon) with `X_Q = 0` and `X_{Q'} ≠ 0` — the non-proportionality `[ProdDiv]` consumes. Two-level witness: the
`h`-level separates `Q'` and not `Q` unless both chords have the same `⌈·/2⌉` ends; then the `f`-level does. -/
theorem pkR_G2 {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) (d₁ : ℕ) (hd : 2 * d₁ + 2 ≤ n) {Q Q' : ℕ × ℕ}
    (hQ : Q ∈ oddDiagonals n) (hQ' : Q' ∈ oddDiagonals n) (hne : Q ≠ Q') :
    ∃ X : ℕ × ℕ → ℚ, pkR_lam n d₁ ∅ X ∧ mesh n X 1 (n - 1) = 0 ∧ X Q = 0 ∧ X Q' ≠ 0 := by
  obtain ⟨p, q⟩ := Q
  obtain ⟨p', q'⟩ := Q'
  have hQd := mem_filter.1 hQ
  have hQd' := mem_filter.1 hQ'
  rw [mem_diagonals] at hQd hQd'
  dsimp only at hQd hQd'
  have hne' : ¬ (p = p' ∧ q = q') := fun hc => hne (by rw [hc.1, hc.2])
  -- generic assembly from two level functions
  have fin : ∀ f h : ℕ → ℚ, f 0 = f (n / 2) → h 1 = h (n / 2 + 1) →
      (f (q / 2) - f (p / 2) = 0 ∨ h ((q + 1) / 2) - h ((p + 1) / 2) = 0) →
      f (q' / 2) - f (p' / 2) ≠ 0 → h ((q' + 1) / 2) - h ((p' + 1) / 2) ≠ 0 →
      ∃ X : ℕ × ℕ → ℚ, pkR_lam n d₁ ∅ X ∧ mesh n X 1 (n - 1) = 0 ∧ X (p, q) = 0 ∧ X (p', q') ≠ 0 := by
    intro f h hf hh h0 h1 h2
    obtain ⟨l1, l2⟩ := pkR_lam_of_sp hE hn d₁ hd (fun a ha b hb hp => pkR_fh_sp hE f h hf hh ha hb hp)
    refine ⟨pkR_fhPt f h, l1, l2, ?_, pkR_fh_ne hQ' f h h1 h2⟩
    rw [pkR_fhPt_def]
    rcases h0 with e | e
    · rw [e]
      ring
    · rw [e]
      ring
  have fc0 : pkR_lev (p' / 2) (q' / 2) 0 (n / 2) 0 = pkR_lev (p' / 2) (q' / 2) 0 (n / 2) (n / 2) := by
    rw [pkR_lev_def, pkR_lev_def]
    split_ifs <;> (try omega) <;> norm_num
  have fc1 : pkR_lev (p' / 2) (q' / 2) 0 (n / 2) (q' / 2) - pkR_lev (p' / 2) (q' / 2) 0 (n / 2) (p' / 2) ≠ 0 := by
    rw [pkR_lev_def, pkR_lev_def]
    split_ifs <;> (try omega) <;> norm_num
  have hc0 : pkR_lev ((p' + 1) / 2) ((q' + 1) / 2) 1 (n / 2 + 1) 1 =
      pkR_lev ((p' + 1) / 2) ((q' + 1) / 2) 1 (n / 2 + 1) (n / 2 + 1) := by
    rw [pkR_lev_def, pkR_lev_def]
    split_ifs <;> (try omega) <;> norm_num
  have hc1 : pkR_lev ((p' + 1) / 2) ((q' + 1) / 2) 1 (n / 2 + 1) ((q' + 1) / 2) -
      pkR_lev ((p' + 1) / 2) ((q' + 1) / 2) 1 (n / 2 + 1) ((p' + 1) / 2) ≠ 0 := by
    rw [pkR_lev_def, pkR_lev_def]
    split_ifs <;> (try omega) <;> norm_num
  by_cases cA : (q' + 1) / 2 ≠ (p + 1) / 2 ∧ (q' + 1) / 2 ≠ (q + 1) / 2
  · -- h = indicator of ⌈q'/2⌉
    refine fin _ (pkR_dlt ((q' + 1) / 2) 1 (n / 2 + 1)) fc0 ?_ (Or.inr ?_) fc1 ?_
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num
  by_cases cB : (p' + 1) / 2 ≠ (p + 1) / 2 ∧ (p' + 1) / 2 ≠ (q + 1) / 2
  · -- h = indicator of ⌈p'/2⌉ (glued 1 ~ n/2 + 1)
    refine fin _ (pkR_dlt ((p' + 1) / 2) 1 (n / 2 + 1)) fc0 ?_ (Or.inr ?_) fc1 ?_
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num
  -- equal ⌈·/2⌉ ends: the f-level separates
  by_cases cC : q' / 2 ≠ p / 2 ∧ q' / 2 ≠ q / 2 ∧ q' / 2 ≠ n / 2
  · refine fin (pkR_dlt (q' / 2) 0 (n / 2)) _ ?_ hc0 (Or.inl ?_) ?_ hc1
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num
  · refine fin (pkR_dlt (p' / 2) 0 (n / 2)) _ ?_ hc0 (Or.inl ?_) ?_ hc1
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num

/-- A mixed tile (odd `a`, even `c`) of the two-level witness point: `c_{a,c} = −2 u_a v_c`. -/
theorem pkR_fh_mixed {n : ℕ} (hE : n % 2 = 0) (f h : ℕ → ℚ) (hf : f 0 = f (n / 2)) (hh : h 1 = h (n / 2 + 1))
    {a c : ℕ} (ha : a ∈ Icc 1 n) (hc : c ∈ Icc 1 n) (hao : a % 2 = 1) (hce : c % 2 = 0) :
    mesh n (pkR_fhPt f h) a c = -2 * (f ((a + 1) / 2) - f (a / 2)) * (h (c / 2 + 1) - h (c / 2)) := by
  rw [mem_Icc] at ha hc
  rcases (show a < c ∨ c < a by omega) with h1 | h1
  · rw [pkR_fh_mesh hE f h hf hh ha.1 h1 hc.2, show (c + 1) / 2 = c / 2 by omega,
      show (c + 1 + 1) / 2 = c / 2 + 1 by omega, show (a + 1 + 1) / 2 = (a + 1) / 2 by omega]
    ring
  · rw [pkR_mesh_comm, pkR_fh_mesh hE f h hf hh hc.1 h1 ha.2, show (c + 1) / 2 = c / 2 by omega,
      show (c + 1 + 1) / 2 = c / 2 + 1 by omega, show (a + 1 + 1) / 2 = (a + 1) / 2 by omega]
    ring

theorem pkR_mem_head (d₁ : ℕ) (Q : ℕ × ℕ) (x : ℕ) :
    x ∈ pkR_head d₁ Q ↔ 2 * Q.1 + 1 ≤ x ∧ x ≤ 2 * d₁ + 2 * Q.2 + 1 := by
  show x ∈ Icc (2 * Q.1 + 1) (2 * d₁ + 2 * Q.2 + 1) ↔ _
  exact mem_Icc

theorem pkR_mem_minrect (n d₁ : ℕ) (Q t : ℕ × ℕ) : t ∈ pkR_minrect n d₁ Q ↔
    (t.1 ∈ Icc 1 n ∧ t.1 % 2 = 1 ∧ t.1 ≠ 2 * d₁ + 1 ∧ t.1 ∉ pkR_head d₁ Q) ∧
      (t.2 ∈ Icc 1 n ∧ t.2 % 2 = 0 ∧ t.2 ≠ n ∧ t.2 ∈ pkR_head d₁ Q) := by
  show t ∈ ((Icc 1 n).filter (fun w => w % 2 = 1 ∧ w ≠ 2 * d₁ + 1 ∧ w ∉ pkR_head d₁ Q)) ×ˢ
    ((Icc 1 n).filter (fun c => c % 2 = 0 ∧ c ≠ n ∧ c ∈ pkR_head d₁ Q)) ↔ _
  rw [mem_product, mem_filter, mem_filter]

/-- Adding `minrect` conditions to a point of `Λ`. -/
theorem pkR_lam_add {n d₁ : ℕ} {I : Finset (ℕ × ℕ)} {X : ℕ × ℕ → ℚ} (h0 : pkR_lam n d₁ ∅ X)
    (hI : ∀ Q ∈ I, ∀ t ∈ pkR_minrect n d₁ Q, mesh n X t.1 t.2 = 0) : pkR_lam n d₁ I X := by
  obtain ⟨a, b, -⟩ := h0
  exact ⟨a, b, hI⟩

/-- **(G″)** (PREFORM-Res §3.4, R2-Z201 C6): for `d₁ ≥ 1` and `b' = (d₁ − 1, 0)` (chord `(2d₁ − 1, 2d₁ + 2)`), every
other mixed diagonal is non-zero somewhere on `Λ^{b'}₀`. -/
theorem pkR_G3 {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) (d₁ : ℕ) (hd1 : 1 ≤ d₁) (hd : 2 * d₁ + 2 ≤ n) {Q : ℕ × ℕ}
    (hQ : Q ∈ oddDiagonals n) (hne : Q ≠ pkR_mchord d₁ (d₁ - 1, 0)) :
    ∃ X : ℕ × ℕ → ℚ, pkR_lam n d₁ {(d₁ - 1, 0)} X ∧ mesh n X 1 (n - 1) = 0 ∧ X Q ≠ 0 := by
  obtain ⟨p, q⟩ := Q
  have hQd := mem_filter.1 hQ
  rw [mem_diagonals] at hQd
  dsimp only at hQd
  have hne' : ¬ (p = 2 * (d₁ - 1) + 1 ∧ q = 2 * d₁ + 2 * 0 + 2) := fun hc => hne (by rw [hc.1, hc.2]; rfl)
  have fin : ∀ h : ℕ → ℚ, h 1 = h (n / 2 + 1) → h (d₁ + 1) = h d₁ → h ((q + 1) / 2) - h ((p + 1) / 2) ≠ 0 →
      ∃ X : ℕ × ℕ → ℚ, pkR_lam n d₁ {(d₁ - 1, 0)} X ∧ mesh n X 1 (n - 1) = 0 ∧ X (p, q) ≠ 0 := by
    intro h hh hv h2
    have hf : pkR_lev (p / 2) (q / 2) 0 (n / 2) 0 = pkR_lev (p / 2) (q / 2) 0 (n / 2) (n / 2) := by
      rw [pkR_lev_def, pkR_lev_def]
      split_ifs <;> (try omega) <;> norm_num
    have h1 : pkR_lev (p / 2) (q / 2) 0 (n / 2) (q / 2) - pkR_lev (p / 2) (q / 2) 0 (n / 2) (p / 2) ≠ 0 := by
      rw [pkR_lev_def, pkR_lev_def]
      split_ifs <;> (try omega) <;> norm_num
    obtain ⟨l1, l2⟩ := pkR_lam_of_sp hE hn d₁ hd (fun a ha b hb hp => pkR_fh_sp hE _ h hf hh ha hb hp)
    refine ⟨pkR_fhPt (pkR_lev (p / 2) (q / 2) 0 (n / 2)) h, pkR_lam_add l1 ?_, l2, pkR_fh_ne hQ _ h h1 h2⟩
    intro Q' hQ' t ht
    rw [mem_singleton] at hQ'
    subst hQ'
    rw [pkR_mem_minrect, pkR_mem_head, pkR_mem_head] at ht
    obtain ⟨⟨w1, w2, -, -⟩, ⟨c1, c2, -, c4⟩⟩ := ht
    dsimp only at c4
    rw [pkR_fh_mixed hE _ h hf hh w1 c1 w2 c2, show t.2 / 2 = d₁ by omega, hv]
    ring
  by_cases cA : (q + 1) / 2 ≠ d₁ ∧ (q + 1) / 2 ≠ d₁ + 1
  · refine fin (pkR_dlt ((q + 1) / 2) 1 (n / 2 + 1)) ?_ ?_ ?_
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num
  · refine fin (pkR_dlt ((p + 1) / 2) 1 (n / 2 + 1)) ?_ ?_ ?_
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num

/-- **Chain point** for `x ≢ 0` on `Λ` (c1): `Σ_{k = 2d₁+2}^{n} (−1)^k e_{(k−1, k+1)}` (short chords, the `k = n` one is
`(1, n − 1)`). Its same-parity tiles telescope to `c⋆ = c⋆′ = 1`. -/
def pkR_chA (n d₁ : ℕ) : ℕ × ℕ → ℚ := fun p =>
  (if p.2 = p.1 + 2 ∧ 2 * d₁ + 1 ≤ p.1 ∧ p.2 ≤ n then (if p.1 % 2 = 1 then 1 else -1) else 0) +
    (if p.1 = 1 ∧ p.2 = n - 1 then 1 else 0)

theorem pkR_chA_def (n d₁ p q : ℕ) : pkR_chA n d₁ (p, q) =
    (if q = p + 2 ∧ 2 * d₁ + 1 ≤ p ∧ q ≤ n then (if p % 2 = 1 then 1 else -1) else 0) +
      (if p = 1 ∧ q = n - 1 then 1 else 0) := rfl

theorem pkR_chA_planar {n : ℕ} (hn : 4 ≤ n) (d₁ : ℕ) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ n) :
    planar n (pkR_chA n d₁) i j = pkR_chA n d₁ (i, j) := by
  rw [planar_of_mem _ hi hij hj]
  by_cases hD : (i, j) ∈ diagonals n
  · exact ite_eq_left hD
  · rw [ite_eq_right hD]
    rw [mem_diagonals] at hD
    dsimp only at hD
    rw [pkR_chA_def]
    split_ifs <;> (try omega) <;> norm_num

theorem pkR_chA_mesh_lt {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ : ℕ} {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) (hb : b < n)
    (hp : a % 2 = b % 2) :
    mesh n (pkR_chA n d₁) a b = (if a = 1 ∧ b = n - 1 then 1 else 0) +
      (if (d₁ = 0 ∧ a = 2 ∧ b = n) ∨ (d₁ ≠ 0 ∧ a = 2 * d₁ ∧ b = 2 * d₁ + 2) then 1 else 0) := by
  rw [pkR_mesh_def, pkR_chA_planar hn d₁ ha (le_of_lt hab) (le_of_lt hb),
    pkR_chA_planar hn d₁ (i := a + 1) (j := b + 1) (by omega) (by omega) (by omega),
    pkR_chA_planar hn d₁ (i := a) (j := b + 1) ha (by omega) (by omega),
    pkR_chA_planar hn d₁ (i := a + 1) (j := b) (by omega) (by omega) (le_of_lt hb)]
  have e3 : pkR_chA n d₁ (a, b + 1) = 0 := by
    rw [pkR_chA_def]
    split_ifs <;> (try omega) <;> norm_num
  have e4 : pkR_chA n d₁ (a + 1, b) = 0 := by
    rw [pkR_chA_def]
    split_ifs <;> (try omega) <;> norm_num
  rw [e3, e4, pkR_chA_def, pkR_chA_def, ite_eq_right (show ¬ (a + 1 = 1 ∧ b + 1 = n - 1) by omega)]
  by_cases hc : b = a + 2 ∧ 2 * d₁ ≤ a
  · rw [ite_eq_left (show b + 1 = a + 1 + 2 ∧ 2 * d₁ + 1 ≤ a + 1 ∧ b + 1 ≤ n by omega)]
    by_cases h2 : a = 2 * d₁
    · rw [ite_eq_right (show ¬ (b = a + 2 ∧ 2 * d₁ + 1 ≤ a ∧ b ≤ n) by omega),
        ite_eq_left (show (a + 1) % 2 = 1 by omega),
        ite_eq_left (show (d₁ = 0 ∧ a = 2 ∧ b = n) ∨ (d₁ ≠ 0 ∧ a = 2 * d₁ ∧ b = 2 * d₁ + 2) by omega)]
      ring
    · rw [ite_eq_left (show b = a + 2 ∧ 2 * d₁ + 1 ≤ a ∧ b ≤ n by omega),
        ite_eq_right (show ¬ ((d₁ = 0 ∧ a = 2 ∧ b = n) ∨ (d₁ ≠ 0 ∧ a = 2 * d₁ ∧ b = 2 * d₁ + 2)) by omega)]
      rcases (show a % 2 = 0 ∨ a % 2 = 1 by omega) with h3 | h3
      · rw [ite_eq_right (show ¬ a % 2 = 1 by omega), ite_eq_left (show (a + 1) % 2 = 1 by omega)]
        ring
      · rw [ite_eq_left h3, ite_eq_right (show ¬ (a + 1) % 2 = 1 by omega)]
        ring
  · rw [ite_eq_right (show ¬ (b + 1 = a + 1 + 2 ∧ 2 * d₁ + 1 ≤ a + 1 ∧ b + 1 ≤ n) by omega),
      ite_eq_right (show ¬ (b = a + 2 ∧ 2 * d₁ + 1 ≤ a ∧ b ≤ n) by omega),
      ite_eq_right (show ¬ ((d₁ = 0 ∧ a = 2 ∧ b = n) ∨ (d₁ ≠ 0 ∧ a = 2 * d₁ ∧ b = 2 * d₁ + 2)) by omega)]
    ring

theorem pkR_chA_mesh_n {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ : ℕ} (hd : 2 * d₁ + 2 ≤ n) {a : ℕ} (ha : 1 ≤ a) (hab : a < n) (hp : a % 2 = n % 2) :
    mesh n (pkR_chA n d₁) a n = (if a = 1 ∧ n = n - 1 then 1 else 0) +
      (if (d₁ = 0 ∧ a = 2 ∧ n = n) ∨ (d₁ ≠ 0 ∧ a = 2 * d₁ ∧ n = 2 * d₁ + 2) then 1 else 0) := by
  have hn1 : 1 ≤ n := by omega
  have v1 : vtx n (n + 1) = vtx n 1 := by rw [add_comm, vtx_add_n]
  rw [pkR_mesh_def, pkR_planar_congr hn1 _ (rfl : vtx n (a + 1) = vtx n (a + 1)) v1,
    pkR_planar_congr hn1 _ (rfl : vtx n a = vtx n a) v1, pkR_planar_comm n _ (a + 1) 1, pkR_planar_comm n _ a 1,
    pkR_chA_planar hn d₁ ha (le_of_lt hab) le_rfl,
    pkR_chA_planar hn d₁ (i := 1) (j := a + 1) le_rfl (by omega) (by omega),
    pkR_chA_planar hn d₁ (i := 1) (j := a) le_rfl ha (by omega),
    pkR_chA_planar hn d₁ (i := a + 1) (j := n) (by omega) (by omega) le_rfl]
  have e3 : pkR_chA n d₁ (1, a) = 0 := by
    rw [pkR_chA_def]
    split_ifs <;> (try omega) <;> norm_num
  have e4 : pkR_chA n d₁ (a + 1, n) = 0 := by
    rw [pkR_chA_def]
    split_ifs <;> (try omega) <;> norm_num
  rw [e3, e4, pkR_chA_def, pkR_chA_def, ite_eq_right (show ¬ (a = 1 ∧ n = n - 1) by omega),
    ite_eq_left (show 1 % 2 = 1 by norm_num)]
  split_ifs <;> (try omega) <;> norm_num

/-- Same-parity tiles of the chain point: `c⋆` and `c⋆′` are `1`, all others `0`. -/
theorem pkR_chA_mesh {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ : ℕ} (hd : 2 * d₁ + 2 ≤ n) {a b : ℕ} (ha : 1 ≤ a)
    (hab : a < b) (hb : b ≤ n) (hp : a % 2 = b % 2) :
    mesh n (pkR_chA n d₁) a b = (if a = 1 ∧ b = n - 1 then 1 else 0) +
      (if (d₁ = 0 ∧ a = 2 ∧ b = n) ∨ (d₁ ≠ 0 ∧ a = 2 * d₁ ∧ b = 2 * d₁ + 2) then 1 else 0) := by
  rcases (show b < n ∨ b = n by omega) with hb' | hb'
  · exact pkR_chA_mesh_lt hE hn ha hab hb' hp
  · subst hb'
    exact pkR_chA_mesh_n hE hn hd ha hab hp

/-- **`x ≢ 0` on `Λ`** (PREFORM-Res §4.3 step 1; K5 (W-ind)-type): the chain point lies on `Λ` of the standard polygon
`(n, d₁)` with `x = c⋆ = 1`. -/
theorem pkR_xwit {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) (d₁ : ℕ) (hd : 2 * d₁ + 2 ≤ n) :
    pkR_lam n d₁ ∅ (pkR_chA n d₁) ∧ mesh n (pkR_chA n d₁) 1 (n - 1) = 1 := by
  have ec : pkR_cstp n d₁ = if d₁ = 0 then (2, n) else (2 * d₁, 2 * d₁ + 2) := rfl
  have hx : mesh n (pkR_chA n d₁) 1 (n - 1) = 1 := by
    rw [pkR_chA_mesh hE hn hd le_rfl (by omega) (by omega) (by omega)]
    split_ifs <;> (try omega) <;> norm_num
  refine ⟨⟨?_, ?_, fun Q hQ => by simp at hQ⟩, hx⟩
  · intro a ha b hb hab hp h1 h2
    rw [mem_Icc] at ha hb
    rw [pkR_chA_mesh hE hn hd ha.1 (by omega) hb.2 hp]
    have h1' : ¬ (a = 1 ∧ b = n - 1) := fun hc => h1 (by rw [hc.1, hc.2])
    have h2' : ¬ ((d₁ = 0 ∧ a = 2 ∧ b = n) ∨ (d₁ ≠ 0 ∧ a = 2 * d₁ ∧ b = 2 * d₁ + 2)) := by
      rintro (hc | hc)
      · exact h2 (by rw [ec, ite_eq_left hc.1, hc.2.1, hc.2.2])
      · exact h2 (by rw [ec, ite_eq_right hc.1, hc.2.1, hc.2.2])
    rw [ite_eq_right h1', ite_eq_right h2']
    norm_num
  · rw [hx, ec]
    split_ifs with h0
    · dsimp only
      rw [pkR_chA_mesh hE hn hd (by omega) (by omega) le_rfl (by omega)]
      split_ifs <;> (try omega) <;> norm_num
    · dsimp only
      rw [pkR_chA_mesh hE hn hd (by omega) (by omega) hd (by omega)]
      split_ifs <;> (try omega) <;> norm_num

/-- The 4-gon identity behind R10(i): for the consecutive 4-gon `[a, a + 1, a + 2, a + 3]` (no wrap),
`X_{a,a+2} + X_{a+1,a+3} − X_{a,a+3} = c_{a,a+2}`. -/
theorem pkR_quad {K : Type*} [Field K] {n : ℕ} (X : ℕ × ℕ → K) {a : ℕ} (ha : 1 ≤ a) (h3 : a + 3 ≤ n) :
    planar n X a (a + 2) + planar n X (a + 1) (a + 3) - planar n X a (a + 3) = mesh n X a (a + 2) := by
  have hs : planar n X (a + 1) (a + 2) = 0 := planar_side X (i := a + 1) (by omega) (by omega)
  rw [pkR_mesh_def, show a + 2 + 1 = a + 3 from rfl, hs]
  ring

/-- **R10(i)** (PREFORM-Res §4.4, K9): on `Λ^I` of the standard polygon (`n ≥ 6`, `d₁ ≥ 1`), the 4-gon
`R̂′ = [2d₁ − 1, 2d₁, 2d₁ + 1, 2d₁ + 2]` satisfies `X_{2d₁−1,2d₁+1} + X_{2d₁,2d₁+2} = X_{2d₁−1,2d₁+2}` (the defect is the
odd–odd tile straddling leg `2d₁`, zero on `Λ`). -/
theorem pkR_R10i {n : ℕ} (hn : 6 ≤ n) {d₁ : ℕ} (hd1 : 1 ≤ d₁) (hd : 2 * d₁ + 2 ≤ n) {I : Finset (ℕ × ℕ)}
    {X : ℕ × ℕ → ℚ} (hX : pkR_lam n d₁ I X) :
    planar n X (2 * d₁ - 1) (2 * d₁ + 1) + planar n X (2 * d₁) (2 * d₁ + 2) = planar n X (2 * d₁ - 1) (2 * d₁ + 2) := by
  have e := pkR_quad (n := n) X (a := 2 * d₁ - 1) (by omega) (by omega)
  rw [show 2 * d₁ - 1 + 2 = 2 * d₁ + 1 by omega, show 2 * d₁ - 1 + 1 = 2 * d₁ by omega,
    show 2 * d₁ - 1 + 3 = 2 * d₁ + 2 by omega] at e
  have ec : pkR_cstp n d₁ = (2 * d₁, 2 * d₁ + 2) := ite_eq_right (by omega)
  have hz := hX.1 (2 * d₁ - 1) (mem_Icc.2 ⟨by omega, by omega⟩) (2 * d₁ + 1) (mem_Icc.2 ⟨by omega, by omega⟩)
    (by omega) (by omega) (fun hc => by rw [Prod.mk.injEq] at hc; omega)
    (fun hc => by rw [ec, Prod.mk.injEq] at hc; omega)
  rw [hz] at e
  linarith

/-- **R10(i), mirrored** (b″ route when `d₁ = 0`, K9b; stated for every `d₁`): the 4-gon `[2d₁ + 1, …, 2d₁ + 4]`
satisfies `X_{2d₁+1,2d₁+3} + X_{2d₁+2,2d₁+4} = X_{2d₁+1,2d₁+4}` on `Λ^I` (`n ≥ 6`, `2d₁ + 4 ≤ n`). -/
theorem pkR_R10i_mirror {n : ℕ} (hn : 6 ≤ n) {d₁ : ℕ} (hd : 2 * d₁ + 4 ≤ n) {I : Finset (ℕ × ℕ)}
    {X : ℕ × ℕ → ℚ} (hX : pkR_lam n d₁ I X) :
    planar n X (2 * d₁ + 1) (2 * d₁ + 3) + planar n X (2 * d₁ + 2) (2 * d₁ + 4) =
      planar n X (2 * d₁ + 1) (2 * d₁ + 4) := by
  have e := pkR_quad (n := n) X (a := 2 * d₁ + 1) (by omega) (by omega)
  have ec : pkR_cstp n d₁ = if d₁ = 0 then (2, n) else (2 * d₁, 2 * d₁ + 2) := rfl
  have hz := hX.1 (2 * d₁ + 1) (mem_Icc.2 ⟨by omega, by omega⟩) (2 * d₁ + 3) (mem_Icc.2 ⟨by omega, by omega⟩)
    (by omega) (by omega) (fun hc => by rw [Prod.mk.injEq] at hc; omega)
    (fun hc => by
      rw [ec] at hc
      split_ifs at hc <;> rw [Prod.mk.injEq] at hc <;> omega)
  rw [hz] at e
  linarith

-- c1b (R12-P7b-pkgRes-c1b): [XQ] / [Region](i), W_q, (W-ind), (G_W)

/-- [XQ] integrand (c1b): `[E a, a < b] c + [E b, a < b] c − [a, b ∈ A, a < b] c` with `A = [p, q − 1]` and `E` = even legs of
`A`; its double sum over `1..n` is `X_{p,q}` (`pkR_XQ_sum`: [RowSum] − [ArcX]). -/
def pkR_xqF (n : ℕ) (X : ℕ × ℕ → ℚ) (p q a b : ℕ) : ℚ :=
  (if (a % 2 = 0 ∧ p ≤ a ∧ a ≤ q - 1) ∧ a < b then mesh n X a b else 0) +
    (if (b % 2 = 0 ∧ p ≤ b ∧ b ≤ q - 1) ∧ a < b then mesh n X a b else 0) -
      (if p ≤ a ∧ a < b ∧ b ≤ q - 1 then mesh n X a b else 0)

theorem pkR_xqF_def (n : ℕ) (X : ℕ × ℕ → ℚ) (p q a b : ℕ) : pkR_xqF n X p q a b =
    (if (a % 2 = 0 ∧ p ≤ a ∧ a ≤ q - 1) ∧ a < b then mesh n X a b else 0) +
      (if (b % 2 = 0 ∧ p ≤ b ∧ b ≤ q - 1) ∧ a < b then mesh n X a b else 0) -
        (if p ≤ a ∧ a < b ∧ b ≤ q - 1 then mesh n X a b else 0) := rfl

/-- `X_{p,q} = Σ_a Σ_b F(a, b)` for every point (`1 ≤ p`, `p + 1 ≤ q ≤ n`). -/
theorem pkR_XQ_sum {n : ℕ} (hn : 2 ≤ n) (X : ℕ × ℕ → ℚ) {p q : ℕ} (hp : 1 ≤ p) (hpq : p + 1 ≤ q) (hq : q ≤ n) :
    planar n X p q = Finset.sum (Icc 1 n) (fun a => Finset.sum (Icc 1 n) (fun b => pkR_xqF n X p q a b)) := by
  have T := pkL_tri (N := n) hn X (u := p) (v := q - 1) hp (by omega) (by omega)
  have R := pkL_rows (N := n) hn X (fun a => a % 2 = 0 ∧ p ≤ a ∧ a ≤ q - 1)
  rw [show q - 1 + 1 = q by omega] at T
  have e : Finset.sum (Icc 1 n) (fun a => Finset.sum (Icc 1 n) (fun b => pkR_xqF n X p q a b)) =
      Finset.sum (Icc 1 n) (fun a => Finset.sum (Icc 1 n) (fun b =>
        ((if (a % 2 = 0 ∧ p ≤ a ∧ a ≤ q - 1) ∧ a < b then mesh n X a b else 0) +
          (if (b % 2 = 0 ∧ p ≤ b ∧ b ≤ q - 1) ∧ a < b then mesh n X a b else 0)))) -
      Finset.sum (Icc 1 n) (fun a => Finset.sum (Icc 1 n) (fun b =>
        (if p ≤ a ∧ a < b ∧ b ≤ q - 1 then mesh n X a b else 0))) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl (fun a _ => ?_)
    rw [← sum_sub_distrib]
    exact sum_congr rfl (fun b _ => pkR_xqF_def n X p q a b)
  rw [e, T, R]
  ring

/-- Pointwise value of the [XQ] integrand on `Λ` of the standard polygon with `minrect(Q) = 0`: only `c⋆′` survives. -/
theorem pkR_XQ_pt {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ i j : ℕ} (hi : i ≤ d₁) (hj : 2 * d₁ + 2 * j + 2 ≤ n)
    (hb : ¬ (i = d₁ ∧ j = 0)) (ha : ¬ (i = 0 ∧ 2 * d₁ + 2 * j + 2 = n)) {X : ℕ × ℕ → ℚ}
    (hsp : ∀ a ∈ Icc 1 n, ∀ b ∈ Icc 1 n, a + 2 ≤ b → a % 2 = b % 2 → (a, b) ≠ (1, n - 1) →
      (a, b) ≠ pkR_cstp n d₁ → mesh n X a b = 0)
    (hmr : ∀ t ∈ pkR_minrect n d₁ (i, j), mesh n X t.1 t.2 = 0) {a b : ℕ} (ha1 : a ∈ Icc 1 n) (hb1 : b ∈ Icc 1 n) :
    pkR_xqF n X (2 * i + 1) (2 * d₁ + 2 * j + 2) a b =
      if a = (pkR_cstp n d₁).1 ∧ b = (pkR_cstp n d₁).2 then mesh n X a b else 0 := by
  rw [pkR_xqF_def]
  by_cases hc : mesh n X a b = 0
  · rw [hc]
    simp only [ite_self]
    ring
  have ec : pkR_cstp n d₁ = if d₁ = 0 then (2, n) else (2 * d₁, 2 * d₁ + 2) := rfl
  have ha' := mem_Icc.1 ha1
  have hb' := mem_Icc.1 hb1
  -- facts from c ≠ 0
  have f1 : ¬ (a + 2 ≤ b ∧ a % 2 = b % 2 ∧ ¬ (a = 1 ∧ b = n - 1) ∧
      ¬ (a = (pkR_cstp n d₁).1 ∧ b = (pkR_cstp n d₁).2)) := by
    rintro ⟨h1, h2, h3, h4⟩
    exact hc (hsp a ha1 b hb1 h1 h2 (fun e => h3 ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩)
      (fun e => h4 ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩))
  have f2 : ¬ (a % 2 = 1 ∧ a ≠ 2 * d₁ + 1 ∧ ¬ (2 * i + 1 ≤ a ∧ a ≤ 2 * d₁ + 2 * j + 1) ∧
      b % 2 = 0 ∧ b ≠ n ∧ (2 * i + 1 ≤ b ∧ b ≤ 2 * d₁ + 2 * j + 1)) := by
    rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine hc (hmr (a, b) ?_)
    rw [pkR_mem_minrect, pkR_mem_head, pkR_mem_head]
    exact ⟨⟨ha1, h1, h2, h3⟩, ⟨hb1, h4, h5, h6⟩⟩
  have f3 : ¬ (b % 2 = 1 ∧ b ≠ 2 * d₁ + 1 ∧ ¬ (2 * i + 1 ≤ b ∧ b ≤ 2 * d₁ + 2 * j + 1) ∧
      a % 2 = 0 ∧ a ≠ n ∧ (2 * i + 1 ≤ a ∧ a ≤ 2 * d₁ + 2 * j + 1)) := by
    rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine hc ?_
    rw [pkR_mesh_comm]
    refine hmr (b, a) ?_
    rw [pkR_mem_minrect, pkR_mem_head, pkR_mem_head]
    exact ⟨⟨hb1, h1, h2, h3⟩, ⟨ha1, h4, h5, h6⟩⟩
  rw [ec] at f1 ⊢
  by_cases h0 : d₁ = 0
  · rw [ite_eq_left h0] at f1 ⊢
    dsimp only at f1 ⊢
    split_ifs <;> (try omega) <;> ring
  · rw [ite_eq_right h0] at f1 ⊢
    dsimp only at f1 ⊢
    split_ifs <;> (try omega) <;> ring

/-- **[XQ] / [Region](i)** (PREFORM-Res §3.3, R11(i), K4b): on `Λ^I` of the standard polygon, a member `Q = (i, j)` with
`minrect(Q) = 0` has `X_Q = x` (`= c⋆ = c⋆′`). Stated for the planar variable of the member chord `(2i + 1, 2d₁ + 2j + 2)`. -/
theorem pkR_XQ {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ i j : ℕ} (hi : i ≤ d₁) (hj : 2 * d₁ + 2 * j + 2 ≤ n)
    (hb : ¬ (i = d₁ ∧ j = 0)) (ha : ¬ (i = 0 ∧ 2 * d₁ + 2 * j + 2 = n)) {I : Finset (ℕ × ℕ)} {X : ℕ × ℕ → ℚ}
    (hX : pkR_lam n d₁ I X) (hmr : ∀ t ∈ pkR_minrect n d₁ (i, j), mesh n X t.1 t.2 = 0) :
    planar n X (2 * i + 1) (2 * d₁ + 2 * j + 2) = mesh n X 1 (n - 1) := by
  rw [pkR_XQ_sum (by omega) X (by omega) (by omega) hj]
  have ec : pkR_cstp n d₁ = if d₁ = 0 then (2, n) else (2 * d₁, 2 * d₁ + 2) := rfl
  have hP1 : (pkR_cstp n d₁).1 ∈ Icc 1 n := by
    rw [ec, mem_Icc]
    split_ifs <;> (dsimp only) <;> omega
  have hP2 : (pkR_cstp n d₁).2 ∈ Icc 1 n := by
    rw [ec, mem_Icc]
    split_ifs <;> (dsimp only) <;> omega
  rw [sum_congr rfl (fun a ha1 => sum_congr rfl (fun b hb1 =>
    pkR_XQ_pt hE hn hi hj hb ha hX.1 hmr ha1 hb1))]
  have e1 : ∀ a, Finset.sum (Icc 1 n) (fun b => if a = (pkR_cstp n d₁).1 ∧ b = (pkR_cstp n d₁).2 then mesh n X a b else 0) =
      if a = (pkR_cstp n d₁).1 then mesh n X a (pkR_cstp n d₁).2 else 0 := by
    intro a
    by_cases h : a = (pkR_cstp n d₁).1
    · rw [ite_eq_left h]
      simp only [h, true_and]
      rw [sum_ite_eq' (Icc 1 n) (pkR_cstp n d₁).2 (fun b => mesh n X (pkR_cstp n d₁).1 b), ite_eq_left hP2]
    · rw [ite_eq_right h]
      simp only [h, false_and, ite_false, sum_const_zero]
  rw [sum_congr rfl (fun a _ => e1 a), sum_ite_eq' (Icc 1 n) (pkR_cstp n d₁).1
    (fun a => mesh n X a (pkR_cstp n d₁).2), ite_eq_left hP1]
  exact hX.2.1.symm

/-- `τ_q` of the standard member `q = (i, j)`: the odd–odd tile of the two end legs of `A_q` (PREFORM-Res §3.4). -/
def pkR_tau (d₁ : ℕ) (Q : ℕ × ℕ) : ℕ × ℕ := (2 * Q.1 + 1, 2 * d₁ + 2 * Q.2 + 1)

/-- **W_q** (PREFORM-Res §3.4, R13): same-parity tiles vanish except `c⋆`, `c⋆′`, `τ_q`; `minrect(q)` tiles vanish. -/
def pkR_W (n d₁ : ℕ) (Q : ℕ × ℕ) (X : ℕ × ℕ → ℚ) : Prop :=
  (∀ a ∈ Icc 1 n, ∀ b ∈ Icc 1 n, a + 2 ≤ b → a % 2 = b % 2 → (a, b) ≠ (1, n - 1) → (a, b) ≠ pkR_cstp n d₁ →
      (a, b) ≠ pkR_tau d₁ Q → mesh n X a b = 0) ∧
  ∀ t ∈ pkR_minrect n d₁ Q, mesh n X t.1 t.2 = 0

theorem pkR_W_iff (n d₁ : ℕ) (Q : ℕ × ℕ) (X : ℕ × ℕ → ℚ) : pkR_W n d₁ Q X ↔
    (∀ a ∈ Icc 1 n, ∀ b ∈ Icc 1 n, a + 2 ≤ b → a % 2 = b % 2 → (a, b) ≠ (1, n - 1) → (a, b) ≠ pkR_cstp n d₁ →
      (a, b) ≠ pkR_tau d₁ Q → mesh n X a b = 0) ∧
    ∀ t ∈ pkR_minrect n d₁ Q, mesh n X t.1 t.2 = 0 := Iff.rfl

/-- The symmetric unit matrix on the pair `{u, v}` (a Gram-matrix building block). -/
def pkR_E (u v : ℕ) : ℕ → ℕ → ℚ := fun a b => if (a = u ∧ b = v) ∨ (a = v ∧ b = u) then 1 else 0

theorem pkR_E_def (u v a b : ℕ) : pkR_E u v a b = if (a = u ∧ b = v) ∨ (a = v ∧ b = u) then 1 else 0 := rfl

theorem pkR_E_symm (u v a b : ℕ) : pkR_E u v a b = pkR_E u v b a := by
  rw [pkR_E_def, pkR_E_def]
  split_ifs <;> (try omega) <;> norm_num

theorem pkR_E_diag {u v : ℕ} (h : u ≠ v) (a : ℕ) : pkR_E u v a a = 0 := by
  rw [pkR_E_def]
  exact ite_eq_right (by omega)

theorem pkR_sum_ind {n v : ℕ} (hv : v ∈ Icc 1 n) :
    Finset.sum (Icc 1 n) (fun b => if b = v then (1 : ℚ) else 0) = 1 := by
  rw [sum_ite_eq', ite_eq_left hv]

theorem pkR_E_zero {u v a b : ℕ} (h : ¬ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) : pkR_E u v a b = 0 := ite_eq_right h

theorem pkR_E_one {u v a b : ℕ} (h : (a = u ∧ b = v) ∨ (a = v ∧ b = u)) : pkR_E u v a b = 1 := ite_eq_left h

theorem pkR_E_row {n u v : ℕ} (hu : u ∈ Icc 1 n) (hv : v ∈ Icc 1 n) (h : u ≠ v) (a : ℕ) :
    Finset.sum (Icc 1 n) (fun b => pkR_E u v a b) = (if a = u then 1 else 0) + (if a = v then 1 else 0) := by
  have e : ∀ b, pkR_E u v a b = (if a = u then 1 else 0) * (if b = v then 1 else 0) +
      (if a = v then 1 else 0) * (if b = u then 1 else 0) := by
    intro b
    rw [pkR_E_def]
    split_ifs <;> (try omega) <;> norm_num
  rw [sum_congr rfl (fun b _ => e b), sum_add_distrib, ← mul_sum, ← mul_sum, pkR_sum_ind hv, pkR_sum_ind hu]
  ring

theorem pkR_ne_pair {a b c d : ℕ} (h : (a, b) ≠ (c, d)) : ¬ (a = c ∧ b = d) := fun e => h (by rw [e.1, e.2])

/-- (W-ind) witness 1: `C = E(e₁, e₂) + E(t₁, t₂) − E(e₁, t₁) − E(e₂, t₂)` (`c⋆′ = τ = 1`, `c⋆ = 0`). -/
def pkR_w1 (e1 e2 t1 t2 : ℕ) : ℕ → ℕ → ℚ := fun a b =>
  pkR_E e1 e2 a b + pkR_E t1 t2 a b - pkR_E e1 t1 a b - pkR_E e2 t2 a b

theorem pkR_w1_def (e1 e2 t1 t2 a b : ℕ) : pkR_w1 e1 e2 t1 t2 a b =
    pkR_E e1 e2 a b + pkR_E t1 t2 a b - pkR_E e1 t1 a b - pkR_E e2 t2 a b := rfl

/-- (W-ind) witness 2 (`s = n`): `C = E(1, n−1) − E(t₁, t₂) − E(1, n) − E(n−1, n) + E(t₁, n) + E(t₂, n)`
(`c⋆ = 1`, `c⋆′ = 0`, `τ = −1`). -/
def pkR_w2 (n t1 t2 : ℕ) : ℕ → ℕ → ℚ := fun a b =>
  pkR_E 1 (n - 1) a b - pkR_E t1 t2 a b - pkR_E 1 n a b - pkR_E (n - 1) n a b + pkR_E t1 n a b + pkR_E t2 n a b

theorem pkR_w2_def (n t1 t2 a b : ℕ) : pkR_w2 n t1 t2 a b =
    pkR_E 1 (n - 1) a b - pkR_E t1 t2 a b - pkR_E 1 n a b - pkR_E (n - 1) n a b + pkR_E t1 n a b +
      pkR_E t2 n a b := rfl

theorem pkR_w1_gram {n e1 e2 t1 t2 : ℕ} (hn : 1 ≤ n) (h1 : e1 ∈ Icc 1 n) (h2 : e2 ∈ Icc 1 n) (h3 : t1 ∈ Icc 1 n)
    (h4 : t2 ∈ Icc 1 n) (d12 : e1 ≠ e2) (d34 : t1 ≠ t2) (d13 : e1 ≠ t1) (d24 : e2 ≠ t2) {a b : ℕ}
    (ha : a ∈ Icc 1 n) (hb : b ∈ Icc 1 n) (hab : a ≠ b) :
    mesh n (pkR_gramPt (pkR_w1 e1 e2 t1 t2)) a b = pkR_w1 e1 e2 t1 t2 a b := by
  refine pkR_gram hn _ (fun a b => ?_) (fun a => ?_) (fun a _ => ?_) ha hb hab
  · rw [pkR_w1_def, pkR_w1_def, pkR_E_symm e1 e2 a b, pkR_E_symm t1 t2 a b, pkR_E_symm e1 t1 a b,
      pkR_E_symm e2 t2 a b]
  · rw [pkR_w1_def, pkR_E_diag d12, pkR_E_diag d34, pkR_E_diag d13, pkR_E_diag d24]
    ring
  · have e : Finset.sum (Icc 1 n) (fun b => pkR_w1 e1 e2 t1 t2 a b) =
        Finset.sum (Icc 1 n) (fun b => pkR_E e1 e2 a b) + Finset.sum (Icc 1 n) (fun b => pkR_E t1 t2 a b) -
          Finset.sum (Icc 1 n) (fun b => pkR_E e1 t1 a b) - Finset.sum (Icc 1 n) (fun b => pkR_E e2 t2 a b) := by
      rw [← sum_add_distrib, ← sum_sub_distrib, ← sum_sub_distrib]
      exact sum_congr rfl (fun b _ => pkR_w1_def e1 e2 t1 t2 a b)
    rw [e, pkR_E_row h1 h2 d12, pkR_E_row h3 h4 d34, pkR_E_row h1 h3 d13, pkR_E_row h2 h4 d24]
    ring

theorem pkR_w2_gram {n t1 t2 : ℕ} (hn : 4 ≤ n) (h3 : t1 ∈ Icc 1 n) (h4 : t2 ∈ Icc 1 n) (d34 : t1 ≠ t2)
    (d3 : t1 ≠ n) (d4 : t2 ≠ n) {a b : ℕ} (ha : a ∈ Icc 1 n) (hb : b ∈ Icc 1 n) (hab : a ≠ b) :
    mesh n (pkR_gramPt (pkR_w2 n t1 t2)) a b = pkR_w2 n t1 t2 a b := by
  have i1 : 1 ∈ Icc 1 n := mem_Icc.2 ⟨le_rfl, by omega⟩
  have i2 : n - 1 ∈ Icc 1 n := mem_Icc.2 ⟨by omega, by omega⟩
  have i3 : n ∈ Icc 1 n := mem_Icc.2 ⟨by omega, le_rfl⟩
  have x1 : 1 ≠ n - 1 := by omega
  have x2 : 1 ≠ n := by omega
  have x3 : n - 1 ≠ n := by omega
  refine pkR_gram (by omega) _ (fun a b => ?_) (fun a => ?_) (fun a _ => ?_) ha hb hab
  · rw [pkR_w2_def, pkR_w2_def, pkR_E_symm 1 (n - 1) a b, pkR_E_symm t1 t2 a b, pkR_E_symm 1 n a b,
      pkR_E_symm (n - 1) n a b, pkR_E_symm t1 n a b, pkR_E_symm t2 n a b]
  · rw [pkR_w2_def, pkR_E_diag x1, pkR_E_diag d34, pkR_E_diag x2, pkR_E_diag x3, pkR_E_diag d3, pkR_E_diag d4]
    ring
  · have e : Finset.sum (Icc 1 n) (fun b => pkR_w2 n t1 t2 a b) =
        Finset.sum (Icc 1 n) (fun b => pkR_E 1 (n - 1) a b) - Finset.sum (Icc 1 n) (fun b => pkR_E t1 t2 a b) -
          Finset.sum (Icc 1 n) (fun b => pkR_E 1 n a b) - Finset.sum (Icc 1 n) (fun b => pkR_E (n - 1) n a b) +
          Finset.sum (Icc 1 n) (fun b => pkR_E t1 n a b) + Finset.sum (Icc 1 n) (fun b => pkR_E t2 n a b) := by
      rw [← sum_sub_distrib, ← sum_sub_distrib, ← sum_sub_distrib, ← sum_add_distrib, ← sum_add_distrib]
      exact sum_congr rfl (fun b _ => pkR_w2_def n t1 t2 a b)
    rw [e, pkR_E_row i1 i2 x1, pkR_E_row h3 h4 d34, pkR_E_row i1 i3 x2, pkR_E_row i2 i3 x3, pkR_E_row h3 i3 d3,
      pkR_E_row h4 i3 d4]
    ring

/-- **(W-ind), first half** (PREFORM-Res §3.4, R8): on `W_q` of the standard polygon there is a point with `c⋆ = 0` and
`c⋆′ ≠ 0` (a Gram point with four entries; `q = (i, j)` a member). -/
theorem pkR_Wind1 {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ i j : ℕ} (hi : i ≤ d₁) (hj : 2 * d₁ + 2 * j + 2 ≤ n)
    (hb : ¬ (i = d₁ ∧ j = 0)) (ha : ¬ (i = 0 ∧ 2 * d₁ + 2 * j + 2 = n)) :
    ∃ X : ℕ × ℕ → ℚ, pkR_W n d₁ (i, j) X ∧ mesh n X 1 (n - 1) = 0 ∧
      mesh n X (pkR_cstp n d₁).1 (pkR_cstp n d₁).2 ≠ 0 := by
  have ec : pkR_cstp n d₁ = if d₁ = 0 then (2, n) else (2 * d₁, 2 * d₁ + 2) := rfl
  have et : pkR_tau d₁ (i, j) = (2 * i + 1, 2 * d₁ + 2 * j + 1) := rfl
  obtain ⟨e1, e2, he⟩ : ∃ e1 e2 : ℕ, pkR_cstp n d₁ = (e1, e2) := ⟨_, _, rfl⟩
  have he' : (d₁ = 0 ∧ e1 = 2 ∧ e2 = n) ∨ (d₁ ≠ 0 ∧ e1 = 2 * d₁ ∧ e2 = 2 * d₁ + 2) := by
    rw [ec] at he
    split_ifs at he with h0
    · rw [Prod.mk.injEq] at he
      omega
    · rw [Prod.mk.injEq] at he
      omega
  rw [he]
  dsimp only
  have G : ∀ {a b : ℕ}, a ∈ Icc 1 n → b ∈ Icc 1 n → a ≠ b →
      mesh n (pkR_gramPt (pkR_w1 e1 e2 (2 * i + 1) (2 * d₁ + 2 * j + 1))) a b =
        pkR_w1 e1 e2 (2 * i + 1) (2 * d₁ + 2 * j + 1) a b := fun ha hb hab =>
    pkR_w1_gram (by omega) (mem_Icc.2 ⟨by omega, by omega⟩) (mem_Icc.2 ⟨by omega, by omega⟩)
      (mem_Icc.2 ⟨by omega, by omega⟩) (mem_Icc.2 ⟨by omega, by omega⟩) (by omega) (by omega) (by omega) (by omega)
      ha hb hab
  refine ⟨pkR_gramPt (pkR_w1 e1 e2 (2 * i + 1) (2 * d₁ + 2 * j + 1)), ⟨?_, ?_⟩, ?_, ?_⟩
  · intro a ha1 b hb1 hab hp h1 h2 h3
    rw [he] at h2
    rw [et] at h3
    have h1' := pkR_ne_pair h1
    have h2' := pkR_ne_pair h2
    have h3' := pkR_ne_pair h3
    have ha' := mem_Icc.1 ha1
    have hb' := mem_Icc.1 hb1
    rw [G ha1 hb1 (by omega), pkR_w1_def, pkR_E_zero (by omega), pkR_E_zero (by omega), pkR_E_zero (by omega), pkR_E_zero (by omega)]
    ring
  · intro t ht
    rw [pkR_mem_minrect, pkR_mem_head, pkR_mem_head] at ht
    obtain ⟨⟨w1, w2, w3, w4⟩, ⟨c1, c2, c3, c4⟩⟩ := ht
    dsimp only at w4 c4
    have w1' := mem_Icc.1 w1
    have c1' := mem_Icc.1 c1
    rw [G w1 c1 (by omega), pkR_w1_def, pkR_E_zero (by omega), pkR_E_zero (by omega), pkR_E_zero (by omega), pkR_E_zero (by omega)]
    ring
  · rw [G (mem_Icc.2 ⟨le_rfl, by omega⟩) (mem_Icc.2 ⟨by omega, by omega⟩) (by omega), pkR_w1_def, pkR_E_zero (by omega),
      pkR_E_zero (by omega), pkR_E_zero (by omega), pkR_E_zero (by omega)]
    ring
  · rw [G (mem_Icc.2 ⟨by omega, by omega⟩) (mem_Icc.2 ⟨by omega, by omega⟩) (by omega), pkR_w1_def,
      pkR_E_one (by omega), pkR_E_zero (by omega), pkR_E_zero (by omega), pkR_E_zero (by omega)]
    norm_num

/-- **(W-ind), second half**: on `W_q` there is a point with `c⋆′ = 0` and `c⋆ ≠ 0`. -/
theorem pkR_Wind2 {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ i j : ℕ} (hi : i ≤ d₁) (hj : 2 * d₁ + 2 * j + 2 ≤ n)
    (hb : ¬ (i = d₁ ∧ j = 0)) (ha : ¬ (i = 0 ∧ 2 * d₁ + 2 * j + 2 = n)) :
    ∃ X : ℕ × ℕ → ℚ, pkR_W n d₁ (i, j) X ∧ mesh n X 1 (n - 1) ≠ 0 ∧
      mesh n X (pkR_cstp n d₁).1 (pkR_cstp n d₁).2 = 0 := by
  have ec : pkR_cstp n d₁ = if d₁ = 0 then (2, n) else (2 * d₁, 2 * d₁ + 2) := rfl
  have et : pkR_tau d₁ (i, j) = (2 * i + 1, 2 * d₁ + 2 * j + 1) := rfl
  obtain ⟨e1, e2, he⟩ : ∃ e1 e2 : ℕ, pkR_cstp n d₁ = (e1, e2) := ⟨_, _, rfl⟩
  have he' : (d₁ = 0 ∧ e1 = 2 ∧ e2 = n) ∨ (d₁ ≠ 0 ∧ e1 = 2 * d₁ ∧ e2 = 2 * d₁ + 2) := by
    rw [ec] at he
    split_ifs at he with h0
    · rw [Prod.mk.injEq] at he
      omega
    · rw [Prod.mk.injEq] at he
      omega
  rw [he]
  dsimp only
  have G : ∀ {a b : ℕ}, a ∈ Icc 1 n → b ∈ Icc 1 n → a ≠ b →
      mesh n (pkR_gramPt (pkR_w2 n (2 * i + 1) (2 * d₁ + 2 * j + 1))) a b =
        pkR_w2 n (2 * i + 1) (2 * d₁ + 2 * j + 1) a b := fun ha hb hab =>
    pkR_w2_gram hn (mem_Icc.2 ⟨by omega, by omega⟩) (mem_Icc.2 ⟨by omega, by omega⟩) (by omega) (by omega) (by omega)
      ha hb hab
  refine ⟨pkR_gramPt (pkR_w2 n (2 * i + 1) (2 * d₁ + 2 * j + 1)), ⟨?_, ?_⟩, ?_, ?_⟩
  · intro a ha1 b hb1 hab hp h1 h2 h3
    rw [he] at h2
    rw [et] at h3
    have h1' := pkR_ne_pair h1
    have h2' := pkR_ne_pair h2
    have h3' := pkR_ne_pair h3
    have ha' := mem_Icc.1 ha1
    have hb' := mem_Icc.1 hb1
    rw [G ha1 hb1 (by omega), pkR_w2_def, pkR_E_zero (by omega), pkR_E_zero (by omega), pkR_E_zero (by omega), pkR_E_zero (by omega), pkR_E_zero (by omega), pkR_E_zero (by omega)]
    ring
  · intro t ht
    rw [pkR_mem_minrect, pkR_mem_head, pkR_mem_head] at ht
    obtain ⟨⟨w1, w2, w3, w4⟩, ⟨c1, c2, c3, c4⟩⟩ := ht
    dsimp only at w4 c4
    have w1' := mem_Icc.1 w1
    have c1' := mem_Icc.1 c1
    rw [G w1 c1 (by omega), pkR_w2_def, pkR_E_zero (by omega), pkR_E_zero (by omega), pkR_E_zero (by omega), pkR_E_zero (by omega), pkR_E_zero (by omega), pkR_E_zero (by omega)]
    ring
  · rw [G (mem_Icc.2 ⟨le_rfl, by omega⟩) (mem_Icc.2 ⟨by omega, by omega⟩) (by omega), pkR_w2_def,
      pkR_E_one (by omega), pkR_E_zero (by omega), pkR_E_zero (by omega), pkR_E_zero (by omega), pkR_E_zero (by omega), pkR_E_zero (by omega)]
    norm_num
  · rw [G (mem_Icc.2 ⟨by omega, by omega⟩) (mem_Icc.2 ⟨by omega, by omega⟩) (by omega), pkR_w2_def,
      pkR_E_zero (by omega), pkR_E_zero (by omega), pkR_E_zero (by omega), pkR_E_zero (by omega), pkR_E_zero (by omega), pkR_E_zero (by omega)]
    ring

/-- Planar variables of a combination `X − t·Y`. -/
theorem pkR_planar_lc (n : ℕ) (X Y : ℕ × ℕ → ℚ) (t : ℚ) (i j : ℕ) :
    planar n (fun p => X p - t * Y p) i j = planar n X i j - t * planar n Y i j := by
  rw [pkR_planar_def, pkR_planar_def n X, pkR_planar_def n Y]
  split_ifs
  · rfl
  · ring

/-- Tiles of a combination `X − t·Y`. -/
theorem pkR_mesh_lc (n : ℕ) (X Y : ℕ × ℕ → ℚ) (t : ℚ) (a b : ℕ) :
    mesh n (fun p => X p - t * Y p) a b = mesh n X a b - t * mesh n Y a b := by
  rw [pkR_mesh_def, pkR_mesh_def n X, pkR_mesh_def n Y, pkR_planar_lc, pkR_planar_lc, pkR_planar_lc, pkR_planar_lc]
  ring

/-- `W_q` is closed under `X − t·Y`. -/
theorem pkR_W_lc {n d₁ : ℕ} {Q : ℕ × ℕ} {X Y : ℕ × ℕ → ℚ} (hX : pkR_W n d₁ Q X) (hY : pkR_W n d₁ Q Y) (t : ℚ) :
    pkR_W n d₁ Q (fun p => X p - t * Y p) := by
  refine ⟨fun a ha b hb h1 h2 h3 h4 h5 => ?_, fun u hu => ?_⟩
  · rw [pkR_mesh_lc, hX.1 a ha b hb h1 h2 h3 h4 h5, hY.1 a ha b hb h1 h2 h3 h4 h5]
    ring
  · rw [pkR_mesh_lc, hX.2 u hu, hY.2 u hu]
    ring

theorem pkR_elim {mA mB : ℚ} (hB : mB ≠ 0) : mA - mA / mB * mB = 0 := by
  rw [div_mul_eq_mul_div, mul_div_assoc, div_self hB]
  ring

/-- **(G^I) for `I = {q}`, core** (PREFORM-Res §3.5; R12 at a singleton): for a standard member `q = (i, j)` and a mixed
diagonal `Q` other than its chord, a two-level point has every same-parity tile `0`, `minrect(q) = 0` and `X_Q ≠ 0`. The
level jumps sit inside `A_q` (odd legs) or outside `A_q` (even legs), whichever separates `Q`. -/
theorem pkR_Gq_core {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ i j : ℕ} (hi : i ≤ d₁) (hj : 2 * d₁ + 2 * j + 2 ≤ n)
    (hb : ¬ (i = d₁ ∧ j = 0)) {Q : ℕ × ℕ} (hQ : Q ∈ oddDiagonals n) (hne : Q ≠ pkR_mchord d₁ (i, j)) :
    ∃ X : ℕ × ℕ → ℚ, (∀ a ∈ Icc 1 n, ∀ b ∈ Icc 1 n, a % 2 = b % 2 → mesh n X a b = 0) ∧
      (∀ t ∈ pkR_minrect n d₁ (i, j), mesh n X t.1 t.2 = 0) ∧ X Q ≠ 0 := by
  obtain ⟨p, q⟩ := Q
  have hQd := mem_filter.1 hQ
  rw [mem_diagonals] at hQd
  dsimp only at hQd
  have hne' : ¬ (p = 2 * i + 1 ∧ q = 2 * d₁ + 2 * j + 2) := fun hc => hne (by rw [hc.1, hc.2]; rfl)
  have fin : ∀ f h : ℕ → ℚ, f 0 = f (n / 2) → h 1 = h (n / 2 + 1) →
      (∀ w c : ℕ, w % 2 = 1 → c % 2 = 0 → (w < 2 * i + 1 ∨ 2 * d₁ + 2 * j + 1 < w) → 2 * i + 1 ≤ c →
        c ≤ 2 * d₁ + 2 * j + 1 → (f ((w + 1) / 2) - f (w / 2)) * (h (c / 2 + 1) - h (c / 2)) = 0) →
      f (q / 2) - f (p / 2) ≠ 0 → h ((q + 1) / 2) - h ((p + 1) / 2) ≠ 0 →
      ∃ X : ℕ × ℕ → ℚ, (∀ a ∈ Icc 1 n, ∀ b ∈ Icc 1 n, a % 2 = b % 2 → mesh n X a b = 0) ∧
        (∀ t ∈ pkR_minrect n d₁ (i, j), mesh n X t.1 t.2 = 0) ∧ X (p, q) ≠ 0 := by
    intro f h hf hh hz h1 h2
    refine ⟨pkR_fhPt f h, fun a ha b hb hp => pkR_fh_sp hE f h hf hh ha hb hp, fun t ht => ?_,
      pkR_fh_ne hQ f h h1 h2⟩
    rw [pkR_mem_minrect, pkR_mem_head, pkR_mem_head] at ht
    obtain ⟨⟨w1, w2, -, w4⟩, ⟨c1, c2, -, c4⟩⟩ := ht
    dsimp only at w4 c4
    rw [pkR_fh_mixed hE f h hf hh w1 c1 w2 c2, mul_assoc,
      hz t.1 t.2 w2 c2 (by omega) c4.1 c4.2]
    ring
  by_cases cA : i + 1 ≤ p / 2 ∧ p / 2 ≤ d₁ + j
  · refine fin (pkR_dlt (p / 2) 0 (n / 2)) (pkR_dlt ((q + 1) / 2) 1 (n / 2 + 1)) ?_ ?_ ?_ ?_ ?_
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num
    · intro w c hw hc hw' hc1 hc2
      rw [show pkR_dlt (p / 2) 0 (n / 2) ((w + 1) / 2) - pkR_dlt (p / 2) 0 (n / 2) (w / 2) = 0 by
        rw [pkR_dlt_def, pkR_dlt_def]
        split_ifs <;> (try omega) <;> norm_num]
      ring
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num
  by_cases cB : i + 1 ≤ q / 2 ∧ q / 2 ≤ d₁ + j
  · refine fin (pkR_dlt (q / 2) 0 (n / 2)) (pkR_dlt ((q + 1) / 2) 1 (n / 2 + 1)) ?_ ?_ ?_ ?_ ?_
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num
    · intro w c hw hc hw' hc1 hc2
      rw [show pkR_dlt (q / 2) 0 (n / 2) ((w + 1) / 2) - pkR_dlt (q / 2) 0 (n / 2) (w / 2) = 0 by
        rw [pkR_dlt_def, pkR_dlt_def]
        split_ifs <;> (try omega) <;> norm_num]
      ring
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num
  by_cases cC : (p + 1) / 2 < i + 1 ∨ d₁ + j + 1 < (p + 1) / 2
  · refine fin (pkR_dlt (p / 2) 0 (n / 2)) (pkR_dlt ((p + 1) / 2) 1 (n / 2 + 1)) ?_ ?_ ?_ ?_ ?_
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num
    · intro w c hw hc hw' hc1 hc2
      rw [show pkR_dlt ((p + 1) / 2) 1 (n / 2 + 1) (c / 2 + 1) - pkR_dlt ((p + 1) / 2) 1 (n / 2 + 1) (c / 2) = 0 by
        rw [pkR_dlt_def, pkR_dlt_def]
        split_ifs <;> (try omega) <;> norm_num]
      ring
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num
  · refine fin (pkR_dlt (p / 2) 0 (n / 2)) (pkR_dlt ((q + 1) / 2) 1 (n / 2 + 1)) ?_ ?_ ?_ ?_ ?_
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num
    · intro w c hw hc hw' hc1 hc2
      rw [show pkR_dlt ((q + 1) / 2) 1 (n / 2 + 1) (c / 2 + 1) - pkR_dlt ((q + 1) / 2) 1 (n / 2 + 1) (c / 2) = 0 by
        rw [pkR_dlt_def, pkR_dlt_def]
        split_ifs <;> (try omega) <;> norm_num]
      ring
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num
    · rw [pkR_dlt_def, pkR_dlt_def]
      split_ifs <;> (try omega) <;> norm_num

/-- **(G^I) at `I = {q}`** (PREFORM-Res §3.5): every mixed diagonal other than the chord of `q` is non-zero somewhere on
`Λ^{q}₀`. -/
theorem pkR_Gq {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ i j : ℕ} (hi : i ≤ d₁) (hj : 2 * d₁ + 2 * j + 2 ≤ n)
    (hb : ¬ (i = d₁ ∧ j = 0)) {Q : ℕ × ℕ} (hQ : Q ∈ oddDiagonals n) (hne : Q ≠ pkR_mchord d₁ (i, j)) :
    ∃ X : ℕ × ℕ → ℚ, pkR_lam n d₁ {(i, j)} X ∧ mesh n X 1 (n - 1) = 0 ∧ X Q ≠ 0 := by
  obtain ⟨X, h1, h2, h3⟩ := pkR_Gq_core hE hn hi hj hb hQ hne
  obtain ⟨l1, l2⟩ := pkR_lam_of_sp hE hn d₁ (by omega) h1
  refine ⟨X, pkR_lam_add l1 (fun Q' hQ' => ?_), l2, h3⟩
  rw [mem_singleton] at hQ'
  rw [hQ']
  exact h2

/-- The same point lies on `W_q` with `c⋆ = c⋆′ = 0` ((G_W): `X_Q ≢ 0` on `W_q ∩ {c⋆ = 0}` and on `W_q ∩ {c⋆′ = 0}`). -/
theorem pkR_GW_Q {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ i j : ℕ} (hi : i ≤ d₁) (hj : 2 * d₁ + 2 * j + 2 ≤ n)
    (hb : ¬ (i = d₁ ∧ j = 0)) {Q : ℕ × ℕ} (hQ : Q ∈ oddDiagonals n) (hne : Q ≠ pkR_mchord d₁ (i, j)) :
    ∃ X : ℕ × ℕ → ℚ, pkR_W n d₁ (i, j) X ∧ mesh n X 1 (n - 1) = 0 ∧
      mesh n X (pkR_cstp n d₁).1 (pkR_cstp n d₁).2 = 0 ∧ X Q ≠ 0 := by
  obtain ⟨X, h1, h2, h3⟩ := pkR_Gq_core hE hn hi hj hb hQ hne
  have ec : pkR_cstp n d₁ = if d₁ = 0 then (2, n) else (2 * d₁, 2 * d₁ + 2) := rfl
  refine ⟨X, ⟨fun a ha b hb _ hp _ _ _ => h1 a ha b hb hp, h2⟩,
    h1 1 (mem_Icc.2 ⟨le_rfl, by omega⟩) (n - 1) (mem_Icc.2 ⟨by omega, by omega⟩) (by omega), ?_, h3⟩
  rw [ec]
  split_ifs with h0
  · exact h1 2 (mem_Icc.2 ⟨by omega, by omega⟩) n (mem_Icc.2 ⟨by omega, le_rfl⟩) (by omega)
  · exact h1 (2 * d₁) (mem_Icc.2 ⟨by omega, by omega⟩) (2 * d₁ + 2) (mem_Icc.2 ⟨by omega, by omega⟩) (by omega)

/-- (G_W) non-proportionality, `X_Q` vs `c⋆`: a point of `W_q` with `X_Q = 0` and `c⋆ ≠ 0` (member `q`, mixed `Q` other
than its chord). -/
theorem pkR_GW_star {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ i j : ℕ} (hi : i ≤ d₁) (hj : 2 * d₁ + 2 * j + 2 ≤ n)
    (hb : ¬ (i = d₁ ∧ j = 0)) (ha : ¬ (i = 0 ∧ 2 * d₁ + 2 * j + 2 = n)) {Q : ℕ × ℕ} (hQ : Q ∈ oddDiagonals n)
    (hne : Q ≠ pkR_mchord d₁ (i, j)) :
    ∃ X : ℕ × ℕ → ℚ, pkR_W n d₁ (i, j) X ∧ X Q = 0 ∧ mesh n X 1 (n - 1) ≠ 0 := by
  obtain ⟨A, hA, hA1, -⟩ := pkR_Wind2 hE hn hi hj hb ha
  obtain ⟨B, hB, hB1, -, hB3⟩ := pkR_GW_Q hE hn hi hj hb hQ hne
  refine ⟨fun p => A p - A Q / B Q * B p, pkR_W_lc hA hB _, ?_, ?_⟩
  · show A Q - A Q / B Q * B Q = 0
    exact pkR_elim hB3
  · rw [pkR_mesh_lc, hB1]
    simpa using hA1

/-- (G_W) non-proportionality, `X_Q` vs `c⋆′`: a point of `W_q` with `X_Q = 0` and `c⋆′ ≠ 0`. -/
theorem pkR_GW_starp {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ i j : ℕ} (hi : i ≤ d₁) (hj : 2 * d₁ + 2 * j + 2 ≤ n)
    (hb : ¬ (i = d₁ ∧ j = 0)) (ha : ¬ (i = 0 ∧ 2 * d₁ + 2 * j + 2 = n)) {Q : ℕ × ℕ} (hQ : Q ∈ oddDiagonals n)
    (hne : Q ≠ pkR_mchord d₁ (i, j)) :
    ∃ X : ℕ × ℕ → ℚ, pkR_W n d₁ (i, j) X ∧ X Q = 0 ∧ mesh n X (pkR_cstp n d₁).1 (pkR_cstp n d₁).2 ≠ 0 := by
  obtain ⟨A, hA, -, hA2⟩ := pkR_Wind1 hE hn hi hj hb ha
  obtain ⟨B, hB, -, hB2, hB3⟩ := pkR_GW_Q hE hn hi hj hb hQ hne
  refine ⟨fun p => A p - A Q / B Q * B p, pkR_W_lc hA hB _, ?_, ?_⟩
  · show A Q - A Q / B Q * B Q = 0
    exact pkR_elim hB3
  · rw [pkR_mesh_lc, hB2]
    simpa using hA2

/-- Interval indicator `[lo ≤ k < hi]` (level function of a rank-one witness). -/
def pkR_ivl (lo hi : ℕ) : ℕ → ℚ := fun k => if lo ≤ k ∧ k < hi then 1 else 0

theorem pkR_ivl_def (lo hi k : ℕ) : pkR_ivl lo hi k = if lo ≤ k ∧ k < hi then 1 else 0 := rfl

/-- **Rank-one witness** (PREFORM-Res §3.5, R2-Z201 C5: `M = (e_w − e_r)(e_c − e_s)ᵀ`): a two-level point whose only
non-zero tiles are the mixed tiles on `{w, r} × {c, s}` (`r = 2d₁ + 1`, `s = n`). -/
def pkR_rk (n d₁ w c : ℕ) : ℕ × ℕ → ℚ :=
  pkR_fhPt (pkR_ivl (min ((w + 1) / 2) (d₁ + 1)) (max ((w + 1) / 2) (d₁ + 1))) (pkR_ivl (c / 2 + 1) (n / 2 + 1))

theorem pkR_rk_def (n d₁ w c : ℕ) : pkR_rk n d₁ w c =
    pkR_fhPt (pkR_ivl (min ((w + 1) / 2) (d₁ + 1)) (max ((w + 1) / 2) (d₁ + 1))) (pkR_ivl (c / 2 + 1) (n / 2 + 1)) :=
  rfl

/-- The rank-one witness lies on `Λ^I₀` whenever `(w, c)` is not a `minrect` entry of any member of `I`. -/
theorem pkR_rk_lam {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ : ℕ} (hd : 2 * d₁ + 2 ≤ n) {w c : ℕ} (hw : w % 2 = 1)
    (hw1 : 1 ≤ w) (hwn : w ≤ n) (hwr : w ≠ 2 * d₁ + 1) (hc : c % 2 = 0) (hc1 : 2 ≤ c) (hcn : c + 2 ≤ n)
    {I : Finset (ℕ × ℕ)}
    (hun : ∀ Q ∈ I, ¬ (¬ (2 * Q.1 + 1 ≤ w ∧ w ≤ 2 * d₁ + 2 * Q.2 + 1) ∧ (2 * Q.1 + 1 ≤ c ∧ c ≤ 2 * d₁ + 2 * Q.2 + 1))) :
    pkR_lam n d₁ I (pkR_rk n d₁ w c) ∧ mesh n (pkR_rk n d₁ w c) 1 (n - 1) = 0 := by
  have hf : pkR_ivl (min ((w + 1) / 2) (d₁ + 1)) (max ((w + 1) / 2) (d₁ + 1)) 0 =
      pkR_ivl (min ((w + 1) / 2) (d₁ + 1)) (max ((w + 1) / 2) (d₁ + 1)) (n / 2) := by
    rw [pkR_ivl_def, pkR_ivl_def]
    split_ifs <;> (try omega) <;> norm_num
  have hh : pkR_ivl (c / 2 + 1) (n / 2 + 1) 1 = pkR_ivl (c / 2 + 1) (n / 2 + 1) (n / 2 + 1) := by
    rw [pkR_ivl_def, pkR_ivl_def]
    split_ifs <;> (try omega) <;> norm_num
  obtain ⟨l1, l2⟩ := pkR_lam_of_sp hE hn d₁ hd (fun a ha b hb hp => pkR_fh_sp hE _ _ hf hh ha hb hp)
  refine ⟨pkR_lam_add l1 (fun Q hQ t ht => ?_), l2⟩
  have hQ' := hun Q hQ
  rw [pkR_mem_minrect, pkR_mem_head, pkR_mem_head] at ht
  obtain ⟨⟨w1, w2, w3, w4⟩, ⟨c1, c2, c3, c4⟩⟩ := ht
  have w1' := mem_Icc.1 w1
  have c1' := mem_Icc.1 c1
  rw [pkR_rk_def, pkR_fh_mixed hE _ _ hf hh w1 c1 w2 c2, mul_assoc]
  by_cases e1 : t.1 = w
  · by_cases e2 : t.2 = c
    · exfalso
      rw [e1] at w4
      rw [e2] at c4
      exact hQ' ⟨w4, c4⟩
    · rw [show pkR_ivl (c / 2 + 1) (n / 2 + 1) (t.2 / 2 + 1) - pkR_ivl (c / 2 + 1) (n / 2 + 1) (t.2 / 2) = 0 by
        rw [pkR_ivl_def, pkR_ivl_def]
        split_ifs <;> (try omega) <;> norm_num]
      ring
  · rw [show pkR_ivl (min ((w + 1) / 2) (d₁ + 1)) (max ((w + 1) / 2) (d₁ + 1)) ((t.1 + 1) / 2) -
        pkR_ivl (min ((w + 1) / 2) (d₁ + 1)) (max ((w + 1) / 2) (d₁ + 1)) (t.1 / 2) = 0 by
      rw [pkR_ivl_def, pkR_ivl_def]
      split_ifs <;> (try omega) <;> norm_num]
    ring

/-- The rank-one witness at a mixed diagonal `(p, q)`: non-zero when exactly one of `w, r` lies in `A = [p, q − 1]` and
`c ∈ A`. -/
theorem pkR_rk_ne {n d₁ p q w c : ℕ} (hE : n % 2 = 0) (hQ : (p, q) ∈ oddDiagonals n) (hw : w % 2 = 1) (hc : c % 2 = 0) (hc1 : 2 ≤ c)
    (hx : (p ≤ w ∧ w + 1 ≤ q ∧ ¬ (p ≤ 2 * d₁ + 1 ∧ 2 * d₁ + 2 ≤ q)) ∨
      (¬ (p ≤ w ∧ w + 1 ≤ q) ∧ p ≤ 2 * d₁ + 1 ∧ 2 * d₁ + 2 ≤ q)) (hcA : p ≤ c ∧ c + 1 ≤ q) :
    pkR_rk n d₁ w c (p, q) ≠ 0 := by
  have hQd := mem_filter.1 hQ
  rw [mem_diagonals] at hQd
  dsimp only at hQd
  rw [pkR_rk_def]
  refine pkR_fh_ne hQ _ _ ?_ ?_
  · rw [pkR_ivl_def, pkR_ivl_def]
    split_ifs <;> (try omega) <;> norm_num
  · rw [pkR_ivl_def, pkR_ivl_def]
    split_ifs <;> (try omega) <;> norm_num

/-- `I` closed (PREFORM-Res §3.1): `I ∪ {a, b}` is closed under meet `(max i, min j)` and join `(min i, max j)`, with
`b = (d₁, 0)`, `a = (0, d₂)`, `d₂ = n/2 − 1 − d₁`. -/
def pkR_closed (n d₁ : ℕ) (I : Finset (ℕ × ℕ)) : Prop :=
  ∀ Q1 ∈ insert (d₁, 0) (insert (0, n / 2 - 1 - d₁) I), ∀ Q2 ∈ insert (d₁, 0) (insert (0, n / 2 - 1 - d₁) I),
    (max Q1.1 Q2.1, min Q1.2 Q2.2) ∈ insert (d₁, 0) (insert (0, n / 2 - 1 - d₁) I) ∧
    (min Q1.1 Q2.1, max Q1.2 Q2.2) ∈ insert (d₁, 0) (insert (0, n / 2 - 1 - d₁) I)

theorem pkR_closed_iff (n d₁ : ℕ) (I : Finset (ℕ × ℕ)) : pkR_closed n d₁ I ↔
    ∀ Q1 ∈ insert (d₁, 0) (insert (0, n / 2 - 1 - d₁) I), ∀ Q2 ∈ insert (d₁, 0) (insert (0, n / 2 - 1 - d₁) I),
      (max Q1.1 Q2.1, min Q1.2 Q2.2) ∈ insert (d₁, 0) (insert (0, n / 2 - 1 - d₁) I) ∧
      (min Q1.1 Q2.1, max Q1.2 Q2.2) ∈ insert (d₁, 0) (insert (0, n / 2 - 1 - d₁) I) := Iff.rfl

/-- The lattice step of R2-Z201 C5 case 1a: in a meet/join-closed set containing `a = (0, d₂)` and `b = (d₁, 0)` (all
elements in the box), the four blocker types force `(i₀, j₀)` into the set. -/
theorem pkR_cl_core {d₁ d₂ i₀ j₀ : ℕ} {Ia : Finset (ℕ × ℕ)}
    (hcl : ∀ Q1 ∈ Ia, ∀ Q2 ∈ Ia, (max Q1.1 Q2.1, min Q1.2 Q2.2) ∈ Ia ∧ (min Q1.1 Q2.1, max Q1.2 Q2.2) ∈ Ia)
    (ha : (0, d₂) ∈ Ia) (hb : (d₁, 0) ∈ Ia) (hm : ∀ Q ∈ Ia, Q.1 ≤ d₁ ∧ Q.2 ≤ d₂) (hi0 : i₀ ≤ d₁) (hj0 : j₀ ≤ d₂)
    (B1 : 1 ≤ i₀ → i₀ < d₁ → ∃ Q ∈ Ia, Q.1 = i₀)
    (B2 : 1 ≤ i₀ → 1 ≤ j₀ → ∃ Q ∈ Ia, i₀ ≤ Q.1 ∧ j₀ ≤ Q.2)
    (B3 : j₀ < d₂ → i₀ < d₁ → ∃ Q ∈ Ia, Q.1 ≤ i₀ ∧ Q.2 ≤ j₀)
    (B4 : j₀ < d₂ → 1 ≤ j₀ → ∃ Q ∈ Ia, Q.2 = j₀) : (i₀, j₀) ∈ Ia := by
  have mt : ∀ a b c d : ℕ, (a, b) ∈ Ia → (c, d) ∈ Ia → (max a c, min b d) ∈ Ia :=
    fun a b c d h1 h2 => (hcl _ h1 _ h2).1
  have jn : ∀ a b c d : ℕ, (a, b) ∈ Ia → (c, d) ∈ Ia → (min a c, max b d) ∈ Ia :=
    fun a b c d h1 h2 => (hcl _ h1 _ h2).2
  obtain ⟨iP, jP, hP, hiP⟩ : ∃ x y : ℕ, (x, y) ∈ Ia ∧ x = i₀ := by
    rcases (show i₀ = 0 ∨ i₀ = d₁ ∨ (1 ≤ i₀ ∧ i₀ < d₁) by omega) with h | h | h
    · exact ⟨0, d₂, ha, h.symm⟩
    · exact ⟨d₁, 0, hb, h.symm⟩
    · obtain ⟨⟨x, y⟩, hQ, hx⟩ := B1 h.1 h.2
      exact ⟨x, y, hQ, hx⟩
  obtain ⟨iR, jR, hR, hjR⟩ : ∃ x y : ℕ, (x, y) ∈ Ia ∧ y = j₀ := by
    rcases (show j₀ = 0 ∨ j₀ = d₂ ∨ (1 ≤ j₀ ∧ j₀ < d₂) by omega) with h | h | h
    · exact ⟨d₁, 0, hb, h.symm⟩
    · exact ⟨0, d₂, ha, h.symm⟩
    · obtain ⟨⟨x, y⟩, hQ, hx⟩ := B4 h.2 h.1
      exact ⟨x, y, hQ, hx⟩
  have bP := hm _ hP
  have bR := hm _ hR
  dsimp only at bP bR
  rcases le_total j₀ jP with h1 | h1 <;> rcases le_total iR i₀ with h2 | h2
  · have h := mt _ _ _ _ hP hR
    rwa [show max iP iR = i₀ by omega, show min jP jR = j₀ by omega] at h
  · -- P and R': make P' with B3, or use a (j₀ = d₂) / b (i₀ = d₁)
    by_cases hc : j₀ < d₂ ∧ i₀ < d₁
    · obtain ⟨⟨x3, y3⟩, h3, e3⟩ := B3 hc.1 hc.2
      dsimp only at e3
      have h' := mt _ _ _ _ hP h3
      have h := jn _ _ _ _ h' hR
      rwa [show min (max iP x3) iR = i₀ by omega, show max (min jP y3) jR = j₀ by omega] at h
    · rcases (show j₀ = d₂ ∨ i₀ = d₁ by omega) with e | e
      · have h := mt _ _ _ _ hP ha
        rwa [show max iP 0 = i₀ by omega, show min jP d₂ = j₀ by omega] at h
      · have h := jn _ _ _ _ hb hR
        rwa [show min d₁ iR = i₀ by omega, show max 0 jR = j₀ by omega] at h
  · -- P' and R: make P with B2, or use a (i₀ = 0) / b (j₀ = 0)
    by_cases hc : 1 ≤ i₀ ∧ 1 ≤ j₀
    · obtain ⟨⟨x2, y2⟩, h2', e2⟩ := B2 hc.1 hc.2
      dsimp only at e2
      have h' := jn _ _ _ _ hP h2'
      have h := mt _ _ _ _ h' hR
      rwa [show max (min iP x2) iR = i₀ by omega, show min (max jP y2) jR = j₀ by omega] at h
    · rcases (show i₀ = 0 ∨ j₀ = 0 by omega) with e | e
      · have h := mt _ _ _ _ ha hR
        rwa [show max 0 iR = i₀ by omega, show min d₂ jR = j₀ by omega] at h
      · have h := jn _ _ _ _ hP hb
        rwa [show min iP d₁ = i₀ by omega, show max jP 0 = j₀ by omega] at h
  · have h := jn _ _ _ _ hP hR
    rwa [show min iP iR = i₀ by omega, show max jP jR = j₀ by omega] at h

theorem pkR_1a_eq {d₁ p q : ℕ} (hp : p % 2 = 1) (hq : q % 2 = 0) (h : 2 * d₁ + 2 ≤ q) :
    p = 2 * (p / 2) + 1 ∧ q = 2 * d₁ + 2 * ((q - 2) / 2 - d₁) + 2 := by
  omega

set_option maxHeartbeats 1000000 in
/-- Choice of the rank-one witness legs for (G^I) (R2-Z201 C5, cases 2 / 1b / 1a). -/
theorem pkR_GI_choose {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ : ℕ} (hd : 2 * d₁ + 2 ≤ n) {I : Finset (ℕ × ℕ)}
    (hIm : ∀ Q ∈ I, Q.1 ≤ d₁ ∧ 2 * d₁ + 2 * Q.2 + 2 ≤ n) (hcl : pkR_closed n d₁ I) {p q : ℕ}
    (hQ : (p, q) ∈ oddDiagonals n) (hnot : ∀ Q ∈ I, (p, q) ≠ pkR_mchord d₁ Q) :
    ∃ w c : ℕ, w % 2 = 1 ∧ 1 ≤ w ∧ w ≤ n ∧ w ≠ 2 * d₁ + 1 ∧ c % 2 = 0 ∧ 2 ≤ c ∧ c + 2 ≤ n ∧
      (∀ Q ∈ I, ¬ (¬ (2 * Q.1 + 1 ≤ w ∧ w ≤ 2 * d₁ + 2 * Q.2 + 1) ∧ (2 * Q.1 + 1 ≤ c ∧ c ≤ 2 * d₁ + 2 * Q.2 + 1))) ∧
      ((p ≤ w ∧ w + 1 ≤ q ∧ ¬ (p ≤ 2 * d₁ + 1 ∧ 2 * d₁ + 2 ≤ q)) ∨
        (¬ (p ≤ w ∧ w + 1 ≤ q) ∧ p ≤ 2 * d₁ + 1 ∧ 2 * d₁ + 2 ≤ q)) ∧ (p ≤ c ∧ c + 1 ≤ q) := by
  have hQd := mem_filter.1 hQ
  rw [mem_diagonals] at hQd
  dsimp only at hQd
  -- Case 2: r ∉ A; adjacent legs of A
  by_cases c2 : ¬ (p ≤ 2 * d₁ + 1 ∧ 2 * d₁ + 2 ≤ q)
  · rcases (show p % 2 = 1 ∨ p % 2 = 0 by omega) with hp | hp
    · refine ⟨p, p + 1, by omega, by omega, by omega, by omega, by omega, by omega, by omega, ?_, by omega, by omega⟩
      rintro ⟨i', j'⟩ -
      dsimp only
      omega
    · refine ⟨p + 1, p, by omega, by omega, by omega, by omega, by omega, by omega, by omega, ?_, by omega, by omega⟩
      rintro ⟨i', j'⟩ -
      dsimp only
      omega
  -- Case 1b: r ∈ A, A even-ended
  by_cases c1b : p % 2 = 0
  · refine ⟨p - 1, p, by omega, by omega, by omega, by omega, by omega, by omega, by omega, ?_, by omega, by omega⟩
    rintro ⟨i', j'⟩ -
    dsimp only
    omega
  -- Case 1a: Q = member (i₀, j₀) ∉ I
  by_cases oA : 3 ≤ p ∧ p + 1 ≤ 2 * d₁ ∧
      ∀ Q ∈ I, ¬ (¬ (2 * Q.1 + 1 ≤ p - 2 ∧ p - 2 ≤ 2 * d₁ + 2 * Q.2 + 1) ∧ (2 * Q.1 + 1 ≤ p + 1 ∧ p + 1 ≤ 2 * d₁ + 2 * Q.2 + 1))
  · exact ⟨p - 2, p + 1, by omega, by omega, by omega, by omega, by omega, by omega, by omega, oA.2.2, by omega, by omega⟩
  by_cases oB : 3 ≤ p ∧ 2 * d₁ + 4 ≤ q ∧
      ∀ Q ∈ I, ¬ (¬ (2 * Q.1 + 1 ≤ p - 2 ∧ p - 2 ≤ 2 * d₁ + 2 * Q.2 + 1) ∧ (2 * Q.1 + 1 ≤ q - 2 ∧ q - 2 ≤ 2 * d₁ + 2 * Q.2 + 1))
  · exact ⟨p - 2, q - 2, by omega, by omega, by omega, by omega, by omega, by omega, by omega, oB.2.2, by omega, by omega⟩
  by_cases oC : q + 2 ≤ n ∧ p + 1 ≤ 2 * d₁ ∧
      ∀ Q ∈ I, ¬ (¬ (2 * Q.1 + 1 ≤ q + 1 ∧ q + 1 ≤ 2 * d₁ + 2 * Q.2 + 1) ∧ (2 * Q.1 + 1 ≤ p + 1 ∧ p + 1 ≤ 2 * d₁ + 2 * Q.2 + 1))
  · exact ⟨q + 1, p + 1, by omega, by omega, by omega, by omega, by omega, by omega, by omega, oC.2.2, by omega, by omega⟩
  by_cases oD : q + 2 ≤ n ∧ 2 * d₁ + 4 ≤ q ∧
      ∀ Q ∈ I, ¬ (¬ (2 * Q.1 + 1 ≤ q + 1 ∧ q + 1 ≤ 2 * d₁ + 2 * Q.2 + 1) ∧ (2 * Q.1 + 1 ≤ q - 2 ∧ q - 2 ≤ 2 * d₁ + 2 * Q.2 + 1))
  · exact ⟨q + 1, q - 2, by omega, by omega, by omega, by omega, by omega, by omega, by omega, oD.2.2, by omega, by omega⟩
  exfalso
  have hcl' := (pkR_closed_iff n d₁ I).1 hcl
  have hin : ∀ Q ∈ I, Q ∈ insert (d₁, 0) (insert (0, n / 2 - 1 - d₁) I) :=
    fun Q hQ => mem_insert_of_mem (mem_insert_of_mem hQ)
  have hmem := pkR_cl_core (i₀ := p / 2) (j₀ := (q - 2) / 2 - d₁) hcl'
    (mem_insert_of_mem (mem_insert_self _ _)) (mem_insert_self _ _)
    (fun Q hQ => by
      rw [mem_insert, mem_insert] at hQ
      rcases hQ with e | e | e
      · rw [e]
        dsimp only
        omega
      · rw [e]
        dsimp only
        omega
      · have := hIm Q e
        omega)
    (by omega) (by omega)
    (fun h1 h2 => by
      by_contra hc
      refine oA ⟨by omega, by omega, fun Q hQ hbk => hc ⟨Q, hin Q hQ, ?_⟩⟩
      have := hIm Q hQ
      omega)
    (fun h1 h2 => by
      by_contra hc
      refine oB ⟨by omega, by omega, fun Q hQ hbk => hc ⟨Q, hin Q hQ, ?_, ?_⟩⟩
      · have := hIm Q hQ
        omega
      · have := hIm Q hQ
        omega)
    (fun h1 h2 => by
      by_contra hc
      refine oC ⟨by omega, by omega, fun Q hQ hbk => hc ⟨Q, hin Q hQ, ?_, ?_⟩⟩
      · have := hIm Q hQ
        omega
      · have := hIm Q hQ
        omega)
    (fun h1 h2 => by
      by_contra hc
      refine oD ⟨by omega, by omega, fun Q hQ hbk => hc ⟨Q, hin Q hQ, ?_⟩⟩
      have := hIm Q hQ
      omega)
  rw [mem_insert, mem_insert, Prod.mk.injEq, Prod.mk.injEq] at hmem
  rcases hmem with e | e | e
  · omega
  · omega
  · have em : pkR_mchord d₁ (p / 2, (q - 2) / 2 - d₁) = (2 * (p / 2) + 1, 2 * d₁ + 2 * ((q - 2) / 2 - d₁) + 2) := rfl
    have hp1 : p % 2 = 1 := by omega
    have hq1 : q % 2 = 0 := by omega
    have hq2 : 2 * d₁ + 2 ≤ q := by omega
    refine hnot _ e ?_
    rw [em, Prod.mk.injEq]
    exact pkR_1a_eq hp1 hq1 hq2

/-- **(G^I)** (PREFORM-Res §3.5, R2-Z201 C5, K6): for a closed set `I` of standard members, every mixed diagonal that
is not the chord of a member of `I` is non-zero somewhere on `Λ^I₀`. -/
theorem pkR_GI {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ : ℕ} (hd : 2 * d₁ + 2 ≤ n) {I : Finset (ℕ × ℕ)}
    (hIm : ∀ Q ∈ I, Q.1 ≤ d₁ ∧ 2 * d₁ + 2 * Q.2 + 2 ≤ n) (hcl : pkR_closed n d₁ I) {Q : ℕ × ℕ}
    (hQ : Q ∈ oddDiagonals n) (hnot : ∀ Q' ∈ I, Q ≠ pkR_mchord d₁ Q') :
    ∃ X : ℕ × ℕ → ℚ, pkR_lam n d₁ I X ∧ mesh n X 1 (n - 1) = 0 ∧ X Q ≠ 0 := by
  obtain ⟨p, q⟩ := Q
  obtain ⟨w, c, hw, hw1, hwn, hwr, hc, hc1, hcn, hun, hx, hcA⟩ := pkR_GI_choose hE hn hd hIm hcl hQ hnot
  obtain ⟨l1, l2⟩ := pkR_rk_lam hE hn hd hw hw1 hwn hwr hc hc1 hcn hun
  exact ⟨pkR_rk n d₁ w c, l1, l2, pkR_rk_ne hE hQ hw hc hc1 hx hcA⟩

-- c1b: [SideType] (PREFORM-Res §4.2): the two sides of a mixed diagonal, as sub-polygon points

theorem pkR_vtx_nxt {n : ℕ} (hn : 1 ≤ n) {x : ℕ} (hx : x ∈ Icc 1 n) : vtx n (x + 1) = if x = n then 1 else x + 1 := by
  rw [vtx_succ hn, vtx_of_mem (mem_Icc.1 hx).1 (mem_Icc.1 hx).2, pkR_nxt_def]

/-- A child tile of a sub-polygon whose child legs `1..m−1` are single parent legs (only child leg `m` is a block):
the parent tile plus the chord corner at `(1, m − 1)`. -/
theorem pkR_single {n m : ℕ} (hn : 2 ≤ n) (hm : 4 ≤ m) {f : ℕ → ℕ} (hf : pkR_CycList n m f)
    (hs : ∀ k, 1 ≤ k → k + 1 ≤ m → f (k + 1) = vtx n (f k + 1)) (X : ℕ × ℕ → ℚ) {k l : ℕ} (hk : 1 ≤ k)
    (hkl : k + 2 ≤ l) (hl : l + 1 ≤ m) :
    mesh m (pkR_subX n f X) k l =
      mesh n X (f k) (f l) + (if k = 1 ∧ l + 1 = m then planar n X (f m) (f 1) else 0) := by
  have hn1 : 1 ≤ n := by omega
  have hdiag : (min k l, max k l) ∈ diagonals m := by
    rw [min_eq_left (show k ≤ l by omega), max_eq_right (show k ≤ l by omega), mem_diagonals]
    dsimp only
    omega
  rw [pkR_subTile hn1 (by omega) hf X (mem_Icc.2 ⟨hk, by omega⟩) (mem_Icc.2 ⟨by omega, by omega⟩) hdiag]
  have hb : ∀ j, 1 ≤ j → j + 1 ≤ m → pkR_blk n m f j = {f j} := by
    intro j hj1 hj2
    have fj := (hf j (mem_Icc.2 ⟨hj1, by omega⟩)).1
    have fj' := mem_Icc.1 fj
    have e1 : vtx m j = j := vtx_of_mem hj1 (by omega)
    have e2 : vtx m (j + 1) = j + 1 := vtx_of_mem (by omega) hj2
    have hl1 : pkR_len n m f j = 1 := by
      show (f (vtx m (j + 1)) + n - f (vtx m j)) % n = 1
      rw [e1, e2, hs j hj1 hj2, pkR_vtx_nxt hn1 fj]
      split_ifs with h
      · rw [h, show 1 + n - n = 1 by omega, Nat.mod_eq_of_lt (by omega)]
      · rw [show f j + 1 + n - f j = 1 + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    show Icc (f (vtx m j)) (f (vtx m j) + pkR_len n m f j - 1) = {f j}
    rw [hl1, e1, show f j + 1 - 1 = f j by omega, Icc_self]
  rw [hb k hk (by omega), hb l (by omega) hl, sum_singleton, sum_singleton]
  have vl : vtx m l = l := vtx_of_mem (by omega) (by omega)
  have vk : vtx m k = k := vtx_of_mem hk (by omega)
  have vk2 : vtx m (k + 2) = k + 2 := vtx_of_mem (by omega) (by omega)
  have vk1 : vtx m (k + 1) = k + 1 := vtx_of_mem (by omega) (by omega)
  have vl1 : vtx m (l + 1) = l + 1 := vtx_of_mem (by omega) (by omega)
  have c1 : (if vtx m l = vtx m (k + 2) then planar n X (f (vtx m (k + 1))) (f (vtx m (k + 2))) else 0) = 0 := by
    rw [vl, vk2, vk1]
    by_cases h : l = k + 2
    · rw [ite_eq_left h, hs (k + 1) (by omega) (by omega)]
      have fk := mem_Icc.1 (hf (k + 1) (mem_Icc.2 ⟨by omega, by omega⟩)).1
      rw [pkR_planar_congr hn1 X (rfl : vtx n (f (k + 1)) = vtx n (f (k + 1)))
        (pkR_vtx_vtx hn1 (f (k + 1) + 1)), pkR_planar_succ hn1]
    · exact ite_eq_right h
  rw [c1, vk, vl1]
  by_cases h2 : l + 2 ≤ m
  · rw [vtx_of_mem (by omega) h2, ite_eq_right (show ¬ k = l + 2 by omega),
      ite_eq_right (show ¬ (k = 1 ∧ l + 1 = m) by omega)]
    ring
  · have e : l + 2 = 1 + m := by omega
    rw [e, vtx_add_n, vtx_of_mem le_rfl (by omega), show l + 1 = m by omega]
    by_cases hk1 : k = 1
    · rw [ite_eq_left hk1, ite_eq_left ⟨hk1, rfl⟩]
      ring
    · rw [ite_eq_right hk1, ite_eq_right (fun h => hk1 h.1)]
      ring

/-- Unfolding `OnZT` at the even legs of an even `m`-gon: every odd–odd pair `a + 2 ≤ b` must vanish. -/
theorem pkR_ZT_evens {m : ℕ} (hm : m % 2 = 0) {Y : ℕ × ℕ → ℚ}
    (h : ∀ a b, 1 ≤ a → a + 2 ≤ b → b + 1 ≤ m → a % 2 = 1 → b % 2 = 1 → mesh m Y a b = 0) :
    OnZT m ((Icc 1 m).filter (fun t => t % 2 = 0)) Y := by
  show ∀ a ∈ Icc 1 m, ∀ b ∈ Icc 1 m, InST ((Icc 1 m).filter (fun t => t % 2 = 0)) a b → mesh m Y a b = 0
  intro a ha b hb hst
  obtain ⟨ha', hb', ⟨t, ht, h1, h2⟩, -⟩ := hst
  have ha1 := mem_Icc.1 ha
  have hb1 := mem_Icc.1 hb
  have ao : a % 2 = 1 := by
    by_contra hc
    exact ha' (mem_filter.2 ⟨ha, by omega⟩)
  have bo : b % 2 = 1 := by
    by_contra hc
    exact hb' (mem_filter.2 ⟨hb, by omega⟩)
  have ht1 := mem_filter.1 ht
  have ht2 := mem_Icc.1 ht1.1
  rcases (show a < b ∨ b < a by omega) with hab | hab
  · exact h a b ha1.1 (by omega) (by omega) ao bo
  · rw [pkR_mesh_comm]
    exact h b a hb1.1 (by omega) (by omega) bo ao

/-- **[SideType], side σ₁ = [p..q]** (PREFORM-Res §4.2; relabelling `k ↦ p + k − 1`, as the base's `relab n p`): if the
same-parity tiles inside `A_Q = [p, q − 1]` of `p`'s parity vanish and `X_Q = 0`, the side is on its `S_T` locus
(`T` = even child legs, the class of `Q̂`). -/
theorem pkR_side1 {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {p q : ℕ} (hQ : (p, q) ∈ oddDiagonals n)
    {X : ℕ × ℕ → ℚ}
    (H : ∀ a b, p ≤ a → a + 2 ≤ b → b + 1 ≤ q → a % 2 = p % 2 → b % 2 = p % 2 → mesh n X a b = 0)
    (hXQ : X (p, q) = 0) :
    OnZT (q - p + 1) ((Icc 1 (q - p + 1)).filter (fun t => t % 2 = 0)) (pkR_subX n (fun k => k + p - 1) X) := by
  have hQd := mem_filter.1 hQ
  rw [mem_diagonals] at hQd
  dsimp only at hQd
  have hn1 : 1 ≤ n := by omega
  have hf : pkR_CycList n (q - p + 1) (fun k => k + p - 1) := by
    intro i hi
    have hi' := mem_Icc.1 hi
    dsimp only
    refine ⟨mem_Icc.2 ⟨by omega, by omega⟩, ?_⟩
    by_cases h : i + 1 ≤ q - p + 1
    · rw [vtx_of_mem (by omega) h]
      omega
    · rw [show i + 1 = 1 + (q - p + 1) by omega, vtx_add_n, vtx_of_mem le_rfl (by omega)]
      omega
  have hs : ∀ k, 1 ≤ k → k + 1 ≤ q - p + 1 → k + 1 + p - 1 = vtx n (k + p - 1 + 1) := by
    intro k hk1 hk2
    rw [vtx_of_mem (by omega) (by omega)]
    omega
  refine pkR_ZT_evens (by omega) (fun a b ha hab hb ao bo => ?_)
  rw [pkR_single (by omega) (by omega) hf hs X ha hab hb]
  rw [H (a + p - 1) (b + p - 1) (by omega) (by omega) (by omega) (by omega) (by omega)]
  by_cases hc : a = 1 ∧ b + 1 = q - p + 1
  · rw [ite_eq_left hc]
    rw [show q - p + 1 + p - 1 = q by omega, show 1 + p - 1 = p by omega, pkR_planar_comm,
      planar_of_mem X (by omega) (by omega) (by omega), ite_eq_left (by rw [mem_diagonals]; dsimp only; omega), hXQ]
    ring
  · rw [ite_eq_right hc]
    ring

/-- **[SideType], side σ₂ = [q..n, 1..p]** (relabelling `k ↦ vtx n (q + k − 1)`, as the base's `relab n q`): if the
same-parity tiles among the legs of `B_Q` (outside `[p, q − 1]`) of `q`'s parity vanish and `X_Q = 0`, the side is on its
`S_T` locus. -/
theorem pkR_side2 {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {p q : ℕ} (hQ : (p, q) ∈ oddDiagonals n)
    {X : ℕ × ℕ → ℚ}
    (H : ∀ a ∈ Icc 1 n, ∀ b ∈ Icc 1 n, a + 2 ≤ b → (a < p ∨ q ≤ a) → (b < p ∨ q ≤ b) → a % 2 = q % 2 →
      b % 2 = q % 2 → mesh n X a b = 0)
    (hXQ : X (p, q) = 0) :
    OnZT (n - q + p + 1) ((Icc 1 (n - q + p + 1)).filter (fun t => t % 2 = 0))
      (pkR_subX n (fun k => vtx n (k + q - 1)) X) := by
  have hQd := mem_filter.1 hQ
  rw [mem_diagonals] at hQd
  dsimp only at hQd
  have hn1 : 1 ≤ n := by omega
  -- the value of the list
  have fv : ∀ k, 1 ≤ k → k ≤ n → vtx n (k + q - 1) = if k + q - 1 ≤ n then k + q - 1 else k + q - 1 - n := by
    intro k hk1 hk2
    split_ifs with h
    · exact vtx_of_mem (by omega) h
    · have e : vtx n (k + q - 1) = vtx n ((k + q - 1 - n) + n) := by
        rw [show (k + q - 1 - n) + n = k + q - 1 by omega]
      rw [e, vtx_add_n, vtx_of_mem (by omega) (by omega)]
  have hf : pkR_CycList n (n - q + p + 1) (fun k => vtx n (k + q - 1)) := by
    intro i hi
    have hi' := mem_Icc.1 hi
    refine ⟨mem_Icc.2 (vtx_bounds n _ hn1), ?_⟩
    dsimp only
    by_cases h : i + 1 ≤ n - q + p + 1
    · rw [vtx_of_mem (by omega) h, fv (i + 1) (by omega) (by omega), fv i (by omega) (by omega)]
      split_ifs <;> omega
    · rw [show i + 1 = 1 + (n - q + p + 1) by omega, vtx_add_n,
        vtx_of_mem le_rfl (by omega), fv 1 le_rfl (by omega), fv i (by omega) (by omega)]
      split_ifs <;> omega
  have hs : ∀ k, 1 ≤ k → k + 1 ≤ n - q + p + 1 → vtx n (k + 1 + q - 1) = vtx n (vtx n (k + q - 1) + 1) := by
    intro k hk1 hk2
    rw [vtx_succ hn1 (vtx n (k + q - 1)), pkR_vtx_vtx hn1, ← vtx_succ hn1, show k + q - 1 + 1 = k + 1 + q - 1 by omega]
  refine pkR_ZT_evens (by omega) (fun a b ha hab hb ao bo => ?_)
  rw [pkR_single (by omega) (by omega) hf hs X ha hab hb]
  rw [fv a ha (by omega), fv b (by omega) (by omega)]
  have hz : mesh n X (if a + q - 1 ≤ n then a + q - 1 else a + q - 1 - n)
      (if b + q - 1 ≤ n then b + q - 1 else b + q - 1 - n) = 0 := by
    split_ifs
    · exact H (a + q - 1) (mem_Icc.2 ⟨by omega, by omega⟩) (b + q - 1) (mem_Icc.2 ⟨by omega, by omega⟩) (by omega)
        (by omega) (by omega) (by omega) (by omega)
    · rw [pkR_mesh_comm]
      exact H (b + q - 1 - n) (mem_Icc.2 ⟨by omega, by omega⟩) (a + q - 1) (mem_Icc.2 ⟨by omega, by omega⟩) (by omega)
        (by omega) (by omega) (by omega) (by omega)
    · omega
    · exact H (a + q - 1 - n) (mem_Icc.2 ⟨by omega, by omega⟩) (b + q - 1 - n) (mem_Icc.2 ⟨by omega, by omega⟩)
        (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [hz]
  by_cases hc : a = 1 ∧ b + 1 = n - q + p + 1
  · rw [ite_eq_left hc, fv 1 le_rfl (by omega), show n - q + p + 1 + q - 1 = p + n by omega, vtx_add_n,
      vtx_of_mem (by omega) (by omega), ite_eq_left (show 1 + q - 1 ≤ n by omega), show 1 + q - 1 = q by omega,
      planar_of_mem X (by omega) (by omega) (by omega), ite_eq_left (by rw [mem_diagonals]; dsimp only; omega), hXQ]
    ring
  · rw [ite_eq_right hc]
    ring

/-- On `Λ₀` (`x = 0`) every same-parity tile vanishes (type B for both sides). -/
theorem pkR_lam0_sp {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ : ℕ} (hd : 2 * d₁ + 2 ≤ n) {I : Finset (ℕ × ℕ)}
    {X : ℕ × ℕ → ℚ} (hX : pkR_lam n d₁ I X) (hx : mesh n X 1 (n - 1) = 0) :
    ∀ a ∈ Icc 1 n, ∀ b ∈ Icc 1 n, a + 2 ≤ b → a % 2 = b % 2 → mesh n X a b = 0 := by
  intro a ha b hb hab hp
  have ec : pkR_cstp n d₁ = if d₁ = 0 then (2, n) else (2 * d₁, 2 * d₁ + 2) := rfl
  by_cases h1 : a = 1 ∧ b = n - 1
  · rw [h1.1, h1.2]
    exact hx
  by_cases h2 : (a, b) = pkR_cstp n d₁
  · rw [show a = (pkR_cstp n d₁).1 by rw [← h2], show b = (pkR_cstp n d₁).2 by rw [← h2], ← hX.2.1]
    exact hx
  exact hX.1 a ha b hb hab hp (fun e => h1 ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩) h2

/-- **[SideType] A for σ₁**: on `Λ` the hypothesis of `pkR_side1` holds unless `c⋆′` lies inside `A_Q` with `p` even
(then it holds on `Λ₀`, `pkR_lam0_sp`). -/
theorem pkR_side1_lam {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ : ℕ} (hd : 2 * d₁ + 2 ≤ n) {I : Finset (ℕ × ℕ)}
    {X : ℕ × ℕ → ℚ} (hX : pkR_lam n d₁ I X) {p q : ℕ} (hQ : (p, q) ∈ oddDiagonals n)
    (hA : ¬ (p % 2 = 0 ∧ p ≤ 2 * d₁ ∧ 2 * d₁ + 3 ≤ q)) :
    ∀ a b, p ≤ a → a + 2 ≤ b → b + 1 ≤ q → a % 2 = p % 2 → b % 2 = p % 2 → mesh n X a b = 0 := by
  have hQd := mem_filter.1 hQ
  rw [mem_diagonals] at hQd
  dsimp only at hQd
  intro a b h1 h2 h3 h4 h5
  have ec : pkR_cstp n d₁ = if d₁ = 0 then (2, n) else (2 * d₁, 2 * d₁ + 2) := rfl
  refine hX.1 a (mem_Icc.2 ⟨by omega, by omega⟩) b (mem_Icc.2 ⟨by omega, by omega⟩) h2 (by omega)
    (fun e => by rw [Prod.mk.injEq] at e; omega) (fun e => ?_)
  rw [ec] at e
  split_ifs at e <;> rw [Prod.mk.injEq] at e <;> omega

/-- **[SideType] A for σ₂**: on `Λ` the hypothesis of `pkR_side2` holds unless `c⋆` (odd `q`, `p ≥ 2`) or `c⋆′` (even
`q`, both legs outside `A_Q`) lies among the legs of `B_Q` (then it holds on `Λ₀`). -/
theorem pkR_side2_lam {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ : ℕ} (hd : 2 * d₁ + 2 ≤ n) {I : Finset (ℕ × ℕ)}
    {X : ℕ × ℕ → ℚ} (hX : pkR_lam n d₁ I X) {p q : ℕ} (hQ : (p, q) ∈ oddDiagonals n)
    (hs : ¬ (q % 2 = 1 ∧ 2 ≤ p))
    (hr : ¬ (q % 2 = 0 ∧ ¬ (p ≤ (pkR_cstp n d₁).1 ∧ (pkR_cstp n d₁).1 + 1 ≤ q) ∧
      ¬ (p ≤ (pkR_cstp n d₁).2 ∧ (pkR_cstp n d₁).2 + 1 ≤ q))) :
    ∀ a ∈ Icc 1 n, ∀ b ∈ Icc 1 n, a + 2 ≤ b → (a < p ∨ q ≤ a) → (b < p ∨ q ≤ b) → a % 2 = q % 2 →
      b % 2 = q % 2 → mesh n X a b = 0 := by
  have hQd := mem_filter.1 hQ
  rw [mem_diagonals] at hQd
  dsimp only at hQd
  intro a ha b hb h2 h3 h4 h5 h6
  have ha' := mem_Icc.1 ha
  have hb' := mem_Icc.1 hb
  have ec : pkR_cstp n d₁ = if d₁ = 0 then (2, n) else (2 * d₁, 2 * d₁ + 2) := rfl
  refine hX.1 a ha b hb h2 (by omega) (fun e => by rw [Prod.mk.injEq] at e; omega) (fun e => ?_)
  rw [← e] at hr
  dsimp only at hr
  rw [ec] at e
  split_ifs at e <;> rw [Prod.mk.injEq] at e <;> omega

/-- A standard member `(i, j)` (neither `a` nor `b`) is a mixed diagonal. -/
theorem pkR_mchord_mem {n d₁ i j : ℕ} (hi : i ≤ d₁) (hj : 2 * d₁ + 2 * j + 2 ≤ n) (hb : ¬ (i = d₁ ∧ j = 0))
    (ha : ¬ (i = 0 ∧ 2 * d₁ + 2 * j + 2 = n)) : pkR_mchord d₁ (i, j) ∈ oddDiagonals n := by
  show (2 * i + 1, 2 * d₁ + 2 * j + 2) ∈ (diagonals n).filter (fun d => (d.2 - d.1) % 2 = 1)
  rw [mem_filter, mem_diagonals]
  dsimp only
  omega

/-- **R14(a)** (PREFORM-Res §4.5, K9): on `W_q ∩ {c⋆ = 0}` every `Z′₁` tile vanishes: `(w, b)` with `w` an odd leg outside
`A_q` and `b` odd or in `A_q` (odd `μ₁` pairs, odd `μ₁ × A_q`, `minrect(q)`). -/
theorem pkR_R14a {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ i j : ℕ} (hi : i ≤ d₁) (hj : 2 * d₁ + 2 * j + 2 ≤ n)
    {X : ℕ × ℕ → ℚ} (hW : pkR_W n d₁ (i, j) X) (hx : mesh n X 1 (n - 1) = 0) :
    ∀ w ∈ Icc 1 n, ∀ b ∈ Icc 1 n, w % 2 = 1 → ¬ (2 * i + 1 ≤ w ∧ w ≤ 2 * d₁ + 2 * j + 1) →
      (b % 2 = 1 ∨ (2 * i + 1 ≤ b ∧ b ≤ 2 * d₁ + 2 * j + 1)) → b ≠ w → mesh n X w b = 0 := by
  have ec : pkR_cstp n d₁ = if d₁ = 0 then (2, n) else (2 * d₁, 2 * d₁ + 2) := rfl
  have et : pkR_tau d₁ (i, j) = (2 * i + 1, 2 * d₁ + 2 * j + 1) := rfl
  have sp : ∀ a c, a ∈ Icc 1 n → c ∈ Icc 1 n → a + 2 ≤ c → a % 2 = 1 → c % 2 = 1 →
      ¬ (2 * i + 1 ≤ a ∧ c ≤ 2 * d₁ + 2 * j + 1) → mesh n X a c = 0 := by
    intro a c ha hc hac h1 h2 h3
    by_cases hs : a = 1 ∧ c = n - 1
    · rw [hs.1, hs.2]
      exact hx
    refine hW.1 a ha c hc hac (by omega) (fun e => hs ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩) (fun e => ?_)
      (fun e => ?_)
    · rw [ec] at e
      split_ifs at e <;> rw [Prod.mk.injEq] at e <;> omega
    · rw [et, Prod.mk.injEq] at e
      omega
  intro w hw b hb h1 h2 h3 h4
  have hw' := mem_Icc.1 hw
  have hb' := mem_Icc.1 hb
  rcases (show b % 2 = 1 ∨ b % 2 = 0 by omega) with h5 | h5
  · rcases (show w < b ∨ b < w by omega) with h6 | h6
    · exact sp w b hw hb (by omega) h1 h5 (by omega)
    · rw [pkR_mesh_comm]
      exact sp b w hb hw (by omega) h5 h1 (by omega)
  · refine hW.2 (w, b) ?_
    rw [pkR_mem_minrect, pkR_mem_head, pkR_mem_head]
    dsimp only
    exact ⟨⟨hw, h1, by omega, h2⟩, ⟨hb, h5, by omega, by omega⟩⟩

/-- **R14(b)** (PREFORM-Res §4.5, K9): on `W_q ∩ {c⋆′ = 0}` every `Z′₂` tile vanishes: `(e, b)` with `e` an even leg in
`A_q` and `b` even or outside `A_q` (even `μ₂` pairs, even `μ₂ × B_q`, `minrect(q)`). -/
theorem pkR_R14b {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ i j : ℕ} (hi : i ≤ d₁) (hj : 2 * d₁ + 2 * j + 2 ≤ n)
    {X : ℕ × ℕ → ℚ} (hW : pkR_W n d₁ (i, j) X) (hy : mesh n X (pkR_cstp n d₁).1 (pkR_cstp n d₁).2 = 0) :
    ∀ e ∈ Icc 1 n, ∀ b ∈ Icc 1 n, e % 2 = 0 → (2 * i + 1 ≤ e ∧ e ≤ 2 * d₁ + 2 * j + 1) →
      (b % 2 = 0 ∨ ¬ (2 * i + 1 ≤ b ∧ b ≤ 2 * d₁ + 2 * j + 1)) → b ≠ e → mesh n X e b = 0 := by
  have ec : pkR_cstp n d₁ = if d₁ = 0 then (2, n) else (2 * d₁, 2 * d₁ + 2) := rfl
  have et : pkR_tau d₁ (i, j) = (2 * i + 1, 2 * d₁ + 2 * j + 1) := rfl
  have sp : ∀ a c, a ∈ Icc 1 n → c ∈ Icc 1 n → a + 2 ≤ c → a % 2 = 0 → c % 2 = 0 → mesh n X a c = 0 := by
    intro a c ha hc hac h1 h2
    by_cases hs : (a, c) = pkR_cstp n d₁
    · rw [show a = (pkR_cstp n d₁).1 by rw [← hs], show c = (pkR_cstp n d₁).2 by rw [← hs]]
      exact hy
    refine hW.1 a ha c hc hac (by omega) (fun e => ?_) hs (fun e => ?_)
    · rw [Prod.mk.injEq] at e
      omega
    · rw [et, Prod.mk.injEq] at e
      omega
  intro e he b hb h1 h2 h3 h4
  have he' := mem_Icc.1 he
  have hb' := mem_Icc.1 hb
  rcases (show b % 2 = 0 ∨ b % 2 = 1 by omega) with h5 | h5
  · rcases (show e < b ∨ b < e by omega) with h6 | h6
    · exact sp e b he hb (by omega) h1 h5
    · rw [pkR_mesh_comm]
      exact sp b e hb he (by omega) h5 h1
  · rw [pkR_mesh_comm]
    refine hW.2 (b, e) ?_
    rw [pkR_mem_minrect, pkR_mem_head, pkR_mem_head]
    dsimp only
    exact ⟨⟨hb, h5, by omega, by omega⟩, ⟨he, h1, by omega, h2⟩⟩

/-- **R14(c), B-side** (PREFORM-Res §4.5): for a member `Q = (i', j')` and any `q`, on `W_q ∩ {X_Q = 0}` the B-side
`[2d₁ + 2j' + 2 .. n, 1 .. 2i' + 1]` of `Q` is on its `S_T` locus. -/
theorem pkR_R14c_B {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ i j i' j' : ℕ} (hi' : i' ≤ d₁)
    (hj' : 2 * d₁ + 2 * j' + 2 ≤ n) (hb' : ¬ (i' = d₁ ∧ j' = 0)) (ha' : ¬ (i' = 0 ∧ 2 * d₁ + 2 * j' + 2 = n))
    {X : ℕ × ℕ → ℚ} (hW : pkR_W n d₁ (i, j) X) (hXQ : X (pkR_mchord d₁ (i', j')) = 0) :
    OnZT (n - (2 * d₁ + 2 * j' + 2) + (2 * i' + 1) + 1)
      ((Icc 1 (n - (2 * d₁ + 2 * j' + 2) + (2 * i' + 1) + 1)).filter (fun t => t % 2 = 0))
      (pkR_subX n (fun k => vtx n (k + (2 * d₁ + 2 * j' + 2) - 1)) X) := by
  have ec : pkR_cstp n d₁ = if d₁ = 0 then (2, n) else (2 * d₁, 2 * d₁ + 2) := rfl
  have et : pkR_tau d₁ (i, j) = (2 * i + 1, 2 * d₁ + 2 * j + 1) := rfl
  refine pkR_side2 hE hn (pkR_mchord_mem hi' hj' hb' ha') (fun a ha b hb hab h1 h2 h3 h4 => ?_) hXQ
  refine hW.1 a ha b hb hab (by omega) (fun e => by rw [Prod.mk.injEq] at e; omega) (fun e => ?_)
    (fun e => by rw [et, Prod.mk.injEq] at e; omega)
  rw [ec] at e
  split_ifs at e <;> rw [Prod.mk.injEq] at e <;> omega

/-- **R14(c), A-side** (PREFORM-Res §4.5): for members `Q = (i', j')` with `A_q ⊄ A_Q` (e.g. `Q ≺ q`), on
`W_q ∩ {X_Q = 0}` the A-side `[2i' + 1 .. 2d₁ + 2j' + 2]` of `Q` is on its `S_T` locus. -/
theorem pkR_R14c_A {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ i j i' j' : ℕ} (hi' : i' ≤ d₁)
    (hj' : 2 * d₁ + 2 * j' + 2 ≤ n) (hb' : ¬ (i' = d₁ ∧ j' = 0)) (ha' : ¬ (i' = 0 ∧ 2 * d₁ + 2 * j' + 2 = n))
    (hq : ¬ (i' ≤ i ∧ j ≤ j')) {X : ℕ × ℕ → ℚ} (hW : pkR_W n d₁ (i, j) X)
    (hXQ : X (pkR_mchord d₁ (i', j')) = 0) :
    OnZT (2 * d₁ + 2 * j' + 2 - (2 * i' + 1) + 1)
      ((Icc 1 (2 * d₁ + 2 * j' + 2 - (2 * i' + 1) + 1)).filter (fun t => t % 2 = 0))
      (pkR_subX n (fun k => k + (2 * i' + 1) - 1) X) := by
  have ec : pkR_cstp n d₁ = if d₁ = 0 then (2, n) else (2 * d₁, 2 * d₁ + 2) := rfl
  have et : pkR_tau d₁ (i, j) = (2 * i + 1, 2 * d₁ + 2 * j + 1) := rfl
  refine pkR_side1 hE hn (pkR_mchord_mem hi' hj' hb' ha') (fun a b h1 h2 h3 h4 h5 => ?_) hXQ
  refine hW.1 a (mem_Icc.2 ⟨by omega, by omega⟩) b (mem_Icc.2 ⟨by omega, by omega⟩) h2 (by omega)
    (fun e => by rw [Prod.mk.injEq] at e; omega) (fun e => ?_) (fun e => by rw [et, Prod.mk.injEq] at e; omega)
  rw [ec] at e
  split_ifs at e <;> rw [Prod.mk.injEq] at e <;> omega

-- c1c (R12-P7b-pkgRes-c1c): [Region](ii)(iii) — the region Ω(y, z) of the standard polygon is standard again

/-- Tiles only see labels through `vtx`. -/
theorem pkR_mesh_vtx {K : Type*} [Field K] {n : ℕ} (hn : 1 ≤ n) (X : ℕ × ℕ → K) (a b : ℕ) :
    mesh n X a b = mesh n X (vtx n a) (vtx n b) := by
  have e0 : vtx n a = vtx n (vtx n a) := (pkR_vtx_vtx hn a).symm
  have f0 : vtx n b = vtx n (vtx n b) := (pkR_vtx_vtx hn b).symm
  have e1 : vtx n (a + 1) = vtx n (vtx n a + 1) := by rw [vtx_succ hn, vtx_succ hn, pkR_vtx_vtx hn]
  have f1 : vtx n (b + 1) = vtx n (vtx n b + 1) := by rw [vtx_succ hn, vtx_succ hn, pkR_vtx_vtx hn]
  rw [pkR_mesh_def n X a b, pkR_mesh_def n X (vtx n a) (vtx n b), pkR_planar_congr hn X e0 f0,
    pkR_planar_congr hn X e1 f1, pkR_planar_congr hn X e0 f1, pkR_planar_congr hn X e1 f0]

/-- `vtx` on `1..2m`. -/
theorem pkR_vtx2 {m i : ℕ} (hm : 1 ≤ m) (h1 : 1 ≤ i) (h2 : i ≤ 2 * m) : vtx m i = if i ≤ m then i else i - m := by
  split_ifs with h
  · exact vtx_of_mem h1 h
  · have e : vtx m i = vtx m ((i - m) + m) := by rw [show i - m + m = i by omega]
    rw [e, vtx_add_n, vtx_of_mem (by omega) (by omega)]

/-- The planar variable of the closing edge `(n, 1)` is `0`. -/
theorem pkR_planar_n1 {K : Type*} [Field K] {n : ℕ} (hn : 1 ≤ n) (X : ℕ × ℕ → K) : planar n X n 1 = 0 := by
  have e : vtx n 1 = vtx n (n + 1) := by rw [show n + 1 = 1 + n by ring, vtx_add_n]
  rw [pkR_planar_congr hn X (rfl : vtx n n = vtx n n) e, pkR_planar_succ hn]

/-- The region list `f_{y,z}` (PREFORM-Res §3.3) for `y = (iy, jz + g) ≻ z = (iy + e, jz)`:
`[2iy+1, …, 2iy+2e+1] ++ [2d₁+2jz+2, …, 2d₁+2jz+2g+2]` (length `2e + 2g + 2`). -/
def pkR_rgf (d₁ iy e jz : ℕ) : ℕ → ℕ := fun k => if k ≤ 2 * e + 1 then 2 * iy + k else k + 2 * d₁ + 2 * jz - 2 * e

theorem pkR_rgf_def (d₁ iy e jz k : ℕ) :
    pkR_rgf d₁ iy e jz k = if k ≤ 2 * e + 1 then 2 * iy + k else k + 2 * d₁ + 2 * jz - 2 * e := rfl

/-- Standing hypotheses of a region: `n` even, `y = (iy, jz + g)` and `z = (iy + e, jz)` in the box, `y ≠ z`. -/
def pkR_RG (n d₁ iy e jz g : ℕ) : Prop :=
  n % 2 = 0 ∧ 4 ≤ n ∧ iy + e ≤ d₁ ∧ 2 * d₁ + 2 * jz + 2 * g + 2 ≤ n ∧ 1 ≤ e + g

theorem pkR_RG_iff (n d₁ iy e jz g : ℕ) : pkR_RG n d₁ iy e jz g ↔
    n % 2 = 0 ∧ 4 ≤ n ∧ iy + e ≤ d₁ ∧ 2 * d₁ + 2 * jz + 2 * g + 2 ≤ n ∧ 1 ≤ e + g := Iff.rfl

theorem pkR_rg_cyc {n d₁ iy e jz g : ℕ} (H : pkR_RG n d₁ iy e jz g) :
    pkR_CycList n (2 * e + 2 * g + 2) (pkR_rgf d₁ iy e jz) := by
  obtain ⟨hE, hn, hd, hj, heg⟩ := H
  intro i hi
  have hi' := mem_Icc.1 hi
  rw [pkR_vtx2 (by omega) (by omega) (by omega), pkR_rgf_def, pkR_rgf_def, mem_Icc]
  split_ifs <;> constructor <;> omega

theorem pkR_rg_blkI {n d₁ iy e jz g : ℕ} (H : pkR_RG n d₁ iy e jz g) {k : ℕ} (hk : k ∈ Icc 1 (2 * e + 2 * g + 2)) :
    pkR_blk n (2 * e + 2 * g + 2) (pkR_rgf d₁ iy e jz) k =
      Icc (pkR_rgf d₁ iy e jz k)
        (if k = 2 * e + 2 * g + 2 then n + 2 * iy else pkR_rgf d₁ iy e jz (k + 1) - 1) := by
  obtain ⟨hE, hn, hd, hj, heg⟩ := H
  have hk' := mem_Icc.1 hk
  have eb : pkR_blk n (2 * e + 2 * g + 2) (pkR_rgf d₁ iy e jz) k =
      Icc (pkR_rgf d₁ iy e jz (vtx (2 * e + 2 * g + 2) k))
        (pkR_rgf d₁ iy e jz (vtx (2 * e + 2 * g + 2) k) + pkR_len n (2 * e + 2 * g + 2) (pkR_rgf d₁ iy e jz) k - 1) := rfl
  have el : pkR_len n (2 * e + 2 * g + 2) (pkR_rgf d₁ iy e jz) k =
      (pkR_rgf d₁ iy e jz (vtx (2 * e + 2 * g + 2) (k + 1)) + n - pkR_rgf d₁ iy e jz (vtx (2 * e + 2 * g + 2) k)) % n := rfl
  rw [eb, el, vtx_of_mem hk'.1 hk'.2, pkR_vtx2 (by omega) (by omega) (by omega)]
  by_cases hkm : k = 2 * e + 2 * g + 2
  · rw [ite_eq_left hkm, ite_eq_right (show ¬ (k + 1 ≤ 2 * e + 2 * g + 2) by omega), pkR_rgf_def, pkR_rgf_def,
      ite_eq_right (show ¬ (k ≤ 2 * e + 1) by omega), ite_eq_left (show k + 1 - (2 * e + 2 * g + 2) ≤ 2 * e + 1 by omega),
      Nat.mod_eq_of_lt (by omega)]
    ext x
    rw [mem_Icc, mem_Icc]
    omega
  · rw [ite_eq_right hkm, ite_eq_left (show k + 1 ≤ 2 * e + 2 * g + 2 by omega), pkR_rgf_def, pkR_rgf_def]
    have key : ∀ A B : ℕ, B < A → A < B + n → (A + n - B) % n = A - B := by
      intro A B h1 h2
      rw [show A + n - B = (A - B) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    split_ifs with h1 h2 h2
    · rw [key _ _ (by omega) (by omega)]
      ext x
      rw [mem_Icc, mem_Icc]
      omega
    · rw [key _ _ (by omega) (by omega)]
      ext x
      rw [mem_Icc, mem_Icc]
      omega
    · omega
    · rw [key _ _ (by omega) (by omega)]
      ext x
      rw [mem_Icc, mem_Icc]
      omega

/-- Classification of the parent legs of child leg `k` (read through `vtx n`): single strip legs of `U`, the block `A_z`,
single strip legs of `V`, the wrapped block `B_y`. -/
theorem pkR_rg_cls {n d₁ iy e jz g : ℕ} (H : pkR_RG n d₁ iy e jz g) {k a : ℕ} (hk : k ∈ Icc 1 (2 * e + 2 * g + 2))
    (ha : a ∈ pkR_blk n (2 * e + 2 * g + 2) (pkR_rgf d₁ iy e jz) k) :
    (k ≤ 2 * e ∧ vtx n a = 2 * iy + k ∧ a = vtx n a) ∨
    (k = 2 * e + 1 ∧ 2 * iy + 2 * e + 1 ≤ vtx n a ∧ vtx n a ≤ 2 * d₁ + 2 * jz + 1 ∧ a = vtx n a) ∨
    (2 * e + 2 ≤ k ∧ k + 1 ≤ 2 * e + 2 * g + 2 ∧ vtx n a + 2 * e = k + 2 * d₁ + 2 * jz ∧ a = vtx n a) ∨
    (k = 2 * e + 2 * g + 2 ∧ 1 ≤ vtx n a ∧ vtx n a ≤ n ∧
      ((2 * d₁ + 2 * jz + 2 * g + 2 ≤ vtx n a ∧ a = vtx n a) ∨ (vtx n a ≤ 2 * iy ∧ a = vtx n a + n))) := by
  have H' := H
  obtain ⟨hE, hn, hd, hj, heg⟩ := H'
  have hk' := mem_Icc.1 hk
  rw [pkR_rg_blkI H hk, mem_Icc, pkR_rgf_def, pkR_rgf_def] at ha
  have hv := pkR_vtx2 (m := n) (i := a) (by omega)
  split_ifs at ha <;> rw [hv (by omega) (by omega)] <;> split_ifs <;> omega

/-- Same-parity tiles on `Λ` vanish away from `c⋆ = (1, n − 1)` and `c⋆′` (both orientations). -/
theorem pkR_rg_vanS {n d₁ : ℕ} {I : Finset (ℕ × ℕ)} {X : ℕ × ℕ → ℚ} (hX : pkR_lam n d₁ I X) {v w : ℕ}
    (hv1 : 1 ≤ v) (hv2 : v ≤ n) (hw1 : 1 ≤ w) (hw2 : w ≤ n) (hp : v % 2 = w % 2) (hne : v ≠ w)
    (h1 : ¬ (v = 1 ∧ w = n - 1)) (h2 : ¬ (w = 1 ∧ v = n - 1)) (h3 : ¬ (d₁ = 0 ∧ v = 2 ∧ w = n))
    (h4 : ¬ (d₁ = 0 ∧ w = 2 ∧ v = n)) (h5 : ¬ (0 < d₁ ∧ v = 2 * d₁ ∧ w = 2 * d₁ + 2))
    (h6 : ¬ (0 < d₁ ∧ w = 2 * d₁ ∧ v = 2 * d₁ + 2)) : mesh n X v w = 0 := by
  have ec : pkR_cstp n d₁ = if d₁ = 0 then (2, n) else (2 * d₁, 2 * d₁ + 2) := rfl
  rcases lt_or_gt_of_ne hne with h | h
  · refine hX.1 v (mem_Icc.2 ⟨hv1, hv2⟩) w (mem_Icc.2 ⟨hw1, hw2⟩) (by omega) hp
      (fun e => h1 ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩) (fun e => ?_)
    rw [ec] at e
    split_ifs at e with h0
    · exact h3 ⟨h0, congrArg Prod.fst e, congrArg Prod.snd e⟩
    · exact h5 ⟨by omega, congrArg Prod.fst e, congrArg Prod.snd e⟩
  · rw [pkR_mesh_comm]
    refine hX.1 w (mem_Icc.2 ⟨hw1, hw2⟩) v (mem_Icc.2 ⟨hv1, hv2⟩) (by omega) hp.symm
      (fun e => h2 ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩) (fun e => ?_)
    rw [ec] at e
    split_ifs at e with h0
    · exact h4 ⟨h0, congrArg Prod.fst e, congrArg Prod.snd e⟩
    · exact h6 ⟨by omega, congrArg Prod.fst e, congrArg Prod.snd e⟩

/-- `minrect(Q)` tiles for a member `Q = (i, j)` in arithmetic form (both orientations). -/
theorem pkR_rg_vanM {n d₁ i j : ℕ} {X : ℕ × ℕ → ℚ} (hj : 2 * d₁ + 2 * j + 2 ≤ n)
    (hm : ∀ t ∈ pkR_minrect n d₁ (i, j), mesh n X t.1 t.2 = 0) {v w : ℕ}
    (hv1 : 1 ≤ v) (hv2 : v ≤ n) (hvo : v % 2 = 1) (hvA : v < 2 * i + 1 ∨ 2 * d₁ + 2 * j + 1 < v)
    (hwe : w % 2 = 0) (hw1 : 2 * i + 1 ≤ w) (hw2 : w ≤ 2 * d₁ + 2 * j + 1) (hd : i ≤ d₁) :
    mesh n X v w = 0 ∧ mesh n X w v = 0 := by
  have h : mesh n X v w = 0 := by
    refine hm (v, w) ?_
    rw [pkR_mem_minrect, pkR_mem_head, pkR_mem_head]
    dsimp only
    exact ⟨⟨mem_Icc.2 ⟨hv1, hv2⟩, hvo, by omega, by omega⟩, ⟨mem_Icc.2 ⟨by omega, by omega⟩, hwe, by omega, by omega, by omega⟩⟩
  exact ⟨h, by rw [pkR_mesh_comm]; exact h⟩

set_option maxHeartbeats 4000000 in
/-- **Parent terms of a child tile** of the region: for child legs `k + 2 ≤ l` of equal parity, every parent tile in the
block product vanishes on `Λ ∧ minrect(y) ∧ minrect(z)`, except the three special terms (`c⋆` when `y = a`, `c⋆′` when
`z = b`), which are excluded by hypothesis. -/
theorem pkR_rg_term {n d₁ iy e jz g : ℕ} (H : pkR_RG n d₁ iy e jz g) {I : Finset (ℕ × ℕ)} {X : ℕ × ℕ → ℚ}
    (hX : pkR_lam n d₁ I X) (hmy : ∀ t ∈ pkR_minrect n d₁ (iy, jz + g), mesh n X t.1 t.2 = 0)
    (hmz : ∀ t ∈ pkR_minrect n d₁ (iy + e, jz), mesh n X t.1 t.2 = 0)
    {k l a b : ℕ} (hk : k ∈ Icc 1 (2 * e + 2 * g + 2)) (hl : l ∈ Icc 1 (2 * e + 2 * g + 2)) (hkl : k + 2 ≤ l)
    (hp : k % 2 = l % 2) (ha : a ∈ pkR_blk n (2 * e + 2 * g + 2) (pkR_rgf d₁ iy e jz) k)
    (hb : b ∈ pkR_blk n (2 * e + 2 * g + 2) (pkR_rgf d₁ iy e jz) l)
    (s1 : k = 1 → l = 2 * e + 2 * g + 1 → iy = 0 → 2 * d₁ + 2 * jz + 2 * g + 2 = n → ¬ (a = 1 ∧ b = n - 1))
    (s2 : e = 0 → k = 2 → l = 2 * e + 2 * g + 2 → iy = d₁ → jz = 0 → ¬ (a = 2 * d₁ + 2 ∧ b = 2 * d₁ + n))
    (s3 : 1 ≤ e → k = 2 * e → l = 2 * e + 2 → iy + e = d₁ → jz = 0 → ¬ (a = 2 * d₁ ∧ b = 2 * d₁ + 2)) :
    mesh n X a b = 0 := by
  have ca := pkR_rg_cls H hk ha
  have cb := pkR_rg_cls H hl hb
  obtain ⟨hE, hn, hd, hj, heg⟩ := H
  rw [pkR_mesh_vtx (by omega) X a b]
  obtain ⟨V, hV⟩ : ∃ V, V = vtx n a := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = vtx n b := ⟨_, rfl⟩
  rw [← hV] at ca
  rw [← hW] at cb
  rw [← hV, ← hW]
  have hk' := mem_Icc.1 hk
  have hl' := mem_Icc.1 hl
  rcases ca with ⟨k1, a1, a2⟩ | ⟨k1, a1, a2, a3⟩ | ⟨k1, k2, a1, a2⟩ | ⟨k1, a1, a2, a3⟩ <;>
    rcases cb with ⟨l1, b1, b2⟩ | ⟨l1, b1, b2, b3⟩ | ⟨l1, l2, b1, b2⟩ | ⟨l1, b1, b2, b3⟩
  -- U × U
  · exact pkR_rg_vanS hX (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)
  -- U × Z
  · rcases Nat.mod_two_eq_zero_or_one W with hw | hw
    · exact (pkR_rg_vanM (i := iy + e) (j := jz) (by omega) hmz (v := V) (w := W) (by omega) (by omega) (by omega)
        (by omega) hw (by omega) (by omega) (by omega)).1
    · exact pkR_rg_vanS hX (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)
  -- U × V
  · exact pkR_rg_vanS hX (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)
  -- U × Y
  · rcases Nat.mod_two_eq_zero_or_one W with hw | hw
    · exact pkR_rg_vanS hX (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)
    · exact (pkR_rg_vanM (i := iy) (j := jz + g) (by omega) hmy (v := W) (w := V) (by omega) (by omega) hw
        (by omega) (by omega) (by omega) (by omega) (by omega)).2
  · omega
  · omega
  -- Z × V
  · rcases Nat.mod_two_eq_zero_or_one V with hv | hv
    · exact (pkR_rg_vanM (i := iy + e) (j := jz) (by omega) hmz (v := W) (w := V) (by omega) (by omega) (by omega)
        (by omega) hv (by omega) (by omega) (by omega)).2
    · exact pkR_rg_vanS hX (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)
  · omega
  · omega
  · omega
  -- V × V
  · exact pkR_rg_vanS hX (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)
  -- V × Y
  · rcases Nat.mod_two_eq_zero_or_one W with hw | hw
    · exact pkR_rg_vanS hX (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)
    · exact (pkR_rg_vanM (i := iy) (j := jz + g) (by omega) hmy (v := W) (w := V) (by omega) (by omega) hw
        (by omega) (by omega) (by omega) (by omega) (by omega)).2
  · omega
  · omega
  · omega
  · omega

/-- A double sum whose summand is an indicator of one pair. -/
theorem pkR_dsum1 {A B : Finset ℕ} {u w : ℕ} (hu : u ∈ A) (hw : w ∈ B) (G : ℕ → ℕ → ℚ) (c : ℚ)
    (h : ∀ a ∈ A, ∀ b ∈ B, G a b = if a = u ∧ b = w then c else 0) :
    Finset.sum A (fun a => Finset.sum B (fun b => G a b)) = c := by
  rw [sum_congr rfl (fun a ha => sum_congr rfl (fun b hb => h a ha b hb)),
    sum_eq_single_of_mem u hu (fun a _ hne => sum_eq_zero (fun b _ => ite_eq_right (fun hh => hne hh.1))),
    sum_eq_single_of_mem w hw (fun b _ hne => ite_eq_right (fun hh => hne hh.2)), ite_eq_left ⟨rfl, rfl⟩]

/-- **[Region](ii), same-parity tiles**: every same-parity tile of the region point other than its `c⋆`, `c⋆′` vanishes. -/
theorem pkR_rg_sp {n d₁ iy e jz g : ℕ} (H : pkR_RG n d₁ iy e jz g) {I : Finset (ℕ × ℕ)} {X : ℕ × ℕ → ℚ}
    (hX : pkR_lam n d₁ I X) (hmy : ∀ t ∈ pkR_minrect n d₁ (iy, jz + g), mesh n X t.1 t.2 = 0)
    (hmz : ∀ t ∈ pkR_minrect n d₁ (iy + e, jz), mesh n X t.1 t.2 = 0)
    {k l : ℕ} (hk : k ∈ Icc 1 (2 * e + 2 * g + 2)) (hl : l ∈ Icc 1 (2 * e + 2 * g + 2)) (hkl : k + 2 ≤ l)
    (hp : k % 2 = l % 2) (h1 : (k, l) ≠ (1, 2 * e + 2 * g + 2 - 1)) (h2 : (k, l) ≠ pkR_cstp (2 * e + 2 * g + 2) e) :
    mesh (2 * e + 2 * g + 2) (pkR_subX n (pkR_rgf d₁ iy e jz) X) k l = 0 := by
  have H' := H
  obtain ⟨hE, hn, hd, hj, heg⟩ := H'
  have hk' := mem_Icc.1 hk
  have hl' := mem_Icc.1 hl
  have ec : pkR_cstp (2 * e + 2 * g + 2) e = if e = 0 then (2, 2 * e + 2 * g + 2) else (2 * e, 2 * e + 2) := rfl
  have n1 : ¬ (k = 1 ∧ l = 2 * e + 2 * g + 1) := fun h => h1 (by rw [h.1, h.2, show 2 * e + 2 * g + 2 - 1 = 2 * e + 2 * g + 1 by omega])
  have n2 : ¬ (e = 0 ∧ k = 2 ∧ l = 2 * e + 2 * g + 2) := fun h => h2 (by rw [ec, ite_eq_left h.1, h.2.1, h.2.2])
  have n3 : ¬ (1 ≤ e ∧ k = 2 * e ∧ l = 2 * e + 2) := fun h =>
    h2 (by rw [ec, ite_eq_right (show ¬ e = 0 by omega), h.2.1, h.2.2])
  have hdiag : (min k l, max k l) ∈ diagonals (2 * e + 2 * g + 2) := by
    rw [mem_diagonals]
    dsimp only
    omega
  rw [pkR_subTile (by omega) (by omega) (pkR_rg_cyc H) X hk hl hdiag]
  have B : Finset.sum (pkR_blk n (2 * e + 2 * g + 2) (pkR_rgf d₁ iy e jz) k)
      (fun a => Finset.sum (pkR_blk n (2 * e + 2 * g + 2) (pkR_rgf d₁ iy e jz) l) (fun b => mesh n X a b)) = 0 :=
    sum_eq_zero (fun a ha => sum_eq_zero (fun b hb => pkR_rg_term H hX hmy hmz hk hl hkl hp ha hb
      (fun e1 e2 _ _ => absurd ⟨e1, e2⟩ n1) (fun e0 e1 e2 _ _ => absurd ⟨e0, e1, e2⟩ n2)
      (fun e0 e1 e2 _ _ => absurd ⟨e0, e1, e2⟩ n3)))
  have C1 : (if vtx (2 * e + 2 * g + 2) l = vtx (2 * e + 2 * g + 2) (k + 2) then
      planar n X (pkR_rgf d₁ iy e jz (vtx (2 * e + 2 * g + 2) (k + 1)))
        (pkR_rgf d₁ iy e jz (vtx (2 * e + 2 * g + 2) (k + 2))) else 0) = 0 := by
    rw [vtx_of_mem hl'.1 hl'.2, vtx_of_mem (show 1 ≤ k + 2 by omega) (show k + 2 ≤ 2 * e + 2 * g + 2 by omega),
      vtx_of_mem (show 1 ≤ k + 1 by omega) (show k + 1 ≤ 2 * e + 2 * g + 2 by omega)]
    by_cases hc : l = k + 2
    · rw [ite_eq_left hc, show pkR_rgf d₁ iy e jz (k + 2) = pkR_rgf d₁ iy e jz (k + 1) + 1 by
        rw [pkR_rgf_def, pkR_rgf_def]
        split_ifs <;> omega, pkR_planar_succ (by omega)]
    · rw [ite_eq_right hc]
  have C2 : (if vtx (2 * e + 2 * g + 2) k = vtx (2 * e + 2 * g + 2) (l + 2) then
      planar n X (pkR_rgf d₁ iy e jz (vtx (2 * e + 2 * g + 2) (l + 1)))
        (pkR_rgf d₁ iy e jz (vtx (2 * e + 2 * g + 2) (l + 2))) else 0) = 0 := by
    by_cases hc : vtx (2 * e + 2 * g + 2) k = vtx (2 * e + 2 * g + 2) (l + 2)
    · have hl2 : l = 2 * e + 2 * g + 2 ∧ k = 2 := by
        rw [vtx_of_mem hk'.1 hk'.2, pkR_vtx2 (by omega) (by omega) (by omega)] at hc
        split_ifs at hc <;> omega
      rw [ite_eq_left hc, hl2.1, show 2 * e + 2 * g + 2 + 1 = 1 + (2 * e + 2 * g + 2) by ring,
        show 2 * e + 2 * g + 2 + 2 = 2 + (2 * e + 2 * g + 2) by ring, vtx_add_n, vtx_add_n,
        vtx_of_mem (le_refl 1) (show 1 ≤ 2 * e + 2 * g + 2 by omega),
        vtx_of_mem (show 1 ≤ 2 by omega) (show 2 ≤ 2 * e + 2 * g + 2 by omega),
        show pkR_rgf d₁ iy e jz 2 = pkR_rgf d₁ iy e jz 1 + 1 by
          rw [pkR_rgf_def, pkR_rgf_def]
          split_ifs <;> omega, pkR_planar_succ (by omega)]
    · rw [ite_eq_right hc]
  rw [B, C1, C2]
  norm_num

/-- **[Region](iii)**: the `minrect` conditions of a member `Q` of `I` inside the box are those of the region member
`(Q.1 − iy, Q.2 − jz)`. -/
theorem pkR_rg_mr {n d₁ iy e jz g : ℕ} (H : pkR_RG n d₁ iy e jz g) {I : Finset (ℕ × ℕ)} {X : ℕ × ℕ → ℚ}
    (hX : pkR_lam n d₁ I X) {Q : ℕ × ℕ} (hQ : Q ∈ I) (hQ1 : iy ≤ Q.1) (hQ2 : Q.1 ≤ iy + e) (hQ3 : jz ≤ Q.2)
    (hQ4 : Q.2 ≤ jz + g) {t : ℕ × ℕ} (ht : t ∈ pkR_minrect (2 * e + 2 * g + 2) e (Q.1 - iy, Q.2 - jz)) :
    mesh (2 * e + 2 * g + 2) (pkR_subX n (pkR_rgf d₁ iy e jz) X) t.1 t.2 = 0 := by
  have H' := H
  obtain ⟨hE, hn, hd, hj, heg⟩ := H'
  obtain ⟨w, c⟩ := t
  rw [pkR_mem_minrect, pkR_mem_head, pkR_mem_head] at ht
  obtain ⟨⟨w1, w2, w3, w4⟩, ⟨c1, c2, c3, c4⟩⟩ := ht
  dsimp only at w1 w2 w3 w4 c1 c2 c3 c4 ⊢
  have w1' := mem_Icc.1 w1
  have c1' := mem_Icc.1 c1
  have hdiag : (min w c, max w c) ∈ diagonals (2 * e + 2 * g + 2) := by
    rw [mem_diagonals]
    dsimp only
    omega
  rw [pkR_subTile (by omega) (by omega) (pkR_rg_cyc H) X w1 c1 hdiag]
  have B : Finset.sum (pkR_blk n (2 * e + 2 * g + 2) (pkR_rgf d₁ iy e jz) w)
      (fun a => Finset.sum (pkR_blk n (2 * e + 2 * g + 2) (pkR_rgf d₁ iy e jz) c) (fun b => mesh n X a b)) = 0 := by
    refine sum_eq_zero (fun a ha => sum_eq_zero (fun b hb => ?_))
    have ca := pkR_rg_cls H w1 ha
    have cb := pkR_rg_cls H c1 hb
    have fa : 1 ≤ a ∧ a ≤ n ∧ ((w ≤ 2 * e ∧ a = 2 * iy + w) ∨ (2 * e + 2 ≤ w ∧ a + 2 * e = w + 2 * d₁ + 2 * jz)) := by
      omega
    have fb : 1 ≤ b ∧ b ≤ n ∧ ((c ≤ 2 * e ∧ b = 2 * iy + c) ∨ (2 * e + 2 ≤ c ∧ b + 2 * e = c + 2 * d₁ + 2 * jz)) := by
      omega
    refine hX.2.2 Q hQ (a, b) ?_
    rw [pkR_mem_minrect, pkR_mem_head, pkR_mem_head]
    dsimp only
    exact ⟨⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega, by omega, by omega⟩,
      ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega, by omega, by omega⟩⟩
  have C1 : ¬ vtx (2 * e + 2 * g + 2) c = vtx (2 * e + 2 * g + 2) (w + 2) := by
    rw [vtx_of_mem c1'.1 c1'.2, pkR_vtx2 (by omega) (by omega) (by omega)]
    split_ifs <;> omega
  have C2 : ¬ vtx (2 * e + 2 * g + 2) w = vtx (2 * e + 2 * g + 2) (c + 2) := by
    rw [vtx_of_mem w1'.1 w1'.2, pkR_vtx2 (by omega) (by omega) (by omega)]
    split_ifs <;> omega
  rw [B, ite_eq_right C1, ite_eq_right C2]
  norm_num

/-- **[Region](ii), `x′ = x`**: the tile `c⋆` of the region point (straddling `ŷ`) equals the parent `x`. -/
theorem pkR_rg_x {n d₁ iy e jz g : ℕ} (H : pkR_RG n d₁ iy e jz g) {I : Finset (ℕ × ℕ)} {X : ℕ × ℕ → ℚ}
    (hX : pkR_lam n d₁ I X) (hmy : ∀ t ∈ pkR_minrect n d₁ (iy, jz + g), mesh n X t.1 t.2 = 0)
    (hmz : ∀ t ∈ pkR_minrect n d₁ (iy + e, jz), mesh n X t.1 t.2 = 0) :
    mesh (2 * e + 2 * g + 2) (pkR_subX n (pkR_rgf d₁ iy e jz) X) 1 (2 * e + 2 * g + 1) = mesh n X 1 (n - 1) := by
  have H' := H
  obtain ⟨hE, hn, hd, hj, heg⟩ := H'
  have h1 : 1 ∈ Icc 1 (2 * e + 2 * g + 2) := mem_Icc.2 ⟨le_rfl, by omega⟩
  have h2 : 2 * e + 2 * g + 1 ∈ Icc 1 (2 * e + 2 * g + 2) := mem_Icc.2 ⟨by omega, by omega⟩
  have hdiag : (min 1 (2 * e + 2 * g + 1), max 1 (2 * e + 2 * g + 1)) ∈ diagonals (2 * e + 2 * g + 2) := by
    rw [mem_diagonals]
    dsimp only
    omega
  rw [pkR_subTile (by omega) (by omega) (pkR_rg_cyc H) X h1 h2 hdiag,
    vtx_of_mem (show 1 ≤ 1 + 1 by omega) (show 1 + 1 ≤ 2 * e + 2 * g + 2 by omega),
    vtx_of_mem (show 1 ≤ 1 + 2 by omega) (show 1 + 2 ≤ 2 * e + 2 * g + 2 by omega),
    vtx_of_mem (show 1 ≤ 2 * e + 2 * g + 1 by omega) (show 2 * e + 2 * g + 1 ≤ 2 * e + 2 * g + 2 by omega),
    vtx_of_mem (show 1 ≤ 2 * e + 2 * g + 1 + 1 by omega) (show 2 * e + 2 * g + 1 + 1 ≤ 2 * e + 2 * g + 2 by omega),
    show 2 * e + 2 * g + 1 + 2 = 1 + (2 * e + 2 * g + 2) by ring, vtx_add_n,
    vtx_of_mem (le_refl 1) (show 1 ≤ 2 * e + 2 * g + 2 by omega), ite_eq_left rfl,
    show pkR_rgf d₁ iy e jz (1 + 2) = pkR_rgf d₁ iy e jz (1 + 1) + 1 by
      rw [pkR_rgf_def, pkR_rgf_def]
      split_ifs <;> omega, pkR_planar_succ (by omega), ite_self,
    show pkR_rgf d₁ iy e jz (2 * e + 2 * g + 1 + 1) = 2 * d₁ + 2 * (jz + g) + 2 by
      rw [pkR_rgf_def, ite_eq_right (show ¬ (2 * e + 2 * g + 1 + 1 ≤ 2 * e + 1) by omega)]
      omega,
    show pkR_rgf d₁ iy e jz 1 = 2 * iy + 1 by rw [pkR_rgf_def, ite_eq_left (show 1 ≤ 2 * e + 1 by omega)]]
  by_cases hya : iy = 0 ∧ 2 * d₁ + 2 * jz + 2 * g + 2 = n
  · rw [show 2 * iy + 1 = 1 by omega, show 2 * d₁ + 2 * (jz + g) + 2 = n by omega, pkR_planar_n1 (by omega),
      pkR_dsum1 (u := 1) (w := n - 1) ?_ ?_ (mesh n X) (mesh n X 1 (n - 1)) ?_]
    · ring
    · rw [pkR_rg_blkI H h1, mem_Icc, pkR_rgf_def, pkR_rgf_def]
      split_ifs <;> omega
    · rw [pkR_rg_blkI H h2, mem_Icc, pkR_rgf_def, pkR_rgf_def]
      split_ifs <;> omega
    · intro a ha b hb
      by_cases hh : a = 1 ∧ b = n - 1
      · rw [ite_eq_left hh, hh.1, hh.2]
      · rw [ite_eq_right hh]
        exact pkR_rg_term H hX hmy hmz h1 h2 (by omega) (by omega) ha hb (fun _ _ _ _ => hh)
          (fun _ h _ _ _ => absurd h (by omega)) (fun _ h _ _ _ => absurd h (by omega))
  · rw [sum_eq_zero (fun a ha => sum_eq_zero (fun b hb => pkR_rg_term H hX hmy hmz h1 h2 (by omega) (by omega) ha hb
      (fun _ _ h3 h4 => absurd ⟨h3, h4⟩ hya) (fun _ h _ _ _ => absurd h (by omega)) (fun _ h _ _ _ => absurd h (by omega)))),
      pkR_planar_comm, pkR_XQ hE hn (i := iy) (j := jz + g) (by omega) (by omega) (by omega) (by omega) hX hmy]
    ring

/-- **[Region](ii), `c⋆′ = x`**: the tile `c⋆′` of the region point (straddling `ẑ`) equals the parent `x`. -/
theorem pkR_rg_xp {n d₁ iy e jz g : ℕ} (H : pkR_RG n d₁ iy e jz g) {I : Finset (ℕ × ℕ)} {X : ℕ × ℕ → ℚ}
    (hX : pkR_lam n d₁ I X) (hmy : ∀ t ∈ pkR_minrect n d₁ (iy, jz + g), mesh n X t.1 t.2 = 0)
    (hmz : ∀ t ∈ pkR_minrect n d₁ (iy + e, jz), mesh n X t.1 t.2 = 0) :
    mesh (2 * e + 2 * g + 2) (pkR_subX n (pkR_rgf d₁ iy e jz) X) (pkR_cstp (2 * e + 2 * g + 2) e).1
      (pkR_cstp (2 * e + 2 * g + 2) e).2 = mesh n X 1 (n - 1) := by
  have H' := H
  obtain ⟨hE, hn, hd, hj, heg⟩ := H'
  have ec : pkR_cstp (2 * e + 2 * g + 2) e = if e = 0 then (2, 2 * e + 2 * g + 2) else (2 * e, 2 * e + 2) := rfl
  have ecn : pkR_cstp n d₁ = if d₁ = 0 then (2, n) else (2 * d₁, 2 * d₁ + 2) := rfl
  have hx := hX.2.1
  rw [ecn] at hx
  rw [ec]
  split_ifs with he
  · dsimp only
    have h1 : 2 ∈ Icc 1 (2 * e + 2 * g + 2) := mem_Icc.2 ⟨by omega, by omega⟩
    have h2 : 2 * e + 2 * g + 2 ∈ Icc 1 (2 * e + 2 * g + 2) := mem_Icc.2 ⟨by omega, le_rfl⟩
    have hdiag : (min 2 (2 * e + 2 * g + 2), max 2 (2 * e + 2 * g + 2)) ∈ diagonals (2 * e + 2 * g + 2) := by
      rw [mem_diagonals]
      dsimp only
      omega
    rw [pkR_subTile (by omega) (by omega) (pkR_rg_cyc H) X h1 h2 hdiag,
      vtx_of_mem (show 1 ≤ 2 + 1 by omega) (show 2 + 1 ≤ 2 * e + 2 * g + 2 by omega),
      vtx_of_mem (show 1 ≤ 2 + 2 by omega) (show 2 + 2 ≤ 2 * e + 2 * g + 2 by omega),
      vtx_of_mem (show 1 ≤ 2 by omega) (show 2 ≤ 2 * e + 2 * g + 2 by omega),
      vtx_of_mem (show 1 ≤ 2 * e + 2 * g + 2 by omega) (le_refl (2 * e + 2 * g + 2)),
      show 2 * e + 2 * g + 2 + 1 = 1 + (2 * e + 2 * g + 2) by ring,
      show 2 * e + 2 * g + 2 + 2 = 2 + (2 * e + 2 * g + 2) by ring, vtx_add_n, vtx_add_n,
      vtx_of_mem (le_refl 1) (show 1 ≤ 2 * e + 2 * g + 2 by omega),
      vtx_of_mem (show 1 ≤ 2 by omega) (show 2 ≤ 2 * e + 2 * g + 2 by omega), ite_eq_left rfl,
      show pkR_rgf d₁ iy e jz (2 + 2) = pkR_rgf d₁ iy e jz (2 + 1) + 1 by
        rw [pkR_rgf_def, pkR_rgf_def]
        split_ifs <;> omega, pkR_planar_succ (by omega), ite_self,
      show pkR_rgf d₁ iy e jz 2 = 2 * d₁ + 2 * jz + 2 by
        rw [pkR_rgf_def, ite_eq_right (show ¬ (2 ≤ 2 * e + 1) by omega)]
        omega,
      show pkR_rgf d₁ iy e jz 1 = 2 * (iy + e) + 1 by
        rw [pkR_rgf_def, ite_eq_left (show 1 ≤ 2 * e + 1 by omega)]
        omega]
    by_cases hzb : iy + e = d₁ ∧ jz = 0
    · rw [show 2 * d₁ + 2 * jz + 2 = 2 * (iy + e) + 1 + 1 by omega, pkR_planar_succ (by omega),
        pkR_dsum1 (u := 2 * d₁ + 2) (w := 2 * d₁ + n) ?_ ?_ (mesh n X) (mesh n X 1 (n - 1)) ?_]
      · ring
      · rw [pkR_rg_blkI H h1, mem_Icc, pkR_rgf_def, pkR_rgf_def]
        split_ifs <;> omega
      · rw [pkR_rg_blkI H h2, mem_Icc, pkR_rgf_def]
        split_ifs <;> omega
      · intro a ha b hb
        by_cases hh : a = 2 * d₁ + 2 ∧ b = 2 * d₁ + n
        · rw [ite_eq_left hh, hh.1, hh.2, pkR_mesh_vtx (by omega) X, vtx_add_n,
            vtx_of_mem (show 1 ≤ 2 * d₁ + 2 by omega) (show 2 * d₁ + 2 ≤ n by omega), hx]
          split_ifs with h0
          · rw [h0, show 2 * 0 = 0 by rfl, show vtx n 0 = vtx n (0 + n) by rw [vtx_add_n],
              zero_add n, vtx_of_mem (show 1 ≤ n by omega) (le_refl n)]
          · rw [vtx_of_mem (show 1 ≤ 2 * d₁ by omega) (show 2 * d₁ ≤ n by omega), pkR_mesh_comm]
        · rw [ite_eq_right hh]
          exact pkR_rg_term H hX hmy hmz h1 h2 (by omega) (by omega) ha hb (fun h _ _ _ => absurd h (by omega))
            (fun _ _ _ _ _ => hh) (fun h _ _ _ _ => absurd h (by omega))
    · rw [sum_eq_zero (fun a ha => sum_eq_zero (fun b hb => pkR_rg_term H hX hmy hmz h1 h2 (by omega) (by omega) ha hb
        (fun h _ _ _ => absurd h (by omega)) (fun _ _ _ h3 h4 => absurd ⟨by omega, h4⟩ hzb)
        (fun h _ _ _ _ => absurd h (by omega)))),
        pkR_XQ hE hn (i := iy + e) (j := jz) (by omega) (by omega) hzb (by omega) hX hmz]
      ring
  · dsimp only
    have h1 : 2 * e ∈ Icc 1 (2 * e + 2 * g + 2) := mem_Icc.2 ⟨by omega, by omega⟩
    have h2 : 2 * e + 2 ∈ Icc 1 (2 * e + 2 * g + 2) := mem_Icc.2 ⟨by omega, by omega⟩
    have hdiag : (min (2 * e) (2 * e + 2), max (2 * e) (2 * e + 2)) ∈ diagonals (2 * e + 2 * g + 2) := by
      rw [mem_diagonals]
      dsimp only
      omega
    rw [pkR_subTile (by omega) (by omega) (pkR_rg_cyc H) X h1 h2 hdiag, ite_eq_left rfl,
      vtx_of_mem (show 1 ≤ 2 * e + 1 by omega) (show 2 * e + 1 ≤ 2 * e + 2 * g + 2 by omega),
      vtx_of_mem (show 1 ≤ 2 * e + 2 by omega) (show 2 * e + 2 ≤ 2 * e + 2 * g + 2 by omega),
      show pkR_rgf d₁ iy e jz (2 * e + 2) = 2 * d₁ + 2 * jz + 2 by
        rw [pkR_rgf_def, ite_eq_right (show ¬ (2 * e + 2 ≤ 2 * e + 1) by omega)]
        omega,
      show pkR_rgf d₁ iy e jz (2 * e + 1) = 2 * (iy + e) + 1 by
        rw [pkR_rgf_def, ite_eq_left (show 2 * e + 1 ≤ 2 * e + 1 by omega)]
        omega]
    have C2 : (if vtx (2 * e + 2 * g + 2) (2 * e) = vtx (2 * e + 2 * g + 2) (2 * e + 2 + 2) then
        planar n X (pkR_rgf d₁ iy e jz (vtx (2 * e + 2 * g + 2) (2 * e + 2 + 1)))
          (pkR_rgf d₁ iy e jz (vtx (2 * e + 2 * g + 2) (2 * e + 2 + 2))) else 0) = 0 := by
      by_cases hc : vtx (2 * e + 2 * g + 2) (2 * e) = vtx (2 * e + 2 * g + 2) (2 * e + 2 + 2)
      · have hl2 : e = 1 ∧ g = 0 := by
          rw [vtx_of_mem (show 1 ≤ 2 * e by omega) (show 2 * e ≤ 2 * e + 2 * g + 2 by omega),
            pkR_vtx2 (by omega) (by omega) (by omega)] at hc
          split_ifs at hc <;> omega
        rw [ite_eq_left hc, pkR_vtx2 (m := 2 * e + 2 * g + 2) (i := 2 * e + 2 + 1) (by omega) (by omega) (by omega),
          pkR_vtx2 (m := 2 * e + 2 * g + 2) (i := 2 * e + 2 + 2) (by omega) (by omega) (by omega),
          ite_eq_right (show ¬ (2 * e + 2 + 1 ≤ 2 * e + 2 * g + 2) by omega),
          ite_eq_right (show ¬ (2 * e + 2 + 2 ≤ 2 * e + 2 * g + 2) by omega),
          show pkR_rgf d₁ iy e jz (2 * e + 2 + 2 - (2 * e + 2 * g + 2)) =
            pkR_rgf d₁ iy e jz (2 * e + 2 + 1 - (2 * e + 2 * g + 2)) + 1 by
            rw [pkR_rgf_def, pkR_rgf_def]
            split_ifs <;> omega, pkR_planar_succ (by omega)]
      · rw [ite_eq_right hc]
    rw [C2]
    by_cases hzb : iy + e = d₁ ∧ jz = 0
    · rw [show 2 * d₁ + 2 * jz + 2 = 2 * (iy + e) + 1 + 1 by omega, pkR_planar_succ (by omega),
        pkR_dsum1 (u := 2 * d₁) (w := 2 * d₁ + 2) ?_ ?_ (mesh n X) (mesh n X 1 (n - 1)) ?_]
      · ring
      · rw [pkR_rg_blkI H h1, mem_Icc, pkR_rgf_def, pkR_rgf_def]
        split_ifs <;> omega
      · rw [pkR_rg_blkI H h2, mem_Icc, pkR_rgf_def, pkR_rgf_def]
        split_ifs <;> omega
      · intro a ha b hb
        by_cases hh : a = 2 * d₁ ∧ b = 2 * d₁ + 2
        · rw [ite_eq_left hh, hh.1, hh.2, hx, ite_eq_right (show ¬ d₁ = 0 by omega)]
        · rw [ite_eq_right hh]
          exact pkR_rg_term H hX hmy hmz h1 h2 (by omega) (by omega) ha hb (fun h _ _ _ => absurd h (by omega))
            (fun h _ _ _ _ => absurd h (by omega)) (fun _ _ _ _ _ => hh)
    · rw [sum_eq_zero (fun a ha => sum_eq_zero (fun b hb => pkR_rg_term H hX hmy hmz h1 h2 (by omega) (by omega) ha hb
        (fun h _ _ _ => absurd h (by omega)) (fun h _ _ _ _ => absurd h (by omega))
        (fun _ _ _ h3 h4 => absurd ⟨h3, h4⟩ hzb))),
        pkR_XQ hE hn (i := iy + e) (j := jz) (by omega) (by omega) hzb (by omega) hX hmz]
      ring

/-- **[Region](ii)+(iii)** (PREFORM-Res §3.3, R11): for members (or the massive legs) `y = (iy, jz + g) ≻ z = (iy + e, jz)`
of the standard polygon `(n, d₁)`, on `Λ^I` with `minrect(y) = minrect(z) = 0` the region point `subX f_{y,z} X` lies on
`Λ^{I′}` of the standard polygon `(2e + 2g + 2, e)`, `I′` = the members of `I` in the box shifted by `(iy, jz)`, and
`x′ = x`. -/
theorem pkR_region {n d₁ iy e jz g : ℕ} (H : pkR_RG n d₁ iy e jz g) {I : Finset (ℕ × ℕ)} {X : ℕ × ℕ → ℚ}
    (hX : pkR_lam n d₁ I X) (hmy : ∀ t ∈ pkR_minrect n d₁ (iy, jz + g), mesh n X t.1 t.2 = 0)
    (hmz : ∀ t ∈ pkR_minrect n d₁ (iy + e, jz), mesh n X t.1 t.2 = 0) :
    pkR_lam (2 * e + 2 * g + 2) e
        ((I.filter (fun Q => iy ≤ Q.1 ∧ Q.1 ≤ iy + e ∧ jz ≤ Q.2 ∧ Q.2 ≤ jz + g)).image
          (fun Q => (Q.1 - iy, Q.2 - jz))) (pkR_subX n (pkR_rgf d₁ iy e jz) X) ∧
      mesh (2 * e + 2 * g + 2) (pkR_subX n (pkR_rgf d₁ iy e jz) X) 1 (2 * e + 2 * g + 2 - 1) = mesh n X 1 (n - 1) := by
  have hx := pkR_rg_x H hX hmy hmz
  have hxp := pkR_rg_xp H hX hmy hmz
  have e1 : 2 * e + 2 * g + 2 - 1 = 2 * e + 2 * g + 1 := by omega
  refine ⟨(pkR_lam_iff _ _ _ _).2 ⟨fun a ha b hb h1 h2 h3 h4 => pkR_rg_sp H hX hmy hmz ha hb h1 h2 h3 h4, ?_, ?_⟩, ?_⟩
  · rw [e1, hx, hxp]
  · intro Q' hQ' t ht
    obtain ⟨Q, hQf, rfl⟩ := mem_image.1 hQ'
    obtain ⟨hQ, q1, q2, q3, q4⟩ := mem_filter.1 hQf
    exact pkR_rg_mr H hX hQ q1 q2 q3 q4 ht
  · rw [e1, hx]

-- c1d: (G_W), X_Q vs X_Q′ (PREFORM-Res §3.4, R13; plan `scratch_pkR/c1c/gwcase.py`, choice `scratch_pkR/c1d/dtree.py`)

/-- The rank-one witness lies on `W_q` when `(w, c)` is not a `minrect(q)` entry. -/
theorem pkR_rk_W {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ : ℕ} (hd : 2 * d₁ + 2 ≤ n) {w c : ℕ} (hw : w % 2 = 1)
    (hw1 : 1 ≤ w) (hwn : w ≤ n) (hwr : w ≠ 2 * d₁ + 1) (hc : c % 2 = 0) (hc1 : 2 ≤ c) (hcn : c + 2 ≤ n) {a b : ℕ}
    (hq : ¬ (¬ (2 * a + 1 ≤ w ∧ w ≤ 2 * d₁ + 2 * b + 1) ∧ (2 * a + 1 ≤ c ∧ c ≤ 2 * d₁ + 2 * b + 1))) :
    pkR_W n d₁ (a, b) (pkR_rk n d₁ w c) := by
  obtain ⟨l1, -⟩ := pkR_rk_lam hE hn hd hw hw1 hwn hwr hc hc1 hcn (I := {(a, b)}) (fun Q hQ => by
    rw [mem_singleton] at hQ
    rw [hQ]
    exact hq)
  obtain ⟨s1, -, s3⟩ := l1
  exact ⟨fun x hx y hy e1 e2 e3 e4 _ => s1 x hx y hy e1 e2 e3 e4, s3 (a, b) (mem_singleton_self _)⟩

/-- The rank-one witness vanishes at a member chord `Q` when `(w, c)` is not a `minrect(Q)` entry. -/
theorem pkR_rk_mz {n d₁ w c x y : ℕ} (hx : x ≤ d₁) (hy : 2 * d₁ + 2 * y + 2 ≤ n)
    (hc1 : 2 ≤ c) (hcn : c + 2 ≤ n)
    (hQ : ¬ (¬ (2 * x + 1 ≤ w ∧ w ≤ 2 * d₁ + 2 * y + 1) ∧ (2 * x + 1 ≤ c ∧ c ≤ 2 * d₁ + 2 * y + 1))) :
    pkR_rk n d₁ w c (pkR_mchord d₁ (x, y)) = 0 := by
  rw [pkR_rk_def]
  show pkR_fhPt _ _ (2 * x + 1, 2 * d₁ + 2 * y + 2) = 0
  rw [pkR_fhPt_def]
  by_cases h : 2 * x + 1 ≤ w ∧ w ≤ 2 * d₁ + 2 * y + 1
  · rw [show pkR_ivl (min ((w + 1) / 2) (d₁ + 1)) (max ((w + 1) / 2) (d₁ + 1)) ((2 * d₁ + 2 * y + 2) / 2) -
        pkR_ivl (min ((w + 1) / 2) (d₁ + 1)) (max ((w + 1) / 2) (d₁ + 1)) ((2 * x + 1) / 2) = 0 by
      rw [pkR_ivl_def, pkR_ivl_def]
      split_ifs <;> (try omega) <;> norm_num]
    ring
  · rw [show pkR_ivl (c / 2 + 1) (n / 2 + 1) ((2 * d₁ + 2 * y + 2 + 1) / 2) -
        pkR_ivl (c / 2 + 1) (n / 2 + 1) ((2 * x + 1 + 1) / 2) = 0 by
      rw [pkR_ivl_def, pkR_ivl_def]
      split_ifs <;> (try omega) <;> norm_num]
    ring

/-- The rank-one witness is non-zero at a member chord `Q` when `(w, c)` is a `minrect(Q)` entry. -/
theorem pkR_rk_mnz {n d₁ w c x y : ℕ} (hE : n % 2 = 0) (hx : x ≤ d₁) (hy : 2 * d₁ + 2 * y + 2 ≤ n)
    (hb : ¬ (x = d₁ ∧ y = 0)) (ha : ¬ (x = 0 ∧ 2 * d₁ + 2 * y + 2 = n)) (hw : w % 2 = 1) (hc : c % 2 = 0) (hc1 : 2 ≤ c)
    (hQ : ¬ (2 * x + 1 ≤ w ∧ w ≤ 2 * d₁ + 2 * y + 1) ∧ (2 * x + 1 ≤ c ∧ c ≤ 2 * d₁ + 2 * y + 1)) :
    pkR_rk n d₁ w c (pkR_mchord d₁ (x, y)) ≠ 0 :=
  pkR_rk_ne (p := 2 * x + 1) (q := 2 * d₁ + 2 * y + 2) hE (pkR_mchord_mem hx hy hb ha) hw hc hc1 (by omega) (by omega)

set_option maxHeartbeats 4000000 in
/-- **Rectangle choice for (G_W)** (c1d; checked in Python `scratch_pkR/c1d/dtree.py`, n ≤ 26, 1 308 846 triples, 0 failures):
for distinct standard members `q = (a, b)`, `Q = (i, j)`, `Q′ = (k, l)`, either one `minrect` pair `t = (w, c)` lies in
`minrect(Q′) ∖ (minrect(Q) ∪ minrect(q))`, or `t ∈ minrect(Q′) ∩ minrect(Q) ∖ minrect(q)` and
`t′ ∈ minrect(Q) ∖ (minrect(Q′) ∪ minrect(q))`. -/
theorem pkR_GW_choose {n d₁ a b i j k l : ℕ} (hE : n % 2 = 0)
    (ha1 : a ≤ d₁) (ha2 : 2 * d₁ + 2 * b + 2 ≤ n) (ha3 : a + 1 ≤ d₁ + b) (ha4 : 1 ≤ a ∨ 2 * d₁ + 2 * b + 4 ≤ n)
    (hi1 : i ≤ d₁) (hi2 : 2 * d₁ + 2 * j + 2 ≤ n) (hi3 : i + 1 ≤ d₁ + j) (hi4 : 1 ≤ i ∨ 2 * d₁ + 2 * j + 4 ≤ n)
    (hk1 : k ≤ d₁) (hk2 : 2 * d₁ + 2 * l + 2 ≤ n) (hk3 : k + 1 ≤ d₁ + l) (hk4 : 1 ≤ k ∨ 2 * d₁ + 2 * l + 4 ≤ n)
    (h1 : ¬ (i = a ∧ j = b)) (h2 : ¬ (k = a ∧ l = b)) (h3 : ¬ (k = i ∧ l = j)) :
    (∃ w c : ℕ, (w % 2 = 1 ∧ 1 ≤ w ∧ w ≤ n ∧ w ≠ 2 * d₁ + 1 ∧ c % 2 = 0 ∧ 2 ≤ c ∧ c + 2 ≤ n) ∧
      (¬ (2 * k + 1 ≤ w ∧ w ≤ 2 * d₁ + 2 * l + 1) ∧ (2 * k + 1 ≤ c ∧ c ≤ 2 * d₁ + 2 * l + 1)) ∧
      ¬ (¬ (2 * i + 1 ≤ w ∧ w ≤ 2 * d₁ + 2 * j + 1) ∧ (2 * i + 1 ≤ c ∧ c ≤ 2 * d₁ + 2 * j + 1)) ∧
      ¬ (¬ (2 * a + 1 ≤ w ∧ w ≤ 2 * d₁ + 2 * b + 1) ∧ (2 * a + 1 ≤ c ∧ c ≤ 2 * d₁ + 2 * b + 1))) ∨
    (∃ w c w' c' : ℕ, (w % 2 = 1 ∧ 1 ≤ w ∧ w ≤ n ∧ w ≠ 2 * d₁ + 1 ∧ c % 2 = 0 ∧ 2 ≤ c ∧ c + 2 ≤ n) ∧
      (w' % 2 = 1 ∧ 1 ≤ w' ∧ w' ≤ n ∧ w' ≠ 2 * d₁ + 1 ∧ c' % 2 = 0 ∧ 2 ≤ c' ∧ c' + 2 ≤ n) ∧
      (¬ (2 * k + 1 ≤ w ∧ w ≤ 2 * d₁ + 2 * l + 1) ∧ (2 * k + 1 ≤ c ∧ c ≤ 2 * d₁ + 2 * l + 1)) ∧
      (¬ (2 * i + 1 ≤ w ∧ w ≤ 2 * d₁ + 2 * j + 1) ∧ (2 * i + 1 ≤ c ∧ c ≤ 2 * d₁ + 2 * j + 1)) ∧
      ¬ (¬ (2 * a + 1 ≤ w ∧ w ≤ 2 * d₁ + 2 * b + 1) ∧ (2 * a + 1 ≤ c ∧ c ≤ 2 * d₁ + 2 * b + 1)) ∧
      (¬ (2 * i + 1 ≤ w' ∧ w' ≤ 2 * d₁ + 2 * j + 1) ∧ (2 * i + 1 ≤ c' ∧ c' ≤ 2 * d₁ + 2 * j + 1)) ∧
      ¬ (¬ (2 * k + 1 ≤ w' ∧ w' ≤ 2 * d₁ + 2 * l + 1) ∧ (2 * k + 1 ≤ c' ∧ c' ≤ 2 * d₁ + 2 * l + 1)) ∧
      ¬ (¬ (2 * a + 1 ≤ w' ∧ w' ≤ 2 * d₁ + 2 * b + 1) ∧ (2 * a + 1 ≤ c' ∧ c' ≤ 2 * d₁ + 2 * b + 1))) := by
  by_cases A : 1 ≤ k ∧ i ≠ k ∧ a ≠ k
  · exact Or.inl ⟨2 * k - 1, 2 * k + 2, by omega⟩
  by_cases B : 2 * d₁ + 2 * l + 4 ≤ n ∧ j ≠ l ∧ b ≠ l
  · exact Or.inl ⟨2 * d₁ + 2 * l + 3, 2 * d₁ + 2 * l, by omega⟩
  by_cases C : k = 0
  · by_cases C1 : j = l
    · by_cases C11 : l < b ∨ 0 < a
      · exact Or.inl ⟨2 * d₁ + 2 * l + 3, 2 * k + 2, by omega⟩
      · exact Or.inr ⟨2 * d₁ + 2 * l + 3, 2 * d₁ + 2 * l, 2 * i - 1, 2 * i + 2, by omega⟩
    · by_cases C12 : l < j ∨ 0 < i
      · exact Or.inl ⟨2 * d₁ + 2 * l + 3, 2 * k + 2, by omega⟩
      · exact Or.inr ⟨2 * d₁ + 2 * l + 3, 2, 2 * d₁ + 2 * j + 3, 2, by omega⟩
  by_cases D : 2 * d₁ + 2 * l + 2 = n
  · by_cases D1 : i = k
    · by_cases D11 : a < k ∨ b < l
      · exact Or.inl ⟨2 * k - 1, 2 * d₁ + 2 * l, by omega⟩
      · exact Or.inr ⟨2 * k - 1, 2 * k + 2, 2 * d₁ + 2 * j + 3, 2 * i + 2, by omega⟩
    · by_cases D12 : i < k ∨ j < l
      · exact Or.inl ⟨2 * k - 1, 2 * d₁ + 2 * l, by omega⟩
      · exact Or.inr ⟨2 * k - 1, 2 * d₁ + 2 * l, 2 * i - 1, 2 * i + 2, by omega⟩
  by_cases E : i = k
  · by_cases E1 : j < l ∧ a < k
    · exact Or.inl ⟨2 * k - 1, 2 * d₁ + 2 * l, by omega⟩
    by_cases E2 : l < j ∧ k < a
    · exact Or.inl ⟨2 * d₁ + 2 * l + 3, 2 * k + 2, by omega⟩
    by_cases E3 : j < l
    · exact Or.inr ⟨2 * k - 1, 2 * k + 2, 2 * d₁ + 2 * j + 3, 2 * i + 2, by omega⟩
    · exact Or.inr ⟨2 * k - 1, 2 * k + 2, 2 * i - 1, 2 * d₁ + 2 * j, by omega⟩
  by_cases F1 : i < k ∧ b < l
  · exact Or.inl ⟨2 * k - 1, 2 * d₁ + 2 * l, by omega⟩
  by_cases F2 : k < i ∧ l < b
  · exact Or.inl ⟨2 * d₁ + 2 * l + 3, 2 * k + 2, by omega⟩
  by_cases F3 : i < k
  · exact Or.inr ⟨2 * d₁ + 2 * l + 3, 2 * k + 2, 2 * d₁ + 2 * j + 3, 2 * i + 2, by omega⟩
  · exact Or.inr ⟨2 * k - 1, 2 * d₁ + 2 * l, 2 * i - 1, 2 * i + 2, by omega⟩

/-- **(G_W), `X_Q` vs `X_Q′`** (PREFORM-Res §3.4, R13; R2-Z201 C6): for distinct standard members `q`, `Q`, `Q′`, a point of
`W_q` with `X_Q = 0` and `X_{Q′} ≠ 0` (one rank-one witness, or a combination of two). -/
theorem pkR_GW_pair {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ a b i j k l : ℕ}
    (ha1 : a ≤ d₁) (ha2 : 2 * d₁ + 2 * b + 2 ≤ n) (hab : ¬ (a = d₁ ∧ b = 0)) (haa : ¬ (a = 0 ∧ 2 * d₁ + 2 * b + 2 = n))
    (hi1 : i ≤ d₁) (hi2 : 2 * d₁ + 2 * j + 2 ≤ n) (hib : ¬ (i = d₁ ∧ j = 0)) (hia : ¬ (i = 0 ∧ 2 * d₁ + 2 * j + 2 = n))
    (hk1 : k ≤ d₁) (hk2 : 2 * d₁ + 2 * l + 2 ≤ n) (hkb : ¬ (k = d₁ ∧ l = 0)) (hka : ¬ (k = 0 ∧ 2 * d₁ + 2 * l + 2 = n))
    (h1 : (i, j) ≠ (a, b)) (h2 : (k, l) ≠ (a, b)) (h3 : (k, l) ≠ (i, j)) :
    ∃ X : ℕ × ℕ → ℚ, pkR_W n d₁ (a, b) X ∧ X (pkR_mchord d₁ (i, j)) = 0 ∧ X (pkR_mchord d₁ (k, l)) ≠ 0 := by
  have hd : 2 * d₁ + 2 ≤ n := by omega
  rcases pkR_GW_choose hE ha1 ha2 (by omega) (by omega) hi1 hi2 (by omega) (by omega) hk1 hk2 (by omega) (by omega)
      (pkR_ne_pair h1) (pkR_ne_pair h2) (pkR_ne_pair h3) with
    ⟨w, c, ⟨hw, hw1, hwn, hwr, hc, hc1, hcn⟩, hin, hout, hq⟩ |
    ⟨w, c, w', c', ⟨hw, hw1, hwn, hwr, hc, hc1, hcn⟩, ⟨hw', hw1', hwn', hwr', hc', hc1', hcn'⟩, hin, hinQ, hq, hinQ',
      hout', hq'⟩
  · exact ⟨pkR_rk n d₁ w c, pkR_rk_W hE hn hd hw hw1 hwn hwr hc hc1 hcn hq,
      pkR_rk_mz hi1 hi2 hc1 hcn hout, pkR_rk_mnz hE hk1 hk2 hkb hka hw hc hc1 hin⟩
  · refine ⟨fun p => pkR_rk n d₁ w c p - pkR_rk n d₁ w c (pkR_mchord d₁ (i, j)) /
        pkR_rk n d₁ w' c' (pkR_mchord d₁ (i, j)) * pkR_rk n d₁ w' c' p,
      pkR_W_lc (pkR_rk_W hE hn hd hw hw1 hwn hwr hc hc1 hcn hq) (pkR_rk_W hE hn hd hw' hw1' hwn' hwr' hc' hc1' hcn' hq') _,
      ?_, ?_⟩
    · show pkR_rk n d₁ w c (pkR_mchord d₁ (i, j)) - pkR_rk n d₁ w c (pkR_mchord d₁ (i, j)) /
        pkR_rk n d₁ w' c' (pkR_mchord d₁ (i, j)) * pkR_rk n d₁ w' c' (pkR_mchord d₁ (i, j)) = 0
      exact pkR_elim (pkR_rk_mnz hE hi1 hi2 hib hia hw' hc' hc1' hinQ')
    · show pkR_rk n d₁ w c (pkR_mchord d₁ (k, l)) - pkR_rk n d₁ w c (pkR_mchord d₁ (i, j)) /
        pkR_rk n d₁ w' c' (pkR_mchord d₁ (i, j)) * pkR_rk n d₁ w' c' (pkR_mchord d₁ (k, l)) ≠ 0
      rw [pkR_rk_mz hk1 hk2 hc1' hcn' hout', mul_zero, sub_zero]
      exact pkR_rk_mnz hE hk1 hk2 hkb hka hw hc hc1 hin

-- c1d: the relabelling bridge `pkR_subX` ↔ `X ∘ relab` (for c2: [STnum] on the children of [ResNum])

/-- A cyclic-shift sub-polygon point is the relabelled parent point on child pairs whose image is a parent diagonal
(and `0` otherwise): `subX N (k ↦ vtx N (k + b − 1)) X d = [relab N b d ∈ diagonals N] · X (relab N b d)`. -/
theorem pkR_subX_relab {K : Type*} [Field K] {N : ℕ} (hN : 1 ≤ N) (b : ℕ) (X : ℕ × ℕ → K) (d : ℕ × ℕ) :
    pkR_subX N (fun k => vtx N (k + b - 1)) X d =
      if relab N b d ∈ diagonals N then X (relab N b d) else 0 := by
  show planar N X (vtx N (d.1 + b - 1)) (vtx N (d.2 + b - 1)) = _
  rw [← pkR_planar_vtx hN]
  rfl

/-- `planar m Y` reads `Y` only on the diagonals of the `m`-gon. -/
theorem pkR_planar_congrD {K : Type*} [Field K] {m : ℕ} {Y Y' : ℕ × ℕ → K} (h : ∀ d ∈ diagonals m, Y d = Y' d)
    (i j : ℕ) : planar m Y i j = planar m Y' i j := by
  rw [pkR_planar_def, pkR_planar_def m Y']
  by_cases hd : (min (vtx m i) (vtx m j), max (vtx m i) (vtx m j)) ∈ diagonals m
  · rw [ite_eq_left hd, ite_eq_left hd, h _ hd]
  · rw [ite_eq_right hd, ite_eq_right hd]

theorem pkR_mesh_congrD {K : Type*} [Field K] {m : ℕ} {Y Y' : ℕ × ℕ → K} (h : ∀ d ∈ diagonals m, Y d = Y' d)
    (i j : ℕ) : mesh m Y i j = mesh m Y' i j := by
  rw [pkR_mesh_def, pkR_mesh_def m Y', pkR_planar_congrD h, pkR_planar_congrD h, pkR_planar_congrD h,
    pkR_planar_congrD h]

/-- `OnZT` transfers between points that agree on the diagonals. -/
theorem pkR_onZT_congrD {K : Type*} [Field K] {m : ℕ} {T : Finset ℕ} {Y Y' : ℕ × ℕ → K}
    (h : ∀ d ∈ diagonals m, Y d = Y' d) (hY : OnZT m T Y) : OnZT m T Y' := by
  intro a ha b hb hst
  rw [← pkR_mesh_congrD h]
  exact hY a ha b hb hst

/-- The even legs of an `m`-gon (`m ≥ 4`) are admissible. -/
theorem pkR_adm_evens {m : ℕ} (hm : 4 ≤ m) : Admissible m 0 ((Icc 1 m).filter (fun t => t % 2 = 0)) := by
  have h24 : ({2, 4} : Finset ℕ) ⊆ (Icc 1 m).filter (fun t => t % 2 = 0) := by
    intro x hx
    rw [mem_insert, mem_singleton] at hx
    rcases hx with h | h <;> rw [h] <;> exact mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, rfl⟩
  have hc := card_le_card h24
  have e : ({2, 4} : Finset ℕ).card = 2 := by decide
  rw [e] at hc
  show (Icc 1 m).filter (fun t => t % 2 = 0) ⊆ Icc 1 m ∧ 2 ≤ ((Icc 1 m).filter (fun t => t % 2 = 0)).card ∧
    ∀ t ∈ (Icc 1 m).filter (fun t => t % 2 = 0), t % 2 = 0
  exact ⟨filter_subset _ _, hc, fun t ht => (mem_filter.1 ht).2⟩

/-- Side σ₁ = `[p..q]` in the `relab` labelling: on child diagonals, `X ∘ relab n p` is the sub-polygon point. -/
theorem pkR_relab1 {n p q : ℕ} (hQ : (p, q) ∈ oddDiagonals n) (X : ℕ × ℕ → ℚ) :
    ∀ d ∈ diagonals (q - p + 1), pkR_subX n (fun k => k + p - 1) X d = X (relab n p d) := by
  have hQd := mem_filter.1 hQ
  rw [mem_diagonals] at hQd
  dsimp only at hQd
  intro d hd
  rw [mem_diagonals] at hd
  have e : relab n p d = (d.1 + p - 1, d.2 + p - 1) := by
    show (min (vtx n (d.1 + p - 1)) (vtx n (d.2 + p - 1)), max (vtx n (d.1 + p - 1)) (vtx n (d.2 + p - 1))) = _
    rw [vtx_of_mem (by omega) (by omega), vtx_of_mem (by omega) (by omega), min_eq_left (by omega),
      max_eq_right (by omega)]
  rw [e]
  show planar n X (d.1 + p - 1) (d.2 + p - 1) = _
  rw [planar_of_mem X (by omega) (by omega) (by omega), ite_eq_left (by rw [mem_diagonals]; dsimp only; omega)]

/-- Side σ₂ = `[q..n, 1..p]` in the `relab` labelling: on child diagonals, `X ∘ relab n q` is the sub-polygon point. -/
theorem pkR_relab2 {n p q : ℕ} (hQ : (p, q) ∈ oddDiagonals n) (X : ℕ × ℕ → ℚ) :
    ∀ d ∈ diagonals (n - q + p + 1), pkR_subX n (fun k => vtx n (k + q - 1)) X d = X (relab n q d) := by
  have hQd := mem_filter.1 hQ
  rw [mem_diagonals] at hQd
  dsimp only at hQd
  have hn1 : 1 ≤ n := by omega
  intro d hd
  rw [mem_diagonals] at hd
  rw [pkR_subX_relab hn1 q X d]
  refine ite_eq_left ?_
  show (min (vtx n (d.1 + q - 1)) (vtx n (d.2 + q - 1)), max (vtx n (d.1 + q - 1)) (vtx n (d.2 + q - 1))) ∈ diagonals n
  rw [mem_diagonals]
  dsimp only
  rw [pkR_vtx2 hn1 (by omega) (by omega), pkR_vtx2 hn1 (by omega) (by omega)]
  split_ifs <;> omega

/-- **[SideType] σ₁ in numerator form** (for R9 / c2): under `pkR_side1`'s hypotheses the relabelled child numerator of
[ResNum] vanishes at `X`. -/
theorem pkR_side1_NP {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {p q : ℕ} (hQ : (p, q) ∈ oddDiagonals n)
    {X : ℕ × ℕ → ℚ}
    (H : ∀ a b, p ≤ a → a + 2 ≤ b → b + 1 ≤ q → a % 2 = p % 2 → b % 2 = p % 2 → mesh n X a b = 0)
    (hXQ : X (p, q) = 0) :
    MvPolynomial.eval X (MvPolynomial.rename (relab n p) (NP ℚ (q - p + 1))) = 0 := by
  have hQd := mem_filter.1 hQ
  rw [mem_diagonals] at hQd
  dsimp only at hQd
  rw [MvPolynomial.eval_rename]
  exact pkR_STnum (by omega) (by omega) (by omega) (pkR_adm_evens (by omega)) _
    (pkR_onZT_congrD (pkR_relab1 hQ X) (pkR_side1 hE hn hQ H hXQ))

/-- **[SideType] σ₂ in numerator form**: under `pkR_side2`'s hypotheses the other relabelled child numerator of [ResNum]
vanishes at `X`. -/
theorem pkR_side2_NP {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {p q : ℕ} (hQ : (p, q) ∈ oddDiagonals n)
    {X : ℕ × ℕ → ℚ}
    (H : ∀ a ∈ Icc 1 n, ∀ b ∈ Icc 1 n, a + 2 ≤ b → (a < p ∨ q ≤ a) → (b < p ∨ q ≤ b) → a % 2 = q % 2 →
      b % 2 = q % 2 → mesh n X a b = 0)
    (hXQ : X (p, q) = 0) :
    MvPolynomial.eval X (MvPolynomial.rename (relab n q) (NP ℚ (n - q + p + 1))) = 0 := by
  have hQd := mem_filter.1 hQ
  rw [mem_diagonals] at hQd
  dsimp only at hQd
  rw [MvPolynomial.eval_rename]
  exact pkR_STnum (by omega) (by omega) (by omega) (pkR_adm_evens (by omega)) _
    (pkR_onZT_congrD (pkR_relab2 hQ X) (pkR_side2 hE hn hQ H hXQ))

-- R12-P7b-pkgRes-b (claude-opus-5-5, 2026-09-28): sub-wave b helper block, every name prefixed `pkR_b_`.
-- Splice immediately before the docstring of `resChild_input` in pkgRes/PionCompleteness.lean.
-- Built and checked against the read-only snapshot work/pkgRes-snap-57aa4860.lean (md5 57aa4860…, c1 part 1).
-- Uses only imported 3c-b lemmas (R12P3C: pkSp_*, pkZ_*, AP_eq_zero, AP/NP defs) and base defs; no sub-wave a / c1 helper.

/-! ### pkgRes sub-wave b (R12-P7b-pkgRes-b, claude-opus-5-5): the ¬K amplitude numerators and I3

Source: PREFORM-Res §5.7 (I3 by single-chord recursion) and §8.3 g2 (the δ-order bound for ¬K amplitudes, numerator
form, had no Lean statement). The ¬K amplitude of the `n`-gon is the sum over triangulations avoiding `K` (a set of odd
= mixed diagonals); its numerator is taken over the denominator `∏_{odd d ∉ K} X_d`, exactly as `AP` is for `K = ∅`
(`pkR_b_AP_empty`). Sub-polygons are the base's `relab` children; the child's banned set is the pull-back `pkR_b_pull`.
Iterating the recursion inside a child gives the non-contiguous vertex lists of §5.7 as compositions of `rename`s. -/

/-- The summand of the ¬K numerator (`pkSp_F` with the banned odd diagonals removed from the numerator product). -/
noncomputable def pkR_b_F (R : Type*) [CommRing R] (n : ℕ) (K T : Finset (ℕ × ℕ)) :
    PowerSeries (MvPolynomial (ℕ × ℕ) R) :=
  PowerSeries.C (Finset.prod ((oddDiagonals n \ T) \ K) (fun d => (MvPolynomial.X d : MvPolynomial (ℕ × ℕ) R))) *
    Finset.prod (T.filter (fun d => shiftSign d ≠ 0)) (fun d => shiftSeriesP R d)

/-- Order-`m` numerator of the ¬K amplitude of the `n`-gon: triangulations disjoint from `K`. -/
noncomputable def pkR_b_AP (R : Type*) [CommRing R] (n m : ℕ) (K : Finset (ℕ × ℕ)) : MvPolynomial (ℕ × ℕ) R :=
  PowerSeries.coeff m (Finset.sum ((triangulations n).filter (fun T => Disjoint T K)) (fun T => pkR_b_F R n K T))

/-- Numerator of the ¬K NLSM amplitude (order `n − 2`). -/
noncomputable def pkR_b_NP (R : Type*) [CommRing R] (n : ℕ) (K : Finset (ℕ × ℕ)) : MvPolynomial (ℕ × ℕ) R :=
  pkR_b_AP R n (n - 2) K

/-- Pull-back of a banned set to the child with relabelling base `b` (child size `n`). -/
def pkR_b_pull (N b n : ℕ) (K : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  (diagonals n).filter (fun d => relab N b d ∈ K)

/-- The odd diagonals crossing `C` that are not banned. -/
noncomputable def pkR_b_cross (R : Type*) [CommRing R] (N : ℕ) (K : Finset (ℕ × ℕ)) (C : ℕ × ℕ) :
    MvPolynomial (ℕ × ℕ) R :=
  Finset.prod (((oddDiagonals N).filter (fun d => Crosses d C)) \ K) (fun d => MvPolynomial.X d)

/-- Setting the variables of a predicate to `1`. -/
noncomputable def pkR_b_psi (R : Type*) [CommRing R] (P : ℕ × ℕ → Prop) [DecidablePred P] :
    AlgHom R (MvPolynomial (ℕ × ℕ) R) (MvPolynomial (ℕ × ℕ) R) :=
  MvPolynomial.aeval (fun d => if P d then (1 : MvPolynomial (ℕ × ℕ) R) else MvPolynomial.X d)

theorem pkR_b_psi_X {R : Type*} [CommRing R] (P : ℕ × ℕ → Prop) [DecidablePred P] (d : ℕ × ℕ) :
    pkR_b_psi R P (MvPolynomial.X d) = if P d then 1 else MvPolynomial.X d := by
  show MvPolynomial.aeval _ (MvPolynomial.X d) = _
  rw [MvPolynomial.aeval_X]

/-- `K = ∅` is the full amplitude numerator. -/
theorem pkR_b_AP_empty {R : Type*} [CommRing R] (n m : ℕ) : pkR_b_AP R n m ∅ = AP R n m := by
  have e1 : (triangulations n).filter (fun T => Disjoint T (∅ : Finset (ℕ × ℕ))) = triangulations n :=
    filter_true_of_mem fun T _ => disjoint_empty_right T
  have e2 : ∀ T : Finset (ℕ × ℕ), pkR_b_F R n ∅ T = pkSp_F R n T := by
    intro T
    show PowerSeries.C (Finset.prod ((oddDiagonals n \ T) \ ∅) (fun d => (MvPolynomial.X d : MvPolynomial (ℕ × ℕ) R))) *
      Finset.prod (T.filter (fun d => shiftSign d ≠ 0)) (fun d => shiftSeriesP R d) = pkSp_F R n T
    rw [sdiff_empty]; rfl
  show PowerSeries.coeff m (Finset.sum ((triangulations n).filter (fun T => Disjoint T (∅ : Finset (ℕ × ℕ))))
    (fun T => pkR_b_F R n ∅ T)) = AP R n m
  rw [e1, sum_congr rfl (fun T _ => e2 T)]
  rfl

/-- The ¬K summand is the image of the full summand under `ψ` (banned variables set to 1). -/
theorem pkR_b_F_psi {R : Type*} [CommRing R] (n : ℕ) (K T : Finset (ℕ × ℕ)) (P : ℕ × ℕ → Prop)
    [DecidablePred P] (hPK : ∀ d ∈ oddDiagonals n, P d ↔ d ∈ K)
    (hT : ∀ d ∈ T, shiftSign d ≠ 0 → ¬ P d) :
    PowerSeries.map (pkR_b_psi R P).toRingHom (pkSp_F R n T) = pkR_b_F R n K T := by
  rw [pkSp_F, map_mul, PowerSeries.map_C, map_prod (PowerSeries.map _)]
  have hs : ∀ d ∈ T.filter (fun d => shiftSign d ≠ 0),
      PowerSeries.map (pkR_b_psi R P).toRingHom (shiftSeriesP R d) = shiftSeriesP R d := by
    intro d hd
    have hd' := mem_filter.1 hd
    refine pkSp_map_sP _ d ?_
    show pkR_b_psi R P (MvPolynomial.X d) = MvPolynomial.X d
    rw [pkR_b_psi_X, ite_eq_right_iff]
    intro h; exact absurd h (hT d hd'.1 hd'.2)
  rw [prod_congr rfl hs]
  have hc : (pkR_b_psi R P).toRingHom (Finset.prod (oddDiagonals n \ T) (fun d => MvPolynomial.X d)) =
      Finset.prod ((oddDiagonals n \ T) \ K) (fun d => (MvPolynomial.X d : MvPolynomial (ℕ × ℕ) R)) := by
    rw [map_prod]
    have e : ∀ d ∈ oddDiagonals n \ T, (pkR_b_psi R P).toRingHom (MvPolynomial.X d) =
        if d ∈ K then 1 else MvPolynomial.X d := by
      intro d hd
      show pkR_b_psi R P (MvPolynomial.X d) = _
      rw [pkR_b_psi_X]
      have := hPK d (mem_sdiff.1 hd).1
      by_cases h : d ∈ K
      · rw [if_pos (this.2 h), if_pos h]
      · rw [if_neg (fun h' => h (this.1 h')), if_neg h]
    rw [prod_congr rfl e, prod_ite, prod_const_one, one_mul]
    refine prod_congr ?_ (fun _ _ => rfl)
    ext d; simp only [mem_filter, mem_sdiff]
  rw [hc]
  rfl


end PiZ
