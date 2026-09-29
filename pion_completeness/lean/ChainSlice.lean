import TreeRectangleZero

/-!
# R12-P4a: T1 on the chain-cosmology slice (T1_E, R2-Z59) — definitions and statements (Phase 4, step 4a)

Thread `surfaceology/threads/R12-P4a.md`. Reference proof: `../r2z59/PROOFS.md` (cited "PROOFS §k" /
"PROOFS Lemma k"), reviewed and confirmed in R2-Z59 R1 (`../../threads/R2-Z59.md` §7).

Phase 1 is imported unchanged: `TreeRectangleZero.lean` here is a byte-identical copy of
`../r12p1b/TreeRectangleZero.lean` (md5 c256cb0eed7bfd945e5175400e59d599), compiled to `build/` (thread §6 E1).
Reused unchanged: `diagonals`, `Crosses`, `triangulations`, `amp`, `vtx`, `planar`, `mesh`, `OnRect`,
`amp_eq_zero_of_onRect` (the tree rectangle zero, PROVED in Phase 1), `amp_eq_F`, `F_rec`, `F_of_le`, `vtx_*`.

Conventions: C0 = arXiv:2312.16282 §2, exactly as Phase 1. The polygon has `m` vertices `1..m` (PROOFS writes
`m = n + 1`, `n` = number of chain sites of arXiv:2503.23579). A tile `c_{ij}` (mesh variable) is labelled by the
same pairs as the diagonals: `(i, j)` with `1 ≤ i`, `i + 2 ≤ j ≤ m`, `(i, j) ≠ (1, m)`; its value is Phase 1's
`mesh m X i j`.

Status markers in docstrings:
* PROVED — no `sorry` in its closure (checked by `#print axioms` at the end of the file);
* ASSEMBLED — proved from statements above it, some still `sorry`;
* `sorry` — statement only, a Phase 4b target.
Every statement carries `[PROOFS …]`, the claim it formalises.
-/

namespace R12P4A

open Finset R12P1

/-! ## 1. Definitions (paper-facing) -/

/-- Normalised label of the tile `c_{ij}` for arbitrary (cyclic) indices: reduce both mod `m` into `1..m`,
then sort. For `i, j` at cyclic distance ≥ 2 this is an element of `diagonals m`. -/
def tlab (m i j : ℕ) : ℕ × ℕ := (min (vtx m i) (vtx m j), max (vtx m i) (vtx m j))

/-- The set `E` of arXiv:2503.23579 eq. (70), with `n = m - 1` chain sites:
`{c_ij : 2 ≤ i < j ≤ n, j − i ≥ 3} ∪ {c_1j : 4 ≤ j ≤ n − 1}` [PROOFS §0]. Equivalent to (70); its bound
`i ≤ n − 3` is implied by `j ≤ n`, `j − i ≥ 3` (checked against the paper's (70) by review R1, m = 5…40). -/
def E (m : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 2 (m - 1) ×ˢ Icc 2 (m - 1)).filter (fun p => p.1 + 3 ≤ p.2)) ∪
    (Icc 4 (m - 2)).image (fun j => (1, j))

/-- The long tiles (cyclic distance ≥ 3) that avoid vertex `m` [PROOFS Lemma 0]. -/
def longAvoid (m : ℕ) : Finset (ℕ × ℕ) :=
  (diagonals m).filter (fun p => 3 ≤ p.2 - p.1 ∧ 3 ≤ m - (p.2 - p.1) ∧ p.2 ≠ m)

/-- The free tiles: every tile not in `E` [PROOFS Lemma 0, "Free := tiles ∖ E"]. -/
def Free (m : ℕ) : Finset (ℕ × ℕ) := diagonals m \ E m

/-- Site labels of PROOFS §0 (chain side of arXiv:2503.23579): `T_j = c_{j−1,j+1}` (`2 ≤ j ≤ m − 2`),
`Q = c_{1,m−1}`, `W_i = c_{i,m}` (`2 ≤ i ≤ m − 2`). Only meaningful in those ranges; note `Tt (m-1) = Wt m (m-2)`
as pairs (the label collision T_n = W_{n−1}), which is why every use below carries the range. -/
def Tt (j : ℕ) : ℕ × ℕ := (j - 1, j + 1)
def Qt (m : ℕ) : ℕ × ℕ := (1, m - 1)
def Wt (m i : ℕ) : ℕ × ℕ := (i, m)

/-- The locus `L_S = {c_S = 0}`: every tile of `S` vanishes at `X`. -/
def OnLocus {K : Type*} [Field K] (m : ℕ) (S : Finset (ℕ × ℕ)) (X : ℕ × ℕ → K) : Prop :=
  ∀ t ∈ S, mesh m X t.1 t.2 = 0

/-- The diamond (causal diamond / rectangle) anchored at the chord `(a, b)`:
`D(a,b) = {c_ij : a ≤ i ≤ b − 2, b ≤ j ≤ a + m − 2}`, indices mod `m` [PROOFS preamble; C0 "Row hidden zero",
arXiv:2312.16282 §3.2]. As a rectangle it is Phase 1's `R_{k,a}` with `k = b − a − 1`. -/
def diamond (m a b : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc a (b - 2)) ×ˢ (Icc b (a + m - 2))).image (fun p => tlab m p.1 p.2)

/-- `S` contains the tile set of some diamond. -/
def ContainsDiamond (m : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  ∃ d ∈ diagonals m, diamond m d.1 d.2 ⊆ S

instance (m : ℕ) (S : Finset (ℕ × ℕ)) : Decidable (ContainsDiamond m S) := by
  unfold ContainsDiamond; infer_instance

/-- "`A_m ≡ 0` on `L_S`", pointwise form over ℚ: `A_m` vanishes at every rational point of `L_S` at which no
chord is `0` (the poles are excluded because Lean's `0⁻¹ = 0` would otherwise give junk values; Phase 1 lesson).
On a degenerate locus (a chord vanishes identically) this is vacuously true — see `negctl_no_E`. -/
def ZeroOn (m : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  ∀ X : ℕ × ℕ → ℚ, OnLocus m S X → (∀ d ∈ diagonals m, X d ≠ 0) → amp m X = 0

/-- `S` is non-degenerate: no chord vanishes identically on `L_S` (over ℚ) [PROOFS §0]. -/
def Nondeg (m : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  ∀ d ∈ diagonals m, ∃ X : ℕ × ℕ → ℚ, OnLocus m S X ∧ X d ≠ 0

/-- The linear closure `cl(S)`: all tiles vanishing identically on `L_S` (over ℚ) [PROOFS §0]. -/
noncomputable def closure (m : ℕ) (S : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) := by
  classical
  exact (diagonals m).filter (fun t => ∀ X : ℕ × ℕ → ℚ, OnLocus m S X → mesh m X t.1 t.2 = 0)

/-! ## 2. Shape of `E` and of the free tiles -/

/-- Helper: arithmetic form of membership in `E`. -/
theorem pkA_mem_E {m : ℕ} {p : ℕ × ℕ} :
    p ∈ E m ↔ (2 ≤ p.1 ∧ p.2 ≤ m - 1 ∧ p.1 + 3 ≤ p.2) ∨ (p.1 = 1 ∧ 4 ≤ p.2 ∧ p.2 ≤ m - 2) := by
  obtain ⟨x, y⟩ := p
  simp only [E, mem_union, mem_filter, mem_product, mem_Icc, mem_image, Prod.mk.injEq]
  constructor
  · rintro (⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩ | ⟨j, ⟨h1, h2⟩, rfl, rfl⟩) <;> omega
  · rintro (⟨h1, h2, h3⟩ | ⟨rfl, h2, h3⟩)
    · left; omega
    · right; exact ⟨y, ⟨h2, h3⟩, rfl, rfl⟩

/-- Helper: arithmetic form of membership in `Free` (short tiles, `Q`, row `m`). -/
theorem pkA_mem_Free {m : ℕ} (hm : 5 ≤ m) {p : ℕ × ℕ} :
    p ∈ Free m ↔ (1 ≤ p.1 ∧ p.2 = p.1 + 2 ∧ p.2 ≤ m - 1) ∨ p = (1, m - 1) ∨
      (2 ≤ p.1 ∧ p.1 ≤ m - 2 ∧ p.2 = m) := by
  obtain ⟨x, y⟩ := p
  rw [Free, mem_sdiff, pkA_mem_E, mem_diagonals, Prod.mk.injEq]
  dsimp only
  constructor <;> intro h <;> omega

theorem pkA_mem_imgT {m : ℕ} {p : ℕ × ℕ} :
    p ∈ (Icc 2 (m - 2)).image Tt ↔ 1 ≤ p.1 ∧ p.2 = p.1 + 2 ∧ p.2 ≤ m - 1 := by
  obtain ⟨x, y⟩ := p
  simp only [mem_image, mem_Icc, Tt, Prod.mk.injEq]
  constructor
  · rintro ⟨j, ⟨h1, h2⟩, rfl, rfl⟩; omega
  · rintro ⟨h1, rfl, h3⟩; exact ⟨x + 1, ⟨by omega, by omega⟩, by omega, by omega⟩

theorem pkA_mem_imgW {m : ℕ} {s : Finset ℕ} {p : ℕ × ℕ} :
    p ∈ s.image (Wt m) ↔ p.1 ∈ s ∧ p.2 = m := by
  obtain ⟨x, y⟩ := p
  simp only [mem_image, Wt, Prod.mk.injEq]
  constructor
  · rintro ⟨i, hi, rfl, rfl⟩; exact ⟨hi, rfl⟩
  · rintro ⟨hx, rfl⟩; exact ⟨x, hx, rfl, rfl⟩

theorem pkA_Tt_inj : Function.Injective Tt := fun a b h => by
  simp only [Tt, Prod.mk.injEq] at h; omega

theorem pkA_Wt_inj (m : ℕ) : Function.Injective (Wt m) := fun a b h => by
  simp only [Wt, Prod.mk.injEq] at h; exact h.1

/-- PROVED · PROOFS Lemma 0 (first half): `E` = the long tiles avoiding vertex `m`. -/
theorem E_eq_longAvoid {m : ℕ} (hm : 5 ≤ m) : E m = longAvoid m := by
  ext ⟨x, y⟩
  rw [pkA_mem_E, longAvoid, mem_filter, mem_diagonals]
  dsimp only
  constructor <;> intro h <;> omega

/-- PROVED · PROOFS Lemma 0 (second half): the free tiles are `T_2 … T_{n−1}`, `Q`, `W_2 … W_{n−1}`
(`n − 1 = m − 2`). -/
theorem Free_eq {m : ℕ} (hm : 5 ≤ m) :
    Free m = (Icc 2 (m - 2)).image Tt ∪ {Qt m} ∪ (Icc 2 (m - 2)).image (Wt m) := by
  ext ⟨x, y⟩
  rw [pkA_mem_Free hm, mem_union, mem_union, mem_singleton, pkA_mem_imgT, pkA_mem_imgW, mem_Icc, Qt]
  simp only [Prod.mk.injEq]
  constructor <;> intro h <;> omega

/-- PROVED · PROOFS Lemma 0 (count): `|Free| = 2m − 5`. -/
theorem card_Free {m : ℕ} (hm : 5 ≤ m) : (Free m).card = 2 * m - 5 := by
  rw [Free_eq hm, card_union_of_disjoint, card_union_of_disjoint, card_singleton,
    card_image_of_injective _ pkA_Tt_inj, card_image_of_injective _ (pkA_Wt_inj m), Nat.card_Icc]
  · omega
  · rw [disjoint_left]
    rintro ⟨x, y⟩ h1 h2
    rw [pkA_mem_imgT] at h1
    rw [mem_singleton, Qt, Prod.mk.injEq] at h2
    dsimp only at h1
    omega
  · rw [disjoint_left]
    rintro ⟨x, y⟩ h1 h2
    rw [mem_union, pkA_mem_imgT, mem_singleton, Qt, Prod.mk.injEq] at h1
    rw [pkA_mem_imgW, mem_Icc] at h2
    dsimp only at h1 h2
    omega

/-- PROVED · every tile of `E` is a tile (a label in `diagonals m`). -/
theorem E_subset_diagonals {m : ℕ} (hm : 5 ≤ m) : E m ⊆ diagonals m := by
  intro p hp
  simp only [E, mem_union, mem_filter, mem_product, mem_Icc, mem_image] at hp
  rw [mem_diagonals]
  rcases hp with ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩ | ⟨j, ⟨h1, h2⟩, rfl⟩ <;> (try dsimp only) <;> omega

/-! ## 3. Tiles are well defined on labels; diamonds are Phase 1 rectangles -/

lemma vtx_vtx {m : ℕ} (hm : 1 ≤ m) (i : ℕ) : vtx m (vtx m i) = vtx m i :=
  vtx_of_mem (vtx_bounds m i hm).1 (vtx_bounds m i hm).2

lemma vtx_vtx_succ {m : ℕ} (hm : 1 ≤ m) (i : ℕ) : vtx m (vtx m i + 1) = vtx m (i + 1) := by
  rw [vtx_succ hm, vtx_succ hm, vtx_vtx hm]

lemma planar_congr {K : Type*} [Field K] {m : ℕ} (X : ℕ × ℕ → K) {i j i' j' : ℕ}
    (hi : vtx m i = vtx m i') (hj : vtx m j = vtx m j') : planar m X i j = planar m X i' j' := by
  unfold planar; rw [hi, hj]

lemma planar_comm {K : Type*} [Field K] (m : ℕ) (X : ℕ × ℕ → K) (i j : ℕ) :
    planar m X i j = planar m X j i := by
  unfold planar; rw [min_comm, max_comm]

/-- PROVED · the tile value depends only on its normalised label (indices mod `m`, unordered). -/
theorem mesh_tlab {K : Type*} [Field K] {m : ℕ} (hm : 1 ≤ m) (X : ℕ × ℕ → K) (i j : ℕ) :
    mesh m X (tlab m i j).1 (tlab m i j).2 = mesh m X i j := by
  unfold tlab mesh
  dsimp only
  rcases le_total (vtx m i) (vtx m j) with h | h
  · rw [min_eq_left h, max_eq_right h]
    rw [planar_congr X (vtx_vtx hm i) (vtx_vtx hm j),
      planar_congr X (vtx_vtx_succ hm i) (vtx_vtx_succ hm j),
      planar_congr X (vtx_vtx hm i) (vtx_vtx_succ hm j),
      planar_congr X (vtx_vtx_succ hm i) (vtx_vtx hm j)]
  · rw [min_eq_right h, max_eq_left h]
    rw [planar_congr X (vtx_vtx hm j) (vtx_vtx hm i),
      planar_congr X (vtx_vtx_succ hm j) (vtx_vtx_succ hm i),
      planar_congr X (vtx_vtx hm j) (vtx_vtx_succ hm i),
      planar_congr X (vtx_vtx_succ hm j) (vtx_vtx hm i)]
    rw [planar_comm m X j i, planar_comm m X (j + 1) (i + 1), planar_comm m X j (i + 1),
      planar_comm m X (j + 1) i]
    ring

theorem pkA_tlab_lo {m i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ m) : tlab m i j = (i, j) := by
  unfold tlab
  rw [vtx_of_mem hi (by omega), vtx_of_mem (by omega) hj, min_eq_left hij, max_eq_right hij]

theorem pkA_tlab_hi {m i k : ℕ} (hk : 1 ≤ k) (hki : k ≤ i) (hi : i ≤ m) :
    tlab m i (k + m) = (k, i) := by
  unfold tlab
  rw [vtx_add_n, vtx_of_mem (by omega) hi, vtx_of_mem hk (by omega), min_eq_right hki, max_eq_left hki]

/-- Helper: arithmetic form of membership in the diamond `D(a, b)`: the part with `j ≤ m` and the wrapped part. -/
theorem pkA_mem_diamond {m a b : ℕ} (ha : 1 ≤ a) (hab : a + 2 ≤ b) (hb : b ≤ m) {p : ℕ × ℕ} :
    p ∈ diamond m a b ↔ (a ≤ p.1 ∧ p.1 + 2 ≤ b ∧ b ≤ p.2 ∧ p.2 ≤ m ∧ p.2 + 2 ≤ a + m) ∨
      (1 ≤ p.1 ∧ p.1 + 2 ≤ a ∧ a ≤ p.2 ∧ p.2 + 2 ≤ b) := by
  obtain ⟨x, y⟩ := p
  simp only [diamond, mem_image, mem_product, mem_Icc, Prod.exists]
  constructor
  · rintro ⟨i, j, ⟨⟨h1, h2⟩, h3, h4⟩, he⟩
    rcases le_or_gt j m with hj | hj
    · rw [pkA_tlab_lo (by omega) (by omega) hj, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      left; omega
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + m := ⟨j - m, by omega⟩
      rw [pkA_tlab_hi (by omega) (by omega) (by omega), Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      right; omega
  · rintro (⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4⟩)
    · exact ⟨x, y, ⟨⟨h1, by omega⟩, h3, by omega⟩, pkA_tlab_lo (by omega) (by omega) h4⟩
    · exact ⟨y, x + m, ⟨⟨h3, by omega⟩, by omega, by omega⟩, pkA_tlab_hi h1 (by omega) (by omega)⟩

/-- PROVED · every tile of a diamond is a tile (cyclic distance ≥ 2), so `diamond ⊆ diagonals`. -/
theorem diamond_subset_diagonals {m : ℕ} {d : ℕ × ℕ} (hd : d ∈ diagonals m) :
    diamond m d.1 d.2 ⊆ diagonals m := by
  obtain ⟨a, b⟩ := d
  rw [mem_diagonals] at hd
  dsimp only at hd
  intro p hp
  dsimp only at hp
  rw [pkA_mem_diamond (by omega) (by omega) (by omega)] at hp
  rw [mem_diagonals]
  omega

/-- PROVED · a diamond inside `S` puts every point of `L_S` on Phase 1's rectangle `R_{b−a−1, a}`. -/
theorem onRect_of_diamond {K : Type*} [Field K] {m : ℕ} {S : Finset (ℕ × ℕ)} {d : ℕ × ℕ}
    (hd : d ∈ diagonals m) (hD : diamond m d.1 d.2 ⊆ S) {X : ℕ × ℕ → K} (hX : OnLocus m S X) :
    OnRect m (d.2 - d.1 - 1) d.1 X := by
  have hd' := mem_diagonals.1 hd
  intro i hi j hj
  simp only [mem_Ico, mem_Icc] at hi hj
  have hmem : tlab m i j ∈ diamond m d.1 d.2 :=
    mem_image.2 ⟨(i, j), mem_product.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, mem_Icc.2 ⟨by omega, by omega⟩⟩, rfl⟩
  rw [← mesh_tlab (by omega) X i j]
  exact hX _ (hD hmem)

/-! ## 4. The "if" direction (imported: Phase 1's rectangle zero) -/

/-- PROVED · **"if" direction of T1_E**, over any field, for any tile set `S` (no `E` needed):
if `S` contains a diamond, `A_m` vanishes at every point of `L_S` with no chord `0`
[PROOFS Cor. 2 "if"; arXiv:2312.16282 §3.2, §6.1 (6.13)–(6.14); here Phase 1's `amp_eq_zero_of_onRect`]. -/
theorem amp_zero_of_diamond {K : Type*} [Field K] {m : ℕ} {S : Finset (ℕ × ℕ)} (hS : ContainsDiamond m S)
    {X : ℕ × ℕ → K} (hL : OnLocus m S X) (hX : ∀ d ∈ diagonals m, X d ≠ 0) : amp m X = 0 := by
  obtain ⟨d, hd, hD⟩ := hS
  have hd' := mem_diagonals.1 hd
  have hR := onRect_of_diamond hd hD hL
  exact amp_eq_zero_of_onRect (k := d.2 - d.1 - 1) (m := d.1) (by omega) (by omega) (by omega) (by omega)
    X hX hR

/-! ## 5. Positivity -/

/-- PROVED · **positivity lemma** [PROOFS Thm 1, first sentence of the proof]: over an ordered field, if every
chord is positive then `A_m > 0` (a non-empty sum of products of positive terms), for `m ≥ 3`. -/
theorem amp_pos {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {m : ℕ} (hm : 3 ≤ m)
    {X : ℕ × ℕ → K} (hX : ∀ d ∈ diagonals m, 0 < X d) : 0 < amp m X := by
  rw [amp_eq_F m hm X]
  -- positivity of every sub-polygon recursion `F a b`, `1 ≤ a < b ≤ m`
  have key : ∀ s a b, b - a = s → 1 ≤ a → a < b → b ≤ m → 0 < F X a b := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
      intro a b hs ha hab hb
      by_cases h : a + 1 < b
      · rw [F_rec X h]
        apply Finset.sum_pos
        · intro k hk
          rw [mem_Ico] at hk
          have hw : ∀ u v, a ≤ u → u < v → v ≤ b → v - u < s → 0 < W X u v := by
            intro u v hu huv hv hlt
            unfold W w
            have hF : 0 < F X u v := ih (v - u) hlt u v rfl (by omega) huv (by omega)
            split_ifs with h2
            · exact mul_pos (inv_pos.2 (hX _ (mem_diagonals.2 ⟨by omega, by omega, by omega, by omega⟩))) hF
            · simpa using hF
          exact mul_pos (hw a k le_rfl (by omega) (by omega) (by omega))
            (hw k b (by omega) (by omega) le_rfl (by omega))
        · exact ⟨a + 1, mem_Ico.2 ⟨le_rfl, h⟩⟩
      · rw [F_of_le X h]; exact one_pos
  exact key (m - 1) 1 m rfl le_rfl (by omega) le_rfl

/-! ## 6. Coordinates on `L_E` (PROOFS §1) -/

/-- Interval sum `s[a,c] = Σ_{i=a}^{c−1} y_i − Σ_{j=a+1}^{c−1} T_j` [PROOFS Lemma 1]. -/
def sInt (y T : ℕ → ℚ) (a c : ℕ) : ℚ := ∑ i ∈ Ico a c, y i - ∑ j ∈ Ioo a c, T j

/-- The point with free coordinates `(y, T)`: chord `(a, b)` ↦ `s[a, b−1]` [PROOFS Lemma 1′]. -/
def coordPt (y T : ℕ → ℚ) : ℕ × ℕ → ℚ := fun d => sInt y T d.1 (d.2 - 1)

/-- `sorry` · PROOFS Lemma 1 (interval formula) on `L_E`: every point of `L_E` is `coordPt` of its own
coordinates `y_i = X_{i,i+2}`, `T_j = c_{j−1,j+1}`, i.e. every chord is an interval of chain sites. -/
theorem eq_coordPt_of_onE {m : ℕ} (hm : 5 ≤ m) {X : ℕ × ℕ → ℚ} (hX : OnLocus m (E m) X) :
    ∀ d ∈ diagonals m, X d = coordPt (fun i => X (i, i + 2)) (fun j => mesh m X (j - 1) (j + 1)) d := by
  sorry

/-- pkgB helper: an interval sum as a difference of prefix sums (`a < c`). -/
lemma pkB_sInt_pre (y T : ℕ → ℚ) {a c : ℕ} (h : a < c) :
    sInt y T a c = (∑ i ∈ range c, y i - ∑ i ∈ range a, y i) -
      (∑ i ∈ range c, T i - ∑ i ∈ range (a + 1), T i) := by
  have hI : Ioo a c = Ico (a + 1) c := by ext x; simp only [mem_Ioo, mem_Ico]; omega
  unfold sInt
  rw [Finset.sum_Ico_eq_sub _ h.le, hI, Finset.sum_Ico_eq_sub _ (show a + 1 ≤ c by omega)]

/-- pkgB helper: `sInt` on an empty interval. -/
lemma pkB_sInt_self (y T : ℕ → ℚ) (a : ℕ) : sInt y T a a = 0 := by
  simp [sInt]

/-- pkgB helper: the planar variable of `coordPt` at a non-wrapping pair `a < b` other than `(1, m)`. -/
lemma pkB_planar {m : ℕ} (y T : ℕ → ℚ) {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ m)
    (h1m : ¬ (a = 1 ∧ b = m)) : planar m (coordPt y T) a b = sInt y T a (b - 1) := by
  rw [planar_of_mem _ ha hab.le hb]
  by_cases h2 : a + 2 ≤ b
  · rw [if_pos (mem_diagonals.2 ⟨ha, hb, h2, h1m⟩)]; rfl
  · rw [if_neg (by rw [mem_diagonals]; dsimp only; omega), show b - 1 = a by omega, pkB_sInt_self]

/-- PROVED · PROOFS Lemma 1′: every `(y, T)` gives a point of `L_E`. -/
theorem coordPt_onE {m : ℕ} (hm : 5 ≤ m) (y T : ℕ → ℚ) : OnLocus m (E m) (coordPt y T) := by
  intro t ht
  have hd := mem_diagonals.1 (E_subset_diagonals hm ht)
  have hE : (2 ≤ t.1 ∧ t.1 + 3 ≤ t.2 ∧ t.2 ≤ m - 1) ∨ (t.1 = 1 ∧ 4 ≤ t.2 ∧ t.2 ≤ m - 2) := by
    simp only [E, mem_union, mem_filter, mem_product, mem_Icc, mem_image] at ht
    rcases ht with ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩ | ⟨j, ⟨h1, h2⟩, rfl⟩
    · left; omega
    · right; dsimp only; omega
  obtain ⟨i, j⟩ := t
  dsimp only at hd hE ⊢
  unfold mesh
  rw [pkB_planar y T (by omega) (by omega) (by omega) (by omega),
    pkB_planar y T (by omega) (by omega) (by omega) (by omega),
    pkB_planar y T (by omega) (by omega) (by omega) (by omega),
    pkB_planar y T (by omega) (by omega) (by omega) (by omega),
    pkB_sInt_pre y T (show i < j - 1 by omega), pkB_sInt_pre y T (show i + 1 < j + 1 - 1 by omega),
    pkB_sInt_pre y T (show i < j + 1 - 1 by omega), pkB_sInt_pre y T (show i + 1 < j - 1 by omega),
    show j + 1 - 1 = j by omega]
  ring

/-- PROVED · PROOFS Lemma 1′: at `coordPt y T` the triangle tile `T_j` has value `T j`. -/
theorem coordPt_T {m : ℕ} (hm : 5 ≤ m) (y T : ℕ → ℚ) {j : ℕ} (hj : 2 ≤ j) (hjm : j ≤ m - 2) :
    mesh m (coordPt y T) (j - 1) (j + 1) = T j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  unfold mesh
  rw [show k + 1 - 1 = k by omega, show k + 1 + 1 + 1 = k + 3 by omega,
    pkB_planar y T (by omega) (by omega) (by omega) (by omega),
    pkB_planar y T (by omega) (by omega) (by omega) (by omega),
    pkB_planar y T (by omega) (by omega) (by omega) (by omega),
    pkB_planar y T (by omega) (by omega) (by omega) (by omega),
    show k + 1 + 1 - 1 = k + 1 by omega, show k + 3 - 1 = k + 2 by omega,
    pkB_sInt_self, pkB_sInt_pre y T (show k < k + 1 by omega),
    pkB_sInt_pre y T (show k + 1 < k + 2 by omega), pkB_sInt_pre y T (show k < k + 2 by omega)]
  simp only [Finset.sum_range_succ]
  ring

/-- PROVED · PROOFS Lemma 1′: `W_i = y_{i−1} + y_i − T_{i−1} − T_{i+1}` with the convention `T_1 = T_n = 0`
(`n = m − 1`), imposed here as hypotheses. -/
theorem coordPt_W {m : ℕ} (hm : 5 ≤ m) (y T : ℕ → ℚ) (hT1 : T 1 = 0) (hTn : T (m - 1) = 0) {i : ℕ}
    (hi : 2 ≤ i) (him : i ≤ m - 2) :
    mesh m (coordPt y T) i m = y (i - 1) + y i - T (i - 1) - T (i + 1) := by
  unfold mesh
  have hw1 : planar m (coordPt y T) (i + 1) (m + 1) = planar m (coordPt y T) 1 (i + 1) := by
    rw [planar_comm]
    exact planar_congr _ (by rw [add_comm, vtx_add_n]) rfl
  have hw2 : planar m (coordPt y T) i (m + 1) = planar m (coordPt y T) 1 i := by
    rw [planar_comm]
    exact planar_congr _ (by rw [add_comm, vtx_add_n]) rfl
  rw [hw1, hw2, pkB_planar y T (by omega) (by omega) (by omega) (by omega),
    pkB_planar y T (by omega) (by omega) (by omega) (by omega),
    pkB_planar y T (by omega) (by omega) (by omega) (by omega),
    pkB_planar y T (by omega) (by omega) (by omega) (by omega), show i + 1 - 1 = i by omega]
  -- left end: `s[1,i] − s[1,i−1] = y_{i−1} − T_{i−1}` (`T_1 = 0` when `i = 2`)
  have hL : sInt y T 1 i - sInt y T 1 (i - 1) = y (i - 1) - T (i - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    rw [show k + 1 - 1 = k by omega]
    rcases Nat.lt_or_ge 1 k with hk | hk
    · rw [pkB_sInt_pre y T (show 1 < k + 1 by omega), pkB_sInt_pre y T hk]
      simp only [Finset.sum_range_succ]; ring
    · obtain rfl : k = 1 := by omega
      rw [pkB_sInt_pre y T (show 1 < 1 + 1 by omega), pkB_sInt_self, hT1]
      simp only [Finset.sum_range_succ]; ring
  -- right end: `s[i,n] − s[i+1,n] = y_i − T_{i+1}` (`T_n = 0` when `i = m − 2`)
  have hR : sInt y T i (m - 1) - sInt y T (i + 1) (m - 1) = y i - T (i + 1) := by
    rcases Nat.lt_or_ge (i + 1) (m - 1) with hk | hk
    · rw [pkB_sInt_pre y T (show i < m - 1 by omega), pkB_sInt_pre y T hk]
      simp only [Finset.sum_range_succ]; ring
    · have e : m - 1 = i + 1 := by omega
      rw [e] at hTn ⊢
      rw [pkB_sInt_pre y T (show i < i + 1 by omega), pkB_sInt_self, hTn]
      simp only [Finset.sum_range_succ]; ring
  linear_combination hL + hR

/-- PROVED · PROOFS Lemma 1′: `Q = s[1, n]`. -/
theorem coordPt_Q {m : ℕ} (hm : 5 ≤ m) (y T : ℕ → ℚ) :
    mesh m (coordPt y T) 1 (m - 1) = sInt y T 1 (m - 1) := by
  unfold mesh
  rw [show m - 1 + 1 = m by omega, planar_one_n _ (by omega),
    pkB_planar y T (by omega) (by omega) (by omega) (by omega),
    pkB_planar y T (by omega) (by omega) (by omega) (by omega),
    pkB_planar y T (by omega) (by omega) (by omega) (by omega),
    pkB_sInt_pre y T (show 1 < m - 1 - 1 by omega), pkB_sInt_pre y T (show 1 + 1 < m - 1 by omega),
    pkB_sInt_pre y T (show 1 + 1 < m - 1 - 1 by omega), pkB_sInt_pre y T (show 1 < m - 1 by omega)]
  ring

/-! ## 7. Diamonds on the slice (PROOFS §2) -/

/-- The free part `Z(a′, b′)` of the diamond `D(a′+1, b′+1)`, `a′ ≥ 1` [PROOFS Lemma 2]. -/
def Zset (m a' b' : ℕ) : Finset (ℕ × ℕ) :=
  (if 2 ≤ a' then {Tt a'} else ∅) ∪ (Ioo a' b').image (Wt m) ∪ (if b' ≤ m - 2 then {Tt b'} else ∅)

/-- PROVED · PROOFS Lemma 2, first kind: `D(1, b) ∩ Free = {T_{b−1}, Q}` (`3 ≤ b ≤ m − 1`). -/
theorem diamond_inter_Free_one {m b : ℕ} (hm : 5 ≤ m) (hb : 3 ≤ b) (hbm : b ≤ m - 1) :
    diamond m 1 b ∩ Free m = {Tt (b - 1), Qt m} := by
  ext ⟨x, y⟩
  rw [mem_inter, pkA_mem_diamond le_rfl (by omega) (by omega), pkA_mem_Free hm, mem_insert, mem_singleton,
    Tt, Qt]
  simp only [Prod.mk.injEq]
  constructor <;> intro h <;> omega

/-- PROVED · PROOFS Lemma 2, second kind: for `a ≥ 2`, `D(a, b) ∩ Free = Z(a − 1, b − 1)`. -/
theorem diamond_inter_Free {m a b : ℕ} (hm : 5 ≤ m) (hab : (a, b) ∈ diagonals m) (ha : 2 ≤ a) :
    diamond m a b ∩ Free m = Zset m (a - 1) (b - 1) := by
  have hd := mem_diagonals.1 hab
  dsimp only at hd
  ext ⟨x, y⟩
  rw [mem_inter, pkA_mem_diamond (by omega) (by omega) (by omega), pkA_mem_Free hm]
  simp only [Zset, mem_union]
  split_ifs with h1 h2 h2 <;>
    simp only [mem_singleton, notMem_empty, pkA_mem_imgW, mem_Ioo, Tt, Prod.mk.injEq, or_false,
      false_or] <;>
    constructor <;> intro h <;> omega

/-- Walls: the chain ends `1`, `n = m − 1`, and the sites `j` with `T_j ∈ F` [PROOFS §2 before Lemma W]. -/
def IsWall (m : ℕ) (F : Finset (ℕ × ℕ)) (j : ℕ) : Prop :=
  j = 1 ∨ j = m - 1 ∨ (2 ≤ j ∧ j ≤ m - 2 ∧ Tt j ∈ F)

/-- PROVED · PROOFS (★): for `Q ∉ F`, `E ∪ F` contains a diamond iff two walls `a < b`, `b − a ≥ 2`, enclose a
run of `W`'s, `W_i ∈ F` for every `a < i < b`. -/
theorem containsDiamond_iff_walls {m : ℕ} (hm : 5 ≤ m) {F : Finset (ℕ × ℕ)} (hF : F ⊆ Free m)
    (hQ : Qt m ∉ F) :
    ContainsDiamond m (E m ∪ F) ↔
      ∃ a b, IsWall m F a ∧ IsWall m F b ∧ a + 2 ≤ b ∧ ∀ i ∈ Ioo a b, Wt m i ∈ F := by
  constructor
  · rintro ⟨⟨a, b⟩, hd, hD⟩
    have hd' := mem_diagonals.1 hd
    dsimp only at hd' hD
    -- every free tile of the diamond lies in `F`
    have hfreeF : ∀ t ∈ diamond m a b ∩ Free m, t ∈ F := by
      intro t ht
      rw [mem_inter] at ht
      rcases mem_union.1 (hD ht.1) with h | h
      · exact absurd h (mem_sdiff.1 ht.2).2
      · exact h
    by_cases ha : a = 1
    · -- first kind: `Q` would be a free tile of the diamond, but `Q ∉ F`
      exfalso
      subst ha
      have hQD : Qt m ∈ diamond m 1 b ∩ Free m := by
        rw [diamond_inter_Free_one hm (by omega) (by omega)]
        exact mem_insert_of_mem (mem_singleton_self _)
      exact hQ (hfreeF _ hQD)
    · -- second kind: read the walls `a − 1`, `b − 1` and the `W`-run off `Z(a − 1, b − 1)`
      have hZF : ∀ t ∈ Zset m (a - 1) (b - 1), t ∈ F := by
        intro t ht
        rw [← diamond_inter_Free hm hd (by omega)] at ht
        exact hfreeF t ht
      refine ⟨a - 1, b - 1, ?_, ?_, by omega, ?_⟩
      · by_cases h1 : a - 1 = 1
        · exact Or.inl h1
        · refine Or.inr (Or.inr ⟨by omega, by omega, hZF _ ?_⟩)
          refine mem_union.2 (Or.inl (mem_union.2 (Or.inl ?_)))
          rw [if_pos (by omega)]
          exact mem_singleton_self _
      · by_cases h1 : b = m
        · exact Or.inr (Or.inl (by omega))
        · refine Or.inr (Or.inr ⟨by omega, by omega, hZF _ ?_⟩)
          refine mem_union.2 (Or.inr ?_)
          rw [if_pos (by omega)]
          exact mem_singleton_self _
      · intro i hi
        exact hZF _ (mem_union.2 (Or.inl (mem_union.2 (Or.inr (mem_image_of_mem _ hi)))))
  · rintro ⟨a, b, ha, hb, hab, hW⟩
    have hwb : ∀ j, IsWall m F j → 1 ≤ j ∧ j ≤ m - 1 := by
      intro j hj
      rcases hj with h | h | ⟨h1, h2, -⟩ <;> omega
    have hab' := hwb a ha
    have hbb' := hwb b hb
    have hd : (a + 1, b + 1) ∈ diagonals m := mem_diagonals.2 (by dsimp only; omega)
    refine ⟨(a + 1, b + 1), hd, ?_⟩
    intro t ht
    have htd := diamond_subset_diagonals hd ht
    by_cases hE : t ∈ E m
    · exact mem_union_left _ hE
    apply mem_union_right
    have htF : t ∈ diamond m (a + 1) (b + 1) ∩ Free m := mem_inter.2 ⟨ht, mem_sdiff.2 ⟨htd, hE⟩⟩
    rw [diamond_inter_Free hm hd (by omega), Nat.add_sub_cancel, Nat.add_sub_cancel] at htF
    rcases mem_union.1 htF with h | h
    · rcases mem_union.1 h with h | h
      · -- `T_a`, present only when `a ≥ 2`: then `a` is a wall of the third kind
        split_ifs at h with h2
        · rw [mem_singleton] at h
          subst h
          rcases ha with h | h | ⟨-, -, hT⟩
          · omega
          · omega
          · exact hT
        · exact absurd h (Finset.notMem_empty _)
      · obtain ⟨i, hi, rfl⟩ := mem_image.1 h
        exact hW i hi
    · -- `T_b`, present only when `b ≤ m − 2`: then `b` is a wall of the third kind
      split_ifs at h with h2
      · rw [mem_singleton] at h
        subst h
        rcases hb with h | h | ⟨-, -, hT⟩
        · omega
        · omega
        · exact hT
      · exact absurd h (Finset.notMem_empty _)

/-! ## 8. Theorem 1: the positive integer point (PROOFS §3) -/

/-- pkgD helper · chain-site shift `x_v` (sites `1..n`): `x_1 = x_n = −1`, `x_k = 2`, else `0`. -/
def pkD_x (n k v : ℕ) : ℤ :=
  (if v = 1 then -1 else 0) + (if v = n then -1 else 0) + (if v = k then 2 else 0)

/-- pkgD helper · energies `Y_0 = Y_n = 0`, `Y_1 = Y_{n−1} = 1`, else `2`. -/
def pkD_Y (n e : ℕ) : ℤ :=
  if e = 0 then 0 else if e = n then 0 else if e = 1 then 1 else if e + 1 = n then 1 else 2

/-- pkgD helper · `y_i = x_i + x_{i+1} + Y_{i−1} + Y_{i+1}`. -/
def pkD_y (n k i : ℕ) : ℚ :=
  (pkD_x n k i : ℚ) + pkD_x n k (i + 1) + pkD_Y n (i - 1) + pkD_Y n (i + 1)

/-- pkgD helper · `T_j = x_j + Y_{j−1} + Y_j`. -/
def pkD_T (n k j : ℕ) : ℚ :=
  (pkD_x n k j : ℚ) + pkD_Y n (j - 1) + pkD_Y n j

/-- pkgD helper · telescoping: `s[a,c] = Σ_{v ∈ [a,c]} x_v + Y_{a−1} + Y_c`. -/
theorem pkD_tele (x Y y T : ℕ → ℚ) (hy : ∀ i, y i = x i + x (i + 1) + Y (i - 1) + Y (i + 1))
    (hT : ∀ j, T j = x j + Y (j - 1) + Y j) {a c : ℕ} (hac : a + 1 ≤ c) :
    sInt y T a c = ∑ v ∈ Icc a c, x v + Y (a - 1) + Y c := by
  induction c, hac using Nat.le_induction with
  | base =>
    unfold sInt
    have h1 : Ico a (a + 1) = {a} := by ext v; simp <;> omega
    have h2 : Ioo a (a + 1) = ∅ := by ext v; simp <;> omega
    have h3 : Icc a (a + 1) = {a, a + 1} := by ext v; simp <;> omega
    rw [h1, h2, h3, sum_singleton, sum_empty, sum_pair (by omega), hy]; ring
  | succ c hc ih =>
    unfold sInt at ih ⊢
    rw [sum_Ico_succ_top (by omega : a ≤ c)]
    have h2 : Ioo a (c + 1) = insert c (Ioo a c) := by ext v; simp <;> omega
    have h3 : Icc a (c + 1) = insert (c + 1) (Icc a c) := by ext v; simp <;> omega
    rw [h2, h3, sum_insert (by simp), sum_insert (by simp), hy c, hT c]
    linarith

/-- pkgD helper · closed form of `Σ_{v ∈ s} x_v`. -/
theorem pkD_sum_x (n k : ℕ) (s : Finset ℕ) :
    ∑ v ∈ s, pkD_x n k v =
      (if 1 ∈ s then -1 else 0) + (if n ∈ s then -1 else 0) + (if k ∈ s then 2 else 0) := by
  simp [pkD_x, sum_add_distrib, sum_ite_eq']

/-- pkgD helper · `x_i = 0` away from `1`, `n`, `k`. -/
theorem pkD_x_zero {n k i : ℕ} (h1 : i ≠ 1) (hn : i ≠ n) (hk : i ≠ k) : pkD_x n k i = 0 := by
  simp [pkD_x, h1, hn, hk]

/-- pkgD helper · `T_1 = 0`. -/
theorem pkD_T1 {n k : ℕ} (hn : 4 ≤ n) (hk2 : 2 ≤ k) (hkn : k + 1 ≤ n) :
    pkD_x n k 1 + pkD_Y n (1 - 1) + pkD_Y n 1 = 0 := by
  have h1 : (1 : ℕ) ≠ n := by omega
  have h2 : (1 : ℕ) ≠ k := by omega
  have h3 : (1 : ℕ) + 1 ≠ n := by omega
  simp [pkD_x, pkD_Y, h1, h2, h3]

/-- pkgD helper · `T_n = 0`. -/
theorem pkD_Tn {n k : ℕ} (hn : 4 ≤ n) (hk2 : 2 ≤ k) (hkn : k + 1 ≤ n) :
    pkD_x n k n + pkD_Y n (n - 1) + pkD_Y n n = 0 := by
  have h1 : n ≠ 1 := by omega
  have h2 : n ≠ k := by omega
  have h3 : n ≠ 0 := by omega
  have h4 : n - 1 ≠ 0 := by omega
  have h5 : n - 1 ≠ n := by omega
  have h6 : n - 1 ≠ 1 := by omega
  have h7 : n - 1 + 1 = n := by omega
  simp [pkD_x, pkD_Y, h1, h2, h3, h4, h5, h6, h7]

/-- pkgD helper · `Q = Σ_{v=1}^n x_v + Y_0 + Y_n = 0`. -/
theorem pkD_Q0 {n k : ℕ} (hn : 4 ≤ n) (hk2 : 2 ≤ k) (hkn : k + 1 ≤ n) :
    ∑ v ∈ Icc 1 n, pkD_x n k v + pkD_Y n (1 - 1) + pkD_Y n n = 0 := by
  rw [pkD_sum_x]
  have h1 : 1 ∈ Icc 1 n := mem_Icc.2 ⟨le_rfl, by omega⟩
  have h2 : n ∈ Icc 1 n := mem_Icc.2 ⟨by omega, le_rfl⟩
  have h3 : k ∈ Icc 1 n := mem_Icc.2 ⟨by omega, by omega⟩
  have h4 : n ≠ 0 := by omega
  simp [pkD_Y, h1, h2, h3, h4]

/-- pkgD helper · every chord `(a, c+1)` has value `≥ 1` at the Case B point. -/
theorem pkD_key {n k a c : ℕ} (hn : 4 ≤ n) (hk2 : 2 ≤ k) (hkn : k + 1 ≤ n) (ha : 1 ≤ a)
    (hac : a + 1 ≤ c) (hc : c ≤ n) (hnot : ¬(a = 1 ∧ c = n)) :
    1 ≤ ∑ v ∈ Icc a c, pkD_x n k v + pkD_Y n (a - 1) + pkD_Y n c := by
  rw [pkD_sum_x]
  simp only [pkD_Y, mem_Icc]
  split_ifs <;> omega

/-- pkgD helper · the chord value at the Case B point, as an integer. -/
theorem pkD_val {m k a c : ℕ} (hac : a + 1 ≤ c) :
    sInt (pkD_y (m - 1) k) (pkD_T (m - 1) k) a c =
      ((∑ v ∈ Icc a c, pkD_x (m - 1) k v + pkD_Y (m - 1) (a - 1) + pkD_Y (m - 1) c : ℤ) : ℚ) := by
  rw [pkD_tele (fun v => (pkD_x (m - 1) k v : ℚ)) (fun e => (pkD_Y (m - 1) e : ℚ))
    (pkD_y (m - 1) k) (pkD_T (m - 1) k) (fun i => rfl) (fun j => rfl) hac]
  push_cast; ring

/-- PROVED · PROOFS Thm 1, Case B (`Q ∈ F`): explicit energies give an integer point of `L_{E∪F}` with every
chord ≥ 1. -/
theorem exists_pos_point_Q {m : ℕ} (hm : 5 ≤ m) {F : Finset (ℕ × ℕ)} (hF : F ⊆ Free m) (hQ : Qt m ∈ F)
    (hfree : ¬ ContainsDiamond m (E m ∪ F)) :
    ∃ X : ℕ × ℕ → ℚ, OnLocus m (E m ∪ F) X ∧ ∀ d ∈ diagonals m, 1 ≤ X d ∧ ∃ z : ℤ, X d = z := by
  classical
  -- (i) no `T_j` lies in `F`: else `D(1, j+1) ⊆ E ∪ F`
  have hTF : ∀ j, 2 ≤ j → j ≤ m - 2 → Tt j ∉ F := by
    intro j hj hjm hTj
    have hd : ((1, j + 1) : ℕ × ℕ) ∈ diagonals m := mem_diagonals.2 (by dsimp only; omega)
    apply hfree
    refine ⟨(1, j + 1), hd, ?_⟩
    intro t ht
    have htd := diamond_subset_diagonals hd ht
    by_cases htE : t ∈ E m
    · exact mem_union_left _ htE
    · apply mem_union_right
      have htF : t ∈ diamond m 1 (j + 1) ∩ Free m := mem_inter.2 ⟨ht, mem_sdiff.2 ⟨htd, htE⟩⟩
      rw [diamond_inter_Free_one hm (by omega) (by omega)] at htF
      simp only [mem_insert, mem_singleton] at htF
      rcases htF with rfl | rfl
      · have e : j + 1 - 1 = j := by omega
        rw [e]; exact hTj
      · exact hQ
  -- (ii) some `W_k` is not in `F`: else `D(2, m) ⊆ E ∪ F`
  obtain ⟨k, hk2, hkm, hkF⟩ : ∃ k, 2 ≤ k ∧ k ≤ m - 2 ∧ Wt m k ∉ F := by
    by_contra hcon
    push_neg at hcon
    have hd : ((2, m) : ℕ × ℕ) ∈ diagonals m := mem_diagonals.2 (by dsimp only; omega)
    apply hfree
    refine ⟨(2, m), hd, ?_⟩
    intro t ht
    have htd := diamond_subset_diagonals hd ht
    by_cases htE : t ∈ E m
    · exact mem_union_left _ htE
    · apply mem_union_right
      have htF : t ∈ diamond m 2 m ∩ Free m := mem_inter.2 ⟨ht, mem_sdiff.2 ⟨htd, htE⟩⟩
      rw [diamond_inter_Free hm hd le_rfl, Zset, if_neg (by omega), if_neg (by omega)] at htF
      simp only [empty_union, union_empty, mem_image, mem_Ioo] at htF
      obtain ⟨i, ⟨hi1, hi2⟩, rfl⟩ := htF
      exact hcon i (by omega) (by omega)
  -- the point `coordPt y T` with the Case B energies
  refine ⟨coordPt (pkD_y (m - 1) k) (pkD_T (m - 1) k), ?_, ?_⟩
  · have hT1 : pkD_T (m - 1) k 1 = 0 := by
      have h := pkD_T1 (n := m - 1) (k := k) (by omega) hk2 (by omega)
      simp only [pkD_T]; exact_mod_cast h
    have hTn : pkD_T (m - 1) k (m - 1) = 0 := by
      have h := pkD_Tn (n := m - 1) (k := k) (by omega) hk2 (by omega)
      simp only [pkD_T]; exact_mod_cast h
    intro t ht
    rcases mem_union.1 ht with htE | htF
    · exact coordPt_onE hm _ _ t htE
    · have htFree := hF htF
      rw [Free_eq hm] at htFree
      simp only [mem_union, mem_image, mem_singleton, mem_Icc] at htFree
      rcases htFree with (⟨j, ⟨hj1, hj2⟩, rfl⟩ | rfl) | ⟨i, ⟨hi1, hi2⟩, rfl⟩
      · exact absurd htF (hTF j hj1 hj2)
      · show mesh m _ 1 (m - 1) = 0
        rw [coordPt_Q hm, pkD_val (by omega), pkD_Q0 (by omega) hk2 (by omega), Int.cast_zero]
      · show mesh m _ i m = 0
        have hik : i ≠ k := by rintro rfl; exact hkF htF
        rw [coordPt_W hm _ _ hT1 hTn hi1 hi2]
        have hx : pkD_x (m - 1) k i = 0 := pkD_x_zero (by omega) (by omega) hik
        have e1 : i - 1 + 1 = i := by omega
        have e2 : i + 1 - 1 = i := by omega
        simp only [pkD_y, pkD_T, e1, e2, hx, Int.cast_zero]
        ring
  · intro d hd
    have hd' := mem_diagonals.1 hd
    have hv : coordPt (pkD_y (m - 1) k) (pkD_T (m - 1) k) d =
        ((∑ v ∈ Icc d.1 (d.2 - 1), pkD_x (m - 1) k v + pkD_Y (m - 1) (d.1 - 1)
          + pkD_Y (m - 1) (d.2 - 1) : ℤ) : ℚ) :=
      pkD_val (m := m) (k := k) (a := d.1) (c := d.2 - 1) (by omega)
    refine ⟨?_, _, hv⟩
    rw [hv]
    have key := pkD_key (n := m - 1) (k := k) (a := d.1) (c := d.2 - 1) (by omega) hk2 (by omega)
      (by omega) (by omega) (by omega) (by omega)
    exact_mod_cast key

/-- pkgE helper: `ε_j = 2` at walls (`IsWall`, spelled out decidably), `0` else. -/
def pkE_eps (m : ℕ) (F : Finset (ℕ × ℕ)) (j : ℕ) : ℕ :=
  if j = 1 ∨ j = m - 1 ∨ (2 ≤ j ∧ j ≤ m - 2 ∧ Tt j ∈ F) then 2 else 0

/-- pkgE helper: `α` by the one-step recursion `α_1 = 1`, `α_{j+1} = if j ∈ I then α_j + ε_{j−1} else 1`. -/
def pkE_al (m : ℕ) (F : Finset (ℕ × ℕ)) : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | j + 2 => if 2 ≤ j + 1 ∧ j + 1 ≤ m - 2 ∧ Wt m (j + 1) ∈ F then pkE_al m F (j + 1) + pkE_eps m F j else 1

/-- pkgE helper: `β` read from the right end, `pkE_bb k = β_{n−k}` (`n = m − 1`):
`β_n = 1`, `β_{j−1} = if j ∈ I then β_j + ε_{j+1} else 1`. -/
def pkE_bb (m : ℕ) (F : Finset (ℕ × ℕ)) : ℕ → ℕ
  | 0 => 1
  | k + 1 => if 2 ≤ m - 1 - k ∧ m - 1 - k ≤ m - 2 ∧ Wt m (m - 1 - k) ∈ F then
      pkE_bb m F k + pkE_eps m F (m - 1 - k + 1) else 1

/-- pkgE helper: `β_j`. -/
def pkE_be (m : ℕ) (F : Finset (ℕ × ℕ)) (j : ℕ) : ℕ := pkE_bb m F (m - 1 - j)

lemma pkE_eps_cases (m : ℕ) (F : Finset (ℕ × ℕ)) (j : ℕ) : pkE_eps m F j = 0 ∨ pkE_eps m F j = 2 := by
  unfold pkE_eps; split_ifs <;> simp

lemma pkE_eps_wall {m : ℕ} {F : Finset (ℕ × ℕ)} {j : ℕ} (h : pkE_eps m F j ≠ 0) : IsWall m F j := by
  unfold pkE_eps at h
  unfold IsWall
  split_ifs at h with hw
  · exact hw
  · exact absurd rfl h

lemma pkE_eps_of_wall {m : ℕ} {F : Finset (ℕ × ℕ)} {j : ℕ} (h : IsWall m F j) : pkE_eps m F j = 2 := by
  unfold IsWall at h
  unfold pkE_eps
  split_ifs
  rfl

lemma pkE_al_pos (m : ℕ) (F : Finset (ℕ × ℕ)) : ∀ j, 1 ≤ pkE_al m F j
  | 0 => by simp [pkE_al]
  | 1 => by simp [pkE_al]
  | j + 2 => by
    rw [pkE_al.eq_3]
    split_ifs
    · have := pkE_al_pos m F (j + 1); omega
    · exact le_rfl

lemma pkE_bb_pos (m : ℕ) (F : Finset (ℕ × ℕ)) : ∀ k, 1 ≤ pkE_bb m F k
  | 0 => by simp [pkE_bb]
  | k + 1 => by
    rw [pkE_bb.eq_2]
    split_ifs
    · have := pkE_bb_pos m F k; omega
    · exact le_rfl

/-- pkgE helper: if `α_j ≠ 1` then a wall `w ≤ j − 2` has `W_i ∈ F` for all `w < i < j`. -/
lemma pkE_al_inv {m : ℕ} {F : Finset (ℕ × ℕ)} : ∀ j, pkE_al m F j = 1 ∨
    ∃ w, IsWall m F w ∧ w + 2 ≤ j ∧ ∀ i ∈ Ioo w j, Wt m i ∈ F
  | 0 => Or.inl (by simp [pkE_al])
  | 1 => Or.inl (by simp [pkE_al])
  | j + 2 => by
    rw [pkE_al.eq_3]
    split_ifs with h
    · rcases pkE_eps_cases m F j with he | he
      · rw [he, add_zero]
        rcases pkE_al_inv (j + 1) with h1 | ⟨w, hw, hwj, hI⟩
        · exact Or.inl h1
        · refine Or.inr ⟨w, hw, by omega, fun i hi => ?_⟩
          rw [mem_Ioo] at hi
          by_cases hij : i = j + 1
          · rw [hij]; exact h.2.2
          · exact hI i (mem_Ioo.2 ⟨hi.1, by omega⟩)
      · refine Or.inr ⟨j, pkE_eps_wall (by omega), le_rfl, fun i hi => ?_⟩
        rw [mem_Ioo] at hi
        have hi' : i = j + 1 := by omega
        rw [hi']; exact h.2.2
    · exact Or.inl rfl

/-- pkgE helper: mirror of `pkE_al_inv` for `β` (site `j = n − k`). -/
lemma pkE_bb_inv {m : ℕ} {F : Finset (ℕ × ℕ)} : ∀ k, pkE_bb m F k = 1 ∨
    ∃ w, IsWall m F w ∧ m - 1 - k + 2 ≤ w ∧ ∀ i ∈ Ioo (m - 1 - k) w, Wt m i ∈ F
  | 0 => Or.inl (by simp [pkE_bb])
  | k + 1 => by
    rw [pkE_bb.eq_2]
    split_ifs with h
    · rcases pkE_eps_cases m F (m - 1 - k + 1) with he | he
      · rw [he, add_zero]
        rcases pkE_bb_inv k with h1 | ⟨w, hw, hwj, hI⟩
        · exact Or.inl h1
        · refine Or.inr ⟨w, hw, by omega, fun i hi => ?_⟩
          rw [mem_Ioo] at hi
          by_cases hij : i = m - 1 - k
          · rw [hij]; exact h.2.2
          · exact hI i (mem_Ioo.2 ⟨by omega, hi.2⟩)
      · refine Or.inr ⟨m - 1 - k + 1, pkE_eps_wall (by omega), by omega, fun i hi => ?_⟩
        rw [mem_Ioo] at hi
        have hi' : i = m - 1 - k := by omega
        rw [hi']; exact h.2.2
    · exact Or.inl rfl

lemma pkE_wall_le {m : ℕ} {F : Finset (ℕ × ℕ)} (hm : 5 ≤ m) {w : ℕ} (hw : IsWall m F w) :
    1 ≤ w ∧ w ≤ m - 1 := by
  rcases hw with h | h | ⟨h1, h2, -⟩ <;> omega

/-- pkgE helper (outline step 2): at a wall, `α_w = 1` (diamond-freeness via `containsDiamond_iff_walls`). -/
lemma pkE_al_wall {m : ℕ} (hm : 5 ≤ m) {F : Finset (ℕ × ℕ)} (hF : F ⊆ Free m) (hQ : Qt m ∉ F)
    (hfree : ¬ ContainsDiamond m (E m ∪ F)) {w : ℕ} (hw : IsWall m F w) : pkE_al m F w = 1 := by
  rcases pkE_al_inv (m := m) (F := F) w with h | ⟨w', hw', hle, hI⟩
  · exact h
  · exact absurd ((containsDiamond_iff_walls hm hF hQ).2 ⟨w', w, hw', hw, hle, hI⟩) hfree

/-- pkgE helper (outline step 2): at a wall, `β_w = 1`. -/
lemma pkE_be_wall {m : ℕ} (hm : 5 ≤ m) {F : Finset (ℕ × ℕ)} (hF : F ⊆ Free m) (hQ : Qt m ∉ F)
    (hfree : ¬ ContainsDiamond m (E m ∪ F)) {w : ℕ} (hw : IsWall m F w) : pkE_be m F w = 1 := by
  have hwm := pkE_wall_le hm hw
  unfold pkE_be
  rcases pkE_bb_inv (m := m) (F := F) (m - 1 - w) with h | ⟨w', hw', hle, hI⟩
  · exact h
  · have e : m - 1 - (m - 1 - w) = w := by omega
    rw [e] at hle hI
    exact absurd ((containsDiamond_iff_walls hm hF hQ).2 ⟨w, w', hw, hw', hle, hI⟩) hfree

/-- pkgE helper (outline step 3): `α_{i+1} = α_i + ε_{i−1}` for `i ∈ I`. -/
lemma pkE_al_step {m : ℕ} {F : Finset (ℕ × ℕ)} {i : ℕ} (hi : 2 ≤ i) (him : i ≤ m - 2) (hW : Wt m i ∈ F) :
    pkE_al m F (i + 1) = pkE_al m F i + pkE_eps m F (i - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  show pkE_al m F (k + 2) = _
  rw [pkE_al.eq_3, Nat.add_sub_cancel]
  split_ifs with hh
  · rfl
  · exact absurd ⟨hi, him, hW⟩ hh

/-- pkgE helper (outline step 3): `β_{i−1} = β_i + ε_{i+1}` for `i ∈ I`. -/
lemma pkE_be_step {m : ℕ} {F : Finset (ℕ × ℕ)} {i : ℕ} (hi : 2 ≤ i) (him : i ≤ m - 2) (hW : Wt m i ∈ F) :
    pkE_be m F (i - 1) = pkE_be m F i + pkE_eps m F (i + 1) := by
  unfold pkE_be
  have e : m - 1 - (i - 1) = (m - 1 - i) + 1 := by omega
  have e2 : m - 1 - (m - 1 - i) = i := by omega
  rw [e, pkE_bb.eq_2, e2]
  split_ifs with hh
  · rfl
  · exact absurd ⟨hi, him, hW⟩ hh

/-- pkgE helper (outline step 1, telescoping, any `α, β, ε`):
`sInt y T a c = α_a + β_c + Σ_{a<j<c} ε_j` for `y_i = α_i + β_{i+1}`, `T_j = α_j + β_j − ε_j`, `c = a + 1 + k`. -/
lemma pkE_tele (al be ep : ℕ → ℚ) (a k : ℕ) :
    sInt (fun i => al i + be (i + 1)) (fun j => al j + be j - ep j) a (a + 1 + k) =
      al a + be (a + 1 + k) + ∑ j ∈ Ioo a (a + 1 + k), ep j := by
  induction k with
  | zero =>
    have h1 : Ico a (a + 1 + 0) = {a} := by ext x; simp; try omega
    have h2 : Ioo a (a + 1 + 0) = ∅ := by ext x; simp; try omega
    unfold sInt
    rw [h1, h2, sum_singleton, sum_empty, sum_empty]
    simp
  | succ k ih =>
    unfold sInt at ih ⊢
    have h1 : Ico a (a + 1 + (k + 1)) = insert (a + 1 + k) (Ico a (a + 1 + k)) := by ext x; simp; omega
    have h2 : Ioo a (a + 1 + (k + 1)) = insert (a + 1 + k) (Ioo a (a + 1 + k)) := by ext x; simp; omega
    have n1 : a + 1 + k ∉ Ico a (a + 1 + k) := by simp
    have n2 : a + 1 + k ∉ Ioo a (a + 1 + k) := by simp
    rw [h1, h2, sum_insert n1, sum_insert n2, sum_insert n2]
    have e : a + 1 + (k + 1) = a + 1 + k + 1 := by omega
    rw [e]
    linarith

/-- PROVED · PROOFS Thm 1, Case A (`Q ∉ F`): the α/β/ε construction per run of `W`'s (window lemma). -/
theorem exists_pos_point_noQ {m : ℕ} (hm : 5 ≤ m) {F : Finset (ℕ × ℕ)} (hF : F ⊆ Free m) (hQ : Qt m ∉ F)
    (hfree : ¬ ContainsDiamond m (E m ∪ F)) :
    ∃ X : ℕ × ℕ → ℚ, OnLocus m (E m ∪ F) X ∧ ∀ d ∈ diagonals m, 1 ≤ X d ∧ ∃ z : ℤ, X d = z := by
  classical
  -- the point: `y_i = α_i + β_{i+1}`, `T_j = α_j + β_j − ε_j`
  have hA := fun {w : ℕ} (hw : IsWall m F w) => pkE_al_wall hm hF hQ hfree hw
  have hB := fun {w : ℕ} (hw : IsWall m F w) => pkE_be_wall hm hF hQ hfree hw
  have w1 : IsWall m F 1 := Or.inl rfl
  have wn : IsWall m F (m - 1) := Or.inr (Or.inl rfl)
  refine ⟨coordPt (fun i => (pkE_al m F i : ℚ) + (pkE_be m F (i + 1) : ℚ))
    (fun j => (pkE_al m F j : ℚ) + (pkE_be m F j : ℚ) - (pkE_eps m F j : ℚ)), ?_, ?_⟩
  · intro t ht
    rcases mem_union.1 ht with htE | htF
    · exact coordPt_onE hm _ _ t htE
    · have htFree := hF htF
      rw [Free_eq hm] at htFree
      rcases mem_union.1 htFree with htTQ | htW
      · rcases mem_union.1 htTQ with htT | htQ
        · obtain ⟨j, hj, rfl⟩ := mem_image.1 htT
          rw [mem_Icc] at hj
          have hw : IsWall m F j := Or.inr (Or.inr ⟨hj.1, hj.2, htF⟩)
          show mesh m _ (j - 1) (j + 1) = 0
          rw [coordPt_T hm _ _ hj.1 hj.2]
          simp only [hA hw, hB hw, pkE_eps_of_wall hw]
          norm_num
        · rw [mem_singleton] at htQ
          exact absurd (htQ ▸ htF) hQ
      · obtain ⟨i, hi, rfl⟩ := mem_image.1 htW
        rw [mem_Icc] at hi
        show mesh m _ i m = 0
        rw [coordPt_W hm _ _ (by simp only [hA w1, hB w1, pkE_eps_of_wall w1]; norm_num)
          (by simp only [hA wn, hB wn, pkE_eps_of_wall wn]; norm_num) hi.1 hi.2]
        have e : i - 1 + 1 = i := by omega
        simp only [e]
        rw [pkE_al_step hi.1 hi.2 htF, pkE_be_step hi.1 hi.2 htF]
        push_cast
        ring
  · intro d hd
    have hd' := mem_diagonals.1 hd
    obtain ⟨k, hk⟩ : ∃ k, d.2 - 1 = d.1 + 1 + k := ⟨d.2 - 1 - (d.1 + 1), by omega⟩
    unfold coordPt
    rw [hk, pkE_tele (fun j => (pkE_al m F j : ℚ)) (fun j => (pkE_be m F j : ℚ))
      (fun j => (pkE_eps m F j : ℚ))]
    have h1 : (1 : ℚ) ≤ (pkE_al m F d.1 : ℚ) := by exact_mod_cast pkE_al_pos m F d.1
    have h2 : (0 : ℚ) ≤ (pkE_be m F (d.1 + 1 + k) : ℚ) := Nat.cast_nonneg _
    have h3 : (0 : ℚ) ≤ ∑ j ∈ Ioo d.1 (d.1 + 1 + k), (pkE_eps m F j : ℚ) :=
      sum_nonneg fun _ _ => Nat.cast_nonneg _
    refine ⟨by linarith, ⟨((pkE_al m F d.1 + pkE_be m F (d.1 + 1 + k) +
      ∑ j ∈ Ioo d.1 (d.1 + 1 + k), pkE_eps m F j : ℕ) : ℤ), ?_⟩⟩
    push_cast
    ring

/-- ASSEMBLED · **the construction (PROOFS Theorem 1)**: for `m ≥ 5` and `F` a set of free tiles with `E ∪ F`
diamond-free, `L_{E∪F}` has an integer point at which every chord is ≥ 1. -/
theorem exists_pos_point {m : ℕ} (hm : 5 ≤ m) {F : Finset (ℕ × ℕ)} (hF : F ⊆ Free m)
    (hfree : ¬ ContainsDiamond m (E m ∪ F)) :
    ∃ X : ℕ × ℕ → ℚ, OnLocus m (E m ∪ F) X ∧ ∀ d ∈ diagonals m, 1 ≤ X d ∧ ∃ z : ℤ, X d = z := by
  by_cases hQ : Qt m ∈ F
  · exact exists_pos_point_Q hm hF hQ hfree
  · exact exists_pos_point_noQ hm hF hQ hfree

/-- `E ∪ F` for `F = S ∩ Free` recovers `S` when `E ⊆ S ⊆ tiles`. -/
lemma E_union_free {m : ℕ} {S : Finset (ℕ × ℕ)} (hE : E m ⊆ S) (hS : S ⊆ diagonals m) :
    E m ∪ (S ∩ Free m) = S := by
  ext t
  simp only [mem_union, mem_inter, Free, mem_sdiff]
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact hE h
    · exact h
  · intro h
    by_cases ht : t ∈ E m
    · exact Or.inl ht
    · exact Or.inr ⟨h, hS h, ht⟩

/-- ASSEMBLED · PROOFS Thm 1 "consequently": for diamond-free `S ⊇ E`, `L_S` has a rational point with every
chord ≥ 1 and `A_m > 0` there. -/
theorem amp_pos_point_of_diamondFree {m : ℕ} (hm : 5 ≤ m) {S : Finset (ℕ × ℕ)} (hE : E m ⊆ S)
    (hS : S ⊆ diagonals m) (hfree : ¬ ContainsDiamond m S) :
    ∃ X : ℕ × ℕ → ℚ, OnLocus m S X ∧ (∀ d ∈ diagonals m, 1 ≤ X d) ∧ 0 < amp m X := by
  have hSF := E_union_free hE hS
  obtain ⟨X, hL, hX⟩ := exists_pos_point hm (F := S ∩ Free m) inter_subset_right (by rwa [hSF])
  rw [hSF] at hL
  exact ⟨X, hL, fun d hd => (hX d hd).1,
    amp_pos (by omega) fun d hd => lt_of_lt_of_le one_pos (hX d hd).1⟩

/-- ASSEMBLED · PROOFS Cor. 2 "non-degeneracy is automatic": a diamond-free `S ⊇ E` is non-degenerate. -/
theorem nondeg_of_diamondFree {m : ℕ} (hm : 5 ≤ m) {S : Finset (ℕ × ℕ)} (hE : E m ⊆ S)
    (hS : S ⊆ diagonals m) (hfree : ¬ ContainsDiamond m S) : Nondeg m S := by
  obtain ⟨X, hL, hX, -⟩ := amp_pos_point_of_diamondFree hm hE hS hfree
  intro d hd
  exact ⟨X, hL, (lt_of_lt_of_le one_pos (hX d hd)).ne'⟩

/-! ## 9. The main theorem T1_E (PROOFS Cor. 2) and its corollaries -/

/-- ASSEMBLED · **T1_E(m), main theorem** [PROOFS Cor. 2; R2-Z59 C6]: for `m ≥ 5` and every tile set `S` with
`E ⊆ S`, `A_m` vanishes at every non-pole rational point of `L_S` iff `S` contains a diamond. -/
theorem t1E {m : ℕ} (hm : 5 ≤ m) {S : Finset (ℕ × ℕ)} (hE : E m ⊆ S) (hS : S ⊆ diagonals m) :
    ZeroOn m S ↔ ContainsDiamond m S := by
  constructor
  · intro hZ
    by_contra hfree
    obtain ⟨X, hL, hX, hpos⟩ := amp_pos_point_of_diamondFree hm hE hS hfree
    have := hZ X hL (fun d hd => (lt_of_lt_of_le one_pos (hX d hd)).ne')
    exact hpos.ne' this
  · intro hD X hL hX
    exact amp_zero_of_diamond hD hL hX

/-- ASSEMBLED · T1_E in the brief's form: `F` any set of free tiles. -/
theorem t1E_free {m : ℕ} (hm : 5 ≤ m) {F : Finset (ℕ × ℕ)} (hF : F ⊆ Free m) :
    ZeroOn m (E m ∪ F) ↔ ContainsDiamond m (E m ∪ F) :=
  t1E hm subset_union_left
    (union_subset (E_subset_diagonals hm) (hF.trans sdiff_subset))

/-- ASSEMBLED · PROOFS Cor. 2 "in particular": every degenerate `S ⊇ E` contains a diamond. -/
theorem diamond_of_degenerate {m : ℕ} (hm : 5 ≤ m) {S : Finset (ℕ × ℕ)} (hE : E m ⊆ S)
    (hS : S ⊆ diagonals m) (hdeg : ¬ Nondeg m S) : ContainsDiamond m S := by
  by_contra h
  exact hdeg (nondeg_of_diamondFree hm hE hS h)

/-- ASSEMBLED · PROOFS Cor. 3 (sets vs loci): for `S ⊇ E`, the closure `cl(S)` contains a diamond iff `S` does. -/
theorem closure_containsDiamond_iff {m : ℕ} (hm : 5 ≤ m) {S : Finset (ℕ × ℕ)} (hE : E m ⊆ S)
    (hS : S ⊆ diagonals m) : ContainsDiamond m (closure m S) ↔ ContainsDiamond m S := by
  have hsub : S ⊆ closure m S := by
    intro t ht
    unfold closure
    simp only [mem_filter]
    exact ⟨hS ht, fun X hX => hX t ht⟩
  constructor
  · intro hD
    by_contra hfree
    obtain ⟨X, hL, hX, hpos⟩ := amp_pos_point_of_diamondFree hm hE hS hfree
    have hLc : OnLocus m (closure m S) X := by
      intro t ht
      unfold closure at ht
      simp only [mem_filter] at ht
      exact ht.2 X hL
    have := amp_zero_of_diamond hD hLc (fun d hd => (lt_of_lt_of_le one_pos (hX d hd)).ne')
    exact hpos.ne' this
  · rintro ⟨d, hd, hD⟩
    exact ⟨d, hd, hD.trans hsub⟩

/-- `sorry` · OPTIONAL (off the main theorem's closure) · PROOFS Prop. 4: among tile sets `E ⊆ S ⊆ tiles`, the
minimal zero sets (non-degenerate, `ZeroOn`, and no proper `E ⊆ S′ ⊂ S` is `ZeroOn`) are exactly the
`E ∪ D(a,b)`. -/
theorem minimal_zero_iff {m : ℕ} (hm : 5 ≤ m) {S : Finset (ℕ × ℕ)} (hE : E m ⊆ S) (hS : S ⊆ diagonals m) :
    (ZeroOn m S ∧ Nondeg m S ∧ ∀ S', E m ⊆ S' → S' ⊂ S → ¬ ZeroOn m S') ↔
      ∃ d ∈ diagonals m, S = E m ∪ diamond m d.1 d.2 := by
  sorry

/-! ## 10. Sanity: small instances proved from the definitions (no `sorry`) -/

section Sanity

/-- PROVED · `E` at `m = 6` is `{c14, c25}` (eq. (70) with `n = 5`), and `E` is empty at `m = 5`. -/
theorem E_six : E 6 = {(1, 4), (2, 5)} := by decide
theorem E_five : E 5 = ∅ := by decide

/-- PROVED · Lemma 0 at `m = 5 … 10`, and `|Free| = 2m − 5` there. -/
theorem E_eq_longAvoid_small : ∀ m ∈ Icc 5 10, E m = longAvoid m := by decide
theorem card_Free_small : ∀ m ∈ Icc 5 10, (Free m).card = 2 * m - 5 := by decide

/-- PROVED · the diamonds are `m(m−3)/2` distinct tile sets at `m = 5, 6, 7`, and each is a set of tiles. -/
theorem card_diamonds_small :
    ∀ m ∈ Icc 5 7, ((diagonals m).image (fun d => diamond m d.1 d.2)).card = m * (m - 3) / 2 := by decide
theorem diamond_subset_diagonals_small :
    ∀ m ∈ Icc 5 8, ∀ d ∈ diagonals m, diamond m d.1 d.2 ⊆ diagonals m := by decide

/-- PROVED · Lemma 2 at `m = 7`: `D(1,4) ∩ Free = {T_3, Q}` and `D(2,6) ∩ Free = Z(1,5) = {W_2, W_3, W_4, T_5}`. -/
theorem diamond_inter_Free_seven :
    diamond 7 1 4 ∩ Free 7 = {Tt 3, Qt 7} ∧ diamond 7 2 6 ∩ Free 7 = Zset 7 1 5 := by decide

/-- A diamond-free free set at `m = 6`: `F6 = {T_2, W_2, T_4, W_4}` (the largest; R2-Z59 C1 count 37/9 at m = 6). -/
def F6 : Finset (ℕ × ℕ) := {(1, 3), (2, 6), (3, 5), (4, 6)}

theorem F6_free : F6 ⊆ Free 6 := by decide
theorem F6_diamondFree : ¬ ContainsDiamond 6 (E 6 ∪ F6) := by decide

/-- The positive integer point on `L_{E∪F6}` (found by `pick_points.py`; `A_6 = 3` there). -/
def X6p : ℕ × ℕ → ℚ := fun d =>
  if d = (1, 3) then 1 else if d = (1, 4) then 3 else if d = (1, 5) then 2 else if d = (2, 4) then 2
  else if d = (2, 5) then 1 else if d = (2, 6) then 2 else if d = (3, 5) then 2 else if d = (3, 6) then 3
  else if d = (4, 6) then 1 else 0

theorem X6p_onLocus : OnLocus 6 (E 6 ∪ F6) X6p := by
  rw [E_six]
  intro t ht
  simp only [F6, mem_union, mem_insert, mem_singleton] at ht
  rcases ht with ((rfl | rfl) | (rfl | rfl | rfl | rfl)) <;>
    simp [mesh, planar, vtx, diagonals, X6p] <;> norm_num

theorem X6p_ge_one : ∀ d ∈ diagonals 6, 1 ≤ X6p d := by decide

/-- PROVED · **non-vacuity of the "only if" side** at `m = 6`: `E ∪ F6` is diamond-free and `A_6` does not vanish
on its locus (so `ZeroOn` is not trivially true), in agreement with `t1E`. -/
theorem sanity_six_pos : ¬ ContainsDiamond 6 (E 6 ∪ F6) ∧ ¬ ZeroOn 6 (E 6 ∪ F6) := by
  refine ⟨F6_diamondFree, fun hZ => ?_⟩
  have hpos := amp_pos (m := 6) (X := X6p) (by norm_num)
    (fun d hd => lt_of_lt_of_le one_pos (X6p_ge_one d hd))
  exact hpos.ne' (hZ X6p X6p_onLocus (fun d hd => (lt_of_lt_of_le one_pos (X6p_ge_one d hd)).ne'))

/-- A diamond set at `m = 6`: `E ∪ {T_2, Q} = E ∪ D(1,3)` (the parametric zero of arXiv:2503.23579 (30)). -/
def S6z : Finset (ℕ × ℕ) := {(1, 4), (2, 5), (1, 3), (1, 5)}

theorem S6z_diamond : ContainsDiamond 6 S6z := by decide

/-- A point of `L_{S6z}` with every chord non-zero (so `ZeroOn 6 S6z` is not vacuous). -/
def X6z : ℕ × ℕ → ℚ := fun d =>
  if d = (1, 3) then -3 else if d = (1, 4) then -6 else if d = (1, 5) then -2 else if d = (2, 4) then -3
  else if d = (2, 5) then 1 else if d = (2, 6) then 3 else if d = (3, 5) then 1 else if d = (3, 6) then 3
  else if d = (4, 6) then 2 else 0

theorem X6z_onLocus : OnLocus 6 S6z X6z := by
  intro t ht
  simp only [S6z, mem_insert, mem_singleton] at ht
  rcases ht with (rfl | rfl | rfl | rfl) <;> simp [mesh, planar, vtx, diagonals, X6z] <;> norm_num

theorem X6z_ne_zero : ∀ d ∈ diagonals 6, X6z d ≠ 0 := by decide

/-- PROVED · **non-vacuity of the "if" side** at `m = 6`: `S6z ⊇ E` contains a diamond, `A_6` vanishes on its
locus, and the locus has a point with no chord `0`. -/
theorem sanity_six_zero :
    E 6 ⊆ S6z ∧ ContainsDiamond 6 S6z ∧ ZeroOn 6 S6z ∧
      (∃ X : ℕ × ℕ → ℚ, OnLocus 6 S6z X ∧ ∀ d ∈ diagonals 6, X d ≠ 0) := by
  refine ⟨by decide, S6z_diamond, fun X hL hX => amp_zero_of_diamond S6z_diamond hL hX,
    ⟨X6z, X6z_onLocus, X6z_ne_zero⟩⟩

/-! ### Negative controls (intentionally false variants, refuted) -/

/-- Off-by-one diamond: `j` running to `a + m − 1` instead of `a + m − 2` (compare Phase 1's `mesh_adjacent`). -/
def diamondBad (m a b : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc a (b - 2)) ×ˢ (Icc b (a + m - 1))).image (fun p => tlab m p.1 p.2)

def ContainsDiamondBad (m : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  ∃ d ∈ diagonals m, diamondBad m d.1 d.2 ⊆ S

instance (m : ℕ) (S : Finset (ℕ × ℕ)) : Decidable (ContainsDiamondBad m S) := by
  unfold ContainsDiamondBad; infer_instance

/-- PROVED · negative control 1: with the off-by-one diamond, T1_E is **false** at `m = 6` (the shifted rectangle
contains the adjacent pair `(a, a−1)`, whose label is an edge, never a tile, so no tile set contains it). Weak by
design (review R1): `ContainsDiamondBad` can never hold, so this only re-tests the "if" instance; see
`rev_negctl_small` for the too-short direction. -/
theorem negctl_offbyone :
    ¬ (∀ S : Finset (ℕ × ℕ), E 6 ⊆ S → S ⊆ diagonals 6 → (ZeroOn 6 S ↔ ContainsDiamondBad 6 S)) := by
  intro h
  have h1 := (h S6z (by decide) (by decide)).1 sanity_six_zero.2.2.1
  revert h1
  decide

/-- Reviewer control (fable-2026-09-24-R12P4arev, copied verbatim from `../r12p4arev/RevControls.lean`, namespace
changed): a diamond one step too SHORT (`j ≤ a + m − 3`). Complements `negctl_offbyone`, whose predicate can never
hold (every too-long diamond contains an edge label), so it tests only the "if" instance. -/
def diamondSmall (m a b : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc a (b - 2)) ×ˢ (Icc b (a + m - 3))).image (fun p => tlab m p.1 p.2)

def ContainsDiamondSmall (m : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  ∃ d ∈ diagonals m, diamondSmall m d.1 d.2 ⊆ S

instance (m : ℕ) (S : Finset (ℕ × ℕ)) : Decidable (ContainsDiamondSmall m S) := by
  unfold ContainsDiamondSmall; infer_instance

/-- `E 6 ∪ {T_2}`. -/
def S6s : Finset (ℕ × ℕ) := {(1, 4), (2, 5), (1, 3)}

theorem X6p_onLocus_S6s : OnLocus 6 S6s X6p := by
  intro t ht
  simp only [S6s, mem_insert, mem_singleton] at ht
  rcases ht with (rfl | rfl | rfl) <;> simp [mesh, planar, vtx, diagonals, X6p] <;> norm_num

/-- PROVED · reviewer negative control: with the too-short diamond the "if" half is **false** at `m = 6`
(`E ∪ {T_2}` contains the short `D(1,3)`, but `A_6 > 0` at `X6p`). -/
theorem rev_negctl_small :
    ¬ (∀ S : Finset (ℕ × ℕ), E 6 ⊆ S → S ⊆ diagonals 6 → (ZeroOn 6 S ↔ ContainsDiamondSmall 6 S)) := by
  intro h
  have hc : ContainsDiamondSmall 6 S6s := by decide
  have hz := (h S6s (by decide) (by decide)).2 hc
  have hpos := amp_pos (m := 6) (X := X6p) (by norm_num)
    (fun d hd => lt_of_lt_of_le one_pos (X6p_ge_one d hd))
  exact hpos.ne' (hz X6p X6p_onLocus_S6s (fun d hd => (lt_of_lt_of_le one_pos (X6p_ge_one d hd)).ne'))

/-- A diamond-free, **degenerate** tile set at `m = 7` not containing `E 7` (found by `degen7.py`, smallest size 8):
every point of its locus has `X_{35} = 0`. -/
def S7d : Finset (ℕ × ℕ) := {(1, 3), (1, 4), (1, 6), (2, 5), (2, 7), (3, 6), (4, 6), (5, 7)}

theorem S7d_forces_X35 {X : ℕ × ℕ → ℚ} (hL : OnLocus 7 S7d X) : X (3, 5) = 0 := by
  have e := fun t (ht : t ∈ S7d) => hL t ht
  have e13 := e (1, 3) (by decide); have e14 := e (1, 4) (by decide); have e16 := e (1, 6) (by decide)
  have e25 := e (2, 5) (by decide); have e27 := e (2, 7) (by decide); have e36 := e (3, 6) (by decide)
  have e46 := e (4, 6) (by decide); have e57 := e (5, 7) (by decide)
  simp [mesh, planar, vtx, diagonals] at e13 e14 e16 e25 e27 e36 e46 e57
  linear_combination e13 + e14 + e16 - e25 - e27 + e36 + e46 - e57

/-- PROVED · negative control 2: **without the hypothesis `E ⊆ S`** the pointwise statement is false at `m = 7`:
`S7d` is diamond-free, yet `ZeroOn 7 S7d` holds vacuously (the locus is degenerate). This is why `t1E` carries
`E ⊆ S`, and why `ZeroOn` must be read together with `Nondeg` off the slice (T1's non-degeneracy clause). -/
theorem negctl_no_E : ¬ E 7 ⊆ S7d ∧ ¬ ContainsDiamond 7 S7d ∧ ZeroOn 7 S7d ∧ ¬ Nondeg 7 S7d := by
  refine ⟨by decide, by decide, fun X hL hX => absurd (S7d_forces_X35 hL) (hX (3, 5) (by decide)), ?_⟩
  intro h
  obtain ⟨X, hL, hX⟩ := h (3, 5) (by decide)
  exact hX (S7d_forces_X35 hL)

end Sanity

end R12P4A

#print axioms R12P4A.mesh_tlab
#print axioms R12P4A.onRect_of_diamond
#print axioms R12P4A.amp_zero_of_diamond
#print axioms R12P4A.amp_pos
#print axioms R12P4A.E_subset_diagonals
#print axioms R12P4A.t1E
#print axioms R12P4A.t1E_free
#print axioms R12P4A.closure_containsDiamond_iff
#print axioms R12P4A.E_eq_longAvoid_small
#print axioms R12P4A.card_Free_small
#print axioms R12P4A.card_diamonds_small
#print axioms R12P4A.diamond_subset_diagonals_small
#print axioms R12P4A.diamond_inter_Free_seven
#print axioms R12P4A.sanity_six_pos
#print axioms R12P4A.sanity_six_zero
#print axioms R12P4A.negctl_offbyone
#print axioms R12P4A.negctl_no_E
#print axioms R12P4A.rev_negctl_small
