import Mathlib

/-!
# R12-P1b: the tree rectangle zero of Tr(φ³), proved for all n

Step 1b of the R12 Lean pilot (thread `surfaceology/threads/R12-P1b.md`). Starting point: the
fidelity-reviewed statement draft `../r12p1/TreeRectangleZero.lean` (R12-P1, reviewed in
`../r12p1rev/REVIEW.md`). The paper-facing definitions (`diagonals`, `Crosses`, `IsTriangulation`,
`triangulations`, `amp`, `vtx`, `planar`, `mesh`, `OnRect`) and the statements of
`amp_eq_zero_of_onRect` and `onRect_inhabited` are copied verbatim (frozen). The only change of
layout: the main statements now come after the lemmas they use.

Conventions: C0 = arXiv:2312.16282 §2. Polygon vertices `1..n`; diagonal `(a,b)` with `a < b`,
`b - a ≥ 2`, `(a,b) ≠ (1,n)`; planar variable `X (a,b)`; polygon edges carry `X = 0`
([arXiv:2312.16282 eq. (2.2) and the sentence after it]). Mesh variable
`c i j = X i j + X (i+1) (j+1) - X i (j+1) - X (i+1) j` with vertex labels mod `n`
([arXiv:2312.16282 eq. (2.4)]). Rectangle `R_{k,m}` of [arXiv:2503.03805 eq. (1)]:
`i ∈ {m, …, m+k-1}`, `j ∈ {k+m+1, …, m-2+n}`.

Proof route A′ (R12-P1 §4): Zhou's factorisation of propagators [arXiv:2411.07944 §2.6, eqs. (55),
(74)–(77)] reorganised as an induction on the apex (Berends–Giele) recursion `F`:
1. triangulation combinatorics: every triangulation of a sub-polygon has a unique apex on its base,
   hence `amp = F 1 n` (`F_eq_sum`, `amp_eq_F`);
2. telescoping of mesh variables (`mesh_telescope`, `star`), the factorisation lemma (`F_factor`),
   the `m = 1` family (`amp_eq_zero_m1`);
3. rotation (`amp_rot`, `onRect_rot`); the main theorem by induction on `m`;
4. the general witness (`onRect_inhabited`) and `mesh_adjacent`.
-/

namespace R12P1

open Finset

/-! ## Definitions (paper-facing) -/

/-- Diagonals of the convex `n`-gon with vertices `1..n`. -/
def diagonals (n : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 n ×ˢ Icc 1 n).filter (fun p => p.1 + 2 ≤ p.2 ∧ ¬ (p.1 = 1 ∧ p.2 = n))

/-- Two diagonals `(a,b)`, `(c,d)` (with `a < b`, `c < d`) cross iff their endpoints interleave. -/
def Crosses (p q : ℕ × ℕ) : Prop :=
  (p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2) ∨ (q.1 < p.1 ∧ p.1 < q.2 ∧ q.2 < p.2)

instance : DecidableRel Crosses := fun _ _ => by unfold Crosses; infer_instance

/-- A triangulation is a maximal set of pairwise non-crossing diagonals. -/
def IsTriangulation (n : ℕ) (T : Finset (ℕ × ℕ)) : Prop :=
  T ⊆ diagonals n ∧ (∀ p ∈ T, ∀ q ∈ T, ¬ Crosses p q) ∧
    (∀ d ∈ diagonals n, d ∉ T → ∃ p ∈ T, Crosses p d)

instance (n : ℕ) : DecidablePred (IsTriangulation n) := fun _ => by
  unfold IsTriangulation; infer_instance

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

/-- The `(k,m)`-zero locus ([arXiv:2503.03805 eq. (1)]). -/
def OnRect (n k m : ℕ) (X : ℕ × ℕ → K) : Prop :=
  ∀ i ∈ Ico m (m + k), ∀ j ∈ Icc (k + m + 1) (m + n - 2), mesh n X i j = 0

/-! ## Skeleton definitions (internal; as in the step-1a draft) -/

/-- Side weight: `1` for a polygon side of the sub-polygon, `1/X` for a diagonal. -/
def w (X : ℕ × ℕ → K) (a b : ℕ) : K := if a + 1 < b then (X (a, b))⁻¹ else 1

/-- Apex recursion on the sub-polygon with vertices `a, a+1, …, b` (base `(a,b)` excluded):
`F a b = ∑_{a<k<b} (w a k · F a k) · (w k b · F k b)`, and `F a b = 1` if `b ≤ a + 1`. -/
def F (X : ℕ × ℕ → K) (a b : ℕ) : K :=
  if a + 1 < b then
    ∑ k ∈ (Ioo a b).attach,
      (w X a k.1 * F X a k.1) * (w X k.1 b * F X k.1 b)
  else 1
termination_by b - a
decreasing_by
  all_goals
    have := (mem_Ioo.mp k.2)
    omega

/-- Current `W a b = w a b · F a b` (Berends–Giele current of the block `a..b-1`). -/
def W (X : ℕ × ℕ → K) (a b : ℕ) : K := w X a b * F X a b

/-- Rotation of vertex labels by one step, acting on diagonals. -/
def rot (n : ℕ) (d : ℕ × ℕ) : ℕ × ℕ :=
  (min (vtx n (d.1 + 1)) (vtx n (d.2 + 1)), max (vtx n (d.1 + 1)) (vtx n (d.2 + 1)))

/-! ## Step 1. Triangulation combinatorics and `amp = F 1 n` -/

/-- Diagonals of the sub-polygon with vertices `a, a+1, …, b` (its base `(a,b)` excluded).
`diagonals n = sdiag 1 n` by definition. -/
def sdiag (a b : ℕ) : Finset (ℕ × ℕ) :=
  (Icc a b ×ˢ Icc a b).filter (fun p => p.1 + 2 ≤ p.2 ∧ ¬ (p.1 = a ∧ p.2 = b))

lemma mem_sdiag {a b : ℕ} {d : ℕ × ℕ} :
    d ∈ sdiag a b ↔ a ≤ d.1 ∧ d.2 ≤ b ∧ d.1 + 2 ≤ d.2 ∧ ¬ (d.1 = a ∧ d.2 = b) := by
  unfold sdiag
  simp only [mem_filter, mem_product, mem_Icc]
  omega

lemma diagonals_eq_sdiag (n : ℕ) : diagonals n = sdiag 1 n := rfl

lemma mem_diagonals {n : ℕ} {d : ℕ × ℕ} :
    d ∈ diagonals n ↔ 1 ≤ d.1 ∧ d.2 ≤ n ∧ d.1 + 2 ≤ d.2 ∧ ¬ (d.1 = 1 ∧ d.2 = n) :=
  mem_sdiag

/-- Triangulations of the sub-polygon `a..b`: maximal non-crossing sets of its diagonals. -/
def IsTri (a b : ℕ) (T : Finset (ℕ × ℕ)) : Prop :=
  T ⊆ sdiag a b ∧ (∀ p ∈ T, ∀ q ∈ T, ¬ Crosses p q) ∧
    (∀ d ∈ sdiag a b, d ∉ T → ∃ p ∈ T, Crosses p d)

instance (a b : ℕ) : DecidablePred (IsTri a b) := fun _ => by
  unfold IsTri; infer_instance

def tri (a b : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  (sdiag a b).powerset.filter (IsTri a b)

lemma mem_tri {a b : ℕ} {T : Finset (ℕ × ℕ)} : T ∈ tri a b ↔ IsTri a b T := by
  unfold tri
  simp only [mem_filter, mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

lemma mem_triangulations {n : ℕ} {T : Finset (ℕ × ℕ)} :
    T ∈ triangulations n ↔ IsTriangulation n T := by
  unfold triangulations
  simp only [mem_filter, mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

lemma triangulations_eq_tri (n : ℕ) : triangulations n = tri 1 n := by
  ext T
  rw [mem_triangulations, mem_tri]
  exact Iff.rfl

/-- Gluing two sub-triangulations at the apex `k`: `T₁ ∪ T₂ ∪ {(a,k), (k,b)}` (sides omitted). -/
def glue (a b k : ℕ) (T1 T2 : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  T1 ∪ T2 ∪ ((if a + 1 < k then {(a, k)} else ∅) ∪ (if k + 1 < b then {(k, b)} else ∅))

lemma mem_glue {a b k : ℕ} {T1 T2 : Finset (ℕ × ℕ)} {d : ℕ × ℕ} :
    d ∈ glue a b k T1 T2 ↔
      d ∈ T1 ∨ d ∈ T2 ∨ (a + 1 < k ∧ d = (a, k)) ∨ (k + 1 < b ∧ d = (k, b)) := by
  unfold glue
  by_cases h1 : a + 1 < k <;> by_cases h2 : k + 1 < b <;>
    simp [h1, h2] <;> tauto

/-- Soundness of gluing. -/
lemma glue_isTri {a b k : ℕ} {T1 T2 : Finset (ℕ × ℕ)} (hak : a < k) (hkb : k < b)
    (h1 : IsTri a k T1) (h2 : IsTri k b T2) : IsTri a b (glue a b k T1 T2) := by
  obtain ⟨s1, n1, m1⟩ := h1
  obtain ⟨s2, n2, m2⟩ := h2
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    rw [mem_glue] at hd
    rw [mem_sdiag]
    rcases hd with hd | hd | ⟨h, rfl⟩ | ⟨h, rfl⟩
    · have := mem_sdiag.1 (s1 hd); omega
    · have := mem_sdiag.1 (s2 hd); omega
    · dsimp only; omega
    · dsimp only; omega
  · intro p hp q hq
    rw [mem_glue] at hp hq
    rcases hp with hp | hp | ⟨hp', rfl⟩ | ⟨hp', rfl⟩ <;>
      rcases hq with hq | hq | ⟨hq', rfl⟩ | ⟨hq', rfl⟩
    all_goals try exact n1 _ hp _ hq
    all_goals try exact n2 _ hp _ hq
    all_goals
      try have := mem_sdiag.1 (s1 hp)
      try have := mem_sdiag.1 (s2 hp)
      try have := mem_sdiag.1 (s1 hq)
      try have := mem_sdiag.1 (s2 hq)
      simp only [Crosses]
      omega
  · rintro ⟨c, e⟩ hd hnot
    rw [mem_glue] at hnot
    push Not at hnot
    obtain ⟨hn1, hn2, hn3, hn4⟩ := hnot
    have hb := mem_sdiag.1 hd
    dsimp only at hb
    by_cases hL : e ≤ k
    · by_cases hak' : c = a ∧ e = k
      · exfalso
        obtain ⟨rfl, rfl⟩ := hak'
        exact hn3 (by omega) rfl
      · have hd1 : (c, e) ∈ sdiag a k := mem_sdiag.2 (by dsimp only; omega)
        obtain ⟨p, hp, hc⟩ := m1 _ hd1 hn1
        exact ⟨p, mem_glue.2 (Or.inl hp), hc⟩
    · by_cases hR : k ≤ c
      · by_cases hkb' : c = k ∧ e = b
        · exfalso
          obtain ⟨rfl, rfl⟩ := hkb'
          exact hn4 (by omega) rfl
        · have hd2 : (c, e) ∈ sdiag k b := mem_sdiag.2 (by dsimp only; omega)
          obtain ⟨p, hp, hc⟩ := m2 _ hd2 hn2
          exact ⟨p, mem_glue.2 (Or.inr (Or.inl hp)), hc⟩
      · by_cases hca : c = a
        · refine ⟨(k, b), mem_glue.2 (Or.inr (Or.inr (Or.inr ⟨by omega, rfl⟩))), ?_⟩
          simp only [Crosses]
          omega
        · refine ⟨(a, k), mem_glue.2 (Or.inr (Or.inr (Or.inl ⟨by omega, rfl⟩))), ?_⟩
          simp only [Crosses]
          omega

/-- Existence of an apex: the largest `k` with `(a,k)` a side or in `T` also has `(k,b)` a side
or in `T` (maximality of `T` is used here). -/
lemma exists_apex {a b : ℕ} {T : Finset (ℕ × ℕ)} (hab : a + 1 < b) (hT : IsTri a b T) :
    ∃ k, a < k ∧ k < b ∧ (a + 1 < k → (a, k) ∈ T) ∧ (k + 1 < b → (k, b) ∈ T) := by
  obtain ⟨hs, hn, hm⟩ := hT
  have hmemS : ∀ j, j ∈ (Ioo a b).filter (fun j => j = a + 1 ∨ (a, j) ∈ T) ↔
      (a < j ∧ j < b) ∧ (j = a + 1 ∨ (a, j) ∈ T) := by
    intro j; simp only [mem_filter, mem_Ioo]
  have hne : ((Ioo a b).filter (fun j => j = a + 1 ∨ (a, j) ∈ T)).Nonempty :=
    ⟨a + 1, (hmemS _).2 ⟨⟨by omega, hab⟩, Or.inl rfl⟩⟩
  obtain ⟨k, hkS, hmax⟩ : ∃ k ∈ (Ioo a b).filter (fun j => j = a + 1 ∨ (a, j) ∈ T),
      ∀ j ∈ (Ioo a b).filter (fun j => j = a + 1 ∨ (a, j) ∈ T), j ≤ k :=
    ⟨_, max'_mem _ hne, fun j hj => le_max' _ j hj⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := (hmemS k).1 hkS
  refine ⟨k, h1, h2, fun h => h3.resolve_left (by omega), ?_⟩
  intro hkb
  by_contra hnot
  have hd : (k, b) ∈ sdiag a b := mem_sdiag.2 (by dsimp only; omega)
  obtain ⟨⟨c, e⟩, hp, hc⟩ := hm _ hd hnot
  have hpb := mem_sdiag.1 (hs hp)
  dsimp only at hpb
  simp only [Crosses] at hc
  rcases hc with ⟨hc1, hc2, hc3⟩ | ⟨_, _, hc3⟩
  · by_cases hca : c = a
    · subst hca
      have := hmax e ((hmemS e).2 ⟨⟨by omega, hc3⟩, Or.inr hp⟩)
      omega
    · have hak : (a, k) ∈ T := h3.resolve_left (by omega)
      exact hn _ hak _ hp (by simp only [Crosses]; omega)
  · omega

/-- No diagonal of `T` straddles an apex. -/
lemma no_straddle {a b k : ℕ} {T : Finset (ℕ × ℕ)} (hT : IsTri a b T) (hak : a < k) (hkb : k < b)
    (hA : a + 1 < k → (a, k) ∈ T) (hB : k + 1 < b → (k, b) ∈ T) :
    ∀ p ∈ T, p.2 ≤ k ∨ k ≤ p.1 := by
  obtain ⟨hs, hn, -⟩ := hT
  rintro ⟨c, e⟩ hp
  have hpb := mem_sdiag.1 (hs hp)
  dsimp only at hpb ⊢
  by_contra h
  by_cases hca : c = a
  · exact hn _ hp _ (hB (by omega)) (by simp only [Crosses]; omega)
  · exact hn _ (hA (by omega)) _ hp (by simp only [Crosses]; omega)

lemma left_isTri {a b k : ℕ} {T : Finset (ℕ × ℕ)} (hT : IsTri a b T) (hak : a < k) (hkb : k < b)
    (hA : a + 1 < k → (a, k) ∈ T) (hB : k + 1 < b → (k, b) ∈ T) :
    IsTri a k (T.filter (fun d => d.2 ≤ k ∧ d ≠ (a, k))) := by
  have hns := no_straddle hT hak hkb hA hB
  obtain ⟨hs, hn, hm⟩ := hT
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨c, e⟩ hd
    rw [mem_filter] at hd
    have := mem_sdiag.1 (hs hd.1)
    obtain ⟨-, h1, h2⟩ := hd
    simp only [ne_eq, Prod.mk.injEq] at h2
    rw [mem_sdiag]
    dsimp only at this h1 ⊢
    omega
  · intro p hp q hq
    exact hn p (mem_filter.1 hp).1 q (mem_filter.1 hq).1
  · rintro ⟨c, e⟩ hd hnot
    have hdb := mem_sdiag.1 hd
    dsimp only at hdb
    have hnotT : (c, e) ∉ T := by
      intro h
      apply hnot
      rw [mem_filter]
      refine ⟨h, hdb.2.1, ?_⟩
      simp only [ne_eq, Prod.mk.injEq]
      omega
    obtain ⟨⟨c', e'⟩, hp, hc⟩ := hm _ (mem_sdiag.2 (by dsimp only; omega)) hnotT
    refine ⟨(c', e'), mem_filter.2 ⟨hp, ?_, ?_⟩, hc⟩
    · have := hns _ hp
      dsimp only at this ⊢
      simp only [Crosses] at hc
      omega
    · simp only [ne_eq, Prod.mk.injEq]
      simp only [Crosses] at hc
      omega

lemma right_isTri {a b k : ℕ} {T : Finset (ℕ × ℕ)} (hT : IsTri a b T) (hak : a < k) (hkb : k < b)
    (hA : a + 1 < k → (a, k) ∈ T) (hB : k + 1 < b → (k, b) ∈ T) :
    IsTri k b (T.filter (fun d => k ≤ d.1 ∧ d ≠ (k, b))) := by
  have hns := no_straddle hT hak hkb hA hB
  obtain ⟨hs, hn, hm⟩ := hT
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨c, e⟩ hd
    rw [mem_filter] at hd
    have := mem_sdiag.1 (hs hd.1)
    obtain ⟨-, h1, h2⟩ := hd
    simp only [ne_eq, Prod.mk.injEq] at h2
    rw [mem_sdiag]
    dsimp only at this h1 ⊢
    omega
  · intro p hp q hq
    exact hn p (mem_filter.1 hp).1 q (mem_filter.1 hq).1
  · rintro ⟨c, e⟩ hd hnot
    have hdb := mem_sdiag.1 hd
    dsimp only at hdb
    have hnotT : (c, e) ∉ T := by
      intro h
      apply hnot
      rw [mem_filter]
      refine ⟨h, hdb.1, ?_⟩
      simp only [ne_eq, Prod.mk.injEq]
      omega
    obtain ⟨⟨c', e'⟩, hp, hc⟩ := hm _ (mem_sdiag.2 (by dsimp only; omega)) hnotT
    refine ⟨(c', e'), mem_filter.2 ⟨hp, ?_, ?_⟩, hc⟩
    · have := hns _ hp
      dsimp only at this ⊢
      simp only [Crosses] at hc
      omega
    · simp only [ne_eq, Prod.mk.injEq]
      simp only [Crosses] at hc
      omega

lemma glue_split {a b k : ℕ} {T : Finset (ℕ × ℕ)} (hT : IsTri a b T) (hak : a < k) (hkb : k < b)
    (hA : a + 1 < k → (a, k) ∈ T) (hB : k + 1 < b → (k, b) ∈ T) :
    glue a b k (T.filter (fun d => d.2 ≤ k ∧ d ≠ (a, k)))
      (T.filter (fun d => k ≤ d.1 ∧ d ≠ (k, b))) = T := by
  have hns := no_straddle hT hak hkb hA hB
  ext ⟨c, e⟩
  rw [mem_glue, mem_filter, mem_filter]
  constructor
  · rintro (h | h | ⟨h, heq⟩ | ⟨h, heq⟩)
    · exact h.1
    · exact h.1
    · rw [heq]; exact hA h
    · rw [heq]; exact hB h
  · intro h
    have hb := mem_sdiag.1 (hT.1 h)
    have hs := hns _ h
    dsimp only at hb hs
    simp only [ne_eq, Prod.mk.injEq]
    by_cases h1 : e ≤ k
    · by_cases h2 : c = a ∧ e = k
      · exact Or.inr (Or.inr (Or.inl ⟨by omega, h2⟩))
      · exact Or.inl ⟨h, h1, h2⟩
    · by_cases h2 : c = k ∧ e = b
      · exact Or.inr (Or.inr (Or.inr ⟨by omega, h2⟩))
      · exact Or.inr (Or.inl ⟨h, by omega, h2⟩)

lemma filter_glue_left {a b k : ℕ} {T1 T2 : Finset (ℕ × ℕ)}
    (h1 : T1 ⊆ sdiag a k) (h2 : T2 ⊆ sdiag k b) :
    (glue a b k T1 T2).filter (fun d => d.2 ≤ k ∧ d ≠ (a, k)) = T1 := by
  ext ⟨c, e⟩
  rw [mem_filter, mem_glue]
  constructor
  · rintro ⟨h | h | ⟨h, heq⟩ | ⟨h, heq⟩, hle, hne⟩
    · exact h
    · have := mem_sdiag.1 (h2 h); dsimp only at this hle; omega
    · exact absurd heq hne
    · simp only [Prod.mk.injEq] at heq; dsimp only at hle; omega
  · intro h
    have := mem_sdiag.1 (h1 h)
    dsimp only at this
    refine ⟨Or.inl h, this.2.1, ?_⟩
    simp only [ne_eq, Prod.mk.injEq]
    omega

lemma filter_glue_right {a b k : ℕ} {T1 T2 : Finset (ℕ × ℕ)}
    (h1 : T1 ⊆ sdiag a k) (h2 : T2 ⊆ sdiag k b) :
    (glue a b k T1 T2).filter (fun d => k ≤ d.1 ∧ d ≠ (k, b)) = T2 := by
  ext ⟨c, e⟩
  rw [mem_filter, mem_glue]
  constructor
  · rintro ⟨h | h | ⟨h, heq⟩ | ⟨h, heq⟩, hle, hne⟩
    · have := mem_sdiag.1 (h1 h); dsimp only at this hle; omega
    · exact h
    · simp only [Prod.mk.injEq] at heq; dsimp only at hle; omega
    · exact absurd heq hne
  · intro h
    have := mem_sdiag.1 (h2 h)
    dsimp only at this
    refine ⟨Or.inr (Or.inl h), this.1, ?_⟩
    simp only [ne_eq, Prod.mk.injEq]
    omega

/-- Uniqueness of the apex, and recovery of the two halves. -/
lemma glue_inj {a b k k' : ℕ} {T1 T2 T1' T2' : Finset (ℕ × ℕ)}
    (hak : a < k) (hkb : k < b) (hak' : a < k') (hkb' : k' < b)
    (h1 : IsTri a k T1) (h2 : IsTri k b T2) (h1' : IsTri a k' T1') (h2' : IsTri k' b T2')
    (heq : glue a b k T1 T2 = glue a b k' T1' T2') : k = k' ∧ T1 = T1' ∧ T2 = T2' := by
  have hG := glue_isTri hak hkb h1 h2
  have hkk : k = k' := by
    rcases lt_trichotomy k k' with h | h | h
    · exfalso
      have hp : (a, k') ∈ glue a b k T1 T2 := by
        rw [heq, mem_glue]; exact Or.inr (Or.inr (Or.inl ⟨by omega, rfl⟩))
      have hq : (k, b) ∈ glue a b k T1 T2 := mem_glue.2 (Or.inr (Or.inr (Or.inr ⟨by omega, rfl⟩)))
      exact hG.2.1 _ hp _ hq (by simp only [Crosses]; omega)
    · exact h
    · exfalso
      have hp : (a, k) ∈ glue a b k T1 T2 := mem_glue.2 (Or.inr (Or.inr (Or.inl ⟨by omega, rfl⟩)))
      have hq : (k', b) ∈ glue a b k T1 T2 := by
        rw [heq, mem_glue]; exact Or.inr (Or.inr (Or.inr ⟨by omega, rfl⟩))
      exact hG.2.1 _ hp _ hq (by simp only [Crosses]; omega)
  subst hkk
  refine ⟨rfl, ?_, ?_⟩
  · rw [← filter_glue_left h1.1 h2.1, heq, filter_glue_left h1'.1 h2'.1]
  · rw [← filter_glue_right h1.1 h2.1, heq, filter_glue_right h1'.1 h2'.1]

lemma w_eq_prod (X : ℕ × ℕ → K) (a k : ℕ) :
    ∏ d ∈ (if a + 1 < k then {(a, k)} else ∅ : Finset (ℕ × ℕ)), (X d)⁻¹ = w X a k := by
  unfold w
  split_ifs <;> simp

lemma prod_glue (X : ℕ × ℕ → K) {a b k : ℕ} {T1 T2 : Finset (ℕ × ℕ)} (hak : a < k) (hkb : k < b)
    (h1 : T1 ⊆ sdiag a k) (h2 : T2 ⊆ sdiag k b) :
    ∏ d ∈ glue a b k T1 T2, (X d)⁻¹ =
      (w X a k * ∏ d ∈ T1, (X d)⁻¹) * (w X k b * ∏ d ∈ T2, (X d)⁻¹) := by
  have hA : ∀ d ∈ (if a + 1 < k then {(a, k)} else ∅ : Finset (ℕ × ℕ)), d = (a, k) := by
    intro d hd; split_ifs at hd <;> simp_all
  have hB : ∀ d ∈ (if k + 1 < b then {(k, b)} else ∅ : Finset (ℕ × ℕ)), d = (k, b) := by
    intro d hd; split_ifs at hd <;> simp_all
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
  unfold glue
  rw [prod_union dTAB, prod_union d12, prod_union dAB, w_eq_prod, w_eq_prod]
  ring

lemma tri_of_le {a b : ℕ} (h : ¬ a + 1 < b) : tri a b = {∅} := by
  have hs : sdiag a b = ∅ := by
    ext d; simp only [mem_sdiag, Finset.notMem_empty, iff_false]; omega
  unfold tri
  rw [hs, powerset_empty]
  ext T
  simp only [mem_filter, mem_singleton]
  constructor
  · exact fun h => h.1
  · rintro rfl
    refine ⟨rfl, ⟨by simp, by simp, ?_⟩⟩
    rw [hs]; simp

lemma F_of_le (X : ℕ × ℕ → K) {a b : ℕ} (h : ¬ a + 1 < b) : F X a b = 1 := by
  rw [F, ite_eq_right h]

lemma F_rec (X : ℕ × ℕ → K) {a b : ℕ} (h : a + 1 < b) :
    F X a b = ∑ k ∈ Ico (a + 1) b, W X a k * W X k b := by
  rw [F, ite_eq_left h]
  have hI : Ioo a b = Ico (a + 1) b := by ext; simp only [mem_Ioo, mem_Ico]; omega
  refine (Finset.sum_attach (Ioo a b) (fun k => W X a k * W X k b)).trans ?_
  rw [hI]

/-- **L-bridge, general form.** On every sub-polygon, the apex recursion is the sum over
triangulations of the product of propagators. -/
theorem F_eq_sum (X : ℕ × ℕ → K) (a b : ℕ) : F X a b = ∑ T ∈ tri a b, ∏ d ∈ T, (X d)⁻¹ := by
  obtain ⟨N, hN⟩ : ∃ N, b - a = N := ⟨_, rfl⟩
  induction N using Nat.strong_induction_on generalizing a b with
  | _ N ih =>
  by_cases hab : a + 1 < b
  swap
  · rw [F_of_le X hab, tri_of_le hab, sum_singleton, prod_empty]
  have step : ∀ k ∈ Ico (a + 1) b, W X a k * W X k b =
      ∑ p ∈ tri a k ×ˢ tri k b, ∏ d ∈ glue a b k p.1 p.2, (X d)⁻¹ := by
    intro k hk
    rw [mem_Ico] at hk
    rw [W, W, ih (k - a) (by omega) a k rfl, ih (b - k) (by omega) k b rfl, sum_product,
      mul_sum, mul_sum, sum_mul_sum]
    refine sum_congr rfl (fun T1 hT1 => sum_congr rfl (fun T2 hT2 => ?_))
    rw [prod_glue X (by omega) (by omega) (mem_tri.1 hT1).1 (mem_tri.1 hT2).1]
  have hbij : ∑ x ∈ (Ico (a + 1) b).sigma (fun k => tri a k ×ˢ tri k b),
      ∏ d ∈ glue a b x.1 x.2.1 x.2.2, (X d)⁻¹ = ∑ T ∈ tri a b, ∏ d ∈ T, (X d)⁻¹ := by
    refine sum_bij (fun x _ => glue a b x.1 x.2.1 x.2.2) ?_ ?_ ?_ ?_
    · rintro ⟨k, T1, T2⟩ hx
      simp only [mem_sigma, mem_product, mem_Ico, mem_tri] at hx
      dsimp only
      exact mem_tri.2 (glue_isTri (by omega) (by omega) hx.2.1 hx.2.2)
    · rintro ⟨k, T1, T2⟩ hx ⟨k', T1', T2'⟩ hx' he
      simp only [mem_sigma, mem_product, mem_Ico, mem_tri] at hx hx'
      obtain ⟨rfl, rfl, rfl⟩ := glue_inj (by omega) (by omega) (by omega) (by omega)
        hx.2.1 hx.2.2 hx'.2.1 hx'.2.2 he
      rfl
    · intro T hT
      rw [mem_tri] at hT
      obtain ⟨k, hak, hkb, hA, hB⟩ := exists_apex hab hT
      refine ⟨⟨k, T.filter (fun d => d.2 ≤ k ∧ d ≠ (a, k)),
        T.filter (fun d => k ≤ d.1 ∧ d ≠ (k, b))⟩, ?_, glue_split hT hak hkb hA hB⟩
      simp only [mem_sigma, mem_product, mem_Ico, mem_tri]
      exact ⟨⟨by omega, hkb⟩, left_isTri hT hak hkb hA hB, right_isTri hT hak hkb hA hB⟩
    · intro x _
      rfl
  rw [F_rec X hab, ← hbij, sum_sigma]
  exact sum_congr rfl step

/-- L-bridge: the triangulation sum equals the apex recursion. -/
theorem amp_eq_F (n : ℕ) (hn : 3 ≤ n) (X : ℕ × ℕ → K) : amp n X = F X 1 n := by
  rw [amp, triangulations_eq_tri, F_eq_sum]

/-! ## Step 2. Telescoping, the factorisation lemma, the `m = 1` family -/

lemma vtx_of_mem {n i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ n) : vtx n i = i := by
  unfold vtx
  rw [show i + n - 1 = (i - 1) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  omega

lemma vtx_bounds (n i : ℕ) (hn : 1 ≤ n) : 1 ≤ vtx n i ∧ vtx n i ≤ n := by
  unfold vtx
  have := Nat.mod_lt (i + n - 1) (by omega : 0 < n)
  omega

lemma vtx_add_n (n i : ℕ) : vtx n (i + n) = vtx n i := by
  unfold vtx
  rw [show i + n + n - 1 = (i + n - 1) + n by omega, Nat.add_mod_right]

/-- Planar variable at labels already in `1..n`. -/
lemma planar_of_mem {n : ℕ} (X : ℕ × ℕ → K) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ n) :
    planar n X i j = if (i, j) ∈ diagonals n then X (i, j) else 0 := by
  unfold planar
  rw [vtx_of_mem hi (by omega), vtx_of_mem (by omega) hj, min_eq_left hij, max_eq_right hij]

lemma planar_eq_X {n : ℕ} (X : ℕ × ℕ → K) {i j : ℕ} (hi : 1 ≤ i) (hij : i + 2 ≤ j) (hj : j ≤ n)
    (h1n : ¬ (i = 1 ∧ j = n)) : planar n X i j = X (i, j) := by
  rw [planar_of_mem X hi (by omega) hj, ite_eq_left (mem_diagonals.2 (by dsimp only; omega))]

lemma planar_side {n : ℕ} (X : ℕ × ℕ → K) {i : ℕ} (hi : 1 ≤ i) (hn : i + 1 ≤ n) :
    planar n X i (i + 1) = 0 := by
  rw [planar_of_mem X hi (by omega) hn, ite_eq_right (by rw [mem_diagonals]; dsimp only; omega)]

lemma planar_one_n {n : ℕ} (X : ℕ × ℕ → K) (hn : 2 ≤ n) : planar n X 1 n = 0 := by
  rw [planar_of_mem X le_rfl (by omega) le_rfl, ite_eq_right (by rw [mem_diagonals]; dsimp only; omega)]

lemma sum_Icc_telescope (φ : ℕ → K) {r t : ℕ} (hrt : r ≤ t) :
    ∑ j ∈ Icc r t, (φ j - φ (j + 1)) = φ r - φ (t + 1) := by
  induction t, hrt using Nat.le_induction with
  | base => simp
  | succ t hrt ih =>
    rw [sum_Icc_succ_top (by omega), ih]
    ring

/-- L-tele: the sum of mesh variables over a rectangle of legs telescopes to its four corners.
(A pure identity for any function of two labels; the hypotheses exclude empty ranges, for which
the statement is false: a disprover check made while drafting.) -/
theorem mesh_telescope (n : ℕ) (X : ℕ × ℕ → K) {p q r t : ℕ} (hpq : p ≤ q) (hrt : r ≤ t) :
    ∑ i ∈ Icc p q, ∑ j ∈ Icc r t, mesh n X i j =
      planar n X p r + planar n X (q + 1) (t + 1) - planar n X p (t + 1) - planar n X (q + 1) r := by
  have inner : ∀ i, ∑ j ∈ Icc r t, mesh n X i j =
      (planar n X i r - planar n X i (t + 1)) - (planar n X (i + 1) r - planar n X (i + 1) (t + 1)) := by
    intro i
    have hm : ∀ j ∈ Icc r t, mesh n X i j = (planar n X i j - planar n X (i + 1) j) -
        (planar n X i (j + 1) - planar n X (i + 1) (j + 1)) := fun j _ => by unfold mesh; ring
    rw [sum_congr rfl hm, sum_Icc_telescope (fun j => planar n X i j - planar n X (i + 1) j) hrt]
    ring
  rw [sum_congr rfl (fun i _ => inner i),
    sum_Icc_telescope (fun i => planar n X i r - planar n X i (t + 1)) hpq]
  ring

/-- (★) On `R_{s-1,1}`: `X_{a b} = X_{a,s+1} + X_{s,b}` for `a ≤ s < b` (planar form; the side
`X_{s,s+1} = 0` is used). -/
lemma star {n s : ℕ} (hs : 2 ≤ s) (hsn : s + 2 ≤ n) (X : ℕ × ℕ → K) (hR : OnRect n (s - 1) 1 X)
    {a b : ℕ} (ha : 1 ≤ a) (has : a ≤ s) (hbs : s + 1 ≤ b) (hbn : b ≤ n) :
    planar n X a b = planar n X a (s + 1) + planar n X s b := by
  have hside : planar n X s (s + 1) = 0 := planar_side X (by omega) (by omega)
  rcases Nat.lt_or_ge a s with h1 | h1
  · rcases Nat.lt_or_ge (s + 1) b with h2 | h2
    · have ht := mesh_telescope n X (p := a) (q := s - 1) (r := s + 1) (t := b - 1)
        (by omega) (by omega)
      have hz : ∑ i ∈ Icc a (s - 1), ∑ j ∈ Icc (s + 1) (b - 1), mesh n X i j = 0 := by
        apply sum_eq_zero
        intro i hi
        apply sum_eq_zero
        intro j hj
        rw [mem_Icc] at hi hj
        exact hR i (by rw [mem_Ico]; omega) j (by rw [mem_Icc]; omega)
      rw [hz, show s - 1 + 1 = s by omega, show b - 1 + 1 = b by omega] at ht
      linear_combination ht - hside
    · obtain rfl : b = s + 1 := by omega
      rw [hside]
      ring
  · obtain rfl : a = s := by omega
    rw [hside]
    ring

lemma W_side (X : ℕ × ℕ → K) (s : ℕ) : W X s (s + 1) = 1 := by
  rw [W, w, ite_eq_right (by omega), F_of_le X (by omega), one_mul]

lemma F_eq_X_mul_W (X : ℕ × ℕ → K) {a b : ℕ} (h : a + 1 < b) (hx : X (a, b) ≠ 0) :
    F X a b = X (a, b) * W X a b := by
  rw [W, w, ite_eq_left h]
  field_simp

/-- L-fact (the factorisation lemma; Zhou's (55)/(76) in current form). Separators: leg `s` and
leg `n`; locus `R_{s-1,1}`. Only the spine diagonals `(a,b)`, `a ≤ s < b`, need `X ≠ 0`. -/
theorem F_factor {n s : ℕ} (hs : 2 ≤ s) (hsn : s + 2 ≤ n) (X : ℕ × ℕ → K)
    (hspine : ∀ a b, 1 ≤ a → a ≤ s → s + 1 ≤ b → b ≤ n → (a, b) ∈ diagonals n → X (a, b) ≠ 0)
    (hR : OnRect n (s - 1) 1 X) {a b : ℕ} (ha : 1 ≤ a) (has : a < s) (hbs : s + 1 < b) (hbn : b ≤ n) :
    F X a b = (planar n X a (s + 1) + planar n X s b) * W X a (s + 1) * W X s b := by
  obtain ⟨N, hN⟩ : ∃ N, b - a = N := ⟨_, rfl⟩
  induction N using Nat.strong_induction_on generalizing a b with
  | _ N ih =>
  have hsp : ∀ a' b', 1 ≤ a' → a' ≤ s → s + 1 ≤ b' → b' ≤ n → a' + 2 ≤ b' →
      ¬ (a' = 1 ∧ b' = n) → X (a', b') ≠ 0 := fun a' b' h1 h2 h3 h4 h5 h6 =>
    hspine a' b' h1 h2 h3 h4 (mem_diagonals.2 (by dsimp only; omega))
  -- consequences of the induction hypothesis: `W(k,b) = W(k,s+1) W(s,b)`, `W(a,k) = W(a,s+1) W(s,k)`
  have hL : ∀ k ∈ Ico (a + 1) s, W X k b = W X k (s + 1) * W X s b := by
    intro k hk
    rw [mem_Ico] at hk
    have e := ih (b - k) (by omega) (by omega) (by omega) hbs hbn rfl
    rw [← star hs hsn X hR (by omega) (by omega) (by omega) hbn,
      planar_eq_X X (by omega) (by omega) hbn (by omega)] at e
    have hx := hsp k b (by omega) (by omega) (by omega) hbn (by omega) (by omega)
    rw [W, w, ite_eq_left (by omega), e]
    field_simp
  have hR' : ∀ k ∈ Ico (s + 2) b, W X a k = W X a (s + 1) * W X s k := by
    intro k hk
    rw [mem_Ico] at hk
    have e := ih (k - a) (by omega) ha has (by omega) (by omega) rfl
    rw [← star hs hsn X hR ha (by omega) (by omega) (by omega),
      planar_eq_X X ha (by omega) (by omega) (by omega)] at e
    have hx := hsp a k ha (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [W, w, ite_eq_left (by omega), e]
    field_simp
  have hxA := hsp a (s + 1) ha (by omega) le_rfl (by omega) (by omega) (by omega)
  have hxB := hsp s b (by omega) le_rfl (by omega) hbn (by omega) (by omega)
  have hA := F_eq_X_mul_W X (by omega : a + 1 < s + 1) hxA
  have hB := F_eq_X_mul_W X (by omega : s + 1 < b) hxB
  have eA : F X a (s + 1) = (∑ k ∈ Ico (a + 1) s, W X a k * W X k (s + 1)) + W X a s * 1 := by
    rw [F_rec X (by omega), sum_Ico_succ_top (by omega), W_side]
  have eB : F X s b = 1 * W X (s + 1) b + ∑ k ∈ Ico (s + 2) b, W X s k * W X k b := by
    rw [F_rec X (by omega), sum_eq_sum_Ico_succ_bot (by omega), W_side]
  rw [F_rec X (by omega), ← sum_Ico_consecutive _ (by omega : a + 1 ≤ s) (by omega : s ≤ b),
    sum_eq_sum_Ico_succ_bot (by omega : s < b), sum_eq_sum_Ico_succ_bot (by omega : s + 1 < b)]
  have hs1 : ∑ k ∈ Ico (a + 1) s, W X a k * W X k b =
      W X s b * ∑ k ∈ Ico (a + 1) s, W X a k * W X k (s + 1) := by
    rw [mul_sum]
    refine sum_congr rfl (fun k hk => ?_)
    rw [hL k hk]
    ring
  have hs2 : ∑ k ∈ Ico (s + 1 + 1) b, W X a k * W X k b =
      W X a (s + 1) * ∑ k ∈ Ico (s + 2) b, W X s k * W X k b := by
    rw [mul_sum]
    refine sum_congr rfl (fun k hk => ?_)
    rw [hR' k hk]
    ring
  rw [hs1, hs2, planar_eq_X X ha (by omega) (by omega) (by omega),
    planar_eq_X X (by omega) (by omega) hbn (by omega)]
  linear_combination (-(W X s b)) * eA + W X s b * hA + (-(W X a (s + 1))) * eB +
    W X a (s + 1) * hB

/-- The `m = 1` family, from L-fact at `(a,b) = (1,n)` and L-tele. -/
theorem amp_eq_zero_m1 {n k : ℕ} (hk : 1 ≤ k) (hkn : k + 3 ≤ n) (X : ℕ × ℕ → K)
    (hX : ∀ d ∈ diagonals n, X d ≠ 0) (hR : OnRect n k 1 X) : amp n X = 0 := by
  have hR' : OnRect n (k + 1 - 1) 1 X := by rwa [Nat.add_sub_cancel]
  have hf := F_factor (s := k + 1) (by omega) (by omega) X
    (fun a b _ _ _ _ hd => hX (a, b) hd) hR' le_rfl (by omega) (by omega) le_rfl
  have hst := star (s := k + 1) (by omega) (by omega) X hR' le_rfl (by omega) (by omega) le_rfl
  rw [planar_one_n X (by omega)] at hst
  rw [amp_eq_F n (by omega), hf, ← hst]
  ring

/-! ## Step 3. Rotation -/

/-- Next label on the `n`-cycle `1..n`. -/
def nxt (n u : ℕ) : ℕ := if u = n then 1 else u + 1

lemma vtx_succ {n : ℕ} (hn : 1 ≤ n) (i : ℕ) : vtx n (i + 1) = nxt n (vtx n i) := by
  unfold vtx nxt
  rw [show i + 1 + n - 1 = (i + n - 1) + 1 by omega]
  generalize i + n - 1 = t
  have ht := Nat.mod_lt t (by omega : 0 < n)
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    simp [Nat.mod_one]
  · rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < n by omega)]
    by_cases hc : t % n + 1 = n
    · rw [hc, Nat.mod_self, ite_eq_left (by omega)]
    · rw [Nat.mod_eq_of_lt (by omega), ite_eq_right (by omega)]

lemma rot_eq {n : ℕ} (hn : 1 ≤ n) {d : ℕ × ℕ} (h1 : 1 ≤ d.1) (h2 : d.1 ≤ n) (h3 : 1 ≤ d.2)
    (h4 : d.2 ≤ n) : rot n d = (min (nxt n d.1) (nxt n d.2), max (nxt n d.1) (nxt n d.2)) := by
  unfold rot
  rw [vtx_succ hn, vtx_succ hn, vtx_of_mem h1 h2, vtx_of_mem h3 h4]

lemma rot_mem {n : ℕ} (hn : 1 ≤ n) {d : ℕ × ℕ} (hd : d ∈ diagonals n) : rot n d ∈ diagonals n := by
  obtain ⟨a, b⟩ := d
  rw [mem_diagonals] at hd
  dsimp only at hd
  rw [rot_eq hn (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)
    (by dsimp only; omega), mem_diagonals]
  dsimp only
  unfold nxt
  split_ifs <;> omega

lemma rot_inj {n : ℕ} (hn : 1 ≤ n) {p q : ℕ × ℕ} (hp : p ∈ diagonals n) (hq : q ∈ diagonals n)
    (h : rot n p = rot n q) : p = q := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  rw [mem_diagonals] at hp hq
  dsimp only at hp hq
  rw [rot_eq hn (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)
    (by dsimp only; omega), rot_eq hn (by dsimp only; omega) (by dsimp only; omega)
    (by dsimp only; omega) (by dsimp only; omega)] at h
  simp only [Prod.mk.injEq] at h ⊢
  unfold nxt at h
  split_ifs at h <;> omega

lemma rot_crosses {n : ℕ} (hn : 1 ≤ n) {p q : ℕ × ℕ} (hp : p ∈ diagonals n)
    (hq : q ∈ diagonals n) : Crosses (rot n p) (rot n q) ↔ Crosses p q := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  rw [mem_diagonals] at hp hq
  dsimp only at hp hq
  rw [rot_eq hn (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)
    (by dsimp only; omega), rot_eq hn (by dsimp only; omega) (by dsimp only; omega)
    (by dsimp only; omega) (by dsimp only; omega)]
  simp only [Crosses]
  unfold nxt
  split_ifs <;> omega

lemma rot_surj {n : ℕ} (hn : 1 ≤ n) {d : ℕ × ℕ} (hd : d ∈ diagonals n) :
    ∃ d0 ∈ diagonals n, rot n d0 = d := by
  have himg : (diagonals n).image (rot n) = diagonals n := by
    refine eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
      exact rot_mem hn hy
    · rw [card_image_of_injOn (fun p hp q hq h => rot_inj hn hp hq h)]
  rw [← himg] at hd
  obtain ⟨d0, hd0, h⟩ := mem_image.1 hd
  exact ⟨d0, hd0, h⟩

/-- Rotation acts on the planar variables by shifting labels. -/
lemma planar_rot {n : ℕ} (hn : 1 ≤ n) (X : ℕ × ℕ → K) (i j : ℕ) :
    planar n (X ∘ rot n) i j = planar n X (i + 1) (j + 1) := by
  unfold planar
  rw [vtx_succ hn i, vtx_succ hn j]
  obtain ⟨h1, h2⟩ := vtx_bounds n i hn
  obtain ⟨h3, h4⟩ := vtx_bounds n j hn
  generalize vtx n i = u at *
  generalize vtx n j = v at *
  have hmem : (min u v, max u v) ∈ diagonals n ↔
      (min (nxt n u) (nxt n v), max (nxt n u) (nxt n v)) ∈ diagonals n := by
    rw [mem_diagonals, mem_diagonals]
    dsimp only
    unfold nxt
    split_ifs <;> omega
  have hpair : rot n (min u v, max u v) = (min (nxt n u) (nxt n v), max (nxt n u) (nxt n v)) := by
    rw [rot_eq hn (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)
      (by dsimp only; omega)]
    dsimp only
    simp only [Prod.mk.injEq]
    unfold nxt
    split_ifs <;> omega
  by_cases hd : (min u v, max u v) ∈ diagonals n
  · rw [ite_eq_left hd, ite_eq_left (hmem.1 hd), Function.comp_apply, hpair]
  · rw [ite_eq_right hd, ite_eq_right (fun h => hd (hmem.2 h))]

lemma mesh_rot {n : ℕ} (hn : 1 ≤ n) (X : ℕ × ℕ → K) (i j : ℕ) :
    mesh n (X ∘ rot n) i j = mesh n X (i + 1) (j + 1) := by
  unfold mesh
  rw [planar_rot hn, planar_rot hn, planar_rot hn, planar_rot hn]

/-- L-rot, locus form: rotating the kinematics moves `R_{k,m+1}` to `R_{k,m}`. -/
theorem onRect_rot {n k m : ℕ} (hn : 4 ≤ n) (X : ℕ × ℕ → K) :
    OnRect n k m (X ∘ rot n) ↔ OnRect n k (m + 1) X := by
  unfold OnRect
  simp only [mesh_rot (by omega : 1 ≤ n)]
  constructor
  · intro h i hi j hj
    rw [mem_Ico] at hi
    rw [mem_Icc] at hj
    have := h (i - 1) (by rw [mem_Ico]; omega) (j - 1) (by rw [mem_Icc]; omega)
    rwa [show i - 1 + 1 = i by omega, show j - 1 + 1 = j by omega] at this
  · intro h i hi j hj
    rw [mem_Ico] at hi
    rw [mem_Icc] at hj
    exact h (i + 1) (by rw [mem_Ico]; omega) (j + 1) (by rw [mem_Icc]; omega)

/-- L-rot: cyclic invariance of the amplitude. -/
theorem amp_rot (n : ℕ) (hn : 3 ≤ n) (X : ℕ × ℕ → K) : amp n (X ∘ rot n) = amp n X := by
  have hn1 : 1 ≤ n := by omega
  have hinj : Set.InjOn (rot n) (diagonals n : Set (ℕ × ℕ)) :=
    fun p hp q hq h => rot_inj hn1 hp hq h
  have hsub : ∀ T ∈ triangulations n, T ⊆ diagonals n := fun T hT => (mem_triangulations.1 hT).1
  have hΦmem : ∀ T ∈ triangulations n, T.image (rot n) ∈ triangulations n := by
    intro T hT
    obtain ⟨hs, hnc, hmax⟩ := mem_triangulations.1 hT
    refine mem_triangulations.2 ⟨?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
      exact rot_mem hn1 (hs hy)
    · intro p hp q hq
      obtain ⟨p0, hp0, rfl⟩ := mem_image.1 hp
      obtain ⟨q0, hq0, rfl⟩ := mem_image.1 hq
      rw [rot_crosses hn1 (hs hp0) (hs hq0)]
      exact hnc p0 hp0 q0 hq0
    · intro d hd hnot
      obtain ⟨d0, hd0, rfl⟩ := rot_surj hn1 hd
      have hnot0 : d0 ∉ T := fun h => hnot (mem_image_of_mem _ h)
      obtain ⟨p0, hp0, hc⟩ := hmax d0 hd0 hnot0
      exact ⟨rot n p0, mem_image_of_mem _ hp0, (rot_crosses hn1 (hs hp0) hd0).2 hc⟩
  have hΦinj : Set.InjOn (fun T : Finset (ℕ × ℕ) => T.image (rot n))
      (triangulations n : Set (Finset (ℕ × ℕ))) := by
    intro T hT T' hT' h
    have hT1 := hsub T hT
    have hT1' := hsub T' hT'
    dsimp only at h
    ext d
    constructor
    · intro hd
      have : rot n d ∈ T'.image (rot n) := h ▸ mem_image_of_mem _ hd
      obtain ⟨d', hd', he⟩ := mem_image.1 this
      rwa [← hinj (hT1' hd') (hT1 hd) he]
    · intro hd
      have : rot n d ∈ T.image (rot n) := h.symm ▸ mem_image_of_mem _ hd
      obtain ⟨d', hd', he⟩ := mem_image.1 this
      rwa [← hinj (hT1 hd') (hT1' hd) he]
  have himg : (triangulations n).image (fun T => T.image (rot n)) = triangulations n := by
    refine eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      obtain ⟨T, hT, rfl⟩ := mem_image.1 hx
      exact hΦmem T hT
    · rw [card_image_of_injOn hΦinj]
  unfold amp
  conv_rhs => rw [← himg]
  rw [sum_image hΦinj]
  refine sum_congr rfl (fun T hT => ?_)
  rw [prod_image (fun p hp q hq h => hinj (hsub T hT hp) (hsub T hT hq) h)]
  rfl

/-! ## Main statement (what Phase 2 imports) -/

/-- **Tree rectangle zero.** Pointwise form over any field: at every point of the `(k,m)`-locus
where all planar variables are non-zero, `A_n = 0`. -/
theorem amp_eq_zero_of_onRect {n k m : ℕ} (hk : 1 ≤ k) (hkn : k + 3 ≤ n) (hm : 1 ≤ m) (hmn : m ≤ n)
    (X : ℕ × ℕ → K) (hX : ∀ d ∈ diagonals n, X d ≠ 0) (hR : OnRect n k m X) :
    amp n X = 0 := by
  clear hmn
  induction m, hm using Nat.le_induction generalizing X with
  | base => exact amp_eq_zero_m1 hk hkn X hX hR
  | succ m hm ih =>
    rw [← onRect_rot (by omega)] at hR
    rw [← amp_rot n (by omega) X]
    exact ih (X ∘ rot n) (fun d hd => hX _ (rot_mem (by omega) hd)) hR

/-! ## Step 5. The general witness, `mesh_adjacent` -/

/-- Witness coordinates on the spine region `a ≤ s < b` (R12-P1 C8), as integers. -/
def uZ (s a : ℕ) : ℤ := if a < s then (s : ℤ) + 1 - a else 0

def vZ (n s b : ℕ) : ℤ := if b = n then -(s : ℤ) else if b = s + 1 then 0 else (b : ℤ) - s

/-- The witness point on `R_{s-1,1}`: `X_{ab} = u_a + v_b` on the spine region, `1` elsewhere. -/
def wit (n s : ℕ) : ℕ × ℕ → ℚ := fun d =>
  if d.1 ≤ s ∧ s + 1 ≤ d.2 then ((uZ s d.1 + vZ n s d.2 : ℤ) : ℚ) else 1

lemma wit_planar {n s : ℕ} (hs : 2 ≤ s) (hsn : s + 2 ≤ n) {a b : ℕ} (ha : 1 ≤ a) (has : a ≤ s)
    (hbs : s + 1 ≤ b) (hbn : b ≤ n) : planar n (wit n s) a b = ((uZ s a + vZ n s b : ℤ) : ℚ) := by
  rw [planar_of_mem _ ha (by omega) hbn]
  by_cases hd : (a, b) ∈ diagonals n
  · rw [ite_eq_left hd, wit, ite_eq_left ⟨has, hbs⟩]
  · rw [ite_eq_right hd]
    rw [mem_diagonals] at hd
    dsimp only at hd
    have h0 : uZ s a + vZ n s b = 0 := by
      unfold uZ vZ
      split_ifs <;> omega
    rw [h0, Int.cast_zero]

lemma wit_ne_zero {n s : ℕ} (hs : 2 ≤ s) (hsn : s + 2 ≤ n) :
    ∀ d ∈ diagonals n, wit n s d ≠ 0 := by
  rintro ⟨a, b⟩ hd
  rw [mem_diagonals] at hd
  dsimp only at hd
  unfold wit
  dsimp only
  split_ifs with h
  · rw [Int.cast_ne_zero]
    unfold uZ vZ
    split_ifs <;> omega
  · exact one_ne_zero

lemma wit_onRect {n s : ℕ} (hs : 2 ≤ s) (hsn : s + 2 ≤ n) : OnRect n (s - 1) 1 (wit n s) := by
  intro i hi j hj
  rw [mem_Ico] at hi
  rw [mem_Icc] at hj
  unfold mesh
  rw [wit_planar hs hsn (by omega) (by omega) (by omega) (by omega),
    wit_planar hs hsn (by omega) (by omega) (by omega) (by omega),
    wit_planar hs hsn (by omega) (by omega) (by omega) (by omega),
    wit_planar hs hsn (by omega) (by omega) (by omega) (by omega)]
  push_cast
  ring

lemma onRect_add_n {n k m : ℕ} (X : ℕ × ℕ → K) (h : OnRect n k m X) : OnRect n k (m + n) X := by
  intro i hi j hj
  rw [mem_Ico] at hi
  rw [mem_Icc] at hj
  have := h (i - n) (by rw [mem_Ico]; omega) (j - n) (by rw [mem_Icc]; omega)
  have hp : ∀ x y, n ≤ x → n ≤ y → planar n X x y = planar n X (x - n) (y - n) := by
    intro x y hx hy
    unfold planar
    conv_lhs => rw [show x = (x - n) + n by omega, show y = (y - n) + n by omega]
    rw [vtx_add_n, vtx_add_n]
  unfold mesh at this ⊢
  rw [hp i j (by omega) (by omega), hp (i + 1) (j + 1) (by omega) (by omega),
    hp i (j + 1) (by omega) (by omega), hp (i + 1) j (by omega) (by omega),
    show i + 1 - n = i - n + 1 by omega, show j + 1 - n = j - n + 1 by omega]
  exact this

/-- Inhabitation witness (general `n`): the hypotheses of the main theorem are satisfiable. -/
theorem onRect_inhabited {n k m : ℕ} (hk : 1 ≤ k) (hkn : k + 3 ≤ n) (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∃ X : ℕ × ℕ → ℚ, (∀ d ∈ diagonals n, X d ≠ 0) ∧ OnRect n k m X := by
  have hn1 : 1 ≤ n := by omega
  -- the witness on `R_{k,1}`, moved to `R_{k,1+n}` by periodicity
  have base : ∃ X : ℕ × ℕ → ℚ, (∀ d ∈ diagonals n, X d ≠ 0) ∧ OnRect n k (1 + n) X := by
    refine ⟨wit n (k + 1), wit_ne_zero (by omega) (by omega), onRect_add_n _ ?_⟩
    have := wit_onRect (n := n) (s := k + 1) (by omega) (by omega)
    rwa [Nat.add_sub_cancel] at this
  -- rotate down one step at a time
  have down : ∀ j, j ≤ n → ∃ X : ℕ × ℕ → ℚ, (∀ d ∈ diagonals n, X d ≠ 0) ∧
      OnRect n k (1 + n - j) X := by
    intro j
    induction j with
    | zero => intro _; simpa using base
    | succ j ih =>
      intro hj
      obtain ⟨X, hX, hR⟩ := ih (by omega)
      refine ⟨X ∘ rot n, fun d hd => hX _ (rot_mem hn1 hd), ?_⟩
      rw [onRect_rot (by omega), show 1 + n - (j + 1) + 1 = 1 + n - j by omega]
      exact hR
  have := down (n + 1 - m) (by omega)
  rwa [show 1 + n - (n + 1 - m) = m by omega] at this

/-- Negative control (off-by-one, too long): extending the `j`-range to `m-1+n` puts the adjacent
pair `(m, m-1)` in the locus, which forces the diagonal `(m-1, m+1)` to vanish, so a theorem with
that locus would hold vacuously. Guarded by `onRect_inhabited`. -/
theorem mesh_adjacent (n : ℕ) (hn : 4 ≤ n) (X : ℕ × ℕ → K) (i : ℕ) :
    mesh n X i (i + 1) = - planar n X i (i + 2) := by
  have hn1 : 1 ≤ n := by omega
  have hadj : ∀ x, planar n X x (x + 1) = 0 := by
    intro x
    unfold planar
    rw [vtx_succ hn1]
    obtain ⟨h1, h2⟩ := vtx_bounds n x hn1
    generalize vtx n x = u at *
    rw [ite_eq_right]
    rw [mem_diagonals]
    dsimp only
    unfold nxt
    split_ifs <;> omega
  have hdiag : ∀ x, planar n X x x = 0 := by
    intro x
    unfold planar
    rw [ite_eq_right]
    rw [mem_diagonals]
    dsimp only
    omega
  unfold mesh
  rw [hadj i, show i + 1 + 1 = i + 2 by omega, show i + 2 = (i + 1) + 1 by omega, hadj (i + 1),
    hdiag (i + 1)]
  ring

/-! ## Sanity checks and negative controls at n = 5 -/

section N5

/-- PROVED (target): the definition reproduces the printed five-term amplitude
[arXiv:2312.16282 eq. (3.1)]. -/
theorem triangulations_five :
    triangulations 5 = {{(1, 3), (1, 4)}, {(1, 3), (3, 5)}, {(1, 4), (2, 4)}, {(2, 5), (3, 5)},
      {(2, 4), (2, 5)}} := by
  decide

/-- The n = 5 witness for `R_{1,1}` (explicit values from `route_a.py witness`). -/
def X5w : ℕ × ℕ → ℚ := fun d =>
  if d = (1, 3) then 2 else if d = (1, 4) then 4 else if d = (2, 4) then 2
  else if d = (2, 5) then -2 else if d = (3, 5) then 1 else 0

theorem X5w_onRect : OnRect 5 1 1 X5w := by
  intro i hi j hj
  simp only [mem_Ico, mem_Icc] at hi hj
  obtain rfl : i = 1 := by omega
  have h1 : 3 ≤ j := by omega
  have h2 : j ≤ 4 := by omega
  interval_cases j <;> simp [mesh, planar, vtx, diagonals, X5w] <;> norm_num

theorem X5w_ne_zero : ∀ d ∈ diagonals 5, X5w d ≠ 0 := by
  decide

/-- Negative control (rectangle minus one tile): `c₁₃ = 0` alone does not force `A_5 = 0`. -/
def X5n : ℕ × ℕ → ℚ := fun d => if d = (1, 4) then 2 else 1

theorem negcontrol_minus_tile :
    mesh 5 X5n 1 3 = 0 ∧ (∀ d ∈ diagonals 5, X5n d ≠ 0) ∧ amp 5 X5n ≠ 0 := by
  refine ⟨by simp [mesh, planar, vtx, diagonals, X5n]; norm_num, by decide, ?_⟩
  rw [amp, triangulations_five]
  simp (config := {decide := true}) only [Finset.sum_insert, Finset.prod_insert, Finset.sum_singleton,
    Finset.prod_singleton, Finset.mem_insert, Finset.mem_singleton]
  norm_num [X5n]

/-- PROVED: the main theorem at `n = 5`, `R_{1,1}`, from the definitions above (end-to-end check
that `vtx`/`planar`/`mesh`/`OnRect` encode [arXiv:2312.16282 §3.1.1] `c₁₃ = c₁₄ = 0`). -/
theorem amp_five_rect11 (X : ℕ × ℕ → K) (hX : ∀ d ∈ diagonals 5, X d ≠ 0) (hR : OnRect 5 1 1 X) :
    amp 5 X = 0 := by
  have e3 := hR 1 (by simp) 3 (by simp)
  have e4 := hR 1 (by simp) 4 (by simp)
  simp [mesh, planar, vtx, diagonals] at e3 e4
  have h13 := hX (1, 3) (by decide)
  have h14 := hX (1, 4) (by decide)
  have h24 := hX (2, 4) (by decide)
  have h25 := hX (2, 5) (by decide)
  have h35 := hX (3, 5) (by decide)
  have x24 : X (2, 4) = X (1, 4) - X (1, 3) := by linear_combination e3
  have x25 : X (2, 5) = - X (1, 3) := by linear_combination e4 + e3
  rw [amp, triangulations_five]
  simp (config := {decide := true}) only [Finset.sum_insert, Finset.prod_insert, Finset.sum_singleton,
    Finset.prod_singleton, Finset.mem_insert, Finset.mem_singleton]
  rw [x24] at h24
  rw [x25] at h25
  rw [x24, x25]
  field_simp
  ring

end N5

/-! ## Reviewer additions (opus-2026-09-23-R12P1-rev) -/

/-- Reviewer negative control 1: the main statement WITHOUT the non-vanishing hypothesis `hX`
is false (junk value `0⁻¹ = 0`). Point on `R_{1,1}` at n = 5 with `X₁₃ = X₁₄ = 1`, hence
`X₂₄ = 0` (a spine diagonal) and `X₂₅ = -1`; `X₃₅ = 1`. Then `amp = 1 ≠ 0`. -/
def Xrev1 : ℕ × ℕ → ℚ := fun d =>
  if d = (1, 3) then 1 else if d = (1, 4) then 1 else if d = (2, 4) then 0
  else if d = (2, 5) then -1 else if d = (3, 5) then 1 else 0

theorem rev_negcontrol_no_hX :
    ¬ (∀ X : ℕ × ℕ → ℚ, OnRect 5 1 1 X → amp 5 X = 0) := by
  intro h
  have hR : OnRect 5 1 1 Xrev1 := by
    intro i hi j hj
    simp only [mem_Ico, mem_Icc] at hi hj
    obtain rfl : i = 1 := by omega
    have h1 : 3 ≤ j := by omega
    have h2 : j ≤ 4 := by omega
    interval_cases j <;> simp [mesh, planar, vtx, diagonals, Xrev1] <;> norm_num
  have h0 := h Xrev1 hR
  rw [amp, triangulations_five] at h0
  simp (config := {decide := true}) only [Finset.sum_insert, Finset.prod_insert, Finset.sum_singleton,
    Finset.prod_singleton, Finset.mem_insert, Finset.mem_singleton] at h0
  norm_num [Xrev1] at h0

/-- Reviewer negative control 2: with a non-strict crossing test (diagonals sharing an endpoint
count as crossing), the "triangulations" of the pentagon would be wrong: none of the five genuine
triangulations survives. Shows `Crosses` must be strict. -/
def CrossesBad (p q : ℕ × ℕ) : Prop :=
  (p.1 ≤ q.1 ∧ q.1 ≤ p.2 ∧ p.2 ≤ q.2 ∧ p ≠ q) ∨ (q.1 ≤ p.1 ∧ p.1 ≤ q.2 ∧ q.2 ≤ p.2 ∧ p ≠ q)

instance : DecidableRel CrossesBad := fun _ _ => by unfold CrossesBad; infer_instance

theorem rev_negcontrol_crossing :
    ((diagonals 5).powerset.filter (fun T => T.card = 2 ∧
      ∀ p ∈ T, ∀ q ∈ T, ¬ CrossesBad p q)).card ≠ 5 := by
  decide

/-- Reviewer sanity: the six-gon has Catalan(4) = 14 triangulations under the file's definition. -/
theorem rev_card_triangulations_six : (triangulations 6).card = 14 := by
  decide

/-! ## R12-P1b additions -/

/-- A concrete non-vacuous instance: the step-5 witness at `n = 7` satisfies every hypothesis of
the `m = 1` theorem on `R_{2,1}` (`s = 3`), which then gives `A_7 = 0` there. -/
example : amp 7 (wit 7 3) = 0 :=
  amp_eq_zero_m1 (k := 2) (by norm_num) (by norm_num) _ (wit_ne_zero (by norm_num) (by norm_num))
    (wit_onRect (n := 7) (s := 3) (by norm_num) (by norm_num))

end R12P1

#print axioms R12P1.amp_eq_zero_of_onRect
#print axioms R12P1.onRect_inhabited
#print axioms R12P1.amp_eq_F
#print axioms R12P1.F_eq_sum
#print axioms R12P1.mesh_telescope
#print axioms R12P1.star
#print axioms R12P1.F_factor
#print axioms R12P1.amp_eq_zero_m1
#print axioms R12P1.amp_rot
#print axioms R12P1.onRect_rot
#print axioms R12P1.mesh_adjacent
#print axioms R12P1.triangulations_five
#print axioms R12P1.X5w_onRect
#print axioms R12P1.X5w_ne_zero
#print axioms R12P1.negcontrol_minus_tile
#print axioms R12P1.amp_five_rect11
#print axioms R12P1.rev_negcontrol_no_hX
#print axioms R12P1.rev_negcontrol_crossing
#print axioms R12P1.rev_card_triangulations_six
