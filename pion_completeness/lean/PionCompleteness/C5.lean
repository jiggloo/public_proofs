import PionCompleteness.C4

namespace PiZ

open Finset R12P1 R12P4A R12P3 R12P3C

/-- **B8 (split of a dissection through `C` gives child dissections)**. -/
theorem pkG_split_dis {N a b : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (ha : 1 ≤ a) (hb : b ≤ N) (hab : a + 3 ≤ b)
    (hC : ¬ (a = 1 ∧ b = N)) (hodd : (b - a) % 2 = 1) {D : Finset (ℕ × ℕ)} (hD : D ∈ pkG_dis N)
    (hCD : (a, b) ∈ D) :
    (pkG_split a b D).1 ∈ pkG_dis (b - a + 1) ∧ (pkG_split a b D).2 ∈ pkG_dis (N - (b - a) + 1) := by
  refine ⟨pkG_mem_dis.2 ⟨fun d hd => ?_, fun p hp q hq => ?_⟩, pkG_mem_dis.2 ⟨fun d hd => ?_, fun p hp q hq => ?_⟩⟩
  · obtain ⟨R, hR, h, rfl⟩ := pkG_mem_split1.1 hd
    have c := pkG_chord hD hR
    rw [pkG_mem_odd, pkG_shI_fst, pkG_shI_snd]
    omega
  · obtain ⟨P, hP, h, rfl⟩ := pkG_mem_split1.1 hp
    obtain ⟨Q, hQ, h', rfl⟩ := pkG_mem_split1.1 hq
    have c := (pkG_mem_dis.1 hD).2 P hP Q hQ
    rw [pkG_crosses_iff] at c ⊢
    rw [pkG_shI_fst, pkG_shI_snd, pkG_shI_fst, pkG_shI_snd]
    omega
  · obtain ⟨R, hR, h, rfl⟩ := pkG_mem_split2.1 hd
    have c := pkG_chord hD hR
    have o := pkG_out_ends hD hCD hR h
    have k1 := pkG_cl_cases a b R.1
    have k2 := pkG_cl_cases a b R.2
    rw [pkG_mem_odd, pkG_clP_fst, pkG_clP_snd]
    omega
  · obtain ⟨P, hP, h, rfl⟩ := pkG_mem_split2.1 hp
    obtain ⟨Q, hQ, h', rfl⟩ := pkG_mem_split2.1 hq
    have c := (pkG_mem_dis.1 hD).2 P hP Q hQ
    have o := pkG_out_ends hD hCD hP h
    have o' := pkG_out_ends hD hCD hQ h'
    have k1 := pkG_cl_cases a b P.1
    have k2 := pkG_cl_cases a b P.2
    have k3 := pkG_cl_cases a b Q.1
    have k4 := pkG_cl_cases a b Q.2
    rw [pkG_crosses_iff] at c ⊢
    rw [pkG_clP_fst, pkG_clP_snd, pkG_clP_fst, pkG_clP_snd]
    omega

/-- **B8 (split ∘ glue = id)**. -/
theorem pkG_split_glue {N a b : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (ha : 1 ≤ a) (hb : b ≤ N) (hab : a + 3 ≤ b)
    (hC : ¬ (a = 1 ∧ b = N)) (hodd : (b - a) % 2 = 1) {D₁ D₂ : Finset (ℕ × ℕ)}
    (hD₁ : D₁ ∈ pkG_dis (b - a + 1)) (hD₂ : D₂ ∈ pkG_dis (N - (b - a) + 1)) :
    pkG_split a b (pkG_glue a b D₁ D₂) = (D₁, D₂) := by
  refine Prod.ext ?_ ?_
  · ext d
    rw [pkG_mem_split1]
    constructor
    · rintro ⟨R, hR, h, rfl⟩
      rcases pkG_mem_glue.1 hR with rfl | ⟨R₁, hR₁, rfl⟩ | ⟨R₂, hR₂, rfl⟩
      · dsimp only at h
        omega
      · have c := pkG_chord hD₁ hR₁
        have e : pkG_shI a (pkG_shP a R₁) = R₁ := by
          refine Prod.ext ?_ ?_
          · rw [pkG_shI_fst, pkG_shP_fst]; omega
          · rw [pkG_shI_snd, pkG_shP_snd]; omega
        rw [e]
        exact hR₁
      · have c := pkG_chord hD₂ hR₂
        have k1 := pkG_ct_cases a b R₂.1
        have k2 := pkG_ct_cases a b R₂.2
        rw [pkG_ctP_fst, pkG_ctP_snd] at h
        omega
    · intro hd
      have c := pkG_chord hD₁ hd
      refine ⟨pkG_shP a d, pkG_mem_glue.2 (Or.inr (Or.inl ⟨d, hd, rfl⟩)), ?_, ?_⟩
      · rw [pkG_shP_fst, pkG_shP_snd]
        omega
      · refine Prod.ext ?_ ?_
        · rw [pkG_shI_fst, pkG_shP_fst]; omega
        · rw [pkG_shI_snd, pkG_shP_snd]; omega
  · ext d
    rw [pkG_mem_split2]
    constructor
    · rintro ⟨R, hR, h, rfl⟩
      rcases pkG_mem_glue.1 hR with rfl | ⟨R₁, hR₁, rfl⟩ | ⟨R₂, hR₂, rfl⟩
      · dsimp only at h
        omega
      · have c := pkG_chord hD₁ hR₁
        rw [pkG_shP_fst, pkG_shP_snd] at h
        omega
      · have e : pkG_clP a b (pkG_ctP a b R₂) = R₂ := by
          have k1 := pkG_ct_cases a b R₂.1
          have k2 := pkG_ct_cases a b R₂.2
          have k3 := pkG_cl_cases a b (pkG_ct a b R₂.1)
          have k4 := pkG_cl_cases a b (pkG_ct a b R₂.2)
          refine Prod.ext ?_ ?_
          · rw [pkG_clP_fst, pkG_ctP_fst]; omega
          · rw [pkG_clP_snd, pkG_ctP_snd]; omega
        rw [e]
        exact hR₂
    · intro hd
      have c := pkG_chord hD₂ hd
      have k1 := pkG_ct_cases a b d.1
      have k2 := pkG_ct_cases a b d.2
      refine ⟨pkG_ctP a b d, pkG_mem_glue.2 (Or.inr (Or.inr ⟨d, hd, rfl⟩)), ?_, ?_⟩
      · rw [pkG_ctP_fst, pkG_ctP_snd]
        omega
      · have k3 := pkG_cl_cases a b (pkG_ct a b d.1)
        have k4 := pkG_cl_cases a b (pkG_ct a b d.2)
        refine Prod.ext ?_ ?_
        · rw [pkG_clP_fst, pkG_ctP_fst]; omega
        · rw [pkG_clP_snd, pkG_ctP_snd]; omega

/-- **B8 (glue ∘ split = id on dissections through `C`)**. -/
theorem pkG_glue_split {N a b : ℕ} (ha : 1 ≤ a) (hab : a + 3 ≤ b) {D : Finset (ℕ × ℕ)} (hD : D ∈ pkG_dis N)
    (hCD : (a, b) ∈ D) : pkG_glue a b (pkG_split a b D).1 (pkG_split a b D).2 = D := by
  ext R
  rw [pkG_mem_glue]
  constructor
  · rintro (rfl | ⟨R₁, hR₁, rfl⟩ | ⟨R₂, hR₂, rfl⟩)
    · exact hCD
    · obtain ⟨R', hR', h, rfl⟩ := pkG_mem_split1.1 hR₁
      have c := pkG_chord hD hR'
      have e : pkG_shP a (pkG_shI a R') = R' := by
        refine Prod.ext ?_ ?_
        · rw [pkG_shP_fst, pkG_shI_fst]; omega
        · rw [pkG_shP_snd, pkG_shI_snd]; omega
      rw [e]
      exact hR'
    · obtain ⟨R', hR', h, rfl⟩ := pkG_mem_split2.1 hR₂
      have o := pkG_out_ends hD hCD hR' h
      have c := pkG_chord hD hR'
      have k1 := pkG_cl_cases a b R'.1
      have k2 := pkG_cl_cases a b R'.2
      have e : pkG_ctP a b (pkG_clP a b R') = R' := by
        have k3 := pkG_ct_cases a b (pkG_cl a b R'.1)
        have k4 := pkG_ct_cases a b (pkG_cl a b R'.2)
        refine Prod.ext ?_ ?_
        · rw [pkG_ctP_fst, pkG_clP_fst]; omega
        · rw [pkG_ctP_snd, pkG_clP_snd]; omega
      rw [e]
      exact hR'
  · intro hR
    by_cases hc : R = (a, b)
    · exact Or.inl hc
    · have hc' : ¬ (R.1 = a ∧ R.2 = b) := fun q => hc (Prod.ext q.1 q.2)
      have c := pkG_chord hD hR
      by_cases hin : a ≤ R.1 ∧ R.2 ≤ b
      · refine Or.inr (Or.inl ⟨pkG_shI a R, pkG_mem_split1.2 ⟨R, hR, ⟨hin.1, hin.2, hc'⟩, rfl⟩, ?_⟩)
        refine Prod.ext ?_ ?_
        · rw [pkG_shP_fst, pkG_shI_fst]; omega
        · rw [pkG_shP_snd, pkG_shI_snd]; omega
      · refine Or.inr (Or.inr ⟨pkG_clP a b R, pkG_mem_split2.2 ⟨R, hR, hin, rfl⟩, ?_⟩)
        have o := pkG_out_ends hD hCD hR hin
        have k1 := pkG_cl_cases a b R.1
        have k2 := pkG_cl_cases a b R.2
        have k3 := pkG_ct_cases a b (pkG_cl a b R.1)
        have k4 := pkG_ct_cases a b (pkG_cl a b R.2)
        refine Prod.ext ?_ ?_
        · rw [pkG_ctP_fst, pkG_clP_fst]; omega
        · rw [pkG_ctP_snd, pkG_clP_snd]; omega

/-- One term of the Cayley numerator: `(−1)^|D| · Π_faces V · Π_{mixed ∖ D} x`. -/
def pkG_term (N : ℕ) (x : ℕ × ℕ → ℚ) (D : Finset (ℕ × ℕ)) : ℚ :=
  (-1 : ℚ) ^ D.card * Finset.prod (pkG_roots N D) (fun r => pkG_V N x D r) *
    Finset.prod (oddDiagonals N \ D) (fun d => x d)

/-- **D1 (pointwise numerator)** `M_N · Π_{mixed} X` as a sum over mixed dissections. -/
def pkG_num (N : ℕ) (x : ℕ × ℕ → ℚ) : ℚ := ∑ D ∈ pkG_dis N, pkG_term N x D

/-- The mixed diagonals crossing `(a, b)`. -/
def pkG_crs (N a b : ℕ) : Finset (ℕ × ℕ) := (oddDiagonals N).filter (fun d => Crosses d (a, b))

theorem pkG_shP_inj {a : ℕ} (ha : 1 ≤ a) : Function.Injective (pkG_shP a) := by
  intro d d' e
  have e1 := congrArg Prod.fst e
  have e2 := congrArg Prod.snd e
  rw [pkG_shP_fst, pkG_shP_fst] at e1
  rw [pkG_shP_snd, pkG_shP_snd] at e2
  exact Prod.ext (by omega) (by omega)

theorem pkG_ctP_inj (a b : ℕ) : Function.Injective (pkG_ctP a b) := by
  intro d d' e
  have e1 := congrArg Prod.fst e
  have e2 := congrArg Prod.snd e
  rw [pkG_ctP_fst, pkG_ctP_fst] at e1
  rw [pkG_ctP_snd, pkG_ctP_snd] at e2
  have k1 := pkG_ct_cases a b d.1
  have k2 := pkG_ct_cases a b d.2
  have k3 := pkG_ct_cases a b d'.1
  have k4 := pkG_ct_cases a b d'.2
  exact Prod.ext (by omega) (by omega)

/-- A relabelled inside pair and a contracted pair coincide only at `C`. -/
theorem pkG_sh_ne_ct {a b : ℕ} (ha : 1 ≤ a) (hab : a + 3 ≤ b) {d₁ d₂ : ℕ × ℕ} (h1 : 1 ≤ d₁.1)
    (h2 : d₁.2 ≤ b - a + 1) (h3 : d₁.1 < d₁.2) (h4 : ¬ (d₁.1 = 1 ∧ d₁.2 = b - a + 1)) (h5 : d₂.1 + 2 ≤ d₂.2) :
    pkG_shP a d₁ ≠ pkG_ctP a b d₂ := by
  intro e
  have e1 := congrArg Prod.fst e
  have e2 := congrArg Prod.snd e
  rw [pkG_shP_fst, pkG_ctP_fst] at e1
  rw [pkG_shP_snd, pkG_ctP_snd] at e2
  have k1 := pkG_ct_cases a b d₂.1
  have k2 := pkG_ct_cases a b d₂.2
  omega

/-- **B8 (the mixed diagonals not in a glued dissection)**: inside ones, outside ones, and those crossing `C`. -/
theorem pkG_odd_sdiff {N a b : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (ha : 1 ≤ a) (hb : b ≤ N) (hab : a + 3 ≤ b)
    (hC : ¬ (a = 1 ∧ b = N)) (hodd : (b - a) % 2 = 1) {D₁ D₂ : Finset (ℕ × ℕ)}
    (hD₁ : D₁ ∈ pkG_dis (b - a + 1)) (hD₂ : D₂ ∈ pkG_dis (N - (b - a) + 1)) :
    oddDiagonals N \ pkG_glue a b D₁ D₂ = ((oddDiagonals (b - a + 1) \ D₁).image (pkG_shP a) ∪
      (oddDiagonals (N - (b - a) + 1) \ D₂).image (pkG_ctP a b)) ∪ pkG_crs N a b := by
  have hD := pkG_glue_dis hN hE ha hb hab hC hodd hD₁ hD₂
  have hCg : (a, b) ∈ pkG_glue a b D₁ D₂ := pkG_mem_glue.2 (Or.inl rfl)
  ext d
  rw [mem_union, mem_union, mem_sdiff]
  constructor
  · rintro ⟨hdo, hdg⟩
    have od := pkG_mem_odd.1 hdo
    by_cases hx : Crosses d (a, b)
    · exact Or.inr (mem_filter.2 ⟨hdo, hx⟩)
    · have hx' := hx
      rw [pkG_crosses_iff] at hx'
      dsimp only at hx'
      by_cases hin : a ≤ d.1 ∧ d.2 ≤ b
      · have hc : ¬ (d.1 = a ∧ d.2 = b) := fun q => hdg (by rw [show d = (a, b) from Prod.ext q.1 q.2]; exact hCg)
        have e : pkG_shP a (pkG_shI a d) = d := by
          refine Prod.ext ?_ ?_
          · rw [pkG_shP_fst, pkG_shI_fst]; omega
          · rw [pkG_shP_snd, pkG_shI_snd]; omega
        refine Or.inl (Or.inl (mem_image.2 ⟨pkG_shI a d, mem_sdiff.2 ⟨?_, fun h => hdg ?_⟩, e⟩))
        · rw [pkG_mem_odd, pkG_shI_fst, pkG_shI_snd]
          omega
        · exact pkG_mem_glue.2 (Or.inr (Or.inl ⟨pkG_shI a d, h, e⟩))
      · have k1 := pkG_cl_cases a b d.1
        have k2 := pkG_cl_cases a b d.2
        have e : pkG_ctP a b (pkG_clP a b d) = d := by
          have k3 := pkG_ct_cases a b (pkG_cl a b d.1)
          have k4 := pkG_ct_cases a b (pkG_cl a b d.2)
          refine Prod.ext ?_ ?_
          · rw [pkG_ctP_fst, pkG_clP_fst]; omega
          · rw [pkG_ctP_snd, pkG_clP_snd]; omega
        refine Or.inl (Or.inr (mem_image.2 ⟨pkG_clP a b d, mem_sdiff.2 ⟨?_, fun h => hdg ?_⟩, e⟩))
        · rw [pkG_mem_odd, pkG_clP_fst, pkG_clP_snd]
          omega
        · exact pkG_mem_glue.2 (Or.inr (Or.inr ⟨pkG_clP a b d, h, e⟩))
  · rintro ((h | h) | h)
    · obtain ⟨d₁, hd₁, rfl⟩ := mem_image.1 h
      obtain ⟨h1, h2⟩ := mem_sdiff.1 hd₁
      have od := pkG_mem_odd.1 h1
      refine ⟨?_, fun hg => ?_⟩
      · rw [pkG_mem_odd, pkG_shP_fst, pkG_shP_snd]
        omega
      · rcases pkG_mem_glue.1 hg with e | ⟨R₁, hR₁, e⟩ | ⟨R₂, hR₂, e⟩
        · have e1 := congrArg Prod.fst e
          have e2 := congrArg Prod.snd e
          rw [pkG_shP_fst] at e1
          rw [pkG_shP_snd] at e2
          dsimp only at e1 e2
          omega
        · rw [pkG_shP_inj ha e] at hR₁
          exact h2 hR₁
        · have c := pkG_chord hD₂ hR₂
          exact pkG_sh_ne_ct ha hab (by omega) (by omega) (by omega) (by omega) (by omega) e.symm
    · obtain ⟨d₂, hd₂, rfl⟩ := mem_image.1 h
      obtain ⟨h1, h2⟩ := mem_sdiff.1 hd₂
      have od := pkG_mem_odd.1 h1
      have k1 := pkG_ct_cases a b d₂.1
      have k2 := pkG_ct_cases a b d₂.2
      refine ⟨?_, fun hg => ?_⟩
      · rw [pkG_mem_odd, pkG_ctP_fst, pkG_ctP_snd]
        omega
      · rcases pkG_mem_glue.1 hg with e | ⟨R₁, hR₁, e⟩ | ⟨R₂, hR₂, e⟩
        · have e1 := congrArg Prod.fst e
          have e2 := congrArg Prod.snd e
          rw [pkG_ctP_fst] at e1
          rw [pkG_ctP_snd] at e2
          dsimp only at e1 e2
          omega
        · have c := pkG_chord hD₁ hR₁
          exact pkG_sh_ne_ct ha hab (by omega) (by omega) (by omega) (by omega) (by omega) e
        · rw [(pkG_ctP_inj a b) e] at hR₂
          exact h2 hR₂
    · obtain ⟨hdo, hx⟩ := mem_filter.1 h
      exact ⟨hdo, fun hg => (pkG_mem_dis.1 hD).2 d hg (a, b) hCg hx⟩

/-- **B8 + B9 (one term of the glued dissection)**: `term(D) = −term(D₁)·term(D₂)·Π_{crossing} X` when `X_C = 0`. -/
theorem pkG_term_glue {N a b : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (ha : 1 ≤ a) (hb : b ≤ N) (hab : a + 3 ≤ b)
    (hC : ¬ (a = 1 ∧ b = N)) (hodd : (b - a) % 2 = 1) {D₁ D₂ : Finset (ℕ × ℕ)}
    (hD₁ : D₁ ∈ pkG_dis (b - a + 1)) (hD₂ : D₂ ∈ pkG_dis (N - (b - a) + 1)) (y : ℕ × ℕ → ℚ) (hy : y (a, b) = 0) :
    pkG_term N y (pkG_glue a b D₁ D₂) =
      -(pkG_term (b - a + 1) (fun d => y (pkG_shP a d)) D₁ * pkG_term (N - (b - a) + 1) (fun d => y (pkG_ctP a b d)) D₂) *
        Finset.prod (pkG_crs N a b) (fun d => y d) := by
  have hD := pkG_glue_dis hN hE ha hb hab hC hodd hD₁ hD₂
  have et : ∀ n x D, pkG_term n x D = (-1 : ℚ) ^ D.card * Finset.prod (pkG_roots n D) (fun r => pkG_V n x D r) *
      Finset.prod (oddDiagonals n \ D) (fun d => x d) := fun _ _ _ => rfl
  have er : ∀ n D, pkG_roots n D = insert (1, n) D := fun _ _ => rfl
  have eg : pkG_glue a b D₁ D₂ = insert (a, b) (D₁.image (pkG_shP a) ∪ D₂.image (pkG_ctP a b)) := rfl
  have hdisj : Disjoint (D₁.image (pkG_shP a)) (D₂.image (pkG_ctP a b)) := by
    rw [disjoint_left]
    intro d h h'
    obtain ⟨d₁, hd₁, rfl⟩ := mem_image.1 h
    obtain ⟨d₂, hd₂, e⟩ := mem_image.1 h'
    have c1 := pkG_chord hD₁ hd₁
    have c2 := pkG_chord hD₂ hd₂
    exact pkG_sh_ne_ct ha hab (by omega) (by omega) (by omega) (by omega) (by omega) e.symm
  have hCn : (a, b) ∉ D₁.image (pkG_shP a) ∪ D₂.image (pkG_ctP a b) := by
    intro h
    rcases mem_union.1 h with h | h
    · obtain ⟨d₁, hd₁, e⟩ := mem_image.1 h
      have c1 := pkG_chord hD₁ hd₁
      have e1 := congrArg Prod.fst e
      have e2 := congrArg Prod.snd e
      rw [pkG_shP_fst] at e1
      rw [pkG_shP_snd] at e2
      dsimp only at e1 e2
      omega
    · obtain ⟨d₂, hd₂, e⟩ := mem_image.1 h
      have c2 := pkG_chord hD₂ hd₂
      have e1 := congrArg Prod.fst e
      have e2 := congrArg Prod.snd e
      rw [pkG_ctP_fst] at e1
      rw [pkG_ctP_snd] at e2
      dsimp only at e1 e2
      have k1 := pkG_ct_cases a b d₂.1
      have k2 := pkG_ct_cases a b d₂.2
      omega
  have hTn : (1, N) ∉ pkG_glue a b D₁ D₂ := pkG_top_nmem hD
  -- the sign
  have hcard : (pkG_glue a b D₁ D₂).card = D₁.card + D₂.card + 1 := by
    rw [eg, card_insert_of_notMem hCn, card_union_of_disjoint hdisj, card_image_of_injective _ (pkG_shP_inj ha),
      card_image_of_injective _ (pkG_ctP_inj a b)]
  -- the faces
  have hsh1 : pkG_shP a (1, b - a + 1) = (a, b) := Prod.ext (by rw [pkG_shP_fst]; dsimp only; omega)
    (by rw [pkG_shP_snd]; dsimp only; omega)
  have hct1 : pkG_ctP a b (1, N - (b - a) + 1) = (1, N) := by
    have k1 := pkG_ct_cases a b 1
    have k2 := pkG_ct_cases a b (N - (b - a) + 1)
    exact Prod.ext (by rw [pkG_ctP_fst]; dsimp only; omega) (by rw [pkG_ctP_snd]; dsimp only; omega)
  have vC := pkG_V_sh hN ha hb hab hodd hD₁ hD₂ hD y hy (mem_insert_self (1, b - a + 1) D₁)
  rw [hsh1] at vC
  have vT := pkG_V_ct hN hE ha hb hab hC hodd hD₁ hD₂ hD y hy (mem_insert_self (1, N - (b - a) + 1) D₂)
  rw [hct1] at vT
  have hP : Finset.prod (pkG_roots N (pkG_glue a b D₁ D₂)) (fun r => pkG_V N y (pkG_glue a b D₁ D₂) r) =
      pkG_V (N - (b - a) + 1) (fun d => y (pkG_ctP a b d)) D₂ (1, N - (b - a) + 1) *
        (pkG_V (b - a + 1) (fun d => y (pkG_shP a d)) D₁ (1, b - a + 1) *
          (Finset.prod D₁ (fun r => pkG_V (b - a + 1) (fun d => y (pkG_shP a d)) D₁ r) *
            Finset.prod D₂ (fun r => pkG_V (N - (b - a) + 1) (fun d => y (pkG_ctP a b d)) D₂ r))) := by
    have eR : pkG_roots N (pkG_glue a b D₁ D₂) =
        insert (1, N) (insert (a, b) (D₁.image (pkG_shP a) ∪ D₂.image (pkG_ctP a b))) := rfl
    have p1 : Finset.prod D₁ (fun r => pkG_V N y (pkG_glue a b D₁ D₂) (pkG_shP a r)) =
        Finset.prod D₁ (fun r => pkG_V (b - a + 1) (fun d => y (pkG_shP a d)) D₁ r) :=
      prod_congr rfl (fun r hr => pkG_V_sh hN ha hb hab hodd hD₁ hD₂ hD y hy (mem_insert_of_mem hr))
    have p2 : Finset.prod D₂ (fun r => pkG_V N y (pkG_glue a b D₁ D₂) (pkG_ctP a b r)) =
        Finset.prod D₂ (fun r => pkG_V (N - (b - a) + 1) (fun d => y (pkG_ctP a b d)) D₂ r) :=
      prod_congr rfl (fun r hr => pkG_V_ct hN hE ha hb hab hC hodd hD₁ hD₂ hD y hy (mem_insert_of_mem hr))
    have hTn' : (1, N) ∉ insert (a, b) (D₁.image (pkG_shP a) ∪ D₂.image (pkG_ctP a b)) := hTn
    rw [eR, prod_insert hTn', prod_insert hCn, prod_union hdisj, prod_image (pkG_shP_inj ha).injOn,
      prod_image (pkG_ctP_inj a b).injOn, vC, vT, p1, p2]
  have hO : Finset.prod (oddDiagonals N \ pkG_glue a b D₁ D₂) (fun d => y d) =
      Finset.prod (oddDiagonals (b - a + 1) \ D₁) (fun d => y (pkG_shP a d)) *
        Finset.prod (oddDiagonals (N - (b - a) + 1) \ D₂) (fun d => y (pkG_ctP a b d)) *
          Finset.prod (pkG_crs N a b) (fun d => y d) := by
    have hd1 : Disjoint ((oddDiagonals (b - a + 1) \ D₁).image (pkG_shP a))
        ((oddDiagonals (N - (b - a) + 1) \ D₂).image (pkG_ctP a b)) := by
      rw [disjoint_left]
      intro d h h'
      obtain ⟨d₁, hd₁, rfl⟩ := mem_image.1 h
      obtain ⟨d₂, hd₂, e⟩ := mem_image.1 h'
      have c1 := pkG_mem_odd.1 (mem_sdiff.1 hd₁).1
      have c2 := pkG_mem_odd.1 (mem_sdiff.1 hd₂).1
      exact pkG_sh_ne_ct ha hab (by omega) (by omega) (by omega) (by omega) (by omega) e.symm
    have hd2 : Disjoint ((oddDiagonals (b - a + 1) \ D₁).image (pkG_shP a) ∪
        (oddDiagonals (N - (b - a) + 1) \ D₂).image (pkG_ctP a b)) (pkG_crs N a b) := by
      rw [disjoint_left]
      intro d h h'
      have hx := (mem_filter.1 h').2
      rcases mem_union.1 h with h | h
      · obtain ⟨d₁, hd₁, rfl⟩ := mem_image.1 h
        have c1 := pkG_mem_odd.1 (mem_sdiff.1 hd₁).1
        refine (pkG_nc_io (a := a) (b := b) (p := pkG_shP a d₁) (q := (a, b)) ?_ ?_).1 hx
        · rw [pkG_shP_fst, pkG_shP_snd]; omega
        · dsimp only; omega
      · obtain ⟨d₂, hd₂, rfl⟩ := mem_image.1 h
        refine (pkG_nc_io (a := a) (b := b) (p := (a, b)) (q := pkG_ctP a b d₂) ?_ ?_).2 hx
        · dsimp only; omega
        · rw [pkG_ctP_fst, pkG_ctP_snd]
          exact ⟨pkG_ct_out (by omega) _, pkG_ct_out (by omega) _⟩
    rw [pkG_odd_sdiff hN hE ha hb hab hC hodd hD₁ hD₂, prod_union hd2, prod_union hd1,
      prod_image (pkG_shP_inj ha).injOn, prod_image (pkG_ctP_inj a b).injOn]
  rw [et, et, et, hcard, hP, hO, er, er, prod_insert (pkG_top_nmem hD₁), prod_insert (pkG_top_nmem hD₂)]
  ring

/-- **D3 (pointwise Cayley residue)**: on `X_C = 0`, the numerator factorises through the two children. -/
theorem pkG_num_res {N a b : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (ha : 1 ≤ a) (hb : b ≤ N) (hab : a + 3 ≤ b)
    (hC : ¬ (a = 1 ∧ b = N)) (hodd : (b - a) % 2 = 1) (y : ℕ × ℕ → ℚ) (hy : y (a, b) = 0) :
    pkG_num N y = -(pkG_num (b - a + 1) (fun d => y (pkG_shP a d)) *
      pkG_num (N - (b - a) + 1) (fun d => y (pkG_ctP a b d))) * Finset.prod (pkG_crs N a b) (fun d => y d) := by
  have en : ∀ n x, pkG_num n x = ∑ D ∈ pkG_dis n, pkG_term n x D := fun _ _ => rfl
  have hCo : (a, b) ∈ oddDiagonals N := by
    rw [pkG_mem_odd]
    dsimp only
    omega
  have hz : ∀ D ∈ pkG_dis N, pkG_term N y D ≠ 0 → (a, b) ∈ D := by
    intro D _ hne
    by_contra hc
    apply hne
    have e : pkG_term N y D = (-1 : ℚ) ^ D.card * Finset.prod (pkG_roots N D) (fun r => pkG_V N y D r) *
        Finset.prod (oddDiagonals N \ D) (fun d => y d) := rfl
    rw [e, prod_eq_zero (mem_sdiff.2 ⟨hCo, hc⟩) hy, mul_zero]
  have hbij : ∑ p ∈ pkG_dis (b - a + 1) ×ˢ pkG_dis (N - (b - a) + 1), pkG_term N y (pkG_glue a b p.1 p.2) =
      ∑ D ∈ (pkG_dis N).filter (fun D => (a, b) ∈ D), pkG_term N y D := by
    refine sum_nbij' (fun p => pkG_glue a b p.1 p.2) (pkG_split a b) ?_ ?_ ?_ ?_ (fun p _ => rfl)
    · intro p hp
      obtain ⟨h1, h2⟩ := mem_product.1 hp
      exact mem_filter.2 ⟨pkG_glue_dis hN hE ha hb hab hC hodd h1 h2, pkG_mem_glue.2 (Or.inl rfl)⟩
    · intro D hD
      obtain ⟨hD', hCD⟩ := mem_filter.1 hD
      exact mem_product.2 (pkG_split_dis hN hE ha hb hab hC hodd hD' hCD)
    · intro p hp
      obtain ⟨h1, h2⟩ := mem_product.1 hp
      exact pkG_split_glue hN hE ha hb hab hC hodd h1 h2
    · intro D hD
      obtain ⟨hD', hCD⟩ := mem_filter.1 hD
      exact pkG_glue_split ha hab hD' hCD
  rw [en, en, en, ← sum_filter_of_ne hz, ← hbij, sum_product, sum_mul_sum]
  have hterm : ∀ D₁ ∈ pkG_dis (b - a + 1), ∀ D₂ ∈ pkG_dis (N - (b - a) + 1),
      pkG_term N y (pkG_glue a b D₁ D₂) = -(pkG_term (b - a + 1) (fun d => y (pkG_shP a d)) D₁ *
        pkG_term (N - (b - a) + 1) (fun d => y (pkG_ctP a b d)) D₂) * Finset.prod (pkG_crs N a b) (fun d => y d) :=
    fun D₁ h1 D₂ h2 => pkG_term_glue hN hE ha hb hab hC hodd h1 h2 y hy
  rw [sum_congr rfl (fun D₁ h1 => sum_congr rfl (fun D₂ h2 => hterm D₁ h1 D₂ h2))]
  simp only [sum_mul, neg_mul, sum_neg_distrib]

/-- The Cayley sum `M_N` (App. A §0.1, rooted form; PREFORM-Germ §2.1): propagator `−1/X_P` on mixed chords. -/
noncomputable def pkG_cay (N : ℕ) (X : ℕ × ℕ → ℚ) : ℚ :=
  ∑ D ∈ pkG_dis N, Finset.prod (pkG_roots N D) (fun r => pkG_V N X D r) * Finset.prod D (fun P => -Inv.inv (X P))

/-- Polynomial twin of `mesh`. -/
noncomputable def pkG_meshP (N i j : ℕ) : MvPolynomial (ℕ × ℕ) ℚ :=
  planarP ℚ N i j + planarP ℚ N (i + 1) (j + 1) - planarP ℚ N i (j + 1) - planarP ℚ N (i + 1) j

/-- Polynomial twin of the Cayley vertex `pkG_V`. -/
noncomputable def pkG_Vp (N : ℕ) (D : Finset (ℕ × ℕ)) (r : ℕ × ℕ) : MvPolynomial (ℕ × ℕ) ℚ :=
  MvPolynomial.C (pkG_sgn (pkG_verts D r).card) *
    ∑ p ∈ (pkG_U D r ×ˢ pkG_U D r).filter (fun p => p.1 < p.2), -pkG_meshP N p.1 p.2

/-- **D1 (numerator polynomial)** `CP_N = Σ_D (−1)^|D| Π_faces V Π_{mixed ∖ D} X` (PREFORM-Germ §2.1). -/
noncomputable def pkG_CP (N : ℕ) : MvPolynomial (ℕ × ℕ) ℚ :=
  ∑ D ∈ pkG_dis N, (-1 : MvPolynomial (ℕ × ℕ) ℚ) ^ D.card * Finset.prod (pkG_roots N D) (fun r => pkG_Vp N D r) *
    Finset.prod (oddDiagonals N \ D) (fun d => MvPolynomial.X d)

theorem pkG_meshP_eval (N i j : ℕ) (x : ℕ × ℕ → ℚ) : MvPolynomial.eval x (pkG_meshP N i j) = mesh N x i j := by
  have e : pkG_meshP N i j =
      planarP ℚ N i j + planarP ℚ N (i + 1) (j + 1) - planarP ℚ N i (j + 1) - planarP ℚ N (i + 1) j := rfl
  rw [e, map_sub, map_sub, map_add, planarP_hom (MvPolynomial.eval x), planarP_hom (MvPolynomial.eval x),
    planarP_hom (MvPolynomial.eval x), planarP_hom (MvPolynomial.eval x)]
  simp only [MvPolynomial.eval_X]
  exact (pkL_mesh_eq N x i j).symm

theorem pkG_Vp_eval (N : ℕ) (D : Finset (ℕ × ℕ)) (r : ℕ × ℕ) (x : ℕ × ℕ → ℚ) :
    MvPolynomial.eval x (pkG_Vp N D r) = pkG_V N x D r := by
  have e : pkG_Vp N D r = MvPolynomial.C (pkG_sgn (pkG_verts D r).card) *
      ∑ p ∈ (pkG_U D r ×ˢ pkG_U D r).filter (fun p => p.1 < p.2), -pkG_meshP N p.1 p.2 := rfl
  rw [e, map_mul, MvPolynomial.eval_C, map_sum]
  simp only [map_neg, pkG_meshP_eval]
  rfl

/-- **D1**: `eval x CP_N = pkG_num N x` (the numerator at every point). -/
theorem pkG_CP_eval (N : ℕ) (x : ℕ × ℕ → ℚ) : MvPolynomial.eval x (pkG_CP N) = pkG_num N x := by
  have e : pkG_CP N = ∑ D ∈ pkG_dis N, (-1 : MvPolynomial (ℕ × ℕ) ℚ) ^ D.card *
      Finset.prod (pkG_roots N D) (fun r => pkG_Vp N D r) *
        Finset.prod (oddDiagonals N \ D) (fun d => MvPolynomial.X d) := rfl
  rw [e, map_sum, show pkG_num N x = ∑ D ∈ pkG_dis N, pkG_term N x D from rfl]
  refine sum_congr rfl (fun D _ => ?_)
  rw [map_mul, map_mul, map_pow, map_neg, map_one, map_prod, map_prod]
  simp only [pkG_Vp_eval, MvPolynomial.eval_X]
  rfl

/-- **D1**: off the poles, `pkG_num N x = M_N(x) · Π_{mixed} x`. -/
theorem pkG_num_cay (N : ℕ) (x : ℕ × ℕ → ℚ) (hx : ∀ d ∈ oddDiagonals N, x d ≠ 0) :
    pkG_num N x = pkG_cay N x * Finset.prod (oddDiagonals N) (fun d => x d) := by
  have en : pkG_num N x = ∑ D ∈ pkG_dis N, pkG_term N x D := rfl
  have ec : pkG_cay N x = ∑ D ∈ pkG_dis N,
      Finset.prod (pkG_roots N D) (fun r => pkG_V N x D r) * Finset.prod D (fun P => -Inv.inv (x P)) := rfl
  rw [en, ec, sum_mul]
  refine sum_congr rfl (fun D hD => ?_)
  have hsub := (pkG_mem_dis.1 hD).1
  have h1 : Finset.prod D (fun P => -Inv.inv (x P)) * Finset.prod D (fun P => x P) = (-1 : ℚ) ^ D.card := by
    rw [← prod_mul_distrib, prod_congr rfl (fun P hP => show -Inv.inv (x P) * x P = -1 by
      rw [neg_mul, inv_mul_cancel₀ (hx P (hsub hP))]), prod_const]
  have et : pkG_term N x D = (-1 : ℚ) ^ D.card * Finset.prod (pkG_roots N D) (fun r => pkG_V N x D r) *
      Finset.prod (oddDiagonals N \ D) (fun d => x d) := rfl
  rw [et, ← prod_sdiff hsub, ← h1]
  ring

/-- **D2 (degree)**: `CP_N` is homogeneous of degree `|mixed| + 1`. -/
theorem pkG_CP_hom {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) :
    (pkG_CP N).IsHomogeneous ((oddDiagonals N).card + 1) := by
  have hp : ∀ i j, (planarP ℚ N i j).IsHomogeneous 1 := by
    intro i j
    have e : planarP ℚ N i j = if npair N i j ∈ diagonals N then MvPolynomial.X (npair N i j) else 0 := rfl
    rw [e]
    split_ifs
    · exact MvPolynomial.isHomogeneous_X ℚ _
    · exact MvPolynomial.isHomogeneous_zero _ _ _
  have hm : ∀ i j, (pkG_meshP N i j).IsHomogeneous 1 := fun i j =>
    (((hp i j).add (hp (i + 1) (j + 1))).sub (hp i (j + 1))).sub (hp (i + 1) j)
  have hV : ∀ D r, (pkG_Vp N D r).IsHomogeneous 1 := by
    intro D r
    have h := (MvPolynomial.isHomogeneous_C (ℕ × ℕ) (pkG_sgn (pkG_verts D r).card)).mul
      (MvPolynomial.IsHomogeneous.sum ((pkG_U D r ×ˢ pkG_U D r).filter (fun p => p.1 < p.2))
        (fun p => -pkG_meshP N p.1 p.2) 1 (fun p _ => (hm p.1 p.2).neg))
    rw [zero_add] at h
    exact h
  have e : pkG_CP N = ∑ D ∈ pkG_dis N, (-1 : MvPolynomial (ℕ × ℕ) ℚ) ^ D.card *
      Finset.prod (pkG_roots N D) (fun r => pkG_Vp N D r) *
        Finset.prod (oddDiagonals N \ D) (fun d => MvPolynomial.X d) := rfl
  rw [e]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ (fun D hD => ?_)
  have hsub := (pkG_mem_dis.1 hD).1
  have h0 : ((-1 : MvPolynomial (ℕ × ℕ) ℚ) ^ D.card).IsHomogeneous 0 := by
    have h := (MvPolynomial.isHomogeneous_C (ℕ × ℕ) (-1 : ℚ)).pow D.card
    rw [zero_mul, map_neg, map_one] at h
    exact h
  have h1 := MvPolynomial.IsHomogeneous.prod (pkG_roots N D) (fun r => pkG_Vp N D r) (fun _ => 1)
    (fun r _ => hV D r)
  have h2 := MvPolynomial.IsHomogeneous.prod (oddDiagonals N \ D) (fun d => (MvPolynomial.X d : MvPolynomial (ℕ × ℕ) ℚ))
    (fun _ => 1) (fun d _ => MvPolynomial.isHomogeneous_X ℚ d)
  have h := (h0.mul h1).mul h2
  have hle := card_le_card hsub
  simp only [sum_const, smul_eq_mul, mul_one, zero_add] at h
  rw [pkG_card_roots hD, card_sdiff, inter_eq_left.2 hsub,
    show D.card + 1 + ((oddDiagonals N).card - D.card) = (oddDiagonals N).card + 1 by omega] at h
  exact h

/-- **Locality**: the numerator reads a point only on the diagonals. -/
theorem pkG_num_congr {n : ℕ} {y y' : ℕ × ℕ → ℚ} (h : ∀ d ∈ diagonals n, y d = y' d) :
    pkG_num n y = pkG_num n y' := by
  have hpl : ∀ i j, planar n y i j = planar n y' i j := by
    intro i j
    have e : ∀ z : ℕ × ℕ → ℚ, planar n z i j = if (min (vtx n i) (vtx n j), max (vtx n i) (vtx n j)) ∈ diagonals n then
        z (min (vtx n i) (vtx n j), max (vtx n i) (vtx n j)) else 0 := fun z => rfl
    rw [e, e]
    by_cases hd : (min (vtx n i) (vtx n j), max (vtx n i) (vtx n j)) ∈ diagonals n
    · rw [if_pos hd, if_pos hd, h _ hd]
    · rw [if_neg hd, if_neg hd]
  have hme : ∀ i j, mesh n y i j = mesh n y' i j := by
    intro i j
    rw [pkL_mesh_eq, pkL_mesh_eq, hpl, hpl, hpl, hpl]
  have hV : ∀ D r, pkG_V n y D r = pkG_V n y' D r := by
    intro D r
    have e : ∀ z : ℕ × ℕ → ℚ, pkG_V n z D r = pkG_sgn (pkG_verts D r).card *
        ∑ p ∈ (pkG_U D r ×ˢ pkG_U D r).filter (fun p => p.1 < p.2), -mesh n z p.1 p.2 := fun z => rfl
    rw [e, e]
    simp only [hme]
  have en : ∀ z, pkG_num n z = ∑ D ∈ pkG_dis n, ((-1 : ℚ) ^ D.card *
      Finset.prod (pkG_roots n D) (fun r => pkG_V n z D r) * Finset.prod (oddDiagonals n \ D) (fun d => z d)) :=
    fun z => rfl
  rw [en, en]
  refine sum_congr rfl (fun D _ => ?_)
  simp only [hV]
  have hp : Finset.prod (oddDiagonals n \ D) (fun d => y d) = Finset.prod (oddDiagonals n \ D) (fun d => y' d) :=
    prod_congr rfl (fun d hd => h d (mem_filter.1 (mem_sdiff.1 hd).1).1)
  rw [hp]

/-- **D3 (Cayley residue, contraction form)**: `zeroAt C CP_N = −(sh CP_{m₁}) · (ct CP_{m₂}) · crossProd` for every mixed
`C = (a, b)`, `m₁ = b − a + 1`, `m₂ = N − b + a + 1` (the child orders of 3c-b's `NP_residue`). -/
theorem pkG_CP_res {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {C : ℕ × ℕ} (hC : C ∈ oddDiagonals N) :
    zeroAt ℚ C (pkG_CP N) = -(MvPolynomial.rename (pkG_shP C.1) (pkG_CP (C.2 - C.1 + 1))) *
      MvPolynomial.rename (pkG_ctP C.1 C.2) (pkG_CP (N - C.2 + C.1 + 1)) * crossProd ℚ N C := by
  obtain ⟨a, b⟩ := C
  have oc := pkG_mem_odd.1 hC
  dsimp only at oc ⊢
  have ha : 1 ≤ a := by omega
  have hb : b ≤ N := by omega
  have hab : a + 3 ≤ b := by omega
  have hCC : ¬ (a = 1 ∧ b = N) := by omega
  have hodd : (b - a) % 2 = 1 := by omega
  rw [show N - b + a + 1 = N - (b - a) + 1 by omega]
  apply MvPolynomial.funext
  intro x
  have hz : ∀ P : MvPolynomial (ℕ × ℕ) ℚ, MvPolynomial.eval x (zeroAt ℚ (a, b) P) =
      MvPolynomial.eval (fun d => if d = (a, b) then 0 else x d) P := by
    intro P
    have e1 : ∀ Q, zeroAt ℚ (a, b) Q = MvPolynomial.aeval
        (fun d => if d = (a, b) then (0 : MvPolynomial (ℕ × ℕ) ℚ) else MvPolynomial.X d) Q := fun Q => rfl
    refine MvPolynomial.induction_on (motive := fun Q => MvPolynomial.eval x (zeroAt ℚ (a, b) Q) =
      MvPolynomial.eval (fun d => if d = (a, b) then 0 else x d) Q) P (fun c => ?_) (fun p q hp hq => ?_) (fun p n hp => ?_)
    · rw [e1, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.eval_C, MvPolynomial.eval_C]
    · rw [map_add, map_add, map_add, hp, hq]
    · rw [map_mul, map_mul, map_mul, hp, e1 (MvPolynomial.X n), MvPolynomial.aeval_X]
      by_cases h : n = (a, b) <;> simp [h]
  have ecr : crossProd ℚ N (a, b) = Finset.prod (pkG_crs N a b) (fun d => MvPolynomial.X d) := rfl
  rw [hz, map_mul, map_mul, map_neg, MvPolynomial.eval_rename, MvPolynomial.eval_rename, pkG_CP_eval, pkG_CP_eval,
    pkG_CP_eval, ecr, map_prod]
  simp only [MvPolynomial.eval_X]
  rw [pkG_num_res hN hE ha hb hab hCC hodd (fun d => if d = (a, b) then 0 else x d) (if_pos rfl)]
  have l1 : pkG_num (b - a + 1) (fun d => (fun d => if d = (a, b) then 0 else x d) (pkG_shP a d)) =
      pkG_num (b - a + 1) (Function.comp x (pkG_shP a)) := by
    refine pkG_num_congr (fun d hd => ?_)
    have hd' := mem_diagonals.1 hd
    have hne : pkG_shP a d ≠ (a, b) := by
      intro e
      have e1 := congrArg Prod.fst e
      have e2 := congrArg Prod.snd e
      rw [pkG_shP_fst] at e1
      rw [pkG_shP_snd] at e2
      dsimp only at e1 e2
      omega
    show (if pkG_shP a d = (a, b) then 0 else x (pkG_shP a d)) = x (pkG_shP a d)
    rw [if_neg hne]
  have l2 : pkG_num (N - (b - a) + 1) (fun d => (fun d => if d = (a, b) then 0 else x d) (pkG_ctP a b d)) =
      pkG_num (N - (b - a) + 1) (Function.comp x (pkG_ctP a b)) := by
    refine pkG_num_congr (fun d hd => ?_)
    have hd' := mem_diagonals.1 hd
    have hne : pkG_ctP a b d ≠ (a, b) := by
      intro e
      have e1 := congrArg Prod.fst e
      have e2 := congrArg Prod.snd e
      rw [pkG_ctP_fst] at e1
      rw [pkG_ctP_snd] at e2
      dsimp only at e1 e2
      have k1 := pkG_ct_cases a b d.1
      have k2 := pkG_ct_cases a b d.2
      omega
    show (if pkG_ctP a b d = (a, b) then 0 else x (pkG_ctP a b d)) = x (pkG_ctP a b d)
    rw [if_neg hne]
  have l3 : Finset.prod (pkG_crs N a b) (fun d => (fun d => if d = (a, b) then 0 else x d) d) =
      Finset.prod (pkG_crs N a b) (fun d => x d) := by
    refine prod_congr rfl (fun d hd => ?_)
    have hx := (mem_filter.1 hd).2
    have hne : d ≠ (a, b) := by
      rintro rfl
      rw [pkG_crosses_iff] at hx
      dsimp only at hx
      omega
    show (if d = (a, b) then 0 else x d) = x d
    rw [if_neg hne]
  rw [l1, l2, l3]
  ring

/-! ### pkgGerm helpers (`pkG_`), sub-wave thmI: D4 (NLSM residue in contraction form), D5–D9 (Theorem I), B10 (row
pairing) (PREFORM-Germ §3 D4–D9, B10). -/

/-- `NLSM` reads a point only on the diagonals. -/
theorem pkG_nlsm_congr {m : ℕ} {y y' : ℕ × ℕ → ℚ} (h : ∀ d ∈ diagonals m, y d = y' d) :
    NLSM m y = NLSM m y' := by
  have e : ∀ z : ℕ × ℕ → ℚ, NLSM m z = HahnSeries.coeff (Finset.sum (triangulations m)
      (fun T => Finset.prod T (fun d => Inv.inv (shifted z d)))) ((m : ℤ) - 2) := fun z => rfl
  have hs : Finset.sum (triangulations m) (fun T => Finset.prod T (fun d => Inv.inv (shifted y d))) =
      Finset.sum (triangulations m) (fun T => Finset.prod T (fun d => Inv.inv (shifted y' d))) := by
    refine sum_congr rfl (fun T hT => prod_congr rfl (fun d hd => ?_))
    have hd' : d ∈ diagonals m := (mem_triangulations.1 hT).1 hd
    have e2 : ∀ z : ℕ × ℕ → ℚ, shifted z d =
        HahnSeries.C (z d) + ((shiftSign d : ℤ) : LaurentSeries ℚ) * delta := fun z => rfl
    rw [e2, e2, h d hd']
  rw [e, e, hs]

/-- The NLSM numerator at a point off the poles. -/
theorem pkG_NP_eval {m : ℕ} (hm : 2 ≤ m) (x : ℕ × ℕ → ℚ) (hx : ∀ d ∈ oddDiagonals m, x d ≠ 0) :
    MvPolynomial.eval x (NP ℚ m) = NLSM m x * Finset.prod (oddDiagonals m) (fun d => x d) := by
  have e0 : NP ℚ m = AP ℚ m (m - 2) := rfl
  have e3 : ((m : ℤ) - 2) = ((m - 2 : ℕ) : ℤ) := by omega
  have e1 : NLSM m x = shiftCoeff m ((m - 2 : ℕ) : ℤ) x := by
    rw [← e3]
    rfl
  rw [e0, AP_eval m (m - 2) x hx, e1]

/-- Rotation keeps mixed diagonals mixed (`m` even). -/
theorem pkG_rot_odd {m : ℕ} (hm : 4 ≤ m) (hE : m % 2 = 0) {d : ℕ × ℕ} (hd : d ∈ oddDiagonals m) :
    rot m d ∈ oddDiagonals m := by
  have hdd : d ∈ diagonals m := (mem_filter.1 hd).1
  refine pkZ_i_sign_zero (rot_mem (by omega) hdd) ?_
  rw [pkRt_sign_rot hm hE hdd, pkZ_i_odd_sign hd, neg_zero]

/-- The product over mixed diagonals is rotation invariant. -/
theorem pkG_prod_rot {m : ℕ} (hm : 4 ≤ m) (hE : m % 2 = 0) (z : ℕ × ℕ → ℚ) :
    Finset.prod (oddDiagonals m) (fun d => z (rot m d)) = Finset.prod (oddDiagonals m) (fun d => z d) := by
  refine prod_nbij (fun d => rot m d) (fun d hd => pkG_rot_odd hm hE hd) ?_ ?_ (fun d _ => rfl)
  · intro p hp q hq h
    exact rot_inj (by omega) (mem_filter.1 (mem_coe.1 hp)).1 (mem_filter.1 (mem_coe.1 hq)).1 h
  · intro d hd
    have hd' := mem_coe.1 hd
    have hdd : d ∈ diagonals m := (mem_filter.1 hd').1
    obtain ⟨d0, hd0, e⟩ := rot_surj (by omega) hdd
    refine ⟨d0, mem_coe.2 (pkZ_i_sign_zero hd0 ?_), e⟩
    have h1 := pkRt_sign_rot hm hE hd0
    rw [e, pkZ_i_odd_sign hd'] at h1
    omega

/-- Rotation by `k` steps on chords. -/
def pkG_rk (m k : ℕ) (d : ℕ × ℕ) : ℕ × ℕ := npair m (d.1 + k) (d.2 + k)

theorem pkG_rk_eq (m k : ℕ) (d : ℕ × ℕ) : pkG_rk m k d =
    (min (vtx m (d.1 + k)) (vtx m (d.2 + k)), max (vtx m (d.1 + k)) (vtx m (d.2 + k))) := rfl

theorem pkG_rk_zero {m : ℕ} {d : ℕ × ℕ} (hd : d ∈ diagonals m) : pkG_rk m 0 d = d := by
  have h := mem_diagonals.1 hd
  rw [pkG_rk_eq, add_zero, add_zero, vtx_of_mem (n := m) (i := d.1) (by omega) (by omega),
    vtx_of_mem (n := m) (i := d.2) (by omega) (by omega)]
  refine Prod.ext ?_ ?_ <;> dsimp only <;> omega

theorem pkG_rk_succ {m k : ℕ} (hk : k < m) {d : ℕ × ℕ} (hd : d ∈ diagonals m) :
    pkG_rk m (k + 1) d = pkG_rk m k (rot m d) := by
  have h := mem_diagonals.1 hd
  rw [rot_eq (n := m) (d := d) (by omega) (by omega) (by omega) (by omega) (by omega)]
  have en : ∀ u, nxt m u = if u = m then 1 else u + 1 := fun u => rfl
  rw [en, en, pkG_rk_eq, pkG_rk_eq]
  by_cases h2 : d.2 = m
  · rw [if_neg (show ¬ d.1 = m by omega), if_pos h2]
    dsimp only
    rw [min_eq_right (show 1 ≤ d.1 + 1 by omega), max_eq_left (show 1 ≤ d.1 + 1 by omega),
      pkI_vtx (N := m) (x := d.1 + (k + 1)) (by omega) (by omega),
      pkI_vtx (N := m) (x := d.2 + (k + 1)) (by omega) (by omega),
      pkI_vtx (N := m) (x := 1 + k) (by omega) (by omega),
      pkI_vtx (N := m) (x := d.1 + 1 + k) (by omega) (by omega)]
    refine Prod.ext ?_ ?_ <;> dsimp only <;> split_ifs <;> omega
  · rw [if_neg (show ¬ d.1 = m by omega), if_neg h2]
    dsimp only
    rw [min_eq_left (show d.1 + 1 ≤ d.2 + 1 by omega), max_eq_right (show d.1 + 1 ≤ d.2 + 1 by omega),
      pkI_vtx (N := m) (x := d.1 + (k + 1)) (by omega) (by omega),
      pkI_vtx (N := m) (x := d.2 + (k + 1)) (by omega) (by omega),
      pkI_vtx (N := m) (x := d.1 + 1 + k) (by omega) (by omega),
      pkI_vtx (N := m) (x := d.2 + 1 + k) (by omega) (by omega)]
    refine Prod.ext ?_ ?_ <;> dsimp only <;> split_ifs <;> omega

theorem pkG_rk_diag {m k : ℕ} (hk : k ≤ m) {d : ℕ × ℕ} (hd : d ∈ diagonals m) : pkG_rk m k d ∈ diagonals m := by
  have h := mem_diagonals.1 hd
  refine mem_diagonals.2 ?_
  rw [pkG_rk_eq, pkI_vtx (N := m) (x := d.1 + k) (by omega) (by omega),
    pkI_vtx (N := m) (x := d.2 + k) (by omega) (by omega)]
  dsimp only
  split_ifs <;> omega

theorem pkG_rk_odd {m k : ℕ} (hE : m % 2 = 0) (hk : k ≤ m) {d : ℕ × ℕ} (hd : d ∈ oddDiagonals m) :
    pkG_rk m k d ∈ oddDiagonals m := by
  have h := pkG_mem_odd.1 hd
  refine pkG_mem_odd.2 ?_
  rw [pkG_rk_eq, pkI_vtx (N := m) (x := d.1 + k) (by omega) (by omega),
    pkI_vtx (N := m) (x := d.2 + k) (by omega) (by omega)]
  dsimp only
  split_ifs <;> omega

/-- `NLSM` and the mixed product are invariant under rotation by `k ≤ m` steps. -/
theorem pkG_nlsm_rk {m : ℕ} (hm : 4 ≤ m) (hE : m % 2 = 0) (k : ℕ) : k ≤ m → ∀ z : ℕ × ℕ → ℚ,
    NLSM m (fun d => z (pkG_rk m k d)) = NLSM m z ∧
    Finset.prod (oddDiagonals m) (fun d => z (pkG_rk m k d)) = Finset.prod (oddDiagonals m) (fun d => z d) := by
  induction k with
  | zero =>
    intro _ z
    refine ⟨pkG_nlsm_congr (fun d hd => by rw [pkG_rk_zero hd]),
      prod_congr rfl (fun d hd => by rw [pkG_rk_zero (mem_filter.1 hd).1])⟩
  | succ k ih =>
    intro hk z
    obtain ⟨i1, i2⟩ := ih (by omega) z
    have c1 : NLSM m (fun d => z (pkG_rk m (k + 1) d)) =
        NLSM m (Function.comp (fun d => z (pkG_rk m k d)) (rot m)) :=
      pkG_nlsm_congr (fun d hd => by rw [pkG_rk_succ (by omega) hd]; rfl)
    have c2 : Finset.prod (oddDiagonals m) (fun d => z (pkG_rk m (k + 1) d)) =
        Finset.prod (oddDiagonals m) (fun d => (fun e => z (pkG_rk m k e)) (rot m d)) :=
      prod_congr rfl (fun d hd => by rw [pkG_rk_succ (by omega) (mem_filter.1 hd).1])
    refine ⟨?_, ?_⟩
    · rw [c1, NLSM_rot hm hE, i1]
    · rw [c2, pkG_prod_rot hm hE (fun e => z (pkG_rk m k e)), i2]

/-- The outside child: 3c-b's `relab N b` is the contraction after rotating the child by `a` steps (PREFORM K10). -/
theorem pkG_relab_ct {N a b : ℕ} (ha : 1 ≤ a) (hab : a + 3 ≤ b) (hb : b ≤ N) {d : ℕ × ℕ}
    (hd : d ∈ diagonals (N - (b - a) + 1)) : relab N b d = pkG_ctP a b (pkG_rk (N - (b - a) + 1) a d) := by
  have h := mem_diagonals.1 hd
  have e1 : relab N b d = (min (vtx N (d.1 + b - 1)) (vtx N (d.2 + b - 1)),
      max (vtx N (d.1 + b - 1)) (vtx N (d.2 + b - 1))) := rfl
  rw [e1, pkG_rk_eq, pkI_vtx (N := N) (x := d.1 + b - 1) (by omega) (by omega),
    pkI_vtx (N := N) (x := d.2 + b - 1) (by omega) (by omega),
    pkI_vtx (N := N - (b - a) + 1) (x := d.1 + a) (by omega) (by omega),
    pkI_vtx (N := N - (b - a) + 1) (x := d.2 + a) (by omega) (by omega), pkG_ctP_eq]
  dsimp only
  rw [pkG_ct_eq, pkG_ct_eq]
  refine Prod.ext ?_ ?_ <;> dsimp only <;> split_ifs <;> omega

/-- The inside child: 3c-b's `relab N a` is the shift. -/
theorem pkG_relab_sh {N a b : ℕ} (ha : 1 ≤ a) (hb : b ≤ N) {d : ℕ × ℕ} (hd : d ∈ diagonals (b - a + 1)) :
    relab N a d = pkG_shP a d := by
  have h := mem_diagonals.1 hd
  have e1 : relab N a d = (min (vtx N (d.1 + a - 1)) (vtx N (d.2 + a - 1)),
      max (vtx N (d.1 + a - 1)) (vtx N (d.2 + a - 1))) := rfl
  rw [e1, vtx_of_mem (n := N) (i := d.1 + a - 1) (by omega) (by omega),
    vtx_of_mem (n := N) (i := d.2 + a - 1) (by omega) (by omega), pkG_shP_eq, pkG_sh_eq, pkG_sh_eq]
  refine Prod.ext ?_ ?_ <;> dsimp only <;> omega

theorem pkG_shP_odd {N a b : ℕ} (ha : 1 ≤ a) (hb : b ≤ N) (hCC : ¬ (a = 1 ∧ b = N)) {d : ℕ × ℕ}
    (hd : d ∈ oddDiagonals (b - a + 1)) : pkG_shP a d ∈ oddDiagonals N := by
  have h := pkG_mem_odd.1 hd
  refine pkG_mem_odd.2 ?_
  rw [pkG_shP_fst, pkG_shP_snd]
  omega

theorem pkG_ctP_odd {N a b : ℕ} (ha : 1 ≤ a) (hab : a + 3 ≤ b) (hb : b ≤ N) (hodd : (b - a) % 2 = 1)
    {d : ℕ × ℕ} (hd : d ∈ oddDiagonals (N - (b - a) + 1)) : pkG_ctP a b d ∈ oddDiagonals N := by
  have h := pkG_mem_odd.1 hd
  refine pkG_mem_odd.2 ?_
  rw [pkG_ctP_fst, pkG_ctP_snd]
  have k1 := pkG_ct_cases a b d.1
  have k2 := pkG_ct_cases a b d.2
  omega

/-- **D4 (NLSM residue, contraction form)**: 3c-b's `NP_residue` with the outside child relabelled by the contraction. -/
theorem pkG_NP_res {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {C : ℕ × ℕ} (hC : C ∈ oddDiagonals N) :
    zeroAt ℚ C (NP ℚ N) = MvPolynomial.rename (pkG_shP C.1) (NP ℚ (C.2 - C.1 + 1)) *
      MvPolynomial.rename (pkG_ctP C.1 C.2) (NP ℚ (N - C.2 + C.1 + 1)) * crossProd ℚ N C := by
  have hres := NP_residue (R := ℚ) hN hE hC
  obtain ⟨a, b⟩ := C
  have oc := pkG_mem_odd.1 hC
  have hc := pkZ_child hE hC
  dsimp only at oc hc hres ⊢
  have ha : 1 ≤ a := by omega
  have hb : b ≤ N := by omega
  have hab : a + 3 ≤ b := by omega
  have hCC : ¬ (a = 1 ∧ b = N) := by omega
  have hodd : (b - a) % 2 = 1 := by omega
  have em : N - b + a + 1 = N - (b - a) + 1 := by omega
  rw [hres, em]
  have hm2 : 4 ≤ N - (b - a) + 1 := by omega
  have hE2 : (N - (b - a) + 1) % 2 = 0 := by omega
  have hm1 : 4 ≤ b - a + 1 := by omega
  refine pkM_eq_of_eval (N := N) _ _ (fun x hx => ?_)
  simp only [map_mul, MvPolynomial.eval_rename]
  have i1 : MvPolynomial.eval (Function.comp x (relab N a)) (NP ℚ (b - a + 1)) =
      MvPolynomial.eval (Function.comp x (pkG_shP a)) (NP ℚ (b - a + 1)) := by
    have hy : ∀ d ∈ oddDiagonals (b - a + 1), Function.comp x (pkG_shP a) d ≠ 0 :=
      fun d hd => hx _ (pkG_shP_odd ha hb hCC hd)
    have hy' : ∀ d ∈ oddDiagonals (b - a + 1), Function.comp x (relab N a) d ≠ 0 := by
      intro d hd
      show x (relab N a d) ≠ 0
      rw [pkG_relab_sh ha hb (mem_filter.1 hd).1]
      exact hy d hd
    rw [pkG_NP_eval (by omega) _ hy, pkG_NP_eval (by omega) _ hy']
    have hq : ∀ d ∈ diagonals (b - a + 1), Function.comp x (relab N a) d = Function.comp x (pkG_shP a) d := by
      intro d hd
      show x (relab N a d) = x (pkG_shP a d)
      rw [pkG_relab_sh ha hb hd]
    have hp : Finset.prod (oddDiagonals (b - a + 1)) (fun d => Function.comp x (relab N a) d) =
        Finset.prod (oddDiagonals (b - a + 1)) (fun d => Function.comp x (pkG_shP a) d) :=
      prod_congr rfl (fun d hd => hq d (mem_filter.1 hd).1)
    rw [pkG_nlsm_congr hq, hp]
  have i2 : MvPolynomial.eval (Function.comp x (relab N b)) (NP ℚ (N - (b - a) + 1)) =
      MvPolynomial.eval (Function.comp x (pkG_ctP a b)) (NP ℚ (N - (b - a) + 1)) := by
    have hy : ∀ d ∈ oddDiagonals (N - (b - a) + 1), Function.comp x (pkG_ctP a b) d ≠ 0 :=
      fun d hd => hx _ (pkG_ctP_odd ha hab hb hodd hd)
    have hq : ∀ d ∈ diagonals (N - (b - a) + 1), Function.comp x (relab N b) d =
        (fun e => Function.comp x (pkG_ctP a b) (pkG_rk (N - (b - a) + 1) a e)) d := by
      intro d hd
      show x (relab N b d) = x (pkG_ctP a b (pkG_rk (N - (b - a) + 1) a d))
      rw [pkG_relab_ct ha hab hb hd]
    have hy' : ∀ d ∈ oddDiagonals (N - (b - a) + 1), Function.comp x (relab N b) d ≠ 0 := by
      intro d hd
      rw [hq d (mem_filter.1 hd).1]
      exact hy _ (pkG_rk_odd hE2 (by omega) hd)
    obtain ⟨r1, r2⟩ := pkG_nlsm_rk hm2 hE2 a (by omega) (Function.comp x (pkG_ctP a b))
    have hp : Finset.prod (oddDiagonals (N - (b - a) + 1)) (fun d => Function.comp x (relab N b) d) =
        Finset.prod (oddDiagonals (N - (b - a) + 1))
          (fun d => (fun e => Function.comp x (pkG_ctP a b) (pkG_rk (N - (b - a) + 1) a e)) d) :=
      prod_congr rfl (fun d hd => hq d (mem_filter.1 hd).1)
    rw [pkG_NP_eval (by omega) _ hy, pkG_NP_eval (by omega) _ hy', pkG_nlsm_congr hq, hp, r1, r2]
  rw [i1, i2]

/-- **D7 input** of the Theorem I induction, as a statement: the quotient `L = (NP + CP)/oddDen` vanishes on the generic
rows `2 ≤ a ≤ N − 2` (discharged below for `N ≥ 8`). -/
def pkG_RowZ (N : ℕ) : Prop :=
  ∀ a : ℕ, 2 ≤ a → a + 2 ≤ N → ∀ L : MvPolynomial (ℕ × ℕ) ℚ, L.totalDegree ≤ 1 →
    NP ℚ N + pkG_CP N = oddDen ℚ N * L → ∀ x : ℕ × ℕ → ℚ, OnRect N 1 a x → MvPolynomial.eval x L = 0

/-- **D6(c)**: the quotient has total degree ≤ 1 (`NP` and `CP` are homogeneous of degree `|mixed| + 1`). -/
theorem pkG_Ldeg {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (L : MvPolynomial (ℕ × ℕ) ℚ)
    (hL : NP ℚ N + pkG_CP N = oddDen ℚ N * L) : L.totalDegree ≤ 1 := by
  by_cases h0 : L = 0
  · rw [h0, MvPolynomial.totalDegree_zero]
    omega
  have hden : oddDen ℚ N ≠ 0 := prod_ne_zero_iff.2 fun d _ => MvPolynomial.X_ne_zero d
  have hdenH : (oddDen ℚ N).IsHomogeneous (oddDiagonals N).card := by
    have h := MvPolynomial.IsHomogeneous.prod (oddDiagonals N)
      (fun d => (MvPolynomial.X d : MvPolynomial (ℕ × ℕ) ℚ)) (fun _ => 1)
      (fun d _ => MvPolynomial.isHomogeneous_X ℚ d)
    rw [sum_const, smul_eq_mul, mul_one] at h
    exact h
  have hA := AP_isHomogeneous (R := ℚ) hN (N - 2) (by omega)
  rw [show (oddDiagonals N).card + (N - 2) - (N - 3) = (oddDiagonals N).card + 1 by omega] at hA
  have hD := hA.add (pkG_CP_hom hN hE)
  have e : NP ℚ N = AP ℚ N (N - 2) := rfl
  rw [← e, hL] at hD
  have h1 := hD.totalDegree (mul_ne_zero hden h0)
  rw [MvPolynomial.totalDegree_mul_of_isDomain hden h0, hdenH.totalDegree hden] at h1
  omega

/-- **D6(a)**: under the induction hypothesis, `NP + CP` vanishes at every mixed pole. -/
theorem pkG_zres {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0)
    (ih : ∀ m : ℕ, m < N → 4 ≤ m → m % 2 = 0 → NP ℚ m = -pkG_CP m) {C : ℕ × ℕ} (hC : C ∈ oddDiagonals N) :
    zeroAt ℚ C (NP ℚ N + pkG_CP N) = 0 := by
  obtain ⟨c1, c2, c3, c4, c5, c6, -⟩ := pkZ_child hE hC
  rw [map_add, pkG_NP_res hN hE hC, pkG_CP_res hN hE hC, ih _ c3 c1 c2, ih _ c6 c4 c5]
  simp only [map_neg]
  ring

/-- **D5 (N = 4)**: `NP₄ = −CP₄`. -/
theorem pkG_thmI_four : NP ℚ 4 = -pkG_CP 4 := by
  refine pkM_eq_of_eval (N := 4) _ _ (fun x hx => ?_)
  have hd : pkG_dis 4 = {∅} := by decide
  have ho : oddDiagonals 4 = ∅ := by decide
  have hr : pkG_roots 4 ∅ = {(1, 4)} := by decide
  have he : (diagonals 4).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0) = {(2, 4)} := by decide
  have en : pkG_num 4 x = ∑ D ∈ pkG_dis 4, pkG_term 4 x D := rfl
  have et : pkG_term 4 x ∅ = (-1 : ℚ) ^ (∅ : Finset (ℕ × ℕ)).card *
      Finset.prod (pkG_roots 4 ∅) (fun r => pkG_V 4 x ∅ r) * Finset.prod (oddDiagonals 4 \ ∅) (fun d => x d) := rfl
  have eE : pkG_E 4 x = ∑ t ∈ (diagonals 4).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0), mesh 4 x t.1 t.2 := rfl
  have p1 : planar 4 x 2 4 = x (2, 4) := by
    unfold planar
    rw [if_pos (by decide)]
    rfl
  have p2 : planar 4 x (2 + 1) (4 + 1) = x (1, 3) := by
    unfold planar
    rw [if_pos (by decide)]
    rfl
  have p3 : planar 4 x 2 (4 + 1) = 0 := by
    unfold planar
    rw [if_neg (by decide)]
  have p4 : planar 4 x (2 + 1) 4 = 0 := by
    unfold planar
    rw [if_neg (by decide)]
  rw [map_neg, pkG_CP_eval, pkG_NP_eval (by norm_num) x hx, pkM_NLSM4, ho, prod_empty, en, hd, sum_singleton, et, hr,
    prod_singleton, pkG_V_empty (by norm_num) (by norm_num), ho, eE, he, sum_singleton, pkL_mesh_eq, p1, p2, p3, p4]
  norm_num
  ring

/-- **Theorem I (numerator form)**, assuming the row input for `N ≥ 8` and the base case `N = 6`. -/
theorem pkG_thmI_of (hrow : ∀ N : ℕ, 8 ≤ N → N % 2 = 0 → pkG_RowZ N) (h6 : NP ℚ 6 = -pkG_CP 6) :
    ∀ N : ℕ, 4 ≤ N → N % 2 = 0 → NP ℚ N = -pkG_CP N := by
  intro N
  refine Nat.strong_induction_on N ?_
  intro N ih hN hE
  by_cases h4 : N = 4
  · subst h4
    exact pkG_thmI_four
  by_cases h6' : N = 6
  · subst h6'
    exact h6
  have hN8 : 8 ≤ N := by omega
  obtain ⟨L, hL⟩ := prod_X_dvd_of_zeroAt (oddDiagonals N) (NP ℚ N + pkG_CP N)
    (fun C hC => pkG_zres (by omega) hE (fun m hm h4m hEm => ih m hm h4m hEm) hC)
  have hL' : NP ℚ N + pkG_CP N = oddDen ℚ N * L := hL
  have hdeg := pkG_Ldeg (by omega) hE L hL'
  have hL0 : L = 0 := three_rows (by omega) hE (a := 2) (by omega) L hdeg (fun x hx => by
    rcases hx with h | h | h
    · exact hrow N hN8 hE 2 le_rfl (by omega) L hdeg hL' x h
    · exact hrow N hN8 hE 4 (by omega) (by omega) L hdeg hL' x h
    · exact hrow N hN8 hE 6 (by omega) (by omega) L hdeg hL' x h)
  rw [hL0, mul_zero] at hL'
  exact eq_neg_of_add_eq_zero_left hL'

/-- **D9 (pointwise Theorem I)** from the numerator form. -/
theorem pkG_thmI_pt {N : ℕ} (hN : 4 ≤ N) (hP : NP ℚ N = -pkG_CP N) (x : ℕ × ℕ → ℚ)
    (hx : ∀ d ∈ oddDiagonals N, x d ≠ 0) : NLSM N x = -pkG_cay N x := by
  have h := congrArg (MvPolynomial.eval x) hP
  rw [pkG_NP_eval (by omega) x hx, map_neg, pkG_CP_eval, pkG_num_cay N x hx] at h
  have hp : Finset.prod (oddDiagonals N) (fun d => x d) ≠ 0 := prod_ne_zero_iff.2 hx
  have h2 : (NLSM N x + pkG_cay N x) * Finset.prod (oddDiagonals N) (fun d => x d) = 0 := by
    rw [add_mul, h]
    ring
  rw [eq_neg_iff_add_eq_zero]
  exact (mul_eq_zero.1 h2).resolve_right hp

/-- The line `s ↦ x₀ + s·y`, variable by variable, as polynomials in `s`. -/
noncomputable def pkG_lg (x0 y : ℕ × ℕ → ℚ) : ℕ × ℕ → Polynomial ℚ :=
  fun d => Polynomial.C (x0 d) + Polynomial.C (y d) * Polynomial.X

theorem pkG_lg_eval (x0 y : ℕ × ℕ → ℚ) (s : ℚ) (P : MvPolynomial (ℕ × ℕ) ℚ) :
    Polynomial.eval s (MvPolynomial.aeval (pkG_lg x0 y) P) = MvPolynomial.eval (fun d => x0 d + s * y d) P := by
  refine MvPolynomial.induction_on (motive := fun Q => Polynomial.eval s (MvPolynomial.aeval (pkG_lg x0 y) Q) =
    MvPolynomial.eval (fun d => x0 d + s * y d) Q) P (fun c => ?_) (fun p q hp hq => ?_) (fun p n hp => ?_)
  · rw [MvPolynomial.aeval_C, MvPolynomial.eval_C, Polynomial.algebraMap_eq, Polynomial.eval_C]
  · rw [map_add, map_add, Polynomial.eval_add, hp, hq]
  · rw [map_mul, map_mul, Polynomial.eval_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_X]
    have e : pkG_lg x0 y n = Polynomial.C (x0 n) + Polynomial.C (y n) * Polynomial.X := rfl
    rw [e, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring

theorem pkG_lg_dvd {x0 y : ℕ × ℕ → ℚ} {P : MvPolynomial (ℕ × ℕ) ℚ} (h : MvPolynomial.eval x0 P = 0) :
    Polynomial.X ∣ MvPolynomial.aeval (pkG_lg x0 y) P := by
  rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero, pkG_lg_eval]
  simp only [zero_mul, add_zero]
  exact h

/-- A polynomial of total degree ≤ 1 is affine along lines. -/
theorem pkG_aff (L : MvPolynomial (ℕ × ℕ) ℚ) (hL : L.totalDegree ≤ 1) (x y : ℕ × ℕ → ℚ) (s : ℚ) :
    MvPolynomial.eval (fun d => x d + s * y d) L =
      MvPolynomial.eval x L + s * (MvPolynomial.eval (fun d => x d + y d) L - MvPolynomial.eval x L) := by
  simp only [MvPolynomial.eval_eq]
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rcases pkRw_mono m ((MvPolynomial.le_totalDegree hm).trans hL) with h | ⟨v, h⟩
  · subst h
    simp
  · subst h
    simp
    ring

/-- Polynomial core of the germ step (PREFORM-Germ D7(c)). -/
theorem pkG_germ_core {c α β : ℚ} {D Q : Polynomial ℚ} (hc : c ≠ 0) (hD : Polynomial.eval 0 D ≠ 0)
    (h : Polynomial.C c * Polynomial.X * D * (Polynomial.C α + Polynomial.C β * Polynomial.X) =
      Polynomial.X ^ 3 * Q) : α = 0 ∧ β = 0 := by
  have hX : (Polynomial.X : Polynomial ℚ) ≠ 0 := Polynomial.X_ne_zero
  have hnd : ¬ Polynomial.X ∣ Polynomial.C c * D := by
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_mul, Polynomial.eval_C]
    exact mul_ne_zero hc hD
  have h1 : Polynomial.C c * D * (Polynomial.C α + Polynomial.C β * Polynomial.X) =
      Polynomial.X * (Polynomial.X * Q) := by
    refine mul_left_cancel₀ hX ?_
    rw [show Polynomial.X * (Polynomial.X * (Polynomial.X * Q)) = Polynomial.X ^ 3 * Q by ring, ← h]
    ring
  have d1 : Polynomial.X ∣ Polynomial.C α + Polynomial.C β * Polynomial.X := by
    rcases Polynomial.prime_X.dvd_or_dvd (show Polynomial.X ∣ Polynomial.C c * D *
        (Polynomial.C α + Polynomial.C β * Polynomial.X) from ⟨Polynomial.X * Q, h1⟩) with h2 | h2
    · exact absurd h2 hnd
    · exact h2
  obtain ⟨B, hB⟩ := d1
  have h3 : Polynomial.C c * D * B = Polynomial.X * Q := by
    refine mul_left_cancel₀ hX ?_
    rw [show Polynomial.X * (Polynomial.C c * D * B) = Polynomial.C c * D * (Polynomial.X * B) by ring,
      ← hB, h1]
  have d2 : Polynomial.X ∣ B := by
    rcases Polynomial.prime_X.dvd_or_dvd (show Polynomial.X ∣ Polynomial.C c * D * B from ⟨Q, h3⟩) with h2 | h2
    · exact absurd h2 hnd
    · exact h2
  obtain ⟨B', hB'⟩ := d2
  have hA : Polynomial.C α + Polynomial.C β * Polynomial.X = Polynomial.X ^ 2 * B' := by
    rw [hB, hB']
    ring
  have hdvd : Polynomial.X ^ 2 ∣ Polynomial.C α + Polynomial.C β * Polynomial.X := ⟨B', hA⟩
  rw [Polynomial.X_pow_dvd_iff] at hdvd
  have c0 := hdvd 0 (by norm_num)
  have c1 := hdvd 1 (by norm_num)
  simp at c0 c1
  exact ⟨c0, c1⟩

/-- The polynomial summand of `pkG_CP`. -/
noncomputable def pkG_tP (N : ℕ) (D : Finset (ℕ × ℕ)) : MvPolynomial (ℕ × ℕ) ℚ :=
  (-1 : MvPolynomial (ℕ × ℕ) ℚ) ^ D.card * Finset.prod (pkG_roots N D) (fun r => pkG_Vp N D r) *
    Finset.prod (oddDiagonals N \ D) (fun d => MvPolynomial.X d)

theorem pkG_CP_tP (N : ℕ) : pkG_CP N = ∑ D ∈ pkG_dis N, pkG_tP N D := rfl

theorem pkG_tP_eval (N : ℕ) (D : Finset (ℕ × ℕ)) (x : ℕ × ℕ → ℚ) :
    MvPolynomial.eval x (pkG_tP N D) = pkG_term N x D := by
  have e : pkG_tP N D = (-1 : MvPolynomial (ℕ × ℕ) ℚ) ^ D.card *
      Finset.prod (pkG_roots N D) (fun r => pkG_Vp N D r) *
        Finset.prod (oddDiagonals N \ D) (fun d => MvPolynomial.X d) := rfl
  rw [e, map_mul, map_mul, map_pow, map_neg, map_one, map_prod, map_prod]
  simp only [pkG_Vp_eval, MvPolynomial.eval_X]
  rfl

/-- **B10 (row pairing)** at row `a`, as a statement (proved below as `pkG_rowpair`). -/
def pkG_Pair (N a : ℕ) : Prop := ∀ z : ℕ × ℕ → ℚ, OnRect N 1 a z → ∀ D ∈ pkG_dis N, (a - 1, a + 2) ∈ D →
    pkG_term N z D + pkG_term N z (D.erase (a - 1, a + 2)) = 0

/-- The base point of the row germ (D7(a)), as a statement (proved below as `pkG_base`). -/
def pkG_Base (N a : ℕ) : Prop := ∃ x0 : ℕ × ℕ → ℚ, OnRect N 1 a x0 ∧ (∀ t ∈ pkG_same N, mesh N x0 t.1 t.2 = 0) ∧
    x0 (a - 1, a + 2) = 0 ∧ ∀ P ∈ oddDiagonals N, P ≠ (a - 1, a + 2) → x0 P ≠ 0

theorem pkG_onRect_lin {N a : ℕ} {x y : ℕ × ℕ → ℚ} (hx : OnRect N 1 a x) (hy : OnRect N 1 a y) (s : ℚ) :
    OnRect N 1 a (fun d => x d + s * y d) := by
  intro i hi j hj
  rw [pkG_mesh_lin, hx i hi j hj, hy i hi j hj]
  ring

/-- `X³` divides the line image of the Cayley numerator (PREFORM-Germ D7(b)–(c)): the pairs cancel on the row, and every
remaining dissection has two leaf faces vanishing at `x₀` and the factor `X_{P₀}`. -/
theorem pkG_dvd3 {N a : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) (ha : 2 ≤ a) (haN : a + 2 ≤ N) (hpair : pkG_Pair N a)
    {x0 y : ℕ × ℕ → ℚ} (hx0R : OnRect N 1 a x0) (hx0s : ∀ t ∈ pkG_same N, mesh N x0 t.1 t.2 = 0)
    (hx00 : x0 (a - 1, a + 2) = 0) (hyR : OnRect N 1 a y) :
    Polynomial.X ^ 3 ∣ MvPolynomial.aeval (pkG_lg x0 y) (pkG_CP N) := by
  have hP0o : (a - 1, a + 2) ∈ oddDiagonals N := pkG_mem_odd.2 (by dsimp only; omega)
  rw [pkG_CP_tP, map_sum, ← sum_filter_add_sum_filter_not (pkG_dis N) (fun D => (a - 1, a + 2) ∈ D),
    ← sum_filter_add_sum_filter_not ((pkG_dis N).filter (fun D => (a - 1, a + 2) ∉ D))
      (fun D => insert (a - 1, a + 2) D ∈ pkG_dis N)]
  have hbij : ∑ D ∈ ((pkG_dis N).filter (fun D => (a - 1, a + 2) ∉ D)).filter
        (fun D => insert (a - 1, a + 2) D ∈ pkG_dis N), MvPolynomial.aeval (pkG_lg x0 y) (pkG_tP N D) =
      ∑ D ∈ (pkG_dis N).filter (fun D => (a - 1, a + 2) ∈ D),
        MvPolynomial.aeval (pkG_lg x0 y) (pkG_tP N (D.erase (a - 1, a + 2))) := by
    refine (sum_nbij' (fun D => D.erase (a - 1, a + 2)) (fun D => insert (a - 1, a + 2) D) ?_ ?_ ?_ ?_ ?_).symm
    · intro D hD
      have hD' := mem_filter.1 hD
      have hdis := pkG_mem_dis.1 hD'.1
      refine mem_filter.2 ⟨mem_filter.2 ⟨pkG_mem_dis.2 ⟨(erase_subset _ _).trans hdis.1,
        fun p hp q hq => hdis.2 p (mem_of_mem_erase hp) q (mem_of_mem_erase hq)⟩, notMem_erase _ _⟩, ?_⟩
      rw [insert_erase hD'.2]
      exact hD'.1
    · intro D hD
      have hD' := mem_filter.1 hD
      exact mem_filter.2 ⟨hD'.2, mem_insert_self _ _⟩
    · intro D hD
      exact insert_erase (mem_filter.1 hD).2
    · intro D hD
      exact erase_insert (mem_filter.1 (mem_filter.1 hD).1).2
    · intro D _
      rfl
  rw [hbij, ← add_assoc, ← sum_add_distrib]
  have hz : ∀ D ∈ (pkG_dis N).filter (fun D => (a - 1, a + 2) ∈ D),
      MvPolynomial.aeval (pkG_lg x0 y) (pkG_tP N D) +
        MvPolynomial.aeval (pkG_lg x0 y) (pkG_tP N (D.erase (a - 1, a + 2))) = 0 := by
    intro D hD
    have hD' := mem_filter.1 hD
    apply Polynomial.funext
    intro s
    rw [Polynomial.eval_add, pkG_lg_eval, pkG_lg_eval, pkG_tP_eval, pkG_tP_eval, Polynomial.eval_zero]
    exact hpair _ (pkG_onRect_lin hx0R hyR s) D hD'.1 hD'.2
  rw [sum_eq_zero hz, zero_add]
  refine dvd_sum (fun D hD => ?_)
  have hD1 := mem_filter.1 hD
  have hD2 := mem_filter.1 hD1.1
  have hdis := hD2.1
  have hne : D.Nonempty := by
    rw [nonempty_iff_ne_empty]
    rintro rfl
    apply hD1.2
    refine pkG_mem_dis.2 ⟨?_, ?_⟩
    · intro p hp
      simp only [mem_insert, Finset.notMem_empty, or_false] at hp
      rw [hp]
      exact hP0o
    · intro p hp q hq
      simp only [mem_insert, Finset.notMem_empty, or_false] at hp hq
      rw [hp, hq, pkG_crosses_iff]
      omega
  have hleaf := pkG_G3_leaf (by omega) hE hdis hne
  obtain ⟨r1, hr1, r2, hr2, h12⟩ := one_lt_card.1 (show 1 < _ from hleaf)
  have hr1' := mem_filter.1 hr1
  have hr2' := mem_filter.1 hr2
  have hV : ∀ r ∈ pkG_roots N D, pkG_deg (pkG_ch D) D r ≤ 1 →
      Polynomial.X ∣ MvPolynomial.aeval (pkG_lg x0 y) (pkG_Vp N D r) := by
    intro r hr hdeg
    refine pkG_lg_dvd ?_
    rw [pkG_Vp_eval]
    exact pkG_V_leaf (by omega) hE hdis hr hdeg x0 (pkG_A4_all (by omega) x0) (pkG_A5_all (by omega) x0) hx0s
  obtain ⟨u1, hu1⟩ := hV r1 hr1'.1 hr1'.2
  obtain ⟨u2, hu2⟩ := hV r2 hr2'.1 hr2'.2
  have hP0D : (a - 1, a + 2) ∈ oddDiagonals N \ D := mem_sdiff.2 ⟨hP0o, hD2.2⟩
  obtain ⟨u3, hu3⟩ : Polynomial.X ∣ MvPolynomial.aeval (pkG_lg x0 y) (MvPolynomial.X (a - 1, a + 2)) :=
    pkG_lg_dvd (by rw [MvPolynomial.eval_X]; exact hx00)
  have e : pkG_tP N D = (-1 : MvPolynomial (ℕ × ℕ) ℚ) ^ D.card *
      Finset.prod (pkG_roots N D) (fun r => pkG_Vp N D r) *
        Finset.prod (oddDiagonals N \ D) (fun d => MvPolynomial.X d) := rfl
  have hr2e : r2 ∈ (pkG_roots N D).erase r1 := mem_erase.2 ⟨fun h => h12 h.symm, hr2'.1⟩
  rw [e, ← mul_prod_erase _ _ hr1'.1, ← mul_prod_erase _ _ hr2e, ← mul_prod_erase _ _ hP0D]
  simp only [map_mul, map_pow, map_neg, map_one]
  rw [hu1, hu2, hu3]
  have k : ∀ p q r s1 s2 s3 : Polynomial ℚ, Polynomial.X ^ 3 ∣
      p * (Polynomial.X * s1 * (Polynomial.X * s2 * q)) * (Polynomial.X * s3 * r) :=
    fun p q r s1 s2 s3 => ⟨p * s1 * s2 * q * s3 * r, by ring⟩
  exact k _ _ _ _ _ _

/-- **D7 (row zero of the quotient)** from the pairing (B10) and a base point: the germ of `L` along `x₀ + s·y` vanishes
to order 2 (PREFORM-Germ D7; the pole-free case by 3c-b's `line_bridge`). -/
theorem pkG_rowZ_of {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {a : ℕ} (ha : 2 ≤ a) (haN : a + 2 ≤ N)
    (hpair : pkG_Pair N a) (hbase : pkG_Base N a) (L : MvPolynomial (ℕ × ℕ) ℚ) (hdeg : L.totalDegree ≤ 1)
    (hL : NP ℚ N + pkG_CP N = oddDen ℚ N * L) : ∀ x : ℕ × ℕ → ℚ, OnRect N 1 a x → MvPolynomial.eval x L = 0 := by
  obtain ⟨x0, hx0R, hx0s, hx00, hx0P⟩ := hbase
  have hP0o : (a - 1, a + 2) ∈ oddDiagonals N := pkG_mem_odd.2 (by dsimp only; omega)
  have germ : ∀ b : ℕ × ℕ → ℚ, OnRect N 1 a b → (∀ t ∈ pkG_same N, mesh N b t.1 t.2 = 0) → b (a - 1, a + 2) = 0 →
      (∀ P ∈ oddDiagonals N, P ≠ (a - 1, a + 2) → b P ≠ 0) → ∀ y : ℕ × ℕ → ℚ, OnRect N 1 a y →
      y (a - 1, a + 2) ≠ 0 →
      MvPolynomial.eval b L = 0 ∧ MvPolynomial.eval (fun d => b d + y d) L - MvPolynomial.eval b L = 0 := by
    intro b hbR hbs hb0 hbP y hyR hy0
    have el : ∀ d, pkG_lg b y d = Polynomial.C (b d) + Polynomial.C (y d) * Polynomial.X := fun d => rfl
    have hg : ∀ d ∈ oddDiagonals N, pkG_lg b y d ≠ 0 := by
      intro d hd h0
      by_cases hdP : d = (a - 1, a + 2)
      · have e := congrArg (Polynomial.eval 1) h0
        rw [el, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
          Polynomial.eval_zero, hdP, hb0] at e
        apply hy0
        linarith
      · have e := congrArg (Polynomial.eval 0) h0
        rw [el, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
          Polynomial.eval_zero] at e
        apply hbP d hd hdP
        linarith
    have hden : MvPolynomial.aeval (pkG_lg b y) (oddDen ℚ N) ≠ 0 := by
      rw [pkM_oddDen, map_prod]
      simp only [MvPolynomial.aeval_X]
      exact prod_ne_zero_iff.2 hg
    have hNP : MvPolynomial.aeval (pkG_lg b y) (NP ℚ N) = 0 := by
      have hm : MvPolynomial.aeval (pkG_lg b y) (NP ℚ N) * MvPolynomial.aeval (pkG_lg b y) (oddDen ℚ N) = 0 := by
        apply Polynomial.funext
        intro s
        rw [Polynomial.eval_mul, pkG_lg_eval, pkG_lg_eval, Polynomial.eval_zero]
        by_cases hz : ∀ d ∈ oddDiagonals N, b d + s * y d ≠ 0
        · rw [pkG_NP_eval (by omega) _ hz,
            NLSM_row_zero (by omega) hE ⟨by omega, by omega⟩ _ hz (pkG_onRect_lin hbR hyR s)]
          ring
        · push_neg at hz
          obtain ⟨d, hd, h0⟩ := hz
          rw [pkM_oddDen, map_prod, prod_eq_zero hd (by rw [MvPolynomial.eval_X]; exact h0), mul_zero]
      exact (mul_eq_zero.1 hm).resolve_right hden
    have hCP : MvPolynomial.aeval (pkG_lg b y) (pkG_CP N) =
        MvPolynomial.aeval (pkG_lg b y) (oddDen ℚ N) * MvPolynomial.aeval (pkG_lg b y) L := by
      have h := congrArg (MvPolynomial.aeval (pkG_lg b y)) hL
      rw [map_add, map_mul, hNP, zero_add] at h
      exact h
    have hsplit : MvPolynomial.aeval (pkG_lg b y) (oddDen ℚ N) = Polynomial.C (y (a - 1, a + 2)) * Polynomial.X *
        Finset.prod ((oddDiagonals N).erase (a - 1, a + 2)) (fun d => pkG_lg b y d) := by
      rw [pkM_oddDen, map_prod, ← mul_prod_erase _ _ hP0o]
      simp only [MvPolynomial.aeval_X]
      rw [el (a - 1, a + 2), hb0, map_zero, zero_add]
    have hD0 : Polynomial.eval 0 (Finset.prod ((oddDiagonals N).erase (a - 1, a + 2)) (fun d => pkG_lg b y d)) ≠ 0 := by
      rw [Polynomial.eval_prod]
      refine prod_ne_zero_iff.2 (fun d hd => ?_)
      rw [el, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        mul_zero, add_zero]
      exact hbP d (mem_of_mem_erase hd) (ne_of_mem_erase hd)
    have hlin : MvPolynomial.aeval (pkG_lg b y) L = Polynomial.C (MvPolynomial.eval b L) +
        Polynomial.C (MvPolynomial.eval (fun d => b d + y d) L - MvPolynomial.eval b L) * Polynomial.X := by
      apply Polynomial.funext
      intro s
      rw [pkG_lg_eval, pkG_aff L hdeg b y s, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X]
      ring
    obtain ⟨Q, hQ⟩ := pkG_dvd3 hN hE ha haN hpair hbR hbs hb0 hyR
    rw [hCP, hsplit, hlin] at hQ
    exact pkG_germ_core hy0 hD0 hQ
  have w2 : OnRect N 1 a (fun d => x0 d + 1 * x0 d) := pkG_onRect_lin hx0R hx0R 1
  obtain ⟨w, hw0, hwR⟩ := onRect_inhabited (n := N) (k := 1) (m := a) le_rfl (by omega) (by omega) (by omega)
  refine line_bridge {x | OnRect N 1 a x} (fun x hx y hy t => by
      simp only [Set.mem_setOf_eq] at hx hy ⊢
      exact onRect_line hx hy t) L (MvPolynomial.X (a - 1, a + 2)) hwR ?_ (fun y hy hQ => ?_)
  · rw [MvPolynomial.eval_X]
    exact hw0 _ (mem_filter.1 hP0o).1
  · simp only [Set.mem_setOf_eq] at hy
    rw [MvPolynomial.eval_X] at hQ
    obtain ⟨g1, g2⟩ := germ x0 hx0R hx0s hx00 hx0P y hy hQ
    obtain ⟨g3, -⟩ := germ (fun d => x0 d + 1 * x0 d) w2
      (fun t ht => by
        show mesh N (fun d => x0 d + 1 * x0 d) t.1 t.2 = 0
        rw [pkG_mesh_lin, hx0s t ht]
        ring)
      (by
        show x0 (a - 1, a + 2) + 1 * x0 (a - 1, a + 2) = 0
        rw [hx00]
        ring)
      (fun P hP hne => by
        show x0 P + 1 * x0 P ≠ 0
        have := hx0P P hP hne
        intro h
        apply this
        linarith) y hy hQ
    have a1 := pkRw_add L hdeg x0 x0
    have a2 := pkRw_add L hdeg x0 y
    have e1 : x0 + x0 = fun d => x0 d + 1 * x0 d := funext (fun d => by
      show x0 d + x0 d = x0 d + 1 * x0 d
      ring)
    have e2 : x0 + y = fun d => x0 d + y d := rfl
    rw [e1, g3, g1] at a1
    rw [e2] at a2
    linarith

theorem pkG_rowZ_all (hPB : ∀ N a : ℕ, 8 ≤ N → N % 2 = 0 → 2 ≤ a → a + 2 ≤ N → pkG_Pair N a ∧ pkG_Base N a) :
    ∀ N : ℕ, 8 ≤ N → N % 2 = 0 → pkG_RowZ N :=
  fun N hN hE a ha haN L hdeg hL x hx =>
    pkG_rowZ_of (by omega) hE ha haN (hPB N a hN hE ha haN).1 (hPB N a hN hE ha haN).2 L hdeg hL x hx

/-- The pairs through leg `a` (the row-`a` tiles). -/
def pkG_rowS (N a : ℕ) : Finset (ℕ × ℕ) := (diagonals N).filter (fun t => t.1 = a ∨ t.2 = a)

theorem pkG_vtx_add {N : ℕ} (hN : 1 ≤ N) (j : ℕ) : vtx N (j + N) = vtx N j := by
  show (j + N + N - 1) % N + 1 = (j + N - 1) % N + 1
  rw [show j + N + N - 1 = (j + N - 1) + N by omega, Nat.add_mod_right]

/-- A point vanishing on the row-`a` tiles lies on the row locus. -/
theorem pkG_rowS_rect {N a : ℕ} (ha : 2 ≤ a) (haN : a + 2 ≤ N) {x : ℕ × ℕ → ℚ}
    (hx : OnLocus N (pkG_rowS N a) x) : OnRect N 1 a x := by
  intro i hi j hj
  have hi' : i = a := by
    have := mem_Ico.1 hi
    omega
  subst hi'
  have hj' := mem_Icc.1 hj
  by_cases hjN : j ≤ N
  · exact hx (i, j) (mem_filter.2 ⟨mem_diagonals.2 (by dsimp only; omega), Or.inl rfl⟩)
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + N := ⟨j - N, by omega⟩
    have v1 : vtx N (k + N) = vtx N k := pkG_vtx_add (by omega) k
    have v2 : vtx N (k + N + 1) = vtx N (k + 1) := by
      rw [show k + N + 1 = k + 1 + N by omega]
      exact pkG_vtx_add (by omega) (k + 1)
    have e : mesh N x i (k + N) = mesh N x i k := by
      rw [pkL_mesh_eq, pkL_mesh_eq, planar_congr (m := N) x (i := i) (i' := i) rfl v1,
        planar_congr (m := N) x (i := i + 1) (i' := i + 1) rfl v2, planar_congr (m := N) x (i := i) (i' := i) rfl v2,
        planar_congr (m := N) x (i := i + 1) (i' := i + 1) rfl v1]
    rw [e, pkI_mesh_symm]
    exact hx (k, i) (mem_filter.2 ⟨mem_diagonals.2 (by dsimp only; omega), Or.inr rfl⟩)

/-- `P₀ = (a − 1, a + 2)` is clean for the row-`a` tiles: its minrect lies in the row. -/
theorem pkG_P0_clean {N a : ℕ} (hN : 6 ≤ N) (ha : 2 ≤ a) (haN : a + 2 ≤ N) (hE : N % 2 = 0) :
    (a - 1, a + 2) ∈ cleanChords N (pkG_rowS N a) := by
  have hP0o : (a - 1, a + 2) ∈ oddDiagonals N := pkG_mem_odd.2 (by dsimp only; omega)
  refine mem_filter.2 ⟨hP0o, disjoint_left.2 (fun p hp hm => ?_)⟩
  obtain ⟨⟨e, o⟩, hq, rfl⟩ := mem_image.1 hp
  obtain ⟨he, ho⟩ := mem_product.1 hq
  have he' := mem_filter.1 he
  have ho' := mem_filter.1 ho
  have heS := (pkG_mem_oddSide (N := N) (R := (a - 1, a + 2)) (by dsimp only; omega) (by dsimp only; omega)).1 he'.1
  have hoS := (pkG_mem_evenSide (N := N) (R := (a - 1, a + 2)) (by dsimp only; omega) (by dsimp only; omega)).1 ho'.1
  have hm' := mem_sdiff.1 hm
  apply hm'.2
  refine mem_filter.2 ⟨hm'.1, ?_⟩
  dsimp only at heS hoS he' ho' ⊢
  omega

/-- Every other mixed chord has a minrect pair off the row, so it is not clean for the row-`a` tiles. -/
theorem pkG_rowS_nclean {N a : ℕ} (ha : 2 ≤ a) (haN : a + 2 ≤ N) (hE : N % 2 = 0) {P : ℕ × ℕ}
    (hP : P ∈ oddDiagonals N) (hne : P ≠ (a - 1, a + 2)) : P ∉ cleanChords N (pkG_rowS N a) := by
  have hPo := pkG_mem_odd.1 hP
  have hne' : ¬ (P.1 = a - 1 ∧ P.2 = a + 2) := fun h => hne (Prod.ext h.1 h.2)
  have hP1 : 1 ≤ P.1 := by omega
  have hP2 : P.2 ≤ N := by omega
  obtain ⟨e, o, he, heo, ho, hoo, hea, hoa⟩ : ∃ e o : ℕ, e ∈ oddSide N P ∧ e % 2 = 0 ∧ o ∈ evenSide N P ∧
      o % 2 = 1 ∧ e ≠ a ∧ o ≠ a := by
    by_cases hu : P.1 % 2 = 1
    · refine ⟨if P.1 + 1 = a then P.1 + 3 else P.1 + 1, if 3 ≤ P.1 then 1 else N - 1,
        (pkG_mem_oddSide hP1 hP2).2 ?_, ?_, (pkG_mem_evenSide hP1 hP2).2 ?_, ?_, ?_, ?_⟩ <;> (try split_ifs) <;> omega
    · refine ⟨N, if P.1 + 1 = a then P.1 + 3 else P.1 + 1,
        (pkG_mem_oddSide hP1 hP2).2 ?_, ?_, (pkG_mem_evenSide hP1 hP2).2 ?_, ?_, ?_, ?_⟩ <;> (try split_ifs) <;> omega
  intro hc
  have hdis := (mem_filter.1 hc).2
  have hp := pkG_mem_minRect_of he heo ho hoo
  refine disjoint_left.1 hdis hp (mem_sdiff.2 ⟨pkG_minRect_diag hP hp, fun h => ?_⟩)
  have h2 := (mem_filter.1 h).2
  dsimp only at h2
  omega

/-- **D7(a) base point**: a point of the row-`a` locus where every same-parity tile vanishes, `X_{P₀} = 0`, and every
other mixed chord is non-zero (A6 witnesses + A8 avoidance). -/
theorem pkG_base {N a : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) (ha : 2 ≤ a) (haN : a + 2 ≤ N) : pkG_Base N a := by
  have hS : pkG_rowS N a ⊆ diagonals N := filter_subset _ _
  obtain ⟨x0, hL, hx⟩ := pkG_avoid_locus (N := N) (S := pkG_rowS N a ∪ pkG_same N) (fun P X => X P)
    (fun P X Y t => rfl) ((oddDiagonals N).erase (a - 1, a + 2)) (fun P hP => by
      obtain ⟨X, hX, h2⟩ := pkG_G1_wit (by omega) hE hS (mem_of_mem_erase hP)
        (pkG_rowS_nclean ha haN hE (mem_of_mem_erase hP) (ne_of_mem_erase hP))
      exact ⟨X, hX, by rw [h2]; norm_num⟩)
  exact ⟨x0, pkG_rowS_rect ha haN (fun t ht => hL t (mem_union_left _ ht)), pkG_same_zero hL,
    pkG_G1_clean (by omega) hE (pkG_P0_clean hN ha haN hE) hL, fun P hP hne => hx P (mem_erase.2 ⟨hne, hP⟩)⟩

theorem pkG_mesh_addN {N : ℕ} (hN : 1 ≤ N) (x : ℕ × ℕ → ℚ) (i k : ℕ) : mesh N x i (k + N) = mesh N x i k := by
  have v1 : vtx N (k + N) = vtx N k := pkG_vtx_add hN k
  have v2 : vtx N (k + N + 1) = vtx N (k + 1) := by
    rw [show k + N + 1 = k + 1 + N by omega]
    exact pkG_vtx_add hN (k + 1)
  rw [pkL_mesh_eq, pkL_mesh_eq, planar_congr (m := N) x (i := i) (i' := i) rfl v1,
    planar_congr (m := N) x (i := i + 1) (i' := i + 1) rfl v2, planar_congr (m := N) x (i := i) (i' := i) rfl v2,
    planar_congr (m := N) x (i := i + 1) (i' := i + 1) rfl v1]

/-- On row `a`, `mesh(a, u) = 0` for every leg `u ∉ {a − 1, a, a + 1}`. -/
theorem pkG_row_zero {N a : ℕ} (ha : 2 ≤ a) (haN : a + 2 ≤ N) {z : ℕ × ℕ → ℚ} (hz : OnRect N 1 a z) {u : ℕ}
    (hu1 : 1 ≤ u) (huN : u ≤ N) (hu : u + 1 < a ∨ a + 1 < u) : mesh N z a u = 0 := by
  have hi : a ∈ Ico a (a + 1) := mem_Ico.2 ⟨le_refl _, by omega⟩
  rcases hu with h | h
  · rw [← pkG_mesh_addN (by omega) z a u]
    exact hz a hi (u + N) (mem_Icc.2 ⟨by omega, by omega⟩)
  · exact hz a hi u (mem_Icc.2 ⟨by omega, by omega⟩)

/-- On row `a`, the row sum over a leg set containing both or neither of `a ± 1` vanishes. -/
theorem pkG_row_sum {N a : ℕ} (ha : 2 ≤ a) (haN : a + 2 ≤ N) {z : ℕ × ℕ → ℚ} (hz : OnRect N 1 a z)
    {W : Finset ℕ} (hW : W ⊆ Icc 1 N) (hiff : a - 1 ∈ W ↔ a + 1 ∈ W) :
    ∑ u ∈ W, mesh N z a u = 0 := by
  have hself : mesh N z a a = 0 := pkL_mesh_self (by omega) z a
  have key : ∀ V : Finset ℕ, V ⊆ Icc 1 N → ∑ u ∈ V, mesh N z a u =
      ∑ u ∈ V.filter (fun u => u = a - 1 ∨ u = a + 1), mesh N z a u := by
    intro V hV
    rw [sum_filter]
    refine sum_congr rfl (fun u hu => ?_)
    have hu' := mem_Icc.1 (hV hu)
    split_ifs with h
    · rfl
    · by_cases hua : u = a
      · rw [hua, hself]
      · exact pkG_row_zero ha haN hz hu'.1 hu'.2 (by omega)
  have hrow : ∑ u ∈ Icc 1 N, mesh N z a u = 0 := pkL_row (by omega) z a
  by_cases hin : a - 1 ∈ W
  · have e1 : W.filter (fun u => u = a - 1 ∨ u = a + 1) =
        (Icc 1 N).filter (fun u => u = a - 1 ∨ u = a + 1) := by
      ext u
      rw [mem_filter, mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨hW h1, h2⟩
      · rintro ⟨h1, h2⟩
        rcases h2 with h2 | h2
        · refine ⟨?_, Or.inl h2⟩
          rw [h2]
          exact hin
        · refine ⟨?_, Or.inr h2⟩
          rw [h2]
          exact hiff.1 hin
    rw [key W hW, e1, ← key (Icc 1 N) (subset_refl _), hrow]
  · have e1 : W.filter (fun u => u = a - 1 ∨ u = a + 1) = ∅ := by
      refine filter_eq_empty_iff.2 (fun u hu h => ?_)
      rcases h with h | h
      · rw [h] at hu
        exact hin hu
      · rw [h] at hu
        exact hin (hiff.2 hu)
    rw [key W hW, e1, sum_empty]

/-- Adding a leg with vanishing row sum does not change `Q`. -/
theorem pkG_Q_ins {N : ℕ} (hN : 2 ≤ N) (z : ℕ × ℕ → ℚ) {a : ℕ} {W : Finset ℕ} (ha : a ∉ W)
    (hs : ∑ u ∈ W, mesh N z a u = 0) : pkG_Q N z (insert a W) = pkG_Q N z W := by
  have h1 := pkG_Q_F hN z (insert a W)
  have h2 := pkG_Q_F hN z W
  have hd : Disjoint ({a} : Finset ℕ) W := disjoint_singleton_left.2 ha
  have e : insert a W = {a} ∪ W := insert_eq a W
  rw [e, pkG_F_unionL _ hd, pkG_F_unionR _ hd, pkG_F_unionR _ hd] at h1
  have f1 : pkG_F (pkG_m N z) {a} {a} = 0 := by
    show ∑ x ∈ ({a} : Finset ℕ), ∑ y ∈ ({a} : Finset ℕ), mesh N z x y = 0
    rw [sum_singleton, sum_singleton]
    exact pkL_mesh_self hN z a
  have f2 : pkG_F (pkG_m N z) {a} W = 0 := by
    show ∑ x ∈ ({a} : Finset ℕ), ∑ y ∈ W, mesh N z x y = 0
    rw [sum_singleton]
    exact hs
  have f3 : pkG_F (pkG_m N z) W {a} = 0 := by
    show ∑ x ∈ W, ∑ y ∈ ({a} : Finset ℕ), mesh N z x y = 0
    simp only [sum_singleton]
    rw [← hs]
    exact sum_congr rfl (fun u _ => pkL_mesh_comm N z u a)
  rw [e]
  linarith

theorem pkG_Q_pair (N : ℕ) (z : ℕ × ℕ → ℚ) {u v : ℕ} (h : u < v) : pkG_Q N z {u, v} = -mesh N z u v := by
  have e : (({u, v} : Finset ℕ) ×ˢ ({u, v} : Finset ℕ)).filter (fun p => p.1 < p.2) = {(u, v)} := by
    ext ⟨p, q⟩
    simp only [mem_filter, mem_product, mem_insert, mem_singleton, Prod.mk.injEq]
    constructor
    · intro h'
      omega
    · intro h'
      omega
  show ∑ p ∈ (({u, v} : Finset ℕ) ×ˢ ({u, v} : Finset ℕ)).filter (fun p => p.1 < p.2), -mesh N z p.1 p.2 = _
  rw [e, sum_singleton]

theorem pkG_sgn_add2 {k : ℕ} (hk : 2 ≤ k) : pkG_sgn (k + 2) = -pkG_sgn k := by
  show (-1 : ℚ) ^ ((k + 2) / 2 - 1) = -((-1 : ℚ) ^ (k / 2 - 1))
  rw [show (k + 2) / 2 - 1 = (k / 2 - 1) + 1 by omega, pow_succ]
  ring

/-- The Cayley vertex depends on the dissection only through the face's vertex set. -/
theorem pkG_V_of_verts (N : ℕ) (z : ℕ × ℕ → ℚ) {D D' : Finset (ℕ × ℕ)} {r : ℕ × ℕ}
    (h : pkG_verts D r = pkG_verts D' r) : pkG_V N z D r = pkG_V N z D' r := by
  have hg : ∀ x, pkG_gov D r x = pkG_gov D' r x := fun x => by
    show ((pkG_verts D r).filter (fun w => w ≤ x)).sup (fun w => w) =
      ((pkG_verts D' r).filter (fun w => w ≤ x)).sup (fun w => w)
    rw [h]
  have hU : pkG_U D r = pkG_U D' r := by
    ext x
    rw [pkG_mem_U, pkG_mem_U, hg]
  show pkG_sgn (pkG_verts D r).card * pkG_Q N z (pkG_U D r) =
    pkG_sgn (pkG_verts D' r).card * pkG_Q N z (pkG_U D' r)
  rw [h, hU]

/-- **B10 (row pairing, numerator form)**: on row `a` (`2 ≤ a ≤ N − 2`), a dissection through `P₀ = (a − 1, a + 2)`
and the one without it contribute opposite terms (PREFORM-Germ B10). -/
theorem pkG_rowpair {N a : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) (ha : 2 ≤ a) (haN : a + 2 ≤ N) : pkG_Pair N a := by
  intro z hz D hD hP0
  have hN4 : 4 ≤ N := by omega
  have hdis := pkG_mem_dis.1 hD
  have hP0o : (a - 1, a + 2) ∈ oddDiagonals N := hdis.1 hP0
  obtain ⟨p, hp, hk⟩ := pkG_par_ex hN4 hE hD hP0
  obtain ⟨-, hInP, hmax⟩ := pkG_mem_kids.1 hk
  have hIn := pkG_In_iff.1 hInP
  dsimp only at hIn
  have cp := pkG_root hN4 hE hD hp
  have hD' : D.erase (a - 1, a + 2) ∈ pkG_dis N := pkG_mem_dis.2 ⟨(erase_subset _ _).trans hdis.1,
    fun p1 hp1 q1 hq1 => hdis.2 p1 (mem_of_mem_erase hp1) q1 (mem_of_mem_erase hq1)⟩
  -- no chord strictly inside `P₀`
  have hin0 : ∀ R ∈ D, R ≠ (a - 1, a + 2) → ¬ (a - 1 ≤ R.1 ∧ R.2 ≤ a + 2) := by
    intro R hR hne hc
    have cR := pkG_chord hD hR
    apply hne
    exact Prod.ext (by omega) (by omega)
  -- laminarity against `P₀` for chords inside `p`
  have hlam : ∀ R ∈ D, R ≠ (a - 1, a + 2) → pkG_In R p → R.2 ≤ a - 1 ∨ a + 2 ≤ R.1 := by
    intro R hR hne hRp
    have cR := pkG_chord hD hR
    rcases pkG_lam (hdis.2 R hR (a - 1, a + 2) hP0) with h | h | h | h
    · dsimp only at h
      exact absurd ⟨h.1, h.2⟩ (hin0 R hR hne)
    · dsimp only at h
      exact absurd (pkG_In_iff.2 ⟨fun e => hne e.symm, h.1, h.2⟩) (hmax R hR hRp)
    · left
      dsimp only at h
      exact h
    · right
      dsimp only at h
      exact h
  -- the face `P₀`
  have hvP0 : pkG_verts D (a - 1, a + 2) = Icc (a - 1) (a + 2) := by
    ext w
    rw [pkG_mem_verts' hD, mem_Icc]
    dsimp only
    constructor
    · rintro ⟨h1, h2, -⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, h2, fun R hR hRi => ?_⟩
      rw [pkG_In_iff] at hRi
      dsimp only at hRi
      exact absurd ⟨hRi.2.1, hRi.2.2⟩ (hin0 R hR hRi.1)
  have hkid0 : ∀ R ∈ pkG_kids D (a - 1, a + 2), False := by
    intro R hR
    obtain ⟨hRD, hne, h1, h2⟩ := pkG_kid_in hR
    exact hin0 R hRD hne ⟨h1, h2⟩
  have hU0 : pkG_U D (a - 1, a + 2) = {a - 1, a + 1} := by
    ext x
    rw [mem_insert, mem_singleton]
    by_cases hx : a - 1 ≤ x ∧ x < a + 2
    · rw [pkG_U_own (D := D) (r := (a - 1, a + 2)) hx.1 hx.2 (fun R hR _ => hkid0 R hR)]
      dsimp only
      omega
    · rw [pkG_mem_U]
      dsimp only
      omega
  have hW0 : ({a - 1, a + 1} : Finset ℕ) ⊆ Icc 1 N := by
    intro u hu
    rw [mem_insert, mem_singleton] at hu
    rw [mem_Icc]
    omega
  have hs0 : ∑ u ∈ ({a - 1, a + 1} : Finset ℕ), mesh N z a u = 0 :=
    pkG_row_sum ha haN hz hW0 ⟨fun _ => by simp, fun _ => by simp⟩
  have hV0 : pkG_V N z D (a - 1, a + 2) = -pkG_Q N z {a - 1, a + 1} := by
    show pkG_sgn (pkG_verts D (a - 1, a + 2)).card * pkG_Q N z (pkG_U D (a - 1, a + 2)) = _
    rw [hvP0, hU0, Nat.card_Icc, show a + 2 + 1 - (a - 1) = 4 by omega]
    show (-1 : ℚ) ^ (4 / 2 - 1) * _ = _
    norm_num
  have hz0 : z (a - 1, a + 2) = pkG_Q N z {a - 1, a + 1} := by
    rw [pkG_S1 (by omega) z (mem_filter.1 hP0o).1]
    have e : Ico (a - 1) (a + 2) = insert a {a - 1, a + 1} := by
      ext x
      rw [mem_Ico, mem_insert, mem_insert, mem_singleton]
      omega
    rw [e]
    exact pkG_Q_ins (by omega) z (by rw [mem_insert, mem_singleton]; omega) hs0
  -- the parent face `p`
  have hv_a : ∀ w, a ≤ w → w ≤ a + 1 → w ∉ pkG_verts D p := by
    intro w h1 h2 hw
    have := ((pkG_mem_verts' hD).1 hw).2.2 (a - 1, a + 2) hP0 hInP
    dsimp only at this
    omega
  have hv2 : a + 2 ∈ pkG_verts D p := by
    refine (pkG_mem_verts' hD).2 ⟨by omega, by omega, fun R hR hRp hc => ?_⟩
    by_cases hne : R = (a - 1, a + 2)
    · rw [hne] at hc
      dsimp only at hc
      omega
    · rcases hlam R hR hne hRp with h | h <;> omega
  have hvp : pkG_verts (D.erase (a - 1, a + 2)) p = insert a (insert (a + 1) (pkG_verts D p)) := by
    ext w
    rw [mem_insert, mem_insert, pkG_mem_verts' hD', pkG_mem_verts' hD]
    constructor
    · rintro ⟨h1, h2, h3⟩
      by_cases hw : w = a ∨ w = a + 1
      · rcases hw with hw | hw
        · exact Or.inl hw
        · exact Or.inr (Or.inl hw)
      · refine Or.inr (Or.inr ⟨h1, h2, fun R hR hRp => ?_⟩)
        by_cases hne : R = (a - 1, a + 2)
        · rw [hne]
          dsimp only
          omega
        · exact h3 R (mem_erase.2 ⟨hne, hR⟩) hRp
    · rintro (hw | hw | ⟨h1, h2, h3⟩)
      · refine ⟨by omega, by omega, fun R hR hRp => ?_⟩
        have hR' := mem_erase.1 hR
        rcases hlam R hR'.2 hR'.1 hRp with h | h <;> omega
      · refine ⟨by omega, by omega, fun R hR hRp => ?_⟩
        have hR' := mem_erase.1 hR
        rcases hlam R hR'.2 hR'.1 hRp with h | h <;> omega
      · exact ⟨h1, h2, fun R hR hRp => h3 R (mem_of_mem_erase hR) hRp⟩
  have hcard : (pkG_verts (D.erase (a - 1, a + 2)) p).card = (pkG_verts D p).card + 2 := by
    have n1 : a ∉ insert (a + 1) (pkG_verts D p) := by
      rw [mem_insert]
      rintro (h | h)
      · omega
      · exact hv_a a le_rfl (by omega) h
    rw [hvp, card_insert_of_notMem n1, card_insert_of_notMem (hv_a (a + 1) (by omega) le_rfl)]
  have hcard2 : 2 ≤ (pkG_verts D p).card := by
    have h1 : p.1 ∈ pkG_verts D p := pkG_r1_vert (by omega)
    have h12 : p.1 ≠ a + 2 := by omega
    exact (one_lt_card.2 ⟨p.1, h1, a + 2, hv2, h12⟩)
  -- governing vertices at `p`
  have hg_old : ∀ x, a - 1 ≤ x → x < a + 2 → pkG_gov D p x = a - 1 := fun x h1 h2 =>
    pkG_gov_kid hD hk h1 h2
  have hg_new : ∀ x, a ≤ x → x ≤ a + 1 → pkG_gov (D.erase (a - 1, a + 2)) p x = x := by
    intro x h1 h2
    have hx : x ∈ pkG_verts (D.erase (a - 1, a + 2)) p := by
      rw [hvp, mem_insert, mem_insert]
      omega
    apply le_antisymm
    · exact Finset.sup_le (fun w hw => (mem_filter.1 hw).2)
    · exact le_sup (f := fun w => w) (mem_filter.2 ⟨hx, le_refl x⟩)
  have hg_same : ∀ x, ¬ (a ≤ x ∧ x ≤ a + 1) →
      pkG_gov (D.erase (a - 1, a + 2)) p x = pkG_gov D p x := by
    intro x hx
    apply le_antisymm
    · refine Finset.sup_le (fun w hw => ?_)
      have hw' := mem_filter.1 hw
      rw [hvp, mem_insert, mem_insert] at hw'
      rcases hw'.1 with h | h | h
      · have : a + 2 ≤ pkG_gov D p x := le_sup (f := fun w => w) (mem_filter.2 ⟨hv2, by omega⟩)
        omega
      · have : a + 2 ≤ pkG_gov D p x := le_sup (f := fun w => w) (mem_filter.2 ⟨hv2, by omega⟩)
        omega
      · exact le_sup (f := fun w => w) (mem_filter.2 ⟨h, hw'.2⟩)
    · refine Finset.sup_le (fun w hw => ?_)
      have hw' := mem_filter.1 hw
      have hw2 : w ∈ pkG_verts (D.erase (a - 1, a + 2)) p := by
        rw [hvp, mem_insert, mem_insert]
        exact Or.inr (Or.inr hw'.1)
      exact le_sup (f := fun w => w) (mem_filter.2 ⟨hw2, hw'.2⟩)
  -- the class at `p` before and after
  have hUo : ∀ x, a - 1 ≤ x → x < a + 2 → (x ∈ pkG_U D p ↔ (a - 1 + p.1) % 2 = 0) := fun x h1 h2 =>
    pkG_U_kid hD hk h1 h2
  have hUn : ∀ x, x ∈ pkG_U (D.erase (a - 1, a + 2)) p ↔
      (x ≠ a ∧ x ∈ pkG_U D p) ∨ (x = a ∧ ¬ (a - 1 + p.1) % 2 = 0) := by
    intro x
    by_cases hx : a ≤ x ∧ x ≤ a + 1
    · rw [pkG_mem_U, hg_new x hx.1 hx.2, hUo x (by omega) (by omega)]
      omega
    · rw [pkG_mem_U, pkG_mem_U, hg_same x hx]
      omega
  have hUsub : pkG_U D p ⊆ Icc 1 N := by
    intro u hu
    have := pkG_mem_U.1 hu
    rw [mem_Icc]
    omega
  have hQp : pkG_Q N z (pkG_U (D.erase (a - 1, a + 2)) p) = pkG_Q N z (pkG_U D p) := by
    by_cases haU : a ∈ pkG_U D p
    · have e1 : pkG_U (D.erase (a - 1, a + 2)) p = (pkG_U D p).erase a := by
        ext x
        rw [hUn x, mem_erase]
        constructor
        · rintro (h | ⟨-, h2⟩)
          · exact h
          · exact absurd ((hUo a (by omega) (by omega)).1 haU) h2
        · intro h
          exact Or.inl h
      have hb : (a - 1 + p.1) % 2 = 0 := (hUo a (by omega) (by omega)).1 haU
      have hiff : a - 1 ∈ (pkG_U D p).erase a ↔ a + 1 ∈ (pkG_U D p).erase a := by
        rw [mem_erase, mem_erase]
        constructor
        · intro _
          exact ⟨by omega, (hUo (a + 1) (by omega) (by omega)).2 hb⟩
        · intro _
          exact ⟨by omega, (hUo (a - 1) (by omega) (by omega)).2 hb⟩
      have hins := pkG_Q_ins (N := N) (by omega) z (notMem_erase a (pkG_U D p))
        (pkG_row_sum ha haN hz ((erase_subset _ _).trans hUsub) hiff)
      rw [insert_erase haU] at hins
      rw [e1]
      exact hins.symm
    · have hb : ¬ (a - 1 + p.1) % 2 = 0 := fun h => haU ((hUo a (by omega) (by omega)).2 h)
      have e1 : pkG_U (D.erase (a - 1, a + 2)) p = insert a (pkG_U D p) := by
        ext x
        rw [hUn x, mem_insert]
        constructor
        · rintro (⟨-, h1⟩ | ⟨h1, -⟩)
          · exact Or.inr h1
          · exact Or.inl h1
        · rintro (h1 | h1)
          · exact Or.inr ⟨h1, hb⟩
          · refine Or.inl ⟨fun e => haU ?_, h1⟩
            rw [← e]
            exact h1
      rw [e1]
      refine pkG_Q_ins (by omega) z haU (pkG_row_sum ha haN hz hUsub ?_)
      constructor
      · intro h
        exact absurd ((hUo (a - 1) (by omega) (by omega)).1 h) hb
      · intro h
        exact absurd ((hUo (a + 1) (by omega) (by omega)).1 h) hb
  have hVp : pkG_V N z (D.erase (a - 1, a + 2)) p = -pkG_V N z D p := by
    show pkG_sgn (pkG_verts (D.erase (a - 1, a + 2)) p).card * pkG_Q N z (pkG_U (D.erase (a - 1, a + 2)) p) =
      -(pkG_sgn (pkG_verts D p).card * pkG_Q N z (pkG_U D p))
    rw [hcard, pkG_sgn_add2 hcard2, hQp]
    ring
  -- the other faces
  have hVo : ∀ r ∈ pkG_roots N D, r ≠ p → pkG_V N z (D.erase (a - 1, a + 2)) r = pkG_V N z D r := by
    intro r hr hrp
    refine pkG_V_of_verts N z ?_
    ext w
    rw [pkG_mem_verts' hD', pkG_mem_verts' hD]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, fun R hR hRr => ?_⟩
      by_cases hne : R = (a - 1, a + 2)
      · have hnk : (a - 1, a + 2) ∉ pkG_kids D r := fun h => hrp (pkG_par_uniq hN4 hE hD hr hp h hk)
        rw [pkG_mem_kids] at hnk
        rw [hne] at hRr
        have : ¬ ∀ R' ∈ D, pkG_In R' r → ¬ pkG_In (a - 1, a + 2) R' := fun h => hnk ⟨hP0, hRr, h⟩
        push_neg at this
        obtain ⟨R', hR', hR'r, hPR'⟩ := this
        have hne' : R' ≠ (a - 1, a + 2) := fun e => (pkG_In_iff.1 hPR').1 e.symm
        have h4 := h3 R' (mem_erase.2 ⟨hne', hR'⟩) hR'r
        rw [pkG_In_iff] at hPR'
        rw [hne]
        dsimp only at hPR' ⊢
        omega
      · exact h3 R (mem_erase.2 ⟨hne, hR⟩) hRr
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, fun R hR hRr => h3 R (mem_of_mem_erase hR) hRr⟩
  -- assemble the two terms
  have hPp : (a - 1, a + 2) ≠ p := hIn.1
  have hp' : p ∈ (pkG_roots N D).erase (a - 1, a + 2) := mem_erase.2 ⟨fun e => hPp e.symm, hp⟩
  have hr' : pkG_roots N (D.erase (a - 1, a + 2)) = (pkG_roots N D).erase (a - 1, a + 2) := by
    show insert (1, N) (D.erase (a - 1, a + 2)) = (insert (1, N) D).erase (a - 1, a + 2)
    rw [erase_insert_of_ne (fun e => by
      have e1 := congrArg Prod.fst e
      have e2 := congrArg Prod.snd e
      dsimp only at e1 e2
      omega)]
  have hP0r : (a - 1, a + 2) ∈ pkG_roots N D := mem_insert_of_mem hP0
  have et : ∀ D0 : Finset (ℕ × ℕ), pkG_term N z D0 = (-1 : ℚ) ^ D0.card *
      Finset.prod (pkG_roots N D0) (fun r => pkG_V N z D0 r) * Finset.prod (oddDiagonals N \ D0) (fun d => z d) :=
    fun D0 => rfl
  have hprod1 : Finset.prod (pkG_roots N D) (fun r => pkG_V N z D r) = pkG_V N z D (a - 1, a + 2) *
      (pkG_V N z D p * Finset.prod (((pkG_roots N D).erase (a - 1, a + 2)).erase p) (fun r => pkG_V N z D r)) := by
    rw [mul_prod_erase _ (fun r => pkG_V N z D r) hp', mul_prod_erase _ (fun r => pkG_V N z D r) hP0r]
  have hprod2 : Finset.prod (pkG_roots N (D.erase (a - 1, a + 2))) (fun r => pkG_V N z (D.erase (a - 1, a + 2)) r) =
      pkG_V N z (D.erase (a - 1, a + 2)) p *
        Finset.prod (((pkG_roots N D).erase (a - 1, a + 2)).erase p) (fun r => pkG_V N z D r) := by
    have hq : Finset.prod (((pkG_roots N D).erase (a - 1, a + 2)).erase p)
        (fun r => pkG_V N z (D.erase (a - 1, a + 2)) r) =
        Finset.prod (((pkG_roots N D).erase (a - 1, a + 2)).erase p) (fun r => pkG_V N z D r) :=
      prod_congr rfl (fun r hr => hVo r (mem_of_mem_erase (mem_of_mem_erase hr)) (ne_of_mem_erase hr))
    rw [hr', ← mul_prod_erase _ (fun r => pkG_V N z (D.erase (a - 1, a + 2)) r) hp', hq]
  have hodd : oddDiagonals N \ D.erase (a - 1, a + 2) = insert (a - 1, a + 2) (oddDiagonals N \ D) :=
    sdiff_erase hP0o
  have hnm : (a - 1, a + 2) ∉ oddDiagonals N \ D := fun h => (mem_sdiff.1 h).2 hP0
  have hc : D.card = (D.erase (a - 1, a + 2)).card + 1 := by
    rw [card_erase_of_mem hP0]
    have := card_pos.2 ⟨_, hP0⟩
    omega
  rw [et, et, hprod1, hprod2, hodd, prod_insert hnm, hVp, hV0, hz0, hc, pow_succ]
  ring

/-- `Q` of a four-leg set. -/
theorem pkG_Q_four (N : ℕ) (x : ℕ × ℕ → ℚ) {u v w t : ℕ} (h1 : u < v) (h2 : v < w) (h3 : w < t) :
    pkG_Q N x {u, v, w, t} = -(mesh N x u v + mesh N x u w + mesh N x u t + mesh N x v w + mesh N x v t +
      mesh N x w t) := by
  have e : (({u, v, w, t} : Finset ℕ) ×ˢ ({u, v, w, t} : Finset ℕ)).filter (fun p => p.1 < p.2) =
      {(u, v), (u, w), (u, t), (v, w), (v, t), (w, t)} := by
    ext ⟨p, q⟩
    simp only [mem_filter, mem_product, mem_insert, mem_singleton, Prod.mk.injEq]
    constructor
    · intro h
      omega
    · intro h
      omega
  show ∑ p ∈ (({u, v, w, t} : Finset ℕ) ×ˢ ({u, v, w, t} : Finset ℕ)).filter (fun p => p.1 < p.2),
    -mesh N x p.1 p.2 = _
  rw [e, sum_insert (by simp only [mem_insert, mem_singleton, Prod.mk.injEq]; omega),
    sum_insert (by simp only [mem_insert, mem_singleton, Prod.mk.injEq]; omega),
    sum_insert (by simp only [mem_insert, mem_singleton, Prod.mk.injEq]; omega),
    sum_insert (by simp only [mem_insert, mem_singleton, Prod.mk.injEq]; omega),
    sum_insert (by simp only [mem_insert, mem_singleton, Prod.mk.injEq]; omega), sum_singleton]
  ring

/-- **D5 (N = 6)**: `NP₆ = −CP₆` (four mixed dissections; `NLSM_six`). -/
theorem pkG_thmI_six : NP ℚ 6 = -pkG_CP 6 := by
  refine pkM_eq_of_eval (N := 6) _ _ (fun x hx => ?_)
  have hd : pkG_dis 6 = {∅, {(1, 4)}, {(2, 5)}, {(3, 6)}} := by decide
  have ho : oddDiagonals 6 = {(1, 4), (2, 5), (3, 6)} := by decide
  have en : pkG_num 6 x = ∑ D ∈ pkG_dis 6, pkG_term 6 x D := rfl
  have et : ∀ D, pkG_term 6 x D = (-1 : ℚ) ^ D.card * Finset.prod (pkG_roots 6 D) (fun r => pkG_V 6 x D r) *
      Finset.prod (oddDiagonals 6 \ D) (fun d => x d) := fun D => rfl
  have eV : ∀ D r, pkG_V 6 x D r = pkG_sgn (pkG_verts D r).card * pkG_Q 6 x (pkG_U D r) := fun D r => rfl
  have eE : pkG_E 6 x = ∑ t ∈ (diagonals 6).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0), mesh 6 x t.1 t.2 := rfl
  have hee : (diagonals 6).filter (fun p => p.1 % 2 = 0 ∧ p.2 % 2 = 0) = {(2, 4), (2, 6), (4, 6)} := by decide
  have s4 : pkG_sgn 4 = -1 := by
    show (-1 : ℚ) ^ (4 / 2 - 1) = -1
    norm_num
  have r0 : pkG_roots 6 ∅ = {(1, 6)} := rfl
  have r1 : pkG_roots 6 {(1, 4)} = {(1, 6), (1, 4)} := rfl
  have r2 : pkG_roots 6 {(2, 5)} = {(1, 6), (2, 5)} := rfl
  have r3 : pkG_roots 6 {(3, 6)} = {(1, 6), (3, 6)} := rfl
  have c1 : (pkG_verts {(1, 4)} (1, 4)).card = 4 := by decide
  have c2 : (pkG_verts {(1, 4)} (1, 6)).card = 4 := by decide
  have c3 : (pkG_verts {(2, 5)} (2, 5)).card = 4 := by decide
  have c4 : (pkG_verts {(2, 5)} (1, 6)).card = 4 := by decide
  have c5 : (pkG_verts {(3, 6)} (3, 6)).card = 4 := by decide
  have c6 : (pkG_verts {(3, 6)} (1, 6)).card = 4 := by decide
  have u1 : pkG_U {(1, 4)} (1, 4) = {1, 3} := by decide
  have u2 : pkG_U {(1, 4)} (1, 6) = {1, 2, 3, 5} := by decide
  have u3 : pkG_U {(2, 5)} (2, 5) = {2, 4} := by decide
  have u4 : pkG_U {(2, 5)} (1, 6) = {1, 5} := by decide
  have u5 : pkG_U {(3, 6)} (3, 6) = {3, 5} := by decide
  have u6 : pkG_U {(3, 6)} (1, 6) = {1, 3, 4, 5} := by decide
  have o0 : oddDiagonals 6 \ ∅ = {(1, 4), (2, 5), (3, 6)} := by decide
  have o1 : oddDiagonals 6 \ {(1, 4)} = {(2, 5), (3, 6)} := by decide
  have o2 : oddDiagonals 6 \ {(2, 5)} = {(1, 4), (3, 6)} := by decide
  have o3 : oddDiagonals 6 \ {(3, 6)} = {(1, 4), (2, 5)} := by decide
  have hdiag : diagonals 6 = {(1, 3), (1, 4), (1, 5), (2, 4), (2, 5), (2, 6), (3, 5), (3, 6), (4, 6)} := by decide
  rw [map_neg, pkG_CP_eval, pkG_NP_eval (by norm_num) x hx, NLSM_six, en, hd,
    sum_insert (show (∅ : Finset (ℕ × ℕ)) ∉ ({{(1, 4)}, {(2, 5)}, {(3, 6)}} : Finset (Finset (ℕ × ℕ))) by decide),
    sum_insert (show ({(1, 4)} : Finset (ℕ × ℕ)) ∉ ({{(2, 5)}, {(3, 6)}} : Finset (Finset (ℕ × ℕ))) by decide),
    sum_insert (show ({(2, 5)} : Finset (ℕ × ℕ)) ∉ ({{(3, 6)}} : Finset (Finset (ℕ × ℕ))) by decide),
    sum_singleton, et, et, et, et,
    r0, r1, r2, r3, o0, o1, o2, o3, ho, prod_singleton, pkG_V_empty (N := 6) (by norm_num) (by norm_num) x, eE, hee]
  simp only [prod_insert (show (1, 6) ∉ ({(1, 4)} : Finset (ℕ × ℕ)) by decide),
    prod_insert (show (1, 6) ∉ ({(2, 5)} : Finset (ℕ × ℕ)) by decide),
    prod_insert (show (1, 6) ∉ ({(3, 6)} : Finset (ℕ × ℕ)) by decide),
    prod_insert (show (1, 4) ∉ ({(2, 5), (3, 6)} : Finset (ℕ × ℕ)) by decide),
    prod_insert (show (2, 5) ∉ ({(3, 6)} : Finset (ℕ × ℕ)) by decide),
    prod_insert (show (1, 4) ∉ ({(3, 6)} : Finset (ℕ × ℕ)) by decide),
    prod_insert (show (1, 4) ∉ ({(2, 5)} : Finset (ℕ × ℕ)) by decide),
    prod_singleton, sum_insert (show (2, 4) ∉ ({(2, 6), (4, 6)} : Finset (ℕ × ℕ)) by decide),
    sum_insert (show (2, 6) ∉ ({(4, 6)} : Finset (ℕ × ℕ)) by decide), sum_singleton, card_empty, card_singleton, eV,
    c1, c2, c3, c4, c5, c6, u1, u2, u3, u4, u5, u6, s4]
  rw [pkG_Q_pair 6 x (show 1 < 3 by norm_num), pkG_Q_pair 6 x (show 2 < 4 by norm_num),
    pkG_Q_pair 6 x (show 1 < 5 by norm_num), pkG_Q_pair 6 x (show 3 < 5 by norm_num),
    pkG_Q_four 6 x (show 1 < 2 by norm_num) (show 2 < 3 by norm_num) (show 3 < 5 by norm_num),
    pkG_Q_four 6 x (show 1 < 3 by norm_num) (show 3 < 4 by norm_num) (show 4 < 5 by norm_num)]
  have h14 : x (1, 4) ≠ 0 := hx (1, 4) (by decide)
  have h25 : x (2, 5) ≠ 0 := hx (2, 5) (by decide)
  have h36 : x (3, 6) ≠ 0 := hx (3, 6) (by decide)
  simp only [pkL_mesh_eq]
  unfold planar vtx paper43
  rw [hdiag]
  norm_num
  field_simp
  ring

/-- **Theorem I (numerator form)**: `NP_N = −CP_N` for every even `N ≥ 4`. -/
theorem pkG_thmI_poly : ∀ N : ℕ, 4 ≤ N → N % 2 = 0 → NP ℚ N = -pkG_CP N :=
  pkG_thmI_of (pkG_rowZ_all (fun _ _ hN hE ha haN =>
    ⟨pkG_rowpair (by omega) hE ha haN, pkG_base (by omega) hE ha haN⟩)) pkG_thmI_six

/-- **D9, Theorem I** (App. A §5.1, raw normalisation): `NLSM_N = −M_N` off the mixed poles, every even `N ≥ 4`. -/
theorem pkG_thmI {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (x : ℕ × ℕ → ℚ) (hx : ∀ d ∈ oddDiagonals N, x d ≠ 0) :
    NLSM N x = -pkG_cay N x :=
  pkG_thmI_pt hN (pkG_thmI_poly N hN hE) x hx

/-! ### pkgGerm helpers (`pkG_`), sub-wave route: E1–E7 ([Germ-route], PREFORM-Germ §3 E). -/

theorem pkG_Xpow_dvd {α : Type*} [DecidableEq α] {s t : Finset α} (f : α → Polynomial ℚ) (hts : t ⊆ s)
    (h : ∀ i ∈ t, Polynomial.X ∣ f i) : Polynomial.X ^ t.card ∣ Finset.prod s f := by
  rw [← prod_sdiff hts, ← prod_const]
  exact Dvd.dvd.mul_left (prod_dvd_prod_of_dvd (fun _ => Polynomial.X) f h) _

/-- **[Germ-route]** (App. A §3.6; PREFORM-Germ E1–E7): for `S ∈ F^π` with `𝒫₁ = ∅`, `NLSM_N ≢ 0` on `L_S`. -/
theorem pkG_germ {N : ℕ} (hN : 6 ≤ N) (hE : Even N) : GermInput N := by
  intro S hF hP1
  have hE' : N % 2 = 0 := Nat.even_iff.1 hE
  have hN4 : 4 ≤ N := by omega
  -- E1: the base point `x₀ ∈ L_{S ∪ same}`, non-zero off the clean chords
  obtain ⟨x0, hx0L, hx0⟩ := pkG_avoid_locus (N := N) (S := S ∪ pkG_same N) (fun P X => X P)
    (fun P X Y t => rfl) ((oddDiagonals N).filter (fun P => P ∉ cleanChords N S)) (fun P hP => by
      have hP' := mem_filter.1 hP
      obtain ⟨X, hX, h2⟩ := pkG_G1_wit hN4 hE' hF.1 hP'.1 hP'.2
      exact ⟨X, hX, by rw [h2]; norm_num⟩)
  have hx0S : OnLocus N S x0 := onLocus_mono subset_union_left hx0L
  have hx0s : ∀ t ∈ pkG_same N, mesh N x0 t.1 t.2 = 0 := pkG_same_zero hx0L
  have hx0c : ∀ P ∈ cleanChords N S, x0 P = 0 := fun P hP => pkG_G1_clean hN4 hE' hP hx0L
  have hx0n : ∀ P ∈ oddDiagonals N, P ∉ cleanChords N S → x0 P ≠ 0 := fun P hP hc =>
    hx0 P (mem_filter.2 ⟨hP, hc⟩)
  -- E2: the direction `y ∈ L_S`, every mixed chord and `E` non-zero
  obtain ⟨y, hyL, hy⟩ := pkG_avoid_locus (N := N) (S := S)
    ((fun i X => Option.elim i (pkG_E N X) (fun P => X P)) : Option (ℕ × ℕ) → (ℕ × ℕ → ℚ) → ℚ)
    (fun i X Y t => by
      rcases i with ⟨⟩ | P
      · exact pkG_E_lin N X Y t
      · rfl)
    (insert none ((oddDiagonals N).image some)) (fun i hi => by
      rcases mem_insert.1 hi with h | h
      · rw [h]
        obtain ⟨X, hX, h2⟩ := pkG_Ewit hN4 hE' hF
        refine ⟨X, hX, ?_⟩
        show pkG_E N X ≠ 0
        rw [h2]
        norm_num
      · obtain ⟨P, hP, rfl⟩ := mem_image.1 h
        exact hF.2.1 P (mem_filter.1 hP).1)
  have hyE : pkG_E N y ≠ 0 := hy none (mem_insert_self _ _)
  have hyP : ∀ P ∈ oddDiagonals N, y P ≠ 0 := fun P hP =>
    hy (some P) (mem_insert_of_mem (mem_image_of_mem some hP))
  have hz : ∀ s : ℚ, OnLocus N S (fun d => x0 d + s * y d) := fun s => pkBr_onLocus_lin hx0S hyL s
  have el : ∀ d, pkG_lg x0 y d = Polynomial.C (x0 d) + Polynomial.C (y d) * Polynomial.X := fun d => rfl
  have hcl : cleanChords N S ⊆ oddDiagonals N := filter_subset _ _
  -- E3/E4: the line image of each dissection term
  have hdis0 : (∅ : Finset (ℕ × ℕ)) ∈ pkG_dis N :=
    pkG_mem_dis.2 ⟨empty_subset _, fun p hp => absurd hp (notMem_empty p)⟩
  have hrest : ∀ D ∈ (pkG_dis N).erase ∅, Polynomial.X ^ ((cleanChords N S).card + 2) ∣
      MvPolynomial.aeval (pkG_lg x0 y) (pkG_tP N D) := by
    intro D hD
    obtain ⟨hne0, hD⟩ := mem_erase.1 hD
    have hne : D.Nonempty := nonempty_iff_ne_empty.2 hne0
    have e : pkG_tP N D = (-1 : MvPolynomial (ℕ × ℕ) ℚ) ^ D.card *
        Finset.prod (pkG_roots N D) (fun r => pkG_Vp N D r) *
          Finset.prod (oddDiagonals N \ D) (fun d => MvPolynomial.X d) := rfl
    by_cases hsub : D ⊆ cleanChords N S
    · obtain ⟨r, hr, hV⟩ := pkG_G4 hN4 hE' hD hP1 hsub hne
      have h0 : MvPolynomial.aeval (pkG_lg x0 y) (pkG_Vp N D r) = 0 := by
        apply Polynomial.funext
        intro s
        rw [pkG_lg_eval, pkG_Vp_eval, Polynomial.eval_zero]
        exact hV _ (pkG_A4_all (by omega) _) (hz s)
      rw [e, map_mul, map_mul, map_prod, prod_eq_zero hr h0, mul_zero, zero_mul]
      exact dvd_zero _
    · have hBne : (D \ cleanChords N S).Nonempty := by
        obtain ⟨R, hR, hRc⟩ := not_subset.1 hsub
        exact ⟨R, mem_sdiff.2 ⟨hR, hRc⟩⟩
      have hG3 := pkG_G3 hN4 hE' hD (sdiff_subset (s := D) (t := cleanChords N S))
      rw [if_pos hBne] at hG3
      have k1 := card_sdiff_add_card_inter D (cleanChords N S)
      have k2 := card_sdiff_add_card_inter (cleanChords N S) D
      rw [inter_comm] at k2
      have d1 : Polynomial.X ^ ((pkG_roots N D).filter
          (fun r => pkG_deg (pkG_ch D) (D \ cleanChords N S) r ≤ 1)).card ∣
          Finset.prod (pkG_roots N D) (fun r => MvPolynomial.aeval (pkG_lg x0 y) (pkG_Vp N D r)) := by
        refine pkG_Xpow_dvd _ (filter_subset _ _) (fun r hr => pkG_lg_dvd ?_)
        have hr' := mem_filter.1 hr
        rw [pkG_Vp_eval]
        exact pkG_V_base hN4 hE' hD hr'.1 S hr'.2 x0 (pkG_A4_all (by omega) x0) (pkG_A5_all (by omega) x0) hx0L
      have d2 : Polynomial.X ^ (cleanChords N S \ D).card ∣
          Finset.prod (oddDiagonals N \ D) (fun d => MvPolynomial.aeval (pkG_lg x0 y) (MvPolynomial.X d : MvPolynomial (ℕ × ℕ) ℚ)) := by
        refine pkG_Xpow_dvd _ (sdiff_subset_sdiff hcl (subset_refl _)) (fun P hP => pkG_lg_dvd ?_)
        rw [MvPolynomial.eval_X]
        exact hx0c P (mem_sdiff.1 hP).1
      rw [e, map_mul, map_mul, map_prod, map_prod]
      refine dvd_trans (pow_dvd_pow _ (show (cleanChords N S).card + 2 ≤ ((pkG_roots N D).filter
        (fun r => pkG_deg (pkG_ch D) (D \ cleanChords N S) r ≤ 1)).card + (cleanChords N S \ D).card by omega)) ?_
      rw [pow_add, mul_assoc]
      exact Dvd.dvd.mul_left (mul_dvd_mul d1 d2) _
  -- E5: the empty dissection gives the leading term
  have hV0 : MvPolynomial.aeval (pkG_lg x0 y) (pkG_Vp N ∅ (1, N)) =
      Polynomial.C (-((-1 : ℚ) ^ (N / 2 + 1)) * pkG_E N y) * Polynomial.X := by
    apply Polynomial.funext
    intro s
    rw [pkG_lg_eval, pkG_Vp_eval, pkG_V_empty hN4 hE', pkG_E_lin, pkG_E_zero hx0s, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    ring
  have hden : Finset.prod (oddDiagonals N) (fun d => MvPolynomial.aeval (pkG_lg x0 y) (MvPolynomial.X d : MvPolynomial (ℕ × ℕ) ℚ)) =
      Finset.prod (oddDiagonals N \ cleanChords N S) (fun d => pkG_lg x0 y d) *
        (Finset.prod (cleanChords N S) (fun d => Polynomial.C (y d)) * Polynomial.X ^ (cleanChords N S).card) := by
    simp only [MvPolynomial.aeval_X]
    have hc : Finset.prod (cleanChords N S) (fun d => pkG_lg x0 y d) =
        Finset.prod (cleanChords N S) (fun d => Polynomial.C (y d) * Polynomial.X) :=
      prod_congr rfl (fun d hd => by rw [el, hx0c d hd, map_zero, zero_add])
    rw [← prod_sdiff hcl, hc, prod_mul_distrib, prod_const]
  have hU0 : Polynomial.eval 0 (Finset.prod (oddDiagonals N \ cleanChords N S) (fun d => pkG_lg x0 y d)) *
      Polynomial.eval 0 (Finset.prod (cleanChords N S) (fun d => Polynomial.C (y d))) ≠ 0 := by
    rw [Polynomial.eval_prod, Polynomial.eval_prod]
    refine mul_ne_zero (prod_ne_zero_iff.2 (fun d hd => ?_)) (prod_ne_zero_iff.2 (fun d hd => ?_))
    · rw [el, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        mul_zero, add_zero]
      exact hx0n d (mem_sdiff.1 hd).1 (mem_sdiff.1 hd).2
    · rw [Polynomial.eval_C]
      exact hyP d (hcl hd)
  obtain ⟨R, hR⟩ := dvd_sum hrest
  have hnum : MvPolynomial.aeval (pkG_lg x0 y) (pkG_CP N) = Polynomial.X ^ ((cleanChords N S).card + 1) *
      (Polynomial.C (-((-1 : ℚ) ^ (N / 2 + 1)) * pkG_E N y) *
        (Finset.prod (oddDiagonals N \ cleanChords N S) (fun d => pkG_lg x0 y d) *
          Finset.prod (cleanChords N S) (fun d => Polynomial.C (y d))) + Polynomial.X * R) := by
    rw [pkG_CP_tP, map_sum, ← add_sum_erase _ _ hdis0, hR]
    have e0 : pkG_tP N ∅ = (-1 : MvPolynomial (ℕ × ℕ) ℚ) ^ (∅ : Finset (ℕ × ℕ)).card *
        Finset.prod (pkG_roots N ∅) (fun r => pkG_Vp N ∅ r) *
          Finset.prod (oddDiagonals N \ ∅) (fun d => MvPolynomial.X d) := rfl
    have r0 : pkG_roots N ∅ = {(1, N)} := rfl
    rw [e0, r0, prod_singleton, sdiff_empty, map_mul, map_mul, map_prod, hden, hV0, card_empty, pow_zero, map_one]
    ring
  have hnum0 : MvPolynomial.aeval (pkG_lg x0 y) (pkG_CP N) ≠ 0 := by
    intro h0
    rw [hnum] at h0
    have h1 := (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ Polynomial.X_ne_zero)
    have h2 := congrArg (Polynomial.eval 0) h1
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, zero_mul, add_zero,
      Polynomial.eval_zero] at h2
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact mul_ne_zero (neg_ne_zero.2 (pow_ne_zero _ (by norm_num))) hyE h3
    · exact hU0 h3
  have hden0 : MvPolynomial.aeval (pkG_lg x0 y) (oddDen ℚ N) ≠ 0 := by
    rw [pkM_oddDen, map_prod]
    refine prod_ne_zero_iff.2 (fun d hd h0 => ?_)
    rw [MvPolynomial.aeval_X] at h0
    by_cases hdc : d ∈ cleanChords N S
    · have e := congrArg (Polynomial.eval 1) h0
      rw [el, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        Polynomial.eval_zero, hx0c d hdc] at e
      exact hyP d hd (by linarith)
    · have e := congrArg (Polynomial.eval 0) h0
      rw [el, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        Polynomial.eval_zero] at e
      exact hx0n d hd hdc (by linarith)
  -- E6: a point off the roots
  obtain ⟨s0, hs0⟩ : ∃ s0 : ℚ, Polynomial.eval s0 (MvPolynomial.aeval (pkG_lg x0 y) (pkG_CP N) *
      MvPolynomial.aeval (pkG_lg x0 y) (oddDen ℚ N)) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact mul_ne_zero hnum0 hden0 (Polynomial.funext (fun s => by rw [hc s, Polynomial.eval_zero]))
  rw [Polynomial.eval_mul, pkG_lg_eval, pkG_lg_eval] at hs0
  obtain ⟨hn1, hn2⟩ := mul_ne_zero_iff.1 hs0
  rw [pkM_oddDen, map_prod] at hn2
  simp only [MvPolynomial.eval_X] at hn2
  have hXo : ∀ d ∈ oddDiagonals N, x0 d + s0 * y d ≠ 0 := prod_ne_zero_iff.1 hn2
  refine ⟨fun d => x0 d + s0 * y d, hz s0, hXo, ?_⟩
  rw [pkG_thmI hN4 hE' _ hXo, neg_ne_zero]
  intro h0
  apply hn1
  rw [pkG_CP_eval, pkG_num_cay N _ hXo, h0, zero_mul]

/-- `sorry` (pkgGerm, M3) · the [Germ] input at every even `N ≥ 6`. -/
theorem germ_input {N : ℕ} (hN : 6 ≤ N) (hE : Even N) : GermInput N :=
  pkG_germ hN hE

-- pkgRes sub-wave a (R12-P7b-pkgRes-a, claude-opus-5-5): PREFORM-Res §6 algebra layer, §2 tile dictionary, §4.1 wrappers.
/-- `V` is a ℚ-linear subspace of `σ → ℚ` (contains `0`, closed under pointwise combinations). -/
def pkR_Sub {σ : Type*} (V : Set (σ → ℚ)) : Prop :=
  (fun _ => (0 : ℚ)) ∈ V ∧ ∀ x ∈ V, ∀ y ∈ V, ∀ a b : ℚ, (fun i => a * x i + b * y i) ∈ V

theorem pkR_Sub_iff {σ : Type*} (V : Set (σ → ℚ)) : pkR_Sub V ↔
    ((fun _ => (0 : ℚ)) ∈ V ∧ ∀ x ∈ V, ∀ y ∈ V, ∀ a b : ℚ, (fun i => a * x i + b * y i) ∈ V) := Iff.rfl

/-- `ℓ` is a linear form: evaluation commutes with pointwise combinations. -/
def pkR_Lin {σ : Type*} (ℓ : MvPolynomial σ ℚ) : Prop :=
  ∀ x y : σ → ℚ, ∀ a b : ℚ,
    MvPolynomial.eval (fun i => a * x i + b * y i) ℓ = a * MvPolynomial.eval x ℓ + b * MvPolynomial.eval y ℓ

theorem pkR_Lin_iff {σ : Type*} (ℓ : MvPolynomial σ ℚ) : pkR_Lin ℓ ↔ ∀ x y : σ → ℚ, ∀ a b : ℚ,
    MvPolynomial.eval (fun i => a * x i + b * y i) ℓ = a * MvPolynomial.eval x ℓ + b * MvPolynomial.eval y ℓ :=
  Iff.rfl

theorem pkR_lin_X {σ : Type*} (d : σ) : pkR_Lin (MvPolynomial.X d : MvPolynomial σ ℚ) := by
  intro x y a b
  simp only [MvPolynomial.eval_X]

theorem pkR_lin_add {σ : Type*} {ℓ ℓ' : MvPolynomial σ ℚ} (h : pkR_Lin ℓ) (h' : pkR_Lin ℓ') :
    pkR_Lin (ℓ + ℓ') := by
  intro x y a b
  rw [map_add, map_add, map_add, h x y a b, h' x y a b]
  ring

theorem pkR_lin_sub {σ : Type*} {ℓ ℓ' : MvPolynomial σ ℚ} (h : pkR_Lin ℓ) (h' : pkR_Lin ℓ') :
    pkR_Lin (ℓ - ℓ') := by
  intro x y a b
  rw [map_sub, map_sub, map_sub, h x y a b, h' x y a b]
  ring

theorem pkR_lin_Cmul {σ : Type*} {ℓ : MvPolynomial σ ℚ} (c : ℚ) (h : pkR_Lin ℓ) :
    pkR_Lin (MvPolynomial.C c * ℓ) := by
  intro x y a b
  rw [map_mul, map_mul, map_mul, h x y a b, MvPolynomial.eval_C, MvPolynomial.eval_C, MvPolynomial.eval_C]
  ring

theorem pkR_lin_zero {σ : Type*} {ℓ : MvPolynomial σ ℚ} (h : pkR_Lin ℓ) :
    MvPolynomial.eval (fun _ => (0 : ℚ)) ℓ = 0 := by
  have e := h (fun _ => 0) (fun _ => 0) 0 0
  have e2 : (fun i : σ => (0 : ℚ) * (fun _ => (0 : ℚ)) i + 0 * (fun _ => (0 : ℚ)) i) = fun _ => 0 := by
    ext i; ring
  rw [e2] at e
  rw [e]; ring

/-- A subspace is closed under affine lines (the hypothesis of `line_bridge`). -/
theorem pkR_line {σ : Type*} {V : Set (σ → ℚ)} (hV : pkR_Sub V) :
    ∀ x ∈ V, ∀ y ∈ V, ∀ t : ℚ, x + HSMul.hSMul t (y - x) ∈ V := by
  intro x hx y hy t
  have e : x + HSMul.hSMul t (y - x) = fun i => (1 - t) * x i + t * y i := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [e]
  exact ((pkR_Sub_iff V).1 hV).2 x hx y hy (1 - t) t

theorem pkR_sub_inter {σ : Type*} {V : Set (σ → ℚ)} (hV : pkR_Sub V) {ℓ : MvPolynomial σ ℚ} (hℓ : pkR_Lin ℓ) :
    pkR_Sub {x | x ∈ V ∧ MvPolynomial.eval x ℓ = 0} := by
  obtain ⟨h0, hc⟩ := hV
  refine (pkR_Sub_iff _).2 ⟨⟨h0, pkR_lin_zero hℓ⟩, ?_⟩
  intro x hx y hy a b
  refine ⟨hc x hx.1 y hy.1 a b, ?_⟩
  rw [hℓ x y a b, hx.2, hy.2]
  ring

theorem pkR_smul_mem {σ : Type*} {V : Set (σ → ℚ)} (hV : pkR_Sub V) {x : σ → ℚ} (hx : x ∈ V) (t : ℚ) :
    (fun i => t * x i) ∈ V := by
  have e : (fun i => t * x i) = fun i => t * x i + 0 * x i := by ext i; ring
  rw [e]
  exact hV.2 x hx x hx t 0

/-- **[Prime]** (PREFORM-Res §6). -/
theorem pkR_prime {σ : Type*} {V : Set (σ → ℚ)} (hV : pkR_Sub V) {ℓ G : MvPolynomial σ ℚ}
    (hw : ∃ w ∈ V, MvPolynomial.eval w ℓ ≠ 0)
    (h : ∀ x ∈ V, MvPolynomial.eval x ℓ * MvPolynomial.eval x G = 0) :
    ∀ x ∈ V, MvPolynomial.eval x G = 0 := by
  obtain ⟨w, hwV, hwl⟩ := hw
  exact line_bridge V (pkR_line hV) G ℓ hwV hwl (fun x hx hq => (mul_eq_zero.1 (h x hx)).resolve_left hq)

/-- `P − P(X − ℓ·w)` is divisible by `ℓ`. -/
theorem pkR_dvd_sub_aeval {σ : Type*} (ℓ : MvPolynomial σ ℚ) (w : σ → ℚ) (P : MvPolynomial σ ℚ) :
    ℓ ∣ P - MvPolynomial.aeval (fun i => MvPolynomial.X i - MvPolynomial.C (w i) * ℓ) P := by
  refine MvPolynomial.induction_on
    (motive := fun P => ℓ ∣ P - MvPolynomial.aeval (fun i => MvPolynomial.X i - MvPolynomial.C (w i) * ℓ) P)
    P ?_ ?_ ?_
  · intro a
    rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, sub_self]
    exact dvd_zero _
  · intro p q hp hq
    rw [map_add, show p + q - (MvPolynomial.aeval (fun i => MvPolynomial.X i - MvPolynomial.C (w i) * ℓ) p +
        MvPolynomial.aeval (fun i => MvPolynomial.X i - MvPolynomial.C (w i) * ℓ) q) =
        (p - MvPolynomial.aeval (fun i => MvPolynomial.X i - MvPolynomial.C (w i) * ℓ) p) +
        (q - MvPolynomial.aeval (fun i => MvPolynomial.X i - MvPolynomial.C (w i) * ℓ) q) by ring]
    exact dvd_add hp hq
  · intro p i hp
    rw [map_mul, MvPolynomial.aeval_X, show p * MvPolynomial.X i -
        MvPolynomial.aeval (fun i => MvPolynomial.X i - MvPolynomial.C (w i) * ℓ) p *
          (MvPolynomial.X i - MvPolynomial.C (w i) * ℓ) =
        (p - MvPolynomial.aeval (fun i => MvPolynomial.X i - MvPolynomial.C (w i) * ℓ) p) * MvPolynomial.X i +
        (MvPolynomial.aeval (fun i => MvPolynomial.X i - MvPolynomial.C (w i) * ℓ) p * MvPolynomial.C (w i)) * ℓ
        by ring]
    exact dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_left ℓ _)

theorem pkR_eval_aeval {σ : Type*} (x : σ → ℚ) (g : σ → MvPolynomial σ ℚ) (P : MvPolynomial σ ℚ) :
    MvPolynomial.eval x (MvPolynomial.aeval g P) = MvPolynomial.eval (fun i => MvPolynomial.eval x (g i)) P := by
  refine MvPolynomial.induction_on
    (motive := fun P => MvPolynomial.eval x (MvPolynomial.aeval g P) =
      MvPolynomial.eval (fun i => MvPolynomial.eval x (g i)) P) P ?_ ?_ ?_
  · intro a
    rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.eval_C, MvPolynomial.eval_C]
  · intro p q hp hq
    rw [map_add, map_add, map_add, hp, hq]
  · intro p i hp
    rw [map_mul, map_mul, map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_X]

/-- **[Div]** (PREFORM-Res §6): a polynomial vanishing on `V ∩ {ℓ = 0}` is `ℓ · G` on `V`. -/
theorem pkR_div {σ : Type*} {V : Set (σ → ℚ)} (hV : pkR_Sub V) {ℓ : MvPolynomial σ ℚ} (hℓ : pkR_Lin ℓ)
    (hw : ∃ w ∈ V, MvPolynomial.eval w ℓ ≠ 0) (P : MvPolynomial σ ℚ)
    (h : ∀ x ∈ V, MvPolynomial.eval x ℓ = 0 → MvPolynomial.eval x P = 0) :
    ∃ G : MvPolynomial σ ℚ, ∀ x ∈ V, MvPolynomial.eval x P = MvPolynomial.eval x ℓ * MvPolynomial.eval x G := by
  obtain ⟨w0, hw0, hl0⟩ := hw
  obtain ⟨w, hwV, hwl⟩ : ∃ w ∈ V, MvPolynomial.eval w ℓ = 1 := by
    refine ⟨fun i => Inv.inv (MvPolynomial.eval w0 ℓ) * w0 i + 0 * w0 i, hV.2 w0 hw0 w0 hw0 _ 0, ?_⟩
    rw [hℓ w0 w0, zero_mul, add_zero]
    exact inv_mul_cancel₀ hl0
  obtain ⟨G, hG⟩ := pkR_dvd_sub_aeval ℓ w P
  refine ⟨G, fun x hx => ?_⟩
  have e1 : MvPolynomial.eval x (MvPolynomial.aeval (fun i => MvPolynomial.X i - MvPolynomial.C (w i) * ℓ) P) =
      MvPolynomial.eval (fun i => 1 * x i + (- MvPolynomial.eval x ℓ) * w i) P := by
    rw [pkR_eval_aeval]
    refine congrArg (fun y => MvPolynomial.eval y P) ?_
    ext i
    simp only [map_sub, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C]
    ring
  have e2 : MvPolynomial.eval (fun i => 1 * x i + (- MvPolynomial.eval x ℓ) * w i) P = 0 := by
    refine h _ (hV.2 x hx w hwV 1 _) ?_
    rw [hℓ x w, hwl]
    ring
  have e3 := congrArg (MvPolynomial.eval x) hG
  rw [map_sub, map_mul, e1, e2, sub_zero] at e3
  exact e3

/-- **[Div2]** (PREFORM-Res §6). -/
theorem pkR_div2 {σ : Type*} {V : Set (σ → ℚ)} (hV : pkR_Sub V) {ℓ ℓ' : MvPolynomial σ ℚ} (hℓ : pkR_Lin ℓ)
    (hℓ' : pkR_Lin ℓ') (hw : ∃ w ∈ V, MvPolynomial.eval w ℓ ≠ 0)
    (hw' : ∃ w ∈ V, MvPolynomial.eval w ℓ = 0 ∧ MvPolynomial.eval w ℓ' ≠ 0) (P : MvPolynomial σ ℚ)
    (h : ∀ x ∈ V, MvPolynomial.eval x ℓ = 0 → MvPolynomial.eval x ℓ' = 0 → MvPolynomial.eval x P = 0) :
    ∃ α β : MvPolynomial σ ℚ, ∀ x ∈ V, MvPolynomial.eval x P =
      MvPolynomial.eval x ℓ * MvPolynomial.eval x α + MvPolynomial.eval x ℓ' * MvPolynomial.eval x β := by
  obtain ⟨w', hw'V, hw'l, hw'l'⟩ := hw'
  obtain ⟨β, hβ⟩ := pkR_div (pkR_sub_inter hV hℓ) hℓ' ⟨w', ⟨hw'V, hw'l⟩, hw'l'⟩ P
    (fun x hx hx' => h x hx.1 hx.2 hx')
  obtain ⟨α, hα⟩ := pkR_div hV hℓ hw (P - ℓ' * β) (fun x hx hx0 => by
    rw [map_sub, map_mul, hβ x ⟨hx, hx0⟩, sub_self])
  refine ⟨α, β, fun x hx => ?_⟩
  have e := hα x hx
  rw [map_sub, map_mul] at e
  rw [← e]
  ring

theorem pkR_prodDiv_aux {σ ι : Type*} [DecidableEq ι] {V : Set (σ → ℚ)} (hV : pkR_Sub V)
    (ℓ : ι → MvPolynomial σ ℚ) (s : Finset ι) : ∀ P : MvPolynomial σ ℚ,
    (∀ i ∈ s, pkR_Lin (ℓ i)) → (∀ i ∈ s, ∃ w ∈ V, MvPolynomial.eval w (ℓ i) ≠ 0) →
    (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∃ w ∈ V, MvPolynomial.eval w (ℓ i) = 0 ∧ MvPolynomial.eval w (ℓ j) ≠ 0) →
    (∀ i ∈ s, ∀ x ∈ V, MvPolynomial.eval x (ℓ i) = 0 → MvPolynomial.eval x P = 0) →
    ∃ G : MvPolynomial σ ℚ, ∀ x ∈ V,
      MvPolynomial.eval x P = MvPolynomial.eval x (Finset.prod s ℓ) * MvPolynomial.eval x G := by
  refine Finset.induction_on s ?_ ?_
  · intro P _ _ _ _
    exact ⟨P, fun x _ => by rw [Finset.prod_empty, map_one, one_mul]⟩
  · intro a s ha ih P hl hn hp h
    obtain ⟨G1, hG1⟩ := pkR_div hV (hl a (mem_insert_self a s)) (hn a (mem_insert_self a s)) P
      (h a (mem_insert_self a s))
    have hz : ∀ i ∈ s, ∀ x ∈ V, MvPolynomial.eval x (ℓ i) = 0 → MvPolynomial.eval x G1 = 0 := by
      intro i hi
      have hne : i ≠ a := fun e => ha (e ▸ hi)
      obtain ⟨w, hwV, hwi, hwa⟩ := hp i (mem_insert_of_mem hi) a (mem_insert_self a s) hne
      have hP := pkR_prime (pkR_sub_inter hV (hl i (mem_insert_of_mem hi))) (ℓ := ℓ a) (G := G1)
        ⟨w, ⟨hwV, hwi⟩, hwa⟩ (fun x hx => by
          rw [← hG1 x hx.1]
          exact h i (mem_insert_of_mem hi) x hx.1 hx.2)
      intro x hx hx0
      exact hP x ⟨hx, hx0⟩
    obtain ⟨G, hG⟩ := ih G1 (fun i hi => hl i (mem_insert_of_mem hi))
      (fun i hi => hn i (mem_insert_of_mem hi))
      (fun i hi j hj hij => hp i (mem_insert_of_mem hi) j (mem_insert_of_mem hj) hij) hz
    refine ⟨G, fun x hx => ?_⟩
    rw [hG1 x hx, hG x hx, Finset.prod_insert ha, map_mul, mul_assoc]

/-- **[ProdDiv]** (PREFORM-Res §6): linear forms, each non-zero on `V`, pairwise non-proportional on `V`
(in the form "`ℓ_i` vanishes somewhere on `V` where `ℓ_j` does not"); a polynomial vanishing on every
`V ∩ {ℓ_i = 0}` is `(∏ ℓ_i) · G` on `V`. -/
theorem pkR_prodDiv {σ ι : Type*} [DecidableEq ι] {V : Set (σ → ℚ)} (hV : pkR_Sub V)
    (ℓ : ι → MvPolynomial σ ℚ) (s : Finset ι) (hl : ∀ i ∈ s, pkR_Lin (ℓ i))
    (hn : ∀ i ∈ s, ∃ w ∈ V, MvPolynomial.eval w (ℓ i) ≠ 0)
    (hp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∃ w ∈ V, MvPolynomial.eval w (ℓ i) = 0 ∧ MvPolynomial.eval w (ℓ j) ≠ 0)
    (P : MvPolynomial σ ℚ) (h : ∀ i ∈ s, ∀ x ∈ V, MvPolynomial.eval x (ℓ i) = 0 → MvPolynomial.eval x P = 0) :
    ∃ G : MvPolynomial σ ℚ, ∀ x ∈ V,
      MvPolynomial.eval x P = MvPolynomial.eval x (Finset.prod s ℓ) * MvPolynomial.eval x G :=
  pkR_prodDiv_aux hV ℓ s P hl hn hp h

/-- **[Const]** (PREFORM-Res §6): `P = D·G` on `V` with `P`, `D` of the same degree `k` along rays and `D ≢ 0` on `V`
⇒ `G` is constant on `V` (its value at `0`). -/
theorem pkR_const {σ : Type*} {V : Set (σ → ℚ)} (hV : pkR_Sub V) {P D G : MvPolynomial σ ℚ} {k : ℕ}
    (hP : ∀ x ∈ V, ∀ t : ℚ, MvPolynomial.eval (fun i => t * x i) P = t ^ k * MvPolynomial.eval x P)
    (hD : ∀ x ∈ V, ∀ t : ℚ, MvPolynomial.eval (fun i => t * x i) D = t ^ k * MvPolynomial.eval x D)
    (hPDG : ∀ x ∈ V, MvPolynomial.eval x P = MvPolynomial.eval x D * MvPolynomial.eval x G)
    (hDw : ∃ w ∈ V, MvPolynomial.eval w D ≠ 0) :
    ∀ x ∈ V, MvPolynomial.eval x G = MvPolynomial.eval (fun _ => (0 : ℚ)) G := by
  have hA : ∀ x ∈ V, MvPolynomial.eval x D ≠ 0 →
      MvPolynomial.eval x G = MvPolynomial.eval (fun _ => (0 : ℚ)) G := by
    intro x hx hDx
    have hVx : pkR_Sub {y : σ → ℚ | ∃ t : ℚ, y = fun i => t * x i} := by
      refine (pkR_Sub_iff _).2 ⟨⟨0, by ext i; ring⟩, ?_⟩
      rintro y ⟨t1, rfl⟩ z ⟨t2, rfl⟩ a b
      exact ⟨a * t1 + b * t2, by ext i; ring⟩
    have hl := line_bridge {y : σ → ℚ | ∃ t : ℚ, y = fun i => t * x i} (pkR_line hVx)
      (G - MvPolynomial.C (MvPolynomial.eval x G)) D (w := x) ⟨1, by ext i; ring⟩ hDx ?_
      (fun _ => (0 : ℚ)) ⟨0, by ext i; ring⟩
    · rw [map_sub, MvPolynomial.eval_C, sub_eq_zero] at hl
      exact hl.symm
    · rintro y ⟨t, rfl⟩ hDy
      rw [map_sub, MvPolynomial.eval_C, sub_eq_zero]
      have hty := pkR_smul_mem hV hx t
      have e := hPDG _ hty
      rw [hP x hx t, hD x hx t, hPDG x hx] at e
      have hDy' : t ^ k * MvPolynomial.eval x D ≠ 0 := by rwa [hD x hx t] at hDy
      refine mul_left_cancel₀ hDy' ?_
      rw [← e]
      ring
  intro x hx
  have hl := line_bridge V (pkR_line hV) (G - MvPolynomial.C (MvPolynomial.eval (fun _ => (0 : ℚ)) G)) D
    hDw.choose_spec.1 hDw.choose_spec.2 (fun y hy hDy => by
      rw [map_sub, MvPolynomial.eval_C, hA y hy hDy, sub_self]) x hx
  rw [map_sub, MvPolynomial.eval_C, sub_eq_zero] at hl
  exact hl

theorem pkR_avoid_aux {σ ι : Type*} [DecidableEq ι] {V : Set (σ → ℚ)} (hV : pkR_Sub V)
    (P : ι → MvPolynomial σ ℚ) (s : Finset ι) :
    (∀ i ∈ s, ∃ w ∈ V, MvPolynomial.eval w (P i) ≠ 0) →
    ∃ x ∈ V, MvPolynomial.eval x (Finset.prod s P) ≠ 0 := by
  refine Finset.induction_on s ?_ ?_
  · intro _
    exact ⟨fun _ => 0, hV.1, by rw [Finset.prod_empty, map_one]; exact one_ne_zero⟩
  · intro a s ha ih h
    obtain ⟨x1, hx1, hne1⟩ := ih (fun i hi => h i (mem_insert_of_mem hi))
    obtain ⟨w, hwV, hwa⟩ := h a (mem_insert_self a s)
    by_contra hcon
    apply hne1
    refine line_bridge V (pkR_line hV) (Finset.prod s P) (P a) hwV hwa (fun x hx hPa => ?_) x1 hx1
    have hz : MvPolynomial.eval x (Finset.prod (insert a s) P) = 0 := by
      by_contra h2
      exact hcon ⟨x, hx, h2⟩
    rw [Finset.prod_insert ha, map_mul] at hz
    exact (mul_eq_zero.1 hz).resolve_left hPa

/-- **[Avoid]** (PREFORM-Res §6): polynomials each non-zero somewhere on `V` are simultaneously non-zero at one
point of `V`. -/
theorem pkR_avoid {σ ι : Type*} [DecidableEq ι] {V : Set (σ → ℚ)} (hV : pkR_Sub V)
    (P : ι → MvPolynomial σ ℚ) (s : Finset ι) (h : ∀ i ∈ s, ∃ w ∈ V, MvPolynomial.eval w (P i) ≠ 0) :
    ∃ x ∈ V, ∀ i ∈ s, MvPolynomial.eval x (P i) ≠ 0 := by
  obtain ⟨x, hx, hne⟩ := pkR_avoid_aux hV P s h
  refine ⟨x, hx, fun i hi => ?_⟩
  rw [map_prod] at hne
  exact prod_ne_zero_iff.1 hne i hi

-- [STnum], [ResNum], [Hom] wrappers

theorem pkR_eval_oddDen (m : ℕ) (x : ℕ × ℕ → ℚ) :
    MvPolynomial.eval x (oddDen ℚ m) = Finset.prod (oddDiagonals m) (fun d => x d) := by
  rw [show oddDen ℚ m = Finset.prod (oddDiagonals m) (fun d => MvPolynomial.X d) from rfl, map_prod]
  simp only [MvPolynomial.eval_X]

/-- **[STnum]** (PREFORM-Res §4.1): the NLSM numerator vanishes at every point of `Z_T` (poles included). -/
theorem pkR_STnum {m r : ℕ} (hm : 4 ≤ m) (hE : m % 2 = 0) (hr : r < 2) {T : Finset ℕ} (hT : Admissible m r T) :
    ∀ X : ℕ × ℕ → ℚ, OnZT m T X → MvPolynomial.eval X (NP ℚ m) = 0 := by
  obtain ⟨⟨w, hwZ, hw⟩, hZ⟩ := nlsm_zero_on_ZT (K := ℚ) hm hE hr hT
  intro X hX
  refine line_bridge {x | OnZT m T x} (fun x hx y hy t => onZT_line hx hy t) (NP ℚ m) (oddDen ℚ m) hwZ ?_ ?_ X hX
  · rw [pkR_eval_oddDen]
    exact prod_ne_zero_iff.2 (fun d hd => hw d (mem_filter.1 hd).1)
  · intro x hx hq
    rw [pkR_eval_oddDen] at hq
    have hodd : ∀ d ∈ oddDiagonals m, x d ≠ 0 := prod_ne_zero_iff.1 hq
    rw [show NP ℚ m = AP ℚ m (m - 2) from rfl, AP_eval m (m - 2) x hodd]
    have e : shiftCoeff m ((m - 2 : ℕ) : ℤ) x = NLSM m x := by
      rw [show ((m - 2 : ℕ) : ℤ) = (m : ℤ) - 2 by omega]
      rfl
    rw [e, hZ x hx hodd, zero_mul]

/-- **[ResNum]** (PREFORM-Res §4.1): `NP_m = X_C · E + NP_L · NP_R · crossProd_C` (children relabelled as in `NP_residue`). -/
theorem pkR_resNum {R : Type*} [CommRing R] {m : ℕ} (hm : 4 ≤ m) (hE : m % 2 = 0) {C : ℕ × ℕ}
    (hC : C ∈ oddDiagonals m) : ∃ E : MvPolynomial (ℕ × ℕ) R, NP R m = MvPolynomial.X C * E +
      MvPolynomial.rename (relab m C.1) (NP R (C.2 - C.1 + 1)) *
        MvPolynomial.rename (relab m C.2) (NP R (m - C.2 + C.1 + 1)) * crossProd R m C := by
  obtain ⟨E, hE'⟩ := pkI_sub_zeroAt C (NP R m)
  refine ⟨E, ?_⟩
  rw [← NP_residue hm hE hC, ← hE']
  ring

/-- **[Hom]** (PREFORM-Res §4.1): `NP_m` is homogeneous of degree `#odd + 1`. -/
theorem pkR_NP_hom {R : Type*} [CommRing R] {m : ℕ} (hm : 4 ≤ m) :
    (NP R m).IsHomogeneous ((oddDiagonals m).card + 1) := by
  have h := AP_isHomogeneous (R := R) hm (m - 2) (by omega)
  rwa [show (oddDiagonals m).card + (m - 2) - (m - 3) = (oddDiagonals m).card + 1 by omega] at h

-- §2 tile dictionary: [ExtMesh], [SubTile]

theorem pkR_planar_def {K : Type*} [Field K] (n : ℕ) (X : ℕ × ℕ → K) (i j : ℕ) :
    planar n X i j = if (min (vtx n i) (vtx n j), max (vtx n i) (vtx n j)) ∈ diagonals n then
      X (min (vtx n i) (vtx n j), max (vtx n i) (vtx n j)) else 0 := rfl

theorem pkR_mesh_def {K : Type*} [Field K] (n : ℕ) (X : ℕ × ℕ → K) (i j : ℕ) :
    mesh n X i j = planar n X i j + planar n X (i + 1) (j + 1) - planar n X i (j + 1) - planar n X (i + 1) j := rfl

theorem pkR_nxt_def (m u : ℕ) : nxt m u = if u = m then 1 else u + 1 := rfl

theorem pkR_planar_comm {K : Type*} [Field K] (n : ℕ) (X : ℕ × ℕ → K) (i j : ℕ) :
    planar n X i j = planar n X j i := by
  rw [pkR_planar_def n X i j, pkR_planar_def n X j i, min_comm (vtx n i) (vtx n j), max_comm (vtx n i) (vtx n j)]

theorem pkR_planar_self {K : Type*} [Field K] (n : ℕ) (X : ℕ × ℕ → K) (i : ℕ) : planar n X i i = 0 := by
  rw [pkR_planar_def, min_self, max_self]
  refine ite_eq_right ?_
  rw [mem_diagonals]
  dsimp only
  omega

theorem pkR_planar_succ {K : Type*} [Field K] {n : ℕ} (hn : 1 ≤ n) (X : ℕ × ℕ → K) (i : ℕ) :
    planar n X i (i + 1) = 0 := by
  rw [pkR_planar_def, vtx_succ hn]
  refine ite_eq_right ?_
  obtain ⟨h1, h2⟩ := vtx_bounds n i hn
  rw [pkR_nxt_def, mem_diagonals]
  split_ifs <;> (try dsimp only) <;> omega

/-- **[ExtMesh]** (PREFORM-Res §2): the extended mesh is symmetric ... -/
theorem pkR_mesh_comm {K : Type*} [Field K] (n : ℕ) (X : ℕ × ℕ → K) (a b : ℕ) : mesh n X a b = mesh n X b a := by
  rw [pkR_mesh_def n X a b, pkR_mesh_def n X b a, pkR_planar_comm n X b a, pkR_planar_comm n X (b + 1) (a + 1),
    pkR_planar_comm n X b (a + 1), pkR_planar_comm n X (b + 1) a]
  ring

/-- **[ExtMesh]** (PREFORM-Res §2): ... with zero diagonal. -/
theorem pkR_mesh_self {K : Type*} [Field K] {n : ℕ} (hn : 1 ≤ n) (X : ℕ × ℕ → K) (a : ℕ) : mesh n X a a = 0 := by
  rw [pkR_mesh_def, pkR_planar_self, pkR_planar_self, pkR_planar_succ hn, pkR_planar_comm n X (a + 1) a,
    pkR_planar_succ hn]
  ring

theorem pkR_vtx_vtx {n : ℕ} (hn : 1 ≤ n) (i : ℕ) : vtx n (vtx n i) = vtx n i :=
  vtx_of_mem (vtx_bounds n i hn).1 (vtx_bounds n i hn).2

theorem pkR_planar_vtx {K : Type*} [Field K] {n : ℕ} (hn : 1 ≤ n) (X : ℕ × ℕ → K) (i j : ℕ) :
    planar n X i j = planar n X (vtx n i) (vtx n j) := by
  rw [pkR_planar_def n X (vtx n i) (vtx n j), pkR_vtx_vtx hn i, pkR_vtx_vtx hn j]
  rfl

theorem pkR_planar_congr {K : Type*} [Field K] {n : ℕ} (hn : 1 ≤ n) (X : ℕ × ℕ → K) {i j i' j' : ℕ}
    (hi : vtx n i = vtx n i') (hj : vtx n j = vtx n j') : planar n X i j = planar n X i' j' := by
  rw [pkR_planar_vtx hn X i j, hi, hj, ← pkR_planar_vtx hn X i' j']

/-- A sub-polygon point: child chord `(k, l)` ↦ parent planar variable at the dual points `f k`, `f l`. -/
def pkR_subX {K : Type*} [Field K] (n : ℕ) (f : ℕ → ℕ) (X : ℕ × ℕ → K) : ℕ × ℕ → K :=
  fun p => planar n X (f p.1) (f p.2)

/-- Number of parent legs in the block of child leg `k` (cyclic difference, no ℕ truncation). -/
def pkR_len (n m : ℕ) (f : ℕ → ℕ) (k : ℕ) : ℕ := (f (vtx m (k + 1)) + n - f (vtx m k)) % n

/-- The parent legs of child leg `k`, as the integer range `f k, …, f k + len − 1` (read through `vtx n`). -/
def pkR_blk (n m : ℕ) (f : ℕ → ℕ) (k : ℕ) : Finset ℕ := Icc (f (vtx m k)) (f (vtx m k) + pkR_len n m f k - 1)

/-- A cyclic vertex list of length `m` in the `n`-gon: values in `1..n`, consecutive values distinct. (No
monotonicity is needed for [SubTile].) -/
def pkR_CycList (n m : ℕ) (f : ℕ → ℕ) : Prop := ∀ i ∈ Icc 1 m, f i ∈ Icc 1 n ∧ f (vtx m (i + 1)) ≠ f i

theorem pkR_CycList_iff (n m : ℕ) (f : ℕ → ℕ) :
    pkR_CycList n m f ↔ ∀ i ∈ Icc 1 m, f i ∈ Icc 1 n ∧ f (vtx m (i + 1)) ≠ f i := Iff.rfl

theorem pkR_len_spec {n a b : ℕ} (ha : a ∈ Icc 1 n) (hb : b ∈ Icc 1 n) (hab : b ≠ a) :
    1 ≤ (b + n - a) % n ∧ vtx n (a + (b + n - a) % n) = b := by
  rw [mem_Icc] at ha hb
  rcases lt_or_gt_of_ne hab with h | h
  · rw [Nat.mod_eq_of_lt (by omega)]
    refine ⟨by omega, ?_⟩
    rw [show a + (b + n - a) = b + n by omega, vtx_add_n, vtx_of_mem hb.1 hb.2]
  · rw [show b + n - a = (b - a) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    refine ⟨by omega, ?_⟩
    rw [show a + (b - a) = b by omega, vtx_of_mem hb.1 hb.2]

/-- [BlockSum] on integer ranges (from Phase 1's `mesh_telescope`). -/
theorem pkR_blockSum {K : Type*} [Field K] (n : ℕ) (X : ℕ × ℕ → K) {p q L1 L2 : ℕ} (h1 : 1 ≤ L1) (h2 : 1 ≤ L2) :
    Finset.sum (Icc p (p + L1 - 1)) (fun a => Finset.sum (Icc q (q + L2 - 1)) (fun b => mesh n X a b)) =
      planar n X p q + planar n X (p + L1) (q + L2) - planar n X p (q + L2) - planar n X (p + L1) q := by
  rw [mesh_telescope n X (by omega : p ≤ p + L1 - 1) (by omega : q ≤ q + L2 - 1),
    show p + L1 - 1 + 1 = p + L1 by omega, show q + L2 - 1 + 1 = q + L2 by omega]

theorem pkR_cpl {K : Type*} [Field K] (n m : ℕ) (f : ℕ → ℕ) (X : ℕ × ℕ → K) (i j : ℕ) :
    planar m (pkR_subX n f X) i j = if (min (vtx m i) (vtx m j), max (vtx m i) (vtx m j)) ∈ diagonals m then
      planar n X (f (vtx m i)) (f (vtx m j)) else 0 := by
  have e : planar m (pkR_subX n f X) i j =
      if (min (vtx m i) (vtx m j), max (vtx m i) (vtx m j)) ∈ diagonals m then
        planar n X (f (min (vtx m i) (vtx m j))) (f (max (vtx m i) (vtx m j))) else 0 := rfl
  rw [e]
  rcases le_total (vtx m i) (vtx m j) with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, pkR_planar_comm n X (f (vtx m j)) (f (vtx m i))]

theorem pkR_D11 {m k l : ℕ} (hk : k ∈ Icc 1 m) (hl : l ∈ Icc 1 m) (h : (min k l, max k l) ∈ diagonals m) :
    (min (nxt m k) (nxt m l), max (nxt m k) (nxt m l)) ∈ diagonals m := by
  rw [mem_Icc] at hk hl
  rw [mem_diagonals] at h ⊢
  dsimp only at h ⊢
  rw [pkR_nxt_def m k, pkR_nxt_def m l]
  split_ifs <;> omega

theorem pkR_D01 {m k l : ℕ} (hk : k ∈ Icc 1 m) (hl : l ∈ Icc 1 m) (h : (min k l, max k l) ∈ diagonals m) :
    (min k (nxt m l), max k (nxt m l)) ∈ diagonals m ↔ ¬ k = nxt m (nxt m l) := by
  rw [mem_Icc] at hk hl
  rw [mem_diagonals] at h ⊢
  dsimp only at h ⊢
  rw [pkR_nxt_def m l, pkR_nxt_def m (if l = m then 1 else l + 1)]
  split_ifs <;> constructor <;> intro hh <;> omega

theorem pkR_D10 {m k l : ℕ} (hk : k ∈ Icc 1 m) (hl : l ∈ Icc 1 m) (h : (min k l, max k l) ∈ diagonals m) :
    (min (nxt m k) l, max (nxt m k) l) ∈ diagonals m ↔ ¬ l = nxt m (nxt m k) := by
  rw [mem_Icc] at hk hl
  rw [mem_diagonals] at h ⊢
  dsimp only at h ⊢
  rw [pkR_nxt_def m k, pkR_nxt_def m (if k = m then 1 else k + 1)]
  split_ifs <;> constructor <;> intro hh <;> omega

/-- **[SubTile]** (PREFORM-Res §2, R4 corner identity for any cyclic vertex list): a tile of the sub-polygon point
is the parent block sum plus the corner (mass) terms of the child edges it straddles. -/
theorem pkR_subTile {K : Type*} [Field K] {n m : ℕ} (hn : 1 ≤ n) (hm : 3 ≤ m) {f : ℕ → ℕ}
    (hf : pkR_CycList n m f) (X : ℕ × ℕ → K) {k l : ℕ} (hk : k ∈ Icc 1 m) (hl : l ∈ Icc 1 m)
    (hkl : (min k l, max k l) ∈ diagonals m) :
    mesh m (pkR_subX n f X) k l =
      Finset.sum (pkR_blk n m f k) (fun a => Finset.sum (pkR_blk n m f l) (fun b => mesh n X a b))
      + (if vtx m l = vtx m (k + 2) then planar n X (f (vtx m (k + 1))) (f (vtx m (k + 2))) else 0)
      + (if vtx m k = vtx m (l + 2) then planar n X (f (vtx m (l + 1))) (f (vtx m (l + 2))) else 0) := by
  have hm1 : 1 ≤ m := by omega
  have hk' := mem_Icc.1 hk
  have hl' := mem_Icc.1 hl
  have vk : vtx m k = k := vtx_of_mem hk'.1 hk'.2
  have vl : vtx m l = l := vtx_of_mem hl'.1 hl'.2
  have vk1 : vtx m (k + 1) = nxt m k := by rw [vtx_succ hm1, vk]
  have vl1 : vtx m (l + 1) = nxt m l := by rw [vtx_succ hm1, vl]
  have vk2 : vtx m (k + 2) = nxt m (nxt m k) := by rw [show k + 2 = k + 1 + 1 from rfl, vtx_succ hm1, vk1]
  have vl2 : vtx m (l + 2) = nxt m (nxt m l) := by rw [show l + 2 = l + 1 + 1 from rfl, vtx_succ hm1, vl1]
  have hnk : nxt m k ∈ Icc 1 m := by rw [← vk1]; exact mem_Icc.2 (vtx_bounds m (k + 1) hm1)
  have hnl : nxt m l ∈ Icc 1 m := by rw [← vl1]; exact mem_Icc.2 (vtx_bounds m (l + 1) hm1)
  obtain ⟨fk, fk1⟩ := hf k hk
  obtain ⟨fl, fl1⟩ := hf l hl
  rw [vk1] at fk1
  rw [vl1] at fl1
  have fnk := (hf (nxt m k) hnk).1
  have fnl := (hf (nxt m l) hnl).1
  obtain ⟨Lk1, Lk2⟩ := pkR_len_spec fk fnk fk1
  obtain ⟨Ll1, Ll2⟩ := pkR_len_spec fl fnl fl1
  have vfk : vtx n (f k) = f k := vtx_of_mem (mem_Icc.1 fk).1 (mem_Icc.1 fk).2
  have vfl : vtx n (f l) = f l := vtx_of_mem (mem_Icc.1 fl).1 (mem_Icc.1 fl).2
  have vfnk : vtx n (f (nxt m k)) = f (nxt m k) := vtx_of_mem (mem_Icc.1 fnk).1 (mem_Icc.1 fnk).2
  have vfnl : vtx n (f (nxt m l)) = f (nxt m l) := vtx_of_mem (mem_Icc.1 fnl).1 (mem_Icc.1 fnl).2
  have c1 : vtx n (f k + (f (nxt m k) + n - f k) % n) = vtx n (f (nxt m k)) := by rw [Lk2, vfnk]
  have c2 : vtx n (f l + (f (nxt m l) + n - f l) % n) = vtx n (f (nxt m l)) := by rw [Ll2, vfnl]
  have eb : ∀ j, pkR_blk n m f j = Icc (f (vtx m j)) (f (vtx m j) + pkR_len n m f j - 1) := fun j => rfl
  have el : ∀ j, pkR_len n m f j = (f (vtx m (j + 1)) + n - f (vtx m j)) % n := fun j => rfl
  have eblk : Finset.sum (pkR_blk n m f k) (fun a => Finset.sum (pkR_blk n m f l) (fun b => mesh n X a b)) =
      planar n X (f k) (f l) + planar n X (f (nxt m k)) (f (nxt m l)) - planar n X (f k) (f (nxt m l)) -
        planar n X (f (nxt m k)) (f l) := by
    rw [eb k, eb l, el k, el l, vk, vl, vk1, vl1, pkR_blockSum n X Lk1 Ll1, pkR_planar_congr hn X c1 c2,
      pkR_planar_congr hn X (rfl : vtx n (f k) = vtx n (f k)) c2,
      pkR_planar_congr hn X c1 (rfl : vtx n (f l) = vtx n (f l))]
  rw [eblk, pkR_mesh_def m (pkR_subX n f X) k l, pkR_cpl, pkR_cpl, pkR_cpl, pkR_cpl]
  simp only [vk, vl, vk1, vl1, vk2, vl2]
  rw [ite_eq_left hkl, ite_eq_left (pkR_D11 hk hl hkl)]
  by_cases h1 : l = nxt m (nxt m k) <;> by_cases h2 : k = nxt m (nxt m l)
  · rw [ite_eq_right (fun hd => (pkR_D01 hk hl hkl).1 hd h2), ite_eq_right (fun hd => (pkR_D10 hk hl hkl).1 hd h1),
      ite_eq_left h1, ite_eq_left h2, ← h1, ← h2, pkR_planar_comm n X (f (nxt m l)) (f k)]
    ring
  · rw [ite_eq_left ((pkR_D01 hk hl hkl).2 h2), ite_eq_right (fun hd => (pkR_D10 hk hl hkl).1 hd h1),
      ite_eq_left h1, ite_eq_right h2, ← h1]
    ring
  · rw [ite_eq_right (fun hd => (pkR_D01 hk hl hkl).1 hd h2), ite_eq_left ((pkR_D10 hk hl hkl).2 h1),
      ite_eq_right h1, ite_eq_left h2, ← h2, pkR_planar_comm n X (f (nxt m l)) (f k)]
    ring
  · rw [ite_eq_left ((pkR_D01 hk hl hkl).2 h2), ite_eq_left ((pkR_D10 hk hl hkl).2 h1), ite_eq_right h1, ite_eq_right h2]
    ring

-- [ArcX] from a Gram matrix, [Collapse], Gram inverse

/-- **[ArcX]** read backwards: the planar value of the arc `[i, j)` defined by a Gram matrix `C`,
`X_{i,j} = −Σ_{i ≤ c < d < j} C_{c,d}`. -/
def pkR_arcX {K : Type*} [Field K] (C : ℕ → ℕ → K) (i j : ℕ) : K :=
  -(Finset.sum (Ico i j) (fun d => Finset.sum (Ico i d) (fun c => C c d)))


end PiZ
