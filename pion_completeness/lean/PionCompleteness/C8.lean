/-
Copyright (c) 2026 Henru Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henru Wang
-/
module

public import PionCompleteness.C7

/-!
# Theorem Π, part 8: the constant of the standard polygon and the ear lemma

This module continues the chain of modules that prove Theorem Π; the chain is cut by size, not by
topic, so the sections run on from `C7`.
All of it lies in section 8, among the helpers of prefix `pkR_` that prove the residue input
`resChild_input` (`C10`); it opens inside the last section of `C7`.

It first shows that the constant `c` of the standard polygon (`NP_n = x · F₁` on `Λ`,
`F₁ = c · oddDen_n` on `Λ₀`, `pkR_const9` in `C7`) is non-zero: one induction step
(`pkR_psi_step`, through the locus `pkRZ5c`), its two routes and the induction `pkR_psi_all`.
Then come the inputs of `pkR_omega` (`C9`): the far-side rotation bridge (`pkR_rotG_NP`), the
numerator that avoids the chord of a member on `W_q` and on `Λ^I` (`pkR_notq_W`, `pkR_notq_lam`),
the children of a member chord (`pkR_childA`, `pkR_childB`) and the Ω algebra (`pkR_omega_alg`,
`pkR_omega0`, `pkR_omega_split`). The section of prefix `pkR_b_` holds the ear lemma on the locus
`Z′` (`pkRBZ5`) for one chord (`pkR_b_R5one2`, `pkR_b_R5one1`: the hypotheses `hR5two`,
`hR5one` above) and for a chain (`pkR_b_R5d`), the children of a chord on `Z′` (`pkR_b_R6Z5`,
`pkR_b_R6Z5B`, `pkR_b_R6van`) and the collapse identity (`pkR_b_R2top`, `pkR_b_R2bot`,
`pkR_b_pull_head`). It ends with the locality and rotation invariance of the numerators
(`pkR_b_NPK_local`, `pkR_b_NP_rot`); the sections on the numerators that avoid a set of odd chords
continue in `C9`.

The conventions are those of `C0`'s module docstring.
-/

@[expose] public section

namespace PionCompleteness.Pi

open Finset PionCompleteness.TreeRectangleZero PionCompleteness.ChainSlice
  PionCompleteness.PionZeros PionCompleteness.PionNLSM
/-- For `1 ≤ p` and `p + 3 ≤ n`, the rotated B-child labelling `relab n (p + 3) ∘ rot^[n − 2 − p]`
sends every odd chord of the `(n − 2)`-gon to an odd chord of the `n`-gon other than
`C = (p, p + 3)`. -/
theorem pkR_rotB_odd {n p : ℕ} (hp : 1 ≤ p) (hpn : p + 3 ≤ n) {d : ℕ × ℕ}
    (hd : d ∈ oddDiagonals (n - 2)) :
    relab n (p + 3) ((rot (n - 2))^[n - 2 - p] d) ∈ oddDiagonals n ∧
      relab n (p + 3) ((rot (n - 2))^[n - 2 - p] d) ≠ (p, p + 3) := by
  obtain ⟨a, b⟩ := d
  have hdd := mem_filter.1 hd
  have h1 := mem_diagonals.1 hdd.1
  have h2 := hdd.2
  dsimp only at h1 h2
  rw [pkR_rot_iter (by omega) _ (a, b) hdd.1]
  dsimp only
  rw [pkR_rotB_pair hp hpn hdd.1]
  obtain ⟨fa, hfa⟩ : ∃ fa, fa = (if a ≤ p then a else a + 2) := ⟨_, rfl⟩
  obtain ⟨fb, hfb⟩ : ∃ fb, fb = (if b ≤ p then b else b + 2) := ⟨_, rfl⟩
  have hfa' : (a ≤ p ∧ fa = a) ∨ (p < a ∧ fa = a + 2) := by rw [hfa]; split_ifs <;> omega
  have hfb' : (b ≤ p ∧ fb = b) ∨ (p < b ∧ fb = b + 2) := by rw [hfb]; split_ifs <;> omega
  rw [← hfa, ← hfb]
  refine ⟨mem_filter.2 ⟨mem_diagonals.2 ?_, ?_⟩, fun e => ?_⟩
  · dsimp only
    omega
  · dsimp only
    omega
  · rw [Prod.mk.injEq] at e
    omega

/-- `Λ^I` (`pkRLam`, `C6`) depends only on the values at the diagonals: if `Y` and `Y′` agree on
`diagonals m` and `Y′` is on `Λ^I`, so is `Y` (`Λ^I` is a list of conditions on mesh variables). -/
theorem pkR_lam_congrD {m d₁ : ℕ} {I : Finset (ℕ × ℕ)} {Y Y' : ℕ × ℕ → ℚ}
    (h : ∀ d ∈ diagonals m, Y d = Y' d)
    (hY' : pkRLam m d₁ I Y') : pkRLam m d₁ I Y := by
  obtain ⟨h1, h2, h3⟩ := (pkR_lam_iff _ _ _ _).1 hY'
  refine (pkR_lam_iff _ _ _ _).2 ⟨fun a ha b hb e1 e2 e3 e4 => ?_, ?_, fun Q hQ t ht => ?_⟩
  · rw [pkR_mesh_congrD h]
    exact h1 a ha b hb e1 e2 e3 e4
  · rw [pkR_mesh_congrD h, pkR_mesh_congrD h (pkRCstp m d₁).1]
    exact h2
  · rw [pkR_mesh_congrD h]
    exact h3 Q hQ t ht

/-- `Λ^I ⊆ Λ`: a point of `Λ^I` is on `Λ = Λ^∅`. -/
theorem pkR_lam_mono {n d₁ : ℕ} {I : Finset (ℕ × ℕ)} {X : ℕ × ℕ → ℚ} (hX : pkRLam n d₁ I X) :
    pkRLam n d₁ ∅ X := by
  obtain ⟨h1, h2, _⟩ := (pkR_lam_iff _ _ _ _).1 hX
  exact (pkR_lam_iff _ _ _ _).2 ⟨h1, h2, fun Q hQ => by simp at hQ⟩

/-- **The 4-gon A-child in numerator form**: for an odd chord `C = (p, p + 3)` of the `n`-gon, if
`X_{p,p+2} + X_{p+1,p+3} = X_{p,p+3}` at `X` (the relation of `pkR_R10i` and `pkR_R10i_mirror`,
`C6`), the numerator of the A-child of `C`, `rename (relab n p) (NP ℚ 4)`, is `−X_C` at `X`. -/
theorem pkR_R10_Ag {n p : ℕ} (hQ : ((p, p + 3) : ℕ × ℕ) ∈ oddDiagonals n) {X : ℕ × ℕ → ℚ}
    (h : planar n X p (p + 2) + planar n X (p + 1) (p + 3) = planar n X p (p + 3)) :
    MvPolynomial.eval X (MvPolynomial.rename (relab n p) (NP ℚ (p + 3 - p + 1))) =
        -X (p, p + 3) := by
  have hQd := mem_diagonals.1 (mem_filter.1 hQ).1
  dsimp only at hQd
  have h4 : p + 3 - p + 1 = 4 := by omega
  have e1 : X (relab n p (1, 3)) = planar n X p (p + 2) := by
    rw [← pkR_relab1 hQ X (1, 3) (by rw [h4]; decide)]
    change planar n X (1 + p - 1) (3 + p - 1) = _
    rw [show 1 + p - 1 = p by omega, show 3 + p - 1 = p + 2 by omega]
  have e2 : X (relab n p (2, 4)) = planar n X (p + 1) (p + 3) := by
    rw [← pkR_relab1 hQ X (2, 4) (by rw [h4]; decide)]
    change planar n X (2 + p - 1) (4 + p - 1) = _
    rw [show 2 + p - 1 = p + 1 by omega, show 4 + p - 1 = p + 3 by omega]
  have eC : planar n X p (p + 3) = X (p, p + 3) := by
    rw [planar_of_mem X (by omega) (by omega) (by omega)]
    exact ite_eq_left (mem_filter.1 hQ).1
  rw [h4, MvPolynomial.eval_rename, pkR_NP4, Function.comp_apply, Function.comp_apply,
      e1, e2, h, eC]

/-! ### The induction step for the constant of the standard polygon

For a member `q` whose chord is `(p, p + 3)`, the points of `W_q` with `c⋆ = 0` or `c⋆′ = 0` lie on
the locus `Z′` (`pkRZ5c`, a copy of `pkRBZ5` below). With this, one step `(n, d₁) → (n − 2, d₁′)`
shows that the constant `c` of the data of `pkR_const9` (`C7`) is non-zero when the constant of the
smaller polygon is (`pkR_psi_step`). -/

/-- The locus `Z′` with the same body as `pkRBZ5` (defined below; the two are definitionally
equal): for a parity `ε`, a set of legs `R` and a set `K` of chords, the points at which the mesh
variables of the pairs (z1)–(z3) of `pkRBZ5` vanish. The statements of this section and of `C9`
that use `Z′` are stated with this copy. -/
def pkRZ5c (n ε : ℕ) (R : Finset ℕ) (K : Finset (ℕ × ℕ)) (X : ℕ × ℕ → ℚ) : Prop :=
  (∀ a ∈ Icc 1 n, ∀ b ∈ Icc 1 n, a % 2 = ε → a ∉ R → b % 2 = ε → b ∉ R → mesh n X a b = 0) ∧
  (∀ a ∈ Icc 1 n, a % 2 = ε → a ∉ R → ∀ w ∈ R, mesh n X a w = 0) ∧
  (∀ Q ∈ K, ∀ w ∈ Icc 1 n, ∀ a ∈ Icc 1 n, w % 2 ≠ ε → a % 2 = ε → a ∉ R →
    (∀ r ∈ R, (Q.1 ≤ w ∧ w < Q.2 ↔ Q.1 ≤ r ∧ r < Q.2)) →
        (∀ r ∈ R, ¬ (Q.1 ≤ a ∧ a < Q.2 ↔ Q.1 ≤ r ∧ r < Q.2)) →
    mesh n X w a = 0)

/-- For `i ≤ d₁` and `2d₁ + 2j + 2 ≤ n` (`n` even, `n ≥ 4`) with `pkRMchord d₁ (i, j)` the chord
`C = (p, p + 3)` of `q = (i, j)`, a point of `W_q` with `c⋆ = 0` lies on
`pkRZ5c n (p % 2) [p, p + 2] {C}` (the run `R = A_q`), by `pkR_R14a` (`C6`). -/
theorem pkR_R14_Z5a {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ i j p : ℕ} (hi : i ≤ d₁)
    (hj : 2 * d₁ + 2 * j + 2 ≤ n) (hC : pkRMchord d₁ (i, j) = (p, p + 3)) {X : ℕ × ℕ → ℚ}
    (hW : pkRW n d₁ (i, j) X) (hx : mesh n X 1 (n - 1) = 0) :
    pkRZ5c n (p % 2) (Icc p (p + 2)) {(p, p + 3)} X := by
  have e1 : 2 * i + 1 = p := congrArg Prod.fst hC
  have e2 : 2 * d₁ + 2 * j + 2 = p + 3 := congrArg Prod.snd hC
  have R := pkR_R14a hE hn hi hj hW hx
  refine ⟨fun a ha b hb h1 h2 h3 h4 => ?_, fun a ha h1 h2 w hw => ?_,
      fun Q hQ w hw a ha h1 h2 h3 h4 _ => ?_⟩
  · rw [mem_Icc] at h2 h4
    by_cases hab : a = b
    · rw [hab]
      exact pkR_mesh_self (by omega) X b
    · exact R a ha b hb (by omega) (by omega) (Or.inl (by omega)) (Ne.symm hab)
  · rw [mem_Icc] at h2 hw
    have ha' := mem_Icc.1 ha
    exact R a ha w (mem_Icc.2 ⟨by omega, by omega⟩) (by omega) (by omega)
        (Or.inr (by omega)) (by omega)
  · rw [mem_singleton] at hQ
    subst hQ
    dsimp only at h4
    have hw' := (h4 p (mem_Icc.2 ⟨le_rfl, by omega⟩)).2 ⟨le_rfl, by omega⟩
    rw [mem_Icc] at h3
    rw [pkR_mesh_comm]
    exact R a ha w hw (by omega) (by omega) (Or.inr (by omega)) (by omega)

/-- In the setting of `pkR_R14_Z5a`, a point of `W_q` with `c⋆′ = 0` lies on
`pkRZ5c n ((p + 3) % 2) ([1, n] ∖ [p, p + 2]) {C}` (the run `R = B_q`), by `pkR_R14b` (`C6`). -/
theorem pkR_R14_Z5b {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ i j p : ℕ} (hi : i ≤ d₁)
    (hj : 2 * d₁ + 2 * j + 2 ≤ n) (hC : pkRMchord d₁ (i, j) = (p, p + 3)) {X : ℕ × ℕ → ℚ}
    (hW : pkRW n d₁ (i, j) X) (hy : mesh n X (pkRCstp n d₁).1 (pkRCstp n d₁).2 = 0) :
    pkRZ5c n ((p + 3) % 2) ((Icc 1 n).filter (fun c => c < p ∨ p + 2 < c)) {(p, p + 3)} X := by
  have e1 : 2 * i + 1 = p := congrArg Prod.fst hC
  have e2 : 2 * d₁ + 2 * j + 2 = p + 3 := congrArg Prod.snd hC
  have R := pkR_R14b hE hn hi hj hW hy
  refine ⟨fun a ha b hb h1 h2 h3 h4 => ?_, fun a ha h1 h2 w hw => ?_,
      fun Q hQ w hw a ha h1 h2 h3 h4 _ => ?_⟩
  · have ha' := mem_Icc.1 ha
    simp only [mem_filter, mem_Icc] at h2
    by_cases hab : a = b
    · rw [hab]
      exact pkR_mesh_self (by omega) X b
    · exact R a ha b hb (by omega) (by omega) (Or.inl (by omega)) (Ne.symm hab)
  · have ha' := mem_Icc.1 ha
    simp only [mem_filter, mem_Icc] at h2 hw
    exact R a ha w (mem_Icc.2 ⟨by omega, by omega⟩) (by omega) (by omega)
        (Or.inr (by omega)) (by omega)
  · rw [mem_singleton] at hQ
    subst hQ
    have ha' := mem_Icc.1 ha
    have hw1 := mem_Icc.1 hw
    have hr : p + 3 ∈ (Icc 1 n).filter (fun c => c < p ∨ p + 2 < c) :=
      mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, Or.inr (by omega)⟩
    have hw' := h4 (p + 3) hr
    dsimp only at hw'
    simp only [mem_filter, mem_Icc] at h3
    rw [pkR_mesh_comm]
    have hwo : ¬ (p ≤ w ∧ w < p + 3) := fun hh => by have := hw'.1 hh; omega
    exact R a ha w hw (by omega) (by omega) (Or.inr (by omega)) (by omega)

/-- **One induction step for the constant**. Let `q = (i, j)` be a member of the standard polygon
`(n, d₁)` (`n` even, `n ≥ 6`, `2d₁ + 2 ≤ n`) with chord `C = (p, p + 3)`. Let `(F₁, c)` be data at
`(n, d₁)` (`NP_n = x · F₁` on `Λ` and `F₁ = c · oddDen_n` on `Λ₀ = Λ ∩ {x = 0}`, as in `pkR_const9`,
`C7`) and `(F₁′, c′)` data at `(n − 2, d₁′)`. Then `c′ ≠ 0` implies `c ≠ 0`, given: the 4-gon
relation `X_{p,p+2} + X_{p+1,p+3} = X_{p,p+3}` on `Λ` (`hA`); for every point of `Λ^{q}`, the region
point of the B-child of `C` is on `Λ` of the standard polygon `(n − 2, d₁′)`, with the same `x`
(`hreg`, read through the rotation bridge `pkR_rotB_eval`, `C7`); a point of `Λ^{q}` with `x ≠ 0`
(`wx`); and for every odd chord `Q ≠ C` a point of `Λ^{q}` with `x = 0` and `X_Q ≠ 0` (`hGI`). The
hypotheses `hR5two`, `hR5one` are the statements of `pkR_b_R5one2`, `pkR_b_R5one1` (below), with
`pkRBZ5` spelled `pkRZ5c`; `pkR_omega` (`C9`) instantiates them with these two lemmas. -/
theorem pkR_psi_step {n : ℕ} (hE : n % 2 = 0) (hn : 6 ≤ n) {d₁ d₁' i j p : ℕ} (hd : 2 * d₁ + 2 ≤ n)
    (hi : i ≤ d₁) (hj : 2 * d₁ + 2 * j + 2 ≤ n) (hb : ¬ (i = d₁ ∧ j = 0))
    (ha : ¬ (i = 0 ∧ 2 * d₁ + 2 * j + 2 = n)) (hC : pkRMchord d₁ (i, j) = (p, p + 3))
    (hA : ∀ X : ℕ × ℕ → ℚ, pkRLam n d₁ ∅ X →
      planar n X p (p + 2) + planar n X (p + 1) (p + 3) = planar n X p (p + 3))
    (hreg : ∀ X : ℕ × ℕ → ℚ, pkRLam n d₁ {(i, j)} X →
      pkRLam (n - 2) d₁' ∅ (pkRSubX n (fun k => if k ≤ p then k else k + 2) X) ∧
        mesh (n - 2) (pkRSubX n (fun k => if k ≤ p then k else k + 2) X) 1 (n - 2 - 1) =
            mesh n X 1 (n - 1))
    (wx : ∃ w : ℕ × ℕ → ℚ, pkRLam n d₁ {(i, j)} w ∧ mesh n w 1 (n - 1) ≠ 0)
    (hGI : ∀ Q ∈ oddDiagonals n, Q ≠ (p, p + 3) →
      ∃ X : ℕ × ℕ → ℚ, pkRLam n d₁ {(i, j)} X ∧ mesh n X 1 (n - 1) = 0 ∧ X Q ≠ 0)
    (hR5two : ∀ {n : ℕ}, n % 2 = 0 → 4 ≤ n → ∀ {p q lo hi : ℕ}, (p, q) ∈ oddDiagonals n → p ≤
        lo → lo ≤ hi →
      hi < q → lo % 2 = p % 2 → ∀ X ∈ {X : ℕ × ℕ → ℚ | pkRZ5c n (p % 2) (Icc lo hi) {(p, q)} X},
        MvPolynomial.eval X (pkRBNP ℚ n {(p, q)}) = 0)
    (hR5one : ∀ {n : ℕ}, n % 2 = 0 → 4 ≤ n → ∀ {p q lo hi : ℕ}, (p, q) ∈ oddDiagonals n → lo ≤ p →
      q ≤ hi + 1 → ∀ {r₀ : ℕ}, r₀ ∈ (Icc 1 n).filter (fun c => c < lo ∨ hi < c) → r₀ % 2 = q % 2 →
        ∀ X ∈ {X : ℕ × ℕ → ℚ | pkRZ5c n (q % 2) ((Icc 1 n).filter (fun c => c < lo ∨ hi < c))
            {(p, q)} X},
          MvPolynomial.eval X (pkRBNP ℚ n {(p, q)}) = 0)
    {F₁ : MvPolynomial (ℕ × ℕ) ℚ} {c : ℚ}
    (hF : ∀ X : ℕ × ℕ → ℚ, pkRLam n d₁ ∅ X →
      MvPolynomial.eval X (NP ℚ n) = mesh n X 1 (n - 1) * MvPolynomial.eval X F₁)
    (hc : ∀ X : ℕ × ℕ → ℚ, pkRLam n d₁ ∅ X → mesh n X 1 (n - 1) = 0 →
      MvPolynomial.eval X F₁ = c * MvPolynomial.eval X (oddDen ℚ n))
    {F₁' : MvPolynomial (ℕ × ℕ) ℚ} {c' : ℚ}
    (hF' : ∀ X : ℕ × ℕ → ℚ, pkRLam (n - 2) d₁' ∅ X →
      MvPolynomial.eval X (NP ℚ (n - 2)) = mesh (n - 2) X 1 (n - 2 - 1) * MvPolynomial.eval X F₁')
    (hc' : ∀ X : ℕ × ℕ → ℚ, pkRLam (n - 2) d₁' ∅ X → mesh (n - 2) X 1 (n - 2 - 1) = 0 →
      MvPolynomial.eval X F₁' = c' * MvPolynomial.eval X (oddDen ℚ (n - 2)))
    (hc0 : c' ≠ 0) : c ≠ 0 := by
  have e1 : 2 * i + 1 = p := congrArg Prod.fst hC
  have e2 : 2 * d₁ + 2 * j + 2 = p + 3 := congrArg Prod.snd hC
  have hQC : ((p, p + 3) : ℕ × ℕ) ∈ oddDiagonals n := hC ▸ pkR_mchord_mem hi hj hb ha
  have hp1 : 1 ≤ p := by omega
  have hpn : p + 3 ≤ n := by
    have hQd := mem_diagonals.1 (mem_filter.1 hQC).1
    dsimp only at hQd
    omega
  -- the rotated B-child point `X ∘ H` lies on the child's `Λ` with the same `x`
  have hZ : ∀ X : ℕ × ℕ → ℚ, pkRLam n d₁ {(i, j)} X →
      pkRLam (n - 2) d₁' ∅ (X ∘ (relab n (p + 3) ∘ (rot (n - 2))^[n - 2 - p])) ∧
        mesh (n - 2) (X ∘ (relab n (p + 3) ∘ (rot (n - 2))^[n - 2 - p])) 1 (n - 2 - 1) =
            mesh n X 1 (n - 1) := by
    intro X hX
    obtain ⟨h1, h2⟩ := hreg X hX
    refine ⟨pkR_lam_congrD (pkR_rotB_eval hp1 hpn X) h1, ?_⟩
    rw [pkR_mesh_congrD (pkR_rotB_eval hp1 hpn X)]
    exact h2
  -- the B-child numerator is `x · F₁′`
  have hB : ∀ X : ℕ × ℕ → ℚ, pkRLam n d₁ {(i, j)} X →
      MvPolynomial.eval X (MvPolynomial.rename (relab n (p + 3)) (NP ℚ (n - (p + 3) + p + 1))) =
        mesh n X 1 (n - 1) *
          MvPolynomial.eval X (MvPolynomial.rename (relab n (p + 3) ∘
              (rot (n - 2))^[n - 2 - p]) F₁') := by
    intro X hX
    obtain ⟨hl, hx⟩ := hZ X hX
    have e := hF' _ hl
    rw [hx] at e
    rw [MvPolynomial.eval_rename, MvPolynomial.eval_rename, show n - (p + 3) + p + 1 = n -
        2 by omega, ← e,
      ← pkR_NP_rotk (m := n - 2) (by omega) (by omega) (n - 2 - p) (X ∘ relab n (p + 3)),
          Function.comp_assoc]
  -- the ¬C numerator is `x² · F₃` on `Λ^{q}`
  obtain ⟨F₃, hF₃⟩ := pkR_R10iii hE (by omega) hi hj hb ha (pkRBNP ℚ n {(p, p + 3)})
    (fun X hW hx => @hR5two n hE (by omega) p (p + 3) p (p + 2) hQC le_rfl (by omega)
        (by omega) rfl X
      (pkR_R14_Z5a hE (by omega) hi hj hC hW hx))
    (fun X hW hy => @hR5one n hE (by omega) p (p + 3) p (p + 2) hQC le_rfl (by omega) (p + 3)
      (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, Or.inr (by omega)⟩) rfl X
      (pkR_R14_Z5b hE (by omega) hi hj hC hW hy))
  have core := pkR_psi_core (V := {X | pkRLam n d₁ ∅ X}) (V₂ := {X | pkRLam n d₁ {(i, j)} X})
    (pkR_lam_sub n d₁ ∅) (pkR_lam_sub n d₁ {(i, j)}) (fun X hX => pkR_lam_mono hX)
        (pkR_meshP_lin n 1 (n - 1))
    (ℓ := MvPolynomial.X (p, p + 3)) (NPn := NP ℚ n)
    (M := pkRBNP ℚ n {(p, p + 3)} -
      MvPolynomial.rename (relab n (p + 3)) (NP ℚ (n - (p + 3) + p + 1)) * crossProd ℚ n (p, p + 3))
    (F₁ := F₁) (D := Finset.prod ((oddDiagonals n).erase (p, p + 3))
        (fun d => MvPolynomial.X d)) (F₃ := F₃)
    (F₁' := MvPolynomial.rename (relab n (p + 3) ∘ (rot (n - 2))^[n - 2 - p]) F₁')
    (D' := MvPolynomial.rename (relab n (p + 3) ∘ (rot (n - 2))^[n - 2 - p]) (oddDen ℚ (n - 2)))
    (cr := crossProd ℚ n (p, p + 3)) (c := c) (c' := c')
    (fun X hX => by
      have hX' : pkRLam n d₁ ∅ X := hX
      have e0 : NP ℚ n = MvPolynomial.X (p, p + 3) * pkRBNP ℚ n {(p, p + 3)} +
          MvPolynomial.rename (relab n p) (NP ℚ (p + 3 - p + 1)) *
            MvPolynomial.rename (relab n (p + 3))
                (NP ℚ (n - (p + 3) + p + 1)) * crossProd ℚ n (p, p + 3) :=
        pkR_b_res1 (R := ℚ) (show 4 ≤ n by omega) hE hQC
      have e := congrArg (MvPolynomial.eval X) e0
      rw [map_add, map_mul, map_mul, map_mul, MvPolynomial.eval_X, pkR_R10_Ag hQC (hA X hX')] at e
      rw [e, map_sub, map_mul, MvPolynomial.eval_X]
      ring)
    (fun X hX => by rw [pkR_meshP_eval]; exact hF X hX)
    (fun X hX hx0 => by
      have hX' : pkRLam n d₁ ∅ X := hX
      rw [pkR_meshP_eval] at hx0
      rw [hc X hX' hx0, pkR_eval_oddDen, map_prod, ← Finset.mul_prod_erase (oddDiagonals n)
          (fun d => X d) hQC]
      simp only [MvPolynomial.eval_X])
    (fun X hX => by
      have hX' : pkRLam n d₁ {(i, j)} X := hX
      rw [map_sub, map_mul, hF₃ X hX', hB X hX', pkR_meshP_eval]
      ring)
    (fun X hX hx0 => by
      have hX' : pkRLam n d₁ {(i, j)} X := hX
      obtain ⟨hl, hxx⟩ := hZ X hX'
      rw [pkR_meshP_eval] at hx0
      rw [MvPolynomial.eval_rename, MvPolynomial.eval_rename]
      exact hc' _ hl (by rw [hxx, hx0]))
    (by
      obtain ⟨w, hw, hwx⟩ := wx
      exact ⟨w, hw, by rw [pkR_meshP_eval]; exact hwx⟩)
    (by
      obtain ⟨Y, hY, hYx, hYQ⟩ := pkR_G hE (by omega) d₁ hd hQC
      exact ⟨Y, hY, by rw [pkR_meshP_eval]; exact hYx, by rw [MvPolynomial.eval_X]; exact hYQ⟩)
  refine pkR_psi_ne core ?_ hc0
  obtain ⟨w, ⟨hwV, hwx⟩, hw⟩ := pkR_avoid_aux
    (pkR_sub_inter (pkR_lam_sub n d₁ {(i, j)}) (pkR_meshP_lin n 1 (n - 1)))
    (fun Q => (MvPolynomial.X Q : MvPolynomial (ℕ × ℕ) ℚ)) ((oddDiagonals n).erase (p, p + 3))
    (fun Q hQ => by
      obtain ⟨hne, hQ'⟩ := mem_erase.1 hQ
      obtain ⟨Y, hY, hYx, hYQ⟩ := hGI Q hQ' hne
      exact ⟨Y, ⟨hY, by rw [pkR_meshP_eval]; exact hYx⟩, by rw [MvPolynomial.eval_X]; exact hYQ⟩)
  rw [map_prod] at hw
  simp only [MvPolynomial.eval_X] at hw
  have hall : ∀ Q ∈ oddDiagonals n, Q ≠ (p, p + 3) → w Q ≠ 0 := fun Q hQ hne =>
    (Finset.prod_ne_zero_iff.1 hw) Q (mem_erase.2 ⟨hne, hQ⟩)
  refine ⟨w, hwV, hwx, mul_ne_zero ?_ ?_⟩
  · rw [MvPolynomial.eval_rename, pkR_eval_oddDen]
    refine Finset.prod_ne_zero_iff.2 (fun d hd => ?_)
    obtain ⟨o1, o2⟩ := pkR_rotB_odd hp1 hpn hd
    exact hall _ o1 o2
  · unfold crossProd
    rw [map_prod]
    refine Finset.prod_ne_zero_iff.2 (fun d hd => ?_)
    rw [MvPolynomial.eval_X]
    obtain ⟨hd1, hcr⟩ := mem_filter.1 hd
    refine hall d hd1 (fun e => ?_)
    subst e
    simp [Crosses] at hcr

/-! ### The two routes of the induction step, and the induction

The step `(n, d₁) → (n − 2, ·)` goes through the member `b′ = (d₁ − 1, 0)` when `d₂ = 0`
(`2d₁ + 2 = n`), and through `b″ = (d₁, 1)` when `d₂ ≥ 1`, `d₂ = n/2 − 1 − d₁`; for each, the
witnesses of `x ≢ 0` on `Λ^{b′}`, `Λ^{b″}` and the regions. The induction on `n` (`pkR_psi_all`)
shows that the constant is non-zero on every standard polygon. -/

/-- On the standard polygon `(n, d₁)` (`n ≥ 4`, `2d₁ + 2 ≤ n`), a point `P` whose mesh variables at
distinct legs are the entries of a matrix `C` lies on `Λ^{q}` with `x = 1` when the only non-zero
same-parity entries `C a b` (`a + 2 ≤ b`) are `c⋆ = C 1 (n − 1) = 1` and `c⋆′ = 1` (at `pkRCstp`),
and `C` vanishes on the pairs of `minrect(q)`. -/
theorem pkR_lam_ofC {n d₁ : ℕ} (hn : 4 ≤ n) (hd : 2 * d₁ + 2 ≤ n) (q : ℕ × ℕ) {P : ℕ × ℕ → ℚ}
    {C : ℕ → ℕ → ℚ} (hPC : ∀ a ∈ Icc 1 n, ∀ b ∈ Icc 1 n, a ≠ b → mesh n P a b = C a b)
    (h1 : ∀ a b : ℕ, 1 ≤ a → a + 2 ≤ b → b ≤ n → a % 2 = b % 2 → ¬ (a = 1 ∧ b = n - 1) →
      ¬ (a = (pkRCstp n d₁).1 ∧ b = (pkRCstp n d₁).2) → C a b = 0)
    (h2 : C 1 (n - 1) = 1) (h3 : C (pkRCstp n d₁).1 (pkRCstp n d₁).2 = 1)
    (h4 : ∀ w c : ℕ, 1 ≤ w → w ≤ n → w % 2 = 1 → w ≠ 2 * d₁ + 1 →
      ¬ (2 * q.1 + 1 ≤ w ∧ w ≤ 2 * d₁ + 2 * q.2 + 1) → 1 ≤ c → c ≤ n → c % 2 = 0 → c ≠ n →
        (2 * q.1 + 1 ≤ c ∧ c ≤ 2 * d₁ + 2 * q.2 + 1) → C w c = 0) :
    pkRLam n d₁ {q} P ∧ mesh n P 1 (n - 1) = 1 := by
  have hcs : 1 ≤ (pkRCstp n d₁).1 ∧ (pkRCstp n d₁).1 + 2 ≤ (pkRCstp n d₁).2 ∧
      (pkRCstp n d₁).2 ≤ n := by
    unfold pkRCstp
    split_ifs <;> dsimp only <;> omega
  have hx : mesh n P 1 (n - 1) = 1 := by
    rw [hPC 1 (mem_Icc.2 ⟨le_rfl, by omega⟩) (n - 1) (mem_Icc.2 ⟨by omega, by omega⟩)
        (by omega), h2]
  refine ⟨(pkR_lam_iff _ _ _ _).2 ⟨fun a ha b hb hab hp hne1 hne2 => ?_, ?_,
      fun Q hQ t ht => ?_⟩, hx⟩
  · have ha' := mem_Icc.1 ha
    have hb' := mem_Icc.1 hb
    rw [hPC a ha b hb (by omega)]
    exact h1 a b ha'.1 hab hb'.2 hp (pkR_ne_pair hne1) (fun e => hne2 (Prod.ext e.1 e.2))
  · rw [hx, hPC _ (mem_Icc.2 ⟨hcs.1, by omega⟩) _ (mem_Icc.2 ⟨by omega, hcs.2.2⟩) (by omega), h3]
  · rw [mem_singleton] at hQ
    subst hQ
    obtain ⟨⟨hw, hw1, hw2, hw3⟩, ⟨hc, hc1, hc2, hc3⟩⟩ := (pkR_mem_minrect _ _ _ _).1 ht
    rw [pkR_mem_head] at hw3 hc3
    have hw' := mem_Icc.1 hw
    have hc' := mem_Icc.1 hc
    rw [hPC _ hw _ hc (by omega)]
    exact h4 _ _ hw'.1 hw'.2 hw1 hw2 hw3 hc'.1 hc'.2 hc1 hc2 hc3

/-- The four-entry matrix `pkRW1 e1 e2 t1 t2` (`C6`) is `0` at a pair `(a, b)` that is none of
`{e1, e2}`, `{t1, t2}`, `{e1, t1}`, `{e2, t2}`; `pkR_w1_o1`, `pkR_w1_o2` and `pkR_w1_m3` give its
values `1`, `1` and `−1` at the first three of them. -/
theorem pkR_w1_z {e1 e2 t1 t2 a b : ℕ} (h1 : ¬ ((a = e1 ∧ b = e2) ∨ (a = e2 ∧ b = e1)))
    (h2 : ¬ ((a = t1 ∧ b = t2) ∨ (a = t2 ∧ b = t1)))
    (h3 : ¬ ((a = e1 ∧ b = t1) ∨ (a = t1 ∧ b = e1)))
    (h4 : ¬ ((a = e2 ∧ b = t2) ∨ (a = t2 ∧ b = e2))) : pkRW1 e1 e2 t1 t2 a b = 0 := by
  rw [pkR_w1_def, pkR_E_zero h1, pkR_E_zero h2, pkR_E_zero h3, pkR_E_zero h4]
  norm_num

theorem pkR_w1_o1 {e1 e2 t1 t2 a b : ℕ} (h1 : (a = e1 ∧ b = e2) ∨ (a = e2 ∧ b = e1))
    (h2 : ¬ ((a = t1 ∧ b = t2) ∨ (a = t2 ∧ b = t1)))
    (h3 : ¬ ((a = e1 ∧ b = t1) ∨ (a = t1 ∧ b = e1)))
    (h4 : ¬ ((a = e2 ∧ b = t2) ∨ (a = t2 ∧ b = e2))) : pkRW1 e1 e2 t1 t2 a b = 1 := by
  rw [pkR_w1_def, pkR_E_one h1, pkR_E_zero h2, pkR_E_zero h3, pkR_E_zero h4]
  norm_num

theorem pkR_w1_o2 {e1 e2 t1 t2 a b : ℕ} (h1 : ¬ ((a = e1 ∧ b = e2) ∨ (a = e2 ∧ b = e1)))
    (h2 : (a = t1 ∧ b = t2) ∨ (a = t2 ∧ b = t1)) (h3 : ¬ ((a = e1 ∧ b = t1) ∨ (a = t1 ∧ b = e1)))
    (h4 : ¬ ((a = e2 ∧ b = t2) ∨ (a = t2 ∧ b = e2))) : pkRW1 e1 e2 t1 t2 a b = 1 := by
  rw [pkR_w1_def, pkR_E_zero h1, pkR_E_one h2, pkR_E_zero h3, pkR_E_zero h4]
  norm_num

theorem pkR_w1_m3 {e1 e2 t1 t2 a b : ℕ} (h1 : ¬ ((a = e1 ∧ b = e2) ∨ (a = e2 ∧ b = e1)))
    (h2 : ¬ ((a = t1 ∧ b = t2) ∨ (a = t2 ∧ b = t1))) (h3 : (a = e1 ∧ b = t1) ∨ (a = t1 ∧ b = e1))
    (h4 : ¬ ((a = e2 ∧ b = t2) ∨ (a = t2 ∧ b = e2))) : pkRW1 e1 e2 t1 t2 a b = -1 := by
  rw [pkR_w1_def, pkR_E_zero h1, pkR_E_zero h2, pkR_E_one h3, pkR_E_zero h4]
  norm_num

/-- `x ≢ 0` on `Λ^{b′}`, `b′ = (d₁ − 1, 0)`, for `n ≥ 6` and `2d₁ + 2 = n` (`d₂ = 0`). The witness
is the Gram point of `E(1, n−1) + E(n, n−2) − E(1, n) − E(n−1, n−2)`, with `x = 1`. -/
theorem pkR_wxA {n d₁ : ℕ} (hn : 6 ≤ n) (hd2 : 2 * d₁ + 2 = n) :
    ∃ w : ℕ × ℕ → ℚ, pkRLam n d₁ {(d₁ - 1, 0)} w ∧ mesh n w 1 (n - 1) ≠ 0 := by
  have ec : pkRCstp n d₁ = (2 * d₁, 2 * d₁ + 2) := ite_eq_right (by omega)
  have i1 : 1 ∈ Icc 1 n := mem_Icc.2 ⟨le_rfl, by omega⟩
  have i2 : n - 1 ∈ Icc 1 n := mem_Icc.2 ⟨by omega, by omega⟩
  have i3 : n ∈ Icc 1 n := mem_Icc.2 ⟨by omega, le_rfl⟩
  have i4 : n - 2 ∈ Icc 1 n := mem_Icc.2 ⟨by omega, by omega⟩
  obtain ⟨h, hx⟩ := pkR_lam_ofC (n := n) (d₁ := d₁) (by omega) (by omega) (d₁ - 1, 0)
    (P := pkRGramPt (pkRW1 1 (n - 1) n (n - 2))) (C := pkRW1 1 (n - 1) n (n - 2))
    (fun a ha b hb hab => pkR_w1_gram (by omega) i1 i2 i3 i4 (by omega) (by omega) (by omega)
        (by omega) ha hb hab)
    (fun a b h1 h2 h3 h4 h5 h6 => by
      rw [ec] at h6
      dsimp only at h6
      exact pkR_w1_z (by omega) (by omega) (by omega) (by omega))
    (pkR_w1_o1 (by omega) (by omega) (by omega) (by omega))
    (by rw [ec]; exact pkR_w1_o2 (by omega) (by omega) (by omega) (by omega))
    (fun w c h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => by
      dsimp only at h5 h10
      exact pkR_w1_z (by omega) (by omega) (by omega) (by omega))
  exact ⟨_, h, by rw [hx]; norm_num⟩

/-- `x ≢ 0` on `Λ^{b″}` for `d₁ = 0` (`b″ = (0, 1)`) and even `n ≥ 6`. The witness is the Gram point
of `E(1, n−1) + E(2, n) − E(1, 2) − E(n−1, n)`, with `x = 1`. -/
theorem pkR_wxB {n : ℕ} (hE : n % 2 = 0) (hn : 6 ≤ n) :
    ∃ w : ℕ × ℕ → ℚ, pkRLam n 0 {(0, 1)} w ∧ mesh n w 1 (n - 1) ≠ 0 := by
  have ec : pkRCstp n 0 = (2, n) := ite_eq_left rfl
  have i1 : 1 ∈ Icc 1 n := mem_Icc.2 ⟨le_rfl, by omega⟩
  have i2 : n - 1 ∈ Icc 1 n := mem_Icc.2 ⟨by omega, by omega⟩
  have i3 : 2 ∈ Icc 1 n := mem_Icc.2 ⟨by omega, by omega⟩
  have i4 : n ∈ Icc 1 n := mem_Icc.2 ⟨by omega, le_rfl⟩
  obtain ⟨h, hx⟩ := pkR_lam_ofC (n := n) (d₁ := 0) (by omega) (by omega) (0, 1)
    (P := pkRGramPt (pkRW1 1 (n - 1) 2 n)) (C := pkRW1 1 (n - 1) 2 n)
    (fun a ha b hb hab => pkR_w1_gram (by omega) i1 i2 i3 i4 (by omega) (by omega) (by omega)
        (by omega) ha hb hab)
    (fun a b h1 h2 h3 h4 h5 h6 => by
      rw [ec] at h6
      dsimp only at h6
      exact pkR_w1_z (by omega) (by omega) (by omega) (by omega))
    (pkR_w1_o1 (by omega) (by omega) (by omega) (by omega))
    (by rw [ec]; exact pkR_w1_o2 (by omega) (by omega) (by omega) (by omega))
    (fun w c h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => by
      dsimp only at h5 h10
      exact pkR_w1_z (by omega) (by omega) (by omega) (by omega))
  exact ⟨_, h, by rw [hx]; norm_num⟩

/-- `x ≢ 0` on `Λ^{b″}` (`b″ = (d₁, 1)`) for even `n`, `d₁ ≥ 1` and `d₂ ≥ 1` (`2d₁ + 4 ≤ n`). The
witness is the sum of the Gram points of `E(1, n−1) + E(2d₁, n) − E(1, 2d₁) − E(n−1, n)` and
`E(2d₁, 2d₁+2) + E(n, r) − E(2d₁, n) − E(2d₁+2, r)`, `r = 2d₁ + 1`, with `x = 1`. -/
theorem pkR_wxC {n d₁ : ℕ} (hE : n % 2 = 0) (hd1 : 1 ≤ d₁) (hm : 2 * d₁ + 4 ≤ n) :
    ∃ w : ℕ × ℕ → ℚ, pkRLam n d₁ {(d₁, 1)} w ∧ mesh n w 1 (n - 1) ≠ 0 := by
  have ec : pkRCstp n d₁ = (2 * d₁, 2 * d₁ + 2) := ite_eq_right (by omega)
  have i1 : 1 ∈ Icc 1 n := mem_Icc.2 ⟨le_rfl, by omega⟩
  have i2 : n - 1 ∈ Icc 1 n := mem_Icc.2 ⟨by omega, by omega⟩
  have i3 : 2 * d₁ ∈ Icc 1 n := mem_Icc.2 ⟨by omega, by omega⟩
  have i4 : n ∈ Icc 1 n := mem_Icc.2 ⟨by omega, le_rfl⟩
  have i5 : 2 * d₁ + 2 ∈ Icc 1 n := mem_Icc.2 ⟨by omega, by omega⟩
  have i6 : 2 * d₁ + 1 ∈ Icc 1 n := mem_Icc.2 ⟨by omega, by omega⟩
  obtain ⟨h, hx⟩ := pkR_lam_ofC (n := n) (d₁ := d₁) (by omega) (by omega) (d₁, 1)
    (P := fun x => 1 * pkRGramPt (pkRW1 1 (n - 1) (2 * d₁) n) x +
      1 * pkRGramPt (pkRW1 (2 * d₁) (2 * d₁ + 2) n (2 * d₁ + 1)) x)
    (C := fun a b => pkRW1 1 (n - 1) (2 * d₁) n a b + pkRW1 (2 * d₁)
        (2 * d₁ + 2) n (2 * d₁ + 1) a b)
    (fun a ha b hb hab => by
      rw [pkR_mesh_comb, pkR_w1_gram (by omega) i1 i2 i3 i4 (by omega) (by omega) (by omega)
          (by omega) ha hb hab,
        pkR_w1_gram (by omega) i3 i5 i4 i6 (by omega) (by omega) (by omega) (by omega) ha hb hab]
      ring)
    (fun a b h1 h2 h3 h4 h5 h6 => by
      rw [ec] at h6
      dsimp only at h6
      show pkRW1 1 (n - 1) (2 * d₁) n a b + pkRW1 (2 * d₁) (2 * d₁ + 2) n (2 * d₁ + 1) a b = 0
      by_cases hs : a = 2 * d₁ ∧ b = n
      · rw [pkR_w1_o2 (by omega) (by omega) (by omega) (by omega),
          pkR_w1_m3 (by omega) (by omega) (by omega) (by omega)]
        norm_num
      · rw [pkR_w1_z (by omega) (by omega) (by omega) (by omega),
          pkR_w1_z (by omega) (by omega) (by omega) (by omega)]
        norm_num)
    (by
      show pkRW1 1 (n - 1) (2 * d₁) n 1 (n - 1) + pkRW1 (2 * d₁)
          (2 * d₁ + 2) n (2 * d₁ + 1) 1 (n - 1) = 1
      rw [pkR_w1_o1 (by omega) (by omega) (by omega) (by omega), pkR_w1_z (by omega) (by omega)
          (by omega) (by omega)]
      norm_num)
    (by
      rw [ec]
      change pkRW1 1 (n - 1) (2 * d₁) n (2 * d₁) (2 * d₁ + 2) +
        pkRW1 (2 * d₁) (2 * d₁ + 2) n (2 * d₁ + 1) (2 * d₁) (2 * d₁ + 2) = 1
      rw [pkR_w1_z (by omega) (by omega) (by omega) (by omega), pkR_w1_o1 (by omega) (by omega)
          (by omega) (by omega)]
      norm_num)
    (fun w c h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => by
      dsimp only at h5 h10
      show pkRW1 1 (n - 1) (2 * d₁) n w c + pkRW1 (2 * d₁) (2 * d₁ + 2) n (2 * d₁ + 1) w c = 0
      rw [pkR_w1_z (by omega) (by omega) (by omega) (by omega), pkR_w1_z (by omega) (by omega)
          (by omega) (by omega)]
      norm_num)
  exact ⟨_, h, by rw [hx]; norm_num⟩

/-- For `d₁ ≥ 1` (and `2d₁ + 2 ≤ n`), `{b′} = {(d₁ − 1, 0)}` is closed (`pkRClosed`, `C6`; a chain
`b ≺ b′ ≺ a`). -/
theorem pkR_closed_bp {n d₁ : ℕ} (hd1 : 1 ≤ d₁) (hd : 2 * d₁ + 2 ≤ n) :
    pkRClosed n d₁ {(d₁ - 1, 0)} := by
  intro Q1 h1 Q2 h2
  simp only [mem_insert, mem_singleton] at h1 h2 ⊢
  rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;>
      simp only [Prod.mk.injEq] <;> omega

/-- For `d₂ ≥ 1` (`2d₁ + 4 ≤ n`), `{b″} = {(d₁, 1)}` is closed (`pkRClosed`, `C6`; a chain
`b ≺ b″ ≺ a`). -/
theorem pkR_closed_mir {n d₁ : ℕ} (hm : 2 * d₁ + 4 ≤ n) : pkRClosed n d₁ {(d₁, 1)} := by
  intro Q1 h1 Q2 h2
  simp only [mem_insert, mem_singleton] at h1 h2 ⊢
  rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;>
      simp only [Prod.mk.injEq] <;> omega

/-- **The region `Ω(a, b″)` is a standard polygon**: for even `n ≥ 6` and `d₂ ≥ 1` (`2d₁ + 4 ≤ n`),
at a point of `Λ^{b″}`, `b″ = (d₁, 1)`, the region point of the list `f k = k` (`k ≤ 2d₁ + 1`),
`k + 2` (otherwise) is on `Λ` of the standard polygon `(n − 2, d₁)`, with the same `x`. -/
theorem pkR_reg_mir {n d₁ : ℕ} (hE : n % 2 = 0) (hn : 6 ≤ n) (hm : 2 * d₁ + 4 ≤ n) {X : ℕ × ℕ → ℚ}
    (hX : pkRLam n d₁ {(d₁, 1)} X) :
    pkRLam (n - 2) d₁ ∅ (pkRSubX n (fun k => if k ≤ 2 * d₁ + 1 then k else k + 2) X) ∧
      mesh (n - 2) (pkRSubX n (fun k => if k ≤ 2 * d₁ + 1 then k else k + 2) X) 1 (n - 2 - 1) =
        mesh n X 1 (n - 1) := by
  have H : pkRRG n d₁ 0 d₁ 1 ((n - 2 * d₁ - 4) / 2) :=
    (pkR_RG_iff _ _ _ _ _ _).2 ⟨hE, by omega, by omega, by omega, by omega⟩
  have hm2 : 2 * d₁ + 2 * ((n - 2 * d₁ - 4) / 2) + 2 = n - 2 := by omega
  have hf : pkRRgf d₁ 0 d₁ 1 = fun k => if k ≤ 2 * d₁ + 1 then k else k + 2 := by
    funext k
    rw [pkR_rgf_def]
    split_ifs <;> omega
  have hmy : ∀ t ∈ pkRMinrect n d₁ (0, 1 + (n - 2 * d₁ - 4) / 2), mesh n X t.1 t.2 = 0 := by
    intro t ht
    obtain ⟨⟨hw, hw1, _, hw3⟩, _⟩ := (pkR_mem_minrect _ _ _ _).1 ht
    rw [pkR_mem_head] at hw3
    have := mem_Icc.1 hw
    dsimp only at hw3
    omega
  have hmz : ∀ t ∈ pkRMinrect n d₁ (0 + d₁, 1), mesh n X t.1 t.2 = 0 := by
    rw [zero_add]
    exact ((pkR_lam_iff _ _ _ _).1 hX).2.2 (d₁, 1) (mem_singleton_self _)
  obtain ⟨h1, h2⟩ := pkR_region H hX hmy hmz
  rw [hm2, hf] at h1 h2
  exact ⟨pkR_lam_mono h1, h2⟩

/-- **The region `Ω(a, b′)` is a standard polygon**: for even `n`, `d₁ ≥ 2` and `d₂ = 0`
(`2d₁ + 2 = n`), at a point of `Λ^{b′}`, `b′ = (d₁ − 1, 0)`, the region point of the list `f k = k`
(`k ≤ 2d₁ − 1`), `k + 2` (otherwise) is on `Λ` of the standard polygon `(n − 2, d₁ − 1)`, with the
same `x`. -/
theorem pkR_reg_bp {n d₁ : ℕ} (hE : n % 2 = 0) (hd1 : 2 ≤ d₁) (hd2 : 2 * d₁ + 2 = n) {X : ℕ × ℕ → ℚ}
    (hX : pkRLam n d₁ {(d₁ - 1, 0)} X) :
    pkRLam (n - 2) (d₁ - 1) ∅ (pkRSubX n (fun k => if k ≤ 2 * d₁ - 1 then k else k + 2) X) ∧
      mesh (n - 2) (pkRSubX n (fun k => if k ≤ 2 * d₁ - 1 then k else k + 2) X) 1 (n - 2 - 1) =
        mesh n X 1 (n - 1) := by
  have H : pkRRG n d₁ 0 (d₁ - 1) 0 0 :=
      (pkR_RG_iff _ _ _ _ _ _).2 ⟨hE, by omega, by omega, by omega, by omega⟩
  have hm2 : 2 * (d₁ - 1) + 2 * 0 + 2 = n - 2 := by omega
  have hf : pkRRgf d₁ 0 (d₁ - 1) 0 = fun k => if k ≤ 2 * d₁ - 1 then k else k + 2 := by
    funext k
    rw [pkR_rgf_def]
    split_ifs <;> omega
  have hmy : ∀ t ∈ pkRMinrect n d₁ (0, 0 + 0), mesh n X t.1 t.2 = 0 := by
    intro t ht
    obtain ⟨⟨hw, hw1, _, hw3⟩, _⟩ := (pkR_mem_minrect _ _ _ _).1 ht
    rw [pkR_mem_head] at hw3
    have := mem_Icc.1 hw
    dsimp only at hw3
    omega
  have hmz : ∀ t ∈ pkRMinrect n d₁ (0 + (d₁ - 1), 0), mesh n X t.1 t.2 = 0 := by
    rw [zero_add]
    exact ((pkR_lam_iff _ _ _ _).1 hX).2.2 (d₁ - 1, 0) (mem_singleton_self _)
  obtain ⟨h1, h2⟩ := pkR_region H hX hmy hmz
  rw [hm2, hf] at h1 h2
  exact ⟨pkR_lam_mono h1, h2⟩

/-- **The induction step through `b″`** (`d₂ ≥ 1`, i.e. `2d₁ + 4 ≤ n`; `b″ = (d₁, 1)` with chord
`C = (2d₁+1, 2d₁+4)`): for even `n ≥ 6`, data `(F₁, c)` at `(n, d₁)` and `(F₁′, c′)` at
`(n − 2, d₁)` as in `pkR_psi_step`, `c′ ≠ 0` implies `c ≠ 0`. The hypotheses `hR5two`, `hR5one` are
as in `pkR_psi_step`. -/
theorem pkR_psi_mir {n d₁ : ℕ} (hE : n % 2 = 0) (hn : 6 ≤ n) (hm : 2 * d₁ + 4 ≤ n)
    (hR5two : ∀ {n : ℕ}, n % 2 = 0 → 4 ≤ n → ∀ {p q lo hi : ℕ}, (p, q) ∈ oddDiagonals n → p ≤
        lo → lo ≤ hi →
      hi < q → lo % 2 = p % 2 → ∀ X ∈ {X : ℕ × ℕ → ℚ | pkRZ5c n (p % 2) (Icc lo hi) {(p, q)} X},
        MvPolynomial.eval X (pkRBNP ℚ n {(p, q)}) = 0)
    (hR5one : ∀ {n : ℕ}, n % 2 = 0 → 4 ≤ n → ∀ {p q lo hi : ℕ}, (p, q) ∈ oddDiagonals n → lo ≤ p →
      q ≤ hi + 1 → ∀ {r₀ : ℕ}, r₀ ∈ (Icc 1 n).filter (fun c => c < lo ∨ hi < c) → r₀ % 2 = q % 2 →
        ∀ X ∈ {X : ℕ × ℕ → ℚ | pkRZ5c n (q % 2) ((Icc 1 n).filter (fun c => c < lo ∨ hi < c))
            {(p, q)} X},
          MvPolynomial.eval X (pkRBNP ℚ n {(p, q)}) = 0)
    {F₁ : MvPolynomial (ℕ × ℕ) ℚ} {c : ℚ}
    (hF : ∀ X : ℕ × ℕ → ℚ, pkRLam n d₁ ∅ X →
      MvPolynomial.eval X (NP ℚ n) = mesh n X 1 (n - 1) * MvPolynomial.eval X F₁)
    (hc : ∀ X : ℕ × ℕ → ℚ, pkRLam n d₁ ∅ X → mesh n X 1 (n - 1) = 0 →
      MvPolynomial.eval X F₁ = c * MvPolynomial.eval X (oddDen ℚ n))
    {F₁' : MvPolynomial (ℕ × ℕ) ℚ} {c' : ℚ}
    (hF' : ∀ X : ℕ × ℕ → ℚ, pkRLam (n - 2) d₁ ∅ X →
      MvPolynomial.eval X (NP ℚ (n - 2)) = mesh (n - 2) X 1 (n - 2 - 1) * MvPolynomial.eval X F₁')
    (hc' : ∀ X : ℕ × ℕ → ℚ, pkRLam (n - 2) d₁ ∅ X → mesh (n - 2) X 1 (n - 2 - 1) = 0 →
      MvPolynomial.eval X F₁' = c' * MvPolynomial.eval X (oddDen ℚ (n - 2)))
    (hc0 : c' ≠ 0) : c ≠ 0 := by
  have hC : pkRMchord d₁ (d₁, 1) = (2 * d₁ + 1, 2 * d₁ + 1 + 3) :=
    Prod.ext rfl (show 2 * d₁ + 2 * 1 + 2 = 2 * d₁ + 1 + 3 by omega)
  have wx : ∃ w : ℕ × ℕ → ℚ, pkRLam n d₁ {(d₁, 1)} w ∧ mesh n w 1 (n - 1) ≠ 0 := by
    rcases Nat.eq_zero_or_pos d₁ with h0 | h0
    · subst h0
      exact pkR_wxB hE hn
    · exact pkR_wxC hE h0 hm
  refine pkR_psi_step hE hn (d₁' := d₁) (i := d₁) (j := 1) (p := 2 * d₁ + 1)
      (by omega) le_rfl (by omega)
    (by omega) (by omega) hC (fun X hX => ?_) (fun X hX => pkR_reg_mir hE hn hm hX) wx
    (fun Q hQ hne => pkR_GI hE (by omega) (by omega)
      (fun Q' hQ' => by rw [mem_singleton.1 hQ']; dsimp only; omega) (pkR_closed_mir hm) hQ
      (fun Q' hQ' => by rw [mem_singleton.1 hQ', hC]; exact hne))
    hR5two hR5one hF hc hF' hc' hc0
  rw [show 2 * d₁ + 1 + 2 = 2 * d₁ + 3 by omega, show 2 * d₁ + 1 + 1 = 2 * d₁ + 2 by omega,
    show 2 * d₁ + 1 + 3 = 2 * d₁ + 4 by omega]
  exact pkR_R10i_mirror hn hm hX

/-- **The induction step through `b′`** (`d₂ = 0`, i.e. `2d₁ + 2 = n`; `b′ = (d₁ − 1, 0)` with chord
`C = (2d₁−1, 2d₁+2)`): for even `n ≥ 6`, data `(F₁, c)` at `(n, d₁)` and `(F₁′, c′)` at
`(n − 2, d₁ − 1)` as in `pkR_psi_step`, `c′ ≠ 0` implies `c ≠ 0`. The hypotheses `hR5two`, `hR5one`
are as in `pkR_psi_step`. -/
theorem pkR_psi_bp {n d₁ : ℕ} (hE : n % 2 = 0) (hn : 6 ≤ n) (hd2 : 2 * d₁ + 2 = n)
    (hR5two : ∀ {n : ℕ}, n % 2 = 0 → 4 ≤ n → ∀ {p q lo hi : ℕ}, (p, q) ∈ oddDiagonals n → p ≤
        lo → lo ≤ hi →
      hi < q → lo % 2 = p % 2 → ∀ X ∈ {X : ℕ × ℕ → ℚ | pkRZ5c n (p % 2) (Icc lo hi) {(p, q)} X},
        MvPolynomial.eval X (pkRBNP ℚ n {(p, q)}) = 0)
    (hR5one : ∀ {n : ℕ}, n % 2 = 0 → 4 ≤ n → ∀ {p q lo hi : ℕ}, (p, q) ∈ oddDiagonals n → lo ≤ p →
      q ≤ hi + 1 → ∀ {r₀ : ℕ}, r₀ ∈ (Icc 1 n).filter (fun c => c < lo ∨ hi < c) → r₀ % 2 = q % 2 →
        ∀ X ∈ {X : ℕ × ℕ → ℚ | pkRZ5c n (q % 2) ((Icc 1 n).filter (fun c => c < lo ∨ hi < c))
            {(p, q)} X},
          MvPolynomial.eval X (pkRBNP ℚ n {(p, q)}) = 0)
    {F₁ : MvPolynomial (ℕ × ℕ) ℚ} {c : ℚ}
    (hF : ∀ X : ℕ × ℕ → ℚ, pkRLam n d₁ ∅ X →
      MvPolynomial.eval X (NP ℚ n) = mesh n X 1 (n - 1) * MvPolynomial.eval X F₁)
    (hc : ∀ X : ℕ × ℕ → ℚ, pkRLam n d₁ ∅ X → mesh n X 1 (n - 1) = 0 →
      MvPolynomial.eval X F₁ = c * MvPolynomial.eval X (oddDen ℚ n))
    {F₁' : MvPolynomial (ℕ × ℕ) ℚ} {c' : ℚ}
    (hF' : ∀ X : ℕ × ℕ → ℚ, pkRLam (n - 2) (d₁ - 1) ∅ X →
      MvPolynomial.eval X (NP ℚ (n - 2)) = mesh (n - 2) X 1 (n - 2 - 1) * MvPolynomial.eval X F₁')
    (hc' : ∀ X : ℕ × ℕ → ℚ, pkRLam (n - 2) (d₁ - 1) ∅ X → mesh (n - 2) X 1 (n - 2 - 1) = 0 →
      MvPolynomial.eval X F₁' = c' * MvPolynomial.eval X (oddDen ℚ (n - 2)))
    (hc0 : c' ≠ 0) : c ≠ 0 := by
  have hC : pkRMchord d₁ (d₁ - 1, 0) = (2 * d₁ - 1, 2 * d₁ - 1 + 3) :=
    Prod.ext (show 2 * (d₁ - 1) + 1 = 2 * d₁ - 1 by omega)
        (show 2 * d₁ + 2 * 0 + 2 = 2 * d₁ - 1 + 3 by omega)
  refine pkR_psi_step hE hn (d₁' := d₁ - 1) (i := d₁ - 1) (j := 0) (p := 2 * d₁ - 1)
      (by omega) (by omega)
    (by omega) (by omega) (by omega) hC (fun X hX => ?_)
        (fun X hX => pkR_reg_bp hE (by omega) hd2 hX)
    (pkR_wxA hn hd2)
    (fun Q hQ hne => pkR_GI hE (by omega) (by omega)
      (fun Q' hQ' => by rw [mem_singleton.1 hQ']; dsimp only; omega)
          (pkR_closed_bp (by omega) (by omega)) hQ
      (fun Q' hQ' => by rw [mem_singleton.1 hQ', hC]; exact hne))
    hR5two hR5one hF hc hF' hc' hc0
  rw [show 2 * d₁ - 1 + 2 = 2 * d₁ + 1 by omega, show 2 * d₁ - 1 + 1 = 2 * d₁ by omega,
    show 2 * d₁ - 1 + 3 = 2 * d₁ + 2 by omega]
  exact pkR_R10i hn (by omega) (by omega) hX

-- registry: C-27FF
/-- **The constant of the standard polygon is non-zero**: on every standard polygon `(n, d₁)` (`n`
even, `n ≥ 4`, `2d₁ + 2 ≤ n`), if `NP_n = x · F₁` on `Λ` and `F₁ = c · oddDen_n` on
`Λ₀ = Λ ∩ {x = 0}`, then `c ≠ 0`. By induction on `n`: the base is `pkR_psi_four` (`C7`;
`c(4) = −1`, and `(4, 1)` has the same `Λ` as `(4, 0)`), the step `pkR_psi_mir` (`d₂ ≥ 1`) or
`pkR_psi_bp` (`d₂ = 0`). The hypotheses `hR5two`, `hR5one` are the statements of `pkR_b_R5one2`,
`pkR_b_R5one1` (below), with `pkRBZ5` spelled `pkRZ5c`; `pkR_omega` (`C9`) instantiates them with
these two lemmas. -/
theorem pkR_psi_all
    (hR5two : ∀ {n : ℕ}, n % 2 = 0 → 4 ≤ n → ∀ {p q lo hi : ℕ}, (p, q) ∈ oddDiagonals n → p ≤
        lo → lo ≤ hi →
      hi < q → lo % 2 = p % 2 → ∀ X ∈ {X : ℕ × ℕ → ℚ | pkRZ5c n (p % 2) (Icc lo hi) {(p, q)} X},
        MvPolynomial.eval X (pkRBNP ℚ n {(p, q)}) = 0)
    (hR5one : ∀ {n : ℕ}, n % 2 = 0 → 4 ≤ n → ∀ {p q lo hi : ℕ}, (p, q) ∈ oddDiagonals n → lo ≤ p →
      q ≤ hi + 1 → ∀ {r₀ : ℕ}, r₀ ∈ (Icc 1 n).filter (fun c => c < lo ∨ hi < c) → r₀ % 2 = q % 2 →
        ∀ X ∈ {X : ℕ × ℕ → ℚ | pkRZ5c n (q % 2) ((Icc 1 n).filter (fun c => c < lo ∨ hi < c))
            {(p, q)} X},
          MvPolynomial.eval X (pkRBNP ℚ n {(p, q)}) = 0) :
    ∀ n : ℕ, n % 2 = 0 → 4 ≤ n → ∀ d₁ : ℕ, 2 * d₁ + 2 ≤ n → ∀ (F₁ : MvPolynomial (ℕ × ℕ) ℚ) (c : ℚ),
      (∀ X : ℕ × ℕ → ℚ, pkRLam n d₁ ∅ X →
        MvPolynomial.eval X (NP ℚ n) = mesh n X 1 (n - 1) * MvPolynomial.eval X F₁) →
      (∀ X : ℕ × ℕ → ℚ, pkRLam n d₁ ∅ X → mesh n X 1 (n - 1) = 0 →
        MvPolynomial.eval X F₁ = c * MvPolynomial.eval X (oddDen ℚ n)) → c ≠ 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hE hn d₁ hd F₁ c hF hc
    by_cases h4 : n = 4
    · subst h4
      rcases (show d₁ = 0 ∨ d₁ = 1 by omega) with h0 | h0
      · subst h0
        rw [pkR_psi_four hF hc]
        norm_num
      · subst h0
        have ec : pkRCstp 4 1 = pkRCstp 4 0 := by decide
        have hl : ∀ X : ℕ × ℕ → ℚ, pkRLam 4 0 ∅ X → pkRLam 4 1 ∅ X := fun X hX => by
          obtain ⟨h1, h2, _⟩ := (pkR_lam_iff _ _ _ _).1 hX
          exact (pkR_lam_iff _ _ _ _).2 ⟨by rw [ec]; exact h1, by rw [ec]; exact h2,
              fun Q hQ => by simp at hQ⟩
        rw [pkR_psi_four (fun X hX => hF X (hl X hX)) (fun X hX hx => hc X (hl X hX) hx)]
        norm_num
    · by_cases hm : 2 * d₁ + 4 ≤ n
      · obtain ⟨F₁', c', hF', hc'⟩ := pkR_const9 (n := n - 2) (by omega) (by omega) d₁ (by omega)
        exact pkR_psi_mir hE (by omega) hm hR5two hR5one hF hc hF' hc'
          (ih (n - 2) (by omega) (by omega) (by omega) d₁ (by omega) F₁' c' hF' hc')
      · obtain ⟨F₁', c', hF', hc'⟩ := pkR_const9 (n := n - 2) (by omega) (by omega)
          (d₁ - 1) (by omega)
        exact pkR_psi_bp hE (by omega) (by omega) hR5two hR5one hF hc hF' hc'
          (ih (n - 2) (by omega) (by omega) (by omega) (d₁ - 1) (by omega) F₁' c' hF' hc')

/-! ### The rotation bridge for the far side of a chord

For a chord `(p, q)` of the `n`-gon, its side `relab n q` (the list `[q, …, n, 1, …, p]`,
`m = n − q + p + 1` legs) is the region list `f = [1, …, p] ++ [q, …, n]` rotated by `m − p` legs
(`pkR_rotB_*`, `C7`, is the case `q = p + 3`). -/

/-- The far-side rotation bridge on labels: for `1 ≤ p`, `p + 2 ≤ q ≤ n` and a diagonal `(a, b)` of
the `m`-gon, `m = n − q + p + 1`, rotating `(a, b)` by `n − q + 1` legs and relabelling by
`relab n q` gives `(f a, f b)`, with `f k = k` for `k ≤ p` and `f k = k + (q − p − 1)` otherwise. -/
theorem pkR_rotG_pair {n p q : ℕ} (hp : 1 ≤ p) (hpq : p + 2 ≤ q) (hqn : q ≤ n) {a b : ℕ}
    (hd : (a, b) ∈ diagonals (n - q + p + 1)) :
    relab n q (npair (n - q + p + 1) (a + (n - q + 1)) (b + (n - q + 1))) =
      (if a ≤ p then a else a + (q - p - 1), if b ≤ p then b else b + (q - p - 1)) := by
  rw [mem_diagonals] at hd
  dsimp only at hd
  obtain ⟨u, hu⟩ : ∃ u, u = vtx (n - q + p + 1) (a + (n - q + 1)) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = vtx (n - q + p + 1) (b + (n - q + 1)) := ⟨_, rfl⟩
  have hu' := pkR_b_vtx2 (N := n - q + p + 1) (u := a + (n - q + 1)) (by omega) (by omega)
  have hv' := pkR_b_vtx2 (N := n - q + p + 1) (u := b + (n - q + 1)) (by omega) (by omega)
  rw [← hu] at hu'
  rw [← hv] at hv'
  have e : npair (n - q + p + 1) (a + (n - q + 1)) (b + (n - q + 1)) = (min u v, max u v) :=
      by rw [hu, hv]; rfl
  rw [e]
  obtain ⟨fa, hfa⟩ : ∃ fa, fa = (if a ≤ p then a else a + (q - p - 1)) := ⟨_, rfl⟩
  obtain ⟨fb, hfb⟩ : ∃ fb, fb = (if b ≤ p then b else b + (q - p - 1)) := ⟨_, rfl⟩
  have hfa' : (a ≤ p ∧ fa = a) ∨ (p < a ∧ fa = a + (q - p - 1)) := by rw [hfa]; split_ifs <;> omega
  have hfb' : (b ≤ p ∧ fb = b) ∨ (p < b ∧ fb = b + (q - p - 1)) := by rw [hfb]; split_ifs <;> omega
  rw [← hfa, ← hfb]
  have eU : vtx n (u + q - 1) = fa := by
    have w := pkR_b_vtx2 (N := n) (u := u + q - 1) (by omega) (by omega)
    omega
  have eV : vtx n (v + q - 1) = fb := by
    have w := pkR_b_vtx2 (N := n) (u := v + q - 1) (by omega) (by omega)
    omega
  change (min (vtx n (min u v + q - 1)) (vtx n (max u v + q - 1)),
    max (vtx n (min u v + q - 1)) (vtx n (max u v + q - 1))) = (fa, fb)
  rcases le_total u v with h | h
  · rw [min_eq_left h, max_eq_right h, eU, eV, min_eq_left (by omega), max_eq_right (by omega)]
  · rw [min_eq_right h, max_eq_left h, eU, eV, min_eq_right (by omega), max_eq_left (by omega)]

/-- The rotated far-side point agrees with the region point on every child diagonal (for `1 ≤ p`,
`p + 2 ≤ q ≤ n`). -/
theorem pkR_rotG_eval {n p q : ℕ} (hp : 1 ≤ p) (hpq : p + 2 ≤ q) (hqn : q ≤ n) (X : ℕ × ℕ → ℚ) :
    ∀ d ∈ diagonals (n - q + p + 1),
      (X ∘ (relab n q ∘ (rot (n - q + p + 1))^[n - q + 1])) d =
        pkRSubX n (fun k => if k ≤ p then k else k + (q - p - 1)) X d := by
  rintro ⟨a, b⟩ hd
  have hdd := mem_diagonals.1 hd
  dsimp only at hdd
  change X (relab n q ((rot (n - q + p + 1))^[n - q + 1] (a, b))) =
    planar n X (if a ≤ p then a else a + (q - p - 1)) (if b ≤ p then b else b + (q - p - 1))
  rw [pkR_rot_iter (by omega) _ (a, b) hd]
  dsimp only
  rw [pkR_rotG_pair hp hpq hqn hd]
  obtain ⟨fa, hfa⟩ : ∃ fa, fa = (if a ≤ p then a else a + (q - p - 1)) := ⟨_, rfl⟩
  obtain ⟨fb, hfb⟩ : ∃ fb, fb = (if b ≤ p then b else b + (q - p - 1)) := ⟨_, rfl⟩
  have hfa' : (a ≤ p ∧ fa = a) ∨ (p < a ∧ fa = a + (q - p - 1)) := by rw [hfa]; split_ifs <;> omega
  have hfb' : (b ≤ p ∧ fb = b) ∨ (p < b ∧ fb = b + (q - p - 1)) := by rw [hfb]; split_ifs <;> omega
  rw [← hfa, ← hfb, planar_of_mem X (by omega) (by omega) (by omega),
    ite_eq_left (by rw [mem_diagonals]; dsimp only; omega)]

/-- The far side of a chord, read at the rotated point: for even `m = n − q + p + 1 ≥ 4`,
`NP_m(X ∘ relab n q) = NP_m(X ∘ (relab n q ∘ rot^[n−q+1]))`. By `pkR_rotG_eval`, the rotated point
agrees with the region point on the child diagonals. -/
theorem pkR_rotG_NP {n p q : ℕ}
    (hm : 4 ≤ n - q + p + 1) (hmE : (n - q + p + 1) % 2 = 0) (X : ℕ × ℕ → ℚ) :
    MvPolynomial.eval X (MvPolynomial.rename (relab n q) (NP ℚ (n - q + p + 1))) =
      MvPolynomial.eval (X ∘ (relab n q ∘ (rot (n - q + p + 1))^[n - q + 1]))
          (NP ℚ (n - q + p + 1)) := by
  rw [MvPolynomial.eval_rename, ← pkR_NP_rotk hm hmE (n - q + 1) (X ∘ relab n q),
      Function.comp_assoc]

/-! ### The ¬q numerator on `W_q`

For any member `q`, the points of `W_q` with `c⋆ = 0` or `c⋆′ = 0` lie on the locus `Z′`
(`pkRZ5c`), so the numerator that avoids the chord of `q` vanishes there (`pkR_notq_W`). -/

/-- `pkR_R14_Z5a` for any chord: for `i ≤ d₁` and `2d₁ + 2j + 2 ≤ n` (`n` even, `n ≥ 4`) with
`pkRMchord d₁ (i, j) = (p, q′)`, a point of `W_q` with `c⋆ = 0` lies on
`pkRZ5c n (p % 2) [p, q′ − 1] {(p, q′)}` (the run `R = A_q = [p, q′ − 1]`). -/
theorem pkR_R14_Z5a' {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ i j p q' : ℕ} (hi : i ≤ d₁)
    (hj : 2 * d₁ + 2 * j + 2 ≤ n) (hC : pkRMchord d₁ (i, j) = (p, q')) {X : ℕ × ℕ → ℚ}
    (hW : pkRW n d₁ (i, j) X) (hx : mesh n X 1 (n - 1) = 0) :
    pkRZ5c n (p % 2) (Icc p (q' - 1)) {(p, q')} X := by
  have e1 : 2 * i + 1 = p := congrArg Prod.fst hC
  have e2 : 2 * d₁ + 2 * j + 2 = q' := congrArg Prod.snd hC
  have R := pkR_R14a hE hn hi hj hW hx
  refine ⟨fun a ha b hb h1 h2 h3 h4 => ?_, fun a ha h1 h2 w hw => ?_,
      fun Q hQ w hw a ha h1 h2 h3 h4 _ => ?_⟩
  · rw [mem_Icc] at h2 h4
    by_cases hab : a = b
    · rw [hab]
      exact pkR_mesh_self (by omega) X b
    · exact R a ha b hb (by omega) (by omega) (Or.inl (by omega)) (Ne.symm hab)
  · rw [mem_Icc] at h2 hw
    have ha' := mem_Icc.1 ha
    exact R a ha w (mem_Icc.2 ⟨by omega, by omega⟩) (by omega) (by omega)
        (Or.inr (by omega)) (by omega)
  · rw [mem_singleton] at hQ
    subst hQ
    dsimp only at h4
    have hw' := (h4 p (mem_Icc.2 ⟨le_rfl, by omega⟩)).2 ⟨le_rfl, by omega⟩
    rw [mem_Icc] at h3
    rw [pkR_mesh_comm]
    exact R a ha w hw (by omega) (by omega) (Or.inr (by omega)) (by omega)

/-- `pkR_R14_Z5b` for any chord: in the setting of `pkR_R14_Z5a'`, a point of `W_q` with `c⋆′ = 0`
lies on `pkRZ5c n (q′ % 2) ([1, n] ∖ [p, q′ − 1]) {(p, q′)}` (the run `R = B_q`). -/
theorem pkR_R14_Z5b' {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ i j p q' : ℕ} (hi : i ≤ d₁)
    (hj : 2 * d₁ + 2 * j + 2 ≤ n) (hC : pkRMchord d₁ (i, j) = (p, q')) {X : ℕ × ℕ → ℚ}
    (hW : pkRW n d₁ (i, j) X) (hy : mesh n X (pkRCstp n d₁).1 (pkRCstp n d₁).2 = 0) :
    pkRZ5c n (q' % 2) ((Icc 1 n).filter (fun c => c < p ∨ q' - 1 < c)) {(p, q')} X := by
  have e1 : 2 * i + 1 = p := congrArg Prod.fst hC
  have e2 : 2 * d₁ + 2 * j + 2 = q' := congrArg Prod.snd hC
  have R := pkR_R14b hE hn hi hj hW hy
  refine ⟨fun a ha b hb h1 h2 h3 h4 => ?_, fun a ha h1 h2 w hw => ?_,
      fun Q hQ w hw a ha h1 h2 h3 h4 _ => ?_⟩
  · have ha' := mem_Icc.1 ha
    simp only [mem_filter, mem_Icc] at h2
    by_cases hab : a = b
    · rw [hab]
      exact pkR_mesh_self (by omega) X b
    · exact R a ha b hb (by omega) (by omega) (Or.inl (by omega)) (Ne.symm hab)
  · have ha' := mem_Icc.1 ha
    simp only [mem_filter, mem_Icc] at h2 hw
    exact R a ha w (mem_Icc.2 ⟨by omega, by omega⟩) (by omega) (by omega)
        (Or.inr (by omega)) (by omega)
  · rw [mem_singleton] at hQ
    subst hQ
    have ha' := mem_Icc.1 ha
    have hr : q' ∈ (Icc 1 n).filter (fun c => c < p ∨ q' - 1 < c) :=
      mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, Or.inr (by omega)⟩
    have hw' := h4 q' hr
    dsimp only at hw'
    simp only [mem_filter, mem_Icc] at h3
    rw [pkR_mesh_comm]
    have hwo : ¬ (p ≤ w ∧ w < q') := fun hh => by have := hw'.1 hh; omega
    exact R a ha w hw (by omega) (by omega) (Or.inr (by omega)) (by omega)

/-- **The ¬q numerator on `W_q`**: for a member `q = (i, j)` of the standard polygon `(n, d₁)` (`n`
even, `n ≥ 4`) with chord `C`, the numerator `pkRBNP ℚ n {C}` vanishes on `W_q ∩ {c⋆ = 0}` and on
`W_q ∩ {c⋆′ = 0}`; these are the hypotheses `h1`, `h2` of `pkR_R14d` and `pkR_R10iii` (`C7`). The
hypotheses `hR5two`, `hR5one` are as in `pkR_psi_step`. -/
theorem pkR_notq_W {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ i j : ℕ} (hi : i ≤ d₁)
    (hj : 2 * d₁ + 2 * j + 2 ≤ n) (hb : ¬ (i = d₁ ∧ j = 0))
    (ha : ¬ (i = 0 ∧ 2 * d₁ + 2 * j + 2 = n))
    (hR5two : ∀ {n : ℕ}, n % 2 = 0 → 4 ≤ n → ∀ {p q lo hi : ℕ}, (p, q) ∈ oddDiagonals n → p ≤
        lo → lo ≤ hi →
      hi < q → lo % 2 = p % 2 → ∀ X ∈ {X : ℕ × ℕ → ℚ | pkRZ5c n (p % 2) (Icc lo hi) {(p, q)} X},
        MvPolynomial.eval X (pkRBNP ℚ n {(p, q)}) = 0)
    (hR5one : ∀ {n : ℕ}, n % 2 = 0 → 4 ≤ n → ∀ {p q lo hi : ℕ}, (p, q) ∈ oddDiagonals n → lo ≤ p →
      q ≤ hi + 1 → ∀ {r₀ : ℕ}, r₀ ∈ (Icc 1 n).filter (fun c => c < lo ∨ hi < c) → r₀ % 2 = q % 2 →
        ∀ X ∈ {X : ℕ × ℕ → ℚ | pkRZ5c n (q % 2) ((Icc 1 n).filter (fun c => c < lo ∨ hi < c))
            {(p, q)} X},
          MvPolynomial.eval X (pkRBNP ℚ n {(p, q)}) = 0) :
    (∀ X : ℕ × ℕ → ℚ, pkRW n d₁ (i, j) X → mesh n X 1 (n - 1) = 0 →
      MvPolynomial.eval X (pkRBNP ℚ n {pkRMchord d₁ (i, j)}) = 0) ∧
    (∀ X : ℕ × ℕ → ℚ, pkRW n d₁ (i, j) X → mesh n X (pkRCstp n d₁).1 (pkRCstp n d₁).2 = 0 →
      MvPolynomial.eval X (pkRBNP ℚ n {pkRMchord d₁ (i, j)}) = 0) := by
  have hQ := pkR_mchord_mem hi hj hb ha
  have hC : pkRMchord d₁ (i, j) = (2 * i + 1, 2 * d₁ + 2 * j + 2) := rfl
  rw [hC] at hQ ⊢
  refine ⟨fun X hW hx => ?_, fun X hW hy => ?_⟩
  · exact @hR5two n hE hn (2 * i + 1) (2 * d₁ + 2 * j + 2) (2 * i + 1)
      (2 * d₁ + 2 * j + 2 - 1) hQ le_rfl
      (by omega) (by omega) rfl X (pkR_R14_Z5a' hE hn hi hj hC hW hx)
  · exact @hR5one n hE hn (2 * i + 1) (2 * d₁ + 2 * j + 2) (2 * i + 1)
      (2 * d₁ + 2 * j + 2 - 1) hQ le_rfl
      (by omega) (2 * d₁ + 2 * j + 2)
          (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, hj⟩, Or.inr (by omega)⟩) rfl X
      (pkR_R14_Z5b' hE hn hi hj hC hW hy)

/-! ### The ¬q numerator on `Λ^I`

The ¬q numerator vanishes on `W_q ∩ {X_Q = 0}` for every other member `Q` (`pkR_notq_Q`), and is
`x^{|I| + 1} · G` on `Λ^I` (`pkR_notq_lam`). -/

/-- **The ¬q numerator on `W_q ∩ {X_Q = 0}`**: for distinct members `q = (i, j)`, `Q = (i′, j′)` of
the standard polygon `(n, d₁)` (`n` even, `n ≥ 4`), the ¬q numerator vanishes at every point of
`W_q` with `X_Q = 0`. Proof: split it at `Q` by `pkR_resNumK` (`C7`); the side of `Q` used (the
A-side if `A_q ⊄ A_Q`, else the B-side) does not contain `q`, so its banned set is empty, and it is
on its `S_T` locus by `pkR_R14c_A` or `pkR_R14c_B` (`C6`). -/
theorem pkR_notq_Q {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ i j i' j' : ℕ} (hi : i ≤ d₁)
    (hj : 2 * d₁ + 2 * j + 2 ≤ n) (hb : ¬ (i = d₁ ∧ j = 0))
    (ha : ¬ (i = 0 ∧ 2 * d₁ + 2 * j + 2 = n)) (hi' : i' ≤ d₁) (hj' : 2 * d₁ + 2 * j' + 2 ≤ n)
    (hb' : ¬ (i' = d₁ ∧ j' = 0)) (ha' : ¬ (i' = 0 ∧ 2 * d₁ + 2 * j' + 2 = n))
    (hne : (i', j') ≠ (i, j)) {X : ℕ × ℕ → ℚ} (hW : pkRW n d₁ (i, j) X)
    (hXQ : X (pkRMchord d₁ (i', j')) = 0) :
    MvPolynomial.eval X (pkRBNP ℚ n {pkRMchord d₁ (i, j)}) = 0 := by
  have hq := pkR_mchord_mem hi hj hb ha
  have hQ := pkR_mchord_mem hi' hj' hb' ha'
  have hne' : pkRMchord d₁ (i, j) ≠ pkRMchord d₁ (i', j') := fun h => hne (pkR_mchord_inj h).symm
  have hne2 := pkR_ne_pair hne
  obtain ⟨E, hEq⟩ := pkR_resNumK hn hE hq hQ hne'
  have eq : pkRMchord d₁ (i, j) = (2 * i + 1, 2 * d₁ + 2 * j + 2) := rfl
  have eQ : pkRMchord d₁ (i', j') = (2 * i' + 1, 2 * d₁ + 2 * j' + 2) := rfl
  rw [eq, eQ] at hEq
  rw [eQ] at hQ hXQ
  rw [eq]
  have hEq' : pkRBNP ℚ n {(2 * i + 1, 2 * d₁ + 2 * j + 2)} =
      MvPolynomial.X (2 * i' + 1, 2 * d₁ + 2 * j' + 2) * E +
        MvPolynomial.rename (relab n (2 * i' + 1))
            (pkRBNP ℚ (2 * d₁ + 2 * j' + 2 - (2 * i' + 1) + 1)
          (pkRBPull n (2 * i' + 1) (2 * d₁ + 2 * j' + 2 - (2 * i' + 1) + 1)
              {(2 * i + 1, 2 * d₁ + 2 * j + 2)})) *
        MvPolynomial.rename (relab n (2 * d₁ + 2 * j' + 2))
          (pkRBNP ℚ (n - (2 * d₁ + 2 * j' + 2) + (2 * i' + 1) + 1)
            (pkRBPull n (2 * d₁ + 2 * j' + 2) (n - (2 * d₁ + 2 * j' + 2) + (2 * i' + 1) + 1)
              {(2 * i + 1, 2 * d₁ + 2 * j + 2)})) *
        pkRBCross ℚ n {(2 * i + 1, 2 * d₁ + 2 * j + 2)} (2 * i' + 1, 2 * d₁ + 2 * j' + 2) := hEq
  rw [hEq', map_add, map_mul, MvPolynomial.eval_X, hXQ, zero_mul, zero_add, map_mul, map_mul]
  have hQd := mem_diagonals.1 (mem_filter.1 hQ).1
  have hQo := (mem_filter.1 hQ).2
  dsimp only at hQd hQo
  by_cases hAB : i' ≤ i ∧ j ≤ j'
  · -- the B-side of `Q` does not contain `q`
    have hpull : pkRBPull n (2 * d₁ + 2 * j' + 2) (n - (2 * d₁ + 2 * j' + 2) + (2 * i' + 1) + 1)
        {(2 * i + 1, 2 * d₁ + 2 * j + 2)} = ∅ := by
      refine filter_false_of_mem fun d hd h => ?_
      have hdd := mem_diagonals.1 hd
      rw [mem_singleton] at h
      have v1 := pkR_b_vtx2 (N := n) (u := d.1 + (2 * d₁ + 2 * j' + 2) - 1) (by omega) (by omega)
      have v2 := pkR_b_vtx2 (N := n) (u := d.2 + (2 * d₁ + 2 * j' + 2) - 1) (by omega) (by omega)
      have e : relab n (2 * d₁ + 2 * j' + 2) d =
          (min (vtx n (d.1 + (2 * d₁ + 2 * j' + 2) - 1)) (vtx n (d.2 + (2 * d₁ + 2 * j' + 2) - 1)),
            max (vtx n (d.1 + (2 * d₁ + 2 * j' + 2) - 1))
                (vtx n (d.2 + (2 * d₁ + 2 * j' + 2) - 1))) := rfl
      rw [e, Prod.mk.injEq] at h
      omega
    have hR : MvPolynomial.eval X (MvPolynomial.rename (relab n (2 * d₁ + 2 * j' + 2))
        (pkRBNP ℚ (n - (2 * d₁ + 2 * j' + 2) + (2 * i' + 1) + 1)
          (pkRBPull n (2 * d₁ + 2 * j' + 2) (n - (2 * d₁ + 2 * j' + 2) + (2 * i' + 1) + 1)
            {(2 * i + 1, 2 * d₁ + 2 * j + 2)}))) = 0 := by
      rw [hpull, pkR_b_NP_empty, MvPolynomial.eval_rename]
      exact pkR_STnum (by omega) (by omega) (by omega) (pkR_adm_evens (by omega)) _
        (pkR_onZT_congrD (pkR_relab2 hQ X) (pkR_R14c_B hE hn hi' hj' hb' ha' hW hXQ))
    rw [hR, mul_zero, zero_mul]
  · -- the A-side of `Q` does not contain `q`
    have hpull : pkRBPull n (2 * i' + 1) (2 * d₁ + 2 * j' + 2 - (2 * i' + 1) + 1)
        {(2 * i + 1, 2 * d₁ + 2 * j + 2)} = ∅ := by
      refine filter_false_of_mem fun d hd h => ?_
      have hdd := mem_diagonals.1 hd
      rw [mem_singleton] at h
      have v1 := pkR_b_vtx2 (N := n) (u := d.1 + (2 * i' + 1) - 1) (by omega) (by omega)
      have v2 := pkR_b_vtx2 (N := n) (u := d.2 + (2 * i' + 1) - 1) (by omega) (by omega)
      have e : relab n (2 * i' + 1) d =
          (min (vtx n (d.1 + (2 * i' + 1) - 1)) (vtx n (d.2 + (2 * i' + 1) - 1)),
            max (vtx n (d.1 + (2 * i' + 1) - 1)) (vtx n (d.2 + (2 * i' + 1) - 1))) := rfl
      rw [e, Prod.mk.injEq] at h
      omega
    have hL : MvPolynomial.eval X (MvPolynomial.rename (relab n (2 * i' + 1))
        (pkRBNP ℚ (2 * d₁ + 2 * j' + 2 - (2 * i' + 1) + 1)
          (pkRBPull n (2 * i' + 1) (2 * d₁ + 2 * j' + 2 - (2 * i' + 1) + 1)
            {(2 * i + 1, 2 * d₁ + 2 * j + 2)}))) = 0 := by
      rw [hpull, pkR_b_NP_empty, MvPolynomial.eval_rename]
      exact pkR_STnum (by omega) (by omega) (by omega) (pkR_adm_evens (by omega)) _
        (pkR_onZT_congrD (pkR_relab1 hQ X) (pkR_R14c_A hE hn hi' hj' hb' ha' hAB hW hXQ))
    rw [hL, zero_mul, zero_mul]

/-- `Λ^I ⊆ W_q` for `q ∈ I`. -/
theorem pkR_lamI_W {n d₁ : ℕ} {I : Finset (ℕ × ℕ)} {q : ℕ × ℕ} (hq : q ∈ I) {X : ℕ × ℕ → ℚ}
    (hX : pkRLam n d₁ I X) : pkRW n d₁ q X := by
  obtain ⟨h1, _, h3⟩ := (pkR_lam_iff _ _ _ _).1 hX
  exact (pkR_W_iff _ _ _ _).2 ⟨fun a ha b hb e1 e2 e3 e4 _ => h1 a ha b hb e1 e2 e3 e4,
      fun t ht => h3 q hq t ht⟩

-- registry: C-27FF
/-- **The ¬q numerator on `Λ^I`**: for a set `I` of members of the standard polygon `(n, d₁)` (`n`
even, `n ≥ 4`) and `q ∈ I`, there is `G` with `NP^{¬q}_n = x^{|I| + 1} · G` on `Λ^I`. Proof:
`pkR_R14d` (`C7`) with `J = I ∖ {q}`, where `c⋆ = c⋆′ = x`, and `X_Q = x` for `Q ∈ I` by `pkR_XQ`
(`C6`). The hypotheses `hR5two`, `hR5one` are as in `pkR_psi_step`. -/
theorem pkR_notq_lam {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ : ℕ} {I : Finset (ℕ × ℕ)}
    (hI : ∀ Q ∈ I, pkRIsMem n d₁ Q) {q : ℕ × ℕ} (hq : q ∈ I)
    (hR5two : ∀ {n : ℕ}, n % 2 = 0 → 4 ≤ n → ∀ {p q lo hi : ℕ}, (p, q) ∈ oddDiagonals n → p ≤
        lo → lo ≤ hi →
      hi < q → lo % 2 = p % 2 → ∀ X ∈ {X : ℕ × ℕ → ℚ | pkRZ5c n (p % 2) (Icc lo hi) {(p, q)} X},
        MvPolynomial.eval X (pkRBNP ℚ n {(p, q)}) = 0)
    (hR5one : ∀ {n : ℕ}, n % 2 = 0 → 4 ≤ n → ∀ {p q lo hi : ℕ}, (p, q) ∈ oddDiagonals n → lo ≤ p →
      q ≤ hi + 1 → ∀ {r₀ : ℕ}, r₀ ∈ (Icc 1 n).filter (fun c => c < lo ∨ hi < c) → r₀ % 2 = q % 2 →
        ∀ X ∈ {X : ℕ × ℕ → ℚ | pkRZ5c n (q % 2) ((Icc 1 n).filter (fun c => c < lo ∨ hi < c))
            {(p, q)} X},
          MvPolynomial.eval X (pkRBNP ℚ n {(p, q)}) = 0) :
    ∃ G : MvPolynomial (ℕ × ℕ) ℚ, ∀ X : ℕ × ℕ → ℚ, pkRLam n d₁ I X →
      MvPolynomial.eval X (pkRBNP ℚ n {pkRMchord d₁ q}) = mesh n X 1 (n - 1) ^ (I.card + 1) *
        MvPolynomial.eval X G := by
  obtain ⟨i, j⟩ := q
  obtain ⟨hi, hj, hb, ha⟩ := (pkR_isMem_iff _ _ _).1 (hI _ hq)
  dsimp only at hi hj hb ha
  obtain ⟨h1, h2⟩ := pkR_notq_W hE hn hi hj hb ha hR5two hR5one
  have hJ : ∀ Q ∈ I.erase (i, j), pkRIsMem n d₁ Q ∧ Q ≠ (i, j) := fun Q hQ =>
    ⟨hI Q (mem_of_mem_erase hQ), ne_of_mem_erase hQ⟩
  obtain ⟨G, hG⟩ := pkR_R14d hE hn hi hj hb ha (I.erase (i, j)) hJ _ h1 h2
    (fun Q hQ X hW hXQ => by
      obtain ⟨m1, m2, m3, m4⟩ := (pkR_isMem_iff _ _ _).1 (hJ Q hQ).1
      exact pkR_notq_Q hE hn hi hj hb ha m1 m2 m3 m4 (hJ Q hQ).2 hW hXQ)
  refine ⟨G, fun X hX => ?_⟩
  obtain ⟨_, hx2, h3⟩ := (pkR_lam_iff _ _ _ _).1 hX
  have hXQ : ∀ Q ∈ I.erase (i, j), X (pkRMchord d₁ Q) = mesh n X 1 (n - 1) := by
    intro Q hQ
    obtain ⟨m1, m2, m3, m4⟩ := (pkR_isMem_iff _ _ _).1 (hJ Q hQ).1
    have hm : (2 * Q.1 + 1, 2 * d₁ + 2 * Q.2 + 2) ∈ oddDiagonals n := pkR_mchord_mem m1 m2 m3 m4
    have hmd := mem_diagonals.1 (mem_filter.1 hm).1
    dsimp only at hmd
    have e := pkR_XQ hE hn m1 m2 m3 m4 hX (h3 Q (mem_of_mem_erase hQ))
    rw [planar_of_mem X (by omega) (by omega) (by omega), ite_eq_left (mem_filter.1 hm).1] at e
    exact e
  rw [hG X (pkR_lamI_W hq hX), prod_congr rfl hXQ, prod_const, card_erase_of_mem hq, ← hx2]
  have hc : 1 ≤ I.card := card_pos.2 ⟨_, hq⟩
  rw [show I.card + 1 = 2 + (I.card - 1) by omega, pow_add]
  ring

/-! ### The children of a member chord, and the algebra of the Ω form

The two children of the chord of a member are standard polygons again (`pkR_childA`, `pkR_childB`).
The algebra `pkR_omega_alg` of the form `x^k (c · x · D + x² · F)`, its case `I = ∅` (`pkR_omega0`)
and the split `pkR_omega_split` of `NP_n` at a member are the inputs of the induction `pkR_omega` in
`C9`. -/

-- registry: C-5DFW
/-- **The A-side child of a member `q = (i, j)`**: for `n` even, `n ≥ 4`, at a point of `Λ^I` with
`q ∈ I`, the point `X ∘ relab n (2i + 1)` (the labelling of the split `pkR_b_res1`, `C7`) lies on
`Λ^{I′}` of the standard polygon `(q′ − p′ + 1, d₁ − i)`, `(p′, q′)` the chord of `q`, where `I′` is
the set of elements of `I` between `q` and `b`, shifted by `(i, 0)`; `x` is the same. -/
theorem pkR_childA {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ i j : ℕ} (hi : i ≤ d₁)
    (hj : 2 * d₁ + 2 * j + 2 ≤ n) (hb : ¬ (i = d₁ ∧ j = 0))
    (ha : ¬ (i = 0 ∧ 2 * d₁ + 2 * j + 2 = n)) {I : Finset (ℕ × ℕ)} (hq : (i, j) ∈ I) {X : ℕ × ℕ → ℚ}
    (hX : pkRLam n d₁ I X) :
    pkRLam (2 * d₁ + 2 * j + 2 - (2 * i + 1) + 1) (d₁ - i)
        ((I.filter (fun Q => i ≤ Q.1 ∧ Q.1 ≤ i + (d₁ - i) ∧ 0 ≤ Q.2 ∧ Q.2 ≤ 0 + j)).image
          (fun Q => (Q.1 - i, Q.2 - 0))) (X ∘ relab n (2 * i + 1)) ∧
      mesh (2 * d₁ + 2 * j + 2 - (2 * i + 1) + 1) (X ∘ relab n (2 * i + 1)) 1
        (2 * d₁ + 2 * j + 2 - (2 * i + 1) + 1 - 1) = mesh n X 1 (n - 1) := by
  have hQ := pkR_mchord_mem hi hj hb ha
  have hQ' : ((2 * i + 1, 2 * d₁ + 2 * j + 2) : ℕ × ℕ) ∈ oddDiagonals n := hQ
  have H : pkRRG n d₁ i (d₁ - i) 0 j :=
      (pkR_RG_iff _ _ _ _ _ _).2 ⟨hE, hn, by omega, by omega, by omega⟩
  have hsz : 2 * (d₁ - i) + 2 * j + 2 = 2 * d₁ + 2 * j + 2 - (2 * i + 1) + 1 := by omega
  have hf : pkRRgf d₁ i (d₁ - i) 0 = fun k => k + (2 * i + 1) - 1 := by
    funext k
    rw [pkR_rgf_def]
    split_ifs <;> omega
  have hmy : ∀ t ∈ pkRMinrect n d₁ (i, 0 + j), mesh n X t.1 t.2 = 0 := by
    rw [zero_add]
    exact ((pkR_lam_iff _ _ _ _).1 hX).2.2 (i, j) hq
  have hmz : ∀ t ∈ pkRMinrect n d₁ (i + (d₁ - i), 0), mesh n X t.1 t.2 = 0 := by
    intro t ht
    obtain ⟨⟨_, hw1, hw2, hw3⟩, ⟨_, hc1, _, hc3⟩⟩ := (pkR_mem_minrect _ _ _ _).1 ht
    rw [pkR_mem_head] at hw3 hc3
    dsimp only at hw3 hc3
    omega
  obtain ⟨h1, h2⟩ := pkR_region H hX hmy hmz
  rw [hsz, hf] at h1 h2
  have hc : ∀ d ∈ diagonals (2 * d₁ + 2 * j + 2 - (2 * i + 1) + 1),
      (X ∘ relab n (2 * i + 1)) d = pkRSubX n (fun k => k + (2 * i + 1) - 1) X d :=
    fun d hd => (pkR_relab1 hQ' X d hd).symm
  refine ⟨pkR_lam_congrD hc h1, ?_⟩
  rw [pkR_mesh_congrD hc]
  exact h2

-- registry: C-5DFW
/-- **The B-side child of a member `q = (i, j)`**: for `n` even, `n ≥ 4`, at a point of `Λ^I` with
`q ∈ I`, the rotated point `X ∘ (relab n q′ ∘ rot^[n − q′ + 1])` lies on `Λ^{I′}` of the standard
polygon `(n − q′ + p′ + 1, i)`, `(p′, q′)` the chord of `q`, where `I′` is the set of elements of
`I` between `a` and `q`, shifted by `(0, j)`; `x` is the same. `NP` of the `relab n q′` child is
read at this point by `pkR_rotG_NP`. -/
theorem pkR_childB {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ i j : ℕ} (hi : i ≤ d₁)
    (hj : 2 * d₁ + 2 * j + 2 ≤ n) (hb : ¬ (i = d₁ ∧ j = 0))
    (ha : ¬ (i = 0 ∧ 2 * d₁ + 2 * j + 2 = n)) {I : Finset (ℕ × ℕ)} (hq : (i, j) ∈ I) {X : ℕ × ℕ → ℚ}
    (hX : pkRLam n d₁ I X) :
    pkRLam (n - (2 * d₁ + 2 * j + 2) + (2 * i + 1) + 1) i
        ((I.filter (fun Q => 0 ≤ Q.1 ∧ Q.1 ≤ 0 + i ∧ j ≤ Q.2 ∧ Q.2 ≤ j +
            (n / 2 - 1 - d₁ - j))).image
          (fun Q => (Q.1 - 0, Q.2 - j)))
        (X ∘ (relab n (2 * d₁ + 2 * j + 2) ∘
          (rot (n - (2 * d₁ + 2 * j + 2) + (2 * i + 1) + 1))^[n - (2 * d₁ + 2 * j + 2) + 1])) ∧
      mesh (n - (2 * d₁ + 2 * j + 2) + (2 * i + 1) + 1)
        (X ∘ (relab n (2 * d₁ + 2 * j + 2) ∘
          (rot (n - (2 * d₁ + 2 * j + 2) + (2 * i + 1) + 1))^[n - (2 * d₁ + 2 * j + 2) + 1])) 1
        (n - (2 * d₁ + 2 * j + 2) + (2 * i + 1) + 1 - 1) = mesh n X 1 (n - 1) := by
  have H : pkRRG n d₁ 0 i j (n / 2 - 1 - d₁ - j) :=
    (pkR_RG_iff _ _ _ _ _ _).2 ⟨hE, hn, by omega, by omega, by omega⟩
  have hsz : 2 * i + 2 * (n / 2 - 1 - d₁ - j) + 2 =
      n - (2 * d₁ + 2 * j + 2) + (2 * i + 1) + 1 := by omega
  have hf : pkRRgf d₁ 0 i j = fun k => if k ≤
      2 * i + 1 then k else k + (2 * d₁ + 2 * j + 2 - (2 * i + 1) - 1) := by
    funext k
    rw [pkR_rgf_def]
    split_ifs <;> omega
  have hmy : ∀ t ∈ pkRMinrect n d₁ (0, j + (n / 2 - 1 - d₁ - j)), mesh n X t.1 t.2 = 0 := by
    intro t ht
    obtain ⟨⟨hw, hw1, _, hw3⟩, _⟩ := (pkR_mem_minrect _ _ _ _).1 ht
    rw [pkR_mem_head] at hw3
    have := mem_Icc.1 hw
    dsimp only at hw3
    omega
  have hmz : ∀ t ∈ pkRMinrect n d₁ (0 + i, j), mesh n X t.1 t.2 = 0 := by
    rw [zero_add]
    exact ((pkR_lam_iff _ _ _ _).1 hX).2.2 (i, j) hq
  obtain ⟨h1, h2⟩ := pkR_region H hX hmy hmz
  rw [hsz, hf] at h1 h2
  have hQd := mem_diagonals.1 (mem_filter.1 (pkR_mchord_mem hi hj hb ha)).1
  dsimp only [pkRMchord] at hQd
  have hc := pkR_rotG_eval (n := n) (p := 2 * i + 1) (q := 2 * d₁ + 2 * j + 2) (by omega)
      (by omega) hj X
  refine ⟨pkR_lam_congrD hc h1, ?_⟩
  rw [pkR_mesh_congrD hc]
  exact h2

/-- **The algebra of the Ω form**: on a set `V` of points, if `NP = X_q · NP^{¬q} + L · R · cr`,
`X_q = x`, `NP^{¬q} = x^{k+1} G` (as `pkR_notq_lam` gives), and the two children have the Ω form
`L = x^a (c_L x D_L + x² F_L)`, `R = x^b (c_R x D_R + x² F_R)` with `a + b + 1 = k`, then
`NP = x^k (c_L c_R · x · D_L D_R cr + x² F)` on `V` for some `F`. -/
theorem pkR_omega_alg {σ : Type*} {V : Set (σ → ℚ)}
    {x NPn Xq NPnot L R cr G DL DR FL FR : MvPolynomial σ ℚ} {cL cR : ℚ} {a b k : ℕ}
    (hk : a + b + 1 = k)
    (hsplit : ∀ X ∈ V, MvPolynomial.eval X NPn = MvPolynomial.eval X Xq *
        MvPolynomial.eval X NPnot +
      MvPolynomial.eval X L * MvPolynomial.eval X R * MvPolynomial.eval X cr)
    (hXq : ∀ X ∈ V, MvPolynomial.eval X Xq = MvPolynomial.eval X x)
    (hnot : ∀ X ∈ V, MvPolynomial.eval X NPnot = MvPolynomial.eval X x ^ (k + 1) *
        MvPolynomial.eval X G)
    (hL : ∀ X ∈ V, MvPolynomial.eval X L = MvPolynomial.eval X x ^ a *
      (cL * MvPolynomial.eval X x * MvPolynomial.eval X DL + MvPolynomial.eval X x ^ 2 *
          MvPolynomial.eval X FL))
    (hR : ∀ X ∈ V, MvPolynomial.eval X R = MvPolynomial.eval X x ^ b *
      (cR * MvPolynomial.eval X x * MvPolynomial.eval X DR + MvPolynomial.eval X x ^ 2 *
          MvPolynomial.eval X FR)) :
    ∃ F : MvPolynomial σ ℚ, ∀ X ∈ V, MvPolynomial.eval X NPn = MvPolynomial.eval X x ^ k *
      (cL * cR * MvPolynomial.eval X x *
          (MvPolynomial.eval X DL * MvPolynomial.eval X DR * MvPolynomial.eval X cr) +
        MvPolynomial.eval X x ^ 2 * MvPolynomial.eval X F) := by
  refine ⟨(MvPolynomial.C cL * DL * FR + MvPolynomial.C cR * DR * FL + x * FL * FR) * cr + G,
      fun X hX => ?_⟩
  rw [hsplit X hX, hXq X hX, hnot X hX, hL X hX, hR X hX, ← hk]
  simp only [map_add, map_mul, MvPolynomial.eval_C]
  ring

-- registry: C-27FF
/-- **The Ω form for `I = ∅`**: on the standard polygon `(n, d₁)` (`n` even, `n ≥ 4`, `2d₁ + 2 ≤ n`)
there are `c ≠ 0` and `F` with `NP_n = x · (c · oddDen_n + x · F)` on `Λ`, by `pkR_const9` (`C7`),
`pkR_div` (`C5`) and `pkR_psi_all`. The hypotheses `hR5two`, `hR5one` are as in `pkR_psi_step`. -/
theorem pkR_omega0
    (hR5two : ∀ {n : ℕ}, n % 2 = 0 → 4 ≤ n → ∀ {p q lo hi : ℕ}, (p, q) ∈ oddDiagonals n → p ≤
        lo → lo ≤ hi →
      hi < q → lo % 2 = p % 2 → ∀ X ∈ {X : ℕ × ℕ → ℚ | pkRZ5c n (p % 2) (Icc lo hi) {(p, q)} X},
        MvPolynomial.eval X (pkRBNP ℚ n {(p, q)}) = 0)
    (hR5one : ∀ {n : ℕ}, n % 2 = 0 → 4 ≤ n → ∀ {p q lo hi : ℕ}, (p, q) ∈ oddDiagonals n → lo ≤ p →
      q ≤ hi + 1 → ∀ {r₀ : ℕ}, r₀ ∈ (Icc 1 n).filter (fun c => c < lo ∨ hi < c) → r₀ % 2 = q % 2 →
        ∀ X ∈ {X : ℕ × ℕ → ℚ | pkRZ5c n (q % 2) ((Icc 1 n).filter (fun c => c < lo ∨ hi < c))
            {(p, q)} X},
          MvPolynomial.eval X (pkRBNP ℚ n {(p, q)}) = 0)
    {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) (d₁ : ℕ) (hd : 2 * d₁ + 2 ≤ n) :
    ∃ (c : ℚ) (F : MvPolynomial (ℕ × ℕ) ℚ), c ≠ 0 ∧ ∀ X : ℕ × ℕ → ℚ, pkRLam n d₁ ∅ X →
      MvPolynomial.eval X (NP ℚ n) = mesh n X 1 (n - 1) *
        (c * MvPolynomial.eval X (oddDen ℚ n) + mesh n X 1 (n - 1) * MvPolynomial.eval X F) := by
  obtain ⟨F₁, c, hF, hc⟩ := pkR_const9 hE hn d₁ hd
  have hc0 := pkR_psi_all hR5two hR5one n hE hn d₁ hd F₁ c hF hc
  obtain ⟨F, hFd⟩ := pkR_div (pkR_lam_sub n d₁ ∅) (pkR_meshP_lin n 1 (n - 1))
    ⟨pkRChA n d₁, (pkR_xwit hE hn d₁ hd).1,
        by rw [pkR_meshP_eval, (pkR_xwit hE hn d₁ hd).2]; norm_num⟩
    (F₁ - MvPolynomial.C c * oddDen ℚ n) (fun X hX hx => by
      rw [pkR_meshP_eval] at hx
      rw [map_sub, map_mul, MvPolynomial.eval_C, hc X hX hx, sub_self])
  refine ⟨c, F, hc0, fun X hX => ?_⟩
  have e := hFd X hX
  rw [map_sub, map_mul, MvPolynomial.eval_C, pkR_meshP_eval, sub_eq_iff_eq_add] at e
  rw [hF X hX, e]
  ring

-- registry: C-5DFW
/-- **The single-chord split on `Λ^I`**: for `n` even, `n ≥ 4`, and a member `q = (i, j) ∈ I` with
chord `(p′, q′)`, at a point of `Λ^I`,
`NP_n = x · NP^{¬q} + NP_A(X ∘ relab n p′) · NP_B(rotated point) · cross_q`, by `pkR_b_res1` (`C7`)
at `K = {q}`. The two child points lie on their standard `Λ` by `pkR_childA` and `pkR_childB`, and
`NP^{¬q}` is given by `pkR_notq_lam`. -/
theorem pkR_omega_split {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ i j : ℕ} (hi : i ≤ d₁)
    (hj : 2 * d₁ + 2 * j + 2 ≤ n) (hb : ¬ (i = d₁ ∧ j = 0))
    (ha : ¬ (i = 0 ∧ 2 * d₁ + 2 * j + 2 = n)) {I : Finset (ℕ × ℕ)} (hq : (i, j) ∈ I) {X : ℕ × ℕ → ℚ}
    (hX : pkRLam n d₁ I X) :
    MvPolynomial.eval X (NP ℚ n) =
      mesh n X 1 (n - 1) * MvPolynomial.eval X (pkRBNP ℚ n {(2 * i + 1, 2 * d₁ + 2 * j + 2)}) +
        MvPolynomial.eval (X ∘ relab n (2 * i + 1)) (NP ℚ (2 * d₁ + 2 * j + 2 - (2 * i + 1) + 1)) *
          MvPolynomial.eval (X ∘ (relab n (2 * d₁ + 2 * j + 2) ∘
            (rot (n - (2 * d₁ + 2 * j + 2) + (2 * i + 1) + 1))^[n - (2 * d₁ + 2 * j + 2) + 1]))
            (NP ℚ (n - (2 * d₁ + 2 * j + 2) + (2 * i + 1) + 1)) *
          MvPolynomial.eval X (crossProd ℚ n (2 * i + 1, 2 * d₁ + 2 * j + 2)) := by
  have hQ : ((2 * i + 1, 2 * d₁ + 2 * j + 2) : ℕ × ℕ) ∈ oddDiagonals n := pkR_mchord_mem hi hj hb ha
  have hQd := mem_diagonals.1 (mem_filter.1 hQ).1
  have hQo := (mem_filter.1 hQ).2
  dsimp only at hQd hQo
  have e0 : NP ℚ n = MvPolynomial.X (2 * i + 1, 2 * d₁ + 2 * j + 2) *
        pkRBNP ℚ n {(2 * i + 1, 2 * d₁ + 2 * j + 2)} +
      MvPolynomial.rename (relab n (2 * i + 1)) (NP ℚ (2 * d₁ + 2 * j + 2 - (2 * i + 1) + 1)) *
        MvPolynomial.rename (relab n (2 * d₁ + 2 * j + 2))
            (NP ℚ (n - (2 * d₁ + 2 * j + 2) + (2 * i + 1) + 1)) *
        crossProd ℚ n (2 * i + 1, 2 * d₁ + 2 * j + 2) := pkR_b_res1 (R := ℚ) hn hE hQ
  have hxq : X (2 * i + 1, 2 * d₁ + 2 * j + 2) = mesh n X 1 (n - 1) := by
    have e := pkR_XQ hE hn hi hj hb ha hX (((pkR_lam_iff _ _ _ _).1 hX).2.2 (i, j) hq)
    rw [planar_of_mem X (by omega) (by omega) (by omega), ite_eq_left (mem_filter.1 hQ).1] at e
    exact e
  rw [e0, map_add, map_mul, map_mul, map_mul, MvPolynomial.eval_X, hxq, MvPolynomial.eval_rename,
    pkR_rotG_NP (n := n) (p := 2 * i + 1) (q := 2 * d₁ + 2 * j + 2) (by omega) (by omega) X]


/-! ### The ear lemma and the collapse identity (prefix `pkR_b_`)

The locus `Z′` (`pkRBZ5`) and the ear lemma on it: the numerator that avoids a chord, or a chain
of chords, vanishes on `Z′` (`pkR_b_R5one2`, `pkR_b_R5one1`, `pkR_b_R5d`). The children of a chord
`Q` lie on `Z′` (`pkR_b_R6Z5`, `pkR_b_R6Z5B`), so their numerators vanish there (`pkR_b_R6van`). The
collapse identity peels a chain of chords off `NP_N` (`pkR_b_R2top`, `pkR_b_R2bot`), and the banned
sets of the children of the top chord are read off (`pkR_b_pull_head`, `pkR_b_pull_comp`). -/

/-! #### The locus `Z′` and the ear lemma for one chord

At the X-level: `Z′ ⊆ Z_T` (`pkR_b_R5a`), a side of a chord in `K` is on its `S_T` locus on `Z′`
(`pkR_b_R5b2`, `pkR_b_R5b1`), the Gram witness of `X_Q ≢ 0` on `Z′` (`pkR_b_R5c2`, `pkR_b_R5c1`),
and the conclusion for a single chord `K = {Q}` (`pkR_b_R5one2`, `pkR_b_R5one1`).
-/

theorem pkR_b_planar_ab (n : ℕ) (x y : ℕ × ℕ → ℚ) (s t : ℚ) (i j : ℕ) :
    planar n (fun d => s * x d + t * y d) i j = s * planar n x i j + t * planar n y i j := by
  rw [pkR_planar_def, pkR_planar_def n x, pkR_planar_def n y]
  split_ifs
  · rfl
  · ring

theorem pkR_b_mesh_ab (n : ℕ) (x y : ℕ × ℕ → ℚ) (s t : ℚ) (a b : ℕ) :
    mesh n (fun d => s * x d + t * y d) a b = s * mesh n x a b + t * mesh n y a b := by
  rw [pkR_mesh_def, pkR_mesh_def n x, pkR_mesh_def n y, pkR_b_planar_ab, pkR_b_planar_ab,
      pkR_b_planar_ab,
    pkR_b_planar_ab]
  ring

/-- **The locus `Z′`** in the X-space of the `n`-gon. `μ⁺` is the set of legs of parity `ε`
outside the run `R`; `K` is a set of members (chords `Q`, whose sides are read as the integer range
`[Q.1, Q.2 − 1]` and its complement). `Z′` is the set of points at which these mesh variables
vanish: (z1) the pairs of `μ⁺`; (z2) `μ⁺ × R`; (z3) for `Q ∈ K`, `minRect(Q)`: the legs of parity
`≠ ε` on the side of `Q` that contains `R`, times the `μ⁺` legs on the other side. -/
def pkRBZ5 (n ε : ℕ) (R : Finset ℕ) (K : Finset (ℕ × ℕ)) (X : ℕ × ℕ → ℚ) : Prop :=
  (∀ a ∈ Icc 1 n, ∀ b ∈ Icc 1 n, a % 2 = ε → a ∉ R → b % 2 = ε → b ∉ R → mesh n X a b = 0) ∧
  (∀ a ∈ Icc 1 n, a % 2 = ε → a ∉ R → ∀ w ∈ R, mesh n X a w = 0) ∧
  (∀ Q ∈ K, ∀ w ∈ Icc 1 n, ∀ a ∈ Icc 1 n, w % 2 ≠ ε → a % 2 = ε → a ∉ R →
    (∀ r ∈ R, (Q.1 ≤ w ∧ w < Q.2 ↔ Q.1 ≤ r ∧ r < Q.2)) →
        (∀ r ∈ R, ¬ (Q.1 ≤ a ∧ a < Q.2 ↔ Q.1 ≤ r ∧ r < Q.2)) →
    mesh n X w a = 0)

theorem pkR_b_mesh_zero (n a b : ℕ) : mesh n (fun _ : ℕ × ℕ => (0 : ℚ)) a b = 0 := by
  have e := pkR_b_mesh_ab n (fun _ => (0 : ℚ)) (fun _ => (0 : ℚ)) 0 0 a b
  simp only [zero_mul, add_zero] at e
  exact e

/-- `Z′` is a linear subspace (`pkRSub`, `C5`), the setting of `pkR_prime` (`C5`). -/
theorem pkR_b_Z5_sub (n ε : ℕ) (R : Finset ℕ) (K : Finset (ℕ × ℕ)) :
    pkRSub {X | pkRBZ5 n ε R K X} := by
  refine ⟨?_, ?_⟩
  · change pkRBZ5 n ε R K (fun _ => (0 : ℚ))
    unfold pkRBZ5
    exact ⟨fun a _ b _ _ _ _ _ => pkR_b_mesh_zero n a b, fun a _ _ _ w _ => pkR_b_mesh_zero n a w,
      fun _ _ w _ a _ _ _ _ _ _ => pkR_b_mesh_zero n w a⟩
  · intro x hx y hy s t
    have hx' : pkRBZ5 n ε R K x := hx
    have hy' : pkRBZ5 n ε R K y := hy
    change pkRBZ5 n ε R K (fun i => s * x i + t * y i)
    unfold pkRBZ5
    refine ⟨fun a ha b hb h1 h2 h3 h4 => ?_, fun a ha h1 h2 w hw => ?_,
      fun Q hQ w hw a ha h1 h2 h3 h4 h5 => ?_⟩
    · rw [pkR_b_mesh_ab, hx'.1 a ha b hb h1 h2 h3 h4, hy'.1 a ha b hb h1 h2 h3 h4]
      ring
    · rw [pkR_b_mesh_ab, hx'.2.1 a ha h1 h2 w hw, hy'.2.1 a ha h1 h2 w hw]
      ring
    · rw [pkR_b_mesh_ab, hx'.2.2 Q hQ w hw a ha h1 h2 h3 h4 h5,
        hy'.2.2 Q hQ w hw a ha h1 h2 h3 h4 h5]
      ring

/-- For `R ⊆ [1, n]`, a point whose mesh variables `c_{a,b}` vanish for every leg `a` of `μ⁺`
(parity `ε`, outside `R`) and every leg `b` lies on `Z′`, for every `K`. -/
theorem pkR_b_Z5_rows {n ε : ℕ} {R : Finset ℕ} (hR : R ⊆ Icc 1 n) (K : Finset (ℕ × ℕ))
    {X : ℕ × ℕ → ℚ}
    (h : ∀ a ∈ Icc 1 n, ∀ b ∈ Icc 1 n, a % 2 = ε → a ∉ R →
        mesh n X a b = 0) : pkRBZ5 n ε R K X := by
  unfold pkRBZ5
  exact ⟨fun a ha b hb h1 h2 _ _ => h a ha b hb h1 h2, fun a ha h1 h2 w hw =>
      h a ha w (hR hw) h1 h2,
    fun _ _ w hw a ha _ h1 h2 _ _ => by rw [pkR_mesh_comm]; exact h a ha w hw h1 h2⟩

/-- Unfolding `OnZT` at the odd legs of an `m`-gon: if the mesh variable of every even–even pair
`(a, b)` with `2 ≤ a`, `a + 2 ≤ b ≤ m` vanishes at `Y`, then `Y` is on `OnZT` for the odd legs. -/
theorem pkR_b_ZT_odds {m : ℕ} {Y : ℕ × ℕ → ℚ}
    (h : ∀ a b, 2 ≤ a → a + 2 ≤ b → b ≤ m → a % 2 = 0 → b % 2 = 0 → mesh m Y a b = 0) :
    OnZT m ((Icc 1 m).filter (fun t => t % 2 = 1)) Y := by
  change ∀ a ∈ Icc 1 m, ∀ b ∈ Icc 1 m, InST ((Icc 1 m).filter (fun t => t % 2 = 1)) a b →
      mesh m Y a b = 0
  intro a ha b hb hst
  obtain ⟨ha', hb', ⟨t, ht, h1, h2⟩, -⟩ := hst
  have ha1 := mem_Icc.1 ha
  have hb1 := mem_Icc.1 hb
  have ao : a % 2 = 0 := by
    by_contra hc
    exact ha' (mem_filter.2 ⟨ha, by omega⟩)
  have bo : b % 2 = 0 := by
    by_contra hc
    exact hb' (mem_filter.2 ⟨hb, by omega⟩)
  have ht1 := mem_filter.1 ht
  have ht2 := mem_Icc.1 ht1.1
  rcases (show a < b ∨ b < a by omega) with hab | hab
  · exact h a b (by omega) (by omega) hb1.2 ao bo
  · rw [pkR_mesh_comm]
    exact h b a (by omega) (by omega) ha1.2 bo ao

theorem pkR_b_adm_odds {m : ℕ} (hm : 4 ≤ m) :
    Admissible m 1 ((Icc 1 m).filter (fun t => t % 2 = 1)) := by
  have h13 : ({1, 3} : Finset ℕ) ⊆ (Icc 1 m).filter (fun t => t % 2 = 1) := by
    intro x hx
    rw [mem_insert, mem_singleton] at hx
    rcases hx with h | h <;> rw [h] <;> exact mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, rfl⟩
  have hc := card_le_card h13
  have e : ({1, 3} : Finset ℕ).card = 2 := by decide
  rw [e] at hc
  change (Icc 1 m).filter (fun t => t % 2 = 1) ⊆ Icc 1 m ∧ 2 ≤
      ((Icc 1 m).filter (fun t => t % 2 = 1)).card ∧
    ∀ t ∈ (Icc 1 m).filter (fun t => t % 2 = 1), t % 2 = 1
  exact ⟨filter_subset _ _, hc, fun t ht => (mem_filter.1 ht).2⟩

/-- For a cyclic list `f` (`pkRCycList`) whose legs `1..m−1` are consecutive parent legs, the block
of a child leg `j < m` is the single parent leg `{f j}`. -/
theorem pkR_b_blk1 {n m : ℕ} (hn : 2 ≤ n) {f : ℕ → ℕ} (hf : pkRCycList n m f)
    (hs : ∀ k, 1 ≤ k → k + 1 ≤ m → f (k + 1) = vtx n (f k + 1)) {j : ℕ} (hj1 : 1 ≤ j)
    (hj2 : j + 1 ≤ m) :
    pkRBlk n m f j = {f j} := by
  have hn1 : 1 ≤ n := by omega
  have fj := (hf j (mem_Icc.2 ⟨hj1, by omega⟩)).1
  have fj' := mem_Icc.1 fj
  have e1 : vtx m j = j := vtx_of_mem hj1 (by omega)
  have e2 : vtx m (j + 1) = j + 1 := vtx_of_mem (by omega) hj2
  have hl1 : pkRLen n m f j = 1 := by
    change (f (vtx m (j + 1)) + n - f (vtx m j)) % n = 1
    rw [e1, e2, hs j hj1 hj2, pkR_vtx_nxt hn1 fj]
    split_ifs with h
    · rw [h, show 1 + n - n = 1 by omega, Nat.mod_eq_of_lt (by omega)]
    · rw [show f j + 1 + n - f j = 1 + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  change Icc (f (vtx m j)) (f (vtx m j) + pkRLen n m f j - 1) = {f j}
  rw [hl1, e1, show f j + 1 - 1 = f j by omega, Icc_self]

/-- For such a list with `m ≥ 4`, the child mesh variable of the pair `(a, m)`, `2 ≤ a ≤ m − 2`, at
the closing side `Q̂` (child leg `m`) is the sum of the parent mesh variables of the single leg
`f a` against the block of `Q̂` (both corner terms are parent edges, hence `0`). -/
theorem pkR_b_hatTile {n m : ℕ} (hn : 2 ≤ n) (hm : 4 ≤ m) {f : ℕ → ℕ} (hf : pkRCycList n m f)
    (hs : ∀ k, 1 ≤ k → k + 1 ≤ m → f (k + 1) = vtx n (f k + 1)) (X : ℕ × ℕ → ℚ) {a : ℕ} (ha : 2 ≤ a)
    (ham : a + 2 ≤ m) :
    mesh m (pkRSubX n f X) a m = Finset.sum (pkRBlk n m f m) (fun w => mesh n X (f a) w) := by
  have hn1 : 1 ≤ n := by omega
  have hdiag : (min a m, max a m) ∈ diagonals m := by
    rw [min_eq_left (show a ≤ m by omega), max_eq_right (show a ≤ m by omega), mem_diagonals]
    dsimp only
    omega
  rw [pkR_subTile hn1 (by omega) hf X (mem_Icc.2 ⟨by omega, by omega⟩)
      (mem_Icc.2 ⟨by omega, le_rfl⟩) hdiag,
    pkR_b_blk1 hn hf hs (by omega) (by omega), sum_singleton]
  have vm : vtx m m = m := vtx_of_mem (by omega) le_rfl
  have va : vtx m a = a := vtx_of_mem (by omega) (by omega)
  have va1 : vtx m (a + 1) = a + 1 := vtx_of_mem (by omega) (by omega)
  have va2 : vtx m (a + 2) = a + 2 := vtx_of_mem (by omega) (by omega)
  have vm1 : vtx m (m + 1) = 1 :=
      by rw [show m + 1 = 1 + m by omega, vtx_add_n, vtx_of_mem le_rfl (by omega)]
  have vm2 : vtx m (m + 2) = 2 :=
      by rw [show m + 2 = 2 + m by omega, vtx_add_n, vtx_of_mem (by omega) (by omega)]
  rw [vm, va, va1, va2, vm1, vm2]
  have c1 : (if m = a + 2 then planar n X (f (a + 1)) (f (a + 2)) else 0) = 0 := by
    split_ifs with h
    · rw [show a + 2 = a + 1 + 1 from rfl, hs (a + 1) (by omega) (by omega),
        pkR_planar_congr hn1 X (rfl : vtx n (f (a + 1)) = vtx n (f (a + 1)))
            (pkR_vtx_vtx hn1 (f (a + 1) + 1)),
        pkR_planar_succ hn1]
    · rfl
  have c2 : (if a = 2 then planar n X (f 1) (f 2) else 0) = 0 := by
    split_ifs with h
    · rw [show (2 : ℕ) = 1 + 1 from rfl, hs 1 le_rfl (by omega),
        pkR_planar_congr hn1 X (rfl : vtx n (f 1) = vtx n (f 1)) (pkR_vtx_vtx hn1 (f 1 + 1)),
            pkR_planar_succ hn1]
    · rfl
  rw [c1, c2]
  ring

/-- **The side `[q..n, 1..p]` is on its `S_T` locus**: let `Q = (p, q) ∈ K` be an odd chord of the
`n`-gon (`n` even, `n ≥ 4`), let the run `R` lie in `A_Q = [p, q − 1]`, and let `μ⁺` be the legs of
`p`'s parity outside `R`. At a point of `Z′`, the polygon `T(Q)` (the side of `Q` without `R`, list
`k ↦ vtx n (k + q − 1)` as in `relab n q`) is on its `S_T` locus for `T` = the odd child legs (the
class of the neighbours of `Q̂`). -/
theorem pkR_b_R5b2 {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {p q : ℕ} (hQ : (p, q) ∈ oddDiagonals n)
    {R : Finset ℕ} {K : Finset (ℕ × ℕ)} (hK : (p, q) ∈ K) (hR : ∀ r ∈ R, p ≤ r ∧ r < q)
    {X : ℕ × ℕ → ℚ} (hZ : pkRBZ5 n (p % 2) R K X) :
    OnZT (n - q + p + 1) ((Icc 1 (n - q + p + 1)).filter (fun t => t % 2 = 1))
      (pkRSubX n (fun k => vtx n (k + q - 1)) X) := by
  have hQd := mem_filter.1 hQ
  rw [mem_diagonals] at hQd
  dsimp only at hQd
  have hn1 : 1 ≤ n := by omega
  have fv : ∀ k, 1 ≤ k → k ≤ n → vtx n (k + q - 1) = if k + q - 1 ≤
      n then k + q - 1 else k + q - 1 - n := by
    intro k hk1 hk2
    split_ifs with h
    · exact vtx_of_mem (by omega) h
    · have e : vtx n (k + q - 1) = vtx n ((k + q - 1 - n) + n) := by
        rw [show (k + q - 1 - n) + n = k + q - 1 by omega]
      rw [e, vtx_add_n, vtx_of_mem (by omega) (by omega)]
  have hf : pkRCycList n (n - q + p + 1) (fun k => vtx n (k + q - 1)) := by
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
  have hs : ∀ k, 1 ≤ k → k + 1 ≤ n - q + p + 1 → vtx n (k + 1 + q - 1) =
      vtx n (vtx n (k + q - 1) + 1) := by
    intro k hk1 hk2
    rw [vtx_succ hn1 (vtx n (k + q - 1)), pkR_vtx_vtx hn1, ← vtx_succ hn1, show k + q - 1 + 1 = k +
        1 + q - 1 by omega]
  have hout : ∀ a, 1 ≤ a → a + 1 ≤ n - q + p + 1 → vtx n (a + q - 1) ∈ Icc 1 n ∧
      ¬ (p ≤ vtx n (a + q - 1) ∧ vtx n (a + q - 1) < q) ∧
          (a % 2 = 0 → vtx n (a + q - 1) % 2 = p % 2) := by
    intro a h1 h2
    rw [fv a h1 (by omega)]
    split_ifs <;> exact ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega, fun _ => by omega⟩
  have hnR : ∀ c, ¬ (p ≤ c ∧ c < q) → c ∉ R := fun c hc hcR => hc (hR c hcR)
  refine pkR_b_ZT_odds (fun a b ha hab hb ao bo => ?_)
  obtain ⟨fa1, fa2, fa3⟩ := hout a (by omega) (by omega)
  rcases (show b + 1 ≤ n - q + p + 1 ∨ b = n - q + p + 1 by omega) with hb' | hb'
  · rw [pkR_single (by omega) (by omega) hf hs X (by omega) hab hb',
      ite_eq_right (by omega), add_zero]
    obtain ⟨fb1, fb2, fb3⟩ := hout b (by omega) hb'
    exact hZ.1 _ fa1 _ fb1 (fa3 ao) (hnR _ fa2) (fb3 bo) (hnR _ fb2)
  · rw [hb', pkR_b_hatTile (by omega) (by omega) hf hs X ha (by omega)]
    have v1 : vtx (n - q + p + 1) (n - q + p + 1) = n - q + p + 1 := vtx_of_mem (by omega) le_rfl
    have v2 : vtx (n - q + p + 1) (n - q + p + 1 + 1) = 1 := by
      rw [show n - q + p + 1 + 1 = 1 + (n - q + p + 1) by omega, vtx_add_n,
          vtx_of_mem le_rfl (by omega)]
    have fm : vtx n (n - q + p + 1 + q - 1) = p := by
      rw [show n - q + p + 1 + q - 1 = p + n by omega, vtx_add_n, vtx_of_mem (by omega) (by omega)]
    have f1 : vtx n (1 + q - 1) = q := by
      rw [show 1 + q - 1 = q by omega]
      exact vtx_of_mem (by omega) (by omega)
    have hl : pkRLen n (n - q + p + 1) (fun k => vtx n (k + q - 1)) (n - q + p + 1) = q - p := by
      change (vtx n (vtx (n - q + p + 1) (n - q + p + 1 + 1) + q - 1) + n -
        vtx n (vtx (n - q + p + 1) (n - q + p + 1) + q - 1)) % n = q - p
      rw [v1, v2, fm, f1, show q + n - p = (q - p) + n by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]
    have hblk : pkRBlk n (n - q + p + 1) (fun k => vtx n (k + q - 1)) (n - q + p + 1) =
        Icc p (q - 1) := by
      change Icc (vtx n (vtx (n - q + p + 1) (n - q + p + 1) + q - 1))
        (vtx n (vtx (n - q + p + 1) (n - q + p + 1) + q - 1) +
          pkRLen n (n - q + p + 1) (fun k => vtx n (k + q - 1))
              (n - q + p + 1) - 1) = Icc p (q - 1)
      rw [hl, v1, fm, show p + (q - p) - 1 = q - 1 by omega]
    rw [hblk]
    refine sum_eq_zero (fun w hw => ?_)
    have hw' := mem_Icc.1 hw
    have hwn : w ∈ Icc 1 n := mem_Icc.2 ⟨by omega, by omega⟩
    by_cases hwe : w % 2 = p % 2
    · by_cases hwR : w ∈ R
      · exact hZ.2.1 _ fa1 (fa3 ao) (hnR _ fa2) w hwR
      · exact hZ.1 _ fa1 w hwn (fa3 ao) (hnR _ fa2) hwe hwR
    · rw [pkR_mesh_comm]
      exact hZ.2.2 (p, q) hK w hwn _ fa1 hwe (fa3 ao) (hnR _ fa2)
        (fun r hr => iff_of_true (show p ≤ w ∧ w < q from ⟨hw'.1, by omega⟩) (hR r hr))
        (fun r hr h => fa2 (h.2 (hR r hr)))

/-- **Numerator form of `pkR_b_R5b2`**: under its hypotheses `N(T(Q)) ≡ 0` on `Z′`, that is, the
second child numerator `rename (relab n q) (NP ℚ (n − q + p + 1))` of the split at `Q` vanishes at
`X`. -/
theorem pkR_b_R5b2_NP {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {p q : ℕ} (hQ : (p, q) ∈ oddDiagonals n)
    {R : Finset ℕ} {K : Finset (ℕ × ℕ)} (hK : (p, q) ∈ K) (hR : ∀ r ∈ R, p ≤ r ∧ r < q)
    {X : ℕ × ℕ → ℚ} (hZ : pkRBZ5 n (p % 2) R K X) :
    MvPolynomial.eval X (MvPolynomial.rename (relab n q) (NP ℚ (n - q + p + 1))) = 0 := by
  have hQd := mem_filter.1 hQ
  rw [mem_diagonals] at hQd
  dsimp only at hQd
  rw [MvPolynomial.eval_rename]
  exact pkR_STnum (by omega) (by omega) (by omega) (pkR_b_adm_odds (by omega)) _
    (pkR_onZT_congrD (pkR_relab2 hQ X) (pkR_b_R5b2 hE hn hQ hK hR hZ))

/-- **The side `[p..q]` is on its `S_T` locus** (the mirror of `pkR_b_R5b2`): for an odd chord
`Q = (p, q) ∈ K` of the `n`-gon (`n` even, `n ≥ 4`), a run `R` outside `A_Q = [p, q − 1]` and `μ⁺`
the legs of `q`'s parity outside `R`, at a point of `Z′` the polygon `T(Q)` = the side `[p..q]`
(list `k ↦ k + p − 1`, as in `relab n p`) is on its `S_T` locus for the odd child legs. -/
theorem pkR_b_R5b1 {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {p q : ℕ} (hQ : (p, q) ∈ oddDiagonals n)
    {R : Finset ℕ} {K : Finset (ℕ × ℕ)} (hK : (p, q) ∈ K) (hR : ∀ r ∈ R, r < p ∨ q ≤ r)
    {X : ℕ × ℕ → ℚ} (hZ : pkRBZ5 n (q % 2) R K X) :
    OnZT (q - p + 1) ((Icc 1 (q - p + 1)).filter (fun t => t % 2 = 1))
        (pkRSubX n (fun k => k + p - 1) X) := by
  have hQd := mem_filter.1 hQ
  rw [mem_diagonals] at hQd
  dsimp only at hQd
  have hn1 : 1 ≤ n := by omega
  have hf : pkRCycList n (q - p + 1) (fun k => k + p - 1) := by
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
  have hnR : ∀ c, p ≤ c → c < q → c ∉ R := fun c h1 h2 hcR => by have := hR c hcR; omega
  refine pkR_b_ZT_odds (fun a b ha hab hb ao bo => ?_)
  have fa1 : a + p - 1 ∈ Icc 1 n := mem_Icc.2 ⟨by omega, by omega⟩
  have fa3 : (a + p - 1) % 2 = q % 2 := by omega
  have fa2 : a + p - 1 ∉ R := hnR _ (by omega) (by omega)
  rcases (show b + 1 ≤ q - p + 1 ∨ b = q - p + 1 by omega) with hb' | hb'
  · rw [pkR_single (by omega) (by omega) hf hs X (by omega) hab hb',
      ite_eq_right (by omega), add_zero]
    exact hZ.1 _ fa1 _ (mem_Icc.2 ⟨by omega, by omega⟩) fa3 fa2 (by omega)
        (hnR _ (by omega) (by omega))
  · rw [hb', pkR_b_hatTile (by omega) (by omega) hf hs X ha (by omega)]
    have v1 : vtx (q - p + 1) (q - p + 1) = q - p + 1 := vtx_of_mem (by omega) le_rfl
    have v2 : vtx (q - p + 1) (q - p + 1 + 1) = 1 := by
      rw [show q - p + 1 + 1 = 1 + (q - p + 1) by omega, vtx_add_n, vtx_of_mem le_rfl (by omega)]
    have hl : pkRLen n (q - p + 1) (fun k => k + p - 1) (q - p + 1) = n - q + p := by
      change (vtx (q - p + 1) (q - p + 1 + 1) + p - 1 + n -
          (vtx (q - p + 1) (q - p + 1) + p - 1)) % n = n - q + p
      rw [v1, v2, show 1 + p - 1 + n - (q - p + 1 + p - 1) = n - q + p by omega,
          Nat.mod_eq_of_lt (by omega)]
    have hblk : pkRBlk n (q - p + 1) (fun k => k + p - 1) (q - p + 1) = Icc q (n + p - 1) := by
      change Icc (vtx (q - p + 1) (q - p + 1) + p - 1)
        (vtx (q - p + 1) (q - p + 1) + p - 1 + pkRLen n (q - p + 1) (fun k => k + p - 1)
            (q - p + 1) - 1) =
          Icc q (n + p - 1)
      rw [hl, v1, show q - p + 1 + p - 1 = q by omega, show q + (n - q + p) - 1 = n +
          p - 1 by omega]
    rw [hblk]
    refine sum_eq_zero (fun w hw => ?_)
    have hw' := mem_Icc.1 hw
    rw [pkR_mesh_vtx hn1 X, vtx_of_mem (show 1 ≤ a + p - 1 by omega) (show a + p - 1 ≤ n by omega)]
    have hw2 : vtx n w ∈ Icc 1 n ∧ (vtx n w < p ∨ q ≤ vtx n w) := by
      rw [pkR_vtx2 hn1 (by omega) (by omega)]
      split_ifs <;> exact ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩
    by_cases hwe : vtx n w % 2 = q % 2
    · by_cases hwR : vtx n w ∈ R
      · exact hZ.2.1 _ fa1 fa3 fa2 _ hwR
      · exact hZ.1 _ fa1 _ hw2.1 fa3 fa2 hwe hwR
    · rw [pkR_mesh_comm]
      exact hZ.2.2 (p, q) hK _ hw2.1 _ fa1 hwe fa3 fa2
        (fun r hr => iff_of_false (show ¬ (p ≤ vtx n w ∧ vtx n w < q) by omega)
          (show ¬ (p ≤ r ∧ r < q) by have := hR r hr; omega))
        (fun r hr h => (show ¬ (p ≤ r ∧ r < q) by have := hR r hr; omega)
          (h.1 (show p ≤ a + p - 1 ∧ a + p - 1 < q by omega)))

/-- **Numerator form of `pkR_b_R5b1`**: under its hypotheses the first child numerator
`rename (relab n p) (NP ℚ (q − p + 1))` of the split at `Q` vanishes at `X`. -/
theorem pkR_b_R5b1_NP {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {p q : ℕ} (hQ : (p, q) ∈ oddDiagonals n)
    {R : Finset ℕ} {K : Finset (ℕ × ℕ)} (hK : (p, q) ∈ K) (hR : ∀ r ∈ R, r < p ∨ q ≤ r)
    {X : ℕ × ℕ → ℚ} (hZ : pkRBZ5 n (q % 2) R K X) :
    MvPolynomial.eval X (MvPolynomial.rename (relab n p) (NP ℚ (q - p + 1))) = 0 := by
  have hQd := mem_filter.1 hQ
  rw [mem_diagonals] at hQd
  dsimp only at hQd
  rw [MvPolynomial.eval_rename]
  exact pkR_STnum (by omega) (by omega) (by omega) (pkR_b_adm_odds (by omega)) _
    (pkR_onZT_congrD (pkR_relab1 hQ X) (pkR_b_R5b1 hE hn hQ hK hR hZ))

/-- The set `T := μ⁻ ∪ {s}`: the legs of parity `≠ ε` outside `R`. -/
def pkRBT5 (n ε : ℕ) (R : Finset ℕ) : Finset ℕ := (Icc 1 n).filter (fun t => t % 2 ≠ ε ∧ t ∉ R)

/-- **`Z′ ⊆ Z_T`**: if no two legs of `R` lie in different arcs of `T = pkRBT5 n ε R` (`R` is a
run), every point of `Z′` is on `Z_T` (`OnZT n T`). -/
theorem pkR_b_R5a {n ε : ℕ} {R : Finset ℕ} {K : Finset (ℕ × ℕ)} {X : ℕ × ℕ → ℚ}
    (hZ : pkRBZ5 n ε R K X)
    (hRR : ∀ a ∈ R, ∀ b ∈ R, ¬ InST (pkRBT5 n ε R) a b) : OnZT n (pkRBT5 n ε R) X := by
  intro a ha b hb hst
  have hT : ∀ c ∈ Icc 1 n, c ∉ pkRBT5 n ε R → c % 2 = ε ∨ c ∈ R := by
    intro c hc hcT
    by_contra h
    exact hcT (mem_filter.2 ⟨hc, fun e => h (Or.inl e), fun e => h (Or.inr e)⟩)
  by_cases haR : a ∈ R
  · by_cases hbR : b ∈ R
    · exact absurd hst (hRR a haR b hbR)
    · have hb2 := (hT b hb hst.2.1).resolve_right hbR
      rw [pkR_mesh_comm]
      exact hZ.2.1 b hb hb2 hbR a haR
  · have ha2 := (hT a ha hst.1).resolve_right haR
    by_cases hbR : b ∈ R
    · exact hZ.2.1 a ha ha2 haR b hbR
    · exact hZ.1 a ha b hb ha2 haR ((hT b hb hst.2.1).resolve_right hbR) hbR

/-- A run `R = [lo, hi]` (no wrap) satisfies the arc hypothesis of `pkR_b_R5a`. -/
theorem pkR_b_ivl_RR {n ε lo hi : ℕ} :
    ∀ a ∈ Icc lo hi, ∀ b ∈ Icc lo hi, ¬ InST (pkRBT5 n ε (Icc lo hi)) a b := by
  intro a ha b hb hst
  obtain ⟨-, -, ⟨t, ht, h1, h2⟩, -⟩ := hst
  have ht' := (mem_filter.1 ht).2.2
  have ha' := mem_Icc.1 ha
  have hb' := mem_Icc.1 hb
  exact ht' (mem_Icc.2 ⟨by omega, by omega⟩)

/-- A wrapping run `R = [1, n] ∖ [lo, hi]` satisfies the arc hypothesis of `pkR_b_R5a`. -/
theorem pkR_b_coivl_RR {n ε lo hi : ℕ} :
    ∀ a ∈ (Icc 1 n).filter (fun c => c < lo ∨ hi < c),
        ∀ b ∈ (Icc 1 n).filter (fun c => c < lo ∨ hi < c),
      ¬ InST (pkRBT5 n ε ((Icc 1 n).filter (fun c => c < lo ∨ hi < c))) a b := by
  intro a ha b hb hst
  obtain ⟨-, -, ⟨t, ht, h1, h2⟩, ⟨t', ht', h3⟩⟩ := hst
  have ht1 := mem_filter.1 ht
  have ht2 := mem_filter.1 ht'
  have ha' := (mem_filter.1 ha).2
  have hb' := (mem_filter.1 hb).2
  have e1 : lo ≤ t ∧ t ≤ hi := by
    by_contra hc
    exact ht1.2.2 (mem_filter.2 ⟨ht1.1, by omega⟩)
  have e2 : lo ≤ t' ∧ t' ≤ hi := by
    by_contra hc
    exact ht2.2.2 (mem_filter.2 ⟨ht2.1, by omega⟩)
  omega

/-- **Numerator form of `pkR_b_R5a`**: for `n` even, `n ≥ 4`, `ε < 2`, under the arc hypothesis of
`pkR_b_R5a` and given two distinct legs `t₁ ≠ t₂` of `T`, `NP_n` vanishes at every point of `Z′`
(`N(P) ≡ 0` on `Z′`). -/
theorem pkR_b_R5a_NP {n ε : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) (hε : ε < 2) {R : Finset ℕ}
    {K : Finset (ℕ × ℕ)} {X : ℕ × ℕ → ℚ} (hZ : pkRBZ5 n ε R K X)
    (hRR : ∀ a ∈ R, ∀ b ∈ R, ¬ InST (pkRBT5 n ε R) a b) {t₁ t₂ : ℕ} (h1 : t₁ ∈ pkRBT5 n ε R)
    (h2 : t₂ ∈ pkRBT5 n ε R) (h12 : t₁ ≠ t₂) :
    MvPolynomial.eval X (NP ℚ n) = 0 := by
  have hsub : ({t₁, t₂} : Finset ℕ) ⊆ pkRBT5 n ε R := by
    intro x hx
    rw [mem_insert, mem_singleton] at hx
    rcases hx with h | h <;> rw [h] <;> assumption
  have hc := card_le_card hsub
  rw [card_pair h12] at hc
  have hadm : Admissible n (1 - ε) (pkRBT5 n ε R) := by
    change pkRBT5 n ε R ⊆ Icc 1 n ∧ 2 ≤ (pkRBT5 n ε R).card ∧ ∀ t ∈ pkRBT5 n ε R,
        t % 2 = 1 - ε
    refine ⟨filter_subset _ _, hc, fun t ht => ?_⟩
    have := (mem_filter.1 ht).2.1
    omega
  exact pkR_STnum hn hE (by omega) hadm X (pkR_b_R5a hZ hRR)

/-- For an odd chord `Q = (p, q)` of the `n`-gon (`n` even), a leg outside `A_Q = [p, q − 1]`, of
`q`'s parity, other than `q`. -/
theorem pkR_b_outer2 {n p q : ℕ} (hE : n % 2 = 0) (hQ : (p, q) ∈ oddDiagonals n) :
    ∃ o : ℕ, o ∈ Icc 1 n ∧ ¬ (p ≤ o ∧ o < q) ∧ o ≠ q ∧ o % 2 = q % 2 := by
  have hQd := mem_filter.1 hQ
  rw [mem_diagonals] at hQd
  dsimp only at hQd
  by_cases h : q + 2 ≤ n
  · exact ⟨q + 2, mem_Icc.2 ⟨by omega, h⟩, by omega, by omega, by omega⟩
  · exact ⟨p - 1, mem_Icc.2 ⟨by omega, by omega⟩, by omega, by omega, by omega⟩

/-- For an odd chord `Q = (p, q)` of the `n`-gon (`n` even), a leg outside `A_Q = [p, q − 1]` of
`p`'s parity. -/
theorem pkR_b_outer1 {n p q : ℕ} (hE : n % 2 = 0) (hQ : (p, q) ∈ oddDiagonals n) :
    ∃ o : ℕ, o ∈ Icc 1 n ∧ ¬ (p ≤ o ∧ o < q) ∧ o % 2 = p % 2 := by
  have hQd := mem_filter.1 hQ
  rw [mem_diagonals] at hQd
  dsimp only at hQd
  by_cases h : q + 1 ≤ n
  · exact ⟨q + 1, mem_Icc.2 ⟨by omega, h⟩, by omega, by omega⟩
  · exact ⟨p - 2, mem_Icc.2 ⟨by omega, by omega⟩, by omega, by omega⟩

/-- `e_i − e_o` as a function of the leg. -/
def pkRBE1 (i o : ℕ) : ℕ → ℚ := fun a => (if a = i then 1 else 0) - (if a = o then 1 else 0)

/-- The four-entry Gram matrix `(e_{i₁} − e_{o₁})(e_{i₂} − e_{o₂})ᵀ + transpose`. -/
def pkRBC4 (i₁ o₁ i₂ o₂ : ℕ) : ℕ → ℕ → ℚ :=
  fun a b => pkRBE1 i₁ o₁ a * pkRBE1 i₂ o₂ b + pkRBE1 i₂ o₂ a * pkRBE1 i₁ o₁ b

theorem pkR_b_e1_sum {n i o : ℕ} (hi : i ∈ Icc 1 n) (ho : o ∈ Icc 1 n) :
    Finset.sum (Icc 1 n) (fun b => pkRBE1 i o b) = 0 := by
  simp only [pkRBE1, sum_sub_distrib, sum_ite_eq', ite_eq_left hi, ite_eq_left ho, sub_self]

/-- **The four-entry Gram witness**: if `i₁ ≠ i₂` lie in `A_Q = [p, q − 1]` and `o₁ ≠ o₂` outside it
(all four legs in `1..n`), the Gram point of `pkRBC4 i₁ o₁ i₂ o₂` has `c_{a,b} = 0` for every leg
`a ∉ {i₁, o₁, i₂, o₂}` and every leg `b`, and `X_{p,q} = −1`. -/
theorem pkR_b_wit4 {n p q i₁ o₁ i₂ o₂ : ℕ} (hn : 1 ≤ n)
    (hi₁ : i₁ ∈ Icc 1 n) (hi₂ : i₂ ∈ Icc 1 n) (ho₁ : o₁ ∈ Icc 1 n) (ho₂ : o₂ ∈ Icc 1 n)
    (hi₁A : p ≤ i₁ ∧ i₁ < q) (hi₂A : p ≤ i₂ ∧ i₂ < q) (ho₁A : ¬ (p ≤ o₁ ∧ o₁ < q))
    (ho₂A : ¬ (p ≤ o₂ ∧ o₂ < q)) (hii : i₁ ≠ i₂) (hoo : o₁ ≠ o₂) :
    (∀ a ∈ Icc 1 n, ∀ b ∈ Icc 1 n, a ≠ i₁ → a ≠ o₁ → a ≠ i₂ → a ≠ o₂ →
      mesh n (pkRGramPt (pkRBC4 i₁ o₁ i₂ o₂)) a b = 0) ∧ pkRGramPt (pkRBC4 i₁ o₁ i₂ o₂)
          (p, q) = -1 := by
  have hs : ∀ a b, pkRBC4 i₁ o₁ i₂ o₂ a b = pkRBC4 i₁ o₁ i₂ o₂ b a := by
    intro a b
    simp only [pkRBC4]
    ring
  have hd : ∀ a, pkRBC4 i₁ o₁ i₂ o₂ a a = 0 := by
    intro a
    simp only [pkRBC4, pkRBE1]
    split_ifs <;> first | omega | norm_num
  have hr : ∀ a ∈ Icc 1 n, Finset.sum (Icc 1 n) (fun b => pkRBC4 i₁ o₁ i₂ o₂ a b) = 0 := by
    intro a _
    simp only [pkRBC4]
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, pkR_b_e1_sum hi₂ ho₂, pkR_b_e1_sum hi₁ ho₁]
    ring
  refine ⟨fun a ha b hb h1 h2 h3 h4 => ?_, ?_⟩
  · by_cases hab : a = b
    · rw [hab]
      exact pkR_mesh_self hn _ b
    · rw [pkR_gram hn _ hs hd hr ha hb hab]
      simp only [pkRBC4, pkRBE1, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
          ite_eq_right h4]
      ring
  · change pkRArcX (pkRBC4 i₁ o₁ i₂ o₂) p q = -1
    rw [pkR_arcX_def]
    have e : ∀ d ∈ Ico p q, Finset.sum (Ico p d) (fun c => pkRBC4 i₁ o₁ i₂ o₂ c d) =
        (if d = i₂ then (if p ≤ i₁ ∧ i₁ < d then (1 : ℚ) else 0) else 0) +
          (if d = i₁ then (if p ≤ i₂ ∧ i₂ < d then (1 : ℚ) else 0) else 0) := by
      intro d hd
      have hd' := mem_Ico.1 hd
      have e2 : ∀ c ∈ Ico p d, pkRBC4 i₁ o₁ i₂ o₂ c d =
          (if c = i₁ then (if d = i₂ then (1 : ℚ) else 0) else 0) +
            (if c = i₂ then (if d = i₁ then (1 : ℚ) else 0) else 0) := by
        intro c hc
        have hc' := mem_Ico.1 hc
        simp only [pkRBC4, pkRBE1, ite_eq_right (show c ≠ o₁ by omega),
            ite_eq_right (show c ≠ o₂ by omega),
          ite_eq_right (show d ≠ o₁ by omega), ite_eq_right (show d ≠ o₂ by omega)]
        split_ifs <;> norm_num
      rw [sum_congr rfl e2, sum_add_distrib]
      simp only [sum_ite_eq', mem_Ico]
      split_ifs <;> first | omega | norm_num
    rw [sum_congr rfl e, sum_add_distrib]
    simp only [sum_ite_eq', mem_Ico]
    split_ifs <;> first | omega | norm_num

/-- **`X_Q ≢ 0` on `Z′`, run inside `A_Q`**: for an odd chord `Q = (p, q)` of the `n`-gon (`n`
even), a run `R ⊆ A_Q` and a leg `r₀ ∈ R` of `p`'s parity, there is a point of `Z′` (`ε = p % 2`,
every `K`) with `X_Q ≠ 0`. -/
theorem pkR_b_R5c2 {n : ℕ} (hE : n % 2 = 0) {p q : ℕ} (hQ : (p, q) ∈ oddDiagonals n)
    {R : Finset ℕ} (hR : ∀ r ∈ R, p ≤ r ∧ r < q) {r₀ : ℕ} (hr₀ : r₀ ∈ R) (hr₀p : r₀ % 2 = p % 2)
    (K : Finset (ℕ × ℕ)) : ∃ X : ℕ × ℕ → ℚ, pkRBZ5 n (p % 2) R K X ∧ X (p, q) ≠ 0 := by
  have hQd := mem_filter.1 hQ
  rw [mem_diagonals] at hQd
  dsimp only at hQd
  have hRn : R ⊆ Icc 1 n := fun r hr => by have := hR r hr; exact mem_Icc.2 ⟨by omega, by omega⟩
  have h0 := hR r₀ hr₀
  obtain ⟨o, ho, hoA, hoq, hop⟩ := pkR_b_outer2 hE hQ
  obtain ⟨h1, h2⟩ := pkR_b_wit4 (p := p) (q := q) (i₁ := r₀) (o₁ := q) (i₂ := p + 1)
      (o₂ := o) (by omega)
    (mem_Icc.2 ⟨by omega, by omega⟩) (mem_Icc.2 ⟨by omega, by omega⟩)
        (mem_Icc.2 ⟨by omega, by omega⟩) ho
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) hoA (by omega) (Ne.symm hoq)
  refine ⟨_, pkR_b_Z5_rows hRn K (fun a ha b hb ha1 ha2 => h1 a ha b hb (fun e => ha2 (e ▸ hr₀))
    (by omega) (by omega) (fun e => by rw [e] at ha1; omega)), ?_⟩
  rw [h2]
  norm_num

/-- **`X_Q ≢ 0` on `Z′`, run outside `A_Q`**: for an odd chord `Q = (p, q)` of the `n`-gon (`n`
even), a run `R ⊆ [1, n]` outside `A_Q` and a leg `r₀ ∈ R` of `q`'s parity, there is a point of `Z′`
(`ε = q % 2`, every `K`) with `X_Q ≠ 0`. -/
theorem pkR_b_R5c1 {n : ℕ} (hE : n % 2 = 0) {p q : ℕ} (hQ : (p, q) ∈ oddDiagonals n)
    {R : Finset ℕ} (hRn : R ⊆ Icc 1 n) (hR : ∀ r ∈ R, r < p ∨ q ≤ r) {r₀ : ℕ} (hr₀ : r₀ ∈ R)
    (hr₀q : r₀ % 2 = q % 2) (K : Finset (ℕ × ℕ)) : ∃ X : ℕ × ℕ → ℚ, pkRBZ5 n (q % 2) R K X ∧
        X (p, q) ≠ 0 := by
  have hQd := mem_filter.1 hQ
  rw [mem_diagonals] at hQd
  dsimp only at hQd
  have h0 := hR r₀ hr₀
  have h0' := mem_Icc.1 (hRn hr₀)
  obtain ⟨o, ho, hoA, hop⟩ := pkR_b_outer1 hE hQ
  obtain ⟨h1, h2⟩ := pkR_b_wit4 (p := p) (q := q) (i₁ := p) (o₁ := r₀) (i₂ := p + 2)
      (o₂ := o) (by omega)
    (mem_Icc.2 ⟨by omega, by omega⟩) (mem_Icc.2 ⟨by omega, by omega⟩) (hRn hr₀) ho
    ⟨le_rfl, by omega⟩ ⟨by omega, by omega⟩ (by omega) hoA (by omega)
        (fun e => by rw [e] at hr₀q; omega)
  refine ⟨_, pkR_b_Z5_rows hRn K (fun a ha b hb ha1 ha2 => h1 a ha b hb (by omega)
    (fun e => ha2 (e ▸ hr₀)) (by omega) (fun e => by rw [e] at ha1; omega)), ?_⟩
  rw [h2]
  norm_num

/-- **The ear lemma for one chord, run inside `A_Q`**: for an odd chord `Q = (p, q)` of the `n`-gon
(`n` even, `n ≥ 4`) and a run `R = [lo, hi] ⊆ A_Q` whose first leg has `p`'s parity, the ¬Q
numerator `pkRBNP ℚ n {Q}` vanishes on `Z′` (`ε = p % 2`, `K = {Q}`); the grouping is the single
split `pkR_b_res1` (`C7`). -/
theorem pkR_b_R5one2 {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {p q lo hi : ℕ}
    (hQ : (p, q) ∈ oddDiagonals n) (hlo : p ≤ lo) (hlh : lo ≤ hi) (hhi : hi < q)
    (hlo2 : lo % 2 = p % 2) :
    ∀ X ∈ {X : ℕ × ℕ → ℚ | pkRBZ5 n (p % 2) (Icc lo hi) {(p, q)} X},
      MvPolynomial.eval X (pkRBNP ℚ n {(p, q)}) = 0 := by
  have hQd := mem_filter.1 hQ
  rw [mem_diagonals] at hQd
  dsimp only at hQd
  have hR : ∀ r ∈ Icc lo hi, p ≤ r ∧ r < q := fun r hr => by have := mem_Icc.1 hr; omega
  refine pkR_prime (pkR_b_Z5_sub n (p % 2) (Icc lo hi) {(p, q)}) (ℓ := MvPolynomial.X (p, q)) ?_ ?_
  · obtain ⟨w, hw, hw0⟩ := pkR_b_R5c2 hE hQ hR (mem_Icc.2 ⟨le_rfl, hlh⟩) hlo2 {(p, q)}
    exact ⟨w, hw, by rw [MvPolynomial.eval_X]; exact hw0⟩
  · intro x hx
    have hx' : pkRBZ5 n (p % 2) (Icc lo hi) {(p, q)} x := hx
    obtain ⟨o, ho, hoA, hoq, hop⟩ := pkR_b_outer2 hE hQ
    have hN : MvPolynomial.eval x (NP ℚ n) = 0 :=
      pkR_b_R5a_NP hE hn (by omega) hx' pkR_b_ivl_RR (t₁ := q) (t₂ := o)
        (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega, fun h =>
            by have := mem_Icc.1 h; omega⟩)
        (mem_filter.2 ⟨ho, by omega, fun h => by have := mem_Icc.1 h; omega⟩) (Ne.symm hoq)
    have h2 := pkR_b_R5b2_NP hE hn hQ (mem_singleton_self _) hR hx'
    have hres := congrArg (MvPolynomial.eval x) (pkR_b_res1 (R := ℚ) hn hE hQ)
    simp only [map_add, map_mul] at hres
    rw [hN, h2, mul_zero, zero_mul, add_zero] at hres
    exact hres.symm

/-- **The ear lemma for one chord, run outside `A_Q`** (the mirror of `pkR_b_R5one2`): for an odd
chord `Q = (p, q)` of the `n`-gon (`n` even, `n ≥ 4`) and `A_Q ⊆ [lo, hi]`, if the run
`R = [1, n] ∖ [lo, hi]` has a leg of `q`'s parity, the ¬Q numerator of the `n`-gon vanishes on `Z′`
(`ε = q % 2`, `K = {Q}`). -/
theorem pkR_b_R5one1 {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {p q lo hi : ℕ}
    (hQ : (p, q) ∈ oddDiagonals n) (hlo : lo ≤ p) (hhi : q ≤ hi + 1) {r₀ : ℕ}
    (hr₀ : r₀ ∈ (Icc 1 n).filter (fun c => c < lo ∨ hi < c)) (hr₀q : r₀ % 2 = q % 2) :
    ∀ X ∈ {X : ℕ × ℕ → ℚ | pkRBZ5 n (q % 2) ((Icc 1 n).filter (fun c => c < lo ∨ hi < c))
        {(p, q)} X},
      MvPolynomial.eval X (pkRBNP ℚ n {(p, q)}) = 0 := by
  have hQd := mem_filter.1 hQ
  rw [mem_diagonals] at hQd
  dsimp only at hQd
  have hRn : (Icc 1 n).filter (fun c => c < lo ∨ hi < c) ⊆ Icc 1 n := filter_subset _ _
  have hR : ∀ r ∈ (Icc 1 n).filter (fun c => c < lo ∨ hi < c), r < p ∨ q ≤ r := fun r hr => by
    have := (mem_filter.1 hr).2
    omega
  refine pkR_prime (pkR_b_Z5_sub n (q % 2) _ {(p, q)}) (ℓ := MvPolynomial.X (p, q)) ?_ ?_
  · obtain ⟨w, hw, hw0⟩ := pkR_b_R5c1 hE hQ hRn hR hr₀ hr₀q {(p, q)}
    exact ⟨w, hw, by rw [MvPolynomial.eval_X]; exact hw0⟩
  · intro x hx
    have hx' : pkRBZ5 n (q % 2) ((Icc 1 n).filter (fun c => c < lo ∨ hi < c)) {(p, q)} x := hx
    have hN : MvPolynomial.eval x (NP ℚ n) = 0 :=
      pkR_b_R5a_NP hE hn (by omega) hx' pkR_b_coivl_RR (t₁ := p) (t₂ := p + 2)
        (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega, fun h =>
            by have := (mem_filter.1 h).2; omega⟩)
        (mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega, fun h =>
            by have := (mem_filter.1 h).2; omega⟩)
        (by omega)
    have h1 := pkR_b_R5b1_NP hE hn hQ (mem_singleton_self _) hR hx'
    have hres := congrArg (MvPolynomial.eval x) (pkR_b_res1 (R := ℚ) hn hE hQ)
    simp only [map_add, map_mul] at hres
    rw [hN, h1, zero_mul, zero_mul, add_zero] at hres
    exact hres.symm


/-! #### The region point on `Λ^I`, and the rotated B-child

The region point lies on `Λ^I` for a whole set `I` of members (`pkR_b_omegaLam`); the B-child
`childSetB` (`C0`) rotated by one leg (`pkRBChildB'`). -/

/-- **The region point on `Λ^I`**: let `Q ≠ Q′` be odd chords of the `N`-gon (`N` even) with
`A_{Q′} ⊆ A_Q`, at a point where the mesh variables of the pairs of `pkRBTP N Q Q′` (`C7`) vanish.
For a set `J` of odd chords `Q″ ≠ Q` with `A_{Q′} ⊆ A_{Q″} ⊆ A_Q` whose parent `minRect` mesh
variables vanish, the region point `pkRBOmX N Q Q′ X` lies on `Λ^I`,
`I = J.image (pkRBOmI N Q Q′)`. -/
theorem pkR_b_omegaLam {N : ℕ} (hE : N % 2 = 0) {Q Q' : ℕ × ℕ} (hQ : Q ∈ oddDiagonals N)
    (hQ' : Q' ∈ oddDiagonals N) (hsub : oddSide N Q' ⊆ oddSide N Q) (hne : Q ≠ Q') {X : ℕ × ℕ → ℚ}
    (hT : ∀ a b, (a, b) ∈ diagonals N → pkRBTP N Q Q' a b → mesh N X a b = 0)
    {J : Finset (ℕ × ℕ)} (hJ : ∀ Q'' ∈ J, Q'' ∈ oddDiagonals N ∧ oddSide N Q' ⊆ oddSide N Q'' ∧
      oddSide N Q'' ⊆ oddSide N Q ∧ Q ≠ Q'' ∧ ∀ t ∈ minRect N Q'', mesh N X t.1 t.2 = 0) :
    pkRLam (pkRBOmM N Q Q') (pkRBOmD N Q Q') (J.image (pkRBOmI N Q Q'))
        (pkRBOmX N Q Q' X) := by
  obtain ⟨h0, -, -⟩ := pkR_b_omegaTiles hE hQ hQ' hsub hne hT
  refine ⟨h0.1, h0.2.1, fun I hI => ?_⟩
  obtain ⟨Q'', hQ'', rfl⟩ := mem_image.1 hI
  obtain ⟨a1, a2, a3, a4, a5⟩ := hJ Q'' hQ''
  exact pkR_b_omegaMem hE hQ hQ' a1 hsub hne a2 a3 a4 a5

-- registry: T-M79D
/-- The B-child of `P` in the `relab N (tailStart P)` labelling: child leg
`j ↦ vtx N (tailStart P + j − 1)`, with `P̂` the last child leg `tailLen N P + 1`. It is `childSetB`
(`C0`), whose `P̂` is child leg `1`, rotated by one leg (`pkR_b_childB_rot`). -/
def pkRBChildB' (N : ℕ) (S : Finset (ℕ × ℕ)) (P : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  (diagonals (tailLen N P + 1)).filter (fun σ => ChildPairIn N S (tailStart P) (tailLen N P)
      (tailLen N P + 1)
    (fun j => vtx N (tailStart P + j - 1)) σ.1 σ.2)

/-- `ChildPairIn` under the rotation `k ↦ k + 1` of child legs (hat `1` ↦ hat `m`), for `m ≥ 3`. -/
theorem pkR_b_cpi_rot {N m s k : ℕ} (S : Finset (ℕ × ℕ)) (hm : 3 ≤ m) {j l : ℕ}
    (hd : (j, l) ∈ diagonals m) :
    (npair m (j + 1) (l + 1) ∈ diagonals m ∧
      ChildPairIn N S s k 1 (fun i => vtx N (s + i - 2))
          (npair m (j + 1) (l + 1)).1 (npair m (j + 1) (l + 1)).2) ↔
    ChildPairIn N S s k m (fun i => vtx N (s + i - 1)) j l := by
  have hd' := mem_diagonals.1 hd
  dsimp only at hd'
  have e : npair m (j + 1) (l + 1) =
      (min (vtx m (j + 1)) (vtx m (l + 1)), max (vtx m (j + 1)) (vtx m (l + 1))) := rfl
  have vj : vtx m (j + 1) = j + 1 := vtx_of_mem (by omega) (by omega)
  rcases (show l + 1 ≤ m ∨ l = m by omega) with hl | hl
  · have vl : vtx m (l + 1) = l + 1 := vtx_of_mem (by omega) hl
    rw [e, vj, vl, min_eq_left (by omega), max_eq_right (by omega)]
    unfold ChildPairIn
    dsimp only
    rw [ite_eq_right (show j + 1 ≠ 1 by omega), ite_eq_right (show l + 1 ≠ 1 by omega),
        ite_eq_right (show j ≠ m by omega),
      ite_eq_right (show l ≠ m by omega), show s + (j + 1) - 2 =
          s + j - 1 by omega, show s + (l + 1) - 2 = s + l - 1 by omega]
    exact ⟨fun h => h.2, fun h => ⟨mem_diagonals.2 (by dsimp only; omega), h⟩⟩
  · have vl : vtx m (l + 1) = 1 :=
      by rw [hl, show m + 1 = 1 + m by omega, vtx_add_n, vtx_of_mem le_rfl (by omega)]
    rw [e, vj, vl, min_eq_right (by omega), max_eq_left (by omega)]
    unfold ChildPairIn
    dsimp only
    rw [ite_eq_left rfl, ite_eq_right (show j ≠ m by omega), ite_eq_left hl, show s + (j + 1) - 2 =
        s + j - 1 by omega]
    exact ⟨fun h => h.2, fun h => ⟨mem_diagonals.2 (by dsimp only; omega), h⟩⟩

/-- **The rotated `childSetB`**: for `tailLen N P + 1 ≥ 3`, the rotated B-child set of
`pkR_b_nonzero_rot` (`C7`) is `pkRBChildB'`.
-/
theorem pkR_b_childB_rot {N : ℕ} (S : Finset (ℕ × ℕ)) (P : ℕ × ℕ) (h3 : 3 ≤ tailLen N P + 1) :
    (diagonals (tailLen N P + 1)).filter (fun d => npair (tailLen N P + 1) (d.1 + 1)
        (d.2 + 1) ∈ childSetB N S P) =
      pkRBChildB' N S P := by
  ext ⟨j, l⟩
  rw [mem_filter, pkRBChildB', mem_filter]
  constructor
  · rintro ⟨hd, hc⟩
    exact ⟨hd, (pkR_b_cpi_rot S h3 hd).1 (mem_filter.1 hc)⟩
  · rintro ⟨hd, hc⟩
    exact ⟨hd, mem_filter.2 ((pkR_b_cpi_rot S h3 hd).2 hc)⟩

/-- For an even child size `tailLen N P + 1 ≥ 4`, `NonzeroOn` for the B-child `childSetB N S P`
gives `NonzeroOn` for `pkRBChildB' N S P`, the B-child in the `relab N (tailStart P)` labelling.
-/
theorem pkR_b_nonzero_B' {N : ℕ} {S : Finset (ℕ × ℕ)} {P : ℕ × ℕ} (h4 : 4 ≤ tailLen N P + 1)
    (hE : (tailLen N P + 1) % 2 = 0) (h : NonzeroOn (tailLen N P + 1) (childSetB N S P)) :
    NonzeroOn (tailLen N P + 1) (pkRBChildB' N S P) := by
  have h' := pkR_b_nonzero_rot h4 hE h
  rwa [pkR_b_childB_rot S P (by omega)] at h'


/-! #### The A-child of a chord on `Z′`

On `T(Q, b)` (`pkRBOT`, `C7`) with `X_Q = 0` and the `minRect(Q″)` blocks zero, the A-child of `Q`
lies on `Z′` (`pkR_b_R6Z5`); this connects `pkR_b_Atile` (`C7`) to the ear lemma. -/

/-- **The A-child of `Q` on `Z′`** (all of (z1)–(z3)): in the A-child of `Q` (list
`pkRBOmL N a (L − 1) 1`, `m = L + 1`, `s` = child leg `m`), with `R` = the child legs
`[p + 1, p + L′]` of `A_b` and `μ⁺` = the odd child legs, the child point lies on `Z′` for the
members `J` (positional chords `(p″, L″)` ↦ child chords `(p″ + 1, p″ + L″ + 1)`, `A_b ⊆ A_{Q″}`)
whenever `T(Q, b)` (`pkRBOT`, `C7`), `X_Q = 0` and every `minRect(Q″)` (positional) hold. Here
`L`, `L′` are odd and `p` even, with `p + L′ ≤ L`, `L′ + 2 ≤ L` and `L < N`. With `J = ∅` or
`J = {b}` this is the input of `pkR_b_R5one2` on the child. -/
theorem pkR_b_R6Z5 {N a p L L' : ℕ} (hN : 1 ≤ N) (ha : 1 ≤ a ∧ a ≤ N) (hL : L % 2 = 1)
    (hp : p % 2 = 0) (hL' : L' % 2 = 1) (hpL : p + L' ≤ L) (hLL : L' + 2 ≤ L) (hLN : L < N)
    {X : ℕ × ℕ → ℚ} (hT : pkRBOT N a p L L' X) (hXQ : planar N X a (a + L) = 0)
    {J : Finset (ℕ × ℕ)}
    (hJ : ∀ c ∈ J, c.1 % 2 = 0 ∧ c.2 % 2 = 1 ∧ c.1 ≤ p ∧ p + L' ≤ c.1 + c.2 ∧ c.1 + c.2 ≤ L ∧
      ∀ i j, c.1 ≤ i → i < c.1 + c.2 → i % 2 = 1 → (j < c.1 ∨ c.1 + c.2 ≤ j) → j < L → j % 2 = 0 →
        mesh N X (vtx N (a + i)) (vtx N (a + j)) = 0) :
    pkRBZ5 (L - 1 + 2) 1 (Icc (p + 1) (p + L')) (J.image (fun c => (c.1 + 1, c.1 + c.2 + 1)))
      (pkRSubX N (pkRBOmL N a (L - 1) 1) X) := by
  obtain ⟨HT1, HT2, -⟩ := (pkR_b_OT_iff N a p L L' X).1 hT
  have tile2 : ∀ k l, 1 ≤ k → 1 ≤ l → k ≤ L → l ≤ L → (k + 2 ≤ l ∨ l + 2 ≤ k) →
      mesh (L - 1 + 2) (pkRSubX N (pkRBOmL N a (L - 1) 1) X) k l =
        mesh N X (vtx N (a + (k - 1))) (vtx N (a + (l - 1))) := by
    intro k l h1 h2 h3 h4 h5
    rcases h5 with h5 | h5
    · rw [pkR_b_Atile hN ha hL (by omega) hLN X h1 h5 h4, hXQ, ite_self, add_zero]
    · rw [pkR_mesh_comm, pkR_b_Atile hN ha hL (by omega) hLN X h2 h5 h3, hXQ, ite_self, add_zero,
        pkR_mesh_comm]
  unfold pkRBZ5
  refine ⟨fun k hk l hl hk1 hkR hl1 hlR => ?_, fun k hk hk1 hkR w hw => ?_,
    fun c hc w hw k hk hw1 hk1 _ hside hout => ?_⟩
  · have hk' := mem_Icc.1 hk
    have hl' := mem_Icc.1 hl
    rw [mem_Icc] at hkR hlR
    by_cases hkl : k = l
    · rw [hkl]
      exact pkR_mesh_self (by omega) _ l
    rw [tile2 k l (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact HT1 (k - 1) (l - 1) (by omega) (by omega) (by omega) (by omega)
  · have hk' := mem_Icc.1 hk
    have hw' := mem_Icc.1 hw
    rw [mem_Icc] at hkR
    rw [tile2 k w (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact HT2 (k - 1) (w - 1) (by omega) (by omega) (by omega) (by omega)
  · obtain ⟨c', hc', rfl⟩ := mem_image.1 hc
    obtain ⟨j1, j2, j3, j4, j5, hM⟩ := hJ c' hc'
    have hr0 : p + 1 ∈ Icc (p + 1) (p + L') := mem_Icc.2 ⟨le_rfl, by omega⟩
    have s1 : c'.1 + 1 ≤ w ∧ w < c'.1 + c'.2 + 1 :=
      (hside (p + 1) hr0).2 (show c'.1 + 1 ≤ p + 1 ∧ p + 1 < c'.1 + c'.2 + 1 by omega)
    have s3 : ¬ (c'.1 + 1 ≤ k ∧ k < c'.1 + c'.2 + 1) := fun h =>
      hout (p + 1) hr0 (iff_of_true h (show c'.1 + 1 ≤ p + 1 ∧ p + 1 < c'.1 + c'.2 + 1 by omega))
    have hw' := mem_Icc.1 hw
    have hk' := mem_Icc.1 hk
    rw [tile2 w k (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact hM (w - 1) (k - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-! #### The B-child of a chord on `Z′`

`T(t, Q)` read from the tail start of `Q` is again a `pkRBOT` (`pkR_b_OT_swap`), so `pkR_b_R6Z5`
applies to the B-child of `Q` (list `pkRBOmL N a′ (N − L′ − 1) 1`, `a′` = the first leg of `B_Q`).
-/

/-- Moving the base of a position reading by `s` legs:
`vtx N (vtx N (a + s) + i) = vtx N (a + (s + i) % N)` for `a ∈ [1, N]` and `s, i < N`. The
hypothesis `1 ≤ N` is not used. -/
theorem pkR_b_vtx_sh {N a s i : ℕ} (_hN : 1 ≤ N) (ha : 1 ≤ a ∧ a ≤ N) (hs : s < N) (hi : i < N) :
    vtx N (vtx N (a + s) + i) = vtx N (a + (s + i) % N) := by
  have key : ∀ x y : ℕ, (x = y ∨ x = y + N ∨ y = x + N) → vtx N x = vtx N y := by
    intro x y h
    rcases h with h | h | h
    · rw [h]
    · rw [h, vtx_add_n]
    · rw [h, vtx_add_n]
  have m := pkR_b_mod2 (N := N) (z := s + i) (by omega)
  have v1 := pkR_b_vtx2 (N := N) (u := a + s) (by omega) (by omega)
  rcases v1 with ⟨v1a, v1b⟩ | ⟨v1a, v1b⟩ <;> rw [v1b] <;> rcases m with ⟨m1, m2⟩ |
      ⟨m1, m2⟩ <;> rw [m2] <;>
    exact key _ _ (by omega)

/-- **`T(Q, Q′)` is symmetric under the change of base** `a ↦ a + p + L′` (from the head start of
`Q` to the tail start of `Q′`): for `N` even, `p` even, `L′` odd and `p + L′ ≤ L < N`, the same set
of pairs, read as `T` of the mirrored pair (μ strips swapped, `A_{Q′}` ↔ `B_Q`). -/
theorem pkR_b_OT_swap {N a p L L' : ℕ} (hN : 1 ≤ N) (hE : N % 2 = 0) (ha : 1 ≤ a ∧ a ≤ N)
    (hp : p % 2 = 0) (hL' : L' % 2 = 1) (hpL : p + L' ≤ L) (hLN : L < N) {X : ℕ × ℕ → ℚ}
    (hT : pkRBOT N a p L L' X) :
    pkRBOT N (vtx N (a + (p + L'))) (L - p - L') (N - L') (N - L) X := by
  obtain ⟨H1, H2, H3⟩ := (pkR_b_OT_iff N a p L L' X).1 hT
  refine (pkR_b_OT_iff _ _ _ _ _ X).2 ⟨fun i j hi hj hij hne => ?_, fun i j hi hi2 hj1 hj2 => ?_,
    fun i j hi hi2 hj1 hj2 => ?_⟩
  · rw [pkR_b_vtx_sh hN ha (by omega) (show i < N by omega), pkR_b_vtx_sh hN ha (by omega)
      (show j < N by omega)]
    have mi := pkR_b_mod2 (N := N) (z := p + L' + i) (by omega)
    have mj := pkR_b_mod2 (N := N) (z := p + L' + j) (by omega)
    exact H1 _ _ (by omega) (by omega) (by omega) (by omega)
  · rw [pkR_b_vtx_sh hN ha (by omega) (show i < N by omega), pkR_b_vtx_sh hN ha (by omega)
      (show j < N by omega)]
    have mi := pkR_b_mod2 (N := N) (z := p + L' + i) (by omega)
    have mj := pkR_b_mod2 (N := N) (z := p + L' + j) (by omega)
    exact H3 _ _ (by omega) (by omega) (by omega) (by omega)
  · rw [pkR_b_vtx_sh hN ha (by omega) (show i < N by omega), pkR_b_vtx_sh hN ha (by omega)
      (show j < N by omega)]
    have mi := pkR_b_mod2 (N := N) (z := p + L' + i) (by omega)
    have mj := pkR_b_mod2 (N := N) (z := p + L' + j) (by omega)
    exact H2 _ _ (by omega) (by omega) (by omega) (by omega)

/-- **The B-child of `Q` on `Z′`** (all of (z1)–(z3), the B-side instance of `pkR_b_R6Z5`):
`T(t, Q)` in positions from `a = headStart t` (`A_Q` = positions `[p, p + L′)`), `X_Q = 0` at the
dual points of the B-child, and the `minRect(Q″)` blocks of the members `Q″` between (positions from
`a′ = vtx N (a + p + L′)`, the first leg of `B_Q`) put the B-child of `Q` (list
`pkRBOmL N a′ (N − L′ − 1) 1`; child leg `k` = parent leg `a′ + k − 1`) on `Z′` with `R` = the
child legs of `B_t` and `μ⁺` = the odd child legs (= the even legs of `μ`). The parities and bounds
are those of `pkR_b_R6Z5`, with `N` even. -/
theorem pkR_b_R6Z5B {N a p L L' : ℕ} (hN : 1 ≤ N) (hE : N % 2 = 0) (ha : 1 ≤ a ∧ a ≤ N)
    (hL : L % 2 = 1) (hp : p % 2 = 0) (hL' : L' % 2 = 1) (hpL : p + L' ≤ L) (hLL : L' + 2 ≤ L)
    (hLN : L < N) {X : ℕ × ℕ → ℚ} (hT : pkRBOT N a p L L' X)
    (hXQ : planar N X (vtx N (a + (p + L'))) (vtx N (a + (p + L')) + (N - L')) = 0)
    {J : Finset (ℕ × ℕ)}
    (hJ : ∀ c ∈ J, c.1 % 2 = 0 ∧ c.2 % 2 = 1 ∧ c.1 ≤ L - p - L' ∧ L - p - L' + (N - L) ≤ c.1 + c.2 ∧
      c.1 + c.2 ≤ N - L' ∧
      ∀ i j, c.1 ≤ i → i < c.1 + c.2 → i % 2 = 1 → (j < c.1 ∨ c.1 + c.2 ≤ j) → j <
          N - L' → j % 2 = 0 →
        mesh N X (vtx N (vtx N (a + (p + L')) + i)) (vtx N (vtx N (a + (p + L')) + j)) = 0) :
    pkRBZ5 (N - L' - 1 + 2) 1 (Icc (L - p - L' + 1) (L - p - L' + (N - L)))
      (J.image (fun c => (c.1 + 1, c.1 + c.2 + 1)))
      (pkRSubX N (pkRBOmL N (vtx N (a + (p + L'))) (N - L' - 1) 1) X) :=
  pkR_b_R6Z5 (a := vtx N (a + (p + L'))) (p := L - p - L') (L := N - L') (L' := N - L) hN
    (vtx_bounds N _ hN) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (pkR_b_OT_swap hN hE ha hp hL' hpL hLN hT) hXQ hJ

/-! #### Peeling a chain: the collapse identity

The top-down peeling of a chain by iterated `pkR_b_I3num` (`C7`; `pkR_b_R2top`) and its bottom-up
mirror (`pkR_b_R2bot`). Every step is a polynomial identity (over any `CommRing` domain); the
evaluation at `X_Q = x` comes last (`pkR_b_R2top_eval`). -/

/-- The glued term of one peeling step, children in head / tail form: `NP^{¬K}` of the A-child (head
side, `relab` base `headStart C`) times `NP^{¬K}` of the B-child (tail side, base `tailStart C`)
times the unbanned crossing chords. -/
noncomputable def pkRBTerm (R : Type*) [CommRing R] (N : ℕ) (K : Finset (ℕ × ℕ)) (C : ℕ × ℕ) :
    MvPolynomial (ℕ × ℕ) R :=
  MvPolynomial.rename (relab N (headStart C))
      (pkRBNP R (headLen N C + 1) (pkRBPull N (headStart C) (headLen N C + 1) K)) *
    MvPolynomial.rename (relab N (tailStart C))
      (pkRBNP R (tailLen N C + 1) (pkRBPull N (tailStart C) (tailLen N C + 1) K)) *
    pkRBCross R N K C

/-- **One peeling step** (`pkR_b_I3num` (`C7`) read forwards, children in head / tail form): over a
domain, for `N` even, `N ≥ 4` and `K ∪ {C}` a set of odd chords with `C ∉ K`, adding `C` to the
banned set gives `NP^{¬K}_N = X_C · NP^{¬(K ∪ C)}_N + term(K, C)`. -/
theorem pkR_b_step {R : Type*} [CommRing R] [IsDomain R] {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0)
    {K : Finset (ℕ × ℕ)} {C : ℕ × ℕ} (hK : insert C K ⊆ oddDiagonals N) (hC : C ∉ K) :
    pkRBNP R N K = MvPolynomial.X C * pkRBNP R N (insert C K) + pkRBTerm R N K C := by
  have hCo : C ∈ oddDiagonals N := hK (mem_insert_self C K)
  have hC2 := mem_diagonals.1 (mem_filter.1 hCo).1
  have h := pkR_b_I3num (R := R) hN hE hK (mem_insert_self C K)
  rw [erase_insert hC] at h
  rw [h]
  unfold pkRBTerm
  rcases pkR_b_head_data hCo with ⟨h1, hs, hl⟩ | ⟨h1, hs, hl⟩ <;>
    rcases pkR_b_tail_data hCo with ⟨h1', ts, tl⟩ | ⟨h1', ts, tl⟩
  · rw [hs, hl, ts, tl, show N - (C.2 - C.1) + 1 = N - C.2 + C.1 + 1 by omega]
  · omega
  · omega
  · rw [hs, hl, ts, tl, show N - (C.2 - C.1) + 1 = N - C.2 + C.1 + 1 by omega]
    ring

/-- **Peeling a sequence of chords**: over a domain, for `N` even, `N ≥ 4`, a set `K₀` of odd chords
and distinct odd chords `C 0, …, C (k−1)` not in `K₀`, with `K_i = K₀ ∪ {C j : j < i}`,
`NP^{¬K₀}_N = Σ_{i<k} (Π_{j<i} X_{C j}) · term(K_i, C i) + (Π_{j<k} X_{C j}) · NP^{¬K_k}_N`. -/
theorem pkR_b_peel {R : Type*} [CommRing R] [IsDomain R] {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0)
    (K₀ : Finset (ℕ × ℕ)) (C : ℕ → ℕ × ℕ) (k : ℕ) (hK₀ : K₀ ⊆ oddDiagonals N)
    (hC : ∀ i < k, C i ∈ oddDiagonals N) (hC₀ : ∀ i < k, C i ∉ K₀)
    (hinj : ∀ i < k, ∀ j < i, C j ≠ C i) :
    pkRBNP R N K₀ =
      Finset.sum (range k) (fun i => Finset.prod (range i) (fun j => MvPolynomial.X (C j)) *
        pkRBTerm R N (K₀ ∪ (range i).image C) (C i)) +
      Finset.prod (range k)
          (fun j => MvPolynomial.X (C j)) * pkRBNP R N (K₀ ∪ (range k).image C) := by
  induction k with
  | zero =>
    rw [sum_range_zero, prod_range_zero, range_zero, image_empty, union_empty, zero_add, one_mul]
  | succ k ih =>
    rw [ih (fun i hi => hC i (by omega)) (fun i hi => hC₀ i (by omega))
      (fun i hi j hj => hinj i (by omega) j hj)]
    have hnot : C k ∉ K₀ ∪ (range k).image C := by
      rw [mem_union, mem_image]
      rintro (h | ⟨j, hj, e⟩)
      · exact hC₀ k (by omega) h
      · exact hinj k (by omega) j (mem_range.1 hj) e
    have hsub : insert (C k) (K₀ ∪ (range k).image C) ⊆ oddDiagonals N := by
      intro d hd
      rw [mem_insert, mem_union, mem_image] at hd
      rcases hd with h | h | ⟨j, hj, e⟩
      · rw [h]
        exact hC k (by omega)
      · exact hK₀ h
      · rw [← e]
        exact hC j (by have := mem_range.1 hj; omega)
    have hins : insert (C k) (K₀ ∪ (range k).image C) = K₀ ∪ (range (k + 1)).image C := by
      rw [range_add_one, image_insert, union_insert]
    rw [pkR_b_step hN hE hsub hnot, hins, sum_range_succ, prod_range_succ]
    ring

/-- The crossing factor of a chord crossed by no banned chord is the full `crossProd`. -/
theorem pkR_b_cross_nc {R : Type*} [CommRing R] {N : ℕ} {K : Finset (ℕ × ℕ)} {C : ℕ × ℕ}
    (h : ∀ Q ∈ K, ¬ Crosses Q C) : pkRBCross R N K C = crossProd R N C := by
  change Finset.prod (((oddDiagonals N).filter (fun d => Crosses d C)) \ K)
      (fun d => MvPolynomial.X d) =
    crossProd R N C
  have e : ((oddDiagonals N).filter (fun d => Crosses d C)) \ K =
      (oddDiagonals N).filter (fun d => Crosses d C) := by
    refine sdiff_eq_self_of_disjoint (disjoint_left.2 fun d hd hdK => h d hdK (mem_filter.1 hd).2)
  rw [e]
  rfl

/-- A pull-back sees only the chords that are diagonals of the child: if `K₁ ⊆ K` and the chords of
`K ∖ K₁` pull back to nothing, the pull-backs of `K` and `K₁` agree. -/
theorem pkR_b_pull_mono {N b n : ℕ} {K K₁ : Finset (ℕ × ℕ)} (h1 : K₁ ⊆ K)
    (h2 : pkRBPull N b n (K \ K₁) = ∅) :
    pkRBPull N b n K = pkRBPull N b n K₁ := by
  ext d
  change d ∈ (diagonals n).filter (fun d => relab N b d ∈ K) ↔
      d ∈ (diagonals n).filter (fun d => relab N b d ∈ K₁)
  rw [mem_filter, mem_filter]
  constructor
  · rintro ⟨hd, hK⟩
    refine ⟨hd, ?_⟩
    by_contra hK1
    have hm : d ∈ pkRBPull N b n (K \ K₁) := mem_filter.2 ⟨hd, mem_sdiff.2 ⟨hK, hK1⟩⟩
    rw [h2] at hm
    simp at hm
  · rintro ⟨hd, hK1⟩
    exact ⟨hd, h1 hK1⟩

/-- **The peeling term of a chain member**: for an odd chord `C` and a set `K` of odd chords, if the
banned chords `K₁ ⊆ K` all have heads `⊇ A_C` and do not cross `C`, and every other chord of `K` has
head `⊆ A_C`, then `term(K₁, C)` = (full `NP` of the A-child of `C`) · (`NP^{¬K}` of the B-child of
`C`, i.e. `a_C`'s numerator) · `crossProd C`, by `pkR_b_R17_head` and `pkR_b_R17_tail` (`C7`). -/
theorem pkR_b_term_chain {R : Type*} [CommRing R] {N : ℕ} {K K₁ : Finset (ℕ × ℕ)} {C : ℕ × ℕ}
    (hC : C ∈ oddDiagonals N) (hK : K ⊆ oddDiagonals N) (h1 : K₁ ⊆ K)
    (hup : ∀ Q ∈ K₁, oddSide N C ⊆ oddSide N Q) (hdown : ∀ Q ∈ K \ K₁, oddSide N Q ⊆ oddSide N C)
    (hnc : ∀ Q ∈ K₁, ¬ Crosses Q C) :
    pkRBTerm R N K₁ C =
      MvPolynomial.rename (relab N (headStart C)) (NP R (headLen N C + 1)) *
        MvPolynomial.rename (relab N (tailStart C))
          (pkRBNP R (tailLen N C + 1) (pkRBPull N (tailStart C) (tailLen N C + 1) K)) *
        crossProd R N C := by
  unfold pkRBTerm
  rw [pkR_b_R17_head hC (fun Q hQ => hK (h1 hQ)) hup, pkR_b_NP_empty, pkR_b_cross_nc hnc,
    pkR_b_pull_mono h1 (pkR_b_R17_tail hC (fun Q hQ => hK (mem_sdiff.1 hQ).1) hdown)]

/-- **The top-down collapse**: over a domain, for `N` even, `N ≥ 4`, and a chain of odd chords
`C 0 ≻ C 1 ≻ … ≻ C (k−1)` (heads decreasing, `A_{C j} ⊆ A_{C i}` for `i ≤ j`; pairwise distinct and
non-crossing) that is all of `K`,
`NP_N = Σ_{i<k} (Π_{j<i} X_{C j}) · NP_{A(C i)} · NP^{¬K}_{B(C i)} · crossProd(C i)` +
`(Π_{j<k} X_{C j}) · NP^{¬K}_N`. -/
theorem pkR_b_R2top {R : Type*} [CommRing R] [IsDomain R] {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0)
    (C : ℕ → ℕ × ℕ) (k : ℕ) (hC : ∀ i < k, C i ∈ oddDiagonals N)
    (hinj : ∀ i < k, ∀ j < i, C j ≠ C i)
    (hord : ∀ i < k, ∀ j < k, i ≤ j → oddSide N (C j) ⊆ oddSide N (C i))
    (hnc : ∀ i < k, ∀ j < k, ¬ Crosses (C j) (C i)) :
    NP R N =
      Finset.sum (range k) (fun i => Finset.prod (range i) (fun j => MvPolynomial.X (C j)) *
        (MvPolynomial.rename (relab N (headStart (C i))) (NP R (headLen N (C i) + 1)) *
          MvPolynomial.rename (relab N (tailStart (C i)))
            (pkRBNP R (tailLen N (C i) + 1)
              (pkRBPull N (tailStart (C i)) (tailLen N (C i) + 1) ((range k).image C))) *
          crossProd R N (C i))) +
      Finset.prod (range k) (fun j => MvPolynomial.X (C j)) * pkRBNP R N ((range k).image C) := by
  have hK : (range k).image C ⊆ oddDiagonals N := by
    intro d hd
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hd
    exact hC j (mem_range.1 hj)
  have h := pkR_b_peel (R := R) hN hE ∅ C k (empty_subset _) hC (fun i _ h => by simp at h) hinj
  rw [pkR_b_NP_empty] at h
  simp only [empty_union] at h
  rw [h]
  refine congrArg₂ (· + ·) (sum_congr rfl fun i hi => ?_) rfl
  have hi' := mem_range.1 hi
  rw [pkR_b_term_chain (R := R)
      (hC i hi') hK (image_subset_image (range_subset_range.2 (show i ≤ k by omega))) ?_ ?_ ?_]
  · intro Q hQ
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hQ
    exact hord j (by have := mem_range.1 hj; omega) i hi' (by have := mem_range.1 hj; omega)
  · intro Q hQ
    obtain ⟨hQ1, hQ2⟩ := mem_sdiff.1 hQ
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hQ1
    have hj' := mem_range.1 hj
    have hij : i ≤ j := by
      by_contra hc
      exact hQ2 (mem_image.2 ⟨j, mem_range.2 (by omega), rfl⟩)
    exact hord i hi' j hj' hij
  · intro Q hQ
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hQ
    exact hnc i hi' j (by have := mem_range.1 hj; omega)

/-- **The top-down collapse at `X_{C i} = x`**: `pkR_b_R2top` over `ℚ`, evaluated at a point where
every chord of the chain takes the value `x`. -/
theorem pkR_b_R2top_eval {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0)
    (C : ℕ → ℕ × ℕ) (k : ℕ) (hC : ∀ i < k, C i ∈ oddDiagonals N)
    (hinj : ∀ i < k, ∀ j < i, C j ≠ C i)
    (hord : ∀ i < k, ∀ j < k, i ≤ j → oddSide N (C j) ⊆ oddSide N (C i))
    (hnc : ∀ i < k, ∀ j < k, ¬ Crosses (C j) (C i)) {X : ℕ × ℕ → ℚ} {x : ℚ}
    (hx : ∀ i < k, X (C i) = x) :
    MvPolynomial.eval X (NP ℚ N) =
      Finset.sum (range k) (fun i => x ^ i *
        (MvPolynomial.eval X (MvPolynomial.rename (relab N (headStart (C i)))
            (NP ℚ (headLen N (C i) + 1))) *
          MvPolynomial.eval X (MvPolynomial.rename (relab N (tailStart (C i)))
            (pkRBNP ℚ (tailLen N (C i) + 1)
              (pkRBPull N (tailStart (C i)) (tailLen N (C i) + 1) ((range k).image C)))) *
          MvPolynomial.eval X (crossProd ℚ N (C i)))) +
      x ^ k * MvPolynomial.eval X (pkRBNP ℚ N ((range k).image C)) := by
  have hp : ∀ i ≤ k, Finset.prod (range i) (fun j => X (C j)) = x ^ i := fun i hi => by
    rw [prod_congr rfl (fun j hj => hx j (by have := mem_range.1 hj; omega)),
        prod_const, card_range]
  rw [pkR_b_R2top (R := ℚ) hN hE C k hC hinj hord hnc]
  simp only [map_add, map_sum, map_mul, map_prod, MvPolynomial.eval_X]
  rw [hp k le_rfl]
  refine congrArg₂ (· + ·) (sum_congr rfl fun i hi => ?_) rfl
  rw [hp i (by have := mem_range.1 hi; omega)]

/-- **The peeling term of a chain member, bottom-up order**: for an odd chord `C` and a set `K` of
odd chords, if the banned chords `K₁ ⊆ K` have heads `⊆ A_C` and do not cross `C`, and the rest of
`K` has heads `⊇ A_C`, then `term(K₁, C)` = `NP^{¬K}` of the A-child (`b_C`'s numerator) · the full
`NP` of the B-child · `crossProd C`. -/
theorem pkR_b_term_chainB {R : Type*} [CommRing R] {N : ℕ} {K K₁ : Finset (ℕ × ℕ)} {C : ℕ × ℕ}
    (hC : C ∈ oddDiagonals N) (hK : K ⊆ oddDiagonals N) (h1 : K₁ ⊆ K)
    (hdown : ∀ Q ∈ K₁, oddSide N Q ⊆ oddSide N C) (hup : ∀ Q ∈ K \ K₁, oddSide N C ⊆ oddSide N Q)
    (hnc : ∀ Q ∈ K₁, ¬ Crosses Q C) :
    pkRBTerm R N K₁ C =
      MvPolynomial.rename (relab N (headStart C))
          (pkRBNP R (headLen N C + 1) (pkRBPull N (headStart C) (headLen N C + 1) K)) *
        MvPolynomial.rename (relab N (tailStart C)) (NP R (tailLen N C + 1)) *
        crossProd R N C := by
  unfold pkRBTerm
  rw [pkR_b_R17_tail hC (fun Q hQ => hK (h1 hQ)) hdown, pkR_b_NP_empty, pkR_b_cross_nc hnc,
    pkR_b_pull_mono h1 (pkR_b_R17_head hC (fun Q hQ => hK (mem_sdiff.1 hQ).1) hup)]

/-- **The bottom-up collapse**, the mirror of `pkR_b_R2top`: over a domain, for `N` even, `N ≥ 4`,
and a chain of odd chords `C 0 ≺ C 1 ≺ … ≺ C (k−1)` (heads increasing, `A_{C i} ⊆ A_{C j}` for
`i ≤ j`; pairwise distinct and non-crossing) that is all of `K`,
`NP_N = Σ_{i<k} (Π_{j<i} X_{C j}) · NP^{¬K}_{A(C i)} · NP_{B(C i)} · crossProd(C i)` +
`(Π_{j<k} X_{C j}) · NP^{¬K}_N`. Applied to the A-child of the top chord (`N = headLen t + 1`, `K` =
the pulled-back lower chords), the B-children are the regions `Ω(t, C i)` and the A-children give
`b_{C i}`. -/
theorem pkR_b_R2bot {R : Type*} [CommRing R] [IsDomain R] {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0)
    (C : ℕ → ℕ × ℕ) (k : ℕ) (hC : ∀ i < k, C i ∈ oddDiagonals N)
    (hinj : ∀ i < k, ∀ j < i, C j ≠ C i)
    (hord : ∀ i < k, ∀ j < k, i ≤ j → oddSide N (C i) ⊆ oddSide N (C j))
    (hnc : ∀ i < k, ∀ j < k, ¬ Crosses (C j) (C i)) :
    NP R N =
      Finset.sum (range k) (fun i => Finset.prod (range i) (fun j => MvPolynomial.X (C j)) *
        (MvPolynomial.rename (relab N (headStart (C i)))
            (pkRBNP R (headLen N (C i) + 1)
              (pkRBPull N (headStart (C i)) (headLen N (C i) + 1) ((range k).image C))) *
          MvPolynomial.rename (relab N (tailStart (C i))) (NP R (tailLen N (C i) + 1)) *
          crossProd R N (C i))) +
      Finset.prod (range k) (fun j => MvPolynomial.X (C j)) * pkRBNP R N ((range k).image C) := by
  have hK : (range k).image C ⊆ oddDiagonals N := by
    intro d hd
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hd
    exact hC j (mem_range.1 hj)
  have h := pkR_b_peel (R := R) hN hE ∅ C k (empty_subset _) hC (fun i _ h => by simp at h) hinj
  rw [pkR_b_NP_empty] at h
  simp only [empty_union] at h
  rw [h]
  refine congrArg₂ (· + ·) (sum_congr rfl fun i hi => ?_) rfl
  have hi' := mem_range.1 hi
  rw [pkR_b_term_chainB (R := R)
      (hC i hi') hK (image_subset_image (range_subset_range.2 (show i ≤ k by omega)))
    ?_ ?_ ?_]
  · intro Q hQ
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hQ
    exact hord j (by have := mem_range.1 hj; omega) i hi' (by have := mem_range.1 hj; omega)
  · intro Q hQ
    obtain ⟨hQ1, hQ2⟩ := mem_sdiff.1 hQ
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hQ1
    have hj' := mem_range.1 hj
    have hij : i ≤ j := by
      by_contra hc
      exact hQ2 (mem_image.2 ⟨j, mem_range.2 (by omega), rfl⟩)
    exact hord i hi' j hj' hij
  · intro Q hQ
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hQ
    exact hnc i hi' j (by have := mem_range.1 hj; omega)

/-! #### The ear lemma for a chain

The ¬K numerator vanishes on `Z′` for a whole chain `K` (`pkR_b_R5d`): by the bottom-up peeling
`pkR_b_R2bot`, `NP_n ≡ 0` on `Z′` (`pkR_b_R5a_NP`), the B-child numerators (`pkR_b_R5bT`), and
`X_C ≢ 0` for every member (`pkR_b_R5cT`), cancelled by `pkR_b_primeProd`. In the A-child of a chord
this gives `pkR_b_R6van`. -/

/-- **Cancelling a product**: on a subspace `V` (`pkRSub`), if `ℓ 0 ⋯ ℓ (m − 1) · G` vanishes on
`V` and no `ℓ j` vanishes at every point of `V`, then `G` vanishes on `V`. -/
theorem pkR_b_primeProd {σ : Type*} {V : Set (σ → ℚ)} (hV : pkRSub V)
    (ℓ : ℕ → MvPolynomial σ ℚ) (m : ℕ) (hw : ∀ j < m, ∃ w ∈ V, MvPolynomial.eval w (ℓ j) ≠ 0)
    {G : MvPolynomial σ ℚ}
    (h : ∀ x ∈ V, Finset.prod (range m) (fun j => MvPolynomial.eval x (ℓ j)) *
        MvPolynomial.eval x G = 0) :
    ∀ x ∈ V, MvPolynomial.eval x G = 0 := by
  induction m generalizing G with
  | zero =>
    intro x hx
    have e := h x hx
    rw [prod_range_zero, one_mul] at e
    exact e
  | succ m ih =>
    have h2 : ∀ x ∈ V, MvPolynomial.eval x (ℓ m * G) = 0 :=
      ih (fun j hj => hw j (by omega)) (fun x hx => by
        rw [map_mul, ← mul_assoc, ← prod_range_succ (fun j => MvPolynomial.eval x (ℓ j)) m]
        exact h x hx)
    exact pkR_prime hV (hw m (by omega)) (fun x hx => by rw [← map_mul]; exact h2 x hx)

/-- **The B-child numerator on `Z′`, head/tail form**: for `n` even, `n ≥ 4`, and an odd chord
`C ∈ K` whose head contains the run `R` (`μ⁺` = odd legs outside `R`), the B-child numerator of `C`
vanishes on `Z′` (both parities of `C.1`, by `pkR_b_R5b2_NP` or `pkR_b_R5b1_NP`). -/
theorem pkR_b_R5bT {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {C : ℕ × ℕ} (hC : C ∈ oddDiagonals n)
    {R : Finset ℕ} (hRA : R ⊆ oddSide n C) {K : Finset (ℕ × ℕ)} (hK : C ∈ K) {X : ℕ × ℕ → ℚ}
    (hZ : pkRBZ5 n 1 R K X) :
    MvPolynomial.eval X (MvPolynomial.rename (relab n (tailStart C))
        (NP ℚ (tailLen n C + 1))) = 0 := by
  obtain ⟨c1, c2⟩ := C
  have hQ := mem_filter.1 hC
  have hd := hQ.1
  have hpar := hQ.2
  rw [mem_diagonals] at hd
  dsimp only at hd hpar
  rcases pkR_b_tail_data hC with ⟨h1, ts, tl⟩ | ⟨h1, ts, tl⟩
  · dsimp only at h1 ts tl
    rw [ts, tl, show n - (c2 - c1) + 1 = n - c2 + c1 + 1 by omega]
    have hZ' : pkRBZ5 n (c1 % 2) R K X := by rw [h1]; exact hZ
    refine pkR_b_R5b2_NP hE hn hC hK (fun r hr => ?_) hZ'
    have := hRA hr
    simp [oddSide, h1] at this
    omega
  · dsimp only at h1 ts tl
    rw [ts, tl]
    have hZ' : pkRBZ5 n (c2 % 2) R K X := by rw [show c2 % 2 = 1 by omega]; exact hZ
    refine pkR_b_R5b1_NP hE hn hC hK (fun r hr => ?_) hZ'
    have := hRA hr
    simp [oddSide, h1] at this
    omega

/-- **`X_C ≢ 0` on `Z′`, head form**: for `n` even, an odd chord `C` whose head contains the run
`R ⊆ [1, n]` and an odd leg `r₀ ∈ R`, there is a point of `Z′` (`ε = 1`, every `K`) with `X_C ≠ 0`.
-/
theorem pkR_b_R5cT {n : ℕ} (hE : n % 2 = 0) {C : ℕ × ℕ} (hC : C ∈ oddDiagonals n) {R : Finset ℕ}
    (hRn : R ⊆ Icc 1 n) (hRA : R ⊆ oddSide n C) {r₀ : ℕ} (hr₀ : r₀ ∈ R) (hr₀o : r₀ % 2 = 1)
    (K : Finset (ℕ × ℕ)) : ∃ X : ℕ × ℕ → ℚ, pkRBZ5 n 1 R K X ∧ X C ≠ 0 := by
  obtain ⟨c1, c2⟩ := C
  have hQ := mem_filter.1 hC
  have hd := hQ.1
  have hpar := hQ.2
  rw [mem_diagonals] at hd
  dsimp only at hd hpar
  by_cases h1 : c1 % 2 = 1
  · obtain ⟨X, hX, hne⟩ := pkR_b_R5c2 hE hC (R := R) (fun r hr => by
      have := hRA hr
      simp [oddSide, h1] at this
      omega) hr₀ (by omega) K
    rw [h1] at hX
    exact ⟨X, hX, hne⟩
  · obtain ⟨X, hX, hne⟩ := pkR_b_R5c1 hE hC hRn (fun r hr => by
      have := hRA hr
      have h0 : c1 % 2 = 0 := by omega
      simp [oddSide, h0] at this
      omega) hr₀ (show r₀ % 2 = c2 % 2 by omega) K
    rw [show c2 % 2 = 1 by omega] at hX
    exact ⟨X, hX, hne⟩

/-- **The ear lemma for a chain**: for `n` even, `n ≥ 4`, let `K = {C 0 ≺ … ≺ C (k−1)}` be a chain
of pairwise distinct odd chords (heads increasing, pairwise non-crossing) whose heads all contain
the run `R ⊆ [1, n]`, with an odd leg `r₀ ∈ R`; let `R` be a run for `T = μ⁻ ∪ {s}` = the even legs
outside `R`, with two such legs `t₁ ≠ t₂`. Then `N^{¬K}_n ≡ 0` on `Z′` (`μ⁺` = the odd legs outside
`R`, members `K`). -/
theorem pkR_b_R5d {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) (C : ℕ → ℕ × ℕ) (k : ℕ)
    (hC : ∀ i < k, C i ∈ oddDiagonals n) (hinj : ∀ i < k, ∀ j < i, C j ≠ C i)
    (hord : ∀ i < k, ∀ j < k, i ≤ j → oddSide n (C i) ⊆ oddSide n (C j))
    (hnc : ∀ i < k, ∀ j < k, ¬ Crosses (C j) (C i)) {R : Finset ℕ} (hRn : R ⊆ Icc 1 n)
    (hRA : ∀ i < k, R ⊆ oddSide n (C i)) {r₀ : ℕ} (hr₀ : r₀ ∈ R) (hr₀o : r₀ % 2 = 1)
    (hRR : ∀ a ∈ R, ∀ b ∈ R, ¬ InST (pkRBT5 n 1 R) a b) {t₁ t₂ : ℕ} (h1 : t₁ ∈ pkRBT5 n 1 R)
    (h2 : t₂ ∈ pkRBT5 n 1 R) (h12 : t₁ ≠ t₂) :
    ∀ X ∈ {X : ℕ × ℕ → ℚ | pkRBZ5 n 1 R ((range k).image C) X},
      MvPolynomial.eval X (pkRBNP ℚ n ((range k).image C)) = 0 := by
  refine pkR_b_primeProd (pkR_b_Z5_sub n 1 R _) (fun j => MvPolynomial.X (C j)) k ?_ ?_
  · intro j hj
    obtain ⟨w, hw, hne⟩ := pkR_b_R5cT hE (hC j hj) hRn (hRA j hj) hr₀ hr₀o ((range k).image C)
    exact ⟨w, hw, by rw [MvPolynomial.eval_X]; exact hne⟩
  · intro x hx
    have hx' : pkRBZ5 n 1 R ((range k).image C) x := hx
    have hN0 : MvPolynomial.eval x (NP ℚ n) = 0 := pkR_b_R5a_NP hE hn (by omega) hx' hRR h1 h2 h12
    have e := pkR_b_R2bot (R := ℚ) hn hE C k hC hinj hord hnc
    have e2 := congrArg (MvPolynomial.eval x) (eq_sub_of_add_eq' e.symm)
    rw [map_mul, map_prod, map_sub, hN0, map_sum, Finset.sum_eq_zero, sub_zero] at e2
    · exact e2
    · intro i hi
      have hi' := mem_range.1 hi
      simp only [map_mul]
      rw [pkR_b_R5bT hE hn (hC i hi') (hRA i hi') (mem_image.2 ⟨i, hi, rfl⟩) hx']
      simp only [mul_zero, zero_mul]

/-- The head of a child chord `(u + 1, u + v + 1)` with `u` even is `[u + 1, u + v]`. -/
theorem pkR_b_oS1 {n u v : ℕ} (h : u % 2 = 0) :
    oddSide n (u + 1, u + v + 1) = Icc (u + 1) (u + v) := by
  change (if (u + 1) % 2 = 1 then Icc (u + 1) (u + v + 1 - 1) else Icc 1 n \ Icc (u + 1)
      (u + v + 1 - 1)) =
    Icc (u + 1) (u + v)
  rw [ite_eq_left (by omega), show u + v + 1 - 1 = u + v by omega]

/-- **`b_Q ≡ 0` on the A-child of `Q`**: in the A-child of `Q` (list `pkRBOmL N a (L − 1) 1`,
positions from `a`), on `T(Q, b) ∩ {X_Q = 0} ∩ minRect(Q″ …)` the `¬K` numerator of the child
vanishes, where the banned chords are the members `c i` (positional `(u, v)`: `A_{c i}` = positions
`[u, u + v)`, all containing `A_b` = `[p, p + L′)`, none equal to `Q`, heads increasing in `i`,
pairwise distinct) read as child chords `(u + 1, u + v + 1)`. Here `L`, `L′` are odd, `L′ ≥ 3`, `p`
is even, `p + L′ ≤ L`, `L′ + 2 ≤ L` and `L < N`. The same lemma gives `a_Q ≡ 0` on the B-child of
`Q` with the parameters of `pkR_b_R6Z5B` (base `vtx N (a + (p + L′))`, `hT` from `pkR_b_OT_swap`).
-/
theorem pkR_b_R6van {N a p L L' : ℕ} (hN : 1 ≤ N) (ha : 1 ≤ a ∧ a ≤ N) (hL : L % 2 = 1)
    (hp : p % 2 = 0) (hL' : L' % 2 = 1) (hL3 : 3 ≤ L') (hpL : p + L' ≤ L) (hLL : L' + 2 ≤ L)
    (hLN : L < N) {X : ℕ × ℕ → ℚ} (hT : pkRBOT N a p L L' X) (hXQ : planar N X a (a + L) = 0)
    (c : ℕ → ℕ × ℕ) (k : ℕ)
    (hc : ∀ i < k, (c i).1 % 2 = 0 ∧ (c i).2 % 2 = 1 ∧ (c i).1 ≤ p ∧ p + L' ≤ (c i).1 + (c i).2 ∧
      (c i).1 + (c i).2 ≤ L ∧ ¬ ((c i).1 = 0 ∧ (c i).2 = L) ∧
      ∀ i' j, (c i).1 ≤ i' → i' < (c i).1 + (c i).2 → i' % 2 = 1 →
          (j < (c i).1 ∨ (c i).1 + (c i).2 ≤ j) → j < L →
        j % 2 = 0 → mesh N X (vtx N (a + i')) (vtx N (a + j)) = 0)
    (hinj : ∀ i < k, ∀ j < i, c j ≠ c i)
    (hord : ∀ i < k, ∀ j < k, i ≤ j → (c j).1 ≤ (c i).1 ∧ (c i).1 + (c i).2 ≤ (c j).1 + (c j).2) :
    MvPolynomial.eval (pkRSubX N (pkRBOmL N a (L - 1) 1) X)
      (pkRBNP ℚ (L - 1 + 2)
          ((range k).image (fun i => ((c i).1 + 1, (c i).1 + (c i).2 + 1)))) = 0 := by
  have hZ := pkR_b_R6Z5 hN ha hL hp hL' hpL hLL hLN hT hXQ (J := (range k).image c)
      (fun cc hcc => by
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hcc
    obtain ⟨a1, a2, a3, a4, a5, -, a7⟩ := hc i (mem_range.1 hi)
    exact ⟨a1, a2, a3, a4, a5, a7⟩)
  rw [image_image] at hZ
  have hC' : ∀ i < k, ((c i).1 + 1, (c i).1 + (c i).2 + 1) ∈ oddDiagonals (L - 1 + 2) := by
    intro i hi
    obtain ⟨a1, a2, a3, a4, a5, a6, -⟩ := hc i hi
    exact mem_filter.2 ⟨mem_diagonals.2 (by dsimp only; omega), by dsimp only; omega⟩
  have hinj' : ∀ i < k, ∀ j < i, ((c j).1 + 1, (c j).1 + (c j).2 + 1) ≠
      ((c i).1 + 1, (c i).1 + (c i).2 + 1) := by
    intro i hi j hj e
    have e1 := congrArg Prod.fst e
    have e2 := congrArg Prod.snd e
    dsimp only at e1 e2
    exact hinj i hi j hj (Prod.ext (by omega) (by omega))
  have hord' : ∀ i < k, ∀ j < k, i ≤ j →
      oddSide (L - 1 + 2) ((c i).1 + 1, (c i).1 + (c i).2 + 1) ⊆ oddSide (L - 1 + 2)
          ((c j).1 + 1, (c j).1 + (c j).2 + 1) := by
    intro i hi j hj hij
    rw [pkR_b_oS1 (hc i hi).1, pkR_b_oS1 (hc j hj).1]
    intro x hx
    rw [mem_Icc] at hx ⊢
    have := hord i hi j hj hij
    omega
  have hnc' : ∀ i < k, ∀ j < k,
      ¬ Crosses ((c j).1 + 1, (c j).1 + (c j).2 + 1) ((c i).1 + 1, (c i).1 + (c i).2 + 1) := by
    intro i hi j hj hcr
    unfold Crosses at hcr
    dsimp only at hcr
    rcases le_total i j with h | h
    · have := hord i hi j hj h
      omega
    · have := hord j hj i hi h
      omega
  have hRA : ∀ i < k, Icc (p + 1) (p + L') ⊆ oddSide (L - 1 + 2)
      ((c i).1 + 1, (c i).1 + (c i).2 + 1) := by
    intro i hi
    rw [pkR_b_oS1 (hc i hi).1]
    intro x hx
    rw [mem_Icc] at hx ⊢
    have := hc i hi
    omega
  have hRn : Icc (p + 1) (p + L') ⊆ Icc 1 (L - 1 + 2) := by
    intro x hx
    rw [mem_Icc] at hx ⊢
    omega
  have ht1 : L - 1 + 2 ∈ pkRBT5 (L - 1 + 2) 1 (Icc (p + 1) (p + L')) :=
    mem_filter.2 ⟨mem_Icc.2 ⟨by omega, le_rfl⟩, by omega, fun h => by rw [mem_Icc] at h; omega⟩
  obtain ⟨t₂, ht2, h12⟩ : ∃ t₂, t₂ ∈ pkRBT5 (L - 1 + 2) 1 (Icc (p + 1) (p + L')) ∧
      L - 1 + 2 ≠ t₂ := by
    by_cases hp0 : p = 0
    · exact ⟨L' + 1,
        mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega, fun h =>
        by rw [mem_Icc] at h; omega⟩,
        by omega⟩
    · exact ⟨p, mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, by omega, fun h =>
        by rw [mem_Icc] at h; omega⟩,
        by omega⟩
  exact pkR_b_R5d (n := L - 1 + 2) (by omega) (by omega)
      (fun i => ((c i).1 + 1, (c i).1 + (c i).2 + 1)) k hC' hinj'
    hord' hnc' hRn hRA (r₀ := p + 1) (mem_Icc.2 ⟨le_rfl, by omega⟩)
        (by omega) pkR_b_ivl_RR ht1 ht2 h12 _ hZ

/-! #### The banned sets inside the A-child of the top chord

The pull-back of `K` to the `relab N (headStart t)` child is the set of child chords
`(p + 1, p + L′ + 1)`, `p` = the position of `A_Q`, `L′ = |A_Q|` (`pkR_b_pull_head`); pull-backs
compose (`pkR_b_pull_comp`). -/

theorem pkR_b_vtx_cyc {N s x : ℕ} (hs : 1 ≤ s ∧ s ≤ N) (hx : 1 ≤ x ∧ x ≤ N) :
    vtx N (s + cycPos N s x) = x := by
  have m := pkR_b_mod2 (N := N) (z := x + N - s) (by omega)
  change vtx N (s + (x + N - s) % N) = x
  rcases m with ⟨m1, m2⟩ | ⟨m1, m2⟩ <;> rw [m2]
  · rw [show s + (x + N - s) = x + N by omega, vtx_add_n, vtx_of_mem hx.1 hx.2]
  · rw [show s + (x + N - s - N) = x by omega, vtx_of_mem hx.1 hx.2]

/-- `relab N s` is injective on the pairs of a child window of size `n ≤ N`. -/
theorem pkR_b_relab_inj {N s n : ℕ} {d d' : ℕ × ℕ} (hs : 1 ≤ s ∧ s ≤ N) (hn : n ≤ N)
    (hd : 1 ≤ d.1 ∧ d.1 < d.2 ∧ d.2 ≤ n) (hd' : 1 ≤ d'.1 ∧ d'.1 < d'.2 ∧ d'.2 ≤ n)
    (h : relab N s d = relab N s d') : d = d' := by
  have v1 := pkR_b_vtx2 (N := N) (u := d.1 + s - 1) (by omega) (by omega)
  have v2 := pkR_b_vtx2 (N := N) (u := d.2 + s - 1) (by omega) (by omega)
  have v3 := pkR_b_vtx2 (N := N) (u := d'.1 + s - 1) (by omega) (by omega)
  have v4 := pkR_b_vtx2 (N := N) (u := d'.2 + s - 1) (by omega) (by omega)
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  change min (vtx N (d.1 + s - 1)) (vtx N (d.2 + s - 1)) = min (vtx N (d'.1 + s - 1))
      (vtx N (d'.2 + s - 1)) at h1
  change max (vtx N (d.1 + s - 1)) (vtx N (d.2 + s - 1)) = max (vtx N (d'.1 + s - 1))
      (vtx N (d'.2 + s - 1)) at h2
  exact Prod.ext (by omega) (by omega)

/-- The child chord of an odd chord `Q′` whose head starts at position `p` from `s`:
`relab N s (p + 1, p + |A_{Q′}| + 1) = Q′` (for `p + |A_{Q′}| < N`). -/
theorem pkR_b_relab_head {N s p : ℕ} {Q' : ℕ × ℕ} (hQ' : Q' ∈ oddDiagonals N) (hs : 1 ≤ s ∧ s ≤ N)
    (hpL : p + headLen N Q' < N) (hv : vtx N (s + p) = headStart Q') :
    relab N s (p + 1, p + headLen N Q' + 1) = Q' := by
  have hN : 1 ≤ N := by omega
  have e2 : vtx N (s + (p + headLen N Q')) = vtx N (headStart Q' + headLen N Q') := by
    have h := pkR_b_vtx_sh hN hs (show p < N by omega) (show headLen N Q' < N by omega)
    rw [hv, Nat.mod_eq_of_lt hpL] at h
    exact h.symm
  change npair N (p + 1 + s - 1) (p + headLen N Q' + 1 + s - 1) = Q'
  rw [show p + 1 + s - 1 = s + p by omega, show p + headLen N Q' + 1 + s - 1 = s +
      (p + headLen N Q') by omega]
  change (min (vtx N (s + p)) (vtx N (s + (p + headLen N Q'))), max (vtx N (s + p))
      (vtx N (s + (p + headLen N Q')))) = Q'
  rw [hv, e2]
  have b := pkR_b_odd_iff.1 hQ'
  have hH := pkR_b_head_data hQ'
  obtain ⟨q1, q2⟩ := Q'
  dsimp only at b hH
  rcases hH with h | h
  · rw [h.2.1, h.2.2, show q1 + (q2 - q1) = q2 by omega, vtx_of_mem (show 1 ≤ q2 by omega)
      (show q2 ≤ N by omega)]
    exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)
  · rw [h.2.1, h.2.2, show q2 + (N - (q2 - q1)) = q1 + N by omega, vtx_add_n,
      vtx_of_mem (show 1 ≤ q1 by omega) (show q1 ≤ N by omega)]
    exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)

/-- **The pull-back of the class to the A-child of the top chord**: for `N` even, an odd chord `t`
and a set `K` of odd chords with every head inside `A_t`, the banned set of the A-child of `t`
(`relab N (headStart t)`, size `|A_t| + 1`) is the set of child chords `(p_Q + 1, p_Q + |A_Q| + 1)`,
`Q ∈ K ∖ {t}`, `p_Q = cycPos N (headStart t) (headStart Q)`. -/
theorem pkR_b_pull_head {N : ℕ} (hE : N % 2 = 0) {t : ℕ × ℕ} (ht : t ∈ oddDiagonals N)
    {K : Finset (ℕ × ℕ)} (hK : K ⊆ oddDiagonals N) (hKt : ∀ Q ∈ K, oddSide N Q ⊆ oddSide N t) :
    pkRBPull N (headStart t) (headLen N t + 1) K =
      (K.erase t).image (fun Q => (cycPos N (headStart t) (headStart Q) + 1,
        cycPos N (headStart t) (headStart Q) + headLen N Q + 1)) := by
  have f1 := pkR_b_head_facts hE ht
  have hrt : relab N (headStart t) (0 + 1, 0 + headLen N t + 1) = t :=
    pkR_b_relab_head ht ⟨f1.1, f1.2.1⟩ (by omega) (by rw [add_zero]; exact vtx_of_mem f1.1 f1.2.1)
  ext d
  constructor
  · intro hd
    obtain ⟨hdd, hdK⟩ := mem_filter.1 hd
    have hdd' := mem_diagonals.1 hdd
    obtain ⟨Q, hQ⟩ : ∃ Q, relab N (headStart t) d = Q := ⟨_, rfl⟩
    rw [hQ] at hdK
    have hQo := hK hdK
    have fQ := pkR_b_head_facts hE hQo
    by_cases hQt : Q = t
    · exfalso
      have hQ2 : relab N (headStart t) d = relab N (headStart t) (0 + 1, 0 + headLen N t + 1) :=
        hQ.trans (hQt.trans hrt.symm)
      have e := pkR_b_relab_inj ⟨f1.1, f1.2.1⟩ (show headLen N t + 1 ≤ N by omega) (by omega)
        ⟨by omega, by omega, by omega⟩ hQ2
      have e1 := congrArg Prod.fst e
      have e2 := congrArg Prod.snd e
      dsimp only at e1 e2
      omega
    · obtain ⟨np1, np2, np3, -⟩ := pkR_b_nest_pos hE ht hQo (hKt Q hdK) (Ne.symm hQt)
      have hv := pkR_b_vtx_cyc (N := N) (s := headStart t) (x := headStart Q) ⟨f1.1, f1.2.1⟩
          ⟨fQ.1, fQ.2.1⟩
      have hrQ := pkR_b_relab_head hQo ⟨f1.1, f1.2.1⟩
        (show cycPos N (headStart t) (headStart Q) + headLen N Q < N by omega) hv
      have e := pkR_b_relab_inj ⟨f1.1, f1.2.1⟩ (show headLen N t + 1 ≤ N by omega) (by omega)
        ⟨by omega, by omega, by omega⟩ (hQ.trans hrQ.symm)
      exact mem_image.2 ⟨Q, mem_erase.2 ⟨hQt, hdK⟩, e.symm⟩
  · intro hd
    obtain ⟨Q, hQ, rfl⟩ := mem_image.1 hd
    obtain ⟨hQt, hQK⟩ := mem_erase.1 hQ
    have hQo := hK hQK
    have fQ := pkR_b_head_facts hE hQo
    obtain ⟨np1, np2, np3, -⟩ := pkR_b_nest_pos hE ht hQo (hKt Q hQK) (Ne.symm hQt)
    have hv := pkR_b_vtx_cyc (N := N) (s := headStart t) (x := headStart Q) ⟨f1.1, f1.2.1⟩
        ⟨fQ.1, fQ.2.1⟩
    have hrQ := pkR_b_relab_head hQo ⟨f1.1, f1.2.1⟩
      (show cycPos N (headStart t) (headStart Q) + headLen N Q < N by omega) hv
    have hne : ¬ (cycPos N (headStart t) (headStart Q) = 0 ∧ headLen N Q = headLen N t) := by
      rintro ⟨e1, e2⟩
      exact hQt (hrQ.symm.trans (by rw [e1, e2]; exact hrt))
    refine mem_filter.2 ⟨mem_diagonals.2 (by dsimp only; omega), ?_⟩
    show relab N (headStart t) (cycPos N (headStart t) (headStart Q) + 1,
      cycPos N (headStart t) (headStart Q) + headLen N Q + 1) ∈ K
    rw [hrQ]
    exact hQK

/-- `relab` of a child with base `p + 1` on a window without wrap is the shift by `p`. -/
theorem pkR_b_relab_shift {n p : ℕ} {d : ℕ × ℕ} (hd : 1 ≤ d.1 ∧ d.1 < d.2) (hp : d.2 + p ≤ n) :
    relab n (p + 1) d = (d.1 + p, d.2 + p) := by
  change (min (vtx n (d.1 + (p + 1) - 1)) (vtx n (d.2 + (p + 1) - 1)),
    max (vtx n (d.1 + (p + 1) - 1)) (vtx n (d.2 + (p + 1) - 1))) = _
  rw [vtx_of_mem (show 1 ≤ d.1 + (p + 1) - 1 by omega) (show d.1 + (p + 1) - 1 ≤ n by omega),
    vtx_of_mem (show 1 ≤ d.2 + (p + 1) - 1 by omega) (show d.2 + (p + 1) - 1 ≤ n by omega)]
  exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)

/-- **Composition of relabellings (no wrap in the child)**: a grandchild at child base `p + 1` read
in the parent is the child of the parent at base `vtx N (s + p)`. -/
theorem pkR_b_relab_comp {N s n p : ℕ} {d : ℕ × ℕ} (hs : 1 ≤ s ∧ s ≤ N) (hn : n ≤ N)
    (hd : 1 ≤ d.1 ∧ d.1 < d.2)
    (hp : d.2 + p ≤ n) : relab N s (relab n (p + 1) d) = relab N (vtx N (s + p)) d := by
  have hN : 1 ≤ N := by omega
  rw [pkR_b_relab_shift hd hp]
  change npair N (d.1 + p + s - 1) (d.2 + p + s - 1) = npair N (d.1 + vtx N (s + p) - 1)
      (d.2 + vtx N (s + p) - 1)
  have k1 : vtx N (d.1 + p + s - 1) = vtx N (d.1 + vtx N (s + p) - 1) := by
    have h := pkR_b_vtx_sh hN hs (show p < N by omega) (show d.1 - 1 < N by omega)
    rw [Nat.mod_eq_of_lt (show p + (d.1 - 1) < N by omega)] at h
    rw [show d.1 + vtx N (s + p) - 1 = vtx N (s + p) + (d.1 - 1) by omega, h,
      show s + (p + (d.1 - 1)) = d.1 + p + s - 1 by omega]
  have k2 : vtx N (d.2 + p + s - 1) = vtx N (d.2 + vtx N (s + p) - 1) := by
    have h := pkR_b_vtx_sh hN hs (show p < N by omega) (show d.2 - 1 < N by omega)
    rw [Nat.mod_eq_of_lt (show p + (d.2 - 1) < N by omega)] at h
    rw [show d.2 + vtx N (s + p) - 1 = vtx N (s + p) + (d.2 - 1) by omega, h,
      show s + (p + (d.2 - 1)) = d.2 + p + s - 1 by omega]
  unfold npair
  rw [k1, k2]

/-- **Banned sets compose**: pulling `K` back to the child (base `s`, size `n`) and then to its
sub-child at base `p + 1` (size `L′ + 1`, no wrap) is pulling `K` back to the parent's child at base
`vtx N (s + p)`. The hypothesis `_hne` (the sub-child is not the whole child) is not used. With
`pkR_b_pull_head` this identifies the grandchild banned sets of `pkR_b_R2bot` (inside the A-child of
`t`) with the parent ones of `b_Q` (`s = headStart t`, `vtx N (s + p_Q) = headStart Q` by
`pkR_b_vtx_cyc`). -/
theorem pkR_b_pull_comp {N s n p L' : ℕ} {K : Finset (ℕ × ℕ)} (hs : 1 ≤ s ∧ s ≤ N) (hn : n ≤ N)
    (hpL : p + L' + 1 ≤ n) (_hne : ¬ (p = 0 ∧ p + L' + 1 = n)) :
    pkRBPull n (p + 1) (L' + 1) (pkRBPull N s n K) = pkRBPull N (vtx N (s + p))
        (L' + 1) K := by
  ext d
  change d ∈ (diagonals (L' + 1)).filter (fun d =>
      relab n (p + 1) d ∈ (diagonals n).filter (fun e => relab N s e ∈ K)) ↔
    d ∈ (diagonals (L' + 1)).filter (fun d => relab N (vtx N (s + p)) d ∈ K)
  rw [mem_filter, mem_filter, mem_filter]
  constructor
  · rintro ⟨hd, -, hK⟩
    have hd' := mem_diagonals.1 hd
    refine ⟨hd, ?_⟩
    rw [← pkR_b_relab_comp hs hn (by omega) (by omega)]
    exact hK
  · rintro ⟨hd, hK⟩
    have hd' := mem_diagonals.1 hd
    refine ⟨hd, ?_, ?_⟩
    · rw [pkR_b_relab_shift (by omega) (by omega)]
      exact mem_diagonals.2 (by dsimp only; omega)
    · rw [pkR_b_relab_comp hs hn (by omega) (by omega)]
      exact hK

/-! ### Locality and rotation invariance of the numerators

The ¬K numerators of the `n`-gon read their point only on the diagonals (`pkR_b_NPK_local`), and
`NP_m` is invariant under rotation (`pkR_b_NP_rot`), so a rotated region list gives the same
numerator value (`pkR_b_NP_subX_rot`). They partly repeat the rotation facts of `C7` (`pkR_NP_rotk`)
under the prefix `pkR_b_`. The sections that use them, on the A-side collapse at a chord, continue
in `C9`. -/

/-- Truncation to the diagonals of the `n`-gon: every variable off the diagonals is set to `0`. -/
noncomputable def pkRBTrunc (n : ℕ) :
    AlgHom ℚ (MvPolynomial (ℕ × ℕ) ℚ) (MvPolynomial (ℕ × ℕ) ℚ) :=
  MvPolynomial.aeval (fun d =>
      if d ∈ diagonals n then (MvPolynomial.X d : MvPolynomial (ℕ × ℕ) ℚ) else 0)

theorem pkR_b_trunc_X {n : ℕ} {d : ℕ × ℕ} (hd : d ∈ diagonals n) :
    pkRBTrunc n (MvPolynomial.X d) = MvPolynomial.X d := by
  change MvPolynomial.aeval _ (MvPolynomial.X d) = _
  rw [MvPolynomial.aeval_X, ite_eq_left hd]

/-- The truncation fixes every ¬K numerator coefficient of the `n`-gon (its variables are
diagonals). -/
theorem pkR_b_trunc_AP (n m : ℕ) (K : Finset (ℕ × ℕ)) :
    pkRBTrunc n (pkRBAP ℚ n m K) = pkRBAP ℚ n m K := by
  change (pkRBTrunc n).toRingHom (PowerSeries.coeff m
      (Finset.sum ((triangulations n).filter (fun T => Disjoint T K))
      (fun T => pkRBF ℚ n K T))) =
    PowerSeries.coeff m (Finset.sum ((triangulations n).filter (fun T => Disjoint T K))
        (fun T => pkRBF ℚ n K T))
  rw [← PowerSeries.coeff_map, map_sum]
  refine congrArg _ (sum_congr rfl fun T hT => ?_)
  have hTd : T ⊆ diagonals n := (mem_triangulations.1 (mem_filter.1 hT).1).1
  rw [pkRBF, map_mul, PowerSeries.map_C, map_prod (PowerSeries.map _)]
  have hs : ∀ d ∈ T.filter (fun d => shiftSign d ≠ 0),
      PowerSeries.map (pkRBTrunc n).toRingHom (shiftSeriesP ℚ d) = shiftSeriesP ℚ d := fun d hd =>
    pkSp_map_sP _ d (pkR_b_trunc_X (hTd (mem_filter.1 hd).1))
  rw [prod_congr rfl hs, map_prod]
  have hc : ∀ d ∈ (oddDiagonals n \ T) \ K,
      (pkRBTrunc n).toRingHom (MvPolynomial.X d) = MvPolynomial.X d :=
    fun d hd => pkR_b_trunc_X (mem_filter.1 (mem_sdiff.1 (mem_sdiff.1 hd).1).1).1
  rw [prod_congr rfl hc]

/-- **Locality**: a ¬K numerator of the `n`-gon reads its point only on the diagonals (proved with
the truncation `pkRBTrunc`, in place of a lemma on `vars`). -/
theorem pkR_b_NPK_local {n : ℕ} (K : Finset (ℕ × ℕ)) {Y Y' : ℕ × ℕ → ℚ}
    (h : ∀ d ∈ diagonals n, Y d = Y' d) :
    MvPolynomial.eval Y (pkRBNP ℚ n K) = MvPolynomial.eval Y' (pkRBNP ℚ n K) := by
  have e : ∀ Z : ℕ × ℕ → ℚ, MvPolynomial.eval Z (pkRBNP ℚ n K) =
      MvPolynomial.eval (fun d => if d ∈ diagonals n then Z d else 0) (pkRBNP ℚ n K) := by
    intro Z
    have h2 : pkRBTrunc n (pkRBNP ℚ n K) = pkRBNP ℚ n K := pkR_b_trunc_AP n (n - 2) K
    calc MvPolynomial.eval Z (pkRBNP ℚ n K) =
        MvPolynomial.eval Z (pkRBTrunc n (pkRBNP ℚ n K)) := by
          rw [h2]
      _ = MvPolynomial.eval (fun i => MvPolynomial.eval Z
            (if i ∈ diagonals n then (MvPolynomial.X i : MvPolynomial (ℕ × ℕ) ℚ) else 0))
                (pkRBNP ℚ n K) :=
          pkR_eval_aeval Z _ _
      _ = _ := by
          refine congrArg (fun W => MvPolynomial.eval W (pkRBNP ℚ n K)) (funext fun i => ?_)
          by_cases hi : i ∈ diagonals n
          · rw [ite_eq_left hi, ite_eq_left hi, MvPolynomial.eval_X]
          · rw [ite_eq_right hi, ite_eq_right hi, map_zero]
  rw [e Y, e Y']
  refine congrArg (fun W => MvPolynomial.eval W (pkRBNP ℚ n K)) (funext fun d => ?_)
  by_cases hd : d ∈ diagonals n
  · rw [ite_eq_left hd, ite_eq_left hd, h d hd]
  · rw [ite_eq_right hd, ite_eq_right hd]

/-- Locality of the full numerator `NP_n`. -/
theorem pkR_b_NP_local {n : ℕ} {Y Y' : ℕ × ℕ → ℚ} (h : ∀ d ∈ diagonals n, Y d = Y' d) :
    MvPolynomial.eval Y (NP ℚ n) = MvPolynomial.eval Y' (NP ℚ n) := by
  rw [← pkR_b_NP_empty]
  exact pkR_b_NPK_local ∅ h

/-- `rot m` keeps the parity of a diagonal's length (`m` even). -/
theorem pkR_b_rot_par {m : ℕ} (hE : m % 2 = 0) {d : ℕ × ℕ} (hd : d ∈ diagonals m) :
    ((rot m d).2 - (rot m d).1) % 2 = (d.2 - d.1) % 2 := by
  have hdd := mem_diagonals.1 hd
  have e : rot m d =
      (min (vtx m (d.1 + 1)) (vtx m (d.2 + 1)), max (vtx m (d.1 + 1)) (vtx m (d.2 + 1))) := rfl
  have v1 := pkR_b_vtx2 (N := m) (u := d.1 + 1) (by omega) (by omega)
  have v2 := pkR_b_vtx2 (N := m) (u := d.2 + 1) (by omega) (by omega)
  rw [e]
  dsimp only
  omega

theorem pkR_b_rot_odd {m : ℕ} (hm : 1 ≤ m) (hE : m % 2 = 0) {d : ℕ × ℕ} (hd : d ∈ diagonals m) :
    rot m d ∈ oddDiagonals m ↔ d ∈ oddDiagonals m := by
  have hp := pkR_b_rot_par hE hd
  constructor
  · intro h
    exact mem_filter.2 ⟨hd, by have := (mem_filter.1 h).2; omega⟩
  · intro h
    exact mem_filter.2 ⟨rot_mem hm hd, by have := (mem_filter.1 h).2; omega⟩

/-- **Rotation invariance of `NP`** (polynomial form of `NLSM_rot` of `PionNLSM`): for even `m ≥ 4`,
`NP_m(Y ∘ rot) = NP_m(Y)` at every point. By density: `(rename rot NP − NP) · oddDen` vanishes at
every point (`AP_eval` and `NLSM_rot` where no odd chord vanishes, the factor `oddDen` elsewhere),
and `oddDen ≠ 0`. -/
theorem pkR_b_NP_rot {m : ℕ} (hm : 4 ≤ m) (hE : m % 2 = 0) (Y : ℕ × ℕ → ℚ) :
    MvPolynomial.eval (fun d => Y (rot m d)) (NP ℚ m) = MvPolynomial.eval Y (NP ℚ m) := by
  have hm1 : 1 ≤ m := by omega
  have hprod : ∀ Z : ℕ × ℕ → ℚ, Finset.prod (oddDiagonals m) (fun d => Z (rot m d)) =
      Finset.prod (oddDiagonals m) (fun d => Z d) := by
    intro Z
    refine Finset.prod_nbij (rot m) (fun d hd => (pkR_b_rot_odd hm1 hE (mem_filter.1 hd).1).2 hd)
      (fun p hp q hq h => rot_inj hm1 (mem_filter.1 hp).1 (mem_filter.1 hq).1 h) (fun d hd => ?_)
          (fun d _ => rfl)
    obtain ⟨d0, hd0, e⟩ := rot_surj hm1 (mem_filter.1 hd).1
    have hd' : rot m d0 ∈ oddDiagonals m := by
      rw [e]
      exact hd
    exact ⟨d0, (pkR_b_rot_odd hm1 hE hd0).1 hd', e⟩
  have key : ∀ Z : ℕ × ℕ → ℚ, (∀ d ∈ oddDiagonals m, Z d ≠ 0) →
      MvPolynomial.eval (fun d => Z (rot m d)) (NP ℚ m) = MvPolynomial.eval Z (NP ℚ m) := by
    intro Z hZ
    have hZ' : ∀ d ∈ oddDiagonals m, (fun d => Z (rot m d)) d ≠ 0 := fun d hd =>
      hZ _ ((pkR_b_rot_odd hm1 hE (mem_filter.1 hd).1).2 hd)
    have e : ((m - 2 : ℕ) : ℤ) = (m : ℤ) - 2 := by omega
    have hr : shiftCoeff m ((m - 2 : ℕ) : ℤ) (fun d => Z (rot m d)) =
        shiftCoeff m ((m - 2 : ℕ) : ℤ) Z := by
      rw [e]
      exact NLSM_rot hm hE Z
    change MvPolynomial.eval (fun d => Z (rot m d)) (AP ℚ m (m - 2)) =
        MvPolynomial.eval Z (AP ℚ m (m - 2))
    rw [AP_eval m (m - 2) _ hZ', AP_eval m (m - 2) Z hZ, hprod Z, hr]
  have hden : (MvPolynomial.rename (rot m) (NP ℚ m) - NP ℚ m) *
      Finset.prod (oddDiagonals m) (fun d => (MvPolynomial.X d : MvPolynomial (ℕ × ℕ) ℚ)) = 0 := by
    refine MvPolynomial.funext fun Z => ?_
    rw [map_mul, map_sub, MvPolynomial.eval_rename, map_zero, map_prod]
    simp only [MvPolynomial.eval_X]
    by_cases hZ : ∀ d ∈ oddDiagonals m, Z d ≠ 0
    · rw [show Function.comp Z (rot m) = fun d => Z (rot m d) from rfl, key Z hZ,
        sub_self, zero_mul]
    · push Not at hZ
      obtain ⟨d, hd, h0⟩ := hZ
      rw [Finset.prod_eq_zero hd h0, mul_zero]
  have hne : Finset.prod (oddDiagonals m)
      (fun d => (MvPolynomial.X d : MvPolynomial (ℕ × ℕ) ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun d _ => MvPolynomial.X_ne_zero d
  have hren : MvPolynomial.rename (rot m) (NP ℚ m) = NP ℚ m :=
    sub_eq_zero.1 ((mul_eq_zero.1 hden).resolve_right hne)
  calc MvPolynomial.eval (fun d => Y (rot m d)) (NP ℚ m) =
      MvPolynomial.eval Y (MvPolynomial.rename (rot m) (NP ℚ m)) := by
        rw [MvPolynomial.eval_rename]
        rfl
    _ = MvPolynomial.eval Y (NP ℚ m) := by rw [hren]

/-- A sub-polygon point read through `rot m` is the sub-polygon point of the list shifted by one
child leg. -/
theorem pkR_b_subX_rot {N m : ℕ} (f : ℕ → ℕ) (X : ℕ × ℕ → ℚ) :
    (fun d => pkRSubX N f X (rot m d)) = pkRSubX N (fun j => f (vtx m (j + 1))) X := by
  funext d
  change planar N X (f (rot m d).1) (f (rot m d).2) = planar N X (f (vtx m (d.1 + 1)))
      (f (vtx m (d.2 + 1)))
  have e : rot m d =
      (min (vtx m (d.1 + 1)) (vtx m (d.2 + 1)), max (vtx m (d.1 + 1)) (vtx m (d.2 + 1))) := rfl
  rw [e]
  dsimp only
  rcases le_total (vtx m (d.1 + 1)) (vtx m (d.2 + 1)) with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, pkR_planar_comm]

/-- **A rotated region list has the same numerator value**: for `m` even `≥ 4`, reading the list `f`
from child leg `r + 1` on (`j ↦ f (vtx m (j + r))`) does not change `NP_m` at the sub-polygon point.
-/
theorem pkR_b_NP_subX_rot {N m : ℕ} (hm : 4 ≤ m) (hE : m % 2 = 0) (f : ℕ → ℕ)
    (X : ℕ × ℕ → ℚ) (r : ℕ) :
    MvPolynomial.eval (pkRSubX N (fun j => f (vtx m (j + r))) X) (NP ℚ m) =
      MvPolynomial.eval (pkRSubX N f X) (NP ℚ m) := by
  have hm1 : 1 ≤ m := by omega
  induction r with
  | zero =>
    refine pkR_b_NP_local (fun d hd => ?_)
    have hdd := mem_diagonals.1 hd
    change planar N X (f (vtx m (d.1 + 0))) (f (vtx m (d.2 + 0))) = planar N X (f d.1) (f d.2)
    rw [Nat.add_zero, Nat.add_zero, vtx_of_mem (show 1 ≤ d.1 by omega) (show d.1 ≤ m by omega),
      vtx_of_mem (show 1 ≤ d.2 by omega) (show d.2 ≤ m by omega)]
  | succ r ih =>
    have e := pkR_b_subX_rot (N := N) (m := m) (fun j => f (vtx m (j + r))) X
    have h : pkRSubX N (fun j => (fun j => f (vtx m (j + r))) (vtx m (j + 1))) X =
        pkRSubX N (fun j => f (vtx m (j + (r + 1)))) X := by
      congr 1
      funext j
      change f (vtx m (vtx m (j + 1) + r)) = f (vtx m (j + (r + 1)))
      rw [pkR_b_vtx_add hm1, show j + 1 + r = j + (r + 1) by omega]
    rw [← (e.trans h)]
    exact (pkR_b_NP_rot hm hE (pkRSubX N (fun j => f (vtx m (j + r))) X)).trans ih


end PionCompleteness.Pi
