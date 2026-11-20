/-
Copyright (c) 2026 Henru Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henru Wang
-/
module

public import PionCompleteness.C8

/-!
# Theorem Π, part 9: the Ω formula, and the reduction of the residue input

This module continues the chain of modules that prove Theorem Π; the chain is cut by size, not by
topic, so the sections run on from `C8`. All
of it lies in section 8, among the helpers of prefix `pkR_` that prove the residue input
`resChild_input` (`C10`).

It first ends the sections on the numerators that avoid a set `K` of odd chords (prefix `pkR_b_`):
relabelled children as sub-polygon points (`pkR_b_evalK_relab`, `pkR_b_child_omL`), the bridge to
the region `Ω(t, c)` (`pkR_b_omega_relab`) and the A-side collapse at an odd chord `t` (`pkR_b_R2A`,
`pkR_b_R2A_eval`). It then proves the Ω formula on the standard polygon:
`NP_n = x^{|I|} · (c · x · D′ + x² · F)` on `Λ^I` with `c ≠ 0` (`pkR_omega`, by strong induction on
`n` in `pkR_omega_ind`). The next section reduces `ResChildInput` to the residue in numerator form
(`pkRDResNum`) and to child surjectivity (`pkRDChild1`) (`pkR_d_reduce`, prefix `pkR_d_`), with
the count of the powers of `x` (`pkR_d_count`); child surjectivity is then proved for both children
by a lift through a Gram matrix (`pkR_ch_gen`, `pkR_ch_childB`, `pkR_ch_childA`, prefix `pkR_ch_`).
The last section (prefix `pkR_d2_`) treats a general class, in which members may cross: the
expansions top-down and bottom-up (`pkR_d2_top_ind`, `pkR_d2_bot_ind`) and on the A-side
(`pkR_d2_Aside`), the count of the powers of `x` (`pkR_d2_count`) and the Ω formula at two class
members (`pkR_d2_omegaQ`); it continues in `C10`.

The conventions are those of `C0`'s module docstring.
-/

@[expose] public section

namespace PionCompleteness.Pi

open Finset PionCompleteness.TreeRectangleZero PionCompleteness.ChainSlice
  PionCompleteness.PionZeros PionCompleteness.PionNLSM
/-! ### Relabelled children as sub-polygon points -/

/-- `relab N s` maps the diagonals of a child window of size `n ≤ N` to parent diagonals (base
`s ∈ 1..N`). -/
theorem pkR_b_relab_mem {N s n : ℕ} (hs : 1 ≤ s ∧ s ≤ N) (hn : n ≤ N) {d : ℕ × ℕ}
    (hd : d ∈ diagonals n) :
    relab N s d ∈ diagonals N := by
  have hdd := mem_diagonals.1 hd
  have v1 := pkR_b_vtx2 (N := N) (u := d.1 + s - 1) (by omega) (by omega)
  have v2 := pkR_b_vtx2 (N := N) (u := d.2 + s - 1) (by omega) (by omega)
  change (min (vtx N (d.1 + s - 1)) (vtx N (d.2 + s - 1)), max (vtx N (d.1 + s - 1))
      (vtx N (d.2 + s - 1))) ∈
    diagonals N
  rw [mem_diagonals]
  dsimp only
  omega

/-- On child diagonals, the relabelled point is the cyclic-shift sub-polygon point (`pkRSubX`,
`C5`; base `s ∈ 1..N`, window `n ≤ N`). -/
theorem pkR_b_relab_subX {N s n : ℕ} (hs : 1 ≤ s ∧ s ≤ N) (hn : n ≤ N) (X : ℕ × ℕ → ℚ) {d : ℕ × ℕ}
    (hd : d ∈ diagonals n) : X (relab N s d) = pkRSubX N (fun k => vtx N (k + s - 1)) X d := by
  rw [pkR_subX_relab (by omega) s X d, ite_eq_left (pkR_b_relab_mem hs hn hd)]

/-- A sub-polygon point at a relabelled pair is the sub-polygon point of the composed list (every
pair). -/
theorem pkR_b_subX_relab {N n s : ℕ} (g : ℕ → ℕ) (X : ℕ × ℕ → ℚ) (d : ℕ × ℕ) :
    pkRSubX N g X (relab n s d) = pkRSubX N (fun k => g (vtx n (k + s - 1))) X d := by
  change planar N X (g (relab n s d).1) (g (relab n s d).2) =
    planar N X (g (vtx n (d.1 + s - 1))) (g (vtx n (d.2 + s - 1)))
  have e : relab n s d = (min (vtx n (d.1 + s - 1)) (vtx n (d.2 + s - 1)),
      max (vtx n (d.1 + s - 1)) (vtx n (d.2 + s - 1))) := rfl
  rw [e]
  dsimp only
  rcases le_total (vtx n (d.1 + s - 1)) (vtx n (d.2 + s - 1)) with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, pkR_planar_comm]

/-- **A relabelled child ¬K numerator is its sub-polygon value** (window `n ≤ N`,
base `s ∈ 1..N`). -/
theorem pkR_b_evalK_relab {N s n : ℕ} (hs : 1 ≤ s ∧ s ≤ N) (hn : n ≤ N) (K : Finset (ℕ × ℕ))
    (X : ℕ × ℕ → ℚ) :
    MvPolynomial.eval X (MvPolynomial.rename (relab N s) (pkRBNP ℚ n K)) =
      MvPolynomial.eval (pkRSubX N (fun k => vtx N (k + s - 1)) X) (pkRBNP ℚ n K) := by
  rw [MvPolynomial.eval_rename]
  exact pkR_b_NPK_local K (fun d hd => pkR_b_relab_subX hs hn X hd)

/-- **A child in `relab` form is the degenerate region list**: for a window of `M + 1 ≤ N` legs from
`s ∈ 1..N` (`M ≥ 1`), the ¬K numerator of the child read through `relab N s` is its value at the
region point `subX (pkRBOmL N s (M − 1) 1) X` (`pkRBOmL`, `C7`). `pkR_b_R6van` (`C8`) reads the
A-child of `Q` at this point, and with base `tailStart` the B-child. -/
theorem pkR_b_child_omL {N s M : ℕ} (hs : 1 ≤ s ∧ s ≤ N) (hM : 1 ≤ M) (hMN : M + 1 ≤ N)
    (K : Finset (ℕ × ℕ)) (X : ℕ × ℕ → ℚ) :
    MvPolynomial.eval X (MvPolynomial.rename (relab N s) (pkRBNP ℚ (M + 1) K)) =
      MvPolynomial.eval (pkRSubX N (pkRBOmL N s (M - 1) 1) X) (pkRBNP ℚ (M - 1 + 2) K) := by
  rw [show M - 1 + 2 = M + 1 by omega, pkR_b_evalK_relab hs hMN K X]
  refine pkR_b_NPK_local K (fun d hd => ?_)
  have hdd := mem_diagonals.1 hd
  change planar N X (vtx N (d.1 + s - 1)) (vtx N (d.2 + s - 1)) =
    planar N X (vtx N (s + pkRBOlo (M - 1) 1 d.1)) (vtx N (s + pkRBOlo (M - 1) 1 d.2))
  rw [show d.1 + s - 1 = s +
      pkRBOlo (M - 1) 1 d.1 by rcases pkR_b_olo_eq (M - 1) 1 d.1 with h | h <;> omega,
    show d.2 + s - 1 =
        s + pkRBOlo (M - 1) 1 d.2 by rcases pkR_b_olo_eq (M - 1) 1 d.2 with h | h <;> omega]

/-! ### The bridge to the region `Ω(t, c)` -/

/-- Position arithmetic of the Ω rotation: child leg `k` of the B-child of `(p + 1, p + L′ + 1)`
inside a head child of size `L + 1` (base `a`) is the parent dual point of region leg
`vtx m (k + p + 1)` of `pkRBOmL N a p L′` (`C7`; `m = L − L′ + 2`), for `1 ≤ L′`, `p + L′ ≤ L` and
`k ∈ 1..m`. -/
theorem pkR_b_om_rot_pos {p L L' k : ℕ} (hL' : 1 ≤ L') (hpL : p + L' ≤ L)
    (hk : 1 ≤ k ∧ k ≤ L - L' + 2) (a : ℕ) :
    vtx (L + 1) (k + (p + L' + 1) - 1) + a - 1 =
        a + pkRBOlo p L' (vtx (L - L' + 2) (k + (p + 1))) := by
  have v1 := pkR_b_vtx2 (N := L + 1) (u := k + (p + L' + 1) - 1) (by omega) (by omega)
  have v2 := pkR_b_vtx2 (N := L - L' + 2) (u := k + (p + 1)) (by omega) (by omega)
  rcases pkR_b_olo_eq p L' (vtx (L - L' + 2) (k + (p + 1))) with h | h <;> omega

/-- **The Ω(t, c) bridge.** Inside the head child of a chord (base `a ∈ 1..N`, `L + 1 ≤ N` legs,
`relab N a`), the B-child of the child chord `(p + 1, p + L′ + 1)` (base `p + L′ + 1`,
`relab (L + 1)`), read in the parent, has the numerator value of the region point
`subX (pkRBOmL N a p L′) X`; here `p` is even, `L` and `L′` are odd, `p + L′ ≤ L` and
`L′ + 2 ≤ L`. The two lists differ by a rotation by `p + 1` child legs, absorbed by
`pkR_b_NP_subX_rot` (`C8`); the rest is `pkR_b_NP_local` (`C8`). -/
theorem pkR_b_omega_relab {N a p L L' : ℕ} (ha : 1 ≤ a ∧ a ≤ N) (hp : p % 2 = 0) (hL : L % 2 = 1)
    (hL' : L' % 2 = 1) (hpL : p + L' ≤ L) (hLL : L' + 2 ≤ L) (hLN : L + 1 ≤ N) (X : ℕ × ℕ → ℚ) :
    MvPolynomial.eval X (MvPolynomial.rename (relab N a)
        (MvPolynomial.rename (relab (L + 1) (p + L' + 1)) (NP ℚ (L - L' + 2)))) =
      MvPolynomial.eval (pkRSubX N (pkRBOmL N a p L') X) (NP ℚ (L - L' + 2)) := by
  rw [MvPolynomial.eval_rename, MvPolynomial.eval_rename,
    ← pkR_b_NP_subX_rot (N := N) (m := L - L' + 2) (by omega) (by omega)
        (pkRBOmL N a p L') X (p + 1)]
  refine pkR_b_NP_local (fun d hd => ?_)
  have hdd := mem_diagonals.1 hd
  have he := pkR_b_relab_mem (N := L + 1) (s := p + L' + 1) (n := L - L' + 2) ⟨by omega, by omega⟩
      (by omega) hd
  change X (relab N a (relab (L + 1) (p + L' + 1) d)) = _
  rw [pkR_b_relab_subX ha hLN X he, pkR_b_subX_relab]
  change planar N X (vtx N (vtx (L + 1) (d.1 + (p + L' + 1) - 1) + a - 1))
      (vtx N (vtx (L + 1) (d.2 + (p + L' + 1) - 1) + a - 1)) =
    planar N X (vtx N (a + pkRBOlo p L' (vtx (L - L' + 2) (d.1 + (p + 1)))))
      (vtx N (a + pkRBOlo p L' (vtx (L - L' + 2) (d.2 + (p + 1)))))
  rw [pkR_b_om_rot_pos (k := d.1) (by omega) hpL ⟨by omega, by omega⟩ a,
    pkR_b_om_rot_pos (k := d.2) (by omega) hpL ⟨by omega, by omega⟩ a]

/-! ### The A-side collapse at an odd chord `t` -/

/-- The child chord of `Q` inside the head child of `t` (`relab N (headStart t)`):
`(p_Q + 1, p_Q + |A_Q| + 1)`, where `p_Q` is the position of `headStart Q` from `headStart t`. -/
def pkRBCc (N : ℕ) (t Q : ℕ × ℕ) : ℕ × ℕ :=
  (cycPos N (headStart t) (headStart Q) + 1, cycPos N (headStart t) (headStart Q) + headLen N Q + 1)

theorem pkR_b_cc_data {N n : ℕ} (t Q : ℕ × ℕ) (h : cycPos N (headStart t) (headStart Q) % 2 = 0) :
    headStart (pkRBCc N t Q) = cycPos N (headStart t) (headStart Q) + 1 ∧
      headLen n (pkRBCc N t Q) = headLen N Q ∧
      tailStart (pkRBCc N t Q) = cycPos N (headStart t) (headStart Q) + headLen N Q + 1 ∧
      tailLen n (pkRBCc N t Q) = n - headLen N Q := by
  have h1 : (cycPos N (headStart t) (headStart Q) + 1) % 2 = 1 := by omega
  have e1 : headStart (pkRBCc N t Q) = if (cycPos N (headStart t) (headStart Q) + 1) % 2 = 1 then
      cycPos N (headStart t) (headStart Q) + 1 else cycPos N (headStart t)
          (headStart Q) + headLen N Q + 1 := rfl
  have e2 : headLen n (pkRBCc N t Q) = if (cycPos N (headStart t) (headStart Q) + 1) % 2 = 1 then
      cycPos N (headStart t)
          (headStart Q) + headLen N Q + 1 - (cycPos N (headStart t) (headStart Q) + 1) else
      n - (cycPos N (headStart t) (headStart Q) + headLen N Q + 1 -
          (cycPos N (headStart t) (headStart Q) + 1)) := rfl
  have e3 : tailStart (pkRBCc N t Q) = if (cycPos N (headStart t) (headStart Q) + 1) % 2 = 1 then
      cycPos N (headStart t) (headStart Q) + headLen N Q + 1 else cycPos N (headStart t)
          (headStart Q) + 1 := rfl
  have e4 : tailLen n (pkRBCc N t Q) = n - headLen n (pkRBCc N t Q) := rfl
  rw [e4, e2, e1, e3, ite_eq_left h1, ite_eq_left h1, ite_eq_left h1]
  exact ⟨rfl, by omega, rfl, by omega⟩

/-- **The A-side collapse at an odd chord `t`.** For even `N`, let `c 0, …, c (k−1)` be distinct odd
chords other than `t` with heads inside `A_t`, nested increasingly in `i` (`A_{c i} ⊆ A_{c j}` for
`i ≤ j`; no crossing hypothesis is needed: it follows from the nesting), and `K = {c i}`. Then at
every point `X`, the full numerator of the head child of `t` (the A-child,
`relab N (headStart t)`) is
`Σ_i (Π_{j<i} X_{c j}) · b_{c i} · N_{Ω(t, c i)} · cross_i + (Π_j X_{c j}) · NP^{¬K}_{A(t)}`, where
- `b_{c i}` = the parent ¬K numerator of the A-child of `c i` (base `headStart (c i)`, banned set
  pulled from `K`),
- `N_{Ω(t, c i)}` = `NP` of the region `Ω(t, c i)` at the region point `pkRBOmX N t (c i) X`
  (`C7`, size `pkRBOmM`), i.e. exactly the point of `pkR_b_omegaTiles` (`C7`) and of the Ω formula
  `pkR_omega`; the rotation is absorbed here,
- `cross_i` = the crossing chords of the child chord `pkRBCc N t (c i)`, read in the parent. -/
theorem pkR_b_R2A {N : ℕ} (hE : N % 2 = 0) {t : ℕ × ℕ} (ht : t ∈ oddDiagonals N)
    (c : ℕ → ℕ × ℕ) (k : ℕ) (hc : ∀ i < k, c i ∈ oddDiagonals N) (hct : ∀ i < k, c i ≠ t)
    (hsub : ∀ i < k, oddSide N (c i) ⊆ oddSide N t) (hinj : ∀ i < k, ∀ j < i, c j ≠ c i)
    (hord : ∀ i < k, ∀ j < k, i ≤ j → oddSide N (c i) ⊆ oddSide N (c j)) (X : ℕ × ℕ → ℚ) :
    MvPolynomial.eval X (MvPolynomial.rename (relab N (headStart t)) (NP ℚ (headLen N t + 1))) =
      Finset.sum (range k) (fun i => Finset.prod (range i) (fun j => X (c j)) *
        (MvPolynomial.eval X (MvPolynomial.rename (relab N (headStart (c i)))
            (pkRBNP ℚ (headLen N (c i) + 1)
              (pkRBPull N (headStart (c i)) (headLen N (c i) + 1) ((range k).image c)))) *
          MvPolynomial.eval (pkRBOmX N t (c i) X) (NP ℚ (pkRBOmM N t (c i))) *
          MvPolynomial.eval X (MvPolynomial.rename (relab N (headStart t))
            (crossProd ℚ (headLen N t + 1) (pkRBCc N t (c i)))))) +
      Finset.prod (range k) (fun j => X (c j)) *
        MvPolynomial.eval X (MvPolynomial.rename (relab N (headStart t))
          (pkRBNP ℚ (headLen N t + 1)
              (pkRBPull N (headStart t) (headLen N t + 1) ((range k).image c)))) := by
  have f1 := pkR_b_head_facts hE ht
  have np := fun i (hi : i < k) => pkR_b_nest_pos hE ht (hc i hi) (hsub i hi) (hct i hi).symm
  have fc := fun i (hi : i < k) => pkR_b_head_facts hE (hc i hi)
  -- nesting of the chain in positions from `headStart t`
  have hnest : ∀ i < k, ∀ j < k, i ≤ j →
      cycPos N (headStart t) (headStart (c j)) ≤ cycPos N (headStart t) (headStart (c i)) ∧
        cycPos N (headStart t) (headStart (c i)) + headLen N (c i) ≤
          cycPos N (headStart t) (headStart (c j)) + headLen N (c j) := by
    intro i hi j hj hij
    obtain ⟨-, a2, a3, a4⟩ := np i hi
    obtain ⟨-, b2, b3, b4⟩ := np j hj
    have fi := fc i hi
    have fj := fc j hj
    have m1 := (b4 (cycPos N (headStart t) (headStart (c i))) (by omega)).1
      (hord i hi j hj hij ((a4 (cycPos N (headStart t) (headStart (c i)))
          (by omega)).2 ⟨le_rfl, by omega⟩))
    have m2 := (b4 (cycPos N (headStart t) (headStart (c i)) + headLen N (c i) - 1) (by omega)).1
      (hord i hi j hj hij ((a4 (cycPos N (headStart t) (headStart (c i)) + headLen N (c i) - 1)
          (by omega)).2
        ⟨by omega, by omega⟩))
    omega
  have hC' : ∀ i < k, pkRBCc N t (c i) ∈ oddDiagonals (headLen N t + 1) := by
    intro i hi
    obtain ⟨a1, a2, a3, -⟩ := np i hi
    have b := fc i hi
    exact pkR_b_odd_iff.2 ⟨by omega, by omega, by omega, by omega, by omega⟩
  have hrel : ∀ i < k, relab N (headStart t) (pkRBCc N t (c i)) = c i := by
    intro i hi
    obtain ⟨a1, a2, a3, -⟩ := np i hi
    exact pkR_b_relab_head (hc i hi) ⟨f1.1, f1.2.1⟩ (by omega)
      (pkR_b_vtx_cyc ⟨f1.1, f1.2.1⟩ ⟨(fc i hi).1, (fc i hi).2.1⟩)
  have hinj' : ∀ i < k, ∀ j < i, pkRBCc N t (c j) ≠ pkRBCc N t (c i) := by
    intro i hi j hj e
    exact hinj i hi j hj ((hrel j (by omega)).symm.trans
        ((congrArg (relab N (headStart t)) e).trans (hrel i hi)))
  have hS : ∀ i < k, oddSide (headLen N t + 1) (pkRBCc N t (c i)) =
      Icc (cycPos N (headStart t) (headStart (c i)) + 1)
        (cycPos N (headStart t) (headStart (c i)) + headLen N (c i)) :=
            fun i hi => pkR_b_oS1 (np i hi).1
  have hord' : ∀ i < k, ∀ j < k, i ≤ j →
      oddSide (headLen N t + 1) (pkRBCc N t (c i)) ⊆ oddSide (headLen N t + 1)
          (pkRBCc N t (c j)) := by
    intro i hi j hj hij
    rw [hS i hi, hS j hj]
    intro x hx
    rw [mem_Icc] at hx ⊢
    have := hnest i hi j hj hij
    omega
  have hnc' : ∀ i < k, ∀ j < k, ¬ Crosses (pkRBCc N t (c j)) (pkRBCc N t (c i)) := by
    intro i hi j hj hcr
    have e : ∀ l, pkRBCc N t (c l) = (cycPos N (headStart t) (headStart (c l)) + 1,
        cycPos N (headStart t) (headStart (c l)) + headLen N (c l) + 1) := fun l => rfl
    rw [e i, e j] at hcr
    unfold Crosses at hcr
    dsimp only at hcr
    rcases le_total i j with h | h
    · have := hnest i hi j hj h
      omega
    · have := hnest j hj i hi h
      omega
  -- the banned set of the head child is the set of child chords
  have hKo : (range k).image c ⊆ oddDiagonals N := by
    intro d hd
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hd
    exact hc j (mem_range.1 hj)
  have hKt : ∀ Q ∈ (range k).image c, oddSide N Q ⊆ oddSide N t := by
    intro Q hQ
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hQ
    exact hsub j (mem_range.1 hj)
  have hnt : t ∉ (range k).image c := by
    intro h
    obtain ⟨i, hi, e⟩ := mem_image.1 h
    exact hct i (mem_range.1 hi) e
  have hK' : pkRBPull N (headStart t) (headLen N t + 1) ((range k).image c) =
      (range k).image (fun i => pkRBCc N t (c i)) := by
    rw [pkR_b_pull_head hE ht hKo hKt, erase_eq_self.2 hnt, image_image]
    rfl
  have h2 := pkR_b_R2bot (R := ℚ) (N := headLen N t + 1) (by omega) (by omega)
      (fun i => pkRBCc N t (c i)) k
    hC' hinj' hord' hnc'
  rw [h2, hK', map_add, map_add, map_sum, map_sum]
  refine congrArg₂ (· + ·) (sum_congr rfl fun i hi => ?_) ?_
  · have hi' := mem_range.1 hi
    obtain ⟨a1, a2, a3, -⟩ := np i hi'
    have fci := fc i hi'
    have hd := pkR_b_cc_data (n := headLen N t + 1) t (c i) a1
    simp only [map_mul, map_prod, MvPolynomial.rename_X, MvPolynomial.eval_X]
    refine congrArg₂ (· * ·) (prod_congr rfl fun j hj => ?_)
        (congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ ?_) rfl)
    · rw [hrel j (by have := mem_range.1 hj; omega)]
    · -- `b_{c i}`: the grandchild A-child is the parent A-child of `c i`
      rw [hd.1, hd.2.1, ← hK',
        pkR_b_pull_comp (N := N) (s := headStart t) (n := headLen N t + 1)
          (p := cycPos N (headStart t) (headStart (c i))) (L' := headLen N (c i))
              ⟨f1.1, f1.2.1⟩ (by omega)
          (by omega) (by omega),
        pkR_b_vtx_cyc ⟨f1.1, f1.2.1⟩ ⟨fci.1, fci.2.1⟩, MvPolynomial.eval_rename,
            MvPolynomial.eval_rename,
        MvPolynomial.eval_rename]
      refine pkR_b_NPK_local _ (fun d hd' => ?_)
      have hdd := mem_diagonals.1 hd'
      change X (relab N (headStart t)
          (relab (headLen N t + 1) (cycPos N (headStart t) (headStart (c i)) + 1) d)) =
        X (relab N (headStart (c i)) d)
      rw [pkR_b_relab_comp (N := N) (s := headStart t) (n := headLen N t + 1)
        (p := cycPos N (headStart t) (headStart (c i))) (d := d) ⟨f1.1, f1.2.1⟩ (by omega)
            (by omega) (by omega),
        pkR_b_vtx_cyc ⟨f1.1, f1.2.1⟩ ⟨fci.1, fci.2.1⟩]
    · -- `N_{Ω(t, c i)}`: the rotation bridge
      rw [hd.2.2.1, hd.2.2.2,
        show headLen N t + 1 - headLen N (c i) + 1 = headLen N t - headLen N (c i) + 2 by omega]
      exact pkR_b_omega_relab (N := N) (a := headStart t)
          (p := cycPos N (headStart t) (headStart (c i)))
        (L := headLen N t) (L' := headLen N (c i))
            ⟨f1.1, f1.2.1⟩ a1 f1.2.2.2.1 fci.2.2.2.1 (by omega) (by omega)
        (by omega) X
  · simp only [map_mul, map_prod, MvPolynomial.rename_X, MvPolynomial.eval_X]
    refine congrArg₂ (· * ·) (prod_congr rfl fun j hj => ?_) rfl
    rw [hrel j (mem_range.1 hj)]

/-- **The A-side collapse on `X_Q = x`**: `pkR_b_R2A` (with its hypotheses) evaluated at a point
where every chord `c i` takes the value `x`. -/
theorem pkR_b_R2A_eval {N : ℕ} (hE : N % 2 = 0) {t : ℕ × ℕ} (ht : t ∈ oddDiagonals N)
    (c : ℕ → ℕ × ℕ) (k : ℕ) (hc : ∀ i < k, c i ∈ oddDiagonals N) (hct : ∀ i < k, c i ≠ t)
    (hsub : ∀ i < k, oddSide N (c i) ⊆ oddSide N t) (hinj : ∀ i < k, ∀ j < i, c j ≠ c i)
    (hord : ∀ i < k, ∀ j < k, i ≤ j → oddSide N (c i) ⊆ oddSide N (c j)) {X : ℕ × ℕ → ℚ} {x : ℚ}
    (hx : ∀ i < k, X (c i) = x) :
    MvPolynomial.eval X (MvPolynomial.rename (relab N (headStart t)) (NP ℚ (headLen N t + 1))) =
      Finset.sum (range k) (fun i => x ^ i *
        (MvPolynomial.eval X (MvPolynomial.rename (relab N (headStart (c i)))
            (pkRBNP ℚ (headLen N (c i) + 1)
              (pkRBPull N (headStart (c i)) (headLen N (c i) + 1) ((range k).image c)))) *
          MvPolynomial.eval (pkRBOmX N t (c i) X) (NP ℚ (pkRBOmM N t (c i))) *
          MvPolynomial.eval X (MvPolynomial.rename (relab N (headStart t))
            (crossProd ℚ (headLen N t + 1) (pkRBCc N t (c i)))))) +
      x ^ k * MvPolynomial.eval X (MvPolynomial.rename (relab N (headStart t))
          (pkRBNP ℚ (headLen N t + 1)
              (pkRBPull N (headStart t) (headLen N t + 1) ((range k).image c)))) := by
  have hp : ∀ i ≤ k, Finset.prod (range i) (fun j => X (c j)) = x ^ i := fun i hi => by
    rw [prod_congr rfl (fun j hj => hx j (by have := mem_range.1 hj; omega)),
        prod_const, card_range]
  rw [pkR_b_R2A hE ht c k hc hct hsub hinj hord X, hp k le_rfl]
  refine congrArg₂ (· + ·) (sum_congr rfl fun i hi => ?_) rfl
  rw [hp i (by have := mem_range.1 hi; omega)]

/-! ### The Ω formula on the standard polygon

By strong induction on `n`, for every set `I` of members. -/

/-- `Λ^I` is antitone in `I`. -/
theorem pkR_om_lamSub {n d₁ : ℕ} {I I' : Finset (ℕ × ℕ)} (h : I' ⊆ I) {X : ℕ × ℕ → ℚ}
    (hX : pkRLam n d₁ I X) : pkRLam n d₁ I' X := by
  obtain ⟨h1, h2, h3⟩ := (pkR_lam_iff _ _ _ _).1 hX
  exact (pkR_lam_iff _ _ _ _).2 ⟨h1, h2, fun Q hQ => h3 Q (h hQ)⟩

/-- For even `n ≥ 4` and a set `I` of standard members (`pkRIsMem`, `C7`), every member chord of
`I` has `X_Q = x` on `Λ^I` (from `pkR_XQ`, `C6`). -/
theorem pkR_om_XQ {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ : ℕ} {I : Finset (ℕ × ℕ)}
    (hI : ∀ Q ∈ I, pkRIsMem n d₁ Q) {X : ℕ × ℕ → ℚ} (hX : pkRLam n d₁ I X) {Q : ℕ × ℕ}
    (hQ : Q ∈ I) :
    X (pkRMchord d₁ Q) = mesh n X 1 (n - 1) := by
  obtain ⟨m1, m2, m3, m4⟩ := (pkR_isMem_iff _ _ _).1 (hI Q hQ)
  have hm : (2 * Q.1 + 1, 2 * d₁ + 2 * Q.2 + 2) ∈ oddDiagonals n := pkR_mchord_mem m1 m2 m3 m4
  have hmd := mem_diagonals.1 (mem_filter.1 hm).1
  dsimp only at hmd
  have e := pkR_XQ hE hn m1 m2 m3 m4 hX (((pkR_lam_iff _ _ _ _).1 hX).2.2 Q hQ)
  rw [planar_of_mem X (by omega) (by omega) (by omega), ite_eq_left (mem_filter.1 hm).1] at e
  exact e

theorem pkR_om_crIff (a b c d : ℕ) :
    Crosses (a, b) (c, d) ↔ (a < c ∧ c < b ∧ b < d) ∨ (c < a ∧ a < d ∧ d < b) := Iff.rfl

/-- The member set of the A-child of `q = (i, j)` (members strictly below `q`, shifted; the image
set of `pkR_childA` (`C8`) without the image of `q` itself, which is the child's `a`). -/
def pkROmIA (d₁ i j : ℕ) (I : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  (I.filter (fun Q => (i ≤ Q.1 ∧ Q.1 ≤ i + (d₁ - i) ∧ 0 ≤ Q.2 ∧ Q.2 ≤ 0 + j) ∧ Q ≠ (i, j))).image
    (fun Q => (Q.1 - i, Q.2 - 0))

/-- The member set of the B-child of `q = (i, j)` (members strictly above `q`, shifted; the image
set of `pkR_childB` (`C8`) without the image of `q` itself, which is the child's `b`). -/
def pkROmIB (n d₁ i j : ℕ) (I : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  (I.filter (fun Q =>
      (0 ≤ Q.1 ∧ Q.1 ≤ 0 + i ∧ j ≤ Q.2 ∧ Q.2 ≤ j + (n / 2 - 1 - d₁ - j)) ∧ Q ≠ (i, j))).image
    (fun Q => (Q.1 - 0, Q.2 - j))

theorem pkR_om_subA (d₁ i j : ℕ) (I : Finset (ℕ × ℕ)) : pkROmIA d₁ i j I ⊆
    (I.filter (fun Q => i ≤ Q.1 ∧ Q.1 ≤ i + (d₁ - i) ∧ 0 ≤ Q.2 ∧
        Q.2 ≤ 0 + j)).image (fun Q => (Q.1 - i, Q.2 - 0)) := by
  intro Q' hQ'
  unfold pkROmIA at hQ'
  obtain ⟨Q, hQf, rfl⟩ := mem_image.1 hQ'
  exact mem_image.2 ⟨Q, mem_filter.2 ⟨(mem_filter.1 hQf).1, (mem_filter.1 hQf).2.1⟩, rfl⟩

theorem pkR_om_subB (n d₁ i j : ℕ) (I : Finset (ℕ × ℕ)) : pkROmIB n d₁ i j I ⊆
    (I.filter (fun Q => 0 ≤ Q.1 ∧ Q.1 ≤ 0 + i ∧ j ≤ Q.2 ∧ Q.2 ≤ j + (n / 2 - 1 - d₁ - j))).image
      (fun Q => (Q.1 - 0, Q.2 - j)) := by
  intro Q' hQ'
  unfold pkROmIB at hQ'
  obtain ⟨Q, hQf, rfl⟩ := mem_image.1 hQ'
  exact mem_image.2 ⟨Q, mem_filter.2 ⟨(mem_filter.1 hQf).1, (mem_filter.1 hQf).2.1⟩, rfl⟩

/-- For a set `I` of members, the A-child member set consists of members of the A-child
`(q′ − p′ + 1, d₁ − i)`. -/
theorem pkR_om_isMemA {n d₁ i j : ℕ} {I : Finset (ℕ × ℕ)} (hI : ∀ Q ∈ I, pkRIsMem n d₁ Q) :
    ∀ Q' ∈ pkROmIA d₁ i j I, pkRIsMem (2 * d₁ + 2 * j + 2 - (2 * i + 1) + 1) (d₁ - i) Q' := by
  intro Q' hQ'
  unfold pkROmIA at hQ'
  obtain ⟨⟨Q1, Q2⟩, hQf, rfl⟩ := mem_image.1 hQ'
  obtain ⟨hQ, hc, hne⟩ := mem_filter.1 hQf
  have c : i ≤ Q1 ∧ Q1 ≤ i + (d₁ - i) ∧ 0 ≤ Q2 ∧ Q2 ≤ 0 + j := hc
  have m : Q1 ≤ d₁ ∧ 2 * d₁ + 2 * Q2 + 2 ≤ n ∧ ¬ (Q1 = d₁ ∧ Q2 = 0) ∧
      ¬ (Q1 = 0 ∧ 2 * d₁ + 2 * Q2 + 2 = n) :=
    hI _ hQ
  have hne' := pkR_ne_pair hne
  change Q1 - i ≤ d₁ - i ∧ 2 * (d₁ - i) + 2 * (Q2 - 0) + 2 ≤ 2 * d₁ + 2 * j + 2 - (2 * i + 1) + 1 ∧
    ¬ (Q1 - i = d₁ - i ∧ Q2 - 0 = 0) ∧
    ¬ (Q1 - i = 0 ∧ 2 * (d₁ - i) + 2 * (Q2 - 0) + 2 = 2 * d₁ + 2 * j + 2 - (2 * i + 1) + 1)
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- For a set `I` of members, the B-child member set consists of members of the B-child
`(n − q′ + p′ + 1, i)`. -/
theorem pkR_om_isMemB {n d₁ i j : ℕ} {I : Finset (ℕ × ℕ)} (hI : ∀ Q ∈ I, pkRIsMem n d₁ Q) :
    ∀ Q' ∈ pkROmIB n d₁ i j I,
      pkRIsMem (n - (2 * d₁ + 2 * j + 2) + (2 * i + 1) + 1) i Q' := by
  intro Q' hQ'
  unfold pkROmIB at hQ'
  obtain ⟨⟨Q1, Q2⟩, hQf, rfl⟩ := mem_image.1 hQ'
  obtain ⟨hQ, hc, hne⟩ := mem_filter.1 hQf
  have c : 0 ≤ Q1 ∧ Q1 ≤ 0 + i ∧ j ≤ Q2 ∧ Q2 ≤ j + (n / 2 - 1 - d₁ - j) := hc
  have m : Q1 ≤ d₁ ∧ 2 * d₁ + 2 * Q2 + 2 ≤ n ∧ ¬ (Q1 = d₁ ∧ Q2 = 0) ∧
      ¬ (Q1 = 0 ∧ 2 * d₁ + 2 * Q2 + 2 = n) :=
    hI _ hQ
  have hne' := pkR_ne_pair hne
  change Q1 - 0 ≤ i ∧ 2 * i + 2 * (Q2 - j) + 2 ≤ n - (2 * d₁ + 2 * j + 2) + (2 * i + 1) + 1 ∧
    ¬ (Q1 - 0 = i ∧ Q2 - j = 0) ∧
    ¬ (Q1 - 0 = 0 ∧ 2 * i + 2 * (Q2 - j) + 2 = n - (2 * d₁ + 2 * j + 2) + (2 * i + 1) + 1)
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- **Count identity**: for a set `I` of members with `q = (i, j) ∈ I`, `|I|` is the number of
members of the A-child set plus that of the B-child set plus the number of members whose chord
crosses that of `q`, plus one: the members of `I` other than `q` are strictly below `q` (A-child),
strictly above `q` (B-child), or cross `q`. -/
theorem pkR_om_count {n d₁ i j : ℕ} {I : Finset (ℕ × ℕ)} (hI : ∀ Q ∈ I, pkRIsMem n d₁ Q)
    (hq : (i, j) ∈ I) :
    I.card = (pkROmIA d₁ i j I).card + (pkROmIB n d₁ i j I).card +
      (I.filter (fun Q => Crosses (pkRMchord d₁ Q) (2 * i + 1, 2 * d₁ + 2 * j + 2))).card + 1 := by
  have injA : Set.InjOn (fun Q : ℕ × ℕ => (Q.1 - i, Q.2 - 0))
      ((I.filter (fun Q => (i ≤ Q.1 ∧ Q.1 ≤ i + (d₁ - i) ∧ 0 ≤ Q.2 ∧ Q.2 ≤ 0 + j) ∧ Q ≠ (i, j))) :
        Set (ℕ × ℕ)) := by
    rintro ⟨a1, a2⟩ ha ⟨b1, b2⟩ hb h
    have ha' : i ≤ a1 ∧ a1 ≤ i + (d₁ - i) ∧ 0 ≤ a2 ∧ a2 ≤ 0 + j :=
        (mem_filter.1 (Finset.mem_coe.1 ha)).2.1
    have hb' : i ≤ b1 ∧ b1 ≤ i + (d₁ - i) ∧ 0 ≤ b2 ∧ b2 ≤ 0 + j :=
        (mem_filter.1 (Finset.mem_coe.1 hb)).2.1
    have h1 : a1 - i = b1 - i := congrArg Prod.fst h
    have h2 : a2 - 0 = b2 - 0 := congrArg Prod.snd h
    have e1 : a1 = b1 := by omega
    have e2 : a2 = b2 := by omega
    rw [e1, e2]
  have injB : Set.InjOn (fun Q : ℕ × ℕ => (Q.1 - 0, Q.2 - j))
      ((I.filter (fun Q =>
          (0 ≤ Q.1 ∧ Q.1 ≤ 0 + i ∧ j ≤ Q.2 ∧ Q.2 ≤ j + (n / 2 - 1 - d₁ - j)) ∧ Q ≠ (i, j))) :
        Set (ℕ × ℕ)) := by
    rintro ⟨a1, a2⟩ ha ⟨b1, b2⟩ hb h
    have ha' : 0 ≤ a1 ∧ a1 ≤ 0 + i ∧ j ≤ a2 ∧ a2 ≤ j + (n / 2 - 1 - d₁ - j) :=
      (mem_filter.1 (Finset.mem_coe.1 ha)).2.1
    have hb' : 0 ≤ b1 ∧ b1 ≤ 0 + i ∧ j ≤ b2 ∧ b2 ≤ j + (n / 2 - 1 - d₁ - j) :=
      (mem_filter.1 (Finset.mem_coe.1 hb)).2.1
    have h1 : a1 - 0 = b1 - 0 := congrArg Prod.fst h
    have h2 : a2 - j = b2 - j := congrArg Prod.snd h
    have e1 : a1 = b1 := by omega
    have e2 : a2 = b2 := by omega
    rw [e1, e2]
  have cA : (pkROmIA d₁ i j I).card =
      (I.filter (fun Q =>
          (i ≤ Q.1 ∧ Q.1 ≤ i + (d₁ - i) ∧ 0 ≤ Q.2 ∧ Q.2 ≤ 0 + j) ∧ Q ≠ (i, j))).card :=
    card_image_of_injOn injA
  have cB : (pkROmIB n d₁ i j I).card =
      (I.filter (fun Q =>
          (0 ≤ Q.1 ∧ Q.1 ≤ 0 + i ∧ j ≤ Q.2 ∧ Q.2 ≤ j + (n / 2 - 1 - d₁ - j)) ∧ Q ≠ (i, j))).card :=
    card_image_of_injOn injB
  have hsum : ∀ Q ∈ I, (1 : ℕ) =
      (if (i ≤ Q.1 ∧ Q.1 ≤ i + (d₁ - i) ∧ 0 ≤ Q.2 ∧ Q.2 ≤ 0 + j) ∧ Q ≠ (i, j) then 1 else 0) +
      (if (0 ≤ Q.1 ∧ Q.1 ≤ 0 + i ∧ j ≤ Q.2 ∧ Q.2 ≤ j + (n / 2 - 1 - d₁ - j)) ∧
          Q ≠ (i, j) then 1 else 0) +
      (if Crosses (pkRMchord d₁ Q) (2 * i + 1, 2 * d₁ + 2 * j + 2) then 1 else 0) +
      (if Q = (i, j) then 1 else 0) := by
    rintro ⟨Q1, Q2⟩ hQ
    have m : Q1 ≤ d₁ ∧ 2 * d₁ + 2 * Q2 + 2 ≤ n ∧ ¬ (Q1 = d₁ ∧ Q2 = 0) ∧
        ¬ (Q1 = 0 ∧ 2 * d₁ + 2 * Q2 + 2 = n) :=
      hI _ hQ
    have mq : i ≤ d₁ ∧ 2 * d₁ + 2 * j + 2 ≤ n ∧ ¬ (i = d₁ ∧ j = 0) ∧
        ¬ (i = 0 ∧ 2 * d₁ + 2 * j + 2 = n) :=
      hI _ hq
    have ec : Crosses (pkRMchord d₁ (Q1, Q2)) (2 * i + 1, 2 * d₁ + 2 * j + 2) ↔
        (Q1 < i ∧ Q2 < j) ∨ (i < Q1 ∧ j < Q2) := by
      rw [show pkRMchord d₁ (Q1, Q2) = (2 * Q1 + 1, 2 * d₁ + 2 * Q2 + 2) from rfl, pkR_om_crIff]
      constructor <;> intro h <;> omega
    simp only [ec, ne_eq, Prod.mk.injEq]
    split_ifs <;> omega
  rw [cA, cB, card_filter, card_filter, card_filter, card_eq_sum_ones, sum_congr rfl hsum,
      sum_add_distrib,
    sum_add_distrib, sum_add_distrib, sum_ite_eq']
  simp [hq]

/-- **The crossing factor on `Λ^I`** (`n ≥ 4` even, `I` a set of members):
`cross_q = x^{#(crossing members)} · cross′_q`, `cross′_q` = the crossing odd chords that are not
member chords of `I` (`pkRBCross` (`C6`) with `K = chords(I)`). -/
theorem pkR_om_cross {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) {d₁ i j : ℕ} {I : Finset (ℕ × ℕ)}
    (hI : ∀ Q ∈ I, pkRIsMem n d₁ Q) {X : ℕ × ℕ → ℚ} (hX : pkRLam n d₁ I X) :
    MvPolynomial.eval X (crossProd ℚ n (2 * i + 1, 2 * d₁ + 2 * j + 2)) =
      mesh n X 1 (n - 1) ^ (I.filter (fun Q => Crosses (pkRMchord d₁ Q)
          (2 * i + 1, 2 * d₁ + 2 * j + 2))).card *
        MvPolynomial.eval X (pkRBCross ℚ n (I.image (pkRMchord d₁))
            (2 * i + 1, 2 * d₁ + 2 * j + 2)) := by
  have e1 : crossProd ℚ n (2 * i + 1, 2 * d₁ + 2 * j + 2) = Finset.prod ((oddDiagonals n).filter
      (fun d => Crosses d (2 * i + 1, 2 * d₁ + 2 * j + 2))) (fun d => MvPolynomial.X d) := rfl
  have e2 : pkRBCross ℚ n (I.image (pkRMchord d₁)) (2 * i + 1, 2 * d₁ + 2 * j + 2) =
      Finset.prod (((oddDiagonals n).filter (fun d => Crosses d (2 * i + 1, 2 * d₁ + 2 * j + 2))) \
        I.image (pkRMchord d₁)) (fun d => MvPolynomial.X d) := rfl
  have hint : (oddDiagonals n).filter (fun d => Crosses d (2 * i + 1, 2 * d₁ + 2 * j + 2)) ∩
      I.image (pkRMchord d₁) =
      (I.filter (fun Q => Crosses (pkRMchord d₁ Q)
          (2 * i + 1, 2 * d₁ + 2 * j + 2))).image (pkRMchord d₁) := by
    ext d
    rw [mem_inter, mem_filter, mem_image, mem_image]
    constructor
    · rintro ⟨⟨-, hc⟩, Q, hQ, rfl⟩
      exact ⟨Q, mem_filter.2 ⟨hQ, hc⟩, rfl⟩
    · rintro ⟨Q, hQ, rfl⟩
      obtain ⟨hQI, hc⟩ := mem_filter.1 hQ
      obtain ⟨m1, m2, m3, m4⟩ := (pkR_isMem_iff _ _ _).1 (hI Q hQI)
      exact ⟨⟨pkR_mchord_mem m1 m2 m3 m4, hc⟩, Q, hQI, rfl⟩
  rw [e1, e2, ← prod_inter_mul_prod_sdiff ((oddDiagonals n).filter
      (fun d => Crosses d (2 * i + 1, 2 * d₁ + 2 * j + 2))) (I.image (pkRMchord d₁)), hint,
    prod_image (fun a _ b _ h => pkR_mchord_inj h)]
  simp only [map_mul, map_prod, MvPolynomial.eval_X]
  rw [prod_congr rfl (fun Q hQ => pkR_om_XQ hE hn hI hX (mem_filter.1 hQ).1), prod_const]

/-- Reindexing a filtered product over the odd chords of the `m`-gon (`m ≥ 4` even) by one
rotation. -/
theorem pkR_om_rot1 {m : ℕ} (hm : 4 ≤ m) (hE : m % 2 = 0) (P : ℕ × ℕ → Prop) [DecidablePred P]
    (g : ℕ × ℕ → ℚ) :
    Finset.prod ((oddDiagonals m).filter P) g =
      Finset.prod ((oddDiagonals m).filter (fun d => P (rot m d))) (fun d => g (rot m d)) := by
  refine (Finset.prod_bij (fun d _ => rot m d) (fun d hd => ?_) (fun a ha b hb h => ?_)
      (fun e he => ?_)
    (fun d _ => rfl)).symm
  · obtain ⟨h1, h2⟩ := mem_filter.1 hd
    exact mem_filter.2 ⟨(pkR_rot_par hm hE (mem_filter.1 h1).1).2 h1, h2⟩
  · exact rot_inj (by omega)
      (mem_filter.1 (mem_filter.1 ha).1).1 (mem_filter.1 (mem_filter.1 hb).1).1 h
  · obtain ⟨h1, h2⟩ := mem_filter.1 he
    obtain ⟨d0, hd0, h⟩ := rot_surj (show 1 ≤ m by omega) (mem_filter.1 h1).1
    have h1' : rot m d0 ∈ oddDiagonals m := by rw [h]; exact h1
    have h2' : P (rot m d0) := by rw [h]; exact h2
    exact ⟨d0, mem_filter.2 ⟨(pkR_rot_par hm hE hd0).1 h1', h2'⟩, h⟩

/-- Reindexing a filtered product over the odd chords of the `m`-gon (`m ≥ 4` even) by an iterated
rotation. -/
theorem pkR_om_rotk {m : ℕ} (hm : 4 ≤ m) (hE : m % 2 = 0) (k : ℕ) (P : ℕ × ℕ → Prop)
    [DecidablePred P] (g : ℕ × ℕ → ℚ) :
    Finset.prod ((oddDiagonals m).filter P) g =
      Finset.prod ((oddDiagonals m).filter (fun d => P ((rot m)^[k] d)))
          (fun d => g ((rot m)^[k] d)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [ih, pkR_om_rot1 hm hE (fun d => P ((rot m)^[k] d)) (fun d => g ((rot m)^[k] d))]
    rfl

/-- `ψ_P` (`pkRBPsi`, `C6`) on a product of variables keeps the variables outside `P`. -/
theorem pkR_om_psiP (P : ℕ × ℕ → Prop) [DecidablePred P] (s : Finset (ℕ × ℕ)) :
    pkRBPsi ℚ P (Finset.prod s (fun d => MvPolynomial.X d)) =
      Finset.prod (s.filter (fun d => ¬ P d))
          (fun d => (MvPolynomial.X d : MvPolynomial (ℕ × ℕ) ℚ)) := by
  rw [map_prod]
  have e : ∀ d ∈ s, pkRBPsi ℚ P (MvPolynomial.X d) = if P d then 1 else MvPolynomial.X d :=
    fun d _ => pkR_b_psi_X _ d
  rw [prod_congr rfl e, prod_ite, prod_const_one, one_mul]

/-- **Member correspondence, A-child**: for a set `I` of members and `q = (i, j)` with `i ≤ d₁` and
`q′ = 2d₁ + 2j + 2 ≤ n`, a child diagonal is a child member chord of `pkROmIA` iff its `relab n p′`
image (`p′ = 2i + 1`) is a member chord of `I`. -/
theorem pkR_om_memA {n d₁ i j : ℕ} {I : Finset (ℕ × ℕ)} (hI : ∀ Q ∈ I, pkRIsMem n d₁ Q)
    (hi : i ≤ d₁) (hj : 2 * d₁ + 2 * j + 2 ≤ n) {d : ℕ × ℕ}
    (hd : d ∈ diagonals (2 * d₁ + 2 * j + 2 - (2 * i + 1) + 1)) :
    relab n (2 * i + 1) d ∈ I.image (pkRMchord d₁) ↔
      d ∈ (pkROmIA d₁ i j I).image (pkRMchord (d₁ - i)) := by
  obtain ⟨a, b⟩ := d
  have hdd := mem_diagonals.1 hd
  dsimp only at hdd
  obtain ⟨u, hu⟩ : ∃ u, u = vtx n (a + (2 * i + 1) - 1) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = vtx n (b + (2 * i + 1) - 1) := ⟨_, rfl⟩
  have hu' := pkR_b_vtx2 (N := n) (u := a + (2 * i + 1) - 1) (by omega) (by omega)
  have hv' := pkR_b_vtx2 (N := n) (u := b + (2 * i + 1) - 1) (by omega) (by omega)
  rw [← hu] at hu'
  rw [← hv] at hv'
  have e : relab n (2 * i + 1) (a, b) = (min u v, max u v) := by rw [hu, hv]; rfl
  rw [e, mem_image, mem_image]
  constructor
  · rintro ⟨⟨Q1, Q2⟩, hQ, hQe⟩
    have m : Q1 ≤ d₁ ∧ 2 * d₁ + 2 * Q2 + 2 ≤ n ∧ ¬ (Q1 = d₁ ∧ Q2 = 0) ∧
        ¬ (Q1 = 0 ∧ 2 * d₁ + 2 * Q2 + 2 = n) := hI _ hQ
    have h1 : 2 * Q1 + 1 = min u v := congrArg Prod.fst hQe
    have h2 : 2 * d₁ + 2 * Q2 + 2 = max u v := congrArg Prod.snd hQe
    refine ⟨(Q1 - i, Q2 - 0), ?_, ?_⟩
    · unfold pkROmIA
      refine mem_image.2 ⟨(Q1, Q2), mem_filter.2 ⟨hQ, ?_, fun h => ?_⟩, rfl⟩
      · exact (show i ≤ Q1 ∧ Q1 ≤ i + (d₁ - i) ∧ 0 ≤ Q2 ∧ Q2 ≤ 0 + j from
          ⟨by omega, by omega, by omega, by omega⟩)
      · have h1' : Q1 = i := congrArg Prod.fst h
        have h2' : Q2 = j := congrArg Prod.snd h
        omega
    · change (2 * (Q1 - i) + 1, 2 * (d₁ - i) + 2 * (Q2 - 0) + 2) = (a, b)
      rw [Prod.mk.injEq]
      constructor <;> omega
  · rintro ⟨Q', hQ', hQe⟩
    unfold pkROmIA at hQ'
    obtain ⟨⟨Q1, Q2⟩, hQf, rfl⟩ := mem_image.1 hQ'
    obtain ⟨hQ, hc, -⟩ := mem_filter.1 hQf
    have c : i ≤ Q1 ∧ Q1 ≤ i + (d₁ - i) ∧ 0 ≤ Q2 ∧ Q2 ≤ 0 + j := hc
    have m : Q1 ≤ d₁ ∧ 2 * d₁ + 2 * Q2 + 2 ≤ n ∧ ¬ (Q1 = d₁ ∧ Q2 = 0) ∧
        ¬ (Q1 = 0 ∧ 2 * d₁ + 2 * Q2 + 2 = n) := hI _ hQ
    have h1 : 2 * (Q1 - i) + 1 = a := congrArg Prod.fst hQe
    have h2 : 2 * (d₁ - i) + 2 * (Q2 - 0) + 2 = b := congrArg Prod.snd hQe
    refine ⟨(Q1, Q2), hQ, ?_⟩
    change (2 * Q1 + 1, 2 * d₁ + 2 * Q2 + 2) = (min u v, max u v)
    rw [Prod.mk.injEq]
    constructor <;> omega

/-- **Member correspondence, B-child**: for a set `I` of members and `q = (i, j) ≠ (d₁, 0)` with
`i ≤ d₁` and `q′ = 2d₁ + 2j + 2 ≤ n`, a child diagonal is a child member chord of `pkROmIB` iff its
image under the rotation by `n − q′ + 1` and `relab n q′` is a member chord of `I` (through the
rotation bridge `pkR_rotG_pair`, `C8`). -/
theorem pkR_om_memB {n d₁ i j : ℕ} {I : Finset (ℕ × ℕ)} (hI : ∀ Q ∈ I, pkRIsMem n d₁ Q)
    (hi : i ≤ d₁) (hj : 2 * d₁ + 2 * j + 2 ≤ n) (hb : ¬ (i = d₁ ∧ j = 0)) {d : ℕ × ℕ}
    (hd : d ∈ diagonals (n - (2 * d₁ + 2 * j + 2) + (2 * i + 1) + 1)) :
    relab n (2 * d₁ + 2 * j + 2)
    ((rot (n - (2 * d₁ + 2 * j + 2) + (2 * i + 1) + 1))^[n - (2 * d₁ + 2 * j + 2) + 1] d)
        ∈ I.image (pkRMchord d₁) ↔
      d ∈ (pkROmIB n d₁ i j I).image (pkRMchord i) := by
  obtain ⟨a, b⟩ := d
  have hdd := mem_diagonals.1 hd
  dsimp only at hdd
  rw [pkR_rot_iter (by omega) _ (a, b) hd]
  dsimp only
  rw [pkR_rotG_pair (n := n) (p := 2 * i + 1) (q := 2 * d₁ + 2 * j + 2) (by omega) (by omega) hj hd]
  obtain ⟨fa, hfa⟩ : ∃ fa, fa =
      (if a ≤ 2 * i + 1 then a else a + (2 * d₁ + 2 * j + 2 - (2 * i + 1) - 1)) :=
    ⟨_, rfl⟩
  obtain ⟨fb, hfb⟩ : ∃ fb, fb =
      (if b ≤ 2 * i + 1 then b else b + (2 * d₁ + 2 * j + 2 - (2 * i + 1) - 1)) :=
    ⟨_, rfl⟩
  have hfa' : (a ≤ 2 * i + 1 ∧ fa = a) ∨
      (2 * i + 1 < a ∧ fa = a + (2 * d₁ + 2 * j + 2 - (2 * i + 1) - 1)) := by
    rw [hfa]; split_ifs <;> omega
  have hfb' : (b ≤ 2 * i + 1 ∧ fb = b) ∨
      (2 * i + 1 < b ∧ fb = b + (2 * d₁ + 2 * j + 2 - (2 * i + 1) - 1)) := by
    rw [hfb]; split_ifs <;> omega
  rw [← hfa, ← hfb, mem_image, mem_image]
  constructor
  · rintro ⟨⟨Q1, Q2⟩, hQ, hQe⟩
    have m : Q1 ≤ d₁ ∧ 2 * d₁ + 2 * Q2 + 2 ≤ n ∧ ¬ (Q1 = d₁ ∧ Q2 = 0) ∧
        ¬ (Q1 = 0 ∧ 2 * d₁ + 2 * Q2 + 2 = n) := hI _ hQ
    have h1 : 2 * Q1 + 1 = fa := congrArg Prod.fst hQe
    have h2 : 2 * d₁ + 2 * Q2 + 2 = fb := congrArg Prod.snd hQe
    refine ⟨(Q1 - 0, Q2 - j), ?_, ?_⟩
    · unfold pkROmIB
      refine mem_image.2 ⟨(Q1, Q2), mem_filter.2 ⟨hQ, ?_, fun h => ?_⟩, rfl⟩
      · exact (show 0 ≤ Q1 ∧ Q1 ≤ 0 + i ∧ j ≤ Q2 ∧ Q2 ≤ j + (n / 2 - 1 - d₁ - j) from
          ⟨by omega, by omega, by omega, by omega⟩)
      · have h1' : Q1 = i := congrArg Prod.fst h
        have h2' : Q2 = j := congrArg Prod.snd h
        omega
    · change (2 * (Q1 - 0) + 1, 2 * i + 2 * (Q2 - j) + 2) = (a, b)
      rw [Prod.mk.injEq]
      constructor <;> omega
  · rintro ⟨Q', hQ', hQe⟩
    unfold pkROmIB at hQ'
    obtain ⟨⟨Q1, Q2⟩, hQf, rfl⟩ := mem_image.1 hQ'
    obtain ⟨hQ, hc, -⟩ := mem_filter.1 hQf
    have c : 0 ≤ Q1 ∧ Q1 ≤ 0 + i ∧ j ≤ Q2 ∧ Q2 ≤ j + (n / 2 - 1 - d₁ - j) := hc
    have m : Q1 ≤ d₁ ∧ 2 * d₁ + 2 * Q2 + 2 ≤ n ∧ ¬ (Q1 = d₁ ∧ Q2 = 0) ∧
        ¬ (Q1 = 0 ∧ 2 * d₁ + 2 * Q2 + 2 = n) := hI _ hQ
    have h1 : 2 * (Q1 - 0) + 1 = a := congrArg Prod.fst hQe
    have h2 : 2 * i + 2 * (Q2 - j) + 2 = b := congrArg Prod.snd hQe
    refine ⟨(Q1, Q2), hQ, ?_⟩
    change (2 * Q1 + 1, 2 * d₁ + 2 * Q2 + 2) = (fa, fb)
    rw [Prod.mk.injEq]
    constructor <;> omega

/-- **The product identity of Ω**: for even `n`, a set `I` of members and `q = (i, j) ∈ I`,
`D′ = cross′_q · D′_A · D′_B` at every point, with `D′_A`, `D′_B` the children's `D′` read at the
child points of `pkR_omega_split` (`C8`). The proof takes `pkQ_odd_prod` of `PionNLSM` at
`T₁ = T₂ = ∅`, then `ψ_K` with `K = chords(I)`, then the member correspondences and the rotation
reindexing. -/
theorem pkR_om_prod {n : ℕ} (hE : n % 2 = 0) {d₁ i j : ℕ} (hi : i ≤ d₁)
    (hj : 2 * d₁ + 2 * j + 2 ≤ n) (hb : ¬ (i = d₁ ∧ j = 0))
    (ha : ¬ (i = 0 ∧ 2 * d₁ + 2 * j + 2 = n)) {I : Finset (ℕ × ℕ)} (hI : ∀ Q ∈ I, pkRIsMem n d₁ Q)
    (hq : (i, j) ∈ I) (X : ℕ × ℕ → ℚ) :
    Finset.prod ((oddDiagonals n).filter (fun Q => Q ∉ I.image (pkRMchord d₁))) (fun Q => X Q) =
      MvPolynomial.eval X (pkRBCross ℚ n (I.image (pkRMchord d₁))
          (2 * i + 1, 2 * d₁ + 2 * j + 2)) *
      Finset.prod ((oddDiagonals (2 * d₁ + 2 * j + 2 - (2 * i + 1) + 1)).filter
          (fun Q => Q ∉ (pkROmIA d₁ i j I).image (pkRMchord (d₁ - i))))
              (fun Q => (X ∘ relab n (2 * i + 1)) Q) *
      Finset.prod ((oddDiagonals (n - (2 * d₁ + 2 * j + 2) + (2 * i + 1) + 1)).filter
          (fun Q => Q ∉ (pkROmIB n d₁ i j I).image (pkRMchord i)))
        (fun Q => (X ∘ (relab n (2 * d₁ + 2 * j + 2) ∘
          (rot (n - (2 * d₁ + 2 * j + 2) + (2 * i + 1) + 1))^[n -
              (2 * d₁ + 2 * j + 2) + 1])) Q) := by
  have hQ : ((2 * i + 1, 2 * d₁ + 2 * j + 2) : ℕ × ℕ) ∈ oddDiagonals n := pkR_mchord_mem hi hj hb ha
  have hQd := mem_diagonals.1 (mem_filter.1 hQ).1
  dsimp only at hQd
  have hqK : ((2 * i + 1, 2 * d₁ + 2 * j + 2) : ℕ × ℕ) ∈ I.image (pkRMchord d₁) :=
      mem_image.2 ⟨(i, j), hq, rfl⟩
  have key := pkQ_odd_prod (R := ℚ) (N := n) (i := 2 * i + 1) (j := 2 * d₁ + 2 * j + 2)
      (by omega) (by omega)
    (by omega) (by omega) hE (T1 := ∅) (T2 := ∅) (empty_subset _) (empty_subset _)
  have k2 := congrArg (pkRBPsi ℚ (fun d => d ∈ I.image (pkRMchord d₁))) key
  have ec : pkRBPsi ℚ (fun d => d ∈ I.image (pkRMchord d₁))
      (crossProd ℚ n (2 * i + 1, 2 * d₁ + 2 * j + 2)) =
      pkRBCross ℚ n (I.image (pkRMchord d₁)) (2 * i + 1, 2 * d₁ + 2 * j + 2) :=
          pkR_b_psi_prod _ _
  rw [pkR_b_psi_prod, map_mul, map_mul, ec, pkR_b_psi_rename, pkR_b_psi_rename, pkR_om_psiP,
      pkR_om_psiP] at k2
  have k3 := congrArg (MvPolynomial.eval X) k2
  simp only [map_mul, map_prod, MvPolynomial.eval_rename, MvPolynomial.eval_X, sdiff_empty] at k3
  have hg : ∀ d, d ∈ pkSpGlue n (2 * i + 1) (2 * d₁ + 2 * j + 2) ∅ ∅ → d =
      (2 * i + 1, 2 * d₁ + 2 * j + 2) := by
    intro d hd
    have hd' : d ∈ insert ((2 * i + 1, 2 * d₁ + 2 * j + 2) : ℕ × ℕ)
        ((∅ : Finset (ℕ × ℕ)).image (relab n (2 * i + 1)) ∪
          (∅ : Finset (ℕ × ℕ)).image (relab n (2 * d₁ + 2 * j + 2))) := hd
    rw [image_empty, image_empty, union_empty, mem_insert] at hd'
    rcases hd' with h | h
    · exact h
    · simp at h
  have sL : (oddDiagonals n).filter (fun Q => Q ∉ I.image (pkRMchord d₁)) =
      (oddDiagonals n \ pkSpGlue n (2 * i + 1)
          (2 * d₁ + 2 * j + 2) ∅ ∅) \ I.image (pkRMchord d₁) := by
    ext d
    rw [mem_filter, mem_sdiff, mem_sdiff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, fun h => h2 ?_⟩, h2⟩
      rw [hg d h]
      exact hqK
    · rintro ⟨⟨h1, -⟩, h2⟩
      exact ⟨h1, h2⟩
  have sA : (oddDiagonals (2 * d₁ + 2 * j + 2 - (2 * i + 1) + 1)).filter
      (fun Q => Q ∉ (pkROmIA d₁ i j I).image (pkRMchord (d₁ - i))) =
      (oddDiagonals (2 * d₁ + 2 * j + 2 - (2 * i + 1) + 1)).filter
        (fun d => ¬ relab n (2 * i + 1) d ∈ I.image (pkRMchord d₁)) := by
    ext d
    rw [mem_filter, mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h => h2 ((pkR_om_memA hI hi hj (mem_filter.1 h1).1).1 h)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h => h2 ((pkR_om_memA hI hi hj (mem_filter.1 h1).1).2 h)⟩
  have sB := pkR_om_rotk (m := n - (2 * d₁ + 2 * j + 2) + (2 * i + 1) + 1) (by omega) (by omega)
    (n - (2 * d₁ + 2 * j + 2) + 1)
        (fun d => ¬ relab n (2 * d₁ + 2 * j + 2) d ∈ I.image (pkRMchord d₁))
    (fun d => (X ∘ relab n (2 * d₁ + 2 * j + 2)) d)
  have sB2 : (oddDiagonals (n - (2 * d₁ + 2 * j + 2) + (2 * i + 1) + 1)).filter
      (fun d => ¬ relab n (2 * d₁ + 2 * j + 2)
        ((rot (n - (2 * d₁ + 2 * j + 2) + (2 * i + 1) + 1))^[n - (2 * d₁ + 2 * j + 2) + 1] d) ∈
          I.image (pkRMchord d₁)) =
      (oddDiagonals (n - (2 * d₁ + 2 * j + 2) + (2 * i + 1) + 1)).filter
        (fun Q => Q ∉ (pkROmIB n d₁ i j I).image (pkRMchord i)) := by
    ext d
    rw [mem_filter, mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h => h2 ((pkR_om_memB hI hi hj hb (mem_filter.1 h1).1).2 h)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h => h2 ((pkR_om_memB hI hi hj hb (mem_filter.1 h1).1).1 h)⟩
  rw [sB2] at sB
  rw [sL, k3, sA, sB]
  try rfl

/-- **The Ω formula, by strong induction on `n`**, with two vanishing statements for the numerator
that avoids one odd chord `(p, q)`, on the loci `pkRZ5c` (`C8`), as hypotheses: for every even
`n ≥ 4`, every `d₁` with `2d₁ + 2 ≤ n` and every set `I` of standard members, there are `c ≠ 0` and
`F` with `NP_n = x^{|I|} · (c · x · D′ + x² · F)` on `Λ^I`, where `D′ = ∏ X_Q` over the odd chords
`Q ∉ chords(I)`. -/
theorem pkR_omega_ind
    (hR5two : ∀ {n : ℕ}, n % 2 = 0 → 4 ≤ n → ∀ {p q lo hi : ℕ}, (p, q) ∈ oddDiagonals n → p ≤
        lo → lo ≤ hi →
      hi < q → lo % 2 = p % 2 → ∀ X ∈ {X : ℕ × ℕ → ℚ | pkRZ5c n (p % 2) (Icc lo hi) {(p, q)} X},
        MvPolynomial.eval X (pkRBNP ℚ n {(p, q)}) = 0)
    (hR5one : ∀ {n : ℕ}, n % 2 = 0 → 4 ≤ n → ∀ {p q lo hi : ℕ}, (p, q) ∈ oddDiagonals n → lo ≤ p →
      q ≤ hi + 1 → ∀ {r₀ : ℕ}, r₀ ∈ (Icc 1 n).filter (fun c => c < lo ∨ hi < c) → r₀ % 2 = q % 2 →
        ∀ X ∈ {X : ℕ × ℕ → ℚ | pkRZ5c n (q % 2) ((Icc 1 n).filter (fun c => c < lo ∨ hi < c))
            {(p, q)} X},
          MvPolynomial.eval X (pkRBNP ℚ n {(p, q)}) = 0) (n : ℕ) :
    n % 2 = 0 → 4 ≤ n → ∀ d₁ : ℕ, 2 * d₁ + 2 ≤ n → ∀ I : Finset (ℕ × ℕ),
        (∀ Q ∈ I, pkRIsMem n d₁ Q) →
    ∃ (c : ℚ) (F : MvPolynomial (ℕ × ℕ) ℚ), c ≠ 0 ∧ ∀ X : ℕ × ℕ → ℚ, pkRLam n d₁ I X →
      MvPolynomial.eval X (NP ℚ n) = mesh n X 1 (n - 1) ^ I.card *
        (c * mesh n X 1 (n - 1) *
            Finset.prod ((oddDiagonals n).filter (fun Q => Q ∉ I.image (pkRMchord d₁)))
                (fun Q => X Q) +
          mesh n X 1 (n - 1) ^ 2 * MvPolynomial.eval X F) := by
  refine Nat.strong_induction_on n ?_
  intro n ih hE hn d₁ hd I hI
  rcases I.eq_empty_or_nonempty with hI0 | ⟨⟨i, j⟩, hq⟩
  · subst hI0
    obtain ⟨c, F, hc, hF⟩ := pkR_omega0 hR5two hR5one hE hn d₁ hd
    refine ⟨c, F, hc, fun X hX => ?_⟩
    have e : (oddDiagonals n).filter (fun Q => Q ∉ (∅ : Finset (ℕ × ℕ)).image (pkRMchord d₁)) =
        oddDiagonals n :=
      filter_true_of_mem (fun Q _ => by simp)
    rw [hF X hX, e, ← pkR_eval_oddDen, card_empty, pow_zero]
    ring
  · obtain ⟨hi, hj, hb, ha⟩ : i ≤ d₁ ∧ 2 * d₁ + 2 * j + 2 ≤ n ∧ ¬ (i = d₁ ∧ j = 0) ∧
        ¬ (i = 0 ∧ 2 * d₁ + 2 * j + 2 = n) := hI _ hq
    obtain ⟨cA, FA, hcA, hA⟩ := ih (2 * d₁ + 2 * j + 2 - (2 * i + 1) + 1) (by omega)
        (by omega) (by omega)
      (d₁ - i) (by omega) (pkROmIA d₁ i j I) (pkR_om_isMemA hI)
    obtain ⟨cB, FB, hcB, hB⟩ := ih (n - (2 * d₁ + 2 * j + 2) + (2 * i + 1) + 1) (by omega)
        (by omega) (by omega)
      i (by omega) (pkROmIB n d₁ i j I) (pkR_om_isMemB hI)
    obtain ⟨G, hG⟩ := pkR_notq_lam hE hn hI hq hR5two hR5one
    obtain ⟨DA, hDA⟩ : ∃ P : MvPolynomial (ℕ × ℕ) ℚ, ∀ X : ℕ × ℕ → ℚ, MvPolynomial.eval X P =
        Finset.prod ((oddDiagonals (2 * d₁ + 2 * j + 2 - (2 * i + 1) + 1)).filter
          (fun Q => Q ∉ (pkROmIA d₁ i j I).image (pkRMchord (d₁ - i))))
              (fun Q => (X ∘ relab n (2 * i + 1)) Q) :=
      ⟨MvPolynomial.rename (relab n (2 * i + 1))
          (Finset.prod ((oddDiagonals (2 * d₁ + 2 * j + 2 - (2 * i + 1) + 1)).filter
          (fun Q => Q ∉ (pkROmIA d₁ i j I).image (pkRMchord (d₁ - i))))
              (fun Q => MvPolynomial.X Q)),
        fun X => by rw [MvPolynomial.eval_rename, map_prod]; simp only [MvPolynomial.eval_X]⟩
    obtain ⟨DB, hDB⟩ : ∃ P : MvPolynomial (ℕ × ℕ) ℚ, ∀ X : ℕ × ℕ → ℚ, MvPolynomial.eval X P =
        Finset.prod ((oddDiagonals (n - (2 * d₁ + 2 * j + 2) + (2 * i + 1) + 1)).filter
          (fun Q => Q ∉ (pkROmIB n d₁ i j I).image (pkRMchord i)))
        (fun Q => (X ∘ (relab n (2 * d₁ + 2 * j + 2) ∘
          (rot (n - (2 * d₁ + 2 * j + 2) + (2 * i + 1) + 1))^[n - (2 * d₁ + 2 * j + 2) + 1])) Q) :=
      ⟨MvPolynomial.rename (relab n (2 * d₁ + 2 * j + 2) ∘
          (rot (n - (2 * d₁ + 2 * j + 2) + (2 * i + 1) + 1))^[n - (2 * d₁ + 2 * j + 2) + 1])
        (Finset.prod ((oddDiagonals (n - (2 * d₁ + 2 * j + 2) + (2 * i + 1) + 1)).filter
          (fun Q => Q ∉ (pkROmIB n d₁ i j I).image (pkRMchord i))) (fun Q => MvPolynomial.X Q)),
        fun X => by rw [MvPolynomial.eval_rename, map_prod]; simp only [MvPolynomial.eval_X]⟩
    refine ⟨cA * cB, G + MvPolynomial.C cA * DA *
        MvPolynomial.rename (relab n (2 * d₁ + 2 * j + 2) ∘
          (rot (n - (2 * d₁ + 2 * j + 2) + (2 * i + 1) + 1))^[n - (2 * d₁ + 2 * j + 2) + 1]) FB *
          pkRBCross ℚ n (I.image (pkRMchord d₁)) (2 * i + 1, 2 * d₁ + 2 * j + 2) +
        MvPolynomial.C cB * DB * MvPolynomial.rename (relab n (2 * i + 1)) FA *
          pkRBCross ℚ n (I.image (pkRMchord d₁)) (2 * i + 1, 2 * d₁ + 2 * j + 2) +
        pkRMeshP n 1 (n - 1) * MvPolynomial.rename (relab n (2 * i + 1)) FA *
          MvPolynomial.rename (relab n (2 * d₁ + 2 * j + 2) ∘
            (rot (n - (2 * d₁ + 2 * j + 2) + (2 * i + 1) + 1))^[n - (2 * d₁ + 2 * j + 2) + 1]) FB *
          pkRBCross ℚ n (I.image (pkRMchord d₁)) (2 * i + 1, 2 * d₁ + 2 * j + 2),
      mul_ne_zero hcA hcB, fun X hX => ?_⟩
    have hsp := pkR_omega_split hE hn hi hj hb ha hq hX
    obtain ⟨hlA, hxA⟩ := pkR_childA hE hn hi hj hb ha hq hX
    obtain ⟨hlB, hxB⟩ := pkR_childB hE hn hi hj hb ha hq hX
    have eA := hA _ (pkR_om_lamSub (pkR_om_subA d₁ i j I) hlA)
    have eB := hB _ (pkR_om_lamSub (pkR_om_subB n d₁ i j I) hlB)
    rw [hxA] at eA
    rw [hxB] at eB
    have eG : MvPolynomial.eval X (pkRBNP ℚ n {(2 * i + 1, 2 * d₁ + 2 * j + 2)}) =
        mesh n X 1 (n - 1) ^ (I.card + 1) * MvPolynomial.eval X G := hG X hX
    have eC := pkR_om_cross (i := i) (j := j) hE hn hI hX
    have eP := pkR_om_prod hE hi hj hb ha hI hq X
    have eN := pkR_om_count (n := n) hI hq
    rw [hsp, eG, eA, eB, eC, eP]
    simp only [map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_rename, hDA, hDB,
        pkR_meshP_eval]
    rw [eN]
    ring

-- registry: C-27FF
/-- **The Ω formula**: for even `n ≥ 4`, `d₁` with `2d₁ + 2 ≤ n` and every set `I` of standard
members (closedness is not needed here; it enters only through `pkR_GI` (`C6`) for `D′ ≢ 0` on
`Λ^I₀`), there are `c ≠ 0` and `F` with `NP_n = x^{|I|} · (c · x · D′ + x² · F)` on `Λ^I`, where
`D′ = ∏ X_Q` over the odd chords `Q ∉ chords(I)`. -/
theorem pkR_omega {n : ℕ} (hE : n % 2 = 0) (hn : 4 ≤ n) (d₁ : ℕ) (hd : 2 * d₁ + 2 ≤ n)
    (I : Finset (ℕ × ℕ)) (hI : ∀ Q ∈ I, pkRIsMem n d₁ Q) :
    ∃ (c : ℚ) (F : MvPolynomial (ℕ × ℕ) ℚ), c ≠ 0 ∧ ∀ X : ℕ × ℕ → ℚ, pkRLam n d₁ I X →
      MvPolynomial.eval X (NP ℚ n) = mesh n X 1 (n - 1) ^ I.card *
        (c * mesh n X 1 (n - 1) *
            Finset.prod ((oddDiagonals n).filter (fun Q => Q ∉ I.image (pkRMchord d₁)))
                (fun Q => X Q) +
          mesh n X 1 (n - 1) ^ 2 * MvPolynomial.eval X F) :=
  pkR_omega_ind @pkR_b_R5one2 @pkR_b_R5one1 n hE hn d₁ hd I hI


/-! ### Reduction of the residue input

`ResChildInput` (`C4`) follows from two statements taken as hypotheses (`pkR_d_reduce`): the residue
at a pole chord `t` in numerator form (`pkRDResNum`) and child surjectivity (`pkRDChild1`). The
section also proves the linear-algebra lemma `pkR_d_g6` and the count of the powers of `x`
(`pkR_d_count`). -/

/-- `L_S` is a linear subspace (mesh variables are linear forms). -/
theorem pkR_d_locus_sub (N : ℕ) (S : Finset (ℕ × ℕ)) : pkRSub {X : ℕ × ℕ → ℚ | OnLocus N S X} := by
  refine (pkR_Sub_iff _).2 ⟨?_, ?_⟩
  · change OnLocus N S (fun _ => (0 : ℚ))
    intro t _
    rw [← pkR_meshP_eval]
    exact pkR_lin_zero (pkR_meshP_lin N t.1 t.2)
  · intro x hx y hy a b
    change OnLocus N S (fun i => a * x i + b * y i)
    intro t ht
    have hx' : OnLocus N S x := hx
    have hy' : OnLocus N S y := hy
    rw [← pkR_meshP_eval, pkR_meshP_lin N t.1 t.2 x y a b, pkR_meshP_eval, pkR_meshP_eval,
        hx' t ht, hy' t ht]
    ring

/-- `H = L_S ∩ {X_t = 0}` is a linear subspace. -/
theorem pkR_d_H_sub (N : ℕ) (S : Finset (ℕ × ℕ)) (t : ℕ × ℕ) :
    pkRSub {X : ℕ × ℕ → ℚ | X ∈ {X : ℕ × ℕ → ℚ | OnLocus N S X} ∧
      MvPolynomial.eval X (MvPolynomial.X t : MvPolynomial (ℕ × ℕ) ℚ) = 0} :=
  pkR_sub_inter (pkR_d_locus_sub N S) (pkR_lin_X t)

/-- **A linear form vanishing on `V ∩ {x = 0}` is a constant multiple of `x` on `V`**: for a linear
subspace `V` and linear forms `ℓ`, `x` with `x` non-zero at `w ∈ V`; the constant is `ℓ(w)/x(w)`. -/
theorem pkR_d_g6 {σ : Type*} {V : Set (σ → ℚ)} (hV : pkRSub V) {ℓ x : MvPolynomial σ ℚ}
    (hℓ : pkRLin ℓ) (hx : pkRLin x) {w : σ → ℚ} (hw : w ∈ V) (hxw : MvPolynomial.eval w x ≠ 0)
    (h : ∀ v ∈ V, MvPolynomial.eval v x = 0 → MvPolynomial.eval v ℓ = 0) :
    ∀ v ∈ V, MvPolynomial.eval v ℓ =
        (MvPolynomial.eval w ℓ / MvPolynomial.eval w x) * MvPolynomial.eval v x := by
  intro v hv
  have hm := hV.2 v hv w hw 1 (-(MvPolynomial.eval v x / MvPolynomial.eval w x))
  have h0 : MvPolynomial.eval (fun i => 1 * v i +
      -(MvPolynomial.eval v x / MvPolynomial.eval w x) * w i) x = 0 := by
    rw [hx v w 1, neg_mul, div_mul_cancel₀ _ hxw]
    ring
  have h1 := h _ hm h0
  rw [hℓ v w 1] at h1
  have e : MvPolynomial.eval v ℓ =
      MvPolynomial.eval v x / MvPolynomial.eval w x * MvPolynomial.eval w ℓ := by linarith
  rw [e]
  ring

/-- **`D_rest ≢ 0` on `H`**: for a non-degenerate `S` and a diagonal `t`, a diagonal `Q` whose chord
is not a non-zero multiple of `X_t` on `L_S` is non-zero somewhere on `H = L_S ∩ {X_t = 0}`. -/
theorem pkR_d_offH {N : ℕ} {S : Finset (ℕ × ℕ)} (hnd : Nondeg N S) {t Q : ℕ × ℕ}
    (ht : t ∈ diagonals N) (hQ : Q ∈ diagonals N)
    (hnp : ¬ ∃ c : ℚ, c ≠ 0 ∧ ∀ X : ℕ × ℕ → ℚ, OnLocus N S X → X Q = c * X t) :
    ∃ X : ℕ × ℕ → ℚ, OnLocus N S X ∧ X t = 0 ∧ X Q ≠ 0 := by
  by_contra hno
  have hc : ∀ X : ℕ × ℕ → ℚ, OnLocus N S X → X t = 0 → X Q = 0 := fun X hX hXt => by
    by_contra hne
    exact hno ⟨X, hX, hXt, hne⟩
  obtain ⟨w, hw, hwt⟩ := hnd t ht
  have hg := pkR_d_g6 (pkR_d_locus_sub N S) (pkR_lin_X Q) (pkR_lin_X t) (w := w) hw
    (by rw [MvPolynomial.eval_X]; exact hwt)
    (fun v hv hv0 => by
      rw [MvPolynomial.eval_X] at hv0 ⊢
      exact hc v hv hv0)
  by_cases hc0 : w Q / w t = 0
  · obtain ⟨u, hu, huQ⟩ := hnd Q hQ
    have e := hg u hu
    rw [MvPolynomial.eval_X, MvPolynomial.eval_X, MvPolynomial.eval_X, MvPolynomial.eval_X, hc0,
        zero_mul] at e
    exact huQ e
  · refine hnp ⟨w Q / w t, hc0, fun X hX => ?_⟩
    have e := hg X hX
    rw [MvPolynomial.eval_X, MvPolynomial.eval_X, MvPolynomial.eval_X, MvPolynomial.eval_X] at e
    exact e

/-- One inclusion of (H3b): for even `N ≥ 6` and odd chords `P`, `P′`, equal hit sets give nested
`innerEE` / `innerOO` (`innerEE N S P ⊆ innerEE N S P′`, the same for `innerOO`), by the cut rule
`pkCh_hit_iff` (`C2`). -/
theorem pkR_d_inner_sub {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} {P P' : ℕ × ℕ}
    (hP : P ∈ oddDiagonals N) (hP' : P' ∈ oddDiagonals N) (hh : hitSet N S P = hitSet N S P') :
    innerEE N S P ⊆ innerEE N S P' ∧ innerOO N S P ⊆ innerOO N S P' := by
  constructor
  · rintro ⟨u, v⟩ huv
    obtain ⟨hm, hs⟩ := mem_filter.1 huv
    obtain ⟨hmm, hp⟩ := mem_filter.1 hm
    dsimp only at hs hp
    refine mem_filter.2 ⟨hm, ?_⟩
    dsimp only
    have e1 := (pkCh_hit_iff hN hE hP hmm (by omega)).1 hp.1
    have e2 := (pkCh_hit_iff hN hE hP' hmm (by omega)).1 hp.1
    rw [← hh] at e2
    by_contra hc
    exact (e1.1 (e2.2 hc)) hs
  · rintro ⟨u, v⟩ huv
    obtain ⟨hm, hs⟩ := mem_filter.1 huv
    obtain ⟨hmm, hp⟩ := mem_filter.1 hm
    dsimp only at hs hp
    refine mem_filter.2 ⟨hm, ?_⟩
    dsimp only
    have e1 := (pkCh_hit_iff hN hE hP hmm (by omega)).2 hp.1
    have e2 := (pkCh_hit_iff hN hE hP' hmm (by omega)).2 hp.1
    rw [← hh] at e2
    by_contra hc
    exact (e1.1 (e2.2 hc)) hs

/-- **(H3b)** for two members of one class (`N ≥ 6` even): equal `innerEE` and `innerOO` (the
hypothesis of `pkR_b_omegaHyp`, `C7`). -/
theorem pkR_d_H3b {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} {t Q Q' : ℕ × ℕ}
    (hQ : Q ∈ hitClass N S t) (hQ' : Q' ∈ hitClass N S t) :
    innerEE N S Q = innerEE N S Q' ∧ innerOO N S Q = innerOO N S Q' := by
  have hQo := (pkR_b_H3a hQ).1
  have hQo' := (pkR_b_H3a hQ').1
  have hh : hitSet N S Q = hitSet N S Q' := ((mem_filter.1 hQ).2).trans ((mem_filter.1 hQ').2).symm
  have a1 := pkR_d_inner_sub hN hE hQo hQo' hh
  have a2 := pkR_d_inner_sub hN hE hQo' hQo hh.symm
  exact ⟨Subset.antisymm a1.1 a2.1, Subset.antisymm a1.2 a2.2⟩

/-- **The residue in numerator form**: on `L_S`, `NP_N = X_t^k · G` for a polynomial `G`, and on
`H = L_S ∩ {X_t = 0}`, `G = ε · NP_{B(t)} · NP_{A(b)} · ∏_{Q ∈ J} X_Q` with `ε ≠ 0` and `J` a set of
odd chords outside the class of `t` (`D_rest`). The children are read in the `relab` labelling
(`pkR_b_R17`, `C7`; `pkRBChildB'`, `C8`). The powers of `x` come explicitly from the expansions
and the Ω formula (`pkR_d_count`), so no division step is needed; `G` must be a polynomial for the
last step (`pkR_d_final`): the Ω and child factors are polynomials read at `subX`/`relab` points,
i.e. `aeval` compositions. -/
def pkRDResNum (N : ℕ) (S : Finset (ℕ × ℕ)) (t b : ℕ × ℕ) : Prop :=
  ∃ (G : MvPolynomial (ℕ × ℕ) ℚ) (k : ℕ) (ε : ℚ) (J : Finset (ℕ × ℕ)), ε ≠ 0 ∧
    J ⊆ oddDiagonals N \ hitClass N S t ∧
    (∀ X : ℕ × ℕ → ℚ, OnLocus N S X → MvPolynomial.eval X (NP ℚ N) = X t ^ k *
        MvPolynomial.eval X G) ∧
    ∀ X : ℕ × ℕ → ℚ, OnLocus N S X → X t = 0 → MvPolynomial.eval X G =
      ε * MvPolynomial.eval (X ∘ relab N (tailStart t)) (NP ℚ (tailLen N t + 1)) *
        MvPolynomial.eval (X ∘ relab N (headStart b)) (NP ℚ (headLen N b + 1)) * ∏ Q ∈ J, X Q

/-- **Child surjectivity** onto a child locus `L_{S_L}` (an `m`-gon read through `relab N s`) from
`H = L_S ∩ {X_t = 0}`: every point of `L_{S_L}` is the restriction (through `relab N s`) of a point
of `H`. -/
def pkRDChild1 (N : ℕ) (S : Finset (ℕ × ℕ)) (t : ℕ × ℕ) (s m : ℕ) (SL : Finset (ℕ × ℕ)) : Prop :=
  ∀ y : ℕ × ℕ → ℚ, OnLocus m SL y → ∃ X : ℕ × ℕ → ℚ, OnLocus N S X ∧ X t = 0 ∧
    ∀ d ∈ diagonals m, X (relab N s d) = y d

/-- A child `NonzeroOn` (`C0`) and child surjectivity (`pkRDChild1`) give a point of `H` where the
child numerator is non-zero (`m ≥ 2`). -/
theorem pkR_d_childNZ {N m s : ℕ} {S SL : Finset (ℕ × ℕ)} {t : ℕ × ℕ} (hm : 2 ≤ m)
    (hC : pkRDChild1 N S t s m SL) (hnz : NonzeroOn m SL) :
    ∃ X : ℕ × ℕ → ℚ, OnLocus N S X ∧ X t = 0 ∧ MvPolynomial.eval (X ∘ relab N s) (NP ℚ m) ≠ 0 := by
  obtain ⟨y, hy, hpole, hne⟩ := hnz
  obtain ⟨X, hX, hXt, hXy⟩ := hC y hy
  refine ⟨X, hX, hXt, ?_⟩
  rw [pkR_b_NP_local (n := m) (Y := X ∘ relab N s) (Y' := y) (fun d hd => hXy d hd)]
  rw [show NP ℚ m = AP ℚ m (m - 2) from rfl, AP_eval m (m - 2) y hpole]
  have e : shiftCoeff m ((m - 2 : ℕ) : ℤ) y = NLSM m y := by
    rw [show ((m - 2 : ℕ) : ℤ) = (m : ℤ) - 2 by omega]
    rfl
  rw [e]
  exact mul_ne_zero hne (prod_ne_zero_iff.2 hpole)

/-- Avoidance on `H`: if the polynomials `PA`, `PB` (the two child numerators, where it is used) and
every chord of `J` are each non-zero somewhere on `H`, they are all non-zero at one point of `H`. -/
theorem pkR_d_Havoid {N : ℕ} {S : Finset (ℕ × ℕ)} {t : ℕ × ℕ} (PA PB : MvPolynomial (ℕ × ℕ) ℚ)
    (J : Finset (ℕ × ℕ))
    (hA : ∃ X : ℕ × ℕ → ℚ, OnLocus N S X ∧ X t = 0 ∧ MvPolynomial.eval X PA ≠ 0)
    (hB : ∃ X : ℕ × ℕ → ℚ, OnLocus N S X ∧ X t = 0 ∧ MvPolynomial.eval X PB ≠ 0)
    (hJ : ∀ Q ∈ J, ∃ X : ℕ × ℕ → ℚ, OnLocus N S X ∧ X t = 0 ∧ X Q ≠ 0) :
    ∃ X : ℕ × ℕ → ℚ, OnLocus N S X ∧ X t = 0 ∧ MvPolynomial.eval X PA ≠ 0 ∧
        MvPolynomial.eval X PB ≠ 0 ∧
      ∀ Q ∈ J, X Q ≠ 0 := by
  classical
  have hmem : ∀ X : ℕ × ℕ → ℚ, OnLocus N S X → X t = 0 →
      X ∈ {X : ℕ × ℕ → ℚ | X ∈ {X : ℕ × ℕ → ℚ | OnLocus N S X} ∧
      MvPolynomial.eval X (MvPolynomial.X t : MvPolynomial (ℕ × ℕ) ℚ) = 0} := fun X hX hXt =>
    ⟨hX, by rw [MvPolynomial.eval_X]; exact hXt⟩
  obtain ⟨X, hX, hall⟩ := pkR_avoid (pkR_d_H_sub N S t)
    (fun o : Option (Option (ℕ × ℕ)) =>
        o.elim PA (fun o' => o'.elim PB (fun Q => MvPolynomial.X Q)))
    (insert none (insert (some none) (J.image (fun Q => some (some Q))))) (by
      intro o ho
      rcases mem_insert.1 ho with h | h
      · subst h
        obtain ⟨Y, hY, hYt, hYA⟩ := hA
        exact ⟨Y, hmem Y hY hYt, hYA⟩
      · rcases mem_insert.1 h with h2 | h2
        · subst h2
          obtain ⟨Y, hY, hYt, hYB⟩ := hB
          exact ⟨Y, hmem Y hY hYt, hYB⟩
        · obtain ⟨Q, hQ, rfl⟩ := mem_image.1 h2
          obtain ⟨Y, hY, hYt, hYQ⟩ := hJ Q hQ
          refine ⟨Y, hmem Y hY hYt, ?_⟩
          change MvPolynomial.eval Y (MvPolynomial.X Q) ≠ 0
          rw [MvPolynomial.eval_X]
          exact hYQ)
  have hXt : X t = 0 := by
    have e := hX.2
    rw [MvPolynomial.eval_X] at e
    exact e
  refine ⟨X, hX.1, hXt, hall none (mem_insert_self _ _),
    hall (some none) (mem_insert_of_mem (mem_insert_self _ _)), fun Q hQ => ?_⟩
  have e := hall (some (some Q)) (mem_insert_of_mem (mem_insert_of_mem (mem_image_of_mem _ hQ)))
  have e2 : MvPolynomial.eval X (MvPolynomial.X Q : MvPolynomial (ℕ × ℕ) ℚ) ≠ 0 := e
  rw [MvPolynomial.eval_X] at e2
  exact e2

/-- For `N ≥ 2`, a non-degenerate `S` and an odd chord `t`: `NP_N = X_t^k · G` on `L_S` with `G ≢ 0`
on `L_S` gives `NonzeroOn N S` (avoidance with every odd chord, then `AP_eval` of `PionNLSM`). -/
theorem pkR_d_final {N : ℕ} (hN : 2 ≤ N) {S : Finset (ℕ × ℕ)} (hnd : Nondeg N S) {t : ℕ × ℕ}
    (ht : t ∈ oddDiagonals N) {G : MvPolynomial (ℕ × ℕ) ℚ} {k : ℕ}
    (hNP : ∀ X : ℕ × ℕ → ℚ, OnLocus N S X → MvPolynomial.eval X (NP ℚ N) = X t ^ k *
        MvPolynomial.eval X G)
    (hG : ∃ X : ℕ × ℕ → ℚ, OnLocus N S X ∧ MvPolynomial.eval X G ≠ 0) : NonzeroOn N S := by
  classical
  obtain ⟨X, hX, hall⟩ := pkR_avoid (pkR_d_locus_sub N S)
    (fun o : Option (ℕ × ℕ) => o.elim G (fun d => MvPolynomial.X d))
    (insert none ((oddDiagonals N).image some)) (by
      intro o ho
      rcases mem_insert.1 ho with h | h
      · subst h
        exact hG
      · obtain ⟨d, hd, rfl⟩ := mem_image.1 h
        obtain ⟨Y, hY, hYd⟩ := hnd d (mem_filter.1 hd).1
        refine ⟨Y, hY, ?_⟩
        change MvPolynomial.eval Y (MvPolynomial.X d) ≠ 0
        rw [MvPolynomial.eval_X]
        exact hYd)
  have hGX : MvPolynomial.eval X G ≠ 0 := hall none (mem_insert_self _ _)
  have hpole : ∀ d ∈ oddDiagonals N, X d ≠ 0 := fun d hd => by
    have e := hall (some d) (mem_insert_of_mem (mem_image_of_mem _ hd))
    have e2 : MvPolynomial.eval X (MvPolynomial.X d : MvPolynomial (ℕ × ℕ) ℚ) ≠ 0 := e
    rw [MvPolynomial.eval_X] at e2
    exact e2
  refine ⟨X, hX, hpole, fun h0 => ?_⟩
  have hNPX := hNP X hX
  rw [show NP ℚ N = AP ℚ N (N - 2) from rfl, AP_eval N (N - 2) X hpole] at hNPX
  have e : shiftCoeff N ((N - 2 : ℕ) : ℤ) X = NLSM N X := by
    rw [show ((N - 2 : ℕ) : ℤ) = (N : ℤ) - 2 by omega]
    rfl
  rw [e, h0, zero_mul] at hNPX
  exact mul_ne_zero (pow_ne_zero k (hpole t ht)) hGX hNPX.symm

/-- **Reduction of `resChild_input`** (`C10`): for even `N ≥ 6`, `ResChildInput N` (`C4`) follows
from the residue in numerator form (`pkRDResNum`) at every pole chord `t` of a set `S` with
`InFpi N S` and the member `b` of its class whose head lies in every head of the class (given the
class facts listed in `hRes`), and from child surjectivity (`pkRDChild1`) for the B-child of `t`
(in the `relab N (tailStart t)` labelling, `pkRBChildB'`, `C8`) and the A-child of `b`
(`childSetA`, `C0`). -/
theorem pkR_d_reduce {N : ℕ} (hN : 6 ≤ N) (hE : Even N)
    (hRes : ∀ (S : Finset (ℕ × ℕ)) (t b : ℕ × ℕ), InFpi N S → t ∈ poleChords N S →
        b ∈ hitClass N S t →
      (∀ Q ∈ hitClass N S t, oddSide N b ⊆ oddSide N Q ∧ oddSide N Q ⊆ oddSide N t) →
      (∀ Q ∈ oddDiagonals N,
        (∃ c : ℚ, c ≠ 0 ∧ ∀ X : ℕ × ℕ → ℚ, OnLocus N S X → X Q = c * X t) ↔ Q ∈ hitClass N S t) →
      (∀ Q ∈ hitClass N S t, ∀ X : ℕ × ℕ → ℚ, OnLocus N S X → X Q = X t) → pkRDResNum N S t b)
    (hChB : ∀ (S : Finset (ℕ × ℕ)) (t : ℕ × ℕ), InFpi N S → t ∈ poleChords N S →
      pkRDChild1 N S t (tailStart t) (tailLen N t + 1) (pkRBChildB' N S t))
    (hChA : ∀ (S : Finset (ℕ × ℕ)) (t b : ℕ × ℕ), InFpi N S → t ∈ poleChords N S →
        b ∈ hitClass N S t →
      pkRDChild1 N S t (headStart b) (headLen N b + 1) (childSetA N S b)) :
    ResChildInput N := by
  intro S t b hF ht hb hint hH2 hH2' hnzB hnzA
  obtain ⟨G, k, ε, J, hε, hJ, hNP, hGH⟩ := hRes S t b hF ht hb hint hH2 hH2'
  have hEN : N % 2 = 0 := Nat.even_iff.1 hE
  have htO : t ∈ oddDiagonals N := (mem_filter.1 (mem_filter.1 ht).1).1
  have hbO : b ∈ oddDiagonals N := (pkR_b_H3a hb).1
  obtain ⟨-, -, htl1, htl3, -, -, -, -, -, -⟩ := pkCh_sides hEN htO
  obtain ⟨-, -, -, -, -, -, -, hbl1, hbl3, -⟩ := pkCh_sides hEN hbO
  have hnzB' := pkR_b_nonzero_B' (by omega) (by omega) hnzB
  obtain ⟨XB, hXB, hXBt, hB⟩ := pkR_d_childNZ (by omega) (hChB S t hF ht) hnzB'
  obtain ⟨XA, hXA, hXAt, hA⟩ := pkR_d_childNZ (by omega) (hChA S t b hF ht hb) hnzA
  have hJw : ∀ Q ∈ J, ∃ X : ℕ × ℕ → ℚ, OnLocus N S X ∧ X t = 0 ∧ X Q ≠ 0 := by
    intro Q hQ
    obtain ⟨hQo, hQK⟩ := mem_sdiff.1 (hJ hQ)
    exact pkR_d_offH hF.2.1 (mem_filter.1 htO).1 (mem_filter.1 hQo).1 (fun hc =>
        hQK ((hH2 Q hQo).1 hc))
  obtain ⟨X, hX, hXt, hXB', hXA', hXJ⟩ := pkR_d_Havoid (t := t)
    (MvPolynomial.rename (relab N (tailStart t)) (NP ℚ (tailLen N t + 1)))
    (MvPolynomial.rename (relab N (headStart b)) (NP ℚ (headLen N b + 1))) J
    ⟨XB, hXB, hXBt, by rw [MvPolynomial.eval_rename]; exact hB⟩
    ⟨XA, hXA, hXAt, by rw [MvPolynomial.eval_rename]; exact hA⟩ hJw
  rw [MvPolynomial.eval_rename] at hXB' hXA'
  refine pkR_d_final (by omega) hF.2.1 htO hNP ⟨X, hX, ?_⟩
  rw [hGH X hX hXt]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hε hXB') hXA') (prod_ne_zero_iff.2 hXJ)

/-- **Count of the powers of `x`** (scalar form at one point of `L_S`; no division needed), for
`κ ≥ 1`. Class chain `C 0 ≻ … ≻ C (κ−1)` (top `t = C 0`), `x` = the common member value. `h1` = the
top-down expansion (`pkR_b_R2top_eval`, `C8`: `A i` = full A-child numerator of `C i`, `a i` = ¬K
B-child numerator, `M` = parent ¬K numerator); `h2` = the A-side collapse (`pkR_b_R2A_eval` at top
`C i`, chain of the `κ − 1 − i` members below, `W i j` = numerator of `Ω(C i, ·)`, `B i` = ¬K
A-child numerator of `C i`); `h3` = the Ω formula (`pkR_omega`) at the Ω point with `κ − 2 − i − j`
interior members. Then `NP = x^{κ−1} · g`. -/
theorem pkR_d_count {κ : ℕ} (hκ : 1 ≤ κ) (x M NPv : ℚ) (A a cr B : ℕ → ℚ)
    (b W cr2 c D F : ℕ → ℕ → ℚ) (h1 : NPv = ∑ i ∈ range κ, x ^ i * A i * a i * cr i + x ^ κ * M)
    (h2 : ∀ i < κ, A i = ∑ j ∈ range (κ - 1 - i), x ^ j * b i j * W i j * cr2 i j +
        x ^ (κ - 1 - i) * B i)
    (h3 : ∀ i < κ, ∀ j < κ - 1 - i, W i j = x ^ (κ - 2 - i - j) *
        (c i j * x * D i j + x ^ 2 * F i j)) :
    NPv = x ^ (κ - 1) * (∑ i ∈ range κ, a i * cr i *
      (∑ j ∈ range (κ - 1 - i), b i j * (c i j * D i j + x * F i j) * cr2 i j + B i) + x * M) := by
  rw [h1, mul_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' : i < κ := Finset.mem_range.1 hi
    rw [h2 i hi']
    have hs : x ^ i * ∑ j ∈ range (κ - 1 - i), x ^ j * b i j * W i j * cr2 i j =
        x ^ (κ - 1) * ∑ j ∈ range (κ - 1 - i), b i j * (c i j * D i j + x * F i j) * cr2 i j := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hj' : j < κ - 1 - i := Finset.mem_range.1 hj
      rw [h3 i hi' j hj', show κ - 1 = i + j + (κ - 2 - i - j) + 1 by omega, pow_add,
          pow_add, pow_add]
      ring
    have hb : x ^ i * x ^ (κ - 1 - i) = x ^ (κ - 1) := by
      rw [← pow_add]
      congr 1
      omega
    calc x ^ i * (∑ j ∈ range (κ - 1 - i), x ^ j * b i j * W i j * cr2 i j +
        x ^ (κ - 1 - i) * B i) * a i * cr i =
          (x ^ i * ∑ j ∈ range (κ - 1 - i), x ^ j * b i j * W i j * cr2 i j) * a i * cr i +
            (x ^ i * x ^ (κ - 1 - i)) * B i * a i * cr i := by ring
      _ = _ := by
          rw [hs, hb]
          ring
  · have e : x ^ κ = x ^ (κ - 1) * x := by
      rw [← pow_succ]
      congr 1
      omega
    rw [e]
    ring

/-- **Value on `H`** of the `pkR_d_count` factor (`x = 0`), for `κ ≥ 2`, under (E): `a i = 0` for
`i ≥ 1` (`C i ≠ t`), `b 0 j = 0` for `j ≥ 1` (`c j ≠ b`), `B 0 = b_t = 0` (`t ≠ b`). Only the
`(t, b)` term survives, with `ε = c 0 0` (the constant of the Ω formula for `Ω(t, b)`). -/
theorem pkR_d_countH {κ : ℕ} (hκ : 2 ≤ κ) (M : ℚ) (a cr B : ℕ → ℚ) (b cr2 c D F : ℕ → ℕ → ℚ)
    (ha : ∀ i, 1 ≤ i → i < κ → a i = 0) (hb : ∀ j, 1 ≤ j → j < κ - 1 → b 0 j = 0) (hB : B 0 = 0) :
    ∑ i ∈ range κ, a i * cr i *
      (∑ j ∈ range (κ - 1 - i), b i j * (c i j * D i j + 0 * F i j) * cr2 i j + B i) + 0 * M =
      c 0 0 * a 0 * b 0 0 * (cr 0 * D 0 0 * cr2 0 0) := by
  rw [Finset.sum_eq_single 0 (fun i hi hi0 => by
      rw [ha i (by omega) (Finset.mem_range.1 hi), zero_mul, zero_mul])
    (fun h => absurd (Finset.mem_range.2 (by omega)) h)]
  rw [Finset.sum_eq_single 0 (fun j hj hj0 => by
      rw [hb j (by omega) (by have := Finset.mem_range.1 hj; omega), zero_mul, zero_mul])
    (fun h => absurd (Finset.mem_range.2 (by omega)) h), hB]
  ring

/-- **Value on `H`**, `κ = 1` (`t = b`): `g = a_t · cr · b_t` (`B 0` is then the full A-child
numerator). -/
theorem pkR_d_countH1 (M : ℚ) (a cr B : ℕ → ℚ) (b cr2 c D F : ℕ → ℕ → ℚ) :
    ∑ i ∈ range 1, a i * cr i *
      (∑ j ∈ range (1 - 1 - i), b i j * (c i j * D i j + 0 * F i j) * cr2 i j + B i) + 0 * M =
          a 0 * cr 0 * B 0 := by
  simp


/-! ### Child surjectivity

`pkRDChild1` for both children (`pkR_ch_childB`, `pkR_ch_childA`), by a lift through a Gram matrix
(`pkR_gram`, `C6`) in the rotated leg index `pkRChChi`. -/

/-- Rotated leg index: leg `a` ↦ (its position in the arc starting at leg `s`) + 1. -/
def pkRChChi (N s a : ℕ) : ℕ := cycPos N s a + 1

theorem pkR_ch_chi_eq {N s a : ℕ} (hs : 1 ≤ s ∧ s ≤ N) (ha : 1 ≤ a ∧ a ≤ N) :
    pkRChChi N s a = if s ≤ a then a - s + 1 else a + N - s + 1 := by
  unfold pkRChChi cycPos
  split_ifs with h
  · rw [show a + N - s = (a - s) + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

theorem pkR_ch_vtx {N x : ℕ} (h1 : 1 ≤ x) (h2 : x ≤ 2 * N) :
    vtx N x = if x ≤ N then x else x - N := by
  split_ifs with h
  · exact vtx_of_mem h1 h
  · have e := vtx_add_n N (x - N)
    rw [show x - N + N = x by omega] at e
    rw [e, vtx_of_mem (by omega) (by omega)]

theorem pkR_ch_psi_chi {N s a : ℕ} (hs : 1 ≤ s ∧ s ≤ N) (ha : 1 ≤ a ∧ a ≤ N) :
    vtx N (s + pkRChChi N s a - 1) = a := by
  rw [pkR_ch_chi_eq hs ha]
  split_ifs with h
  · rw [pkR_ch_vtx (by omega) (by omega)]
    split_ifs <;> omega
  · rw [pkR_ch_vtx (by omega) (by omega)]
    split_ifs <;> omega

theorem pkR_ch_chi_psi {N s j : ℕ} (hs : 1 ≤ s ∧ s ≤ N) (hj : 1 ≤ j ∧ j ≤ N) :
    pkRChChi N s (vtx N (s + j - 1)) = j := by
  have hv := pkR_ch_vtx (N := N) (x := s + j - 1) (by omega) (by omega)
  have hb := vtx_bounds N (s + j - 1) (by omega)
  rw [pkR_ch_chi_eq hs hb]
  split_ifs at hv ⊢ <;> omega

theorem pkR_ch_chi_mem {N s a : ℕ} (hs : 1 ≤ s ∧ s ≤ N) (ha : 1 ≤ a ∧ a ≤ N) :
    1 ≤ pkRChChi N s a ∧ pkRChChi N s a ≤ N := by
  rw [pkR_ch_chi_eq hs ha]
  split_ifs <;> omega

/-- A pair of cyclically adjacent (or equal) legs is not a diagonal. -/
theorem pkR_ch_nd {N u v : ℕ}
    (h : u + 1 = v ∨ v + 1 = u ∨ (u = 1 ∧ v = N) ∨ (u = N ∧ v = 1) ∨ u = v) :
    (min u v, max u v) ∉ diagonals N := by
  rw [mem_diagonals]
  dsimp only
  rw [Nat.min_def, Nat.max_def]
  split_ifs <;> omega

theorem pkR_ch_pmem {N u v : ℕ} (hu : 1 ≤ u ∧ u ≤ N) (hv : 1 ≤ v ∧ v ≤ N)
    (h : u + 2 ≤ v ∨ v + 2 ≤ u)
    (h1 : ¬ (u = 1 ∧ v = N)) (h2 : ¬ (u = N ∧ v = 1)) : (min u v, max u v) ∈ diagonals N := by
  rw [mem_diagonals]
  dsimp only
  rw [Nat.min_def, Nat.max_def]
  split_ifs <;> omega

/-- The arc sum inside one `n`-gon: `Σ_{u ≤ c < v} c_{c,v} = X_{u,v} − X_{u,v+1}`. -/
theorem pkR_ch_inner {n : ℕ} (hn : 1 ≤ n) (Z : ℕ × ℕ → ℚ) {u v : ℕ} (huv : u ≤ v) :
    ∑ c ∈ Ico u v, mesh n Z c v = planar n Z u v - planar n Z u (v + 1) := by
  rcases Nat.eq_or_lt_of_le huv with h | h
  · subst h
    rw [Ico_self, sum_empty, pkR_planar_self, pkR_planar_succ hn]
    ring
  · obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
    have ht := mesh_telescope n Z (p := u) (q := w) (r := w + 1) (t := w + 1) (by omega) le_rfl
    rw [Icc_self] at ht
    simp only [sum_singleton] at ht
    have e : Ico u (w + 1) = Icc u w := by
      ext x
      simp only [mem_Ico, mem_Icc]
      omega
    rw [e, ht, pkR_planar_succ hn Z (w + 1), pkR_planar_self]
    ring

/-- **The arc formula as an identity** for any point (legs as integers, no range restriction;
`u ≤ v`): `X_{u,v} = −Σ_{u ≤ c < d < v} c_{c,d}`. -/
theorem pkR_ch_tri {n : ℕ} (hn : 1 ≤ n) (Z : ℕ × ℕ → ℚ) {u v : ℕ} (huv : u ≤ v) :
    planar n Z u v = -∑ d ∈ Ico u v, ∑ c ∈ Ico u d, mesh n Z c d := by
  induction v, huv using Nat.le_induction with
  | base => rw [Ico_self, sum_empty, neg_zero, pkR_planar_self]
  | succ v hv ih =>
    rw [sum_Ico_succ_top hv, neg_add, ← ih, pkR_ch_inner hn Z hv]
    ring

/-- Parent planar variables on the side `[s, s + k]` agree with the child's when the mesh variables
of the side legs do. -/
theorem pkR_ch_shift {N s k : ℕ} (hN : 1 ≤ N) (hs : 1 ≤ s) {X y : ℕ × ℕ → ℚ}
    (hm : ∀ a b, 1 ≤ a → a < b → b ≤ k → mesh N X (a + s - 1) (b + s - 1) = mesh (k + 1) y a b)
    {p r : ℕ} (hp : 1 ≤ p) (hpr : p ≤ r) (hr : r ≤ k + 1) :
    planar N X (p + s - 1) (r + s - 1) = planar (k + 1) y p r := by
  rw [pkR_ch_tri hN X (show p + s - 1 ≤ r + s - 1 by omega), pkR_ch_tri (by omega) y hpr,
    show p + s - 1 = p + (s - 1) by omega, show r + s - 1 = r + (s - 1) by omega]
  congr 1
  rw [← Finset.sum_Ico_add']
  refine sum_congr rfl (fun d hd => ?_)
  rw [← Finset.sum_Ico_add']
  refine sum_congr rfl (fun c hc => ?_)
  rw [mem_Ico] at hc hd
  rw [show c + (s - 1) = c + s - 1 by omega, show d + (s - 1) = d + s - 1 by omega]
  exact hm c d (by omega) hc.2 (by omega)

/-! The Gram matrix of the lift, in the rotated index (side = `1..k`, complement = `k+1..N`). -/

/-- The side block: `M j l` for `j, l ≤ k`, else `0`. -/
def pkRChL (k : ℕ) (M : ℕ → ℕ → ℚ) (j l : ℕ) : ℚ := if j ≤ k ∧ l ≤ k then M j l else 0

/-- The side–complement entries: `r j` at `(j, W j)` for `j ≤ k`, else `0`. -/
def pkRChE (k : ℕ) (r : ℕ → ℚ) (W : ℕ → ℕ) (j l : ℕ) : ℚ := if j ≤ k ∧ l = W j then r j else 0

/-- The path entries: `e j` at `(j, j + 1)` for `k + 1 ≤ j` and `j + 1 ≤ N`, else `0`. -/
def pkRChPe (N k : ℕ) (e : ℕ → ℚ) (j l : ℕ) :
    ℚ := if k + 1 ≤ j ∧ l = j + 1 ∧ l ≤ N then e j else 0

/-- The balancing entries: `c` at `(g1, g2)` and at `(g2, g1)`, else `0`. -/
def pkRChG (g1 g2 : ℕ) (c : ℚ) (j l : ℕ) :
    ℚ := if (j = g1 ∧ l = g2) ∨ (j = g2 ∧ l = g1) then c else 0

/-- The Gram matrix of the lift: the side block, the side–complement and path entries (each with its
transpose), and the balancing entries. -/
def pkRChD (N k : ℕ) (M : ℕ → ℕ → ℚ) (r : ℕ → ℚ) (W : ℕ → ℕ) (e : ℕ → ℚ) (g1 g2 : ℕ) (c : ℚ)
    (j l : ℕ) : ℚ :=
  pkRChL k M j l + (pkRChE k r W j l + pkRChE k r W l j) + (pkRChPe N k e j l +
      pkRChPe N k e l j) +
    pkRChG g1 g2 c j l

/-- Alternating prefix sums along the complement path. -/
def pkRChF (k : ℕ) (T : ℕ → ℚ) (q : ℕ) : ℚ := ∑ i ∈ Icc (k + 1) q, (-1) ^ i * T i

/-- The path weights `e q = (−1)^q · F q`, from the alternating prefix sums `pkRChF`. -/
def pkRChe (k : ℕ) (T : ℕ → ℚ) (q : ℕ) : ℚ := (-1) ^ q * pkRChF k T q

theorem pkR_ch_rowL {N k : ℕ} (hkN : k ≤ N) (M : ℕ → ℕ → ℚ) (j : ℕ) :
    ∑ l ∈ Icc 1 N, pkRChL k M j l = if j ≤ k then ∑ l ∈ Icc 1 k, M j l else 0 := by
  unfold pkRChL
  split_ifs with h
  · have e : (Icc 1 N).filter (fun l => j ≤ k ∧ l ≤ k) = Icc 1 k := by
      ext l
      simp only [mem_filter, mem_Icc]
      omega
    rw [← sum_filter, e]
  · exact sum_eq_zero (fun l _ => ite_eq_right (fun h' => h h'.1))

theorem pkR_ch_rowE {N k : ℕ} (r : ℕ → ℚ) (W : ℕ → ℕ) (j : ℕ) (hW : 1 ≤ W j ∧ W j ≤ N) :
    ∑ l ∈ Icc 1 N, pkRChE k r W j l = if j ≤ k then r j else 0 := by
  unfold pkRChE
  split_ifs with h
  · simp only [h, true_and]
    rw [sum_ite_eq', ite_eq_left (mem_Icc.2 hW)]
  · exact sum_eq_zero (fun l _ => ite_eq_right (fun h' => h h'.1))

theorem pkR_ch_rowpe1 {N k : ℕ} (e : ℕ → ℚ) (j : ℕ) :
    ∑ l ∈ Icc 1 N, pkRChPe N k e j l = if k + 1 ≤ j ∧ j + 1 ≤ N then e j else 0 := by
  have e1 : ∀ l ∈ Icc 1 N, pkRChPe N k e j l =
      if l = j + 1 then (if k + 1 ≤ j ∧ j + 1 ≤ N then e j else 0) else 0 := by
    intro l _
    unfold pkRChPe
    by_cases hl : l = j + 1
    · subst hl
      simp
    · rw [ite_eq_right (fun h => hl h.2.1), ite_eq_right hl]
  rw [sum_congr rfl e1, sum_ite_eq']
  by_cases h : k + 1 ≤ j ∧ j + 1 ≤ N
  · rw [ite_eq_left (mem_Icc.2 ⟨by omega, h.2⟩)]
  · rw [ite_eq_right h]
    exact ite_self 0

theorem pkR_ch_rowpe2 {N k : ℕ} (e : ℕ → ℚ) {j : ℕ} (hj : 1 ≤ j) :
    ∑ l ∈ Icc 1 N, pkRChPe N k e l j = if k + 2 ≤ j ∧ j ≤ N then e (j - 1) else 0 := by
  have e1 : ∀ l ∈ Icc 1 N, pkRChPe N k e l j =
      if l = j - 1 then (if k + 2 ≤ j ∧ j ≤ N then e (j - 1) else 0) else 0 := by
    intro l _
    unfold pkRChPe
    by_cases hl : l = j - 1
    · subst hl
      rw [ite_eq_left rfl]
      by_cases h : k + 2 ≤ j ∧ j ≤ N
      · rw [ite_eq_left ⟨by omega, by omega, h.2⟩, ite_eq_left h]
      · rw [ite_eq_right (fun h' => h ⟨by omega, h'.2.2⟩), ite_eq_right h]
    · rw [ite_eq_right (fun h => hl (by omega)), ite_eq_right hl]
  rw [sum_congr rfl e1, sum_ite_eq']
  by_cases h : k + 2 ≤ j ∧ j ≤ N
  · rw [ite_eq_left (mem_Icc.2 ⟨by omega, by omega⟩)]
  · rw [ite_eq_right h]
    exact ite_self 0

theorem pkR_ch_rowG {N g1 g2 : ℕ} (c : ℚ) (j : ℕ) (hg1 : g1 ∈ Icc 1 N) (hg2 : g2 ∈ Icc 1 N)
    (hg : g1 ≠ g2) :
    ∑ l ∈ Icc 1 N, pkRChG g1 g2 c j l =
        (if j = g1 then c else 0) + (if j = g2 then c else 0) := by
  have e1 : ∀ l ∈ Icc 1 N, pkRChG g1 g2 c j l =
      (if l = g2 then (if j = g1 then c else 0) else 0) + (if l =
          g1 then (if j = g2 then c else 0) else 0) := by
    intro l _
    unfold pkRChG
    split_ifs <;> first | (exfalso; omega) | ring
  rw [sum_congr rfl e1, sum_add_distrib, sum_ite_eq', sum_ite_eq', ite_eq_left hg2, ite_eq_left hg1]

/-- Row sums of the lift's Gram matrix: they vanish on `1..N` when the side rows (`hr`) and the
complement rows (`hpath`) balance (`k + 1 ≤ N`, `W` and `g1 ≠ g2` in the complement `k + 1..N`). -/
theorem pkR_ch_row {N k : ℕ} (hkN : k + 1 ≤ N) (M : ℕ → ℕ → ℚ) (r : ℕ → ℚ) (W : ℕ → ℕ) (e : ℕ → ℚ)
    {g1 g2 : ℕ} (c : ℚ) (hW : ∀ j, k + 1 ≤ W j ∧ W j ≤ N) (hg1 : k + 1 ≤ g1 ∧ g1 ≤ N)
    (hg2 : k + 1 ≤ g2 ∧ g2 ≤ N) (hg : g1 ≠ g2)
    (hr : ∀ j, 1 ≤ j → j ≤ k → ∑ l ∈ Icc 1 k, M j l + r j = 0)
    (hpath : ∀ j, k + 1 ≤ j → j ≤ N → (∑ l ∈ Icc 1 N, pkRChE k r W l j) +
      ((if k + 1 ≤ j ∧ j + 1 ≤ N then e j else 0) + (if k + 2 ≤ j ∧ j ≤ N then e (j - 1) else 0)) +
      ((if j = g1 then c else 0) + (if j = g2 then c else 0)) = 0) :
    ∀ j ∈ Icc 1 N, ∑ l ∈ Icc 1 N, pkRChD N k M r W e g1 g2 c j l = 0 := by
  intro j hj
  rw [mem_Icc] at hj
  unfold pkRChD
  simp only [sum_add_distrib]
  rw [pkR_ch_rowL (by omega) M j, pkR_ch_rowE r W j ⟨by have := (hW j).1; omega, (hW j).2⟩,
      pkR_ch_rowpe1 e j,
    pkR_ch_rowpe2 e hj.1, pkR_ch_rowG c j (mem_Icc.2 ⟨by omega, hg1.2⟩)
        (mem_Icc.2 ⟨by omega, hg2.2⟩) hg]
  by_cases h : j ≤ k
  · rw [ite_eq_left h, ite_eq_left h]
    have h0 : ∑ l ∈ Icc 1 N, pkRChE k r W l j = 0 :=
      sum_eq_zero (fun l _ => by
        unfold pkRChE
        exact ite_eq_right (fun h' => by have := (hW l).1; omega))
    rw [h0, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega)]
    linarith [hr j hj.1 h]
  · rw [ite_eq_right h, ite_eq_right h]
    have := hpath j (by omega) hj.2
    linarith

/-- The path solution: consecutive complement edges carry `e`, and row `j` of the complement
receives `T j` (needs `F N = 0`). -/
theorem pkR_ch_path {N k : ℕ} (T : ℕ → ℚ) (hF : pkRChF k T N = 0) {j : ℕ} (hj1 : k + 1 ≤ j)
    (hj2 : j ≤ N) :
    (if k + 1 ≤ j ∧ j + 1 ≤ N then pkRChe k T j else 0) +
      (if k + 2 ≤ j ∧ j ≤ N then pkRChe k T (j - 1) else 0) = T j := by
  have hstep : pkRChe k T j + pkRChe k T (j - 1) = T j := by
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hF1 : pkRChF k T (i + 1) = pkRChF k T i + (-1) ^ (i + 1) * T (i + 1) := by
      unfold pkRChF
      exact sum_Icc_succ_top (by omega) _
    unfold pkRChe
    rw [show i + 1 - 1 = i by omega, hF1]
    have hsq : ((-1 : ℚ) ^ i) * (-1) ^ i = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [pow_succ]
    linear_combination (T (i + 1)) * hsq
  have hk : pkRChe k T k = 0 := by
    unfold pkRChe pkRChF
    rw [Icc_eq_empty (by omega), sum_empty, mul_zero]
  have hN : pkRChe k T N = 0 := by
    unfold pkRChe
    rw [hF, mul_zero]
  by_cases a : j + 1 ≤ N
  · by_cases b : k + 2 ≤ j
    · rw [ite_eq_left ⟨hj1, a⟩, ite_eq_left ⟨b, hj2⟩]
      exact hstep
    · rw [ite_eq_left ⟨hj1, a⟩, ite_eq_right (by omega)]
      rw [show j - 1 = k by omega, hk] at hstep
      linarith
  · have hjN : j = N := by omega
    rw [ite_eq_right (by omega)]
    rw [hjN] at hstep ⊢
    rw [hN] at hstep
    by_cases b : k + 2 ≤ N
    · rw [ite_eq_left ⟨b, le_rfl⟩]
      linarith
    · rw [ite_eq_right (by omega)]
      rw [show N - 1 = k by omega, hk] at hstep
      linarith

/-- The balancing constant `c` (as in `hc`) on the same-parity pair `g1`, `g2` of complement legs
makes the alternating sum of the complement targets vanish. -/
theorem pkR_ch_FN {N k : ℕ} (ρ : ℕ → ℚ) {g1 g2 : ℕ} (hg1 : k + 1 ≤ g1 ∧ g1 ≤ N)
    (hg2 : k + 1 ≤ g2 ∧ g2 ≤ N) (hgp : g1 % 2 = g2 % 2) {c : ℚ}
    (hc : c = -((-1) ^ g1 * ∑ i ∈ Icc (k + 1) N, (-1) ^ i * ρ i) / 2) :
    pkRChF k (fun q => -ρ q - (if q = g1 then c else 0) - (if q = g2 then c else 0)) N = 0 := by
  unfold pkRChF
  have e1 : ∀ i ∈ Icc (k + 1) N,
      (-1 : ℚ) ^ i * (-ρ i - (if i = g1 then c else 0) - (if i = g2 then c else 0)) =
      -((-1) ^ i * ρ i) - (if i = g1 then (-1) ^ g1 * c else 0) - (if i =
          g2 then (-1) ^ g2 * c else 0) := by
    intro i _
    split_ifs with h1 h2 h2
    · subst h1
      subst h2
      ring
    · subst h1
      ring
    · subst h2
      ring
    · ring
  rw [sum_congr rfl e1, sum_sub_distrib, sum_sub_distrib, sum_neg_distrib, sum_ite_eq', sum_ite_eq',
    ite_eq_left (mem_Icc.2 hg1), ite_eq_left (mem_Icc.2 hg2)]
  have hp : (-1 : ℚ) ^ g2 = (-1) ^ g1 := by
    rw [neg_one_pow_eq_pow_mod_two, ← hgp, ← neg_one_pow_eq_pow_mod_two]
  have hsq : (-1 : ℚ) ^ g1 * (-1) ^ g1 = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [hp, hc]
  linear_combination (∑ i ∈ Icc (k + 1) N, (-1) ^ i * ρ i) * hsq

theorem pkR_ch_Dsymm {N k : ℕ} {M : ℕ → ℕ → ℚ} (hM : ∀ a b, M a b = M b a) (r : ℕ → ℚ)
    (W : ℕ → ℕ) (e : ℕ → ℚ)
    (g1 g2 : ℕ) (c : ℚ) (a b : ℕ) : pkRChD N k M r W e g1 g2 c a b =
        pkRChD N k M r W e g1 g2 c b a := by
  unfold pkRChD
  have h1 : pkRChL k M a b = pkRChL k M b a := by
    unfold pkRChL
    rw [hM a b]
    by_cases ha : a ≤ k <;> by_cases hb : b ≤ k <;> simp [ha, hb]
  have h2 : pkRChG g1 g2 c a b = pkRChG g1 g2 c b a := by
    unfold pkRChG
    by_cases h : (a = g1 ∧ b = g2) ∨ (a = g2 ∧ b = g1)
    · rw [ite_eq_left h, ite_eq_left (by omega)]
    · rw [ite_eq_right h, ite_eq_right (by omega)]
  rw [h1, h2]
  ring

theorem pkR_ch_Ddiag {N k : ℕ} {M : ℕ → ℕ → ℚ} (hM0 : ∀ a, M a a = 0) (r : ℕ → ℚ) {W : ℕ → ℕ}
    (hW : ∀ j, k + 1 ≤ W j) (e : ℕ → ℚ) {g1 g2 : ℕ} (hg : g1 ≠ g2) (c : ℚ) (a : ℕ) :
    pkRChD N k M r W e g1 g2 c a a = 0 := by
  have := hW a
  unfold pkRChD pkRChL pkRChE pkRChPe pkRChG
  rw [ite_eq_right (show ¬ (a ≤ k ∧ a = W a) by omega),
      ite_eq_right (show ¬ (k + 1 ≤ a ∧ a = a + 1 ∧ a ≤ N) by omega),
    ite_eq_right (show ¬ ((a = g1 ∧ a = g2) ∨ (a = g2 ∧ a = g1)) by omega), hM0 a]
  simp

/-- The target of the mesh variable of each child leg `j ∈ 1..k` with `P̂` (child leg `k + 1`): a
complement leg `W j` (rotated index in `k + 1..N`) such that the parent pair of `j` and `W j` is not
in `S`, unless that mesh variable vanishes on the child locus (`3 ≤ k`, `k + 3 ≤ N`,
`S ⊆ diagonals N`). The proof takes an adjacent leg for the end legs and a missing crossing pair for
interior legs. -/
theorem pkR_ch_W {N s k : ℕ} (hs : 1 ≤ s ∧ s ≤ N) (hk : 3 ≤ k) (hkN : k + 3 ≤ N)
    {S : Finset (ℕ × ℕ)} (hS : S ⊆ diagonals N) (y : ℕ × ℕ → ℚ)
    (hy : OnLocus (k + 1) ((diagonals (k + 1)).filter (fun σ => ChildPairIn N S s k (k + 1)
      (fun j => vtx N (s + j - 1)) σ.1 σ.2)) y) :
    ∃ W : ℕ → ℕ, (∀ j, k + 1 ≤ W j ∧ W j ≤ N) ∧ ∀ j, 1 ≤ j → j ≤ k → (mesh (k + 1) y j (k + 1) = 0 ∨
      (min (vtx N (s + j - 1)) (vtx N (s + W j - 1)), max (vtx N (s + j - 1))
          (vtx N (s + W j - 1))) ∉ S) := by
  classical
  refine ⟨fun j => if j = 1 then N else if j = k then k + 1 else
    if h : ∃ w ∈ Icc 1 N, w ∉ cycArc N s k ∧
        (min (vtx N (s + j - 1)) w, max (vtx N (s + j - 1)) w) ∉ S then
      pkRChChi N s (Classical.choose h) else k + 1, ?_, ?_⟩
  · intro j
    dsimp only
    split_ifs with h1 h2 h3
    · omega
    · omega
    · obtain ⟨hw, hwc, -⟩ := Classical.choose_spec h3
      rw [pkCo_mem_cycArc_pos (mem_Icc.2 hs) (by omega)] at hwc
      have h' : ¬ cycPos N s (Classical.choose h3) < k := fun h => hwc ⟨hw, h⟩
      have hlt : cycPos N s (Classical.choose h3) < N := Nat.mod_lt _ (by omega)
      change k + 1 ≤ cycPos N s (Classical.choose h3) + 1 ∧ cycPos N s (Classical.choose h3) + 1 ≤ N
      omega
    · omega
  · intro j hj1 hjk
    dsimp only
    split_ifs with h1 h2 h3
    · right
      intro hmem
      subst h1
      have e1 : vtx N (s + 1 - 1) = s := by
        rw [show s + 1 - 1 = s by omega]
        exact vtx_of_mem hs.1 hs.2
      have e2 := pkR_ch_vtx (N := N) (x := s + N - 1) (by omega) (by omega)
      refine pkR_ch_nd ?_ (hS hmem)
      rw [e1]
      split_ifs at e2 <;> omega
    · right
      intro hmem
      subst h2
      have e1 := pkR_ch_vtx (N := N) (x := s + j - 1) (by omega) (by omega)
      have e2 := pkR_ch_vtx (N := N) (x := s + (j + 1) - 1) (by omega) (by omega)
      refine pkR_ch_nd ?_ (hS hmem)
      split_ifs at e1 e2 <;> omega
    · right
      obtain ⟨hw, -, hwS⟩ := Classical.choose_spec h3
      rw [pkR_ch_psi_chi hs (mem_Icc.1 hw)]
      exact hwS
    · left
      refine hy (j, k + 1) (mem_filter.2 ⟨mem_diagonals.2 (by dsimp only; omega), ?_⟩)
      unfold ChildPairIn
      dsimp only
      rw [ite_eq_right (by omega), ite_eq_left rfl]
      intro w hw hwc
      by_contra hc
      exact h3 ⟨w, hw, hwc, hc⟩

/-- **Child surjectivity, generic side**: the child of the arc `(s, k)` in the `relab N s` labelling
(child legs `1..k` = the side, `P̂` = child leg `k + 1`), for `3 ≤ k`, `k + 3 ≤ N` and
`S ⊆ diagonals N`. Given one missing same-parity pair of distinct complement legs (rotated indices
`g1`, `g2`), every point of the child locus lifts to a point of `L_S` with `X_P = 0` (`P` = the
chord `(s, s + k)`). -/
theorem pkR_ch_gen {N s k : ℕ} (hs : 1 ≤ s ∧ s ≤ N) (hk : 3 ≤ k) (hkN : k + 3 ≤ N)
    {S : Finset (ℕ × ℕ)} (hS : S ⊆ diagonals N) {g1 g2 : ℕ} (hg1 : k + 1 ≤ g1 ∧ g1 ≤ N)
    (hg2 : k + 1 ≤ g2 ∧ g2 ≤ N) (hg : g1 ≠ g2) (hgp : g1 % 2 = g2 % 2)
    (hgS : (min (vtx N (s + g1 - 1)) (vtx N (s + g2 - 1)), max (vtx N (s + g1 - 1))
        (vtx N (s + g2 - 1))) ∉ S)
    (y : ℕ × ℕ → ℚ)
    (hy : OnLocus (k + 1) ((diagonals (k + 1)).filter (fun σ => ChildPairIn N S s k (k + 1)
      (fun j => vtx N (s + j - 1)) σ.1 σ.2)) y) :
    ∃ X : ℕ × ℕ → ℚ, OnLocus N S X ∧ planar N X s (s + k) = 0 ∧
      ∀ d ∈ diagonals (k + 1), X (relab N s d) = y d := by
  classical
  have hN1 : 1 ≤ N := by omega
  obtain ⟨W, hW, hWS⟩ := pkR_ch_W hs hk hkN hS y hy
  obtain ⟨M, hM⟩ : ∃ M : ℕ → ℕ → ℚ, M = fun a b => mesh (k + 1) y a b := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℕ → ℚ, r = fun j => mesh (k + 1) y j (k + 1) := ⟨_, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ → ℚ, ρ = fun q => ∑ l ∈ Icc 1 N, pkRChE k r W l q := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℚ, c = -((-1) ^ g1 * ∑ i ∈ Icc (k + 1) N, (-1) ^ i * ρ i) / 2 := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℕ → ℚ, T =
      fun q => -ρ q - (if q = g1 then c else 0) - (if q = g2 then c else 0) :=
    ⟨_, rfl⟩
  have hFN : pkRChF k T N = 0 := by
    rw [hT]
    exact pkR_ch_FN ρ hg1 hg2 hgp hc
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℕ → ℚ, D = pkRChD N k M r W (pkRChe k T) g1 g2 c := ⟨_, rfl⟩
  have hMs : ∀ a b, M a b = M b a := fun a b => by rw [hM]; exact pkR_mesh_comm (k + 1) y a b
  have hM0 : ∀ a, M a a = 0 := fun a => by rw [hM]; exact pkR_mesh_self (by omega) y a
  have hrow : ∀ j ∈ Icc 1 N, ∑ l ∈ Icc 1 N, D j l = 0 := by
    rw [hD]
    refine pkR_ch_row (by omega) M r W (pkRChe k T) c hW hg1 hg2 hg ?_ ?_
    · intro j _ _
      rw [hM, hr]
      dsimp only
      rw [← sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
      exact pkL_row (by omega) y j
    · intro j hj1 hj2
      rw [pkR_ch_path T hFN hj1 hj2]
      have e : ∑ l ∈ Icc 1 N, pkRChE k r W l j = ρ j := by rw [hρ]
      rw [e, hT]
      dsimp only
      ring
  obtain ⟨C, hCdef⟩ : ∃ C : ℕ → ℕ → ℚ, C = fun a b => D (pkRChChi N s a)
      (pkRChChi N s b) := ⟨_, rfl⟩
  have hCs : ∀ a b, C a b = C b a := fun a b => by
    rw [hCdef, hD]
    exact pkR_ch_Dsymm hMs r W _ g1 g2 c _ _
  have hCd : ∀ a, C a a = 0 := fun a => by
    rw [hCdef, hD]
    exact pkR_ch_Ddiag hM0 r (fun j => (hW j).1) _ hg c _
  have hCr : ∀ a ∈ Icc 1 N, Finset.sum (Icc 1 N) (fun b => C a b) = 0 := by
    intro a ha
    rw [hCdef]
    have hm := pkR_ch_chi_mem hs (mem_Icc.1 ha)
    refine (Finset.sum_nbij' (fun b => pkRChChi N s b) (fun l => vtx N (s + l - 1)) ?_ ?_ ?_ ?_
      (fun b _ => rfl)).trans (hrow _ (mem_Icc.2 hm))
    · intro b hb
      exact mem_Icc.2 (pkR_ch_chi_mem hs (mem_Icc.1 hb))
    · intro l _
      exact mem_Icc.2 (vtx_bounds N _ hN1)
    · intro b hb
      exact pkR_ch_psi_chi hs (mem_Icc.1 hb)
    · intro l hl
      exact pkR_ch_chi_psi hs (mem_Icc.1 hl)
  obtain ⟨X, hX⟩ : ∃ X : ℕ × ℕ → ℚ, X = pkRGramPt C := ⟨_, rfl⟩
  have hC : ∀ a b, 1 ≤ a ∧ a ≤ N → 1 ≤ b ∧ b ≤ N → a ≠ b →
      mesh N X a b = D (pkRChChi N s a) (pkRChChi N s b) := by
    intro a b ha hb hab
    rw [hX, pkR_gram hN1 C hCs hCd hCr (mem_Icc.2 ha) (mem_Icc.2 hb) hab, hCdef]
  -- side block: D = child mesh
  have hDL : ∀ a b, 1 ≤ a → a < b → b ≤ k → D a b = mesh (k + 1) y a b := by
    intro a b ha hab hb
    rw [hD]
    unfold pkRChD pkRChL pkRChE pkRChPe pkRChG
    have h1 := (hW a).1
    have h2 := (hW b).1
    rw [ite_eq_left ⟨by omega, hb⟩, ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), hM]
    ring
  have hm : ∀ a b, 1 ≤ a → a < b → b ≤ k → mesh N X (a + s - 1) (b + s - 1) =
      mesh (k + 1) y a b := by
    intro a b ha hab hb
    have va := vtx_bounds N (a + s - 1) hN1
    have vb := vtx_bounds N (b + s - 1) hN1
    have hne : vtx N (a + s - 1) ≠ vtx N (b + s - 1) := by
      intro h
      have := congrArg (pkRChChi N s) h
      rw [show a + s - 1 = s + a - 1 by omega, show b + s - 1 = s + b - 1 by omega,
        pkR_ch_chi_psi hs ⟨ha, by omega⟩, pkR_ch_chi_psi hs ⟨by omega, by omega⟩] at this
      omega
    rw [pkR_mesh_vtx hN1, hC _ _ va vb hne, show a + s - 1 = s + a - 1 by omega, show b + s - 1 =
        s + b - 1 by omega,
      pkR_ch_chi_psi hs ⟨ha, by omega⟩, pkR_ch_chi_psi hs ⟨by omega, by omega⟩]
    exact hDL a b ha hab hb
  refine ⟨X, ?_, ?_, ?_⟩
  · -- OnLocus N S X
    intro t ht
    obtain ⟨a, b⟩ := t
    have htd := mem_diagonals.1 (hS ht)
    dsimp only at htd ⊢
    rw [hC a b ⟨htd.1, by omega⟩ ⟨by omega, htd.2.1⟩ (by omega)]
    have ea := pkR_ch_chi_eq hs ⟨htd.1, (show a ≤ N by omega)⟩
    have eb := pkR_ch_chi_eq hs ⟨(show 1 ≤ b by omega), htd.2.1⟩
    have pa := pkR_ch_psi_chi hs ⟨htd.1, (show a ≤ N by omega)⟩
    have pb := pkR_ch_psi_chi hs ⟨(show 1 ≤ b by omega), htd.2.1⟩
    have hadj : pkRChChi N s b ≠ pkRChChi N s a + 1 ∧ pkRChChi N s a ≠ pkRChChi N s b + 1 ∧
        pkRChChi N s a ≠ pkRChChi N s b ∧ 1 ≤ pkRChChi N s a ∧ 1 ≤ pkRChChi N s b := by
      rw [ea, eb]
      split_ifs <;> omega
    generalize hj : pkRChChi N s a = j at hadj pa
    generalize hl : pkRChChi N s b = l at hadj pb
    have hab : (min a b, max a b) = (a, b) := by
      rw [min_eq_left (by omega), max_eq_right (by omega)]
    have hba : (min b a, max b a) = (a, b) := by
      rw [min_eq_right (by omega), max_eq_left (by omega)]
    rw [hD]
    unfold pkRChD
    have hL : pkRChL k M j l = 0 := by
      unfold pkRChL
      split_ifs with hjl
      · rw [hM]
        dsimp only
        rcases lt_or_gt_of_ne hadj.2.2.1 with hlt | hlt
        · refine hy (j, l) (mem_filter.2 ⟨mem_diagonals.2 (by dsimp only; omega), ?_⟩)
          unfold ChildPairIn
          dsimp only
          rw [ite_eq_right (by omega), ite_eq_right (by omega), pa, pb, hab]
          exact ht
        · rw [pkR_mesh_comm]
          refine hy (l, j) (mem_filter.2 ⟨mem_diagonals.2 (by dsimp only; omega), ?_⟩)
          unfold ChildPairIn
          dsimp only
          rw [ite_eq_right (by omega), ite_eq_right (by omega), pa, pb, hba]
          exact ht
      · rfl
    have hE1 : pkRChE k r W j l = 0 := by
      unfold pkRChE
      split_ifs with h
      · rcases hWS j hadj.2.2.2.1 h.1 with h0 | h0
        · rw [hr]
          exact h0
        · exfalso
          rw [← h.2, pa, pb, hab] at h0
          exact h0 ht
      · rfl
    have hE2 : pkRChE k r W l j = 0 := by
      unfold pkRChE
      split_ifs with h
      · rcases hWS l hadj.2.2.2.2 h.1 with h0 | h0
        · rw [hr]
          exact h0
        · exfalso
          rw [← h.2, pa, pb, hba] at h0
          exact h0 ht
      · rfl
    have hP1 : pkRChPe N k (pkRChe k T) j l = 0 := by
      unfold pkRChPe
      exact ite_eq_right (fun h => hadj.1 h.2.1)
    have hP2 : pkRChPe N k (pkRChe k T) l j = 0 := by
      unfold pkRChPe
      exact ite_eq_right (fun h => hadj.2.1 h.2.1)
    have hG : pkRChG g1 g2 c j l = 0 := by
      unfold pkRChG
      split_ifs with h
      · exfalso
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [← h1, ← h2, pa, pb, hab] at hgS
          exact hgS ht
        · rw [min_comm, max_comm, ← h1, ← h2, pa, pb, hab] at hgS
          exact hgS ht
      · rfl
    rw [hL, hE1, hE2, hP1, hP2, hG]
    ring
  · -- X_P = 0
    have h1 := pkR_ch_shift hN1 hs.1 hm (p := 1) (r := k + 1) le_rfl (by omega) le_rfl
    rw [show 1 + s - 1 = s by omega, show k + 1 + s - 1 = s + k by omega] at h1
    rw [h1, pkR_planar_def, vtx_of_mem le_rfl (by omega), vtx_of_mem (by omega) le_rfl,
      min_eq_left (by omega), max_eq_right (by omega)]
    refine ite_eq_right ?_
    rw [mem_diagonals]
    dsimp only
    omega
  · -- X ∘ relab = y on the child diagonals
    rintro ⟨d1, d2⟩ hd
    have hd' := mem_diagonals.1 hd
    dsimp only at hd'
    have h1 := pkR_ch_shift hN1 hs.1 hm (p := d1) (r := d2) hd'.1 (by omega) hd'.2.1
    have e1 := pkR_ch_vtx (N := N) (x := d1 + s - 1) (by omega) (by omega)
    have e2 := pkR_ch_vtx (N := N) (x := d2 + s - 1) (by omega) (by omega)
    have hmem : relab N s (d1, d2) ∈ diagonals N := by
      change (min (vtx N (d1 + s - 1)) (vtx N (d2 + s - 1)), max (vtx N (d1 + s - 1))
          (vtx N (d2 + s - 1))) ∈
        diagonals N
      rw [e1, e2]
      apply pkR_ch_pmem <;> split_ifs <;> omega
    have h2 : planar N X (d1 + s - 1) (d2 + s - 1) = X (relab N s (d1, d2)) := by
      rw [pkR_planar_def]
      exact ite_eq_left hmem
    have h3 : planar (k + 1) y d1 d2 = y (d1, d2) := by
      rw [pkR_planar_def, vtx_of_mem hd'.1 (by omega), vtx_of_mem (by omega) hd'.2.1,
          min_eq_left (by omega),
        max_eq_right (by omega)]
      exact ite_eq_left hd
    rw [← h2, h1, h3]

theorem pkR_ch_planarP {N : ℕ} (X : ℕ × ℕ → ℚ) {P : ℕ × ℕ} (hP : P ∈ diagonals N) {u v : ℕ}
    (hu : (vtx N u = P.1 ∧ vtx N v = P.2) ∨
        (vtx N u = P.2 ∧ vtx N v = P.1)) : planar N X u v = X P := by
  obtain ⟨i, j⟩ := P
  have h := mem_diagonals.1 hP
  dsimp only at h hu
  rw [pkR_planar_def]
  rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  · rw [min_eq_left (by omega), max_eq_right (by omega)]
    exact ite_eq_left hP
  · rw [min_eq_right (by omega), max_eq_left (by omega)]
    exact ite_eq_left hP

/-- The variable of an odd chord `P` read from its head:
`X_{(headStart, headStart + headLen)} = X_P`. -/
theorem pkR_ch_chordH {N : ℕ} (X : ℕ × ℕ → ℚ) {P : ℕ × ℕ} (hP : P ∈ oddDiagonals N) :
    planar N X (headStart P) (headStart P + headLen N P) = X P := by
  have hPd : P ∈ diagonals N := (mem_filter.1 hP).1
  obtain ⟨i, j⟩ := P
  have h := mem_diagonals.1 hPd
  dsimp only at h
  refine pkR_ch_planarP X hPd ?_
  unfold headStart headLen
  dsimp only
  split_ifs with hp
  · have e1 := pkR_ch_vtx (N := N) (x := i) (by omega) (by omega)
    have e2 := pkR_ch_vtx (N := N) (x := i + (j - i)) (by omega) (by omega)
    split_ifs at e1 e2 <;> omega
  · have e1 := pkR_ch_vtx (N := N) (x := j) (by omega) (by omega)
    have e2 := pkR_ch_vtx (N := N) (x := j + (N - (j - i))) (by omega) (by omega)
    split_ifs at e1 e2 <;> omega

/-- The same from the tail. -/
theorem pkR_ch_chordT {N : ℕ} (X : ℕ × ℕ → ℚ) {P : ℕ × ℕ} (hP : P ∈ oddDiagonals N) :
    planar N X (tailStart P) (tailStart P + tailLen N P) = X P := by
  have hPd : P ∈ diagonals N := (mem_filter.1 hP).1
  obtain ⟨i, j⟩ := P
  have h := mem_diagonals.1 hPd
  dsimp only at h
  refine pkR_ch_planarP X hPd ?_
  unfold tailStart tailLen headLen
  dsimp only
  split_ifs with hp
  · have e1 := pkR_ch_vtx (N := N) (x := j) (by omega) (by omega)
    have e2 := pkR_ch_vtx (N := N) (x := j + (N - (j - i))) (by omega) (by omega)
    split_ifs at e1 e2 <;> omega
  · have e1 := pkR_ch_vtx (N := N) (x := i) (by omega) (by omega)
    have e2 := pkR_ch_vtx (N := N) (x := i + (N - (N - (j - i)))) (by omega) (by omega)
    split_ifs at e1 e2 <;> omega

/-- A missing same-parity pair with both legs outside the side `cycArc N s k` (`N` even) gives the
rotated-index hypotheses of `pkR_ch_gen`. -/
theorem pkR_ch_gpair {N s k : ℕ} (hE : N % 2 = 0) (hs : 1 ≤ s ∧ s ≤ N) (hkN : k ≤ N)
    {S : Finset (ℕ × ℕ)} {g : ℕ × ℕ} (hgd : g ∈ diagonals N) (hgS : g ∉ S) (hgp : g.1 % 2 = g.2 % 2)
    (h1 : g.1 ∉ cycArc N s k) (h2 : g.2 ∉ cycArc N s k) :
    (k + 1 ≤ pkRChChi N s g.1 ∧ pkRChChi N s g.1 ≤ N) ∧
        (k + 1 ≤ pkRChChi N s g.2 ∧ pkRChChi N s g.2 ≤ N) ∧
      pkRChChi N s g.1 ≠ pkRChChi N s g.2 ∧ pkRChChi N s g.1 % 2 = pkRChChi N s g.2 % 2 ∧
      (min (vtx N (s + pkRChChi N s g.1 - 1)) (vtx N (s + pkRChChi N s g.2 - 1)),
        max (vtx N (s + pkRChChi N s g.1 - 1)) (vtx N (s + pkRChChi N s g.2 - 1))) ∉ S := by
  obtain ⟨a, b⟩ := g
  have h := mem_diagonals.1 hgd
  dsimp only at h hgp h1 h2 ⊢
  rw [pkCo_mem_cycArc_pos (mem_Icc.2 hs) hkN] at h1 h2
  have c1 : ¬ cycPos N s a < k := fun hc => h1 ⟨mem_Icc.2 ⟨h.1, by omega⟩, hc⟩
  have c2 : ¬ cycPos N s b < k := fun hc => h2 ⟨mem_Icc.2 ⟨by omega, h.2.1⟩, hc⟩
  have ea := pkR_ch_chi_eq hs ⟨h.1, (show a ≤ N by omega)⟩
  have eb := pkR_ch_chi_eq hs ⟨(show 1 ≤ b by omega), h.2.1⟩
  have fa : pkRChChi N s a = cycPos N s a + 1 := rfl
  have fb : pkRChChi N s b = cycPos N s b + 1 := rfl
  rw [pkR_ch_psi_chi hs ⟨h.1, (show a ≤ N by omega)⟩,
      pkR_ch_psi_chi hs ⟨(show 1 ≤ b by omega), h.2.1⟩,
    min_eq_left (by omega), max_eq_right (by omega)]
  refine ⟨?_, ?_, ?_, ?_, hgS⟩
  · rw [ea] at fa ⊢
    split_ifs at fa ⊢ <;> omega
  · rw [eb] at fb ⊢
    split_ifs at fb ⊢ <;> omega
  · rw [ea, eb]
    split_ifs <;> omega
  · rw [ea, eb]
    split_ifs <;> omega

/-- **Child surjectivity for the B-child of `t`** (the `relab N (tailStart t)` labelling,
`pkRBChildB'`, `C8`), for even `N ≥ 6`, `InFpi N S` and a pole chord `t`: the form `pkR_d_reduce`
takes as `hChB`. The balancing pair is a missing oo pair inside the head (`innerOO t ≠ ∅`,
`t ∈ 𝒫₁`). -/
theorem pkR_ch_childB {N : ℕ} (hN : 6 ≤ N) (hE : Even N) :
    ∀ (S : Finset (ℕ × ℕ)) (t : ℕ × ℕ), InFpi N S →
    t ∈ poleChords N S → pkRDChild1 N S t (tailStart t) (tailLen N t + 1)
        (pkRBChildB' N S t) := by
  intro S t hF ht y hy
  have hEN : N % 2 = 0 := Nat.even_iff.1 hE
  have htO : t ∈ oddDiagonals N := (mem_filter.1 (mem_filter.1 ht).1).1
  obtain ⟨hs, -, -, hk3, hkN, -, -, -, -, -⟩ := pkCh_sides hEN htO
  obtain ⟨g, hg⟩ := (mem_filter.1 ht).2.2
  obtain ⟨hgM, hg1, hg2⟩ := mem_filter.1 hg
  obtain ⟨hgmiss, hgo⟩ := mem_filter.1 hgM
  obtain ⟨hgd, hgS⟩ := mem_sdiff.1 hgmiss
  have hcyc : ∀ x, x ∈ oddSide N t → x ∉ cycArc N (tailStart t) (tailLen N t) := fun x hx hc => by
    rw [← (sides_eq_cycArc (by omega) hE htO).2] at hc
    exact (mem_sdiff.1 hc).2 hx
  have hgp : g.1 % 2 = g.2 % 2 := by
    obtain ⟨o1, o2⟩ := hgo
    omega
  obtain ⟨q1, q2, q3, q4, q5⟩ := pkR_ch_gpair hEN (mem_Icc.1 hs) (by omega) hgd hgS hgp (hcyc _ hg1)
    (hcyc _ hg2)
  obtain ⟨X, hX, hXP, hXd⟩ := pkR_ch_gen (mem_Icc.1 hs) hk3 hkN hF.1 q1 q2 q3 q4 q5 y hy
  refine ⟨X, hX, ?_, hXd⟩
  rw [← pkR_ch_chordT X htO]
  exact hXP

/-- **Child surjectivity for the A-child of `b`** (`childSetA` (`C0`), `relab N (headStart b)`), for
even `N ≥ 6`, `InFpi N S`, a pole chord `t` and `b` in its class: the form `pkR_d_reduce` takes as
`hChA`. The lift has `X_b = 0`; `X_t = X_b` on `L_S` by `chord_restrict` (`C0`; equal hit sets). The
balancing pair is a missing ee pair inside the tail of `b` (`innerEE b ≠ ∅`, `b ∈ 𝒫₁`). -/
theorem pkR_ch_childA {N : ℕ} (hN : 6 ≤ N) (hE : Even N) :
    ∀ (S : Finset (ℕ × ℕ)) (t b : ℕ × ℕ), InFpi N S →
    t ∈ poleChords N S → b ∈ hitClass N S t →
    pkRDChild1 N S t (headStart b) (headLen N b + 1) (childSetA N S b) := by
  intro S t b hF ht hb y hy
  have hEN : N % 2 = 0 := Nat.even_iff.1 hE
  have htO : t ∈ oddDiagonals N := (mem_filter.1 (mem_filter.1 ht).1).1
  have hbP : b ∈ poleChords N S := (mem_filter.1 hb).1
  have hbO : b ∈ oddDiagonals N := (mem_filter.1 (mem_filter.1 hbP).1).1
  obtain ⟨-, -, -, -, -, hs, -, -, hk3, hkN⟩ := pkCh_sides hEN hbO
  obtain ⟨g, hg⟩ := (mem_filter.1 hbP).2.1
  obtain ⟨hgM, hg1, hg2⟩ := mem_filter.1 hg
  obtain ⟨hgmiss, hgo⟩ := mem_filter.1 hgM
  obtain ⟨hgd, hgS⟩ := mem_sdiff.1 hgmiss
  have hcyc : ∀ x, x ∈ evenSide N b → x ∉ cycArc N (headStart b) (headLen N b) := fun x hx hc => by
    rw [← (sides_eq_cycArc (by omega) hE hbO).1] at hc
    exact (mem_sdiff.1 hx).2 hc
  have hgp : g.1 % 2 = g.2 % 2 := by
    obtain ⟨o1, o2⟩ := hgo
    omega
  obtain ⟨q1, q2, q3, q4, q5⟩ := pkR_ch_gpair hEN (mem_Icc.1 hs) (by omega) hgd hgS hgp (hcyc _ hg1)
    (hcyc _ hg2)
  obtain ⟨X, hX, hXP, hXd⟩ := pkR_ch_gen (mem_Icc.1 hs) hk3 hkN hF.1 q1 q2 q3 q4 q5 y hy
  refine ⟨X, hX, ?_, hXd⟩
  have hXb : X b = 0 := by
    rw [← pkR_ch_chordH X hbO]
    exact hXP
  have et := chord_restrict (by omega) hE hF.1 X hX htO
  have eb := chord_restrict (by omega) hE hF.1 X hX hbO
  rw [(mem_filter.1 hb).2] at eb
  rw [et, ← eb, hXb]

/-! ### The residue in numerator form for a general class

For a class in which members may cross, the numerator is expanded by peeling members in
head order, by strong induction (no enumeration): top-down (`pkR_d2_top_ind`), bottom-up
(`pkR_d2_bot_ind`) and on the A-side (`pkR_d2_Aside`); then the count of the powers of `x`
(`pkR_d2_count`) and the Ω formula at two class members (`pkR_d2_omegaQ`). The section continues in
`C10`. -/

/-- Crossing is symmetric. -/
theorem pkR_d2_cross_symm {p q : ℕ × ℕ} (h : Crosses p q) : Crosses q p := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- An odd chord is determined by its head. -/
theorem pkR_d2_eq_of_head {N : ℕ} {Q Q' : ℕ × ℕ} (hQ : Q ∈ oddDiagonals N)
    (hQ' : Q' ∈ oddDiagonals N)
    (h : oddSide N Q = oddSide N Q') : Q = Q' := by
  obtain ⟨q1, q2⟩ := Q
  obtain ⟨r1, r2⟩ := Q'
  obtain ⟨h1, h2⟩ := pkR_b_head_inj hQ hQ' h
  rw [h1, h2]

/-- If two odd chords `Q`, `Q′` cross, `A_Q ⊄ A_{Q′}` (with `pkR_d2_cross_symm`, the heads are
incomparable); pair form of `pkR_b_cross_not_sub` (`C7`). -/
theorem pkR_d2_cross_nsub {N : ℕ} {Q Q' : ℕ × ℕ} (hQ : Q ∈ oddDiagonals N)
    (hQ' : Q' ∈ oddDiagonals N)
    (hc : Crosses Q Q') : ¬ oddSide N Q ⊆ oddSide N Q' := by
  obtain ⟨q1, q2⟩ := Q
  obtain ⟨r1, r2⟩ := Q'
  exact pkR_b_cross_not_sub hQ hQ' hc

/-- **Head child, crossing allowed:** for an odd chord `C` and a set `K` of odd chords each of which
crosses `C` or has a head containing `A_C`, no chord of `K` is a diagonal of the head child of `C`:
the banned set pulled back to that child is empty. -/
theorem pkR_d2_pull_head {N : ℕ} {C : ℕ × ℕ} (hC : C ∈ oddDiagonals N) {K : Finset (ℕ × ℕ)}
    (hK : K ⊆ oddDiagonals N) (hKC : ∀ Q ∈ K, oddSide N C ⊆ oddSide N Q ∨ Crosses Q C) :
    pkRBPull N (headStart C) (headLen N C + 1) K = ∅ := by
  refine filter_false_of_mem fun d hd hQ => ?_
  have hd' := mem_diagonals.1 hd
  have bb := pkR_b_odd_iff.1 hC
  have hH := pkR_b_head_data hC
  obtain ⟨p1, p2, e, h1, h2⟩ := pkR_b_relab_eq (N := N) (s := headStart C) (n := headLen N C + 1)
    (by omega) (by omega) hd
  rw [e] at hQ
  have hQo := hK hQ
  rcases hKC _ hQ with hsub | hc
  · obtain ⟨b1, b2⟩ := C
    dsimp only at hH hd' bb h1 h2
    have c := pkR_b_R17_hcore hQo hC hsub (by omega)
    omega
  · obtain ⟨b1, b2⟩ := C
    dsimp only at hH hd' bb h1 h2
    unfold Crosses at hc
    dsimp only at hc
    omega

/-- **Tail child, crossing allowed:** for an odd chord `C` and a set `K` of odd chords each of which
crosses `C` or has a head inside `A_C`, no chord of `K` is a diagonal of the tail child of `C`: the
banned set pulled back to that child is empty. -/
theorem pkR_d2_pull_tail {N : ℕ} {C : ℕ × ℕ} (hC : C ∈ oddDiagonals N) {K : Finset (ℕ × ℕ)}
    (hK : K ⊆ oddDiagonals N) (hKC : ∀ Q ∈ K, oddSide N Q ⊆ oddSide N C ∨ Crosses Q C) :
    pkRBPull N (tailStart C) (tailLen N C + 1) K = ∅ := by
  refine filter_false_of_mem fun d hd hQ => ?_
  have hd' := mem_diagonals.1 hd
  have b := pkR_b_odd_iff.1 hC
  have hT := pkR_b_tail_data hC
  obtain ⟨p1, p2, e, h1, h2⟩ := pkR_b_relab_eq (N := N) (s := tailStart C) (n := tailLen N C + 1)
    (by omega) (by omega) hd
  rw [e] at hQ
  have hQo := hK hQ
  rcases hKC _ hQ with hsub | hc
  · obtain ⟨t1, t2⟩ := C
    dsimp only at hT hd' b h1 h2
    have c := pkR_b_R17_tcore hQo hC hsub (by omega)
    omega
  · obtain ⟨t1, t2⟩ := C
    dsimp only at hT hd' b h1 h2
    unfold Crosses at hc
    dsimp only at hc
    omega

/-- **Crossing factor on `{X_Q = x, Q ∈ K}`:** unbanning the members `K ∖ K₀` multiplies the
non-member crossing product by `x` per member crossing `C`. -/
theorem pkR_d2_cross_eval {N : ℕ} {K K₀ : Finset (ℕ × ℕ)} {C : ℕ × ℕ} (hK : K ⊆ oddDiagonals N)
    (h0 : K₀ ⊆ K) {X : ℕ × ℕ → ℚ} {x : ℚ} (hx : ∀ Q ∈ K, X Q = x) :
    MvPolynomial.eval X (pkRBCross ℚ N K₀ C) =
      x ^ ((K \ K₀).filter (fun Q => Crosses Q C)).card * MvPolynomial.eval X (pkRBCross ℚ
          N K C) := by
  unfold pkRBCross
  have e : ((oddDiagonals N).filter (fun d => Crosses d C)) \ K₀ =
      ((K \ K₀).filter
          (fun Q => Crosses Q C)) ∪ (((oddDiagonals N).filter (fun d => Crosses d C)) \ K) := by
    ext d
    simp only [mem_sdiff, mem_filter, mem_union]
    constructor
    · rintro ⟨⟨hd, hc⟩, h0'⟩
      by_cases hdK : d ∈ K
      · exact Or.inl ⟨⟨hdK, h0'⟩, hc⟩
      · exact Or.inr ⟨⟨hd, hc⟩, hdK⟩
    · rintro (⟨⟨hdK, h0'⟩, hc⟩ | ⟨⟨hd, hc⟩, hdK⟩)
      · exact ⟨⟨hK hdK, hc⟩, h0'⟩
      · exact ⟨⟨hd, hc⟩, fun h => hdK (h0 h)⟩
  have hdisj : Disjoint ((K \ K₀).filter (fun Q => Crosses Q C))
      (((oddDiagonals N).filter (fun d => Crosses d C)) \ K) :=
    disjoint_left.2 fun d h1 h2 => (mem_sdiff.1 h2).2 (mem_sdiff.1 (mem_filter.1 h1).1).1
  have hc : Finset.prod ((K \ K₀).filter (fun Q => Crosses Q C)) (fun d => X d) =
      x ^ ((K \ K₀).filter (fun Q => Crosses Q C)).card := by
    rw [prod_congr rfl (fun Q hQ => hx Q (mem_sdiff.1 (mem_filter.1 hQ).1).1), prod_const]
  rw [e, prod_union hdisj, map_mul]
  congr 1
  rw [map_prod]
  simp only [MvPolynomial.eval_X]
  exact hc

/-- Members of `R` strictly above `Q` (heads `⊋ A_Q`). -/
def pkRD2Above (N : ℕ) (R : Finset (ℕ × ℕ)) (Q : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  R.filter (fun Q' => Q' ≠ Q ∧ oddSide N Q ⊆ oddSide N Q')

/-- Members of `R` crossing `Q`. -/
def pkRD2Crs (R : Finset (ℕ × ℕ)) (Q : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  R.filter (fun Q' => Crosses Q' Q)

/-- The top-down term of a member `Q` of the class `K` (value at `X`): full numerator of the head
child of `Q`, the ¬K numerator of its tail child (`a_Q`), and the non-member crossing chords of
`Q`. -/
noncomputable def pkRD2TopT (N : ℕ) (K : Finset (ℕ × ℕ)) (Q : ℕ × ℕ) (X : ℕ × ℕ → ℚ) : ℚ :=
  MvPolynomial.eval X (MvPolynomial.rename (relab N (headStart Q)) (NP ℚ (headLen N Q + 1))) *
    MvPolynomial.eval X (MvPolynomial.rename (relab N (tailStart Q))
      (pkRBNP ℚ (tailLen N Q + 1) (pkRBPull N (tailStart Q) (tailLen N Q + 1) K))) *
    MvPolynomial.eval X (pkRBCross ℚ N K Q)

/-- **Top-down expansion for a general class** (crossing members allowed), for even `N ≥ 4`. `K` a
set of odd chords in which non-crossing members are nested (the class, `pkR_b_chain`
(`C7`)), `X_Q = x` on `K`. For a down-closed `R ⊆ K` (the members not yet banned), peeling a member
of `R` with the largest head (`pkR_b_step`, `C8`) gives
`NP^{¬(K∖R)}_N = Σ_{Q∈R} x^{#above_R(Q) + #cross_R(Q)} · topT(Q) + x^{|R|} · NP^{¬K}_N` —
order-independent, since nested-above members have larger heads and a crossing member costs one `x`
whether banned first (prefactor) or later (crossing factor). -/
theorem pkR_d2_top_ind {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {K : Finset (ℕ × ℕ)}
    (hK : K ⊆ oddDiagonals N)
    (hnc : ∀ Q ∈ K, ∀ Q' ∈ K, ¬ Crosses Q' Q → oddSide N Q ⊆ oddSide N Q' ∨
        oddSide N Q' ⊆ oddSide N Q)
    {X : ℕ × ℕ → ℚ} {x : ℚ} (hx : ∀ Q ∈ K, X Q = x) (R : Finset (ℕ × ℕ)) (hRK : R ⊆ K)
    (hdown : ∀ Q ∈ R, ∀ Q' ∈ K, oddSide N Q' ⊆ oddSide N Q → Q' ∈ R) :
    MvPolynomial.eval X (pkRBNP ℚ N (K \ R)) =
      ∑ Q ∈ R, x ^ ((pkRD2Above N R Q).card + (pkRD2Crs R Q).card) * pkRD2TopT N K Q X +
        x ^ R.card * MvPolynomial.eval X (pkRBNP ℚ N K) := by
  induction R using Finset.strongInduction with
  | H R ih =>
  rcases R.eq_empty_or_nonempty with hR | hR
  · subst hR
    rw [sdiff_empty, sum_empty, card_empty, pow_zero, one_mul, zero_add]
  obtain ⟨Q, hQR, hmax⟩ := exists_max_image R (fun Q => (oddSide N Q).card) hR
  have hQK := hRK hQR
  have hQo := hK hQK
  have hsame : ∀ Q' ∈ R, oddSide N Q ⊆ oddSide N Q' → Q' = Q := fun Q' hQ' hs =>
    (pkR_d2_eq_of_head hQo (hK (hRK hQ')) (eq_of_subset_of_card_le hs (hmax Q' hQ'))).symm
  have hR'K : R.erase Q ⊆ K := (erase_subset Q R).trans hRK
  have hdown' : ∀ Q₁ ∈ R.erase Q, ∀ Q' ∈ K, oddSide N Q' ⊆ oddSide N Q₁ → Q' ∈ R.erase Q := by
    intro Q₁ hQ₁ Q' hQ' hs
    have hQ₁R := mem_of_mem_erase hQ₁
    refine mem_erase.2 ⟨fun h => ?_, hdown Q₁ hQ₁R Q' hQ' hs⟩
    rw [h] at hs
    exact ne_of_mem_erase hQ₁ (hsame Q₁ hQ₁R hs)
  have ih' := ih (R.erase Q) (erase_ssubset hQR) hR'K hdown'
  have hQn : Q ∉ K \ R := fun h => (mem_sdiff.1 h).2 hQR
  have hins : insert Q (K \ R) ⊆ oddDiagonals N := by
    intro d hd
    rcases mem_insert.1 hd with h | h
    · rw [h]
      exact hQo
    · exact hK (mem_sdiff.1 h).1
  have hstep := pkR_b_step (R := ℚ) hN hE hins hQn
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
  have hpullH : pkRBPull N (headStart Q) (headLen N Q + 1) (K \ R) = ∅ := by
    refine pkR_d2_pull_head hQo (fun d hd => hK (mem_sdiff.1 hd).1) fun Q' hQ' => ?_
    obtain ⟨hQ'K, hQ'R⟩ := mem_sdiff.1 hQ'
    by_cases hc : Crosses Q' Q
    · exact Or.inr hc
    · rcases hnc Q hQK Q' hQ'K hc with h | h
      · exact Or.inl h
      · exact absurd (hdown Q hQR Q' hQ'K h) hQ'R
  have hpullT : pkRBPull N (tailStart Q) (tailLen N Q + 1) (K \ R) =
      pkRBPull N (tailStart Q) (tailLen N Q + 1) K := by
    refine (pkR_b_pull_mono sdiff_subset ?_).symm
    rw [Finset.sdiff_sdiff_eq_self hRK]
    refine pkR_d2_pull_tail hQo (fun d hd => hK (hRK hd)) fun Q' hQ' => ?_
    by_cases hc : Crosses Q' Q
    · exact Or.inr hc
    · rcases hnc Q hQK Q' (hRK hQ') hc with h | h
      · rw [hsame Q' hQ' h]
        exact Or.inl subset_rfl
      · exact Or.inl h
  have hterm : MvPolynomial.eval X (pkRBTerm ℚ N (K \ R) Q) =
      x ^ (pkRD2Crs R Q).card * pkRD2TopT N K Q X := by
    unfold pkRBTerm pkRD2TopT
    rw [hpullH, pkR_b_NP_empty, hpullT, map_mul, map_mul, pkR_d2_cross_eval hK sdiff_subset hx,
      Finset.sdiff_sdiff_eq_self hRK]
    unfold pkRD2Crs
    ring
  have hQe : (pkRD2Above N R Q).card = 0 :=
    card_eq_zero.2 (filter_eq_empty_iff.2 fun Q' hQ' h => h.1 (hsame Q' hQ' h.2))
  have he : ∀ Q'' ∈ R.erase Q, (pkRD2Above N R Q'').card + (pkRD2Crs R Q'').card =
      (pkRD2Above N (R.erase Q) Q'').card + (pkRD2Crs (R.erase Q) Q'').card + 1 := by
    intro Q'' hQ''
    have hQ''R := mem_of_mem_erase hQ''
    have hne : Q'' ≠ Q := ne_of_mem_erase hQ''
    have hQ''o := hK (hRK hQ''R)
    have e1 : pkRD2Above N (R.erase Q) Q'' = (pkRD2Above N R Q'').erase Q := by
      unfold pkRD2Above
      rw [filter_erase]
    have e2 : pkRD2Crs (R.erase Q) Q'' = (pkRD2Crs R Q'').erase Q := by
      unfold pkRD2Crs
      rw [filter_erase]
    rw [e1, e2]
    by_cases hc : Crosses Q Q''
    · have hQc : Q ∈ pkRD2Crs R Q'' := mem_filter.2 ⟨hQR, hc⟩
      have hQa : Q ∉ pkRD2Above N R Q'' := fun h =>
        pkR_d2_cross_nsub hQ''o hQo (pkR_d2_cross_symm hc) (mem_filter.1 h).2.2
      rw [erase_eq_self.2 hQa, card_erase_of_mem hQc]
      have : 1 ≤ (pkRD2Crs R Q'').card := card_pos.2 ⟨Q, hQc⟩
      omega
    · have hs : oddSide N Q'' ⊆ oddSide N Q := by
        rcases hnc Q'' (hRK hQ''R) Q hQK hc with h | h
        · exact h
        · exact absurd (hsame Q'' hQ''R h) hne
      have hQa : Q ∈ pkRD2Above N R Q'' := mem_filter.2 ⟨hQR, fun h => hne h.symm, hs⟩
      have hQc : Q ∉ pkRD2Crs R Q'' := fun h => hc (mem_filter.1 h).2
      rw [erase_eq_self.2 hQc, card_erase_of_mem hQa]
      have : 1 ≤ (pkRD2Above N R Q'').card := card_pos.2 ⟨Q, hQa⟩
      omega
  have hsum : ∑ Q'' ∈ R.erase Q, x ^ ((pkRD2Above N R Q'').card + (pkRD2Crs R Q'').card) *
      pkRD2TopT N K Q'' X = x * ∑ Q'' ∈ R.erase Q, x ^ ((pkRD2Above N (R.erase Q) Q'').card +
        (pkRD2Crs (R.erase Q) Q'').card) * pkRD2TopT N K Q'' X := by
    rw [mul_sum]
    refine sum_congr rfl fun Q'' hQ'' => ?_
    rw [he Q'' hQ'', pow_succ]
    ring
  have hcard : R.card = (R.erase Q).card + 1 := by
    rw [card_erase_of_mem hQR]
    have := card_pos.2 hR
    omega
  rw [hstep, map_add, map_mul, MvPolynomial.eval_X, hx Q hQK, ih', hterm, ← add_sum_erase R _ hQR,
      hQe, zero_add,
    hsum, hcard, pow_succ]
  ring

/-- Members of `R` strictly below `Q` (heads `⊊ A_Q`). -/
def pkRD2Below (N : ℕ) (R : Finset (ℕ × ℕ)) (Q : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  R.filter (fun Q' => Q' ≠ Q ∧ oddSide N Q' ⊆ oddSide N Q)

/-- **Partition of a class around a member:** in a set `K` of odd chords in which non-crossing
members are nested, every other member is strictly above, strictly below, or crossing:
`#above + #cross + #below + 1 = |K|`. -/
theorem pkR_d2_part {N : ℕ} {K : Finset (ℕ × ℕ)} (hK : K ⊆ oddDiagonals N)
    (hnc : ∀ Q ∈ K, ∀ Q' ∈ K, ¬ Crosses Q' Q → oddSide N Q ⊆ oddSide N Q' ∨
        oddSide N Q' ⊆ oddSide N Q)
    {Q : ℕ × ℕ} (hQ : Q ∈ K) :
    (pkRD2Above N K Q).card + (pkRD2Crs K Q).card + (pkRD2Below N K Q).card + 1 = K.card := by
  have h1 : ∀ Q' ∈ K,
      ((if (Q' ≠ Q ∧ oddSide N Q ⊆ oddSide N Q') then 1 else 0) + (if Crosses Q' Q then 1 else 0) +
      (if (Q' ≠ Q ∧ oddSide N Q' ⊆ oddSide N Q) then 1 else 0) + (if Q' =
          Q then 1 else 0) : ℕ) = 1 := by
    intro Q' hQ'
    by_cases hc : Crosses Q' Q
    · have n1 : ¬ oddSide N Q ⊆ oddSide N Q' := pkR_d2_cross_nsub (hK hQ) (hK hQ')
        (pkR_d2_cross_symm hc)
      have n2 : ¬ oddSide N Q' ⊆ oddSide N Q := pkR_d2_cross_nsub (hK hQ') (hK hQ) hc
      have n3 : Q' ≠ Q := fun h => by
        rw [h] at hc
        unfold Crosses at hc
        omega
      simp [hc, n1, n2, n3]
    · by_cases he : Q' = Q
      · subst he
        simp [hc]
      · rcases hnc Q hQ Q' hQ' hc with h | h
        · have n2 : ¬ oddSide N Q' ⊆ oddSide N Q := fun h' =>
            he (pkR_d2_eq_of_head (hK hQ') (hK hQ) (Subset.antisymm h' h))
          simp [hc, he, h, n2]
        · have n1 : ¬ oddSide N Q ⊆ oddSide N Q' := fun h' =>
            he (pkR_d2_eq_of_head (hK hQ') (hK hQ) (Subset.antisymm h h'))
          simp [hc, he, h, n1]
  unfold pkRD2Above pkRD2Crs pkRD2Below
  rw [card_filter, card_filter, card_filter, card_eq_sum_ones, ← sum_congr rfl h1, sum_add_distrib,
      sum_add_distrib,
    sum_add_distrib, sum_ite_eq']
  simp [hQ]

/-- The bottom-up term of a member `Q` (value at `X`): the ¬K numerator of the head child (`b_Q`),
the full numerator of the tail child, and the non-member crossing chords of `Q`. -/
noncomputable def pkRD2BotT (N : ℕ) (K : Finset (ℕ × ℕ)) (Q : ℕ × ℕ) (X : ℕ × ℕ → ℚ) : ℚ :=
  MvPolynomial.eval X (MvPolynomial.rename (relab N (headStart Q))
      (pkRBNP ℚ (headLen N Q + 1) (pkRBPull N (headStart Q) (headLen N Q + 1) K))) *
    MvPolynomial.eval X (MvPolynomial.rename (relab N (tailStart Q)) (NP ℚ (tailLen N Q + 1))) *
    MvPolynomial.eval X (pkRBCross ℚ N K Q)

/-- **Bottom-up expansion for a general class** (the mirror of `pkR_d2_top_ind`, under its
hypotheses on `N`, `K` and `x`): for an up-closed `R ⊆ K`, peeling a member of `R` with the smallest
head gives `NP^{¬(K∖R)}_N = Σ_{Q∈R} x^{#below_R(Q) + #cross_R(Q)} · botT(Q) + x^{|R|} · NP^{¬K}_N`.
-/
theorem pkR_d2_bot_ind {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {K : Finset (ℕ × ℕ)}
    (hK : K ⊆ oddDiagonals N)
    (hnc : ∀ Q ∈ K, ∀ Q' ∈ K, ¬ Crosses Q' Q → oddSide N Q ⊆ oddSide N Q' ∨
        oddSide N Q' ⊆ oddSide N Q)
    {X : ℕ × ℕ → ℚ} {x : ℚ} (hx : ∀ Q ∈ K, X Q = x) (R : Finset (ℕ × ℕ)) (hRK : R ⊆ K)
    (hup : ∀ Q ∈ R, ∀ Q' ∈ K, oddSide N Q ⊆ oddSide N Q' → Q' ∈ R) :
    MvPolynomial.eval X (pkRBNP ℚ N (K \ R)) =
      ∑ Q ∈ R, x ^ ((pkRD2Below N R Q).card + (pkRD2Crs R Q).card) * pkRD2BotT N K Q X +
        x ^ R.card * MvPolynomial.eval X (pkRBNP ℚ N K) := by
  induction R using Finset.strongInduction with
  | H R ih =>
  rcases R.eq_empty_or_nonempty with hR | hR
  · subst hR
    rw [sdiff_empty, sum_empty, card_empty, pow_zero, one_mul, zero_add]
  obtain ⟨Q, hQR, hmin⟩ := exists_min_image R (fun Q => (oddSide N Q).card) hR
  have hQK := hRK hQR
  have hQo := hK hQK
  have hsame : ∀ Q' ∈ R, oddSide N Q' ⊆ oddSide N Q → Q' = Q := fun Q' hQ' hs =>
    pkR_d2_eq_of_head (hK (hRK hQ')) hQo (eq_of_subset_of_card_le hs (hmin Q' hQ'))
  have hR'K : R.erase Q ⊆ K := (erase_subset Q R).trans hRK
  have hup' : ∀ Q₁ ∈ R.erase Q, ∀ Q' ∈ K, oddSide N Q₁ ⊆ oddSide N Q' → Q' ∈ R.erase Q := by
    intro Q₁ hQ₁ Q' hQ' hs
    have hQ₁R := mem_of_mem_erase hQ₁
    refine mem_erase.2 ⟨fun h => ?_, hup Q₁ hQ₁R Q' hQ' hs⟩
    rw [h] at hs
    exact ne_of_mem_erase hQ₁ (hsame Q₁ hQ₁R hs)
  have ih' := ih (R.erase Q) (erase_ssubset hQR) hR'K hup'
  have hQn : Q ∉ K \ R := fun h => (mem_sdiff.1 h).2 hQR
  have hins : insert Q (K \ R) ⊆ oddDiagonals N := by
    intro d hd
    rcases mem_insert.1 hd with h | h
    · rw [h]
      exact hQo
    · exact hK (mem_sdiff.1 h).1
  have hstep := pkR_b_step (R := ℚ) hN hE hins hQn
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
  have hpullT : pkRBPull N (tailStart Q) (tailLen N Q + 1) (K \ R) = ∅ := by
    refine pkR_d2_pull_tail hQo (fun d hd => hK (mem_sdiff.1 hd).1) fun Q' hQ' => ?_
    obtain ⟨hQ'K, hQ'R⟩ := mem_sdiff.1 hQ'
    by_cases hc : Crosses Q' Q
    · exact Or.inr hc
    · rcases hnc Q hQK Q' hQ'K hc with h | h
      · exact absurd (hup Q hQR Q' hQ'K h) hQ'R
      · exact Or.inl h
  have hpullH : pkRBPull N (headStart Q) (headLen N Q + 1) (K \ R) =
      pkRBPull N (headStart Q) (headLen N Q + 1) K := by
    refine (pkR_b_pull_mono sdiff_subset ?_).symm
    rw [Finset.sdiff_sdiff_eq_self hRK]
    refine pkR_d2_pull_head hQo (fun d hd => hK (hRK hd)) fun Q' hQ' => ?_
    by_cases hc : Crosses Q' Q
    · exact Or.inr hc
    · rcases hnc Q hQK Q' (hRK hQ') hc with h | h
      · exact Or.inl h
      · rw [hsame Q' hQ' h]
        exact Or.inl subset_rfl
  have hterm : MvPolynomial.eval X (pkRBTerm ℚ N (K \ R) Q) =
      x ^ (pkRD2Crs R Q).card * pkRD2BotT N K Q X := by
    unfold pkRBTerm pkRD2BotT
    rw [hpullT, pkR_b_NP_empty, hpullH, map_mul, map_mul, pkR_d2_cross_eval hK sdiff_subset hx,
      Finset.sdiff_sdiff_eq_self hRK]
    unfold pkRD2Crs
    ring
  have hQe : (pkRD2Below N R Q).card = 0 :=
    card_eq_zero.2 (filter_eq_empty_iff.2 fun Q' hQ' h => h.1 (hsame Q' hQ' h.2))
  have he : ∀ Q'' ∈ R.erase Q, (pkRD2Below N R Q'').card + (pkRD2Crs R Q'').card =
      (pkRD2Below N (R.erase Q) Q'').card + (pkRD2Crs (R.erase Q) Q'').card + 1 := by
    intro Q'' hQ''
    have hQ''R := mem_of_mem_erase hQ''
    have hne : Q'' ≠ Q := ne_of_mem_erase hQ''
    have hQ''o := hK (hRK hQ''R)
    have e1 : pkRD2Below N (R.erase Q) Q'' = (pkRD2Below N R Q'').erase Q := by
      unfold pkRD2Below
      rw [filter_erase]
    have e2 : pkRD2Crs (R.erase Q) Q'' = (pkRD2Crs R Q'').erase Q := by
      unfold pkRD2Crs
      rw [filter_erase]
    rw [e1, e2]
    by_cases hc : Crosses Q Q''
    · have hQc : Q ∈ pkRD2Crs R Q'' := mem_filter.2 ⟨hQR, hc⟩
      have hQa : Q ∉ pkRD2Below N R Q'' := fun h =>
        pkR_d2_cross_nsub hQo hQ''o hc (mem_filter.1 h).2.2
      rw [erase_eq_self.2 hQa, card_erase_of_mem hQc]
      have : 1 ≤ (pkRD2Crs R Q'').card := card_pos.2 ⟨Q, hQc⟩
      omega
    · have hs : oddSide N Q ⊆ oddSide N Q'' := by
        rcases hnc Q'' (hRK hQ''R) Q hQK hc with h | h
        · exact absurd (hsame Q'' hQ''R h) hne
        · exact h
      have hQa : Q ∈ pkRD2Below N R Q'' := mem_filter.2 ⟨hQR, fun h => hne h.symm, hs⟩
      have hQc : Q ∉ pkRD2Crs R Q'' := fun h => hc (mem_filter.1 h).2
      rw [erase_eq_self.2 hQc, card_erase_of_mem hQa]
      have : 1 ≤ (pkRD2Below N R Q'').card := card_pos.2 ⟨Q, hQa⟩
      omega
  have hsum : ∑ Q'' ∈ R.erase Q, x ^ ((pkRD2Below N R Q'').card + (pkRD2Crs R Q'').card) *
      pkRD2BotT N K Q'' X = x * ∑ Q'' ∈ R.erase Q, x ^ ((pkRD2Below N (R.erase Q) Q'').card +
        (pkRD2Crs (R.erase Q) Q'').card) * pkRD2BotT N K Q'' X := by
    rw [mul_sum]
    refine sum_congr rfl fun Q'' hQ'' => ?_
    rw [he Q'' hQ'', pow_succ]
    ring
  have hcard : R.card = (R.erase Q).card + 1 := by
    rw [card_erase_of_mem hQR]
    have := card_pos.2 hR
    omega
  rw [hstep, map_add, map_mul, MvPolynomial.eval_X, hx Q hQK, ih', hterm, ← add_sum_erase R _ hQR,
      hQe, zero_add,
    hsum, hcard, pow_succ]
  ring

/-- Legs of a head are legs. -/
theorem pkR_d2_side_bd {N : ℕ} {Q : ℕ × ℕ} (hQ : Q ∈ oddDiagonals N) {m : ℕ}
    (hm : m ∈ oddSide N Q) :
    1 ≤ m ∧ m ≤ N := by
  obtain ⟨q1, q2⟩ := Q
  have a := pkR_b_odd_iff.1 hQ
  rcases Nat.mod_two_eq_zero_or_one q1 with hq | hq
  · rw [pkR_b_headE hq] at hm
    omega
  · rw [pkR_b_headO hq] at hm
    omega

/-- Nesting of two chords below `Q`, read in positions from `headStart Q` (`N` even; `c`, `c′` odd
chords other than `Q` with heads in `A_Q`). -/
theorem pkR_d2_nest_iff {N : ℕ} (hE : N % 2 = 0) {Q c c' : ℕ × ℕ} (hQ : Q ∈ oddDiagonals N)
    (hc : c ∈ oddDiagonals N) (hc' : c' ∈ oddDiagonals N) (hsc : oddSide N c ⊆ oddSide N Q)
    (hsc' : oddSide N c' ⊆ oddSide N Q) (hnc : Q ≠ c) (hnc' : Q ≠ c') :
    oddSide N c ⊆ oddSide N c' ↔
      cycPos N (headStart Q) (headStart c') ≤ cycPos N (headStart Q) (headStart c) ∧
        cycPos N (headStart Q) (headStart c) + headLen N c ≤
          cycPos N (headStart Q) (headStart c') + headLen N c' := by
  have f1 := pkR_b_head_facts hE hQ
  have fc := pkR_b_head_facts hE hc
  obtain ⟨a1, a2, a3, a4⟩ := pkR_b_nest_pos hE hQ hc hsc hnc
  obtain ⟨b1, b2, b3, b4⟩ := pkR_b_nest_pos hE hQ hc' hsc' hnc'
  constructor
  · intro hs
    have m1 := (b4 (cycPos N (headStart Q) (headStart c)) (by omega)).1
      (hs ((a4 (cycPos N (headStart Q) (headStart c)) (by omega)).2 ⟨le_rfl, by omega⟩))
    have m2 := (b4 (cycPos N (headStart Q) (headStart c) + headLen N c - 1) (by omega)).1
      (hs ((a4 (cycPos N (headStart Q) (headStart c) + headLen N c - 1)
          (by omega)).2 ⟨by omega, by omega⟩))
    omega
  · intro h m hm
    have hb := pkR_d2_side_bd hQ (hsc hm)
    have hi : cycPos N (headStart Q) m < N := Nat.mod_lt _ (by omega)
    have hv := pkR_b_vtx_cyc (N := N) (s := headStart Q) (x := m) ⟨f1.1, f1.2.1⟩ hb
    rw [← hv] at hm ⊢
    have := (a4 _ hi).1 hm
    exact (b4 _ hi).2 ⟨by omega, by omega⟩

/-- The A-side term of `c` below `Q` (value at `X`): `b_c` (¬K numerator of the head child of `c`),
the full numerator of the region `Ω(Q, c)` at the region point (`pkRBOmX`, `C7`), and the
non-member crossing chords of the child chord of `c` in the head child of `Q`. -/
noncomputable def pkRD2AT (N : ℕ) (K : Finset (ℕ × ℕ)) (Q c : ℕ × ℕ) (X : ℕ × ℕ → ℚ) : ℚ :=
  MvPolynomial.eval X (MvPolynomial.rename (relab N (headStart c))
      (pkRBNP ℚ (headLen N c + 1) (pkRBPull N (headStart c) (headLen N c + 1) K))) *
    MvPolynomial.eval (pkRBOmX N Q c X) (NP ℚ (pkRBOmM N Q c)) *
    MvPolynomial.eval X (MvPolynomial.rename (relab N (headStart Q))
      (pkRBCross ℚ (headLen N Q + 1) (pkRBPull N (headStart Q) (headLen N Q + 1) K)
          (pkRBCc N Q c)))

/-- **A-side expansion for a general class** (`pkR_b_R2A` without the chain hypothesis): `N` even,
`K` a class-like set of odd chords (non-crossing members nested, a common leg `ℓ` in every head),
`Q ∈ K`, `X_Q = x` on `K`. The full numerator of the head child of `Q` is
`Σ_{c below Q} x^{#below(Q) − 1 − #between(Q, c)} · b_c · N_{Ω(Q,c)} · cr_c +
x^{#below(Q)} · NP^{¬K}_{A(Q)}` (`pkR_d2_bot_ind` in the child, exponents by `pkR_d2_part` in the
child, terms by the bridges of `C8` and of the first sections of this module). -/
theorem pkR_d2_Aside {N : ℕ} (hE : N % 2 = 0) {K : Finset (ℕ × ℕ)} (hK : K ⊆ oddDiagonals N)
    (hnc : ∀ Q ∈ K, ∀ Q' ∈ K, ¬ Crosses Q' Q → oddSide N Q ⊆ oddSide N Q' ∨
        oddSide N Q' ⊆ oddSide N Q)
    {ℓ : ℕ} (hℓ : ∀ c ∈ K, ℓ ∈ oddSide N c) {Q : ℕ × ℕ} (hQK : Q ∈ K) {X : ℕ × ℕ → ℚ} {x : ℚ}
    (hx : ∀ Q ∈ K, X Q = x) :
    MvPolynomial.eval X (MvPolynomial.rename (relab N (headStart Q)) (NP ℚ (headLen N Q + 1))) =
      ∑ c ∈ pkRD2Below N K Q,
          x ^ ((pkRD2Below N K Q).card - 1 -
              (pkRD2Above N (pkRD2Below N K Q) c).card) * pkRD2AT N K Q c X +
        x ^ (pkRD2Below N K Q).card * MvPolynomial.eval X (MvPolynomial.rename
            (relab N (headStart Q))
          (pkRBNP ℚ (headLen N Q + 1) (pkRBPull N (headStart Q) (headLen N Q + 1) K))) := by
  have hQo := hK hQK
  have f1 := pkR_b_head_facts hE hQo
  have hKQK : pkRD2Below N K Q ⊆ K := filter_subset _ _
  have hKQ : ∀ c ∈ pkRD2Below N K Q, c ≠ Q ∧ oddSide N c ⊆ oddSide N Q :=
      fun c hc => (mem_filter.1 hc).2
  have np := fun c (hc : c ∈ pkRD2Below N K Q) =>
    pkR_b_nest_pos hE hQo (hK (hKQK hc)) (hKQ c hc).2 (hKQ c hc).1.symm
  have fc := fun c (hc : c ∈ pkRD2Below N K Q) => pkR_b_head_facts hE (hK (hKQK hc))
  have hrel : ∀ c ∈ pkRD2Below N K Q, relab N (headStart Q) (pkRBCc N Q c) = c := by
    intro c hc
    obtain ⟨a1, a2, a3, -⟩ := np c hc
    exact pkR_b_relab_head (hK (hKQK hc)) ⟨f1.1, f1.2.1⟩ (by omega)
      (pkR_b_vtx_cyc ⟨f1.1, f1.2.1⟩ ⟨(fc c hc).1, (fc c hc).2.1⟩)
  have hC' : ∀ c ∈ pkRD2Below N K Q, pkRBCc N Q c ∈ oddDiagonals (headLen N Q + 1) := by
    intro c hc
    obtain ⟨a1, a2, a3, -⟩ := np c hc
    have b := fc c hc
    exact pkR_b_odd_iff.2 ⟨by omega, by omega, by omega, by omega, by omega⟩
  have hS : ∀ c ∈ pkRD2Below N K Q, oddSide (headLen N Q + 1) (pkRBCc N Q c) =
      Icc (cycPos N (headStart Q) (headStart c) + 1)
          (cycPos N (headStart Q) (headStart c) + headLen N c) :=
    fun c hc => pkR_b_oS1 (np c hc).1
  have hinj : Set.InjOn (pkRBCc N Q) ↑(pkRD2Below N K Q) := fun c hc c' hc' e =>
    (hrel c hc).symm.trans ((congrArg (relab N (headStart Q)) e).trans (hrel c' hc'))
  have hKcI : pkRBPull N (headStart Q) (headLen N Q + 1) K =
      (pkRD2Below N K Q).image (pkRBCc N Q) := by
    have h1 : pkRBPull N (headStart Q) (headLen N Q + 1) K =
        pkRBPull N (headStart Q) (headLen N Q + 1) (pkRD2Below N K Q) := by
      refine pkR_b_pull_mono hKQK (pkR_d2_pull_head hQo (fun d hd =>
          hK (mem_sdiff.1 hd).1) fun Q' hQ' => ?_)
      obtain ⟨hQ'K, hQ'n⟩ := mem_sdiff.1 hQ'
      by_cases hc : Crosses Q' Q
      · exact Or.inr hc
      · rcases hnc Q hQK Q' hQ'K hc with h | h
        · exact Or.inl h
        · by_cases he : Q' = Q
          · rw [he]
            exact Or.inl subset_rfl
          · exact absurd (mem_filter.2 ⟨hQ'K, he, h⟩) hQ'n
    rw [h1, pkR_b_pull_head hE hQo (fun d hd => hK (hKQK hd)) (fun d hd => (hKQ d hd).2),
      erase_eq_self.2 (fun h => (hKQ Q h).1 rfl)]
    rfl
  have hcardKc : (pkRBPull N (headStart Q) (headLen N Q + 1) K).card =
      (pkRD2Below N K Q).card := by
    rw [hKcI, card_image_of_injOn hinj]
  have hKco : pkRBPull N (headStart Q) (headLen N Q + 1) K ⊆ oddDiagonals (headLen N Q + 1) := by
    rw [hKcI]
    intro d hd
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hd
    exact hC' c hc
  have hxc : ∀ d ∈ pkRBPull N (headStart Q) (headLen N Q + 1) K,
      (X ∘ relab N (headStart Q)) d = x := by
    rw [hKcI]
    intro d hd
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hd
    change X (relab N (headStart Q) (pkRBCc N Q c)) = x
    rw [hrel c hc]
    exact hx c (hKQK hc)
  have hncc : ∀ d ∈ pkRBPull N (headStart Q) (headLen N Q + 1) K,
      ∀ d' ∈ pkRBPull N (headStart Q) (headLen N Q + 1) K, ¬ Crosses d' d →
        oddSide (headLen N Q + 1) d ⊆ oddSide (headLen N Q + 1) d' ∨
          oddSide (headLen N Q + 1) d' ⊆ oddSide (headLen N Q + 1) d := by
    rw [hKcI]
    intro d hd d' hd' hcr
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hd
    obtain ⟨c', hc', rfl⟩ := mem_image.1 hd'
    obtain ⟨a1, a2, a3, a4⟩ := np c hc
    obtain ⟨b1, b2, b3, b4⟩ := np c' hc'
    have hb := pkR_d2_side_bd hQo ((hKQ c hc).2 (hℓ c (hKQK hc)))
    have hi : cycPos N (headStart Q) ℓ < N := Nat.mod_lt _ (by omega)
    have hv := pkR_b_vtx_cyc (N := N) (s := headStart Q) (x := ℓ) ⟨f1.1, f1.2.1⟩ hb
    have i1 := (a4 _ hi).1 (by rw [hv]; exact hℓ c (hKQK hc))
    have i2 := (b4 _ hi).1 (by rw [hv]; exact hℓ c' (hKQK hc'))
    rw [hS c hc, hS c' hc']
    have e : ∀ c₀, pkRBCc N Q c₀ = (cycPos N (headStart Q) (headStart c₀) + 1,
        cycPos N (headStart Q) (headStart c₀) + headLen N c₀ + 1) := fun _ => rfl
    rw [e c, e c'] at hcr
    unfold Crosses at hcr
    dsimp only at hcr
    have fcc := fc c hc
    have fcc' := fc c' hc'
    by_cases h : cycPos N (headStart Q) (headStart c') ≤ cycPos N (headStart Q) (headStart c) ∧
        cycPos N (headStart Q) (headStart c) + headLen N c ≤ cycPos N (headStart Q)
            (headStart c') + headLen N c'
    · exact Or.inl (Icc_subset_Icc (by omega) (by omega))
    · exact Or.inr (Icc_subset_Icc (by omega) (by omega))
  have habove : ∀ c ∈ pkRD2Below N K Q,
      (pkRD2Above (headLen N Q + 1) (pkRBPull N (headStart Q) (headLen N Q + 1) K)
          (pkRBCc N Q c)).card =
        (pkRD2Above N (pkRD2Below N K Q) c).card := by
    intro c hc
    have e : pkRD2Above (headLen N Q + 1) (pkRBPull N (headStart Q) (headLen N Q + 1) K)
        (pkRBCc N Q c) =
        (pkRD2Above N (pkRD2Below N K Q) c).image (pkRBCc N Q) := by
      unfold pkRD2Above
      rw [hKcI, filter_image]
      congr 1
      refine filter_congr fun c' hc' => ?_
      obtain ⟨a1, a2, a3, -⟩ := np c hc
      obtain ⟨b1, b2, b3, -⟩ := np c' hc'
      have fcc := fc c hc
      have hn := pkR_d2_nest_iff hE hQo (hK (hKQK hc)) (hK (hKQK hc')) (hKQ c hc).2 (hKQ c' hc').2
        (hKQ c hc).1.symm (hKQ c' hc').1.symm
      rw [hS c hc, hS c' hc', Icc_subset_Icc_iff (by omega), hn]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun e' => h1 (by rw [e']), by omega⟩
      · rintro ⟨h1, h2⟩
        exact ⟨fun e' => h1 (hinj hc' hc e'), by omega⟩
    have hsub : pkRD2Above N (pkRD2Below N K Q) c ⊆ pkRD2Below N K Q := filter_subset _ _
    rw [e, card_image_of_injOn (hinj.mono (coe_subset.2 hsub))]
  have hexp : ∀ c ∈ pkRD2Below N K Q,
      (pkRD2Below (headLen N Q + 1) (pkRBPull N (headStart Q) (headLen N Q + 1) K)
          (pkRBCc N Q c)).card +
        (pkRD2Crs (pkRBPull N (headStart Q) (headLen N Q + 1) K) (pkRBCc N Q c)).card =
      (pkRD2Below N K Q).card - 1 - (pkRD2Above N (pkRD2Below N K Q) c).card := by
    intro c hc
    have hd : pkRBCc N Q c ∈ pkRBPull N (headStart Q) (headLen N Q + 1) K := by
      rw [hKcI]
      exact mem_image_of_mem _ hc
    have hp := pkR_d2_part hKco hncc hd
    rw [habove c hc, hcardKc] at hp
    omega
  have hbi := pkR_d2_bot_ind (N := headLen N Q + 1) (by omega) (by omega) hKco hncc hxc
    (pkRBPull N (headStart Q) (headLen N Q + 1) K) subset_rfl (fun d hd d' hd' _ => hd')
  rw [Finset.sdiff_self, pkR_b_NP_empty] at hbi
  have hL : MvPolynomial.eval X (MvPolynomial.rename (relab N (headStart Q))
      (NP ℚ (headLen N Q + 1))) =
      MvPolynomial.eval (X ∘ relab N (headStart Q)) (NP ℚ (headLen N Q + 1)) :=
          MvPolynomial.eval_rename _ _ _
  rw [hL, hbi, hcardKc]
  refine congrArg₂ (· + ·) ((sum_congr hKcI fun _ _ => rfl).trans ?_)
      (by rw [MvPolynomial.eval_rename])
  rw [sum_image hinj]
  refine sum_congr rfl fun c hc => ?_
  rw [hexp c hc]
  obtain ⟨a1, a2, a3, -⟩ := np c hc
  have fci := fc c hc
  have hd := pkR_b_cc_data (n := headLen N Q + 1) Q c a1
  unfold pkRD2BotT pkRD2AT
  refine congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ ?_)
      (MvPolynomial.eval_rename _ _ _).symm)
  · rw [hd.1, hd.2.1,
      pkR_b_pull_comp (N := N) (s := headStart Q) (n := headLen N Q + 1)
        (p := cycPos N (headStart Q) (headStart c)) (L' := headLen N c) ⟨f1.1, f1.2.1⟩ (by omega)
        (by omega) (by omega),
      pkR_b_vtx_cyc ⟨f1.1, f1.2.1⟩ ⟨fci.1, fci.2.1⟩, MvPolynomial.eval_rename,
          MvPolynomial.eval_rename]
    refine pkR_b_NPK_local _ (fun d hd' => ?_)
    have hdd := mem_diagonals.1 hd'
    change X (relab N (headStart Q)
        (relab (headLen N Q + 1) (cycPos N (headStart Q) (headStart c) + 1) d)) =
      X (relab N (headStart c) d)
    rw [pkR_b_relab_comp (N := N) (s := headStart Q) (n := headLen N Q + 1)
      (p := cycPos N (headStart Q) (headStart c)) (d := d) ⟨f1.1, f1.2.1⟩ (by omega)
          (by omega) (by omega),
      pkR_b_vtx_cyc ⟨f1.1, f1.2.1⟩ ⟨fci.1, fci.2.1⟩]
  · rw [← MvPolynomial.eval_rename, hd.2.2.1, hd.2.2.2,
      show headLen N Q + 1 - headLen N c + 1 = headLen N Q - headLen N c + 2 by omega]
    exact pkR_b_omega_relab (N := N) (a := headStart Q) (p := cycPos N (headStart Q) (headStart c))
      (L := headLen N Q) (L' := headLen N c)
          ⟨f1.1, f1.2.1⟩ a1 f1.2.2.2.1 fci.2.2.2.1 (by omega) (by omega)
      (by omega) X

/-- **Count of the powers of `x` for a general class** (scalar form at one point; generalises
`pkR_d_count`: per-term exponents, crossing members allowed), for `κ = |K| ≥ 1`. `h1` =
`pkR_d2_top_ind` at `R = K` (`e Q = #above + #cross`), `he` = `pkR_d2_part`, `h2` = `pkR_d2_Aside`
(`bl Q = #below(Q)`, `f Q c = #between(Q, c)`, with `f Q c + 1 ≤ bl Q`), `h3` = the Ω formula
(`pkR_omega`) at the Ω point with `f Q c` interior members. Then `NP = x^{κ−1} · g`. -/
theorem pkR_d2_count {ι : Type*} (K : Finset ι) (hκ : 1 ≤ K.card) (x M NPv : ℚ) (e bl : ι → ℕ)
    (A a cr B : ι → ℚ) (S : ι → Finset ι) (f : ι → ι → ℕ) (b W cr2 c D F : ι → ι → ℚ)
    (h1 : NPv = ∑ Q ∈ K, x ^ e Q * (A Q * a Q * cr Q) + x ^ K.card * M)
    (he : ∀ Q ∈ K, e Q + bl Q + 1 = K.card)
    (h2 : ∀ Q ∈ K, A Q = ∑ c' ∈ S Q, x ^ (bl Q - 1 - f Q c') * (b Q c' * W Q c' * cr2 Q c') +
        x ^ bl Q * B Q)
    (hf : ∀ Q ∈ K, ∀ c' ∈ S Q, f Q c' + 1 ≤ bl Q)
    (h3 : ∀ Q ∈ K, ∀ c' ∈ S Q, W Q c' = x ^ f Q c' * (c Q c' * x * D Q c' + x ^ 2 * F Q c')) :
    NPv = x ^ (K.card - 1) * (∑ Q ∈ K, a Q * cr Q *
      (∑ c' ∈ S Q, b Q c' * (c Q c' * D Q c' + x * F Q c') * cr2 Q c' + B Q) + x * M) := by
  rw [h1, mul_add, mul_sum]
  congr 1
  · refine sum_congr rfl fun Q hQ => ?_
    rw [h2 Q hQ]
    have hs : x ^ e Q * ∑ c' ∈ S Q, x ^ (bl Q - 1 - f Q c') * (b Q c' * W Q c' * cr2 Q c') =
        x ^ (K.card - 1) * ∑ c' ∈ S Q, b Q c' * (c Q c' * D Q c' + x * F Q c') * cr2 Q c' := by
      rw [mul_sum, mul_sum]
      refine sum_congr rfl fun c' hc' => ?_
      have k1 := he Q hQ
      have k2 := hf Q hQ c' hc'
      rw [h3 Q hQ c' hc', show K.card - 1 = e Q + (bl Q - 1 - f Q c') + f Q c' + 1 by omega,
          pow_add, pow_add,
        pow_add]
      ring
    have hb : x ^ e Q * x ^ bl Q = x ^ (K.card - 1) := by
      rw [← pow_add]
      congr 1
      have := he Q hQ
      omega
    calc x ^ e Q * ((∑ c' ∈ S Q, x ^ (bl Q - 1 - f Q c') * (b Q c' * W Q c' * cr2 Q c') +
        x ^ bl Q * B Q) *
          a Q * cr Q) =
          (x ^ e Q * ∑ c' ∈ S Q, x ^ (bl Q - 1 - f Q c') *
              (b Q c' * W Q c' * cr2 Q c')) * a Q * cr Q +
            (x ^ e Q * x ^ bl Q) * B Q * a Q * cr Q := by ring
      _ = _ := by
          rw [hs, hb]
          ring
  · have e2 : x ^ K.card = x ^ (K.card - 1) * x := by
      rw [← pow_succ]
      congr 1
      omega
    rw [e2]
    ring

/-- **Value on `H`** of the `pkR_d2_count` factor (`x = 0`) under (E): `a_Q = 0` for `Q ≠ t`,
`b_c = 0` for `c ≠ b` below `t`, `B_t = b_t = 0` (`t ≠ b`): only the `(t, b)` term survives, with
`ε = c t b` (the constant of the Ω formula). -/
theorem pkR_d2_countH {ι : Type*} (K : Finset ι) (t b₀ : ι) (ht : t ∈ K) (M : ℚ) (a cr B : ι → ℚ)
    (S : ι → Finset ι) (hb : b₀ ∈ S t) (b cr2 c D F : ι → ι → ℚ) (ha : ∀ Q ∈ K, Q ≠ t → a Q = 0)
    (hbv : ∀ c' ∈ S t, c' ≠ b₀ → b t c' = 0) (hB : B t = 0) :
    ∑ Q ∈ K, a Q * cr Q * (∑ c' ∈ S Q, b Q c' * (c Q c' * D Q c' + 0 * F Q c') *
        cr2 Q c' + B Q) + 0 * M =
      c t b₀ * a t * b t b₀ * (cr t * D t b₀ * cr2 t b₀) := by
  rw [sum_eq_single_of_mem t ht (fun Q hQ hQt => by rw [ha Q hQ hQt, zero_mul, zero_mul]),
    sum_eq_single_of_mem b₀ hb (fun c' hc' hcb => by rw [hbv c' hc' hcb, zero_mul, zero_mul]), hB]
  ring

/-- **Value on `H`**, `t = b` (`S t = ∅`: nothing below the top), given `a_Q = 0` for `Q ≠ t`:
`g = a_t · cr_t · b_t`. -/
theorem pkR_d2_countH1 {ι : Type*} (K : Finset ι) (t : ι) (ht : t ∈ K) (M : ℚ) (a cr B : ι → ℚ)
    (S : ι → Finset ι) (hS : S t = ∅) (b cr2 c D F : ι → ι → ℚ) (ha : ∀ Q ∈ K, Q ≠ t → a Q = 0) :
    ∑ Q ∈ K, a Q * cr Q * (∑ c' ∈ S Q, b Q c' * (c Q c' * D Q c' + 0 * F Q c') *
        cr2 Q c' + B Q) + 0 * M =
      a t * cr t * B t := by
  rw [sum_eq_single_of_mem t ht (fun Q hQ hQt => by rw [ha Q hQ hQt, zero_mul, zero_mul]),
      hS, sum_empty]
  ring

/-- `minRect(P)` of an odd chord consists of diagonals (no adjacent pair: the end legs of the head
are odd). -/
theorem pkR_d2_minRect_diag {N : ℕ} {P : ℕ × ℕ} (hP : P ∈ oddDiagonals N) {q : ℕ × ℕ}
    (hq : q ∈ minRect N P) :
    q ∈ diagonals N := by
  obtain ⟨e, he, o, ho, rfl⟩ := pkCh_mem_minRect.1 hq
  obtain ⟨p1, p2⟩ := P
  have a := pkR_b_odd_iff.1 hP
  obtain ⟨he1, he2⟩ := mem_filter.1 he
  obtain ⟨ho1, ho2⟩ := mem_filter.1 ho
  have ho3 := mem_sdiff.1 ho1
  rw [mem_Icc] at ho3
  refine mem_diagonals.2 ?_
  dsimp only
  rcases Nat.mod_two_eq_zero_or_one p1 with hq1 | hq1
  · rw [pkR_b_headE hq1] at he1 ho3
    omega
  · rw [pkR_b_headO hq1] at he1 ho3
    omega

/-- Two odd chords below `Q` (other than `Q`, heads in `A_Q`, `N` even) with the same position from
`headStart Q` and the same head length are equal. -/
theorem pkR_d2_pos_eq {N : ℕ} (hE : N % 2 = 0) {Q c c' : ℕ × ℕ} (hQ : Q ∈ oddDiagonals N)
    (hc : c ∈ oddDiagonals N) (hc' : c' ∈ oddDiagonals N) (hsc : oddSide N c ⊆ oddSide N Q)
    (hsc' : oddSide N c' ⊆ oddSide N Q) (hnc : Q ≠ c) (hnc' : Q ≠ c')
    (hp : cycPos N (headStart Q) (headStart c) = cycPos N (headStart Q) (headStart c'))
    (hl : headLen N c = headLen N c') : c = c' := by
  have h1 := (pkR_d2_nest_iff hE hQ hc hc' hsc hsc' hnc hnc').2 ⟨by omega, by omega⟩
  have h2 := (pkR_d2_nest_iff hE hQ hc' hc hsc' hsc hnc' hnc).2 ⟨by omega, by omega⟩
  exact pkR_d2_eq_of_head hc hc' (Subset.antisymm h1 h2)

set_option maxHeartbeats 800000 in
-- one proof of about 90 lines (two `simp` calls, six `omega` calls): 641,724 heartbeats
/-- **The Ω formula at the Ω point of two class members**: for even `N ≥ 6` and `c` strictly below
`Q` in the class of `t`, there are `ε ≠ 0` and `F` such that on `L_S` the full numerator of
`Ω(Q, c)` at the region point (`pkRBOmX`, `C7`) is `x^{|J|} · (ε · x · D′ + x² · F)` with
`x = X_Q` and `J` = the members strictly between (`pkRD2Above` of `c` among the members below
`Q`); `D′` is the product of the odd chords of the region other than the member chords of `J`. The
proof is `pkR_omega` with `pkR_b_omegaHyp` (`C7`; (H3a), and (H3b) = `pkR_d_H3b`) and
`pkR_b_omegaLam` (`C8`). -/
theorem pkR_d2_omegaQ {N : ℕ} (hN : 6 ≤ N) (hE : N % 2 = 0) {S : Finset (ℕ × ℕ)} {t Q c : ℕ × ℕ}
    (hQ : Q ∈ hitClass N S t) (hc : c ∈ hitClass N S t) (hsub : oddSide N c ⊆ oddSide N Q)
    (hne : Q ≠ c) :
    ∃ (ε : ℚ) (F : MvPolynomial (ℕ × ℕ) ℚ), ε ≠ 0 ∧ ∀ X : ℕ × ℕ → ℚ, OnLocus N S X →
      MvPolynomial.eval (pkRBOmX N Q c X) (NP ℚ (pkRBOmM N Q c)) =
        X Q ^ (pkRD2Above N (pkRD2Below N (hitClass N S t) Q) c).card *
          (ε * X Q * Finset.prod ((oddDiagonals (pkRBOmM N Q c)).filter (fun Q' => Q' ∉
              ((pkRD2Above N (pkRD2Below N (hitClass N S t) Q) c).image (pkRBOmI N Q c)).image
                (pkRMchord (pkRBOmD N Q c)))) (fun Q' => pkRBOmX N Q c X Q') +
            X Q ^ 2 * MvPolynomial.eval (pkRBOmX N Q c X) F) := by
  have hQo := (pkR_b_H3a hQ).1
  have hco := (pkR_b_H3a hc).1
  have f1 := pkR_b_head_facts hE hQo
  have fc := pkR_b_head_facts hE hco
  obtain ⟨p0, p1, p2, -⟩ := pkR_b_nest_pos hE hQo hco hsub hne
  have hm : pkRBOmM N Q c % 2 = 0 := by
    change (headLen N Q - headLen N c + 2) % 2 = 0
    omega
  have hm4 : 4 ≤ pkRBOmM N Q c := by
    change 4 ≤ headLen N Q - headLen N c + 2
    omega
  have hd : 2 * pkRBOmD N Q c + 2 ≤ pkRBOmM N Q c := by
    change 2 * (cycPos N (headStart Q) (headStart c) / 2) + 2 ≤ headLen N Q - headLen N c + 2
    omega
  -- the members strictly between
  have hJ : ∀ Q'' ∈ pkRD2Above N (pkRD2Below N (hitClass N S t) Q) c,
      Q'' ∈ hitClass N S t ∧ (Q'' ≠ Q ∧ oddSide N Q'' ⊆ oddSide N Q) ∧
          (Q'' ≠ c ∧ oddSide N c ⊆ oddSide N Q'') := by
    intro Q'' h
    obtain ⟨h1, h2⟩ := mem_filter.1 h
    obtain ⟨h3, h4⟩ := mem_filter.1 h1
    exact ⟨h3, h4, h2⟩
  have hpos : ∀ Q'' ∈ pkRD2Above N (pkRD2Below N (hitClass N S t) Q) c,
      Q'' ∈ oddDiagonals N ∧ cycPos N (headStart Q) (headStart Q'') % 2 = 0 ∧
        cycPos N (headStart Q) (headStart Q'') + headLen N Q'' ≤ headLen N Q ∧ headLen N Q'' + 2 ≤
            headLen N Q ∧
        headLen N Q'' % 2 = 1 ∧
        cycPos N (headStart Q) (headStart Q'') ≤ cycPos N (headStart Q) (headStart c) ∧
        cycPos N (headStart Q) (headStart c) + headLen N c ≤ cycPos N (headStart Q)
            (headStart Q'') + headLen N Q'' := by
    intro Q'' h
    obtain ⟨h1, ⟨h2, h3⟩, ⟨h4, h5⟩⟩ := hJ Q'' h
    have ho := (pkR_b_H3a h1).1
    obtain ⟨q0, q1, q2, -⟩ := pkR_b_nest_pos hE hQo ho h3 (fun e => h2 e.symm)
    have hn := (pkR_d2_nest_iff hE hQo hco ho hsub h3 hne (fun e => h2 e.symm)).1 h5
    exact ⟨ho, q0, q1, q2, (pkR_b_head_facts hE ho).2.2.2.1, hn⟩
  have hinjI : Set.InjOn (pkRBOmI N Q c) ↑(pkRD2Above N
      (pkRD2Below N (hitClass N S t) Q) c) := by
    intro Q₁ h₁ Q₂ h₂ e
    obtain ⟨o1, a1, b1, -, d1, -, g1⟩ := hpos Q₁ h₁
    obtain ⟨o2, a2, b2, -, d2, -, g2⟩ := hpos Q₂ h₂
    have e1 := congrArg Prod.fst e
    have e2 := congrArg Prod.snd e
    simp only [pkRBOmI] at e1 e2
    obtain ⟨-, ⟨n1, s1⟩, -⟩ := hJ Q₁ h₁
    obtain ⟨-, ⟨n2, s2⟩, -⟩ := hJ Q₂ h₂
    exact pkR_d2_pos_eq hE hQo o1 o2 s1 s2 (fun e' => n1 e'.symm) (fun e' => n2 e'.symm)
        (by omega) (by omega)
  have hI : ∀ I ∈ (pkRD2Above N (pkRD2Below N (hitClass N S t) Q) c).image (pkRBOmI N Q c),
      pkRIsMem (pkRBOmM N Q c) (pkRBOmD N Q c) I := by
    intro I hI'
    obtain ⟨Q'', h, rfl⟩ := mem_image.1 hI'
    obtain ⟨o, a1, a2, a3, a4, a5, a6⟩ := hpos Q'' h
    obtain ⟨-, ⟨n1, s1⟩, ⟨n2, s2⟩⟩ := hJ Q'' h
    have hne1 : ¬ (cycPos N (headStart Q) (headStart Q'') = cycPos N (headStart Q) (headStart c) ∧
        headLen N Q'' = headLen N c) := fun ⟨e1, e2⟩ =>
      n2 (pkR_d2_pos_eq hE hQo o hco s1 hsub (fun e' => n1 e'.symm) hne e1 e2)
    refine (pkR_isMem_iff _ _ _).2 ?_
    simp only [pkRBOmI, pkRBOmM, pkRBOmD]
    omega
  obtain ⟨ε, F, hε, hΩ⟩ := pkR_omega hm hm4 (pkRBOmD N Q c) hd _ hI
  refine ⟨ε, F, hε, fun X hX => ?_⟩
  have hT : ∀ a b, (a, b) ∈ diagonals N → pkRBTP N Q c a b → mesh N X a b = 0 :=
      fun a b hab hTP =>
    hX _ (pkR_b_omegaHyp hsub (pkR_b_H3a hQ).2 (pkR_b_H3a hc).2 (pkR_d_H3b hN hE hQ hc).1
        (pkR_d_H3b hN hE hQ hc).2
      hab hTP)
  have hlam := pkR_b_omegaLam hE hQo hco hsub hne hT (J :=
      pkRD2Above N (pkRD2Below N (hitClass N S t) Q) c)
    (fun Q'' h => by
      obtain ⟨o, -⟩ := hpos Q'' h
      obtain ⟨h1, ⟨n1, s1⟩, ⟨-, s2⟩⟩ := hJ Q'' h
      refine ⟨o, s2, s1, fun e => n1 e.symm, fun q hq => hX _ ?_⟩
      by_contra hqS
      exact disjoint_left.1 (pkR_b_H3a h1).2 hq (mem_sdiff.2 ⟨pkR_d2_minRect_diag o hq, hqS⟩))
  have hx := (pkR_b_omegaTiles hE hQo hco hsub hne hT).2.1
  rw [hΩ _ hlam, hx, card_image_of_injOn hinjI]


end PionCompleteness.Pi
