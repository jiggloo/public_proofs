/-
Copyright (c) 2026 Henru Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henru Wang
-/
module

public import PionCompleteness.Paper

/-!
# The conventions of `𝒜_N` against an outside source

`calA` (`𝒜_N`, module `C0`) is defined from the δ-shift of the φ³ amplitude, as in arXiv:2312.16282.
The library's other checks of it (`calA_four`, `calA_six = paper43`, and `theoremB`, which relates
it to the quartic sum `Qpi`) use the same variables `X` and conventions set by the same authors, so
a slip in sign, normalisation or leg labels made the same way in all of them would pass. This
module checks `calA` against closed forms from a source with its own derivation and its own
variables: the stripped tree amplitudes of the chiral nonlinear sigma model computed from Feynman
diagrams of the Lagrangian, in

* K. Kampf, J. Novotný, J. Trnka, *Tree-level amplitudes in the nonlinear sigma model*,
  arXiv:1304.3048 (2013) (KNT): eq. (33) (N = 4), eq. (34) (N = 6), eq. (200) (App. B, N = 8),
  and the Feynman rules of the Cayley parametrisation, eq. (62) (§4.2; App. A, eqs. (179), (181)).

KNT's conventions (their §2): `L = (F²/4)⟨∂_μU ∂^μU⁻¹⟩` (eq. (3)), `U = exp(√2 i φ/F)`,
`φ = φᵃtᵃ`, `⟨tᵃtᵇ⟩ = δᵃᵇ` (eqs. (4)–(5)); the full amplitude is a sum over orderings of
`⟨t^{a_σ(1)}…t^{a_σ(n)}⟩` times the stripped amplitude `𝓜(p_σ(1), …, p_σ(n))` (eq. (11) with
eqs. (12)–(14)), all momenta incoming; `𝓜(1, …, n)` does not depend on the parametrisation of `U`
(§2.3.2), and KNT compute it in the minimal one (eq. (31)); `s_{i,j} = (p_i + … + p_j)²`
(eq. (30)), with `s_{i,j} = s_{j+1,i−1}`.

**The dictionary.** The library's chord `X_{i,j}` is `(p_i + … + p_{j−1})²` (leg `a` between dual
points `a` and `a + 1`, `C0`), so `s_{i,j} = X_{i,j+1}`, labels read mod `N`; `kntS` is this,
through the library's `planar` (which gives `0` on an edge: `s_{i,i} = p_i² = 0`, massless
legs). KNT write each closed form as `(2F²)^{(N−2)/2} 𝓜_N = …`; `kntM4`, `kntM6`, `kntM8`
transcribe the right-hand sides in KNT's own symbols (a function `s` of two labels) and divide by
KNT's left-hand constant, so they are KNT's `𝓜_N` as a function of the `s_{i,j}`. The controls
apply them to `kntS N X`, so the dictionary appears in each statement.

**The checked statement.** `𝒜_N = (−1)^{N/2} (2F²)^{(N−2)/2} 𝓜_N` (`kntConst`) for `N = 4, 6, 8`
(`calA_four_knt`, `calA_six_knt`, `calA_eight_knt`), for every `F ≠ 0`. `N = 8` is the first size
with two propagators per diagram, and the first at which the library had no printed amplitude to
compare `calA` with (at `N = 6` it has the paper's `paper43`); its proof goes through Theorem B
(`theoremB`, `Q_8^π = σ_8 · NLSM_8`) and the library's `Q_8` written out (`Qpi_eight`), and holds
off the poles (no odd chord zero), where both sides are defined. Two negative controls
(`negctl_knt_sign`, `negctl_knt_dictionary`) show at a rational point of the hexagon that the wrong
sign `(−1)^{N/2−1}` and the dictionary off by one (`s_{i,j} = X_{i,j}`) fail; they are at `N = 6`
only, the smallest size at which both slips show (the sign control amounts to `𝒜₆ ≠ 0` there).

**Every N, through the Cayley form.** KNT's Feynman rules in the Cayley parametrisation
`U = (1 + iφ/(√2F)) / (1 − iφ/(√2F))` (eq. (60)) have no odd vertices and the even vertex
`V_{2n+2} = ((−1)^n / 2^n) F^{−2n} (Σ_{i=0}^{n} p_{2i+1})²` (eq. (62), from eqs. (179), (181)),
`p_1, …, p_{2n+2}` the momenta into the vertex in cyclic order. `kntV` transcribes it, `kntSq` the
square through KNT's `s` (`kntDot`: `2 p_a·p_b = s_{a,b} − s_{a+1,b} − s_{a,b−1} + s_{a+1,b−1}`,
from eq. (30)), and `kntCayleySum` their flavour-ordered sum of tree diagrams with the factor
`−1/p_P²` for each propagator (the propagator `i/p²` of §2.3.1 with the vertex factors `i V`; KNT's
own uses: `𝓜₄ = V₄` in eq. (33), the minus of the exchange terms in eq. (34), and `J` in eqs.
(64)–(65)). A planar tree diagram with even vertices is the dual of an even dissection of the
`N`-gon (a vertex is a face, a propagator a chord, the momentum into a vertex along a side the sum
of the legs the side carries), so `kntCayleySum` sums over the library's dissections `pkGDis`, and
the odd momenta of the vertex of a face `f` are the sides that start at an odd vertex (`U_f`,
`oddStartLegs`; the even ones give the same square, by momentum conservation). The constant is then
one line: a face with `|f| = 2n + 2` vertices gives `V_{|f|} = (2F²)^{−(|f|/2 − 1)} V_f`, with `V_f`
the paper's Cayley vertex (`faceVertex`), and `Σ_f (|f| − 2) = N − 2` over the faces of every
dissection (`faces_card_sub_two_sum`), so every diagram carries the same `(2F²)^{−(N−2)/2}`:
`(2F²)^{(N−2)/2} kntCayleySum = cayleySum` for every even `N ≥ 4` (`kntCayleySum_eq`). With the
Cayley form (`cayley_form`, `NLSM_N = −Cay_N`) this gives `NLSM_N = −(2F²)^{(N−2)/2} kntCayleySum_N`
for every even `N ≥ 4` (`nlsm_knt_cayley`). The section follows the paper's order and form: the
definition of the Feynman sum, the constant, the identification, the checks. The controls
`kntCayleySum_four_knt`, `kntCayleySum_six_knt` and `kntCayleySum_eight_knt` check the transcription
of eq. (62) against KNT's closed forms: `kntCayleySum_N = 𝓜_N` at `N = 4` and `6` directly (at `6`
off the poles, as the vertices depend on the momenta of the propagators), at `N = 8` as rational
functions, through `cayley_form` and `nlsm_eight_knt`. Three negative controls
(`negctl_knt_vertex_constant`, `negctl_knt_vertex_sign`, `negctl_knt_propagator_sign`) show at a
rational point of the hexagon, with `F = 1`, that the vertex with the constant of the first form of
eq. (62), `−(−1)^n / 2^{n+1}`, put in front of the square of the second, the vertex with the
opposite sign, and the propagator `+1/p²` fail. What is not checked here: that these Feynman rules,
of the Cayley parametrisation of `U(N)`, give the amplitude of the `SU(N)` Lagrangian, independently
of the parametrisation (KNT §§2.3.2–2.3.3, eqs. (60)–(61), App. A); Lean has no Lagrangian to state
it for.

**What is fixed, and what is not.** `NLSM_N = −(2F²)^{(N−2)/2} 𝓜_N`, with one sign for every `N`
(`nlsm_four_knt`, `nlsm_six_knt`, `nlsm_eight_knt`, the form in which the paper states it);
the `(−1)^{N/2−1}` of `calA` (chosen so that `calA 4 = X₁₃ + X₂₄`, `C0`) makes it `(−1)^{N/2}`. That
one global sign is fixed relative to KNT's formulas read with `s = X`: `𝓜_N` is of degree 1 in the
`s`, so `s ↦ −s` would flip it, and KNT do not state their metric signature (their eq. (3), with a
positive kinetic term, implies mostly-minus). Leg labels are fixed up to the symmetries of the
amplitude, rotations and the reflection `i ↦ 1 − i`: a relabelling by one of them is not a slip.

**How to check this by hand.** Open KNT at eqs. (30), (33), (34) and (200); compare them with
`kntM4`, `kntM6`, `kntM8` symbol by symbol (`cycl` of eq. (35) is the sum over `k`); check the
dictionary `kntS` (`s_{i,j} = X_{i,j+1}`) against eq. (30) and the leg convention of `C0` (`planar`,
`TreeRectangleZero`, reads labels mod `N` and is `0` off the diagonals, so the shifted labels of
`cycl` are allowed); check the constant `kntConst`. For every `N`: compare `kntV` with eq. (62) (its
second form, a transcription); expand `kntDot` from eq. (30) (a derived formula); check the factor
`−1/s_{i,j−1}` of `kntCayleySum` for the chord `(i, j)` (the momentum `p_i + … + p_{j−1}`) against
KNT's propagator and eqs. (33), (34), (64), (65); and check the reading of diagrams as dissections
above. Lean checks the rest.

AF arXiv:2403.04826 (§2–§3) is not used: it gives the minimal-parametrisation vertices (2.1) and
the Catalan numerators (2.2) in the library's own variables `X`, with no `F`; its amplitude is the
library's `NLSM_N` (its six-point (2.3) equals `paper43` after regrouping), so it would add no check
of the dictionary or of the factor `2F²`.
-/

@[expose] public section

namespace PionCompleteness.Pi

open Finset PionCompleteness.TreeRectangleZero PionCompleteness.PionZeros
  PionCompleteness.PionNLSM PionCompleteness.Paper PionCompleteness.Paper.Combinatorics.Polygons
  PionCompleteness.Paper.NLSM.FeynmanRules

variable {K : Type*} [Field K]

/-! ## KNT's variables and closed forms -/

-- registry: C-MCJA
/-- KNT's `s_{i,j} = (p_i + … + p_j)²` (arXiv:1304.3048 eq. (30)) in the library's chords:
`X_{i,j+1}`, labels read mod `N`, `0` for a single leg or all legs but one (massless). -/
def kntS (N : ℕ) (X : ℕ × ℕ → K) (i j : ℕ) : K := planar N X i (j + 1)

/-- KNT's `𝓜(1, 2, 3, 4)` as a function of the `s_{i,j}`, from arXiv:1304.3048 eq. (33):
`2F² 𝓜 = s_{1,2} + s_{2,3}`. -/
noncomputable def kntM4 (F : K) (s : ℕ → ℕ → K) : K :=
  (s 1 2 + s 2 3) / (2 * F ^ 2)

/-- KNT's `𝓜(1, …, 6)` as a function of the `s_{i,j}`, from arXiv:1304.3048 eq. (34):
`4F⁴ 𝓜 = −(s₁₂+s₂₃)(s₁₄+s₄₅)/s₁₃ − (s₁₄+s₂₅)(s₂₃+s₃₄)/s₂₄ − (s₁₂+s₂₅)(s₃₄+s₄₅)/s₃₅
+ (s₁₂+s₁₄+s₂₃+s₂₅+s₃₄+s₄₅)`. -/
noncomputable def kntM6 (F : K) (s : ℕ → ℕ → K) : K :=
  (-((s 1 2 + s 2 3) * (s 1 4 + s 4 5) / s 1 3)
    - (s 1 4 + s 2 5) * (s 2 3 + s 3 4) / s 2 4
    - (s 1 2 + s 2 5) * (s 3 4 + s 4 5) / s 3 5
    + (s 1 2 + s 1 4 + s 2 3 + s 2 5 + s 3 4 + s 4 5)) / (4 * F ^ 4)

/-- KNT's `𝓜(1, …, 8)` as a function of the `s_{i,j}`, from arXiv:1304.3048 eq. (200):
`8F⁶ 𝓜 = ½(s₁₂+s₂₃)(s₁₄+s₄₇)(s₅₆+s₆₇)/(s₁₃s₅₇) + (s₁₂+s₂₃)(s₁₄+s₄₅)(s₆₇+s₇₈)/(s₁₃s₆₈)
− (s₁₂+s₂₃)(s₄₅+s₄₇+s₅₆+s₅₈+s₆₇+s₇₈)/s₁₃ + 2s₁₂ + ½s₁₄ + cycl`, where `cycl` sums the shifts of
every label by `k = 0, …, 7` (eq. (35)). -/
noncomputable def kntM8 (F : K) (s : ℕ → ℕ → K) : K :=
  (∑ k ∈ range 8,
    (1 / 2 * ((s (1 + k) (2 + k) + s (2 + k) (3 + k)) * (s (1 + k) (4 + k) + s (4 + k) (7 + k)) *
          (s (5 + k) (6 + k) + s (6 + k) (7 + k)) / (s (1 + k) (3 + k) * s (5 + k) (7 + k)))
      + (s (1 + k) (2 + k) + s (2 + k) (3 + k)) * (s (1 + k) (4 + k) + s (4 + k) (5 + k)) *
          (s (6 + k) (7 + k) + s (7 + k) (8 + k)) / (s (1 + k) (3 + k) * s (6 + k) (8 + k))
      - (s (1 + k) (2 + k) + s (2 + k) (3 + k)) *
          (s (4 + k) (5 + k) + s (4 + k) (7 + k) + s (5 + k) (6 + k) + s (5 + k) (8 + k) +
            s (6 + k) (7 + k) + s (7 + k) (8 + k)) / s (1 + k) (3 + k)
      + 2 * s (1 + k) (2 + k) + 1 / 2 * s (1 + k) (4 + k))) / (8 * F ^ 6)

/-- The constant between the library's `𝒜_N` and KNT's `𝓜_N`: `(−1)^{N/2} (2F²)^{(N−2)/2}`. -/
def kntConst (N : ℕ) (F : K) : K := (-1) ^ (N / 2) * (2 * F ^ 2) ^ ((N - 2) / 2)

/-! ## The controls -/

/-- **Control against KNT eq. (33)**: `𝒜₄ = (−1)² (2F²) 𝓜₄`, for every `F ≠ 0`. -/
theorem calA_four_knt [CharZero K] (F : K) (hF : F ≠ 0) (X : ℕ × ℕ → K) :
    calA 4 X = kntConst 4 F * kntM4 F (kntS 4 X) := by
  rw [calA_four, kntConst, kntM4]
  simp only [kntS, planar, vtx]
  norm_num [diagonals]
  field_simp

/-- **Control against KNT eq. (34)**: `𝒜₆ = (−1)³ (2F²)² 𝓜₆`, for every `F ≠ 0`. Stated without a
side condition, since both sides use the same `x⁻¹` atoms; on a pole (`s₁₃`, `s₂₄` or `s₃₅` zero) it
holds only through Lean's `x / 0 = 0` and says nothing physical there. -/
theorem calA_six_knt [CharZero K] (F : K) (hF : F ≠ 0) (X : ℕ × ℕ → K) :
    calA 6 X = kntConst 6 F * kntM6 F (kntS 6 X) := by
  rw [calA_six, paper43, kntConst, kntM6]
  simp only [kntS, planar, vtx]
  norm_num [diagonals]
  field_simp
  ring

/-- The odd diagonals of the octagon (the poles of `𝒜₈`). A fact about `PionZeros`, stated here
because `Base/PionZeros` is compared with its accepted copy and gains no new declarations. -/
theorem oddDiagonals_eight :
    oddDiagonals 8 = {(1, 4), (1, 6), (2, 5), (2, 7), (3, 6), (3, 8), (4, 7), (5, 8)} := by
  decide

/-- **Control against KNT eq. (200)**: `𝒜₈ = (−1)⁴ (2F²)³ 𝓜₈`, for every `F ≠ 0`, at every point
where no odd chord (pole) vanishes (satisfiable: `theoremB_hyp_inhabited`). -/
theorem calA_eight_knt [CharZero K] (F : K) (hF : F ≠ 0) (X : ℕ × ℕ → K)
    (hX : ∀ d ∈ oddDiagonals 8, X d ≠ 0) :
    calA 8 X = kntConst 8 F * kntM8 F (kntS 8 X) := by
  have hB := theoremB (N := 8) (π := 0) (by norm_num) (by norm_num) (by norm_num) X hX
  have hA : calA 8 X = Qpi 8 0 X := by
    rw [hB, calA, sigma]; norm_num
  rw [oddDiagonals_eight] at hX
  have h14 := hX (1, 4) (by simp)
  have h16 := hX (1, 6) (by simp)
  have h25 := hX (2, 5) (by simp)
  have h27 := hX (2, 7) (by simp)
  have h36 := hX (3, 6) (by simp)
  have h38 := hX (3, 8) (by simp)
  have h47 := hX (4, 7) (by simp)
  have h58 := hX (5, 8) (by simp)
  rw [hA, Qpi_eight, kntConst, kntM8]
  simp only [sum_range_succ, sum_range_zero, kntS, vnumX, planar, vtx]
  norm_num [diagonals_eight]
  field_simp
  ring

/-! ## The controls for `NLSM_N`

The statements of the main theorem in the paper's terms (module `Paper`) are about `NLSM_N` itself,
and the paper relates it to KNT with one sign for every `N`: `NLSM_N = −(2F²)^{(N−2)/2} 𝓜_N`. These
are the three controls above in that form (`calA N = (−1)^{N/2−1} NLSM N`, module `C0`). -/

-- registry: C-PPZA
/-- **Control against KNT eq. (33)**: `NLSM₄ = −(2F²) 𝓜₄`, for every `F ≠ 0`. -/
theorem nlsm_four_knt [CharZero K] (F : K) (hF : F ≠ 0) (X : ℕ × ℕ → K) :
    NLSM 4 X = -(2 * F ^ 2) ^ ((4 - 2) / 2) * kntM4 F (kntS 4 X) := by
  have h := calA_four_knt F hF X
  rw [calA, kntConst] at h
  norm_num at h ⊢
  linear_combination -h

-- registry: C-PPZA
/-- **Control against KNT eq. (34)**: `NLSM₆ = −(2F²)² 𝓜₆`, for every `F ≠ 0` (on a pole only
through Lean's `x / 0 = 0`, as `calA_six_knt`). -/
theorem nlsm_six_knt [CharZero K] (F : K) (hF : F ≠ 0) (X : ℕ × ℕ → K) :
    NLSM 6 X = -(2 * F ^ 2) ^ ((6 - 2) / 2) * kntM6 F (kntS 6 X) := by
  have h := calA_six_knt F hF X
  rw [calA, kntConst] at h
  norm_num at h ⊢
  linear_combination h

-- registry: C-PPZA
/-- **Control against KNT eq. (200)**: `NLSM₈ = −(2F²)³ 𝓜₈`, for every `F ≠ 0`, at every point
where no odd chord (pole) vanishes. -/
theorem nlsm_eight_knt [CharZero K] (F : K) (hF : F ≠ 0) (X : ℕ × ℕ → K)
    (hX : ∀ d ∈ oddDiagonals 8, X d ≠ 0) :
    NLSM 8 X = -(2 * F ^ 2) ^ ((8 - 2) / 2) * kntM8 F (kntS 8 X) := by
  have h := calA_eight_knt F hF X hX
  rw [calA, kntConst] at h
  norm_num at h ⊢
  linear_combination -h

/-! ## Negative controls -/

/-- **Negative control (sign)**: with the sign `(−1)^{N/2−1}` instead of `kntConst`'s `(−1)^{N/2}`,
the `N = 6` control fails at a rational point off the poles. Given `calA_six_knt`, this amounts to
`𝒜₆ ≠ 0` at that point: it shows the sign matters, not a second check of the transcription. -/
theorem negctl_knt_sign :
    calA 6 (hexPt 2 3 5 7 11 13 17 19 23) ≠
      (-1 : ℚ) ^ (6 / 2 - 1) * (2 * 1 ^ 2) ^ ((6 - 2) / 2) *
        kntM6 1 (kntS 6 (hexPt 2 3 5 7 11 13 17 19 23)) := by
  rw [calA_six, paper43, kntM6]
  simp only [kntS, planar, vtx, hexPt]
  norm_num [diagonals]

/-- **Negative control (dictionary)**: with the dictionary off by one, `s_{i,j} = X_{i,j}` instead
of `kntS`'s `X_{i,j+1}`, the `N = 6` control fails at a rational point off the poles. -/
theorem negctl_knt_dictionary :
    calA 6 (hexPt 2 3 5 7 11 13 17 19 23) ≠
      kntConst 6 1 * kntM6 1 (planar 6 (hexPt 2 3 5 7 11 13 17 19 23)) := by
  rw [calA_six, paper43, kntConst, kntM6]
  simp only [planar, vtx, hexPt]
  norm_num [diagonals]

/-! ## Every `N`: KNT's Feynman rules in the Cayley parametrisation

In the order of the paper: the Feynman sum of the Cayley parametrisation, the constant that relates
it to the Cayley sum (with the face count its proof uses), the identification for every even `N`
through the Cayley form, and the checks of the transcription against KNT's closed forms. -/

/-! ### The Feynman sum of the Cayley parametrisation (the paper's definition) -/

-- registry: C-MCJA
/-- KNT's vertex with `2n + 2` legs in the Cayley parametrisation, transcribed from
arXiv:1304.3048 eq. (62), whose second form is printed as
`V_{2n+2} = ((−1)^n / 2^n) (1/F)^{2n} (Σ_{i=0}^{n} p_{2i+1})²`: here as a function of the square `q`
of the sum of the momenta at every other leg (`kntSq`). -/
noncomputable def kntV (F : K) (n : ℕ) (q : K) : K := (-1) ^ n / 2 ^ n * (1 / F) ^ (2 * n) * q

-- registry: C-MCJA
/-- `2 p_a·p_b` for legs `a < b`, in KNT's symbols. A derived formula, not one KNT prints: from
their definition `s_{i,j} = (p_i + … + p_j)²` (arXiv:1304.3048 eq. (30)), with
`M = p_{a+1} + … + p_{b−1}`, `(p_a + M + p_b)² − (M + p_b)² − (p_a + M)² + M² = 2 p_a·p_b`, that
is `s_{a,b} − s_{a+1,b} − s_{a,b−1} + s_{a+1,b−1}` (`s_{a+1,a}`, no legs, is `0`). -/
def kntDot (s : ℕ → ℕ → K) (a b : ℕ) : K := s a b - s (a + 1) b - s a (b - 1) + s (a + 1) (b - 1)

-- registry: C-MCJA
/-- KNT's `(Σ_{a ∈ U} p_a)²` for massless legs, in their symbols: `Σ_{a < b ∈ U} 2 p_a·p_b`. -/
def kntSq (s : ℕ → ℕ → K) (U : Finset ℕ) : K :=
  ∑ p ∈ (U ×ˢ U).filter (fun p => p.1 < p.2), kntDot s p.1 p.2

-- registry: C-MCJA
/-- The flavour-ordered sum of KNT's tree diagrams with the even vertices `V` and the propagator
`Δ`, over the even-angulations of the `N`-gon (`pkGDis`, the dissections by odd chords): for each
face `f` (a vertex with `|f| = 2n + 2` legs) the vertex `V n` of the square of the sum of the
momenta of its sides that start at an odd vertex (the legs `U_f`), and for each chord `(i, j)` (a
propagator, momentum `p_i + … + p_{j−1}`) the factor `Δ s_{i,j−1}`. The vertex and the propagator
are arguments for the negative controls. -/
noncomputable def kntFeynman (N : ℕ) (V : ℕ → K → K) (Δ : K → K) (s : ℕ → ℕ → K) : K :=
  ∑ D ∈ pkGDis N, (∏ f ∈ faces N D, V (f.card / 2 - 1) (kntSq s (oddStartLegs N f))) *
    ∏ P ∈ D, Δ (s P.1 (P.2 - 1))

-- registry: C-MCJA
/-- KNT's Feynman sum in the Cayley parametrisation: `kntFeynman` with the vertices `kntV` of
eq. (62) and the factor `−1/p²` for each propagator. -/
noncomputable def kntCayleySum (N : ℕ) (F : K) (s : ℕ → ℕ → K) : K :=
  kntFeynman N (kntV F) (fun x => -1 / x) s

/-- Through the dictionary, KNT's square is the block sum `Σ_{a < b ∈ U} −c_{a,b}`. -/
theorem kntSq_kntS (N : ℕ) (X : ℕ × ℕ → K) (U : Finset ℕ) :
    kntSq (kntS N X) U = ∑ p ∈ (U ×ˢ U).filter (fun p => p.1 < p.2), -mesh N X p.1 p.2 := by
  refine sum_congr rfl fun p hp => ?_
  have h := (mem_filter.1 hp).2
  have e : p.2 - 1 + 1 = p.2 := by omega
  simp only [kntDot, kntS, mesh, e]
  ring

/-! ### The constant (the paper's proposition) and the face count its proof uses -/

/-- The vertex constant: `(2F²)^n V_{2n+2} = (−1)^n q`, for `F ≠ 0`. -/
theorem kntV_const [CharZero K] (F : K) (hF : F ≠ 0) (n : ℕ) (q : K) :
    (2 * F ^ 2) ^ n * kntV F n q = (-1) ^ n * q := by
  have h2 : (2 : K) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
  have hFn : F ^ (2 * n) ≠ 0 := pow_ne_zero _ hF
  rw [kntV, mul_pow, ← pow_mul, one_div, inv_pow]
  field_simp

/-- Each chord of a dissection is a child (`pkGKids`) of exactly one root side, so summing over the
children of every root side is summing over the chords. -/
theorem pkG_sum_kids {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {D : Finset (ℕ × ℕ)}
    (hD : D ∈ pkGDis N) (f : ℕ × ℕ → ℕ) :
    ∑ r ∈ pkGRoots N D, ∑ K ∈ pkGKids D r, f K = ∑ K ∈ D, f K := by
  have hdisj : (pkGRoots N D : Set (ℕ × ℕ)).PairwiseDisjoint (pkGKids D) := by
    intro r hr r' hr' hne
    rw [Function.onFun, disjoint_left]
    intro K hK hK'
    exact hne (pkG_par_uniq hN hE hD hr hr' hK hK')
  have hU : (pkGRoots N D).biUnion (pkGKids D) = D := by
    ext K
    rw [mem_biUnion]
    refine ⟨fun ⟨r, _, hK⟩ => (pkG_kid_in hK).1, fun hK => ?_⟩
    obtain ⟨r, hr, hK'⟩ := pkG_par_ex hN hE hD hK
    exact ⟨r, hr, hK'⟩
  rw [← sum_biUnion hdisj, hU]

/-- The legs `[r.1, r.2)` of a root side are those the face owns and those of its children's
blocks: `r.2 − r.1 = |own| + Σ_{children K} (K.2 − K.1)` (the count of `pkG_Ico_eq`; the proof of
`pkG_verts_even` makes the same count inline, modulo 2). -/
theorem pkG_card_Ico_root {N : ℕ} {D : Finset (ℕ × ℕ)} (hD : D ∈ pkGDis N) (r : ℕ × ℕ) :
    r.2 - r.1 = (pkGOwn D r).card + ∑ K ∈ pkGKids D r, (K.2 - K.1) := by
  have hdisjK : ∀ K ∈ pkGKids D r, ∀ K' ∈ pkGKids D r, K ≠ K' →
      Disjoint ((fun K : ℕ × ℕ => Ico K.1 K.2) K) ((fun K : ℕ × ℕ => Ico K.1 K.2) K') := by
    intro K hK K' hK' hne
    have := pkG_kids_disj hD hK hK' hne
    rw [disjoint_left]
    intro x hx hx'
    have := mem_Ico.1 hx
    have := mem_Ico.1 hx'
    omega
  have hcb := card_biUnion hdisjK
  have hd : Disjoint (pkGOwn D r) ((pkGKids D r).biUnion (fun K => Ico K.1 K.2)) := by
    rw [disjoint_left]
    intro x hx hx'
    obtain ⟨-, -, hw⟩ := pkG_mem_own.1 hx
    obtain ⟨K, hK, hxK⟩ := mem_biUnion.1 hx'
    exact hw K hK (mem_Ico.1 hxK)
  have hc := card_union_of_disjoint hd
  rw [← pkG_Ico_eq, Nat.card_Ico, hcb] at hc
  simpa only [Nat.card_Ico] using hc

/-- **The face sizes of a dissection**: for even `N ≥ 4` and a dissection `D`, the numbers of
vertices of the faces add up to `N + 2|D|`. The proof counts on the library's root sides (the legs
of a root side are those its face owns and those of its children's blocks), not by merging the two
faces of a chord, as the paper does: the faces' sides are not a separate statement here. -/
theorem faces_card_sum {N : ℕ} (hN : 4 ≤ N) (hE : Even N) {D : Finset (ℕ × ℕ)}
    (hD : D ∈ pkGDis N) : ∑ f ∈ faces N D, f.card = N + 2 * D.card := by
  have hE : N % 2 = 0 := Nat.even_iff.1 hE
  rw [faces_eq_image hN hE hD, sum_image (pkG_verts_injOn hN hE hD),
    sum_congr rfl (fun r hr => pkG_card_verts hN hE hD hr), sum_add_distrib, sum_add_distrib,
    sum_const, smul_eq_mul, mul_one, pkG_card_roots hD]
  have hk := pkG_sum_kids hN hE hD (fun _ => 1)
  simp only [sum_const, smul_eq_mul, mul_one] at hk
  have hl := sum_congr rfl (fun r (_ : r ∈ pkGRoots N D) => pkG_card_Ico_root hD r)
  rw [sum_add_distrib, pkG_sum_kids hN hE hD (fun K => K.2 - K.1)] at hl
  rw [pkGRoots, sum_insert (pkG_top_nmem hD)] at hl
  rw [hk, pkGRoots]
  dsimp only at hl
  omega

-- registry: C-EAMB
/-- **The face count**: for even `N ≥ 4` and a dissection `D`, `Σ_f (|f| − 2) = N − 2` over the
faces `f` of `D`. -/
theorem faces_card_sub_two_sum {N : ℕ} (hN : 4 ≤ N) (hE : Even N) {D : Finset (ℕ × ℕ)}
    (hD : D ∈ pkGDis N) : ∑ f ∈ faces N D, (f.card - 2) = N - 2 := by
  have h4 : ∀ f ∈ faces N D, 4 ≤ f.card := fun f hf => ((dissections hN hE hD).2 f hf).1
  have h := faces_card_sum hN hE hD
  have hc := (dissections hN hE hD).1
  have : ∑ f ∈ faces N D, (f.card - 2) + 2 * (faces N D).card = ∑ f ∈ faces N D, f.card := by
    rw [mul_comm, ← smul_eq_mul, ← sum_const, ← sum_add_distrib]
    exact sum_congr rfl fun f hf => by have := h4 f hf; omega
  omega

/-- The exponents of the vertex constants add up to the same number for every dissection:
`Σ_f (|f|/2 − 1) = (N − 2)/2`. -/
theorem faces_half_sum {N : ℕ} (hN : 4 ≤ N) (hE : Even N) {D : Finset (ℕ × ℕ)}
    (hD : D ∈ pkGDis N) : ∑ f ∈ faces N D, (f.card / 2 - 1) = (N - 2) / 2 := by
  have h := faces_card_sub_two_sum hN hE hD
  have h2 : 2 * ∑ f ∈ faces N D, (f.card / 2 - 1) = ∑ f ∈ faces N D, (f.card - 2) := by
    rw [mul_sum]
    refine sum_congr rfl fun f hf => ?_
    obtain ⟨h4, he, -⟩ := (dissections hN hE hD).2 f hf
    have := Nat.even_iff.1 he
    omega
  omega

-- registry: C-EAMB
/-- **The constant**: for every even `N ≥ 4` and `F ≠ 0`, KNT's Feynman sum in the Cayley
parametrisation, read through the dictionary, is `(2F²)^{−(N−2)/2}` times the Cayley sum:
`(2F²)^{(N−2)/2} kntCayleySum_N = Cay_N`, at every point (on a pole, some odd `X P = 0`, only
through Lean's `x / 0 = 0`, both sides alike). -/
theorem kntCayleySum_eq [CharZero K] {N : ℕ} (hN : 4 ≤ N) (hE : Even N) (F : K) (hF : F ≠ 0)
    (X : ℕ × ℕ → K) :
    (2 * F ^ 2) ^ ((N - 2) / 2) * kntCayleySum N F (kntS N X) = cayleySum N X := by
  rw [kntCayleySum, kntFeynman, cayleySum, mul_sum]
  refine sum_congr rfl fun D hD => ?_
  have hP : ∏ P ∈ D, (-1 / kntS N X P.1 (P.2 - 1)) = ∏ P ∈ D, -(X P)⁻¹ := by
    refine prod_congr rfl fun P hP => ?_
    have c := pkG_chord hD hP
    have e : P.2 - 1 + 1 = P.2 := by omega
    rw [kntS, e, planar_eq_X X c.1 (by omega) c.2.1 c.2.2.2.2, neg_div, one_div]
  rw [hP, ← mul_assoc, ← faces_half_sum hN hE hD, ← prod_pow_eq_pow_sum, ← prod_mul_distrib]
  congr 1
  refine prod_congr rfl fun f _ => ?_
  rw [kntV_const F hF, kntSq_kntS, faceVertex]

/-! ### The identification (the paper's corollary) -/

-- registry: C-X0M8
/-- **The identification for every `N`**: for every even `N ≥ 4` and `F ≠ 0`,
`NLSM_N = −(2F²)^{(N−2)/2} kntCayleySum_N` as rational functions (the Cayley form,
`cayley_form`, with `kntCayleySum_eq`). `F` is any non-zero element of the field of rational
functions, so every non-zero constant, the paper's `F`, is one. -/
theorem nlsm_knt_cayley {N : ℕ} (hN : 4 ≤ N) (hE : Even N) (F : RF) (hF : F ≠ 0) :
    NLSM N gen = -(2 * F ^ 2) ^ ((N - 2) / 2) * kntCayleySum N F (kntS N gen) := by
  rw [cayley_form hN hE, ← kntCayleySum_eq hN hE F hF gen, neg_mul]

/-! ### The transcription checked against KNT's closed forms -/

/-- KNT's Feynman sum at `N = 4`: one diagram, the vertex `V₄` with the odd legs `1, 3`. -/
theorem kntFeynman_four (V : ℕ → K → K) (Δ : K → K) (s : ℕ → ℕ → K) :
    kntFeynman 4 V Δ s = V 1 (kntSq s {1, 3}) := by
  have hdis : pkGDis 4 = {∅} := by decide
  have h0 : (∅ : Finset (ℕ × ℕ)) ∈ pkGDis 4 := by rw [hdis]; exact mem_singleton_self _
  have f0 : faces 4 ∅ = {{1, 2, 3, 4}} := by
    rw [faces_eq_image (by norm_num) (by norm_num) h0]; decide
  have u0 : oddStartLegs 4 {1, 2, 3, 4} = {1, 3} := by decide
  rw [kntFeynman, hdis, sum_singleton, f0, prod_singleton, u0, prod_empty, mul_one]
  norm_num

/-- KNT's Feynman sum at `N = 6`: the contact diagram `V₆` and the three exchange diagrams, one for
each odd chord `(1, 4)`, `(2, 5)`, `(3, 6)`, with the odd legs of each face. -/
theorem kntFeynman_six (V : ℕ → K → K) (Δ : K → K) (s : ℕ → ℕ → K) :
    kntFeynman 6 V Δ s =
      V 2 (kntSq s {1, 3, 5}) +
      V 1 (kntSq s {1, 3}) * V 1 (kntSq s {1, 2, 3, 5}) * Δ (s 1 3) +
      V 1 (kntSq s {1, 5}) * V 1 (kntSq s {1, 3, 5, 6}) * Δ (s 2 4) +
      V 1 (kntSq s {1, 3, 4, 5}) * V 1 (kntSq s {3, 5}) * Δ (s 3 5) := by
  have hdis : pkGDis 6 = {∅, {(1, 4)}, {(2, 5)}, {(3, 6)}} := by decide
  have hm : ∀ D, D ∈ ({∅, {(1, 4)}, {(2, 5)}, {(3, 6)}} : Finset (Finset (ℕ × ℕ))) →
      D ∈ pkGDis 6 := fun D hD => hdis ▸ hD
  have f0 : faces 6 ∅ = {{1, 2, 3, 4, 5, 6}} := by
    rw [faces_eq_image (by norm_num) (by norm_num) (hm _ (by simp))]; decide
  have f1 : faces 6 {(1, 4)} = {{1, 2, 3, 4}, {1, 4, 5, 6}} := by
    rw [faces_eq_image (by norm_num) (by norm_num) (hm _ (by simp))]; decide
  have f2 : faces 6 {(2, 5)} = {{1, 2, 5, 6}, {2, 3, 4, 5}} := by
    rw [faces_eq_image (by norm_num) (by norm_num) (hm _ (by simp))]; decide
  have f3 : faces 6 {(3, 6)} = {{1, 2, 3, 6}, {3, 4, 5, 6}} := by
    rw [faces_eq_image (by norm_num) (by norm_num) (hm _ (by simp))]; decide
  have u0 : oddStartLegs 6 {1, 2, 3, 4, 5, 6} = {1, 3, 5} := by decide
  have u1 : oddStartLegs 6 {1, 2, 3, 4} = {1, 3} := by decide
  have u2 : oddStartLegs 6 {1, 4, 5, 6} = {1, 2, 3, 5} := by decide
  have u3 : oddStartLegs 6 {1, 2, 5, 6} = {1, 5} := by decide
  have u4 : oddStartLegs 6 {2, 3, 4, 5} = {1, 3, 5, 6} := by decide
  have u5 : oddStartLegs 6 {1, 2, 3, 6} = {1, 3, 4, 5} := by decide
  have u6 : oddStartLegs 6 {3, 4, 5, 6} = {3, 5} := by decide
  rw [kntFeynman, hdis, sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_singleton, f0, f1, f2, f3, prod_singleton, prod_pair (by decide), prod_pair (by decide),
    prod_pair (by decide), u0, u1, u2, u3, u4, u5, u6, prod_empty, prod_singleton, prod_singleton,
    prod_singleton]
  norm_num
  ring

-- registry: C-BHQ5
/-- **Control of eq. (62) against eq. (33)**: `kntCayleySum₄ = 𝓜₄`, for every `F` (at `F = 0` only
through Lean's `x / 0 = 0`, both sides alike). -/
theorem kntCayleySum_four_knt (F : K) (X : ℕ × ℕ → K) :
    kntCayleySum 4 F (kntS 4 X) = kntM4 F (kntS 4 X) := by
  rw [kntCayleySum, kntFeynman_four, kntM4]
  norm_num [kntSq, sum_filter, sum_product]
  simp only [kntV, kntDot, kntS, planar, vtx]
  norm_num [diagonals]
  field_simp
  ring

-- registry: C-BHQ5
/-- **Control of eq. (62) against eq. (34)**: `kntCayleySum₆ = 𝓜₆`, for every `F` (at `F = 0` only
through Lean's `x / 0 = 0`, both sides alike), at every point where no odd chord (pole) vanishes.
The two sides agree diagram by diagram only up to terms in which a vertex, which depends on the
momentum of a propagator, cancels that propagator (KNT computed eq. (34) in another
parametrisation); on a pole Lean's `x / 0 = 0` drops different terms on the two sides. -/
theorem kntCayleySum_six_knt (F : K) (X : ℕ × ℕ → K)
    (h14 : X (1, 4) ≠ 0) (h25 : X (2, 5) ≠ 0) (h36 : X (3, 6) ≠ 0) :
    kntCayleySum 6 F (kntS 6 X) = kntM6 F (kntS 6 X) := by
  rw [kntCayleySum, kntFeynman_six, kntM6]
  norm_num [kntSq, sum_filter, sum_product]
  simp only [kntV, kntDot, kntS, planar, vtx]
  norm_num [diagonals]
  field_simp
  ring

-- registry: C-BHQ5
/-- **Control of eq. (62) against eq. (200)**: `kntCayleySum₈ = 𝓜₈` as rational functions, for every
`F ≠ 0` (through `nlsm_knt_cayley` and `nlsm_eight_knt`). -/
theorem kntCayleySum_eight_knt (F : RF) (hF : F ≠ 0) :
    kntCayleySum 8 F (kntS 8 gen) = kntM8 F (kntS 8 gen) := by
  have h1 := nlsm_knt_cayley (N := 8) (by norm_num) (by decide) F hF
  have hX : ∀ d ∈ oddDiagonals 8, gen d ≠ 0 := fun d _ => gen_ne_zero d
  have h2 := nlsm_eight_knt F hF gen hX
  have hc : (2 * F ^ 2) ^ ((8 - 2) / 2) ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero two_ne_zero (pow_ne_zero _ hF))
  rw [h1, neg_mul, neg_mul, neg_inj] at h2
  exact mul_left_cancel₀ hc h2

-- registry: C-BHQ5
/-- **Negative control (vertex constant)**: with the constant of the first form of eq. (62),
`−(−1)^n / 2^{n+1}`, that is `−½` times `kntV`'s, in front of the square of its second form, KNT's
Feynman sum fails the `N = 6` control, with `F = 1`, at a rational point off the poles. -/
theorem negctl_knt_vertex_constant :
    kntFeynman 6 (fun n q => -(1 / 2) * kntV (1 : ℚ) n q) (fun x => -1 / x)
        (kntS 6 (hexPt 2 3 5 7 11 13 17 19 23)) ≠
      kntM6 1 (kntS 6 (hexPt 2 3 5 7 11 13 17 19 23)) := by
  rw [kntFeynman_six, kntM6]
  norm_num [kntSq, sum_filter, sum_product, kntV]
  simp only [kntDot, kntS, planar, vtx, hexPt]
  norm_num [diagonals]

-- registry: C-BHQ5
/-- **Negative control (vertex sign)**: with the opposite sign of `kntV`, `(−1)^{n+1}` instead of
eq. (62)'s `(−1)^n`, KNT's Feynman sum fails the `N = 6` control, with `F = 1`, at a rational point
off the poles. At `N = 6` this amounts to the contact diagram `V₆` not vanishing there (the sign
flips each diagram with one propagator twice). -/
theorem negctl_knt_vertex_sign :
    kntFeynman 6 (fun n q => -kntV (1 : ℚ) n q) (fun x => -1 / x)
        (kntS 6 (hexPt 2 3 5 7 11 13 17 19 23)) ≠
      kntM6 1 (kntS 6 (hexPt 2 3 5 7 11 13 17 19 23)) := by
  rw [kntFeynman_six, kntM6]
  norm_num [kntSq, sum_filter, sum_product, kntV]
  simp only [kntDot, kntS, planar, vtx, hexPt]
  norm_num [diagonals]

-- registry: C-BHQ5
/-- **Negative control (propagator sign)**: with the propagator `+1/p²` instead of `−1/p²` (the
factor `i · i = −1` of a propagator and a vertex dropped), KNT's Feynman sum fails the `N = 6`
control, with `F = 1`, at a rational point off the poles. At `N = 6` this amounts to the three
exchange diagrams not adding up to zero there. -/
theorem negctl_knt_propagator_sign :
    kntFeynman 6 (kntV (1 : ℚ)) (fun x => 1 / x)
        (kntS 6 (hexPt 2 3 5 7 11 13 17 19 23)) ≠
      kntM6 1 (kntS 6 (hexPt 2 3 5 7 11 13 17 19 23)) := by
  rw [kntFeynman_six, kntM6]
  norm_num [kntSq, sum_filter, sum_product, kntV]
  simp only [kntDot, kntS, planar, vtx, hexPt]
  norm_num [diagonals]

end PionCompleteness.Pi
