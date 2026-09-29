import TreeRectangleZero

/-!
# R12-P3a: the pion S_T zeros, Theorem A of R2-Z30 — definitions and statements (Phase 3, step 3a)

Thread `surfaceology/threads/R12-P3a.md`. Reference proof: `../r2z30/PROOFS.md` (cited as PROOFS §k), reviewed and
confirmed in `../r2z30rev/REVIEW.md`. Paper for the Feynman rule: arXiv:2607.27345 §II eqs. (3)–(4) (cached as
`../../sources/nlsm-quartic-vertex-2026.md`). Kinematic conventions: C0 = arXiv:2312.16282 §2, exactly as Phase 1:
polygon vertices `1..N`, planar variables `X (i,j)` on diagonals, `0` on polygon edges, mesh (tile) variables
`c_ab = mesh N X a b` for legs `a, b` (leg `a` = the edge `(a, a+1)`, leg `N` = the edge `(N, 1)`).

Phase 1 is imported unchanged: `TreeRectangleZero.lean` here is a byte-identical copy of
`../r12p1b/TreeRectangleZero.lean`, compiled to `build/TreeRectangleZero.olean` (thread §6 E2). Reused: `diagonals`,
`Crosses`, `vtx`, `planar`, `mesh`, `mesh_telescope`, `vtx_add_n`, `vtx_of_mem`, `vtx_bounds`.

Step 3b (thread `R12-P3b.md`, log `LOG.md`): `theoremA`, `ZT_inhabited`, `exists_goodQ`, `quads_alternating`,
`card_quads`, `leg_side_unique` are PROVED (helpers prefixed `p3b_`; frozen statements unchanged, checked by
`../frozen_check.py`). Integrator amendments of 2026-09-23 (owner-approved; statement diff in
`../base-v2/STATEMENT-CHANGES.diff`, frozen base now `../base-v2/PionZeros.lean`): `diag_plus_minus` gains the missing
hypothesis `π < 2` (it was false for `π ≥ 2`) and is PROVED from `p3b_diag_plus_minus`; the unused optional statements
`steiner_tree`, `steiner_count` are removed (the proof route uses the descent walk instead). No `sorry` remains:
`card_quadrangulations` (Fuss–Catalan count; not used by Theorem A) is PROVED by package F (helpers `p3bF_`).

Status markers in docstrings:
* PROVED — no `sorry` in its closure (checked by `#print axioms` at the end of the file);
* `sorry` — statement only, a 3b target.

Design decisions (thread §4, C1–C6):
* A quartic diagram is a quadrangulation, encoded as a maximal set of pairwise non-crossing **odd** diagonals
  (reusing Phase 1's `diagonals` and `Crosses`). Its quads are the 4-tuples `u₁ < u₂ < u₃ < u₄` whose four sides are
  each a polygon edge or a member of the set. Counts 1, 3, 12 are proved by `decide` (N = 4, 6, 8); the Fuss–Catalan
  law is a 3b statement, checked to N = 12 by `defs_mirror.py`.
* Sides are written with unwrapped labels: `(u₁,u₂), (u₂,u₃), (u₃,u₄), (u₄, u₁ + N)`, so every side's block of legs is
  the interval `Icc u (v − 1)` and no case split on wrap-around is needed; labels are read mod `N` by `vtx`.
* The vertex numerator is the paper's `V(ψ₁⁺ψ₂⁻ψ₃⁺ψ₄⁻) = −2k₁·k₃` [arXiv:2607.27345 eq. (4)] written as the sum of
  tiles `c_ab = −2 p_a·p_b` [arXiv:2312.16282 eq. (2.4) and C0] over the two `+` blocks (`vnum`); the linear form in
  `X` given by PROOFS §0 identity (R) is `vnumX`, and `vnum = vnumX` is PROVED from Phase 1's `mesh_telescope`.
* Theorem A is stated pointwise over any field and **without** a non-vanishing hypothesis: the numerator product of
  every diagram vanishes on `Z_T`, so `0⁻¹ = 0` plays no role. What makes the pointwise statement mean "the rational
  function restricts to 0 on Z_T" is that `Z_T` is not inside any polar hyperplane: the witness theorems
  (`ZT_inhabited`, general, 3b; `ZT_inhabited_six`, PROVED) give a point of `Z_T` with every diagonal non-zero.
-/

namespace R12P3

open Finset R12P1

/-! ## Quadrangulations (PROOFS §0.1) -/

/-- Odd diagonals: `(i, j)` with `j − i` odd (the only possible propagators of a quartic diagram). -/
def oddDiagonals (N : ℕ) : Finset (ℕ × ℕ) := (diagonals N).filter (fun d => (d.2 - d.1) % 2 = 1)

/-- A quadrangulation: a maximal set of pairwise non-crossing odd diagonals. (In an even polygon every face of a
dissection by odd diagonals has an even number of corners, and a face with ≥ 6 corners admits a further odd
diagonal; so the maximal sets are exactly the quadrangulations. Thread §4 C1.) -/
def IsQuadrangulation (N : ℕ) (G : Finset (ℕ × ℕ)) : Prop :=
  G ⊆ oddDiagonals N ∧ (∀ p ∈ G, ∀ q ∈ G, ¬ Crosses p q) ∧
    (∀ d ∈ oddDiagonals N, d ∉ G → ∃ p ∈ G, Crosses p d)

instance (N : ℕ) : DecidablePred (IsQuadrangulation N) := fun _ => by
  unfold IsQuadrangulation; infer_instance

def quadrangulations (N : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  (oddDiagonals N).powerset.filter (IsQuadrangulation N)

/-- A quad (quartic vertex): corners `u1 < u2 < u3 < u4`. -/
structure Quad where
  u1 : ℕ
  u2 : ℕ
  u3 : ℕ
  u4 : ℕ
  deriving DecidableEq

/-- All 4-tuples `1 ≤ u1 < u2 < u3 < u4 ≤ N`. -/
def quadIdx (N : ℕ) : Finset Quad :=
  (Icc 1 N).biUnion fun a => (Ioc a N).biUnion fun b => (Ioc b N).biUnion fun c =>
    (Ioc c N).image fun d => ⟨a, b, c, d⟩

/-- The four sides of a quad, as pairs of unwrapped labels `(u, v)` with `u < v`: the closing side is
`(u4, u1 + N)`. The side `(u, v)` carries the block of legs `u, …, v − 1` (read mod `N`). -/
def Quad.sides (N : ℕ) (q : Quad) : List (ℕ × ℕ) :=
  [(q.u1, q.u2), (q.u2, q.u3), (q.u3, q.u4), (q.u4, q.u1 + N)]

/-- The chord joining two (cyclic) labels, normalised to `(min, max)` in `1..N`. -/
def npair (N u v : ℕ) : ℕ × ℕ := (min (vtx N u) (vtx N v), max (vtx N u) (vtx N v))

/-- A side is admissible for `G` if it is a polygon edge (not a diagonal) or a diagonal of `G`. -/
def SideOK (N : ℕ) (G : Finset (ℕ × ℕ)) (s : ℕ × ℕ) : Prop :=
  npair N s.1 s.2 ∈ G ∨ npair N s.1 s.2 ∉ diagonals N

instance (N : ℕ) (G : Finset (ℕ × ℕ)) : DecidablePred (SideOK N G) := fun _ => by
  unfold SideOK; infer_instance

/-- The quads (faces) of `G`: 4-tuples all of whose sides are edges or diagonals of `G`. For a quadrangulation these
are exactly its faces (thread §4 C1: no diagonal of `G` can enter a quad whose sides are in `G ∪ edges`, since the
only chords inside a quad join opposite corners and are even). -/
def quads (N : ℕ) (G : Finset (ℕ × ℕ)) : Finset Quad :=
  (quadIdx N).filter fun q => ∀ s ∈ q.sides N, SideOK N G s

/-- Consecutive corners have opposite parity (true for every face of a quadrangulation: sides are odd). -/
def Quad.Alternating (q : Quad) : Prop :=
  (q.u1 + q.u2) % 2 = 1 ∧ (q.u2 + q.u3) % 2 = 1 ∧ (q.u3 + q.u4) % 2 = 1

instance : DecidablePred Quad.Alternating := fun _ => by unfold Quad.Alternating; infer_instance

/-! ## Polarity and the vertex numerator (PROOFS §0.1, "Polarity", "Vertex factor") -/

/-- Block of legs carried by the side `(u, v)`: `u, u+1, …, v−1` (unwrapped labels). -/
def blk (u v : ℕ) : Finset ℕ := Icc u (v - 1)

/-- Polarity `π ∈ {0, 1}`: the legs of parity `π` carry ψ⁺ and the others ψ⁻ (adjacent legs opposite,
arXiv:2607.27345 §II after eq. (4)). A side `(u, v)` is a `+` slot iff its first leg `u` has parity `π`. -/
def IsPlus (π : ℕ) (s : ℕ × ℕ) : Prop := s.1 % 2 = π

instance (π : ℕ) (s : ℕ × ℕ) : Decidable (IsPlus π s) := by unfold IsPlus; infer_instance

/-- The two `+` sides of an alternating quad (those whose first corner has parity `π`). -/
def plusPair (N π : ℕ) (q : Quad) : (ℕ × ℕ) × (ℕ × ℕ) :=
  if q.u1 % 2 = π then ((q.u1, q.u2), (q.u3, q.u4)) else ((q.u2, q.u3), (q.u4, q.u1 + N))

variable {K : Type*} [Field K]

/-- Sum of tiles `c_ab` over `a` in the block of side `s` and `b` in the block of side `t`: `−2 K_s · K_t` with
`K` the total momentum of a block (C0: `c_ab = −2 p_a·p_b`). -/
def tileSum (N : ℕ) (X : ℕ × ℕ → K) (s t : ℕ × ℕ) : K :=
  ∑ a ∈ blk s.1 s.2, ∑ b ∈ blk t.1 t.2, mesh N X a b

/-- The vertex numerator `n_q^π = −2 k₁·k₃`, `k₁, k₃` the momenta on the two `+` slots
[arXiv:2607.27345 eq. (4)]. -/
def vnum (N π : ℕ) (X : ℕ × ℕ → K) (q : Quad) : K :=
  tileSum N X (plusPair N π q).1 (plusPair N π q).2

/-- The same numerator as a linear form in `X` (PROOFS §0 identity (R)):
`X_{u1u3} + X_{u2u4} −` (the `X`'s of the two `−` sides; edges read as 0). -/
def vnumX (N π : ℕ) (X : ℕ × ℕ → K) (q : Quad) : K :=
  planar N X q.u1 q.u3 + planar N X q.u2 q.u4 -
    (if q.u1 % 2 = π then planar N X q.u2 q.u3 + planar N X q.u4 q.u1
     else planar N X q.u1 q.u2 + planar N X q.u3 q.u4)

/-- One quartic diagram: `∏_{quads} n_q^π / ∏_{propagators} X_C`. -/
def diagram (N π : ℕ) (X : ℕ × ℕ → K) (G : Finset (ℕ × ℕ)) : K :=
  (∏ q ∈ quads N G, vnum N π X q) * ∏ d ∈ G, (X d)⁻¹

/-- `Q_N^π`: the sum of all quartic diagrams (PROOFS §0.1, Definition). -/
def Qpi (N π : ℕ) (X : ℕ × ℕ → K) : K := ∑ G ∈ quadrangulations N, diagram N π X G

/-! ## The loci S_T and Z_T (PROOFS header; R2-Z13 C7) -/

/-- `T` is admissible: legs in `1..N`, at least two of them, all of parity `r`. -/
def Admissible (N r : ℕ) (T : Finset ℕ) : Prop := T ⊆ Icc 1 N ∧ 2 ≤ T.card ∧ ∀ t ∈ T, t % 2 = r

instance (N r : ℕ) : DecidablePred (Admissible N r) := fun _ => by unfold Admissible; infer_instance

/-- The tile `c_ab` (legs `a, b ∈ 1..N`) lies in `S_T`: neither leg is in `T`, and `a`, `b` lie in different arcs
of the leg circle cut at `T`, i.e. a leg of `T` lies strictly between them on each side. (Non-adjacency follows.) -/
def InST (T : Finset ℕ) (a b : ℕ) : Prop :=
  a ∉ T ∧ b ∉ T ∧ (∃ t ∈ T, min a b < t ∧ t < max a b) ∧ (∃ t ∈ T, t < min a b ∨ max a b < t)

instance (T : Finset ℕ) (a b : ℕ) : Decidable (InST T a b) := by unfold InST; infer_instance

/-- `X ∈ Z_T`: every tile of `S_T` vanishes. -/
def OnZT (N : ℕ) (T : Finset ℕ) (X : ℕ × ℕ → K) : Prop :=
  ∀ a ∈ Icc 1 N, ∀ b ∈ Icc 1 N, InST T a b → mesh N X a b = 0

/-! ## Good quads and the Steiner counts (PROOFS §1) -/

/-- The block of side `s` contains a leg of `T`. -/
def Meets (N : ℕ) (T : Finset ℕ) (s : ℕ × ℕ) : Prop := ∃ a ∈ blk s.1 s.2, vtx N a ∈ T

instance (N : ℕ) (T : Finset ℕ) : DecidablePred (Meets N T) := fun _ => by unfold Meets; infer_instance

/-- A good quad (PROOFS Lemma A.2): its `−` blocks meet `T` and its `+` blocks do not. -/
def GoodQ (N : ℕ) (T : Finset ℕ) (π : ℕ) (q : Quad) : Prop :=
  ∀ s ∈ q.sides N, (IsPlus π s ↔ ¬ Meets N T s)

instance (N : ℕ) (T : Finset ℕ) (π : ℕ) : DecidablePred (GoodQ N T π) := fun _ => by
  unfold GoodQ IsPlus; infer_instance

/-- Number of `T`-live `−` slots of `q`. -/
def dMinus (N : ℕ) (T : Finset ℕ) (π : ℕ) (q : Quad) : ℕ :=
  ((q.sides N).filter fun s => decide (¬ IsPlus π s ∧ Meets N T s)).length

/-- Number of `T`-live `+` slots of `q`. -/
def dPlus (N : ℕ) (T : Finset ℕ) (π : ℕ) (q : Quad) : ℕ :=
  ((q.sides N).filter fun s => decide (IsPlus π s ∧ Meets N T s)).length

/-- The Steiner quads: at least two `T`-live sides. -/
def steiner (N : ℕ) (T : Finset ℕ) (π : ℕ) (G : Finset (ℕ × ℕ)) : Finset Quad :=
  (quads N G).filter fun q => 2 ≤ dMinus N T π q + dPlus N T π q

/-- A diagonal `(i, j)` splits `T`: both of its blocks (legs `i..j−1` and the rest) contain legs of `T`. -/
def Splits (T : Finset ℕ) (d : ℕ × ℕ) : Prop :=
  (∃ t ∈ T, d.1 ≤ t ∧ t < d.2) ∧ (∃ t ∈ T, t < d.1 ∨ d.2 ≤ t)

instance (T : Finset ℕ) : DecidablePred (Splits T) := fun _ => by unfold Splits; infer_instance

/-! ## Structural lemmas (PROOFS §0.1, Lemma 0.1): statements; 3b targets -/

/-! ## Faces of a quadrangulation and the descent walk (3b) -/

lemma p3b_npair {N u v : ℕ} (hu : 1 ≤ u) (huv : u ≤ v) (hv : v ≤ N) : npair N u v = (u, v) := by
  unfold npair
  rw [vtx_of_mem hu (by omega), vtx_of_mem (by omega) hv, min_eq_left huv, max_eq_right huv]

lemma p3b_npair_close {N a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ N) : npair N b (a + N) = (a, b) := by
  unfold npair
  rw [vtx_add_n, vtx_of_mem ha (by omega), vtx_of_mem (by omega) hb, min_eq_right hab, max_eq_left hab]

/-- A side `(u, v)` strictly inside `1..N` is admissible iff it is in `G` or a polygon edge. -/
lemma p3b_sideOK_iff {N : ℕ} {G : Finset (ℕ × ℕ)} {u v : ℕ} (hu : 1 ≤ u) (huv : u < v) (hv : v ≤ N)
    (h1N : ¬ (u = 1 ∧ v = N)) : SideOK N G (u, v) ↔ (u, v) ∈ G ∨ v = u + 1 := by
  unfold SideOK
  rw [p3b_npair hu huv.le hv, mem_diagonals]
  dsimp only
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right; omega
  · rintro (h | h)
    · exact Or.inl h
    · right; omega

lemma p3b_sideOK_close {N : ℕ} {G : Finset (ℕ × ℕ)} {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ N)
    (h : (a, b) ∈ G ∨ (a = 1 ∧ b = N)) : SideOK N G (b, a + N) := by
  unfold SideOK
  rw [p3b_npair_close ha hab.le hb]
  rcases h with h | ⟨rfl, rfl⟩
  · exact Or.inl h
  · right; rw [mem_diagonals]; dsimp only; omega

lemma p3b_mem_quadIdx {N : ℕ} {q : Quad} :
    q ∈ quadIdx N ↔ 1 ≤ q.u1 ∧ q.u1 < q.u2 ∧ q.u2 < q.u3 ∧ q.u3 < q.u4 ∧ q.u4 ≤ N := by
  obtain ⟨a, b, c, d⟩ := q
  simp only [quadIdx, mem_biUnion, mem_image, mem_Icc, mem_Ioc, Quad.mk.injEq]
  constructor
  · rintro ⟨a', ⟨h1, _⟩, b', ⟨h2, _⟩, c', ⟨h3, _⟩, d', ⟨h4, h5⟩, rfl, rfl, rfl, rfl⟩
    exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨a, ⟨h1, by omega⟩, b, ⟨h2, by omega⟩, c, ⟨h3, by omega⟩, d, ⟨h4, h5⟩, rfl, rfl, rfl, rfl⟩

lemma p3b_mem_quads {N : ℕ} {G : Finset (ℕ × ℕ)} {a b c d : ℕ}
    (h : 1 ≤ a ∧ a < b ∧ b < c ∧ c < d ∧ d ≤ N) (s1 : SideOK N G (a, b)) (s2 : SideOK N G (b, c))
    (s3 : SideOK N G (c, d)) (s4 : SideOK N G (d, a + N)) : (⟨a, b, c, d⟩ : Quad) ∈ quads N G := by
  refine mem_filter.2 ⟨p3b_mem_quadIdx.2 h, ?_⟩
  intro s hs
  simp only [Quad.sides, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl <;> assumption

lemma p3b_sides_of_mem {N : ℕ} {G : Finset (ℕ × ℕ)} {q : Quad} (hq : q ∈ quads N G) :
    (1 ≤ q.u1 ∧ q.u1 < q.u2 ∧ q.u2 < q.u3 ∧ q.u3 < q.u4 ∧ q.u4 ≤ N) ∧ SideOK N G (q.u1, q.u2) ∧
      SideOK N G (q.u2, q.u3) ∧ SideOK N G (q.u3, q.u4) := by
  obtain ⟨h1, h2⟩ := mem_filter.1 hq
  exact ⟨p3b_mem_quadIdx.1 h1, h2 _ (by simp [Quad.sides]), h2 _ (by simp [Quad.sides]),
    h2 _ (by simp [Quad.sides])⟩

lemma p3b_odd_of_mem {N : ℕ} {G : Finset (ℕ × ℕ)} (hG : G ⊆ oddDiagonals N) {d : ℕ × ℕ} (hd : d ∈ G) :
    1 ≤ d.1 ∧ d.2 ≤ N ∧ d.1 + 2 ≤ d.2 ∧ ¬ (d.1 = 1 ∧ d.2 = N) ∧ (d.2 - d.1) % 2 = 1 := by
  have := mem_filter.1 (hG hd)
  have h2 := mem_diagonals.1 this.1
  exact ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2, this.2⟩

lemma p3b_quads_alternating {N : ℕ} {G : Finset (ℕ × ℕ)} (hG : G ⊆ oddDiagonals N) {q : Quad}
    (hq : q ∈ quads N G) : q.Alternating := by
  obtain ⟨hb, s1, s2, s3⟩ := p3b_sides_of_mem hq
  have odd : ∀ u v, 1 ≤ u → u < v → v ≤ N → ¬ (u = 1 ∧ v = N) → SideOK N G (u, v) → (u + v) % 2 = 1 := by
    intro u v hu huv hv h1N hs
    rcases (p3b_sideOK_iff hu huv hv h1N).1 hs with h | h
    · have := p3b_odd_of_mem hG h
      dsimp only at this
      omega
    · omega
  exact ⟨odd _ _ hb.1 hb.2.1 (by omega) (by omega) s1, odd _ _ (by omega) hb.2.2.1 (by omega) (by omega) s2,
    odd _ _ (by omega) hb.2.2.2.1 hb.2.2.2.2 (by omega) s3⟩

/-- **Face existence** (the quadrangulation analogue of Phase 1's `exists_apex`): every base `(a, b)` — a diagonal
of `G`, or the root `(1, N)` — has a quad `a < u₂ < u₃ < b` of `G` on its inner side. `u₂` is the farthest vertex
joined to `a`, `u₃` the nearest joined to `b`; parity separates them and maximality supplies `(u₂, u₃)`. -/
lemma p3b_face {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {G : Finset (ℕ × ℕ)} (hQ : IsQuadrangulation N G)
    {a b : ℕ} (hab : (a, b) ∈ G ∨ (a = 1 ∧ b = N)) :
    ∃ u2 u3, a < u2 ∧ u2 < u3 ∧ u3 < b ∧ ((a, u2) ∈ G ∨ u2 = a + 1) ∧ ((u2, u3) ∈ G ∨ u3 = u2 + 1) ∧
      ((u3, b) ∈ G ∨ b = u3 + 1) := by
  obtain ⟨hGs, hnc, hmax⟩ := hQ
  have odd := fun {d : ℕ × ℕ} (hd : d ∈ G) => p3b_odd_of_mem hGs hd
  have hb0 : 1 ≤ a ∧ b ≤ N ∧ a + 3 ≤ b ∧ (b - a) % 2 = 1 := by
    rcases hab with h | ⟨rfl, rfl⟩
    · have := odd h; dsimp only at this; omega
    · omega
  -- u₂: the farthest vertex joined to `a`
  set SL := (Ioo a b).filter (fun j => j = a + 1 ∨ (a, j) ∈ G) with hSL
  have hSLne : SL.Nonempty := ⟨a + 1, mem_filter.2 ⟨mem_Ioo.2 ⟨by omega, by omega⟩, Or.inl rfl⟩⟩
  set u2 := SL.max' hSLne with hu2
  have hu2m := mem_filter.1 (SL.max'_mem hSLne)
  rw [← hu2, mem_Ioo] at hu2m
  have hu2max : ∀ j, a < j → j < b → (a, j) ∈ G → j ≤ u2 := fun j h1 h2 h3 =>
    SL.le_max' j (mem_filter.2 ⟨mem_Ioo.2 ⟨h1, h2⟩, Or.inr h3⟩)
  -- u₃: the nearest vertex joined to `b`
  set SR := (Ioo a b).filter (fun j => j = b - 1 ∨ (j, b) ∈ G) with hSR
  have hSRne : SR.Nonempty := ⟨b - 1, mem_filter.2 ⟨mem_Ioo.2 ⟨by omega, by omega⟩, Or.inl rfl⟩⟩
  set u3 := SR.min' hSRne with hu3
  have hu3m := mem_filter.1 (SR.min'_mem hSRne)
  rw [← hu3, mem_Ioo] at hu3m
  have hu3min : ∀ j, a < j → j < b → (j, b) ∈ G → u3 ≤ j := fun j h1 h2 h3 =>
    SR.min'_le j (mem_filter.2 ⟨mem_Ioo.2 ⟨h1, h2⟩, Or.inr h3⟩)
  have p2 : (u2 - a) % 2 = 1 := by
    rcases hu2m.2 with h | h
    · omega
    · have := odd h; dsimp only at this; omega
  have p3 : (b - u3) % 2 = 1 := by
    rcases hu3m.2 with h | h
    · omega
    · have := odd h; dsimp only at this; omega
  have h23 : u2 < u3 := by
    by_contra hc
    have hne : u2 ≠ u3 := by intro h; rw [h] at p2; omega
    rcases hu2m.2 with h2 | h2
    · omega
    rcases hu3m.2 with h3 | h3
    · omega
    exact hnc _ h2 _ h3 (by simp only [Crosses]; omega)
  refine ⟨u2, u3, hu2m.1.1, h23, hu3m.1.2, hu2m.2.symm, ?_, hu3m.2.symm.imp_right fun h => by omega⟩
  by_cases hadj : u3 = u2 + 1
  · exact Or.inr hadj
  left
  by_contra hnot
  have hdo : (u2, u3) ∈ oddDiagonals N :=
    mem_filter.2 ⟨mem_diagonals.2 (by dsimp only; omega), by dsimp only; omega⟩
  obtain ⟨⟨c, e⟩, hp, hcr⟩ := hmax _ hdo hnot
  have hpo := odd hp
  dsimp only at hpo
  simp only [Crosses] at hcr
  rcases hcr with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · -- `c < u₂ < e < u₃`
    rcases lt_trichotomy c a with hca | rfl | hca
    · rcases hab with hab | ⟨rfl, rfl⟩
      · exact hnc _ hp _ hab (by simp only [Crosses]; omega)
      · omega
    · have := hu2max e (by omega) (by omega) hp; omega
    · rcases hu2m.2 with h | h
      · omega
      · exact hnc _ h _ hp (by simp only [Crosses]; omega)
  · -- `u₂ < c < u₃ < e`
    rcases lt_trichotomy e b with heb | rfl | heb
    · rcases hu3m.2 with h | h
      · omega
      · exact hnc _ hp _ h (by simp only [Crosses]; omega)
    · have := hu3min c (by omega) (by omega) hp; omega
    · rcases hab with hab | ⟨rfl, rfl⟩
      · exact hnc _ hab _ hp (by simp only [Crosses]; omega)
      · omega

lemma p3b_meets_child {N : ℕ} {T : Finset ℕ} {u v : ℕ} (hu : 1 ≤ u) (hv : v ≤ N) :
    Meets N T (u, v) ↔ ∃ t ∈ T, u ≤ t ∧ t < v := by
  unfold Meets blk
  dsimp only
  constructor
  · rintro ⟨x, hx, hxT⟩
    rw [mem_Icc] at hx
    rw [vtx_of_mem (by omega) (by omega)] at hxT
    exact ⟨x, hxT, by omega, by omega⟩
  · rintro ⟨t, ht, h1, h2⟩
    exact ⟨t, mem_Icc.2 ⟨h1, by omega⟩, by rw [vtx_of_mem (by omega) (by omega)]; exact ht⟩

lemma p3b_meets_close {N : ℕ} {T : Finset ℕ} (hT : T ⊆ Icc 1 N) {a b : ℕ} (ha : 1 ≤ a) (hab : a < b)
    (hb : b ≤ N) : Meets N T (b, a + N) ↔ ∃ t ∈ T, t < a ∨ b ≤ t := by
  unfold Meets blk
  dsimp only
  constructor
  · rintro ⟨x, hx, hxT⟩
    rw [mem_Icc] at hx
    rcases Nat.lt_or_ge N x with hxN | hxN
    · have e := vtx_add_n N (x - N)
      have e2 : vtx N (x - N) = x - N := vtx_of_mem (by omega) (by omega)
      rw [show x - N + N = x by omega, e2] at e
      rw [e] at hxT
      exact ⟨x - N, hxT, Or.inl (by omega)⟩
    · rw [vtx_of_mem (by omega) hxN] at hxT
      exact ⟨x, hxT, Or.inr (by omega)⟩
  · rintro ⟨t, ht, h⟩
    have := mem_Icc.1 (hT ht)
    rcases h with h | h
    · exact ⟨t + N, mem_Icc.2 ⟨by omega, by omega⟩, by rw [vtx_add_n, vtx_of_mem (by omega) (by omega)]; exact ht⟩
    · exact ⟨t, mem_Icc.2 ⟨h, by omega⟩, by rw [vtx_of_mem (by omega) (by omega)]; exact ht⟩

lemma p3b_goodQ_mk {N : ℕ} {T : Finset ℕ} {π a b c d : ℕ} (h1 : a % 2 = π ↔ ¬ Meets N T (a, b))
    (h2 : b % 2 = π ↔ ¬ Meets N T (b, c)) (h3 : c % 2 = π ↔ ¬ Meets N T (c, d))
    (h4 : d % 2 = π ↔ ¬ Meets N T (d, a + N)) : GoodQ N T π ⟨a, b, c, d⟩ := by
  intro s hs
  simp only [Quad.sides, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4

/-- The walk hypothesis at a base `(a, b)`: its inner block (legs `a..b−1`) meets `T`, and either its closing side
is a live `−` slot, or all of `T` lies inside. -/
def p3b_H (T : Finset ℕ) (π a b : ℕ) : Prop :=
  (∃ t ∈ T, a ≤ t ∧ t < b) ∧ ((b % 2 ≠ π ∧ ∃ t ∈ T, t < a ∨ b ≤ t) ∨ (∀ t ∈ T, a ≤ t ∧ t < b))

/-- **The descent walk** (thread R12-P3a C6, run top-down from the root): under `p3b_H` the subtree below the base
`(a, b)` contains a good quad. Induction on `b − a`. -/
lemma p3b_walk {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {G : Finset (ℕ × ℕ)} (hQ : IsQuadrangulation N G)
    {T : Finset ℕ} {π : ℕ} (hπ : π < 2) (hT1 : T ⊆ Icc 1 N) (hT2 : 2 ≤ T.card)
    (hpar : ∀ t ∈ T, t % 2 ≠ π) :
    ∀ n a b, b - a ≤ n → ((a, b) ∈ G ∨ (a = 1 ∧ b = N)) → p3b_H T π a b →
      ∃ q ∈ quads N G, GoodQ N T π q := by
  obtain ⟨t0, ht0, t1, ht1, ht01⟩ := one_lt_card.1 (by omega : 1 < T.card)
  have hTN : ∀ t ∈ T, 1 ≤ t ∧ t ≤ N := fun t ht => mem_Icc.1 (hT1 ht)
  intro n
  induction n with
  | zero =>
    intro a b hn hab _
    rcases hab with hab | ⟨rfl, rfl⟩
    · have := p3b_odd_of_mem hQ.1 hab; dsimp only at this; omega
    · omega
  | succ n ih =>
    intro a b hn hab hH
    have hb0 : 1 ≤ a ∧ b ≤ N ∧ a + 3 ≤ b ∧ (b - a) % 2 = 1 := by
      rcases hab with h | ⟨rfl, rfl⟩
      · have := p3b_odd_of_mem hQ.1 h; dsimp only at this; omega
      · omega
    obtain ⟨u2, u3, h12, h23, h34, s1, s2, s3⟩ := p3b_face hN hE hQ hab
    have hq : (⟨a, u2, u3, b⟩ : Quad) ∈ quads N G :=
      p3b_mem_quads ⟨hb0.1, h12, h23, h34, hb0.2.1⟩
        ((p3b_sideOK_iff hb0.1 h12 (by omega) (by omega)).2 s1)
        ((p3b_sideOK_iff (by omega) h23 (by omega) (by omega)).2 s2)
        ((p3b_sideOK_iff (by omega) h34 hb0.2.1 (by omega)).2 (s3.imp_right (by omega)))
        (p3b_sideOK_close hb0.1 (by omega) hb0.2.1 hab)
    obtain ⟨p12, p23, p34⟩ := p3b_quads_alternating hQ.1 hq
    dsimp only at p12 p23 p34
    -- recursion into a child side `(u, v)`
    have hrec : ∀ u v, ((u, v) ∈ G ∨ v = u + 1) → v - u < b - a → p3b_H T π u v →
        ∃ q ∈ quads N G, GoodQ N T π q := by
      intro u v huv hlt hHuv
      rcases huv with huv | huv
      · exact ih u v (by omega) (Or.inl huv) hHuv
      · exfalso
        obtain ⟨⟨t, ht, h1, h2⟩, hH2⟩ := hHuv
        have htu : t = u := by omega
        subst htu
        rcases hH2 with ⟨hp, -⟩ | hall
        · have := hpar t ht; omega
        · have := hall t0 ht0; have := hall t1 ht1; omega
    have lt1 : u2 - a < b - a := by omega
    have lt2 : u3 - u2 < b - a := by omega
    have lt3 : b - u3 < b - a := by omega
    have q1 : a % 2 = π → u2 % 2 ≠ π := by omega
    have q2 : u2 % 2 = π → u3 % 2 ≠ π := by omega
    have q3 : u3 % 2 = π → b % 2 ≠ π := by omega
    -- a `+` child side that is live and whose outside is live: recurse (first disjunct)
    by_cases r1 : a % 2 = π ∧ (∃ t ∈ T, a ≤ t ∧ t < u2) ∧ ∃ t ∈ T, t < a ∨ u2 ≤ t
    · exact hrec a u2 s1 lt1 ⟨r1.2.1, Or.inl ⟨q1 r1.1, r1.2.2⟩⟩
    by_cases r2 : u2 % 2 = π ∧ (∃ t ∈ T, u2 ≤ t ∧ t < u3) ∧ ∃ t ∈ T, t < u2 ∨ u3 ≤ t
    · exact hrec u2 u3 s2 lt2 ⟨r2.2.1, Or.inl ⟨q2 r2.1, r2.2.2⟩⟩
    by_cases r3 : u3 % 2 = π ∧ (∃ t ∈ T, u3 ≤ t ∧ t < b) ∧ ∃ t ∈ T, t < u3 ∨ b ≤ t
    · exact hrec u3 b s3 lt3 ⟨r3.2.1, Or.inl ⟨q3 r3.1, r3.2.2⟩⟩
    -- a child side containing all of `T`: recurse (second disjunct)
    by_cases a1 : ∀ t ∈ T, a ≤ t ∧ t < u2
    · exact hrec a u2 s1 lt1 ⟨⟨t0, ht0, a1 t0 ht0⟩, Or.inr a1⟩
    by_cases a2 : ∀ t ∈ T, u2 ≤ t ∧ t < u3
    · exact hrec u2 u3 s2 lt2 ⟨⟨t0, ht0, a2 t0 ht0⟩, Or.inr a2⟩
    by_cases a3 : ∀ t ∈ T, u3 ≤ t ∧ t < b
    · exact hrec u3 b s3 lt3 ⟨⟨t0, ht0, a3 t0 ht0⟩, Or.inr a3⟩
    -- otherwise the face itself is good
    -- the four blocks
    have mc1 := p3b_meets_child (T := T) hb0.1 (show u2 ≤ N by omega)
    have mc2 := p3b_meets_child (T := T) (show 1 ≤ u2 by omega) (show u3 ≤ N by omega)
    have mc3 := p3b_meets_child (T := T) (show 1 ≤ u3 by omega) hb0.2.1
    have mc0 := p3b_meets_close hT1 hb0.1 (show a < b by omega) hb0.2.1
    obtain ⟨⟨ti, hti, hti1, hti2⟩, hH2⟩ := hH
    -- a `+` child side is dead
    have d1 : a % 2 = π → ¬ ∃ t ∈ T, a ≤ t ∧ t < u2 := by
      intro hp hl
      apply a1
      intro t ht
      by_contra hc
      exact r1 ⟨hp, hl, t, ht, by have := hTN t ht; omega⟩
    have d2 : u2 % 2 = π → ¬ ∃ t ∈ T, u2 ≤ t ∧ t < u3 := by
      intro hp hl
      apply a2
      intro t ht
      by_contra hc
      exact r2 ⟨hp, hl, t, ht, by have := hTN t ht; omega⟩
    have d3 : u3 % 2 = π → ¬ ∃ t ∈ T, u3 ≤ t ∧ t < b := by
      intro hp hl
      apply a3
      intro t ht
      by_contra hc
      exact r3 ⟨hp, hl, t, ht, by have := hTN t ht; omega⟩
    by_cases hp : a % 2 = π
    · -- slots `+ − + −`: the `+` children are dead, the middle child and the closing side are live
      have hp2 : u2 % 2 ≠ π := by omega
      have hp3 : u3 % 2 = π := by omega
      have hp0 : b % 2 ≠ π := by omega
      have n1 : ∀ t ∈ T, ¬ (a ≤ t ∧ t < u2) := fun t ht h => d1 hp ⟨t, ht, h⟩
      have n3 : ∀ t ∈ T, ¬ (u3 ≤ t ∧ t < b) := fun t ht h => d3 hp3 ⟨t, ht, h⟩
      have l2 : ∃ t ∈ T, u2 ≤ t ∧ t < u3 := ⟨ti, hti, by have := n1 ti hti; have := n3 ti hti; omega⟩
      have l0 : ∃ t ∈ T, t < a ∨ b ≤ t := by
        rcases hH2 with ⟨-, h⟩ | hall
        · exact h
        · exfalso
          exact a2 fun t ht => by have := hall t ht; have := n1 t ht; have := n3 t ht; omega
      refine ⟨_, hq, p3b_goodQ_mk ?_ ?_ ?_ ?_⟩
      · rw [mc1]; exact ⟨fun _ ⟨t, ht, h⟩ => n1 t ht h, fun _ => hp⟩
      · rw [mc2]; exact ⟨fun h => absurd h hp2, fun h => absurd l2 h⟩
      · rw [mc3]; exact ⟨fun _ ⟨t, ht, h⟩ => n3 t ht h, fun _ => hp3⟩
      · rw [mc0]; exact ⟨fun h => absurd h hp0, fun h => absurd l0 h⟩
    · -- slots `− + − +`: the middle child is dead, so all of `T` is inside and split between children 1, 3
      have hp2 : u2 % 2 = π := by omega
      have hp3 : u3 % 2 ≠ π := by omega
      have hp0 : b % 2 = π := by omega
      have n2 : ∀ t ∈ T, ¬ (u2 ≤ t ∧ t < u3) := fun t ht h => d2 hp2 ⟨t, ht, h⟩
      have hall : ∀ t ∈ T, a ≤ t ∧ t < b := by
        rcases hH2 with ⟨h, -⟩ | hall
        · exact absurd hp0 h
        · exact hall
      have l1 : ∃ t ∈ T, a ≤ t ∧ t < u2 := by
        by_contra hc
        exact a3 fun t ht => by
          have := hall t ht; have := n2 t ht
          have h' : ¬ (a ≤ t ∧ t < u2) := fun h => hc ⟨t, ht, h⟩
          omega
      have l3 : ∃ t ∈ T, u3 ≤ t ∧ t < b := by
        by_contra hc
        exact a1 fun t ht => by
          have := hall t ht; have := n2 t ht
          have h' : ¬ (u3 ≤ t ∧ t < b) := fun h => hc ⟨t, ht, h⟩
          omega
      have n0 : ¬ ∃ t ∈ T, t < a ∨ b ≤ t := fun ⟨t, ht, h⟩ => by have := hall t ht; omega
      refine ⟨_, hq, p3b_goodQ_mk ?_ ?_ ?_ ?_⟩
      · rw [mc1]; exact ⟨fun h => absurd h hp, fun h => absurd l1 h⟩
      · rw [mc2]; exact ⟨fun _ ⟨t, ht, h⟩ => n2 t ht h, fun _ => hp2⟩
      · rw [mc3]; exact ⟨fun h => absurd h hp3, fun h => absurd l3 h⟩
      · rw [mc0]; exact ⟨fun _ => n0, fun _ => hp0⟩

theorem p3b_exists_goodQ {N r : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (hr : r < 2) {T : Finset ℕ}
    (hT : Admissible N r T) {G : Finset (ℕ × ℕ)} (hG : G ∈ quadrangulations N) :
    ∃ q ∈ quads N G, GoodQ N T (1 - r) q := by
  have hQ : IsQuadrangulation N G := (mem_filter.1 hG).2
  obtain ⟨hT1, hT2, hT3⟩ := hT
  have hpar : ∀ t ∈ T, t % 2 ≠ 1 - r := fun t ht => by have := hT3 t ht; omega
  have walk := p3b_walk hN hE hQ (by omega : 1 - r < 2) hT1 hT2 hpar N 1 N (by omega) (Or.inr ⟨rfl, rfl⟩)
  obtain ⟨t0, ht0, t1, ht1, ht01⟩ := one_lt_card.1 (by omega : 1 < T.card)
  have h0 := mem_Icc.1 (hT1 ht0)
  have h1 := mem_Icc.1 (hT1 ht1)
  by_cases hNT : N ∈ T
  · apply walk
    refine ⟨?_, Or.inl ⟨by have := hpar N hNT; omega, N, hNT, Or.inr le_rfl⟩⟩
    by_cases h : t0 = N
    · exact ⟨t1, ht1, by omega, by omega⟩
    · exact ⟨t0, ht0, by omega, by omega⟩
  · apply walk
    have hlt : ∀ t ∈ T, 1 ≤ t ∧ t < N := fun t ht => by
      have := mem_Icc.1 (hT1 ht); have : t ≠ N := fun h => hNT (h ▸ ht); omega
    exact ⟨⟨t0, ht0, hlt t0 ht0⟩, Or.inr hlt⟩

/-! ## Lemma 0.1: faces are determined by their base; each leg / diagonal is a side of one / two faces (3b) -/

/-- Everything a face of `G` knows about its corners. -/
lemma p3b_qf {N : ℕ} {G : Finset (ℕ × ℕ)} (hG : G ⊆ oddDiagonals N) {q : Quad} (hq : q ∈ quads N G) :
    (1 ≤ q.u1 ∧ q.u1 < q.u2 ∧ q.u2 < q.u3 ∧ q.u3 < q.u4 ∧ q.u4 ≤ N) ∧
    ((q.u1, q.u2) ∈ G ∨ q.u2 = q.u1 + 1) ∧ ((q.u2, q.u3) ∈ G ∨ q.u3 = q.u2 + 1) ∧
    ((q.u3, q.u4) ∈ G ∨ q.u4 = q.u3 + 1) ∧ ((q.u1, q.u4) ∈ G ∨ (q.u1 = 1 ∧ q.u4 = N)) ∧
    (q.u1 + q.u2) % 2 = 1 ∧ (q.u2 + q.u3) % 2 = 1 ∧ (q.u3 + q.u4) % 2 = 1 := by
  obtain ⟨hb, s1, s2, s3⟩ := p3b_sides_of_mem hq
  obtain ⟨p1, p2, p3⟩ := p3b_quads_alternating hG hq
  have s4 : SideOK N G (q.u4, q.u1 + N) := (mem_filter.1 hq).2 _ (by simp [Quad.sides])
  unfold SideOK at s4
  rw [p3b_npair_close hb.1 (by omega) hb.2.2.2.2, mem_diagonals] at s4
  dsimp only at s4
  refine ⟨hb, (p3b_sideOK_iff hb.1 hb.2.1 (by omega) (by omega)).1 s1,
    (p3b_sideOK_iff (by omega) hb.2.2.1 (by omega) (by omega)).1 s2,
    (p3b_sideOK_iff (by omega) hb.2.2.2.1 hb.2.2.2.2 (by omega)).1 s3, ?_, p1, p2, p3⟩
  rcases s4 with h | h
  · exact Or.inl h
  · right; omega

/-- A face as a quad of `G` on the inner side of a base. -/
lemma p3b_face_quad {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {G : Finset (ℕ × ℕ)} (hQ : IsQuadrangulation N G)
    {a b : ℕ} (hab : (a, b) ∈ G ∨ (a = 1 ∧ b = N)) : ∃ q ∈ quads N G, q.u1 = a ∧ q.u4 = b := by
  have hb0 : 1 ≤ a ∧ b ≤ N ∧ a + 3 ≤ b := by
    rcases hab with h | ⟨rfl, rfl⟩
    · have := p3b_odd_of_mem hQ.1 h; dsimp only at this; omega
    · omega
  obtain ⟨u2, u3, h12, h23, h34, s1, s2, s3⟩ := p3b_face hN hE hQ hab
  exact ⟨⟨a, u2, u3, b⟩, p3b_mem_quads ⟨hb0.1, h12, h23, h34, hb0.2.1⟩
    ((p3b_sideOK_iff hb0.1 h12 (by omega) (by omega)).2 s1)
    ((p3b_sideOK_iff (by omega) h23 (by omega) (by omega)).2 s2)
    ((p3b_sideOK_iff (by omega) h34 hb0.2.1 (by omega)).2 s3)
    (p3b_sideOK_close hb0.1 (by omega) hb0.2.1 hab), rfl, rfl⟩

/-- A diagonal of `G` inside a face's base (and not the base) lies inside one of the face's three child blocks. -/
lemma p3b_within {N : ℕ} {G : Finset (ℕ × ℕ)} (hQ : IsQuadrangulation N G) {q : Quad} (hq : q ∈ quads N G)
    {c e : ℕ} (hp : (c, e) ∈ G) (h1 : q.u1 ≤ c) (h2 : e ≤ q.u4) (hne : ¬ (c = q.u1 ∧ e = q.u4)) :
    (e ≤ q.u2) ∨ (q.u2 ≤ c ∧ e ≤ q.u3) ∨ (q.u3 ≤ c) := by
  obtain ⟨hb, s1, s2, s3, -, p1, p2, p3⟩ := p3b_qf hQ.1 hq
  have hnc := hQ.2.1
  have hpo := p3b_odd_of_mem hQ.1 hp
  dsimp only at hpo
  by_cases st2 : c < q.u2 ∧ q.u2 < e
  · exfalso
    rcases Nat.lt_or_ge q.u1 c with hc | hc
    · rcases s1 with s1 | s1
      · exact hnc _ s1 _ hp (by simp only [Crosses]; omega)
      · omega
    · have hc' : c = q.u1 := by omega
      subst hc'
      rcases Nat.lt_or_ge e q.u3 with he | he
      · rcases s2 with s2 | s2
        · exact hnc _ hp _ s2 (by simp only [Crosses]; omega)
        · omega
      · rcases Nat.lt_or_ge q.u3 e with he' | he'
        · rcases s3 with s3 | s3
          · exact hnc _ hp _ s3 (by simp only [Crosses]; omega)
          · omega
        · omega
  by_cases st3 : c < q.u3 ∧ q.u3 < e
  · exfalso
    rcases Nat.lt_or_ge q.u2 c with hc | hc
    · rcases s2 with s2 | s2
      · exact hnc _ s2 _ hp (by simp only [Crosses]; omega)
      · omega
    · have hc' : c = q.u2 := by omega
      subst hc'
      rcases Nat.lt_or_ge e q.u4 with he | he
      · rcases s3 with s3 | s3
        · exact hnc _ hp _ s3 (by simp only [Crosses]; omega)
        · omega
      · omega
  omega

/-- A face is determined by its base. -/
lemma p3b_eq_of_base {N : ℕ} {G : Finset (ℕ × ℕ)} (hQ : IsQuadrangulation N G) {q q' : Quad}
    (hq : q ∈ quads N G) (hq' : q' ∈ quads N G) (h1 : q.u1 = q'.u1) (h4 : q.u4 = q'.u4) : q = q' := by
  have le2 : ∀ {q q' : Quad}, q ∈ quads N G → q' ∈ quads N G → q.u1 = q'.u1 → q.u4 = q'.u4 →
      q'.u2 ≤ q.u2 ∧ q.u3 ≤ q'.u3 := by
    intro q q' hq hq' h1 h4
    obtain ⟨hb, -⟩ := p3b_qf hQ.1 hq
    obtain ⟨hb', s1', -, s3', -⟩ := p3b_qf hQ.1 hq'
    constructor
    · rcases s1' with s | s
      · have := p3b_within hQ hq (c := q'.u1) (e := q'.u2) s (by omega) (by omega) (by omega)
        omega
      · omega
    · rcases s3' with s | s
      · have := p3b_within hQ hq (c := q'.u3) (e := q'.u4) s (by omega) (by omega) (by omega)
        omega
      · omega
  obtain ⟨a2, a3⟩ := le2 hq hq' h1 h4
  obtain ⟨b2, b3⟩ := le2 hq' hq h1.symm h4.symm
  cases q; cases q'
  simp only [Quad.mk.injEq] at *
  omega

/-- `(c, e)` is one of the three child sides of `q`. -/
def p3b_IsChild (q : Quad) (c e : ℕ) : Prop :=
  (c = q.u1 ∧ e = q.u2) ∨ (c = q.u2 ∧ e = q.u3) ∨ (c = q.u3 ∧ e = q.u4)

/-- A pair `(c, e)` is a child side of at most one face (the parent). -/
lemma p3b_child_unique {N : ℕ} {G : Finset (ℕ × ℕ)} (hQ : IsQuadrangulation N G) {q q' : Quad}
    (hq : q ∈ quads N G) (hq' : q' ∈ quads N G) {c e : ℕ} (hc : p3b_IsChild q c e)
    (hc' : p3b_IsChild q' c e) : q = q' := by
  have one : ∀ {q q' : Quad}, q ∈ quads N G → q' ∈ quads N G → p3b_IsChild q c e → p3b_IsChild q' c e →
      q.u1 ≤ q'.u1 → q'.u4 ≤ q.u4 → q = q' := by
    intro q q' hq hq' hc hc' ha hb
    obtain ⟨hbq, -, -, -, hB, -⟩ := p3b_qf hQ.1 hq
    obtain ⟨hbq', -, -, -, hB', -⟩ := p3b_qf hQ.1 hq'
    unfold p3b_IsChild at hc hc'
    by_cases heq : q.u1 = q'.u1 ∧ q.u4 = q'.u4
    · exact p3b_eq_of_base hQ hq hq' heq.1 heq.2
    · exfalso
      rcases hB' with hB' | hB'
      · have := p3b_within hQ hq hB' ha hb (by omega)
        omega
      · omega
  obtain ⟨hbq, -, -, -, hB, -⟩ := p3b_qf hQ.1 hq
  obtain ⟨hbq', -, -, -, hB', -⟩ := p3b_qf hQ.1 hq'
  have hc2 := hc
  have hc2' := hc'
  unfold p3b_IsChild at hc2 hc2'
  -- the two bases do not cross, and both contain `[c, e]`: they are nested
  have hnest : (q.u1 ≤ q'.u1 ∧ q'.u4 ≤ q.u4) ∨ (q'.u1 ≤ q.u1 ∧ q.u4 ≤ q'.u4) := by
    rcases hB with hB | hB
    · rcases hB' with hB' | hB'
      · have n1 := hQ.2.1 _ hB _ hB'
        have n2 := hQ.2.1 _ hB' _ hB
        simp only [Crosses] at n1 n2
        omega
      · omega
    · omega
  rcases hnest with h | h
  · exact one hq hq' hc hc' h.1 h.2
  · exact (one hq' hq hc' hc h.1 h.2).symm

/-- Every leg and every diagonal of `G` is a child side of some face (its parent). -/
lemma p3b_parent_exists {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {G : Finset (ℕ × ℕ)} (hQ : IsQuadrangulation N G)
    {c e : ℕ} (hx : (c, e) ∈ G ∨ (1 ≤ c ∧ e = c + 1 ∧ e ≤ N)) : ∃ q ∈ quads N G, p3b_IsChild q c e := by
  have hce : 1 ≤ c ∧ c < e ∧ e ≤ N ∧ ¬ (c = 1 ∧ e = N) := by
    rcases hx with h | h
    · have := p3b_odd_of_mem hQ.1 h; dsimp only at this; omega
    · omega
  have key : ∀ n a b, b - a ≤ n → ((a, b) ∈ G ∨ (a = 1 ∧ b = N)) → a ≤ c → e ≤ b → ¬ (a = c ∧ b = e) →
      ∃ q ∈ quads N G, p3b_IsChild q c e := by
    intro n
    induction n with
    | zero => intro a b h _ h1 h2 _; omega
    | succ n ih =>
      intro a b hn hab h1 h2 hne
      obtain ⟨q, hq, rfl, rfl⟩ := p3b_face_quad hN hE hQ hab
      obtain ⟨hb, s1, s2, s3, -⟩ := p3b_qf hQ.1 hq
      have hin : (e ≤ q.u2) ∨ (q.u2 ≤ c ∧ e ≤ q.u3) ∨ (q.u3 ≤ c) := by
        rcases hx with hx | hx
        · exact p3b_within hQ hq hx h1 h2 (by omega)
        · omega
      rcases hin with hin | hin | hin
      · by_cases he : c = q.u1 ∧ e = q.u2
        · exact ⟨q, hq, Or.inl he⟩
        · rcases s1 with s1 | s1
          · exact ih _ _ (by omega) (Or.inl s1) h1 hin (by omega)
          · omega
      · by_cases he : c = q.u2 ∧ e = q.u3
        · exact ⟨q, hq, Or.inr (Or.inl he)⟩
        · rcases s2 with s2 | s2
          · exact ih _ _ (by omega) (Or.inl s2) hin.1 hin.2 (by omega)
          · omega
      · by_cases he : c = q.u3 ∧ e = q.u4
        · exact ⟨q, hq, Or.inr (Or.inr he)⟩
        · rcases s3 with s3 | s3
          · exact ih _ _ (by omega) (Or.inl s3) hin h2 (by omega)
          · omega
  exact key N 1 N (by omega) (Or.inr ⟨rfl, rfl⟩) hce.1 hce.2.2.1 (by omega)

/-- The sides of a face through their `npair`s: children `(u₁,u₂), (u₂,u₃), (u₃,u₄)` and the base `(u₁,u₄)`. -/
lemma p3b_exists_side {N : ℕ} {q : Quad} (hb : 1 ≤ q.u1 ∧ q.u1 < q.u2 ∧ q.u2 < q.u3 ∧ q.u3 < q.u4 ∧ q.u4 ≤ N)
    (P : ℕ × ℕ → Prop) (x : ℕ × ℕ) :
    (∃ s ∈ q.sides N, npair N s.1 s.2 = x ∧ P s) ↔
      ((q.u1, q.u2) = x ∧ P (q.u1, q.u2)) ∨ ((q.u2, q.u3) = x ∧ P (q.u2, q.u3)) ∨
      ((q.u3, q.u4) = x ∧ P (q.u3, q.u4)) ∨ ((q.u1, q.u4) = x ∧ P (q.u4, q.u1 + N)) := by
  have e1 := p3b_npair (N := N) hb.1 (by omega) (show q.u2 ≤ N by omega)
  have e2 := p3b_npair (N := N) (show 1 ≤ q.u2 by omega) (show q.u2 ≤ q.u3 by omega) (show q.u3 ≤ N by omega)
  have e3 := p3b_npair (N := N) (show 1 ≤ q.u3 by omega) (show q.u3 ≤ q.u4 by omega) hb.2.2.2.2
  have e4 := p3b_npair_close (N := N) hb.1 (show q.u1 ≤ q.u4 by omega) hb.2.2.2.2
  constructor
  · rintro ⟨s, hs, h1, h2⟩
    simp only [Quad.sides, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact Or.inl ⟨e1 ▸ h1, h2⟩
    · exact Or.inr (Or.inl ⟨e2 ▸ h1, h2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨e3 ▸ h1, h2⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨e4 ▸ h1, h2⟩))
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨_, by simp [Quad.sides], by rw [e1]; exact h1, h2⟩
    · exact ⟨_, by simp [Quad.sides], by rw [e2]; exact h1, h2⟩
    · exact ⟨_, by simp [Quad.sides], by rw [e3]; exact h1, h2⟩
    · exact ⟨_, by simp [Quad.sides], by rw [e4]; exact h1, h2⟩

/-- The four sides of a face as chords (`npair`s): three children and the base. -/
def p3b_S (q : Quad) : Finset (ℕ × ℕ) := {(q.u1, q.u2), (q.u2, q.u3), (q.u3, q.u4), (q.u1, q.u4)}

lemma p3b_side_iff_S {N : ℕ} {q : Quad} (hb : 1 ≤ q.u1 ∧ q.u1 < q.u2 ∧ q.u2 < q.u3 ∧ q.u3 < q.u4 ∧ q.u4 ≤ N)
    (x : ℕ × ℕ) : (∃ s ∈ q.sides N, npair N s.1 s.2 = x) ↔ x ∈ p3b_S q := by
  have := p3b_exists_side hb (fun _ => True) x
  simp only [and_true] at this
  rw [this]
  simp only [p3b_S, mem_insert, mem_singleton]
  constructor
  · rintro (h | h | h | h) <;> simp [← h]
  · rintro (h | h | h | h) <;> simp [h]

lemma p3b_card_S {q : Quad} (hb : q.u1 < q.u2 ∧ q.u2 < q.u3 ∧ q.u3 < q.u4) : (p3b_S q).card = 4 := by
  unfold p3b_S
  rw [card_insert_of_notMem (by simp only [mem_insert, mem_singleton, Prod.mk.injEq]; omega),
    card_insert_of_notMem (by simp only [mem_insert, mem_singleton, Prod.mk.injEq]; omega),
    card_insert_of_notMem (by simp only [mem_singleton, Prod.mk.injEq]; omega), card_singleton]

lemma p3b_npair_leg {N a : ℕ} (hN : 2 ≤ N) (ha : 1 ≤ a ∧ a ≤ N) :
    npair N a (a + 1) = if a < N then (a, a + 1) else (1, N) := by
  split_ifs with h
  · exact p3b_npair ha.1 (by omega) (by omega)
  · have : a = N := by omega
    subst this
    unfold npair
    rw [show a + 1 = 1 + a by omega, vtx_add_n, vtx_of_mem le_rfl (by omega), vtx_of_mem ha.1 le_rfl,
      min_eq_right ha.1, max_eq_left ha.1]

/-- Lemma 0.1(i), counting form: each leg is a side of exactly one face. -/
lemma p3b_leg_count {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {G : Finset (ℕ × ℕ)} (hQ : IsQuadrangulation N G)
    {a : ℕ} (ha : 1 ≤ a ∧ a ≤ N) : ((quads N G).filter fun q => npair N a (a + 1) ∈ p3b_S q).card = 1 := by
  rw [card_eq_one, p3b_npair_leg (by omega) ha]
  split_ifs with haN
  · obtain ⟨q0, hq0, hc0⟩ := p3b_parent_exists hN hE hQ (Or.inr ⟨ha.1, rfl, by omega⟩)
    refine ⟨q0, ?_⟩
    ext q
    rw [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hq, hs⟩
      obtain ⟨hb, -⟩ := p3b_qf hQ.1 hq
      simp only [p3b_S, mem_insert, mem_singleton, Prod.mk.injEq] at hs
      exact p3b_child_unique hQ hq hq0 (by unfold p3b_IsChild; omega) hc0
    · rintro rfl
      refine ⟨hq0, ?_⟩
      unfold p3b_IsChild at hc0
      simp only [p3b_S, mem_insert, mem_singleton, Prod.mk.injEq]
      omega
  · obtain ⟨q0, hq0, h1, h4⟩ := p3b_face_quad hN hE hQ (Or.inr ⟨rfl, rfl⟩)
    refine ⟨q0, ?_⟩
    ext q
    rw [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hq, hs⟩
      obtain ⟨hb, -⟩ := p3b_qf hQ.1 hq
      simp only [p3b_S, mem_insert, mem_singleton, Prod.mk.injEq] at hs
      exact p3b_eq_of_base hQ hq hq0 (by omega) (by omega)
    · rintro rfl
      refine ⟨hq0, ?_⟩
      simp only [p3b_S, mem_insert, mem_singleton, Prod.mk.injEq]
      omega

/-- The two faces on a diagonal: its inner face (base) and its parent (child side); they differ. -/
lemma p3b_diag_faces {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {G : Finset (ℕ × ℕ)} (hQ : IsQuadrangulation N G)
    {c e : ℕ} (hd : (c, e) ∈ G) : ∃ qi ∈ quads N G, ∃ qo ∈ quads N G, qi.u1 = c ∧ qi.u4 = e ∧
      p3b_IsChild qo c e ∧ qi ≠ qo ∧
      ∀ q ∈ quads N G, (c, e) ∈ p3b_S q → q = qi ∨ q = qo := by
  obtain ⟨qi, hqi, h1, h4⟩ := p3b_face_quad hN hE hQ (Or.inl hd)
  obtain ⟨qo, hqo, hc⟩ := p3b_parent_exists hN hE hQ (Or.inl hd)
  obtain ⟨hbi, -⟩ := p3b_qf hQ.1 hqi
  obtain ⟨hbo, -⟩ := p3b_qf hQ.1 hqo
  refine ⟨qi, hqi, qo, hqo, h1, h4, hc, ?_, ?_⟩
  · rintro rfl
    unfold p3b_IsChild at hc
    omega
  · intro q hq hs
    simp only [p3b_S, mem_insert, mem_singleton, Prod.mk.injEq] at hs
    rcases hs with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩
    · exact Or.inr (p3b_child_unique hQ hq hqo (by unfold p3b_IsChild; omega) hc)
    · exact Or.inr (p3b_child_unique hQ hq hqo (by unfold p3b_IsChild; omega) hc)
    · exact Or.inr (p3b_child_unique hQ hq hqo (by unfold p3b_IsChild; omega) hc)
    · exact Or.inl (p3b_eq_of_base hQ hq hqi (by omega) (by omega))

lemma p3b_diag_count {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {G : Finset (ℕ × ℕ)} (hQ : IsQuadrangulation N G)
    {d : ℕ × ℕ} (hd : d ∈ G) : ((quads N G).filter fun q => d ∈ p3b_S q).card = 2 := by
  obtain ⟨c, e⟩ := d
  obtain ⟨qi, hqi, qo, hqo, h1, h4, hc, hne, hall⟩ := p3b_diag_faces hN hE hQ hd
  rw [card_eq_two]
  refine ⟨qi, qo, hne, ?_⟩
  ext q
  rw [mem_filter, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hq, hs⟩
    exact hall q hq hs
  · rintro (rfl | rfl)
    · refine ⟨hqi, ?_⟩
      simp only [p3b_S, mem_insert, mem_singleton, Prod.mk.injEq]
      omega
    · refine ⟨hqo, ?_⟩
      unfold p3b_IsChild at hc
      simp only [p3b_S, mem_insert, mem_singleton, Prod.mk.injEq]
      omega

/-- `diag_plus_minus` with the missing hypothesis `π < 2` (for `π ≥ 2` no slot is `+`; see
`p3b_diag_plus_minus_needs_pi_lt_two`). -/
lemma p3b_diag_plus_minus {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {G : Finset (ℕ × ℕ)}
    (hG : G ∈ quadrangulations N) {π : ℕ} (hπ : π < 2) {d : ℕ × ℕ} (hd : d ∈ G) :
    ((quads N G).filter fun q => ∃ s ∈ q.sides N, npair N s.1 s.2 = d ∧ IsPlus π s).card = 1 ∧
    ((quads N G).filter fun q => ∃ s ∈ q.sides N, npair N s.1 s.2 = d ∧ ¬ IsPlus π s).card = 1 := by
  have hQ : IsQuadrangulation N G := (mem_filter.1 hG).2
  obtain ⟨c, e⟩ := d
  have hpo := p3b_odd_of_mem hQ.1 hd
  dsimp only at hpo
  obtain ⟨qi, hqi, qo, hqo, h1, h4, hc, hne, hall⟩ := p3b_diag_faces hN hE hQ hd
  obtain ⟨hbi, -⟩ := p3b_qf hQ.1 hqi
  obtain ⟨hbo, -⟩ := p3b_qf hQ.1 hqo
  -- the slot of `(c, e)` in `qo` starts at `c`; in `qi` (closing side `(e, c + N)`) it starts at `e`
  have key : ∀ (P : ℕ → Prop), ∀ q ∈ quads N G,
      ((∃ s ∈ q.sides N, npair N s.1 s.2 = (c, e) ∧ P s.1) ↔ (q = qo ∧ P c) ∨ (q = qi ∧ P e)) := by
    intro P q hq
    obtain ⟨hb, -⟩ := p3b_qf hQ.1 hq
    rw [p3b_exists_side hb (fun s => P s.1)]
    unfold p3b_IsChild at hc
    constructor
    · rintro (⟨h, hP⟩ | ⟨h, hP⟩ | ⟨h, hP⟩ | ⟨h, hP⟩) <;> simp only [Prod.mk.injEq] at h
      · exact Or.inl ⟨p3b_child_unique hQ hq hqo (Or.inl ⟨h.1.symm, h.2.symm⟩) hc, h.1 ▸ hP⟩
      · exact Or.inl ⟨p3b_child_unique hQ hq hqo (Or.inr (Or.inl ⟨h.1.symm, h.2.symm⟩)) hc, h.1 ▸ hP⟩
      · exact Or.inl ⟨p3b_child_unique hQ hq hqo (Or.inr (Or.inr ⟨h.1.symm, h.2.symm⟩)) hc, h.1 ▸ hP⟩
      · exact Or.inr ⟨p3b_eq_of_base hQ hq hqi (by omega) (by omega), h.2 ▸ hP⟩
    · rintro (⟨rfl, hP⟩ | ⟨rfl, hP⟩)
      · rcases hc with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩
        · exact Or.inl ⟨by rw [h, h'], h ▸ hP⟩
        · exact Or.inr (Or.inl ⟨by rw [h, h'], h ▸ hP⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨by rw [h, h'], h ▸ hP⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨by rw [h1, h4], h4 ▸ hP⟩))
  have hplus := key (fun u => u % 2 = π)
  have hminus := key (fun u => ¬ u % 2 = π)
  constructor
  · rw [card_eq_one]
    by_cases hcπ : c % 2 = π
    · refine ⟨qo, ext fun q => ?_⟩
      rw [mem_filter, mem_singleton]
      constructor
      · rintro ⟨hq, hs⟩
        rcases (hplus q hq).1 hs with ⟨h, -⟩ | ⟨-, h⟩
        · exact h
        · omega
      · rintro h; rw [h]; exact ⟨hqo, (hplus qo hqo).2 (Or.inl ⟨rfl, hcπ⟩)⟩
    · refine ⟨qi, ext fun q => ?_⟩
      rw [mem_filter, mem_singleton]
      constructor
      · rintro ⟨hq, hs⟩
        rcases (hplus q hq).1 hs with ⟨-, h⟩ | ⟨h, -⟩
        · exact absurd h hcπ
        · exact h
      · rintro h; rw [h]; exact ⟨hqi, (hplus qi hqi).2 (Or.inr ⟨rfl, by omega⟩)⟩
  · rw [card_eq_one]
    by_cases hcπ : c % 2 = π
    · refine ⟨qi, ext fun q => ?_⟩
      rw [mem_filter, mem_singleton]
      constructor
      · rintro ⟨hq, hs⟩
        rcases (hminus q hq).1 hs with ⟨-, h⟩ | ⟨h, -⟩
        · exact absurd hcπ h
        · exact h
      · rintro h; rw [h]; exact ⟨hqi, (hminus qi hqi).2 (Or.inr ⟨rfl, by omega⟩)⟩
    · refine ⟨qo, ext fun q => ?_⟩
      rw [mem_filter, mem_singleton]
      constructor
      · rintro ⟨hq, hs⟩
        rcases (hminus q hq).1 hs with ⟨h, -⟩ | ⟨-, h⟩
        · exact h
        · omega
      · rintro h; rw [h]; exact ⟨hqo, (hminus qo hqo).2 (Or.inl ⟨rfl, hcπ⟩)⟩

/-- Counterexample to `diag_plus_minus` as frozen (`π` unconstrained): at `N = 6`, `G = {(1,4)}`, `π = 2`, no side is
a `+` slot, so the first count is `0`, not `1`. -/
theorem p3b_diag_plus_minus_needs_pi_lt_two :
    ({(1, 4)} : Finset (ℕ × ℕ)) ∈ quadrangulations 6 ∧
    ((quads 6 {(1, 4)}).filter fun q => ∃ s ∈ q.sides 6, npair 6 s.1 s.2 = (1, 4) ∧ IsPlus 2 s).card = 0 := by
  decide

/-- `card_quads` (Lemma 0.1 counting): faces ↔ bases gives `|Q| = |G| + 1`; double counting (face, side) pairs gives
`4|Q| = N + 2|G|` (each leg on one face, each diagonal on two). -/
lemma p3b_card_quads {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {G : Finset (ℕ × ℕ)} (hQ : IsQuadrangulation N G) :
    (quads N G).card = (N - 2) / 2 := by
  set Q := quads N G with hQdef
  have hnd : ∀ x ∈ G, x ∈ diagonals N := fun x hx => (mem_filter.1 (hQ.1 hx)).1
  -- faces ↔ bases
  have h1 : Q.card = G.card + 1 := by
    have hinj : Set.InjOn (fun q : Quad => (q.u1, q.u4)) Q := by
      intro q hq q' hq' h
      simp only [Prod.mk.injEq] at h
      exact p3b_eq_of_base hQ hq hq' h.1 h.2
    have himg : Q.image (fun q : Quad => (q.u1, q.u4)) = insert (1, N) G := by
      ext x
      rw [mem_image, mem_insert]
      constructor
      · rintro ⟨q, hq, rfl⟩
        obtain ⟨-, -, -, -, hB, -⟩ := p3b_qf hQ.1 hq
        rcases hB with hB | hB
        · exact Or.inr hB
        · left; rw [hB.1, hB.2]
      · rintro (rfl | hx)
        · obtain ⟨q, hq, h1, h4⟩ := p3b_face_quad hN hE hQ (Or.inr ⟨rfl, rfl⟩)
          exact ⟨q, hq, by rw [h1, h4]⟩
        · obtain ⟨c, e⟩ := x
          obtain ⟨q, hq, h1, h4⟩ := p3b_face_quad hN hE hQ (Or.inl hx)
          exact ⟨q, hq, by rw [h1, h4]⟩
    have h1N : (1, N) ∉ G := fun h => by
      have := mem_diagonals.1 (hnd _ h); dsimp only at this; omega
    rw [← card_image_of_injOn hinj, himg, card_insert_of_notMem h1N]
  -- the legs, as chords
  set L := (Icc 1 N).image (fun a => npair N a (a + 1)) with hL
  have hLinj : Set.InjOn (fun a => npair N a (a + 1)) (Icc 1 N) := by
    intro a ha b hb h
    rw [coe_Icc, Set.mem_Icc] at ha hb
    dsimp only at h
    rw [p3b_npair_leg (by omega) ha, p3b_npair_leg (by omega) hb] at h
    split_ifs at h <;> simp only [Prod.mk.injEq] at h <;> omega
  have hLcard : L.card = N := by rw [card_image_of_injOn hLinj, Nat.card_Icc]; omega
  have hLG : Disjoint L G := by
    rw [disjoint_left]
    intro x hx hxG
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hx
    have := mem_diagonals.1 (hnd _ hxG)
    rw [mem_Icc] at ha
    rw [p3b_npair_leg (by omega) ha] at this
    split_ifs at this <;> dsimp only at this <;> omega
  -- every side of every face is a leg or a diagonal of `G`
  have hSU : ∀ q ∈ Q, p3b_S q ⊆ L ∪ G := by
    intro q hq x hx
    obtain ⟨hb, s1, s2, s3, hB, -⟩ := p3b_qf hQ.1 hq
    have leg : ∀ u, 1 ≤ u → u < N → (u, u + 1) ∈ L := fun u h1 h2 =>
      mem_image.2 ⟨u, mem_Icc.2 ⟨h1, by omega⟩, by rw [p3b_npair_leg (by omega) ⟨h1, by omega⟩]; simp [h2]⟩
    have root : (1, N) ∈ L :=
      mem_image.2 ⟨N, mem_Icc.2 ⟨by omega, le_rfl⟩, by rw [p3b_npair_leg (by omega) ⟨by omega, le_rfl⟩]; simp⟩
    rw [mem_union]
    simp only [p3b_S, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · rcases s1 with s | s
      · exact Or.inr s
      · left; rw [s]; exact leg _ hb.1 (by omega)
    · rcases s2 with s | s
      · exact Or.inr s
      · left; rw [s]; exact leg _ (by omega) (by omega)
    · rcases s3 with s | s
      · exact Or.inr s
      · left; rw [s]; exact leg _ (by omega) (by omega)
    · rcases hB with s | s
      · exact Or.inr s
      · left; rw [s.1, s.2]; exact root
  -- double counting
  have hdc : ∑ q ∈ Q, ((L ∪ G).filter fun x => x ∈ p3b_S q).card =
      ∑ x ∈ L ∪ G, (Q.filter fun q => x ∈ p3b_S q).card := by
    simp only [card_filter]
    exact sum_comm
  have hlhs : ∑ q ∈ Q, ((L ∪ G).filter fun x => x ∈ p3b_S q).card = 4 * Q.card := by
    rw [card_eq_sum_ones, mul_sum, mul_one]
    apply sum_congr rfl
    intro q hq
    rw [filter_mem_eq_inter, inter_eq_right.2 (hSU q hq)]
    obtain ⟨hb, -⟩ := p3b_qf hQ.1 hq
    exact p3b_card_S ⟨hb.2.1, hb.2.2.1, hb.2.2.2.1⟩
  have hrhs : ∑ x ∈ L ∪ G, (Q.filter fun q => x ∈ p3b_S q).card = N + 2 * G.card := by
    rw [sum_union hLG]
    congr 1
    · rw [hL, sum_image hLinj, sum_congr rfl (fun a ha => p3b_leg_count hN hE hQ (mem_Icc.1 ha)), sum_const,
        Nat.card_Icc, smul_eq_mul, mul_one]
      omega
    · rw [card_eq_sum_ones, mul_sum, mul_one]
      exact sum_congr rfl fun d hd => p3b_diag_count hN hE hQ hd
  have := hdc
  rw [hlhs, hrhs] at this
  omega

/-- PROVED (3b). Every quadrangulation has `(N − 2)/2` quads. [checked `defs_mirror.py` D2, N ≤ 12] -/
theorem card_quads {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {G : Finset (ℕ × ℕ)}
    (hG : G ∈ quadrangulations N) : (quads N G).card = (N - 2) / 2 := by
  exact p3b_card_quads hN hE (mem_filter.1 hG).2

/-- PROVED (3b). The faces of a quadrangulation alternate in parity. [D2, N ≤ 12] -/
theorem quads_alternating {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {G : Finset (ℕ × ℕ)}
    (hG : G ∈ quadrangulations N) {q : Quad} (hq : q ∈ quads N G) : q.Alternating := by
  clear hN hE
  exact p3b_quads_alternating (mem_filter.1 hG).2.1 hq

/-- PROVED after the integrator's amendment of 2026-09-23 (added `hπ : π < 2`; as originally frozen it was false for
`π ≥ 2`, a 3b finding — see `../base-v2/STATEMENT-CHANGES.diff`). Lemma 0.1(ii): a diagonal of `G` is a side of exactly one quad as a
`+` slot and of exactly one as a `−` slot (for either polarity). [D2, N ≤ 12] The statement quantifies over every
`π : ℕ`; for `π ≥ 2` no slot is `+` and the first count is `0` (`p3b_diag_plus_minus_needs_pi_lt_two`: N = 6,
`G = {(1,4)}`, `π = 2`). With the missing hypothesis `π < 2` it is PROVED as `p3b_diag_plus_minus`. Not used by
Theorem A. -/
theorem diag_plus_minus {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {G : Finset (ℕ × ℕ)}
    (hG : G ∈ quadrangulations N) (π : ℕ) (hπ : π < 2) {d : ℕ × ℕ} (hd : d ∈ G) :
    ((quads N G).filter fun q => ∃ s ∈ q.sides N, npair N s.1 s.2 = d ∧ IsPlus π s).card = 1 ∧
    ((quads N G).filter fun q => ∃ s ∈ q.sides N, npair N s.1 s.2 = d ∧ ¬ IsPlus π s).card = 1 := by
  exact p3b_diag_plus_minus hN hE hG hπ hd

/-- PROVED (3b). Lemma 0.1(i): each leg `a` (the edge `(a, a+1)`) is a side of exactly one quad, and that side is a
`+` slot iff `a` has parity `π` (immediate from `IsPlus`). [D2, N ≤ 12] -/
theorem leg_side_unique {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) {G : Finset (ℕ × ℕ)}
    (hG : G ∈ quadrangulations N) {a : ℕ} (ha : a ∈ Icc 1 N) :
    ((quads N G).filter fun q => ∃ s ∈ q.sides N, npair N s.1 s.2 = npair N a (a + 1)).card = 1 := by
  have hQ : IsQuadrangulation N G := (mem_filter.1 hG).2
  rw [filter_congr (fun q hq => p3b_side_iff_S (N := N) (p3b_qf hQ.1 hq).1 _)]
  exact p3b_leg_count hN hE hQ (mem_Icc.1 ha)

/-! ### Package F: counting quadrangulations (Fuss–Catalan) -/

/-- Odd diagonals of the sub-polygon `a..b`. -/
def p3bF_od (a b : ℕ) : Finset (ℕ × ℕ) := (sdiag a b).filter (fun d => (d.2 - d.1) % 2 = 1)

/-- Quadrangulations of the sub-polygon `a..b`. -/
def p3bF_IsQ (a b : ℕ) (G : Finset (ℕ × ℕ)) : Prop :=
  G ⊆ p3bF_od a b ∧ (∀ p ∈ G, ∀ q ∈ G, ¬ Crosses p q) ∧
    (∀ d ∈ p3bF_od a b, d ∉ G → ∃ p ∈ G, Crosses p d)

instance p3bF_IsQ_dec (a b : ℕ) : DecidablePred (p3bF_IsQ a b) := fun _ => by
  unfold p3bF_IsQ; infer_instance

def p3bF_qs (a b : ℕ) : Finset (Finset (ℕ × ℕ)) := (p3bF_od a b).powerset.filter (p3bF_IsQ a b)

lemma p3bF_mem_od {a b : ℕ} {d : ℕ × ℕ} :
    d ∈ p3bF_od a b ↔ a ≤ d.1 ∧ d.2 ≤ b ∧ d.1 + 2 ≤ d.2 ∧ ¬ (d.1 = a ∧ d.2 = b) ∧ (d.2 - d.1) % 2 = 1 := by
  unfold p3bF_od
  rw [mem_filter, mem_sdiag]
  tauto

lemma p3bF_mem_qs {a b : ℕ} {G : Finset (ℕ × ℕ)} : G ∈ p3bF_qs a b ↔ p3bF_IsQ a b G := by
  unfold p3bF_qs
  simp only [mem_filter, mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

lemma p3bF_quadrangulations_eq (N : ℕ) : quadrangulations N = p3bF_qs 1 N := rfl

lemma p3bF_qs_one (a : ℕ) : p3bF_qs a (a + 1) = {∅} := by
  have hs : p3bF_od a (a + 1) = ∅ := by
    ext d; simp only [p3bF_mem_od, Finset.notMem_empty, iff_false]; omega
  unfold p3bF_qs
  rw [hs, powerset_empty]
  ext G
  simp only [mem_filter, mem_singleton]
  constructor
  · exact fun h => h.1
  · rintro rfl
    refine ⟨rfl, ⟨by simp, by simp, ?_⟩⟩
    rw [hs]; simp

/-- The optional side `(x, y)` of a face: present iff it is a diagonal (`x + 1 < y`). -/
def p3bF_side (x y : ℕ) : Finset (ℕ × ℕ) := if x + 1 < y then {(x, y)} else ∅

/-- Gluing three sub-quadrangulations along the face `(a, u, v, b)`. -/
def p3bF_glue (a b u v : ℕ) (G1 G2 G3 : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  G1 ∪ G2 ∪ G3 ∪ (p3bF_side a u ∪ p3bF_side u v ∪ p3bF_side v b)

lemma p3bF_mem_side {x y : ℕ} {d : ℕ × ℕ} : d ∈ p3bF_side x y ↔ x + 1 < y ∧ d = (x, y) := by
  unfold p3bF_side
  split_ifs with h <;> simp [h]

lemma p3bF_mem_glue {a b u v : ℕ} {G1 G2 G3 : Finset (ℕ × ℕ)} {d : ℕ × ℕ} :
    d ∈ p3bF_glue a b u v G1 G2 G3 ↔ d ∈ G1 ∨ d ∈ G2 ∨ d ∈ G3 ∨ (a + 1 < u ∧ d = (a, u)) ∨
      (u + 1 < v ∧ d = (u, v)) ∨ (v + 1 < b ∧ d = (v, b)) := by
  simp only [p3bF_glue, mem_union, p3bF_mem_side]
  tauto

/-- Where an odd chord of `a..b` sits relative to a face `(a, u, v, b)` with odd sides. -/
lemma p3bF_locate {a b u v c e : ℕ} (hau : a < u) (huv : u < v) (hvb : v < b) (p1 : (u - a) % 2 = 1)
    (p2 : (v - u) % 2 = 1) (p3 : (b - v) % 2 = 1) (hc : a ≤ c) (he : e ≤ b) (hce : c + 2 ≤ e)
    (hne : ¬ (c = a ∧ e = b)) (hp : (e - c) % 2 = 1) :
    (e ≤ u ∧ ¬ (c = a ∧ e = u)) ∨ (c = a ∧ e = u) ∨ (u ≤ c ∧ e ≤ v ∧ ¬ (c = u ∧ e = v)) ∨
      (c = u ∧ e = v) ∨ (v ≤ c ∧ ¬ (c = v ∧ e = b)) ∨ (c = v ∧ e = b) ∨
      (a + 1 < u ∧ Crosses (a, u) (c, e)) ∨ (u + 1 < v ∧ Crosses (u, v) (c, e)) ∨
      (v + 1 < b ∧ Crosses (v, b) (c, e)) := by
  simp only [Crosses]
  by_cases h1 : e ≤ u
  · by_cases h : c = a ∧ e = u
    · exact Or.inr (Or.inl h)
    · exact Or.inl ⟨h1, h⟩
  by_cases h2 : u ≤ c ∧ e ≤ v
  · by_cases h : c = u ∧ e = v
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inl ⟨h2.1, h2.2, h⟩))
  by_cases h3 : v ≤ c
  · by_cases h : c = v ∧ e = b
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h3, h⟩))))
  right; right; right; right; right; right
  by_cases hcu : c < u
  · by_cases hac : a < c
    · left; omega
    have hca : c = a := by omega
    subst hca
    rcases lt_trichotomy e v with hev | rfl | hev
    · right; left; omega
    · exfalso; omega
    · right; right; omega
  · by_cases huc : u < c
    · right; left; omega
    have hcu' : c = u := by omega
    subst hcu'
    right; right; omega

lemma p3bF_glue_isQ {a b u v : ℕ} {G1 G2 G3 : Finset (ℕ × ℕ)} (hau : a < u) (huv : u < v) (hvb : v < b)
    (p1 : (u - a) % 2 = 1) (p2 : (v - u) % 2 = 1) (p3 : (b - v) % 2 = 1)
    (h1 : p3bF_IsQ a u G1) (h2 : p3bF_IsQ u v G2) (h3 : p3bF_IsQ v b G3) :
    p3bF_IsQ a b (p3bF_glue a b u v G1 G2 G3) := by
  obtain ⟨s1, n1, m1⟩ := h1
  obtain ⟨s2, n2, m2⟩ := h2
  obtain ⟨s3, n3, m3⟩ := h3
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    rw [p3bF_mem_glue] at hd
    rw [p3bF_mem_od]
    rcases hd with hd | hd | hd | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩
    · have := p3bF_mem_od.1 (s1 hd); omega
    · have := p3bF_mem_od.1 (s2 hd); omega
    · have := p3bF_mem_od.1 (s3 hd); omega
    · dsimp only; omega
    · dsimp only; omega
    · dsimp only; omega
  · intro p hp q hq
    rw [p3bF_mem_glue] at hp hq
    rcases hp with hp | hp | hp | ⟨hp', rfl⟩ | ⟨hp', rfl⟩ | ⟨hp', rfl⟩ <;>
      rcases hq with hq | hq | hq | ⟨hq', rfl⟩ | ⟨hq', rfl⟩ | ⟨hq', rfl⟩
    all_goals try exact n1 _ hp _ hq
    all_goals try exact n2 _ hp _ hq
    all_goals try exact n3 _ hp _ hq
    all_goals
      try have := p3bF_mem_od.1 (s1 hp)
      try have := p3bF_mem_od.1 (s2 hp)
      try have := p3bF_mem_od.1 (s3 hp)
      try have := p3bF_mem_od.1 (s1 hq)
      try have := p3bF_mem_od.1 (s2 hq)
      try have := p3bF_mem_od.1 (s3 hq)
      simp only [Crosses]
      omega
  · rintro ⟨c, e⟩ hd hnot
    rw [p3bF_mem_glue] at hnot
    have hb := p3bF_mem_od.1 hd
    dsimp only at hb
    rcases p3bF_locate hau huv hvb p1 p2 p3 hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2 with
      h | h | h | h | h | h | h | h | h
    · have hd1 : (c, e) ∈ p3bF_od a u := p3bF_mem_od.2 (by dsimp only; omega)
      obtain ⟨p, hp, hc⟩ := m1 _ hd1 (fun h' => hnot (Or.inl h'))
      exact ⟨p, p3bF_mem_glue.2 (Or.inl hp), hc⟩
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by rw [h.1, h.2]⟩)))) hnot
    · have hd1 : (c, e) ∈ p3bF_od u v := p3bF_mem_od.2 (by dsimp only; omega)
      obtain ⟨p, hp, hc⟩ := m2 _ hd1 (fun h' => hnot (Or.inr (Or.inl h')))
      exact ⟨p, p3bF_mem_glue.2 (Or.inr (Or.inl hp)), hc⟩
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by rw [h.1, h.2]⟩))))) hnot
    · have hd1 : (c, e) ∈ p3bF_od v b := p3bF_mem_od.2 (by dsimp only; omega)
      obtain ⟨p, hp, hc⟩ := m3 _ hd1 (fun h' => hnot (Or.inr (Or.inr (Or.inl h'))))
      exact ⟨p, p3bF_mem_glue.2 (Or.inr (Or.inr (Or.inl hp))), hc⟩
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by rw [h.1, h.2]⟩))))) hnot
    · exact ⟨_, p3bF_mem_glue.2 (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1, rfl⟩)))), h.2⟩
    · exact ⟨_, p3bF_mem_glue.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1, rfl⟩))))), h.2⟩
    · exact ⟨_, p3bF_mem_glue.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h.1, rfl⟩))))), h.2⟩

/-- Face existence in a sub-polygon (as `p3b_face`, for the root `(a, b)` of `a..b`). -/
lemma p3bF_face {a b : ℕ} {G : Finset (ℕ × ℕ)} (hQ : p3bF_IsQ a b G) (hab : a + 3 ≤ b)
    (hpar : (b - a) % 2 = 1) :
    ∃ u v, a < u ∧ u < v ∧ v < b ∧ (u - a) % 2 = 1 ∧ (v - u) % 2 = 1 ∧ (b - v) % 2 = 1 ∧
      ((a, u) ∈ G ∨ u = a + 1) ∧ ((u, v) ∈ G ∨ v = u + 1) ∧ ((v, b) ∈ G ∨ b = v + 1) := by
  obtain ⟨hGs, hnc, hmax⟩ := hQ
  have odd := fun {d : ℕ × ℕ} (hd : d ∈ G) => p3bF_mem_od.1 (hGs hd)
  set SL := (Ioo a b).filter (fun j => j = a + 1 ∨ (a, j) ∈ G) with hSL
  have hSLne : SL.Nonempty := ⟨a + 1, mem_filter.2 ⟨mem_Ioo.2 ⟨by omega, by omega⟩, Or.inl rfl⟩⟩
  set u2 := SL.max' hSLne with hu2
  have hu2m := mem_filter.1 (SL.max'_mem hSLne)
  rw [← hu2, mem_Ioo] at hu2m
  have hu2max : ∀ j, a < j → j < b → (a, j) ∈ G → j ≤ u2 := fun j h1 h2 h3 =>
    SL.le_max' j (mem_filter.2 ⟨mem_Ioo.2 ⟨h1, h2⟩, Or.inr h3⟩)
  set SR := (Ioo a b).filter (fun j => j = b - 1 ∨ (j, b) ∈ G) with hSR
  have hSRne : SR.Nonempty := ⟨b - 1, mem_filter.2 ⟨mem_Ioo.2 ⟨by omega, by omega⟩, Or.inl rfl⟩⟩
  set u3 := SR.min' hSRne with hu3
  have hu3m := mem_filter.1 (SR.min'_mem hSRne)
  rw [← hu3, mem_Ioo] at hu3m
  have hu3min : ∀ j, a < j → j < b → (j, b) ∈ G → u3 ≤ j := fun j h1 h2 h3 =>
    SR.min'_le j (mem_filter.2 ⟨mem_Ioo.2 ⟨h1, h2⟩, Or.inr h3⟩)
  have p2 : (u2 - a) % 2 = 1 := by
    rcases hu2m.2 with h | h
    · omega
    · have := odd h; dsimp only at this; omega
  have p3 : (b - u3) % 2 = 1 := by
    rcases hu3m.2 with h | h
    · omega
    · have := odd h; dsimp only at this; omega
  have h23 : u2 < u3 := by
    by_contra hc
    have hne : u2 ≠ u3 := by intro h; rw [h] at p2; omega
    rcases hu2m.2 with h2 | h2
    · omega
    rcases hu3m.2 with h3 | h3
    · omega
    exact hnc _ h2 _ h3 (by simp only [Crosses]; omega)
  have hmid : (u2, u3) ∈ G ∨ u3 = u2 + 1 := by
    by_cases hadj : u3 = u2 + 1
    · exact Or.inr hadj
    left
    by_contra hnot
    have hdo : (u2, u3) ∈ p3bF_od a b := p3bF_mem_od.2 (by dsimp only; omega)
    obtain ⟨⟨c, e⟩, hp, hcr⟩ := hmax _ hdo hnot
    have hpo := odd hp
    dsimp only at hpo
    simp only [Crosses] at hcr
    rcases hcr with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · rcases lt_or_eq_of_le hpo.1 with hca | rfl
      · rcases hu2m.2 with h | h
        · omega
        · exact hnc _ h _ hp (by simp only [Crosses]; omega)
      · have := hu2max e (by omega) (by omega) hp; omega
    · rcases lt_or_eq_of_le hpo.2.1 with heb | rfl
      · rcases hu3m.2 with h | h
        · omega
        · exact hnc _ hp _ h (by simp only [Crosses]; omega)
      · have := hu3min c (by omega) (by omega) hp; omega
  have p23 : (u3 - u2) % 2 = 1 := by
    rcases hmid with h | h
    · have := odd h; dsimp only at this; omega
    · omega
  exact ⟨u2, u3, hu2m.1.1, h23, hu3m.1.2, p2, p23, p3, hu2m.2.symm, hmid,
    hu3m.2.symm.imp_right fun h => by omega⟩

/-- Restriction of a quadrangulation to a sub-polygon cut off by a wall `(x, y)`. -/
lemma p3bF_restrict {a b x y : ℕ} {G : Finset (ℕ × ℕ)} (hQ : p3bF_IsQ a b G) (hax : a ≤ x) (hyb : y ≤ b)
    (hxy : x < y) (hw : (x, y) ∈ G ∨ y = x + 1) :
    p3bF_IsQ x y (G.filter (· ∈ sdiag x y)) := by
  obtain ⟨hs, hn, hm⟩ := hQ
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    rw [mem_filter] at hd
    have h1 := p3bF_mem_od.1 (hs hd.1)
    have h2 := mem_sdiag.1 hd.2
    exact p3bF_mem_od.2 ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2, h1.2.2.2.2⟩
  · intro p hp q hq
    exact hn p (mem_filter.1 hp).1 q (mem_filter.1 hq).1
  · rintro ⟨c, e⟩ hd hnot
    have hdb := p3bF_mem_od.1 hd
    dsimp only at hdb
    have hnotG : (c, e) ∉ G := fun h => hnot (mem_filter.2 ⟨h, mem_sdiag.2 (by dsimp only; omega)⟩)
    obtain ⟨⟨c', e'⟩, hp, hc⟩ := hm _ (p3bF_mem_od.2 (by dsimp only; omega)) hnotG
    have hpb := p3bF_mem_od.1 (hs hp)
    dsimp only at hpb
    refine ⟨(c', e'), mem_filter.2 ⟨hp, mem_sdiag.2 ?_⟩, hc⟩
    dsimp only
    simp only [Crosses] at hc
    rcases hw with hw | hw
    · have hnc := hn _ hp _ hw
      simp only [Crosses] at hnc
      omega
    · omega

lemma p3bF_split {a b u v : ℕ} {G : Finset (ℕ × ℕ)} (hQ : p3bF_IsQ a b G) (hau : a < u) (huv : u < v)
    (hvb : v < b) (p1 : (u - a) % 2 = 1) (p2 : (v - u) % 2 = 1) (p3 : (b - v) % 2 = 1)
    (w1 : (a, u) ∈ G ∨ u = a + 1) (w2 : (u, v) ∈ G ∨ v = u + 1) (w3 : (v, b) ∈ G ∨ b = v + 1) :
    p3bF_glue a b u v (G.filter (· ∈ sdiag a u)) (G.filter (· ∈ sdiag u v)) (G.filter (· ∈ sdiag v b)) = G := by
  ext ⟨c, e⟩
  rw [p3bF_mem_glue, mem_filter, mem_filter, mem_filter]
  constructor
  · rintro (h | h | h | ⟨h, heq⟩ | ⟨h, heq⟩ | ⟨h, heq⟩)
    · exact h.1
    · exact h.1
    · exact h.1
    · rw [heq]; exact w1.resolve_right (by omega)
    · rw [heq]; exact w2.resolve_right (by omega)
    · rw [heq]; exact w3.resolve_right (by omega)
  · intro h
    have hb := p3bF_mem_od.1 (hQ.1 h)
    dsimp only at hb
    have ncr : ∀ q ∈ G, ¬ Crosses q (c, e) := fun q hq => hQ.2.1 q hq _ h
    simp only [mem_sdiag, Prod.mk.injEq]
    rcases p3bF_locate hau huv hvb p1 p2 p3 hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2 with
      h' | h' | h' | h' | h' | h' | h' | h' | h'
    · left; exact ⟨h, by omega⟩
    · right; right; right; left; omega
    · right; left; exact ⟨h, by omega⟩
    · right; right; right; right; left; omega
    · right; right; left; exact ⟨h, by omega⟩
    · right; right; right; right; right; omega
    · exact absurd h'.2 (ncr _ (w1.resolve_right (by omega)))
    · exact absurd h'.2 (ncr _ (w2.resolve_right (by omega)))
    · exact absurd h'.2 (ncr _ (w3.resolve_right (by omega)))

lemma p3bF_filter_glue {a b u v x y : ℕ} {G1 G2 G3 H : Finset (ℕ × ℕ)} (hau : a < u) (huv : u < v)
    (hvb : v < b) (h1 : G1 ⊆ sdiag a u) (h2 : G2 ⊆ sdiag u v) (h3 : G3 ⊆ sdiag v b)
    (hH : H ⊆ sdiag x y)
    (hsel : (x = a ∧ y = u ∧ H = G1) ∨ (x = u ∧ y = v ∧ H = G2) ∨ (x = v ∧ y = b ∧ H = G3)) :
    (p3bF_glue a b u v G1 G2 G3).filter (· ∈ sdiag x y) = H := by
  ext ⟨c, e⟩
  rw [mem_filter, p3bF_mem_glue]
  constructor
  · rintro ⟨h, hxy⟩
    have hs := mem_sdiag.1 hxy
    dsimp only at hs
    rcases hsel with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    rcases h with h | h | h | ⟨h, heq⟩ | ⟨h, heq⟩ | ⟨h, heq⟩ <;>
    first
      | assumption
      | (simp only [Prod.mk.injEq] at heq; omega)
      | (have := mem_sdiag.1 (h1 h); dsimp only at this; omega)
      | (have := mem_sdiag.1 (h2 h); dsimp only at this; omega)
      | (have := mem_sdiag.1 (h3 h); dsimp only at this; omega)
  · intro h
    refine ⟨?_, hH h⟩
    rcases hsel with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))

lemma p3bF_sub {x y : ℕ} {G : Finset (ℕ × ℕ)} (h : p3bF_IsQ x y G) : G ⊆ sdiag x y :=
  fun _ hd => (mem_filter.1 (h.1 hd)).1

lemma p3bF_glue_inj {a b u v u' v' : ℕ} {G1 G2 G3 G1' G2' G3' : Finset (ℕ × ℕ)}
    (hau : a < u) (huv : u < v) (hvb : v < b) (hau' : a < u') (huv' : u' < v') (hvb' : v' < b)
    (h1 : p3bF_IsQ a u G1) (h2 : p3bF_IsQ u v G2) (h3 : p3bF_IsQ v b G3)
    (h1' : p3bF_IsQ a u' G1') (h2' : p3bF_IsQ u' v' G2') (h3' : p3bF_IsQ v' b G3')
    (heq : p3bF_glue a b u v G1 G2 G3 = p3bF_glue a b u' v' G1' G2' G3') :
    u = u' ∧ v = v' ∧ G1 = G1' ∧ G2 = G2' ∧ G3 = G3' := by
  -- every `(a, j)` in a glue has `j ≤ u`; every `(j, b)` has `v ≤ j`
  have left : ∀ {u v : ℕ} {G1 G2 G3 : Finset (ℕ × ℕ)}, a < u → u < v → v < b → G1 ⊆ sdiag a u →
      G2 ⊆ sdiag u v → G3 ⊆ sdiag v b → ∀ j, (a, j) ∈ p3bF_glue a b u v G1 G2 G3 → j ≤ u := by
    intro u v G1 G2 G3 hau huv hvb s1 s2 s3 j hj
    rw [p3bF_mem_glue] at hj
    rcases hj with h | h | h | ⟨h, heq⟩ | ⟨h, heq⟩ | ⟨h, heq⟩
    · have := mem_sdiag.1 (s1 h); dsimp only at this; omega
    · have := mem_sdiag.1 (s2 h); dsimp only at this; omega
    · have := mem_sdiag.1 (s3 h); dsimp only at this; omega
    all_goals simp only [Prod.mk.injEq] at heq; omega
  have right : ∀ {u v : ℕ} {G1 G2 G3 : Finset (ℕ × ℕ)}, a < u → u < v → v < b → G1 ⊆ sdiag a u →
      G2 ⊆ sdiag u v → G3 ⊆ sdiag v b → ∀ j, (j, b) ∈ p3bF_glue a b u v G1 G2 G3 → v ≤ j := by
    intro u v G1 G2 G3 hau huv hvb s1 s2 s3 j hj
    rw [p3bF_mem_glue] at hj
    rcases hj with h | h | h | ⟨h, heq⟩ | ⟨h, heq⟩ | ⟨h, heq⟩
    · have := mem_sdiag.1 (s1 h); dsimp only at this; omega
    · have := mem_sdiag.1 (s2 h); dsimp only at this; omega
    · have := mem_sdiag.1 (s3 h); dsimp only at this; omega
    all_goals simp only [Prod.mk.injEq] at heq; omega
  have S := fun {x y} {G : Finset (ℕ × ℕ)} (h : p3bF_IsQ x y G) => p3bF_sub h
  have side1 : ∀ {u v : ℕ} {G1 G2 G3 : Finset (ℕ × ℕ)}, a + 1 < u →
      (a, u) ∈ p3bF_glue a b u v G1 G2 G3 := fun h => p3bF_mem_glue.2 (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, rfl⟩))))
  have side3 : ∀ {u v : ℕ} {G1 G2 G3 : Finset (ℕ × ℕ)}, v + 1 < b →
      (v, b) ∈ p3bF_glue a b u v G1 G2 G3 := fun h =>
        p3bF_mem_glue.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h, rfl⟩)))))
  have hu : u = u' := by
    have e1 : u' ≤ u := by
      by_cases h : a + 1 < u'
      · exact left hau huv hvb (S h1) (S h2) (S h3) _ (heq ▸ side1 h)
      · omega
    have e2 : u ≤ u' := by
      by_cases h : a + 1 < u
      · exact left hau' huv' hvb' (S h1') (S h2') (S h3') _ (heq ▸ side1 h)
      · omega
    omega
  have hv : v = v' := by
    have e1 : v ≤ v' := by
      by_cases h : v' + 1 < b
      · exact right hau huv hvb (S h1) (S h2) (S h3) _ (heq ▸ side3 h)
      · omega
    have e2 : v' ≤ v := by
      by_cases h : v + 1 < b
      · exact right hau' huv' hvb' (S h1') (S h2') (S h3') _ (heq ▸ side3 h)
      · omega
    omega
  subst hu hv
  have F := fun {x y} {H H' : Finset (ℕ × ℕ)} (hH : H ⊆ sdiag x y) (hH' : H' ⊆ sdiag x y)
      (hs : (x = a ∧ y = u ∧ H = G1) ∨ (x = u ∧ y = v ∧ H = G2) ∨ (x = v ∧ y = b ∧ H = G3))
      (hs' : (x = a ∧ y = u ∧ H' = G1') ∨ (x = u ∧ y = v ∧ H' = G2') ∨ (x = v ∧ y = b ∧ H' = G3')) =>
    (p3bF_filter_glue hau huv hvb (S h1) (S h2) (S h3) hH hs).symm.trans
      (heq ▸ p3bF_filter_glue hau huv hvb (S h1') (S h2') (S h3') hH' hs')
  refine ⟨rfl, rfl, F (S h1) (S h1') (Or.inl ⟨rfl, rfl, rfl⟩) (Or.inl ⟨rfl, rfl, rfl⟩),
    F (S h2) (S h2') (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)),
    F (S h3) (S h3') (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)) (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))⟩

lemma p3bF_card_rec (a m : ℕ) :
    (p3bF_qs a (a + 2 * m + 3)).card = ∑ x ∈ antidiagonal m, ∑ y ∈ antidiagonal x.2,
      (p3bF_qs a (a + 2 * x.1 + 1)).card * (p3bF_qs (a + 2 * x.1 + 1) (a + 2 * x.1 + 1 + 2 * y.1 + 1)).card *
        (p3bF_qs (a + 2 * x.1 + 1 + 2 * y.1 + 1) (a + 2 * m + 3)).card := by
  obtain ⟨b, hb⟩ : ∃ b, b = a + 2 * m + 3 := ⟨_, rfl⟩
  rw [← hb]
  let S := (antidiagonal m).sigma (fun x : ℕ × ℕ => antidiagonal x.2)
  let F := fun z : (Σ _ : ℕ × ℕ, ℕ × ℕ) => p3bF_qs a (a + 2 * z.1.1 + 1) ×ˢ
    p3bF_qs (a + 2 * z.1.1 + 1) (a + 2 * z.1.1 + 1 + 2 * z.2.1 + 1) ×ˢ
      p3bF_qs (a + 2 * z.1.1 + 1 + 2 * z.2.1 + 1) b
  calc (p3bF_qs a b).card = (S.sigma F).card := by
        symm
        refine card_bij (fun z _ => p3bF_glue a b (a + 2 * z.1.1.1 + 1) (a + 2 * z.1.1.1 + 1 + 2 * z.1.2.1 + 1)
          z.2.1 z.2.2.1 z.2.2.2) ?_ ?_ ?_
        · rintro ⟨⟨⟨i, r⟩, ⟨j, k⟩⟩, ⟨G1, G2, G3⟩⟩ hz
          simp only [S, F, mem_sigma, mem_product, Finset.HasAntidiagonal.mem_antidiagonal, p3bF_mem_qs] at hz
          dsimp only
          exact p3bF_mem_qs.2 (p3bF_glue_isQ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            hz.2.1 hz.2.2.1 hz.2.2.2)
        · rintro ⟨⟨⟨i, r⟩, ⟨j, k⟩⟩, ⟨G1, G2, G3⟩⟩ hz ⟨⟨⟨i', r'⟩, ⟨j', k'⟩⟩, ⟨G1', G2', G3'⟩⟩ hz' he
          simp only [S, F, mem_sigma, mem_product, Finset.HasAntidiagonal.mem_antidiagonal, p3bF_mem_qs] at hz hz'
          dsimp only at he
          obtain ⟨hu, hv, rfl, rfl, rfl⟩ := p3bF_glue_inj (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) hz.2.1 hz.2.2.1 hz.2.2.2 hz'.2.1 hz'.2.2.1 hz'.2.2.2 he
          have e1 : i = i' := by omega
          have e2 : j = j' := by omega
          have e3 : r = r' := by omega
          have e4 : k = k' := by omega
          subst e1 e2 e3 e4
          rfl
        · intro G hG
          have hQ := p3bF_mem_qs.1 hG
          obtain ⟨u, v, hau, huv, hvb, p1, p2, p3, w1, w2, w3⟩ := p3bF_face hQ (by omega) (by omega)
          obtain ⟨i, rfl⟩ : ∃ i, u = a + 2 * i + 1 := ⟨(u - a - 1) / 2, by omega⟩
          obtain ⟨j, rfl⟩ : ∃ j, v = a + 2 * i + 1 + 2 * j + 1 := ⟨(v - (a + 2 * i + 1) - 1) / 2, by omega⟩
          have hjm : i + j ≤ m := by omega
          refine ⟨⟨⟨(i, m - i), (j, m - i - j)⟩, (G.filter (· ∈ sdiag a (a + 2 * i + 1)),
            G.filter (· ∈ sdiag (a + 2 * i + 1) (a + 2 * i + 1 + 2 * j + 1)),
            G.filter (· ∈ sdiag (a + 2 * i + 1 + 2 * j + 1) b))⟩, ?_, ?_⟩
          · simp only [S, F, mem_sigma, mem_product, Finset.HasAntidiagonal.mem_antidiagonal, p3bF_mem_qs]
            refine ⟨⟨by omega, by omega⟩, p3bF_restrict hQ le_rfl (by omega) hau w1,
              p3bF_restrict hQ (by omega) (by omega) huv w2, p3bF_restrict hQ (by omega) le_rfl hvb w3⟩
          · exact p3bF_split hQ hau huv hvb p1 p2 p3 w1 w2 w3
    _ = _ := by
        rw [card_sigma, sum_sigma]
        refine sum_congr rfl (fun x _ => sum_congr rfl (fun y _ => ?_))
        simp only [F, card_product, mul_assoc]

/-- The count depends only on the size of the sub-polygon. -/
lemma p3bF_card_inv (m : ℕ) : ∀ a, (p3bF_qs a (a + 2 * m + 1)).card = (p3bF_qs 0 (2 * m + 1)).card := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro a
  rcases m with _ | m
  · show (p3bF_qs a (a + 1)).card = (p3bF_qs 0 (0 + 1)).card
    rw [p3bF_qs_one, p3bF_qs_one]
  · rw [show a + 2 * (m + 1) + 1 = a + 2 * m + 3 by ring, show 2 * (m + 1) + 1 = 0 + 2 * m + 3 by ring,
      p3bF_card_rec, p3bF_card_rec]
    refine sum_congr rfl (fun x hx => sum_congr rfl (fun y hy => ?_))
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx hy
    rw [show a + 2 * m + 3 = a + 2 * x.1 + 1 + 2 * y.1 + 1 + 2 * y.2 + 1 by omega,
      show 0 + 2 * m + 3 = 0 + 2 * x.1 + 1 + 2 * y.1 + 1 + 2 * y.2 + 1 by omega,
      ih x.1 (by omega) a, ih x.1 (by omega) 0, ih y.1 (by omega), ih y.1 (by omega), ih y.2 (by omega),
      ih y.2 (by omega)]

/-- `c m`: the number of quadrangulations of a `(2m+2)`-gon. -/
def p3bF_c (m : ℕ) : ℕ := (p3bF_qs 0 (2 * m + 1)).card

lemma p3bF_c_zero : p3bF_c 0 = 1 := by
  show (p3bF_qs 0 (0 + 1)).card = 1
  rw [p3bF_qs_one]; rfl

/-- The ternary recurrence `c (m+1) = Σ_{i+j+k=m} c i · c j · c k`. -/
lemma p3bF_c_succ (m : ℕ) :
    p3bF_c (m + 1) = ∑ x ∈ antidiagonal m, p3bF_c x.1 * ∑ y ∈ antidiagonal x.2, p3bF_c y.1 * p3bF_c y.2 := by
  rw [p3bF_c, show 2 * (m + 1) + 1 = 0 + 2 * m + 3 by ring, p3bF_card_rec]
  refine sum_congr rfl (fun x hx => ?_)
  rw [mul_sum]
  refine sum_congr rfl (fun y hy => ?_)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx hy
  rw [show 0 + 2 * m + 3 = 0 + 2 * x.1 + 1 + 2 * y.1 + 1 + 2 * y.2 + 1 by omega, p3bF_card_inv x.1 0,
    p3bF_card_inv y.1, p3bF_card_inv y.2, mul_assoc]
  rfl

/-- The generating function `P = Σ c m X^m`. -/
noncomputable def p3bF_P : PowerSeries ℚ := PowerSeries.mk fun m => (p3bF_c m : ℚ)

lemma p3bF_P_eq : p3bF_P = 1 + PowerSeries.X * p3bF_P ^ 3 := by
  ext n
  rcases n with _ | m
  · simp [p3bF_P, p3bF_c_zero]
  · rw [map_add, PowerSeries.coeff_one, PowerSeries.coeff_succ_X_mul, ite_eq_right (by omega), zero_add, pow_three]
    simp only [p3bF_P, PowerSeries.coeff_mul, PowerSeries.coeff_mk]
    rw [p3bF_c_succ]
    push_cast
    rfl

lemma p3bF_P_pow_succ (p : ℕ) : p3bF_P ^ (p + 1) = p3bF_P ^ p + PowerSeries.X * p3bF_P ^ (p + 3) := by
  linear_combination p3bF_P ^ p * p3bF_P_eq

lemma p3bF_coeff_zero (p : ℕ) : PowerSeries.coeff 0 (p3bF_P ^ p) = 1 := by
  induction p with
  | zero => simp
  | succ p ih => rw [p3bF_P_pow_succ, map_add, PowerSeries.coeff_zero_X_mul, add_zero, ih]

lemma p3bF_alg (p n A B : ℚ) (hp : 0 ≤ p) (hn : 0 ≤ n) (h : B * (n + 1) = A * (p + 2 * n + 3)) :
    p * B / (p + 3 * n + 3) + (p + 3) * A / (p + 3 * n + 3) = (p + 1) * (A + B) / (p + 3 * n + 3 + 1) := by
  have h1 : (p + 3 * n + 3 + 1) ≠ 0 := by positivity
  have h2 : (p + 3 * n + 3) ≠ 0 := by positivity
  rw [← add_div, div_eq_div_iff h2 h1]
  linear_combination (-3) * h

/-- Raney numbers: `[X^n] P^p = p/(p+3n) · C(p+3n, n)` for `p ≥ 1`. -/
lemma p3bF_closed (s : ℕ) : ∀ p n, p + 3 * n = s → 1 ≤ p →
    PowerSeries.coeff n (p3bF_P ^ p) = (p : ℚ) * ((p + 3 * n).choose n : ℚ) / ((p : ℚ) + 3 * n) := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro p n hs hp
  rcases n with _ | n
  · rw [p3bF_coeff_zero]
    have : (p : ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
    simp only [Nat.cast_zero, mul_zero, add_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
    exact (div_self this).symm
  obtain ⟨p, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [p3bF_P_pow_succ, map_add, PowerSeries.coeff_succ_X_mul]
  have hA := ih (p + 3 + 3 * n) (by omega) (p + 3) n rfl (by omega)
  have hB : PowerSeries.coeff (n + 1) (p3bF_P ^ p) =
      (p : ℚ) * ((p + 3 * (n + 1)).choose (n + 1) : ℚ) / ((p : ℚ) + 3 * ((n + 1 : ℕ) : ℚ)) := by
    rcases p with _ | p
    · simp [PowerSeries.coeff_one]
    · exact ih _ (by omega) _ _ rfl (by omega)
  rw [hA, hB, show p + 3 + 3 * n = p + 3 * n + 3 by ring, show p + 3 * (n + 1) = p + 3 * n + 3 by ring,
    show p + 1 + 3 * (n + 1) = p + 3 * n + 3 + 1 by ring, Nat.choose_succ_succ' (p + 3 * n + 3) n]
  have h := Nat.choose_succ_right_eq (p + 3 * n + 3) n
  rw [show p + 3 * n + 3 - n = p + 2 * n + 3 by omega] at h
  have hq : ((p + 3 * n + 3).choose (n + 1) : ℚ) * ((n : ℚ) + 1) =
      ((p + 3 * n + 3).choose n : ℚ) * ((p : ℚ) + 2 * n + 3) := by exact_mod_cast h
  push_cast
  have := p3bF_alg p n _ _ (by positivity) (by positivity) hq
  convert this using 2 <;> ring

/-- PROVED (package F, 2026-09-23): root-face decomposition gives the ternary recurrence; P = 1 + X·P³ and Raney numbers give
the closed form (not needed for Theorem A). The number of quadrangulations is the Fuss–Catalan number
`(3k choose k)/(2k+1)`, `k = (N−2)/2` (arXiv:2607.27345 Table 2; OEIS A001764). [D1, N ≤ 12] -/
theorem card_quadrangulations {N : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) :
    (quadrangulations N).card = (3 * ((N - 2) / 2)).choose ((N - 2) / 2) / (2 * ((N - 2) / 2) + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, N = 2 * k + 2 := ⟨(N - 2) / 2, by omega⟩
  rw [show (2 * k + 2 - 2) / 2 = k by omega, p3bF_quadrangulations_eq, show 2 * k + 2 = 1 + 2 * k + 1 by ring,
    p3bF_card_inv]
  have hc : (p3bF_c k : ℚ) * (3 * k + 1) = ((3 * k + 1).choose k : ℚ) := by
    have h := p3bF_closed _ 1 k rfl le_rfl
    rw [pow_one, p3bF_P, PowerSeries.coeff_mk, add_comm 1 (3 * k)] at h
    rw [h]
    have : (3 * (k : ℚ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  have h1 := Nat.choose_mul_succ_eq (3 * k) k
  rw [show 3 * k + 1 - k = 2 * k + 1 by omega] at h1
  have h1q : ((3 * k).choose k : ℚ) * (3 * k + 1) = ((3 * k + 1).choose k : ℚ) * (2 * k + 1) := by
    exact_mod_cast h1
  have h3 : ((p3bF_c k : ℚ) * (2 * k + 1)) * (3 * k + 1) = ((3 * k).choose k : ℚ) * (3 * k + 1) := by
    linear_combination (2 * (k : ℚ) + 1) * hc - h1q
  have h4 := mul_right_cancel₀ (by positivity : (3 * (k : ℚ) + 1) ≠ 0) h3
  have key : (3 * k).choose k = p3bF_c k * (2 * k + 1) := by exact_mod_cast h4.symm
  rw [Nat.div_eq_of_eq_mul_left (by omega) key]
  rfl

/-! ## Identity (R) (PROOFS §0) — PROVED -/

lemma planar_comm (N : ℕ) (X : ℕ × ℕ → K) (i j : ℕ) : planar N X i j = planar N X j i := by
  unfold planar
  rw [min_comm, max_comm]

lemma planar_add_n (N : ℕ) (X : ℕ × ℕ → K) (i j : ℕ) : planar N X i (j + N) = planar N X i j := by
  unfold planar
  rw [vtx_add_n]

lemma mesh_add_n (N : ℕ) (X : ℕ × ℕ → K) (a b : ℕ) : mesh N X a (b + N) = mesh N X a b := by
  unfold mesh
  rw [planar_add_n, show b + N + 1 = (b + 1) + N by omega, planar_add_n, planar_add_n,
    planar_add_n]

lemma mem_quadIdx {N : ℕ} {q : Quad} :
    q ∈ quadIdx N ↔ 1 ≤ q.u1 ∧ q.u1 < q.u2 ∧ q.u2 < q.u3 ∧ q.u3 < q.u4 ∧ q.u4 ≤ N := by
  obtain ⟨a, b, c, d⟩ := q
  simp only [quadIdx, mem_biUnion, mem_image, mem_Icc, mem_Ioc, Quad.mk.injEq]
  constructor
  · rintro ⟨a', ⟨h1, _⟩, b', ⟨h2, _⟩, c', ⟨h3, _⟩, d', ⟨h4, h5⟩, rfl, rfl, rfl, rfl⟩
    exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨a, ⟨h1, by omega⟩, b, ⟨h2, by omega⟩, c, ⟨h3, by omega⟩, d, ⟨h4, h5⟩, rfl, rfl, rfl, rfl⟩

/-- PROVED. Identity (R): the tile sum over the two `+` blocks is the linear form `vnumX`. -/
theorem vnum_eq_vnumX {N : ℕ} (π : ℕ) (X : ℕ × ℕ → K) {q : Quad} (hq : q ∈ quadIdx N) :
    vnum N π X q = vnumX N π X q := by
  rw [mem_quadIdx] at hq
  obtain ⟨h1, h2, h3, h4, h5⟩ := hq
  unfold vnum vnumX plusPair tileSum blk
  split_ifs with h
  · dsimp only
    rw [mesh_telescope N X (by omega) (by omega), show q.u2 - 1 + 1 = q.u2 by omega,
      show q.u4 - 1 + 1 = q.u4 by omega, planar_comm N X q.u1 q.u4]
    ring
  · dsimp only
    rw [mesh_telescope N X (by omega) (by omega), show q.u3 - 1 + 1 = q.u3 by omega,
      show q.u1 + N - 1 + 1 = q.u1 + N by omega, planar_add_n, planar_add_n,
      planar_comm N X q.u3 q.u1, planar_comm N X q.u2 q.u1]
    ring

/-! ## Theorem A (PROOFS §1) -/

/-- PROVED (3b). Lemma A.2: every quadrangulation has a good quad for `π = 1 − r`.
[checked `defs_mirror.py` D6, every T, N ≤ 12; PROVED below for N = 6, 8 by `decide`. Planned 3b route: the
descent walk of thread §5 (checked D12, N ≤ 12), which avoids building the Steiner tree.] -/
theorem exists_goodQ {N r : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (hr : r < 2) {T : Finset ℕ}
    (hT : Admissible N r T) {G : Finset (ℕ × ℕ)} (hG : G ∈ quadrangulations N) :
    ∃ q ∈ quads N G, GoodQ N T (1 - r) q := by
  exact p3b_exists_goodQ hN hE hr hT hG

lemma vtx_of_gt {N x : ℕ} (h1 : N < x) (h2 : x ≤ 2 * N) : vtx N x = x - N := by
  have := vtx_add_n N (x - N)
  rw [show x - N + N = x by omega] at this
  rw [this, vtx_of_mem (by omega) (by omega)]

/-- PROVED. Lemma A.3: at a good alternating quad, every `+`-block pair is a tile of `S_T`, so the numerator vanishes
on `Z_T`. -/
theorem vnum_eq_zero_of_goodQ {N : ℕ} {T : Finset ℕ} {π : ℕ} (hπ : π < 2)
    {q : Quad} (hq : q ∈ quadIdx N) (halt : q.Alternating) (hg : GoodQ N T π q)
    {X : ℕ × ℕ → K} (hZ : OnZT N T X) : vnum N π X q = 0 := by
  rw [mem_quadIdx] at hq
  obtain ⟨h1, h2, h3, h4, h5⟩ := hq
  obtain ⟨p12, p23, p34⟩ := halt
  have hs : ∀ s ∈ q.sides N, (IsPlus π s → ¬ Meets N T s) ∧ (¬ IsPlus π s → Meets N T s) :=
    fun s hs' => ⟨(hg s hs').1, fun hn => by_contra fun hm => hn ((hg s hs').2 hm)⟩
  obtain ⟨m1p, m1m⟩ := hs (q.u1, q.u2) (by simp [Quad.sides])
  obtain ⟨m2p, m2m⟩ := hs (q.u2, q.u3) (by simp [Quad.sides])
  obtain ⟨m3p, m3m⟩ := hs (q.u3, q.u4) (by simp [Quad.sides])
  obtain ⟨m4p, m4m⟩ := hs (q.u4, q.u1 + N) (by simp [Quad.sides])
  simp only [IsPlus, Meets, blk] at m1p m1m m2p m2m m3p m3m m4p m4m
  have vid : ∀ x, 1 ≤ x → x ≤ N → vtx N x = x := fun x a b => vtx_of_mem a b
  unfold vnum plusPair tileSum blk
  split_ifs with h
  · dsimp only
    apply sum_eq_zero
    intro a ha
    apply sum_eq_zero
    intro b hb
    rw [mem_Icc] at ha hb
    have ha' : a ∉ T := fun hm => m1p h ⟨a, mem_Icc.2 ha, by rw [vid a (by omega) (by omega)]; exact hm⟩
    have hb' : b ∉ T := fun hm => m3p (by omega) ⟨b, mem_Icc.2 hb, by rw [vid b (by omega) (by omega)]; exact hm⟩
    obtain ⟨x, hx, hxT⟩ := m2m (by omega)
    obtain ⟨y, hy, hyT⟩ := m4m (by omega)
    rw [mem_Icc] at hx hy
    rw [vid x (by omega) (by omega)] at hxT
    apply hZ a (mem_Icc.2 ⟨by omega, by omega⟩) b (mem_Icc.2 ⟨by omega, by omega⟩)
    refine ⟨ha', hb', ⟨x, hxT, ?_⟩, ?_⟩
    · rw [min_eq_left (by omega), max_eq_right (by omega)]; omega
    · rw [min_eq_left (by omega), max_eq_right (by omega)]
      rcases Nat.lt_or_ge N y with hyN | hyN
      · rw [vtx_of_gt hyN (by omega)] at hyT
        exact ⟨y - N, hyT, Or.inl (by omega)⟩
      · rw [vid y (by omega) hyN] at hyT
        exact ⟨y, hyT, Or.inr (by omega)⟩
  · dsimp only
    apply sum_eq_zero
    intro a ha
    apply sum_eq_zero
    intro b hb
    rw [mem_Icc] at ha hb
    have ha' : a ∉ T := fun hm => m2p (by omega) ⟨a, mem_Icc.2 ha, by rw [vid a (by omega) (by omega)]; exact hm⟩
    obtain ⟨x, hx, hxT⟩ := m1m h
    obtain ⟨y, hy, hyT⟩ := m3m (by omega)
    rw [mem_Icc] at hx hy
    rw [vid x (by omega) (by omega)] at hxT
    rw [vid y (by omega) (by omega)] at hyT
    rcases Nat.lt_or_ge N b with hbN | hbN
    · have hb' : b - N ∉ T := fun hm =>
        m4p (by omega) ⟨b, mem_Icc.2 hb, by rw [vtx_of_gt hbN (by omega)]; exact hm⟩
      rw [show b = (b - N) + N by omega, mesh_add_n]
      apply hZ a (mem_Icc.2 ⟨by omega, by omega⟩) (b - N) (mem_Icc.2 ⟨by omega, by omega⟩)
      refine ⟨ha', hb', ⟨x, hxT, ?_⟩, ⟨y, hyT, ?_⟩⟩
      · rw [min_eq_right (by omega), max_eq_left (by omega)]; omega
      · rw [max_eq_left (by omega)]; right; omega
    · have hb' : b ∉ T := fun hm =>
        m4p (by omega) ⟨b, mem_Icc.2 hb, by rw [vid b (by omega) hbN]; exact hm⟩
      apply hZ a (mem_Icc.2 ⟨by omega, by omega⟩) b (mem_Icc.2 ⟨by omega, hbN⟩)
      refine ⟨ha', hb', ⟨y, hyT, ?_⟩, ⟨x, hxT, ?_⟩⟩
      · rw [min_eq_left (by omega), max_eq_right (by omega)]; omega
      · rw [min_eq_left (by omega)]; left; omega


/-! ## Theorem A, assembled -/

/-- ASSEMBLED (from `exists_goodQ`, `quads_alternating`: 3b). **Theorem A, per diagram**: with `T`'s legs `ψ⁻`
(`π = 1 − r`), every quartic diagram vanishes at every point of `Z_T`, over any field. -/
theorem diagram_eq_zero {N r : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (hr : r < 2) {T : Finset ℕ}
    (hT : Admissible N r T) {G : Finset (ℕ × ℕ)} (hG : G ∈ quadrangulations N)
    {X : ℕ × ℕ → K} (hZ : OnZT N T X) : diagram N (1 - r) X G = 0 := by
  obtain ⟨q, hq, hgood⟩ := exists_goodQ hN hE hr hT hG
  unfold diagram
  rw [prod_eq_zero hq (vnum_eq_zero_of_goodQ (by omega) (mem_filter.1 hq).1
    (quads_alternating hN hE hG hq) hgood hZ), zero_mul]

/-- ASSEMBLED. **Theorem A, the sum**: `Q_N^{π_T}` vanishes at every point of `Z_T`. -/
theorem Qpi_eq_zero {N r : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (hr : r < 2) {T : Finset ℕ}
    (hT : Admissible N r T) {X : ℕ × ℕ → K} (hZ : OnZT N T X) : Qpi N (1 - r) X = 0 :=
  sum_eq_zero fun _ hG => diagram_eq_zero hN hE hr hT hG hZ

/-! ## The general witness (3b): momentum points, four-leg cycles, generic combination -/

/-- Momentum-type point: `G_s(B) = Σ_{x,y ∈ B} s x y` (twice the Mandelstam invariant of the block `B`). -/
def p3b_G (s : ℕ → ℕ → ℚ) (B : Finset ℕ) : ℚ := ∑ x ∈ B, ∑ y ∈ B, s x y

/-- The point `X_{ij} = G_s(legs i..j−1)`. -/
def p3b_Xs (s : ℕ → ℕ → ℚ) : ℕ × ℕ → ℚ := fun d => p3b_G s (Icc d.1 (d.2 - 1))

lemma p3b_G_insert (s : ℕ → ℕ → ℚ) {x : ℕ} {B : Finset ℕ} (hx : x ∉ B) :
    p3b_G s (insert x B) = p3b_G s B + s x x + ∑ y ∈ B, s x y + ∑ y ∈ B, s y x := by
  unfold p3b_G
  rw [sum_insert hx, sum_insert hx]
  simp only [sum_insert hx, sum_add_distrib]
  ring

lemma p3b_G_empty (s : ℕ → ℕ → ℚ) : p3b_G s ∅ = 0 := by simp [p3b_G]

lemma p3b_G_single (s : ℕ → ℕ → ℚ) (hd : ∀ x, s x x = 0) (x : ℕ) : p3b_G s {x} = 0 := by
  simp [p3b_G, hd]

/-- Complement: with symmetric `s` and zero row sums over `L`, `G(B) = G(L \ B)`. -/
lemma p3b_G_compl (s : ℕ → ℕ → ℚ) (hsym : ∀ x y, s x y = s y x) {L B : Finset ℕ}
    (hrow : ∀ x ∈ L, ∑ y ∈ L, s x y = 0) (hB : B ⊆ L) : p3b_G s B = p3b_G s (L \ B) := by
  unfold p3b_G
  have h1 : ∀ x ∈ L, ∑ y ∈ B, s x y = - ∑ y ∈ L \ B, s x y := by
    intro x hx
    have := hrow x hx
    rw [← sum_sdiff hB] at this
    linarith
  have hL : ∀ x ∈ B, ∑ y ∈ B, s x y = - ∑ y ∈ L \ B, s x y := fun x hx => h1 x (hB hx)
  have hC : ∀ x ∈ L \ B, ∑ y ∈ L \ B, s x y = - ∑ y ∈ B, s x y := by
    intro x hx
    rw [h1 x (sdiff_subset hx)]; ring
  rw [sum_congr rfl hL, sum_congr rfl hC, sum_neg_distrib, sum_neg_distrib, sum_comm]
  congr 1
  apply sum_congr rfl; intro x _; apply sum_congr rfl; intro y _; exact hsym _ _

section W
variable {N : ℕ} {s : ℕ → ℕ → ℚ}

lemma p3b_G_all (hsym : ∀ x y, s x y = s y x) (hrow : ∀ x ∈ Icc 1 N, ∑ y ∈ Icc 1 N, s x y = 0) :
    p3b_G s (Icc 1 N) = 0 := by
  rw [p3b_G_compl s hsym hrow subset_rfl, sdiff_self, bot_eq_empty, p3b_G_empty]

/-- The planar variable of the momentum point, read through `vtx`: the block `u..v−1`. -/
lemma p3b_planar_Xs (hN : 2 ≤ N) (hsym : ∀ x y, s x y = s y x) (hd : ∀ x, s x x = 0)
    (hrow : ∀ x ∈ Icc 1 N, ∑ y ∈ Icc 1 N, s x y = 0) {u v : ℕ} (hu : 1 ≤ u) (huN : u ≤ N) (huv : u ≤ v)
    (hv : v ≤ N + 1) : planar N (p3b_Xs s) u v = p3b_G s (Icc u (v - 1)) := by
  have compl : ∀ k, 1 ≤ k → k ≤ N + 1 → p3b_G s (Icc 1 (k - 1)) = p3b_G s (Icc k N) := by
    intro k hk1 hk2
    rw [p3b_G_compl s hsym hrow (by intro x; simp only [mem_Icc]; omega)]
    congr 1
    ext x; simp only [mem_sdiff, mem_Icc]; omega
  rcases Nat.lt_or_ge N v with hvN | hvN
  · have hv' : v = N + 1 := by omega
    subst hv'
    unfold planar
    rw [vtx_of_mem hu huN, show N + 1 = 1 + N by omega, vtx_add_n, vtx_of_mem le_rfl (by omega),
      min_eq_right hu, max_eq_left hu, show 1 + N - 1 = N by omega]
    split_ifs with hdg
    · simp only [p3b_Xs]; exact compl u hu (by omega)
    · rw [mem_diagonals] at hdg
      dsimp only at hdg
      rw [← compl u hu (by omega)]
      rcases (show u = 1 ∨ u = 2 ∨ u = N by omega) with h | h | h
      · subst h; simp [p3b_G_empty]
      · subst h; rw [show (2 : ℕ) - 1 = 1 by rfl, Icc_self, p3b_G_single s hd]
      · rw [h, compl N (by omega) (by omega), Icc_self, p3b_G_single s hd]
  · unfold planar
    rw [vtx_of_mem hu huN, vtx_of_mem (by omega) hvN, min_eq_left huv, max_eq_right huv]
    split_ifs with hdg
    · rfl
    · rw [mem_diagonals] at hdg
      dsimp only at hdg
      rcases (show v = u ∨ v = u + 1 ∨ (u = 1 ∧ v = N) by omega) with h | h | ⟨h1, h2⟩
      · subst h; rw [Icc_eq_empty (by omega), p3b_G_empty]
      · subst h; rw [show u + 1 - 1 = u by omega, Icc_self, p3b_G_single s hd]
      · rw [h1, h2, compl N (by omega) (by omega), Icc_self, p3b_G_single s hd]

/-- The mesh variable of the momentum point: `c_ab = −2 s_ab` for legs `a < b`. -/
lemma p3b_mesh_Xs (hN : 2 ≤ N) (hsym : ∀ x y, s x y = s y x) (hd : ∀ x, s x x = 0)
    (hrow : ∀ x ∈ Icc 1 N, ∑ y ∈ Icc 1 N, s x y = 0) {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ N) :
    mesh N (p3b_Xs s) a b = -2 * s a b := by
  unfold mesh
  rw [p3b_planar_Xs hN hsym hd hrow ha (by omega) (by omega) (by omega),
    p3b_planar_Xs hN hsym hd hrow (by omega) (by omega) (by omega) (by omega),
    p3b_planar_Xs hN hsym hd hrow ha (by omega) (by omega) (by omega),
    p3b_planar_Xs hN hsym hd hrow (by omega) (by omega) (by omega) (by omega)]
  set A := Icc (a + 1) (b - 1) with hA
  have e1 : Icc a (b - 1) = insert a A := by ext x; simp only [hA, mem_insert, mem_Icc]; omega
  have e2 : Icc (a + 1) (b + 1 - 1) = insert b A := by ext x; simp only [hA, mem_insert, mem_Icc]; omega
  have e3 : Icc a (b + 1 - 1) = insert a (insert b A) := by
    ext x; simp only [hA, mem_insert, mem_Icc]; omega
  have haA : a ∉ A := by simp only [hA, mem_Icc]; omega
  have hbA : b ∉ A := by simp only [hA, mem_Icc]; omega
  have habA : a ∉ insert b A := by simp only [hA, mem_insert, mem_Icc]; omega
  rw [e1, e2, e3, p3b_G_insert s habA, p3b_G_insert s haA, p3b_G_insert s hbA, sum_insert hbA,
    sum_insert hbA, hd, hd]
  have : ∑ y ∈ A, s y a = ∑ y ∈ A, s a y := sum_congr rfl fun y _ => hsym y a
  rw [this, hsym b a]
  ring

lemma p3b_mesh_symm (X : ℕ × ℕ → ℚ) (a b : ℕ) : mesh N X a b = mesh N X b a := by
  unfold mesh
  rw [planar_comm N X a b, planar_comm N X (a + 1) (b + 1), planar_comm N X a (b + 1),
    planar_comm N X (a + 1) b]
  ring

lemma p3b_InST_comm {T : Finset ℕ} {a b : ℕ} : InST T a b ↔ InST T b a := by
  unfold InST
  rw [min_comm, max_comm]
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨h2, h1, h3, h4⟩

lemma p3b_onZT_Xs (hN : 2 ≤ N) {T : Finset ℕ} (hsym : ∀ x y, s x y = s y x) (hd : ∀ x, s x x = 0)
    (hrow : ∀ x ∈ Icc 1 N, ∑ y ∈ Icc 1 N, s x y = 0) (hST : ∀ x y, InST T x y → s x y = 0) :
    OnZT N T (p3b_Xs s) := by
  intro a ha b hb h
  rw [mem_Icc] at ha hb
  rcases lt_trichotomy a b with hab | rfl | hab
  · rw [p3b_mesh_Xs hN hsym hd hrow ha.1 hab hb.2, hST a b h, mul_zero]
  · exfalso
    obtain ⟨-, -, ⟨t, -, h1, h2⟩, -⟩ := h
    simp only [min_self, max_self] at h1 h2
    omega
  · rw [p3b_mesh_symm, p3b_mesh_Xs hN hsym hd hrow hb.1 hab ha.2, hST b a (p3b_InST_comm.1 h), mul_zero]

end W

/-! The four-leg points (R2-Z26 Lemma 1.7, simplified): an alternating 4-cycle `p₁p₂p₃p₄`. -/

/-- The symmetric elementary matrix on the pair `{p, q}`. -/
def p3b_e (p q x y : ℕ) : ℚ := (if x = p ∧ y = q then 1 else 0) + (if x = q ∧ y = p then 1 else 0)

/-- The alternating 4-cycle `s = e₁₂ − e₂₃ + e₃₄ − e₄₁`: symmetric, zero row sums (a momentum point). -/
def p3b_cyc (p1 p2 p3 p4 : ℕ) (x y : ℕ) : ℚ :=
  p3b_e p1 p2 x y - p3b_e p2 p3 x y + p3b_e p3 p4 x y - p3b_e p4 p1 x y

lemma p3b_e_symm (p q x y : ℕ) : p3b_e p q x y = p3b_e p q y x := by
  unfold p3b_e; rw [add_comm]
  congr 1 <;> simp only [and_comm]

lemma p3b_e_diag {p q : ℕ} (h : p ≠ q) (x : ℕ) : p3b_e p q x x = 0 := by
  unfold p3b_e
  split_ifs <;> first | omega | simp_all

lemma p3b_e_row {p q : ℕ} {L : Finset ℕ} (hp : p ∈ L) (hq : q ∈ L) (x : ℕ) :
    ∑ y ∈ L, p3b_e p q x y = (if x = p then 1 else 0) + (if x = q then 1 else 0) := by
  unfold p3b_e
  rw [sum_add_distrib]
  congr 1
  · by_cases hx : x = p <;> simp [hx, hq]
  · by_cases hx : x = q <;> simp [hx, hp]

lemma p3b_e_G (p q : ℕ) (B : Finset ℕ) :
    p3b_G (p3b_e p q) B = if p ∈ B ∧ q ∈ B then 2 else 0 := by
  unfold p3b_G p3b_e
  simp only [sum_add_distrib]
  by_cases hp : p ∈ B <;> by_cases hq : q ∈ B <;> simp [hp, hq, sum_ite_eq', ite_and]
  norm_num

lemma p3b_e_zero {T : Finset ℕ} {p q x y : ℕ} (hpq : ¬ InST T p q) (h : InST T x y) : p3b_e p q x y = 0 := by
  unfold p3b_e
  split_ifs with h1 h2 h2
  · exact absurd (h1.1 ▸ h1.2 ▸ h) hpq
  · exact absurd (h1.1 ▸ h1.2 ▸ h) hpq
  · exact absurd (p3b_InST_comm.1 (h2.1 ▸ h2.2 ▸ h)) hpq
  · simp

/-- A four-leg point in `Z_T` with `X_{ij} ≠ 0`, given an alternating 4-cycle with `p₁, p₂` in the block `i..j−1`,
`p₃, p₄` outside it, and no edge of the cycle a tile of `S_T`. -/
lemma p3b_cycle_witness {N : ℕ} (hN : 2 ≤ N) {T : Finset ℕ} {i j p1 p2 p3 p4 : ℕ}
    (h1 : p1 ∈ Icc i (j - 1)) (h2 : p2 ∈ Icc i (j - 1)) (h3 : p3 ∈ Icc 1 N \ Icc i (j - 1))
    (h4 : p4 ∈ Icc 1 N \ Icc i (j - 1)) (hij : Icc i (j - 1) ⊆ Icc 1 N) (h12 : p1 ≠ p2) (h34 : p3 ≠ p4)
    (n12 : ¬ InST T p1 p2) (n23 : ¬ InST T p2 p3) (n34 : ¬ InST T p3 p4) (n41 : ¬ InST T p4 p1) :
    ∃ X : ℕ × ℕ → ℚ, OnZT N T X ∧ X (i, j) ≠ 0 := by
  have h3' := mem_sdiff.1 h3
  have h4' := mem_sdiff.1 h4
  have h23 : p2 ≠ p3 := fun h => h3'.2 (h ▸ h2)
  have h41 : p4 ≠ p1 := fun h => h4'.2 (h ▸ h1)
  refine ⟨p3b_Xs (p3b_cyc p1 p2 p3 p4), p3b_onZT_Xs hN ?_ ?_ ?_ ?_, ?_⟩
  · intro x y; unfold p3b_cyc; rw [p3b_e_symm p1, p3b_e_symm p2, p3b_e_symm p3, p3b_e_symm p4]
  · intro x; unfold p3b_cyc
    rw [p3b_e_diag h12, p3b_e_diag h23, p3b_e_diag h34, p3b_e_diag h41]; ring
  · intro x _
    unfold p3b_cyc
    simp only [sum_add_distrib, sum_sub_distrib]
    rw [p3b_e_row (hij h1) (hij h2), p3b_e_row (hij h2) h3'.1, p3b_e_row h3'.1 h4'.1,
      p3b_e_row h4'.1 (hij h1)]
    ring
  · intro x y h
    unfold p3b_cyc
    rw [p3b_e_zero n12 h, p3b_e_zero n23 h, p3b_e_zero n34 h, p3b_e_zero n41 h]; ring
  · have hG : p3b_Xs (p3b_cyc p1 p2 p3 p4) (i, j) = p3b_G (p3b_e p1 p2) (Icc i (j - 1)) -
        p3b_G (p3b_e p2 p3) (Icc i (j - 1)) + p3b_G (p3b_e p3 p4) (Icc i (j - 1)) -
        p3b_G (p3b_e p4 p1) (Icc i (j - 1)) := by
      simp only [p3b_Xs, p3b_G, p3b_cyc, sum_add_distrib, sum_sub_distrib]
    rw [hG, p3b_e_G, p3b_e_G, p3b_e_G, p3b_e_G]
    simp [h1, h2, h3'.2, h4'.2]

lemma p3b_planar_lin {N : ℕ} (X Y : ℕ × ℕ → ℚ) (c : ℚ) (u v : ℕ) :
    planar N (fun d => X d + c * Y d) u v = planar N X u v + c * planar N Y u v := by
  unfold planar; split_ifs <;> simp

lemma p3b_onZT_zero {N : ℕ} {T : Finset ℕ} : OnZT N T (fun _ => (0 : ℚ)) := by
  intro a _ b _ _
  simp [mesh, planar]

lemma p3b_onZT_lin {N : ℕ} {T : Finset ℕ} {X Y : ℕ × ℕ → ℚ} (c : ℚ) (hX : OnZT N T X) (hY : OnZT N T Y) :
    OnZT N T (fun d => X d + c * Y d) := by
  intro a ha b hb h
  have e : mesh N (fun d => X d + c * Y d) a b = mesh N X a b + c * mesh N Y a b := by
    unfold mesh; simp only [p3b_planar_lin]; ring
  rw [e, hX a ha b hb h, hY a ha b hb h]; ring

/-- A linear family that is non-zero at each coordinate of `D` separately has a member non-zero at all of them
(a vector space over an infinite field is no finite union of proper subspaces; induction on `D`). -/
lemma p3b_avoid (P : (ℕ × ℕ → ℚ) → Prop) (h0 : P fun _ => 0)
    (hadd : ∀ X Y (c : ℚ), P X → P Y → P fun d => X d + c * Y d) :
    ∀ D : Finset (ℕ × ℕ), (∀ d ∈ D, ∃ Y, P Y ∧ Y d ≠ 0) → ∃ X, P X ∧ ∀ d ∈ D, X d ≠ 0 := by
  intro D
  induction D using Finset.induction_on with
  | empty => exact fun _ => ⟨_, h0, by simp⟩
  | insert e S he ih =>
    intro hD
    obtain ⟨X, hX, hXS⟩ := ih fun d hd => hD d (mem_insert_of_mem hd)
    obtain ⟨Y, hY, hYe⟩ := hD e (mem_insert_self e S)
    obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ((insert e S).image fun d => -X d / Y d)
    refine ⟨fun d => X d + c * Y d, hadd X Y c hX hY, fun d hd h => ?_⟩
    dsimp only at h
    by_cases hYd : Y d = 0
    · rw [hYd, mul_zero, add_zero] at h
      rcases mem_insert.1 hd with rfl | hdS
      · exact hYe hYd
      · exact hXS d hdS h
    · apply hc
      refine mem_image.2 ⟨d, hd, ?_⟩
      field_simp
      linarith

lemma p3b_nInST_left {T : Finset ℕ} {x y : ℕ} (h : x ∈ T) : ¬ InST T x y := fun h' => h'.1 h
lemma p3b_nInST_right {T : Finset ℕ} {x y : ℕ} (h : y ∈ T) : ¬ InST T x y := fun h' => h'.2.1 h

lemma p3b_nInST_in {T : Finset ℕ} {i j x y : ℕ} (hT : ∀ t ∈ T, ¬ (i ≤ t ∧ t ≤ j)) (hx : i ≤ x ∧ x ≤ j)
    (hy : i ≤ y ∧ y ≤ j) : ¬ InST T x y := by
  rintro ⟨-, -, ⟨t, ht, h1, h2⟩, -⟩
  apply hT t ht
  constructor
  · rcases le_total x y with h | h
    · rw [min_eq_left h] at h1; omega
    · rw [min_eq_right h] at h1; omega
  · rcases le_total x y with h | h
    · rw [max_eq_right h] at h2; omega
    · rw [max_eq_left h] at h2; omega

lemma p3b_nInST_out {T : Finset ℕ} {i j x y : ℕ} (hT : ∀ t ∈ T, i ≤ t ∧ t ≤ j) (hx : x < i ∨ j < x)
    (hy : y < i ∨ j < y) : ¬ InST T x y := by
  rintro ⟨-, -, ⟨t, ht, h1, h2⟩, ⟨t', ht', h3⟩⟩
  have := hT t ht
  have := hT t' ht'
  rcases le_total x y with h | h
  · rw [min_eq_left h] at h1 h3; rw [max_eq_right h] at h2 h3; omega
  · rw [min_eq_right h] at h1 h3; rw [max_eq_left h] at h2 h3; omega

/-- Per-chord witness (R2-Z26 Lemma 1.7 in the 4-cycle form): for every diagonal `(i, j)` a point of `Z_T` with
`X_{ij} ≠ 0`. Two legs `p₁, p₂` inside the block `i..j−1`, two `p₃, p₄` outside, chosen so that every edge of the
cycle meets `T` or stays inside a `T`-free arc. -/
lemma p3b_chord_witness {N r : ℕ} (hN : 4 ≤ N) {T : Finset ℕ} (hT : Admissible N r T) {i j : ℕ}
    (hd : (i, j) ∈ diagonals N) : ∃ X : ℕ × ℕ → ℚ, OnZT N T X ∧ X (i, j) ≠ 0 := by
  obtain ⟨hT1, hT2, -⟩ := hT
  rw [mem_diagonals] at hd
  dsimp only at hd
  have hTN : ∀ t ∈ T, 1 ≤ t ∧ t ≤ N := fun t ht => mem_Icc.1 (hT1 ht)
  obtain ⟨t, ht, t', ht', htt'⟩ := one_lt_card.1 (by omega : 1 < T.card)
  have hB : Icc i (j - 1) ⊆ Icc 1 N := by intro x; simp only [mem_Icc]; omega
  have mB : ∀ x, x ∈ Icc i (j - 1) ↔ i ≤ x ∧ x ≤ j - 1 := fun x => mem_Icc
  have mC : ∀ x, x ∈ Icc 1 N \ Icc i (j - 1) ↔ (1 ≤ x ∧ x ≤ N) ∧ ¬ (i ≤ x ∧ x ≤ j - 1) := by
    intro x; simp only [mem_sdiff, mem_Icc]
  set q := if i = 1 then j else i - 1 with hq
  have hq1 : 1 ≤ q ∧ q ≤ N ∧ ¬ (i ≤ q ∧ q ≤ j - 1) ∧ q ≠ N := by
    rw [hq]; split_ifs <;> omega
  by_cases hA : ∃ t ∈ T, i ≤ t ∧ t ≤ j - 1
  · by_cases hC : ∃ t ∈ T, ¬ (i ≤ t ∧ t ≤ j - 1)
    · obtain ⟨t1, ht1, ht1B⟩ := hA
      obtain ⟨t3, ht3, ht3B⟩ := hC
      have := hTN t3 ht3
      refine p3b_cycle_witness (by omega) ((mB t1).2 ht1B)
        ((mB (if t1 = i then i + 1 else i)).2 (by split_ifs <;> omega)) ((mC t3).2 ⟨this, ht3B⟩)
        ((mC (if t3 = N then q else N)).2 (by split_ifs <;> omega)) hB (by split_ifs <;> omega)
        (by split_ifs <;> omega) (p3b_nInST_left ht1) (p3b_nInST_right ht3) (p3b_nInST_left ht3)
        (p3b_nInST_right ht1)
    · push Not at hC
      have ht3 := hTN t ht
      have ht4 := hTN t' ht'
      have hq2 := hq1
      refine p3b_cycle_witness (by omega) ((mB t).2 (hC t ht)) ((mB t').2 (hC t' ht'))
        ((mC q).2 ⟨⟨hq1.1, hq1.2.1⟩, hq1.2.2.1⟩) ((mC N).2 ⟨⟨by omega, le_rfl⟩, by omega⟩) hB htt' hq1.2.2.2
        (p3b_nInST_left ht) (p3b_nInST_left ht') (p3b_nInST_out (i := i) (j := j - 1) hC ?_ ?_)
        (p3b_nInST_right ht)
      · have := hq1.2.2.1; omega
      · omega
  · push Not at hA
    have ht3 := hTN t ht
    have ht4 := hTN t' ht'
    have hA' : ∀ t ∈ T, ¬ (i ≤ t ∧ t ≤ j - 1) := fun t ht h => absurd h.2 (Nat.not_le.2 (hA t ht h.1))
    refine p3b_cycle_witness (by omega) ((mB i).2 (by omega)) ((mB (i + 1)).2 (by omega))
      ((mC t).2 ⟨ht3, hA' t ht⟩) ((mC t').2 ⟨ht4, hA' t' ht'⟩) hB (by omega) htt'
      (p3b_nInST_in hA' (by omega) (by omega)) (p3b_nInST_right ht) (p3b_nInST_left ht)
      (p3b_nInST_left ht')

theorem p3b_ZT_inhabited {N r : ℕ} (hN : 4 ≤ N) {T : Finset ℕ} (hT : Admissible N r T) :
    ∃ X : ℕ × ℕ → ℚ, OnZT N T X ∧ ∀ d ∈ diagonals N, X d ≠ 0 :=
  p3b_avoid (OnZT N T) p3b_onZT_zero (fun _ _ c hX hY => p3b_onZT_lin c hX hY) (diagonals N)
    fun d hd => p3b_chord_witness hN hT (i := d.1) (j := d.2) hd

/-- PROVED (3b). **Inhabitation witness**: `Z_T` contains a rational point at which every diagonal (in particular
every propagator) is non-zero, so `Z_T` lies in no polar hyperplane and Theorem A is a statement about the rational
function `Q_N^{π_T}` restricted to `Z_T`, not a junk-value artefact. Planned proof (thread §5): R2-Z26 Lemma 1.7's
4-leg momentum points, one per chord, combined with weights `3^k` (balanced ternary). [checked `defs_mirror.py` D10,
N ≤ 10, every T; D9 small integer points N = 6, 8; PROVED below for N = 6] -/
theorem ZT_inhabited {N r : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (hr : r < 2) {T : Finset ℕ}
    (hT : Admissible N r T) :
    ∃ X : ℕ × ℕ → ℚ, OnZT N T X ∧ ∀ d ∈ diagonals N, X d ≠ 0 := by
  clear hE hr
  exact p3b_ZT_inhabited hN hT

/-- ASSEMBLED. Theorem A in the form "the rational function vanishes on `Z_T`": a non-degenerate point exists, and
every diagram and the sum vanish at every point of `Z_T`. -/
theorem theoremA {N r : ℕ} (hN : 4 ≤ N) (hE : N % 2 = 0) (hr : r < 2) {T : Finset ℕ}
    (hT : Admissible N r T) :
    (∃ X : ℕ × ℕ → ℚ, OnZT N T X ∧ ∀ d ∈ diagonals N, X d ≠ 0) ∧
    (∀ (X : ℕ × ℕ → K), OnZT N T X →
      (∀ G ∈ quadrangulations N, diagram N (1 - r) X G = 0) ∧ Qpi N (1 - r) X = 0) :=
  ⟨ZT_inhabited hN hE hr hT, fun _ hZ =>
    ⟨fun _ hG => diagram_eq_zero hN hE hr hT hG hZ, Qpi_eq_zero hN hE hr hT hZ⟩⟩

/-! ## Small cases, proved end to end from the definitions -/

section Small

theorem card_quadrangulations_small :
    (quadrangulations 4).card = 1 ∧ (quadrangulations 6).card = 3 ∧ (quadrangulations 8).card = 12 := by
  decide

theorem diagonals_six :
    diagonals 6 = {(1, 3), (1, 4), (1, 5), (2, 4), (2, 5), (2, 6), (3, 5), (3, 6), (4, 6)} := by
  decide

theorem quadrangulations_6 : quadrangulations 6 = {{(1, 4)}, {(2, 5)}, {(3, 6)}} := by
  decide

theorem quads_6_0 : quads 6 {(1, 4)} = {⟨1, 2, 3, 4⟩, ⟨1, 4, 5, 6⟩} := by
  decide

theorem quads_6_1 : quads 6 {(2, 5)} = {⟨1, 2, 5, 6⟩, ⟨2, 3, 4, 5⟩} := by
  decide

theorem quads_6_2 : quads 6 {(3, 6)} = {⟨1, 2, 3, 6⟩, ⟨3, 4, 5, 6⟩} := by
  decide

/-- PROVED. The hexagon's quads alternate in parity (instance of `quads_alternating`). -/
theorem alternating_six : ∀ G ∈ quadrangulations 6, ∀ q ∈ quads 6 G, q.Alternating := by
  decide

/-- PROVED. Lemma A.2 at N = 6, for every admissible `T` (8 sets) and both parities. -/
theorem goodQ_six : ∀ r ∈ range 2, ∀ T ∈ (Icc 1 6).powerset, Admissible 6 r T →
    ∀ G ∈ quadrangulations 6, ∃ q ∈ quads 6 G, GoodQ 6 T (1 - r) q := by
  decide

/-- PROVED. **Theorem A at N = 6, end to end**: for every admissible `T`, over any field, every diagram and
`Q_6^{π_T}` vanish on `Z_T` (A.2 and alternation by `decide`, A.3 proved for all N). -/
theorem theoremA_six {r : ℕ} (hr : r < 2) {T : Finset ℕ} (hT : Admissible 6 r T) (X : ℕ × ℕ → K)
    (hZ : OnZT 6 T X) : (∀ G ∈ quadrangulations 6, diagram 6 (1 - r) X G = 0) ∧ Qpi 6 (1 - r) X = 0 := by
  have hd : ∀ G ∈ quadrangulations 6, diagram 6 (1 - r) X G = 0 := by
    intro G hG
    obtain ⟨q, hq, hgood⟩ := goodQ_six r (mem_range.2 hr) T (mem_powerset.2 hT.1) hT G hG
    unfold diagram
    rw [prod_eq_zero hq (vnum_eq_zero_of_goodQ (by omega) (mem_filter.1 hq).1
      (alternating_six G hG q hq) hgood hZ), zero_mul]
  exact ⟨hd, sum_eq_zero hd⟩

/-- PROVED. `Q_6^π` written out: three diagrams, numerators in the `(R)` form. -/
theorem Qpi_six (π : ℕ) (X : ℕ × ℕ → K) : Qpi 6 π X =
  vnumX 6 π X ⟨1, 2, 3, 4⟩ * vnumX 6 π X ⟨1, 4, 5, 6⟩ * ((X (1, 4))⁻¹) +
  vnumX 6 π X ⟨1, 2, 5, 6⟩ * vnumX 6 π X ⟨2, 3, 4, 5⟩ * ((X (2, 5))⁻¹) +
  vnumX 6 π X ⟨1, 2, 3, 6⟩ * vnumX 6 π X ⟨3, 4, 5, 6⟩ * ((X (3, 6))⁻¹) := by
  rw [Qpi, quadrangulations_6, sum_insert (by decide), sum_insert (by decide), sum_singleton]
  simp only [diagram, quads_6_0, quads_6_1, quads_6_2]
  rw [prod_insert (by decide), prod_singleton, prod_insert (by decide), prod_singleton,
    prod_insert (by decide), prod_singleton, prod_singleton, prod_singleton, prod_singleton]
  simp only [vnum_eq_vnumX π X (by decide : (⟨1, 2, 3, 4⟩ : Quad) ∈ quadIdx 6),
    vnum_eq_vnumX π X (by decide : (⟨1, 4, 5, 6⟩ : Quad) ∈ quadIdx 6),
    vnum_eq_vnumX π X (by decide : (⟨1, 2, 5, 6⟩ : Quad) ∈ quadIdx 6),
    vnum_eq_vnumX π X (by decide : (⟨2, 3, 4, 5⟩ : Quad) ∈ quadIdx 6),
    vnum_eq_vnumX π X (by decide : (⟨1, 2, 3, 6⟩ : Quad) ∈ quadIdx 6),
    vnum_eq_vnumX π X (by decide : (⟨3, 4, 5, 6⟩ : Quad) ∈ quadIdx 6)]
  ring

/-- A point of the hexagon's kinematic space from its nine diagonal values (order of `diagonals_six`). -/
def hexPt (x13 x14 x15 x24 x25 x26 x35 x36 x46 : ℚ) : ℕ × ℕ → ℚ := fun d =>
  if d = (1, 3) then x13 else if d = (1, 4) then x14 else if d = (1, 5) then x15
  else if d = (2, 4) then x24 else if d = (2, 5) then x25 else if d = (2, 6) then x26
  else if d = (3, 5) then x35 else if d = (3, 6) then x36 else if d = (4, 6) then x46 else 0

lemma onZT_of_list {N : ℕ} {T : Finset ℕ} {X : ℕ × ℕ → K} (L : Finset (ℕ × ℕ))
    (hL : ∀ a ∈ Icc 1 N, ∀ b ∈ Icc 1 N, InST T a b → (a, b) ∈ L)
    (hX : ∀ p ∈ L, mesh N X p.1 p.2 = 0) : OnZT N T X :=
  fun a ha b hb h => hX (a, b) (hL a ha b hb h)

lemma hexPt_ne {x13 x14 x15 x24 x25 x26 x35 x36 x46 : ℚ} (h13 : x13 ≠ 0) (h14 : x14 ≠ 0) (h15 : x15 ≠ 0)
    (h24 : x24 ≠ 0) (h25 : x25 ≠ 0) (h26 : x26 ≠ 0) (h35 : x35 ≠ 0) (h36 : x36 ≠ 0) (h46 : x46 ≠ 0) :
    ∀ d ∈ diagonals 6, hexPt x13 x14 x15 x24 x25 x26 x35 x36 x46 d ≠ 0 := by
  intro d hd
  rw [diagonals_six] at hd
  simp only [mem_insert, mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hexPt, *]

theorem admissible_six :
    ((Icc 1 6).powerset.filter fun T => Admissible 6 0 T ∨ Admissible 6 1 T) =
      {{1, 3}, {1, 5}, {3, 5}, {1, 3, 5}, {2, 4}, {2, 6}, {4, 6}, {2, 4, 6}} := by
  decide

/-- PROVED. **Inhabitation witness at N = 6** (vacuity guard): for every admissible `T`, an explicit rational point
of `Z_T` with all nine diagonals non-zero (values from `defs_mirror.py` D9). -/
theorem ZT_inhabited_six {r : ℕ} (hr : r < 2) {T : Finset ℕ} (hT : Admissible 6 r T) :
    ∃ X : ℕ × ℕ → ℚ, OnZT 6 T X ∧ ∀ d ∈ diagonals 6, X d ≠ 0 := by
  have hmem : T ∈ ((Icc 1 6).powerset.filter fun T => Admissible 6 0 T ∨ Admissible 6 1 T) := by
    refine mem_filter.2 ⟨mem_powerset.2 hT.1, ?_⟩
    interval_cases r
    · exact Or.inl hT
    · exact Or.inr hT
  rw [admissible_six] at hmem
  simp only [mem_insert, mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨hexPt 2 (-1) 2 (-2) (-1) (-1) 1 1 2, onZT_of_list {(2, 4), (2, 5), (2, 6), (4, 2), (5, 2), (6, 2)} (by decide) (by
      intro p hp; simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [mesh, planar, vtx, diagonals_six, hexPt]),
      hexPt_ne (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)⟩
  · exact ⟨hexPt 1 1 (-1) 1 2 1 1 2 2, onZT_of_list {(2, 6), (3, 6), (4, 6), (6, 2), (6, 3), (6, 4)} (by decide) (by
      intro p hp; simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [mesh, planar, vtx, diagonals_six, hexPt]),
      hexPt_ne (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)⟩
  · exact ⟨hexPt (-1) (-2) (-1) 1 2 1 1 2 (-1), onZT_of_list {(1, 4), (2, 4), (4, 1), (4, 2), (4, 6), (6, 4)} (by decide) (by
      intro p hp; simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [mesh, planar, vtx, diagonals_six, hexPt]),
      hexPt_ne (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)⟩
  · exact ⟨hexPt (-1) 1 2 2 1 2 (-1) 1 (-1), onZT_of_list {(2, 4), (2, 6), (4, 2), (4, 6), (6, 2), (6, 4)} (by decide) (by
      intro p hp; simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [mesh, planar, vtx, diagonals_six, hexPt]),
      hexPt_ne (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)⟩
  · exact ⟨hexPt (-1) (-2) (-2) (-1) (-1) 2 1 (-1) (-2), onZT_of_list {(1, 3), (3, 1), (3, 5), (3, 6), (5, 3), (6, 3)} (by decide) (by
      intro p hp; simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [mesh, planar, vtx, diagonals_six, hexPt]),
      hexPt_ne (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)⟩
  · exact ⟨hexPt 2 1 1 (-1) (-1) (-2) 1 1 1, onZT_of_list {(1, 3), (1, 4), (1, 5), (3, 1), (4, 1), (5, 1)} (by decide) (by
      intro p hp; simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [mesh, planar, vtx, diagonals_six, hexPt]),
      hexPt_ne (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)⟩
  · exact ⟨hexPt (-1) 2 (-2) (-1) (-1) 1 (-1) 1 2, onZT_of_list {(1, 5), (2, 5), (3, 5), (5, 1), (5, 2), (5, 3)} (by decide) (by
      intro p hp; simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [mesh, planar, vtx, diagonals_six, hexPt]),
      hexPt_ne (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)⟩
  · exact ⟨hexPt 1 (-1) (-1) (-2) (-2) (-1) (-2) (-1) 1, onZT_of_list {(1, 3), (1, 5), (3, 1), (3, 5), (5, 1), (5, 3)} (by decide) (by
      intro p hp; simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [mesh, planar, vtx, diagonals_six, hexPt]),
      hexPt_ne (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)⟩

/-! ### Negative controls (each must fail; values from `defs_mirror.py` D8) -/

/-- PROVED. Control 1 (`S_T` minus one tile): at N = 6, `T = {1, 3}` (`S_T = {c24, c25, c26}`, the row locus of
leg 2), a point where `c24 = c26 = 0` but `c25 ≠ 0`, all diagonals non-zero, has `Q_6^{π_T} ≠ 0` (it is `−4`). -/
theorem negctl_minus_tile :
    ∃ X : ℕ × ℕ → ℚ, (∀ a ∈ Icc 1 6, ∀ b ∈ Icc 1 6, InST {1, 3} a b → (a, b) ≠ (2, 5) → (a, b) ≠ (5, 2) →
      mesh 6 X a b = 0) ∧ mesh 6 X 2 5 ≠ 0 ∧ (∀ d ∈ diagonals 6, X d ≠ 0) ∧ Qpi 6 (1 - 1) X ≠ 0 := by
  refine ⟨hexPt 1 1 1 1 (-1) (-2) (-2) (-1) (-2), ?_, ?_, ?_, ?_⟩
  · have hL : ∀ a ∈ Icc 1 6, ∀ b ∈ Icc 1 6, InST {1, 3} a b → (a, b) ≠ (2, 5) → (a, b) ≠ (5, 2) →
        (a, b) ∈ ({(2, 4), (2, 6), (4, 2), (6, 2)} : Finset (ℕ × ℕ)) := by decide
    intro a ha b hb h h1 h2
    have hp := hL a ha b hb h h1 h2
    simp only [mem_insert, mem_singleton, Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      norm_num [mesh, planar, vtx, diagonals_six, hexPt]
  · norm_num [mesh, planar, vtx, diagonals_six, hexPt]
  · exact hexPt_ne (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · rw [Qpi_six]
    norm_num [vnumX, planar, vtx, diagonals_six, hexPt]

/-- PROVED. `diagram 6 π X {(2,5)}` written out. -/
theorem diagram_six_25 (π : ℕ) (X : ℕ × ℕ → K) : diagram 6 π X {(2, 5)} =
    vnumX 6 π X ⟨1, 2, 5, 6⟩ * vnumX 6 π X ⟨2, 3, 4, 5⟩ * (X (2, 5))⁻¹ := by
  rw [diagram, quads_6_1, prod_insert (by decide), prod_singleton, prod_singleton,
    vnum_eq_vnumX π X (by decide : (⟨1, 2, 5, 6⟩ : Quad) ∈ quadIdx 6),
    vnum_eq_vnumX π X (by decide : (⟨2, 3, 4, 5⟩ : Quad) ∈ quadIdx 6)]

/-- PROVED. Control 2 (wrong polarity): at N = 6, `T = {1, 3}` with `T`'s legs `ψ⁺` (`π = r = 1`), a point of `Z_T`
with all diagonals non-zero where the diagram `{(2,5)}` is non-zero (`2`); the sum still vanishes there (Theorem B,
R2-Z30 C8: the zero is manifest only in the polarity `π_T`). -/
theorem negctl_wrong_polarity :
    ∃ X : ℕ × ℕ → ℚ, OnZT 6 {1, 3} X ∧ (∀ d ∈ diagonals 6, X d ≠ 0) ∧
      diagram 6 1 X {(2, 5)} ≠ 0 ∧ Qpi 6 1 X = 0 := by
  refine ⟨hexPt (-2) (-2) 2 2 1 1 (-1) (-1) (-2), onZT_of_list {(2, 4), (2, 5), (2, 6), (4, 2), (5, 2), (6, 2)}
    (by decide) (by
      intro p hp; simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [mesh, planar, vtx, diagonals_six, hexPt]),
    hexPt_ne (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num), ?_, ?_⟩
  · rw [diagram_six_25]
    norm_num [vnumX, planar, vtx, diagonals_six, hexPt]
  · rw [Qpi_six]
    norm_num [vnumX, planar, vtx, diagonals_six, hexPt]


/-! ### N = 8 -/

theorem quadrangulations_8 : quadrangulations 8 = {{(1, 4), (1, 6)}, {(1, 4), (4, 7)}, {(1, 4), (5, 8)}, {(1, 6), (2, 5)}, {(1, 6), (3, 6)}, {(2, 5), (2, 7)}, {(2, 5), (5, 8)}, {(2, 7), (3, 6)}, {(2, 7), (4, 7)}, {(3, 6), (3, 8)}, {(3, 8), (4, 7)}, {(3, 8), (5, 8)}} := by
  decide

theorem quads_8_0 : quads 8 {(1, 4), (1, 6)} = {⟨1, 2, 3, 4⟩, ⟨1, 4, 5, 6⟩, ⟨1, 6, 7, 8⟩} := by
  decide

theorem quads_8_1 : quads 8 {(1, 4), (4, 7)} = {⟨1, 2, 3, 4⟩, ⟨1, 4, 7, 8⟩, ⟨4, 5, 6, 7⟩} := by
  decide

theorem quads_8_2 : quads 8 {(1, 4), (5, 8)} = {⟨1, 2, 3, 4⟩, ⟨1, 4, 5, 8⟩, ⟨5, 6, 7, 8⟩} := by
  decide

theorem quads_8_3 : quads 8 {(1, 6), (2, 5)} = {⟨1, 2, 5, 6⟩, ⟨1, 6, 7, 8⟩, ⟨2, 3, 4, 5⟩} := by
  decide

theorem quads_8_4 : quads 8 {(1, 6), (3, 6)} = {⟨1, 2, 3, 6⟩, ⟨1, 6, 7, 8⟩, ⟨3, 4, 5, 6⟩} := by
  decide

theorem quads_8_5 : quads 8 {(2, 5), (2, 7)} = {⟨1, 2, 7, 8⟩, ⟨2, 3, 4, 5⟩, ⟨2, 5, 6, 7⟩} := by
  decide

theorem quads_8_6 : quads 8 {(2, 5), (5, 8)} = {⟨1, 2, 5, 8⟩, ⟨2, 3, 4, 5⟩, ⟨5, 6, 7, 8⟩} := by
  decide

theorem quads_8_7 : quads 8 {(2, 7), (3, 6)} = {⟨1, 2, 7, 8⟩, ⟨2, 3, 6, 7⟩, ⟨3, 4, 5, 6⟩} := by
  decide

theorem quads_8_8 : quads 8 {(2, 7), (4, 7)} = {⟨1, 2, 7, 8⟩, ⟨2, 3, 4, 7⟩, ⟨4, 5, 6, 7⟩} := by
  decide

theorem quads_8_9 : quads 8 {(3, 6), (3, 8)} = {⟨1, 2, 3, 8⟩, ⟨3, 4, 5, 6⟩, ⟨3, 6, 7, 8⟩} := by
  decide

theorem quads_8_10 : quads 8 {(3, 8), (4, 7)} = {⟨1, 2, 3, 8⟩, ⟨3, 4, 7, 8⟩, ⟨4, 5, 6, 7⟩} := by
  decide

theorem quads_8_11 : quads 8 {(3, 8), (5, 8)} = {⟨1, 2, 3, 8⟩, ⟨3, 4, 5, 8⟩, ⟨5, 6, 7, 8⟩} := by
  decide

/-- PROVED. `card_quads` at N = 6 and 8: every quadrangulation has `(N − 2)/2` quads. -/
theorem card_quads_small : (∀ G ∈ quadrangulations 6, (quads 6 G).card = 2) ∧
    (∀ G ∈ quadrangulations 8, (quads 8 G).card = 3) := by
  rw [quadrangulations_6, quadrangulations_8]
  decide

/-- PROVED. The octagon's quads alternate in parity. -/
theorem alternating_eight : ∀ G ∈ quadrangulations 8, ∀ q ∈ quads 8 G, q.Alternating := by
  rw [quadrangulations_8]
  decide

/-- PROVED. Lemma A.2 at N = 8, for every admissible `T` (22 sets: `T` ranges over the subsets of one parity class). -/
theorem goodQ_eight : ∀ G ∈ quadrangulations 8, ∀ r ∈ range 2,
    ∀ T ∈ ((Icc 1 8).filter fun t => t % 2 = r).powerset, 2 ≤ T.card →
      ∃ q ∈ quads 8 G, GoodQ 8 T (1 - r) q := by
  rw [quadrangulations_8]
  simp only [forall_mem_insert, mem_singleton, forall_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [quads_8_0]; decide
  · rw [quads_8_1]; decide
  · rw [quads_8_2]; decide
  · rw [quads_8_3]; decide
  · rw [quads_8_4]; decide
  · rw [quads_8_5]; decide
  · rw [quads_8_6]; decide
  · rw [quads_8_7]; decide
  · rw [quads_8_8]; decide
  · rw [quads_8_9]; decide
  · rw [quads_8_10]; decide
  · rw [quads_8_11]; decide

/-- PROVED. **Theorem A at N = 8, end to end**, every admissible `T`. -/
theorem theoremA_eight {r : ℕ} (hr : r < 2) {T : Finset ℕ} (hT : Admissible 8 r T) (X : ℕ × ℕ → K)
    (hZ : OnZT 8 T X) : (∀ G ∈ quadrangulations 8, diagram 8 (1 - r) X G = 0) ∧ Qpi 8 (1 - r) X = 0 := by
  have hd : ∀ G ∈ quadrangulations 8, diagram 8 (1 - r) X G = 0 := by
    intro G hG
    have hTm : T ∈ ((Icc 1 8).filter fun t => t % 2 = r).powerset :=
      mem_powerset.2 fun t ht => mem_filter.2 ⟨hT.1 ht, hT.2.2 t ht⟩
    obtain ⟨q, hq, hgood⟩ := goodQ_eight G hG r (mem_range.2 hr) T hTm hT.2.1
    unfold diagram
    rw [prod_eq_zero hq (vnum_eq_zero_of_goodQ (by omega) (mem_filter.1 hq).1
      (alternating_eight G hG q hq) hgood hZ), zero_mul]
  exact ⟨hd, sum_eq_zero hd⟩

lemma vnum_eq_vnumX' {N : ℕ} (π : ℕ) (X : ℕ × ℕ → K) (a b c d : ℕ)
    (h : 1 ≤ a ∧ a < b ∧ b < c ∧ c < d ∧ d ≤ N) :
    vnum N π X ⟨a, b, c, d⟩ = vnumX N π X ⟨a, b, c, d⟩ := vnum_eq_vnumX π X (mem_quadIdx.2 h)

/-- PROVED. `Q_8^π` written out: twelve diagrams, numerators in the `(R)` form. -/
theorem Qpi_eight (π : ℕ) (X : ℕ × ℕ → K) : Qpi 8 π X =
  vnumX 8 π X ⟨1, 2, 3, 4⟩ * vnumX 8 π X ⟨1, 4, 5, 6⟩ * vnumX 8 π X ⟨1, 6, 7, 8⟩ * ((X (1, 4))⁻¹ * (X (1, 6))⁻¹) +
  vnumX 8 π X ⟨1, 2, 3, 4⟩ * vnumX 8 π X ⟨1, 4, 7, 8⟩ * vnumX 8 π X ⟨4, 5, 6, 7⟩ * ((X (1, 4))⁻¹ * (X (4, 7))⁻¹) +
  vnumX 8 π X ⟨1, 2, 3, 4⟩ * vnumX 8 π X ⟨1, 4, 5, 8⟩ * vnumX 8 π X ⟨5, 6, 7, 8⟩ * ((X (1, 4))⁻¹ * (X (5, 8))⁻¹) +
  vnumX 8 π X ⟨1, 2, 5, 6⟩ * vnumX 8 π X ⟨1, 6, 7, 8⟩ * vnumX 8 π X ⟨2, 3, 4, 5⟩ * ((X (1, 6))⁻¹ * (X (2, 5))⁻¹) +
  vnumX 8 π X ⟨1, 2, 3, 6⟩ * vnumX 8 π X ⟨1, 6, 7, 8⟩ * vnumX 8 π X ⟨3, 4, 5, 6⟩ * ((X (1, 6))⁻¹ * (X (3, 6))⁻¹) +
  vnumX 8 π X ⟨1, 2, 7, 8⟩ * vnumX 8 π X ⟨2, 3, 4, 5⟩ * vnumX 8 π X ⟨2, 5, 6, 7⟩ * ((X (2, 5))⁻¹ * (X (2, 7))⁻¹) +
  vnumX 8 π X ⟨1, 2, 5, 8⟩ * vnumX 8 π X ⟨2, 3, 4, 5⟩ * vnumX 8 π X ⟨5, 6, 7, 8⟩ * ((X (2, 5))⁻¹ * (X (5, 8))⁻¹) +
  vnumX 8 π X ⟨1, 2, 7, 8⟩ * vnumX 8 π X ⟨2, 3, 6, 7⟩ * vnumX 8 π X ⟨3, 4, 5, 6⟩ * ((X (2, 7))⁻¹ * (X (3, 6))⁻¹) +
  vnumX 8 π X ⟨1, 2, 7, 8⟩ * vnumX 8 π X ⟨2, 3, 4, 7⟩ * vnumX 8 π X ⟨4, 5, 6, 7⟩ * ((X (2, 7))⁻¹ * (X (4, 7))⁻¹) +
  vnumX 8 π X ⟨1, 2, 3, 8⟩ * vnumX 8 π X ⟨3, 4, 5, 6⟩ * vnumX 8 π X ⟨3, 6, 7, 8⟩ * ((X (3, 6))⁻¹ * (X (3, 8))⁻¹) +
  vnumX 8 π X ⟨1, 2, 3, 8⟩ * vnumX 8 π X ⟨3, 4, 7, 8⟩ * vnumX 8 π X ⟨4, 5, 6, 7⟩ * ((X (3, 8))⁻¹ * (X (4, 7))⁻¹) +
  vnumX 8 π X ⟨1, 2, 3, 8⟩ * vnumX 8 π X ⟨3, 4, 5, 8⟩ * vnumX 8 π X ⟨5, 6, 7, 8⟩ * ((X (3, 8))⁻¹ * (X (5, 8))⁻¹) := by
  rw [Qpi, quadrangulations_8]
  simp (config := {decide := true}) only [sum_insert, sum_singleton, mem_insert, mem_singleton, diagram,
    quads_8_0, quads_8_1, quads_8_2, quads_8_3, quads_8_4, quads_8_5, quads_8_6, quads_8_7, quads_8_8,
    quads_8_9, quads_8_10, quads_8_11, prod_insert, prod_singleton, vnum_eq_vnumX']
  ring

theorem diagonals_eight : diagonals 8 = {(1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 5), (3, 6), (3, 7), (3, 8), (4, 6), (4, 7), (4, 8), (5, 7), (5, 8), (6, 8)} := by
  decide

/-- The control point for `T = {1, 3, 6}` at N = 8 (`defs_mirror.py` D8b). -/
def octMixed : ℕ × ℕ → ℚ := fun d =>
  if d = (1, 3) then 2
  else if d = (1, 4) then 3
  else if d = (1, 5) then 3
  else if d = (1, 6) then 2
  else if d = (1, 7) then (-2)
  else if d = (2, 4) then (-1)
  else if d = (2, 5) then 1
  else if d = (2, 6) then (-2)
  else if d = (2, 7) then (-1)
  else if d = (2, 8) then (-3)
  else if d = (3, 5) then 2
  else if d = (3, 6) then (-1)
  else if d = (3, 7) then 1
  else if d = (3, 8) then (-1)
  else if d = (4, 6) then 2
  else if d = (4, 7) then 1
  else if d = (4, 8) then 2
  else if d = (5, 7) then 1
  else if d = (5, 8) then 2
  else if d = (6, 8) then 1 else 0

/-- PROVED. Control 3 (mixed parity): `T = {1, 3, 6}` at N = 8 has legs of both parities (pairwise non-adjacent). At a
point of `Z_T` with all diagonals non-zero, `Q_8^π = −7 ≠ 0` for both polarities; and some quadrangulation has no
good quad for either polarity. So the one-parity hypothesis of Theorem A cannot be dropped. -/
theorem negctl_mixed_parity :
    (∃ X : ℕ × ℕ → ℚ, OnZT 8 {1, 3, 6} X ∧ (∀ d ∈ diagonals 8, X d ≠ 0) ∧ Qpi 8 0 X ≠ 0 ∧ Qpi 8 1 X ≠ 0) ∧
    (∃ G ∈ quadrangulations 8, ∀ q ∈ quads 8 G, ¬ GoodQ 8 {1, 3, 6} 0 q ∧ ¬ GoodQ 8 {1, 3, 6} 1 q) := by
  refine ⟨⟨octMixed, onZT_of_list {(2, 4), (2, 5), (2, 7), (2, 8), (4, 2), (4, 7), (4, 8), (5, 2), (5, 7), (5, 8), (7, 2), (7, 4), (7, 5), (8, 2), (8, 4), (8, 5)} (by decide) (by
      intro p hp; simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [mesh, planar, vtx, diagonals_eight, octMixed]), ?_, ?_, ?_⟩, ?_⟩
  · intro d hd
    rw [diagonals_eight] at hd
    simp only [mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [octMixed]
  · rw [Qpi_eight]
    norm_num [vnumX, planar, vtx, diagonals_eight, octMixed]
  · rw [Qpi_eight]
    norm_num [vnumX, planar, vtx, diagonals_eight, octMixed]
  · refine ⟨{(1, 4), (4, 7)}, by rw [quadrangulations_8]; decide, ?_⟩
    rw [quads_8_1]
    decide

/-! ### Reviewer's controls (R12-P3a R1, `../../r12p3arev/RevControls.lean`, carried in verbatim)
1. `|T| = 1`: `S_T` is empty, `Z_T` is everything, `Q_6 ≠ 0` there (`2 ≤ T.card` is load-bearing).
2. `S_T` minus one tile at the maximal `T = {1,3,5}` (drop `c₄₆`): `Q_6 = −4 ≠ 0`.
3. Maximality among **all** diagonals (instead of odd ones) has no members at N = 6 (would make Theorem A vacuous). -/

theorem rev_negctl_singleton_T :
    (∀ a b : ℕ, ¬ InST {1} a b) ∧
    ∃ X : ℕ × ℕ → ℚ, OnZT 6 {1} X ∧ (∀ d ∈ diagonals 6, X d ≠ 0) ∧ Qpi 6 0 X ≠ 0 ∧ Qpi 6 1 X ≠ 0 := by
  have hS : ∀ a b : ℕ, ¬ InST {1} a b := by
    rintro a b ⟨_, _, ⟨t, ht, h1⟩, ⟨t', ht', h2⟩⟩
    rw [mem_singleton] at ht ht'
    subst ht ht'
    omega
  refine ⟨hS, hexPt 1 1 1 1 1 1 1 1 1, fun a _ b _ h => absurd h (hS a b),
    hexPt_ne (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num), ?_, ?_⟩
  · rw [Qpi_six]
    norm_num [vnumX, planar, vtx, diagonals_six, hexPt]
  · rw [Qpi_six]
    norm_num [vnumX, planar, vtx, diagonals_six, hexPt]

theorem rev_negctl_minus_tile_T135 :
    ∃ X : ℕ × ℕ → ℚ, (∀ a ∈ Icc 1 6, ∀ b ∈ Icc 1 6, InST {1, 3, 5} a b → (a, b) ≠ (4, 6) → (a, b) ≠ (6, 4) →
      mesh 6 X a b = 0) ∧ mesh 6 X 4 6 ≠ 0 ∧ (∀ d ∈ diagonals 6, X d ≠ 0) ∧ Qpi 6 (1 - 1) X ≠ 0 := by
  refine ⟨hexPt (-1) 1 2 (-1) (-2) (-1) (-1) (-2) 1, ?_, ?_, ?_, ?_⟩
  · have hL : ∀ a ∈ Icc 1 6, ∀ b ∈ Icc 1 6, InST {1, 3, 5} a b → (a, b) ≠ (4, 6) → (a, b) ≠ (6, 4) →
        (a, b) ∈ ({(2, 4), (2, 6), (4, 2), (6, 2)} : Finset (ℕ × ℕ)) := by decide
    intro a ha b hb h h1 h2
    have hp := hL a ha b hb h h1 h2
    simp only [mem_insert, mem_singleton, Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      norm_num [mesh, planar, vtx, diagonals_six, hexPt]
  · norm_num [mesh, planar, vtx, diagonals_six, hexPt]
  · exact hexPt_ne (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · rw [Qpi_six]
    norm_num [vnumX, planar, vtx, diagonals_six, hexPt]

theorem rev_negctl_maximal_among_all :
    ((oddDiagonals 6).powerset.filter fun G => (∀ p ∈ G, ∀ q ∈ G, ¬ Crosses p q) ∧
      ∀ d ∈ diagonals 6, d ∉ G → ∃ p ∈ G, Crosses p d) = ∅ := by
  decide

end Small

end R12P3

#print axioms R12P3.vnum_eq_vnumX
#print axioms R12P3.vnum_eq_zero_of_goodQ
#print axioms R12P3.diagram_eq_zero
#print axioms R12P3.Qpi_eq_zero
#print axioms R12P3.theoremA
#print axioms R12P3.card_quadrangulations_small
#print axioms R12P3.alternating_six
#print axioms R12P3.goodQ_six
#print axioms R12P3.theoremA_six
#print axioms R12P3.Qpi_six
#print axioms R12P3.ZT_inhabited_six
#print axioms R12P3.negctl_minus_tile
#print axioms R12P3.negctl_wrong_polarity
#print axioms R12P3.card_quads_small
#print axioms R12P3.alternating_eight
#print axioms R12P3.goodQ_eight
#print axioms R12P3.theoremA_eight
#print axioms R12P3.Qpi_eight
#print axioms R12P3.negctl_mixed_parity
#print axioms R12P3.ZT_inhabited
#print axioms R12P3.exists_goodQ
#print axioms R12P3.quads_alternating
#print axioms R12P3.rev_negctl_singleton_T
#print axioms R12P3.rev_negctl_minus_tile_T135
#print axioms R12P3.rev_negctl_maximal_among_all
#print axioms R12P3.card_quads
#print axioms R12P3.leg_side_unique
#print axioms R12P3.p3b_diag_plus_minus
#print axioms R12P3.p3b_diag_plus_minus_needs_pi_lt_two
#print axioms R12P3.diag_plus_minus
#print axioms R12P3.card_quadrangulations
