import GroupApproximation.GGT.OlshanskiiBisection
import GroupApproximation.GGT.DGOPolygonGeodesicChain
import GroupApproximation.GGT.CayleyGeodesicRealisation
import GroupApproximation.GGT.CayleyFourPointBridge

/-!
# The cut of a word into sides, and the bisection read in word language

`GGT/OlshanskiiBisection.lean` proves the balanced cut in a metric space: a
closed geodesic `n`-gon, presented as an `IsSideFamily`, has two sides whose
indices are quarter-separated and which carry points at distance
`6δ(k+1) + 1`.  DGO's §4.2 polygons are not in that vocabulary --- they are
closed words `w` with a monotone cut function `c`, and their sides are the
segments `[c s, c (s+1))` --- so this module is the passage between the two,
built once for both consumers of the layer.

## What is named here

* `IsPolygonCut n w c`, the three clauses that `IsQuasiGeodesicPolygon` carries
  existentially.  Naming them is the whole point: a lane that has to speak about
  an individual side cannot reach inside an `∃ c`.
* `cutVertex v w c s`, the corner where the `s`-th side begins, with the two
  facts that make the polygon closed --- `cutVertex … 0 = v` and, when the word
  spells the identity, `cutVertex … n = v`.
* `exists_balanced_cut_vertices`, the metric statement with the cut points
  already pulled back to corners.
* `exists_balanced_cut_word`, the composite, stated with no metric space in
  sight: two quarter-separated side indices whose corners are close **in the
  word metric of `X ⊔ ℋ`**.

## Why the corners, and what it costs

`exists_balanced_cut` returns points *on* two sides, not corners, and DGO's
proof needs vertices --- they say "without loss of generality `u` and `v` are
vertices of `Γ`".  The passage is cheaper than that remark suggests and needs no
Morse lemma: a side is a geodesic segment parametrised on
`[0, dist (vs i) (vs (i+1))]`, so *every* point of it is within the side's own
length of the side's initial corner.  The pull-back therefore costs one side
length at each end, and nothing else.

That is why the statement carries `e`, a bound on the number of letters in a
side.  At the instantiation both consumers actually use --- every edge a side,
`n ≈ 3ℓ(p)` --- one has `e = 1` and the pull-back costs `2` in total.  A
polygon with long sides would pay its longest side twice, which is the honest
price of not knowing where inside a side the cut point fell.

## Which polygon the metric argument sees

The sides handed to `exists_balanced_cut` are geodesics of the model **between
the corners**, not the images of the word's own sides --- which is what makes
the passage cheap, since a `(μ,b)`-quasi-geodesic side has no reason to be a
geodesic segment of anything.  This is legitimate because the conclusion
mentions only corners and side indices, and both are shared by the two
polygons: the geodesic polygon on the corners has the same corner sequence and
the same indexing as the word polygon, so a cut of one is a cut of the other.
It is also slightly stronger than DGO's own form, where the cut points may fall
inside a side and the side then has to be split; here the cut runs corner to
corner and no side is ever cut.

## The model, and the two constants it adds

The metric space is `CayleyGeodesicModel.PointQuot D.alphabet`, the quotient
realisation: `Point` itself is **not** geodesic --- the two ends of the loop
that `Letters` adjoins at every vertex are distinct points at distance zero ---
so `isGeodesicRealisationQuot` is the model that works, and it is the same one
the Morse discharge uses.  Two constants enter with it and neither is
avoidable: the realisation is `δ + 6`-hyperbolic rather than `δ`-hyperbolic
(the four-point condition pulls back along the retraction at cost `3 · 2`), and
the vertex inclusion has additive distortion `1`, spent once going up and once
coming back down.
-/

namespace GroupApproximation
namespace GGT
namespace DGOPolygonCut

open GroupApproximation.HullGeometry
open GroupApproximation.Olshanskii
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w z

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## The cut -/

/-- **A cut of a word into `n` sides.**  `c s` is the index of the letter at
which the `s`-th side begins, so that side is the segment `[c s, c (s+1))`.

These are exactly the three clauses `OsinComponents.IsQuasiGeodesicPolygon`
carries existentially, with the quasi-geodesicity clause left out: a cut is
combinatorial data about the word, and how straight its sides are is a separate
question asked of a separate hypothesis. -/
structure IsPolygonCut (n : ℕ) (w : List (RelLetter G Λ)) (c : ℕ → ℕ) : Prop where
  /-- The first side starts at the beginning of the word. -/
  start : c 0 = 0
  /-- The last side ends at the end of the word. -/
  finish : c n = w.length
  /-- The cut points advance. -/
  mono : ∀ s : ℕ, c s ≤ c (s + 1)

namespace IsPolygonCut

variable {n : ℕ} {w : List (RelLetter G Λ)} {c : ℕ → ℕ}

omit [Group G] in
/-- **The cut function is monotone**, not merely step-monotone. -/
theorem mono_le (h : IsPolygonCut n w c) {s t : ℕ} (hst : s ≤ t) : c s ≤ c t := by
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, t = s + d := ⟨t - s, by omega⟩
  clear hst
  induction d with
  | zero => exact le_refl _
  | succ d ih =>
      have hstep : c (s + d) ≤ c (s + d + 1) := h.mono (s + d)
      have harg : s + (d + 1) = s + d + 1 := by omega
      rw [harg]
      exact le_trans ih hstep

omit [Group G] in
/-- **No cut point runs past the end of the word.** -/
theorem le_length (h : IsPolygonCut n w c) {s : ℕ} (hs : s ≤ n) : c s ≤ w.length := by
  have hmono := h.mono_le hs
  rw [h.finish] at hmono
  exact hmono

end IsPolygonCut

/-! ## The corners -/

/-- **The corner of the polygon at which the `s`-th side begins.** -/
def cutVertex (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ) (s : ℕ) : G :=
  vertex v w (c s)

@[simp] theorem cutVertex_apply (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ)
    (s : ℕ) : cutVertex v w c s = vertex v w (c s) := rfl

/-- **The polygon starts at its basepoint.** -/
theorem cutVertex_zero {n : ℕ} {w : List (RelLetter G Λ)} {c : ℕ → ℕ}
    (h : IsPolygonCut n w c) (v : G) : cutVertex v w c 0 = v := by
  rw [cutVertex_apply, h.start, vertex_zero]

/-- **The polygon closes up.**  This is the one place the hypothesis that `w`
spells the identity is spent. -/
theorem cutVertex_last {n : ℕ} {w : List (RelLetter G Λ)} {c : ℕ → ℕ}
    (h : IsPolygonCut n w c) (v : G) (hw : RelLetter.listVal w = 1) :
    cutVertex v w c n = v := by
  rw [cutVertex_apply, h.finish, vertex_eq_mul_listVal_take, List.take_length, hw,
    mul_one]

/-- **A side is no longer, in the word metric, than the number of letters it
carries.** -/
theorem wordDist_cutVertex_le (D : RelGenSet G Λ) {n : ℕ} {w : List (RelLetter G Λ)}
    {c : ℕ → ℕ} (h : IsPolygonCut n w c) (hlet : ∀ a ∈ w, D.IsLetter a) (v : G)
    {s : ℕ} (hs : s < n) :
    wordDist D.alphabet.carrier (cutVertex v w c s) (cutVertex v w c (s + 1))
      ≤ c (s + 1) - c s := by
  refine wordDist_vertex_le' D hlet v (h.mono s) ?_
  exact h.le_length (by omega)

/-! ## Side families in a geodesic space -/

section Metric

variable {X : Type z} [PseudoMetricSpace X]

/-- **Every vertex sequence in a geodesic space carries a side family.**  The
sides are data in `IsSideFamily`, and this is where the data comes from. -/
theorem exists_isSideFamily (hgeo : IsGeodesicSpace X) (vs : ℕ → X) (n : ℕ) :
    ∃ sides : ℕ → ℝ → X, IsSideFamily vs sides n := by
  choose f hf hf0 hf1 using fun s : ℕ => hgeo (vs s) (vs (s + 1))
  exact ⟨f, fun i _ => ⟨hf i, hf0 i, hf1 i⟩⟩

/-- **A point of a side is within the side's length of the side's initial
corner.**  Immediately from the parametrisation: the side is an isometry of
`[0, ℓ]`, so the parameter *is* the distance from the corner. -/
theorem dist_le_of_mem_side {vs : ℕ → X} {sides : ℕ → ℝ → X} {n : ℕ}
    (h : IsSideFamily vs sides n) {i : ℕ} (hi : i < n) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) (dist (vs i) (vs (i + 1)))) :
    dist (sides i s) (vs i) ≤ dist (vs i) (vs (i + 1)) := by
  obtain ⟨hseg, h0, _⟩ := h i hi
  have hz : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (dist (vs i) (vs (i + 1))) :=
    ⟨le_refl 0, dist_nonneg⟩
  have hd := hseg.dist_eq hs hz
  rw [h0] at hd
  rw [hd]
  have habs : |s - 0| = s := by
    rw [sub_zero, abs_of_nonneg hs.1]
  rw [habs]
  exact hs.2

/-- **The balanced cut, read at the corners.**

`exists_balanced_cut` places its two points on the sides; this places them at
the corners, at the cost of one side length at each end.  Nothing about the
polygon is used beyond a uniform bound `E` on the length of a side, so the
statement stays sharp for polygons whose sides are single edges. -/
theorem exists_balanced_cut_vertices {δ : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X) {n k : ℕ} (hn : 8 ≤ n)
    (hk : n ≤ 2 ^ k) (vs : ℕ → X) (hclose : vs n = vs 0) {E : ℝ}
    (hlen : ∀ i : ℕ, i < n → dist (vs i) (vs (i + 1)) ≤ E) :
    ∃ a b : ℕ, a < b ∧ b < n ∧ n ≤ 4 * (b - a) ∧ 4 * (b - a) ≤ 3 * n ∧
      dist (vs a) (vs b) ≤ 6 * δ * ((k : ℝ) + 1) + 1 + 2 * E := by
  obtain ⟨sides, hsf⟩ := exists_isSideFamily hgeo vs n
  obtain ⟨a, b, hab, hbn, hq1, hq2, s, hs, s', hs', hdist⟩ :=
    exists_balanced_cut hδ hδ0 hgeo hn hk vs sides hsf hclose
  refine ⟨a, b, hab, hbn, hq1, hq2, ?_⟩
  have h1 : dist (vs a) (sides a s) ≤ E := by
    rw [dist_comm]
    exact le_trans (dist_le_of_mem_side hsf (by omega) hs) (hlen a (by omega))
  have h2 : dist (sides b s') (vs b) ≤ E :=
    le_trans (dist_le_of_mem_side hsf hbn hs') (hlen b hbn)
  have h3 := dist_triangle4 (vs a) (sides a s) (sides b s') (vs b)
  linarith

end Metric

/-! ## The vertex inclusion into the geodesic model -/

/-- **The vertex inclusion of `G` into the geodesic model of `Γ(G, X ⊔ ℋ)`.** -/
noncomputable def iotaG (A : Alphabet G) (g : G) : CayleyGeodesicModel.PointQuot A :=
  CayleyGeodesicModel.iotaQuot A (Cayley.of A g)

/-- **Going up costs at most one.** -/
theorem dist_iotaG_le (A : Alphabet G) (a b : G) :
    dist (iotaG A a) (iotaG A b) ≤ ((wordDist A.carrier a b : ℕ) : ℝ) + 1 := by
  have h := CayleyGeodesicModel.hasAdditiveDistortion_iotaQuot A
    (Cayley.of A a) (Cayley.of A b)
  have hd : dist (Cayley.of A a) (Cayley.of A b)
      = ((wordDist A.carrier a b : ℕ) : ℝ) := Cayley.dist_eq _ _
  rw [hd] at h
  have h2 := (abs_le.mp h).2
  show dist (CayleyGeodesicModel.iotaQuot A (Cayley.of A a))
      (CayleyGeodesicModel.iotaQuot A (Cayley.of A b)) ≤ _
  linarith

/-- **Coming back down costs at most one.** -/
theorem le_dist_iotaG (A : Alphabet G) (a b : G) :
    ((wordDist A.carrier a b : ℕ) : ℝ) - 1 ≤ dist (iotaG A a) (iotaG A b) := by
  have h := CayleyGeodesicModel.hasAdditiveDistortion_iotaQuot A
    (Cayley.of A a) (Cayley.of A b)
  have hd : dist (Cayley.of A a) (Cayley.of A b)
      = ((wordDist A.carrier a b : ℕ) : ℝ) := Cayley.dist_eq _ _
  rw [hd] at h
  have h1 := (abs_le.mp h).1
  show ((wordDist A.carrier a b : ℕ) : ℝ) - 1
    ≤ dist (CayleyGeodesicModel.iotaQuot A (Cayley.of A a))
      (CayleyGeodesicModel.iotaQuot A (Cayley.of A b))
  linarith

/-! ## The bisection in word language -/

/-- **The balanced bisection of a closed word.**

A closed word cut into `n ≥ 8` sides, each carrying at most `e` letters, in a
`δ`-hyperbolic alphabet, has two side indices `a < b` that are
quarter-separated --- `n ≤ 4(b − a) ≤ 3n`, so cutting there splits the polygon
into two pieces whose side counts both lie strictly between `n/4` and
`3n/4 + 2` --- whose corners are within
`6(δ + 6)(k + 1) + 2e + 4` of each other **in the word metric**, where
`n ≤ 2 ^ k`.

Every constant beyond the bisection's own `6δ(k+1) + 1` is accounted for: `+ 6`
in the hyperbolicity constant is the realisation, `2e` is the two side lengths
spent pulling the cut points back to corners, and `4` is `1` from the
bisection, `2` from the two distortions of the vertex inclusion, and `1` from
the two `+ 1`s in the side-length bound.  At `e = 1`, the instantiation both
consumers use, this reads `6(δ+6)(k+1) + 6`. -/
theorem exists_balanced_cut_word (D : RelGenSet G Λ) {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) {n k e : ℕ}
    (hn : 8 ≤ n) (hk : n ≤ 2 ^ k) (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ)
    (hcut : IsPolygonCut n w c) (hclosed : RelLetter.listVal w = 1)
    (hlet : ∀ a ∈ w, D.IsLetter a)
    (hsides : ∀ s : ℕ, s < n → c (s + 1) - c s ≤ e) :
    ∃ a b : ℕ, a < b ∧ b < n ∧ n ≤ 4 * (b - a) ∧ 4 * (b - a) ≤ 3 * n ∧
      wordDist D.alphabet.carrier (cutVertex v w c a) (cutVertex v w c b)
        ≤ 6 * (δ + 6) * (k + 1) + 2 * e + 4 := by
  have hgeo : IsGeodesicSpace (CayleyGeodesicModel.PointQuot D.alphabet) :=
    CayleyGeodesicModel.isGeodesicRealisationQuot D.alphabet
  have hhypC : IsHyperbolicSpace ((δ : ℝ)) (Cayley D.alphabet) :=
    isHyperbolicSpace_cayley_of_fourPoint D.alphabet hδ
  have hhyp : IsHyperbolicSpace ((δ : ℝ) + 6)
      (CayleyGeodesicModel.PointQuot D.alphabet) :=
    CayleyGeodesicModel.isHyperbolicSpace_pointQuot
      (CayleyGeodesicModel.isHyperbolicSpace_point D.alphabet hhypC)
  have hδ0 : (0 : ℝ) ≤ (δ : ℝ) + 6 := by positivity
  have hclose : (fun s => iotaG D.alphabet (cutVertex v w c s)) n
      = (fun s => iotaG D.alphabet (cutVertex v w c s)) 0 := by
    show iotaG D.alphabet (cutVertex v w c n) = iotaG D.alphabet (cutVertex v w c 0)
    rw [cutVertex_last hcut v hclosed, cutVertex_zero hcut v]
  have hlen : ∀ i : ℕ, i < n →
      dist ((fun s => iotaG D.alphabet (cutVertex v w c s)) i)
        ((fun s => iotaG D.alphabet (cutVertex v w c s)) (i + 1)) ≤ (e : ℝ) + 1 := by
    intro i hi
    show dist (iotaG D.alphabet (cutVertex v w c i))
      (iotaG D.alphabet (cutVertex v w c (i + 1))) ≤ (e : ℝ) + 1
    have hup := dist_iotaG_le D.alphabet (cutVertex v w c i) (cutVertex v w c (i + 1))
    have hword : wordDist D.alphabet.carrier (cutVertex v w c i)
        (cutVertex v w c (i + 1)) ≤ e :=
      le_trans (wordDist_cutVertex_le D hcut hlet v hi) (hsides i hi)
    have hcast : ((wordDist D.alphabet.carrier (cutVertex v w c i)
        (cutVertex v w c (i + 1)) : ℕ) : ℝ) ≤ (e : ℝ) := by exact_mod_cast hword
    linarith
  obtain ⟨a, b, hab, hbn, hq1, hq2, hdist⟩ :=
    exists_balanced_cut_vertices hhyp hδ0 hgeo hn hk
      (fun s => iotaG D.alphabet (cutVertex v w c s)) hclose hlen
  refine ⟨a, b, hab, hbn, hq1, hq2, ?_⟩
  have hd : dist (iotaG D.alphabet (cutVertex v w c a))
      (iotaG D.alphabet (cutVertex v w c b))
      ≤ 6 * ((δ : ℝ) + 6) * ((k : ℝ) + 1) + 1 + 2 * ((e : ℝ) + 1) := hdist
  have hlow := le_dist_iotaG D.alphabet (cutVertex v w c a) (cutVertex v w c b)
  have hfinal : ((wordDist D.alphabet.carrier (cutVertex v w c a)
      (cutVertex v w c b) : ℕ) : ℝ)
      ≤ 6 * ((δ : ℝ) + 6) * ((k : ℝ) + 1) + 2 * (e : ℝ) + 4 := by linarith
  have hcast : ((6 * (δ + 6) * (k + 1) + 2 * e + 4 : ℕ) : ℝ)
      = 6 * ((δ : ℝ) + 6) * ((k : ℝ) + 1) + 2 * (e : ℝ) + 4 := by
    push_cast
    ring
  rw [← hcast] at hfinal
  exact_mod_cast hfinal

/-! ## The polygon with its cut named -/

/-- **A `(1,b)`-quasi-geodesic `n`-gon with its cut named.**  The same content as
`OsinComponents.IsQuasiGeodesicPolygon`, with the cut function pulled out of the
existential so that a consumer can speak about the `s`-th side. -/
structure IsCutPolygon (D : RelGenSet G Λ) (b : ℝ) (n : ℕ) (v : G)
    (w : List (RelLetter G Λ)) (c : ℕ → ℕ) : Prop where
  /-- Every letter is admissible. -/
  letters : ∀ a ∈ w, D.IsLetter a
  /-- The word spells the identity. -/
  closed : RelLetter.listVal w = 1
  /-- The cut. -/
  cut : IsPolygonCut n w c
  /-- Every side is `(1,b)`-quasi-geodesic. -/
  quasi : ∀ s : ℕ, s < n → ∀ i j : ℕ, c s ≤ i → i ≤ j → j ≤ c (s + 1) →
    ((j - i : ℕ) : ℝ) - b
      ≤ ((wordDist D.alphabet.carrier (vertex v w i) (vertex v w j) : ℕ) : ℝ)

/-- **A named cut is a cut.** -/
theorem IsCutPolygon.toPolygon {D : RelGenSet G Λ} {b : ℝ} {n : ℕ} {v : G}
    {w : List (RelLetter G Λ)} {c : ℕ → ℕ} (h : IsCutPolygon D b n v w c) :
    IsQuasiGeodesicPolygon D 1 b n v w := by
  refine ⟨h.letters, h.closed, c, h.cut.start, h.cut.finish, h.cut.mono, ?_⟩
  intro s hs i j hi hij hj
  have hq := h.quasi s hs i j hi hij hj
  have hone : ((j - i : ℕ) : ℝ) / 1 = ((j - i : ℕ) : ℝ) := by ring
  rw [hone]
  exact hq

/-- **Every polygon has a named cut.**  The service this layer owes: the cut is
carried existentially by `IsQuasiGeodesicPolygon`, and a lane that must index
sides cannot reach inside the existential. -/
theorem exists_cut_of_isQuasiGeodesicPolygon {D : RelGenSet G Λ} {b : ℝ} {n : ℕ}
    {v : G} {w : List (RelLetter G Λ)} (h : IsQuasiGeodesicPolygon D 1 b n v w) :
    ∃ c : ℕ → ℕ, IsCutPolygon D b n v w c := by
  obtain ⟨hlet, hclosed, c, h0, hn, hmono, hq⟩ := h
  refine ⟨c, hlet, hclosed, ⟨h0, hn, hmono⟩, ?_⟩
  intro s hs i j hi hij hj
  have hqs := hq s hs i j hi hij hj
  have hone : ((j - i : ℕ) : ℝ) / 1 = ((j - i : ℕ) : ℝ) := by ring
  rw [hone] at hqs
  exact hqs

/-! ## The sum bound

The Prop the whole linear campaign is stated at, in the form settled with both
consumers: a **witness radius function** rather than a relative norm.  The two
are equivalent in use --- `∑ ℓ̂(s) ≤ K` versus radii summing to `K` --- but the
witness form needs no new definition and, decisively, **cannot be satisfied when
some `d̂` is infinite**, since `span ∈ relBall lam (r s)` is itself a finiteness
witness.  A `relNorm` defined as an `sInf` would instead return `0` on an
unreachable component, so it would be sound exactly where 4.14 uses it and junk
everywhere else: it would pass its own tests and mislead the next consumer.

The distinguished sides are single edges.  This is DGO's own reduction, made
at the top of both Lemma 4.16 and Proposition 4.14 --- "we may assume that every
`p_i ∈ I` consists of a single edge", since replacing a component by one edge
labelled by its span changes no `ℓ̂` --- and it is what the tree's own assembly
already assumes, `DGOCycleAssembly.cycle_of_connector` being stated at
`IsComp lam w 0 1`.  It is met at both consumers, who take every edge a side,
and it is preserved by the decomposition of Proposition 4.14: of the five types
of side of the cycles `c_j`, the distinguished ones are components from `I`, the
connecting edges `f_j` and `e_j`, and the components `y_j` of the chord, and the
last are single letters because the chord is geodesic.

Note which sides carry the quasi-geodesic clause.  DGO's Definition 4.13 exempts
the distinguished sides --- the components in `I` are allowed to be trivial ---
so the clause is imposed only off `I`.  Imposing it everywhere would be a
different and strictly stronger hypothesis, and would not be met at the
polygons the consumers build. -/

/-- **The sum bound at side count `n`.** -/
def SumBound (D : RelGenSet G Λ) (b : ℝ) (n K : ℕ) : Prop :=
  ∀ (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ) (I : Finset ℕ) (lam : ℕ → Λ),
    (∀ a ∈ w, D.IsLetter a) → RelLetter.listVal w = 1 → IsPolygonCut n w c →
    (∀ s ∈ I, s < n) →
    (∀ s ∈ I, c (s + 1) = c s + 1) →
    (∀ s ∈ I, IsComp (lam s) w (c s) (c (s + 1))) →
    (∀ s ∈ I, IsIsolated D.fam (lam s) v w (c s)) →
    (∀ s : ℕ, s < n → s ∉ I → ∀ p q : ℕ, c s ≤ p → p ≤ q → q ≤ c (s + 1) →
      ((q - p : ℕ) : ℝ) - b
        ≤ ((wordDist D.alphabet.carrier (vertex v w p) (vertex v w q) : ℕ) : ℝ)) →
    ∃ r : ℕ → ℕ,
      (∀ s ∈ I,
        (vertex v w (c s))⁻¹ * vertex v w (c (s + 1)) ∈ D.relBall (lam s) (r s)) ∧
      ∑ s ∈ I, r s ≤ K

/-- **A larger constant is a weaker bound.**  What makes `Nat.find` on the set of
admissible constants legitimate downstream. -/
theorem SumBound.mono {D : RelGenSet G Λ} {b : ℝ} {n K K' : ℕ}
    (h : SumBound D b n K) (hK : K ≤ K') : SumBound D b n K' := by
  intro v w c I lam hlet hclosed hcut hI hedge hcomp hiso hquasi
  obtain ⟨r, hr, hsum⟩ := h v w c I lam hlet hclosed hcut hI hedge hcomp hiso hquasi
  exact ⟨r, hr, le_trans hsum hK⟩

/-- **The bound has teeth: every distinguished component is `K`-close.**  The
sum bounds each summand, and relative balls grow with the radius. -/
theorem mem_relBall_of_sumBound {D : RelGenSet G Λ} {b : ℝ} {n K : ℕ}
    (h : SumBound D b n K) (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ)
    (I : Finset ℕ) (lam : ℕ → Λ) (hlet : ∀ a ∈ w, D.IsLetter a)
    (hclosed : RelLetter.listVal w = 1) (hcut : IsPolygonCut n w c)
    (hI : ∀ s ∈ I, s < n) (hedge : ∀ s ∈ I, c (s + 1) = c s + 1)
    (hcomp : ∀ s ∈ I, IsComp (lam s) w (c s) (c (s + 1)))
    (hiso : ∀ s ∈ I, IsIsolated D.fam (lam s) v w (c s))
    (hquasi : ∀ s : ℕ, s < n → s ∉ I →
      ∀ p q : ℕ, c s ≤ p → p ≤ q → q ≤ c (s + 1) →
        ((q - p : ℕ) : ℝ) - b
          ≤ ((wordDist D.alphabet.carrier (vertex v w p) (vertex v w q) : ℕ) : ℝ))
    {s : ℕ} (hs : s ∈ I) :
    (vertex v w (c s))⁻¹ * vertex v w (c (s + 1)) ∈ D.relBall (lam s) K := by
  obtain ⟨r, hr, hsum⟩ := h v w c I lam hlet hclosed hcut hI hedge hcomp hiso hquasi
  have hle : r s ≤ K :=
    le_trans (Finset.single_le_sum (fun i _ => Nat.zero_le (r i)) hs) hsum
  exact relBall_mono_radius D (lam s) hle (hr s hs)

/-- **The counting step, once and for all.**

Every consumption site of the sum bound divides it by a per-component lower
bound: the distinguished components are *deep*, meaning no one of them lies in
the ball of radius `M`, and the conclusion is a bound on how many of them there
can be.  Stating it here means no consumer has to redo the division. -/
theorem card_le_of_sumBound {D : RelGenSet G Λ} {b : ℝ} {n K M : ℕ}
    (h : SumBound D b n K) (v : G) (w : List (RelLetter G Λ)) (c : ℕ → ℕ)
    (I : Finset ℕ) (lam : ℕ → Λ) (hlet : ∀ a ∈ w, D.IsLetter a)
    (hclosed : RelLetter.listVal w = 1) (hcut : IsPolygonCut n w c)
    (hI : ∀ s ∈ I, s < n) (hedge : ∀ s ∈ I, c (s + 1) = c s + 1)
    (hcomp : ∀ s ∈ I, IsComp (lam s) w (c s) (c (s + 1)))
    (hiso : ∀ s ∈ I, IsIsolated D.fam (lam s) v w (c s))
    (hquasi : ∀ s : ℕ, s < n → s ∉ I →
      ∀ p q : ℕ, c s ≤ p → p ≤ q → q ≤ c (s + 1) →
        ((q - p : ℕ) : ℝ) - b
          ≤ ((wordDist D.alphabet.carrier (vertex v w p) (vertex v w q) : ℕ) : ℝ))
    (hdeep : ∀ s ∈ I,
      (vertex v w (c s))⁻¹ * vertex v w (c (s + 1)) ∉ D.relBall (lam s) M) :
    I.card * (M + 1) ≤ K := by
  obtain ⟨r, hr, hsum⟩ := h v w c I lam hlet hclosed hcut hI hedge hcomp hiso hquasi
  have hlow : ∀ s ∈ I, M + 1 ≤ r s := by
    intro s hs
    by_contra hcon
    have hle : r s ≤ M := by omega
    exact hdeep s hs (relBall_mono_radius D (lam s) hle (hr s hs))
  have hconst : ∑ _s ∈ I, (M + 1) = I.card * (M + 1) :=
    Finset.sum_const_nat (fun _ _ => rfl)
  have hstep : ∑ _s ∈ I, (M + 1) ≤ ∑ s ∈ I, r s := Finset.sum_le_sum hlow
  rw [hconst] at hstep
  exact le_trans hstep hsum

end DGOPolygonCut
end GGT
end GroupApproximation
