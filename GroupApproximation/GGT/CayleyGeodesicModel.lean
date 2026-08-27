import GroupApproximation.GGT.HyperbolicAdditiveTransfer
import GroupApproximation.Manuscript.NonMF.HullFillAxisDichotomy

/-!
# The metric realisation of `Γ(G,A)`

`Manuscript.NonMF.HullFillAxisDichotomy.not_isGeodesicSpace_cayley` shows that
`Cayley A` — the vertex set of `Γ(G,A)` with the word metric — is not a geodesic
space: its distances are natural numbers, and a geodesic segment of length one
would have to realise the distance `1/2`.  Every geodesic lemma of
`Sofic.HullSuitabilityGeometry` is therefore unavailable at `Γ(G,A)` until the
graph itself is built.  This module builds it.

## The space

A point is a triple `(base, letter, param)` with `letter ∈ A ∪ {1}` and
`param ∈ [0,1]`: the point `param` of the way along the edge from `base` to
`base * letter`.  Adjoining `1` to the alphabet makes every vertex a point of
the realisation — the vertex `g` is `(g, 1, 0)` — and keeps the letter set
nonempty when the alphabet is not.

Edges are **not** identified: `(g, a, t)` and `(g * a, a⁻¹, 1 - t)` are two
points at distance `2t` from each other, so each geometric edge appears twice
and the two copies meet at their endpoints.  That is deliberate — quotienting
would cost a setoid and every proof below would be about equivalence classes —
and it is harmless: a bigon of length two changes no quasi-isometry class, and
the hyperbolicity constant is imported from `Γ(G,A)` anyway.

## The distance

`viaVertex p q` is the least of the four ways of leaving `p` by one of its two
endpoints, crossing `Γ(G,A)` in the word metric, and entering `q` by one of its
two endpoints.  `pointDist p q` is `viaVertex p q`, except that two points of
the *same* edge may also be joined along it, at cost `|t - t'|`.

The `letter ∈ A ∪ {1}` constraint is what makes this a pseudometric: it forces
`d(base, tip) ≤ 1`, so traversing an edge is never a shortcut.  Without it the
triangle inequality fails outright, since the edge from `g` to `g * a` would
have length one however far apart `g` and `g * a` are in the word metric.

## What is proved, and the one residual

Proved: `pointDist` is a pseudometric (`instPseudoMetricSpacePoint`); the
translation action is by isometries (`isIsometricAction_point`); the vertex
inclusion is equivariant, changes no distance, and has `1`-dense image
(`isEquivariant_iota`, `hasAdditiveDistortion_iota`, `hasDenseImage_iota`); and
the realisation is hyperbolic whenever `Γ(G,A)` is (`isHyperbolicSpace_point`),
by pulling the four-point condition back along the base-vertex retraction, which
has additive distortion `2`.

Also proved, and this is the geodesicity the consumers need:
`exists_vertexGeodesic` — **between vertices the realisation is geodesic**, by
induction on the word distance.  One step of a minimal word gives a unit edge
(`exists_step`, `isGeodesicSegment_edgePath`), the rest is the inductive
geodesic, and `isGeodesicSegment_glue` joins them, its hypothesis being two
triangle inequalities — one through the intermediate vertex for the upper
bound, one through the target for the lower.  `exists_geodesic_vertex` states
it in the metric of the realisation.  That is the case
`exists_long_fellow_geodesics_of_not_independent` uses: its basepoint is a
vertex and its endpoints are orbit points of it, which are vertices too.

Not proved, and left as `IsGeodesicRealisation`: geodesicity between *arbitrary*
points, which `IsGeodesicSpace` asks for.  What is missing is only the two
partial edges at the ends, glued to a vertex geodesic by
`isGeodesicSegment_glue`.  `model` takes it as a hypothesis, so everything else
here is available without it.

## Status

**Not compiled.**  Written while builds were frozen, and not in the root import
list for that reason.
-/

namespace GroupApproximation
namespace GGT
namespace CayleyGeodesicModel

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.AxisDichotomyRoute
open scoped Classical

universe u

variable {G : Type u} [Group G]

/-! ## Points -/

/-- The letters of the realisation: the alphabet with the identity adjoined, so
that every vertex is a point and the letter set is never empty. -/
def Letters (A : Alphabet G) : Set G := insert 1 A.carrier

/-- A point of the metric realisation of `Γ(G,A)`: `param` of the way along the
edge from `base` to `base * letter`. -/
structure Point (A : Alphabet G) where
  /-- The vertex the edge starts at. -/
  base : G
  /-- The letter labelling the edge. -/
  letter : G
  /-- The letter is one of the alphabet, or the identity. -/
  letter_mem : letter ∈ Letters A
  /-- The position along the edge. -/
  param : ℝ
  /-- The position is at least `0`. -/
  param_nonneg : 0 ≤ param
  /-- The position is at most `1`. -/
  param_le_one : param ≤ 1

namespace Point

variable {A : Alphabet G}

/-- The vertex the edge ends at. -/
def tip (p : Point A) : G := p.base * p.letter

theorem wordDist_base_tip (p : Point A) :
    wordDist A.carrier p.base p.tip = wordNorm A.carrier p.letter := by
  show wordNorm A.carrier (p.base⁻¹ * (p.base * p.letter))
    = wordNorm A.carrier p.letter
  rw [← mul_assoc, inv_mul_cancel, one_mul]

/-- **An edge has length at most one in the word metric.**  This is what the
`letter ∈ A ∪ {1}` constraint buys, and it is used in every case of the
triangle inequality that crosses an edge. -/
theorem wordDist_base_tip_le_one (p : Point A) :
    (wordDist A.carrier p.base p.tip : ℝ) ≤ 1 := by
  have h : wordNorm A.carrier p.letter ≤ 1 := by
    rcases Set.mem_insert_iff.mp p.letter_mem with h1 | hmem
    · rw [h1, wordNorm_one]
      norm_num
    · exact wordNorm_le_one_of_mem hmem
  rw [wordDist_base_tip]
  exact_mod_cast h

/-! ## The distance to a vertex -/

/-- The distance from `p` to the vertex `v`: leave `p` by whichever endpoint is
better, then cross in the word metric. -/
noncomputable def toVertex (p : Point A) (v : G) : ℝ :=
  min (p.param + (wordDist A.carrier p.base v : ℝ))
    (1 - p.param + (wordDist A.carrier p.tip v : ℝ))

/-- The two ways of leaving `p`, as a disjunction, so that no proof below has to
unfold the definition. -/
theorem toVertex_cases (p : Point A) (v : G) :
    p.toVertex v = p.param + (wordDist A.carrier p.base v : ℝ) ∨
      p.toVertex v = 1 - p.param + (wordDist A.carrier p.tip v : ℝ) := by
  rcases min_cases (p.param + (wordDist A.carrier p.base v : ℝ))
      (1 - p.param + (wordDist A.carrier p.tip v : ℝ)) with ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

theorem toVertex_le_base_add (p : Point A) (v : G) :
    p.toVertex v ≤ p.param + (wordDist A.carrier p.base v : ℝ) :=
  min_le_left _ _

theorem toVertex_le_tip_add (p : Point A) (v : G) :
    p.toVertex v ≤ 1 - p.param + (wordDist A.carrier p.tip v : ℝ) :=
  min_le_right _ _

theorem le_toVertex {c : ℝ} {p : Point A} {v : G}
    (h1 : c ≤ p.param + (wordDist A.carrier p.base v : ℝ))
    (h2 : c ≤ 1 - p.param + (wordDist A.carrier p.tip v : ℝ)) :
    c ≤ p.toVertex v :=
  le_min h1 h2

theorem toVertex_nonneg (p : Point A) (v : G) : 0 ≤ p.toVertex v := by
  have h0 : (0 : ℝ) ≤ (wordDist A.carrier p.base v : ℝ) := by positivity
  have h1 : (0 : ℝ) ≤ (wordDist A.carrier p.tip v : ℝ) := by positivity
  have hp0 := p.param_nonneg
  have hp1 := p.param_le_one
  exact le_toVertex (by linarith) (by linarith)

theorem toVertex_le_base (p : Point A) : p.toVertex p.base ≤ p.param := by
  have h := toVertex_le_base_add p p.base
  rw [wordDist_self] at h
  push_cast at h
  linarith

theorem toVertex_le_tip (p : Point A) : p.toVertex p.tip ≤ 1 - p.param := by
  have h := toVertex_le_tip_add p p.tip
  rw [wordDist_self] at h
  push_cast at h
  linarith

/-- Moving the target vertex costs at most the word distance between the two
targets. -/
theorem toVertex_le_add (p : Point A) (v w : G) :
    p.toVertex w ≤ p.toVertex v + (wordDist A.carrier v w : ℝ) := by
  have hS := A.symmetricGenerating
  have h1 : (wordDist A.carrier p.base w : ℝ)
      ≤ (wordDist A.carrier p.base v : ℝ) + (wordDist A.carrier v w : ℝ) := by
    exact_mod_cast wordDist_triangle hS p.base v w
  have h2 : (wordDist A.carrier p.tip w : ℝ)
      ≤ (wordDist A.carrier p.tip v : ℝ) + (wordDist A.carrier v w : ℝ) := by
    exact_mod_cast wordDist_triangle hS p.tip v w
  have key1 := toVertex_le_base_add p w
  have key2 := toVertex_le_tip_add p w
  rcases toVertex_cases p v with h | h <;> rw [h] <;> linarith

/-- **Two vertices are no further apart than the sum of their distances to a
common point.**  The mixed case is where the edge length enters. -/
theorem wordDist_le_toVertex_add (p : Point A) (v w : G) :
    (wordDist A.carrier v w : ℝ) ≤ p.toVertex v + p.toVertex w := by
  have hS := A.symmetricGenerating
  have hbt := wordDist_base_tip_le_one p
  have hp0 := p.param_nonneg
  have hp1 := p.param_le_one
  have cb : (wordDist A.carrier p.base v : ℝ)
      = (wordDist A.carrier v p.base : ℝ) := by
    exact_mod_cast wordDist_comm hS p.base v
  have ct : (wordDist A.carrier p.tip v : ℝ)
      = (wordDist A.carrier v p.tip : ℝ) := by
    exact_mod_cast wordDist_comm hS p.tip v
  have t1 : (wordDist A.carrier v w : ℝ)
      ≤ (wordDist A.carrier v p.base : ℝ)
        + (wordDist A.carrier p.base w : ℝ) := by
    exact_mod_cast wordDist_triangle hS v p.base w
  have t2 : (wordDist A.carrier v w : ℝ)
      ≤ (wordDist A.carrier v p.tip : ℝ)
        + (wordDist A.carrier p.tip w : ℝ) := by
    exact_mod_cast wordDist_triangle hS v p.tip w
  have t3 : (wordDist A.carrier v p.tip : ℝ)
      ≤ (wordDist A.carrier v p.base : ℝ)
        + (wordDist A.carrier p.base p.tip : ℝ) := by
    exact_mod_cast wordDist_triangle hS v p.base p.tip
  have t4 : (wordDist A.carrier v p.base : ℝ)
      ≤ (wordDist A.carrier v p.tip : ℝ)
        + (wordDist A.carrier p.tip p.base : ℝ) := by
    exact_mod_cast wordDist_triangle hS v p.tip p.base
  have hts : (wordDist A.carrier p.tip p.base : ℝ)
      = (wordDist A.carrier p.base p.tip : ℝ) := by
    exact_mod_cast wordDist_comm hS p.tip p.base
  rcases toVertex_cases p v with hv | hv <;> rcases toVertex_cases p w with hw | hw <;>
    rw [hv, hw] <;> linarith

/-- The distance to a vertex is at least the distance from the base vertex, less
the length of one edge. -/
theorem sub_one_le_toVertex (p : Point A) (v : G) :
    (wordDist A.carrier p.base v : ℝ) - 1 ≤ p.toVertex v := by
  have hS := A.symmetricGenerating
  have hbt := wordDist_base_tip_le_one p
  have hp0 := p.param_nonneg
  have hp1 := p.param_le_one
  have h0 : (0 : ℝ) ≤ (wordDist A.carrier p.tip v : ℝ) := by positivity
  have htri : (wordDist A.carrier p.base v : ℝ)
      ≤ (wordDist A.carrier p.base p.tip : ℝ)
        + (wordDist A.carrier p.tip v : ℝ) := by
    exact_mod_cast wordDist_triangle hS p.base p.tip v
  exact le_toVertex (by linarith) (by linarith)

/-- On one edge, the distance to a vertex is `1`-Lipschitz in the parameter. -/
theorem toVertex_le_abs_add {p q : Point A} (hb : p.base = q.base)
    (hl : p.letter = q.letter) (v : G) :
    p.toVertex v ≤ |p.param - q.param| + q.toVertex v := by
  have h1 : p.param - q.param ≤ |p.param - q.param| := le_abs_self _
  have h2 : -(p.param - q.param) ≤ |p.param - q.param| := neg_le_abs _
  have htip : p.tip = q.tip := by
    show p.base * p.letter = q.base * q.letter
    rw [hb, hl]
  have key1 := toVertex_le_base_add p v
  have key2 := toVertex_le_tip_add p v
  rw [hb] at key1
  rw [htip] at key2
  rcases toVertex_cases q v with h | h <;> rw [h] <;> linarith

/-! ## The distance -/

/-- The four ways of joining `p` to `q` through the vertices of `Γ(G,A)`. -/
noncomputable def viaVertex (p q : Point A) : ℝ :=
  min (p.toVertex q.base + q.param) (p.toVertex q.tip + (1 - q.param))

theorem viaVertex_cases (p q : Point A) :
    viaVertex p q = p.toVertex q.base + q.param ∨
      viaVertex p q = p.toVertex q.tip + (1 - q.param) := by
  rcases min_cases (p.toVertex q.base + q.param)
      (p.toVertex q.tip + (1 - q.param)) with ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

theorem viaVertex_le_base (p q : Point A) :
    viaVertex p q ≤ p.toVertex q.base + q.param := min_le_left _ _

theorem viaVertex_le_tip (p q : Point A) :
    viaVertex p q ≤ p.toVertex q.tip + (1 - q.param) := min_le_right _ _

theorem viaVertex_nonneg (p q : Point A) : 0 ≤ viaVertex p q := by
  have h1 := toVertex_nonneg p q.base
  have h2 := toVertex_nonneg p q.tip
  have h3 := q.param_nonneg
  have h4 := q.param_le_one
  exact le_min (by linarith) (by linarith)

/-- Leaving `p` for any vertex and entering `q` from it is at least as long as
the best of the four ways. -/
theorem viaVertex_le_toVertex_add (p q : Point A) (v : G) :
    viaVertex p q ≤ p.toVertex v + q.toVertex v := by
  have hS := A.symmetricGenerating
  have hb := toVertex_le_add p v q.base
  have ht := toVertex_le_add p v q.tip
  have hcb : (wordDist A.carrier v q.base : ℝ)
      = (wordDist A.carrier q.base v : ℝ) := by
    exact_mod_cast wordDist_comm hS v q.base
  have hct : (wordDist A.carrier v q.tip : ℝ)
      = (wordDist A.carrier q.tip v : ℝ) := by
    exact_mod_cast wordDist_comm hS v q.tip
  rw [hcb] at hb
  rw [hct] at ht
  have h1 := viaVertex_le_base p q
  have h2 := viaVertex_le_tip p q
  rcases toVertex_cases q v with h | h <;> rw [h] <;> linarith

/-- **The four ways are the same from either end.** -/
theorem viaVertex_comm (p q : Point A) : viaVertex p q = viaVertex q p := by
  have hpb := toVertex_le_base p
  have hpt := toVertex_le_tip p
  have hqb := toVertex_le_base q
  have hqt := toVertex_le_tip q
  have hpqb := viaVertex_le_toVertex_add p q p.base
  have hpqt := viaVertex_le_toVertex_add p q p.tip
  have hqpb := viaVertex_le_toVertex_add q p q.base
  have hqpt := viaVertex_le_toVertex_add q p q.tip
  refine le_antisymm ?_ ?_
  · rcases viaVertex_cases q p with h | h <;> rw [h] <;> linarith
  · rcases viaVertex_cases p q with h | h <;> rw [h] <;> linarith

/-- Two points of one edge are joined along it, or through the vertices. -/
noncomputable def pointDist (p q : Point A) : ℝ :=
  if p.base = q.base ∧ p.letter = q.letter then
    min |p.param - q.param| (viaVertex p q)
  else viaVertex p q

theorem pointDist_le_viaVertex (p q : Point A) :
    pointDist p q ≤ viaVertex p q := by
  unfold pointDist
  split_ifs with h
  · exact min_le_right _ _
  · exact le_refl _

/-- The distance is one of its two candidates, and the edge candidate is only
available when the two points share an edge. -/
theorem pointDist_cases (p q : Point A) :
    pointDist p q = viaVertex p q ∨
      (p.base = q.base ∧ p.letter = q.letter) ∧
        pointDist p q = |p.param - q.param| := by
  unfold pointDist
  split_ifs with h
  · rcases min_cases |p.param - q.param| (viaVertex p q) with ⟨he, -⟩ | ⟨he, -⟩
    · exact Or.inr ⟨h, he⟩
    · exact Or.inl he
  · exact Or.inl rfl

theorem pointDist_nonneg (p q : Point A) : 0 ≤ pointDist p q := by
  unfold pointDist
  split_ifs with h
  · exact le_min (abs_nonneg _) (viaVertex_nonneg p q)
  · exact viaVertex_nonneg p q

theorem pointDist_self (p : Point A) : pointDist p p = 0 := by
  have hvia : 0 ≤ viaVertex p p := viaVertex_nonneg p p
  unfold pointDist
  rw [if_pos ⟨rfl, rfl⟩, sub_self, abs_zero]
  exact min_eq_left hvia

theorem pointDist_comm (p q : Point A) : pointDist p q = pointDist q p := by
  have hvia := viaVertex_comm p q
  have habs : |p.param - q.param| = |q.param - p.param| := abs_sub_comm _ _
  unfold pointDist
  by_cases h : p.base = q.base ∧ p.letter = q.letter
  · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩, habs, hvia]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩), hvia]

/-! ## The triangle inequality -/

/-- Through the vertices, the triangle inequality is the word metric's, with one
edge length paying for the two endpoints of the middle point. -/
theorem viaVertex_triangle (p q r : Point A) :
    viaVertex p r ≤ viaVertex p q + viaVertex q r := by
  have hS := A.symmetricGenerating
  have hqr : viaVertex q r = viaVertex r q := viaVertex_comm q r
  have hbase := viaVertex_le_toVertex_add p r q.base
  have htip := viaVertex_le_toVertex_add p r q.tip
  have hmove : r.toVertex q.base
      ≤ r.toVertex q.tip + (wordDist A.carrier q.tip q.base : ℝ) :=
    toVertex_le_add r q.tip q.base
  have hmove' : r.toVertex q.tip
      ≤ r.toVertex q.base + (wordDist A.carrier q.base q.tip : ℝ) :=
    toVertex_le_add r q.base q.tip
  have hbt := wordDist_base_tip_le_one q
  have hts : (wordDist A.carrier q.tip q.base : ℝ)
      = (wordDist A.carrier q.base q.tip : ℝ) := by
    exact_mod_cast wordDist_comm hS q.tip q.base
  rw [hts] at hmove
  have hq0 := q.param_nonneg
  have hq1 := q.param_le_one
  rw [hqr]
  rcases viaVertex_cases p q with h1 | h1 <;>
    rcases viaVertex_cases r q with h2 | h2 <;> rw [h1, h2] <;> linarith

/-- Along one edge, moving the first point costs the difference of the
parameters. -/
theorem viaVertex_le_abs_add {p q : Point A} (hb : p.base = q.base)
    (hl : p.letter = q.letter) (r : Point A) :
    viaVertex p r ≤ |p.param - q.param| + viaVertex q r := by
  have h1 := toVertex_le_abs_add hb hl r.base
  have h2 := toVertex_le_abs_add hb hl r.tip
  have hb1 := viaVertex_le_base p r
  have hb2 := viaVertex_le_tip p r
  rcases viaVertex_cases q r with h | h <;> rw [h] <;> linarith

/-- Along one edge, moving the second point costs the difference of the
parameters. -/
theorem viaVertex_le_abs_add_right {q r : Point A} (hb : q.base = r.base)
    (hl : q.letter = r.letter) (p : Point A) :
    viaVertex p r ≤ |q.param - r.param| + viaVertex p q := by
  have hrq : viaVertex r p ≤ |r.param - q.param| + viaVertex q p :=
    viaVertex_le_abs_add hb.symm hl.symm p
  rw [viaVertex_comm r p, viaVertex_comm q p, abs_sub_comm] at hrq
  exact hrq

/-- **The triangle inequality for `pointDist`.**  Two points may be joined
through the vertices always, and along a shared edge when they have one; the
four combinations are the four cases. -/
theorem pointDist_triangle (p q r : Point A) :
    pointDist p r ≤ pointDist p q + pointDist q r := by
  have hpr := pointDist_le_viaVertex p r
  rcases pointDist_cases p q with hpq | ⟨⟨hb1, hl1⟩, hpq⟩ <;>
    rcases pointDist_cases q r with hqr | ⟨⟨hb2, hl2⟩, hqr⟩
  · rw [hpq, hqr]
    exact le_trans hpr (viaVertex_triangle p q r)
  · rw [hpq, hqr]
    have h := viaVertex_le_abs_add_right hb2 hl2 p
    linarith
  · rw [hpq, hqr]
    have h := viaVertex_le_abs_add hb1 hl1 r
    linarith
  · rw [hpq, hqr]
    have hprEdge : p.base = r.base ∧ p.letter = r.letter :=
      ⟨hb1.trans hb2, hl1.trans hl2⟩
    have hd : pointDist p r ≤ |p.param - r.param| := by
      unfold pointDist
      rw [if_pos hprEdge]
      exact min_le_left _ _
    have habs : |p.param - r.param|
        ≤ |p.param - q.param| + |q.param - r.param| := by
      have hsplit : p.param - r.param
          = (p.param - q.param) + (q.param - r.param) := by ring
      rw [hsplit]
      exact abs_add _ _
    linarith

end Point

/-! ## The realisation as a pseudometric space -/

/-- **The metric realisation of `Γ(G,A)`.** -/
noncomputable instance instPseudoMetricSpacePoint (A : Alphabet G) :
    PseudoMetricSpace (Point A) where
  dist p q := Point.pointDist p q
  dist_self p := Point.pointDist_self p
  dist_comm p q := Point.pointDist_comm p q
  dist_triangle p q r := Point.pointDist_triangle p q r

@[simp] theorem dist_point_eq {A : Alphabet G} (p q : Point A) :
    dist p q = Point.pointDist p q := rfl

/-! ## The translation action -/

/-- `G` acts on the realisation by translating the base vertex. -/
instance instMulActionPoint (A : Alphabet G) : MulAction G (Point A) where
  smul g p := { p with base := g * p.base }
  one_smul p := by
    show { p with base := 1 * p.base } = p
    rw [one_mul]
  mul_smul g h p := by
    show { p with base := g * h * p.base } = { p with base := g * (h * p.base) }
    rw [mul_assoc]

@[simp] theorem smul_base {A : Alphabet G} (g : G) (p : Point A) :
    (g • p).base = g * p.base := rfl

@[simp] theorem smul_letter {A : Alphabet G} (g : G) (p : Point A) :
    (g • p).letter = p.letter := rfl

@[simp] theorem smul_param {A : Alphabet G} (g : G) (p : Point A) :
    (g • p).param = p.param := rfl

theorem smul_tip {A : Alphabet G} (g : G) (p : Point A) :
    (g • p).tip = g * p.tip := by
  show g * p.base * p.letter = g * (p.base * p.letter)
  rw [mul_assoc]

theorem toVertex_smul {A : Alphabet G} (g : G) (p : Point A) (v : G) :
    (g • p).toVertex (g * v) = p.toVertex v := by
  have hb : wordDist A.carrier (g * p.base) (g * v)
      = wordDist A.carrier p.base v := wordDist_left_invariant _ g p.base v
  have ht : wordDist A.carrier (g * p.tip) (g * v)
      = wordDist A.carrier p.tip v := wordDist_left_invariant _ g p.tip v
  unfold Point.toVertex
  rw [smul_base, smul_param, smul_tip, hb, ht]

theorem viaVertex_smul {A : Alphabet G} (g : G) (p q : Point A) :
    Point.viaVertex (g • p) (g • q) = Point.viaVertex p q := by
  have hb : (g • p).toVertex (g • q).base = p.toVertex q.base := by
    rw [smul_base]
    exact toVertex_smul g p q.base
  have ht : (g • p).toVertex (g • q).tip = p.toVertex q.tip := by
    rw [smul_tip]
    exact toVertex_smul g p q.tip
  unfold Point.viaVertex
  rw [hb, ht, smul_param]

/-- **The translation action is by isometries.** -/
theorem isIsometricAction_point (A : Alphabet G) :
    IsIsometricAction G (Point A) := by
  intro g p q
  show Point.pointDist (g • p) (g • q) = Point.pointDist p q
  have hvia := viaVertex_smul g p q
  have hbase : (g • p).base = (g • q).base ↔ p.base = q.base := by
    rw [smul_base, smul_base]
    exact mul_right_inj g
  unfold Point.pointDist
  by_cases h : p.base = q.base ∧ p.letter = q.letter
  · rw [if_pos ⟨hbase.mpr h.1, h.2⟩, if_pos h, hvia, smul_param, smul_param]
  · rw [if_neg (fun h' => h ⟨hbase.mp h'.1, h'.2⟩), if_neg h, hvia]

/-! ## The vertex inclusion -/

/-- The vertex `g`, as a point of the realisation. -/
def vertex (A : Alphabet G) (g : G) : Point A where
  base := g
  letter := 1
  letter_mem := Set.mem_insert _ _
  param := 0
  param_nonneg := le_refl 0
  param_le_one := zero_le_one

@[simp] theorem vertex_base (A : Alphabet G) (g : G) :
    (vertex A g).base = g := rfl

@[simp] theorem vertex_letter (A : Alphabet G) (g : G) :
    (vertex A g).letter = 1 := rfl

@[simp] theorem vertex_param (A : Alphabet G) (g : G) :
    (vertex A g).param = 0 := rfl

theorem vertex_tip (A : Alphabet G) (g : G) : (vertex A g).tip = g := by
  show g * 1 = g
  rw [mul_one]

theorem toVertex_vertex (A : Alphabet G) (g v : G) :
    (vertex A g).toVertex v = (wordDist A.carrier g v : ℝ) := by
  have h0 : (0 : ℝ) ≤ (wordDist A.carrier g v : ℝ) := by positivity
  have hb := Point.toVertex_le_base_add (vertex A g) v
  have hge := Point.le_toVertex (c := (wordDist A.carrier g v : ℝ))
    (p := vertex A g) (v := v) (by rw [vertex_base, vertex_param]; linarith)
    (by rw [vertex_tip, vertex_param]; linarith)
  rw [vertex_base, vertex_param] at hb
  linarith

theorem pointDist_vertex (A : Alphabet G) (g h : G) :
    Point.pointDist (vertex A g) (vertex A h)
      = (wordDist A.carrier g h : ℝ) := by
  have hvia : Point.viaVertex (vertex A g) (vertex A h)
      = (wordDist A.carrier g h : ℝ) := by
    have hb := Point.viaVertex_le_base (vertex A g) (vertex A h)
    have hge : (wordDist A.carrier g h : ℝ)
        ≤ Point.viaVertex (vertex A g) (vertex A h) := by
      refine le_min ?_ ?_
      · rw [vertex_base, vertex_param, toVertex_vertex]
        linarith
      · rw [vertex_tip, vertex_param, toVertex_vertex]
        linarith
    rw [vertex_base, vertex_param, toVertex_vertex] at hb
    linarith
  unfold Point.pointDist
  rw [hvia]
  split_ifs with hcond
  · have hgh : g = h := hcond.1
    subst hgh
    rw [wordDist_self, vertex_param, sub_self, abs_zero]
    push_cast
    exact min_eq_left (le_refl 0)
  · rfl

/-- The vertex inclusion of `Γ(G,A)` into its realisation. -/
def iota (A : Alphabet G) (x : Cayley A) : Point A := vertex A (Cayley.val x)

/-- **The vertex inclusion changes no distance.** -/
theorem hasAdditiveDistortion_iota (A : Alphabet G) :
    HasAdditiveDistortion 1 (iota A) := by
  intro x y
  have h : dist (iota A x) (iota A y) = dist x y := by
    show Point.pointDist (vertex A (Cayley.val x)) (vertex A (Cayley.val y))
      = dist x y
    rw [pointDist_vertex, Cayley.dist_eq]
  rw [h, sub_self, abs_zero]
  norm_num

/-- **Every point is within `1` of a vertex.** -/
theorem hasDenseImage_iota (A : Alphabet G) : HasDenseImage 1 (iota A) := by
  intro p
  refine ⟨Cayley.of A p.base, ?_⟩
  have hvia : Point.viaVertex (vertex A p.base) p
      ≤ (vertex A p.base).toVertex p.base + p.param :=
    Point.viaVertex_le_base _ _
  have hbase : (vertex A p.base).toVertex p.base = 0 := by
    rw [toVertex_vertex, wordDist_self]
    norm_num
  have hle := Point.pointDist_le_viaVertex (vertex A p.base) p
  have hp1 := p.param_le_one
  show Point.pointDist (vertex A (Cayley.val (Cayley.of A p.base))) p ≤ 1
  rw [Cayley.val_of]
  rw [hbase] at hvia
  linarith

/-- **The vertex inclusion is equivariant.** -/
theorem isEquivariant_iota (A : Alphabet G) : IsEquivariant G (iota A) := by
  intro g x
  rfl

/-! ## Hyperbolicity, pulled back along the retraction -/

/-- The retraction of the realisation onto the vertices. -/
def retr (A : Alphabet G) (p : Point A) : Cayley A := Cayley.of A p.base

/-- **The retraction has additive distortion `2`**: a point is within `1` of its
base vertex, whichever end it leaves by. -/
theorem hasAdditiveDistortion_retr (A : Alphabet G) :
    HasAdditiveDistortion 2 (retr A) := by
  intro p q
  have hS := A.symmetricGenerating
  have hretr : dist (retr A p) (retr A q)
      = (wordDist A.carrier p.base q.base : ℝ) := by
    show (wordDist A.carrier (Cayley.val (Cayley.of A p.base))
      (Cayley.val (Cayley.of A q.base)) : ℝ) = _
    rw [Cayley.val_of, Cayley.val_of]
  have hupper : Point.pointDist p q
      ≤ (wordDist A.carrier p.base q.base : ℝ) + 2 := by
    have h1 := Point.toVertex_le_base_add p q.base
    have h2 := Point.viaVertex_le_base p q
    have h3 := Point.pointDist_le_viaVertex p q
    have hp1 := p.param_le_one
    have hq1 := q.param_le_one
    linarith
  have hlower : (wordDist A.carrier p.base q.base : ℝ)
      ≤ Point.pointDist p q + 2 := by
    rcases Point.pointDist_cases p q with h | ⟨⟨hb, hl⟩, h⟩
    · rw [h]
      have hb1 := Point.sub_one_le_toVertex p q.base
      have ht1 := Point.sub_one_le_toVertex p q.tip
      have hbt := Point.wordDist_base_tip_le_one q
      have htri : (wordDist A.carrier p.base q.base : ℝ)
          ≤ (wordDist A.carrier p.base q.tip : ℝ)
            + (wordDist A.carrier q.tip q.base : ℝ) := by
        exact_mod_cast wordDist_triangle hS p.base q.tip q.base
      have hts : (wordDist A.carrier q.tip q.base : ℝ)
          = (wordDist A.carrier q.base q.tip : ℝ) := by
        exact_mod_cast wordDist_comm hS q.tip q.base
      rw [hts] at htri
      have hq0 := q.param_nonneg
      have hq1 := q.param_le_one
      rcases Point.viaVertex_cases p q with hv | hv <;> rw [hv] <;> linarith
    · rw [h]
      have h0 : wordDist A.carrier p.base q.base = 0 := by
        rw [hb, wordDist_self]
      rw [h0]
      have habs := abs_nonneg (p.param - q.param)
      push_cast
      linarith
  rw [hretr]
  show |(wordDist A.carrier p.base q.base : ℝ) - Point.pointDist p q| ≤ 2
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- **The realisation is hyperbolic whenever `Γ(G,A)` is.**  The four-point
condition pulls back along the retraction, at the cost `3 · 2`. -/
theorem isHyperbolicSpace_point (A : Alphabet G) {δ : ℝ}
    (hδ : IsHyperbolicSpace δ (Cayley A)) :
    IsHyperbolicSpace (δ + 6) (Point A) := by
  have h := isHyperbolicSpace_of_additiveDistortion
    (hasAdditiveDistortion_retr A) hδ
  have hEq : δ + 3 * (2 : ℝ) = δ + 6 := by norm_num
  rwa [hEq] at h

/-! ## One step of a minimal word -/

/-- The word distance from `x` to `x * a` is the word length of `a`. -/
theorem wordDist_mul_right (A : Alphabet G) (x a : G) :
    wordDist A.carrier x (x * a) = wordNorm A.carrier a := by
  show wordNorm A.carrier (x⁻¹ * (x * a)) = wordNorm A.carrier a
  rw [← mul_assoc, inv_mul_cancel, one_mul]

/-- An alphabet letter other than the identity is one step away. -/
theorem wordDist_step_eq_one (A : Alphabet G) (x : G) {a : G}
    (ha : a ∈ A.carrier) (hane : a ≠ 1) : wordDist A.carrier x (x * a) = 1 := by
  rw [wordDist_mul_right]
  exact le_antisymm (wordNorm_le_one_of_mem ha)
    (one_le_wordNorm A.symmetricGenerating hane)

/-- **One step along a minimal word.**  If `x` is `n + 1` away from `y` then
some letter of the alphabet takes `x` to a point `n` away, and that letter is
not the identity. -/
theorem exists_step (A : Alphabet G) {x y : G} {n : ℕ}
    (hn : wordDist A.carrier x y = n + 1) :
    ∃ a ∈ A.carrier, a ≠ 1 ∧ wordDist A.carrier (x * a) y = n := by
  have hS := A.symmetricGenerating
  obtain ⟨l, hl, hlen⟩ := exists_isWord_length_eq hS (x⁻¹ * y)
  have hlen' : l.length = n + 1 := by
    rw [hlen]
    exact hn
  cases l with
  | nil =>
      rw [List.length_nil] at hlen'
      exact absurd hlen'.symm (Nat.succ_ne_zero n)
  | cons a l' =>
      have ha : a ∈ A.carrier := hl.letters a (List.mem_cons_self a l')
      have hprod : a * l'.prod = x⁻¹ * y := by
        have h := hl.prod_eq
        rwa [List.prod_cons] at h
      have hkey : l'.prod = (x * a)⁻¹ * y := by
        rw [mul_inv_rev, mul_assoc, ← hprod, ← mul_assoc, inv_mul_cancel, one_mul]
      have hl'word : IsWord A.carrier l' ((x * a)⁻¹ * y) :=
        ⟨fun z hz => hl.letters z (List.mem_cons_of_mem a hz), hkey⟩
      have hlen'' : l'.length = n := by
        rw [List.length_cons] at hlen'
        omega
      have hle : wordDist A.carrier (x * a) y ≤ n := by
        have h : wordNorm A.carrier ((x * a)⁻¹ * y) ≤ l'.length :=
          wordNorm_le_length hl'word
        rw [hlen''] at h
        exact h
      have hone : wordDist A.carrier x (x * a) ≤ 1 := by
        rw [wordDist_mul_right]
        exact wordNorm_le_one_of_mem ha
      have htri := wordDist_triangle hS x (x * a) y
      have hane : a ≠ 1 := by
        intro h1
        rw [h1, mul_one] at hle
        omega
      exact ⟨a, ha, hane, by omega⟩

/-! ## Points along one edge -/

/-- The point `σ` of the way along the edge from `x` labelled `a`.  The
parameter is clamped, so that the definition is total. -/
noncomputable def edgePoint (A : Alphabet G) (x a : G) (ha : a ∈ A.carrier)
    (σ : ℝ) : Point A where
  base := x
  letter := a
  letter_mem := Set.mem_insert_of_mem _ ha
  param := min 1 (max 0 σ)
  param_nonneg := le_min (by norm_num) (le_max_left _ _)
  param_le_one := min_le_left _ _

@[simp] theorem edgePoint_base (A : Alphabet G) (x a : G) (ha : a ∈ A.carrier)
    (σ : ℝ) : (edgePoint A x a ha σ).base = x := rfl

@[simp] theorem edgePoint_letter (A : Alphabet G) (x a : G) (ha : a ∈ A.carrier)
    (σ : ℝ) : (edgePoint A x a ha σ).letter = a := rfl

@[simp] theorem edgePoint_tip (A : Alphabet G) (x a : G) (ha : a ∈ A.carrier)
    (σ : ℝ) : (edgePoint A x a ha σ).tip = x * a := rfl

theorem edgePoint_param (A : Alphabet G) (x a : G) (ha : a ∈ A.carrier) {σ : ℝ}
    (h0 : 0 ≤ σ) (h1 : σ ≤ 1) : (edgePoint A x a ha σ).param = σ := by
  show min 1 (max 0 σ) = σ
  rw [max_eq_right h0, min_eq_right h1]

theorem toVertex_edgePoint (A : Alphabet G) (x a : G) (ha : a ∈ A.carrier)
    {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (v : G) :
    (edgePoint A x a ha σ).toVertex v
      = min (σ + (wordDist A.carrier x v : ℝ))
        (1 - σ + (wordDist A.carrier (x * a) v : ℝ)) := by
  show min ((edgePoint A x a ha σ).param + (wordDist A.carrier x v : ℝ))
      (1 - (edgePoint A x a ha σ).param + (wordDist A.carrier (x * a) v : ℝ))
    = min (σ + (wordDist A.carrier x v : ℝ))
      (1 - σ + (wordDist A.carrier (x * a) v : ℝ))
  rw [edgePoint_param A x a ha h0 h1]

/-- Against a vertex, the four ways collapse to the distance to that vertex. -/
theorem viaVertex_vertex_right {A : Alphabet G} (p : Point A) (v : G) :
    Point.viaVertex p (vertex A v) = p.toVertex v := by
  show min (p.toVertex (vertex A v).base + (vertex A v).param)
      (p.toVertex (vertex A v).tip + (1 - (vertex A v).param)) = p.toVertex v
  rw [vertex_base, vertex_tip, vertex_param]
  exact min_eq_left (by linarith)

/-- Against a vertex on a different edge, the distance is the distance to that
vertex. -/
theorem pointDist_vertex_right {A : Alphabet G} (p : Point A) (v : G)
    (hcond : ¬ (p.base = v ∧ p.letter = 1)) :
    Point.pointDist p (vertex A v) = p.toVertex v := by
  unfold Point.pointDist
  rw [if_neg hcond, viaVertex_vertex_right]

/-- **The far endpoint is `1 - σ` away.** -/
theorem dist_edgePoint_tip (A : Alphabet G) (x a : G) (ha : a ∈ A.carrier)
    (hane : a ≠ 1) {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ 1) :
    dist (edgePoint A x a ha σ) (vertex A (x * a)) = 1 - σ := by
  have hstep := wordDist_step_eq_one A x ha hane
  have hne : x ≠ x * a := by
    intro h
    rw [← h, wordDist_self] at hstep
    exact absurd hstep (by norm_num)
  have hcond : ¬ ((edgePoint A x a ha σ).base = x * a ∧
      (edgePoint A x a ha σ).letter = 1) := by
    intro h
    exact hne h.1
  show Point.pointDist (edgePoint A x a ha σ) (vertex A (x * a)) = 1 - σ
  rw [pointDist_vertex_right _ _ hcond, toVertex_edgePoint A x a ha h0 h1,
    hstep, wordDist_self]
  push_cast
  exact min_eq_right (by linarith)

/-- **The base vertex is `σ` away.** -/
theorem dist_vertex_edgePoint (A : Alphabet G) (x a : G) (ha : a ∈ A.carrier)
    (hane : a ≠ 1) {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ 1) :
    dist (vertex A x) (edgePoint A x a ha σ) = σ := by
  have hstep := wordDist_step_eq_one A x ha hane
  have hcomm : wordDist A.carrier (x * a) x = 1 := by
    rw [wordDist_comm A.symmetricGenerating]
    exact hstep
  have hcond : ¬ ((edgePoint A x a ha σ).base = x ∧
      (edgePoint A x a ha σ).letter = 1) := by
    intro h
    exact hane h.2
  show Point.pointDist (vertex A x) (edgePoint A x a ha σ) = σ
  rw [Point.pointDist_comm, pointDist_vertex_right _ _ hcond,
    toVertex_edgePoint A x a ha h0 h1, wordDist_self, hcomm]
  push_cast
  exact min_eq_left (by linarith)

/-- **Two points of one edge are `|σ - τ|` apart.** -/
theorem dist_edgePoint_edgePoint (A : Alphabet G) (x a : G) (ha : a ∈ A.carrier)
    (hane : a ≠ 1) {σ τ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ 1) (k0 : 0 ≤ τ)
    (k1 : τ ≤ 1) :
    dist (edgePoint A x a ha σ) (edgePoint A x a ha τ) = |σ - τ| := by
  have hstep := wordDist_step_eq_one A x ha hane
  have hcomm : wordDist A.carrier (x * a) x = 1 := by
    rw [wordDist_comm A.symmetricGenerating]
    exact hstep
  have hbase : (edgePoint A x a ha σ).toVertex x = σ := by
    rw [toVertex_edgePoint A x a ha h0 h1, wordDist_self, hcomm]
    push_cast
    exact min_eq_left (by linarith)
  have htip : (edgePoint A x a ha σ).toVertex (x * a) = 1 - σ := by
    rw [toVertex_edgePoint A x a ha h0 h1, hstep, wordDist_self]
    push_cast
    exact min_eq_right (by linarith)
  have hvia : Point.viaVertex (edgePoint A x a ha σ) (edgePoint A x a ha τ)
      = min (σ + τ) (1 - σ + (1 - τ)) := by
    show min ((edgePoint A x a ha σ).toVertex (edgePoint A x a ha τ).base
        + (edgePoint A x a ha τ).param)
      ((edgePoint A x a ha σ).toVertex (edgePoint A x a ha τ).tip
        + (1 - (edgePoint A x a ha τ).param)) = _
    rw [edgePoint_base, edgePoint_tip, edgePoint_param A x a ha k0 k1, hbase,
      htip]
  have hle : |σ - τ| ≤ min (σ + τ) (1 - σ + (1 - τ)) :=
    le_min (abs_le.mpr ⟨by linarith, by linarith⟩)
      (abs_le.mpr ⟨by linarith, by linarith⟩)
  show Point.pointDist (edgePoint A x a ha σ) (edgePoint A x a ha τ) = |σ - τ|
  unfold Point.pointDist
  rw [if_pos ⟨rfl, rfl⟩, edgePoint_param A x a ha h0 h1,
    edgePoint_param A x a ha k0 k1, hvia]
  exact min_eq_left hle

/-- **A vertex further along is `wordDist - σ` away**, when the far endpoint of
the edge is one step closer to it. -/
theorem dist_edgePoint_vertex (A : Alphabet G) (x a y : G) (ha : a ∈ A.carrier)
    (hane : a ≠ 1)
    (hfar : wordDist A.carrier x y = wordDist A.carrier (x * a) y + 1)
    {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ 1) :
    dist (edgePoint A x a ha σ) (vertex A y)
      = (wordDist A.carrier x y : ℝ) - σ := by
  have hne : x ≠ y := by
    intro h
    rw [h, wordDist_self] at hfar
    omega
  have hcond : ¬ ((edgePoint A x a ha σ).base = y ∧
      (edgePoint A x a ha σ).letter = 1) := by
    intro h
    exact hne h.1
  have hcast : ((wordDist A.carrier x y : ℕ) : ℝ)
      = ((wordDist A.carrier (x * a) y : ℕ) : ℝ) + 1 := by
    rw [hfar]
    push_cast
    ring
  show Point.pointDist (edgePoint A x a ha σ) (vertex A y)
    = (wordDist A.carrier x y : ℝ) - σ
  rw [pointDist_vertex_right _ _ hcond, toVertex_edgePoint A x a ha h0 h1,
    hcast]
  exact min_eq_right (by linarith)

/-! ## The unit edge, parametrised from its base -/

/-- The edge from `x` labelled `a`, parametrised on `[0,1]` so that it starts at
the vertex `x` and ends at the vertex `x * a` — rather than at the points
`(x,a,0)` and `(x,a,1)`, which are only at distance zero from them.  The
endpoints have to be hit on the nose, because `IsGeodesicSpace` asks for
equality there. -/
noncomputable def edgePath (A : Alphabet G) (x a : G) (ha : a ∈ A.carrier) :
    ℝ → Point A :=
  fun r => if r ≤ 0 then vertex A x else
    if 1 ≤ r then vertex A (x * a) else edgePoint A x a ha r

theorem edgePath_of_nonpos (A : Alphabet G) (x a : G) (ha : a ∈ A.carrier)
    {r : ℝ} (h : r ≤ 0) : edgePath A x a ha r = vertex A x := by
  show (if r ≤ 0 then vertex A x else
    if 1 ≤ r then vertex A (x * a) else edgePoint A x a ha r) = vertex A x
  rw [if_pos h]

theorem edgePath_of_one_le (A : Alphabet G) (x a : G) (ha : a ∈ A.carrier)
    {r : ℝ} (h : 1 ≤ r) : edgePath A x a ha r = vertex A (x * a) := by
  have h0 : ¬ r ≤ 0 := by linarith
  show (if r ≤ 0 then vertex A x else
    if 1 ≤ r then vertex A (x * a) else edgePoint A x a ha r) = vertex A (x * a)
  rw [if_neg h0, if_pos h]

theorem edgePath_of_mem (A : Alphabet G) (x a : G) (ha : a ∈ A.carrier)
    {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
    edgePath A x a ha r = edgePoint A x a ha r := by
  have hz : ¬ r ≤ 0 := by linarith
  have ho : ¬ (1 : ℝ) ≤ r := by linarith
  show (if r ≤ 0 then vertex A x else
    if 1 ≤ r then vertex A (x * a) else edgePoint A x a ha r)
    = edgePoint A x a ha r
  rw [if_neg hz, if_neg ho]

theorem edgePath_zero (A : Alphabet G) (x a : G) (ha : a ∈ A.carrier) :
    edgePath A x a ha 0 = vertex A x :=
  edgePath_of_nonpos A x a ha (le_refl 0)

theorem edgePath_one (A : Alphabet G) (x a : G) (ha : a ∈ A.carrier) :
    edgePath A x a ha 1 = vertex A (x * a) :=
  edgePath_of_one_le A x a ha (le_refl 1)

/-- The distance from a point of the edge to its far endpoint. -/
theorem dist_edgePath_tip (A : Alphabet G) (x a : G) (ha : a ∈ A.carrier)
    (hane : a ≠ 1) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    dist (edgePath A x a ha s) (vertex A (x * a)) = 1 - s := by
  have hstep := wordDist_step_eq_one A x ha hane
  by_cases hz : s ≤ 0
  · have hs0 : s = 0 := le_antisymm hz h0
    rw [edgePath_of_nonpos A x a ha hz, hs0]
    show Point.pointDist (vertex A x) (vertex A (x * a)) = 1 - 0
    rw [pointDist_vertex, hstep]
    norm_num
  · by_cases ho : (1 : ℝ) ≤ s
    · have hs1 : s = 1 := le_antisymm h1 ho
      rw [edgePath_of_one_le A x a ha ho, hs1]
      show Point.pointDist (vertex A (x * a)) (vertex A (x * a)) = 1 - 1
      rw [Point.pointDist_self]
      norm_num
    · rw [edgePath_of_mem A x a ha (by linarith) (by linarith)]
      exact dist_edgePoint_tip A x a ha hane h0 h1

/-- The distance from a point of the edge to a vertex the edge points at. -/
theorem dist_edgePath_vertex (A : Alphabet G) (x a y : G) (ha : a ∈ A.carrier)
    (hane : a ≠ 1)
    (hfar : wordDist A.carrier x y = wordDist A.carrier (x * a) y + 1)
    {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    dist (edgePath A x a ha s) (vertex A y)
      = (wordDist A.carrier x y : ℝ) - s := by
  have hcast : ((wordDist A.carrier x y : ℕ) : ℝ)
      = ((wordDist A.carrier (x * a) y : ℕ) : ℝ) + 1 := by
    rw [hfar]
    push_cast
    ring
  by_cases hz : s ≤ 0
  · have hs0 : s = 0 := le_antisymm hz h0
    rw [edgePath_of_nonpos A x a ha hz, hs0]
    show Point.pointDist (vertex A x) (vertex A y)
      = (wordDist A.carrier x y : ℝ) - 0
    rw [pointDist_vertex]
    norm_num
  · by_cases ho : (1 : ℝ) ≤ s
    · have hs1 : s = 1 := le_antisymm h1 ho
      rw [edgePath_of_one_le A x a ha ho, hs1]
      show Point.pointDist (vertex A (x * a)) (vertex A y)
        = (wordDist A.carrier x y : ℝ) - 1
      rw [pointDist_vertex, hcast]
      ring
    · rw [edgePath_of_mem A x a ha (by linarith) (by linarith)]
      exact dist_edgePoint_vertex A x a y ha hane hfar h0 h1

/-- **The edge is a geodesic segment of length one.** -/
theorem isGeodesicSegment_edgePath (A : Alphabet G) (x a : G)
    (ha : a ∈ A.carrier) (hane : a ≠ 1) :
    IsGeodesicSegment (edgePath A x a ha) 0 1 := by
  have hstep := wordDist_step_eq_one A x ha hane
  have key : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, s ≤ t →
      dist (edgePath A x a ha s) (edgePath A x a ha t) = t - s := by
    intro s hs t ht hst
    obtain ⟨hs0, hs1⟩ := hs
    obtain ⟨ht0, ht1⟩ := ht
    by_cases hsz : s ≤ 0
    · have hs0' : s = 0 := le_antisymm hsz hs0
      rw [edgePath_of_nonpos A x a ha hsz]
      by_cases htz : t ≤ 0
      · have ht0' : t = 0 := le_antisymm htz ht0
        rw [edgePath_of_nonpos A x a ha htz, hs0', ht0']
        show Point.pointDist (vertex A x) (vertex A x) = 0 - 0
        rw [Point.pointDist_self]
        norm_num
      · by_cases hto : (1 : ℝ) ≤ t
        · have ht1' : t = 1 := le_antisymm ht1 hto
          rw [edgePath_of_one_le A x a ha hto, hs0', ht1']
          show Point.pointDist (vertex A x) (vertex A (x * a)) = 1 - 0
          rw [pointDist_vertex, hstep]
          norm_num
        · rw [edgePath_of_mem A x a ha (by linarith) (by linarith), hs0',
            sub_zero]
          exact dist_vertex_edgePoint A x a ha hane ht0 ht1
    · by_cases hso : (1 : ℝ) ≤ s
      · have hs1' : s = 1 := le_antisymm hs1 hso
        have ht1' : t = 1 := le_antisymm ht1 (by linarith)
        rw [edgePath_of_one_le A x a ha hso,
          edgePath_of_one_le A x a ha (by linarith : (1 : ℝ) ≤ t), hs1', ht1']
        show Point.pointDist (vertex A (x * a)) (vertex A (x * a)) = 1 - 1
        rw [Point.pointDist_self]
        norm_num
      · rw [edgePath_of_mem A x a ha (by linarith) (by linarith)]
        by_cases hto : (1 : ℝ) ≤ t
        · have ht1' : t = 1 := le_antisymm ht1 hto
          rw [edgePath_of_one_le A x a ha hto, ht1']
          exact dist_edgePoint_tip A x a ha hane hs0 hs1
        · rw [edgePath_of_mem A x a ha (by linarith) (by linarith),
            dist_edgePoint_edgePoint A x a ha hane hs0 hs1 ht0 ht1,
            abs_of_nonpos (by linarith)]
          ring
  intro s hs t ht
  rcases le_total s t with h | h
  · rw [key s hs t ht h, abs_of_nonpos (by linarith)]
    ring
  · rw [dist_comm, key t ht s hs h, abs_of_nonneg (by linarith)]

/-! ## Gluing two geodesic segments -/

/-- **Concatenation.**  Two geodesic segments whose points are at the sum of
their distances to the junction concatenate to a geodesic segment.  The two
junction values need not be equal: in a pseudometric space it is enough that
they are at distance zero, which is the case `s = L`, `t = 0` of `hfar`. -/
theorem isGeodesicSegment_glue {X : Type*} [PseudoMetricSpace X] {f g : ℝ → X}
    {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hf : IsGeodesicSegment f 0 L) (hg : IsGeodesicSegment g 0 M)
    (hfar : ∀ s ∈ Set.Icc (0 : ℝ) L, ∀ t ∈ Set.Icc (0 : ℝ) M,
      dist (f s) (g t) = L - s + t) :
    IsGeodesicSegment (fun r => if r ≤ L then f r else g (r - L)) 0 (L + M) := by
  have key : ∀ s ∈ Set.Icc (0 : ℝ) (L + M), ∀ t ∈ Set.Icc (0 : ℝ) (L + M),
      s ≤ t →
      dist (if s ≤ L then f s else g (s - L))
        (if t ≤ L then f t else g (t - L)) = t - s := by
    intro s hs t ht hst
    obtain ⟨hs0, hs1⟩ := hs
    obtain ⟨ht0, ht1⟩ := ht
    by_cases hsL : s ≤ L
    · by_cases htL : t ≤ L
      · rw [if_pos hsL, if_pos htL, hf s ⟨hs0, hsL⟩ t ⟨ht0, htL⟩,
          abs_of_nonpos (by linarith)]
        ring
      · rw [if_pos hsL, if_neg htL,
          hfar s ⟨hs0, hsL⟩ (t - L) ⟨by linarith, by linarith⟩]
        ring
    · have htL : ¬ t ≤ L := fun h => hsL (le_trans hst h)
      rw [if_neg hsL, if_neg htL,
        hg (s - L) ⟨by linarith, by linarith⟩ (t - L)
          ⟨by linarith, by linarith⟩, abs_of_nonpos (by linarith)]
      ring
  intro s hs t ht
  rcases le_total s t with h | h
  · rw [key s hs t ht h, abs_of_nonpos (by linarith)]
    ring
  · rw [dist_comm, key t ht s hs h, abs_of_nonneg (by linarith)]

/-! ## Geodesics between vertices -/

/-- **The realisation is geodesic between vertices.**  Induction on the word
distance: one step of a minimal word gives a unit edge, the rest is the
inductive geodesic, and `isGeodesicSegment_glue` joins them.  The hypothesis of
that lemma is the two triangle inequalities through the intermediate vertex and
through the target — the upper bound and the lower bound of `hfar`. -/
theorem exists_vertexGeodesic (A : Alphabet G) :
    ∀ (n : ℕ) (x y : G), wordDist A.carrier x y = n →
      ∃ f : ℝ → Point A, IsGeodesicSegment f 0 (n : ℝ) ∧
        f 0 = vertex A x ∧ f (n : ℝ) = vertex A y := by
  intro n
  induction n with
  | zero =>
      intro x y hxy
      have hxy' : x = y :=
        (wordDist_eq_zero_iff A.symmetricGenerating x y).mp hxy
      refine ⟨fun _ => vertex A x, ?_, rfl, ?_⟩
      · intro s hs t ht
        have hs0 : s = 0 := le_antisymm (by simpa using hs.2) hs.1
        have ht0 : t = 0 := le_antisymm (by simpa using ht.2) ht.1
        rw [hs0, ht0]
        show Point.pointDist (vertex A x) (vertex A x) = |(0 : ℝ) - 0|
        rw [Point.pointDist_self]
        norm_num
      · rw [hxy']
  | succ n ih =>
      intro x y hxy
      have hxy' : wordDist A.carrier x y = n + 1 := hxy
      obtain ⟨a, ha, hane, hstep⟩ := exists_step A hxy'
      obtain ⟨f', hf'geo, hf'0, hf'n⟩ := ih (x * a) y hstep
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
      have hfarStep : wordDist A.carrier x y
          = wordDist A.carrier (x * a) y + 1 := by
        rw [hstep, hxy']
      have hcast : ((wordDist A.carrier x y : ℕ) : ℝ) = (n : ℝ) + 1 := by
        rw [hxy']
        push_cast
        ring
      -- The distance from a point of the tail to the junction and to the target.
      have htail_tip : ∀ t ∈ Set.Icc (0 : ℝ) (n : ℝ),
          dist (f' t) (vertex A (x * a)) = t := by
        intro t ht
        have h := hf'geo 0 ⟨le_refl 0, hn0⟩ t ht
        rw [hf'0] at h
        rw [dist_comm, h, abs_of_nonpos (by linarith [ht.1])]
        ring
      have htail_far : ∀ t ∈ Set.Icc (0 : ℝ) (n : ℝ),
          dist (f' t) (vertex A y) = (n : ℝ) - t := by
        intro t ht
        have h := hf'geo t ht (n : ℝ) ⟨hn0, le_refl _⟩
        rw [hf'n] at h
        rw [h, abs_of_nonpos (by linarith [ht.2])]
        ring
      have hfar : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) (n : ℝ),
          dist (edgePath A x a ha s) (f' t) = 1 - s + t := by
        intro s hs t ht
        have hup : dist (edgePath A x a ha s) (f' t) ≤ 1 - s + t := by
          have h1 := dist_edgePath_tip A x a ha hane hs.1 hs.2
          have h2 := htail_tip t ht
          have h3 := dist_triangle (edgePath A x a ha s) (vertex A (x * a)) (f' t)
          rw [dist_comm (vertex A (x * a)) (f' t)] at h3
          linarith
        have hdown : 1 - s + t ≤ dist (edgePath A x a ha s) (f' t) := by
          have h1 := dist_edgePath_vertex A x a y ha hane hfarStep hs.1 hs.2
          have h2 := htail_far t ht
          have h3 := dist_triangle (edgePath A x a ha s) (f' t) (vertex A y)
          rw [hcast] at h1
          linarith
        linarith
      have hglue := isGeodesicSegment_glue (f := edgePath A x a ha) (g := f')
        (L := 1) (M := (n : ℝ)) (by norm_num) hn0
        (isGeodesicSegment_edgePath A x a ha hane) hf'geo hfar
      refine ⟨fun r => if r ≤ 1 then edgePath A x a ha r else f' (r - 1), ?_,
        ?_, ?_⟩
      · have hL : (1 : ℝ) + (n : ℝ) = ((n + 1 : ℕ) : ℝ) := by
          push_cast
          ring
        rwa [hL] at hglue
      · show (if (0 : ℝ) ≤ 1 then edgePath A x a ha 0 else f' (0 - 1))
          = vertex A x
        rw [if_pos (by norm_num : (0 : ℝ) ≤ 1), edgePath_zero]
      · by_cases hzero : n = 0
        · have hy : x * a = y :=
            (wordDist_eq_zero_iff A.symmetricGenerating (x * a) y).mp
              (by rw [hstep, hzero])
          have hone : ((n + 1 : ℕ) : ℝ) = 1 := by
            rw [hzero]
            norm_num
          show (if ((n + 1 : ℕ) : ℝ) ≤ 1 then edgePath A x a ha ((n + 1 : ℕ) : ℝ)
            else f' (((n + 1 : ℕ) : ℝ) - 1)) = vertex A y
          rw [hone, if_pos (le_refl (1 : ℝ)), edgePath_one, hy]
        · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
            have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hzero
            exact_mod_cast this
          have hnot : ¬ ((n + 1 : ℕ) : ℝ) ≤ 1 := by
            push_cast
            linarith
          have hsub : ((n + 1 : ℕ) : ℝ) - 1 = (n : ℝ) := by
            push_cast
            ring
          show (if ((n + 1 : ℕ) : ℝ) ≤ 1 then edgePath A x a ha ((n + 1 : ℕ) : ℝ)
            else f' (((n + 1 : ℕ) : ℝ) - 1)) = vertex A y
          rw [if_neg hnot, hsub, hf'n]

/-- **Geodesics between vertices, in the metric of the realisation.**  This is
the case the fellow-travelling lemma of `Sofic.HullSuitabilityGeometry` needs:
its basepoint is a vertex and its endpoints are orbit points of it, which are
vertices too, since the action carries vertices to vertices. -/
theorem exists_geodesic_vertex (A : Alphabet G) (x y : G) :
    ∃ f : ℝ → Point A,
      IsGeodesicSegment f 0 (dist (vertex A x) (vertex A y)) ∧
        f 0 = vertex A x ∧
        f (dist (vertex A x) (vertex A y)) = vertex A y := by
  obtain ⟨f, hgeo, h0, hn⟩ :=
    exists_vertexGeodesic A (wordDist A.carrier x y) x y rfl
  have hdist : dist (vertex A x) (vertex A y)
      = ((wordDist A.carrier x y : ℕ) : ℝ) := pointDist_vertex A x y
  rw [hdist]
  exact ⟨f, hgeo, h0, hn⟩

/-! ## The model -/

/-- **What is left of geodesicity.**  `exists_vertexGeodesic` proves it between
vertices, which is the case every consumer uses; `IsGeodesicSpace` asks for it
between arbitrary points, and the difference is the two partial edges at the
ends — from `p` to whichever of its endpoints the distance is realised through,
and from an endpoint of `q` into `q`.  `isGeodesicSegment_glue` is the tool for
both, and `dist_edgePoint_edgePoint` settles the remaining case, where `p` and
`q` share an edge and the distance is realised along it. -/
def IsGeodesicRealisation (A : Alphabet G) : Prop := IsGeodesicSpace (Point A)

/-- **The geodesic model of `Γ(G,A)`**, on that one residual. -/
noncomputable def model (A : Alphabet G) {δ : ℝ}
    (hδ : IsHyperbolicSpace δ (Cayley A)) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicRealisation A) : GeodesicModel G (Cayley A) where
  W := Point A
  iota := iota A
  distortion := 1
  distortion_nonneg := zero_le_one
  hasAdditiveDistortion := hasAdditiveDistortion_iota A
  hasDenseImage := hasDenseImage_iota A
  equivariant := isEquivariant_iota A
  isometric := isIsometricAction_point A
  geodesic := hgeo
  delta := δ + 6
  delta_nonneg := by linarith
  hyperbolic := isHyperbolicSpace_point A hδ

/-- **`HasGeodesicModel`, on that one residual.**  With
`Manuscript.NonMF.HullFillAxisDichotomy.axisDichotomy_cayley`, what
`AxisDichotomy` still costs is `CommonPowerInGeodesicSpace` and
`IsGeodesicRealisation` — one theorem in a geodesic space, and one
parametrisation. -/
theorem hasGeodesicModel (A : HullGeneratingSet G)
    (hgeo : IsGeodesicRealisation A.alphabet) :
    HasGeodesicModel A.alphabet :=
  ⟨model A.alphabet A.hyperbolic
    (nonneg_of_isHyperbolicSpace A.hyperbolic (Cayley.base A.alphabet)) hgeo⟩

end CayleyGeodesicModel
end GGT
end GroupApproximation
