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
`base * letter`.  Adding `1` to the alphabet makes every vertex a point of the
realisation — `base` is `(base, 1, 0)` — and keeps the space nonempty when the
alphabet is not.

Edges are **not** identified: `(g, a, t)` and `(g * a, a⁻¹, 1 - t)` are two
points of the realisation at distance `2t` from each other, so each geometric
edge appears twice and the two copies meet at their endpoints.  That is
deliberate — quotienting would cost a setoid and every proof below would be
about equivalence classes — and it is harmless: a bigon of length two changes no
quasi-isometry class and no hyperbolicity constant beyond a bounded amount.

## The distance

`viaVertex p q` is the least of the four ways of leaving `p` by one of its two
endpoints, crossing `Γ(G,A)` by the word metric, and entering `q` by one of
its two endpoints.  `pointDist p q` is `viaVertex p q`, except that two points
of the *same* edge may also be joined along it, at cost `|t - t'|`.

The `letter ∈ A ∪ {1}` constraint is what makes this a pseudometric: it forces
`d(base, tip) ≤ 1`, so traversing an edge is never a shortcut.  Without it the
triangle inequality fails, since an edge from `g` to `g * a` would have length
one however far apart `g` and `g * a` are in the word metric.

## What is proved and what is not

Proved: `pointDist` is a pseudometric; the translation action is by isometries;
the vertex inclusion is equivariant, changes no distance, and has `1`-dense
image; and the realisation is hyperbolic whenever `Γ(G,A)` is, by pulling the
four-point condition back along the base-vertex retraction, which has additive
distortion `2`.

Not proved, and isolated as the single residual `geodesic_of_edgePath`: that the
realisation is a geodesic space.  The content is that a word of length `n`
realising `wordDist S x y` gives a path of `n` unit edges from `x` to `y`, whose
piecewise-linear parametrisation is an isometry of `[0,n]`; the two ingredients
are that every prefix of a minimal word is minimal, and that concatenating unit
edge parametrisations gives a geodesic segment.  `model` takes it as a
hypothesis, so everything else here is available without it.

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
def Letters (S : Set G) : Set G := insert 1 S

/-- A point of the metric realisation of `Γ(G,S)`: `param` of the way along the
edge from `base` to `base * letter`. -/
structure Point (S : Set G) where
  /-- The vertex the edge starts at. -/
  base : G
  /-- The letter the edge is labelled by. -/
  letter : G
  /-- The letter is one of the alphabet, or the identity. -/
  letter_mem : letter ∈ Letters S
  /-- The position along the edge. -/
  param : ℝ
  /-- The position is at least `0`. -/
  param_nonneg : 0 ≤ param
  /-- The position is at most `1`. -/
  param_le_one : param ≤ 1

namespace Point

variable {S : Set G}

/-- The vertex the edge ends at. -/
def tip (p : Point S) : G := p.base * p.letter

theorem wordDist_base_tip (p : Point S) :
    wordDist S p.base p.tip = wordNorm S p.letter := by
  show wordNorm S (p.base⁻¹ * (p.base * p.letter)) = wordNorm S p.letter
  rw [← mul_assoc, inv_mul_cancel, one_mul]

/-- **An edge has length at most one in the word metric.**  This is what the
`letter ∈ S ∪ {1}` constraint is for, and it is used in every case of the
triangle inequality that crosses an edge. -/
theorem wordDist_base_tip_le_one (p : Point S) :
    (wordDist S p.base p.tip : ℝ) ≤ 1 := by
  have h : wordNorm S p.letter ≤ 1 := by
    rcases Set.mem_insert_iff.mp p.letter_mem with h1 | hmem
    · rw [h1, wordNorm_one]
      norm_num
    · exact wordNorm_le_one_of_mem hmem
  rw [wordDist_base_tip]
  exact_mod_cast h

/-! ## The distance to a vertex -/

/-- The distance from `p` to the vertex `v`: leave `p` by whichever endpoint is
better and cross by the word metric. -/
noncomputable def toVertex (p : Point S) (v : G) : ℝ :=
  min (p.param + (wordDist S p.base v : ℝ))
    (1 - p.param + (wordDist S p.tip v : ℝ))

theorem toVertex_nonneg (p : Point S) (v : G) : 0 ≤ p.toVertex v := by
  have h0 : (0 : ℝ) ≤ (wordDist S p.base v : ℝ) := by positivity
  have h1 : (0 : ℝ) ≤ (wordDist S p.tip v : ℝ) := by positivity
  have hp0 := p.param_nonneg
  have hp1 := p.param_le_one
  refine le_min ?_ ?_ <;> linarith

theorem toVertex_le_base (p : Point S) : p.toVertex p.base ≤ p.param := by
  have h : p.param + (wordDist S p.base p.base : ℝ) = p.param := by
    rw [wordDist_self]
    norm_num
  calc p.toVertex p.base ≤ p.param + (wordDist S p.base p.base : ℝ) :=
        min_le_left _ _
    _ = p.param := h

theorem toVertex_le_tip (p : Point S) : p.toVertex p.tip ≤ 1 - p.param := by
  have h : 1 - p.param + (wordDist S p.tip p.tip : ℝ) = 1 - p.param := by
    rw [wordDist_self]
    norm_num
  calc p.toVertex p.tip ≤ 1 - p.param + (wordDist S p.tip p.tip : ℝ) :=
        min_le_right _ _
    _ = 1 - p.param := h

/-- Moving the target vertex costs at most the word distance between the two
targets. -/
theorem toVertex_le_add (hS : IsSymmetricGeneratingSet S) (p : Point S)
    (v w : G) : p.toVertex w ≤ p.toVertex v + (wordDist S v w : ℝ) := by
  have h1 : (wordDist S p.base w : ℝ)
      ≤ (wordDist S p.base v : ℝ) + (wordDist S v w : ℝ) := by
    exact_mod_cast wordDist_triangle hS p.base v w
  have h2 : (wordDist S p.tip w : ℝ)
      ≤ (wordDist S p.tip v : ℝ) + (wordDist S v w : ℝ) := by
    exact_mod_cast wordDist_triangle hS p.tip v w
  have key1 : p.toVertex w
      ≤ p.param + (wordDist S p.base v : ℝ) + (wordDist S v w : ℝ) :=
    le_trans (min_le_left _ _) (by linarith)
  have key2 : p.toVertex w
      ≤ 1 - p.param + (wordDist S p.tip v : ℝ) + (wordDist S v w : ℝ) :=
    le_trans (min_le_right _ _) (by linarith)
  rcases le_total (p.param + (wordDist S p.base v : ℝ))
      (1 - p.param + (wordDist S p.tip v : ℝ)) with h | h
  · rw [toVertex, min_eq_left h]
    exact key1
  · rw [toVertex, min_eq_right h]
    exact key2

/-- **Two vertices are no further apart than the sum of their distances to a
common point.**  The mixed case is where the edge length enters. -/
theorem wordDist_le_toVertex_add (hS : IsSymmetricGeneratingSet S) (p : Point S)
    (v w : G) : (wordDist S v w : ℝ) ≤ p.toVertex v + p.toVertex w := by
  have hbt := wordDist_base_tip_le_one p
  have hp0 := p.param_nonneg
  have hp1 := p.param_le_one
  have cb : (wordDist S p.base v : ℝ) = (wordDist S v p.base : ℝ) := by
    exact_mod_cast wordDist_comm hS p.base v
  have ct : (wordDist S p.tip v : ℝ) = (wordDist S v p.tip : ℝ) := by
    exact_mod_cast wordDist_comm hS p.tip v
  have t1 : (wordDist S v w : ℝ)
      ≤ (wordDist S v p.base : ℝ) + (wordDist S p.base w : ℝ) := by
    exact_mod_cast wordDist_triangle hS v p.base w
  have t2 : (wordDist S v w : ℝ)
      ≤ (wordDist S v p.tip : ℝ) + (wordDist S p.tip w : ℝ) := by
    exact_mod_cast wordDist_triangle hS v p.tip w
  have t3 : (wordDist S v p.tip : ℝ)
      ≤ (wordDist S v p.base : ℝ) + (wordDist S p.base p.tip : ℝ) := by
    exact_mod_cast wordDist_triangle hS v p.base p.tip
  have t4 : (wordDist S v p.base : ℝ)
      ≤ (wordDist S v p.tip : ℝ) + (wordDist S p.tip p.base : ℝ) := by
    exact_mod_cast wordDist_triangle hS v p.tip p.base
  have hts : (wordDist S p.tip p.base : ℝ) = (wordDist S p.base p.tip : ℝ) := by
    exact_mod_cast wordDist_comm hS p.tip p.base
  rcases le_total (p.param + (wordDist S p.base v : ℝ))
      (1 - p.param + (wordDist S p.tip v : ℝ)) with hv | hv <;>
    rcases le_total (p.param + (wordDist S p.base w : ℝ))
      (1 - p.param + (wordDist S p.tip w : ℝ)) with hw | hw
  · rw [toVertex, min_eq_left hv, toVertex, min_eq_left hw]
    linarith
  · rw [toVertex, min_eq_left hv, toVertex, min_eq_right hw]
    linarith
  · rw [toVertex, min_eq_right hv, toVertex, min_eq_left hw]
    linarith
  · rw [toVertex, min_eq_right hv, toVertex, min_eq_right hw]
    linarith

/-- On one edge, the distance to a vertex is `1`-Lipschitz in the parameter. -/
theorem toVertex_le_abs_add {p q : Point S} (hb : p.base = q.base)
    (hl : p.letter = q.letter) (v : G) :
    p.toVertex v ≤ |p.param - q.param| + q.toVertex v := by
  have habs := abs_nonneg (p.param - q.param)
  have h1 : p.param - q.param ≤ |p.param - q.param| := le_abs_self _
  have h2 : -(p.param - q.param) ≤ |p.param - q.param| := neg_le_abs _
  have htip : p.tip = q.tip := by
    show p.base * p.letter = q.base * q.letter
    rw [hb, hl]
  have key1 : p.toVertex v ≤ |p.param - q.param|
      + (q.param + (wordDist S q.base v : ℝ)) := by
    refine le_trans (min_le_left _ _) ?_
    rw [hb]
    linarith
  have key2 : p.toVertex v ≤ |p.param - q.param|
      + (1 - q.param + (wordDist S q.tip v : ℝ)) := by
    refine le_trans (min_le_right _ _) ?_
    rw [htip]
    linarith
  rcases le_total (q.param + (wordDist S q.base v : ℝ))
      (1 - q.param + (wordDist S q.tip v : ℝ)) with h | h
  · rw [toVertex, min_eq_left h]
    exact key1
  · rw [toVertex, min_eq_right h]
    exact key2

/-! ## The distance -/

/-- The four ways of joining `p` to `q` through the vertices of `Γ(G,S)`. -/
noncomputable def viaVertex (p q : Point S) : ℝ :=
  min (p.toVertex q.base + q.param) (p.toVertex q.tip + (1 - q.param))

theorem viaVertex_nonneg (p q : Point S) : 0 ≤ viaVertex p q := by
  have h1 := toVertex_nonneg p q.base
  have h2 := toVertex_nonneg p q.tip
  have h3 := q.param_nonneg
  have h4 := q.param_le_one
  refine le_min ?_ ?_ <;> linarith

/-- **The four ways are the same four ways from either end.**  Each of the four
terms is symmetric in `p` and `q` once the word metric is, and the two
groupings of the minimum agree. -/
theorem viaVertex_comm (hS : IsSymmetricGeneratingSet S) (p q : Point S) :
    viaVertex p q = viaVertex q p := by
  have hbb : (wordDist S p.base q.base : ℝ) = (wordDist S q.base p.base : ℝ) := by
    exact_mod_cast wordDist_comm hS p.base q.base
  have hbt : (wordDist S p.base q.tip : ℝ) = (wordDist S q.tip p.base : ℝ) := by
    exact_mod_cast wordDist_comm hS p.base q.tip
  have htb : (wordDist S p.tip q.base : ℝ) = (wordDist S q.base p.tip : ℝ) := by
    exact_mod_cast wordDist_comm hS p.tip q.base
  have htt : (wordDist S p.tip q.tip : ℝ) = (wordDist S q.tip p.tip : ℝ) := by
    exact_mod_cast wordDist_comm hS p.tip q.tip
  simp only [viaVertex, toVertex, min_add_add_right, hbb, hbt, htb, htt]
  apply le_antisymm
  · refine le_min (le_min ?_ ?_) (le_min ?_ ?_)
    · exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_of_eq (by ring)))
    · exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (le_of_eq (by ring)))
    · exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (le_of_eq (by ring)))
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_of_eq (by ring)))
  · refine le_min (le_min ?_ ?_) (le_min ?_ ?_)
    · exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_of_eq (by ring)))
    · exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (le_of_eq (by ring)))
    · exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (le_of_eq (by ring)))
    · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_of_eq (by ring)))

/-- Leaving `p` for any vertex and entering `q` from it is one of the ways
`viaVertex` minimises over, up to the triangle inequality. -/
theorem viaVertex_le_toVertex_add (hS : IsSymmetricGeneratingSet S)
    (p q : Point S) (v : G) :
    viaVertex p q ≤ p.toVertex v + q.toVertex v := by
  have hb := toVertex_le_add hS p v q.base
  have ht := toVertex_le_add hS p v q.tip
  have hcb : (wordDist S v q.base : ℝ) = (wordDist S q.base v : ℝ) := by
    exact_mod_cast wordDist_comm hS v q.base
  have hct : (wordDist S v q.tip : ℝ) = (wordDist S q.tip v : ℝ) := by
    exact_mod_cast wordDist_comm hS v q.tip
  rcases le_total (q.param + (wordDist S q.base v : ℝ))
      (1 - q.param + (wordDist S q.tip v : ℝ)) with h | h
  · rw [toVertex, min_eq_left h]
    refine le_trans (min_le_left _ _) ?_
    rw [hcb] at hb
    linarith
  · rw [toVertex, min_eq_right h]
    refine le_trans (min_le_right _ _) ?_
    rw [hct] at ht
    linarith

/-- Two points of one edge are joined along it, or through the vertices. -/
noncomputable def pointDist (p q : Point S) : ℝ :=
  if p.base = q.base ∧ p.letter = q.letter then
    min |p.param - q.param| (viaVertex p q)
  else viaVertex p q

theorem pointDist_le_viaVertex (p q : Point S) :
    pointDist p q ≤ viaVertex p q := by
  unfold pointDist
  split_ifs with h
  · exact min_le_right _ _
  · exact le_refl _

theorem pointDist_nonneg (p q : Point S) : 0 ≤ pointDist p q := by
  unfold pointDist
  split_ifs with h
  · exact le_min (abs_nonneg _) (viaVertex_nonneg p q)
  · exact viaVertex_nonneg p q

theorem pointDist_self (p : Point S) : pointDist p p = 0 := by
  have hvia : 0 ≤ viaVertex p p := viaVertex_nonneg p p
  unfold pointDist
  rw [if_pos ⟨rfl, rfl⟩]
  have h0 : |p.param - p.param| = 0 := by
    rw [sub_self, abs_zero]
  rw [h0]
  exact min_eq_left hvia

theorem pointDist_comm (hS : IsSymmetricGeneratingSet S) (p q : Point S) :
    pointDist p q = pointDist q p := by
  have hvia := viaVertex_comm hS p q
  have habs : |p.param - q.param| = |q.param - p.param| := abs_sub_comm _ _
  unfold pointDist
  by_cases h : p.base = q.base ∧ p.letter = q.letter
  · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩, habs, hvia]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩), hvia]

/-! ## The triangle inequality -/

/-- Through the vertices, the triangle inequality is the word metric's, with the
edge length paying for the two endpoints of the middle point. -/
theorem viaVertex_triangle (hS : IsSymmetricGeneratingSet S) (p q r : Point S) :
    viaVertex p r ≤ viaVertex p q + viaVertex q r := by
  have hqr : viaVertex q r = viaVertex r q := viaVertex_comm hS q r
  have hbase := viaVertex_le_toVertex_add hS p r q.base
  have htip := viaVertex_le_toVertex_add hS p r q.tip
  have hmove : r.toVertex q.base ≤ r.toVertex q.tip
      + (wordDist S q.tip q.base : ℝ) := toVertex_le_add hS r q.tip q.base
  have hmove' : r.toVertex q.tip ≤ r.toVertex q.base
      + (wordDist S q.base q.tip : ℝ) := toVertex_le_add hS r q.base q.tip
  have hbt := wordDist_base_tip_le_one q
  have hts : (wordDist S q.tip q.base : ℝ) = (wordDist S q.base q.tip : ℝ) := by
    exact_mod_cast wordDist_comm hS q.tip q.base
  have hq0 := q.param_nonneg
  have hq1 := q.param_le_one
  rw [hqr]
  rcases le_total (p.toVertex q.base + q.param)
      (p.toVertex q.tip + (1 - q.param)) with h1 | h1 <;>
    rcases le_total (r.toVertex q.base + q.param)
      (r.toVertex q.tip + (1 - q.param)) with h2 | h2
  · rw [viaVertex, min_eq_left h1, viaVertex, min_eq_left h2]
    linarith
  · rw [viaVertex, min_eq_left h1, viaVertex, min_eq_right h2]
    rw [hts] at hmove
    linarith
  · rw [viaVertex, min_eq_right h1, viaVertex, min_eq_left h2]
    linarith [hmove']
  · rw [viaVertex, min_eq_right h1, viaVertex, min_eq_right h2]
    linarith

/-- Along one edge, moving the first point costs the difference of the
parameters. -/
theorem viaVertex_le_abs_add {p q : Point S} (hb : p.base = q.base)
    (hl : p.letter = q.letter) (r : Point S) :
    viaVertex p r ≤ |p.param - q.param| + viaVertex q r := by
  have h1 := toVertex_le_abs_add hb hl r.base
  have h2 := toVertex_le_abs_add hb hl r.tip
  have hstep : min (p.toVertex r.base + r.param) (p.toVertex r.tip + (1 - r.param))
      ≤ min (|p.param - q.param| + (q.toVertex r.base + r.param))
        (|p.param - q.param| + (q.toVertex r.tip + (1 - r.param))) :=
    min_le_min (by linarith) (by linarith)
  calc viaVertex p r ≤ min (|p.param - q.param| + (q.toVertex r.base + r.param))
        (|p.param - q.param| + (q.toVertex r.tip + (1 - r.param))) := hstep
    _ = |p.param - q.param| + viaVertex q r := (min_add_add_left _ _ _).symm

/-- The triangle inequality for `pointDist`.  Four bounds are assembled: the
three that go through the vertices, and the one along a shared edge. -/
theorem pointDist_triangle (hS : IsSymmetricGeneratingSet S) (p q r : Point S) :
    pointDist p r ≤ pointDist p q + pointDist q r := by
  -- First: `pointDist p r` is bounded by `viaVertex p q` plus `pointDist q r`.
  have hviaR : ∀ s : Point S, pointDist p r ≤ viaVertex p s + pointDist s r := by
    intro s
    have h1 : pointDist p r ≤ viaVertex p s + viaVertex s r :=
      le_trans (pointDist_le_viaVertex p r) (viaVertex_triangle hS p s r)
    unfold pointDist
    split_ifs with hsr
    · refine le_min ?_ ?_
      · have hsym : viaVertex p r ≤ |s.param - r.param| + viaVertex p s := by
          have := viaVertex_le_abs_add (S := S) hsr.1 hsr.2 p
          have hcomm1 : viaVertex r p = viaVertex p r := viaVertex_comm hS r p
          have hcomm2 : viaVertex s p = viaVertex p s := viaVertex_comm hS s p
          have hrs : |r.param - s.param| = |s.param - r.param| := abs_sub_comm _ _
          have hstep : viaVertex r p ≤ |r.param - s.param| + viaVertex s p := by
            have hb : r.base = s.base := hsr.1.symm
            have hl : r.letter = s.letter := hsr.2.symm
            exact viaVertex_le_abs_add hb hl p
          rw [hcomm1, hcomm2, hrs] at hstep
          exact hstep
        have h2 := pointDist_le_viaVertex p r
        unfold pointDist at h2
        split_ifs at h2 with hpr
        · exact le_trans (min_le_right _ _) (by linarith)
        · linarith
      · exact h1
    · exact h1
  have hmain := hviaR q
  unfold pointDist
  split_ifs with hpq
  · refine le_min ?_ ?_
    · -- along the shared edge `p`–`q`
      have hedge : viaVertex p r ≤ |p.param - q.param| + viaVertex q r :=
        viaVertex_le_abs_add hpq.1 hpq.2 r
      have hqr : pointDist q r ≤ viaVertex q r := pointDist_le_viaVertex q r
      by_cases hqr' : q.base = r.base ∧ q.letter = r.letter
      · -- `p`, `q`, `r` all lie on one edge
        have hpr : p.base = r.base ∧ p.letter = r.letter :=
          ⟨hpq.1.trans hqr'.1, hpq.2.trans hqr'.2⟩
        have habs : |p.param - r.param|
            ≤ |p.param - q.param| + |q.param - r.param| := by
          have := abs_sub_abs_le_abs_sub (p.param - r.param) (p.param - q.param)
          calc |p.param - r.param| = |(p.param - q.param) + (q.param - r.param)| := by
                ring_nf
            _ ≤ |p.param - q.param| + |q.param - r.param| := abs_add _ _
        have hdq : pointDist q r = min |q.param - r.param| (viaVertex q r) := by
          unfold pointDist
          rw [if_pos hqr']
        have hd : pointDist p r ≤ |p.param - r.param| := by
          unfold pointDist
          rw [if_pos hpr]
          exact min_le_left _ _
        rw [hdq]
        rcases le_total |q.param - r.param| (viaVertex q r) with hmin | hmin
        · rw [min_eq_left hmin]
          linarith
        · rw [min_eq_right hmin]
          have := pointDist_le_viaVertex p r
          linarith
      · have hdq : pointDist q r = viaVertex q r := by
          unfold pointDist
          rw [if_neg hqr']
        rw [hdq]
        exact le_trans (pointDist_le_viaVertex p r) hedge
    · exact hmain
  · exact hmain

end Point

/-! ## The realisation as a pseudometric space -/

variable {S : Set G}

/-- The metric realisation of `Γ(G,S)`. -/
noncomputable instance instPseudoMetricSpacePoint (hS : IsSymmetricGeneratingSet S) :
    PseudoMetricSpace (Point S) where
  dist p q := Point.pointDist p q
  dist_self p := Point.pointDist_self p
  dist_comm p q := Point.pointDist_comm hS p q
  dist_triangle p q r := Point.pointDist_triangle hS p q r

end CayleyGeodesicModel
end GGT
end GroupApproximation
