import GroupApproximation.Sofic.HullSuitabilityGeometry

/-!
# Metric betweenness, and the comparison of two geodesics leaving a point

Second module of the windmill campaign aimed at
`Manuscript.NonMF.TheoremCDebts.dgoTheorem53` (DGO's Theorem 5.3(b)).

DGO's §5.1.2 is written in the language of chosen geodesic segments: *"consider
`q₁ ∈ [c,x]` and `q₂ ∈ [c,y]` at distance `28δ` from `c`"*, and their induction
concatenates such segments into broken paths.  Formalising that literally means
carrying parametrisations `ℝ → X` through every step and splicing them, which
in a `PseudoMetricSpace` also has a degenerate case: a concatenation
`fun t => if t ≤ D₁ then f t else g (t - D₁)` cannot be proved to end at `z`
when `dist y z = 0` and `y ≠ z`.

The whole campaign avoids that by carrying **metric betweenness** instead:
`Between c z x` says `d(c,x) = d(c,z) + d(z,x)`.  It is what "`z` is on a
geodesic from `c` to `x`" gives, it is transitive by three uses of the triangle
inequality, and it is preserved by every step of the induction.  A geodesic is
then produced only where a genuine triangle is needed --- inside the sharp-corner
lemma --- and never spliced.

## What is proved

* `between_of_mem_geodesic` / `exists_between_dist_eq` --- betweenness comes from
  a geodesic, and in a geodesic space the point at any prescribed radius exists.
  This is the "`q₁` at distance `30δ` from `c`" of every estimate downstream.
* `Between.trans_left`, `Between.trans_right` --- the two compositions the
  broken-path induction performs.
* `gromovProduct_eq_of_between` --- `(z|x)_c = d(c,z)` for `z` between `c` and
  `x`.  Every four-point computation in the campaign starts here.
* `dist_le_four_delta_of_between` --- **the comparison lemma**: two points at the
  same distance `r` from `c`, lying between `c` and `a` respectively `c` and
  `b`, are `4δ` apart as soon as `(a|b)_c ≥ r`.  Pure four-point algebra, no
  thin triangles, and it replaces the `δ`-close comparison DGO read off a
  tripod.  It is used three times: to transfer the radius-`30δ` points of
  `[c,x₁]` and `[c,x₂]` onto a geodesic `[x₁,x₂]`, to prove that a nontrivial
  rotation fixes nothing far from its apex, and to compare a geodesic with its
  rotate.
* `eq_of_dist_eq_zero_of_geodesic` --- a geodesic space is separated even when
  its metric is only a pseudometric, because `IsGeodesicSpace` demands the
  endpoint equations `f 0 = x` and `f (dist x y) = y` on the nose.  Recorded
  once so that no later module has to worry about the degenerate case again.

## The constant is `4δ`, not `δ`

`HullGeometry.IsHyperbolicSpace δ` is the four-point condition.  Two
applications of it give `(p|q)_c ≥ r - 2δ` where a tripod would give
`(p|q)_c ≥ r`, and `d(p,q) = 2r - 2(p|q)_c` turns that into `4δ`.  DGO's
printed `δ` is a thin-triangle constant and is not available here; the
downstream estimates are re-derived with `4δ` rather than transcribed.
-/

namespace GroupApproximation
namespace DGOWindmill

open GroupApproximation.HullGeometry

universe v

variable {X : Type v} [PseudoMetricSpace X]

/-! ## Betweenness -/

/-- **`z` lies metrically between `c` and `x`**: the triangle inequality through
`z` is an equality.  This is DGO's "`z ∈ [c,x]`", weakened to the statement
about distances that every one of their estimates actually uses. -/
def Between (c z x : X) : Prop := dist c x = dist c z + dist z x

theorem Between.dist_le_left {c z x : X} (h : Between c z x) : dist c z ≤ dist c x := by
  have hnn : (0 : ℝ) ≤ dist z x := dist_nonneg
  unfold Between at h
  linarith

theorem Between.dist_le_right {c z x : X} (h : Between c z x) :
    dist z x ≤ dist c x := by
  have hnn : (0 : ℝ) ≤ dist c z := dist_nonneg
  unfold Between at h
  linarith

/-- **Betweenness is symmetric in its two ends.**  `d(c,x) = d(c,z) + d(z,x)`
and `d(x,c) = d(x,z) + d(z,c)` are the same equation read through `dist_comm`.

Used at every corner: the induction establishes betweenness looking outward from
an apex and the comparison lemma consumes it looking inward from the far
endpoint. -/
theorem Between.symm {c z x : X} (h : Between c z x) : Between x z c := by
  unfold Between at h ⊢
  rw [dist_comm x c, dist_comm x z, dist_comm z c]
  linarith

/-- The distance from the far end, for a point between two others. -/
theorem Between.dist_far {c z x : X} (h : Between c z x) :
    dist z x = dist c x - dist c z := by
  unfold Between at h
  linarith

theorem between_self_left (c x : X) : Between c c x := by
  unfold Between
  rw [dist_self, zero_add]

theorem between_self_right (c x : X) : Between c x x := by
  unfold Between
  rw [dist_self, add_zero]

/-- **Betweenness composes towards the far end.**  If `z` is between `c` and `x`
and `w` is between `z` and `x`, then `w` is between `c` and `x` and `z` is
between `c` and `w`.

The broken-path induction uses this to extend an established equality one apex
further along. -/
theorem Between.trans_right {c z w x : X} (h1 : Between c z x)
    (h2 : Between z w x) : Between c w x := by
  unfold Between at h1 h2 ⊢
  have hcw : dist c w ≤ dist c z + dist z w := dist_triangle c z w
  have hlow : dist c x ≤ dist c w + dist w x := dist_triangle c w x
  linarith

/-- **Betweenness composes towards the near end.**  If `z` is between `c` and
`x` and `p` is between `c` and `z`, then `p` is between `c` and `x`.

This is the step that lets the corner lemma take its radius-`30δ` point on a
geodesic from `c` to a nearby anchor `z` and still know it lies between `c` and
the far endpoint `x`. -/
theorem Between.trans_left {c p z x : X} (h1 : Between c z x)
    (h2 : Between c p z) : Between c p x := by
  unfold Between at h1 h2 ⊢
  have hpx : dist p x ≤ dist p z + dist z x := dist_triangle p z x
  have hlow : dist c x ≤ dist c p + dist p x := dist_triangle c p x
  linarith

/-! ## Betweenness from geodesics -/

/-- A point of a geodesic from `c` to `x` lies between `c` and `x`. -/
theorem between_of_mem_geodesic {c x : X} {f : ℝ → X} {r : ℝ}
    (hf : IsGeodesicSegment f 0 (dist c x)) (hf0 : f 0 = c)
    (hf1 : f (dist c x) = x) (hr : r ∈ Set.Icc (0 : ℝ) (dist c x)) :
    dist c (f r) = r ∧ Between c (f r) x := by
  have hD : (0 : ℝ) ≤ dist c x := dist_nonneg
  have h1 := hf r hr 0 ⟨le_refl 0, hD⟩
  have h2 := hf r hr (dist c x) ⟨hD, le_refl _⟩
  rw [hf0, sub_zero, abs_of_nonneg hr.1] at h1
  rw [hf1, abs_of_nonpos (by linarith [hr.2])] at h2
  have h3 : dist c (f r) = r := by rw [dist_comm]; exact h1
  refine ⟨h3, ?_⟩
  unfold Between
  linarith

/-- **The point at a prescribed radius.**  In a geodesic space, for `0 ≤ r ≤
d(c,x)` there is a point at distance exactly `r` from `c` lying between `c` and
`x`.

This is `HullSC.exists_mem_annulus`'s mechanism, stated once with the
betweenness the campaign needs alongside the radius. -/
theorem exists_between_dist_eq (hgeo : IsGeodesicSpace X) (c x : X) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r ≤ dist c x) :
    ∃ p : X, dist c p = r ∧ Between c p x := by
  obtain ⟨f, hf, hf0, hf1⟩ := hgeo c x
  exact ⟨f r, between_of_mem_geodesic hf hf0 hf1 ⟨hr0, hr⟩⟩

/-- **A geodesic space is separated.**  `IsGeodesicSpace` asks for `f 0 = x` and
`f (dist x y) = y` as equations, so at `dist x y = 0` both name `f 0` and the
two points coincide -- even though the ambient structure is only a
`PseudoMetricSpace`.

Recorded because the campaign's induction repeatedly needs to turn a distance
bound into a disequality of apices, and without this the degenerate case would
have to be carried through every statement. -/
theorem eq_of_dist_eq_zero_of_geodesic (hgeo : IsGeodesicSpace X) {x y : X}
    (h : dist x y = 0) : x = y := by
  obtain ⟨f, -, hf0, hf1⟩ := hgeo x y
  rw [h] at hf1
  rw [← hf0]
  exact hf1

/-! ## Gromov products along a betweenness -/

/-- **`(z|x)_c = d(c,z)` for `z` between `c` and `x`.**  The Gromov product sees
no slack along a geodesic. -/
theorem gromovProduct_eq_of_between {c z x : X} (h : Between c z x) :
    gromovProduct z x c = dist c z := by
  unfold Between at h
  unfold gromovProduct
  rw [dist_comm z c, dist_comm x c, h]
  ring

/-- The Gromov product read off a distance: `d(p,q) = d(c,p) + d(c,q) - 2(p|q)_c`. -/
theorem dist_eq_of_gromovProduct (c p q : X) :
    dist p q = dist c p + dist c q - 2 * gromovProduct p q c := by
  unfold gromovProduct
  rw [dist_comm c p, dist_comm c q]
  ring

/-! ## The comparison lemma -/

/-- **Two geodesics leaving `c` stay `4δ`-close out to their Gromov product.**

If `p` is between `c` and `a`, `q` is between `c` and `b`, both at distance `r`
from `c`, and `(a|b)_c ≥ r`, then `d(p,q) ≤ 4δ`.

Two applications of the four-point condition based at `c`:
`(a|q)_c ≥ min((a|b)_c, (b|q)_c) - δ = r - δ` and then
`(p|q)_c ≥ min((p|a)_c, (a|q)_c) - δ ≥ r - 2δ`, and
`d(p,q) = 2r - 2(p|q)_c ≤ 4δ`.

DGO read the corresponding statement off a tripod and pay `δ`; four-point
hyperbolicity pays `4δ`, and every constant downstream is recomputed with `4δ`
rather than transcribed from the paper. -/
theorem dist_le_four_delta_of_between {δ : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hδ0 : 0 ≤ δ) {c a b p q : X} {r : ℝ}
    (hp : Between c p a) (hpr : dist c p = r)
    (hq : Between c q b) (hqr : dist c q = r)
    (hab : r ≤ gromovProduct a b c) : dist p q ≤ 4 * δ := by
  have hpa : gromovProduct p a c = r := by
    rw [gromovProduct_eq_of_between hp, hpr]
  have hqb : gromovProduct q b c = r := by
    rw [gromovProduct_eq_of_between hq, hqr]
  have hbq : gromovProduct b q c = r := by
    rw [gromovProduct_comm b q c]; exact hqb
  have h1 := hδ c a b q
  have h2 := hδ c p a q
  have hmin1 : min (gromovProduct a b c) (gromovProduct b q c) = r := by
    rw [hbq]; exact min_eq_right hab
  rw [hmin1] at h1
  have hmin2 : r - δ ≤ min (gromovProduct p a c) (gromovProduct a q c) := by
    rw [hpa]
    exact le_min (by linarith) (by linarith)
  have h3 : r - 2 * δ ≤ gromovProduct p q c := by linarith
  have hexp := dist_eq_of_gromovProduct c p q
  linarith

/-- **The comparison lemma at a common far endpoint.**  Two points between `c`
and `a` respectively between `c` and `b`, at the same distance from `c`, when
`a` and `b` are the same point: `(a|a)_c = d(c,a)`, so the hypothesis is just
`r ≤ d(c,a)`.

This is the form used to show a nontrivial rotation moves every point far from
its apex: a fixed point `z` would give two geodesics `[c,z]` and `g·[c,z]` with
the same endpoints. -/
theorem dist_le_four_delta_of_between_same {δ : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hδ0 : 0 ≤ δ) {c a p q : X} {r : ℝ}
    (hp : Between c p a) (hpr : dist c p = r)
    (hq : Between c q a) (hqr : dist c q = r) : dist p q ≤ 4 * δ := by
  refine dist_le_four_delta_of_between hδ hδ0 hp hpr hq hqr ?_
  rw [gromovProduct_self a c, dist_comm a c]
  rw [← hpr]
  exact Between.dist_le_left hp

end DGOWindmill
end GroupApproximation
