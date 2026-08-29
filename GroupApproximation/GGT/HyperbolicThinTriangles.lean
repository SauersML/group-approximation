import GroupApproximation.Sofic.HullSuitabilityGeometry

/-!
# Thin triangles, in the shape fp-geometry applies them

`HullGeometry.exists_close_on_other_side_of_geodesic_triangle` already proves
that geodesic triangles in a `δ`-hyperbolic space are `3δ`-thin, and proves it
with the constant derived rather than assumed: at a point of the `A–C` side the
Gromov product `(A|C)` is zero, the four-point condition makes one of `(A|B)`
and `(B|C)` at most `δ`, and `exists_mem_geodesic_dist_le` -- the
product-to-geodesic dictionary -- costs a further `2δ`.  That is the classical
implication (Bridson-Haefliger III.H.1.17, Ghys-de la Harpe), and nothing below
reproves it.

This module only changes its shape.  Four differences were asked for, and each
is bookkeeping over the existing theorem:

* the constant is produced once, as `∃ K`, outside the quantification over
  triangles.  `K = 3δ` depends on `δ` and on nothing else, which is what a
  consumer applying it to triangles of unbounded size needs;
* the sides are parametrised on `[0, L]` for a free `L` rather than on
  `[0, dist _ _]`.  That is not a weakening: `IsGeodesicSegment f 0 L` with
  `f 0 = x` and `f L = y` forces `L = dist x y` (`IsGeodesicSegment.dist_endpoints`),
  so the two forms carry the same content and the free `L` merely saves the
  caller a rewrite;
* the third side runs `y → z`, where the existing theorem takes it as `z → y`.
  `IsGeodesicSegment.reverse` turns one into the other;
* the conclusion is a disjunction of two existentials rather than membership in
  a neighbourhood of a union, so it can be cased on directly.

## What it does not need

No geodesicity of `X`, no properness, and `0 ≤ δ` rather than `0 < δ`.  The
three sides are supplied by the caller, so the theorem says nothing about
geodesics existing; a caller with a bigon supplies the degenerate third side
(`z = y`, `L₃ = 0`, `f₃` constant) and the statement applies unchanged.  The
carrier is a `PseudoMetricSpace`, as `HullGeometry.IsHyperbolicSpace` is.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry

universe v

/-- **Geodesic triangles are `3δ`-thin, at an explicit constant.**

The whole of the work: the sides are parametrised on `[0, L]` for free `L`, the
third runs `y → z`, and the constant is `3δ` rather than hidden behind an
existential.  `geodesicTriangle_thin` packages it as fp-geometry consumes it,
and `geodesicTriangle_thin_zero` reads it at `δ = 0`.

Nothing here reproves hyperbolicity: the content is
`HullGeometry.exists_close_on_other_side_of_geodesic_triangle`, and the three
steps below are the change of parametrisation. -/
theorem geodesicTriangle_thin_const {X : Type v} [PseudoMetricSpace X] {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (x y z : X) (L₁ L₂ L₃ : ℝ) (f₁ f₂ f₃ : ℝ → X)
    (h1 : 0 ≤ L₁) (h2 : 0 ≤ L₂) (h3 : 0 ≤ L₃)
    (hg1 : IsGeodesicSegment f₁ 0 L₁) (hx1 : f₁ 0 = x) (hy1 : f₁ L₁ = y)
    (hg2 : IsGeodesicSegment f₂ 0 L₂) (hx2 : f₂ 0 = x) (hz2 : f₂ L₂ = z)
    (hg3 : IsGeodesicSegment f₃ 0 L₃) (hy3 : f₃ 0 = y) (hz3 : f₃ L₃ = z)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) L₁) :
    (∃ s ∈ Set.Icc (0 : ℝ) L₂, dist (f₁ t) (f₂ s) ≤ 3 * δ) ∨
    (∃ s ∈ Set.Icc (0 : ℝ) L₃, dist (f₁ t) (f₃ s) ≤ 3 * δ) := by
  -- each side length is the distance between its endpoints
  have hL1 : dist x y = L₁ := by
    have h := IsGeodesicSegment.dist_endpoints h1 hg1
    rw [hx1, hy1] at h
    linarith
  have hL2 : dist x z = L₂ := by
    have h := IsGeodesicSegment.dist_endpoints h2 hg2
    rw [hx2, hz2] at h
    linarith
  have hL3 : dist y z = L₃ := by
    have h := IsGeodesicSegment.dist_endpoints h3 hg3
    rw [hy3, hz3] at h
    linarith
  subst hL1
  subst hL2
  subst hL3
  -- the third side, reversed to run from `z` to `y` as the cited theorem wants
  have hzy : dist z y = dist y z := dist_comm z y
  have hg3' : IsGeodesicSegment (fun s => f₃ (dist y z - s)) 0 (dist z y) := by
    rw [hzy]
    exact IsGeodesicSegment.reverse hg3
  have hb0 : (fun s => f₃ (dist y z - s)) 0 = z := by
    simpa using hz3
  have hb1 : (fun s => f₃ (dist y z - s)) (dist z y) = y := by
    rw [hzy]
    simpa using hy3
  rcases exists_close_on_other_side_of_geodesic_triangle hδ hδ0
      hg1 hx1 hy1 hg2 hx2 hz2 hg3' hb0 hb1 ht with hleft | hright
  · exact Or.inl hleft
  · obtain ⟨s, hs, hnear⟩ := hright
    rw [hzy] at hs
    refine Or.inr ⟨dist y z - s, ?_, hnear⟩
    exact ⟨by linarith [hs.2], by linarith [hs.1]⟩

/-- **Thin triangles, in the shape fp-geometry applies them.**

The constant is produced once, outside the quantification over triangles: `K`
depends on `δ` and on nothing else, which is what an application to triangles of
unbounded size needs.  Its value is `3 * δ`; a caller who needs the value rather
than its existence should use `geodesicTriangle_thin_const`.

The bigon is the case `z = y`, `L₃ = 0`, `f₃` constant. -/
theorem geodesicTriangle_thin {X : Type v} [PseudoMetricSpace X] {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (x y z : X) (L₁ L₂ L₃ : ℝ) (f₁ f₂ f₃ : ℝ → X),
        0 ≤ L₁ → 0 ≤ L₂ → 0 ≤ L₃ →
        IsGeodesicSegment f₁ 0 L₁ → f₁ 0 = x → f₁ L₁ = y →
        IsGeodesicSegment f₂ 0 L₂ → f₂ 0 = x → f₂ L₂ = z →
        IsGeodesicSegment f₃ 0 L₃ → f₃ 0 = y → f₃ L₃ = z →
        ∀ t ∈ Set.Icc (0 : ℝ) L₁,
          (∃ s ∈ Set.Icc (0 : ℝ) L₂, dist (f₁ t) (f₂ s) ≤ K) ∨
          (∃ s ∈ Set.Icc (0 : ℝ) L₃, dist (f₁ t) (f₃ s) ≤ K) :=
  ⟨3 * δ, by linarith, fun x y z L₁ L₂ L₃ f₁ f₂ f₃ h1 h2 h3 hg1 hx1 hy1 hg2 hx2
      hz2 hg3 hy3 hz3 _t ht =>
    geodesicTriangle_thin_const hδ hδ0 x y z L₁ L₂ L₃ f₁ f₂ f₃ h1 h2 h3
      hg1 hx1 hy1 hg2 hx2 hz2 hg3 hy3 hz3 ht⟩

/-- **The model test at `δ = 0`: the tripod property.**

A `0`-hyperbolic space has `0`-thin triangles, so every point of one side of a
geodesic triangle is at distance zero from a point of one of the other two --
in a metric space, ON one of the other two.  This is the tree case, and it is
the sanity check that the constant is not merely finite but degenerates
correctly.

The Euclidean test belongs at the definition rather than here: a Euclidean
triangle fails thinness because `ℝ²` fails `IsHyperbolicSpace δ` for small `δ`,
which is a statement about `HullGeometry.IsHyperbolicSpace` and not about this
theorem. -/
theorem geodesicTriangle_thin_zero {X : Type v} [PseudoMetricSpace X]
    (hδ : IsHyperbolicSpace 0 X)
    (x y z : X) (L₁ L₂ L₃ : ℝ) (f₁ f₂ f₃ : ℝ → X)
    (h1 : 0 ≤ L₁) (h2 : 0 ≤ L₂) (h3 : 0 ≤ L₃)
    (hg1 : IsGeodesicSegment f₁ 0 L₁) (hx1 : f₁ 0 = x) (hy1 : f₁ L₁ = y)
    (hg2 : IsGeodesicSegment f₂ 0 L₂) (hx2 : f₂ 0 = x) (hz2 : f₂ L₂ = z)
    (hg3 : IsGeodesicSegment f₃ 0 L₃) (hy3 : f₃ 0 = y) (hz3 : f₃ L₃ = z)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) L₁) :
    (∃ s ∈ Set.Icc (0 : ℝ) L₂, dist (f₁ t) (f₂ s) = 0) ∨
    (∃ s ∈ Set.Icc (0 : ℝ) L₃, dist (f₁ t) (f₃ s) = 0) := by
  rcases geodesicTriangle_thin_const hδ le_rfl x y z L₁ L₂ L₃ f₁ f₂ f₃
      h1 h2 h3 hg1 hx1 hy1 hg2 hx2 hz2 hg3 hy3 hz3 ht with hleft | hright
  · obtain ⟨s, hs, hnear⟩ := hleft
    refine Or.inl ⟨s, hs, le_antisymm ?_ dist_nonneg⟩
    linarith
  · obtain ⟨s, hs, hnear⟩ := hright
    refine Or.inr ⟨s, hs, le_antisymm ?_ dist_nonneg⟩
    linarith

end GGT
end GroupApproximation
