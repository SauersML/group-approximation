import GroupApproximation.GGT.DGOWindmillCorner

/-!
# Spoke sets: a windmill with segments attached to the new apices

Seventh module of the campaign aimed at
`Manuscript.NonMF.TheoremCDebts.dgoTheorem53` (DGO's Theorem 5.3(b)).

The growth step of DGO's Proposition 5.12 enlarges a windmill `W` in two stages.
The first is `W₁ = W ∪ ⋃_{c ∈ C₁} [c, c̄]`, the windmill together with a segment
from each new apex to a point of `W` near it.  This module builds that set and
proves the two facts the growth step needs of it.

## Why the segments cannot be dropped

They look like an artefact, and the campaign tried twice to do without them.
Both attempts fail, for the same reason and at the same inequality.

* Take `W₁ = W ∪ C₁`.  A geodesic between two new apices runs within `M + O(δ)`
  of `W ∪ C₁` and no closer, because its midpoint is far from both `W` and every
  apex.  So the unfolded windmill `W₂` is only `(M + O(δ))`-quasiconvex, while the
  gap that has to absorb that constant is `M - 55δ`.  There is no `M`.
* Take `W₁ = W^{+M}`, a fat neighbourhood.  Now the segments are inside it for
  free and `W₁` is `6δ`-quasiconvex, but an apex at distance `M + ε` from `W` is
  at distance `ε` from `W₁`, so the windmill's `far` clause is destroyed at the
  next stage.

The segments are exactly the object that is thin enough for apices to stay far
from it and fat enough to be quasiconvex with a constant independent of `M`.

## The formalisation: betweenness, not chosen segments

DGO choose, for each `c ∈ C₁`, a closest point `c̄ ∈ W`, and note that the choice
can be made `G_W`-equivariantly because `G_W` acts freely on `C₁`.  Neither the
closest point nor the equivariance is needed here.

* A closest point need not exist in a general metric space; a point within
  `M + δ` does, and that is all any estimate uses.
* The set is defined by a *membership condition* rather than as a union of chosen
  segments: `p` is in the spoke set when it lies metrically between some tip
  `e ∈ A` and some point `w ∈ W` with `d(e,w) ≤ r`.  So no choice function
  appears, the set is manifestly invariant under any isometry preserving `W` and
  `A`, and the equivariance DGO have to arrange is automatic.

## What is proved

* `isQuasiconvexSet_spokeSet` --- **a spoke set over a `6δ`-quasiconvex `W` is
  `12δ`-quasiconvex**, whatever the reach `r`.  The constant is independent of
  `r`, which is the whole point: one thin quadrilateral `p, w, w', p'` whose two
  outer sides lie in the spoke set outright and whose middle side lies in
  `W^{+6δ}`.
* `le_dist_of_mem_spokeSet` --- **a point far from `W` and `r`-further from every
  tip is far from the whole spoke set**.  This is what keeps the new apices away
  from `S_c`, and it needs no hyperbolicity at all: a point of a spoke is within
  `r` of its tip.
* `exists_foot_of_mem_spokeSet` --- every point of a spoke set has a *foot* in
  `W` with the whole segment back to it still inside the set.  This is the
  induction's handle on the set, and it is where `IsGeodesicSpace` is spent: for
  a point of `W` the foot is the point itself, and the argument needs
  `dist p q = 0 → p = q`, which `eq_of_dist_eq_zero_of_geodesic` supplies even
  though the ambient structure is a `PseudoMetricSpace`.
-/

namespace GroupApproximation
namespace DGOWindmill

open GroupApproximation.HullGeometry

universe v

variable {X : Type v} [PseudoMetricSpace X]

/-! ## The spoke set -/

/-- **`W` with a spoke attached at each tip.**  A point belongs when it is in `W`
or lies metrically between some tip `e ∈ A` and some point of `W` within `r` of
`e`.

DGO's `W₁ = W ∪ ⋃_{c ∈ C₁} [c, c̄]`, with `A = C₁` and `r` the reach.  Stated as
a membership condition rather than a union of chosen segments so that no choice
function is involved and the set is automatically invariant under isometries
preserving `W` and `A`. -/
def spokeSet (W A : Set X) (r : ℝ) : Set X :=
  {p : X | p ∈ W ∨ ∃ e ∈ A, ∃ w ∈ W, dist e w ≤ r ∧ Between e p w}

theorem mem_spokeSet_iff {W A : Set X} {r : ℝ} {p : X} :
    p ∈ spokeSet W A r ↔
      p ∈ W ∨ ∃ e ∈ A, ∃ w ∈ W, dist e w ≤ r ∧ Between e p w := Iff.rfl

theorem subset_spokeSet {W A : Set X} {r : ℝ} : W ⊆ spokeSet W A r :=
  fun _ hp => Or.inl hp

theorem mem_spokeSet_of_mem_tips {W A : Set X} {r : ℝ} {e : X} (he : e ∈ A)
    {w : X} (hw : w ∈ W) (hd : dist e w ≤ r) : e ∈ spokeSet W A r :=
  Or.inr ⟨e, he, w, hw, hd, between_self_left e w⟩

theorem spokeSet_mono_tips {W A A' : Set X} {r : ℝ} (h : A ⊆ A') :
    spokeSet W A r ⊆ spokeSet W A' r := by
  intro p hp
  rcases mem_spokeSet_iff.mp hp with hpW | ⟨e, he, w, hw, hd, hb⟩
  · exact Or.inl hpW
  · exact Or.inr ⟨e, h he, w, hw, hd, hb⟩

/-! ## The foot of a point -/

/-- **Every point of a spoke set has a foot in `W`, and the whole way back to it
stays inside the set.**

For a point of `W` the foot is the point itself: anything between `p` and `p` is
at distance zero from `p`, hence equal to it, `IsGeodesicSpace` making the
ambient pseudometric separated.  For a point of a spoke the foot is the `w` the
spoke ends at, and `Between.trans_right` carries the betweenness from the tip
past any intermediate point. -/
theorem exists_foot_of_mem_spokeSet (hgeo : IsGeodesicSpace X) {W A : Set X}
    {r : ℝ} {p : X} (hp : p ∈ spokeSet W A r) :
    ∃ w ∈ W, ∀ q : X, Between p q w → q ∈ spokeSet W A r := by
  rcases mem_spokeSet_iff.mp hp with hpW | ⟨e, he, w, hw, hd, hb⟩
  · refine ⟨p, hpW, ?_⟩
    intro q hq
    unfold Between at hq
    rw [dist_self] at hq
    have h1 : (0 : ℝ) ≤ dist p q := dist_nonneg
    have h2 : (0 : ℝ) ≤ dist q p := dist_nonneg
    have h3 : dist q p = dist p q := dist_comm q p
    have h4 : dist p q = 0 := by linarith
    have h5 : p = q := eq_of_dist_eq_zero_of_geodesic hgeo h4
    rw [← h5]
    exact Or.inl hpW
  · refine ⟨w, hw, ?_⟩
    intro q hq
    exact Or.inr ⟨e, he, w, hw, hd, Between.trans_right hb hq⟩

/-! ## Quasiconvexity -/

/-- **A spoke set is `12δ`-quasiconvex, with a constant independent of the
reach.**

The quadrilateral `p, w, w', p'`, where `w` and `w'` are the feet of `p` and
`p'`: a point of a geodesic `[p,p']` is within `6δ` of one of the three other
sides, the two outer sides `[p,w]` and `[w',p']` lie in the spoke set outright by
`exists_foot_of_mem_spokeSet`, and the middle side `[w,w']` joins two points of
`W`, so it lies in `W^{+6δ}`.

This is the estimate that forces the segments into the definition of `W₁`: it is
false for `W ∪ A`, whose geodesics between two tips run `O(r)` from the set. -/
theorem isQuasiconvexSet_spokeSet {δ r : ℝ} (hδ0 : 0 ≤ δ)
    (hhyp : IsHyperbolicSpace δ X) (hgeo : IsGeodesicSpace X) {W A : Set X}
    (hW : IsQuasiconvexSet W (6 * δ)) :
    IsQuasiconvexSet (spokeSet W A r) (12 * δ) := by
  intro p hp p' hp' f hf hf0 hf1 t ht
  obtain ⟨w, hwW, hwspoke⟩ := exists_foot_of_mem_spokeSet hgeo hp
  obtain ⟨w', hw'W, hw'spoke⟩ := exists_foot_of_mem_spokeSet hgeo hp'
  obtain ⟨g₁, hg₁, hg₁0, hg₁1⟩ := hgeo p w
  obtain ⟨g₂, hg₂, hg₂0, hg₂1⟩ := hgeo w w'
  obtain ⟨g₃, hg₃, hg₃0, hg₃1⟩ := hgeo w' p'
  rcases exists_close_on_other_sides_of_quadrilateral hhyp hδ0 hgeo hf hf0 hf1
      hg₁ hg₁0 hg₁1 hg₂ hg₂0 hg₂1 hg₃ hg₃0 hg₃1 ht with
    ⟨s, hs, hclose⟩ | ⟨s, hs, hclose⟩ | ⟨s, hs, hclose⟩
  · obtain ⟨-, hb⟩ := between_of_mem_geodesic hg₁ hg₁0 hg₁1 hs
    exact ⟨g₁ s, hwspoke (g₁ s) hb, by linarith⟩
  · obtain ⟨q, hqW, hqd⟩ := hW w hwW w' hw'W g₂ hg₂ hg₂0 hg₂1 s hs
    have htri := dist_triangle (f t) (g₂ s) q
    exact ⟨q, subset_spokeSet hqW, by linarith⟩
  · obtain ⟨-, hb⟩ := between_of_mem_geodesic hg₃ hg₃0 hg₃1 hs
    exact ⟨g₃ s, hw'spoke (g₃ s) (Between.symm hb), by linarith⟩

/-! ## Staying far from a spoke set -/

/-- **A point far from `W`, and `r` further from every tip, is far from the whole
spoke set.**

No hyperbolicity: a point of a spoke is within `r` of its tip, because the tip,
the point and the foot are metrically in that order.

This is the clause that keeps a new apex `c` away from the reference set `S_c`
of the corner lemma.  With `s = 55δ`, tips the *other* new apices at distance at
least `ρ ≥ 200δ` from `c`, and reach `r ≤ 76δ`, the hypothesis
`s + r ≤ ρ` reads `131δ ≤ 200δ`. -/
theorem le_dist_of_mem_spokeSet {W A : Set X} {r s : ℝ} {c : X}
    (hWfar : ∀ w ∈ W, s ≤ dist c w) (hAfar : ∀ e ∈ A, s + r ≤ dist c e)
    {p : X} (hp : p ∈ spokeSet W A r) : s ≤ dist c p := by
  rcases mem_spokeSet_iff.mp hp with hpW | ⟨e, he, w, hw, hd, hb⟩
  · exact hWfar p hpW
  · have hep : dist e p ≤ dist e w := Between.dist_le_left hb
    have hce : s + r ≤ dist c e := hAfar e he
    have htri : dist c e ≤ dist c p + dist p e := dist_triangle c p e
    have hcomm : dist p e = dist e p := dist_comm p e
    linarith

end DGOWindmill
end GroupApproximation
