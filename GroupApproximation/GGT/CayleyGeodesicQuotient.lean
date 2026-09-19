import GroupApproximation.GGT.CayleyGeodesicModel

/-!
# The metric identification of the realisation

`CayleyGeodesicModel` builds `Point A`, the metric realisation of `Γ(G,A)`, with
its edges *doubled rather than quotiented*: the far end `⟨x, a, 1⟩` of an edge
and the vertex `⟨x * a, 1, 0⟩` it runs into are different terms of `Point A` at
distance `0`, and so are the two ends `⟨x, 1, 0⟩`, `⟨x, 1, 1⟩` of the degenerate
loop that `Letters A = insert 1 A.carrier` adjoins at every vertex.  So
`Point A` is a genuine *pseudo*metric space, and

    IsGeodesicSpace (Point A)

is **false for every `G` and every `A`** --- it demands `f 0 = p` and
`f (dist p q) = q` on the nose, and the loop witness has `dist p q = 0` with
`p ≠ q`, so `f (dist p q) = f 0 = p ≠ q`.  That is not a gap in the geometry: it
is the doubling, and no choice of `f` repairs it.

This module takes the metric identification and moves the geodesic statement
there.  `PointQuot A` is `Point A` modulo distance zero; `mk` is the projection.
Every field of `GeodesicModel` is a statement about distances, and `mk` is a
surjective distance-preserving map, so every one of them transports:

* `dist_mk` --- `mk` preserves distances, by definition of the quotient metric;
* `mk_surjective`, `mk_eq_mk` --- the projection is onto, and identifies exactly
  the pairs at distance zero;
* `instMulActionPointQuot` --- the translation action descends, because it is by
  isometries, and stays isometric;
* `isHyperbolicSpace_pointQuot` --- the four-point condition is a statement about
  four distances;
* `iotaQuot` and its three clauses --- distortion, density and equivariance;
* `isGeodesicSpace_pointQuot` --- a family of segments whose endpoints are
  correct *up to distance zero* becomes a genuine geodesic space downstairs.

The last one is the point of the construction: the segments built in
`CayleyGeodesicRealisation` were always correct up to distance zero, and it is
only the on-the-nose endpoint that the doubling obstructs.

## On `SeparationQuotient`

Mathlib's `SeparationQuotient` is the same construction and carries a
`MetricSpace` instance.  It is not used here because this checkout has no Mathlib
source tree to confirm the spelling of its API against, and the quotient is four
lines of `Quotient`; the names below (`mk`, `dist_mk`, `mk_surjective`,
`mk_eq_mk`) deliberately mirror it, so substituting it later is a rename.

## What does not move

`HasGeodesicModel A = Nonempty (GeodesicModel G (Cayley A))` quantifies the model
space `W` existentially, so **no consumer of `HasGeodesicModel` changes**:
`axisDichotomy_cayley` and everything below it are untouched.  Only the
construction that fixes `W := Point A` --- `CayleyGeodesicModel.model` --- needs
the sibling `modelQuot` built here.
-/

namespace GroupApproximation
namespace GGT
namespace CayleyGeodesicModel

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.OsinNormalReduction
open GroupApproximation.Manuscript.NonMF.AxisDichotomyRoute

universe u

variable {G : Type u} [Group G]

/-! ## Distance zero is an equivalence -/

/-- **Distance is invariant under moving either argument by zero.**  Two
applications of the triangle inequality in each direction; this is what makes the
quotient metric well defined. -/
theorem dist_congr {A : Alphabet G} {p p' q q' : Point A}
    (hp : dist p p' = 0) (hq : dist q q' = 0) : dist p q = dist p' q' := by
  have hp' : dist p' p = 0 := by rw [dist_comm]; exact hp
  have hq' : dist q' q = 0 := by rw [dist_comm]; exact hq
  have h1 : dist p q ≤ dist p p' + dist p' q := dist_triangle p p' q
  have h2 : dist p' q ≤ dist p' q' + dist q' q := dist_triangle p' q' q
  have h3 : dist p' q' ≤ dist p' p + dist p q' := dist_triangle p' p q'
  have h4 : dist p q' ≤ dist p q + dist q q' := dist_triangle p q q'
  linarith

/-- **Distance zero is an equivalence relation** on the realisation. -/
def pointSetoid (A : Alphabet G) : Setoid (Point A) where
  r p q := dist p q = 0
  iseqv := by
    refine ⟨fun p => dist_self p, fun {p q} h => ?_, fun {p q r} hpq hqr => ?_⟩
    · rw [dist_comm]
      exact h
    · have h1 : dist p r ≤ dist p q + dist q r := dist_triangle p q r
      have h2 : (0 : ℝ) ≤ dist p r := dist_nonneg
      linarith

/-- **The metric identification of the realisation**: points of `Γ(G,A)`'s metric
realisation, with the pairs at distance zero identified. -/
def PointQuot (A : Alphabet G) : Type u := Quotient (pointSetoid A)

/-- The projection onto the metric identification. -/
def mk {A : Alphabet G} (p : Point A) : PointQuot A := Quotient.mk (pointSetoid A) p

/-- Every class has a representative. -/
theorem mk_surjective (A : Alphabet G) : Function.Surjective (mk (A := A)) := by
  refine fun x => Quotient.inductionOn x ?_
  intro p
  exact ⟨p, rfl⟩

/-! ## The quotient metric -/

/-- **The metric identification is a metric space.**  The distance descends by
`dist_congr`, and it separates points by construction, which is the whole
purpose: it is exactly the failure of separation that made
`IsGeodesicSpace (Point A)` false. -/
noncomputable instance instMetricSpacePointQuot (A : Alphabet G) :
    MetricSpace (PointQuot A) where
  dist x y := Quotient.liftOn₂ x y (fun p q => dist p q)
    (fun _ _ _ _ hp hq => dist_congr hp hq)
  dist_self x := Quotient.inductionOn x (fun p => dist_self p)
  dist_comm x y := Quotient.inductionOn₂ x y (fun p q => dist_comm p q)
  dist_triangle x y z :=
    Quotient.inductionOn₃ x y z (fun p q r => dist_triangle p q r)
  eq_of_dist_eq_zero := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro p q h
    exact Quotient.sound h

/-- **The projection preserves distances.** -/
@[simp] theorem dist_mk {A : Alphabet G} (p q : Point A) :
    dist (mk p) (mk q) = dist p q := rfl

/-- **The projection identifies exactly the pairs at distance zero.** -/
theorem mk_eq_mk {A : Alphabet G} {p q : Point A} :
    mk p = mk q ↔ dist p q = 0 :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-! ## The translation action descends -/

/-- **The translation action on the metric identification.**  It is well defined
because the action upstairs is by isometries, so it moves a pair at distance zero
to a pair at distance zero. -/
instance instMulActionPointQuot (A : Alphabet G) : MulAction G (PointQuot A) where
  smul g := Quotient.map (fun p => g • p) (by
    intro p q h
    show dist (g • p) (g • q) = 0
    rw [isIsometricAction_point A g p q]
    exact h)
  one_smul x := by
    refine Quotient.inductionOn x ?_
    intro p
    show mk ((1 : G) • p) = mk p
    rw [one_smul]
  mul_smul g h x := by
    refine Quotient.inductionOn x ?_
    intro p
    show mk ((g * h) • p) = mk (g • h • p)
    rw [mul_smul]

/-- The action commutes with the projection. -/
@[simp] theorem smul_mk {A : Alphabet G} (g : G) (p : Point A) :
    g • mk p = mk (g • p) := rfl

/-- **The descended action is by isometries.** -/
theorem isIsometricAction_pointQuot (A : Alphabet G) :
    IsIsometricAction G (PointQuot A) := by
  intro g x y
  refine Quotient.inductionOn₂ x y ?_
  intro p q
  show dist (mk (g • p)) (mk (g • q)) = dist (mk p) (mk q)
  rw [dist_mk, dist_mk]
  exact isIsometricAction_point A g p q

/-! ## Hyperbolicity descends -/

/-- The Gromov product is a function of three distances, so it is unchanged by
the projection. -/
theorem gromovProduct_mk {A : Alphabet G} (p q r : Point A) :
    gromovProduct (mk p) (mk q) (mk r) = gromovProduct p q r := by
  unfold gromovProduct
  rw [dist_mk, dist_mk, dist_mk]

/-- **The metric identification is hyperbolic whenever the realisation is.**  The
four-point condition mentions only distances, and every point downstairs has a
representative upstairs. -/
theorem isHyperbolicSpace_pointQuot {A : Alphabet G} {δ : ℝ}
    (h : IsHyperbolicSpace δ (Point A)) : IsHyperbolicSpace δ (PointQuot A) := by
  intro w x y z
  refine Quotient.inductionOn₂ w x ?_
  intro pw px
  refine Quotient.inductionOn₂ y z ?_
  intro py pz
  -- `Quotient.inductionOn₂` leaves the goal phrased with `⟦·⟧` at type
  -- `Quotient (pointSetoid A)` rather than `mk · : PointQuot A`, which `rw`
  -- will not match through the `def`.  `show` puts it back in `mk` form.
  show min (gromovProduct (mk px) (mk py) (mk pw))
      (gromovProduct (mk py) (mk pz) (mk pw)) - δ
    ≤ gromovProduct (mk px) (mk pz) (mk pw)
  rw [gromovProduct_mk, gromovProduct_mk, gromovProduct_mk]
  exact h pw px py pz

/-! ## The vertex inclusion descends -/

/-- The vertex inclusion of `Γ(G,A)` into the metric identification. -/
def iotaQuot (A : Alphabet G) (x : Cayley A) : PointQuot A := mk (iota A x)

/-- **The vertex inclusion still changes no distance.** -/
theorem hasAdditiveDistortion_iotaQuot (A : Alphabet G) :
    HasAdditiveDistortion 1 (iotaQuot A) := by
  intro x y
  have h := hasAdditiveDistortion_iota A x y
  show |dist (mk (iota A x)) (mk (iota A y)) - dist x y| ≤ 1
  rw [dist_mk]
  exact h

/-- **Every class is still within `1` of a vertex.** -/
theorem hasDenseImage_iotaQuot (A : Alphabet G) :
    HasDenseImage 1 (iotaQuot A) := by
  intro u
  refine Quotient.inductionOn u ?_
  intro p
  obtain ⟨x, hx⟩ := hasDenseImage_iota A p
  refine ⟨x, ?_⟩
  show dist (mk (iota A x)) (mk p) ≤ 1
  rw [dist_mk]
  exact hx

/-- **The vertex inclusion is still equivariant.** -/
theorem isEquivariant_iotaQuot (A : Alphabet G) :
    IsEquivariant G (iotaQuot A) := by
  intro g x
  show mk (iota A (g • x)) = g • mk (iota A x)
  rw [smul_mk, isEquivariant_iota A g x]

/-! ## Geodesics descend -/

/-- **Endpoints correct up to distance zero are correct downstairs.**  This is
what the doubling costs and what the identification refunds: a family of
`1`-Lipschitz segments realising `dist p q`, whose ends are merely *at distance
zero* from `p` and `q`, is a genuine geodesic structure on `PointQuot A`. -/
theorem isGeodesicSpace_pointQuot {A : Alphabet G}
    (h : ∀ p q : Point A, ∃ f : ℝ → Point A,
      IsGeodesicSegment f 0 (dist p q) ∧ dist (f 0) p = 0 ∧
        dist (f (dist p q)) q = 0) :
    IsGeodesicSpace (PointQuot A) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro p q
  obtain ⟨f, hgeo, h0, h1⟩ := h p q
  refine ⟨fun r => mk (f r), ?_, ?_, ?_⟩
  · intro s hs t ht
    show dist (mk (f s)) (mk (f t)) = |s - t|
    rw [dist_mk]
    exact hgeo s hs t ht
  · show mk (f 0) = mk p
    exact Quotient.sound h0
  · show mk (f (dist p q)) = mk q
    exact Quotient.sound h1

/-! ## The model, on the identification -/

/-- **The geodesic model of `Γ(G,A)`, built on the metric identification.**  Field
for field this is `CayleyGeodesicModel.model` with `W := PointQuot A`; every
clause is the corresponding clause upstairs, transported along `mk`. -/
noncomputable def modelQuot (A : Alphabet G) {δ : ℝ}
    (hδ : IsHyperbolicSpace δ (Cayley A)) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace (PointQuot A)) : GeodesicModel G (Cayley A) where
  W := PointQuot A
  iota := iotaQuot A
  distortion := 1
  distortion_nonneg := zero_le_one
  hasAdditiveDistortion := hasAdditiveDistortion_iotaQuot A
  hasDenseImage := hasDenseImage_iotaQuot A
  equivariant := isEquivariant_iotaQuot A
  isometric := isIsometricAction_pointQuot A
  geodesic := hgeo
  delta := δ + 6
  delta_nonneg := by linarith
  hyperbolic := isHyperbolicSpace_pointQuot (isHyperbolicSpace_point A hδ)

/-- **`HasGeodesicModel`, on the identification.**  The statement is the one
`CayleyGeodesicModel.hasGeodesicModel` proves; only the model space differs, and
`HasGeodesicModel` hides it. -/
theorem hasGeodesicModelQuot (A : HullGeneratingSet G)
    (hgeo : IsGeodesicSpace (PointQuot A.alphabet)) :
    HasGeodesicModel A.alphabet :=
  ⟨modelQuot A.alphabet A.hyperbolic
    (nonneg_of_isHyperbolicSpace A.hyperbolic (Cayley.base A.alphabet)) hgeo⟩

end CayleyGeodesicModel
end GGT
end GroupApproximation
