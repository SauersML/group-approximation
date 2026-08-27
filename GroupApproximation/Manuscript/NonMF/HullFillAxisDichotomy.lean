import GroupApproximation.GGT.HyperbolicAdditiveTransfer
import GroupApproximation.Manuscript.NonMF.HullFillOsinNormalReduction

/-!
# `AxisDichotomy`, and the geodesic model `Γ(G,A)` does not have

`Manuscript.NonMF.HullFillOsinNormalReduction` reduces the Osin debt to three
facts about elementary closures.  This module is the third of them,
`OsinNormalReduction.AxisDichotomy`:

> for a loxodromic `g` and any `c`, either `g` and `c g⁻¹ c⁻¹` are independent,
> or `c gᵐ c⁻¹ = gⁿ` with `m, n ≠ 0`.

Two things are settled here.  The dichotomy is the common-power theorem in
disguise, and the disguise comes off in five lines
(`axisDichotomy_of_commonPower`).  And the landed route to the common-power
theorem cannot be run at `Γ(G,A)` as this repository models it — that is
`not_isGeodesicSpace_cayley`, and it is why the residual below is stated at a
geodesic model rather than at the Cayley graph itself.

## The dichotomy is the common-power theorem

`CommonPowerOfNotIndependent` says that two loxodromic elements that fail to be
independent have a common nonzero power, `gᵖ = hᑫ`.  Apply it to `h = c g⁻¹ c⁻¹`
— loxodromic, being a conjugate of the inverse of a loxodromic — and
`(c g⁻¹ c⁻¹)ᑫ = c g⁻ᑫ c⁻¹` turns `gᵖ = hᑫ` into `c g⁻ᑫ c⁻¹ = gᵖ`, which is the
second disjunct with `m = -q` and `n = p`.  No geometry enters, only
`conj_zpow`.

## `Γ(G,A)` is not a geodesic space

`Sofic.HullSuitabilityGeometry`'s route to a common power is
`exists_long_fellow_geodesics_of_not_independent` — negate independence, get
power endpoints with large Gromov product, and take geodesics to them that
`4δ`-fellow-travel — followed by
`acylindrical_common_power_of_two_orbit_fellow_travel`, which pigeonholes the
difference elements.  The first of those carries `hgeo : IsGeodesicSpace X`.

`Cayley A` is the vertex set of `Γ(G,A)` with the word metric, so every distance
in it is a natural number.  A geodesic segment of length at least `1` would have
to realise the distance `1/2` between two of its points, so:

> `not_isGeodesicSpace_cayley` — for a nontrivial `G`, `Cayley A` is **not** a
> geodesic space,

and neither `exists_long_fellow_geodesics_of_not_independent` nor
`acylindrical_relaxed` nor `exists_geodesic_point_near_penultimate_orbit` can be
applied to it.  This is a property of the model, not a gap in the geometry: the
vertex set of a graph is never geodesic in the `ℝ`-parameterised sense, and the
geometric statements of that module are all about a space in which they are.

## What replaces it

`GGT.HyperbolicAdditiveTransfer` is the bridge, and it is already built:
loxodromy, independence and acylindricity all transfer along an equivariant map
of bounded additive distortion, in the directions needed here.  So the argument
should be run in a geodesic model `W` of `Γ(G,A)` — the metric realisation of
the graph, in which each edge is an isometric copy of `[0,1]` — and the
conclusion `c gᵐ c⁻¹ = gⁿ`, being an equation in `G`, needs no transfer back.

`GeodesicModel` bundles what such a model must supply, and
`commonPowerOfNotIndependent_of_geodesicModel` runs the transfer.  Two named
residuals remain:

* `HasGeodesicModel` — the metric realisation of `Γ(G,A)`, with its `G`-action,
  its hyperbolicity, and the vertex inclusion as an equivariant `0`-distortion
  map with `1`-dense image.  Hyperbolicity of the realisation follows from
  hyperbolicity of the vertex set by the nearest-vertex retraction, which is a
  map of additive distortion `2` in the other direction; the repository has
  `isHyperbolicSpace_of_additiveDistortion` for exactly that step, so this
  residual is a construction rather than a theorem.
* `CommonPowerInGeodesicSpace` — the common-power theorem itself, in a geodesic
  space.  That is the missing final assembly:
  `exists_long_fellow_geodesics_of_not_independent` produces one long
  fellow-travelling pair, and `acylindrical_common_power_of_two_orbit_fellow_travel`
  consumes `N + 1` of them with injective exponents at two points `R` apart, so
  what is left is the iteration that turns the first into the second.
  `exists_long_fellow_geodesics_of_not_independent` has no consumer in the
  repository today; this is the consumer it is waiting for.

## Status

**Not compiled.**  Written while builds were frozen, and not in the root import
list for that reason.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace AxisDichotomyRoute

open GroupApproximation.HullGeometry
open GroupApproximation.GGT
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.OsinNormalReduction

universe u v

/-! ## The common-power theorem, and the dichotomy from it -/

/-- **The common-power theorem, at one action and one basepoint.**  Two
loxodromic elements whose power orbits are not independent have a common nonzero
power.  This is the content of `AxisDichotomy`; everything else is conjugation
bookkeeping. -/
def CommonPowerOfNotIndependent (G : Type u) [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] (x : X) : Prop :=
  ∀ g h : G, IsLoxodromic g x → IsLoxodromic h x → ¬ Independent g h x →
    ∃ p q : ℤ, p ≠ 0 ∧ q ≠ 0 ∧ g ^ p = h ^ q

/-- **`AxisDichotomy` is the common-power theorem.**  The second disjunct is
`gᵖ = (c g⁻¹ c⁻¹)ᑫ` rewritten with `conj_zpow`. -/
theorem axisDichotomy_of_commonPower {G : Type u} [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] (hiso : IsIsometricAction G X) {x : X}
    (hCP : CommonPowerOfNotIndependent G x) : AxisDichotomy G x := by
  intro g c hg
  by_cases hind : Independent g (c * g⁻¹ * c⁻¹) x
  · exact Or.inl hind
  · have hconj : IsLoxodromic (c * g⁻¹ * c⁻¹) x :=
      isLoxodromic_conj hiso (isLoxodromic_inv hiso hg)
    obtain ⟨p, q, hp, hq, hpq⟩ := hCP g (c * g⁻¹ * c⁻¹) hg hconj hind
    refine Or.inr ⟨-q, p, neg_ne_zero.mpr hq, hp, ?_⟩
    rw [hpq, conj_zpow, inv_zpow, zpow_neg]

/-! ## The vertex set of `Γ(G,A)` is not geodesic -/

/-- A space whose distances are all natural numbers has no geodesic segment of
length `1` or more: the segment would realise the distance `1/2`. -/
theorem not_isGeodesicSpace_of_natCast_dist {X : Type v} [PseudoMetricSpace X]
    (hnat : ∀ a b : X, ∃ n : ℕ, dist a b = (n : ℝ))
    {x y : X} (hxy : 1 ≤ dist x y) : ¬ IsGeodesicSpace X := by
  intro hgeo
  obtain ⟨f, hf, -, -⟩ := hgeo x y
  have hhalf : dist (f 0) (f (1 / 2)) = 1 / 2 := by
    have h := hf 0 ⟨le_refl 0, by linarith⟩ (1 / 2)
      ⟨by norm_num, by linarith⟩
    rw [h]
    norm_num
  obtain ⟨n, hn⟩ := hnat (f 0) (f (1 / 2))
  rw [hn] at hhalf
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0] at hhalf
    norm_num at hhalf
  · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpos
    linarith

/-- Every distance in `Cayley A` is a natural number: it is a word length. -/
theorem natCast_dist_cayley {G : Type u} [Group G] (A : Alphabet G)
    (a b : Cayley A) :
    ∃ n : ℕ, dist a b = (n : ℝ) :=
  ⟨WordMetric.wordDist A.carrier (Cayley.val a) (Cayley.val b), rfl⟩

/-- **`Γ(G,A)` is not a geodesic space**, as this repository models it: its
points are the vertices, its distances are word lengths, and a nontrivial group
has two vertices at distance at least `1`.

So the geodesic half of `Sofic.HullSuitabilityGeometry` —
`exists_long_fellow_geodesics_of_not_independent`, `acylindrical_relaxed`,
`exists_geodesic_point_near_penultimate_orbit` — cannot be applied at
`Cayley A`, and an argument that needs it has to run in a geodesic model and
transfer. -/
theorem not_isGeodesicSpace_cayley {G : Type u} [Group G] (A : Alphabet G)
    {g : G} (hg : g ≠ 1) : ¬ IsGeodesicSpace (Cayley A) := by
  refine not_isGeodesicSpace_of_natCast_dist (natCast_dist_cayley A)
    (x := Cayley.base A) (y := Cayley.of A g) ?_
  have hne : WordMetric.wordDist A.carrier 1 g ≠ 0 := by
    intro h0
    exact hg ((WordMetric.wordDist_eq_zero_iff A.symmetricGenerating 1 g).mp h0).symm
  have h1 : 1 ≤ WordMetric.wordDist A.carrier 1 g := Nat.one_le_iff_ne_zero.mpr hne
  simp only [Cayley.dist_eq, Cayley.val_base, Cayley.val_of]
  exact_mod_cast h1

/-! ## A geodesic model, and the transfer -/

/-- **What a geodesic model of an action supplies.**  The metric realisation of
`Γ(G,A)` is the intended term: the vertex inclusion is equivariant, changes no
distance between vertices, and every point of an edge is within `1` of a
vertex. -/
structure GeodesicModel (G : Type u) [Group G] (X : Type v)
    [PseudoMetricSpace X] [MulAction G X] where
  /-- The model. -/
  W : Type v
  /-- Its metric. -/
  [metric : PseudoMetricSpace W]
  /-- The action on it. -/
  [action : MulAction G W]
  /-- The comparison map. -/
  iota : X → W
  /-- Its distortion constant. -/
  distortion : ℝ
  /-- The distortion constant is nonnegative. -/
  distortion_nonneg : 0 ≤ distortion
  /-- `iota` changes distances by at most `distortion`. -/
  hasAdditiveDistortion : HasAdditiveDistortion distortion iota
  /-- Its image is `distortion`-dense. -/
  hasDenseImage : HasDenseImage distortion iota
  /-- `iota` is equivariant. -/
  equivariant : IsEquivariant G iota
  /-- The action on the model is by isometries. -/
  isometric : IsIsometricAction G W
  /-- The model is geodesic — which `X` itself need not be. -/
  geodesic : IsGeodesicSpace W
  /-- Its hyperbolicity constant. -/
  delta : ℝ
  /-- The constant is nonnegative. -/
  delta_nonneg : 0 ≤ delta
  /-- The model is hyperbolic. -/
  hyperbolic : IsHyperbolicSpace delta W

namespace GeodesicModel

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
  [MulAction G X]

instance instPseudoMetricSpace (M : GeodesicModel G X) :
    PseudoMetricSpace M.W := M.metric

instance instMulAction (M : GeodesicModel G X) : MulAction G M.W := M.action

end GeodesicModel

/-- **The common-power theorem in a geodesic space**, the residual of the
geometric half.  `exists_long_fellow_geodesics_of_not_independent` and
`acylindrical_common_power_of_two_orbit_fellow_travel` are its two ends. -/
def CommonPowerInGeodesicSpace : Prop :=
  ∀ {G : Type u} [Group G] {Y : Type v} [PseudoMetricSpace Y] [MulAction G Y]
    {δ : ℝ}, IsHyperbolicSpace δ Y → 0 ≤ δ → IsGeodesicSpace Y →
      IsIsometricAction G Y → IsAcylindrical G Y →
        ∀ {g h : G} {y : Y}, IsLoxodromic g y → IsLoxodromic h y →
          ¬ Independent g h y → ∃ p q : ℤ, p ≠ 0 ∧ q ≠ 0 ∧ g ^ p = h ^ q

/-- **The transfer.**  Loxodromy pushes forward to the model, independence pulls
back from it, and acylindricity pushes forward because the comparison map has
dense image.  The conclusion is an equation in `G`, so it comes back for
free. -/
theorem commonPowerOfNotIndependent_of_geodesicModel {G : Type u} [Group G]
    {X : Type v} [PseudoMetricSpace X] [MulAction G X]
    (hCP : CommonPowerInGeodesicSpace.{u, v}) (M : GeodesicModel G X)
    (hacy : IsAcylindrical G X) (x : X) :
    CommonPowerOfNotIndependent G x := by
  intro g h hg hh hnind
  have hacyW : IsAcylindrical G M.W :=
    isAcylindrical_of_additiveDistortion_of_dense M.distortion_nonneg
      M.hasAdditiveDistortion M.hasDenseImage M.equivariant M.isometric hacy
  have hgW : IsLoxodromic g (M.iota x) :=
    isLoxodromic_map M.distortion_nonneg M.hasAdditiveDistortion M.equivariant hg
  have hhW : IsLoxodromic h (M.iota x) :=
    isLoxodromic_map M.distortion_nonneg M.hasAdditiveDistortion M.equivariant hh
  have hnindW : ¬ Independent g h (M.iota x) := fun hind =>
    hnind (independent_of_map M.hasAdditiveDistortion M.equivariant hind)
  exact hCP M.hyperbolic M.delta_nonneg M.geodesic M.isometric hacyW hgW hhW
    hnindW

/-! ## `AxisDichotomy` at Hull's Cayley graph -/

/-- **The metric realisation of `Γ(G,A)`**, as a named residual: a geodesic
model of the vertex action.  `not_isGeodesicSpace_cayley` is why it cannot be
`Cayley A` itself. -/
def HasGeodesicModel {G : Type u} [Group G] (A : Alphabet G) : Prop :=
  Nonempty (GeodesicModel G (Cayley A))

/-- **`AxisDichotomy` at `Γ(G,A)`, from the two residuals.**  This is the third
of the three facts `HullFillOsinNormalReduction` asks for, and what remains of
it is a construction (`HasGeodesicModel`) and a theorem in a geodesic space
(`CommonPowerInGeodesicSpace`). -/
theorem axisDichotomy_cayley {G : Type u} [Group G] (A : HullGeneratingSet G)
    (hCP : CommonPowerInGeodesicSpace.{u, u})
    (hmodel : HasGeodesicModel A.alphabet) :
    AxisDichotomy G (Cayley.base A.alphabet) := by
  obtain ⟨M⟩ := hmodel
  exact axisDichotomy_of_commonPower A.isometric
    (commonPowerOfNotIndependent_of_geodesicModel hCP M A.acylindrical
      (Cayley.base A.alphabet))

end AxisDichotomyRoute
end NonMF
end Manuscript
end GroupApproximation
