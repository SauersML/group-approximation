import GroupApproximation.GGT.ElementaryIndependence
import GroupApproximation.GGT.ElementaryBowditch

/-!
# The Morse and common-power theorems at a bare alphabet

`ElementaryMorseOrbit.centralizerOrbitNearAxis_cayley` and
`ElementaryIndependence.independentOfNoCommonZpow_cayley` take a
`HullGeneratingSet`, which bundles non-elementarity of the action.  Neither
proof uses that field: the geodesic realisation needs only the alphabet and
hyperbolicity of `Γ(G,A)`, and the common-power theorem needs acylindricity in
addition.  A consumer whose *conclusion* is non-elementarity
(`GGT.WPD…relativeCayleyNonElementary_of`) cannot supply a `HullGeneratingSet`
without circularity, so the two theorems are restated here at a bare alphabet
with hyperbolicity (and acylindricity) as explicit hypotheses.
-/

namespace GroupApproximation
namespace GGT
namespace ElementaryMorse

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.AxisDichotomyRoute

universe u

variable {G : Type u} [Group G]

/-- **`CentralizerOrbitNearAxis` at `Γ(G,A)` from hyperbolicity alone.** -/
theorem centralizerOrbitNearAxis_cayley_of_hyperbolic (A : Alphabet G) {δ : ℝ}
    (hδ : IsHyperbolicSpace δ (Cayley A)) :
    Elementary.CentralizerOrbitNearAxis G (Cayley.base A) := by
  have hM : Nonempty (GeodesicModel G (Cayley A)) :=
    ⟨CayleyGeodesicModel.model A hδ
      (Elementary.nonneg_of_isHyperbolicSpace hδ (Cayley.base A))
      (CayleyGeodesicModel.isGeodesicRealisation A)⟩
  obtain ⟨M⟩ := hM
  exact Elementary.centralizerOrbitNearAxis_of_map M.distortion_nonneg
    M.hasAdditiveDistortion M.equivariant
    (centralizerOrbitNearAxis_of_geodesic M.hyperbolic M.delta_nonneg M.geodesic
      M.isometric _)

/-- **`IndependentOfNoCommonZpow` at `Γ(G,A)` from hyperbolicity and
acylindricity alone.** -/
theorem independentOfNoCommonZpow_cayley_of_hyperbolic (A : Alphabet G) {δ : ℝ}
    (hδ : IsHyperbolicSpace δ (Cayley A)) (hacy : IsAcylindrical G (Cayley A)) :
    Elementary.IndependentOfNoCommonZpow G (Cayley.base A) := by
  have hM : Nonempty (GeodesicModel G (Cayley A)) :=
    ⟨CayleyGeodesicModel.model A hδ
      (Elementary.nonneg_of_isHyperbolicSpace hδ (Cayley.base A))
      (CayleyGeodesicModel.isGeodesicRealisation A)⟩
  obtain ⟨M⟩ := hM
  have hacyW : IsAcylindrical G M.W :=
    isAcylindrical_of_additiveDistortion_of_dense M.distortion_nonneg
      M.hasAdditiveDistortion M.hasDenseImage M.equivariant M.isometric hacy
  exact Elementary.independentOfNoCommonZpow_of_map M.distortion_nonneg
    M.hasAdditiveDistortion M.equivariant
    (independentOfNoCommonZpow_of_geodesic M.hyperbolic M.delta_nonneg M.geodesic
      M.isometric hacyW _)

end ElementaryMorse
end GGT
end GroupApproximation
