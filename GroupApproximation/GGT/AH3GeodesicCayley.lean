import GroupApproximation.GGT.CayleyGeodesicRealisation
import GroupApproximation.GGT.HyperbolicWPDTransfer
import GroupApproximation.GGT.WPDAcylindricalHyperbolicity

/-!
# The source-faithful `(AH₁) ⇒ (AH₃)` Cayley witness

The vertex set of a Cayley graph is not a geodesic space.  This module restores
the converse direction of Osin Theorem 1.2 after `AH3Data` was corrected to
record the geodesicity convention used in the source: it packages the genuine
metric realization `CayleyGeodesicModel.PointQuot` instead.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.AxisDichotomyRoute

universe u

/-- **`(AH₁) ⇒ (AH₃)` on the genuine geodesic realization of the Cayley
graph.**  Hyperbolicity and geodesicity are fields of `modelQuot`; loxodromy
and WPD push forward along its equivariant additive-distortion vertex map. -/
theorem exists_ah3Data_of_isAcylindricallyHyperbolic (G : Type u) [Group G]
    [h : IsAcylindricallyHyperbolic G] : Nonempty (AH3Data.{u, u} G) := by
  obtain ⟨A, δ, hδ, hacy, hne⟩ := h.out
  obtain ⟨g, _, _, _, hlox, _, _⟩ := hne
  have hδ0 : 0 ≤ δ := by
    have hbase := hδ (Cayley.base A) (Cayley.base A) (Cayley.base A)
      (Cayley.base A)
    rw [min_self] at hbase
    linarith
  let M := CayleyGeodesicModel.modelQuot A hδ hδ0
    (CayleyGeodesicModel.isGeodesicRealisationQuot A)
  letI : PseudoMetricSpace M.W := M.metric
  letI : MulAction G M.W := M.action
  have hwpd : IsWPDAt g (Cayley.base A) :=
    isWPDAt_of_isAcylindrical hacy hlox
  exact ⟨AH3Data.ofData M.W M.isometric M.delta M.hyperbolic M.geodesic g
    (M.iota (Cayley.base A))
    (isLoxodromic_map M.distortion_nonneg M.hasAdditiveDistortion M.equivariant hlox)
    (isWPDAt_map M.distortion_nonneg M.hasAdditiveDistortion M.equivariant hwpd)⟩

end GGT
end GroupApproximation
