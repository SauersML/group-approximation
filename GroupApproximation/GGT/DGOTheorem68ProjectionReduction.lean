import GroupApproximation.GGT.ElementaryCoarseTranslationQuasiconvex
import GroupApproximation.GGT.WPDElementaryEmbedding

/-!
# DGO Theorem 6.8 through the projection criterion

This follows DGO's proof literally: Lemma 6.5 supplies uniform coarse
translation, Lemma 6.7 supplies geometric separation, and Theorem 4.42 supplies
the relative generating set.  Quasiconvexity and both properness conclusions
are derived from coarse translation rather than retained as further inputs.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

open GroupApproximation.HullGeometry

universe u

/-- The two remaining orbit-geometric conclusions of DGO Lemmas 6.5 and 6.7.
Uniform coarse translation implies quasiconvexity and both properness results;
geometric separation is the independent conclusion of Lemma 6.7. -/
def ElementaryProjectionGeometry : Prop :=
  ∀ (G : Type u) [Group G] (D : AH3Data.{u, u} G),
    @ElementaryClosureCoarseTranslation G _ D.Space D.metricSpace D.mulAction D.base ∧
    @GeometricallySeparatedAt G _ D.Space D.metricSpace D.mulAction
      (elementaryClosure D.elt) D.base

/-- DGO Theorem 6.8 from its projection-complex theorem and the exact
elementary-closure geometry used in its proof. -/
theorem dgoTheorem68_of_projection
    (h442 : DGOTheorem442.{u, u})
    (hgeom : ElementaryProjectionGeometry.{u}) : DGOTheorem68.{u, u} := by
  intro G _inst D hnvc
  letI : PseudoMetricSpace D.Space := D.metricSpace
  letI : MulAction G D.Space := D.mulAction
  obtain ⟨hct, hsep⟩ := hgeom G D
  have hδ0 : 0 ≤ D.delta := by
    have h := D.hyperbolic D.base D.base D.base D.base
    rw [min_self] at h
    linarith
  have hqc : IsQuasiconvexOrbitAt (elementaryClosure D.elt) D.base :=
    isQuasiconvexOrbitAt_elementaryClosure_of_coarseTranslation D.hyperbolic
      hδ0 D.isometric D.loxodromic hct
  have hproper : ActsProperlyAt (elementaryClosure D.elt) D.base :=
    actsProperlyAt_elementaryClosure_of_coarseTranslation D.isometric D.wpd
      D.loxodromic hct
  have hemb : IsHypEmbedded G (elementaryClosure D.elt) :=
    isHypEmbedded_of_dgo442 h442 (elementaryClosure D.elt) D.base D.delta
      D.isometric D.hyperbolic hqc hsep hproper
  have hne : elementaryClosure D.elt ≠ ⊤ :=
    elementaryClosure_ne_top_of_coarseTranslation D.isometric D.wpd
      D.loxodromic hct hnvc
  exact ⟨elementaryClosure D.elt, self_mem_elementaryClosure D.elt, hne, hemb⟩

end Elementary
end GGT
end GroupApproximation
