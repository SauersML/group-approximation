import GroupApproximation.GGT.ElementaryCoarseTranslationProperAction
import GroupApproximation.GGT.WPDElementaryEmbedding

/-!
# DGO Theorem 6.8 through the projection criterion

This follows DGO's proof literally: Lemma 6.5 supplies uniform coarse
translation and quasiconvexity of the elementary-closure orbit, Lemma 6.7
supplies geometric separation, and Theorem 4.42 supplies the relative
generating set.  Properness of the orbit action and properness of the subgroup
are derived here rather than retained as further inputs.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

open GroupApproximation.HullGeometry

universe u

/-- The two orbit-geometric conclusions of DGO Lemmas 6.5 and 6.7, together
with the uniform coarse-translation form that implies both properness results. -/
def ElementaryProjectionGeometry : Prop :=
  ∀ (G : Type u) [Group G] (D : AH3Data.{u, u} G),
    @ElementaryClosureCoarseTranslation G _ D.Space D.metricSpace D.mulAction D.base ∧
    @IsQuasiconvexOrbitAt G _ D.Space D.metricSpace D.mulAction
      (elementaryClosure D.elt) D.base ∧
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
  obtain ⟨hct, hqc, hsep⟩ := hgeom G D
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
