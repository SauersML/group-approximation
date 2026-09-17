import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.Triangle
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.RootLift
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Criterion
import GroupApproximation.Meta.AxiomGuard

/-!
# Edge and triangle lifts VI: the endpoint (lane sk-leavitt-13)

Carto `sk-leavitt` lane 13 (`LK2/EdgeTriangleLift`).  Khanh (arXiv:2609.08428), proof of
Theorem 5.1.  Lane 05's section `σ = VertexLift.vertexSection h : J → St_4(L)`, together with
`T ↦ w₃₂`, satisfies Brown's edge and triangle relations.

* `sectionJ_edge_relation`: `w₃₂ σ(k) w₃₂⁻¹ = σ(τ k τ⁻¹)` for `k ∈ K = J ∩ Stab(e₂)`.
* `weyl_triangle_relation`: `w₃₂ σ(h) w₃₂ = σ(h) w₃₂ σ(h)` for `h = swapMid`.
* `projection_weyl`: `w₃₂` maps to `τ`, the Weyl monomial `x₃₂(1) x₂₃(-1) x₃₂(1)`.
* `rankFourLift`: lane 14's input `Criterion.RankFourLiftStatement`.
* `rankFourInjective_of_stabKernelThreeTrivial_of_brownExtension`: the lift half of lane 14's
  inputs is now closed.  Only `Criterion.BrownExtensionStatement` (lanes 06–12) remains.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Criterion
open scoped Matrix

/-- Lane 05's vertex section lifts the roots. -/
theorem liftsRoots_vertexSection
    (h : EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement) :
    LiftsRoots (VertexLift.vertexSection h) :=
  liftsRoots_sectionJ h VertexLift.rowVecStabConj

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.liftsRoots_vertexSection

/-- **Lane 13 endpoint: the edge relation.**  For `k ∈ K` (`k e₂ = e₂`) and `k' = τ k τ⁻¹`,
`w₃₂ σ(k) w₃₂⁻¹ = σ(k')`. -/
theorem sectionJ_edge_relation
    (h : EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement) (k k' : vertexStab)
    (hk : ((k : GLFour) : Matrix (Fin 4) (Fin 4) BinL) *ᵥ prevCol = prevCol)
    (hk' : (k' : GLFour) = swapLast * (k : GLFour) * swapLast⁻¹) :
    weylLast * VertexLift.vertexSection h k * weylLast⁻¹ = VertexLift.vertexSection h k' :=
  edgeRelation_of_liftsRoots _ (liftsRoots_vertexSection h) k k' hk hk'

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.sectionJ_edge_relation

/-- **Lane 13 endpoint: the triangle relation.**  For `j = h = swapMid`,
`w₃₂ σ(h) w₃₂ = σ(h) w₃₂ σ(h)`. -/
theorem weyl_triangle_relation
    (h : EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement) (j : vertexStab)
    (hj : (j : GLFour) = swapMid) :
    weylLast * VertexLift.vertexSection h j * weylLast =
      VertexLift.vertexSection h j * weylLast * VertexLift.vertexSection h j :=
  triangleRelation_of_liftsRoots _ (liftsRoots_vertexSection h) j hj

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.weyl_triangle_relation

/-- **Lane 13 endpoint: `w₃₂ ↦ τ`.**  The image of `w₃₂` in `GL_4(L)` is the Weyl monomial
`x₃₂(1) x₂₃(-1) x₃₂(1)`, i.e. `swapLast = weylUnit 3 2`. -/
theorem projection_weyl :
    ((projection weylLast : elementaryGroup (Fin 4) BinL) : GLFour) =
      ElementaryWeyl.weylUnit (3 : Fin 4) 2 lastIdx_ne :=
  projection_weyl_three_two two_eq_zero_binL lastIdx_ne

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.projection_weyl

/-- **Lane 14's lift input**: the vertex section lifts the roots and satisfies Brown's edge and
triangle relations. -/
theorem rankFourLift : RankFourLiftStatement := fun h =>
  ⟨VertexLift.vertexSection h, liftsRoots_vertexSection h,
    edgeRelation_of_liftsRoots _ (liftsRoots_vertexSection h),
    triangleRelation_of_liftsRoots _ (liftsRoots_vertexSection h)⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.rankFourLift

/-- **Reduction of lane 14 to Brown's extension property.**  Given
`Criterion.BrownExtensionStatement`, `stab (K₂(3, L)) = ⊥` implies `K₂(4, L) = ⊥`. -/
theorem rankFourInjective_of_stabKernelThreeTrivial_of_brownExtension
    (hB : BrownExtensionStatement) :
    EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement →
      LeavittFP.BinaryLeavittSteinbergRankFourInjectiveStatement :=
  rankFourInjective_of_stabKernelThreeTrivial ⟨hB, rankFourLift⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.rankFourInjective_of_stabKernelThreeTrivial_of_brownExtension

/-- The interface form of the reduction. -/
theorem rankFourInjectiveOfStabKernelThreeTrivial_of_brownExtension
    (hB : BrownExtensionStatement) :
    EndpointInterfaces.RankFourInjectiveOfStabKernelThreeTrivialStatement :=
  rankFourInjectiveOfStabKernelThreeTrivial_of_criterionInputs ⟨hB, rankFourLift⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.rankFourInjectiveOfStabKernelThreeTrivial_of_brownExtension

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift
