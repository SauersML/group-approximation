import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.SimplyConnected
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.Relations
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Frame.FourBridge
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan.FrameComplex
import GroupApproximation.Meta.AxiomGuard

/-!
# Brown bridge V: the frame cone gives lane 14's Brown extension (lane sk-leavitt-20)

Endpoint (b): `brownExtension_of_frameConeFour :
FrameFan.BinaryLeavittFrameConeFourStatement → Criterion.BrownExtensionStatement`.

Route.
* `frame_bijective`: lane 10 turns the frame cone into simple connectivity of
  `FrameFan.frameComplexFour L`; lane 07's `frameVertexFourEquiv`, `frameComplexFour_edge_iff`
  and `frameComplexFour_tri_iff` identify that complex with the complex of `frameSetting`, so
  `brownMap_bijective_of_twoComplex` (lane 12's `brownMap_injective` plus surjectivity from
  connectivity) makes Brown's map `Π →* GL₄(L)` bijective.
* `frameEquiv : Π ≃* GL₄(L)`, sending `incl j ↦ j` and `T ↦ τ = swapLast`.
* Given `f`, `t` with the edge and triangle relations, `F := bridgeLift f t ∘ frameEquiv⁻¹`
  satisfies `F j = f j` (`frameEquiv_symm_incl`, `bridgeLift_incl`, `jHom_mk`) and
  `F swapLast = t` (`frameEquiv_symm_swapLast`, `bridgeLift_T`).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge

open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Criterion

noncomputable section

/-- The frame cone makes Brown's map `Π →* GL₄(L)` bijective. -/
theorem frame_bijective (h : FrameFan.BinaryLeavittFrameConeFourStatement) :
    Function.Bijective frameSetting.brownMap :=
  brownMap_bijective_of_twoComplex (X := FrameFan.frameComplexFour BinL) frameSetting
    (frameVertexFourEquiv (A := BinL))
    (fun u w => frameComplexFour_edge_iff u w)
    (fun u v w ht => (frameComplexFour_tri_iff u v w).1 ht)
    (FrameFan.binaryLeavitt_frameComplexFour_simplyConnected_of_frameConeFour h)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.frame_bijective

/-- Brown's isomorphism `Π ≃* GL₄(L)`. -/
def frameEquiv (h : FrameFan.BinaryLeavittFrameConeFourStatement) :
    frameSetting.PiGroup ≃* GLFour :=
  MulEquiv.ofBijective frameSetting.brownMap (frame_bijective h)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.frameEquiv

theorem frameEquiv_symm_incl (h : FrameFan.BinaryLeavittFrameConeFourStatement)
    (j : vertexStab) :
    (frameEquiv h).symm (j : GLFour) = frameSetting.incl ⟨j, mem_J_of_mem_vertexStab j.2⟩ := by
  rw [MulEquiv.symm_apply_eq]
  exact (frameSetting.p_incl ⟨j, mem_J_of_mem_vertexStab j.2⟩).symm

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.frameEquiv_symm_incl

theorem frameEquiv_symm_swapLast (h : FrameFan.BinaryLeavittFrameConeFourStatement) :
    (frameEquiv h).symm swapLast = frameSetting.T := by
  rw [MulEquiv.symm_apply_eq, swapLast_eq_frameTau]
  exact frameSetting.p_T.symm

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.frameEquiv_symm_swapLast

/-- **Endpoint (b).**  The rank-four frame cone implies lane 14's Brown extension property. -/
theorem brownExtension_of_frameConeFour (h : FrameFan.BinaryLeavittFrameConeFourStatement) :
    BrownExtensionStatement := by
  intro f t hE hT
  refine ⟨(bridgeLift f t hE hT).comp (frameEquiv h).symm.toMonoidHom, fun j => ?_, ?_⟩
  · show bridgeLift f t hE hT ((frameEquiv h).symm (j : GLFour)) = f j
    rw [frameEquiv_symm_incl, bridgeLift_incl, jHom_mk]
  · show bridgeLift f t hE hT ((frameEquiv h).symm swapLast) = t
    rw [frameEquiv_symm_swapLast, bridgeLift_T]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.brownExtension_of_frameConeFour

end

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge
