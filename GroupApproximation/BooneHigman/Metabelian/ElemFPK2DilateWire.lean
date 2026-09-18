import GroupApproximation.BooneHigman.Metabelian.ElemFPK2DilateStatement
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2CubeDilateEndpoint
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHmClosedWire
import GroupApproximation.Meta.AxiomGuard

/-!
# The cube gap from the local step and dilation on `K₂`

Lane `bh-met-90h`, wire module.

* `k2Dilate_polyK2CubeNilLocal (hL) (hR)`: `PolyK2CubeNilLocalStatement` from the local residual
  `k2CubeDilate_LocalStatement` and the `K₂` dilation residual `k2Dilate_PolyK2Statement`.  The
  argument is that of `polyK2CubeNilLocal_of_k2CubeDilate`.  The element `g = v_1(ψ u)` to which
  dilation is applied is the underlying element of the Quillen difference `quillenDiff (ψ u) 1`,
  so it lies in `K₂`.  Its rank `N` satisfies `N ≥ k + 5 ≥ 5`.
* `k2Dilate_polyK2CubeNilLocal_of_dilation`: the same with the general dilation residual D in
  place of the `K₂` one (via `k2Dilate_polyK2_of_polyDilation`).
* `Envelope.k2Dilate_hmClosed_finitelyPresentedMetabelian`: the Boone–Higman root
  `hmClosed_finitelyPresentedMetabelian_of_six`, with `hloc` replaced by `hL` and `hR`.

## LOUD

D is **not** closed.  `hloc` is reduced to `hL` together with `hR`.  `hR` is Tulenbaev's lemma
on `K₂` elements in rank `≥ 5` over `F_p[s_1..s_k][t]`.  It is true (Tulenbaev; or Quillen
`NK₂ = 0` with `r = 0`).  It is implied by D.  Over the proved torsion and padding steps, it
implies D at every `p` (`k2Dilate_polyDilation_of_allK2`).  So it is equivalent to D in content,
minus the proved non-`K₂` part.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

/-- **Endpoint**: the cube gap `hloc` from the local residual and `K₂` dilation. -/
theorem k2Dilate_polyK2CubeNilLocal (hL : k2CubeDilate_LocalStatement)
    (hR : k2Dilate_PolyK2Statement) : PolyK2CubeNilLocalStatement := by
  intro p hp k N hkN u hu m hm
  obtain ⟨s₀, hs₀, hloc⟩ := hL p hp k N hkN u hu m hm
  have hev := k2CubeDilate_evalZero_stDiff
    (SteinbergGroup.ringMap (MvPolynomial.finSuccEquiv (ZMod p) k).toRingEquiv.toRingHom
      (u : SteinbergGroup (Fin N) (MvPolynomial (Fin (k + 1)) (ZMod p)))) 1
  have hlocg := k2CubeDilate_stDies_loc_stDiff
    (SteinbergGroup.ringMap (MvPolynomial.finSuccEquiv (ZMod p) k).toRingEquiv.toRingHom
      (u : SteinbergGroup (Fin N) (MvPolynomial (Fin (k + 1)) (ZMod p)))) s₀ 1 hloc
  have hK := SetLike.coe_mem
    (quillenDiff (K2Map (MvPolynomial.finSuccEquiv (ZMod p) k).toRingEquiv.toRingHom u) 1)
  rw [cubeDiagDilate_coe_quillenDiff, K2Map_apply] at hK
  obtain ⟨r, hr⟩ := hR p hp k s₀ N (by omega) _ hK hev hlocg
  refine ⟨s₀ ^ r, fun h ↦ hs₀ (hm.isPrime.mem_of_pow_mem r h), ?_⟩
  rw [k2CubeDilate_ringMap_scale_stDiff, mul_one] at hr
  rw [cubeDiagDilate_diesAfterPadding_iff, cubeDiagDilate_coe_quillenDiff, K2Map_apply]
  exact hr

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Dilate_polyK2CubeNilLocal

/-- The endpoint with the general dilation residual D in place of its `K₂` case. -/
theorem k2Dilate_polyK2CubeNilLocal_of_dilation (hL : k2CubeDilate_LocalStatement)
    (hD : k2CubeDilate_PolyDilationStatement) : PolyK2CubeNilLocalStatement :=
  k2Dilate_polyK2CubeNilLocal hL (k2Dilate_polyK2_of_polyDilation hD)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.k2Dilate_polyK2CubeNilLocal_of_dilation

end GroupApproximation.BooneHigman.Metabelian.ElemFP

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Boone–Higman root, `K₂`-dilation form**: `hloc` is replaced by the local residual `hL` and
the `K₂` dilation residual `hR`. -/
theorem k2Dilate_hmClosed_finitelyPresentedMetabelian
    (hH : Absorption.SuslinLocalHorrocksStatement)
    (hvdk : ElemFP.VdKRowExtensionStatement)
    (hL : ElemFP.k2CubeDilate_LocalStatement)
    (hR : ElemFP.k2Dilate_PolyK2Statement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hswap : HigmanVSwapSectionStatement) : FinitelyPresentedMetabelianStatement :=
  hmClosed_finitelyPresentedMetabelian_of_six hH hvdk (ElemFP.k2Dilate_polyK2CubeNilLocal hL hR)
    hgen hcube hswap

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.k2Dilate_hmClosed_finitelyPresentedMetabelian

end GroupApproximation.BooneHigman.Metabelian.Envelope
