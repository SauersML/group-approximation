import GroupApproximation.BooneHigman.Metabelian.ElemFPNK2UnifyStatement
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHmClosedWire
import GroupApproximation.Meta.AxiomGuard

/-!
# The Boone–Higman metabelian root with one `NK₂` cone residual

Lane `bh-met-90i`, wire module.  `nk2Unify_ConeStatement` is `czNK2_ConeOverStatement A` over
`A = ℤ[1/m]` (`m ≥ 1`) and over `A = F_p` (`p` prime).  Module `ElemFPNK2UnifyStatement` shows
that its `F_p` half gives `hloc = PolyK2CubeNilLocalStatement` without the dilation residual.

* `nk2Unify_polyK2CubeNilLocal`, `nk2Unify_gapPos`: the root hypotheses `hloc` and (with the
  stability half) `hcube`.
* `nk2Unify_cone_of_k2CubeDilate`: the old sub-gaps L, D, C give the new residual, so the new
  frontier is no stronger than the old one.
* `nk2Unify_cone_iff`: **LOUD**, the residual is logically equivalent to `hloc ∧ C`.  It is not
  strictly weaker logically; it is strictly smaller in proof content (cone images at minimal
  rank only, no Tulenbaev dilation) and removes D from the frontier.
* `Envelope.nk2Unify_finitelyPresentedMetabelian`: the root with hypotheses
  `hH, hvdk, hgen, hU, hstab, hswap`.  Against `hmClosed_finitelyPresentedMetabelian_of_six`
  with `hloc ← L, D` and `hcube ← C, hstab`, the three `NK₂` sub-gaps L, D, C become `hU`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.Metabelian.ElemFP

/-- **The unified `NK₂` cone residual**: the cone residual `czNK2_ConeOverStatement A` over every
`ℤ[1/m]`, `m ≥ 1`, and over every prime field `F_p`. -/
def nk2Unify_ConeStatement : Prop :=
  czNK2_ConeStatement ∧ nk2Unify_CharPConeStatement

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Unify_ConeStatement

/-- The unified residual gives the root hypothesis `hloc`. -/
theorem nk2Unify_polyK2CubeNilLocal (h : nk2Unify_ConeStatement) :
    PolyK2CubeNilLocalStatement :=
  nk2Unify_polyK2CubeNilLocal_of_charPCone h.2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Unify_polyK2CubeNilLocal

/-- The unified residual and the stability half give the root hypothesis `hcube`. -/
theorem nk2Unify_gapPos (h : nk2Unify_ConeStatement)
    (hstab : ∀ m : ℕ, 0 < m → CZCubePosStabOverStatement (Localization.Away (m : ℤ))) :
    CharZeroK2CubeGapPosStatement :=
  czNK2_gapPos_of_cone_of_cubeStab h.1 hstab

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Unify_gapPos

/-- The old sub-gaps L, D (lane `bh-met-90c`) and C (lane `bh-met-90g`) give the unified
residual. -/
theorem nk2Unify_cone_of_k2CubeDilate (hL : k2CubeDilate_LocalStatement)
    (hD : k2CubeDilate_PolyDilationStatement) (hC : czNK2_ConeStatement) :
    nk2Unify_ConeStatement :=
  ⟨hC, nk2Unify_charPCone_of_k2CubeDilate hL hD⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Unify_cone_of_k2CubeDilate

/-- **LOUD**: the unified residual is logically equivalent to `hloc ∧ C`. -/
theorem nk2Unify_cone_iff :
    nk2Unify_ConeStatement ↔ PolyK2CubeNilLocalStatement ∧ czNK2_ConeStatement :=
  ⟨fun h ↦ ⟨nk2Unify_polyK2CubeNilLocal h, h.1⟩,
    fun h ↦ ⟨h.2, nk2Unify_charPCone_of_polyK2CubeNilLocal h.1⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Unify_cone_iff

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **The root with one `NK₂` cone residual.**  The hypotheses `hloc` and `hcube` of
`hmClosed_finitelyPresentedMetabelian_of_six` are replaced by the unified cone residual `hU`
and the stability half `hstab`. -/
theorem nk2Unify_finitelyPresentedMetabelian
    (hH : Absorption.SuslinLocalHorrocksStatement)
    (hvdk : ElemFP.VdKRowExtensionStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hU : ElemFPCharZero.nk2Unify_ConeStatement)
    (hstab : ∀ m : ℕ, 0 < m →
      ElemFPCharZero.CZCubePosStabOverStatement (Localization.Away (m : ℤ)))
    (hswap : HigmanVSwapSectionStatement) : FinitelyPresentedMetabelianStatement :=
  hmClosed_finitelyPresentedMetabelian_of_six hH hvdk
    (ElemFPCharZero.nk2Unify_polyK2CubeNilLocal hU) hgen
    (ElemFPCharZero.nk2Unify_gapPos hU hstab) hswap

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.nk2Unify_finitelyPresentedMetabelian

end GroupApproximation.BooneHigman.Metabelian.Envelope
