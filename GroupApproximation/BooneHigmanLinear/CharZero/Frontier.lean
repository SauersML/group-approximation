import GroupApproximation.BooneHigman.Statement.Basic
import GroupApproximation.BooneHigman.Products.Hosts
import GroupApproximation.BooneHigman.Metabelian.ChainWiredFrontierTwoBase
import GroupApproximation.BooneHigman.Metabelian.ChainWiredFrontierTwo
import GroupApproximation.BooneHigman.Metabelian.SuslinLocalHorrocksStatement
import GroupApproximation.BooneHigman.Metabelian.SuslinMonicPatching
import GroupApproximation.BooneHigman.Metabelian.AbsorptionSuslinReduction
import GroupApproximation.BooneHigman.Metabelian.ElemFPZInvK2Endpoint
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2PosStabGen
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVGenReduce
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVSection
import GroupApproximation.BooneHigman.Metabelian.EnvelopeNormalFormSection
import GroupApproximation.BooneHigman.Metabelian.EnvelopeRelatorsFiniteStatement
import GroupApproximation.BooneHigman.Metabelian.EnvelopeRelatorsNormalFormFinal
import GroupApproximation.BooneHigman.Metabelian.EnvelopeGenTorsion
import GroupApproximation.BooneHigman.Metabelian.EnvelopeVPerfect
import GroupApproximation.Meta.AxiomGuard

/-!
# T3 in characteristic zero, from four gap Statements

`CharZeroLinearStatement` is T3 (`BooneHigman.FinitelyGeneratedLinearStatement`) restricted to
fields of characteristic zero. It says that every finitely generated subgroup of `GL_n(K)`,
`char K = 0`, embeds in a finitely presented simple group. The published case is finitely
generated subgroups of `GL_n(ℚ)` (Zaremsky). Here `K` is any field of characteristic zero, for
example `ℚ(t)`, `ℂ` or a number field.

`charZeroLinearStatement_of_frontier` proves it from four Statements of the metabelian chain:

* `hH : Absorption.SuslinLocalHorrocksStatement`, local Horrocks (for Suslin's `SL_N = E_N`);
* `hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement`, base generation for stable `K₂` over
  `ℤ[1/m]`;
* `hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement`, the cube / nil gap for `K₂` over
  `ℤ[1/m][t]`;
* `hswap : Envelope.HigmanVSwapSectionStatement`, a finite presentation of Higman's `V_d`
  through cone swaps.

The full T3 wiring (`BooneHigmanLinear.finitelyGeneratedLinearStatement_of_frontierFour`, lane
bh-pal-wire) needs these four and also the two characteristic-`p` gaps `ElemFP.VdKRowExtension`
and `ElemFP.PolyK2CubeNilLocal`. The characteristic-zero half needs neither. `hH` is stated for
both coefficient families, `ℤ[1/m][t]` and `F_p[t]`, because the chain states it that way.

Everything else is supplied by proved endpoints:

* the coordinates `CharZeroHost.fgSubringCoordinates`, inside
  `Chain.charZeroLinearHostStatement_of_frontierTwo`;
* the relator core `Envelope.rnNF_finiteCore`;
* the perfection of `V` `Envelope.genTorsionVPerfect`;
* fragmentation, compression and the wreath embedding, inside
  `Chain.fpSelfSimilarEnvelope_of_frontierTwo`.

The reductions are the ones in `Metabelian/ChainWiredFrontierThree.lean`. This file adds no new
mathematics.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace CharZeroHalf

open GroupApproximation.BooneHigman
open GroupApproximation.BooneHigman.Metabelian

/-- **T3 in characteristic zero**: every finitely generated subgroup of `GL_n(K)`, for a field `K`
of characteristic zero, embeds in a finitely presented simple group. -/
def CharZeroLinearStatement : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (n : ℕ)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)),
    H.FG → EmbedsInFinitelyPresentedSimpleGroup H

#audit_axioms CharZeroLinearStatement

/-- T3 implies its characteristic-zero half. -/
theorem charZeroLinearStatement_of_finitelyGeneratedLinear
    (h : FinitelyGeneratedLinearStatement) : CharZeroLinearStatement :=
  fun K _ _ n H hH => h K n H hH

#audit_axioms charZeroLinearStatement_of_finitelyGeneratedLinear

/-- The characteristic-zero half from the characteristic-zero linear host and the self-similar
envelope (Zaremsky's theorem). -/
theorem charZeroLinearStatement_of_host (hlin : Chain.CharZeroLinearHostStatement)
    (henv : Products.FPSelfSimilarEnvelopeStatement) : CharZeroLinearStatement :=
  fun K _ _ n H hH => (hlin K n H hH).embedsInFinitelyPresentedSimpleGroup henv

#audit_axioms charZeroLinearStatement_of_host

/-- The self-similar envelope from the single open envelope gap `hswap`: the relator core and the
perfection of `V` are proved. -/
theorem fpSelfSimilarEnvelope_of_swapSection (hswap : Envelope.HigmanVSwapSectionStatement) :
    Products.FPSelfSimilarEnvelopeStatement :=
  Chain.fpSelfSimilarEnvelope_of_frontierTwo
    (Envelope.higmanVFinSection_of_swapSection hswap)
    (Envelope.rnFreeSectionCore_of_normalForm
      (Envelope.higmanVFP_of_finSection (Envelope.higmanVFinSection_of_swapSection hswap))
      (Envelope.rnNormalFormRelators_of_finiteCore Envelope.rnNF_finiteCore))
    (Envelope.rnFiniteIndex_of_vPerfect Envelope.genTorsionVPerfect)

#audit_axioms fpSelfSimilarEnvelope_of_swapSection

/-- The characteristic-zero linear host from its three open gaps. -/
theorem charZeroLinearHost_of_frontier (hH : Absorption.SuslinLocalHorrocksStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement) : Chain.CharZeroLinearHostStatement :=
  Chain.charZeroLinearHostStatement_of_frontierTwo
    (Absorption.polynomialSuslin_of_oneVariable
      (Absorption.suslinOneVariable_of_patching (Absorption.suslinPatching_of_localHorrocks hH)))
    (ElemFPCharZero.charZeroStableK2FG_of_basePos_of_cubeGapPos
      (ElemFPCharZero.charZeroK2BasePos_of_stabGen hgen) hcube)

#audit_axioms charZeroLinearHost_of_frontier

/-- **T3 in characteristic zero from four gaps**: every finitely generated subgroup of `GL_n(K)`,
`char K = 0`, embeds in a finitely presented simple group, given local Horrocks, base generation
and the cube gap for `K₂` over `ℤ[1/m]`, and the cone-swap presentation of Higman's `V`. -/
theorem charZeroLinearStatement_of_frontier (hH : Absorption.SuslinLocalHorrocksStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hswap : Envelope.HigmanVSwapSectionStatement) : CharZeroLinearStatement :=
  charZeroLinearStatement_of_host (charZeroLinearHost_of_frontier hH hgen hcube)
    (fpSelfSimilarEnvelope_of_swapSection hswap)

#audit_axioms charZeroLinearStatement_of_frontier

end CharZeroHalf
end BooneHigmanLinear
end GroupApproximation
