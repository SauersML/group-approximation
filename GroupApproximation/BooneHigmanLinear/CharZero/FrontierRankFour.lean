import GroupApproximation.BooneHigmanLinear.CharZero.Frontier
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngEndpoint
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroTriOffEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# T3 in characteristic zero, with the base gap at rank four

Lane bh-met-90l proved `ElemFPCharZero.czTriOff_posStabGen_of_rankFour`. It closes the base
generation gap `hgen : CharZeroK2PosStabGenStatement` from one input: `K₂(4, ℤ[1/m])` is finitely
normally generated in `St_4(ℤ[1/m])` for `m ≥ 1` (`ElemFPCharZero.CZK2FngRankFourStatement`).
That input is true: `St_4(ℤ[1/m])` is finitely generated and `E_4(ℤ[1/m]) = SL_4(ℤ[1/m])` is
finitely presented (Behr; Borel–Serre).

With it, the characteristic-zero half of T3 needs the four gaps
`hH` (local Horrocks), `h4` (rank-four finite normal generation), `hcube` (the cube / nil gap)
and `hswap` (the cone-swap presentation of Higman's `V`). This file adds no new mathematics.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace CharZeroHalf

open GroupApproximation.BooneHigman
open GroupApproximation.BooneHigman.Metabelian

/-- **T3 in characteristic zero, base gap at rank four**: every finitely generated subgroup of
`GL_n(K)`, `char K = 0`, embeds in a finitely presented simple group, given local Horrocks,
finite normal generation of `K₂(4, ℤ[1/m])`, the cube gap over `ℤ[1/m]`, and the cone-swap
presentation of Higman's `V`. -/
theorem charZeroLinearStatement_of_frontier_rankFour
    (hH : Absorption.SuslinLocalHorrocksStatement)
    (h4 : ElemFPCharZero.CZK2FngRankFourStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hswap : Envelope.HigmanVSwapSectionStatement) : CharZeroLinearStatement :=
  charZeroLinearStatement_of_frontier hH (ElemFPCharZero.czTriOff_posStabGen_of_rankFour h4)
    hcube hswap

#audit_axioms charZeroLinearStatement_of_frontier_rankFour

end CharZeroHalf
end BooneHigmanLinear
end GroupApproximation
