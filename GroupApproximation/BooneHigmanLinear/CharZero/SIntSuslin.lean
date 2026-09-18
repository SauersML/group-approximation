import GroupApproximation.BooneHigmanLinear.CharZero.Frontier
import GroupApproximation.BooneHigman.Metabelian.ChainFiveCharZero
import GroupApproximation.BooneHigman.Metabelian.ChainFiveStableK2
import GroupApproximation.BooneHigman.Metabelian.CharZeroHost.Coords
import GroupApproximation.BooneHigman.Metabelian.SuslinMonicKaroubi
import GroupApproximation.BooneHigman.Metabelian.SuslinLocalGlobalPatching
import GroupApproximation.BooneHigman.Metabelian.AbsorptionSuslinEuclidInstances
import GroupApproximation.BooneHigman.Metabelian.AbsorptionEndpoint
import GroupApproximation.BooneHigman.Metabelian.AbsorptionSuslinReduction
import GroupApproximation.BooneHigman.Metabelian.SuslinLocalHorrocksStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# T3 in characteristic zero needs no characteristic-`p` input

The chain states local Horrocks, `Absorption.SuslinLocalHorrocksStatement`, for two coefficient
families at once: `F_p[s_0, …, s_{k-1}]` and `ℤ[1/m][t_0, …, t_{k-1}]`. Every reduction below
it (patching, the one-variable step, the induction on the number of variables) treats the two
families separately. So the characteristic-zero half of T3 uses only the `ℤ[1/m][t]` family.

* `SIntLocalHorrocksStatement` is the `ℤ[1/m][t]` half of local Horrocks. It is implied by the
  chain's statement (`sIntLocalHorrocks_of_localHorrocks`).
* `sIntSuslin_of_localHorrocks` is Suslin's `SL_N = E_N` over `ℤ[1/m][t_0, …, t_{k-1}]`, `N ≥ 3`,
  from that half alone. The induction on `k` starts at `SL_N(ℤ[1/m]) = E_N(ℤ[1/m])`, which is
  proved in the corpus by Euclidean division (`Absorption.specialLinearInElementary_away`).
* `charZeroLinearStatement_of_sIntFrontier` is the characteristic-zero half of T3 from four
  statements. None mentions a field of positive characteristic:
  - the `ℤ[1/m][t]` half of local Horrocks;
  - base generation and the cube gap for `K₂` over `ℤ[1/m]`;
  - the cone-swap presentation of Higman's `V`.

Every proof is a composition of existing reductions, split by family. This file adds no new
mathematics.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace CharZeroHalf

open GroupApproximation.BooneHigman
open GroupApproximation.BooneHigman.Metabelian

/-- **Local Horrocks over `ℤ[1/m][t_0, …, t_{k-1}]`**: the characteristic-zero half of
`Absorption.SuslinLocalHorrocksStatement`. -/
def SIntLocalHorrocksStatement : Prop :=
  ∀ (m k N : ℕ),
    (∀ N' : ℕ, 3 ≤ N' → Absorption.SpecialLinearInElementary (Chain.SIntPoly m k) N') →
      3 ≤ N →
        Absorption.SuslinLocalHorrocksLocallyQuillen (Chain.SIntPoly m k) N

#audit_axioms SIntLocalHorrocksStatement

/-- The chain's two-family statement gives the characteristic-zero half. -/
theorem sIntLocalHorrocks_of_localHorrocks (h : Absorption.SuslinLocalHorrocksStatement) :
    SIntLocalHorrocksStatement :=
  h.2

#audit_axioms sIntLocalHorrocks_of_localHorrocks

/-- **Suslin over `ℤ[1/m][t]` from its own local Horrocks half**: `SL_N = E_N` over
`ℤ[1/m][t_0, …, t_{k-1}]` for `N ≥ 3`. -/
theorem sIntSuslin_of_localHorrocks (h : SIntLocalHorrocksStatement) (m k : ℕ) :
    ∀ N : ℕ, 3 ≤ N → Absorption.SpecialLinearInElementary (Chain.SIntPoly m k) N := by
  induction k with
  | zero =>
      intro N hN
      exact Absorption.suslin_mvPolynomial_zero (Localization.Away (m : ℤ))
        (Absorption.specialLinearInElementary_away m (by omega))
  | succ k IH =>
      intro N hN
      exact Absorption.suslin_mvPolynomial_succ (Localization.Away (m : ℤ)) k
        (Absorption.suslinMonic_specialLinearInElementary_polynomial_of_normalized (IH N hN)
          (Absorption.suslinNormalized_of_locallyQuillen
            (Absorption.suslinLocallyQuillen_of_localHorrocks
              (h m k N IH hN))))

#audit_axioms sIntSuslin_of_localHorrocks

/-- Absorption `GL_M(S) ↪ E_N(S)` over `S = ℤ[1/m][t]`, `N ≥ 3`, `N ≥ 2M`, from the
characteristic-zero half of local Horrocks. -/
theorem charZeroAbsorption_of_sIntLocalHorrocks (h : SIntLocalHorrocksStatement) :
    Chain.CharZeroElementaryAbsorptionStatement :=
  fun m k _ N hN hMN =>
    Absorption.exists_injective_hom_elementaryGroup (Chain.SIntPoly m k) hMN
      (sIntSuslin_of_localHorrocks h m k N hN)

#audit_axioms charZeroAbsorption_of_sIntLocalHorrocks

/-- The characteristic-zero linear host from characteristic-zero inputs only. -/
theorem charZeroLinearHost_of_sIntFrontier (hH : SIntLocalHorrocksStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement) : Chain.CharZeroLinearHostStatement :=
  Chain.charZeroLinearHostStatement_of_chainFive
    (CharZeroHost.coordinatesStatement_of_fgSubring CharZeroHost.fgSubringCoordinates)
    (charZeroAbsorption_of_sIntLocalHorrocks hH)
    (Chain.charZeroElementaryFPFive_of_stableK2FG
      (ElemFPCharZero.charZeroStableK2FG_of_basePos_of_cubeGapPos
        (ElemFPCharZero.charZeroK2BasePos_of_stabGen hgen) hcube))
    Chain.affineExtensionFPStatement_holds CharZeroHost.charZeroAffineSelfSimilarStatement

#audit_axioms charZeroLinearHost_of_sIntFrontier

/-- **T3 in characteristic zero, characteristic-zero inputs only**: every finitely generated
subgroup of `GL_n(K)`, `char K = 0`, embeds in a finitely presented simple group, given local
Horrocks over `ℤ[1/m][t]`, base generation and the cube gap for `K₂` over `ℤ[1/m]`, and the
cone-swap presentation of Higman's `V`. -/
theorem charZeroLinearStatement_of_sIntFrontier (hH : SIntLocalHorrocksStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hswap : Envelope.HigmanVSwapSectionStatement) : CharZeroLinearStatement :=
  charZeroLinearStatement_of_host (charZeroLinearHost_of_sIntFrontier hH hgen hcube)
    (fpSelfSimilarEnvelope_of_swapSection hswap)

#audit_axioms charZeroLinearStatement_of_sIntFrontier

end CharZeroHalf
end BooneHigmanLinear
end GroupApproximation
