import GroupApproximation.BooneHigmanLinear.CharZero.ElementaryFactor
import GroupApproximation.BooneHigmanLinear.CharZero.Frontier
import GroupApproximation.BooneHigman.Metabelian.CharZeroCoordsAssembly
import GroupApproximation.BooneHigman.Metabelian.CharZeroHost.Endpoint
import GroupApproximation.BooneHigman.Metabelian.ChainWiredAffine
import GroupApproximation.BooneHigman.Metabelian.ChainFiveCharZero
import GroupApproximation.BooneHigman.Metabelian.ChainFiveStableK2
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2Split
import GroupApproximation.Meta.AxiomGuard

/-!
# The characteristic-zero linear host without Suslin's theorem

`charZeroElementaryCoordinates` is a closed theorem with no hypotheses. A finitely generated
subgroup of `GL_n(K)`, `char K = 0`, embeds in the elementary group
`E_N(ℤ[1/m][t_0, …, t_{k-1}])` for some `m`, `k` and `N ≥ k + 5`. The proof follows
`NoSuslin.exists_finset_elementary_embedding`: factor over the field first, then pick the finite
set of entries and coefficients. The coordinates `CharZeroHost.fgSubringCoordinates` are applied to
that set, and `NoSuslin.exists_elementary_transport` carries `E_N` across the matrix embedding.

The chain's host (`Chain.charZeroLinearHostStatement_of_chainFive`) needs two inputs to reach
`E_N`: coordinates in `GL_M` and absorption `GL_M ↪ E_N`. Absorption is Suslin's theorem
`SL_N(ℤ[1/m][t]) = E_N`, owed on route A as `S1`. This file uses neither.

So `charZeroLinearHost_of_elementaryFPFive` gets the characteristic-zero linear host from the
finite presentation of `E_N(ℤ[1/m][t])` alone. That is `Chain.CharZeroElementaryFPFiveStatement`,
and on route A it follows from `Z1 = ElemFPCharZero.CharZeroK2SplitGapStatement`. The affine
extension, the self-similar tree action and the coordinates are proved leaves of the chain.

Consequences, in terms of the route-A owed inputs:
* `charZeroLinearHost_of_splitGap`: the characteristic-zero linear host from `Z1` alone;
* `charZeroLinearStatement_of_splitGap`: T3 over fields of characteristic zero from `Z1` and the
  self-similar envelope. On route A the envelope is `H1`, via `BooneHigmanLinear.envelope_routeA`.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace NoSuslin

open GroupApproximation.BooneHigman
open GroupApproximation.BooneHigman.Metabelian

/-- **Elementary polynomial coordinates in characteristic zero**: every finitely generated subgroup
of `GL_n(K)`, `char K = 0`, embeds in `E_N(ℤ[1/m][t_0, …, t_{k-1}])` for some `m`, `k` and
`N ≥ k + 5`. -/
def CharZeroElementaryCoordinatesStatement : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (n : ℕ)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)), H.FG →
      ∃ m k N : ℕ, k + 5 ≤ N ∧
        ∃ f : H →* elementaryGroup (Fin N) (Chain.SIntPoly m k), Function.Injective f

#audit_axioms CharZeroElementaryCoordinatesStatement

/-- **Elementary polynomial coordinates in characteristic zero, proved.** No Suslin input. -/
theorem charZeroElementaryCoordinates : CharZeroElementaryCoordinatesStatement := by
  intro K _ _ n H hH
  haveI : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hH
  obtain ⟨s, hs⟩ := exists_finset_elementary_embedding H.subtype H.subtype_injective
  obtain ⟨φ, hφ⟩ := hs (Subring.closure (↑s : Set K)) Subring.subset_closure
  obtain ⟨m, k, d, Φ, hΦ⟩ := CharZeroHost.fgSubringCoordinates K s
  obtain ⟨f, hf⟩ := exists_elementary_transport (N := 2 * n + 2) (by omega) Φ hΦ (k + 5)
  exact ⟨m, k, (2 * n + 2) * d + (k + 5), by omega, f.comp φ, hf.comp hφ⟩

#audit_closed_axioms charZeroElementaryCoordinates

/-- **The characteristic-zero linear host from finite presentation of `E_N` alone.** Every
finitely generated subgroup of `GL_n(K)`, `char K = 0`, embeds in a finitely presented
self-similar group, given only that `E_N(ℤ[1/m][t_0, …, t_{k-1}])` is finitely presented for
`N ≥ k + 4`, `N ≥ 5`. -/
theorem charZeroLinearHost_of_elementaryFPFive (hfp : Chain.CharZeroElementaryFPFiveStatement) :
    Chain.CharZeroLinearHostStatement := by
  intro K _ _ n H hH
  obtain ⟨m, k, N, hN, f, hf⟩ := charZeroElementaryCoordinates K n H hH
  haveI : Group.IsFinitelyPresented (Chain.AffineElementaryGroup N (Chain.SIntPoly m k)) :=
    Chain.affineExtensionFPStatement_holds (Chain.SIntPoly m k)
      (Chain.finiteType_int_transfer _ (Chain.sIntPoly_finiteType m k) _) N (by omega)
      (hfp m k N (by omega) (by omega))
  obtain ⟨X, _, _, ρ, hρ⟩ := CharZeroHost.charZeroAffineSelfSimilarStatement m k N (by omega)
  exact Chain.embedsInFPSelfSimilarGroup_of_affineHost (X := X) ρ hρ hf

#audit_axioms charZeroLinearHost_of_elementaryFPFive

/-- **The characteristic-zero linear host from `Z1` alone** (route A without `S1`). -/
theorem charZeroLinearHost_of_splitGap (hZ1 : ElemFPCharZero.CharZeroK2SplitGapStatement) :
    Chain.CharZeroLinearHostStatement :=
  charZeroLinearHost_of_elementaryFPFive
    (Chain.charZeroElementaryFPFive_of_stableK2FG
      (ElemFPCharZero.charZeroStableK2FG_of_splitGap hZ1))

#audit_axioms charZeroLinearHost_of_splitGap

/-- **T3 in characteristic zero from `Z1` and the envelope**: every finitely generated subgroup of
`GL_n(K)`, `char K = 0`, embeds in a finitely presented simple group. -/
theorem charZeroLinearStatement_of_splitGap (hZ1 : ElemFPCharZero.CharZeroK2SplitGapStatement)
    (henv : Products.FPSelfSimilarEnvelopeStatement) : CharZeroHalf.CharZeroLinearStatement :=
  CharZeroHalf.charZeroLinearStatement_of_host (charZeroLinearHost_of_splitGap hZ1) henv

#audit_axioms charZeroLinearStatement_of_splitGap

end NoSuslin
end BooneHigmanLinear
end GroupApproximation
