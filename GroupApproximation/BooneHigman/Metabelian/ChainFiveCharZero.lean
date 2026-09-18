import GroupApproximation.BooneHigman.Metabelian.ChainAssembly
import GroupApproximation.Meta.AxiomGuard

/-!
# Chain skeleton over the rank-at-least-five elementary leaf

Lane `bh-met-25`.  The characteristic-zero composition `charZeroLinearHostStatement_of_chain`
uses `CharZeroElementaryFPStatement` at the single rank `N = k + 4 + 2 * M`.  It does not need that
exact rank.  The absorption leaf needs `3 ≤ N` and `2 * M ≤ N`, the affine host leaf needs `4 ≤ N`,
and the self-similarity leaf needs `1 ≤ N`.  So the rank `N = k + 5 + 2 * M` works just as well,
and it always satisfies `5 ≤ N`.

With this rank, the elementary leaf is only used for `N ≥ 5`.  This is
`CharZeroElementaryFPFiveStatement`.  It is implied by `CharZeroElementaryFPStatement`
(`charZeroElementaryFPFive_of_charZeroElementaryFP`), so it is logically weaker.  In particular,
the rank-four corner `E_4(ℤ[1/m])` is no longer needed by the chain.

Endpoints:
* `charZeroLinearHostStatement_of_chainFive`;
* `quasiLinearHostStatement_of_chainFive`;
* `finitelyPresentedMetabelianStatement_of_chainFive`: the root from the same eleven leaves, with
  `CharZeroElementaryFPFiveStatement` in place of `CharZeroElementaryFPStatement`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Chain

/-- **The elementary leaf at rank at least five.**  `E_N(ℤ[1/m][t_0, ..., t_{k-1}])` is finitely
presented for `N ≥ k + 4` and `N ≥ 5`.

*Truth.*  This is `CharZeroElementaryFPStatement` restricted to `N ≥ 5`.
*Strictly weaker.*  See `charZeroElementaryFPFive_of_charZeroElementaryFP`.  It omits the rank-four
case `E_4(ℤ[1/m])`. -/
def CharZeroElementaryFPFiveStatement : Prop :=
  ∀ (m k N : ℕ), k + 4 ≤ N → 5 ≤ N →
    Group.IsFinitelyPresented (elementaryGroup (Fin N) (SIntPoly m k))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.CharZeroElementaryFPFiveStatement

/-- The original elementary leaf implies the rank-at-least-five leaf. -/
theorem charZeroElementaryFPFive_of_charZeroElementaryFP (h : CharZeroElementaryFPStatement) :
    CharZeroElementaryFPFiveStatement :=
  fun m k N hN _ => h m k N hN

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Chain.charZeroElementaryFPFive_of_charZeroElementaryFP

/-- **Composition for the characteristic-zero node** at rank `k + 5 + 2 * M`. -/
theorem charZeroLinearHostStatement_of_chainFive
    (hcoord : CharZeroPolynomialCoordinatesStatement)
    (habs : CharZeroElementaryAbsorptionStatement) (hfp : CharZeroElementaryFPFiveStatement)
    (haff : AffineExtensionFPStatement) (hss : CharZeroAffineSelfSimilarStatement) :
    CharZeroLinearHostStatement := by
  intro K _ _ n H hH
  obtain ⟨m, k, M, ψ, hψ⟩ := hcoord K n H hH
  obtain ⟨f, hf⟩ := habs m k M (k + 5 + 2 * M) (by omega) (by omega)
  have hE : Group.IsFinitelyPresented
      (elementaryGroup (Fin (k + 5 + 2 * M)) (SIntPoly m k)) :=
    hfp m k (k + 5 + 2 * M) (by omega) (by omega)
  haveI : Group.IsFinitelyPresented (AffineElementaryGroup (k + 5 + 2 * M) (SIntPoly m k)) :=
    haff (SIntPoly m k) (finiteType_int_transfer _ (sIntPoly_finiteType m k) _)
      (k + 5 + 2 * M) (by omega) hE
  obtain ⟨X, _, _, ρ, hρ⟩ := hss m k (k + 5 + 2 * M) (by omega)
  exact embedsInFPSelfSimilarGroup_of_affineHost (X := X) ρ hρ (f := f.comp ψ) (hf.comp hψ)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Chain.charZeroLinearHostStatement_of_chainFive

/-- **Composition for the quasi-linear node**, with the rank-at-least-five elementary leaf. -/
theorem quasiLinearHostStatement_of_chainFive
    (hcoordP : CharPCoords.CharPPolynomialCoordinatesStatement)
    (habsP : CharPElementaryAbsorptionStatement) (hfpP : ElemFP.PolynomialFpElementaryFPStatement)
    (hssP : CharPAffineSelfSimilarStatement)
    (hcoord0 : CharZeroPolynomialCoordinatesStatement)
    (habs0 : CharZeroElementaryAbsorptionStatement) (hfp0 : CharZeroElementaryFPFiveStatement)
    (hss0 : CharZeroAffineSelfSimilarStatement) (haff : AffineExtensionFPStatement) :
    QuasiLinearHostStatement :=
  quasiLinearHostStatement_of_linearHost
    (linearHostStatement_of_charP_charZero
      (charPLinearHostStatement_of_chain hcoordP habsP hfpP haff hssP)
      (charZeroLinearHostStatement_of_chainFive hcoord0 habs0 hfp0 haff hss0))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.quasiLinearHostStatement_of_chainFive

/-- **The root from the leaves of the FRONTIER tree**, with the rank-at-least-five elementary
leaf. -/
theorem finitelyPresentedMetabelianStatement_of_chainFive
    (hcop : CoprimaryLinearQuotientsStatement)
    (hcoordP : CharPCoords.CharPPolynomialCoordinatesStatement)
    (habsP : CharPElementaryAbsorptionStatement) (hfpP : ElemFP.PolynomialFpElementaryFPStatement)
    (hssP : CharPAffineSelfSimilarStatement)
    (hcoord0 : CharZeroPolynomialCoordinatesStatement)
    (habs0 : CharZeroElementaryAbsorptionStatement) (hfp0 : CharZeroElementaryFPFiveStatement)
    (hss0 : CharZeroAffineSelfSimilarStatement) (haff : AffineExtensionFPStatement)
    (henv : Products.FPSelfSimilarEnvelopeStatement) :
    FinitelyPresentedMetabelianStatement :=
  Products.finitelyPresentedMetabelianStatement_of_pieces
    (metabelianPiecesStatement_of_quasiLinear hcop
      (quasiLinearHostStatement_of_chainFive hcoordP habsP hfpP hssP hcoord0 habs0 hfp0 hss0
        haff))
    henv

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Chain.finitelyPresentedMetabelianStatement_of_chainFive

end Chain
end Metabelian
end BooneHigman
end GroupApproximation
