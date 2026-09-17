import GroupApproximation.Manuscript.SimpleKazhdanSofic.HyperbolicKazhdanHost.GeometryEndpoint
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmFrontier.Tight
import GroupApproximation.Meta.AxiomGuard

/-!
# SK `cor:host`, tex l.477–481, over the four open frontier Statements of the Greendlinger leaf

`simple_kazhdan_sofic_group.tex`, section "LEF groups", tex l.477–481 (census row
`fc84c012b409`):

> Without LEF, every countable group embeds in a finitely generated simple group~\cite{Gorjuskin,Schupp},
> and even in a simple quotient of a torsion-free hyperbolic Kazhdan group~\cite[Theorem~1.5]{CoulonFournierFacio},
> so one simple Kazhdan group contains Higman's universal finitely presented group~\cite{Higman}.

Lane gl-assembly-11, tight variant.  `AsmFrontier.relativeGreendlingerQuasiGeodesicLeastArea_of_tightFrontier`
(lane gl-assembly-03) discharges, besides the waist and the closed trio, the three region endpoints
`Piece01.proof` (residual 01), `Piece06.MonogonCorner.monogonCorner` and `P10ChordLift.proof`, and
the reductions of residuals 04, 06, 07 and 10 to their frontier gaps.  What remains are four true
region-level Statements:

* `Piece04.ClassPocketRotationTurnStatement` (rotation turns of a class pocket);
* `Piece06.CellRoseUncutLakesBelowStatement` (uncut lakes of the cell rose, below the bound);
* `P07LakeExclusion.CellPocketInnerTwoArcLongStatement` (the long inner two-arc);
* `P10Rose.RoseRegionMoveSubArcStatement` (the sub-arc region move of the rose case; the corrected
  form of the false filter route).

Each is strictly smaller in proof content than the residual it feeds (the reduction to it is
proved on disk), so these endpoints carry strictly more proof content than the five-residual forms
of `HyperbolicKazhdanHostClosed/FiveResiduals`, which in turn carry more than
`HyperbolicKazhdanHost.manuscriptSentence_withoutLEFSimpleHosts_of_greendlinger`.

This module is kept apart from `FiveResiduals` so that a defect in the import trees of the three
region endpoints (`Piece01/Proof`, `Piece06/MonogonCorner`, `P10ChordLift/Proof`) does not affect
the five-residual endpoints.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace HyperbolicKazhdanHostClosed

open GroupApproximation.Manuscript.NonMF.TorsionFree

/-- **Clause (b) of tex l.477–481 over the four open frontier Statements of the Greendlinger
leaf.** -/
theorem manuscriptSentence_simpleQuotientOfHyperbolicKazhdan_of_tightFrontier
    (hrot : GGT.VanKampen.GreendlingerLeaf.Piece04.ClassPocketRotationTurnStatement.{0, 0, 0})
    (hlakes : GGT.VanKampen.GreendlingerLeaf.Piece06.CellRoseUncutLakesBelowStatement.{0, 0, 0})
    (hinner :
      GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.CellPocketInnerTwoArcLongStatement.{0, 0, 0})
    (hsub : GGT.VanKampen.GreendlingerLeaf.P10Rose.RoseRegionMoveSubArcStatement.{0, 0, 0}) :
    ∃ (H : Type) (_ : Group H), Infinite H ∧ Group.IsFinitelyPresented H ∧
      IsPowerTorsionFree H ∧ Hyperbolic.IsHyperbolicGroup H ∧ HasKazhdanPropertyT.{0, 0} H ∧
      ∀ (Γ : Type) [Group Γ] [Countable Γ], ∃ (S : Type) (_ : Group S), IsSimpleGroup S ∧
        (∃ π : H →* S, Function.Surjective π) ∧ ∃ f : Γ →* S, Function.Injective f :=
  HyperbolicKazhdanHost.simpleQuotientOfHyperbolicKazhdan_of_greendlinger
    (GGT.VanKampen.GreendlingerLeaf.AsmFrontier.relativeGreendlingerQuasiGeodesicLeastArea_of_tightFrontier
      hrot hlakes hinner hsub)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HyperbolicKazhdanHostClosed.manuscriptSentence_simpleQuotientOfHyperbolicKazhdan_of_tightFrontier

/-- **The whole sentence of tex l.477–481 over the four open frontier Statements of the
Greendlinger leaf**: clauses (a) and (c) closed, clause (b) over the four frontier gaps. -/
theorem manuscriptSentence_withoutLEFSimpleHosts_of_tightFrontier
    (hrot : GGT.VanKampen.GreendlingerLeaf.Piece04.ClassPocketRotationTurnStatement.{0, 0, 0})
    (hlakes : GGT.VanKampen.GreendlingerLeaf.Piece06.CellRoseUncutLakesBelowStatement.{0, 0, 0})
    (hinner :
      GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.CellPocketInnerTwoArcLongStatement.{0, 0, 0})
    (hsub : GGT.VanKampen.GreendlingerLeaf.P10Rose.RoseRegionMoveSubArcStatement.{0, 0, 0}) :
    (∀ (Γ : Type) [Group Γ] [Countable Γ], ∃ (G : Type) (_ : Group G), Group.FG G ∧
        IsSimpleGroup G ∧ ∃ f : Γ →* G, Function.Injective f) ∧
      (∃ (H : Type) (_ : Group H), Infinite H ∧ Group.IsFinitelyPresented H ∧
        IsPowerTorsionFree H ∧ Hyperbolic.IsHyperbolicGroup H ∧ HasKazhdanPropertyT.{0, 0} H ∧
        ∀ (Γ : Type) [Group Γ] [Countable Γ], ∃ (S : Type) (_ : Group S), IsSimpleGroup S ∧
          (∃ π : H →* S, Function.Surjective π) ∧ ∃ f : Γ →* S, Function.Injective f) ∧
      ∃ (G : Type) (_ : Group G), IsSimpleGroup G ∧ HasKazhdanPropertyT.{0, 0} G ∧
        ∀ (H : Type) [Group H] [Group.IsFinitelyPresented H],
          ∃ f : H →* G, Function.Injective f :=
  HyperbolicKazhdanHost.manuscriptSentence_withoutLEFSimpleHosts_of_greendlinger
    (GGT.VanKampen.GreendlingerLeaf.AsmFrontier.relativeGreendlingerQuasiGeodesicLeastArea_of_tightFrontier
      hrot hlakes hinner hsub)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HyperbolicKazhdanHostClosed.manuscriptSentence_withoutLEFSimpleHosts_of_tightFrontier

end HyperbolicKazhdanHostClosed
end SimpleKazhdanSofic
end GroupApproximation
