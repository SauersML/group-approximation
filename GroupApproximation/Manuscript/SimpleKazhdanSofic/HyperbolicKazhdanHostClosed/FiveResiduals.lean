import GroupApproximation.Manuscript.SimpleKazhdanSofic.HyperbolicKazhdanHost.GeometryEndpoint
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.AsmWaist.Endpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# SK `cor:host`, tex l.477–481, over the five open residuals of the Greendlinger waist

`simple_kazhdan_sofic_group.tex`, section "LEF groups", tex l.477–481 (census row
`fc84c012b409`):

> Without LEF, every countable group embeds in a finitely generated simple group~\cite{Gorjuskin,Schupp},
> and even in a simple quotient of a torsion-free hyperbolic Kazhdan group~\cite[Theorem~1.5]{CoulonFournierFacio},
> so one simple Kazhdan group contains Higman's universal finitely presented group~\cite{Higman}.

Lane gl-assembly-11.  The lane endpoint is the closed application
`HyperbolicKazhdanHost.manuscriptSentence_withoutLEFSimpleHosts_of_greendlinger
  AsmClose.relativeGreendlingerQuasiGeodesicLeastAreaClosed.{0, 0, 0}`
(and likewise for clause (b)).  The producer `AsmClose.relativeGreendlingerQuasiGeodesicLeastAreaClosed`
(lane gl-assembly-04) is not on disk.  Its type is already on disk: it is
`GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}`, and the `_of_`
reduction over it is `HyperbolicKazhdanHost.manuscriptSentence_withoutLEFSimpleHosts_of_greendlinger`
(module `HyperbolicKazhdanHost/GeometryEndpoint`).  Restating that reduction here would add nothing.

## What this module proves

It discharges strictly more proof content than `_of_greendlinger`: the Below waist
`relativeGreendlingerQuasiGeodesicLeastArea_of_eightResidualsBelow` and the closed trio (residuals
05, 08, 09) are applied, via `AsmWaist.relativeGreendlingerQuasiGeodesicLeastArea_of_fiveResidualsBelow`.
What remains are the five open residuals (01 budget, 04 gap span, 06 Below cell step, 07 Below proper
arcs, 10 outer pinch step), each a true section form of Osin's Lemmas 9.4 / 9.7(b).  The hypotheses
are therefore strictly weaker-in-content inputs than the whole Greendlinger leaf, and all of them are
implied by region endpoints in flight.

* `manuscriptSentence_simpleQuotientOfHyperbolicKazhdan_of_fiveResidualsBelow`: clause (b);
* `manuscriptSentence_withoutLEFSimpleHosts_of_fiveResidualsBelow`: the whole sentence.

Clauses (a) and (c) are closed in `SimpleHosts.Endpoints`, and the residual geometry
`CoulonFournierFacioGeometryStatement` is closed in `GeometryEndpoint`.

## Closing once gl-assembly-04 lands

```
theorem manuscriptSentence_withoutLEFSimpleHosts : <conclusion below> :=
  HyperbolicKazhdanHost.manuscriptSentence_withoutLEFSimpleHosts_of_greendlinger
    GGT.VanKampen.GreendlingerLeaf.AsmClose.relativeGreendlingerQuasiGeodesicLeastAreaClosed.{0, 0, 0}
```
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace HyperbolicKazhdanHostClosed

open GroupApproximation.Manuscript.NonMF.TorsionFree

/-- **Clause (b) of tex l.477–481 over the five open residuals of the Below Greendlinger waist**:
one infinite, finitely presented, torsion-free hyperbolic Kazhdan group `H` has, for every countable
group `Γ`, a simple quotient into which `Γ` embeds. -/
theorem manuscriptSentence_simpleQuotientOfHyperbolicKazhdan_of_fiveResidualsBelow
    (hbudget : GGT.VanKampen.OsinLemma94ClassEndLoopsBudgetInput.{0, 0, 0})
    (hspan : GGT.VanKampen.OsinLemma94ClassCaseGapSpanStatement.{0, 0, 0})
    (hcellStep :
      GGT.VanKampen.CellPocketOuterPinchStepSectionDistinctBelowStatement.{0, 0, 0})
    (hproper : GGT.VanKampen.CellPocketWalkProperArcsBelowSectionStatement.{0, 0, 0})
    (hstep : GGT.VanKampen.PocketOuterPinchStepSectionStatement.{0, 0, 0}) :
    ∃ (H : Type) (_ : Group H), Infinite H ∧ Group.IsFinitelyPresented H ∧
      IsPowerTorsionFree H ∧ Hyperbolic.IsHyperbolicGroup H ∧ HasKazhdanPropertyT.{0, 0} H ∧
      ∀ (Γ : Type) [Group Γ] [Countable Γ], ∃ (S : Type) (_ : Group S), IsSimpleGroup S ∧
        (∃ π : H →* S, Function.Surjective π) ∧ ∃ f : Γ →* S, Function.Injective f :=
  HyperbolicKazhdanHost.simpleQuotientOfHyperbolicKazhdan_of_greendlinger
    (GGT.VanKampen.GreendlingerLeaf.AsmWaist.relativeGreendlingerQuasiGeodesicLeastArea_of_fiveResidualsBelow
      hbudget hspan hcellStep hproper hstep)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HyperbolicKazhdanHostClosed.manuscriptSentence_simpleQuotientOfHyperbolicKazhdan_of_fiveResidualsBelow

/-- **The whole sentence of tex l.477–481 over the five open residuals of the Below Greendlinger
waist**: (a) every countable group embeds in a finitely generated simple group; (b) one torsion-free
hyperbolic Kazhdan group has a simple quotient containing any given countable group; (c) one simple
Kazhdan group contains every finitely presented group. -/
theorem manuscriptSentence_withoutLEFSimpleHosts_of_fiveResidualsBelow
    (hbudget : GGT.VanKampen.OsinLemma94ClassEndLoopsBudgetInput.{0, 0, 0})
    (hspan : GGT.VanKampen.OsinLemma94ClassCaseGapSpanStatement.{0, 0, 0})
    (hcellStep :
      GGT.VanKampen.CellPocketOuterPinchStepSectionDistinctBelowStatement.{0, 0, 0})
    (hproper : GGT.VanKampen.CellPocketWalkProperArcsBelowSectionStatement.{0, 0, 0})
    (hstep : GGT.VanKampen.PocketOuterPinchStepSectionStatement.{0, 0, 0}) :
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
    (GGT.VanKampen.GreendlingerLeaf.AsmWaist.relativeGreendlingerQuasiGeodesicLeastArea_of_fiveResidualsBelow
      hbudget hspan hcellStep hproper hstep)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HyperbolicKazhdanHostClosed.manuscriptSentence_withoutLEFSimpleHosts_of_fiveResidualsBelow

end HyperbolicKazhdanHostClosed
end SimpleKazhdanSofic
end GroupApproximation
