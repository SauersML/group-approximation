import GroupApproximation.Manuscript.SimpleKazhdanSofic.HyperbolicKazhdanHost.GeometryEndpoint
import GroupApproximation.Manuscript.NonMF.Full.GL06.Assembly
import GroupApproximation.Meta.AxiomGuard

/-!
# Simple quotients of a torsion-free hyperbolic Kazhdan group (census key `fc84c012b409`, clause (b))

`simple_kazhdan_sofic_group.tex`, section "LEF groups" (census tex l.477–481):

> Without LEF, every countable group embeds in a finitely generated simple group~\cite{Gorjuskin,Schupp},
> and even in a simple quotient of a torsion-free hyperbolic Kazhdan group~\cite[Theorem~1.5]{CoulonFournierFacio},
> so one simple Kazhdan group contains Higman's universal finitely presented group~\cite{Higman}.

Clauses (a) and (c) are closed in `SimpleHosts.Endpoints`. Clause (b) is
`HyperbolicKazhdanHost.simpleQuotientOfHyperbolicKazhdan_of_greendlinger`, whose only hypothesis is
Osin's Lemma 4.4 at least-area diagrams, the Greendlinger waist
`GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}`. The non-MF
torsion-free section needs the same waist.

**CONDITIONAL.** `Full.GL06.relativeGreendlinger_zero_of_allCells_of_core` proves the waist from two
residuals, and neither is proved in the repository:
* `hall : Full.GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{0, 0, 0}` (lane nm-gl06e);
* `hcore : Full.GL03DKept.gl03dKept_KeptSubwalkCoreStatement.{0, 0, 0}` (lane nm-gl03d).

This module routes clause (b) and the whole sentence through those two residuals. That is strictly
more proof content than `_of_greendlinger`, and it fixes the interface on the SK side. When both
producers land, the unconditional clause is one application of `simpleQuotientOfHyperbolicKazhdan_of_allCells_of_core`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.SkOpen

/-- **tex l.478–480, clause (b), CONDITIONAL on the two Greendlinger residuals**: there is an
infinite, finitely presented, torsion-free hyperbolic group `H` with property (T) such that every
countable group embeds in a simple quotient of `H`. -/
theorem simpleQuotientOfHyperbolicKazhdan_of_allCells_of_core
    (hall : GroupApproximation.Full.GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{0, 0, 0})
    (hcore : GroupApproximation.Full.GL03DKept.gl03dKept_KeptSubwalkCoreStatement.{0, 0, 0}) :
    ∃ (H : Type) (_ : Group H), Infinite H ∧ Group.IsFinitelyPresented H ∧
      IsPowerTorsionFree H ∧ Hyperbolic.IsHyperbolicGroup H ∧ HasKazhdanPropertyT.{0, 0} H ∧
      ∀ (Γ : Type) [Group Γ] [Countable Γ], ∃ (S : Type) (_ : Group S), IsSimpleGroup S ∧
        (∃ π : H →* S, Function.Surjective π) ∧ ∃ f : Γ →* S, Function.Injective f :=
  GroupApproximation.SimpleKazhdanSofic.HyperbolicKazhdanHost.simpleQuotientOfHyperbolicKazhdan_of_greendlinger
    (GroupApproximation.Full.GL06.relativeGreendlinger_zero_of_allCells_of_core hall hcore)

/-- **tex l.477–481, the whole sentence, CONDITIONAL on the two Greendlinger residuals.** Clauses
(a) and (c) do not use the hypotheses. -/
theorem manuscriptSentence_withoutLEFSimpleHosts_of_allCells_of_core
    (hall : GroupApproximation.Full.GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{0, 0, 0})
    (hcore : GroupApproximation.Full.GL03DKept.gl03dKept_KeptSubwalkCoreStatement.{0, 0, 0}) :
    (∀ (Γ : Type) [Group Γ] [Countable Γ], ∃ (G : Type) (_ : Group G), Group.FG G ∧
        IsSimpleGroup G ∧ ∃ f : Γ →* G, Function.Injective f) ∧
      (∃ (H : Type) (_ : Group H), Infinite H ∧ Group.IsFinitelyPresented H ∧
        IsPowerTorsionFree H ∧ Hyperbolic.IsHyperbolicGroup H ∧ HasKazhdanPropertyT.{0, 0} H ∧
        ∀ (Γ : Type) [Group Γ] [Countable Γ], ∃ (S : Type) (_ : Group S), IsSimpleGroup S ∧
          (∃ π : H →* S, Function.Surjective π) ∧ ∃ f : Γ →* S, Function.Injective f) ∧
      ∃ (G : Type) (_ : Group G), IsSimpleGroup G ∧ HasKazhdanPropertyT.{0, 0} G ∧
        ∀ (H : Type) [Group H] [Group.IsFinitelyPresented H],
          ∃ f : H →* G, Function.Injective f :=
  GroupApproximation.SimpleKazhdanSofic.HyperbolicKazhdanHost.manuscriptSentence_withoutLEFSimpleHosts_of_greendlinger
    (GroupApproximation.Full.GL06.relativeGreendlinger_zero_of_allCells_of_core hall hcore)

end GroupApproximation.Manuscript.SimpleKazhdanSofic.SkOpen

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.SkOpen.simpleQuotientOfHyperbolicKazhdan_of_allCells_of_core
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.SkOpen.manuscriptSentence_withoutLEFSimpleHosts_of_allCells_of_core
