import GroupApproximation.Manuscript.SimpleKazhdanSofic.HyperbolicKazhdanHost.GeometryEndpoint
import GroupApproximation.Manuscript.NonMF.Full.GL03DQuadrant.Waist
import GroupApproximation.Manuscript.NonMF.Full.GL06p.Windows
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.ArcWitness
import GroupApproximation.Meta.AxiomGuard

/-!
# Simple quotients of a torsion-free hyperbolic Kazhdan group (census key `fc84c012b409`, clause (b))

`simple_kazhdan_sofic_group.tex`, section "LEF groups" (census tex l.477–481):

> Without LEF, every countable group embeds in a finitely generated simple group~\cite{Gorjuskin,Schupp},
> and even in a simple quotient of a torsion-free hyperbolic Kazhdan group~\cite[Theorem~1.5]{CoulonFournierFacio},
> so one simple Kazhdan group contains Higman's universal finitely presented group~\cite{Higman}.

Clauses (a) and (c) are closed in `SimpleHosts.Endpoints`. Clause (b) is
`HyperbolicKazhdanHost.simpleQuotientOfHyperbolicKazhdan_of_greendlinger`, whose only hypothesis is
the Greendlinger waist `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}`
(Osin's Lemma 4.4 at least-area diagrams). The non-MF torsion-free section needs the same waist.

## CONDITIONAL: the open statements of the non-MF lanes

The waist is proved from these statements, and none of them is proved in the repository:
* `GL06p.slitPocketCoreStatement.{0, 0, 0}`: steps 2 and 3 of the slit pocket (ms-nm-uncond-a);
* `GL06p.GluedSlitWalkInStatement.{0, 0, 0}` and `GL06p.GluedSlitWalkOutStatement.{0, 0, 0}`: the
  glued walks of step 4 (nm-gl06e);
* `P10LocalSelect.p10LS_SelectionArcStatement.{0}`: the local selection with arc-meeting lobes
  (nm-gl03d).

The route:
* `GL06p.allCellsShort_of_core_of_gluedWalk` turns the first three into
  `hall : GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{0, 0, 0}`;
* `P10LocalSelect.p10LS_quadrantMove_of_selectionArc` turns the fourth into the quadrant move;
* `GL03DQuadrant.relativeGreendlinger_zero_of_allCells_of_quadrantMove` gives the waist from `hall`
  and the quadrant move.

Both forms are stated below: over `hall` and the selection (stable if the GL06p step design changes),
and over the four open statements. When the producers land, clause (b) closes by substitution.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.SkOpen

/-- The Greendlinger waist from binder 5 (`hall`) and nm-gl03d's local selection. -/
theorem relativeGreendlinger_of_allCells_of_selectionArc
    (hall : GroupApproximation.Full.GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{0, 0, 0})
    (harc : GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.p10LS_SelectionArcStatement.{0}) :
    GroupApproximation.GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0} :=
  GroupApproximation.Full.GL03DQuadrant.relativeGreendlinger_zero_of_allCells_of_quadrantMove hall
    (GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.p10LS_quadrantMove_of_selectionArc
      harc)

/-- The Greendlinger waist from the four open statements of the non-MF lanes. -/
theorem relativeGreendlinger_of_slitPocket_of_selectionArc
    (hcore : GroupApproximation.Full.GL06p.slitPocketCoreStatement.{0, 0, 0})
    (hin : GroupApproximation.Full.GL06p.GluedSlitWalkInStatement.{0, 0, 0})
    (hout : GroupApproximation.Full.GL06p.GluedSlitWalkOutStatement.{0, 0, 0})
    (harc : GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.p10LS_SelectionArcStatement.{0}) :
    GroupApproximation.GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0} :=
  relativeGreendlinger_of_allCells_of_selectionArc
    (GroupApproximation.Full.GL06p.allCellsShort_of_core_of_gluedWalk hcore hin hout) harc

/-- **tex l.478–480, clause (b), CONDITIONAL on `hall` and the local selection**: there is an
infinite, finitely presented, torsion-free hyperbolic group `H` with property (T) such that every
countable group embeds in a simple quotient of `H`. -/
theorem simpleQuotientOfHyperbolicKazhdan_of_allCells_of_selectionArc
    (hall : GroupApproximation.Full.GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{0, 0, 0})
    (harc : GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.p10LS_SelectionArcStatement.{0}) :
    ∃ (H : Type) (_ : Group H), Infinite H ∧ Group.IsFinitelyPresented H ∧
      IsPowerTorsionFree H ∧ Hyperbolic.IsHyperbolicGroup H ∧ HasKazhdanPropertyT.{0, 0} H ∧
      ∀ (Γ : Type) [Group Γ] [Countable Γ], ∃ (S : Type) (_ : Group S), IsSimpleGroup S ∧
        (∃ π : H →* S, Function.Surjective π) ∧ ∃ f : Γ →* S, Function.Injective f :=
  GroupApproximation.SimpleKazhdanSofic.HyperbolicKazhdanHost.simpleQuotientOfHyperbolicKazhdan_of_greendlinger
    (relativeGreendlinger_of_allCells_of_selectionArc hall harc)

/-- **tex l.478–480, clause (b), CONDITIONAL on the four open statements of the non-MF lanes.** -/
theorem simpleQuotientOfHyperbolicKazhdan_of_slitPocket_of_selectionArc
    (hcore : GroupApproximation.Full.GL06p.slitPocketCoreStatement.{0, 0, 0})
    (hin : GroupApproximation.Full.GL06p.GluedSlitWalkInStatement.{0, 0, 0})
    (hout : GroupApproximation.Full.GL06p.GluedSlitWalkOutStatement.{0, 0, 0})
    (harc : GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.p10LS_SelectionArcStatement.{0}) :
    ∃ (H : Type) (_ : Group H), Infinite H ∧ Group.IsFinitelyPresented H ∧
      IsPowerTorsionFree H ∧ Hyperbolic.IsHyperbolicGroup H ∧ HasKazhdanPropertyT.{0, 0} H ∧
      ∀ (Γ : Type) [Group Γ] [Countable Γ], ∃ (S : Type) (_ : Group S), IsSimpleGroup S ∧
        (∃ π : H →* S, Function.Surjective π) ∧ ∃ f : Γ →* S, Function.Injective f :=
  GroupApproximation.SimpleKazhdanSofic.HyperbolicKazhdanHost.simpleQuotientOfHyperbolicKazhdan_of_greendlinger
    (relativeGreendlinger_of_slitPocket_of_selectionArc hcore hin hout harc)

/-- **tex l.477–481, the whole sentence, CONDITIONAL on the four open statements of the non-MF
lanes.** Clauses (a) and (c) do not use the hypotheses. -/
theorem manuscriptSentence_withoutLEFSimpleHosts_of_slitPocket_of_selectionArc
    (hcore : GroupApproximation.Full.GL06p.slitPocketCoreStatement.{0, 0, 0})
    (hin : GroupApproximation.Full.GL06p.GluedSlitWalkInStatement.{0, 0, 0})
    (hout : GroupApproximation.Full.GL06p.GluedSlitWalkOutStatement.{0, 0, 0})
    (harc : GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.p10LS_SelectionArcStatement.{0}) :
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
    (relativeGreendlinger_of_slitPocket_of_selectionArc hcore hin hout harc)

end GroupApproximation.Manuscript.SimpleKazhdanSofic.SkOpen

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.SkOpen.relativeGreendlinger_of_allCells_of_selectionArc
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.SkOpen.relativeGreendlinger_of_slitPocket_of_selectionArc
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.SkOpen.simpleQuotientOfHyperbolicKazhdan_of_allCells_of_selectionArc
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.SkOpen.simpleQuotientOfHyperbolicKazhdan_of_slitPocket_of_selectionArc
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.SkOpen.manuscriptSentence_withoutLEFSimpleHosts_of_slitPocket_of_selectionArc
