import GroupApproximation.Manuscript.SimpleKazhdanSofic.ThompsonConstruction.Endpoints
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterWP.Host
import GroupApproximation.Meta.AxiomGuard

/-!
# The theorem of Boone and Higman in Thompson's form, closed (census key `9fe4e2896405`)

`simple_kazhdan_sofic_group.tex`, section "LEF groups" (census tex l.447–451, an attribution row):

> Its last statement is the analogue for LEF groups of the theorem of Boone and Higman that a
> finitely generated group has solvable word problem if and only if it embeds in a simple subgroup
> of a finitely presented group~\cite{BooneHigman}, in Thompson's form, where the simple group is
> finitely generated and has solvable word problem~\cite{Thompson80}.

The sentence credits Boone, Higman and Thompson, and it asserts their theorem. For a finitely
generated group `G`, the following are equivalent:
* (d) `G` has solvable word problem;
* (a) `G` embeds in a finitely generated simple group with solvable word problem;
* (b) Thompson's form: `G` embeds in a finitely generated simple subgroup, with solvable word problem,
  of a finitely presented group;
* (c) `G` embeds in a simple subgroup of a finitely presented group.

## Where the pieces are

* `BooneHigman.manuscriptSentence_booneHigman_chain`: (a) ⇒ (b) ⇒ (c) ⇒ (d). The step (a) ⇒ (b) is
  Higman's embedding theorem (`Higman.OmegaSharedProof.reBenign`). The step (c) ⇒ (d) is
  Kuznetsov's argument.
* `ThompsonConstruction.manuscriptSentence_booneHigman_thompson_iff_of_printedLamplighterHostSolvableWordProblem`:
  the equivalences, from one hypothesis `Lamplighter.PrintedLamplighterHostSolvableWordProblem`. This
  says that the lamplighter host `G_Δ` of an infinite finitely generated group `Δ` with solvable word
  problem has solvable word problem (`lem:halfline`(b)). With it, (d) ⇒ (a) is `G ↪ G_Δ`.
* `LamplighterWP.hostProof`: that hypothesis, proved.

The `ThompsonConstruction` module was written while the hypothesis was still open, so it stops at the
`_of_` form. This module applies the proof. The mathematics is the corpus's, and the host is the
manuscript's lamplighter host. Thompson's original simple group is not used.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.SkOpen

/-- **Boone–Higman in Thompson's form** (tex l.447–451), unconditional: a finitely generated group
has solvable word problem if and only if it embeds in a finitely generated simple group with solvable
word problem; if and only if it embeds in a finitely generated simple subgroup, with solvable word
problem, of a finitely presented group; and if and only if it embeds in a simple subgroup of a
finitely presented group. -/
theorem manuscriptSentence_booneHigmanThompson {G : Type} [Group G] (hG : Group.FG G) :
    (GroupApproximation.SimpleKazhdanSofic.HasSolvableWordProblem G ↔
        GroupApproximation.SimpleKazhdanSofic.BooneHigman.EmbedsInFGSimpleSolvable G) ∧
      (GroupApproximation.SimpleKazhdanSofic.HasSolvableWordProblem G ↔
        GroupApproximation.SimpleKazhdanSofic.BooneHigman.EmbedsInThompsonSimpleSubgroup G) ∧
        (GroupApproximation.SimpleKazhdanSofic.HasSolvableWordProblem G ↔
          GroupApproximation.SimpleKazhdanSofic.BooneHigman.EmbedsInSimpleSubgroupOfFinitelyPresented
            G) :=
  GroupApproximation.SimpleKazhdanSofic.ThompsonConstruction.manuscriptSentence_booneHigman_thompson_iff_of_printedLamplighterHostSolvableWordProblem
    GroupApproximation.SimpleKazhdanSofic.LamplighterWP.hostProof hG

/-- **Thompson's embedding** (tex l.450–451), unconditional: every group with solvable word problem
embeds in a finitely generated simple group with solvable word problem. -/
theorem embedsInFGSimpleSolvable_of_hasSolvableWordProblem {Γ : Type} [Group Γ]
    (h : GroupApproximation.SimpleKazhdanSofic.HasSolvableWordProblem Γ) :
    GroupApproximation.SimpleKazhdanSofic.BooneHigman.EmbedsInFGSimpleSolvable Γ :=
  GroupApproximation.SimpleKazhdanSofic.ThompsonConstruction.embedsInFGSimpleSolvable_of_hasSolvableWordProblem
    (GroupApproximation.SimpleKazhdanSofic.ThompsonConstruction.hostRecursivePresentationStatement_of_printedLamplighterHostSolvableWordProblem
      GroupApproximation.SimpleKazhdanSofic.LamplighterWP.hostProof) h

end GroupApproximation.Manuscript.SimpleKazhdanSofic.SkOpen

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.SkOpen.manuscriptSentence_booneHigmanThompson
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.SkOpen.embedsInFGSimpleSolvable_of_hasSolvableWordProblem
