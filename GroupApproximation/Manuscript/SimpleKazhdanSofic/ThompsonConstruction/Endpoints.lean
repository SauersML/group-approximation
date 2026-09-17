import GroupApproximation.Manuscript.SimpleKazhdanSofic.ThompsonConstruction.Host
import GroupApproximation.Manuscript.SimpleKazhdanSofic.BooneHigman.Endpoints
import GroupApproximation.Meta.AxiomGuard

/-!
# Thompson's form of Boone–Higman: the converse and the equivalence

`simple_kazhdan_sofic_group.tex`, section "LEF groups", tex l.447–451:

> Its last statement is the analogue for LEF groups of the
> theorem of Boone and Higman that a finitely generated group has solvable
> word problem if and only if it embeds in a simple subgroup of a finitely
> presented group~\cite{BooneHigman}, in Thompson's form, where the simple
> group is finitely generated and has solvable word problem~\cite{Thompson80}.

For a finitely generated group `G`, consider:

* (d) `HasSolvableWordProblem G`;
* (a) `BooneHigman.EmbedsInFGSimpleSolvable G`;
* (b) `BooneHigman.EmbedsInThompsonSimpleSubgroup G`;
* (c) `BooneHigman.EmbedsInSimpleSubgroupOfFinitelyPresented G`.

`BooneHigman/Endpoints.lean` proves (a) ⇒ (b) ⇒ (c) ⇒ (d). This file proves (d) ⇒ (a).

## Proof route for (d) ⇒ (a)

`exists_simpleHost_embedding_of_hasSolvableWordProblem` (unconditional) gives `G ↪ G_Δ`. Here
`G_Δ` is the finitely generated simple lamplighter host of an infinite group `Δ` with solvable word
problem. The word problem of `G_Δ` is solved by
`hasSolvableWordProblem_host_of_hostRecursivePresentationStatement`. That step uses the single
isolated gap `HostRecursivePresentationStatement`: `G_Δ` is recursively presented. This is the
recursively enumerable half of `lem:host`; Kuznetsov's argument gives the other half.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace ThompsonConstruction

open Lamplighter BooneHigman

/-- **Thompson's form, (d) ⇒ (a)** (tex l.450–451): a group with solvable word problem embeds in
a finitely generated simple group with solvable word problem. The only input is the isolated gap
`HostRecursivePresentationStatement`. -/
theorem embedsInFGSimpleSolvable_of_hasSolvableWordProblem
    (hS : HostRecursivePresentationStatement) {Γ : Type} [Group Γ]
    (h : HasSolvableWordProblem Γ) : EmbedsInFGSimpleSolvable Γ := by
  obtain ⟨Δ, _, hinf, hwp, hGs, hGfg, f, hf⟩ :=
    exists_simpleHost_embedding_of_hasSolvableWordProblem h
  haveI : Infinite Δ := hinf
  exact ⟨↥(elementaryGroup (Fin 3) (LampRing Δ)), inferInstance, hGs, hGfg,
    hasSolvableWordProblem_host_of_hostRecursivePresentationStatement hS Δ hwp, f, hf⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThompsonConstruction.embedsInFGSimpleSolvable_of_hasSolvableWordProblem

/-- **Boone–Higman in Thompson's form** (tex l.447–451): a finitely generated group has solvable
word problem if and only if it embeds in a finitely generated simple group with solvable word
problem (a). It is also equivalent to Thompson's form (b), and to embedding in a simple subgroup
of a finitely presented group (c). The only input is the isolated gap
`HostRecursivePresentationStatement`. -/
theorem manuscriptSentence_booneHigman_thompson_iff (hS : HostRecursivePresentationStatement)
    {G : Type} [Group G] (hG : Group.FG G) :
    (HasSolvableWordProblem G ↔ EmbedsInFGSimpleSolvable G) ∧
      (HasSolvableWordProblem G ↔ EmbedsInThompsonSimpleSubgroup G) ∧
        (HasSolvableWordProblem G ↔ EmbedsInSimpleSubgroupOfFinitelyPresented G) := by
  obtain ⟨hab, hbc, hcd⟩ := manuscriptSentence_booneHigman_chain hG
  have hda : HasSolvableWordProblem G → EmbedsInFGSimpleSolvable G :=
    embedsInFGSimpleSolvable_of_hasSolvableWordProblem hS
  exact ⟨⟨hda, fun h => hcd (hbc (hab h))⟩, ⟨fun h => hab (hda h), fun h => hcd (hbc h)⟩,
    ⟨fun h => hbc (hab (hda h)), hcd⟩⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThompsonConstruction.manuscriptSentence_booneHigman_thompson_iff

/-- The equivalence (d) ⇔ (a) ⇔ (b) ⇔ (c), with the gap discharged by the corpus target
`Lamplighter.PrintedLamplighterHostSolvableWordProblem`. -/
theorem manuscriptSentence_booneHigman_thompson_iff_of_printedLamplighterHostSolvableWordProblem
    (hP : PrintedLamplighterHostSolvableWordProblem) {G : Type} [Group G] (hG : Group.FG G) :
    (HasSolvableWordProblem G ↔ EmbedsInFGSimpleSolvable G) ∧
      (HasSolvableWordProblem G ↔ EmbedsInThompsonSimpleSubgroup G) ∧
        (HasSolvableWordProblem G ↔ EmbedsInSimpleSubgroupOfFinitelyPresented G) :=
  manuscriptSentence_booneHigman_thompson_iff
    (hostRecursivePresentationStatement_of_printedLamplighterHostSolvableWordProblem hP) hG

#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThompsonConstruction.manuscriptSentence_booneHigman_thompson_iff_of_printedLamplighterHostSolvableWordProblem

end ThompsonConstruction
end SimpleKazhdanSofic
end GroupApproximation
