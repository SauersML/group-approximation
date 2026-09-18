import GroupApproximation.Manuscript.SimpleKazhdanSofic.BooneHigman.HigmanStep
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FinitelyPresentedRecursivePresentation
import GroupApproximation.Meta.AxiomGuard

/-!
# The theorem of Boone and Higman, in Thompson's form: endpoints

`simple_kazhdan_sofic_group.tex`, section "LEF groups", tex l.447–451:

> Its last statement is the analogue for LEF groups of the
> theorem of Boone and Higman that a finitely generated group has solvable
> word problem if and only if it embeds in a simple subgroup of a finitely
> presented group~\cite{BooneHigman}, in Thompson's form, where the simple
> group is finitely generated and has solvable word problem~\cite{Thompson80}.

## What is proved

For a finitely generated group `G` consider

* (a) `EmbedsInFGSimpleSolvable G`: `G` embeds in a finitely generated simple group with solvable
  word problem;
* (b) `EmbedsInThompsonSimpleSubgroup G`: Thompson's form;
* (c) `EmbedsInSimpleSubgroupOfFinitelyPresented G`: the embedding of Boone and Higman;
* (d) `HasSolvableWordProblem G`.

The endpoints prove (a) ⇒ (b) ⇒ (c) ⇒ (d) unconditionally, and (d) ⇒ (b) ⇒ (c) for finitely
generated simple groups, where (d) ⇒ (a) is the identity. The step (d) ⇒ (a) for an arbitrary
finitely generated group (Thompson's embedding in a finitely generated simple group with solvable
word problem) is not proved here.

## Proof route

* (c) ⇒ (d): `finitelyPresentedRecursivePresentationStatement` and Kuznetsov's argument
  `hasSolvableWordProblem_of_simpleSubgroup`.
* (a) ⇒ (b): Higman's embedding theorem,
  `embedsInThompsonSimpleSubgroup_of_embedsInFGSimpleSolvable`.
* (b) ⇒ (c): forget, `embedsInSimpleSubgroupOfFinitelyPresented_of_thompson`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace BooneHigman

/-- **Boone–Higman, (c) ⇒ (d)** (tex l.447–450): a finitely generated group that embeds in a
simple subgroup of a finitely presented group has solvable word problem. -/
theorem manuscriptSentence_booneHigman_solvable_of_embeds {G : Type} [Group G]
    (hG : Group.FG G) (h : EmbedsInSimpleSubgroupOfFinitelyPresented G) :
    HasSolvableWordProblem G := by
  obtain ⟨H, _, hfp, S, hS, f, hf⟩ := h
  obtain ⟨rp⟩ := finitelyPresentedRecursivePresentationStatement H hfp
  exact hasSolvableWordProblem_of_simpleSubgroup hG rp S f hf

#audit_axioms GroupApproximation.SimpleKazhdanSofic.BooneHigman.manuscriptSentence_booneHigman_solvable_of_embeds

/-- **Thompson's form, (a) ⇒ (b) ⇒ (c)** (tex l.450–451): a group embedding in a finitely
generated simple group with solvable word problem embeds in a finitely generated simple subgroup
with solvable word problem of a finitely presented group. -/
theorem manuscriptSentence_thompsonForm {G : Type} [Group G] (h : EmbedsInFGSimpleSolvable G) :
    EmbedsInThompsonSimpleSubgroup G ∧ EmbedsInSimpleSubgroupOfFinitelyPresented G :=
  ⟨embedsInThompsonSimpleSubgroup_of_embedsInFGSimpleSolvable h,
    embedsInSimpleSubgroupOfFinitelyPresented_of_thompson
      (embedsInThompsonSimpleSubgroup_of_embedsInFGSimpleSolvable h)⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.BooneHigman.manuscriptSentence_thompsonForm

/-- **Thompson's form, (b) ⇒ (d)**: a finitely generated group embedding in a simple subgroup as
in Thompson's form has solvable word problem. -/
theorem manuscriptSentence_thompson_solvable {G : Type} [Group G] (hG : Group.FG G)
    (h : EmbedsInThompsonSimpleSubgroup G) : HasSolvableWordProblem G :=
  manuscriptSentence_booneHigman_solvable_of_embeds hG
    (embedsInSimpleSubgroupOfFinitelyPresented_of_thompson h)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.BooneHigman.manuscriptSentence_thompson_solvable

/-- Property (a) passes to subgroups. -/
theorem embedsInFGSimpleSolvable_of_injective {G G' : Type} [Group G] [Group G'] (g : G →* G')
    (hg : Function.Injective g) (h : EmbedsInFGSimpleSolvable G') : EmbedsInFGSimpleSolvable G := by
  obtain ⟨E, _, hsimple, hfg, hwp, f, hf⟩ := h
  exact ⟨E, inferInstance, hsimple, hfg, hwp, f.comp g, hf.comp hg⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.BooneHigman.embedsInFGSimpleSolvable_of_injective

/-- **Boone–Higman and Thompson for finitely generated simple groups** (tex l.447–451): a finitely
generated simple group has solvable word problem if and only if it embeds in a simple subgroup of
a finitely presented group, if and only if it embeds as in Thompson's form. -/
theorem manuscriptSentence_booneHigman_thompson_simple {E : Type} [Group E] [IsSimpleGroup E]
    [Group.FG E] :
    (HasSolvableWordProblem E ↔ EmbedsInSimpleSubgroupOfFinitelyPresented E) ∧
      (HasSolvableWordProblem E ↔ EmbedsInThompsonSimpleSubgroup E) := by
  have hfwd : HasSolvableWordProblem E → EmbedsInFGSimpleSolvable E := fun h =>
    ⟨E, inferInstance, inferInstance, inferInstance, h, MonoidHom.id E, Function.injective_id⟩
  exact ⟨⟨fun h => (manuscriptSentence_thompsonForm (hfwd h)).2,
      manuscriptSentence_booneHigman_solvable_of_embeds inferInstance⟩,
    ⟨fun h => (manuscriptSentence_thompsonForm (hfwd h)).1,
      manuscriptSentence_thompson_solvable inferInstance⟩⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.BooneHigman.manuscriptSentence_booneHigman_thompson_simple

/-- **The chain (a) ⇒ (b) ⇒ (c) ⇒ (d)** for a finitely generated group. -/
theorem manuscriptSentence_booneHigman_chain {G : Type} [Group G] (hG : Group.FG G) :
    (EmbedsInFGSimpleSolvable G → EmbedsInThompsonSimpleSubgroup G) ∧
      (EmbedsInThompsonSimpleSubgroup G → EmbedsInSimpleSubgroupOfFinitelyPresented G) ∧
        (EmbedsInSimpleSubgroupOfFinitelyPresented G → HasSolvableWordProblem G) :=
  ⟨embedsInThompsonSimpleSubgroup_of_embedsInFGSimpleSolvable,
    embedsInSimpleSubgroupOfFinitelyPresented_of_thompson,
    manuscriptSentence_booneHigman_solvable_of_embeds hG⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.BooneHigman.manuscriptSentence_booneHigman_chain

end BooneHigman
end SimpleKazhdanSofic
end GroupApproximation
