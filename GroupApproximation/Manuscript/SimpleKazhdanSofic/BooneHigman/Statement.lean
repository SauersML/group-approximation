import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFSolvableWordProblem
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.Subgroup.Simple
import GroupApproximation.Meta.AxiomGuard

/-!
# The theorem of Boone and Higman, in Thompson's form: statements

`simple_kazhdan_sofic_group.tex`, section "LEF groups", tex l.447–451:

> Its last statement is the analogue for LEF groups of the
> theorem of Boone and Higman that a finitely generated group has solvable
> word problem if and only if it embeds in a simple subgroup of a finitely
> presented group~\cite{BooneHigman}, in Thompson's form, where the simple
> group is finitely generated and has solvable word problem~\cite{Thompson80}.

The sentence is an attribution. The mathematics it cites is:

* (BH) a finitely generated group `G` has solvable word problem if and only if `G` embeds in a
  simple subgroup of a finitely presented group;
* (Thompson) the simple subgroup can be taken finitely generated with solvable word problem.

## Proof route

1. **Kuznetsov's argument** (`BooneHigman/Kuznetsov.lean`). Let `H` be recursively presented,
   `S ≤ H` simple, `φ : G ↪ S`, and fix `x ∈ S` with `x ≠ 1`. For `h ∈ S`,
   `h ≠ 1 ↔ x ∈ ⟪h⟫^H`: the trace of `⟪h⟫^H` on `S` is normal in `S`, so it is `⊤` when it contains
   `h ≠ 1`. Both `h = 1` (the presentation) and `x ∈ ⟪h⟫^H` (a search over products of conjugates)
   are recursively enumerable, so the word problem of `G` is decidable (Post). A finitely
   presented group is recursively presented (`finitelyPresentedRecursivePresentationStatement`).
   This proves the direction "embeds in a simple subgroup of a finitely presented group ⇒
   solvable word problem".
2. **Higman's embedding step** (`BooneHigman/HigmanStep.lean`). A finitely generated group with
   solvable word problem has a finite-rank recursive presentation, so it embeds in a finitely
   presented group (`Higman.fpOvergroup_of_fgRecursive` with `Higman.OmegaSharedProof.reBenign`).
   Hence a finitely generated simple group `S` with solvable word problem is itself a finitely
   generated simple subgroup with solvable word problem of a finitely presented group, and so is
   every group that embeds in such an `S`.
3. **Thompson's reduction** (`BooneHigman/Endpoints.lean`). Both (BH) and Thompson's form for `G`
   follow once `G` embeds in a finitely generated simple group with solvable word problem, and
   Thompson's form implies the embedding in (BH). The endpoints record exactly what is proved.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace BooneHigman

/-- `G` embeds in a simple subgroup of a finitely presented group (tex l.449–450). -/
def EmbedsInSimpleSubgroupOfFinitelyPresented (G : Type) [Group G] : Prop :=
  ∃ (H : Type) (_ : Group H), Group.IsFinitelyPresented H ∧
    ∃ S : Subgroup H, IsSimpleGroup S ∧ ∃ f : G →* S, Function.Injective f

/-- Thompson's form (tex l.450–451): `G` embeds in a simple subgroup of a finitely presented group
that is finitely generated and has solvable word problem. -/
def EmbedsInThompsonSimpleSubgroup (G : Type) [Group G] : Prop :=
  ∃ (H : Type) (_ : Group H), Group.IsFinitelyPresented H ∧
    ∃ S : Subgroup H, IsSimpleGroup S ∧ Group.FG S ∧ HasSolvableWordProblem S ∧
      ∃ f : G →* S, Function.Injective f

/-- `G` embeds in a finitely generated simple group with solvable word problem. -/
def EmbedsInFGSimpleSolvable (G : Type) [Group G] : Prop :=
  ∃ (E : Type) (_ : Group E), IsSimpleGroup E ∧ Group.FG E ∧ HasSolvableWordProblem E ∧
    ∃ f : G →* E, Function.Injective f

/-- Thompson's form gives the embedding of Boone and Higman. -/
theorem embedsInSimpleSubgroupOfFinitelyPresented_of_thompson {G : Type} [Group G]
    (h : EmbedsInThompsonSimpleSubgroup G) : EmbedsInSimpleSubgroupOfFinitelyPresented G := by
  obtain ⟨H, _, hfp, S, hS, _, _, f, hf⟩ := h
  exact ⟨H, inferInstance, hfp, S, hS, f, hf⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.BooneHigman.embedsInSimpleSubgroupOfFinitelyPresented_of_thompson

end BooneHigman
end SimpleKazhdanSofic
end GroupApproximation
