import GroupApproximation.Manuscript.SimpleKazhdanSofic.ThompsonConstruction.Delta
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimpleHosts.Host
import GroupApproximation.Manuscript.SimpleKazhdanSofic.BooneHigman.Kuznetsov
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SolvableWordProblemRecursivePresentation
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterWordProblem
import GroupApproximation.Meta.AxiomGuard

/-!
# Thompson's form of Boone–Higman, step 2: the simple host `G_Δ` and its word problem

`simple_kazhdan_sofic_group.tex`, section "LEF groups", tex l.447–451:

> Its last statement is the analogue for LEF groups of the
> theorem of Boone and Higman that a finitely generated group has solvable
> word problem if and only if it embeds in a simple subgroup of a finitely
> presented group~\cite{BooneHigman}, in Thompson's form, where the simple
> group is finitely generated and has solvable word problem~\cite{Thompson80}.

Thompson's 1980 construction is not formalized here. The simple group is the lamplighter host of
`cor:lef` instead (tex l.453–460 and the proof after it). Its simplicity and finite generation hold
with no LEF hypothesis.

## Proof route

1. `exists_levelDelta_commutator_embedding` (step 1): `Γ ↪ [Δ, Δ]`, with `Δ` infinite, finitely
   generated and with solvable word problem.
2. `SimpleHosts.simpleKazhdanHost`: `G_Δ = EL_3(LC(Ω, F_2) ⋊ Λ)` is finitely generated and simple.
   `Lamplighter.exists_commutator_embedding` embeds `[Δ, Δ]` in `G_Δ`. Composing gives
   `exists_simpleHost_embedding_of_hasSolvableWordProblem`, which is unconditional.
3. **Kuznetsov** (`BooneHigman.hasSolvableWordProblem_of_simpleSubgroup` with `S = ⊤`): a finitely
   generated simple group has solvable word problem if and only if it is recursively presented
   (`hasSolvableWordProblem_iff_nonempty_recursivePresentation`). This part is also
   unconditional.
4. **The one isolated gap**, `HostRecursivePresentationStatement`: for an infinite group `Δ` with
   solvable word problem, the set of trivial words of `G_Δ` is recursively enumerable. The
   manuscript's `lem:host` (used in the proof of `cor:lef`) says more: the word problem of `G_Δ`
   is Turing reducible to that of `Δ`, so the statement is true. By step 3 the gap is equivalent
   to "`G_Δ` has solvable word problem" (`hostRecursivePresentationStatement_iff`).
   `hostRecursivePresentationStatement_of_printedLamplighterHostSolvableWordProblem` discharges it
   from the corpus target `Lamplighter.PrintedLamplighterHostSolvableWordProblem`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace ThompsonConstruction

open Lamplighter

/-- A group with solvable word problem is finitely generated. -/
theorem fg_of_hasSolvableWordProblem {Γ : Type} [Group Γ] (h : HasSolvableWordProblem Γ) :
    Group.FG Γ := by
  obtain ⟨ι, _, _, s, hs, -⟩ := h
  exact Group.fg_iff.2 ⟨Set.range s, hs, Set.finite_range s⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThompsonConstruction.fg_of_hasSolvableWordProblem

/-- **Kuznetsov, for a simple group itself**: a finitely generated simple group with a recursive
presentation has solvable word problem. -/
theorem hasSolvableWordProblem_of_isSimpleGroup_of_recursivePresentation {H : Type} [Group H]
    [IsSimpleGroup H] (hH : Group.FG H) (rp : Higman.RecursivePresentation H) :
    HasSolvableWordProblem H := by
  haveI : IsSimpleGroup ↥(⊤ : Subgroup H) :=
    (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H).isSimpleGroup
  exact BooneHigman.hasSolvableWordProblem_of_simpleSubgroup hH rp ⊤
    (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H).symm.toMonoidHom
    (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H).symm.injective

#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThompsonConstruction.hasSolvableWordProblem_of_isSimpleGroup_of_recursivePresentation

/-- A finitely generated simple group has solvable word problem if and only if it is recursively
presented. -/
theorem hasSolvableWordProblem_iff_nonempty_recursivePresentation {H : Type} [Group H]
    [IsSimpleGroup H] (hH : Group.FG H) :
    HasSolvableWordProblem H ↔ Nonempty (Higman.RecursivePresentation H) :=
  ⟨nonempty_recursivePresentation_of_hasSolvableWordProblem, fun ⟨rp⟩ =>
    hasSolvableWordProblem_of_isSimpleGroup_of_recursivePresentation hH rp⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThompsonConstruction.hasSolvableWordProblem_iff_nonempty_recursivePresentation

/-- For an infinite finitely generated `Δ`, the host `G_Δ` has solvable word problem if and only
if it is recursively presented. -/
theorem hasSolvableWordProblem_host_iff (Δ : Type) [Group Δ] [Infinite Δ] (hΔ : Group.FG Δ) :
    HasSolvableWordProblem ↥(elementaryGroup (Fin 3) (LampRing Δ)) ↔
      Nonempty (Higman.RecursivePresentation ↥(elementaryGroup (Fin 3) (LampRing Δ))) := by
  obtain ⟨-, hfg, hsimple, -⟩ := SimpleHosts.simpleKazhdanHost Δ hΔ
  haveI : IsSimpleGroup ↥(elementaryGroup (Fin 3) (LampRing Δ)) := hsimple
  exact hasSolvableWordProblem_iff_nonempty_recursivePresentation hfg

#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThompsonConstruction.hasSolvableWordProblem_host_iff

/-- **The isolated gap** (the recursively enumerable half of `lem:host`): for an infinite group
`Δ` with solvable word problem, the lamplighter host `G_Δ = EL_3(LC(Ω, F_2) ⋊ Λ)` has a recursive
presentation, i.e. its trivial words form a recursively enumerable set.

It is true: `lem:host` gives a Turing reduction of the word problem of `G_Δ` to that of `Δ`. -/
def HostRecursivePresentationStatement : Prop :=
  ∀ (Δ : Type) [Group Δ], Infinite Δ → HasSolvableWordProblem Δ →
    Nonempty (Higman.RecursivePresentation ↥(elementaryGroup (Fin 3) (LampRing Δ)))

/-- **The gap closes the host word problem**: under `HostRecursivePresentationStatement`, the host
of an infinite group with solvable word problem has solvable word problem (Kuznetsov). -/
theorem hasSolvableWordProblem_host_of_hostRecursivePresentationStatement
    (hS : HostRecursivePresentationStatement) (Δ : Type) [Group Δ] [Infinite Δ]
    (hΔ : HasSolvableWordProblem Δ) :
    HasSolvableWordProblem ↥(elementaryGroup (Fin 3) (LampRing Δ)) :=
  (hasSolvableWordProblem_host_iff Δ (fg_of_hasSolvableWordProblem hΔ)).2
    (hS Δ inferInstance hΔ)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThompsonConstruction.hasSolvableWordProblem_host_of_hostRecursivePresentationStatement

/-- The gap is equivalent to solvability of the word problem of every such host. -/
theorem hostRecursivePresentationStatement_iff :
    HostRecursivePresentationStatement ↔
      ∀ (Δ : Type) [Group Δ], Infinite Δ → HasSolvableWordProblem Δ →
        HasSolvableWordProblem ↥(elementaryGroup (Fin 3) (LampRing Δ)) := by
  constructor
  · intro hS Δ _ _ hΔ
    exact hasSolvableWordProblem_host_of_hostRecursivePresentationStatement hS Δ hΔ
  · intro h Δ _ hinf hΔ
    exact nonempty_recursivePresentation_of_hasSolvableWordProblem (h Δ hinf hΔ)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThompsonConstruction.hostRecursivePresentationStatement_iff

/-- The corpus target `Lamplighter.PrintedLamplighterHostSolvableWordProblem` discharges the gap. -/
theorem hostRecursivePresentationStatement_of_printedLamplighterHostSolvableWordProblem
    (h : Lamplighter.PrintedLamplighterHostSolvableWordProblem) :
    HostRecursivePresentationStatement := by
  intro Δ _ _ hΔ
  exact nonempty_recursivePresentation_of_hasSolvableWordProblem (h Δ hΔ)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThompsonConstruction.hostRecursivePresentationStatement_of_printedLamplighterHostSolvableWordProblem

/-- **Every group with solvable word problem lies in a finitely generated simple host**
`G_Δ`, where `Δ` is infinite with solvable word problem. This is unconditional. -/
theorem exists_simpleHost_embedding_of_hasSolvableWordProblem {Γ : Type} [Group Γ]
    (h : HasSolvableWordProblem Γ) :
    ∃ (Δ : Type) (_ : Group Δ), Infinite Δ ∧ HasSolvableWordProblem Δ ∧
      IsSimpleGroup ↥(elementaryGroup (Fin 3) (LampRing Δ)) ∧
      Group.FG ↥(elementaryGroup (Fin 3) (LampRing Δ)) ∧
      ∃ f : Γ →* ↥(elementaryGroup (Fin 3) (LampRing Δ)), Function.Injective f := by
  obtain ⟨Δ, _, hinf, hfg, hwp, f, hf, hcomm⟩ := exists_levelDelta_commutator_embedding h
  haveI : Infinite Δ := hinf
  obtain ⟨-, hGfg, hGs, -⟩ := SimpleHosts.simpleKazhdanHost Δ hfg
  obtain ⟨e, he⟩ := Lamplighter.exists_commutator_embedding Δ
  refine ⟨Δ, inferInstance, hinf, hwp, hGs, hGfg,
    e.comp (f.codRestrict (commutator Δ) hcomm), ?_⟩
  intro x y hxy
  have h1 : e (f.codRestrict (commutator Δ) hcomm x) = e (f.codRestrict (commutator Δ) hcomm y) :=
    hxy
  exact hf (congrArg Subtype.val (he h1))

#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThompsonConstruction.exists_simpleHost_embedding_of_hasSolvableWordProblem

end ThompsonConstruction
end SimpleKazhdanSofic
end GroupApproximation
