import GroupApproximation.Manuscript.SimpleKazhdanSofic.LevelShiftDeltaWordProblem
import GroupApproximation.Meta.AxiomGuard

/-!
# Thompson's form of Boone–Higman, step 1: the level-shift group `Δ` without LEF

`simple_kazhdan_sofic_group.tex`, section "LEF groups", tex l.447–451:

> Its last statement is the analogue for LEF groups of the
> theorem of Boone and Higman that a finitely generated group has solvable
> word problem if and only if it embeds in a simple subgroup of a finitely
> presented group~\cite{BooneHigman}, in Thompson's form, where the simple
> group is finitely generated and has solvable word problem~\cite{Thompson80}.

The open direction of the row is "solvable word problem ⇒ embeds in a finitely generated simple
group with solvable word problem". This file is its first step. It is the second choice of `Δ`
from the proof of `cor:lef` with the LEF clause dropped.

Let `Γ` have solvable word problem with finite generating family `s`, and put `E = range s`.
On `Γ × ℤ`, `β` raises the level and `h_γ` multiplies the levels `m ≥ 0` by `γ` on the left.
Then `Δ = ⟨β, h_γ : γ ∈ E⟩` has these properties:

* `Δ` is infinite (`LevelShiftDelta.infinite_levelDelta`) and finitely generated
  (`LevelShiftDelta.fg_levelDelta`);
* `Γ ↪ [Δ, Δ]` (`LevelShiftDelta.exists_levelZeroEmbedding`);
* `Δ` has solvable word problem
  (`LevelShiftDeltaWordProblem.hasSolvableWordProblem_closure_levelGen`).

`exists_levelDelta_commutator_embedding` packages the four facts.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace ThompsonConstruction

open LevelShiftDelta LevelShiftDeltaWordProblem

/-- **A group with solvable word problem lies in the commutator subgroup of an infinite finitely
generated group with solvable word problem.** No LEF hypothesis is needed. -/
theorem exists_levelDelta_commutator_embedding {Γ : Type} [Group Γ]
    (h : HasSolvableWordProblem Γ) :
    ∃ (Δ : Type) (_ : Group Δ), Infinite Δ ∧ Group.FG Δ ∧ HasSolvableWordProblem Δ ∧
      ∃ f : Γ →* Δ, Function.Injective f ∧ ∀ γ, f γ ∈ commutator Δ := by
  obtain ⟨ι, hp, hfin, s, hgen, hpar⟩ := h
  classical
  have hfinr : (Set.range s).Finite := Set.finite_range s
  have ht : Set.range s = ((hfinr.toFinset : Finset Γ) : Set Γ) := by
    rw [Set.Finite.coe_toFinset]
  have hE : Subgroup.closure ((hfinr.toFinset : Finset Γ) : Set Γ) = ⊤ := by
    rw [← ht]
    exact hgen
  have hΔ : levelDelta Γ hfinr.toFinset = Subgroup.closure (Set.range (levelGen s)) :=
    levelDelta_eq_closure_range hfinr.toFinset s ht
  obtain ⟨f, hf, hfc⟩ := exists_levelZeroEmbedding hfinr.toFinset hE
  have hswp := hasSolvableWordProblem_closure_levelGen s hpar
  rw [← hΔ] at hswp
  exact ⟨↥(levelDelta Γ hfinr.toFinset), inferInstance, infinite_levelDelta hfinr.toFinset,
    fg_levelDelta hfinr.toFinset, hswp, f, hf, hfc⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThompsonConstruction.exists_levelDelta_commutator_embedding

end ThompsonConstruction
end SimpleKazhdanSofic
end GroupApproximation
