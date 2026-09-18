import GroupApproximation.GroupTheory.HydeLodha.FinitelyPresentedInfiniteSimpleClosed
import GroupApproximation.Meta.AxiomGuard

/-!
# An infinite finitely presented simple group, as an explicit finite presentation

This module restates `finitelyPresentedInfiniteSimple_closed` (Hyde–Lodha's
`Q₂ = [Γ₂, Γ₂]`, finitely presented, infinite and simple) in the concrete form of the
lean-eval benchmark problem `higman_infinite_simple`: some `n` and a finite relator set
`rels ⊆ FreeGroup (Fin n)` whose presented group is simple and infinite.

The only step beyond the closed theorem is Mathlib's
`Group.IsFinitelyPresented.exists_mulEquiv_presentedGroup`, which replaces an abstract
finitely presented group by an isomorphic `PresentedGroup` on finitely many relators;
simplicity and infinitude transfer along the isomorphism.
-/

namespace GroupApproximation
namespace HydeLodha

/-- **An infinite finitely presented simple group, as a finite presentation.**
The statement is the lean-eval problem `higman_infinite_simple` verbatim. -/
theorem higman_infinite_simple :
    ∃ (n : ℕ) (rels : Set (FreeGroup (Fin n))),
      rels.Finite ∧ IsSimpleGroup (PresentedGroup rels) ∧
        Infinite (PresentedGroup rels) := by
  obtain ⟨W, _, hfp, -, hsimple, hinf⟩ := finitelyPresentedInfiniteSimple_closed
  obtain ⟨n, rels, hrels, ⟨e⟩⟩ := Group.IsFinitelyPresented.exists_mulEquiv_presentedGroup (G := W)
  exact ⟨n, rels, hrels, e.symm.isSimpleGroup, Infinite.of_injective e e.injective⟩

#audit_closed_axioms GroupApproximation.HydeLodha.higman_infinite_simple

end HydeLodha
end GroupApproximation
