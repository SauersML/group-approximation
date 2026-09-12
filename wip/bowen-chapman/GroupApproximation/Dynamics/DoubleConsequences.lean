import GroupApproximation.Sofic.WeakMFNonsoficDouble
import Mathlib.GroupTheory.Finiteness

/-!
# Finite generation and witness consequences for symmetric doubles

The two copies of a finite generating set generate the symmetric double.
-/

namespace GroupApproximation

open Monoid

universe u

/-- A symmetric double of a finitely generated group is finitely generated,
without any finite-generation assumption on the amalgamating subgroup. -/
theorem symmetricDouble_finitelyGenerated (G : Type u) [Group G] [Group.FG G]
    (Γ : Subgroup G) : Group.FG (SymmetricDouble G Γ) := by
  classical
  obtain ⟨S, hS⟩ : (⊤ : Subgroup G).FG := (inferInstance : Group.FG G).out
  let T : Set (SymmetricDouble G Γ) :=
    inDouble G Γ false '' (S : Set G) ∪ inDouble G Γ true '' (S : Set G)
  have hvertex (b : Bool) (g : G) : inDouble G Γ b g ∈ Subgroup.closure T := by
    have hg : inDouble G Γ b g ∈ Subgroup.closure (inDouble G Γ b '' (S : Set G)) := by
      rw [← MonoidHom.map_closure, hS]
      exact ⟨g, Subgroup.mem_top g, rfl⟩
    apply Subgroup.closure_mono (t := T) ?_ hg
    cases b
    · exact Set.subset_union_left
    · exact Set.subset_union_right
  refine Group.fg_iff.mpr ⟨T, ?_,
    ((S : Set G).toFinite.image _).union ((S : Set G).toFinite.image _)⟩
  apply eq_top_iff.mpr
  intro x _
  apply PushoutI.induction_on x
  · exact hvertex
  · intro γ
    rw [← PushoutI.of_apply_eq_base (doubleMap G Γ) false γ]
    exact hvertex false γ
  · exact fun _ _ => (Subgroup.closure T).mul_mem

end GroupApproximation
