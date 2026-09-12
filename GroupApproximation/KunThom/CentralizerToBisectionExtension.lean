import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Basic

/-!
# Extending a partial injection to a class-preserving permutation

The object permutation of a bisection moves every object inside its
connectivity class.  A permutation of the ambient model determines the object
map only on the objects where it gives a candidate arrow.  This file extends
such a map to a permutation of all objects that does not leave any class.

* `exists_perm_extending_fiberwise`: a map injective on a subset and
  preserving a function `q` there extends to a permutation preserving `q`.
-/

namespace GroupApproximation
namespace BlockPatching

/-- **Fiberwise extension.**  If `π` is injective on `good` and preserves `q`
there, some permutation agrees with `π` on `good` and preserves `q`
everywhere. -/
theorem exists_perm_extending_fiberwise {I : Type*} [Finite I] {γ : Type*}
    (q : I → γ) (good : Set I) (π : I → I) (hinj : Set.InjOn π good)
    (hq : ∀ X ∈ good, q (π X) = q X) :
    ∃ σ : Equiv.Perm I, (∀ X ∈ good, σ X = π X) ∧ ∀ X, q (σ X) = q X := by
  classical
  have hfiber : ∀ c : γ, ∃ e : Equiv.Perm {X // q X = c},
      ∀ a : {X // X ∈ good ∧ q X = c},
        e ⟨a.1, a.2.2⟩ = ⟨π a.1, (hq a.1 a.2.1).trans a.2.2⟩ := fun c ↦
    Equiv.Perm.exists_extending_pair
      (fun a : {X // X ∈ good ∧ q X = c} ↦ (⟨a.1, a.2.2⟩ : {X // q X = c}))
      (fun a : {X // X ∈ good ∧ q X = c} ↦
        (⟨π a.1, (hq a.1 a.2.1).trans a.2.2⟩ : {X // q X = c}))
      (fun a b hab ↦ by
        have h := congrArg Subtype.val hab
        exact Subtype.ext h)
      (fun a b hab ↦ by
        have h := congrArg Subtype.val hab
        exact Subtype.ext (hinj a.2.1 b.2.1 h))
  choose e he using hfiber
  refine ⟨Equiv.ofFiberEquiv e, fun X hX ↦ ?_, fun X ↦ Equiv.ofFiberEquiv_map e X⟩
  have h := congrArg Subtype.val (he (q X) ⟨X, hX, rfl⟩)
  exact h

end BlockPatching
end GroupApproximation
