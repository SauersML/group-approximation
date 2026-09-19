import GroupApproximation.Kazhdan.IntegerNotKazhdan
import GroupApproximation.Sofic.MarkedCompressionGroup

/-!
# The ascending HNN skeleton is not Kazhdan

Corollary 9.4 of the dossier, applied to the repository's ascending-HNN model.

The vertical group is the telescope extended by the shift, so its right
projection onto `Multiplicative ℤ` is the height homomorphism and is surjective.
Since property `(T)` passes to quotients and `ℤ` is not Kazhdan, the ambient
group of the compression construction is as far from `(T)` as having an infinite
cyclic quotient.

This is exactly the structural difference from the Kun--Thom nonsoficity
criterion, whose hypotheses require the *ambient* group to be Kazhdan too: here
only the compressed base `Γ` is Kazhdan.
-/

namespace GroupApproximation
namespace MarkedCompression

open SemidirectProduct

universe u

variable {Γ : Type u} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

/-- The height homomorphism of the ascending-HNN model. -/
abbrev heightHom : Vertical α hα →* Multiplicative ℤ := rightHom

theorem heightHom_surjective : Function.Surjective (heightHom α hα) :=
  rightHom_surjective

/-- **Corollary 9.4.**  The ascending-HNN skeleton does not have property `(T)`,
because it surjects onto `ℤ`. -/
theorem not_hasKazhdanPropertyT_vertical :
    ¬ HasKazhdanPropertyT.{u, 0} (Vertical α hα) :=
  not_hasKazhdanPropertyT_of_surjective_onto_int (heightHom α hα)
    (heightHom_surjective α hα)

end MarkedCompression
end GroupApproximation
