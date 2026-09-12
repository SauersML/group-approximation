import GroupApproximation.Sofic.AlternatingLampExactRadical

/-!
# The factorization, on Hom-sets

Equality of radicals is the computation.  The statement worth printing is what
that equality does to `Hom`-sets: because the wreath projection `πₙ : Wₙ ↠ V` is
surjective and its kernel is exactly the lamp subgroup — which the finite,
residually finite and all-fields linear target classes each erase — precomposition
with `πₙ` is a **bijection**

  `Hom(V, T) ≃ Hom(Wₙ, T)`.

Read out loud: all of these target theories see `Wₙ` as exactly the same group
`V`.  That is more memorable than "four radicals coincide", and it is the same
fact.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRadicals

open SemidirectProduct AlternatingLampFamily MarkedCompression ExplicitLinearModel

/-- **The Hom-set form of the factorization.**  Precomposition with the wreath
projection is a bijection into every residually finite target, every finite
target, and every finite-dimensional linear target over every field. -/
def AlternatingFamilyTargetEquivalence : Prop :=
  ∀ n : ℕ, 5 ≤ n →
    (∀ (T : Type) [Group T], IsResiduallyFinite T →
        Function.Bijective
          (precomp (rightHom : WAlt n →* Vertical conjD conjD_injective) T)) ∧
      (∀ (T : Type) [Group T] [Finite T],
        Function.Bijective
          (precomp (rightHom : WAlt n →* Vertical conjD conjD_injective) T)) ∧
      (∀ (F : Type) [Field F] (d : ℕ),
        Function.Bijective
          (precomp (rightHom : WAlt n →* Vertical conjD conjD_injective)
            (Matrix.GeneralLinearGroup (Fin d) F)))

theorem manuscriptAlternatingFamilyTargetEquivalence :
    AlternatingFamilyTargetEquivalence := by
  intro n hn
  refine ⟨fun T _ hT => precomp_bijective_residuallyFinite hn T hT, ?_, ?_⟩
  · intro T _ _
    exact precomp_bijective_finite hn T
  · intro F _ d
    exact precomp_bijective_generalLinearGroup hn F d

end MFRadicals
end Manuscript
end GroupApproximation
