import GroupApproximation.Sofic.NormMFUniversalCorona
import GroupApproximation.Sofic.OperatorMFFreeProductConsequences

/-!
# MF-radical membership on a retracting free factor

The canonical retraction `E * A -> A` detects every nonidentity element of the
right factor whenever `A` has trivial MF residual.  This is the group-theoretic
core of the fixed-group radical-membership reduction; the external existence
of a finitely presented amenable `A` with undecidable word problem is kept in
Cairn rather than asserted as a Lean axiom.
-/

namespace GroupApproximation
namespace FreeProductMFRadicalRetraction

open scoped Monoid.Coprod

universe u v

variable {E : Type u} {A : Type v} [Group E] [Group A]

/-- The canonical retraction from `E * A` onto its right factor. -/
def rightRetraction : E ∗ A →* A :=
  Monoid.Coprod.lift (1 : E →* A) (MonoidHom.id A)

@[simp] theorem rightRetraction_inr (a : A) :
    rightRetraction (E := E) (Monoid.Coprod.inr a) = a := by
  simp [rightRetraction]

/-- A right-factor word belongs to the free product's MF residual exactly when
it is trivial, provided the right factor has trivial MF residual. -/
theorem inr_mem_normMFResidual_iff_of_residual_eq_bot
    (hA : normMFResidual A = ⊥) (a : A) :
    Monoid.Coprod.inr a ∈ normMFResidual (E ∗ A) ↔ a = 1 := by
  constructor
  · intro ha
    have hmap : rightRetraction (E := E) (Monoid.Coprod.inr a) ∈
        normMFResidual A :=
      (show NormMFInvisible (Monoid.Coprod.inr a : E ∗ A) from ha).map
        (rightRetraction (E := E))
    rw [rightRetraction_inr, hA] at hmap
    exact Subgroup.mem_bot.mp hmap
  · rintro rfl
    simp

/-- In particular, every countable operator-MF right factor has this exact
membership reduction inside an arbitrary free product. -/
theorem inr_mem_normMFResidual_iff_of_isOperatorMF [Countable A]
    (hA : IsOperatorMF A) (a : A) :
    Monoid.Coprod.inr a ∈ normMFResidual (E ∗ A) ↔ a = 1 :=
  inr_mem_normMFResidual_iff_of_residual_eq_bot
    (normMFResidual_eq_bot_of_isOperatorMF hA) a

/-- Package the finite-presentation and non-MF clauses used when a non-MF
left factor is adjoined solely to make the fixed ambient group non-MF. -/
theorem finitelyPresented_not_isOperatorMF
    [Group.IsFinitelyPresented E] [Group.IsFinitelyPresented A]
    (hE : ¬ IsOperatorMF E) :
    Group.IsFinitelyPresented (E ∗ A) ∧ ¬ IsOperatorMF (E ∗ A) :=
  ⟨coprod_isFinitelyPresented, not_isOperatorMF_coprod_left hE⟩

end FreeProductMFRadicalRetraction
end GroupApproximation
