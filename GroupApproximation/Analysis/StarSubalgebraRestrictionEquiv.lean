import Mathlib.Topology.Algebra.StarSubalgebra

/-!
# Restricting star-algebra equivalences between subalgebras
-/

namespace GroupApproximation

noncomputable section

universe u v

variable {R : Type u} {A : Type v}
variable [CommSemiring R] [StarRing R]
variable [Semiring A] [StarRing A] [Algebra R A] [StarModule R A]

/-- Restrict an ambient star-algebra equivalence from one subalgebra to
another when the equivalence and its inverse preserve the respective
subalgebras. -/
def restrictStarAlgEquivBetween (S T : StarSubalgebra R A)
    (F : A ≃⋆ₐ[R] A) (hforward : ∀ x : S, F x.1 ∈ T)
    (hbackward : ∀ x : T, F.symm x.1 ∈ S) : S ≃⋆ₐ[R] T := by
  let f : S →⋆ₐ[R] T :=
    (F.toStarAlgHom.comp S.subtype).codRestrict T hforward
  let g : T →⋆ₐ[R] S :=
    (F.symm.toStarAlgHom.comp T.subtype).codRestrict S hbackward
  have hgf : g.comp f = StarAlgHom.id R S := by
    apply StarAlgHom.ext
    intro x
    apply Subtype.ext
    exact F.symm_apply_apply x.1
  have hfg : f.comp g = StarAlgHom.id R T := by
    apply StarAlgHom.ext
    intro x
    apply Subtype.ext
    exact F.apply_symm_apply x.1
  exact StarAlgEquiv.ofStarAlgHom f g hgf hfg

@[simp] theorem restrictStarAlgEquivBetween_coe
    (S T : StarSubalgebra R A) (F : A ≃⋆ₐ[R] A)
    (hforward : ∀ x : S, F x.1 ∈ T)
    (hbackward : ∀ x : T, F.symm x.1 ∈ S) (x : S) :
    ((restrictStarAlgEquivBetween S T F hforward hbackward x : T) : A) =
      F x.1 :=
  rfl

end

end GroupApproximation
