import GroupApproximation.Analysis.StarSubalgebraRestrictionEquiv

/-!
# A star subalgebra is equivalent to its injective image
-/

namespace GroupApproximation

noncomputable section

universe u v w

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R] [StarRing R]
variable [Semiring A] [StarRing A] [Algebra R A] [StarModule R A]
variable [Semiring B] [StarRing B] [Algebra R B] [StarModule R B]

/-- An injective star-algebra homomorphism identifies a star subalgebra with
its image. -/
def starSubalgebraMapEquivOfInjective (S : StarSubalgebra R A)
    (f : A →⋆ₐ[R] B) (hf : Function.Injective f) :
    S ≃⋆ₐ[R] S.map f := by
  let e := S.toSubalgebra.equivMapOfInjective f.toAlgHom hf
  exact
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_mul' := e.map_mul
      map_star' := fun x ↦ by
        apply Subtype.ext
        exact map_star f (x : A)
      map_smul' := fun r x ↦ by
        apply Subtype.ext
        exact map_smul f r (x : A) }

end

end GroupApproximation
