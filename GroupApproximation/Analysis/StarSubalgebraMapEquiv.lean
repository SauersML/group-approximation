import GroupApproximation.Analysis.StarSubalgebraMapEquivDef

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

@[simp] theorem starSubalgebraMapEquivOfInjective_coe
    (S : StarSubalgebra R A) (f : A →⋆ₐ[R] B)
    (hf : Function.Injective f) (x : S) :
    ((starSubalgebraMapEquivOfInjective S f hf x : S.map f) : B) = f x :=
  rfl

@[simp] theorem starSubalgebraMapEquivOfInjective_symm_coe
    (S : StarSubalgebra R A) (f : A →⋆ₐ[R] B)
    (hf : Function.Injective f) (x : S.map f) :
    f (((starSubalgebraMapEquivOfInjective S f hf).symm x : S) : A) =
      (x : B) := by
  have h := starSubalgebraMapEquivOfInjective_coe S f hf
    ((starSubalgebraMapEquivOfInjective S f hf).symm x)
  simpa only [StarAlgEquiv.apply_symm_apply] using h.symm

end

end GroupApproximation
