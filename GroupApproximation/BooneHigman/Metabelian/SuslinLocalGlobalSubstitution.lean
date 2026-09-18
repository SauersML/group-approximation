import GroupApproximation.BooneHigman.Metabelian.SuslinMonicPatching
import Mathlib.Algebra.Polynomial.Eval.Defs
import GroupApproximation.Meta.AxiomGuard

/-!
# Suslin local-global route, part 1: the substitutions of Quillen's patching argument

Lane `bh-met-53`.  Quillen's patching argument (in Suslin's form for the elementary group)
studies, for `τ(X) ∈ GL_N(A[X])`, the matrix `τ(X + aY) τ(X)⁻¹` over `A[X][Y]`.  Here
`A[X][Y]` is `Polynomial (Polynomial A)`: the inner variable `X` is `C X` and the outer
variable `Y` is `X`.  This file defines the four ring homomorphisms the argument uses and
proves their composition laws:

* `suslinLocalGlobalShift a : A[X] → A[X][Y]`, `p(X) ↦ p(X + aY)`;
* `suslinLocalGlobalDilate c : A[X][Y] → A[X][Y]`, `q(X, Y) ↦ q(X, cY)`;
* `suslinLocalGlobalTranslate b : A[X][Y] → A[X][Y]`, `q(X, Y) ↦ q(X + bY, Y)`;
* `suslinLocalGlobalRestrict : A[X][Y] → A[X]`, `q(X, Y) ↦ q(0, X)`;

with `shift 0 = C`, `dilate c ∘ shift a = shift (c a)`, `translate b ∘ shift a = shift (a + b)`,
`restrict ∘ shift 1 = id` and `restrict ∘ C = C ∘ (evaluation at 0)`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

variable {A : Type*} [CommRing A]

/-- `p(X) ↦ p(X + aY)`, as a ring homomorphism `A[X] → A[X][Y]`. -/
noncomputable def suslinLocalGlobalShift (a : A) : Polynomial A →+* Polynomial (Polynomial A) :=
  Polynomial.eval₂RingHom
    ((Polynomial.C : Polynomial A →+* Polynomial (Polynomial A)).comp
      (Polynomial.C : A →+* Polynomial A))
    (Polynomial.C (Polynomial.X : Polynomial A) +
      Polynomial.C (Polynomial.C a) * (Polynomial.X : Polynomial (Polynomial A)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalGlobalShift

/-- `q(X, Y) ↦ q(X, cY)`, as a ring homomorphism `A[X][Y] → A[X][Y]`. -/
noncomputable def suslinLocalGlobalDilate (c : A) :
    Polynomial (Polynomial A) →+* Polynomial (Polynomial A) :=
  Polynomial.eval₂RingHom (Polynomial.C : Polynomial A →+* Polynomial (Polynomial A))
    (Polynomial.C (Polynomial.C c) * (Polynomial.X : Polynomial (Polynomial A)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalGlobalDilate

/-- `q(X, Y) ↦ q(X + bY, Y)`, as a ring homomorphism `A[X][Y] → A[X][Y]`. -/
noncomputable def suslinLocalGlobalTranslate (b : A) :
    Polynomial (Polynomial A) →+* Polynomial (Polynomial A) :=
  Polynomial.eval₂RingHom (suslinLocalGlobalShift b) (Polynomial.X : Polynomial (Polynomial A))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalGlobalTranslate

/-- `q(X, Y) ↦ q(0, X)`, as a ring homomorphism `A[X][Y] → A[X]`. -/
noncomputable def suslinLocalGlobalRestrict : Polynomial (Polynomial A) →+* Polynomial A :=
  Polynomial.eval₂RingHom
    ((Polynomial.C : A →+* Polynomial A).comp (Polynomial.constantCoeff (R := A)))
    (Polynomial.X : Polynomial A)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalGlobalRestrict

theorem suslinLocalGlobalShift_C (a x : A) :
    suslinLocalGlobalShift a (Polynomial.C x) = Polynomial.C (Polynomial.C x) := by
  rw [suslinLocalGlobalShift, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
    RingHom.comp_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalGlobalShift_C

theorem suslinLocalGlobalShift_X (a : A) :
    suslinLocalGlobalShift a Polynomial.X =
      Polynomial.C (Polynomial.X : Polynomial A) +
        Polynomial.C (Polynomial.C a) * (Polynomial.X : Polynomial (Polynomial A)) := by
  rw [suslinLocalGlobalShift, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalGlobalShift_X

theorem suslinLocalGlobalDilate_C (c : A) (p : Polynomial A) :
    suslinLocalGlobalDilate c (Polynomial.C p) = Polynomial.C p := by
  rw [suslinLocalGlobalDilate, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalGlobalDilate_C

theorem suslinLocalGlobalDilate_X (c : A) :
    suslinLocalGlobalDilate c Polynomial.X =
      Polynomial.C (Polynomial.C c) * (Polynomial.X : Polynomial (Polynomial A)) := by
  rw [suslinLocalGlobalDilate, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalGlobalDilate_X

theorem suslinLocalGlobalTranslate_C (b : A) (p : Polynomial A) :
    suslinLocalGlobalTranslate b (Polynomial.C p) = suslinLocalGlobalShift b p := by
  rw [suslinLocalGlobalTranslate, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalGlobalTranslate_C

theorem suslinLocalGlobalTranslate_X (b : A) :
    suslinLocalGlobalTranslate b Polynomial.X = (Polynomial.X : Polynomial (Polynomial A)) := by
  rw [suslinLocalGlobalTranslate, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalGlobalTranslate_X

theorem suslinLocalGlobalRestrict_C (p : Polynomial A) :
    suslinLocalGlobalRestrict (Polynomial.C p) = Polynomial.C (Polynomial.constantCoeff p) := by
  rw [suslinLocalGlobalRestrict, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
    RingHom.comp_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalGlobalRestrict_C

theorem suslinLocalGlobalRestrict_X :
    suslinLocalGlobalRestrict (A := A) Polynomial.X = (Polynomial.X : Polynomial A) := by
  rw [suslinLocalGlobalRestrict, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalGlobalRestrict_X

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
