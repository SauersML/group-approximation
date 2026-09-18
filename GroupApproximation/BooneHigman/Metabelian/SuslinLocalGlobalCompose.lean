import GroupApproximation.BooneHigman.Metabelian.SuslinLocalGlobalSubstitution
import GroupApproximation.Meta.AxiomGuard

/-!
# Suslin local-global route, part 2: composition laws of the substitutions

Lane `bh-met-53`.  The composition laws of the substitutions of
`SuslinLocalGlobalSubstitution.lean` (checked on the generators `C x` and `X` with
`Polynomial.ringHom_ext`), and the functoriality of `elementaryMatrixUnitMap`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

variable {A : Type*} [CommRing A]

/-- `p(X + 0 Y) = p(X)`. -/
theorem suslinLocalGlobalShift_zero :
    suslinLocalGlobalShift (0 : A) =
      (Polynomial.C : Polynomial A →+* Polynomial (Polynomial A)) := by
  apply Polynomial.ringHom_ext
  · intro x
    rw [suslinLocalGlobalShift_C]
  · rw [suslinLocalGlobalShift_X, map_zero, map_zero, zero_mul, add_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalGlobalShift_zero

/-- Dilating `Y` by `c` after shifting by `a` is shifting by `c a`. -/
theorem suslinLocalGlobalDilate_comp_shift (c a : A) :
    (suslinLocalGlobalDilate c).comp (suslinLocalGlobalShift a) =
      suslinLocalGlobalShift (c * a) := by
  apply Polynomial.ringHom_ext
  · intro x
    rw [RingHom.comp_apply, suslinLocalGlobalShift_C, suslinLocalGlobalShift_C,
      suslinLocalGlobalDilate_C]
  · rw [RingHom.comp_apply, suslinLocalGlobalShift_X, suslinLocalGlobalShift_X,
      map_add (suslinLocalGlobalDilate c), map_mul (suslinLocalGlobalDilate c),
      suslinLocalGlobalDilate_C, suslinLocalGlobalDilate_C, suslinLocalGlobalDilate_X]
    simp only [map_mul]
    ring

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalGlobalDilate_comp_shift

/-- Dilating `Y` fixes `A[X]`. -/
theorem suslinLocalGlobalDilate_comp_C (c : A) :
    (suslinLocalGlobalDilate c).comp
        (Polynomial.C : Polynomial A →+* Polynomial (Polynomial A)) =
      (Polynomial.C : Polynomial A →+* Polynomial (Polynomial A)) :=
  RingHom.ext fun p ↦ suslinLocalGlobalDilate_C c p

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalGlobalDilate_comp_C

/-- Translating `X` by `bY` after shifting by `a` is shifting by `a + b`. -/
theorem suslinLocalGlobalTranslate_comp_shift (b a : A) :
    (suslinLocalGlobalTranslate b).comp (suslinLocalGlobalShift a) =
      suslinLocalGlobalShift (a + b) := by
  apply Polynomial.ringHom_ext
  · intro x
    rw [RingHom.comp_apply, suslinLocalGlobalShift_C, suslinLocalGlobalShift_C,
      suslinLocalGlobalTranslate_C, suslinLocalGlobalShift_C]
  · rw [RingHom.comp_apply, suslinLocalGlobalShift_X, suslinLocalGlobalShift_X,
      map_add (suslinLocalGlobalTranslate b), map_mul (suslinLocalGlobalTranslate b),
      suslinLocalGlobalTranslate_C, suslinLocalGlobalTranslate_C, suslinLocalGlobalTranslate_X,
      suslinLocalGlobalShift_X, suslinLocalGlobalShift_C]
    simp only [map_add]
    ring

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalGlobalTranslate_comp_shift

/-- Translating `X` by `bY` restricts on `A[X]` to shifting by `b`. -/
theorem suslinLocalGlobalTranslate_comp_C (b : A) :
    (suslinLocalGlobalTranslate b).comp
        (Polynomial.C : Polynomial A →+* Polynomial (Polynomial A)) =
      suslinLocalGlobalShift b :=
  RingHom.ext fun p ↦ suslinLocalGlobalTranslate_C b p

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalGlobalTranslate_comp_C

/-- `q(X, Y) ↦ q(0, X)` undoes `p(X) ↦ p(X + Y)`. -/
theorem suslinLocalGlobalRestrict_comp_shift_one :
    (suslinLocalGlobalRestrict (A := A)).comp (suslinLocalGlobalShift (1 : A)) =
      RingHom.id (Polynomial A) := by
  apply Polynomial.ringHom_ext
  · intro x
    rw [RingHom.comp_apply, RingHom.id_apply, suslinLocalGlobalShift_C,
      suslinLocalGlobalRestrict_C, Polynomial.constantCoeff_apply, Polynomial.coeff_C_zero]
  · rw [RingHom.comp_apply, RingHom.id_apply, suslinLocalGlobalShift_X,
      map_add (suslinLocalGlobalRestrict (A := A)), map_mul (suslinLocalGlobalRestrict (A := A)),
      suslinLocalGlobalRestrict_C, suslinLocalGlobalRestrict_C, suslinLocalGlobalRestrict_X,
      Polynomial.constantCoeff_apply, Polynomial.constantCoeff_apply, Polynomial.coeff_X_zero,
      Polynomial.coeff_C_zero, map_zero, map_one, zero_add, one_mul]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalGlobalRestrict_comp_shift_one

/-- On `A[X]`, `q(X, Y) ↦ q(0, X)` is evaluation at `0`. -/
theorem suslinLocalGlobalRestrict_comp_C :
    (suslinLocalGlobalRestrict (A := A)).comp
        (Polynomial.C : Polynomial A →+* Polynomial (Polynomial A)) =
      (Polynomial.C : A →+* Polynomial A).comp (Polynomial.constantCoeff (R := A)) :=
  RingHom.ext fun p ↦ suslinLocalGlobalRestrict_C p

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalGlobalRestrict_comp_C

/-- Functoriality of `elementaryMatrixUnitMap`. -/
theorem suslinLocalGlobal_map_map {R S T : Type*} [Ring R] [Ring S] [Ring T]
    {N : ℕ} (f : S →+* T) (g : R →+* S) (u : Matrix.GeneralLinearGroup (Fin N) R) :
    elementaryMatrixUnitMap (ι := Fin N) f (elementaryMatrixUnitMap (ι := Fin N) g u) =
      elementaryMatrixUnitMap (ι := Fin N) (f.comp g) u := by
  apply Units.ext
  ext i j
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalGlobal_map_map

/-- `elementaryMatrixUnitMap` of the identity. -/
theorem suslinLocalGlobal_map_id {R : Type*} [Ring R] {N : ℕ}
    (u : Matrix.GeneralLinearGroup (Fin N) R) :
    elementaryMatrixUnitMap (ι := Fin N) (RingHom.id R) u = u := by
  apply Units.ext
  ext i j
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalGlobal_map_id

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
