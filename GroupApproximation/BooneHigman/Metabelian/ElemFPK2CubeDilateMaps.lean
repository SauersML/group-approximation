import Mathlib.RingTheory.Localization.Away.Basic
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2CubeDiagDilateLocal
import GroupApproximation.Meta.AxiomGuard

/-!
# Ring maps for the Tulenbaev dilation step of the cube gap

Lane `bh-met-90c`, helper module.  For a commutative ring `A` and `c ∈ A`:

* `k2CubeDilate_scale A c : A[X] → A[X]`, `X ↦ c X`, fixing `A` (the *dilation*).
  With `A = B[t]` and `c = C b` this is `quillenScale B b` by definition
  (`k2CubeDilate_scale_polynomial`).
* `k2CubeDilate_scale_zero`: `X ↦ 0 · X` is `C ∘ ev_{X=0}`.
* `k2CubeDilate_scale_one`: `X ↦ 1 · X` is the identity.
* `k2CubeDilate_evalZero_comp_shift`, `k2CubeDilate_evalZero_comp_C`: `ev_{y=0} ∘ σ_a = id` and
  `ev_{y=0} ∘ C = id`.

For `B`, `s₀ ∈ B` and `L = B[t]_{C s₀}`, write `ι : B[t] → L` and `ι[y] : B[t][y] → L[y]`.

* `k2CubeDilate_shiftLoc s₀ a : L → L[y]` is the unique extension of `ι[y] ∘ σ_a` through `ι`.  It
  exists because `σ_a (C s₀) = C (C s₀)` becomes a unit in `L[y]`.
* `k2CubeDilate_loc_comp_shift`: `ι[y] ∘ σ_a = shiftLoc ∘ ι`.
* `k2CubeDilate_loc_comp_C`: `ι[y] ∘ C = C ∘ ι`.

All of this is ring theory: the evaluation, composition and universal property of `Away`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

section DilateMaps

variable (A : Type*) [CommRing A]

/-- The dilation `X ↦ c X` of `A[X]`, fixing `A`. -/
noncomputable def k2CubeDilate_scale (c : A) : Polynomial A →+* Polynomial A :=
  Polynomial.eval₂RingHom (Polynomial.C : A →+* Polynomial A) (Polynomial.C c * Polynomial.X)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2CubeDilate_scale

variable {A}

theorem k2CubeDilate_scale_C (c a : A) :
    k2CubeDilate_scale A c (Polynomial.C a) = Polynomial.C a := by
  rw [k2CubeDilate_scale, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2CubeDilate_scale_C

theorem k2CubeDilate_scale_X (c : A) :
    k2CubeDilate_scale A c Polynomial.X = Polynomial.C c * Polynomial.X := by
  rw [k2CubeDilate_scale, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2CubeDilate_scale_X

/-- The dilation by `0` is `C ∘ ev_{X=0}`. -/
theorem k2CubeDilate_scale_zero :
    k2CubeDilate_scale A 0 =
      (Polynomial.C : A →+* Polynomial A).comp (Polynomial.evalRingHom (0 : A)) :=
  Polynomial.ringHom_ext
    (fun a ↦ by
      rw [k2CubeDilate_scale_C, RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_C])
    (by
      rw [k2CubeDilate_scale_X, RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_X,
        map_zero, zero_mul])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2CubeDilate_scale_zero

/-- The dilation by `1` is the identity. -/
theorem k2CubeDilate_scale_one : k2CubeDilate_scale A 1 = RingHom.id (Polynomial A) :=
  Polynomial.ringHom_ext
    (fun a ↦ by rw [k2CubeDilate_scale_C, RingHom.id_apply])
    (by rw [k2CubeDilate_scale_X, map_one, one_mul, RingHom.id_apply])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2CubeDilate_scale_one

/-- On `B[t][y]`, the dilation of `y` by `C b` is `quillenScale B b`, by definition. -/
theorem k2CubeDilate_scale_polynomial {B : Type*} [CommRing B] (b : B) :
    k2CubeDilate_scale (Polynomial B) (Polynomial.C b) = quillenScale B b :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2CubeDilate_scale_polynomial

/-- `ev_{X=0} ∘ C = id`. -/
theorem k2CubeDilate_evalZero_comp_C :
    (Polynomial.evalRingHom (0 : A)).comp (Polynomial.C : A →+* Polynomial A) = RingHom.id A :=
  RingHom.ext fun a ↦ by
    rw [RingHom.comp_apply, RingHom.id_apply, Polynomial.coe_evalRingHom, Polynomial.eval_C]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2CubeDilate_evalZero_comp_C

/-- `ev_{y=0} ∘ σ_a = id` on `B[t]`: `t + a y` becomes `t` at `y = 0`. -/
theorem k2CubeDilate_evalZero_comp_shift {B : Type*} [CommRing B] (a : B) :
    (Polynomial.evalRingHom (0 : Polynomial B)).comp (quillenShift B a) =
      RingHom.id (Polynomial B) :=
  Polynomial.ringHom_ext
    (fun b ↦ by
      rw [RingHom.comp_apply, RingHom.id_apply, quillenShift_C, Polynomial.coe_evalRingHom,
        Polynomial.eval_C])
    (by
      rw [RingHom.comp_apply, RingHom.id_apply, quillenShift_X, Polynomial.coe_evalRingHom,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_C,
        Polynomial.eval_X, mul_zero, add_zero])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2CubeDilate_evalZero_comp_shift

end DilateMaps

section DilateLoc

variable {B : Type*} [CommRing B]

/-- `ι[y] (σ_a (C s₀)) = C (ι (C s₀))` is a unit in `L[y]`, `L = B[t]_{C s₀}`. -/
theorem k2CubeDilate_isUnit_loc_shift (s₀ a : B) :
    IsUnit (((Polynomial.mapRingHom (algebraMap (Polynomial B)
        (Localization.Away (Polynomial.C s₀ : Polynomial B)))).comp (quillenShift B a))
      (Polynomial.C s₀)) := by
  rw [RingHom.comp_apply, quillenShift_C, Polynomial.coe_mapRingHom, Polynomial.map_C]
  exact (IsLocalization.Away.algebraMap_isUnit
    (S := Localization.Away (Polynomial.C s₀ : Polynomial B)) (Polynomial.C s₀)).map
      (Polynomial.C : Localization.Away (Polynomial.C s₀ : Polynomial B) →+*
        Polynomial (Localization.Away (Polynomial.C s₀ : Polynomial B)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2CubeDilate_isUnit_loc_shift

/-- The extension `L → L[y]` of `ι[y] ∘ σ_a` through `ι : B[t] → L = B[t]_{C s₀}`. -/
noncomputable def k2CubeDilate_shiftLoc (s₀ a : B) :
    Localization.Away (Polynomial.C s₀ : Polynomial B) →+*
      Polynomial (Localization.Away (Polynomial.C s₀ : Polynomial B)) :=
  IsLocalization.Away.lift (Polynomial.C s₀ : Polynomial B) (k2CubeDilate_isUnit_loc_shift s₀ a)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2CubeDilate_shiftLoc

/-- `ι[y] ∘ σ_a = shiftLoc ∘ ι`. -/
theorem k2CubeDilate_loc_comp_shift (s₀ a : B) :
    (Polynomial.mapRingHom (algebraMap (Polynomial B)
        (Localization.Away (Polynomial.C s₀ : Polynomial B)))).comp (quillenShift B a) =
      (k2CubeDilate_shiftLoc s₀ a).comp
        (algebraMap (Polynomial B) (Localization.Away (Polynomial.C s₀ : Polynomial B))) := by
  rw [k2CubeDilate_shiftLoc, IsLocalization.Away.lift_comp]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2CubeDilate_loc_comp_shift

/-- `ι[y] ∘ C = C ∘ ι`. -/
theorem k2CubeDilate_loc_comp_C (s₀ : B) :
    (Polynomial.mapRingHom (algebraMap (Polynomial B)
        (Localization.Away (Polynomial.C s₀ : Polynomial B)))).comp
        (Polynomial.C : Polynomial B →+* Polynomial (Polynomial B)) =
      (Polynomial.C : Localization.Away (Polynomial.C s₀ : Polynomial B) →+*
          Polynomial (Localization.Away (Polynomial.C s₀ : Polynomial B))).comp
        (algebraMap (Polynomial B) (Localization.Away (Polynomial.C s₀ : Polynomial B))) :=
  RingHom.ext fun f ↦ by
    rw [RingHom.comp_apply, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2CubeDilate_loc_comp_C

end DilateLoc

end GroupApproximation.BooneHigman.Metabelian.ElemFP
