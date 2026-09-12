import GroupApproximation.Analysis.CStarProductCorona
import GroupApproximation.Analysis.NormMatrixCorona

/-!
# Identifying the generic and matrix reduced products

`CStarProductCorona` constructs the reduced product for an arbitrary family of
C-star algebras.  `NormMatrixCStarCorona` constructs the same object directly
for finite matrix blocks, with the concrete interface used by matrix-corona
exactification.  This file gives the canonical star-algebra equivalence between
the two constructions.  Both maps are induced by the identity map on bounded
matrix sequences; no change of representatives and no analytic estimate is
involved.
-/

namespace GroupApproximation
namespace NormMatrixCoronaGenericBridge

open Filter Matrix PolarLiftingGeneralCStar
open scoped Matrix.Norms.L2Operator

noncomputable section

local instance matrixBlockCStarAlgebra
    (Y : Type) [Fintype Y] [DecidableEq Y] [Nonempty Y] :
    CStarAlgebra (Matrix Y Y ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

variable (X : ℕ → Type) [∀ n, Fintype (X n)]
  [∀ n, DecidableEq (X n)] [∀ n, Nonempty (X n)]

private theorem genericToNorm_kernel
    (a : BoundedCStarSequence (fun n ↦ Matrix (X n) (X n) ℂ))
    (ha : a ∈ nullCStarSequenceIdeal
      (fun n ↦ Matrix (X n) (X n) ℂ) cofinite) :
    normMatrixCStarCoronaQuotient X a = 0 := by
  change normMatrixCStarCoronaMk X a = 0
  rw [normMatrixCStarCoronaMk_eq_zero_iff]
  exact ha

/-- The identity on bounded matrix sequences descends from the generic
reduced product to the concrete norm-matrix corona. -/
def genericToNormRingHom :
    CStarProductCorona (fun n ↦ Matrix (X n) (X n) ℂ) cofinite →+*
      NormMatrixCStarCorona X :=
  Ideal.Quotient.lift
    (nullCStarSequenceIdeal (fun n ↦ Matrix (X n) (X n) ℂ) cofinite)
    (normMatrixCStarCoronaQuotient X).toAlgHom.toRingHom
    (genericToNorm_kernel X)

@[simp] theorem genericToNormRingHom_mk
    (a : BoundedCStarSequence (fun n ↦ Matrix (X n) (X n) ℂ)) :
    genericToNormRingHom X
        (cStarProductCoronaQuotient
          (fun n ↦ Matrix (X n) (X n) ℂ) cofinite a) =
      normMatrixCStarCoronaQuotient X a :=
  Ideal.Quotient.lift_mk _ _ _

/-- The identity descent as a unital complex star-algebra homomorphism. -/
def genericToNorm :
    CStarProductCorona (fun n ↦ Matrix (X n) (X n) ℂ) cofinite →⋆ₐ[ℂ]
      NormMatrixCStarCorona X where
  toFun := genericToNormRingHom X
  map_one' := map_one (genericToNormRingHom X)
  map_mul' := map_mul (genericToNormRingHom X)
  map_zero' := map_zero (genericToNormRingHom X)
  map_add' := map_add (genericToNormRingHom X)
  commutes' z := by
    have h := genericToNormRingHom_mk X
      (algebraMap ℂ
        (BoundedCStarSequence (fun n ↦ Matrix (X n) (X n) ℂ)) z)
    have hgeneric :
        cStarProductCoronaQuotient (fun n ↦ Matrix (X n) (X n) ℂ) cofinite
            (algebraMap ℂ
              (BoundedCStarSequence (fun n ↦ Matrix (X n) (X n) ℂ)) z) =
          algebraMap ℂ
            (CStarProductCorona (fun n ↦ Matrix (X n) (X n) ℂ) cofinite) z :=
      AlgHomClass.commutes
        (cStarProductCoronaQuotient
          (fun n ↦ Matrix (X n) (X n) ℂ) cofinite) z
    have hnorm :
        normMatrixCStarCoronaQuotient X
            (algebraMap ℂ (BoundedMatrixSequence X) z) =
          algebraMap ℂ (NormMatrixCStarCorona X) z :=
      AlgHomClass.commutes (normMatrixCStarCoronaQuotient X) z
    rw [hgeneric, hnorm] at h
    exact h
  map_star' x := by
    obtain ⟨a, rfl⟩ :=
      cStarProductCoronaQuotient_surjective
        (fun n ↦ Matrix (X n) (X n) ℂ) cofinite x
    rw [← map_star
        (cStarProductCoronaQuotient
          (fun n ↦ Matrix (X n) (X n) ℂ) cofinite) a,
      genericToNormRingHom_mk, genericToNormRingHom_mk,
      map_star (normMatrixCStarCoronaQuotient X) a]

private theorem normToGeneric_kernel
    (a : BoundedMatrixSequence X)
    (ha : a ∈ nullMatrixSequenceIdeal X cofinite) :
    cStarProductCoronaQuotient
      (fun n ↦ Matrix (X n) (X n) ℂ) cofinite a = 0 := by
  rw [cStarProductCoronaQuotient_eq_zero_iff]
  exact ha

/-- The inverse identity descent, from the concrete matrix corona to the
generic reduced product. -/
def normToGenericRingHom :
    NormMatrixCStarCorona X →+*
      CStarProductCorona (fun n ↦ Matrix (X n) (X n) ℂ) cofinite := by
  unfold NormMatrixCStarCorona
  exact Ideal.Quotient.lift
    (nullMatrixSequenceIdeal X cofinite)
    (cStarProductCoronaQuotient
      (fun n ↦ Matrix (X n) (X n) ℂ) cofinite).toAlgHom.toRingHom
    (normToGeneric_kernel X)

@[simp] theorem normToGenericRingHom_mk
    (a : BoundedMatrixSequence X) :
    normToGenericRingHom X (normMatrixCStarCoronaQuotient X a) =
      cStarProductCoronaQuotient
        (fun n ↦ Matrix (X n) (X n) ℂ) cofinite a := by
  unfold normMatrixCStarCoronaQuotient normMatrixCStarCoronaMk
  exact Ideal.Quotient.lift_mk _ _ _

/-- The inverse identity descent as a unital complex star-algebra
homomorphism. -/
def normToGeneric :
    NormMatrixCStarCorona X →⋆ₐ[ℂ]
      CStarProductCorona (fun n ↦ Matrix (X n) (X n) ℂ) cofinite where
  toFun := normToGenericRingHom X
  map_one' := map_one (normToGenericRingHom X)
  map_mul' := map_mul (normToGenericRingHom X)
  map_zero' := map_zero (normToGenericRingHom X)
  map_add' := map_add (normToGenericRingHom X)
  commutes' z := by
    have h := normToGenericRingHom_mk X
      (algebraMap ℂ (BoundedMatrixSequence X) z)
    have hnorm :
        normMatrixCStarCoronaQuotient X
            (algebraMap ℂ (BoundedMatrixSequence X) z) =
          algebraMap ℂ (NormMatrixCStarCorona X) z :=
      AlgHomClass.commutes (normMatrixCStarCoronaQuotient X) z
    have hgeneric :
        cStarProductCoronaQuotient (fun n ↦ Matrix (X n) (X n) ℂ) cofinite
            (algebraMap ℂ
              (BoundedCStarSequence (fun n ↦ Matrix (X n) (X n) ℂ)) z) =
          algebraMap ℂ
            (CStarProductCorona (fun n ↦ Matrix (X n) (X n) ℂ) cofinite) z :=
      AlgHomClass.commutes
        (cStarProductCoronaQuotient
          (fun n ↦ Matrix (X n) (X n) ℂ) cofinite) z
    rw [hnorm, hgeneric] at h
    exact h
  map_star' x := by
    obtain ⟨a, rfl⟩ := normMatrixCStarCoronaMk_surjective X x
    change normToGenericRingHom X
        (star (normMatrixCStarCoronaQuotient X a)) =
      star (normToGenericRingHom X (normMatrixCStarCoronaQuotient X a))
    rw [← map_star (normMatrixCStarCoronaQuotient X) a,
      normToGenericRingHom_mk, normToGenericRingHom_mk,
      map_star (cStarProductCoronaQuotient
        (fun n ↦ Matrix (X n) (X n) ℂ) cofinite) a]

theorem normToGeneric_genericToNorm
    (x : CStarProductCorona
      (fun n ↦ Matrix (X n) (X n) ℂ) cofinite) :
    normToGeneric X (genericToNorm X x) = x := by
  obtain ⟨a, rfl⟩ :=
    cStarProductCoronaQuotient_surjective
      (fun n ↦ Matrix (X n) (X n) ℂ) cofinite x
  change normToGenericRingHom X
      (genericToNormRingHom X (cStarProductCoronaQuotient
        (fun n ↦ Matrix (X n) (X n) ℂ) cofinite a)) =
    cStarProductCoronaQuotient
      (fun n ↦ Matrix (X n) (X n) ℂ) cofinite a
  rw [genericToNormRingHom_mk, normToGenericRingHom_mk]

theorem genericToNorm_normToGeneric
    (x : NormMatrixCStarCorona X) :
    genericToNorm X (normToGeneric X x) = x := by
  obtain ⟨a, rfl⟩ := normMatrixCStarCoronaMk_surjective X x
  change genericToNormRingHom X
      (normToGenericRingHom X (normMatrixCStarCoronaQuotient X a)) =
    normMatrixCStarCoronaQuotient X a
  rw [normToGenericRingHom_mk, genericToNormRingHom_mk]

/-- The canonical identification of the two matrix reduced-product
constructions. -/
def coronaEquiv :
    CStarProductCorona (fun n ↦ Matrix (X n) (X n) ℂ) cofinite ≃⋆ₐ[ℂ]
      NormMatrixCStarCorona X :=
  StarAlgEquiv.ofBijective (genericToNorm X)
    ⟨fun x y h ↦ by
        simpa only [normToGeneric_genericToNorm] using congrArg (normToGeneric X) h,
      fun y ↦ ⟨normToGeneric X y, genericToNorm_normToGeneric X y⟩⟩

@[simp] theorem coronaEquiv_mk
    (a : BoundedCStarSequence (fun n ↦ Matrix (X n) (X n) ℂ)) :
    coronaEquiv X (cStarProductCoronaQuotient
      (fun n ↦ Matrix (X n) (X n) ℂ) cofinite a) =
      normMatrixCStarCoronaQuotient X a :=
  genericToNormRingHom_mk X a

end

end NormMatrixCoronaGenericBridge
end GroupApproximation
