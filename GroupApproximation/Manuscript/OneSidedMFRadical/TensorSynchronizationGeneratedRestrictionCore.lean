import GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationGeneratedInstanceCore

/-!
# Restrictions to the tensor-synchronized generated algebra
-/

namespace GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationAssembly

open HNNCoronaConjugatorSentenceAudit
open TensorSynchronizationMatrixCore
open PolarLiftingGeneralCStar Filter

noncomputable section

universe u w

noncomputable local instance tensorGeneratedRestrictionPartialOrder
    (A : Type*) [CStarAlgebra A] : PartialOrder A :=
  CStarAlgebra.spectralOrder A

local instance tensorGeneratedRestrictionStarOrderedRing
    (A : Type*) [CStarAlgebra A] : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

/-- A unitary-valued monoid homomorphism, restricted to its synchronized
generated C-star algebra. -/
def synchronizedGeneratedUnitaryHom
    {G : Type w} [MulOneClass G] {D : Type u} [CStarAlgebra D]
    (rho : G →* unitary D) :
    G →* unitary (SynchronizedGeneratedCStar (fun g ↦ rho g)) where
  toFun g := ⟨⟨(rho g : D),
    StarSubalgebra.le_topologicalClosure _
      (StarAlgebra.subset_adjoin ℂ _ ⟨g, rfl⟩)⟩, by
        constructor
        · apply Subtype.ext
          exact (rho g).property.1
        · apply Subtype.ext
          exact (rho g).property.2⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    change (rho 1 : D) = 1
    simp
  map_mul' g h := by
    apply Subtype.ext
    apply Subtype.ext
    change (rho (g * h) : D) = (rho g : D) * (rho h : D)
    simp

/-- The product representation with codomain restricted to the synchronized
generated C-star algebra. -/
def synchronizedGeneratedProductHom
    {G : Type w} [Group G] {D : Type u} [CStarAlgebra D]
    (rho : Monoid.Coprod G (Multiplicative ℤ) →* unitary D) :
    G →* unitary (SynchronizedGeneratedCStar (fun x ↦ rho x)) :=
  (synchronizedGeneratedUnitaryHom rho).comp Monoid.Coprod.inl

/-- The corona conjugator, now regarded as a unitary of the synchronized
generated C-star algebra. -/
def synchronizedGeneratedConjugator
    {G : Type w} [Group G] {D : Type u} [CStarAlgebra D]
    (rho : Monoid.Coprod G (Multiplicative ℤ) →* unitary D) :
    unitary (SynchronizedGeneratedCStar (fun x ↦ rho x)) :=
  synchronizedGeneratedUnitaryHom rho
    (Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ℤ)))

@[simp] theorem coe_synchronizedGeneratedProductHom
    {G : Type w} [Group G] {D : Type u} [CStarAlgebra D]
    (rho : Monoid.Coprod G (Multiplicative ℤ) →* unitary D) (g : G) :
    (((synchronizedGeneratedProductHom rho g :
        unitary (SynchronizedGeneratedCStar (fun x ↦ rho x))) :
      SynchronizedGeneratedCStar (fun x ↦ rho x)) : D) =
      (rho (Monoid.Coprod.inl g) : D) :=
  rfl

@[simp] theorem coe_synchronizedGeneratedConjugator
    {G : Type w} [Group G] {D : Type u} [CStarAlgebra D]
    (rho : Monoid.Coprod G (Multiplicative ℤ) →* unitary D) :
    (((synchronizedGeneratedConjugator rho :
        unitary (SynchronizedGeneratedCStar (fun x ↦ rho x))) :
      SynchronizedGeneratedCStar (fun x ↦ rho x)) : D) =
      (rho (Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ℤ))) : D) :=
  rfl

end

end GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationAssembly
