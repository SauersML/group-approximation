import GroupApproximation.Kazhdan.ExactHodgeCertificate

/-!
# Finite-support verification for exact Hodge certificates

This module collects group-ring identities into a finite coordinate basis.
The basis need not be injective: this is important for presented groups,
where every identification is supplied separately by a checked relator
replay.  All quantitative checks then reduce to finite rational arithmetic.
-/

namespace GroupApproximation
namespace FiniteSupportHodgeCertificate

open ExactHodgeCertificate
open scoped BigOperators MonoidAlgebra

universe u

variable {G : Type u}

/-- Interpret a finite rational coefficient vector in the group ring. -/
noncomputable def coordinateSum {C : Type*} [Fintype C]
    (basis : C → G) (coefficient : C → ℚ) : RatGroupRing G :=
  ∑ c, MonoidAlgebra.single (basis c) (coefficient c)

theorem coordinateSum_add {C : Type*} [Fintype C]
    (basis : C → G) (left right : C → ℚ) :
    coordinateSum basis (fun c ↦ left c + right c) =
      coordinateSum basis left + coordinateSum basis right := by
  simp [coordinateSum, MonoidAlgebra.single_add, Finset.sum_add_distrib]

theorem coordinateSum_sum {C J : Type*} [Fintype C] [Fintype J]
    (basis : C → G) (coefficient : J → C → ℚ) :
    coordinateSum basis (fun c ↦ ∑ j, coefficient j c) =
      ∑ j, coordinateSum basis (coefficient j) := by
  classical
  unfold coordinateSum
  calc
    ∑ c, MonoidAlgebra.single (basis c) (∑ j, coefficient j c) =
        ∑ c, ∑ j, MonoidAlgebra.single (basis c) (coefficient j c) := by
      apply Finset.sum_congr rfl
      intro c _
      change (MonoidAlgebra.singleAddHom (basis c))
          (∑ j, coefficient j c) = _
      rw [map_sum]
      rfl
    _ = ∑ j, ∑ c, MonoidAlgebra.single (basis c) (coefficient j c) := by
      rw [Finset.sum_comm]

/-- Coordinate collection can only decrease coefficient `ℓ1` norm, even
when distinct coordinates represent the same group element. -/
theorem l1_coordinateSum_le {C : Type*} [Fintype C]
    (basis : C → G) (coefficient : C → ℚ) :
    l1 (coordinateSum basis coefficient) ≤ ∑ c, |coefficient c| := by
  classical
  exact (l1_sum_le fun c ↦
    MonoidAlgebra.single (basis c) (coefficient c)).trans_eq (by simp)

/-- Collect all pairs of support coordinates according to a supplied product
class table. -/
def convolution {S C : Type*} [Fintype S] [DecidableEq C]
    (productClass : S → S → C) (left right : S → ℚ) (c : C) : ℚ :=
  ∑ a, ∑ b, if productClass a b = c then left a * right b else 0

/-- Integer numerator version of `convolution`. -/
def integerConvolution {S C : Type*} [Fintype S] [DecidableEq C]
    (productClass : S → S → C) (left right : S → ℤ) (c : C) : ℤ :=
  ∑ a, ∑ b, if productClass a b = c then left a * right b else 0

theorem convolution_int_div
    {S C : Type*} [Fintype S] [DecidableEq C]
    (productClass : S → S → C) (left right : S → ℤ)
    (denominator : ℚ) (c : C) :
    convolution productClass
        (fun a ↦ (left a : ℚ) / denominator)
        (fun b ↦ (right b : ℚ) / denominator) c =
      (integerConvolution productClass left right c : ℚ) /
        (denominator * denominator) := by
  classical
  unfold convolution integerConvolution
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : productClass a b = c
  · simp [h]
    ring
  · simp [h]

/-- Expanding a collected convolution gives the corresponding double sum. -/
theorem coordinateSum_convolution
    {S C : Type*} [Fintype S] [Fintype C] [DecidableEq C]
    (basis : C → G) (productClass : S → S → C)
    (left right : S → ℚ) :
    coordinateSum basis (convolution productClass left right) =
      ∑ a, ∑ b, MonoidAlgebra.single (basis (productClass a b))
        (left a * right b) := by
  classical
  unfold coordinateSum convolution
  calc
    ∑ c, MonoidAlgebra.single (basis c)
        (∑ a, ∑ b, if productClass a b = c then left a * right b else 0) =
        ∑ c, ∑ a, ∑ b, MonoidAlgebra.single (basis c)
          (if productClass a b = c then left a * right b else 0) := by
      apply Finset.sum_congr rfl
      intro c _
      change (MonoidAlgebra.singleAddHom (basis c))
          (∑ a, ∑ b, if productClass a b = c then left a * right b else 0) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [map_sum]
      rfl
    _ = ∑ a, ∑ b, ∑ c, MonoidAlgebra.single (basis c)
          (if productClass a b = c then left a * right b else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ b, MonoidAlgebra.single (basis (productClass a b))
          (left a * right b) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_eq_single (productClass a b)]
      · simp
      · intro c _ hc
        simp [hc.symm]
      · simp

variable [Group G]

/-- Product of two support expansions, when the supplied class table is
verified in the group.  The left expansion is adjointed. -/
theorem adjoint_coordinateSum_mul_coordinateSum
    {S C : Type*} [Fintype S] [Fintype C] [DecidableEq C]
    (support : S → G) (basis : C → G)
    (productClass : S → S → C)
    (hproduct : ∀ a b, (support a)⁻¹ * support b =
      basis (productClass a b))
    (left right : S → ℚ) :
    adjoint (coordinateSum support left) * coordinateSum support right =
      coordinateSum basis (convolution productClass left right) := by
  classical
  rw [coordinateSum_convolution]
  unfold coordinateSum
  rw [adjoint_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [adjoint_single, MonoidAlgebra.single_mul_single, hproduct]

/-- Coefficients of the degree-one Hodge matrix in the collected product
basis. -/
def hodgeCoefficient
    {I J S C : Type*} [Fintype J] [Fintype S] [DecidableEq C]
    (productClass : S → S → C)
    (boundaryCoefficient : J → I → S → ℚ)
    (adjointCoboundaryCoefficient : I → S → ℚ)
    (i k : I) (c : C) : ℚ :=
  (∑ j, convolution productClass
      (boundaryCoefficient j i) (boundaryCoefficient j k) c) +
    convolution productClass
      (adjointCoboundaryCoefficient i) (adjointCoboundaryCoefficient k) c

/-- Coefficients of a finite Gram factor in the collected product basis. -/
def gramCoefficient
    {I K S C : Type*} [Fintype K] [Fintype S] [DecidableEq C]
    (productClass : S → S → C)
    (qCoefficient : K → I → S → ℚ)
    (i k : I) (c : C) : ℚ :=
  ∑ row, convolution productClass
    (qCoefficient row i) (qCoefficient row k) c

/-- Scalar-matrix coefficients at a distinguished identity coordinate. -/
def scalarCoefficient
    {I C : Type*} [DecidableEq I] [DecidableEq C]
    (identityClass : C) (gap : ℚ) (i k : I) (c : C) : ℚ :=
  if i = k ∧ c = identityClass then gap else 0

theorem hodgeMatrix_eq_coordinateSum
    {I J S C : Type*} [Fintype J]
    [Fintype S] [Fintype C] [DecidableEq C]
    (D : I → RatGroupRing G) (B : J → I → RatGroupRing G)
    (support : S → G) (basis : C → G)
    (productClass : S → S → C)
    (hproduct : ∀ a b, (support a)⁻¹ * support b =
      basis (productClass a b))
    (boundaryCoefficient : J → I → S → ℚ)
    (adjointCoboundaryCoefficient : I → S → ℚ)
    (hboundary : ∀ j i, B j i =
      coordinateSum support (boundaryCoefficient j i))
    (hcoboundary : ∀ i, adjoint (D i) =
      coordinateSum support (adjointCoboundaryCoefficient i))
    (i k : I) :
    hodgeMatrix D B i k = coordinateSum basis
      (hodgeCoefficient productClass boundaryCoefficient
        adjointCoboundaryCoefficient i k) := by
  classical
  unfold hodgeMatrix hodgeCoefficient
  have hB :
      (∑ j, adjoint (B j i) * B j k) =
        coordinateSum basis (fun c ↦ ∑ j,
          convolution productClass
            (boundaryCoefficient j i) (boundaryCoefficient j k) c) := by
    rw [coordinateSum_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hboundary, hboundary,
      adjoint_coordinateSum_mul_coordinateSum support basis productClass hproduct]
  have hD : D i * adjoint (D k) =
      coordinateSum basis (convolution productClass
        (adjointCoboundaryCoefficient i)
        (adjointCoboundaryCoefficient k)) := by
    rw [← adjoint_adjoint (D i), hcoboundary, hcoboundary,
      adjoint_coordinateSum_mul_coordinateSum support basis productClass hproduct]
  rw [hB, hD, ← coordinateSum_add]

theorem gramMatrix_eq_coordinateSum
    {I K S C : Type*} [Fintype K]
    [Fintype S] [Fintype C] [DecidableEq C]
    (q : K → I → RatGroupRing G)
    (support : S → G) (basis : C → G)
    (productClass : S → S → C)
    (hproduct : ∀ a b, (support a)⁻¹ * support b =
      basis (productClass a b))
    (qCoefficient : K → I → S → ℚ)
    (hq : ∀ row i, q row i = coordinateSum support (qCoefficient row i))
    (i k : I) :
    (∑ row, adjoint (q row i) * q row k) = coordinateSum basis
      (gramCoefficient productClass qCoefficient i k) := by
  classical
  unfold gramCoefficient
  rw [coordinateSum_sum]
  apply Finset.sum_congr rfl
  intro row _
  rw [hq, hq,
    adjoint_coordinateSum_mul_coordinateSum support basis productClass hproduct]

theorem scalarMatrix_eq_coordinateSum
    {I C : Type*} [Fintype C] [DecidableEq I] [DecidableEq C]
    (basis : C → G) (identityClass : C) (hone : basis identityClass = 1)
    (gap : ℚ) (i k : I) :
    scalarMatrix gap i k = coordinateSum basis
      (scalarCoefficient identityClass gap i k) := by
  classical
  by_cases hik : i = k
  · subst k
    simp only [scalarMatrix, if_pos]
    unfold coordinateSum
    rw [Finset.sum_eq_single identityClass]
    · simp [hone, scalarCoefficient]
    · intro c _ hc
      simp [scalarCoefficient, hc]
    · simp
  · simp [scalarMatrix, scalarCoefficient, hik, coordinateSum]

/-- Assemble an ordinary exact Hodge certificate from finite support
coordinates and a pointwise rational residual identity. -/
theorem certificate_of_finite_support
    {I J K S C : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype K]
    [Fintype S] [Fintype C] [DecidableEq C]
    (D : I → RatGroupRing G) (B : J → I → RatGroupRing G)
    (q : K → I → RatGroupRing G)
    (support : S → G) (basis : C → G)
    (productClass : S → S → C)
    (hproduct : ∀ a b, (support a)⁻¹ * support b =
      basis (productClass a b))
    (identityClass : C) (hone : basis identityClass = 1)
    (boundaryCoefficient : J → I → S → ℚ)
    (adjointCoboundaryCoefficient : I → S → ℚ)
    (qCoefficient : K → I → S → ℚ)
    (residualCoefficient : I → I → C → ℚ)
    (gap residualBound : ℚ)
    (hgap : residualBound < gap)
    (hchain : ∀ j, ∑ i, B j i * D i = 0)
    (hboundary : ∀ j i, B j i =
      coordinateSum support (boundaryCoefficient j i))
    (hcoboundary : ∀ i, adjoint (D i) =
      coordinateSum support (adjointCoboundaryCoefficient i))
    (hq : ∀ row i, q row i = coordinateSum support (qCoefficient row i))
    (hcoefficient : ∀ i k c,
      hodgeCoefficient productClass boundaryCoefficient
          adjointCoboundaryCoefficient i k c =
        scalarCoefficient identityClass gap i k c +
          gramCoefficient productClass qCoefficient i k c +
          residualCoefficient i k c)
    (hrow : ∀ i, ∑ k, ∑ c, |residualCoefficient i k c| ≤ residualBound)
    (hcolumn : ∀ k, ∑ i, ∑ c, |residualCoefficient i k c| ≤ residualBound) :
    Certificate D B q
      (fun i k ↦ coordinateSum basis (residualCoefficient i k))
      gap residualBound := by
  classical
  refine ⟨hgap, hchain, ?_, ?_, ?_⟩
  · intro i k
    rw [hodgeMatrix_eq_coordinateSum D B support basis productClass hproduct
        boundaryCoefficient adjointCoboundaryCoefficient hboundary hcoboundary,
      gramMatrix_eq_coordinateSum q support basis productClass hproduct
        qCoefficient hq,
      scalarMatrix_eq_coordinateSum basis identityClass hone,
      ← coordinateSum_add, ← coordinateSum_add]
    exact congrArg (coordinateSum basis) (funext fun c ↦ hcoefficient i k c)
  · intro i
    exact (Finset.sum_le_sum fun k _ ↦
      l1_coordinateSum_le basis (residualCoefficient i k)).trans (hrow i)
  · intro k
    exact (Finset.sum_le_sum fun i _ ↦
      l1_coordinateSum_le basis (residualCoefficient i k)).trans (hcolumn k)

end FiniteSupportHodgeCertificate
end GroupApproximation
