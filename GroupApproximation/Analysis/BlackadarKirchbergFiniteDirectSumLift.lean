import GroupApproximation.Analysis.BlackadarKirchbergFiniteDimensionalLift
import Mathlib.Algebra.GroupWithZero.Pi
import Mathlib.LinearAlgebra.Pi

/-!
# Completely positive lifting from explicit finite sums of matrix blocks

This is the finite-direct-sum layer of the Blackadar--Kirchberg lifting
argument.  The domain is an actual dependent finite product of full matrix
algebras, not a predicate asserting that an abstract algebra has such a
decomposition.

An exact completely positive lift is obtained block by block and summed.
The common coordinate normalization from
`BlackadarKirchbergFiniteDimensionalLift` then makes the sum contractive while
leaving its corona class unchanged.
-/

namespace GroupApproximation
namespace BlackadarKirchberg

open Matrix Filter
open scoped Matrix.Norms.L2Operator

universe u

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (d : I → ℕ) [∀ i, Nonempty (Fin (d i))]

/-- An explicit finite direct sum of full complex matrix algebras. -/
abbrev DirectMatrixSum := ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ

local instance directMatrixBlockCStarAlgebra (i : I) :
    CStarAlgebra (Matrix (Fin (d i)) (Fin (d i)) ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

local instance directMatrixSumCStarAlgebra :
    CStarAlgebra (DirectMatrixSum d) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-! ## Completely positive finite sums -/

variable {A : Type*} {B : Type*} [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B]

/-- Completely positive maps are closed under addition. -/
theorem CStarExactness.IsCompletelyPositive.add
    {f g : A →ₗ[ℂ] B}
    (hf : CStarExactness.IsCompletelyPositive f)
    (hg : CStarExactness.IsCompletelyPositive g) :
    CStarExactness.IsCompletelyPositive (f + g) := by
  letI : PartialOrder B := CStarAlgebra.spectralOrder _
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing _
  intro n M hM
  obtain ⟨P, hP⟩ := hf n M hM
  obtain ⟨Q, hQ⟩ := hg n M hM
  have hnonneg : 0 ≤ M.map ⇑(f + g) := by
    have hfnonneg : 0 ≤ M.map ⇑f := by
      rw [hP]
      exact star_mul_self_nonneg P
    have hgnonneg : 0 ≤ M.map ⇑g := by
      rw [hQ]
      exact star_mul_self_nonneg Q
    have hadd : M.map ⇑(f + g) = M.map ⇑f + M.map ⇑g := by
      ext i j
      rfl
    rw [hadd]
    exact add_nonneg hfnonneg hgnonneg
  obtain ⟨R, hR⟩ := CStarExactness.exists_star_mul_self_of_nonneg hnonneg
  exact ⟨R, hR⟩

/-- A finite sum of completely positive maps is completely positive. -/
theorem isCompletelyPositive_finsetSum {J : Type*} [Fintype J]
    [DecidableEq J] (f : J → A →ₗ[ℂ] B)
    (hf : ∀ j, CStarExactness.IsCompletelyPositive (f j)) :
    CStarExactness.IsCompletelyPositive (∑ j, f j) := by
  classical
  induction (Finset.univ : Finset J) using Finset.induction_on with
  | empty => simpa using (isCompletelyPositive_zero (A := A) (B := B))
  | @insert j s hj ih =>
      rw [Finset.sum_insert hj]
      exact CStarExactness.IsCompletelyPositive.add (hf j) ih

/-! ## The summand maps -/

/-- The nonunital star-homomorphism that places one matrix block in its
  coordinate of the finite direct sum. -/
def directMatrixSummandInclusion (i : I) :
    Matrix (Fin (d i)) (Fin (d i)) ℂ →⋆ₙₐ[ℂ] DirectMatrixSum d where
  toFun := fun x ↦ Pi.single
    (M := fun j : I ↦ Matrix (Fin (d j)) (Fin (d j)) ℂ) i x
  map_zero' := by
    ext j
    by_cases h : j = i
    · subst j
      simp
    · simp [h]
  map_add' x y := by
    ext j
    by_cases h : j = i
    · subst j
      simp
    · simp [h]
  map_mul' x y := by
    ext j
    by_cases h : j = i
    · subst j
      simp
    · simp [h]
  map_smul' c x := by
    ext j
    by_cases h : j = i
    · subst j
      simp
    · simp [h]
  map_star' x := by
    exact Pi.single_star
      (f := fun j : I ↦ Matrix (Fin (d j)) (Fin (d j)) ℂ) i x

omit [Fintype I] [∀ i, Nonempty (Fin (d i))] in
@[simp] theorem directMatrixSummandInclusion_apply (i : I)
    (x : Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    directMatrixSummandInclusion d i x = Pi.single i x := by
  rfl

omit [∀ i, Nonempty (Fin (d i))] in
/-- A dependent finite product is the sum of its coordinate inclusions. -/
theorem sum_directMatrixSummandInclusion (x : DirectMatrixSum d) :
    (∑ i, directMatrixSummandInclusion d i (x i)) = x := by
  ext j
  simp [directMatrixSummandInclusion_apply]

/-- The linear map obtained by summing a family of component maps. -/
def componentLiftSum {C : Type*} [AddCommMonoid C] [Module ℂ C]
    (L : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ →ₗ[ℂ] C) :
    DirectMatrixSum d →ₗ[ℂ] C :=
  ∑ i, (L i).comp
    ((Pi.evalStarAlgHom ℂ (fun i ↦ Matrix (Fin (d i)) (Fin (d i)) ℂ) i :
      DirectMatrixSum d →⋆ₐ[ℂ] Matrix (Fin (d i)) (Fin (d i)) ℂ) :
        DirectMatrixSum d →ₗ[ℂ] Matrix (Fin (d i)) (Fin (d i)) ℂ)

omit [DecidableEq I] [∀ i, Nonempty (Fin (d i))] in
/-- Evaluation of the sum of the component maps. -/
theorem componentLiftSum_apply {C : Type*} [AddCommMonoid C]
    [Module ℂ C]
    (L : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ →ₗ[ℂ] C)
    (x : DirectMatrixSum d) :
    componentLiftSum d L x = ∑ i, L i (x i) := by
  simp [componentLiftSum]

attribute [simp] componentLiftSum_apply

variable (X : ℕ → Type u) [∀ n, Fintype (X n)]
  [∀ n, DecidableEq (X n)] [∀ n, Nonempty (X n)]

local instance boundedMatrixSequenceCStarAlgebra' :
    CStarAlgebra (BoundedMatrixSequence X) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

omit [∀ i, Nonempty (Fin (d i))] in
/-- The sum of completely positive component maps from an explicit direct sum
is completely positive. -/
theorem isCompletelyPositive_componentLiftSum
    (L : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ →ₗ[ℂ]
      BoundedMatrixSequence X)
    (hL : ∀ i, CStarExactness.IsCompletelyPositive (L i)) :
    CStarExactness.IsCompletelyPositive (componentLiftSum d L) := by
  apply isCompletelyPositive_finsetSum
  intro i
  exact hL i |>.comp <|
    CStarExactness.isCompletelyPositive_of_starAlgHom
      (Pi.evalStarAlgHom ℂ
        (fun i ↦ Matrix (Fin (d i)) (Fin (d i)) ℂ) i).toNonUnitalStarAlgHom

/-! ## Exact CP and CPC lifts -/

/-- A completely positive map from an explicit finite direct sum of matrix
blocks to the matrix corona has an exact completely positive lift. -/
theorem exists_completelyPositive_directMatrixSum_lift
    (f : DirectMatrixSum d →ₗ[ℂ] NormMatrixCStarCorona X)
    (hf : CStarExactness.IsCompletelyPositive f) :
    ∃ lift : DirectMatrixSum d →ₗ[ℂ] BoundedMatrixSequence X,
      CStarExactness.IsCompletelyPositive lift ∧
      ∀ x, normMatrixCStarCoronaQuotient X (lift x) = f x := by
  have hcomponent : ∀ i, ∃ L :
      Matrix (Fin (d i)) (Fin (d i)) ℂ →ₗ[ℂ] BoundedMatrixSequence X,
      CStarExactness.IsCompletelyPositive L ∧
      ∀ x, normMatrixCStarCoronaQuotient X (L x) =
        f (directMatrixSummandInclusion d i x) := by
    intro i
    let fi : Matrix (Fin (d i)) (Fin (d i)) ℂ →ₗ[ℂ]
        NormMatrixCStarCorona X :=
      f.comp (directMatrixSummandInclusion d i :
        Matrix (Fin (d i)) (Fin (d i)) ℂ →ₗ[ℂ] DirectMatrixSum d)
    have hfi : CStarExactness.IsCompletelyPositive fi :=
      hf.comp (CStarExactness.isCompletelyPositive_of_starAlgHom
        (directMatrixSummandInclusion d i))
    obtain ⟨L, hL, hLquot⟩ :=
      exists_completelyPositive_matrix_lift X fi hfi
    refine ⟨L, hL, ?_⟩
    intro x
    change normMatrixCStarCoronaQuotient X (L x) = fi x
    exact hLquot x
  choose L hLCP hLquot using hcomponent
  let lift := componentLiftSum d L
  refine ⟨lift, isCompletelyPositive_componentLiftSum d X L hLCP, ?_⟩
  intro x
  simp only [lift, componentLiftSum_apply]
  rw [map_sum]
  calc
    (∑ i, normMatrixCStarCoronaQuotient X (L i (x i))) =
        ∑ i, f (directMatrixSummandInclusion d i (x i)) := by
      exact Finset.sum_congr rfl fun i _ ↦ hLquot i (x i)
    _ = f (∑ i, directMatrixSummandInclusion d i (x i)) := by
      rw [map_sum]
    _ = f x := by rw [sum_directMatrixSummandInclusion]

/-- A completely positive contraction from an explicit finite direct sum of
matrix blocks to the matrix corona has an exact c.p.c. lift. -/
theorem exists_completelyPositiveContractive_directMatrixSum_lift
    (f : DirectMatrixSum d →ₗ[ℂ] NormMatrixCStarCorona X)
    (hf : CStarExactness.IsCompletelyPositive f)
    (hcontract : ∀ x, ‖f x‖ ≤ ‖x‖) :
    ∃ lift : DirectMatrixSum d →ₗ[ℂ] BoundedMatrixSequence X,
      CStarExactness.IsCompletelyPositive lift ∧
      (∀ x, ‖lift x‖ ≤ ‖x‖) ∧
      ∀ x, normMatrixCStarCoronaQuotient X (lift x) = f x := by
  obtain ⟨lift, hliftCP, hlift⟩ :=
    exists_completelyPositive_directMatrixSum_lift d X f hf
  have hunit : ‖normMatrixCStarCoronaMk X (lift 1)‖ ≤ 1 := by
    have hunitEq : normMatrixCStarCoronaMk X (lift 1) = f 1 := hlift 1
    rw [hunitEq]
    refine (hcontract 1).trans ?_
    rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    exact le_of_eq norm_one
  let normalized := normalizeMatrixLift X lift
  refine ⟨normalized, isCompletelyPositive_normalizeMatrixLift X lift hliftCP,
    normalizeMatrixLift_norm_le X lift hliftCP, ?_⟩
  · intro x
    change normMatrixCStarCoronaMk X (normalizeMatrixLift X lift x) = f x
    rw [normalizeMatrixLift_quotient_eq X lift hunit]
    exact hlift x

end

end BlackadarKirchberg
end GroupApproximation

open GroupApproximation.BlackadarKirchberg

#audit_axioms exists_completelyPositive_directMatrixSum_lift
#audit_axioms exists_completelyPositiveContractive_directMatrixSum_lift
