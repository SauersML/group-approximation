import GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit
import GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationCore
import GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationGroupData
import GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationMatrixCore

/-!
# Finite-coordinate core for tensor synchronization

This module isolates the exact finite-coordinate representation, trace, and
covariance calculations used by tensor synchronization.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace TensorSynchronizationAssembly

open HNNCoronaConjugatorSentenceAudit
open TensorSynchronizationMatrixCore
open TensorSynchronizationGroupData
open Filter
open scoped ComplexOrder

noncomputable section

universe u v w

/-- A regular realization cannot live in the zero C-star algebra: its
tracial state sends zero to zero and the unit to one. -/
theorem regularRealization_nontrivial
    {G : Type u} [Group G] {A : Type v} [CStarAlgebra A]
    (R : RegularRealizationData G A) : Nontrivial A := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have htau : (0 : ℂ) = 1 := by
    simpa using congrArg R.tau.toLinearMap h
  exact zero_ne_one htau

/-- Tensor a unitary representation with a finite permutation
representation, coordinate by coordinate. -/
def tensorPermutationHom
    {G : Type w} [Group G] {A : Type u} [CStarAlgebra A]
    {I : Type v} [Fintype I] [DecidableEq I]
    (rho : G →* unitary A) (sigma : G →* Equiv.Perm I) :
    G →* unitary (CStarMatrix I I A) where
  toFun g := weightedPermutationUnitary (rho g) (sigma g)
  map_one' := by
    apply Subtype.ext
    simp [weightedPermutationUnitary]
  map_mul' g h := by
    apply Subtype.ext
    change weightedPermutationMatrix ((rho (g * h) : unitary A) : A) (sigma (g * h)) =
      weightedPermutationMatrix ((rho g : unitary A) : A) (sigma g) *
        weightedPermutationMatrix ((rho h : unitary A) : A) (sigma h)
    rw [map_mul, map_mul, weightedPermutationMatrix_mul]
    rfl

/-- The left-regular permutation representation of a group. -/
def leftRegularPermutationHom (E : Type v) [Group E] :
    E →* Equiv.Perm E where
  toFun := Equiv.mulLeft
  map_one' := by ext x; simp
  map_mul' g h := by
    ext x
    simp [Equiv.Perm.mul_apply]

/-- The coordinate representation used in tensor synchronization. -/
def finiteProductTensorHom
    {Gamma : Type w} [Group Gamma] {Q : Type u} [Group Q]
    {A : Type v} [CStarAlgebra A] {E : Type u} [Group E]
    [Fintype E] [DecidableEq E]
    (rho : Gamma →* unitary A) (ell : Gamma × Q →* E) :
    Gamma × Q →* unitary (CStarMatrix E E A) :=
  tensorPermutationHom (rho.comp (MonoidHom.fst Gamma Q))
    ((leftRegularPermutationHom E).comp ell)

/-- The manuscript's one-sided kernel hypothesis gives equality of the two
product-image kernels: adding a second coordinate cannot enlarge the kernel,
and it does not shrink it when that coordinate already dies on the first
kernel. -/
theorem ker_prod_one_eq_prod_of_ker_le
    {S : Type w} [Group S] {G : Type v} [Group G]
    {Q : Type u} [Group Q] (lambda : S →* G) (eta : S →* Q)
    (hker : lambda.ker ≤ eta.ker) :
    (lambda.prod (1 : S →* Q)).ker = (lambda.prod eta).ker := by
  ext s
  constructor
  · intro hs
    have hpair := MonoidHom.mem_ker.mp hs
    have hlambda : lambda s = 1 := by
      simpa using congrArg Prod.fst hpair
    have heta : eta s = 1 :=
      MonoidHom.mem_ker.mp (hker (MonoidHom.mem_ker.mpr hlambda))
    apply MonoidHom.mem_ker.mpr
    apply Prod.ext
    · exact hlambda
    · exact heta
  · intro hs
    have hpair := MonoidHom.mem_ker.mp hs
    have hlambda : lambda s = 1 := by
      simpa using congrArg Prod.fst hpair
    apply MonoidHom.mem_ker.mpr
    apply Prod.ext
    · exact hlambda
    · simp

/-! ## The manuscript's finite-product data -/

/-- Combine the two finite quotient maps into the homomorphism on the direct
product used by tensor synchronization.  Using the whole finite product,
rather than its image subgroup, gives the same kernel and avoids an
inessential choice of a finite model. -/
def productFiniteQuotientHom
    {Gamma : Type*} [Group Gamma] {Q : Type*} [Group Q]
    {G : Type*} [Group G] {B : Type*} [Group B]
    (lambda : Gamma →* G) (beta : Q →* B) : Gamma × Q →* G × B :=
  (lambda.comp (MonoidHom.fst Gamma Q)).prod
    (beta.comp (MonoidHom.snd Gamma Q))

@[simp] theorem productFiniteQuotientHom_apply
    {Gamma : Type*} [Group Gamma] {Q : Type*} [Group Q]
    {G : Type*} [Group G] {B : Type*} [Group B]
    (lambda : Gamma →* G) (beta : Q →* B) (z : Gamma × Q) :
    productFiniteQuotientHom lambda beta z =
      (lambda z.1, beta z.2) :=
  rfl

/-- The subgroup map `s ↦ (s,1)` appearing on the left of the covariance
relation. -/
def tensorSynchronizationSource
    {S : Type u} [Group S] {Gamma : Type v} [Group Gamma]
    {Q : Type w} [Group Q] (iota : S →* Gamma) : S →* Gamma × Q :=
  iota.prod (1 : S →* Q)

/-- The subgroup map `s ↦ (s,tau(s))` appearing on the right of the
covariance relation. -/
def tensorSynchronizationTarget
    {S : Type u} [Group S] {Gamma : Type v} [Group Gamma]
    {Q : Type w} [Group Q] (iota : S →* Gamma) (tau : S →* Q) :
    S →* Gamma × Q :=
  iota.prod tau

@[simp] theorem tensorSynchronizationSource_apply
    {S : Type u} [Group S] {Gamma : Type v} [Group Gamma]
    {Q : Type w} [Group Q] (iota : S →* Gamma) (s : S) :
    tensorSynchronizationSource (Q := Q) iota s = (iota s, 1) :=
  rfl

@[simp] theorem tensorSynchronizationTarget_apply
    {S : Type u} [Group S] {Gamma : Type v} [Group Gamma]
    {Q : Type w} [Group Q] (iota : S →* Gamma) (tau : S →* Q) (s : S) :
    tensorSynchronizationTarget iota tau s = (iota s, tau s) :=
  rfl

/-- The manuscript's one-sided kernel hypothesis gives exactly the equal
kernels needed by the finite left-regular synchronization theorem. -/
theorem productFiniteQuotient_source_target_ker_eq
    {S : Type*} [Group S] {Gamma : Type*} [Group Gamma]
    {Q : Type*} [Group Q] {G : Type*} [Group G]
    {B : Type*} [Group B]
    (iota : S →* Gamma) (tau : S →* Q)
    (lambda : Gamma →* G) (beta : Q →* B)
    (hker : (lambda.comp iota).ker ≤ (beta.comp tau).ker) :
    ((productFiniteQuotientHom lambda beta).comp
        (tensorSynchronizationSource (Q := Q) iota)).ker =
      ((productFiniteQuotientHom lambda beta).comp
        (tensorSynchronizationTarget iota tau)).ker := by
  ext s
  constructor
  · intro hs
    have hpair := MonoidHom.mem_ker.mp hs
    have hlambda : lambda (iota s) = 1 := by
      simpa [productFiniteQuotientHom, tensorSynchronizationSource] using
        congrArg Prod.fst hpair
    have hbeta : beta (tau s) = 1 :=
      MonoidHom.mem_ker.mp
        (hker (MonoidHom.mem_ker.mpr hlambda))
    apply MonoidHom.mem_ker.mpr
    apply Prod.ext
    · simpa [productFiniteQuotientHom, tensorSynchronizationTarget]
        using hlambda
    · simpa [productFiniteQuotientHom, tensorSynchronizationTarget]
        using hbeta
  · intro hs
    have hpair := MonoidHom.mem_ker.mp hs
    have hlambda : lambda (iota s) = 1 := by
      simpa [productFiniteQuotientHom, tensorSynchronizationTarget] using
        congrArg Prod.fst hpair
    apply MonoidHom.mem_ker.mpr
    apply Prod.ext
    · simpa [productFiniteQuotientHom, tensorSynchronizationSource]
        using hlambda
    · simp [productFiniteQuotientHom, tensorSynchronizationSource]

/-- Eventual detection in the `Q`-quotients implies eventual detection of
every product element whose first coordinate is trivial and whose second
coordinate is nontrivial. -/
theorem productFiniteQuotient_eventually_detects_second
    {Gamma : Type w} [Group Gamma] {Q : Type v} [Group Q]
    {G : ℕ → Type u} [∀ n, Group (G n)]
    {B : ℕ → Type u} [∀ n, Group (B n)]
    (lambda : ∀ n, Gamma →* G n) (beta : ∀ n, Q →* B n)
    (hdetect : ∀ q : Q, q ≠ 1 → ∀ᶠ n in cofinite, beta n q ≠ 1)
    (z : Gamma × Q) (_hfirst : z.1 = 1) (hsecond : z.2 ≠ 1) :
    ∀ᶠ n in cofinite, productFiniteQuotientHom (lambda n) (beta n) z ≠ 1 := by
  filter_upwards [hdetect z.2 hsecond] with n hn
  intro hz
  apply hn
  have := congrArg Prod.snd hz
  simpa using this

/-! ## Exact normalized-trace formulas -/

@[simp] theorem matrixTracialState_weighted_one
    {A : Type u} [CStarAlgebra A] (tau : TracialState A)
    {I : Type v} [Fintype I] [DecidableEq I] (hI : Nonempty I)
    (a : A) :
    matrixTracialState tau I hI
        (weightedPermutationMatrix a (1 : Equiv.Perm I)) = tau a := by
  letI := hI
  rw [matrixTracialState_apply]
  simp only [weightedPermutationMatrix, inv_one, Equiv.Perm.one_apply,
    if_pos, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card I : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp [hcard]

theorem matrixTracialState_weighted_eq_zero_of_coefficient
    {A : Type u} [CStarAlgebra A] (tau : TracialState A)
    {I : Type v} [Fintype I] [DecidableEq I] (hI : Nonempty I)
    {a : A} (ha : tau a = 0) (p : Equiv.Perm I) :
    matrixTracialState tau I hI (weightedPermutationMatrix a p) = 0 := by
  rw [matrixTracialState_apply]
  have hsum : ∑ i, tau (weightedPermutationMatrix a p i i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : p⁻¹ i = i
    · rw [weightedPermutationMatrix_apply, if_pos hi, ha]
    · rw [weightedPermutationMatrix_apply, if_neg hi, tau.map_zero]
  rw [hsum, mul_zero]

theorem matrixTracialState_weighted_eq_zero_of_fixedPointFree
    {A : Type u} [CStarAlgebra A] (tau : TracialState A)
    {I : Type v} [Fintype I] [DecidableEq I] (hI : Nonempty I)
    (a : A) (p : Equiv.Perm I) (hp : ∀ i : I, p⁻¹ i ≠ i) :
    matrixTracialState tau I hI (weightedPermutationMatrix a p) = 0 := by
  rw [matrixTracialState_apply]
  have hsum : ∑ i, tau (weightedPermutationMatrix a p i i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [weightedPermutationMatrix_apply, if_neg (hp i), tau.map_zero]
  rw [hsum, mul_zero]

theorem mulLeft_inv_fixedPointFree
    {E : Type u} [Group E] (e : E) (he : e ≠ 1) :
    ∀ x : E, (Equiv.mulLeft e)⁻¹ x ≠ x := by
  intro x hx
  apply he
  change e⁻¹ * x = x at hx
  have hinv : e⁻¹ = 1 := by
    simpa [mul_assoc] using congrArg (fun y : E ↦ y * x⁻¹) hx
  simpa using congrArg Inv.inv hinv

/-- If the first group coordinate is nontrivial, the original regular trace
already forces the tensor-coordinate trace to vanish. -/
theorem finiteProductTensorHom_trace_zero_of_first_ne_one
    {Gamma : Type w} [Group Gamma] {Q : Type u} [Group Q]
    {A : Type v} [CStarAlgebra A] {E : Type u} [Group E]
    [Fintype E] [DecidableEq E] (hE : Nonempty E)
    (R : RegularRealizationData Gamma A) (ell : Gamma × Q →* E)
    (z : Gamma × Q) (hz : z.1 ≠ 1) :
    matrixTracialState R.tau E hE
        (finiteProductTensorHom R.rho ell z : CStarMatrix E E A) = 0 := by
  change matrixTracialState R.tau E hE
    (weightedPermutationMatrix (R.rho z.1 : A) (Equiv.mulLeft (ell z))) = 0
  apply matrixTracialState_weighted_eq_zero_of_coefficient R.tau hE
  exact R.regular z.1 hz

/-- If the finite quotient coordinate is nontrivial, the left-regular
permutation has no fixed point and forces the tensor-coordinate trace to
vanish. -/
theorem finiteProductTensorHom_trace_zero_of_finite_ne_one
    {Gamma : Type w} [Group Gamma] {Q : Type u} [Group Q]
    {A : Type v} [CStarAlgebra A] {E : Type u} [Group E]
    [Fintype E] [DecidableEq E] (hE : Nonempty E)
    (rho : Gamma →* unitary A) (tau : TracialState A)
    (ell : Gamma × Q →* E) (z : Gamma × Q) (hz : ell z ≠ 1) :
    matrixTracialState tau E hE
        (finiteProductTensorHom rho ell z : CStarMatrix E E A) = 0 := by
  change matrixTracialState tau E hE
    (weightedPermutationMatrix (rho z.1 : A) (Equiv.mulLeft (ell z))) = 0
  apply matrixTracialState_weighted_eq_zero_of_fixedPointFree tau hE
  exact mulLeft_inv_fixedPointFree (ell z) hz

/-! ## Exact finite-coordinate covariance -/

/-- A permutation conjugator becomes a unitary weighted-permutation
conjugator, and it commutes with the coefficient in the required tensor
fashion. -/
theorem weightedPermutation_conjugation
    {A : Type u} [CStarAlgebra A] {I : Type v} [Fintype I]
    [DecidableEq I] (a : unitary A) (W p : Equiv.Perm I) :
    (weightedPermutationUnitary (1 : unitary A) W : CStarMatrix I I A) *
        (weightedPermutationUnitary a p : CStarMatrix I I A) *
          star (weightedPermutationUnitary (1 : unitary A) W :
            CStarMatrix I I A) =
      weightedPermutationUnitary a (W * p * W⁻¹) := by
  rw [coe_weightedPermutationUnitary, coe_weightedPermutationUnitary,
    coe_weightedPermutationUnitary, weightedPermutationMatrix_star,
    weightedPermutationMatrix_mul, weightedPermutationMatrix_mul]
  simp

/-- Coordinate covariance for two subgroup maps with the same first
component and equal kernels after the finite quotient map. -/
theorem exists_finiteProductTensor_conjugator
    {S : Type w} [Group S] {Gamma : Type v} [Group Gamma]
    {Q : Type u} [Group Q] {A : Type v} [CStarAlgebra A]
    {E : Type u} [Group E] [Fintype E] [DecidableEq E]
    (rho : Gamma →* unitary A) (ell : Gamma × Q →* E)
    (source target : S →* Gamma × Q)
    (hfirst : ∀ s : S, (source s).1 = (target s).1)
    (hker : (ell.comp source).ker = (ell.comp target).ker) :
    ∃ W : unitary (CStarMatrix E E A), ∀ s : S,
      (W : CStarMatrix E E A) *
          (finiteProductTensorHom rho ell (source s) : CStarMatrix E E A) *
            star (W : CStarMatrix E E A) =
        (finiteProductTensorHom rho ell (target s) : CStarMatrix E E A) := by
  obtain ⟨P, hP⟩ :=
    TensorSynchronizationCore.exists_leftRegular_conjugator_of_ker_eq
    (ell.comp source) (ell.comp target) hker
  let W : unitary (CStarMatrix E E A) :=
    weightedPermutationUnitary (1 : unitary A) P
  refine ⟨W, ?_⟩
  intro s
  change
    (weightedPermutationUnitary (1 : unitary A) P : CStarMatrix E E A) *
        (weightedPermutationUnitary (rho (source s).1)
          (Equiv.mulLeft (ell (source s))) : CStarMatrix E E A) *
      star (weightedPermutationUnitary (1 : unitary A) P :
        CStarMatrix E E A) =
    (weightedPermutationUnitary (rho (target s).1)
      (Equiv.mulLeft (ell (target s))) : CStarMatrix E E A)
  rw [weightedPermutation_conjugation]
  change weightedPermutationMatrix
      ((rho ((source s).1) : unitary A) : A)
      (P * Equiv.mulLeft (ell (source s)) * P⁻¹) =
    weightedPermutationMatrix
      ((rho ((target s).1) : unitary A) : A)
      (Equiv.mulLeft (ell (target s)))
  have hPs :
      P * Equiv.mulLeft (ell (source s)) * P⁻¹ =
        Equiv.mulLeft (ell (target s)) := by
    simpa only [MonoidHom.comp_apply] using hP s
  rw [hPs, hfirst s]

end

end TensorSynchronizationAssembly
end OneSidedMFRadical
end Manuscript
end GroupApproximation
