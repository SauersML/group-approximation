import GroupApproximation.Analysis.CStarProductCorona
import GroupApproximation.Analysis.MFAlgebraMatrixAmplification
import GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit
import GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationCore

/-!
# Algebraic assembly for tensor synchronization

This module packages the exact coordinate algebra used by the manuscript's
tensor-synchronization argument.  It deliberately stops before the HNN
permanence theorem: no MF permanence for an HNN construction is assumed.

At one finite coordinate, a unitary `u` and a permutation `p` determine the
weighted permutation matrix with its unique nonzero entry in each row equal
to `u`.  This realizes the tensor product of `u` with the permutation
representation, but avoids choosing a Hilbert-space tensor-product model.
The module proves multiplication, adjoint, normalized diagonal trace, and
conjugator covariance exactly.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace TensorSynchronizationAssembly

open HNNCoronaConjugatorSentenceAudit
open scoped ComplexOrder

noncomputable section

universe u v w

/-! ## Normalized diagonal traces -/

/-- The normalized diagonal amplification of an arbitrary tracial state. -/
def matrixTracialState {A : Type u} [CStarAlgebra A]
    (tau : TracialState A) (I : Type v) [Fintype I] [DecidableEq I]
    (hI : Nonempty I) : TracialState (CStarMatrix I I A) := by
  letI := hI
  exact {
    toLinearMap :=
      { toFun := fun M ↦ (Fintype.card I : ℂ)⁻¹ * ∑ i, tau (M i i)
        map_add' := by
          intro M N
          simp only [CStarMatrix.add_apply, map_add, Finset.sum_add_distrib]
          ring
        map_smul' := by
          intro c M
          simp only [CStarMatrix.smul_apply, map_smul, RingHom.id_apply]
          rw [← Finset.smul_sum]
          change (Fintype.card I : ℂ)⁻¹ * (c * ∑ i, tau (M i i)) =
            c * ((Fintype.card I : ℂ)⁻¹ * ∑ i, tau (M i i))
          ac_rfl }
    map_one := by
      simp only [CStarMatrix.one_apply_eq, tau.apply_one, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      field_simp
    map_star_mul_self_nonneg := by
      intro M
      simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply, map_sum]
      apply mul_nonneg
      · exact inv_nonneg.mpr (Nat.cast_nonneg _)
      · exact Finset.sum_nonneg fun i _ ↦
          Finset.sum_nonneg fun j _ ↦
            tau.map_star_mul_self_nonneg (M j i)
    map_mul_comm := by
      intro M N
      simp only [CStarMatrix.mul_apply, map_sum]
      congr 1
      calc
        (∑ i, ∑ j, tau (M i j * N j i)) =
            ∑ i, ∑ j, tau (N j i * M i j) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          exact tau.map_mul_comm _ _
        _ = ∑ j, ∑ i, tau (N j i * M i j) := Finset.sum_comm }

@[simp] theorem matrixTracialState_apply
    {A : Type u} [CStarAlgebra A] (tau : TracialState A)
    (I : Type v) [Fintype I] [DecidableEq I] (hI : Nonempty I)
    (M : CStarMatrix I I A) :
    matrixTracialState tau I hI M =
      (Fintype.card I : ℂ)⁻¹ * ∑ i, tau (M i i) :=
  rfl

/-! ## Weighted permutation matrices -/

/-- The matrix of a permutation whose nonzero coefficient in every row is a
fixed element `a` of the coefficient algebra.  The inverse on `p` makes the
assignment multiplicative rather than antimultiplicative. -/
def weightedPermutationMatrix {A : Type u} [CStarAlgebra A]
    {I : Type v} [Fintype I] (a : A) (p : Equiv.Perm I) :
    CStarMatrix I I A :=
  fun i j ↦ if p⁻¹ i = j then a else 0

@[simp] theorem weightedPermutationMatrix_apply
    {A : Type u} [CStarAlgebra A] {I : Type v} [Fintype I]
    (a : A) (p : Equiv.Perm I) (i j : I) :
    weightedPermutationMatrix a p i j = if p⁻¹ i = j then a else 0 :=
  rfl

theorem weightedPermutationMatrix_mul
    {A : Type u} [CStarAlgebra A] {I : Type v} [Fintype I]
    (a b : A) (p q : Equiv.Perm I) :
    weightedPermutationMatrix a p * weightedPermutationMatrix b q =
      weightedPermutationMatrix (a * b) (p * q) := by
  classical
  ext i k
  rw [CStarMatrix.mul_apply]
  rw [Finset.sum_eq_single (p⁻¹ i)]
  · simp [weightedPermutationMatrix, _root_.mul_inv_rev,
      Equiv.Perm.mul_apply]
  · intro j _ hj
    simp [weightedPermutationMatrix, hj, Ne.symm hj]
  · simp

@[simp] theorem weightedPermutationMatrix_one
    {A : Type u} [CStarAlgebra A] {I : Type v} [Fintype I]
    [DecidableEq I] :
    weightedPermutationMatrix (1 : A) (1 : Equiv.Perm I) = 1 := by
  ext i j
  simp [weightedPermutationMatrix, CStarMatrix.one_apply_eq]

theorem weightedPermutationMatrix_star
    {A : Type u} [CStarAlgebra A] {I : Type v} [Fintype I]
    (a : A) (p : Equiv.Perm I) :
    star (weightedPermutationMatrix a p) =
      weightedPermutationMatrix (star a) p⁻¹ := by
  classical
  ext i j
  by_cases h : p i = j
  · have hinv : p⁻¹ j = i := by simpa [h]
    simp [weightedPermutationMatrix, CStarMatrix.star_apply, h, hinv]
  · have hinv : p⁻¹ j ≠ i := by
      intro hij
      apply h
      simpa using (congrArg p hij).symm
    simp [weightedPermutationMatrix, CStarMatrix.star_apply, h, hinv]

/-- A unitary coefficient and a permutation give a unitary weighted
permutation matrix. -/
def weightedPermutationUnitary
    {A : Type u} [CStarAlgebra A] {I : Type v} [Fintype I]
    [DecidableEq I] (a : unitary A) (p : Equiv.Perm I) :
    unitary (CStarMatrix I I A) :=
  ⟨weightedPermutationMatrix (a : A) p, by
    constructor
    · rw [weightedPermutationMatrix_star, weightedPermutationMatrix_mul,
        a.property.1, inv_mul_cancel, weightedPermutationMatrix_one]
    · rw [weightedPermutationMatrix_star, weightedPermutationMatrix_mul,
        a.property.2, mul_inv_cancel, weightedPermutationMatrix_one]⟩

@[simp] theorem coe_weightedPermutationUnitary
    {A : Type u} [CStarAlgebra A] {I : Type v} [Fintype I]
    [DecidableEq I] (a : unitary A) (p : Equiv.Perm I) :
    (weightedPermutationUnitary a p : CStarMatrix I I A) =
      weightedPermutationMatrix (a : A) p :=
  rfl

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
    simp [Equiv.Perm.mul_apply, mul_assoc]

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
  change lambda s = 1 ↔ lambda s = 1 ∧ eta s = 1
  constructor
  · intro hs
    refine ⟨hs, ?_⟩
    exact MonoidHom.mem_ker.mp (hker (MonoidHom.mem_ker.mpr hs))
  · exact fun hs ↦ hs.1

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
  simp [weightedPermutationMatrix, ha]

theorem matrixTracialState_weighted_eq_zero_of_fixedPointFree
    {A : Type u} [CStarAlgebra A] (tau : TracialState A)
    {I : Type v} [Fintype I] [DecidableEq I] (hI : Nonempty I)
    (a : A) (p : Equiv.Perm I) (hp : ∀ i : I, p⁻¹ i ≠ i) :
    matrixTracialState tau I hI (weightedPermutationMatrix a p) = 0 := by
  rw [matrixTracialState_apply]
  simp [weightedPermutationMatrix, hp]

theorem mulLeft_inv_fixedPointFree
    {E : Type u} [Group E] (e : E) (he : e ≠ 1) :
    ∀ x : E, (Equiv.mulLeft e)⁻¹ x ≠ x := by
  intro x hx
  apply he
  have h := congrArg (Equiv.mulLeft e) hx
  simp only [Equiv.apply_symm_apply, Equiv.coe_mulLeft] at h
  exact mul_right_cancel (by simpa using h.symm)

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
  apply matrixTracialState_weighted_eq_zero_of_fixedPointFree tau hE
  exact mulLeft_inv_fixedPointFree (ell z) hz

/-! ## Passage to the C-star product corona -/

open PolarLiftingGeneralCStar Filter

/-- A coordinatewise unitary family is a bounded C-star sequence. -/
def boundedUnitaryCStarSequence
    (B : ℕ → Type u) [∀ n, CStarAlgebra (B n)] [∀ n, Nontrivial (B n)]
    (U : ∀ n, unitary (B n)) : BoundedCStarSequence B :=
  ⟨fun n ↦ (U n : B n), memℓp_infty ⟨1, by
    rintro _ ⟨n, rfl⟩
    exact le_of_eq (CStarRing.norm_of_mem_unitary (U n).property)⟩⟩

@[simp] theorem boundedUnitaryCStarSequence_apply
    (B : ℕ → Type u) [∀ n, CStarAlgebra (B n)] [∀ n, Nontrivial (B n)]
    (U : ∀ n, unitary (B n)) (n : ℕ) :
    boundedUnitaryCStarSequence B U n = (U n : B n) :=
  rfl

/-- The class of a coordinatewise unitary family in the reduced product. -/
def unitaryCStarSequenceToProductCorona
    (B : ℕ → Type u) [∀ n, CStarAlgebra (B n)] [∀ n, Nontrivial (B n)]
    (U : ∀ n, unitary (B n)) :
    unitary (CStarProductCorona B cofinite) :=
  ⟨cStarProductCoronaQuotient B cofinite
      (boundedUnitaryCStarSequence B U), by
    constructor
    · rw [← map_star, ← map_mul, ← map_one]
      congr 1
      apply lp.ext
      funext n
      exact (U n).property.1
    · rw [← map_star, ← map_mul, ← map_one]
      congr 1
      apply lp.ext
      funext n
      exact (U n).property.2⟩

@[simp] theorem coe_unitaryCStarSequenceToProductCorona
    (B : ℕ → Type u) [∀ n, CStarAlgebra (B n)] [∀ n, Nontrivial (B n)]
    (U : ∀ n, unitary (B n)) :
    (unitaryCStarSequenceToProductCorona B U : CStarProductCorona B cofinite) =
      cStarProductCoronaQuotient B cofinite
        (boundedUnitaryCStarSequence B U) :=
  rfl

/-- Exact coordinate homomorphisms assemble into a homomorphism to the
unitary group of the C-star reduced product. -/
def coordinateProductCoronaHom
    {G : Type w} [Group G]
    (B : ℕ → Type u) [∀ n, CStarAlgebra (B n)] [∀ n, Nontrivial (B n)]
    (V : ∀ n, G →* unitary (B n)) :
    G →* unitary (CStarProductCorona B cofinite) where
  toFun g := unitaryCStarSequenceToProductCorona B (fun n ↦ V n g)
  map_one' := by
    apply Subtype.ext
    change cStarProductCoronaQuotient B cofinite
        (boundedUnitaryCStarSequence B (fun n ↦ V n 1)) = 1
    rw [← map_one (cStarProductCoronaQuotient B cofinite)]
    congr 1
    apply lp.ext
    funext n
    exact congrArg Subtype.val (map_one (V n))
  map_mul' g h := by
    apply Subtype.ext
    change cStarProductCoronaQuotient B cofinite
        (boundedUnitaryCStarSequence B (fun n ↦ V n (g * h))) =
      cStarProductCoronaQuotient B cofinite
          (boundedUnitaryCStarSequence B (fun n ↦ V n g)) *
        cStarProductCoronaQuotient B cofinite
          (boundedUnitaryCStarSequence B (fun n ↦ V n h))
    rw [← map_mul]
    congr 1
    apply lp.ext
    funext n
    exact congrArg Subtype.val (map_mul (V n) g h)

/-- Coordinate covariance descends verbatim to covariance in the C-star
product corona. -/
theorem productCorona_covariance_of_coordinate
    {G : Type w} [Group G] {S : Type v} [Group S]
    (B : ℕ → Type u) [∀ n, CStarAlgebra (B n)] [∀ n, Nontrivial (B n)]
    (V : ∀ n, G →* unitary (B n))
    (source target : S →* G) (W : ∀ n, unitary (B n))
    (hcov : ∀ (n : ℕ) (s : S),
      (W n : B n) * (V n (source s) : B n) * star (W n : B n) =
        (V n (target s) : B n)) :
    let Vbar := coordinateProductCoronaHom B V
    let Wbar := unitaryCStarSequenceToProductCorona B W
    ∀ s : S,
      (Wbar : CStarProductCorona B cofinite) *
          (Vbar (source s) : CStarProductCorona B cofinite) *
            star (Wbar : CStarProductCorona B cofinite) =
        (Vbar (target s) : CStarProductCorona B cofinite) := by
  intro Vbar Wbar s
  change cStarProductCoronaQuotient B cofinite
        (boundedUnitaryCStarSequence B W) *
      cStarProductCoronaQuotient B cofinite
        (boundedUnitaryCStarSequence B (fun n ↦ V n (source s))) *
      star (cStarProductCoronaQuotient B cofinite
        (boundedUnitaryCStarSequence B W)) =
    cStarProductCoronaQuotient B cofinite
      (boundedUnitaryCStarSequence B (fun n ↦ V n (target s)))
  rw [← map_star, ← map_mul, ← map_mul]
  congr 1
  apply lp.ext
  funext n
  exact hcov n s

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
  obtain ⟨P, hP⟩ := exists_leftRegular_conjugator_of_ker_eq
    (ell.comp source) (ell.comp target) hker
  let W : unitary (CStarMatrix E E A) :=
    weightedPermutationUnitary (1 : unitary A) P
  refine ⟨W, ?_⟩
  intro s
  rw [weightedPermutation_conjugation]
  change weightedPermutationMatrix
      ((rho ((source s).1) : unitary A) : A)
      (P * Equiv.mulLeft (ell (source s)) * P⁻¹) =
    weightedPermutationMatrix
      ((rho ((target s).1) : unitary A) : A)
      (Equiv.mulLeft (ell (target s)))
  rw [hP s, hfirst s]

/-! ## MF and separability packages that require no reduced-product axiom -/

/-- Matrix amplification by any nonempty finite index type preserves MF. -/
theorem isMFAlgebra_cstarMatrix_fintype
    {A : Type u} [CStarAlgebra A] [Nontrivial A]
    {I : Type v} [Fintype I] [DecidableEq I] (hI : Nonempty I)
    (hA : IsMFAlgebra A) : IsMFAlgebra (CStarMatrix I I A) := by
  letI : Nonempty (Fin (Fintype.card I)) :=
    ⟨⟨0, Fintype.card_pos_iff.mpr hI⟩⟩
  have hFin := MFAlgebraMatrixAmplification.isMFAlgebra_cstarMatrix
    (Fintype.card I) hA
  exact hFin.of_injective_nonUnitalStarAlgHom
    (CStarMatrix.reindexₐ ℂ A (Fintype.equivFin I)).toNonUnitalStarAlgHom
    (CStarMatrix.reindexₐ ℂ A (Fintype.equivFin I)).injective

/-- The free product representation whose generated C-star algebra contains
both a represented group and one prescribed unitary. -/
def representedGroupWithUnitaryHom
    {G : Type w} [Group G] {A : Type u} [CStarAlgebra A]
    (rho : G →* unitary A) (W : unitary A) :
    Monoid.Coprod G (Multiplicative ℤ) →* unitary A :=
  Monoid.Coprod.lift rho
    { toFun := fun n ↦ W ^ Multiplicative.toAdd n
      map_one' := by simp
      map_mul' := by intro m n; simp [zpow_add] }

/-- A countable represented group together with one unitary generates a
separable MF C-star subalgebra of every MF-embeddable ambient algebra.  This
is the exact generated-subalgebra step; the separate reduced-product
permanence theorem is what supplies `hA` in the manuscript application. -/
theorem representedGroupWithUnitary_generated_isMF
    {G : Type w} [Group G] [Countable G]
    {A : Type u} [CStarAlgebra A]
    (hA : HasMFEmbedding A) (rho : G →* unitary A) (W : unitary A) :
    IsMFAlgebra
      (groupGeneratedCStar (representedGroupWithUnitaryHom rho W)) := by
  letI : Countable (Multiplicative ℤ) :=
    Countable.of_equiv ℤ Multiplicative.ofAdd
  letI : Countable (Monoid.Coprod G (Multiplicative ℤ)) :=
    Monoid.Coprod.mk_surjective.countable
  exact ⟨groupGeneratedCStar_separableSpace
      (representedGroupWithUnitaryHom rho W),
    hA.of_injective_nonUnitalStarAlgHom
      (groupGeneratedCStar (representedGroupWithUnitaryHom rho W)).subtype.toNonUnitalStarAlgHom
      (fun x y hxy ↦ Subtype.ext hxy)⟩

end

end TensorSynchronizationAssembly
end OneSidedMFRadical
end Manuscript
end GroupApproximation
