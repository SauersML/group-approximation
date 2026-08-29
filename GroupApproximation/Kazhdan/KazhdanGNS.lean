import GroupApproximation.Kazhdan.KazhdanFiniteModel
import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
# GNS representation of a positive-definite group function

This module uses mathlib's Moore--Aronszajn construction to turn the
positive-definite limiting correlation into a genuine complete real Hilbert
space and an orthogonal group representation.
-/

namespace GroupApproximation
namespace KazhdanGNS

open KazhdanFiniteModel
open scoped InnerProductSpace

universe u

variable {G : Type u} [Group G]

/-- The scalar-valued translation-invariant kernel associated to a real
function on a group. -/
noncomputable def scalarKernel (f : G → ℝ) :
    Matrix G G (ℝ →L[ℝ] ℝ) :=
  Matrix.of fun x y ↦
    ContinuousLinearMap.lsmul ℝ ℝ (f (y⁻¹ * x))

/-- Symmetry of a positive-definite function makes its scalar kernel
Hermitian. -/
theorem scalarKernel_isHermitian {f : G → ℝ} (hf : IsPositiveDefinite f) :
    (scalarKernel f).IsHermitian := by
  ext x y
  change star (ContinuousLinearMap.lsmul ℝ ℝ (f (x⁻¹ * y))) 1 =
    f (y⁻¹ * x) * 1
  rw [hf.1 y x, mul_one]
  rw [ContinuousLinearMap.star_eq_adjoint]
  refine ext_inner_right ℝ fun r ↦ ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp [mul_comm]

/-- The scalar kernel of a positive-definite group function is positive
semidefinite in mathlib's operator-valued kernel sense. -/
theorem scalarKernel_posSemidef {f : G → ℝ} (hf : IsPositiveDefinite f) :
    (scalarKernel f).PosSemidef := by
  apply (RKHS.posSemidef_tfae.out 2 0).mp
  refine ⟨scalarKernel_isHermitian hf, ?_⟩
  intro v
  have hquad := hf.2 v.support v
  simpa [scalarKernel, Finsupp.sum, mul_assoc, mul_comm, mul_left_comm] using hquad

/-- A real positive-definite function, bundled only so that its proved
positivity can supply mathlib's kernel instance. -/
structure PositiveDefiniteFunction (G : Type u) [Group G] where
  toFun : G → ℝ
  isPositiveDefinite : IsPositiveDefinite toFun

instance : CoeFun (PositiveDefiniteFunction G) (fun _ ↦ G → ℝ) :=
  ⟨PositiveDefiniteFunction.toFun⟩

noncomputable instance scalarKernelFact (p : PositiveDefiniteFunction G) :
    Fact (scalarKernel p.toFun).PosSemidef :=
  ⟨scalarKernel_posSemidef p.isPositiveDefinite⟩

/-- The complete real Hilbert space produced by the Moore--Aronszajn
construction from a positive-definite group function. -/
abbrev HilbertSpace (p : PositiveDefiniteFunction G) :=
  RKHS.OfKernel (scalarKernel p.toFun)

/-- The finitely supported pre-Hilbert space whose completion is the GNS
Hilbert space. -/
abbrev PreHilbertSpace (p : PositiveDefiniteFunction G) :=
  RKHS.H₀ (scalarKernel p.toFun)

@[reducible] noncomputable def preHilbertSeminormed
    (p : PositiveDefiniteFunction G) :
    SeminormedAddCommGroup (PreHilbertSpace p) :=
  RKHS.instSeminormedAddCommGroupH₀ (K := scalarKernel p.toFun)

@[reducible] noncomputable def preHilbertInnerProduct
    (p : PositiveDefiniteFunction G) :
    InnerProductSpace ℝ (PreHilbertSpace p) :=
  RKHS.instInnerProductSpaceH₀ (K := scalarKernel p.toFun)

/-- The kernel vector indexed by a group element, explicitly realized as a
free generator in the Hilbert completion. -/
noncomputable def kernelVector (p : PositiveDefiniteFunction G) (g : G) :
    HilbertSpace p := by
  letI : SeminormedAddCommGroup (PreHilbertSpace p) :=
    preHilbertSeminormed p
  letI : InnerProductSpace ℝ (PreHilbertSpace p) :=
    preHilbertInnerProduct p
  exact UniformSpace.Completion.coe'
    (Finsupp.single (g, (1 : ℝ)) 1 : PreHilbertSpace p)

/-- Left translation on the group coordinate of the free kernel-vector
indexing type. -/
def leftIndexEquiv (s : G) : G × ℝ ≃ G × ℝ where
  toFun x := (s * x.1, x.2)
  invFun x := (s⁻¹ * x.1, x.2)
  left_inv x := by simp
  right_inv x := by simp

/-- Left multiplication as an equivalence of the group index itself. -/
def leftGroupEquiv (s : G) : G ≃ G where
  toFun g := s * g
  invFun g := s⁻¹ * g
  left_inv g := by simp
  right_inv g := by simp

/-- Left translation on finitely supported kernel generators. -/
noncomputable def preTranslationLinearEquiv (p : PositiveDefiniteFunction G) (s : G) :
    PreHilbertSpace p ≃ₗ[ℝ] PreHilbertSpace p :=
  Finsupp.domLCongr (leftIndexEquiv s)

@[simp] theorem preTranslationLinearEquiv_single
    (p : PositiveDefiniteFunction G) (s : G) (i : G × ℝ) (c : ℝ) :
    preTranslationLinearEquiv p s (Finsupp.single i c) =
      Finsupp.single (leftIndexEquiv s i) c := by
  simp [preTranslationLinearEquiv]

/-- Explicit inner product of two free kernel generators. -/
theorem inner_single (p : PositiveDefiniteFunction G)
    (i j : G × ℝ) (c d : ℝ) :
    letI : SeminormedAddCommGroup (PreHilbertSpace p) :=
      preHilbertSeminormed p
    letI : InnerProductSpace ℝ (PreHilbertSpace p) :=
      preHilbertInnerProduct p
    inner ℝ (Finsupp.single i c : PreHilbertSpace p)
        (Finsupp.single j d : PreHilbertSpace p) =
      c * d * (p (i.1⁻¹ * j.1) * i.2 * j.2) := by
  change (Finsupp.single i c).sum (fun yu z ↦
    (Finsupp.single j d).sum (fun xv w ↦
      star z * w * inner ℝ (scalarKernel p.toFun xv.1 yu.1 yu.2) xv.2)) = _
  simp [scalarKernel, mul_assoc, mul_comm, mul_left_comm]

/-- Inner products of kernel vectors recover the original group
coefficient. -/
theorem inner_kernelVector (p : PositiveDefiniteFunction G) (g h : G) :
    inner ℝ (kernelVector p g) (kernelVector p h) = p (g⁻¹ * h) := by
  letI : SeminormedAddCommGroup (PreHilbertSpace p) :=
    preHilbertSeminormed p
  letI : InnerProductSpace ℝ (PreHilbertSpace p) :=
    preHilbertInnerProduct p
  change inner ℝ
    (UniformSpace.Completion.coe'
      (Finsupp.single (g, (1 : ℝ)) 1 : PreHilbertSpace p))
    (UniformSpace.Completion.coe'
      (Finsupp.single (h, (1 : ℝ)) 1 : PreHilbertSpace p)) = _
  rw [UniformSpace.Completion.inner_coe, inner_single]
  simp

/-- Left translation preserves the pre-Hilbert inner product. -/
theorem inner_preTranslationLinearEquiv (p : PositiveDefiniteFunction G)
    (s : G) (f g : PreHilbertSpace p) :
    letI : SeminormedAddCommGroup (PreHilbertSpace p) :=
      preHilbertSeminormed p
    letI : InnerProductSpace ℝ (PreHilbertSpace p) :=
      preHilbertInnerProduct p
    inner ℝ (preTranslationLinearEquiv p s f)
        (preTranslationLinearEquiv p s g) = inner ℝ f g := by
  letI : SeminormedAddCommGroup (PreHilbertSpace p) :=
    preHilbertSeminormed p
  letI : InnerProductSpace ℝ (PreHilbertSpace p) :=
    preHilbertInnerProduct p
  let L := preTranslationLinearEquiv p s
  have hsingle (i : G × ℝ) (c : ℝ) (g : PreHilbertSpace p) :
      inner ℝ (L (Finsupp.single i c)) (L g) =
        inner ℝ (Finsupp.single i c) g := by
    induction g using Finsupp.induction with
    | zero => simp
    | single_add j d g _ _ ih =>
        rw [map_add, inner_add_right, inner_add_right, ih]
        congr 1
        rw [show L (Finsupp.single i c) =
            Finsupp.single (leftIndexEquiv s i) c by
              simp [L, preTranslationLinearEquiv],
          show L (Finsupp.single j d) =
            Finsupp.single (leftIndexEquiv s j) d by
              simp [L, preTranslationLinearEquiv],
          inner_single, inner_single]
        simp [leftIndexEquiv]
  induction f using Finsupp.induction with
  | zero => simp
  | single_add i c f _ _ ih =>
      rw [map_add, inner_add_left, inner_add_left, ih, hsingle]

/-- Left translation as a linear isometric equivalence of the pre-Hilbert
space. -/
noncomputable def preTranslationLinearIsometryEquiv
    (p : PositiveDefiniteFunction G) (s : G) :
    letI : SeminormedAddCommGroup (PreHilbertSpace p) :=
      preHilbertSeminormed p
    letI : InnerProductSpace ℝ (PreHilbertSpace p) :=
      preHilbertInnerProduct p
    PreHilbertSpace p ≃ₗᵢ[ℝ] PreHilbertSpace p := by
  letI : SeminormedAddCommGroup (PreHilbertSpace p) :=
    preHilbertSeminormed p
  letI : InnerProductSpace ℝ (PreHilbertSpace p) :=
    preHilbertInnerProduct p
  refine
    { preTranslationLinearEquiv p s with
      norm_map' := fun f ↦ ?_ }
  have hinner := inner_preTranslationLinearEquiv p s f f
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hinner
  nlinarith only [hinner, norm_nonneg (preTranslationLinearEquiv p s f), norm_nonneg f]

@[simp] theorem preTranslationLinearEquiv_inv_apply
    (p : PositiveDefiniteFunction G) (s : G) (f : PreHilbertSpace p) :
    preTranslationLinearEquiv p s⁻¹ (preTranslationLinearEquiv p s f) = f := by
  ext i
  simp [preTranslationLinearEquiv, leftIndexEquiv]

@[simp] theorem preTranslationLinearEquiv_apply_inv
    (p : PositiveDefiniteFunction G) (s : G) (f : PreHilbertSpace p) :
    preTranslationLinearEquiv p s (preTranslationLinearEquiv p s⁻¹ f) = f := by
  ext i
  simp [preTranslationLinearEquiv, leftIndexEquiv]

/-- Left translation as a continuous linear map on the seminormed
pre-Hilbert space. -/
noncomputable def preTranslationContinuousLinearMap
    (p : PositiveDefiniteFunction G) (s : G) :
    letI : SeminormedAddCommGroup (PreHilbertSpace p) :=
      preHilbertSeminormed p
    letI : InnerProductSpace ℝ (PreHilbertSpace p) :=
      preHilbertInnerProduct p
    PreHilbertSpace p →L[ℝ] PreHilbertSpace p := by
  letI : SeminormedAddCommGroup (PreHilbertSpace p) :=
    preHilbertSeminormed p
  letI : InnerProductSpace ℝ (PreHilbertSpace p) :=
    preHilbertInnerProduct p
  exact (preTranslationLinearEquiv p s).toLinearMap.mkContinuous 1 fun f ↦ by
    change ‖preTranslationLinearEquiv p s f‖ ≤ 1 * ‖f‖
    have hn := (preTranslationLinearIsometryEquiv p s).norm_map f
    change ‖preTranslationLinearEquiv p s f‖ = ‖f‖ at hn
    rw [hn]
    simp

/-- Left translation extended continuously to the completed RKHS. -/
noncomputable def translationOperator (p : PositiveDefiniteFunction G) (s : G) :
    HilbertSpace p ≃ₗᵢ[ℝ] HilbertSpace p := by
  letI : SeminormedAddCommGroup (PreHilbertSpace p) :=
    preHilbertSeminormed p
  letI : InnerProductSpace ℝ (PreHilbertSpace p) :=
    preHilbertInnerProduct p
  let L := preTranslationContinuousLinearMap p s
  let Linv := preTranslationContinuousLinearMap p s⁻¹
  let T : HilbertSpace p →L[ℝ] HilbertSpace p :=
    L.completion
  let Tinv : HilbertSpace p →L[ℝ] HilbertSpace p :=
    Linv.completion
  refine
    { toFun := T
      invFun := Tinv
      left_inv := fun x ↦ ?_
      right_inv := fun x ↦ ?_
      map_add' := T.map_add
      map_smul' := T.map_smul
      norm_map' := fun x ↦ ?_ }
  · induction x using UniformSpace.Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x => simp [T, Tinv, L, Linv, preTranslationContinuousLinearMap]
  · induction x using UniformSpace.Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x => simp [T, Tinv, L, Linv, preTranslationContinuousLinearMap]
  · induction x using UniformSpace.Completion.induction_on with
    | hp =>
        change IsClosed {x | ‖T x‖ = ‖x‖}
        exact isClosed_eq (continuous_norm.comp T.continuous) continuous_norm
    | ih x =>
        have hn := (preTranslationLinearIsometryEquiv p s).norm_map x
        change ‖preTranslationLinearEquiv p s x‖ = ‖x‖ at hn
        simpa [T, L, preTranslationContinuousLinearMap] using hn

@[simp] theorem preTranslationLinearEquiv_one
    (p : PositiveDefiniteFunction G) (f : PreHilbertSpace p) :
    preTranslationLinearEquiv p 1 f = f := by
  ext i
  simp [preTranslationLinearEquiv, leftIndexEquiv]

@[simp] theorem preTranslationLinearEquiv_mul
    (p : PositiveDefiniteFunction G) (s t : G) (f : PreHilbertSpace p) :
    preTranslationLinearEquiv p (s * t) f =
      preTranslationLinearEquiv p s (preTranslationLinearEquiv p t f) := by
  ext i
  simp [preTranslationLinearEquiv, leftIndexEquiv, mul_assoc]

/-- The completed translation agrees with the explicit translation on the
dense finitely supported subspace. -/
@[simp] theorem translationOperator_coe
    (p : PositiveDefiniteFunction G) (s : G) (f : PreHilbertSpace p) :
    translationOperator p s (UniformSpace.Completion.coe' f) =
      UniformSpace.Completion.coe' (preTranslationLinearEquiv p s f) := by
  change (preTranslationContinuousLinearMap p s).completion
      (UniformSpace.Completion.coe' f) = _
  simp [preTranslationContinuousLinearMap]

@[simp] theorem translationOperator_one (p : PositiveDefiniteFunction G) :
    translationOperator p 1 = 1 := by
  apply LinearIsometryEquiv.ext
  intro x
  induction x using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih f => simp

@[simp] theorem translationOperator_mul (p : PositiveDefiniteFunction G) (s t : G) :
    translationOperator p (s * t) =
      translationOperator p s * translationOperator p t := by
  apply LinearIsometryEquiv.ext
  intro x
  induction x using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih f => simp

/-- The left-translation representation generated by a positive-definite
function. -/
noncomputable def representation (p : PositiveDefiniteFunction G) :
    G →* (HilbertSpace p ≃ₗᵢ[ℝ] HilbertSpace p) where
  toFun := translationOperator p
  map_one' := translationOperator_one p
  map_mul' := translationOperator_mul p

@[simp] theorem representation_kernelVector
    (p : PositiveDefiniteFunction G) (s g : G) :
    representation p s (kernelVector p g) = kernelVector p (s * g) := by
  letI : SeminormedAddCommGroup (PreHilbertSpace p) :=
    preHilbertSeminormed p
  letI : InnerProductSpace ℝ (PreHilbertSpace p) :=
    preHilbertInnerProduct p
  change translationOperator p s
    (UniformSpace.Completion.coe'
      (Finsupp.single (g, (1 : ℝ)) 1 : PreHilbertSpace p)) =
    UniformSpace.Completion.coe'
      (Finsupp.single (s * g, (1 : ℝ)) 1 : PreHilbertSpace p)
  rw [translationOperator_coe, preTranslationLinearEquiv_single]
  change UniformSpace.Completion.coe'
    (Finsupp.single (s * g, (1 : ℝ)) 1 : PreHilbertSpace p) = _
  rfl

/-- The linear combination of cyclic kernel vectors encoded by a finitely
supported coefficient function on the group. -/
noncomputable def finsuppCombination (p : PositiveDefiniteFunction G) :
    (G →₀ ℝ) →ₗ[ℝ] HilbertSpace p :=
  Finsupp.linearCombination ℝ (kernelVector p)

/-- Left translation of a finitely supported coefficient function. -/
noncomputable def translateCoefficients (s : G) :
    (G →₀ ℝ) ≃ₗ[ℝ] (G →₀ ℝ) :=
  Finsupp.domLCongr (leftGroupEquiv s)

@[simp] theorem translateCoefficients_single (s g : G) (r : ℝ) :
    translateCoefficients s (Finsupp.single g r) =
      Finsupp.single (s * g) r := by
  simp [translateCoefficients, leftGroupEquiv]

/-- The GNS representation translates every finitely supported cyclic
combination by left multiplication of its indices. -/
theorem representation_finsuppCombination
    (p : PositiveDefiniteFunction G) (s : G) (c : G →₀ ℝ) :
    representation p s (finsuppCombination p c) =
      finsuppCombination p (translateCoefficients s c) := by
  induction c using Finsupp.induction with
  | zero => simp
  | single_add g r c _ _ ih =>
      rw [map_add, map_add, ih]
      simp [finsuppCombination, representation_kernelVector]

/-- The finitely supported probability measure obtained by taking `k`
uniform steps in the averaging set. -/
noncomputable def averagingCoefficients (S : Finset G) : ℕ → G →₀ ℝ
  | 0 => Finsupp.single 1 1
  | k + 1 => (S.card : ℝ)⁻¹ •
      ∑ s ∈ S, translateCoefficients s (averagingCoefficients S k)

/-- Applying one GNS orbit average advances the averaging coefficients by
one step. -/
theorem finsuppCombination_averagingCoefficients_succ
    (p : PositiveDefiniteFunction G) (S : Finset G) (k : ℕ) :
    finsuppCombination p (averagingCoefficients S (k + 1)) =
      IsKazhdanPair.orbitAverage S (representation p)
        (finsuppCombination p (averagingCoefficients S k)) := by
  classical
  rw [averagingCoefficients]
  rw [IsKazhdanPair.orbitAverage]
  simp only [map_smul, map_sum]
  simp_rw [representation_finsuppCombination]

/-- A finite linear combination whose index type may retain repeated group
words.  This is convenient for powers of an averaging operator. -/
noncomputable def indexedCombination {I : Type*}
    (p : PositiveDefiniteFunction G) (F : Finset I)
    (a : I → G) (c : I → ℝ) : HilbertSpace p :=
  ∑ i ∈ F, c i • kernelVector p (a i)

/-- Squared norms of indexed cyclic combinations are their finite Gram
quadratic forms. -/
theorem norm_indexedCombination_sq {I : Type*}
    (p : PositiveDefiniteFunction G) (F : Finset I)
    (a : I → G) (c : I → ℝ) :
    ‖indexedCombination p F a c‖ ^ 2 =
      ∑ i ∈ F, ∑ j ∈ F, c i * c j * p ((a i)⁻¹ * a j) := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  simp_rw [indexedCombination, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, inner_kernelVector]
  simp [mul_assoc]

/-- A `Finsupp` cyclic combination is its support-indexed finite
combination. -/
theorem finsuppCombination_eq_indexed (p : PositiveDefiniteFunction G)
    (c : G →₀ ℝ) :
    finsuppCombination p c = indexedCombination p c.support id c := by
  classical
  simp [finsuppCombination, indexedCombination,
    Finsupp.linearCombination_apply, Finsupp.sum]

/-- Iterated orbit averaging of the cyclic vector is represented by the
explicit finitely supported convolution coefficients. -/
theorem iterate_orbitAverage_kernelVector
    (p : PositiveDefiniteFunction G) (S : Finset G) (k : ℕ) :
    let A := IsKazhdanPair.orbitAverage S (representation p)
    (A^[k]) (kernelVector p 1) =
      finsuppCombination p (averagingCoefficients S k) := by
  let A := IsKazhdanPair.orbitAverage S (representation p)
  induction k with
  | zero =>
      simp [averagingCoefficients, finsuppCombination]
  | succ k ih =>
      dsimp only
      rw [Function.iterate_succ_apply', ih]
      exact (finsuppCombination_averagingCoefficients_succ p S k).symm

/-- Coefficients of the displacement between two successive averaging
steps. -/
noncomputable def averagingDisplacementCoefficients
    (S : Finset G) (k : ℕ) : G →₀ ℝ :=
  averagingCoefficients S (k + 1) - averagingCoefficients S k

/-- Successive GNS averaging displacement as one explicit cyclic
combination. -/
theorem iterate_orbitAverage_succ_sub_eq_finsuppCombination
    (p : PositiveDefiniteFunction G) (S : Finset G) (k : ℕ) :
    let A := IsKazhdanPair.orbitAverage S (representation p)
    (A^[k + 1]) (kernelVector p 1) -
        (A^[k]) (kernelVector p 1) =
      finsuppCombination p (averagingDisplacementCoefficients S k) := by
  dsimp only
  have hk1 := iterate_orbitAverage_kernelVector p S (k + 1)
  have hk := iterate_orbitAverage_kernelVector p S k
  dsimp only at hk1 hk
  rw [hk1, hk]
  simp [averagingDisplacementCoefficients]

/-- Finite hyperreals are closed under negation. -/
theorem hyperreal_neg_finite {x : Hyperreal}
    (hx : 0 ≤ ArchimedeanClass.mk x) :
    0 ≤ ArchimedeanClass.mk (-x) := by
  rw [ArchimedeanClass.mk_neg]
  exact hx

/-- Finite hyperreals are closed under subtraction. -/
theorem hyperreal_sub_finite {x y : Hyperreal}
    (hx : 0 ≤ ArchimedeanClass.mk x)
    (hy : 0 ≤ ArchimedeanClass.mk y) :
    0 ≤ ArchimedeanClass.mk (x - y) := by
  rw [sub_eq_add_neg]
  exact hyperreal_add_finite hx (hyperreal_neg_finite hy)

end KazhdanGNS
end GroupApproximation
