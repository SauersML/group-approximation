import GroupApproximation.Analysis.DenseRationalStarPolynomialExtension
import GroupApproximation.Analysis.ReducedProductMFBlockDiagonal

/-!
# Reduced products of MF algebras

This is the manuscript's reduced-product permanence lemma.  For a separable
C-star algebra faithfully represented in `prod B_n / direct sum B_n`, choose a
dense sequence and the block-diagonal matrix sequence constructed in the
preceding modules.  The finite-stage estimates make every rational star
polynomial norm agree.  `DenseRationalStarPolynomialExtension` extends the
assignment isometrically to the whole algebra, yielding an MF embedding.
-/

namespace GroupApproximation
namespace ReducedProductMFPermanence

open Filter
open PolarLiftingGeneralCStar
open RationalNoncommutativeStarPolynomial
open DenseRationalStarPolynomialExtension
open ReducedProductMFDiagonalData
open ReducedProductMFFiniteSelection
open ReducedProductMFBlockDiagonal
open NormMatrixCoronaPolynomialLifts
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u v

noncomputable local instance matrixBlockCStarAlgebraForReducedProductPermanence
    (Z : Type*) [Fintype Z] [DecidableEq Z] [Nonempty Z] :
    CStarAlgebra (Matrix Z Z ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

noncomputable local instance boundedMatrixSequenceCStarAlgebraForReducedProductPermanence
    (X : ℕ → Type*) [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
    [∀ n, Nonempty (X n)] : CStarAlgebra (BoundedMatrixSequence X) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

variable (B : ℕ → Type u) [∀ n, CStarAlgebra (B n)]
  [∀ n, Nontrivial (B n)]
variable {C : Type v} [CStarAlgebra C]
variable (i : C →⋆ₙₐ[ℂ] CStarProductCorona B cofinite)
variable (hi : Function.Injective i)
variable (a : ℕ → C)
variable (hB : ∀ n, HasMFEmbedding (B n))

theorem reducedProductPolynomial_quotient (p : Polynomial) :
    cStarProductCoronaQuotient B cofinite
        (eval (reducedProductGeneratorLift B i a) p) = i (eval a p) := by
  let q := (cStarProductCoronaQuotient B cofinite).toNonUnitalStarAlgHom
  calc
    cStarProductCoronaQuotient B cofinite
        (eval (reducedProductGeneratorLift B i a) p) =
      eval (fun j ↦ q (reducedProductGeneratorLift B i a j)) p :=
        map_eval q (reducedProductGeneratorLift B i a) p
    _ = eval (fun j ↦ i (a j)) p := by
      congr 1
      funext j
      exact reducedProductGeneratorLift_quotient B i a j
    _ = i (eval a p) := (map_eval i a p).symm

private theorem eval_reducedProductGeneratorLift_apply
    (p : Polynomial) (n : ℕ) :
    eval (reducedProductGeneratorLift B i a) p n =
      eval (fun j ↦ reducedProductGeneratorLift B i a j n) p := by
  induction p with
  | zero => rfl
  | generator j => rfl
  | smul q p hp =>
      rw [eval_smul, eval_smul, lp.coeFn_smul, Pi.smul_apply, hp]
  | add p q hp hq =>
      rw [eval_add, eval_add, lp.coeFn_add, Pi.add_apply, hp, hq]
  | mul p q hp hq =>
      rw [eval_mul, eval_mul, lp.infty_coeFn_mul, Pi.mul_apply, hp, hq]
  | star p hp =>
      rw [eval_star, eval_star, lp.coeFn_star, Pi.star_apply, hp]

include hi in
theorem norm_polynomial_eq_outer_limsup (p : Polynomial) :
    ‖eval a p‖ = Filter.limsup
      (fun n ↦ ‖eval (fun j ↦ reducedProductGeneratorLift B i a j n) p‖)
      atTop := by
  rw [← NonUnitalStarAlgHom.norm_map i hi]
  rw [← reducedProductPolynomial_quotient B i a p]
  rw [norm_cStarProductCorona_quotient_eq_limsup]
  rw [Nat.cofinite_eq_atTop]
  congr 1
  funext n
  exact congrArg norm (eval_reducedProductGeneratorLift_apply B i a p n)

theorem tendsto_selectedPolynomial_norm_sub (p : Polynomial) :
    Tendsto
      (fun n ↦ ‖eval (selectedGenerator B i a hB n) p‖ -
        ‖eval (fun j ↦ reducedProductGeneratorLift B i a j n) p‖)
      atTop (nhds 0) := by
  obtain ⟨r, hr⟩ := enumeration_surjective p
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp tendsto_stageError ε hε
  refine ⟨max r N, fun n hn ↦ ?_⟩
  have hnr : r ≤ n := le_trans (Nat.le_max_left r N) hn
  have hnN : N ≤ n := le_trans (Nat.le_max_right r N) hn
  have herr : stageError n < ε := by
    simpa only [Real.dist_eq, sub_zero,
      abs_of_pos (stageError_pos n)] using hN n hnN
  have habs :
      |‖eval (selectedGenerator B i a hB n) p‖ -
        ‖eval (fun j ↦ reducedProductGeneratorLift B i a j n) p‖| <
          stageError n := by
    let rf : Fin (n + 1) := ⟨r, Nat.lt_succ_of_le hnr⟩
    have hu := selectedPolynomial_upper B i a hB n rf
    have hl := selectedPolynomial_lower B i a hB n rf
    rw [hr] at hu hl
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  rw [Real.dist_eq, sub_zero]
  exact habs.trans herr

private theorem limsup_le_of_tendsto_sub_zero
    (x y : ℕ → ℝ)
    (hx : IsBoundedUnder (· ≤ ·) atTop x)
    (hxc : IsCoboundedUnder (· ≤ ·) atTop x)
    (hy : IsBoundedUnder (· ≤ ·) atTop y)
    (hsub : Tendsto (fun n ↦ x n - y n) atTop (nhds 0)) :
    Filter.limsup x atTop ≤ Filter.limsup y atTop := by
  apply (Filter.limsup_le_iff hxc hx).mpr
  intro z hz
  let ε := (z - Filter.limsup y atTop) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hylt : ∀ᶠ n in atTop, y n < Filter.limsup y atTop + ε :=
    Filter.eventually_lt_of_limsup_lt (lt_add_of_pos_right _ hε) hy
  have hdiff : ∀ᶠ n in atTop, |x n - y n| < ε := by
    have h := (Metric.tendsto_nhds.mp hsub) ε hε
    filter_upwards [h] with n hn
    simpa only [Real.dist_eq, sub_zero, abs_abs] using hn
  filter_upwards [hylt, hdiff] with n hyn hdn
  have hxy : x n - y n ≤ |x n - y n| := le_abs_self _
  dsimp [ε] at *
  linarith

private theorem limsup_eq_of_tendsto_sub_zero
    (x y : ℕ → ℝ)
    (hx : IsBoundedUnder (· ≤ ·) atTop x)
    (hxc : IsCoboundedUnder (· ≤ ·) atTop x)
    (hy : IsBoundedUnder (· ≤ ·) atTop y)
    (hyc : IsCoboundedUnder (· ≤ ·) atTop y)
    (hsub : Tendsto (fun n ↦ x n - y n) atTop (nhds 0)) :
    Filter.limsup x atTop = Filter.limsup y atTop := by
  apply le_antisymm
  · exact limsup_le_of_tendsto_sub_zero x y hx hxc hy hsub
  · apply limsup_le_of_tendsto_sub_zero y x hy hyc hx
    simpa [neg_sub] using hsub.neg

theorem selectedPolynomial_limsup_eq (p : Polynomial) :
    Filter.limsup (fun n ↦ ‖eval (selectedGenerator B i a hB n) p‖) atTop =
      Filter.limsup
        (fun n ↦ ‖eval (fun j ↦ reducedProductGeneratorLift B i a j n) p‖)
        atTop := by
  let x := fun n ↦ ‖eval (selectedGenerator B i a hB n) p‖
  let y := fun n ↦
    ‖eval (fun j ↦ reducedProductGeneratorLift B i a j n) p‖
  let xb : BoundedMatrixSequence (fun n ↦ selectedModel B i a hB n) :=
    eval (diagonalGenerator B i a hB) p
  let yb : BoundedCStarSequence B := eval (reducedProductGeneratorLift B i a) p
  have hx : IsBoundedUnder (· ≤ ·) atTop x :=
    ⟨‖xb‖, show ∀ᶠ n : ℕ in atTop, x n ≤ ‖xb‖ from
      Eventually.of_forall fun n ↦ by
        have heval := congrArg norm
          (eval_diagonalGenerator_apply B i a hB p n)
        calc
          x n = ‖eval (diagonalGenerator B i a hB) p n‖ := by
            simpa only [x] using heval.symm
          _ ≤ ‖xb‖ := by
            simpa only [xb] using boundedMatrixSequence_coord_norm_le
              (fun r ↦ selectedModel B i a hB r) xb n⟩
  have hy : IsBoundedUnder (· ≤ ·) atTop y :=
    ⟨‖yb‖, show ∀ᶠ n : ℕ in atTop, y n ≤ ‖yb‖ from
      Eventually.of_forall fun n ↦ by
        have heval := congrArg norm
          (eval_reducedProductGeneratorLift_apply B i a p n)
        calc
          y n = ‖eval (reducedProductGeneratorLift B i a) p n‖ := by
            simpa only [y] using heval.symm
          _ ≤ ‖yb‖ := by
            simpa only [yb] using boundedCStarSequence_coord_norm_le B yb n⟩
  have hxc : IsCoboundedUnder (· ≤ ·) atTop x :=
    Filter.isCoboundedUnder_le_of_le atTop fun n ↦ norm_nonneg _
  have hyc : IsCoboundedUnder (· ≤ ·) atTop y :=
    Filter.isCoboundedUnder_le_of_le atTop fun n ↦ norm_nonneg _
  exact limsup_eq_of_tendsto_sub_zero x y hx hxc hy hyc
    (tendsto_selectedPolynomial_norm_sub B i a hB p)

include hi in
/-- The block-diagonal generator classes have exactly the same rational star
polynomial norms as the original dense family. -/
theorem diagonalPolynomial_norm (p : Polynomial) :
    ‖eval (fun j ↦ normMatrixCStarCoronaMk
      (fun n ↦ selectedModel B i a hB n)
      (diagonalGenerator B i a hB j)) p‖ = ‖eval a p‖ := by
  let q := (normMatrixCStarCoronaQuotient
    (fun n ↦ selectedModel B i a hB n)).toNonUnitalStarAlgHom
  change ‖eval (fun j ↦ q (diagonalGenerator B i a hB j)) p‖ = ‖eval a p‖
  calc
    ‖eval (fun j ↦ q (diagonalGenerator B i a hB j)) p‖ =
        ‖q (eval (diagonalGenerator B i a hB) p)‖ :=
      congrArg norm (map_eval q (diagonalGenerator B i a hB) p).symm
    _ = Filter.limsup
        (fun n ↦ ‖eval (diagonalGenerator B i a hB) p n‖) cofinite := by
      change ‖normMatrixCStarCoronaMk
        (fun n ↦ selectedModel B i a hB n)
        (eval (diagonalGenerator B i a hB) p)‖ = _
      exact norm_normMatrixCStarCoronaMk_eq_limsup _ _
    _ = Filter.limsup
        (fun n ↦ ‖eval (selectedGenerator B i a hB n) p‖) cofinite := by
      congr 1
      funext n
      exact congrArg norm (eval_diagonalGenerator_apply B i a hB p n)
    _ = Filter.limsup
        (fun n ↦ ‖eval (selectedGenerator B i a hB n) p‖) atTop := by
      rw [Nat.cofinite_eq_atTop]
    _ = Filter.limsup
        (fun n ↦ ‖eval (fun j ↦ reducedProductGeneratorLift B i a j n) p‖)
        atTop := selectedPolynomial_limsup_eq B i a hB p
    _ = ‖eval a p‖ := (norm_polynomial_eq_outer_limsup B i hi a p).symm

include B i hi hB in
/-- **Reduced-product MF permanence, with an explicit dense sequence.** -/
theorem hasMFEmbedding_of_denseRange (ha : DenseRange a) : HasMFEmbedding C := by
  let d : ℕ → NormMatrixCStarCorona
      (fun n ↦ selectedModel B i a hB n) := fun j ↦
    normMatrixCStarCoronaMk (fun n ↦ selectedModel B i a hB n)
      (diagonalGenerator B i a hB j)
  let S := ApproximationScheme.ofDenseRange a ha
  let e : C →⋆ₙₐ[ℂ] NormMatrixCStarCorona
      (fun n ↦ selectedModel B i a hB n) :=
    extensionHom a d S (diagonalPolynomial_norm B i hi a hB)
  have he : Function.Injective e :=
    extensionHom_injective a d S (diagonalPolynomial_norm B i hi a hB)
  apply (MFAlgebraDimension.hasMFEmbedding_iff C).mpr
  exact ⟨selectedModel B i a hB, fun n ↦ inferInstance,
    fun n ↦ Fintype.card_pos_iff.mpr inferInstance, e, he⟩

include B i hi hB in
/-- **The manuscript lemma.**  If every coordinate algebra is MF, then every
separable C-star algebra faithfully represented in their norm reduced product
is MF. -/
theorem isMFAlgebra_of_injective_reducedProduct
    [TopologicalSpace.SeparableSpace C] : IsMFAlgebra C := by
  let a : ℕ → C := TopologicalSpace.denseSeq C
  have ha : DenseRange a := by
    exact TopologicalSpace.denseRange_denseSeq C
  exact ⟨inferInstance, hasMFEmbedding_of_denseRange B i hi a hB ha⟩

end

end ReducedProductMFPermanence
end GroupApproximation

#print axioms GroupApproximation.ReducedProductMFPermanence.hasMFEmbedding_of_denseRange
#print axioms GroupApproximation.ReducedProductMFPermanence.isMFAlgebra_of_injective_reducedProduct
