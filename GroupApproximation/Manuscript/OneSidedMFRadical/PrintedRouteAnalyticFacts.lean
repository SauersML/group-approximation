import GroupApproximation.Manuscript.OneSidedMFRadical.CornerCoronaClass
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedCoronaNormSeparation
import GroupApproximation.Analysis.MaximalGroupCStarTrace
import GroupApproximation.Analysis.TracialMatrixUltraproduct
import GroupApproximation.Sofic.LeavittTraceFloor

/-!
# Analytic facts used by the printed proof of `thm:normal-kazhdan`

`non_mf_groups_exist.tex`, the proof of Theorem `thm:normal-kazhdan` as it now
stands (the ultrafilter-free rewrite).  That proof spends four facts which the
development carried only in pieces:

* the corner embedding `q_n M_{d_n}(ℂ) q_n ⊆ M_{d_n}(ℂ)` is **linear**, so a
  finite linear combination `Σ α_k W_n(k)` of corner unitaries may be read
  inside the ambient matrices without changing its operator norm
  (`CornerMatrixEmbedding` proves only `sub`, `mul`, `star` and the isometry);
* "after passing to an infinite coordinate subsequence" is a **⋆-algebra**
  homomorphism of coronas, not merely a ring homomorphism: the printed
  combination carries complex coefficients, so `coronaRestrict` has to move
  scalars (`CornerCoronaClass.coronaRestrict` is bundled as a `→+*`);
* the printed sentence "the group algebra `ℂ[K]` is dense in `C*_max(K)`, so
  there are a finite set `F ⊆ K` and scalars `(α_k)`" needs the density of
  `Analysis/MaximalGroupCStarTrace.maximalGroupCStar_dense_span_generator` in
  the *explicit finite sum* form;
* the printed `|tr_{r_n}(W_n(k)) - 1| ≤ ‖W_n(k) - I_{r_n}‖₂`, which is
  `norm_normTrace_le_hsNorm` after `normTrace_one'` moves the `1` inside.

Nothing here is manuscript-facing on its own; the printed sentences are in
`Manuscript/OneSidedMFRadical/NormalKazhdanPrintedRoute.lean`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace NormalKazhdanPrintedRoute

open Filter Matrix Topology
open PrintedCornerCompression
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## Linearity of the zero extension and of the corner embedding -/

theorem blockExtend_zero {Y : Type*} (p : Y → Prop) [DecidablePred p] :
    blockExtend p (0 : Matrix {i : Y // p i} {i : Y // p i} ℂ) = 0 := by
  ext i j
  simp only [blockExtend_apply, Matrix.zero_apply]
  by_cases hi : p i <;> by_cases hj : p j <;> simp [hi, hj]

theorem blockExtend_add {Y : Type*} (p : Y → Prop) [DecidablePred p]
    (C C' : Matrix {i : Y // p i} {i : Y // p i} ℂ) :
    blockExtend p (C + C') = blockExtend p C + blockExtend p C' := by
  ext i j
  simp only [blockExtend_apply, Matrix.add_apply]
  by_cases hi : p i <;> by_cases hj : p j <;> simp [hi, hj]

theorem blockExtend_smul {Y : Type*} (p : Y → Prop) [DecidablePred p]
    (z : ℂ) (C : Matrix {i : Y // p i} {i : Y // p i} ℂ) :
    blockExtend p (z • C) = z • blockExtend p C := by
  ext i j
  simp only [blockExtend_apply, Matrix.smul_apply]
  by_cases hi : p i <;> by_cases hj : p j <;> simp [hi, hj]

theorem cornerEmbed_zero {Y : Type*} [Fintype Y] [DecidableEq Y]
    {q : Matrix Y Y ℂ} (hq : q.IsHermitian) :
    cornerEmbed hq (0 : Matrix {i : Y // cornerPredicate hq i}
      {i : Y // cornerPredicate hq i} ℂ) = 0 := by
  rw [cornerEmbed, blockExtend_zero, Matrix.mul_zero, Matrix.zero_mul]

theorem cornerEmbed_add {Y : Type*} [Fintype Y] [DecidableEq Y]
    {q : Matrix Y Y ℂ} (hq : q.IsHermitian)
    (C C' : Matrix {i : Y // cornerPredicate hq i}
      {i : Y // cornerPredicate hq i} ℂ) :
    cornerEmbed hq (C + C') = cornerEmbed hq C + cornerEmbed hq C' := by
  simp only [cornerEmbed, blockExtend_add, Matrix.mul_add, Matrix.add_mul]

theorem cornerEmbed_smul {Y : Type*} [Fintype Y] [DecidableEq Y]
    {q : Matrix Y Y ℂ} (hq : q.IsHermitian) (z : ℂ)
    (C : Matrix {i : Y // cornerPredicate hq i}
      {i : Y // cornerPredicate hq i} ℂ) :
    cornerEmbed hq (z • C) = z • cornerEmbed hq C := by
  simp only [cornerEmbed, blockExtend_smul, Matrix.mul_smul, Matrix.smul_mul]

/-- **The corner embedding carries a printed finite combination to a finite
combination.**  This is what lets `‖Σ_k α_k W_n(k)‖` be computed inside the
ambient matrices, where the corona lives. -/
theorem cornerEmbed_sum_smul {Y : Type*} [Fintype Y] [DecidableEq Y]
    {q : Matrix Y Y ℂ} (hq : q.IsHermitian) {ι : Type*} (F : Finset ι)
    (alpha : ι → ℂ) (C : ι → Matrix {i : Y // cornerPredicate hq i}
      {i : Y // cornerPredicate hq i} ℂ) :
    cornerEmbed hq (∑ s ∈ F, alpha s • C s)
      = ∑ s ∈ F, alpha s • cornerEmbed hq (C s) := by
  classical
  refine Finset.induction_on F ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, cornerEmbed_zero]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, cornerEmbed_add,
      cornerEmbed_smul, ih]

/-! ## Discarding coordinates is a ⋆-algebra homomorphism -/

variable (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]

/-- **`coronaRestrict` as a ⋆-algebra homomorphism.**  `CornerCoronaClass`
bundles the coordinate restriction as a ring homomorphism, which cannot move
the complex coefficients `α_k` of the printed combination. -/
def coronaRestrictAlg (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    NormMatrixCStarCorona (fun n ↦ X n) →⋆ₐ[ℂ]
      NormMatrixCStarCorona (fun k ↦ X (φ k)) where
  toFun := coronaRestrict X φ hφ
  map_one' := map_one (coronaRestrict X φ hφ)
  map_mul' := map_mul (coronaRestrict X φ hφ)
  map_zero' := map_zero (coronaRestrict X φ hφ)
  map_add' := map_add (coronaRestrict X φ hφ)
  commutes' z := by
    have h1 : (algebraMap ℂ (NormMatrixCStarCorona (fun n ↦ X n))) z
        = normMatrixCStarCoronaMk (fun n ↦ X n)
            ((algebraMap ℂ (BoundedMatrixSequence (fun n ↦ X n))) z) :=
      ((normMatrixCStarCoronaQuotient (fun n ↦ X n)).commutes z).symm
    have h2 : restrictSeq X φ
          ((algebraMap ℂ (BoundedMatrixSequence (fun n ↦ X n))) z)
        = (algebraMap ℂ (BoundedMatrixSequence (fun k ↦ X (φ k)))) z :=
      (restrictSeq X φ).commutes z
    have h3 : normMatrixCStarCoronaMk (fun k ↦ X (φ k))
          ((algebraMap ℂ (BoundedMatrixSequence (fun k ↦ X (φ k)))) z)
        = (algebraMap ℂ (NormMatrixCStarCorona (fun k ↦ X (φ k)))) z :=
      (normMatrixCStarCoronaQuotient (fun k ↦ X (φ k))).commutes z
    show coronaRestrict X φ hφ _ = _
    rw [h1, coronaRestrict_mk, h2, h3]
  map_star' := coronaRestrict_star X φ hφ

@[simp] theorem coronaRestrictAlg_apply (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (x : NormMatrixCStarCorona (fun n ↦ X n)) :
    coronaRestrictAlg X φ hφ x = coronaRestrict X φ hφ x := rfl

theorem coronaRestrictAlg_mk (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (a : BoundedMatrixSequence (fun n ↦ X n)) :
    coronaRestrictAlg X φ hφ (normMatrixCStarCoronaMk (fun n ↦ X n) a)
      = normMatrixCStarCoronaMk (fun k ↦ X (φ k)) (restrictSeq X φ a) :=
  coronaRestrict_mk X φ hφ a

theorem norm_coronaRestrictAlg_le (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (x : NormMatrixCStarCorona (fun n ↦ X n)) :
    ‖coronaRestrictAlg X φ hφ x‖ ≤ ‖x‖ :=
  NonUnitalStarAlgHom.norm_apply_le (coronaRestrictAlg X φ hφ) x

/-! ## Density of the group algebra, with the finite sum exhibited -/

/-- **"The group algebra `ℂ[K]` is dense in `C*_max(K)`."**  In the form the
printed proof uses it: a finite subset `F` of the group and scalars `α` with
`‖Σ_{k ∈ F} α_k u_k − x‖ < ε`. -/
theorem exists_generatorCombination_close {K : Type} [Group K]
    (x : MaximalGroupCStar K) {eps : ℝ} (heps : 0 < eps) :
    ∃ (F : Finset K) (alpha : K → ℂ),
      ‖(∑ k ∈ F, alpha k • maximalGroupCStarGenerator K k) - x‖ < eps := by
  classical
  obtain ⟨y, hyball, hyspan⟩ :=
    (Metric.dense_iff.mp (maximalGroupCStar_dense_span_generator K)) x eps heps
  have hmem : y ∈ Submodule.span ℂ (Set.range (maximalGroupCStarGenerator K)) :=
    hyspan
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hmem
  refine ⟨c.support, fun k ↦ c k, ?_⟩
  have hsum : (∑ k ∈ c.support, c k • maximalGroupCStarGenerator K k) = y := hc
  rw [hsum]
  have hdist : dist y x < eps := Metric.mem_ball.mp hyball
  rwa [dist_eq_norm] at hdist

/-! ## The printed trace estimates -/

/-- **`|tr_r(u) − 1| ≤ ‖u − I_r‖₂`.**  The printed inequality that turns the
Hilbert--Schmidt hypothesis into a statement about traces. -/
theorem norm_normTrace_sub_one_le (Y : FiniteModel) (hY : 0 < Fintype.card Y)
    (u : Matrix Y Y ℂ) :
    ‖normTrace Y u - 1‖ ≤ Real.sqrt (hsLengthSq Y u) := by
  have h1 : normTrace Y u - 1 = normTrace Y (u - 1) := by
    rw [normTrace_sub, normTrace_one' Y hY]
  rw [h1]
  have h2 := norm_normTrace_le_hsNorm Y (u - 1)
  have h3 : hsNorm Y (u - 1) = Real.sqrt (hsLengthSq Y u) := rfl
  rwa [h3] at h2

/-- The normalized trace of a printed finite combination. -/
theorem normTrace_sum_smul {ι : Type*} (Y : FiniteModel) (F : Finset ι)
    (alpha : ι → ℂ) (A : ι → Matrix Y Y ℂ) :
    normTrace Y (∑ s ∈ F, alpha s • A s)
      = ∑ s ∈ F, alpha s * normTrace Y (A s) := by
  classical
  refine Finset.induction_on F ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, TracialUltraproduct.normTrace_zero]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      TracialUltraproduct.normTrace_add, TracialUltraproduct.normTrace_smul, ih]

end

end NormalKazhdanPrintedRoute
end OneSidedMFRadical
end Manuscript
end GroupApproximation
