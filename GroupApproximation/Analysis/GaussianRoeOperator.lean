import GroupApproximation.Analysis.L2KernelOperator
import GroupApproximation.Analysis.SchoenbergKernel
import GroupApproximation.Algebra.WordMetricBall

/-!
# The Gaussian kernel as an element of the uniform Roe algebra

This module carries out step 1 of Guentner--Kaminker's Lemma 3.5 without a
Schur test.  The Gaussian kernel is approximated by its finite-width
truncations, which `Analysis/L2KernelOperator.lean` realises as honest bounded
operators, and the truncations form a Cauchy sequence in operator norm because
the `ℓ¹`-over-the-window bound is exactly the tail estimate
`CoarseCompression.exists_tail_bound_norm`.  The limit is therefore an element
of the norm closure of the finite-propagation operators, which is the uniform
Roe algebra.

## Reading the kernel through inversion

`gaussianKernel` decays in the **left**-invariant word metric `|x⁻¹y|`, while
the finite-propagation decomposition of `L2KernelOperator` is indexed by the
**right**-invariant displacement `s t⁻¹`.  Composing with inversion in both
arguments converts one into the other:

```
    invGaussian f κ s t = gaussianKernel f κ s⁻¹ t⁻¹ ,
```

and then the `g`-th diagonal is `s ↦ invGaussian f κ s (g⁻¹ s) =
gaussianKernel f κ s⁻¹ (s⁻¹ g)`, whose displacement is `|s · s⁻¹ g| = |g|`,
uniformly in `s`.  That uniformity is the whole point; without it the
`ℓ¹`-over-the-window bound would range over a conjugacy class and diverge.

Inversion costs nothing: the diagonal, symmetry, and positive type of the
kernel are all invariant under it, since it is a bijection of the index set.

## Statements

* `invGaussian` and its diagonal, symmetry, positivity and positive type;
* `diagBound` --- the bound on the `g`-th diagonal, `1` near the identity and
  the Gaussian majorant `exp(-κ|g|^{1+ε})` beyond `r₀`;
* `truncOp` --- the operator of the kernel truncated to the ball of radius `N`;
* `norm_truncOp_sub_le` --- the Cauchy estimate;
* `exists_roeOperator` --- **the conclusion**: there is an operator in the
  uniform Roe algebra whose matrix is the kernel.
-/

namespace GroupApproximation
namespace GaussianRoeOperator

open ReducedGroupCStarTrace UniformRoe L2KernelOperator CoarseCompression
open SchoenbergKernel
open scoped InnerProductSpace

universe u v

variable {G : Type u} [Group G] [DecidableEq G]
  {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## The kernel, read through inversion -/

/-- The Gaussian kernel composed with inversion in both arguments. -/
noncomputable def invGaussian (f : G → E) (κ : ℝ) (s t : G) : ℝ :=
  gaussianKernel f κ s⁻¹ t⁻¹

omit [DecidableEq G] [InnerProductSpace ℝ E] in
theorem invGaussian_self (f : G → E) (κ : ℝ) (s : G) : invGaussian f κ s s = 1 :=
  gaussianKernel_self f κ s⁻¹

omit [DecidableEq G] [InnerProductSpace ℝ E] in
theorem invGaussian_comm (f : G → E) (κ : ℝ) (s t : G) :
    invGaussian f κ s t = invGaussian f κ t s :=
  gaussianKernel_comm f κ s⁻¹ t⁻¹

omit [DecidableEq G] [InnerProductSpace ℝ E] in
theorem invGaussian_pos (f : G → E) (κ : ℝ) (s t : G) : 0 < invGaussian f κ s t :=
  gaussianKernel_pos f κ s⁻¹ t⁻¹

omit [DecidableEq G] [InnerProductSpace ℝ E] in
theorem invGaussian_le_one {κ : ℝ} (hκ : 0 ≤ κ) (f : G → E) (s t : G) :
    invGaussian f κ s t ≤ 1 :=
  gaussianKernel_le_one hκ f s⁻¹ t⁻¹

omit [DecidableEq G] in
/-- Inversion is a bijection of the index set, so it preserves positive type. -/
theorem invGaussian_isPositiveDefinite (f : G → E) {κ : ℝ} (hκ : 0 ≤ κ) :
    IsPositiveDefiniteKernel (invGaussian f κ) := fun n x c ↦
  gaussianKernel_isPositiveDefinite f hκ n (fun i ↦ (x i)⁻¹) c

/-- The complexification, which is what an operator matrix is. -/
noncomputable def invGaussianC (f : G → E) (κ : ℝ) (s t : G) : ℂ :=
  (invGaussian f κ s t : ℂ)

/-! ## The diagonal bound -/

/-- The bound on the `g`-th diagonal of the kernel: trivial inside the ball of
radius `r₀`, the Gaussian majorant outside it. -/
noncomputable def diagBound (T : Finset G) (r₀ : ℕ) (κ ε : ℝ) (g : G) : ℝ :=
  if WordMetric.wordNorm (↑T : Set G) g ≤ r₀ then 1
  else Real.exp (-(κ * (WordMetric.wordNorm (↑T : Set G) g : ℝ) ^ (1 + ε)))

omit [DecidableEq G] in
theorem diagBound_nonneg (T : Finset G) (r₀ : ℕ) (κ ε : ℝ) (g : G) :
    0 ≤ diagBound T r₀ κ ε g := by
  rw [diagBound]
  split
  · exact zero_le_one
  · exact Real.exp_nonneg _

omit [DecidableEq G] in
/-- Beyond the radius `r₀` the bound is the Gaussian majorant. -/
theorem diagBound_of_lt {T : Finset G} {r₀ : ℕ} {κ ε : ℝ} {g : G}
    (hg : r₀ < WordMetric.wordNorm (↑T : Set G) g) :
    diagBound T r₀ κ ε g
      = Real.exp (-(κ * (WordMetric.wordNorm (↑T : Set G) g : ℝ) ^ (1 + ε))) := by
  rw [diagBound, if_neg (by omega)]

omit [DecidableEq G] [InnerProductSpace ℝ E] in
/-- **The diagonal estimate.**  Compression above `1/2` bounds the `g`-th
diagonal of the inverted Gaussian kernel by `exp(-κ|g|^{1+ε})`, uniformly in
the base point.  Here `1 + ε = 2β`. -/
theorem norm_invGaussianC_diag_le {T : Finset G} {f : G → E} {β : ℝ} {r₀ : ℕ}
    (hr₀ : ∀ x y : G, r₀ ≤ WordMetric.wordDist (↑T : Set G) x y →
      ((WordMetric.wordDist (↑T : Set G) x y : ℝ)) ^ β ≤ ‖f x - f y‖)
    {κ : ℝ} (hκ : 0 ≤ κ) (hr₁ : 1 ≤ r₀) (g s : G) :
    ‖invGaussianC f κ s (g⁻¹ * s)‖ ≤ diagBound T r₀ κ (2 * β - 1) g := by
  have hval : invGaussianC f κ s (g⁻¹ * s)
      = ((gaussianKernel f κ s⁻¹ (s⁻¹ * g) : ℝ) : ℂ) := by
    rw [invGaussianC, invGaussian]
    congr 2
    group
  have hnn : (0 : ℝ) ≤ gaussianKernel f κ s⁻¹ (s⁻¹ * g) :=
    (gaussianKernel_pos f κ _ _).le
  rw [hval, Complex.norm_real, Real.norm_of_nonneg hnn]
  by_cases hg : WordMetric.wordNorm (↑T : Set G) g ≤ r₀
  · rw [diagBound, if_pos hg]
    exact gaussianKernel_le_one hκ f _ _
  · replace hg : r₀ < WordMetric.wordNorm (↑T : Set G) g := by omega
    rw [diagBound_of_lt hg]
    -- the displacement of the `g`-th diagonal is `|g|`, uniformly in `s`
    have hd : WordMetric.wordDist (↑T : Set G) s⁻¹ (s⁻¹ * g)
        = WordMetric.wordNorm (↑T : Set G) g := by
      unfold WordMetric.wordDist
      congr 1
      group
    have hfar : r₀ ≤ WordMetric.wordDist (↑T : Set G) s⁻¹ (s⁻¹ * g) := by
      rw [hd]; omega
    have hlow : ((WordMetric.wordNorm (↑T : Set G) g : ℝ)) ^ β
        ≤ ‖f s⁻¹ - f (s⁻¹ * g)‖ := by
      have h := hr₀ s⁻¹ (s⁻¹ * g) hfar
      rwa [hd] at h
    have hn1 : 1 ≤ WordMetric.wordNorm (↑T : Set G) g := le_trans hr₁ (le_of_lt hg)
    have hn0R : (0 : ℝ) < (WordMetric.wordNorm (↑T : Set G) g : ℝ) := by
      have h : (1 : ℝ) ≤ (WordMetric.wordNorm (↑T : Set G) g : ℝ) := by exact_mod_cast hn1
      linarith
    have hpos : (0 : ℝ) ≤ ((WordMetric.wordNorm (↑T : Set G) g : ℝ)) ^ β :=
      Real.rpow_nonneg hn0R.le _
    have hsq : ((WordMetric.wordNorm (↑T : Set G) g : ℝ)) ^ (1 + (2 * β - 1))
        ≤ ‖f s⁻¹ - f (s⁻¹ * g)‖ ^ 2 := by
      have hmul : (((WordMetric.wordNorm (↑T : Set G) g : ℝ)) ^ β)
            * (((WordMetric.wordNorm (↑T : Set G) g : ℝ)) ^ β)
          ≤ ‖f s⁻¹ - f (s⁻¹ * g)‖ * ‖f s⁻¹ - f (s⁻¹ * g)‖ :=
        mul_self_le_mul_self hpos hlow
      have hadd : ((WordMetric.wordNorm (↑T : Set G) g : ℝ)) ^ (β + β)
          = (((WordMetric.wordNorm (↑T : Set G) g : ℝ)) ^ β)
            * (((WordMetric.wordNorm (↑T : Set G) g : ℝ)) ^ β) :=
        Real.rpow_add hn0R β β
      have hβε : β + β = 1 + (2 * β - 1) := by ring
      rw [pow_two, ← hβε, hadd]
      exact hmul
    rw [gaussianKernel]
    exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hsq hκ])

/-! ## The truncations and their limit -/

/-- The operator of the kernel truncated to the ball of radius `N`. -/
noncomputable def truncOp {T : Finset G}
    (hT : WordMetric.IsSymmetricGeneratingSet (↑T : Set G)) {f : G → E} {β : ℝ}
    {r₀ : ℕ} (hr₀ : ∀ x y : G, r₀ ≤ WordMetric.wordDist (↑T : Set G) x y →
      ((WordMetric.wordDist (↑T : Set G) x y : ℝ)) ^ β ≤ ‖f x - f y‖)
    {κ : ℝ} (hκ : 0 ≤ κ) (hr₁ : 1 ≤ r₀) (N : ℕ) :
    GroupHilbert G →L[ℂ] GroupHilbert G :=
  kernelOp (WordMetric.ballFinset hT N) (invGaussianC f κ)
    (diagBound T r₀ κ (2 * β - 1)) (fun g s ↦ norm_invGaussianC_diag_le hr₀ hκ hr₁ g s)

omit [InnerProductSpace ℝ E] in
theorem matrixCoeff_truncOp {T : Finset G}
    (hT : WordMetric.IsSymmetricGeneratingSet (↑T : Set G)) {f : G → E} {β : ℝ}
    {r₀ : ℕ} (hr₀ : ∀ x y : G, r₀ ≤ WordMetric.wordDist (↑T : Set G) x y →
      ((WordMetric.wordDist (↑T : Set G) x y : ℝ)) ^ β ≤ ‖f x - f y‖)
    {κ : ℝ} (hκ : 0 ≤ κ) (hr₁ : 1 ≤ r₀) (N : ℕ) (s t : G) :
    matrixCoeff G (truncOp hT hr₀ hκ hr₁ N) s t
      = if s * t⁻¹ ∈ WordMetric.ballFinset hT N then invGaussianC f κ s t else 0 :=
  matrixCoeff_kernelOp _ _ _ _ s t

omit [InnerProductSpace ℝ E] in
theorem finitePropagation_truncOp {T : Finset G}
    (hT : WordMetric.IsSymmetricGeneratingSet (↑T : Set G)) {f : G → E} {β : ℝ}
    {r₀ : ℕ} (hr₀ : ∀ x y : G, r₀ ≤ WordMetric.wordDist (↑T : Set G) x y →
      ((WordMetric.wordDist (↑T : Set G) x y : ℝ)) ^ β ≤ ‖f x - f y‖)
    {κ : ℝ} (hκ : 0 ≤ κ) (hr₁ : 1 ≤ r₀) (N : ℕ) :
    FinitePropagation G (truncOp hT hr₀ hκ hr₁ N) :=
  finitePropagation_kernelOp _ _ _ _

omit [InnerProductSpace ℝ E] in
/-- **The Cauchy estimate.**  The difference of two truncations is the operator
of the kernel restricted to the annulus between them, so its norm is bounded by
the tail of the diagonal sums. -/
theorem norm_truncOp_sub_le {T : Finset G}
    (hT : WordMetric.IsSymmetricGeneratingSet (↑T : Set G)) {f : G → E} {β : ℝ}
    {r₀ : ℕ} (hr₀ : ∀ x y : G, r₀ ≤ WordMetric.wordDist (↑T : Set G) x y →
      ((WordMetric.wordDist (↑T : Set G) x y : ℝ)) ^ β ≤ ‖f x - f y‖)
    {κ : ℝ} (hκ : 0 ≤ κ) (hr₁ : 1 ≤ r₀) {N M : ℕ} (hNM : N ≤ M) :
    ‖truncOp hT hr₀ hκ hr₁ M - truncOp hT hr₀ hκ hr₁ N‖
      ≤ ∑ g ∈ WordMetric.ballFinset hT M \ WordMetric.ballFinset hT N,
          diagBound T r₀ κ (2 * β - 1) g := by
  classical
  have hsub : WordMetric.ballFinset hT N ⊆ WordMetric.ballFinset hT M :=
    WordMetric.ballFinset_mono hT hNM
  have hdiff : truncOp hT hr₀ hκ hr₁ M - truncOp hT hr₀ hκ hr₁ N
      = kernelOp (WordMetric.ballFinset hT M \ WordMetric.ballFinset hT N)
          (invGaussianC f κ) (diagBound T r₀ κ (2 * β - 1))
          (fun g s ↦ norm_invGaussianC_diag_le hr₀ hκ hr₁ g s) := by
    rw [truncOp, truncOp, kernelOp, kernelOp, kernelOp]
    exact (Finset.sum_sdiff_eq_sub hsub).symm
  rw [hdiff]
  exact norm_kernelOp_le _ _ _ _

/-! ## The limit -/

omit [Group G] in
theorem norm_delta (t : G) : ‖delta G t‖ = 1 := by
  rw [delta, lp.norm_single (by norm_num)]
  simp

omit [Group G] in
/-- Matrix coefficients are bounded by the operator norm, so they are
continuous in the operator. -/
theorem norm_matrixCoeff_le (A : GroupHilbert G →L[ℂ] GroupHilbert G) (s t : G) :
    ‖matrixCoeff G A s t‖ ≤ ‖A‖ := by
  have h1 : ‖matrixCoeff G A s t‖ ≤ ‖A (delta G t)‖ := by
    rw [matrixCoeff_def]
    exact lp.norm_apply_le_norm (by norm_num) _ _
  have h2 : ‖A (delta G t)‖ ≤ ‖A‖ * ‖delta G t‖ := A.le_opNorm _
  rw [norm_delta, mul_one] at h2
  exact le_trans h1 h2

omit [Group G] in
theorem continuous_matrixCoeff (s t : G) :
    Continuous (fun A : GroupHilbert G →L[ℂ] GroupHilbert G ↦ matrixCoeff G A s t) :=
  (lp.evalCLM ℂ (fun _ : G ↦ ℂ) 2 s).continuous.comp
    (ContinuousLinearMap.apply ℂ (GroupHilbert G) (delta G t)).continuous

omit [InnerProductSpace ℝ E] in
/-- **The truncations are Cauchy**: their differences are the operators of the
kernel restricted to annuli, and the tail estimate bounds those. -/
theorem cauchySeq_truncOp {T : Finset G}
    (hT : WordMetric.IsSymmetricGeneratingSet (↑T : Set G)) {f : G → E} {β : ℝ}
    (hβ : 1 / 2 < β) {r₀ : ℕ}
    (hr₀ : ∀ x y : G, r₀ ≤ WordMetric.wordDist (↑T : Set G) x y →
      ((WordMetric.wordDist (↑T : Set G) x y : ℝ)) ^ β ≤ ‖f x - f y‖)
    {κ : ℝ} (hκ : 0 < κ) (hr₁ : 1 ≤ r₀) :
    CauchySeq (fun N ↦ truncOp hT hr₀ hκ.le hr₁ N) := by
  have hε : (0 : ℝ) < 2 * β - 1 := by linarith
  rw [Metric.cauchySeq_iff']
  intro δ hδ
  obtain ⟨N₁, hN₁⟩ := exists_tail_bound_norm hT hε hκ (half_pos hδ)
  refine ⟨max N₁ r₀, ?_⟩
  intro M hM
  rw [dist_eq_norm]
  refine lt_of_le_of_lt (norm_truncOp_sub_le hT hr₀ hκ.le hr₁ hM) ?_
  have hout : ∀ g ∈ WordMetric.ballFinset hT M \ WordMetric.ballFinset hT (max N₁ r₀),
      max N₁ r₀ < WordMetric.wordNorm (↑T : Set G) g := by
    intro g hg
    have h := (Finset.mem_sdiff.mp hg).2
    rw [WordMetric.mem_ballFinset] at h
    omega
  have heq : ∀ g ∈ WordMetric.ballFinset hT M \ WordMetric.ballFinset hT (max N₁ r₀),
      diagBound T r₀ κ (2 * β - 1) g
        = Real.exp (-(κ * (WordMetric.wordNorm (↑T : Set G) g : ℝ) ^ (1 + (2 * β - 1)))) :=
    fun g hg ↦ diagBound_of_lt (lt_of_le_of_lt (le_max_right N₁ r₀) (hout g hg))
  rw [Finset.sum_congr rfl heq]
  refine lt_of_le_of_lt (hN₁ _ fun g hg ↦ lt_of_le_of_lt (le_max_left N₁ r₀) (hout g hg)) ?_
  linarith

omit [InnerProductSpace ℝ E] in
/-- **The Gaussian kernel is the matrix of an element of the uniform Roe
algebra.**  This is step 1 of Guentner--Kaminker's Lemma 3.5, proved without a
Schur test. -/
theorem exists_roeOperator {T : Finset G}
    (hT : WordMetric.IsSymmetricGeneratingSet (↑T : Set G)) {f : G → E} {β : ℝ}
    (hβ : 1 / 2 < β) {r₀ : ℕ}
    (hr₀ : ∀ x y : G, r₀ ≤ WordMetric.wordDist (↑T : Set G) x y →
      ((WordMetric.wordDist (↑T : Set G) x y : ℝ)) ^ β ≤ ‖f x - f y‖)
    {κ : ℝ} (hκ : 0 < κ) (hr₁ : 1 ≤ r₀) :
    ∃ K : GroupHilbert G →L[ℂ] GroupHilbert G,
      K ∈ uniformRoeSubalgebra G ∧
        ∀ s t : G, matrixCoeff G K s t = invGaussianC f κ s t := by
  obtain ⟨K, hK⟩ := cauchySeq_tendsto_of_complete (cauchySeq_truncOp hT hβ hr₀ hκ hr₁)
  refine ⟨K, ?_, ?_⟩
  · refine mem_closure_of_tendsto hK ?_
    filter_upwards with N
    exact finitePropagation_truncOp hT hr₀ hκ.le hr₁ N
  · intro s t
    have hcont : Filter.Tendsto
        (fun N ↦ matrixCoeff G (truncOp hT hr₀ hκ.le hr₁ N) s t) Filter.atTop
        (nhds (matrixCoeff G K s t)) :=
      ((continuous_matrixCoeff s t).tendsto K).comp hK
    have heventually : ∀ᶠ N in Filter.atTop,
        invGaussianC f κ s t = matrixCoeff G (truncOp hT hr₀ hκ.le hr₁ N) s t := by
      filter_upwards [Filter.eventually_ge_atTop
        (WordMetric.wordNorm (↑T : Set G) (s * t⁻¹))] with N hN
      symm
      rw [matrixCoeff_truncOp, if_pos]
      rw [WordMetric.mem_ballFinset]
      exact hN
    exact tendsto_nhds_unique hcont
      (Filter.Tendsto.congr' heventually tendsto_const_nhds)

/-! ## Positivity

Guentner--Kaminker need `Op(u)` to be a *positive* element of `C*_u(Γ)`; that is
what makes its square root available.  Positivity is exactly positive type of
the kernel, transported through the dense span of the point masses. -/

omit [Group G] in
/-- The quadratic form of an operator at a finite combination of point masses,
read off its matrix. -/
theorem inner_apply_span (A : GroupHilbert G →L[ℂ] GroupHilbert G) (F : Finset G)
    (c : G → ℂ) :
    ⟪A (∑ i ∈ F, c i • delta G i), ∑ j ∈ F, c j • delta G j⟫_ℂ
      = ∑ i ∈ F, ∑ j ∈ F,
          (starRingEnd ℂ) (c i) * c j * (starRingEnd ℂ) (matrixCoeff G A j i) := by
  have hA : A (∑ i ∈ F, c i • delta G i) = ∑ i ∈ F, c i • A (delta G i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ A.map_smul _ _
  rw [hA, sum_inner]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [inner_smul_left, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [inner_smul_right]
  have hij : ⟪A (delta G i), delta G j⟫_ℂ
      = (starRingEnd ℂ) (matrixCoeff G A j i) := by
    rw [matrixCoeff_def, coord_eq_inner G (A (delta G i)) j]
    exact (inner_conj_symm _ _).symm
  rw [hij]
  ring

omit  in
/-- **The Roe operator of a real symmetric kernel of positive type is
positive.**  Self-adjointness is symmetry of the kernel, read through
`matrixCoeff_star`; the quadratic form is nonnegative on the span of the point
masses by positive type, and the span is dense while the form is continuous. -/
omit [Group G] in
theorem isPositive_of_kernel {A : GroupHilbert G →L[ℂ] GroupHilbert G}
    {u : G → G → ℝ} (hu : IsPositiveDefiniteKernel u) (hsymm : ∀ s t, u s t = u t s)
    (hcoeff : ∀ s t, matrixCoeff G A s t = ((u s t : ℝ) : ℂ)) :
    A.IsPositive := by
  classical
  have hsa : IsSelfAdjoint A := by
    refine ext_of_matrixCoeff fun s t ↦ ?_
    rw [matrixCoeff_star, hcoeff t s, hcoeff s t, hsymm t s, Complex.conj_ofReal]
  refine ⟨ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa, ?_⟩
  have hcont : Continuous fun w : GroupHilbert G ↦ A.reApplyInnerSelf w :=
    RCLike.continuous_re.comp (A.continuous.inner continuous_id)
  have hclosed : IsClosed {w : GroupHilbert G | 0 ≤ A.reApplyInnerSelf w} :=
    isClosed_le continuous_const hcont
  have hspan : (Submodule.span ℂ (Set.range (delta G)) : Set (GroupHilbert G))
      ⊆ {w : GroupHilbert G | 0 ≤ A.reApplyInnerSelf w} := by
    intro w hw
    obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hw
    show 0 ≤ RCLike.re (⟪A _, _⟫_ℂ)
    rw [Finsupp.sum, inner_apply_span A c.support fun i ↦ c i]
    have hrw : ∀ i ∈ c.support, ∀ j ∈ c.support,
        (starRingEnd ℂ) (c i) * c j * (starRingEnd ℂ) (matrixCoeff G A j i)
          = (starRingEnd ℂ) (c i) * c j * ((u i j : ℝ) : ℂ) := by
      intro i _ j _
      rw [hcoeff j i, Complex.conj_ofReal, hsymm j i]
    rw [Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ hrw i hi j hj]
    exact hu.finset_complex_re c.support fun i ↦ c i
  intro v
  exact hclosed.closure_subset_iff.mpr hspan (dense_span_delta v)

/-- **The Gaussian kernel is the matrix of a positive element of the uniform Roe
algebra.**  This is the whole of step 1 of Guentner--Kaminker's Lemma 3.5, with
no Schur test and no hypothesis beyond compression above `1/2`. -/
theorem exists_positive_roeOperator {T : Finset G}
    (hT : WordMetric.IsSymmetricGeneratingSet (↑T : Set G)) {f : G → E} {β : ℝ}
    (hβ : 1 / 2 < β) {r₀ : ℕ}
    (hr₀ : ∀ x y : G, r₀ ≤ WordMetric.wordDist (↑T : Set G) x y →
      ((WordMetric.wordDist (↑T : Set G) x y : ℝ)) ^ β ≤ ‖f x - f y‖)
    {κ : ℝ} (hκ : 0 < κ) (hr₁ : 1 ≤ r₀) :
    ∃ K : GroupHilbert G →L[ℂ] GroupHilbert G,
      K ∈ uniformRoeSubalgebra G ∧ K.IsPositive ∧
        ∀ s t : G, matrixCoeff G K s t = ((invGaussian f κ s t : ℝ) : ℂ) := by
  obtain ⟨K, hmem, hcoeff⟩ := exists_roeOperator hT hβ hr₀ hκ hr₁
  refine ⟨K, hmem, ?_, hcoeff⟩
  exact isPositive_of_kernel (invGaussian_isPositiveDefinite f hκ.le)
    (invGaussian_comm f κ) hcoeff

end GaussianRoeOperator
end GroupApproximation
