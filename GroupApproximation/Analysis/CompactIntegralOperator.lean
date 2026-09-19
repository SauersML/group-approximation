import GroupApproximation.Analysis.CompactHaar
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Integral operators on a compact target

Step one of the route recorded in `Analysis/CompactHaar`: the convolution-type
operator, built so that the analysis stays inside what Mathlib already proves.

For `φ : C(C, ℂ)` the operator is

  `T_φ f x = ⟪k_φ x, f⟫`,   `k_φ x y = conj (φ (x⁻¹ * y))`,

which is the `L²` pairing form of `∫ φ (x⁻¹ y) f y`.  Writing it as a pairing
rather than an integral is what keeps the side conditions cheap: `k_φ` is
continuous on `C × C`, so currying gives a *continuous* map `x ↦ k_φ x` into
`C(C, ℂ)` with no uniform-continuity argument, and `ContinuousMap.toLp` carries
it into `L²` as a continuous linear map of norm at most one, Haar being a
probability measure.

`T_φ f` is then continuous in `x`, hence bounded on a compact space, hence back
in `L²` -- and the same bound `‖T_φ f‖₂ ≤ ‖φ‖_∞ ‖f‖₂` comes out of
Cauchy--Schwarz with nothing else assumed.
-/

namespace GroupApproximation
namespace PeterWeyl

open MeasureTheory Measure Complex
open scoped InnerProductSpace Pointwise

variable (C : CompactTarget)

/-- Complex conjugation as a continuous map. -/
noncomputable def conjCM : C(ℂ, ℂ) := ⟨starRingEnd ℂ, continuous_star⟩

/-- The conjugated kernel, curried: `x ↦ (y ↦ conj (k (x, y)))`.  Currying needs
the second factor locally compact, which a compact Hausdorff group is. -/
noncomputable def kernelCurried (k : C(C.carrier × C.carrier, ℂ)) :
    C(C.carrier, C(C.carrier, ℂ)) :=
  (conjCM.comp k).curry

/-- The kernel slice at `x`, as an element of `L²`.  Pairing against it computes
`∫ k x y * f y`, the conjugation in `kernelCurried` cancelling the one in the
inner product. -/
noncomputable def kernelL2 (k : C(C.carrier × C.carrier, ℂ)) (x : C.carrier) :
    Lp ℂ 2 C.haar :=
  ContinuousMap.toLp (E := ℂ) 2 C.haar ℂ (kernelCurried C k x)

/-- **The kernel slice varies continuously in `L²`.**  Currying supplies
continuity into `C(C, ℂ)` and `ContinuousMap.toLp` is continuous, so no
uniform-continuity argument is needed. -/
theorem continuous_kernelL2 (k : C(C.carrier × C.carrier, ℂ)) :
    Continuous (kernelL2 C k) :=
  (ContinuousMap.toLp (E := ℂ) 2 C.haar ℂ).continuous.comp
    (kernelCurried C k).continuous


/-- Haar on a compact target has total NNReal mass one. -/
@[simp] theorem measureUnivNNReal_haar : measureUnivNNReal C.haar = 1 := by
  simp [measureUnivNNReal, C.haar_univ]

/-- `ContinuousMap.toLp` into `L²` of a probability measure is a contraction. -/
theorem toLp_opNorm_le_one :
    ‖(ContinuousMap.toLp (E := ℂ) 2 C.haar ℂ)‖ ≤ 1 := by
  refine le_trans (ContinuousMap.toLp_norm_le C.haar) ?_
  simp

/-- The kernel slice is bounded by the sup norm of `φ`. -/
theorem norm_kernelL2_le (k : C(C.carrier × C.carrier, ℂ)) (x : C.carrier) :
    ‖kernelL2 C k x‖ ≤ ‖k‖ := by
  have h3 : ‖kernelCurried C k x‖ ≤ ‖k‖ := by
    refine (ContinuousMap.norm_le _ (norm_nonneg _)).mpr fun y => ?_
    have hval : ‖(kernelCurried C k x) y‖ = ‖k (x, y)‖ := by
      simp [kernelCurried, conjCM]
    rw [hval]
    exact k.norm_coe_le_norm _
  calc ‖kernelL2 C k x‖
      ≤ ‖(ContinuousMap.toLp (E := ℂ) 2 C.haar ℂ)‖ * ‖kernelCurried C k x‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖k‖ :=
        mul_le_mul (toLp_opNorm_le_one C) h3 (norm_nonneg _) zero_le_one
    _ = ‖k‖ := one_mul _


/-! ## The operator -/

/-- `T_φ f` as a continuous function of `x`: the `L²` pairing of `f` against the
kernel slice. -/
noncomputable def applyCM (k : C(C.carrier × C.carrier, ℂ)) (f : Lp ℂ 2 C.haar) :
    C(C.carrier, ℂ) :=
  ⟨fun x => ⟪kernelL2 C k x, f⟫_ℂ,
    continuous_inner.comp ((continuous_kernelL2 C k).prodMk continuous_const)⟩

@[simp] theorem applyCM_apply (k : C(C.carrier × C.carrier, ℂ)) (f : Lp ℂ 2 C.haar)
    (x : C.carrier) : applyCM C k f x = ⟪kernelL2 C k x, f⟫_ℂ := rfl

theorem norm_applyCM_le (k : C(C.carrier × C.carrier, ℂ)) (f : Lp ℂ 2 C.haar) :
    ‖applyCM C k f‖ ≤ ‖k‖ * ‖f‖ := by
  refine (ContinuousMap.norm_le _ (by positivity)).mpr fun x => ?_
  have hcs : ‖(⟪kernelL2 C k x, f⟫_ℂ : ℂ)‖ ≤ ‖kernelL2 C k x‖ * ‖f‖ := by
    simpa using norm_inner_le_norm (𝕜 := ℂ) (kernelL2 C k x) f
  have hx : applyCM C k f x = ⟪kernelL2 C k x, f⟫_ℂ := rfl
  rw [hx]
  exact hcs.trans (mul_le_mul_of_nonneg_right (norm_kernelL2_le C k x) (norm_nonneg _))

/-- **The integral operator.**  Bounded by the sup norm of `φ`, with no
hypothesis: Haar is a probability measure, so both `ContinuousMap.toLp` and the
Cauchy--Schwarz step are contractions. -/
noncomputable def integralOp (k : C(C.carrier × C.carrier, ℂ)) :
    Lp ℂ 2 C.haar →L[ℂ] Lp ℂ 2 C.haar :=
  LinearMap.mkContinuous
    { toFun := fun f => ContinuousMap.toLp (E := ℂ) 2 C.haar ℂ (applyCM C k f)
      map_add' := by
        intro f g
        have h : applyCM C k (f + g) = applyCM C k f + applyCM C k g := by
          ext x; simp [inner_add_right]
        rw [h, map_add]
      map_smul' := by
        intro a f
        have h : applyCM C k (a • f) = a • applyCM C k f := by
          ext x; simp [inner_smul_right]
        rw [h, map_smul]
        rfl }
    ‖k‖
    (by
      intro f
      calc ‖ContinuousMap.toLp (E := ℂ) 2 C.haar ℂ (applyCM C k f)‖
          ≤ ‖(ContinuousMap.toLp (E := ℂ) 2 C.haar ℂ)‖ * ‖applyCM C k f‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * (‖k‖ * ‖f‖) :=
            mul_le_mul (toLp_opNorm_le_one C) (norm_applyCM_le C k f)
              (norm_nonneg _) zero_le_one
        _ = ‖k‖ * ‖f‖ := one_mul _)

theorem integralOp_apply (k : C(C.carrier × C.carrier, ℂ)) (f : Lp ℂ 2 C.haar) :
    integralOp C k f = ContinuousMap.toLp (E := ℂ) 2 C.haar ℂ (applyCM C k f) :=
  rfl


/-! ## Dependence on the kernel

The two conjugations cancel, so `k ↦ T_k` is linear, and the sup-norm bound makes
it Lipschitz.  That is exactly what lets a uniform approximation of the kernel
become a norm approximation of the operator.
-/

theorem kernelCurried_sub (k₁ k₂ : C(C.carrier × C.carrier, ℂ)) (x : C.carrier) :
    kernelCurried C (k₁ - k₂) x = kernelCurried C k₁ x - kernelCurried C k₂ x := by
  ext y; simp [kernelCurried, conjCM]

theorem kernelL2_sub (k₁ k₂ : C(C.carrier × C.carrier, ℂ)) (x : C.carrier) :
    kernelL2 C (k₁ - k₂) x = kernelL2 C k₁ x - kernelL2 C k₂ x := by
  rw [kernelL2, kernelCurried_sub, map_sub]
  rfl

theorem applyCM_sub (k₁ k₂ : C(C.carrier × C.carrier, ℂ)) (f : Lp ℂ 2 C.haar) :
    applyCM C (k₁ - k₂) f = applyCM C k₁ f - applyCM C k₂ f := by
  ext x
  simp [applyCM_apply, kernelL2_sub, inner_sub_left]

theorem integralOp_sub (k₁ k₂ : C(C.carrier × C.carrier, ℂ)) :
    integralOp C (k₁ - k₂) = integralOp C k₁ - integralOp C k₂ := by
  ext f
  simp [integralOp_apply, applyCM_sub, map_sub]

/-- The operator norm is bounded by the sup norm of the kernel. -/
theorem norm_integralOp_le (k : C(C.carrier × C.carrier, ℂ)) :
    ‖integralOp C k‖ ≤ ‖k‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

/-- **Uniform convergence of kernels gives norm convergence of operators.** -/
theorem norm_integralOp_sub_le (k₁ k₂ : C(C.carrier × C.carrier, ℂ)) :
    ‖integralOp C k₁ - integralOp C k₂‖ ≤ ‖k₁ - k₂‖ := by
  rw [← integralOp_sub]
  exact norm_integralOp_le C _


/-! ## Elementary kernels give rank-one operators

`k (x, y) = f₀ x * g₀ y` makes `T_k f = ⟪w, f⟫ • f₀` with `w` the `L²` class of
`conj ∘ g₀`, so the range lies in a line.  Rank-one operators are compact by the
ball criterion, the image of the unit ball landing in a dilate of a single
vector by a bounded scalar.
-/

/-- The elementary kernel `(x, y) ↦ f₀ x * g₀ y`. -/
noncomputable def elemKernel (f₀ g₀ : C(C.carrier, ℂ)) :
    C(C.carrier × C.carrier, ℂ) :=
  ⟨fun p => f₀ p.1 * g₀ p.2,
    (f₀.continuous.comp continuous_fst).mul (g₀.continuous.comp continuous_snd)⟩

/-- The `L²` vector an elementary kernel pairs against. -/
noncomputable def elemVec (g₀ : C(C.carrier, ℂ)) : Lp ℂ 2 C.haar :=
  ContinuousMap.toLp (E := ℂ) 2 C.haar ℂ (conjCM.comp g₀)

theorem kernelL2_elemKernel (f₀ g₀ : C(C.carrier, ℂ)) (x : C.carrier) :
    kernelL2 C (elemKernel C f₀ g₀) x
      = (starRingEnd ℂ) (f₀ x) • elemVec C g₀ := by
  have h : kernelCurried C (elemKernel C f₀ g₀) x
      = (starRingEnd ℂ) (f₀ x) • (conjCM.comp g₀) := by
    ext y; simp [kernelCurried, conjCM, elemKernel]
  rw [kernelL2, h, map_smul]
  rfl

theorem applyCM_elemKernel (f₀ g₀ : C(C.carrier, ℂ)) (f : Lp ℂ 2 C.haar) :
    applyCM C (elemKernel C f₀ g₀) f = ⟪elemVec C g₀, f⟫_ℂ • f₀ := by
  ext x
  rw [applyCM_apply, kernelL2_elemKernel, inner_smul_left]
  simp [mul_comm]

theorem integralOp_elemKernel (f₀ g₀ : C(C.carrier, ℂ)) (f : Lp ℂ 2 C.haar) :
    integralOp C (elemKernel C f₀ g₀) f
      = ⟪elemVec C g₀, f⟫_ℂ • ContinuousMap.toLp (E := ℂ) 2 C.haar ℂ f₀ := by
  rw [integralOp_apply, applyCM_elemKernel, map_smul]

/-- **Rank-one operators built from an inner product are compact.** -/
theorem isCompactOperator_elemKernel (f₀ g₀ : C(C.carrier, ℂ)) :
    IsCompactOperator (integralOp C (elemKernel C f₀ g₀)) := by
  set w := elemVec C g₀ with hw
  set v := ContinuousMap.toLp (E := ℂ) 2 C.haar ℂ f₀ with hv
  have key : IsCompactOperator
      ((integralOp C (elemKernel C f₀ g₀)).toLinearMap) := by
    refine (isCompactOperator_iff_image_ball_subset_compact
      (integralOp C (elemKernel C f₀ g₀)).toLinearMap one_pos).mpr ?_
    refine ⟨(fun c : ℂ => c • v) '' Metric.closedBall 0 ‖w‖,
      (isCompact_closedBall _ _).image (continuous_id.smul continuous_const), ?_⟩
    rintro _ ⟨f, hf, rfl⟩
    refine ⟨⟪w, f⟫_ℂ, ?_, ?_⟩
    · have hfle : ‖f‖ ≤ 1 := le_of_lt (by simpa using Metric.mem_ball.mp hf)
      have hcs : ‖(⟪w, f⟫_ℂ : ℂ)‖ ≤ ‖w‖ * ‖f‖ := by
        simpa using norm_inner_le_norm (𝕜 := ℂ) w f
      simpa using hcs.trans (by
        simpa using mul_le_mul_of_nonneg_left hfle (norm_nonneg w))
    · simpa [hw, hv] using (integralOp_elemKernel C f₀ g₀ f).symm
  exact key


/-! ## Compactness for every continuous kernel

The kernels whose operator is compact form a closed set, by the Lipschitz bound
of `norm_integralOp_sub_le` together with `isCompactOperator_of_tendsto`.  With
the elementary kernels inside it, Stone--Weierstrass will finish the job.
-/

theorem kernelCurried_add (k₁ k₂ : C(C.carrier × C.carrier, ℂ)) (x : C.carrier) :
    kernelCurried C (k₁ + k₂) x = kernelCurried C k₁ x + kernelCurried C k₂ x := by
  ext y; simp [kernelCurried, conjCM]

theorem kernelL2_add (k₁ k₂ : C(C.carrier × C.carrier, ℂ)) (x : C.carrier) :
    kernelL2 C (k₁ + k₂) x = kernelL2 C k₁ x + kernelL2 C k₂ x := by
  rw [kernelL2, kernelCurried_add, map_add]
  rfl

theorem integralOp_add (k₁ k₂ : C(C.carrier × C.carrier, ℂ)) :
    integralOp C (k₁ + k₂) = integralOp C k₁ + integralOp C k₂ := by
  ext f
  have h : applyCM C (k₁ + k₂) f = applyCM C k₁ f + applyCM C k₂ f := by
    ext x; simp [applyCM_apply, kernelL2_add, inner_add_left]
  simp [integralOp_apply, h, map_add]

/-- **The compact-kernel set is closed.** -/
theorem isClosed_compactKernels :
    IsClosed {k : C(C.carrier × C.carrier, ℂ) | IsCompactOperator (integralOp C k)} := by
  refine IsSeqClosed.isClosed ?_
  intro kn k hmem hlim
  have h1 : Filter.Tendsto (fun n => ‖kn n - k‖) Filter.atTop (nhds 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hlim
  have h2 : Filter.Tendsto (fun n => ‖integralOp C (kn n) - integralOp C k‖)
      Filter.atTop (nhds 0) :=
    squeeze_zero (fun n => norm_nonneg _)
      (fun n => norm_integralOp_sub_le C (kn n) k) h1
  exact isCompactOperator_of_tendsto
    (tendsto_iff_norm_sub_tendsto_zero.mpr h2) (Filter.Eventually.of_forall hmem)


/-! ## The algebra of elementary kernels

Elementary kernels are closed under product and star and contain `1`, so their
span is a star-subalgebra.  It separates the points of `C × C` because
continuous functions separate the points of a compact Hausdorff space, and
Stone--Weierstrass then makes it dense.
-/

/-- The set of elementary kernels. -/
def elemSet : Set C(C.carrier × C.carrier, ℂ) :=
  {k | ∃ f₀ g₀ : C(C.carrier, ℂ), k = elemKernel C f₀ g₀}

theorem elemKernel_mem (f₀ g₀ : C(C.carrier, ℂ)) : elemKernel C f₀ g₀ ∈ elemSet C :=
  ⟨f₀, g₀, rfl⟩

theorem one_mem_elemSet : (1 : C(C.carrier × C.carrier, ℂ)) ∈ elemSet C :=
  ⟨1, 1, by ext p; simp [elemKernel]⟩

theorem elemSet_mul_subset : elemSet C * elemSet C ⊆ elemSet C := by
  rintro _ ⟨_, ⟨f₁, g₁, rfl⟩, _, ⟨f₂, g₂, rfl⟩, rfl⟩
  exact ⟨f₁ * f₂, g₁ * g₂, by ext p; simp [elemKernel]; ring⟩

theorem elemSet_star (k : C(C.carrier × C.carrier, ℂ)) (hk : k ∈ elemSet C) :
    star k ∈ elemSet C := by
  obtain ⟨f₀, g₀, rfl⟩ := hk
  exact ⟨star f₀, star g₀, by ext p; simp [elemKernel]⟩

/-- The span of the elementary kernels, as a star-subalgebra. -/
noncomputable def elemAlg : StarSubalgebra ℂ C(C.carrier × C.carrier, ℂ) where
  carrier := (Submodule.span ℂ (elemSet C) : Set C(C.carrier × C.carrier, ℂ))
  mul_mem' := by
    intro a b ha hb
    have h : a * b ∈ Submodule.span ℂ (elemSet C) * Submodule.span ℂ (elemSet C) :=
      Submodule.mul_mem_mul ha hb
    rw [Submodule.span_mul_span] at h
    exact Submodule.span_le.mpr
      (fun x hx => Submodule.subset_span (elemSet_mul_subset C hx)) h
  one_mem' := Submodule.subset_span (one_mem_elemSet C)
  add_mem' := fun ha hb => Submodule.add_mem _ ha hb
  zero_mem' := Submodule.zero_mem _
  algebraMap_mem' := by
    intro r
    have h : (algebraMap ℂ C(C.carrier × C.carrier, ℂ)) r
        = r • (1 : C(C.carrier × C.carrier, ℂ)) := by
      ext p; simp [Algebra.algebraMap_eq_smul_one]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (one_mem_elemSet C))
  star_mem' := by
    intro a ha
    refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
    · intro x hx
      exact Submodule.subset_span (elemSet_star C x hx)
    · simp
    · intro x y _ _ hx hy
      simpa [star_add] using Submodule.add_mem _ hx hy
    · intro r x _ hx
      simpa [star_smul] using Submodule.smul_mem _ (starRingEnd ℂ r) hx

@[simp] theorem elemAlg_coe :
    (elemAlg C : Set C(C.carrier × C.carrier, ℂ))
      = (Submodule.span ℂ (elemSet C) : Set C(C.carrier × C.carrier, ℂ)) := rfl


/-! ## Compactness on the span -/

theorem kernelCurried_smul (r : ℂ) (k : C(C.carrier × C.carrier, ℂ)) (x : C.carrier) :
    kernelCurried C (r • k) x = (starRingEnd ℂ) r • kernelCurried C k x := by
  ext y; simp [kernelCurried, conjCM]

theorem kernelL2_smul (r : ℂ) (k : C(C.carrier × C.carrier, ℂ)) (x : C.carrier) :
    kernelL2 C (r • k) x = (starRingEnd ℂ) r • kernelL2 C k x := by
  rw [kernelL2, kernelCurried_smul, map_smul]
  rfl

theorem integralOp_smul (r : ℂ) (k : C(C.carrier × C.carrier, ℂ)) :
    integralOp C (r • k) = r • integralOp C k := by
  ext f
  have h : applyCM C (r • k) f = r • applyCM C k f := by
    ext x
    rw [applyCM_apply, kernelL2_smul, inner_smul_left]
    simp
  simp [integralOp_apply, h, map_smul]

theorem integralOp_zero : integralOp C 0 = 0 := by
  have h : (0 : C(C.carrier × C.carrier, ℂ)) = (0 : ℂ) • 0 := by simp
  rw [h, integralOp_smul]
  simp

/-- **Every kernel in the span of the elementary ones gives a compact operator.**
Finite sums and scalar multiples of rank-one operators. -/
theorem isCompactOperator_of_mem_elemAlg {k : C(C.carrier × C.carrier, ℂ)}
    (hk : k ∈ elemAlg C) : IsCompactOperator (integralOp C k) := by
  have hk' : k ∈ Submodule.span ℂ (elemSet C) := hk
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hk'
  · rintro x ⟨f₀, g₀, rfl⟩
    exact isCompactOperator_elemKernel C f₀ g₀
  · rw [integralOp_zero]
    change IsCompactOperator
      (fun _ : Lp ℂ 2 C.haar ↦ (0 : Lp ℂ 2 C.haar))
    exact isCompactOperator_zero
  · intro x y _ _ hx hy
    rw [integralOp_add]
    exact hx.add hy
  · intro r x _ hx
    rw [integralOp_smul]
    exact hx.smul r

end PeterWeyl
end GroupApproximation
