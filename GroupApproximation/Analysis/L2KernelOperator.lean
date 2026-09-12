import GroupApproximation.Analysis.UniformRoeAlgebra

/-!
# Finite-propagation operators from finite-width kernels

Guentner--Kaminker's Lemma 3.5 needs `Op(u)` --- the operator on `ℓ²(Γ)` with
matrix `u` --- to be an element of the uniform Roe algebra.  Mathlib has no
Schur test, and building one directly on `lp` is a substantial piece of
analysis.  This module takes the cheaper road, available because the kernels in
question have *finite width*:

> a kernel supported in `{(s,t) : s t⁻¹ ∈ S}` with `S` finite is a **finite sum
> of multiplication operators composed with translations**,
> `Op(k) = Σ_{g ∈ S} M_{a_g} λ_g` with `a_g(s) = k(s, g⁻¹ s)`,

because `t = g⁻¹ s` is the unique point of the `g`-diagonal above `s`.  Both
factors are elementary: `λ_g` is the left regular unitary, which
`Analysis/ReducedGroupCStarTrace.lean` already supplies, and `M_a` is
multiplication by a bounded family, built here.  The norm bound

```
    ‖Op(k)‖ ≤ Σ_{g ∈ S} ‖a_g‖_∞
```

is then just the triangle inequality, and it is exactly the bound the Gaussian
tail estimate of `Analysis/CoarseCompression.lean` controls.

## Why the propagation convention is `s * t⁻¹`

That is `UniformRoeAlgebra`'s convention, and it is the one that makes the
decomposition work: with `g = s t⁻¹` the translation appearing is `λ_g`, and
the sup over `s` of `|k(s, g⁻¹ s)|` is a sup over a *right*-invariant
displacement, `d(s, g⁻¹s) = |s (g⁻¹ s)⁻¹| = |g|`.  With the other convention
the displacement would be `|s⁻¹ g⁻¹ s|`, a conjugate, whose infimum over `s`
does not grow with `|g|` --- and the norm bound would diverge.  This is why
`Analysis/CoarseCompression.lean` states its geometric hypotheses against the
right-invariant word metric.

## Statements

* `mulOp` --- multiplication by a bounded family, as a bounded operator, with
  `mulOp_apply` and `norm_mulOp_le`;
* `kernelOp` --- `Op(k)` for a kernel of width `S`;
* `matrixCoeff_kernelOp` --- its matrix is `k` on the window and `0` off it;
* `hasPropagationIn_kernelOp` --- it has propagation in `S`;
* `norm_kernelOp_le` --- the `ℓ¹`-over-the-window norm bound.
-/

namespace GroupApproximation
namespace L2KernelOperator

open ReducedGroupCStarTrace UniformRoe

universe u

/-! ## Multiplication by a bounded family

Stated for an arbitrary index type: neither the group structure nor decidable
equality plays any role in multiplication. -/

section Mult

variable {α : Type u}

private theorem toReal_two : ((2 : ENNReal)).toReal = 2 := by
  norm_num

private theorem toReal_two_pos : (0 : ℝ) < ((2 : ENNReal)).toReal := by
  rw [toReal_two]; norm_num

/-- A bounded family multiplies `ℓ²` into `ℓ²`. -/
theorem memℓp_mul {a : α → ℂ} {M : ℝ} (hM : 0 ≤ M) (ha : ∀ s, ‖a s‖ ≤ M)
    (v : lp (fun _ : α ↦ ℂ) 2) :
    Memℓp (fun s : α ↦ a s * v s) 2 := by
  have hv : Summable (fun s : α ↦ ‖v s‖ ^ ((2 : ENNReal)).toReal) :=
    v.2.summable toReal_two_pos
  refine memℓp_gen (Summable.of_nonneg_of_le (fun s ↦ ?_) (fun s ↦ ?_)
    (hv.mul_left (M ^ ((2 : ENNReal)).toReal)))
  · positivity
  · have h1 : ‖a s * v s‖ = ‖a s‖ * ‖v s‖ := norm_mul _ _
    rw [h1]
    calc (‖a s‖ * ‖v s‖) ^ ((2 : ENNReal)).toReal
        ≤ (M * ‖v s‖) ^ ((2 : ENNReal)).toReal :=
          Real.rpow_le_rpow (by positivity)
            (mul_le_mul_of_nonneg_right (ha s) (norm_nonneg _)) toReal_two_pos.le
      _ = M ^ ((2 : ENNReal)).toReal * ‖v s‖ ^ ((2 : ENNReal)).toReal :=
          Real.mul_rpow hM (norm_nonneg _)

/-- Multiplication by a bounded family, as a linear map on `ℓ²(G)`. -/
noncomputable def mulLinear (a : α → ℂ) (M : ℝ) (hM : 0 ≤ M) (ha : ∀ s, ‖a s‖ ≤ M) :
    lp (fun _ : α ↦ ℂ) 2 →ₗ[ℂ] lp (fun _ : α ↦ ℂ) 2 where
  toFun v := ⟨fun s ↦ a s * v s, memℓp_mul hM ha v⟩
  map_add' v w := by
    refine lp.ext (funext fun s ↦ ?_)
    simp [mul_add]
  map_smul' c v := by
    refine lp.ext (funext fun s ↦ ?_)
    simp [smul_eq_mul]
    ring

@[simp] theorem mulLinear_apply (a : α → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (ha : ∀ s, ‖a s‖ ≤ M) (v : lp (fun _ : α ↦ ℂ) 2) (s : α) :
    mulLinear a M hM ha v s = a s * v s := rfl

theorem norm_mulLinear_le (a : α → ℂ) (M : ℝ) (hM : 0 ≤ M) (ha : ∀ s, ‖a s‖ ≤ M)
    (v : lp (fun _ : α ↦ ℂ) 2) : ‖mulLinear a M hM ha v‖ ≤ M * ‖v‖ := by
  have hv : Summable (fun s : α ↦ ‖v s‖ ^ ((2 : ENNReal)).toReal) :=
    v.2.summable toReal_two_pos
  have hw : Summable (fun s : α ↦ ‖(mulLinear a M hM ha v) s‖ ^ ((2 : ENNReal)).toReal) :=
    (mulLinear a M hM ha v).2.summable toReal_two_pos
  have h1 : ‖mulLinear a M hM ha v‖ ^ ((2 : ENNReal)).toReal
      = ∑' s : α, ‖(mulLinear a M hM ha v) s‖ ^ ((2 : ENNReal)).toReal :=
    lp.norm_rpow_eq_tsum toReal_two_pos _
  have h2 : ‖v‖ ^ ((2 : ENNReal)).toReal = ∑' s : α, ‖v s‖ ^ ((2 : ENNReal)).toReal :=
    lp.norm_rpow_eq_tsum toReal_two_pos _
  have hterm : ∀ s : α, ‖(mulLinear a M hM ha v) s‖ ^ ((2 : ENNReal)).toReal
      ≤ M ^ ((2 : ENNReal)).toReal * ‖v s‖ ^ ((2 : ENNReal)).toReal := by
    intro s
    rw [mulLinear_apply, norm_mul]
    calc (‖a s‖ * ‖v s‖) ^ ((2 : ENNReal)).toReal
        ≤ (M * ‖v s‖) ^ ((2 : ENNReal)).toReal :=
          Real.rpow_le_rpow (by positivity)
            (mul_le_mul_of_nonneg_right (ha s) (norm_nonneg _)) toReal_two_pos.le
      _ = M ^ ((2 : ENNReal)).toReal * ‖v s‖ ^ ((2 : ENNReal)).toReal :=
          Real.mul_rpow hM (norm_nonneg _)
  have hsum : ‖mulLinear a M hM ha v‖ ^ ((2 : ENNReal)).toReal
      ≤ (M * ‖v‖) ^ ((2 : ENNReal)).toReal := by
    rw [h1, Real.mul_rpow hM (norm_nonneg _), h2, ← tsum_mul_left]
    exact Summable.tsum_le_tsum hterm hw (hv.mul_left _)
  -- pass from the squares to the norms
  rw [toReal_two] at hsum
  have hx : (0 : ℝ) ≤ ‖mulLinear a M hM ha v‖ := norm_nonneg _
  have hy : (0 : ℝ) ≤ M * ‖v‖ := mul_nonneg hM (norm_nonneg _)
  have hsq : ‖mulLinear a M hM ha v‖ ^ (2 : ℕ) ≤ (M * ‖v‖) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_natCast (M * ‖v‖) 2]
    push_cast
    exact hsum
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq hx, Real.sqrt_sq hy] at this

/-- Multiplication by a bounded family, as a bounded operator on `ℓ²`. -/
noncomputable def mulOp (a : α → ℂ) (M : ℝ) (hM : 0 ≤ M) (ha : ∀ s, ‖a s‖ ≤ M) :
    lp (fun _ : α ↦ ℂ) 2 →L[ℂ] lp (fun _ : α ↦ ℂ) 2 :=
  (mulLinear a M hM ha).mkContinuous M (norm_mulLinear_le a M hM ha)

@[simp] theorem mulOp_apply (a : α → ℂ) (M : ℝ) (hM : 0 ≤ M) (ha : ∀ s, ‖a s‖ ≤ M)
    (v : lp (fun _ : α ↦ ℂ) 2) (s : α) : mulOp a M hM ha v s = a s * v s := rfl

theorem norm_mulOp_le (a : α → ℂ) (M : ℝ) (hM : 0 ≤ M) (ha : ∀ s, ‖a s‖ ≤ M) :
    ‖mulOp a M hM ha‖ ≤ M :=
  LinearMap.mkContinuous_norm_le _ hM _

end Mult

/-! ## The operator of a finite-width kernel -/

variable {G : Type u} [Group G]

/-- **`Op(k)` for a kernel of width `S`.**  `M g` is a bound for the `g`-th
diagonal `s ↦ k s (g⁻¹ s)`. -/
noncomputable def kernelOp (S : Finset G) (k : G → G → ℂ) (M : G → ℝ)
    (hM : ∀ g s, ‖k s (g⁻¹ * s)‖ ≤ M g) :
    GroupHilbert G →L[ℂ] GroupHilbert G :=
  ∑ g ∈ S, (mulOp (fun s ↦ k s (g⁻¹ * s)) (M g)
      (le_trans (norm_nonneg _) (hM g 1)) (hM g)).comp
    (leftRegularOperator G g)

theorem kernelOp_apply (S : Finset G) (k : G → G → ℂ) (M : G → ℝ)
    (hM : ∀ g s, ‖k s (g⁻¹ * s)‖ ≤ M g) (v : GroupHilbert G) (s : G) :
    kernelOp S k M hM v s = ∑ g ∈ S, k s (g⁻¹ * s) * v (g⁻¹ * s) := by
  classical
  rw [kernelOp]
  induction S using Finset.induction with
  | empty => simp
  | insert g S hg ih =>
    rw [Finset.sum_insert hg, Finset.sum_insert hg, ← ih]
    simp

section Coeff

variable [DecidableEq G]

/-- The matrix of `Op(k)`: the kernel on the window, zero off it. -/
theorem matrixCoeff_kernelOp (S : Finset G) (k : G → G → ℂ) (M : G → ℝ)
    (hM : ∀ g s, ‖k s (g⁻¹ * s)‖ ≤ M g) (s t : G) :
    matrixCoeff G (kernelOp S k M hM) s t = if s * t⁻¹ ∈ S then k s t else 0 := by
  classical
  rw [matrixCoeff_def, kernelOp_apply]
  have hterm : ∀ g ∈ S, k s (g⁻¹ * s) * (delta G t) (g⁻¹ * s)
      = if g = s * t⁻¹ then k s t else 0 := by
    intro g _
    by_cases hgt : g = s * t⁻¹
    · subst hgt
      have hst : (s * t⁻¹)⁻¹ * s = t := by group
      rw [hst, delta_apply_self, mul_one, if_pos rfl]
    · have hne : g⁻¹ * s ≠ t := by
        intro h
        exact hgt (by
          have : g = s * t⁻¹ := by
            rw [← h]; group
          exact this)
      rw [delta_apply_ne G hne, mul_zero, if_neg hgt]
  rw [Finset.sum_congr rfl hterm]
  exact Finset.sum_ite_eq' S (s * t⁻¹) (fun _ ↦ k s t)

theorem hasPropagationIn_kernelOp (S : Finset G) (k : G → G → ℂ) (M : G → ℝ)
    (hM : ∀ g s, ‖k s (g⁻¹ * s)‖ ≤ M g) :
    HasPropagationIn G (kernelOp S k M hM) (S : Set G) := by
  intro s t h0
  rw [matrixCoeff_kernelOp] at h0
  by_contra hmem
  exact h0 (if_neg hmem)

theorem finitePropagation_kernelOp (S : Finset G) (k : G → G → ℂ) (M : G → ℝ)
    (hM : ∀ g s, ‖k s (g⁻¹ * s)‖ ≤ M g) :
    FinitePropagation G (kernelOp S k M hM) :=
  ⟨S, hasPropagationIn_kernelOp S k M hM⟩

/-! ## Operators are determined by their matrices -/

omit [Group G] in
theorem matrixCoeff_sub (A B : GroupHilbert G →L[ℂ] GroupHilbert G) (s t : G) :
    matrixCoeff G (A - B) s t = matrixCoeff G A s t - matrixCoeff G B s t := by
  have h := matrixCoeff_add (A - B) B s t
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

omit [Group G] in
/-- A point mass is `z` times the point mass at `1`. -/
theorem single_eq_smul_delta (t : G) (z : ℂ) : lp.single 2 t z = z • delta G t := by
  -- Going through `lp.coeFn_single` rather than through `lp.single_apply_ne`
  -- keeps the whole argument on the plain function `Pi.single t z`, where the
  -- rewrites match syntactically; applied to a coordinate first, the `lp`
  -- coercion makes the pattern of the `_ne` lemma unfindable.
  refine lp.ext ?_
  rw [lp.coeFn_single, lp.coeFn_smul]
  funext x
  by_cases hx : x = t
  · subst hx
    rw [Pi.single_eq_same, Pi.smul_apply, delta_apply_self, smul_eq_mul,
      mul_one]
  · rw [Pi.single_eq_of_ne hx, Pi.smul_apply, delta_apply_ne G hx,
      smul_eq_mul, mul_zero]

omit [Group G] in
/-- Every vector of `ℓ²(G)` is the sum of its point masses. -/
theorem hasSum_smul_delta (v : GroupHilbert G) :
    HasSum (fun t : G ↦ (v t) • delta G t) v := by
  have heq : (fun t : G ↦ lp.single 2 t (v t)) = fun t : G ↦ (v t) • delta G t :=
    funext fun t ↦ single_eq_smul_delta t (v t)
  rw [← heq]
  exact lp.hasSum_single (by norm_num) v

omit [Group G] in
/-- The point masses span a dense subspace. -/
theorem dense_span_delta :
    Dense ((Submodule.span ℂ (Set.range (delta G)) : Submodule ℂ (GroupHilbert G)) :
      Set (GroupHilbert G)) := by
  intro v
  refine mem_closure_of_tendsto (hasSum_smul_delta v) ?_
  filter_upwards with F
  refine Submodule.sum_mem _ fun t _ ↦ ?_
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)

omit [Group G] in
/-- **An operator is determined by its matrix.**  Two bounded operators with the
same matrix coefficients agree on every point mass, hence on their dense span,
hence everywhere. -/
theorem ext_of_matrixCoeff {A B : GroupHilbert G →L[ℂ] GroupHilbert G}
    (h : ∀ s t, matrixCoeff G A s t = matrixCoeff G B s t) : A = B := by
  refine ContinuousLinearMap.ext_on dense_span_delta ?_
  rintro _ ⟨t, rfl⟩
  exact lp.ext (funext fun s ↦ h s t)

end Coeff

/-- **The norm bound**: the `ℓ¹` sum over the window of the diagonal sups. -/
theorem norm_kernelOp_le (S : Finset G) (k : G → G → ℂ) (M : G → ℝ)
    (hM : ∀ g s, ‖k s (g⁻¹ * s)‖ ≤ M g) :
    ‖kernelOp S k M hM‖ ≤ ∑ g ∈ S, M g := by
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun g _ ↦ ?_)
  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
  have h1 : ‖leftRegularOperator G g‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ ?_
    rw [one_mul]
    exact le_of_eq ((leftRegular G g).norm_map v)
  have h2 : ‖mulOp (fun s ↦ k s (g⁻¹ * s)) (M g)
      (le_trans (norm_nonneg _) (hM g 1)) (hM g)‖ ≤ M g :=
    norm_mulOp_le _ _ _ _
  have h3 : (0 : ℝ) ≤ M g := le_trans (norm_nonneg _) (hM g 1)
  calc ‖mulOp (fun s ↦ k s (g⁻¹ * s)) (M g)
        (le_trans (norm_nonneg _) (hM g 1)) (hM g)‖ * ‖leftRegularOperator G g‖
      ≤ M g * 1 := by
        exact mul_le_mul h2 h1 (norm_nonneg _) h3
    _ = M g := mul_one _

end L2KernelOperator
end GroupApproximation
