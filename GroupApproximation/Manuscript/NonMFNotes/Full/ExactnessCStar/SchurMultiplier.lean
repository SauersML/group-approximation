import GroupApproximation.Manuscript.NonMFNotes.Full.ExactnessCStar.SchurDilation
import GroupApproximation.Manuscript.NonMFNotes.Full.ExactnessCStar.TranslationForm

/-!
# Schur multipliers of property-A overlap kernels

Source: `non_mf_group_notes.tex`, section `sec:Esofic`, paragraph
"Exactness" \cite{KWExact}.  Compressing the amplified regular representation
of `C*_r(G)` by the Schur dilation `V` of a property-A witness gives the
completely positive contraction

  `Φ(c) = V⋆ (c ⊗ 1) V`,

which acts on the translation operators by the Schur multiplier of the overlap
kernel `k(a, b) = ∑_x √(μ_a x) √(μ_b x)`:

  `Φ(λ_g) f (s) = k(s⁻¹, s⁻¹ g) f(g⁻¹ s)`.

* `schurMultiplier` --- the compression `Φ`, a linear map
  `C*_r(G) → B(ℓ²(G))`;
* `schurMultiplier_reducedLeftRegular_apply` --- the multiplier formula;
* `norm_schurMultiplier_reducedLeftRegular_le` --- `‖Φ(λ_g)‖ ≤ 1`;
* `norm_leftRegular_sub_schurMultiplier_le` --- `‖λ_g - Φ(λ_g)‖ ≤ ε / 2`
  for `g ∈ R`;
* `schurMultiplier_reducedLeftRegular_eq_zero` --- `Φ(λ_g) = 0` for `g`
  outside the finite difference set of the template.
-/

namespace GroupApproximation.Full.NN09c

open GroupApproximation.ExactnessPermanence GroupApproximation.ReducedGroupCStarTrace
open GroupApproximation.TwistedTensor
open scoped InnerProductSpace ComplexConjugate

universe u

noncomputable section

section Multiplier

variable {G : Type u} [Group G] {R : Finset G} {ε : ℝ}

local instance decEqSchurMultiplier : DecidableEq G := Classical.decEq G

/-- **The Schur multiplier** `Φ(c) = V⋆ (c ⊗ 1) V` of a property-A witness. -/
def schurMultiplier (W : PropertyAWitness G R ε) :
    ReducedGroupCStar G →ₗ[ℂ] (GroupHilbert G →L[ℂ] GroupHilbert G) where
  toFun c := (ContinuousLinearMap.adjoint (schurDilation W)).comp
    ((ampRegRep G c).comp (schurDilation W))
  map_add' c d := ContinuousLinearMap.ext fun f ↦ by
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, map_add]
  map_smul' a c := ContinuousLinearMap.ext fun f ↦ by
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, map_smul,
      RingHom.id_apply]

theorem schurMultiplier_apply (W : PropertyAWitness G R ε) (c : ReducedGroupCStar G) :
    schurMultiplier W c = (ContinuousLinearMap.adjoint (schurDilation W)).comp
      ((ampRegRep G c).comp (schurDilation W)) :=
  rfl

theorem schurColumn_single (W : PropertyAWitness G R ε) (x s : G) :
    schurColumn W x (lp.single 2 s (1 : ℂ)) = lp.single 2 s (schurSymbol W x s) := by
  refine lp.ext (funext fun t ↦ ?_)
  change schurSymbol W x t * (lp.single 2 s (1 : ℂ) : GroupHilbert G) t
    = (lp.single 2 s (schurSymbol W x s) : GroupHilbert G) t
  rw [lp.single_apply, lp.single_apply]
  by_cases hts : t = s
  · rw [hts, Pi.single_eq_same, Pi.single_eq_same, mul_one]
  · rw [Pi.single_eq_of_ne hts, Pi.single_eq_of_ne hts, mul_zero]

theorem apply_eq_inner_single (f : GroupHilbert G) (s : G) :
    f s = ⟪(lp.single 2 s (1 : ℂ) : GroupHilbert G), f⟫_ℂ := by
  rw [lp.inner_single_left, RCLike.inner_apply', map_one, one_mul]

/-- **The multiplier formula**: `Φ(λ_g) f (s) = k(s⁻¹, s⁻¹ g) f(g⁻¹ s)`. -/
theorem schurMultiplier_reducedLeftRegular_apply (W : PropertyAWitness G R ε) (g : G)
    (f : GroupHilbert G) (s : G) :
    schurMultiplier W (reducedLeftRegular G g) f s
      = ((sqrtKernel W s⁻¹ (s⁻¹ * g) : ℝ) : ℂ) * f (g⁻¹ * s) := by
  have hinv : (g⁻¹ * s)⁻¹ = s⁻¹ * g := by rw [mul_inv_rev, inv_inv]
  have hterm : ∀ x : G,
      ⟪(schurDilation W (lp.single 2 s (1 : ℂ))) x,
        (ampRegRep G (reducedLeftRegular G g) (schurDilation W f)) x⟫_ℂ
        = ((Real.sqrt (W.weight s⁻¹ x) * Real.sqrt (W.weight (s⁻¹ * g) x) : ℝ) : ℂ)
          * f (g⁻¹ * s) := by
    intro x
    rw [schurDilation_apply W (lp.single 2 s (1 : ℂ)) x, schurColumn_single,
      lp.inner_single_left, RCLike.inner_apply']
    change conj (schurSymbol W x s) * (schurSymbol W x (g⁻¹ * s) * f (g⁻¹ * s)) = _
    unfold schurSymbol
    rw [Complex.conj_ofReal, hinv, Complex.ofReal_mul, mul_assoc]
  have hzero : ∀ x ∉ window W s⁻¹,
      ((Real.sqrt (W.weight s⁻¹ x) * Real.sqrt (W.weight (s⁻¹ * g) x) : ℝ) : ℂ)
        * f (g⁻¹ * s) = 0 := by
    intro x hx
    rw [weight_eq_zero_of_not_mem_window W hx, Real.sqrt_zero, zero_mul,
      Complex.ofReal_zero, zero_mul]
  rw [apply_eq_inner_single (schurMultiplier W (reducedLeftRegular G g) f) s,
    schurMultiplier_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.comp_apply,
    lp.inner_eq_tsum]
  refine (tsum_congr hterm).trans ?_
  rw [tsum_eq_sum hzero, ← Finset.sum_mul, ← Complex.ofReal_sum, sqrtKernel]

/-- The symbol `s ↦ k(s⁻¹, s⁻¹ g)` of `Φ(λ_g) λ_g⁻¹`. -/
def kernelSymbol (W : PropertyAWitness G R ε) (g s : G) : ℂ :=
  ((sqrtKernel W s⁻¹ (s⁻¹ * g) : ℝ) : ℂ)

theorem norm_kernelSymbol_le (W : PropertyAWitness G R ε) (g s : G) :
    ‖kernelSymbol W g s‖ ≤ 1 := by
  rw [kernelSymbol, Complex.norm_of_nonneg (sqrtKernel_nonneg W _ _)]
  exact sqrtKernel_le_one W _ _

theorem schurMultiplier_reducedLeftRegular (W : PropertyAWitness G R ε) (g : G) :
    schurMultiplier W (reducedLeftRegular G g)
      = (CStarExactness.mulOp (kernelSymbol W g) 1 (norm_kernelSymbol_le W g)).comp
          (leftRegularOperator G g) :=
  ContinuousLinearMap.ext fun f ↦ lp.ext (funext fun s ↦
    schurMultiplier_reducedLeftRegular_apply W g f s)

/-- `‖Φ(λ_g)‖ ≤ 1`. -/
theorem norm_schurMultiplier_reducedLeftRegular_le (W : PropertyAWitness G R ε) (g : G) :
    ‖schurMultiplier W (reducedLeftRegular G g)‖ ≤ 1 := by
  rw [schurMultiplier_reducedLeftRegular]
  calc _ ≤ ‖CStarExactness.mulOp (kernelSymbol W g) 1 (norm_kernelSymbol_le W g)‖
        * ‖leftRegularOperator G g‖ := ContinuousLinearMap.opNorm_comp_le ..
    _ ≤ 1 * 1 := mul_le_mul (CStarExactness.norm_mulOp_le _ _ _)
        (norm_leftRegularOperator_le_one G g) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- The symbol `s ↦ 1 - k(s⁻¹, s⁻¹ g)` of `(λ_g - Φ(λ_g)) λ_g⁻¹`. -/
def oneSubKernelSymbol (W : PropertyAWitness G R ε) (g s : G) : ℂ :=
  ((1 - sqrtKernel W s⁻¹ (s⁻¹ * g) : ℝ) : ℂ)

theorem norm_oneSubKernelSymbol_le (W : PropertyAWitness G R ε) {g : G} (hg : g ∈ R)
    (s : G) : ‖oneSubKernelSymbol W g s‖ ≤ ε / 2 := by
  rw [oneSubKernelSymbol, Complex.norm_of_nonneg (sub_nonneg.mpr (sqrtKernel_le_one W _ _))]
  have hs : s⁻¹⁻¹ * (s⁻¹ * g) ∈ R := by
    rw [inv_inv, mul_inv_cancel_left]
    exact hg
  exact one_sub_sqrtKernel_le W hs

/-- **The multiplier is close to the identity on short translations**:
`‖λ_g - Φ(λ_g)‖ ≤ ε / 2` for `g ∈ R`. -/
theorem norm_leftRegular_sub_schurMultiplier_le (W : PropertyAWitness G R ε) {g : G}
    (hg : g ∈ R) :
    ‖leftRegularOperator G g - schurMultiplier W (reducedLeftRegular G g)‖ ≤ ε / 2 := by
  have heq : leftRegularOperator G g - schurMultiplier W (reducedLeftRegular G g)
      = (CStarExactness.mulOp (oneSubKernelSymbol W g) (ε / 2)
          (norm_oneSubKernelSymbol_le W hg)).comp (leftRegularOperator G g) :=
    ContinuousLinearMap.ext fun f ↦ lp.ext (funext fun s ↦ by
      change f (g⁻¹ * s) - schurMultiplier W (reducedLeftRegular G g) f s
        = ((1 - sqrtKernel W s⁻¹ (s⁻¹ * g) : ℝ) : ℂ) * f (g⁻¹ * s)
      rw [schurMultiplier_reducedLeftRegular_apply, Complex.ofReal_sub, Complex.ofReal_one,
        sub_mul, one_mul])
  have hε : 0 ≤ ε / 2 := le_trans (norm_nonneg _) (norm_oneSubKernelSymbol_le W hg 1)
  rw [heq]
  calc _ ≤ ‖CStarExactness.mulOp (oneSubKernelSymbol W g) (ε / 2)
          (norm_oneSubKernelSymbol_le W hg)‖ * ‖leftRegularOperator G g‖ :=
        ContinuousLinearMap.opNorm_comp_le ..
    _ ≤ ε / 2 * 1 := mul_le_mul (CStarExactness.norm_mulOp_le _ _ _)
        (norm_leftRegularOperator_le_one G g) (norm_nonneg _) hε
    _ = ε / 2 := mul_one _

/-- **The multiplier kills long translations**: `Φ(λ_g) = 0` unless `g` lies
in the finite difference set of the template. -/
theorem schurMultiplier_reducedLeftRegular_eq_zero (W : PropertyAWitness G R ε) {g : G}
    (hg : g ∉ diffSet W) : schurMultiplier W (reducedLeftRegular G g) = 0 :=
  ContinuousLinearMap.ext fun f ↦ lp.ext (funext fun s ↦ by
    have hs : s⁻¹⁻¹ * (s⁻¹ * g) ∉ diffSet W := by
      rw [inv_inv, mul_inv_cancel_left]
      exact hg
    have h0 : schurMultiplier W (reducedLeftRegular G g) f s = 0 := by
      rw [schurMultiplier_reducedLeftRegular_apply, sqrtKernel_eq_zero W hs,
        Complex.ofReal_zero, zero_mul]
    exact h0)

end Multiplier

end

end GroupApproximation.Full.NN09c
