import GroupApproximation.Analysis.ReducedGroupCStarTrace
import GroupApproximation.Analysis.GroupVonNeumannAlgebra
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Multiplication operators on the group Hilbert space

Toward proof-ledger row `RE.05` (the Lance debt).  The hypertrace obtained
from the compression composite is evaluated on the copy of `ℓ∞(G)` inside
`B(ℓ²(G))` given by coordinatewise multiplication.  This module builds that
copy: for a bounded `f : G → ℂ` the diagonal operator `mulOp f`, its
coefficients, its norm bound, additivity, products, adjoints, positivity
for nonnegative real symbols (a square root factorization plus the Loewner
order), the constant symbol, and the covariance identity

  `λ_s ∘ mulOp f ∘ λ_{s⁻¹} = mulOp (fun h ↦ f (s⁻¹ * h))`

that converts left translation of the symbol into conjugation by the left
regular representation.

## Manuscript status

Infrastructure for the Lance lane; certifies no manuscript step on its own.
`RE.05` remains conditional until the full compression statement lands.
-/

namespace GroupApproximation
namespace CStarExactness

open scoped InnerProductSpace
open ReducedGroupCStarTrace GroupVonNeumann

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- Coordinatewise multiplication by a bounded symbol, as a linear map on
`ℓ²(G)`. -/
def mulOpAux (f : G → ℂ) (C : ℝ) (hC : ∀ g, ‖f g‖ ≤ C) :
    GroupHilbert G →ₗ[ℂ] GroupHilbert G where
  toFun x := ⟨fun g ↦ f g * x g, by
    refine Memℓp.mono' ((lp.memℓp x).const_smul (C : ℂ)) fun g ↦ ?_
    calc ‖f g * x g‖ = ‖f g‖ * ‖x g‖ := norm_mul _ _
      _ ≤ C * ‖x g‖ := mul_le_mul_of_nonneg_right (hC g) (norm_nonneg _)
      _ ≤ |C| * ‖x g‖ := mul_le_mul_of_nonneg_right (le_abs_self C)
          (norm_nonneg _)
      _ = ‖((C : ℂ) • (⇑x : G → ℂ)) g‖ := by
          rw [Pi.smul_apply, norm_smul, Complex.norm_real,
            Real.norm_eq_abs]⟩
  map_add' x y := by
    refine lp.ext (funext fun g ↦ ?_)
    show f g * (x + y) g = f g * x g + f g * y g
    rw [lp.coeFn_add, Pi.add_apply]
    ring
  map_smul' c x := by
    refine lp.ext (funext fun g ↦ ?_)
    show f g * (c • x) g = (c • ⟨fun g ↦ f g * x g, _⟩ :
      GroupHilbert G) g
    rw [lp.coeFn_smul, Pi.smul_apply, lp.coeFn_smul, Pi.smul_apply]
    show f g * (c * x g) = c * (f g * x g)
    ring

omit [Group G] in
@[simp]
theorem mulOpAux_apply (f : G → ℂ) (C : ℝ) (hC : ∀ g, ‖f g‖ ≤ C)
    (x : GroupHilbert G) (g : G) :
    mulOpAux f C hC x g = f g * x g := rfl

/-- Coordinatewise multiplication by a bounded symbol, as a bounded
operator on `ℓ²(G)`. -/
def mulOp (f : G → ℂ) (C : ℝ) (hC : ∀ g, ‖f g‖ ≤ C) :
    GroupHilbert G →L[ℂ] GroupHilbert G :=
  LinearMap.mkContinuous (mulOpAux f C hC) C fun x ↦ by
    have hC0 : 0 ≤ C := le_trans (norm_nonneg (f 1)) (hC 1)
    calc ‖mulOpAux f C hC x‖
        ≤ ‖(C : ℂ) • x‖ := by
          refine lp.norm_mono (by norm_num) fun g ↦ ?_
          rw [mulOpAux_apply, lp.coeFn_smul, Pi.smul_apply]
          calc ‖f g * x g‖ = ‖f g‖ * ‖x g‖ := norm_mul _ _
            _ ≤ C * ‖x g‖ := mul_le_mul_of_nonneg_right (hC g)
                (norm_nonneg _)
            _ = ‖(C : ℂ) • x g‖ := by
                rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
                  abs_of_nonneg hC0]
      _ = C * ‖x‖ := by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hC0]

@[simp]
theorem mulOp_apply (f : G → ℂ) (C : ℝ) (hC : ∀ g, ‖f g‖ ≤ C)
    (x : GroupHilbert G) (g : G) :
    mulOp f C hC x g = f g * x g := rfl

theorem norm_mulOp_le (f : G → ℂ) (C : ℝ) (hC : ∀ g, ‖f g‖ ≤ C) :
    ‖mulOp f C hC‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _
    (le_trans (norm_nonneg (f 1)) (hC 1)) _

/-- The symbol map is additive. -/
theorem mulOp_add (f₁ f₂ : G → ℂ) (C₁ C₂ : ℝ)
    (hC₁ : ∀ g, ‖f₁ g‖ ≤ C₁) (hC₂ : ∀ g, ‖f₂ g‖ ≤ C₂)
    (hC : ∀ g, ‖f₁ g + f₂ g‖ ≤ C₁ + C₂) :
    mulOp (fun g ↦ f₁ g + f₂ g) (C₁ + C₂) hC
      = mulOp f₁ C₁ hC₁ + mulOp f₂ C₂ hC₂ := by
  refine ContinuousLinearMap.ext fun x ↦ lp.ext (funext fun g ↦ ?_)
  show (f₁ g + f₂ g) * x g
      = (mulOp f₁ C₁ hC₁ x + mulOp f₂ C₂ hC₂ x) g
  rw [lp.coeFn_add, Pi.add_apply, mulOp_apply, mulOp_apply]
  ring

/-- The symbol map turns products into compositions. -/
theorem mulOp_comp (f₁ f₂ : G → ℂ) (C₁ C₂ : ℝ)
    (hC₁ : ∀ g, ‖f₁ g‖ ≤ C₁) (hC₂ : ∀ g, ‖f₂ g‖ ≤ C₂)
    (hC : ∀ g, ‖f₁ g * f₂ g‖ ≤ C₁ * C₂) :
    mulOp (fun g ↦ f₁ g * f₂ g) (C₁ * C₂) hC
      = mulOp f₁ C₁ hC₁ ∘L mulOp f₂ C₂ hC₂ := by
  refine ContinuousLinearMap.ext fun x ↦ lp.ext (funext fun g ↦ ?_)
  show (f₁ g * f₂ g) * x g = f₁ g * (mulOp f₂ C₂ hC₂ x) g
  rw [mulOp_apply]
  ring

/-- The constant symbol is the scalar operator. -/
theorem mulOp_const (c : ℂ) :
    mulOp (fun _ : G ↦ c) ‖c‖ (fun _ ↦ le_rfl)
      = c • (1 : GroupHilbert G →L[ℂ] GroupHilbert G) := by
  refine ContinuousLinearMap.ext fun x ↦ lp.ext (funext fun g ↦ ?_)
  show c * x g = ((c • x : GroupHilbert G)) g
  rw [lp.coeFn_smul, Pi.smul_apply]
  rfl

/-- The unit symbol is the identity. -/
theorem mulOp_one :
    mulOp (fun _ : G ↦ (1 : ℂ)) 1 (fun _ ↦ by norm_num)
      = (1 : GroupHilbert G →L[ℂ] GroupHilbert G) := by
  refine ContinuousLinearMap.ext fun x ↦ lp.ext (funext fun g ↦ ?_)
  show (1 : ℂ) * x g = x g
  ring

/-- The adjoint of a multiplication operator is multiplication by the
conjugate symbol. -/
theorem star_mulOp (f : G → ℂ) (C : ℝ) (hC : ∀ g, ‖f g‖ ≤ C) :
    star (mulOp f C hC)
      = mulOp (fun g ↦ (starRingEnd ℂ) (f g)) C
          (fun g ↦ by simpa using hC g) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun g ↦ ?_
  rw [mulOp_apply, mulOp_apply, RCLike.inner_apply, RCLike.inner_apply,
    map_mul, Complex.conj_conj]
  ring

/-- Multiplication by a nonnegative real symbol is a positive operator:
factor through the square root of the symbol. -/
theorem mulOp_nonneg (r : G → ℝ) (C : ℝ) (hr : ∀ g, 0 ≤ r g)
    (hC : ∀ g, ‖((r g : ℂ))‖ ≤ C) :
    (0 : GroupHilbert G →L[ℂ] GroupHilbert G)
      ≤ mulOp (fun g ↦ (r g : ℂ)) C hC := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 1)
  have hsq : ∀ g, ‖((Real.sqrt (r g) : ℂ))‖ ≤ Real.sqrt C := by
    intro g
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    refine Real.sqrt_le_sqrt ?_
    have := hC g
    rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr g)] at this
  set S := mulOp (fun g ↦ (Real.sqrt (r g) : ℂ)) (Real.sqrt C) hsq with hS
  have hfac : mulOp (fun g ↦ (r g : ℂ)) C hC = star S * S := by
    have hstar : star S
        = mulOp (fun g ↦ (starRingEnd ℂ) ((Real.sqrt (r g) : ℂ)))
            (Real.sqrt C) (fun g ↦ by simpa using hsq g) := by
      rw [hS, star_mulOp]
    rw [hstar]
    refine ContinuousLinearMap.ext fun x ↦ lp.ext (funext fun g ↦ ?_)
    show (r g : ℂ) * x g
        = (starRingEnd ℂ) ((Real.sqrt (r g) : ℂ)) * (S x) g
    rw [hS, mulOp_apply, Complex.conj_ofReal]
    have hmul : ((Real.sqrt (r g) : ℂ)) * ((Real.sqrt (r g) : ℂ))
        = ((r g : ℂ)) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hr g)]
    calc (r g : ℂ) * x g
        = ((Real.sqrt (r g) : ℂ)) * ((Real.sqrt (r g) : ℂ)) * x g := by
          rw [hmul]
      _ = ((Real.sqrt (r g) : ℂ)) * (((Real.sqrt (r g) : ℂ)) * x g) := by
          ring
  rw [hfac]
  exact star_mul_self_nonneg S

/-- **Covariance.**  Conjugating a multiplication operator by the left
regular representation translates the symbol. -/
theorem leftRegular_conj_mulOp (s : G) (f : G → ℂ) (C : ℝ)
    (hC : ∀ g, ‖f g‖ ≤ C) :
    leftRegularOperator G s ∘L mulOp f C hC ∘L leftRegularOperator G s⁻¹
      = mulOp (fun h ↦ f (s⁻¹ * h)) C (fun h ↦ hC (s⁻¹ * h)) := by
  refine ContinuousLinearMap.ext fun x ↦ lp.ext (funext fun h ↦ ?_)
  show (mulOp f C hC (leftRegularOperator G s⁻¹ x)) (s⁻¹ * h)
      = f (s⁻¹ * h) * x h
  rw [mulOp_apply]
  congr 1
  show x (s⁻¹⁻¹ * (s⁻¹ * h)) = x h
  rw [inv_inv, mul_inv_cancel_left]

end

end CStarExactness
end GroupApproximation
