import GroupApproximation.Analysis.TraciallyCompleteCStar
import GroupApproximation.Analysis.CStarSimple

/-!
# On a simple C⋆-algebra every tracial state is faithful

Let `τ` be a tracial state on a unital C⋆-algebra `A` and let `J = {x | τ (x⋆ x) = 0}`, written
through the trace two-norm `‖x‖₂ = τ (x⋆ x)^{1/2}` of `Analysis/UniformTracialGNSTwoGauge`.

* `J` is a left ideal: `‖x + y‖₂ ≤ ‖x‖₂ + ‖y‖₂` and `‖a x‖₂ ≤ ‖a‖ ‖x‖₂`;
* it is two-sided: `‖x a‖₂ ≤ ‖x‖₂ ‖a‖`, which is where traciality is used;
* it is closed, because `τ` is contractive, hence norm-continuous;
* it is proper, because `‖1‖₂ = 1`.

So on a C⋆-simple algebra `J = ⊥`, which is faithfulness.  This is the step that turns *a* tracial
state of the LIX counterexample algebra into a *faithful* one, and faithful traces force stable
finiteness (`FaithfulTracialState.matrix_mul_star_eq_one_of_star_mul_eq_one`).
-/

namespace GroupApproximation
namespace LIX
namespace TraceFaithful

universe u

noncomputable section

open UniformTracialGNSTwoGauge
open scoped ComplexOrder

variable {A : Type u} [CStarAlgebra A]

/-- A tracial state of a C⋆-algebra is norm-continuous: it is contractive. -/
theorem continuous_tracialState (τ : TracialState A) : Continuous fun x : A => τ x :=
  AddMonoidHomClass.continuous_of_bound τ.toLinearMap 1 fun x => by
    rw [one_mul]
    exact Manuscript.MFRecognition.TensorSynchronization.norm_tracialState_le τ x

/-- The null space `{x | τ (x⋆ x) = 0}` of a tracial state, as a left ideal. -/
def traceKernel (τ : TracialState A) : Ideal A where
  carrier := {x | tracialTwoNorm τ x = 0}
  add_mem' := by
    intro x y hx hy
    have hx' : tracialTwoNorm τ x = 0 := hx
    have hy' : tracialTwoNorm τ y = 0 := hy
    show tracialTwoNorm τ (x + y) = 0
    have h := tracialTwoNorm_add_le τ x y
    rw [hx', hy', add_zero] at h
    exact le_antisymm h (tracialTwoNorm_nonneg τ _)
  zero_mem' := tracialTwoNorm_zero τ
  smul_mem' := by
    intro c x hx
    have hx' : tracialTwoNorm τ x = 0 := hx
    show tracialTwoNorm τ (c • x) = 0
    have h := tracialTwoNorm_mul_left_le τ c x
    rw [hx', mul_zero] at h
    rw [smul_eq_mul]
    exact le_antisymm h (tracialTwoNorm_nonneg τ _)

theorem mem_traceKernel {τ : TracialState A} {x : A} :
    x ∈ traceKernel τ ↔ tracialTwoNorm τ x = 0 :=
  Iff.rfl

/-- The null space of a tracial state is a two-sided ideal: right absorption is the left bound read
through traciality. -/
instance isTwoSided_traceKernel (τ : TracialState A) : (traceKernel τ).IsTwoSided := by
  constructor
  intro a b ha
  have ha' : tracialTwoNorm τ a = 0 := ha
  show tracialTwoNorm τ (a * b) = 0
  have h := tracialTwoNorm_mul_right_le τ a b
  rw [ha', zero_mul] at h
  exact le_antisymm h (tracialTwoNorm_nonneg τ _)

/-- The null space of a tracial state is closed. -/
theorem isClosed_traceKernel (τ : TracialState A) : IsClosed (traceKernel τ : Set A) := by
  have hc : Continuous fun x : A => tracialTwoNorm τ x :=
    Real.continuous_sqrt.comp (Complex.continuous_re.comp
      ((continuous_tracialState τ).comp (continuous_star.mul continuous_id)))
  exact isClosed_eq hc continuous_const

/-- **On a C⋆-simple algebra a tracial state vanishes on `x⋆ x` only at `x = 0`.** -/
theorem eq_zero_of_isSimpleCStar (h : IsSimpleCStar A) (τ : TracialState A) {x : A}
    (hx : τ (star x * x) = 0) : x = 0 := by
  rcases h.eq_bot_or_eq_top (traceKernel τ) (isClosed_traceKernel τ) with hbot | htop
  · have hmem : x ∈ traceKernel τ := by
      rw [mem_traceKernel, tracialTwoNorm_def, hx, Complex.zero_re, Real.sqrt_zero]
    rw [hbot] at hmem
    exact Ideal.mem_bot.mp hmem
  · exfalso
    have h1 : (1 : A) ∈ traceKernel τ := by
      rw [htop]
      exact Submodule.mem_top
    rw [mem_traceKernel, tracialTwoNorm_one] at h1
    exact one_ne_zero h1

/-- **On a C⋆-simple algebra every tracial state is faithful.** -/
def faithfulTracialStateOfIsSimpleCStar (h : IsSimpleCStar A) (τ : TracialState A) :
    FaithfulTracialState A where
  toLinearMap := τ.toLinearMap
  map_one := τ.map_one
  map_star_mul_self_nonneg := τ.map_star_mul_self_nonneg
  map_mul_comm := τ.map_mul_comm
  eq_zero_of_map_star_mul_self_eq_zero := fun hx => eq_zero_of_isSimpleCStar h τ hx

end

end TraceFaithful
end LIX
end GroupApproximation
