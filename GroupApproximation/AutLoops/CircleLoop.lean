import GroupApproximation.AutLoops.LoopGroup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Loops of circle actions

A continuous homomorphism `σ : 𝕋 → G` into a topological group gives the loop
`t ↦ σ(e^{2πit})` at `1`. The STW loops `σ_j` and `ρ_i` have this form in `G = PointNormAut A`.

## Main declarations

* `circleExp_two_pi`: `e^{2πi} = 1` in `Circle`.
* `circleLoop σ`, `circleClass σ`: the loop of `σ` and its class in `π_1(G, 1)`.
* `circleClass_eq_mul`: the class of a pointwise product of actions is the product of classes.
* `mapOfEq_circleClass`: naturality under continuous homomorphisms `G → H`.
-/

open Real

noncomputable section

namespace GroupApproximation
namespace AutLoops

theorem circleExp_two_pi : Circle.exp (2 * π) = 1 := by
  refine Circle.coe_eq_one.1 ?_
  rw [Circle.coe_exp]
  push_cast
  exact Complex.exp_two_pi_mul_I

section TopologicalGroup

variable {G : Type*} [TopologicalSpace G] [Group G]

/-- The loop `t ↦ σ(e^{2πit})` of a continuous homomorphism `σ : 𝕋 → G`. -/
def circleLoop (σ : Circle →ₜ* G) : Path (1 : G) 1 where
  toFun t := σ (Circle.exp (2 * π * t))
  continuous_toFun := (map_continuous σ).comp
    (Circle.exp.continuous.comp (continuous_const.mul continuous_subtype_val))
  source' := by simp
  target' := by simp [circleExp_two_pi]

@[simp] theorem circleLoop_apply (σ : Circle →ₜ* G) (t : unitInterval) :
    circleLoop σ t = σ (Circle.exp (2 * π * t)) := rfl

/-- The class of `circleLoop σ` in `π_1(G, 1)`. -/
def circleClass (σ : Circle →ₜ* G) : FundamentalGroup G 1 :=
  FundamentalGroup.fromPath (.mk (circleLoop σ))

theorem circleLoop_eq_loopMul [IsTopologicalGroup G] {σ τ ρ : Circle →ₜ* G}
    (h : ∀ z, ρ z = σ z * τ z) : circleLoop ρ = loopMul (circleLoop σ) (circleLoop τ) :=
  DFunLike.ext _ _ fun t : unitInterval => h (Circle.exp (2 * π * (t : ℝ)))

/-- The loop class of a pointwise product of circle actions is the product of the classes. -/
theorem circleClass_eq_mul [IsTopologicalGroup G] {σ τ ρ : Circle →ₜ* G}
    (h : ∀ z, ρ z = σ z * τ z) :
    circleClass ρ = circleClass σ * circleClass τ :=
  (congrArg (fun p => FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))
    (circleLoop_eq_loopMul h)).trans (fromPath_mk_loopMul (circleLoop σ) (circleLoop τ))

theorem mapOfEq_circleClass {H : Type*} [TopologicalSpace H] [Group H]
    (f : G →ₜ* H) (σ : Circle →ₜ* G) :
    FundamentalGroup.mapOfEq (f : C(G, H)) (map_one f) (circleClass σ) =
      circleClass (f.comp σ) := by
  rw [FundamentalGroup.mapOfEq_apply]
  rfl

end TopologicalGroup

end AutLoops
end GroupApproximation
