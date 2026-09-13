import GroupApproximation.AutLoops.CircleLoop
import Mathlib.Topology.Algebra.Star.Unitary

/-!
# The unitary invariant of a loop of automorphisms

For a unitary `w ∈ A` the orbit map `α ↦ α(w) w⋆ : Aut A → U(A)` is continuous for the point-norm
topology and sends `id` to `1`. It induces `Δ_w : π_1(Aut A, id) → π_1(U(A), 1)`, the class of the
loop `z ↦ α_z(w) w⋆`. Composed with the Bott map this is the `K_1 → K_0` part of Dadarlat's `Δ_α`.

## Main declarations

* `PointNormAut.apply_mem_unitary`: automorphisms preserve unitaries.
* `orbitMap w`: the continuous map `α ↦ α(w) w⋆`, with `orbitMap_one`.
* `deltaUnitary w : AutLoopGroup A →* FundamentalGroup (unitary A) 1`.
* `orbitLoop σ w`, `deltaUnitary_circleClass`: `Δ_w` of a circle action is `t ↦ σ(e^{2πit})(w) w⋆`.
-/

open Real

noncomputable section

namespace GroupApproximation
namespace AutLoops

variable {A : Type*} [CStarAlgebra A]

namespace PointNormAut

theorem apply_mem_unitary (α : PointNormAut A) {w : A} (hw : w ∈ unitary A) :
    α w ∈ unitary A := by
  rw [Unitary.mem_iff] at hw ⊢
  refine ⟨?_, ?_⟩
  · rw [← map_star, ← map_mul, hw.1, map_one]
  · rw [← map_star, ← map_mul, hw.2, map_one]

end PointNormAut

/-- The orbit map `α ↦ α(w) w⋆` of a unitary `w`. -/
def orbitMap (w : unitary A) : C(PointNormAut A, unitary A) where
  toFun α := ⟨α (w : A) * star (w : A), mul_mem (α.apply_mem_unitary w.2) (Unitary.star_mem w.2)⟩
  continuous_toFun :=
    ((PointNormAut.continuous_apply (w : A)).mul continuous_const).subtype_mk _

@[simp] theorem orbitMap_apply (w : unitary A) (α : PointNormAut A) :
    (orbitMap w α : A) = α w * star (w : A) := rfl

theorem orbitMap_one (w : unitary A) : orbitMap w 1 = 1 :=
  Subtype.ext (Unitary.mul_star_self_of_mem w.2)

/-- `Δ_w : π_1(Aut A, id) → π_1(U(A), 1)`, the class of the loop `z ↦ α_z(w) w⋆`. -/
def deltaUnitary (w : unitary A) : AutLoopGroup A →* FundamentalGroup (unitary A) 1 :=
  FundamentalGroup.mapOfEq (orbitMap w) (orbitMap_one w)

theorem deltaUnitary_mk (w : unitary A) (p : Path (1 : PointNormAut A) 1) :
    deltaUnitary w (FundamentalGroup.fromPath (.mk p)) =
      FundamentalGroup.fromPath (.mk ((p.map (orbitMap w).continuous).cast
        (orbitMap_one w).symm (orbitMap_one w).symm)) := by
  rw [deltaUnitary, FundamentalGroup.mapOfEq_apply]
  rfl

/-- The loop `t ↦ σ(e^{2πit})(w) w⋆` in `U(A)`. -/
def orbitLoop (σ : Circle →ₜ* PointNormAut A) (w : unitary A) : Path (1 : unitary A) 1 :=
  ((circleLoop σ).map (orbitMap w).continuous).cast (orbitMap_one w).symm (orbitMap_one w).symm

@[simp] theorem orbitLoop_apply (σ : Circle →ₜ* PointNormAut A) (w : unitary A)
    (t : unitInterval) :
    (orbitLoop σ w t : A) = σ (Circle.exp (2 * π * t)) (w : A) * star (w : A) := rfl

theorem deltaUnitary_circleClass (σ : Circle →ₜ* PointNormAut A) (w : unitary A) :
    deltaUnitary w (circleClass σ) = FundamentalGroup.fromPath (.mk (orbitLoop σ w)) :=
  deltaUnitary_mk w (circleLoop σ)

end AutLoops
end GroupApproximation
