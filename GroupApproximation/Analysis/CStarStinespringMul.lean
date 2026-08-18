import GroupApproximation.Analysis.CStarStinespringAct

/-!
# The action laws of the dilation

## What this module proves

The three algebraic laws that make the dilation action a
⋆-representation, all on the free model and none needing analysis:

* `stinespringActFree_one` -- the unit acts as the identity;
* `stinespringActFree_mul` -- the action is multiplicative;
* `stinespringSesq_act_adjoint` -- the action of `star c` is the formal
  adjoint of the action of `c` for the Stinespring form: associativity
  of multiplication, read through the form.

With the seminorm bound of `CStarStinespringDefect`, these are exactly
the inputs the representation on the completion consumes.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.  `RE.05`
remains **MISSING**.
-/

namespace GroupApproximation
namespace CStarExactness

open scoped InnerProductSpace
open Finsupp

universe u w

variable {A : Type u} [CStarAlgebra A]
variable {H : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {φ : A →ₗ[ℂ] (H →L[ℂ] H)}

theorem stinespringActFree_one :
    stinespringActFree (1 : A) = (LinearMap.id : (A →₀ H) →ₗ[ℂ] (A →₀ H)) := by
  refine LinearMap.ext fun f => ?_
  rw [stinespringActFree, Finsupp.lmapDomain_apply]
  have h : (fun a : A => 1 * a) = id := funext fun a => one_mul a
  rw [h, Finsupp.mapDomain_id, LinearMap.id_apply]

theorem stinespringActFree_mul (c₁ c₂ : A) :
    stinespringActFree (c₁ * c₂)
      = ((stinespringActFree c₁).comp (stinespringActFree c₂) :
          (A →₀ H) →ₗ[ℂ] (A →₀ H)) := by
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.comp_apply, stinespringActFree, stinespringActFree,
    stinespringActFree, Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply,
    Finsupp.lmapDomain_apply]
  have h : (fun a : A => c₁ * c₂ * a)
      = (fun a : A => c₁ * a) ∘ (fun a : A => c₂ * a) :=
    funext fun a => mul_assoc c₁ c₂ a
  rw [h, Finsupp.mapDomain_comp]

theorem stinespringSesq_act_right (c : A) (f g : A →₀ H) :
    stinespringSesq φ f (stinespringActFree c g)
      = f.sum fun a x => g.sum fun b y =>
          ⟪x, φ (star a * (c * b)) y⟫_ℂ := by
  classical
  unfold stinespringSesq
  refine Finsupp.sum_congr fun a _ => ?_
  rw [stinespringActFree, Finsupp.lmapDomain_apply]
  exact Finsupp.sum_mapDomain_index (fun b' => by simp)
    (fun b' y₁ y₂ => by simp [inner_add_right])

/-- **The formal adjoint law**: for the Stinespring form, `star c` acts
as the adjoint of `c`.  Associativity of multiplication, read through
the form. -/
theorem stinespringSesq_act_adjoint (c : A) (f g : A →₀ H) :
    stinespringSesq φ (stinespringActFree c f) g
      = stinespringSesq φ f (stinespringActFree (star c) g) := by
  rw [stinespringSesq_act_left, stinespringSesq_act_right]
  refine Finsupp.sum_congr fun a _ => ?_
  refine Finsupp.sum_congr fun b _ => ?_
  rw [star_mul, mul_assoc]

end CStarExactness
end GroupApproximation
