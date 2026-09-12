import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.Algebra.StarSubalgebra

/-!
# Strongly continuous C-star flows and cocycle conjugacy

These are the actual dynamical notions used in STW Problem LV.  They are
introduced independently of the quasifree model so the later classification
statement is literally a theorem about cocycle conjugacy of C-star flows.
-/

namespace STW.Actual

noncomputable section

universe u v

/-- A unitary element of a unital star algebra, recorded by its two defining
relations.  We keep the element bundled because cocycles are functions into
this type. -/
structure UnitaryElement (A : Type u) [Ring A] [StarRing A] where
  val : A
  star_mul : star val * val = 1
  mul_star : val * star val = 1

namespace UnitaryElement

variable {A : Type u} [Ring A] [StarRing A]

instance : Coe (UnitaryElement A) A := ⟨UnitaryElement.val⟩

@[simp] theorem coe_mk (a : A) (h₁ : star a * a = 1) (h₂ : a * star a = 1) :
    ((⟨a, h₁, h₂⟩ : UnitaryElement A) : A) = a := rfl

end UnitaryElement

/-- A strongly continuous one-parameter automorphism group of a C-star
algebra.  The group law is encoded by a monoid homomorphism from the
multiplicative copy of the additive real line. -/
structure CStarFlow (A : Type u) [CStarAlgebra A] where
  action : Multiplicative ℝ →* (A ≃⋆ₐ[ℂ] A)
  stronglyContinuous : ∀ a : A,
    Continuous fun t : ℝ => action (Multiplicative.ofAdd t) a

namespace CStarFlow

variable {A : Type u} [CStarAlgebra A]

/-- Time-`t` automorphism.

Named `atTime`, not `at`: `at` is a reserved token (`rw ... at h`, `simp at h`,
...) and cannot be a declaration name -- attempting it desyncs the parser for
the rest of the file, which is why this single name change is the whole fix
for a cascade of otherwise-unrelated-looking errors below it. -/
def atTime (α : CStarFlow A) (t : ℝ) : A ≃⋆ₐ[ℂ] A :=
  α.action (Multiplicative.ofAdd t)

@[simp] theorem atTime_zero (α : CStarFlow A) : α.atTime 0 = 1 := by
  exact map_one α.action

@[simp] theorem atTime_add (α : CStarFlow A) (s t : ℝ) :
    α.atTime (s + t) = α.atTime s * α.atTime t := by
  exact map_mul α.action (Multiplicative.ofAdd s) (Multiplicative.ofAdd t)

@[simp] theorem atTime_zero_apply (α : CStarFlow A) (a : A) : α.atTime 0 a = a := by
  rw [atTime_zero]
  rfl

@[simp] theorem atTime_add_apply (α : CStarFlow A) (s t : ℝ) (a : A) :
    α.atTime (s + t) a = α.atTime s (α.atTime t a) := by
  rw [atTime_add]
  rfl

end CStarFlow

/-- A norm-continuous unitary cocycle for a flow `α`, satisfying
`u_{s+t} = u_s α_s(u_t)`. -/
structure UnitaryCocycle {A : Type u} [CStarAlgebra A] (α : CStarFlow A) where
  u : ℝ → UnitaryElement A
  continuous_coe : Continuous fun t : ℝ => ((u t : UnitaryElement A) : A)
  zero : ((u 0 : UnitaryElement A) : A) = 1
  cocycle : ∀ s t : ℝ,
    ((u (s + t) : UnitaryElement A) : A) =
      ((u s : UnitaryElement A) : A) * α.atTime s ((u t : UnitaryElement A) : A)

/-- `α` and `β` are cocycle conjugate when a star-algebra isomorphism carries
`α` to a unitary cocycle perturbation of `β` at every time.  This is the plain
(no time rescaling) notion used in STW Problem LV. -/
def CocycleConjugate {A : Type u} {B : Type v}
    [CStarAlgebra A] [CStarAlgebra B] (α : CStarFlow A) (β : CStarFlow B) : Prop :=
  ∃ θ : A ≃⋆ₐ[ℂ] B, ∃ u : UnitaryCocycle β,
    ∀ t : ℝ, ∀ a : A,
      θ (α.atTime t a) =
        ((u.u t : UnitaryElement B) : B) * β.atTime t (θ a) *
          star ((u.u t : UnitaryElement B) : B)

end

end STW.Actual
