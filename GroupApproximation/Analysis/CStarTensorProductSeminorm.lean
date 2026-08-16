import GroupApproximation.Analysis.CStarTensorProductAdjointable

/-!
# C⋆-seminorms on a complex ⋆-algebra, and the ones coming from representations

## Why this file exists

The minimal (spatial) tensor product `A ⊗_min B` is, by definition, the
completion of the algebraic tensor product `A ⊙ B` in the norm

  `‖x‖_min = ‖(π ⊗ ρ)(x)‖`,

the operator norm of the image of `x` under a product representation on
`H ⊗ K`, for faithful representations `π : A → B(H)`, `ρ : B → B(K)`.  Two
separate things have to be proved about that recipe:

1. the resulting function really is a C⋆-norm on the ⋆-algebra `A ⊙ B`;
2. it does not depend on the choice of `π` and `ρ` (Takesaki).

This file settles (1) **in complete generality**, once and for all: the
operator seminorm attached to *any* representation of a complex ⋆-algebra by
adjointable operators on an inner product space is a C⋆-seminorm, and is a
C⋆-norm as soon as the representation is injective.  (Only that direction is
proved.  The converse --- definiteness forces injectivity --- is immediate from
`seminorm_eq_zero_iff` but is not stated, so "exactly when", as an earlier
version of this paragraph put it, overstates what is here.)  When the product
representation of `A ⊙ B` on `H ⊗ K` is eventually constructed, its C⋆-property
is then immediate from `StarRep.isCStarSeminorm` below; nothing about tensor
products has to be re-proved.

Point (2) is the hard theorem and is **not** proved anywhere in this
development; see the roadmap in `CStarTensorProduct.lean`.

As in `CStarTensorProductAdjointable.lean`, no completeness is assumed
anywhere: a representation on a pre-Hilbert space already gives a C⋆-seminorm.
This is what allows the spatial construction to live on the *algebraic* tensor
product `H ⊗[ℂ] K`, whose completion Mathlib does not have.

## Contents

* `IsCStarSeminorm` --- a submultiplicative seminorm satisfying the
  C⋆-identity `p (star a * a) = p a * p a`.  Star-invariance is deliberately
  *not* an axiom: it is a theorem (`IsCStarSeminorm.map_star`).
* `IsCStarNorm` --- a definite C⋆-seminorm.
* `StarRep` --- a representation of a complex ⋆-algebra by adjointable
  operators on an inner product space.
* `StarRep.isCStarSeminorm`, `StarRep.isCStarNorm_of_injective`.

## Manuscript status

Infrastructure only; certifies no manuscript step.  The exactness and
nuclearity rows of `non_mf_groups_exist.tex` remain **MISSING**.
-/

namespace GroupApproximation
namespace CStarTensor

open scoped InnerProductSpace

universe u v

/-! ## C⋆-seminorms -/

/-- A **C⋆-seminorm** on a complex ⋆-algebra: a submultiplicative seminorm
satisfying the C⋆-identity.

Star-invariance is not assumed; it follows (`IsCStarSeminorm.map_star`). -/
structure IsCStarSeminorm {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A]
    (p : A → ℝ) : Prop where
  /-- A seminorm is nonnegative. -/
  nonneg : ∀ a : A, 0 ≤ p a
  /-- The triangle inequality. -/
  add_le : ∀ a b : A, p (a + b) ≤ p a + p b
  /-- Absolute homogeneity for the complex scalars. -/
  smul : ∀ (c : ℂ) (a : A), p (c • a) = ‖c‖ * p a
  /-- Submultiplicativity. -/
  mul_le : ∀ a b : A, p (a * b) ≤ p a * p b
  /-- The C⋆-identity. -/
  cstar : ∀ a : A, p (star a * a) = p a * p a

namespace IsCStarSeminorm

variable {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A] {p : A → ℝ}

/-- A C⋆-seminorm vanishes at zero. -/
theorem map_zero (h : IsCStarSeminorm p) : p 0 = 0 := by
  have hz : ((0 : ℂ) • (0 : A)) = (0 : A) := by rw [zero_smul]
  have := h.smul 0 0
  rw [hz] at this
  simpa using this

/-- One half of star-invariance.  If `p a = 0` this is nonnegativity, and
otherwise it is cancellation in the C⋆-identity against submultiplicativity. -/
theorem le_map_star (h : IsCStarSeminorm p) (a : A) : p a ≤ p (star a) := by
  have hkey : p a * p a ≤ p (star a) * p a := by
    have h1 : p (star a * a) ≤ p (star a) * p a := h.mul_le (star a) a
    rwa [h.cstar a] at h1
  rcases eq_or_lt_of_le (h.nonneg a) with hzero | hpos
  · rw [← hzero]
    exact h.nonneg (star a)
  · exact le_of_mul_le_mul_right hkey hpos

/-- **A C⋆-seminorm is star-invariant.**  This is a theorem, not an axiom. -/
theorem map_star (h : IsCStarSeminorm p) (a : A) : p (star a) = p a := by
  refine le_antisymm ?_ (h.le_map_star a)
  have h1 : p (star a) ≤ p (star (star a)) := h.le_map_star (star a)
  rwa [star_star] at h1

/-- The other form of the C⋆-identity. -/
theorem cstar' (h : IsCStarSeminorm p) (a : A) : p (a * star a) = p a * p a := by
  have h1 : p (star (star a) * star a) = p (star a) * p (star a) :=
    h.cstar (star a)
  rwa [star_star, h.map_star a] at h1

end IsCStarSeminorm

/-- A **C⋆-norm** on a complex ⋆-algebra: a definite C⋆-seminorm. -/
structure IsCStarNorm {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A]
    (p : A → ℝ) : Prop where
  /-- The underlying C⋆-seminorm.  Spelled as a field rather than by
  `extends`, so that the declaration is insensitive to the Lean version's
  placement of the `extends` clause relative to the `: Prop` ascription. -/
  isCStarSeminorm : IsCStarSeminorm p
  /-- Definiteness. -/
  eq_zero : ∀ a : A, p a = 0 → a = 0

/-! ## Representations by adjointable operators -/

/-- A **⋆-representation** of a complex ⋆-algebra `A` on an inner product
space `V`: an algebra homomorphism into the bounded operators, whose value at
`star a` is an adjoint of its value at `a`.

The target `V →L[ℂ] V` is not a `StarRing` unless `V` is complete, which is
why the ⋆-compatibility is carried by the unbundled relation `IsAdjoint`
rather than by asking for a `StarAlgHom`.  On a Hilbert space this is exactly
a ⋆-homomorphism into `B(V)`. -/
structure StarRep (A : Type u) (V : Type v) [Ring A] [StarRing A] [Algebra ℂ A]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] where
  /-- The underlying algebra homomorphism. -/
  hom : A →ₐ[ℂ] (V →L[ℂ] V)
  /-- The image of `star a` is an adjoint of the image of `a`. -/
  isAdjoint_star : ∀ a : A, IsAdjoint (hom a) (hom (star a))

namespace StarRep

variable {A : Type u} {V : Type v} [Ring A] [StarRing A] [Algebra ℂ A]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The operator seminorm attached to a ⋆-representation.

`noncomputable` because the operator norm on `V →L[ℂ] V` is
(`ContinuousLinearMap.hasOpNorm` is a `noncomputable` instance); nothing here
is meant to be evaluated. -/
noncomputable def seminorm (π : StarRep A V) : A → ℝ := fun a ↦ ‖π.hom a‖

@[simp] theorem seminorm_apply (π : StarRep A V) (a : A) :
    π.seminorm a = ‖π.hom a‖ := rfl

/-- The seminorm of a product is submultiplicative. -/
theorem seminorm_mul_le (π : StarRep A V) (a b : A) :
    π.seminorm (a * b) ≤ π.seminorm a * π.seminorm b := by
  have hmul : π.hom (a * b) = π.hom a * π.hom b := map_mul π.hom a b
  have hcomp : π.hom a * π.hom b = (π.hom a).comp (π.hom b) := rfl
  show ‖π.hom (a * b)‖ ≤ ‖π.hom a‖ * ‖π.hom b‖
  rw [hmul, hcomp]
  exact norm_comp_le_mul (π.hom a) (π.hom b)

/-- The seminorm is star-invariant, because the adjoint is isometric. -/
theorem seminorm_star (π : StarRep A V) (a : A) :
    π.seminorm (star a) = π.seminorm a :=
  (π.isAdjoint_star a).norm_eq

/-- **The C⋆-identity for the operator seminorm of a ⋆-representation.** -/
theorem seminorm_star_mul_self (π : StarRep A V) (a : A) :
    π.seminorm (star a * a) = π.seminorm a * π.seminorm a := by
  have hmul : π.hom (star a * a) = π.hom (star a) * π.hom a :=
    map_mul π.hom (star a) a
  have hcomp : π.hom (star a) * π.hom a = (π.hom (star a)).comp (π.hom a) := rfl
  show ‖π.hom (star a * a)‖ = ‖π.hom a‖ * ‖π.hom a‖
  rw [hmul, hcomp]
  exact (π.isAdjoint_star a).norm_comp_self

/-- **The operator seminorm of a ⋆-representation is a C⋆-seminorm.** -/
theorem isCStarSeminorm (π : StarRep A V) : IsCStarSeminorm π.seminorm where
  nonneg a := norm_nonneg (π.hom a)
  add_le a b := by
    show ‖π.hom (a + b)‖ ≤ ‖π.hom a‖ + ‖π.hom b‖
    rw [map_add π.hom a b]
    exact norm_add_le (π.hom a) (π.hom b)
  smul c a := by
    show ‖π.hom (c • a)‖ = ‖c‖ * ‖π.hom a‖
    rw [map_smul π.hom c a, norm_smul]
  mul_le := π.seminorm_mul_le
  cstar := π.seminorm_star_mul_self

/-- The seminorm vanishes exactly on the kernel of the representation. -/
theorem seminorm_eq_zero_iff (π : StarRep A V) (a : A) :
    π.seminorm a = 0 ↔ π.hom a = 0 := by
  constructor
  · intro h
    exact norm_eq_zero.mp h
  · intro h
    show ‖π.hom a‖ = 0
    rw [h, norm_zero]

/-- **A faithful ⋆-representation gives a C⋆-norm.**  This is the abstract form
of "the spatial norm is a norm": once a faithful product representation of
`A ⊙ B` on `H ⊗ K` is available, this supplies every property of `‖·‖_min`
except independence of the chosen representations. -/
theorem isCStarNorm_of_injective (π : StarRep A V) (hπ : Function.Injective π.hom) :
    IsCStarNorm π.seminorm where
  isCStarSeminorm := π.isCStarSeminorm
  eq_zero a ha := by
    have h0 : π.hom a = 0 := (π.seminorm_eq_zero_iff a).mp ha
    have hz : π.hom (0 : A) = 0 := map_zero π.hom
    exact hπ (by rw [h0, hz])

end StarRep

end CStarTensor
end GroupApproximation
