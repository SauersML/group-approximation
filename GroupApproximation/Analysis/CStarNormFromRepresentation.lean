import GroupApproximation.Algebra.GroupRingStar
import GroupApproximation.Analysis.CStarSeminormQuotient

/-!
# The C⋆-seminorm a unitary representation puts on the group ring

## Where this sits

Proof-ledger rows `PRE.19` and `MC.02` need the universal property of
`Cmax(G)` for a target `B` in an *arbitrary* universe.
`Analysis/MaximalCStarAnyUniverse.maximalGroupCStar_existsUnique_lift_of_factors`
reduces that to producing, for `ρ : G → U(B)`, a C⋆-algebra `B₀` **at the
universe of `G`** with `ρ₀ : G → U(B₀)` and a ⋆-homomorphism `j : B₀ → B`
carrying `ρ₀` to `ρ`.  The route is

  `ℂ[G]`  --(seminorm `‖ρ̃(·)‖_B`)-->  a pre-C⋆-algebra  --(completion)-->  `B₀`,

and `ℂ[G] : Type u` is what keeps `B₀` at the universe of `G`.

This file is the **front end** of that route: it puts the seminorm on `ℂ[G]`
and records the two facts about unitaries the assembly needs.  The pieces
downstream already exist --- `CStarSeminormQuotient` descends a C⋆-seminorm to
a C⋆-norm, `CStarNormBundled` turns that into a pre-C⋆-algebra,
`CStarCompletion` completes it to a C⋆-algebra, and `CStarCompletionHom`
extends `ρ̃` across the completion to give `j`.

## Contents

* `repSeminorm`, `isCStarSeminorm_repSeminorm` --- the pullback along the
  ⋆-homomorphism `ρ̃ = GroupRingStar.unitaryLift ρ`, so `‖ρ̃(·)‖_B` is a
  C⋆-seminorm on `ℂ[G]`.
* `single_mem_unitary` --- each group element is a unitary of `ℂ[G]`.  This is
  what makes `ρ₀` land in the unitary group downstream.
* `map_mem_unitary` --- a ⋆-homomorphism carries unitaries to unitaries, so
  that property survives every arrow of the route above.

## What is deliberately not here

The assembly itself.  It needs two further pieces that do not exist yet: the
universal property of the null-ideal quotient *for ⋆-algebra homomorphisms*
(so `ρ̃` descends), and the canonical map into a completion as a ⋆-algebra
homomorphism (so `ρ₀` is defined).  Both are small and neither is stated here
rather than half-stated.

There is also a simplification worth recording before anyone writes the
assembly: mathlib's `NormedRing (Completion A)` instance takes a
**`SeminormedRing`** and returns a *normed* ring, because `Completion` is
already separated.  So the null-ideal quotient can be skipped entirely if
`CStarCompletion` is generalized from `NormedRing` to `SeminormedRing` --- the
completion kills the null ideal by itself.  That is a strictly shorter route
than quotient-then-complete, and it is why no quotient appears in this file.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.  `PRE.19`/`MC.02`
remain open at the existence half, with `maximalGroupCStar_lift_unique`
continuing to close the uniqueness half at every universe.
-/

namespace GroupApproximation
namespace CStarRepresentationNorm

open CStarTensor

universe u v

/-! ## Unitaries -/

/-- **A ⋆-homomorphism carries unitaries to unitaries.**  Used at each arrow of
the route `ℂ[G] → ℂ[G]/N → completion`, so that the distinguished unitaries
survive to the end. -/
theorem map_mem_unitary {A : Type*} {B : Type*} [Semiring A] [StarRing A]
    [Algebra ℂ A] [Semiring B] [StarRing B] [Algebra ℂ B]
    (f : A →⋆ₐ[ℂ] B) {u : A} (hu : u ∈ unitary A) : f u ∈ unitary B := by
  refine ⟨?_, ?_⟩
  · have h : star (f u) * f u = f (star u * u) := by
      rw [map_mul f (star u) u, StarHomClass.map_star f u]
    rw [h, hu.1, map_one]
  · have h : f u * star (f u) = f (u * star u) := by
      rw [map_mul f u (star u), StarHomClass.map_star f u]
    rw [h, hu.2, map_one]

/-- **Every group element is a unitary of the group ring.**  With
`map_mem_unitary` this is what puts `ρ₀` in the unitary group of the
completion. -/
theorem single_mem_unitary {G : Type u} [Group G] (g : G) :
    MonoidAlgebra.single g (1 : ℂ) ∈ unitary (MonoidAlgebra ℂ G) := by
  refine ⟨?_, ?_⟩
  · rw [GroupRingStar.star_single, MonoidAlgebra.single_mul_single, star_one,
      one_mul, inv_mul_cancel]
    exact MonoidAlgebra.one_def.symm
  · rw [GroupRingStar.star_single, MonoidAlgebra.single_mul_single, star_one,
      one_mul, mul_inv_cancel]
    exact MonoidAlgebra.one_def.symm

/-! ## The seminorm a representation induces -/

section Representation

variable {G : Type u} [Group G] {B : Type v} [CStarAlgebra B]

/-- The seminorm `x ↦ ‖ρ̃(x)‖_B` on the group ring, where `ρ̃` is the
⋆-homomorphism extending the unitary representation `ρ`. -/
noncomputable def repSeminorm (rho : G →* unitary B) :
    MonoidAlgebra ℂ G → ℝ :=
  fun x ↦ ‖GroupRingStar.unitaryLift (R := ℂ) rho x‖

@[simp] theorem repSeminorm_apply (rho : G →* unitary B) (x : MonoidAlgebra ℂ G) :
    repSeminorm rho x = ‖GroupRingStar.unitaryLift (R := ℂ) rho x‖ := rfl

/-- **The representation seminorm is a C⋆-seminorm.**  It is the norm of `B`
pulled back along `ρ̃`, so this is `IsCStarSeminorm.comp` applied to
`isCStarSeminorm_norm`; nothing about the group ring is re-proved. -/
theorem isCStarSeminorm_repSeminorm (rho : G →* unitary B) :
    IsCStarSeminorm (repSeminorm rho) :=
  isCStarSeminorm_norm.comp (GroupRingStar.unitaryLift (R := ℂ) rho)

/-- The seminorm of a group element is the norm of its unitary image, hence
`1` when `B` is nontrivial.  Recorded because it is what shows the
distinguished elements stay unitary after completing. -/
theorem repSeminorm_single (rho : G →* unitary B) (g : G) :
    repSeminorm rho (MonoidAlgebra.single g (1 : ℂ)) = ‖(rho g : B)‖ := by
  show ‖GroupRingStar.unitaryLift (R := ℂ) rho (MonoidAlgebra.single g 1)‖
    = ‖(rho g : B)‖
  rw [GroupRingStar.unitaryLift_single, one_smul]

end Representation

end CStarRepresentationNorm
end GroupApproximation
