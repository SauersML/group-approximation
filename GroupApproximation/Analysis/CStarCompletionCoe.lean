import GroupApproximation.Analysis.CStarCompletion

/-!
# The canonical map into a completion, as a ⋆-algebra homomorphism

`Analysis/CStarCompletion` makes `Completion A` a C⋆-algebra and
`Analysis/CStarCompletionHom` extends a ⋆-homomorphism *out of* `A` across the
completion.  This file supplies the remaining arrow: the canonical map
`A → Completion A` is itself a ⋆-algebra homomorphism.

## Why this is the last gate for `PRE.19`/`MC.02`

`MaximalCStarAnyUniverse.maximalGroupCStar_existsUnique_lift_of_factors`
reduces the universal property of `Cmax(G)` at an arbitrary universe to a
factoring datum `(B₀, ρ₀, j)` with `B₀` at the universe of `G`.  Along the
route `ℂ[G] → … → Completion(…) = B₀`, the map `j` is
`CStarCompletionHom.extendStarAlgHom` and the *distinguished unitaries* `ρ₀ g`
are the images of the group elements — which requires knowing that the map
into the completion carries the ⋆-algebra structure, so that
`CStarRepresentationNorm.map_mem_unitary` applies to it and `ρ₀ g` is a
unitary of `B₀`.  That is `coeStarAlgHom` below.

Mathlib has `UniformSpace.Completion.coeRingHom`, the same map as a *ring*
homomorphism.  It carries neither the scalars nor the involution, and a
`→⋆ₐ[ℂ]` is what the factoring datum consumes.

## A correction to the route this file was written for

An earlier note of mine claimed the null-ideal quotient could be deleted
outright, because mathlib's `[SeminormedRing A] : NormedRing (Completion A)`
means the completion separates the seminorm by itself.  The first half is
true; the conclusion was too strong.  `CStarRing E` is stated over
`[NonUnitalNormedRing E]`, and `NonUnitalNormedRing extends MetricSpace` --
not `PseudoMetricSpace` -- so the C⋆-identity **cannot be stated as a class
for a merely seminormed algebra**.  Taking the seminormed route therefore
forces the C⋆-identity to become an explicit hypothesis, turning
`completionCStarRing` and `completionCStarAlgebra` from instances into
hypothesis-taking definitions and propagating that through
`CStarNormBundled`.  The quotient route needs two small additive lemmas
instead and touches no existing instance.  Both routes need *this* file.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace CStarCompletion

open UniformSpace UniformSpace.Completion

section Coe

-- `StarModule ℂ A` is deliberately absent: a `→⋆ₐ[ℂ]` needs `Algebra` and
-- `Star` on each side, and the completion's `Algebra ℂ` instance is built by
-- density from the module laws without touching `star`.
variable (A : Type*) [NormedRing A] [StarRing A] [NormedStarGroup A]
  [NormedAlgebra ℂ A]

/-- **The canonical map into the completion is a ⋆-algebra homomorphism.**

Every field is one of the `Completion.coe_*` transport lemmas, except the
scalar one, where `algebraMap ℂ (Completion A) r` has to be recognized as the
image of `algebraMap ℂ A r`; both sides are `r • 1`, so `Completion.coe_smul`
and `Completion.coe_one` settle it. -/
noncomputable def coeStarAlgHom : A →⋆ₐ[ℂ] Completion A where
  toFun a := (a : Completion A)
  -- tactic form throughout: `rw` instantiates these regardless of whether the
  -- carrier is an explicit or implicit argument of the transport lemma.
  map_one' := by rw [Completion.coe_one]
  map_zero' := by rw [Completion.coe_zero]
  map_add' a b := by rw [Completion.coe_add]
  map_mul' a b := by rw [Completion.coe_mul]
  commutes' r := by
    show ((algebraMap ℂ A r : A) : Completion A) = algebraMap ℂ (Completion A) r
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      Completion.coe_smul, Completion.coe_one]
  map_star' a := (star_coe a).symm

@[simp] theorem coeStarAlgHom_apply (a : A) :
    coeStarAlgHom A a = (a : Completion A) := rfl

/-- The canonical map is isometric, so in particular injective on a genuinely
normed `A`: the completion adds points but identifies none. -/
theorem norm_coeStarAlgHom (a : A) : ‖coeStarAlgHom A a‖ = ‖a‖ :=
  Completion.norm_coe a

/-- The canonical map has dense range.  With
`CStarCompletionHom.extendStarAlgHom_unique` this is what makes an extension
across the completion unique. -/
theorem denseRange_coeStarAlgHom : DenseRange (coeStarAlgHom A) :=
  Completion.denseRange_coe

end Coe

end CStarCompletion
end GroupApproximation
