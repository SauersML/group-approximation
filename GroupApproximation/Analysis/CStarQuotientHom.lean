import GroupApproximation.Analysis.CStarSeminormQuotient

/-!
# The quotient by a star-stable ideal, as a ⋆-algebra

`Analysis/CStarSeminormQuotient` gives `A ⧸ I` its involution and `⋆`-ring
structure for a star-stable two-sided ideal `I`.  This file adds the two things
the maximal-C⋆-algebra assembly still needs from that quotient, both additive:
the compatibility of the involution with the complex scalars, and the universal
property for ⋆-algebra homomorphisms.

## Why these two, and why here

By the accounting in `Analysis/CStarCompletionCoe`, proof-ledger rows `PRE.19`
and `MC.02` are gated on exactly this pair plus wiring.  The route is

  `ℂ[G]` --`ρ̃`--> `B`,  factored as
  `ℂ[G]` --`mk`--> `ℂ[G] ⧸ N` --`coe`--> `Completion(…)` = `B₀` --`j`--> `B`,

and `j` is built by extending, across the completion, the map that `ρ̃` induces
on the quotient.  `quotientStarLift` is what produces that induced map, and
`quotientStarModule` is what lets `WithCStarNorm` see the quotient as a complex
⋆-algebra at all.

Neither is deep.  They are recorded because the alternative --- generalizing
`CStarCompletion` from `NormedRing` to `SeminormedRing` so that the quotient
could be skipped --- is *not* available: `CStarRing` is stated over
`NonUnitalNormedRing`, which at this pin extends `MetricSpace` rather than
`PseudoMetricSpace`, so the C⋆-identity cannot be a class for a merely
seminormed algebra.  That route would convert two working instances into
hypothesis-carrying definitions; this pair touches no existing instance.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace CStarTensor

universe u v

section QuotientHom

variable {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A]
  (I : Ideal A) [I.IsTwoSided] [IsStarStable I]

/-- **The involution on the quotient is conjugate-linear.**  With the `⋆`-ring
structure of `CStarSeminormQuotient` this makes `A ⧸ I` a complex ⋆-algebra,
which is what `IsCStarSeminorm` and `WithCStarNorm` require of it. -/
noncomputable instance quotientStarModule [StarModule ℂ A] :
    StarModule ℂ (A ⧸ I) where
  star_smul c x := by
    -- `QuotientAddGroup.induction_on` produces a representative in
    -- `A ⧸ Submodule.toAddSubgroup I`, which is only *definitionally* `A ⧸ I`;
    -- every subsequent `rw` then fails as not type-correct at `instances`
    -- transparency.  Take the representative through `Ideal.Quotient` instead.
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← quotient_mk_smul I c a, quotient_star_mk, quotient_star_mk,
      StarModule.star_smul c a, quotient_mk_smul]

/-- **The universal property of the quotient, for ⋆-algebra homomorphisms.**
A ⋆-homomorphism killing `I` factors through `A ⧸ I`, still as a
⋆-homomorphism.

Mathlib's `Ideal.Quotient.lift` supplies the ring homomorphism; what is added
here is that the factored map respects the complex scalars and the
involution. -/
noncomputable def quotientStarLift {B : Type v} [Ring B] [StarRing B]
    [Algebra ℂ B] (f : A →⋆ₐ[ℂ] B) (hf : ∀ a : A, a ∈ I → f a = 0) :
    (A ⧸ I) →⋆ₐ[ℂ] B where
  toFun := Ideal.Quotient.lift I f.toAlgHom.toRingHom hf
  map_one' := map_one _
  map_mul' := map_mul _
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' r := by
    rw [← Ideal.Quotient.mk_algebraMap ℂ I r, Ideal.Quotient.lift_mk]
    exact f.commutes r
  map_star' x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [quotient_star_mk, Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk]
    exact StarHomClass.map_star f a

@[simp] theorem quotientStarLift_mk {B : Type v} [Ring B] [StarRing B]
    [Algebra ℂ B] (f : A →⋆ₐ[ℂ] B) (hf : ∀ a : A, a ∈ I → f a = 0) (a : A) :
    quotientStarLift I f hf (Ideal.Quotient.mk I a) = f a :=
  Ideal.Quotient.lift_mk I _ hf

end QuotientHom

/-! ## The hypothesis in the case the assembly meets

For the seminorm `p = ‖f ·‖` the null ideal is exactly where `f` vanishes, so
the hypothesis of `quotientStarLift` is discharged by the definition of the
norm rather than by an argument. -/

section Vanishing

variable {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A]
variable {B : Type v} [CStarAlgebra B]

/-- A ⋆-homomorphism into a C⋆-algebra kills exactly the elements its pulled
back seminorm kills.  This is the hypothesis `quotientStarLift` asks for, in
the case where the seminorm is `‖f ·‖`. -/
theorem eq_zero_of_norm_eq_zero (f : A →⋆ₐ[ℂ] B) {a : A} (ha : ‖f a‖ = 0) :
    f a = 0 :=
  norm_eq_zero.mp ha

end Vanishing

end CStarTensor
end GroupApproximation
