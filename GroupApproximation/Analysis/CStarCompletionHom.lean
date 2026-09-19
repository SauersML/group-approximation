import GroupApproximation.Analysis.CStarCompletion

/-!
# Extending a ⋆-homomorphism along the completion

`Analysis/CStarCompletion` makes `Completion A` a C⋆-algebra when `A` is a
pre-C⋆-algebra.  This file supplies the other half of the universal property
of that completion: a ⋆-homomorphism out of `A` into a C⋆-algebra extends to
the completion, uniquely, as a ⋆-homomorphism.

## Why this is needed and what it is for

It is step (iii) of the route to the universal property of `Cmax(G)` for a
target in an arbitrary universe (proof-ledger rows `PRE.19` and `MC.02`).
`Analysis/MaximalCStarAnyUniverse.maximalGroupCStar_existsUnique_lift_of_factors`
reduces that row to producing, for `ρ : G → U(B)` with `B` in any universe, a
C⋆-algebra `B₀` **at the universe of `G`** together with `ρ₀ : G → U(B₀)` and
a unital ⋆-homomorphism `j : B₀ → B` with `j ∘ ρ₀ = ρ`.  The only construction
of such a `B₀` that stays at the universe of `G` is a completion, so `j` is
necessarily an extension along a completion --- which is exactly
`extendStarAlgHom` below.

Mathlib has `UniformSpace.Completion.extensionHom`, which extends a *ring*
homomorphism.  It does not extend the scalars or the involution, and a
`→⋆ₐ[ℂ]` is what the factoring datum requires.

## The uniform-continuity hypothesis, and why it costs nothing here

`extendStarAlgHom` takes `UniformContinuous f` as a hypothesis rather than
deriving it.  A ⋆-homomorphism from a *Banach* ⋆-algebra to a C⋆-algebra is
automatically contractive, but `A` here is exactly the case that is **not**
complete, so that theorem does not apply and assuming continuity would be
circular.  In the intended application the map is isometric by construction
--- the norm on `A` is *defined* as `‖ρ̃(·)‖_B` --- so
`uniformContinuous_of_norm_map` below discharges the hypothesis outright, and
nothing is left conditional.

## Contents

* `uniformContinuous_of_norm_map` --- a norm-preserving additive map is
  uniformly continuous.
* `extendStarAlgHom` --- the extension, as a `Completion A →⋆ₐ[ℂ] B`, with
  `extendStarAlgHom_coe` computing it on the dense image.
* `extendStarAlgHom_unique` --- uniqueness among *continuous* extensions,
  which is the form density gives.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.  `PRE.19`/`MC.02`
still need the involution on the group algebra `ℂ[G]`, which Mathlib does not
have at the pinned revision (there is no `star` anywhere under
`Mathlib/Algebra/MonoidAlgebra/`), and the assembly on top of it.
-/

namespace GroupApproximation
namespace CStarCompletion

open UniformSpace UniformSpace.Completion

/-! ### Uniform continuity from norm preservation

Stated in its own section, carrying only the instances it uses: a
⋆-homomorphism needs `Star` and `Algebra` on the source but neither
`NormedStarGroup` nor `StarModule`, so including those here would leave
section variables unused. -/

section Isometric

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℂ A]
variable {B : Type*} [CStarAlgebra B]

/-- A norm-preserving additive map between normed groups is uniformly
continuous.  In the intended application the ⋆-homomorphism is isometric
because the norm on the source is defined as the norm of the image. -/
theorem uniformContinuous_of_norm_map (f : A →⋆ₐ[ℂ] B)
    (h : ∀ a : A, ‖f a‖ = ‖a‖) : UniformContinuous (f : A → B) :=
  (AddMonoidHomClass.isometry_of_norm f h).uniformContinuous

/-- A norm-*decreasing* ⋆-homomorphism is uniformly continuous.

The isometric form above is not enough for the maximal seminorm.  There the norm
on the source is the supremum over *all* representations, which dominates the
norm of any one of them and in general dominates it strictly, so the map to a
single target contracts rather than preserves.  Contraction is all uniform
continuity needs. -/
theorem uniformContinuous_of_norm_le (f : A →⋆ₐ[ℂ] B)
    (h : ∀ a : A, ‖f a‖ ≤ ‖a‖) : UniformContinuous (f : A → B) := by
  refine (LipschitzWith.mk_one fun x y ↦ ?_).uniformContinuous
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact h (x - y)

end Isometric

section Extend

-- `StarModule ℂ A` is deliberately absent: the completion's `Algebra ℂ`
-- instance is built by density from the module laws and never touches `star`,
-- and a `→⋆ₐ[ℂ]` needs only `Algebra` and `Star` on each side.  Including it
-- would leave it unused in `extendStarAlgHom_coe`.
variable {A : Type*} [NormedRing A] [StarRing A] [NormedStarGroup A]
  [NormedAlgebra ℂ A]
variable {B : Type*} [CStarAlgebra B]

/-- **A ⋆-homomorphism into a C⋆-algebra extends along the completion.**
Every law is an identity between continuous functions, so it holds on the
closure of the image of `A`, where it is the corresponding law in `A`.

`f` and `hf` are explicit binders rather than section variables: a plain
hypothesis is not auto-included, and `extendStarAlgHom`'s *type* does not
mention `hf`, so as a section variable it would not be in scope inside these
proofs. -/
noncomputable def extendStarAlgHom (f : A →⋆ₐ[ℂ] B)
    (hf : UniformContinuous (f : A → B)) : Completion A →⋆ₐ[ℂ] B where
  toFun := Completion.extension (f : A → B)
  map_one' := by
    rw [← Completion.coe_one, Completion.extension_coe hf, map_one]
  map_zero' := by
    rw [← Completion.coe_zero, Completion.extension_coe hf, map_zero]
  map_add' x y := by
    refine Completion.induction_on₂ x y (isClosed_eq ?_ ?_) ?_
    · exact Completion.continuous_extension.comp continuous_add
    · exact (Completion.continuous_extension.comp continuous_fst).add
        (Completion.continuous_extension.comp continuous_snd)
    · intro a b
      rw [← Completion.coe_add, Completion.extension_coe hf, Completion.extension_coe hf,
        Completion.extension_coe hf, map_add]
  map_mul' x y := by
    refine Completion.induction_on₂ x y (isClosed_eq ?_ ?_) ?_
    · exact Completion.continuous_extension.comp continuous_mul
    · exact (Completion.continuous_extension.comp continuous_fst).mul
        (Completion.continuous_extension.comp continuous_snd)
    · intro a b
      rw [← Completion.coe_mul, Completion.extension_coe hf, Completion.extension_coe hf,
        Completion.extension_coe hf, map_mul]
  commutes' r := by
    have hmap : (algebraMap ℂ (Completion A) r)
        = ((algebraMap ℂ A r : A) : Completion A) := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        Completion.coe_smul, Completion.coe_one]
    rw [hmap, Completion.extension_coe hf]
    exact f.commutes r
  map_star' x := by
    refine Completion.induction_on x (isClosed_eq ?_ ?_) ?_
    · exact Completion.continuous_extension.comp continuous_star_completion
    · exact continuous_star.comp Completion.continuous_extension
    · intro a
      rw [star_coe, Completion.extension_coe hf, Completion.extension_coe hf, map_star]

@[simp] theorem extendStarAlgHom_coe (f : A →⋆ₐ[ℂ] B)
    (hf : UniformContinuous (f : A → B)) (a : A) :
    extendStarAlgHom f hf (a : Completion A) = f a :=
  Completion.extension_coe hf a

/-- **Uniqueness of the extension.**  Density of `A` in its completion forces
any two continuous extensions to agree; continuity is the only hypothesis
needed, and every ⋆-homomorphism between C⋆-algebras has it. -/
theorem extendStarAlgHom_unique (f : A →⋆ₐ[ℂ] B)
    (hf : UniformContinuous (f : A → B)) (g : Completion A →⋆ₐ[ℂ] B)
    (hg : Continuous (g : Completion A → B))
    (hga : ∀ a : A, g (a : Completion A) = f a) :
    g = extendStarAlgHom f hf := by
  have hcont : Continuous ((extendStarAlgHom f hf : Completion A → B)) :=
    Completion.continuous_extension
  refine DFunLike.ext _ _ fun x ↦ ?_
  refine Completion.induction_on x (isClosed_eq hg hcont) ?_
  intro a
  rw [hga a, extendStarAlgHom_coe f hf a]

end Extend

end CStarCompletion
end GroupApproximation
