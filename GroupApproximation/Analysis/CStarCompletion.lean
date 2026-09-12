import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Analysis.CStarAlgebra.Classes

/-!
# The completion of a pre-C⋆-algebra is a C⋆-algebra

## Stage B of the tensor-product roadmap

`Analysis/CStarTensorProduct.lean` lays out what is missing for the minimal
tensor product and calls this **Stage B**, listing exactly four gaps:

> * `Star (Completion A)` --- extend the isometric involution along
>   `Completion.map`, then `star_involutive`, `star_add`, `star_mul` and
>   `norm_star` by density;
> * the C⋆-identity on the completion, again by density;
> * `Algebra ℂ (Completion A)` for **non**commutative `A` --- Mathlib's
>   `NormedAlgebra 𝕜 (Completion A)` instance is stated only for
>   `SeminormedCommRing A`, so the noncommutative case needs supplying;
> * assembly of `CStarAlgebra (Completion A)`.

All four are supplied here, and the assembly is `completionCStarAlgebra`.
With it, "the completion of `A ⊙ B` in the spatial norm" is a genuine
C⋆-algebra rather than a normed ⋆-algebra one hopes to complete.

## What is actually assumed

The input is a **pre-C⋆-algebra**: a complex normed ⋆-algebra satisfying the
C⋆-identity, *not* assumed complete.  In Mathlib's vocabulary that is
`[NormedRing A] [StarRing A] [NormedStarGroup A] [CStarRing A]
[NormedAlgebra ℂ A] [StarModule ℂ A]` --- exactly `CStarAlgebra A` with
`CompleteSpace A` deleted.  Every C⋆-normed ⋆-subalgebra of a C⋆-algebra is
one, and so is the algebraic tensor product `A ⊙ B` once the spatial norm is
installed on it as a `Norm` instance.

## How the proofs go

Uniformly by density.  Each law is an equation or inequality between two
continuous functions of one or two variables on `Completion A`; the set where
it holds is therefore closed (`isClosed_eq`, `isClosed_le`), and it contains
the dense image of `A`, where the law is the corresponding law in `A`.
`Completion.induction_on` and `induction_on₂` package that.  No completeness
of `A`, no approximate units, no functional calculus.

## The one instance-level caution

Mathlib already supplies `Algebra 𝕜 (Completion A)` when `A` is a
*commutative* seminormed ring.  The instance below is declared at priority
`100` so that Mathlib's wins whenever it applies, and this one is used only
in the noncommutative case that Mathlib does not cover.  The two agree (both
send `r` to `↑(algebraMap r)`), so the diamond is harmless, but the priority
keeps elaboration deterministic.

## Manuscript status

Infrastructure only; certifies no manuscript step.  `SO.16` and `RE.05` remain
**MISSING**: this closes Stage B of the roadmap, and exactness needs Stage C
(Takesaki's independence theorem) and Stage D on top of it.
-/

namespace GroupApproximation
namespace CStarCompletion

open UniformSpace UniformSpace.Completion

section StarRing

variable {A : Type*} [NormedRing A] [StarRing A] [NormedStarGroup A]

theorem uniformContinuous_star : UniformContinuous (star : A → A) :=
  star_isometry.uniformContinuous

/-- The involution on the completion, extended from `A` along
`Completion.map`. -/
noncomputable instance completionStar : Star (Completion A) where
  star := Completion.map star

@[simp] theorem star_coe (a : A) : star (↑a : Completion A) = ↑(star a) :=
  Completion.map_coe uniformContinuous_star a

omit [NormedStarGroup A] in
theorem continuous_star_completion :
    Continuous (star : Completion A → Completion A) :=
  Completion.continuous_map

/-- **The completion of a normed ⋆-ring is a ⋆-ring.**  Every law is an
identity between continuous functions, so each holds on a closed set
containing the dense image of `A`.

All three flat fields are given explicitly rather than letting the
`InvolutiveStar` parent be synthesized from a separate instance, so that there
is exactly one path to `star` on the completion and no structure diamond. -/
noncomputable instance completionStarRing : StarRing (Completion A) where
  star_involutive x := by
    refine Completion.induction_on x
      (isClosed_eq (continuous_star_completion.comp continuous_star_completion)
        continuous_id) ?_
    intro a
    rw [star_coe, star_coe, star_star]
  star_add x y := by
    refine Completion.induction_on₂ x y (isClosed_eq ?_ ?_) ?_
    · exact continuous_star_completion.comp continuous_add
    · exact (continuous_star_completion.comp continuous_fst).add
        (continuous_star_completion.comp continuous_snd)
    · intro a b
      rw [← Completion.coe_add, star_coe, star_coe, star_coe,
        show star (a + b) = star a + star b from StarAddMonoid.star_add a b,
        Completion.coe_add]
  star_mul x y := by
    refine Completion.induction_on₂ x y (isClosed_eq ?_ ?_) ?_
    · exact continuous_star_completion.comp continuous_mul
    · exact (continuous_star_completion.comp continuous_snd).mul
        (continuous_star_completion.comp continuous_fst)
    · intro a b
      rw [← Completion.coe_mul, star_coe, star_coe, star_coe,
        show star (a * b) = star b * star a from StarMul.star_mul a b,
        Completion.coe_mul]

/-- The involution is still isometric after completion. -/
noncomputable instance completionNormedStarGroup :
    NormedStarGroup (Completion A) where
  norm_star_le x := by
    refine Completion.induction_on x
      (isClosed_le (continuous_norm.comp continuous_star_completion)
        continuous_norm) ?_
    intro a
    rw [star_coe]
    simp only [Completion.norm_coe]
    exact (norm_star a).le

/-- **The C⋆-identity survives completion.**  It is an inequality between two
continuous functions, so it holds on the closure of the image of `A`. -/
noncomputable instance completionCStarRing [CStarRing A] :
    CStarRing (Completion A) where
  norm_mul_self_le x := by
    refine Completion.induction_on x
      (isClosed_le (continuous_norm.mul continuous_norm)
        (continuous_norm.comp (continuous_star_completion.mul continuous_id)))
      ?_
    intro a
    rw [star_coe, ← Completion.coe_mul]
    simp only [Completion.norm_coe]
    exact CStarRing.norm_mul_self_le a

end StarRing

/-! ## The complex structure, in the noncommutative case Mathlib does not cover -/

section Algebra

variable {A : Type*} [NormedRing A] [StarRing A] [NormedStarGroup A]
  [NormedAlgebra ℂ A] [StarModule ℂ A]

/-- The complex algebra structure on the completion of a **noncommutative**
normed complex algebra.  Mathlib supplies this only for a commutative `A`;
the priority keeps Mathlib's instance in front where it applies. -/
noncomputable instance (priority := 100) completionAlgebra :
    Algebra ℂ (Completion A) :=
  Algebra.ofModule
    (fun r x y => by
      refine Completion.induction_on₂ x y (isClosed_eq ?_ ?_) ?_
      · exact ((continuous_const_smul r).comp continuous_fst).mul continuous_snd
      · exact (continuous_const_smul r).comp (continuous_fst.mul continuous_snd)
      · intro a b
        rw [← Completion.coe_smul, ← Completion.coe_mul, ← Completion.coe_mul,
          ← Completion.coe_smul, smul_mul_assoc])
    (fun r x y => by
      refine Completion.induction_on₂ x y (isClosed_eq ?_ ?_) ?_
      · exact continuous_fst.mul ((continuous_const_smul r).comp continuous_snd)
      · exact (continuous_const_smul r).comp (continuous_fst.mul continuous_snd)
      · intro a b
        rw [← Completion.coe_smul, ← Completion.coe_mul, ← Completion.coe_mul,
          ← Completion.coe_smul, mul_smul_comm])

noncomputable instance (priority := 100) completionNormedAlgebra :
    NormedAlgebra ℂ (Completion A) where
  norm_smul_le r x := _root_.norm_smul_le r x

noncomputable instance completionStarModule : StarModule ℂ (Completion A) where
  star_smul r x := by
    refine Completion.induction_on x (isClosed_eq ?_ ?_) ?_
    · exact continuous_star_completion.comp (continuous_const_smul r)
    · exact (continuous_const_smul (star r)).comp continuous_star_completion
    · intro a
      rw [← Completion.coe_smul, star_coe, StarModule.star_smul r a,
        Completion.coe_smul, star_coe]

/-- **Stage B, assembled: the completion of a pre-C⋆-algebra is a
C⋆-algebra.**

The hypotheses are `CStarAlgebra A` with `CompleteSpace A` deleted.  Applied
to the algebraic tensor product `A ⊙ B` carrying the spatial norm of
`Analysis/CStarTensorProductSpatial`, this is the object the roadmap calls
`A ⊗_{π,ρ} B`.  It is still indexed by the chosen pair of representations:
making it canonical is Takesaki's theorem, which is Stage C and is not
touched here. -/
noncomputable instance completionCStarAlgebra [CStarRing A] :
    CStarAlgebra (Completion A) where

end Algebra

end CStarCompletion
end GroupApproximation
