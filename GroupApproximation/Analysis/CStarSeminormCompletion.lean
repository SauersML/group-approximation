import GroupApproximation.Analysis.CStarNormBundled
import GroupApproximation.Analysis.CStarQuotientHom
import GroupApproximation.Analysis.CStarCompletionCoe
import GroupApproximation.Analysis.CStarCompletionHom
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# The C⋆-algebra a C⋆-seminorm envelops

Given a C⋆-seminorm `p` on a complex ⋆-algebra `A`, this file assembles

  `A` --`mk`--> `A ⧸ N(p)` --retag--> pre-C⋆-algebra --complete--> `SeminormCompletion p`

and proves the universal property of the result: a ⋆-homomorphism out of `A`
that `p` dominates extends to the completion, uniquely.

Every arrow already existed; only the assembly is new.
`CStarSeminormQuotient` descends `p` to a C⋆-norm on the quotient by its null
ideal, `CStarQuotientHom` supplies the quotient map and the quotient's universal
property for ⋆-homomorphisms, `CStarNormBundled` retags the quotient so the
descended norm *is* its norm, `CStarCompletion` makes the completion of such a
pre-C⋆-algebra a C⋆-algebra, and `CStarCompletionCoe`/`CStarCompletionHom`
supply the canonical map into a completion and the extension across it.

## Why the universe bookkeeping is the point

`SeminormCompletion` lies in the universe of `A` — a quotient of `A` and then a
completion, neither of which leaves it — while the target `B` of the universal
property below is quantified at an *independent* universe.  That asymmetry is
the whole reason this file exists.  The maximal group C⋆-algebra of
`Analysis/MaximalGroupCStar` is a bounded product indexed by representations
whose carriers are required to lie in one fixed universe, so its universal
property is stated only for targets there; a representation on a `B` anywhere
else is not a coordinate of that product.  Running a representation through the
seminorm it puts on the group ring erases the universe of `B` — a seminorm on
`ℂ[G]` is a function `ℂ[G] → ℝ` no matter where the representation lives — and
what comes back out is a C⋆-algebra at the universe of the *group*, through
which the representation factors.  That is what
`Analysis/MaximalCStarAllUniverses` does with this file.

## Where `StarModule ℂ A` is and is not needed

It is not needed to *form* the envelope: the norm, the uniformity and the
completion of the retagged quotient are built from the additive and
multiplicative structure alone.  It is needed for the envelope to be a
C⋆-*algebra*, which is what makes a ⋆-homomorphism out of it contractive, so it
appears exactly on the C⋆-structure instance and on the two statements that use
continuity.  Carrying it as a section variable instead would leave it unused in
most declarations here, which the unused-variable linter rejects.

## Manuscript status

Infrastructure.  It certifies no manuscript step by itself; it is what
`Analysis/MaximalCStarAllUniverses` and
`Analysis/MaximalCStarPrintedCompletion` are built from.
-/

namespace GroupApproximation
namespace CStarTensor

open scoped CStarAlgebra

noncomputable section

universe u v

section Envelope

variable {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A] {p : A → ℝ}

/-- **The C⋆-algebra a C⋆-seminorm envelops**: kill the null ideal, norm the
quotient by the descended seminorm, complete.

Stated as an `abbrev` so that instance search sees the completion and finds the
structures `Analysis/CStarCompletion` puts on it, exactly as `MaximalGroupCStar`
is an `abbrev` for its subalgebra. -/
abbrev SeminormCompletion (h : IsCStarSeminorm p) : Type u :=
  UniformSpace.Completion (WithCStarNorm h.isCStarNorm_quotientNorm)

/-- The C⋆-algebra structure, named on the abbreviation rather than left to be
rediscovered through it at each use.  This is what `MaximalGroupCStar` does with
`maximalGroupCStarCStarAlgebra`, and for the same reason: the contractivity of a
⋆-homomorphism out of this algebra is found through its C⋆-structure, and
instance search should not have to unfold a completion of a retagged quotient to
get there. -/
instance seminormCompletionCStarAlgebra [StarModule ℂ A] (h : IsCStarSeminorm p) :
    CStarAlgebra (SeminormCompletion h) :=
  inferInstanceAs (CStarAlgebra
    (UniformSpace.Completion (WithCStarNorm h.isCStarNorm_quotientNorm)))

/-- The pre-C⋆-algebra the completion is taken of: the quotient by the null
ideal, retagged so that the descended seminorm is its norm.

This is the quotient map read into the retagged copy, which is the same type,
so the field proofs are `quotientStarMk`'s.  Composing with a generic retagging
arrow would say the same thing at the cost of a dependency on the module that
owns it. -/
def toPreCompletion (h : IsCStarSeminorm p) :
    A →⋆ₐ[ℂ] WithCStarNorm h.isCStarNorm_quotientNorm where
  toFun := Ideal.Quotient.mk h.nullIdeal
  map_one' := map_one _
  map_mul' _ _ := map_mul _ _ _
  map_zero' := map_zero _
  map_add' _ _ := map_add _ _ _
  commutes' _ := rfl
  map_star' a := quotient_star_mk h.nullIdeal a

/-- The quotient map is surjective and the retagging is the identity, so `A`
exhausts the pre-C⋆-algebra.  This is what makes the image of `A` dense in the
completion. -/
theorem toPreCompletion_surjective (h : IsCStarSeminorm p) :
    Function.Surjective (toPreCompletion h) := fun y ↦ by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (y : A ⧸ h.nullIdeal)
  exact ⟨a, ha⟩

@[simp] theorem norm_toPreCompletion (h : IsCStarSeminorm p) (a : A) :
    ‖toPreCompletion h a‖ = p a := by
  show h.quotientNorm (Ideal.Quotient.mk h.nullIdeal a) = p a
  exact h.quotientNorm_mk a

/-- **The canonical ⋆-homomorphism of `A` into the C⋆-algebra it envelops.**
It is norm-preserving for `p`, so it is injective exactly modulo the null
ideal. -/
def toSeminormCompletion (h : IsCStarSeminorm p) : A →⋆ₐ[ℂ] SeminormCompletion h :=
  (CStarCompletion.coeStarAlgHom (WithCStarNorm h.isCStarNorm_quotientNorm)).comp
    (toPreCompletion h)

@[simp] theorem norm_toSeminormCompletion (h : IsCStarSeminorm p) (a : A) :
    ‖toSeminormCompletion h a‖ = p a := by
  -- stated through the pieces rather than by `show`, so that the completion's
  -- coercion is produced by the lemma rather than by an ascription
  have hcoe := CStarCompletion.norm_coeStarAlgHom
    (WithCStarNorm h.isCStarNorm_quotientNorm) (toPreCompletion h a)
  rw [norm_toPreCompletion] at hcoe
  exact hcoe

/-- **A ⋆-homomorphism out of the envelope is continuous.**  The envelope is a
complex C⋆-algebra, and a ⋆-homomorphism of complex C⋆-algebras is contractive,
hence Lipschitz.

Contractivity — `NonUnitalStarAlgHom.norm_apply_le`, the spectral-radius
argument — is quoted directly rather than through the `ContinuousMapClass`
instance that packages it, so that the Lipschitz constant is visible.  Both live
in `Mathlib/Analysis/CStarAlgebra/Spectrum.lean`, which is why this file imports
it; without that import a ⋆-homomorphism out of a C⋆-algebra is not known to be
continuous at all. -/
theorem continuous_of_seminormCompletion [StarModule ℂ A] {B : Type v}
    [CStarAlgebra B] (h : IsCStarSeminorm p) (f : SeminormCompletion h →⋆ₐ[ℂ] B) :
    Continuous (f : SeminormCompletion h → B) := by
  refine (LipschitzWith.mk_one fun x y ↦ ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact NonUnitalStarAlgHom.norm_apply_le f (x - y)

/-- **Two ⋆-homomorphisms out of the envelope that agree on the image of `A`
are equal**, with no restriction on the universe of the target.

The image of `A` is dense and a ⋆-homomorphism between C⋆-algebras is
continuous, so the set where two of them agree is closed and contains a dense
set.  Nothing here sees the universe of `B`. -/
theorem seminormCompletion_ext [StarModule ℂ A] {B : Type v} [CStarAlgebra B]
    (h : IsCStarSeminorm p) (f₁ f₂ : SeminormCompletion h →⋆ₐ[ℂ] B)
    (hagree : ∀ a : A,
      f₁ (toSeminormCompletion h a) = f₂ (toSeminormCompletion h a)) :
    f₁ = f₂ := by
  refine DFunLike.ext _ _ fun x ↦ ?_
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (continuous_of_seminormCompletion h f₁)
      (continuous_of_seminormCompletion h f₂)) ?_
  intro y
  obtain ⟨a, rfl⟩ := toPreCompletion_surjective h y
  exact hagree a

end Envelope

/-! ## The universal property -/

section Lift

variable {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A] {p : A → ℝ}
  {B : Type v} [CStarAlgebra B]

/-- A ⋆-homomorphism dominated by `p` kills the null ideal of `p`. -/
theorem eq_zero_of_mem_nullIdeal (h : IsCStarSeminorm p) (f : A →⋆ₐ[ℂ] B)
    (hf : ∀ a : A, ‖f a‖ ≤ p a) {a : A} (ha : a ∈ h.nullIdeal) : f a = 0 := by
  have h0 : p a = 0 := ha
  refine norm_eq_zero.mp (le_antisymm ?_ (norm_nonneg _))
  rw [← h0]
  exact hf a

/-- The map a dominated ⋆-homomorphism induces on the pre-C⋆-algebra. -/
def preLift (h : IsCStarSeminorm p) (f : A →⋆ₐ[ℂ] B) (hf : ∀ a : A, ‖f a‖ ≤ p a) :
    WithCStarNorm h.isCStarNorm_quotientNorm →⋆ₐ[ℂ] B :=
  (quotientStarLift h.nullIdeal f
      (fun _ ha ↦ eq_zero_of_mem_nullIdeal h f hf ha)).comp
    (WithCStarNorm.unretagStarAlgHom h.isCStarNorm_quotientNorm)

@[simp] theorem preLift_apply (h : IsCStarSeminorm p) (f : A →⋆ₐ[ℂ] B)
    (hf : ∀ a : A, ‖f a‖ ≤ p a) (a : A) :
    preLift h f hf (toPreCompletion h a) = f a :=
  quotientStarLift_mk h.nullIdeal f
    (fun _ ha ↦ eq_zero_of_mem_nullIdeal h f hf ha) a

theorem norm_preLift_le (h : IsCStarSeminorm p) (f : A →⋆ₐ[ℂ] B)
    (hf : ∀ a : A, ‖f a‖ ≤ p a)
    (y : WithCStarNorm h.isCStarNorm_quotientNorm) : ‖preLift h f hf y‖ ≤ ‖y‖ := by
  obtain ⟨a, rfl⟩ := toPreCompletion_surjective h y
  rw [preLift_apply, norm_toPreCompletion]
  exact hf a

/-- **The universal property of the envelope, at an arbitrary universe.**  A
⋆-homomorphism `f : A → B` that `p` dominates extends across the completion.

`B` is quantified at a universe independent of `A`'s: the extension is built by
continuity from the dense image of `A`, and neither the domination hypothesis
nor the density argument mentions where `B` lives. -/
def seminormCompletionLift (h : IsCStarSeminorm p) (f : A →⋆ₐ[ℂ] B)
    (hf : ∀ a : A, ‖f a‖ ≤ p a) : SeminormCompletion h →⋆ₐ[ℂ] B :=
  CStarCompletion.extendStarAlgHom (preLift h f hf)
    (CStarCompletion.uniformContinuous_of_norm_le _ (norm_preLift_le h f hf))

@[simp] theorem seminormCompletionLift_apply (h : IsCStarSeminorm p)
    (f : A →⋆ₐ[ℂ] B) (hf : ∀ a : A, ‖f a‖ ≤ p a) (a : A) :
    seminormCompletionLift h f hf (toSeminormCompletion h a) = f a := by
  have hext := CStarCompletion.extendStarAlgHom_coe (preLift h f hf)
    (CStarCompletion.uniformContinuous_of_norm_le _ (norm_preLift_le h f hf))
    (toPreCompletion h a)
  rw [preLift_apply] at hext
  exact hext

/-- **Existence and uniqueness together.** -/
theorem seminormCompletion_existsUnique_lift [StarModule ℂ A]
    (h : IsCStarSeminorm p) (f : A →⋆ₐ[ℂ] B) (hf : ∀ a : A, ‖f a‖ ≤ p a) :
    ∃! F : SeminormCompletion h →⋆ₐ[ℂ] B,
      ∀ a : A, F (toSeminormCompletion h a) = f a := by
  refine ⟨seminormCompletionLift h f hf, seminormCompletionLift_apply h f hf, ?_⟩
  intro q hq
  refine seminormCompletion_ext h q _ fun a ↦ ?_
  rw [hq a, seminormCompletionLift_apply]

end Lift

end

end CStarTensor
end GroupApproximation
