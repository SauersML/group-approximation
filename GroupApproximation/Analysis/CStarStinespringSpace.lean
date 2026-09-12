import GroupApproximation.Analysis.CStarStinespringForm
import Mathlib.Analysis.InnerProductSpace.Completion

/-!
# The Stinespring dilation space

## What this module provides

The dilation space of a completely positive map
`φ : A →ₗ[ℂ] (H →L[ℂ] H)`, built on the finitely supported functions
`A →₀ H` rather than on a tensor product: the family `f : A →₀ H` stands
for the algebraic tensor `∑ a ⊗ f a`, the sesquilinear form

  `⟪f, g⟫ = ∑ₐ ∑_b ⟪f a, φ (star a * b) (g b)⟫`

needs no lift along the tensor relations because `A →₀ H` is free, and
the vectors that the relations would have killed are null vectors of the
form, which die in the Hausdorff completion.  Concretely:

* `stinespringSesq` -- the form, with its `single`/additivity/scalar
  laws and its conjugate symmetry (star-preservation of `φ`, proved in
  `CStarCompletelyPositiveStar`, is exactly what conjugate symmetry
  consumes);
* `stinespringSesq_self` -- positivity of the form, the finset-indexed
  form positivity of `CStarStinespringForm` applied to the support;
* `StinespringPre φ hφ` -- the type synonym of `A →₀ H` carrying the
  form as a `PreInnerProductSpace.Core`, with the induced seminorm and
  semi-inner product;
* `StinespringSpace φ hφ` -- the Hilbert completion.

The representation `π`, the intertwiner `V`, and the dilation identity
`φ a = V* ∘ π a ∘ V` are the next module, not this one.

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

/-! ## The sesquilinear form on the free model -/

/-- The Stinespring sesquilinear form of `φ` on finitely supported
families: `f` stands for the algebraic tensor `∑ a ⊗ f a`. -/
noncomputable def stinespringSesq (φ : A →ₗ[ℂ] (H →L[ℂ] H))
    (f g : A →₀ H) : ℂ :=
  f.sum fun a x => g.sum fun b y => ⟪x, φ (star a * b) y⟫_ℂ

theorem stinespringSesq_single (φ : A →ₗ[ℂ] (H →L[ℂ] H))
    (a b : A) (x y : H) :
    stinespringSesq φ (Finsupp.single a x) (Finsupp.single b y)
      = ⟪x, φ (star a * b) y⟫_ℂ := by
  classical
  unfold stinespringSesq
  rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]

theorem stinespringSesq_add_left (φ : A →ₗ[ℂ] (H →L[ℂ] H))
    (f₁ f₂ g : A →₀ H) :
    stinespringSesq φ (f₁ + f₂) g
      = stinespringSesq φ f₁ g + stinespringSesq φ f₂ g := by
  classical
  unfold stinespringSesq
  exact Finsupp.sum_add_index' (fun a => by simp)
    (fun a x₁ x₂ => by simp [Finsupp.sum_add])

theorem stinespringSesq_smul_left (φ : A →ₗ[ℂ] (H →L[ℂ] H))
    (r : ℂ) (f g : A →₀ H) :
    stinespringSesq φ (r • f) g
      = (starRingEnd ℂ) r * stinespringSesq φ f g := by
  classical
  unfold stinespringSesq
  rw [Finsupp.sum_smul_index' (fun a => by simp)]
  show (∑ a ∈ f.support, ∑ b ∈ g.support,
      ⟪r • f a, φ (star a * b) (g b)⟫_ℂ)
    = (starRingEnd ℂ) r * ∑ a ∈ f.support, ∑ b ∈ g.support,
        ⟪f a, φ (star a * b) (g b)⟫_ℂ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [inner_smul_left]

section WithComplete

variable [CompleteSpace H]

/-- **Conjugate symmetry of the form.**  This is where star-preservation
of a completely positive map enters the dilation. -/
theorem stinespringSesq_conj (hφ : IsCompletelyPositive φ)
    (f g : A →₀ H) :
    (starRingEnd ℂ) (stinespringSesq φ g f) = stinespringSesq φ f g := by
  classical
  show (starRingEnd ℂ) (∑ b ∈ g.support, ∑ a ∈ f.support,
      ⟪g b, φ (star b * a) (f a)⟫_ℂ)
    = ∑ a ∈ f.support, ∑ b ∈ g.support,
        ⟪f a, φ (star a * b) (g b)⟫_ℂ
  rw [map_sum]
  calc (∑ b ∈ g.support, (starRingEnd ℂ) (∑ a ∈ f.support,
        ⟪g b, φ (star b * a) (f a)⟫_ℂ))
      = ∑ b ∈ g.support, ∑ a ∈ f.support,
          ⟪f a, φ (star a * b) (g b)⟫_ℂ := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [map_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [inner_conj_symm]
        have h1 : star (φ (star b * a)) = φ (star a * b) := by
          rw [← hφ.map_star, star_mul, star_star]
        rw [← h1, ContinuousLinearMap.star_eq_adjoint,
          ContinuousLinearMap.adjoint_inner_right]
    _ = ∑ a ∈ f.support, ∑ b ∈ g.support,
          ⟪f a, φ (star a * b) (g b)⟫_ℂ := Finset.sum_comm

/-- **Positivity of the form**: the finset form positivity applied to
the support of `f`. -/
theorem stinespringSesq_self (hφ : IsCompletelyPositive φ) (f : A →₀ H) :
    0 ≤ (stinespringSesq φ f f).re ∧ (stinespringSesq φ f f).im = 0 := by
  classical
  exact hφ.form_nonneg_finset f.support fun a => f a

/-! ## The pre-dilation space -/

set_option linter.unusedVariables false in
/-- The **Stinespring pre-space** of a completely positive map: the
finitely supported families `A →₀ H`, as a type synonym carrying the
Stinespring form.  The parameters record which map (and which proof of
its complete positivity) induces the geometry. -/
@[nolint unusedArguments]
def StinespringPre (φ : A →ₗ[ℂ] (H →L[ℂ] H))
    (hφ : IsCompletelyPositive φ) := A →₀ H

variable (hφ : IsCompletelyPositive φ) in
noncomputable instance : AddCommGroup (StinespringPre φ hφ) :=
  inferInstanceAs (AddCommGroup (A →₀ H))

variable (hφ : IsCompletelyPositive φ) in
noncomputable instance : Module ℂ (StinespringPre φ hφ) :=
  inferInstanceAs (Module ℂ (A →₀ H))

/-- The identification of the free model with the pre-space. -/
noncomputable def toStinespringPre (φ : A →ₗ[ℂ] (H →L[ℂ] H))
    (hφ : IsCompletelyPositive φ) :
    (A →₀ H) ≃ₗ[ℂ] StinespringPre φ hφ := LinearEquiv.refl ℂ _

/-- The identification of the pre-space with the free model. -/
noncomputable def ofStinespringPre (φ : A →ₗ[ℂ] (H →L[ℂ] H))
    (hφ : IsCompletelyPositive φ) :
    StinespringPre φ hφ ≃ₗ[ℂ] (A →₀ H) := (toStinespringPre φ hφ).symm

variable (φ) (hφ : IsCompletelyPositive φ)

/-- The Stinespring form as a semi-inner-product core on the
pre-space. -/
noncomputable abbrev stinespringCore :
    PreInnerProductSpace.Core ℂ (StinespringPre φ hφ) where
  inner f g :=
    stinespringSesq φ (ofStinespringPre φ hφ f) (ofStinespringPre φ hφ g)
  conj_inner_symm f g := stinespringSesq_conj hφ f g
  re_inner_nonneg f := (stinespringSesq_self hφ f).1
  add_left f₁ f₂ g := stinespringSesq_add_left φ f₁ f₂ g
  smul_left f g r := stinespringSesq_smul_left φ r f g

noncomputable instance : SeminormedAddCommGroup (StinespringPre φ hφ) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := stinespringCore φ hφ)

noncomputable instance : InnerProductSpace ℂ (StinespringPre φ hφ) :=
  InnerProductSpace.ofCore (stinespringCore φ hφ)

@[simp] theorem stinespringPre_inner_def (f g : StinespringPre φ hφ) :
    ⟪f, g⟫_ℂ = stinespringSesq φ (ofStinespringPre φ hφ f)
      (ofStinespringPre φ hφ g) := rfl

/-- **The Stinespring dilation space**: the Hilbert completion of the
pre-space.  The null vectors of the form -- among them every image of a
tensor relation of `A ⊗ H` -- are identified with `0` here, which is
why the free model needs no quotient of its own. -/
abbrev StinespringSpace := UniformSpace.Completion (StinespringPre φ hφ)

end WithComplete

end CStarExactness
end GroupApproximation
