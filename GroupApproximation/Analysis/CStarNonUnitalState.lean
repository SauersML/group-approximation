import GroupApproximation.Analysis.CStarStateGNS
import Mathlib.Analysis.CStarAlgebra.Unitization

/-!
# States on non-unital C⋆-algebras, by unitization transport

## What this module provides

The state theory of `CStarStateSeparation`/`CStarStateGNS` is unital: a
state is a unital contraction, and its positivity is Kadison's theorem.  The
ideal leg of the exactness sequence concerns *non-unital* algebras, where
there is no unit to evaluate at, so positivity must enter the definition:

* `NonUnitalState A` -- a contractive functional, **positive by definition**
  in the order-free spelling of this development: real and nonnegative on
  every `star x * x`;
* `exists_nonUnitalState_star_mul_self` -- the norm-attaining state exists:
  the unital theorem applied to the unitization `A⁺¹`, restricted along the
  isometric ⋆-embedding `A → A⁺¹`, with the restriction's positivity
  inherited from Kadison positivity upstairs.

This is the entry point of the non-unital minimal-tensor layer; the
non-unital GNS representations (Mathlib's construction is already
non-unital) and the embedding of a non-unital `⊗_min` into the unitization's
are later modules, not this one.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.  `SO.16` and
`RE.05` remain **MISSING**.
-/

namespace GroupApproximation
namespace CStarState

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- A **state on a non-unital C⋆-algebra**: a contractive functional, real
and nonnegative on every `star x * x`.  Positivity is a field rather than a
theorem because without a unit Kadison's characterization is unavailable. -/
structure NonUnitalState (A : Type u) [NonUnitalCStarAlgebra A] where
  /-- The underlying continuous linear functional. -/
  toCLM : A →L[ℂ] ℂ
  /-- A state is a contraction. -/
  norm_le : ‖toCLM‖ ≤ 1
  /-- Positivity, real part. -/
  re_nonneg : ∀ x : A, 0 ≤ (toCLM (star x * x)).re
  /-- Positivity, imaginary part. -/
  im_eq_zero : ∀ x : A, (toCLM (star x * x)).im = 0

/-! ## The unitization transport -/

instance : Nontrivial (Unitization ℂ A) :=
  ⟨1, 0, fun h => by
    have h1 := congrArg (Unitization.fstHom ℂ A) h
    rw [map_one, map_zero] at h1
    exact one_ne_zero h1⟩

/-- The inclusion into the unitization, as a continuous linear map:
⋆-homomorphisms of C⋆-algebras are automatically contractive. -/
noncomputable def inrCLM : A →L[ℂ] Unitization ℂ A :=
  LinearMap.mkContinuous
    { toFun := fun a => (a : Unitization ℂ A)
      map_add' := fun a b => by rw [Unitization.inr_add]
      map_smul' := fun c a => by rw [Unitization.inr_smul]; rfl }
    1 fun a => by
      rw [one_mul]
      exact NonUnitalStarAlgHom.norm_apply_le
        (Unitization.inrNonUnitalStarAlgHom ℂ A) a

@[simp] theorem inrCLM_apply (a : A) :
    inrCLM a = (a : Unitization ℂ A) := rfl

/-- **The norm-attaining state, non-unitally**: restrict the unital
norm-attaining state of the unitization along the isometric embedding. -/
theorem exists_nonUnitalState_star_mul_self (a : A) :
    ∃ φ : NonUnitalState A,
      φ.toCLM (star a * a) = ((‖a‖ : ℝ) : ℂ) ^ 2 := by
  obtain ⟨f, hf1, hfle, hfval⟩ :=
    exists_state_star_mul_self ((a : Unitization ℂ A))
  refine ⟨⟨f.comp inrCLM, ?_, ?_, ?_⟩, ?_⟩
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [one_mul]
    have h1 : ‖f (inrCLM x)‖ ≤ ‖inrCLM x‖ := by
      have h := f.le_opNorm (inrCLM x)
      have h2 : ‖f‖ * ‖inrCLM x‖ ≤ 1 * ‖inrCLM x‖ := by
        gcongr
      rw [one_mul] at h2
      exact h.trans h2
    refine h1.trans ?_
    rw [inrCLM_apply]
    exact NonUnitalStarAlgHom.norm_apply_le
      (Unitization.inrNonUnitalStarAlgHom ℂ A) x
  · intro x
    have h := (state_apply_star_mul_self_nonneg f hf1 hfle
      ((x : Unitization ℂ A))).1
    have hx : ((star x * x : A) : Unitization ℂ A)
        = star ((x : Unitization ℂ A)) * ((x : Unitization ℂ A)) := by
      rw [Unitization.inr_mul, Unitization.inr_star]
    show 0 ≤ (f (inrCLM (star x * x))).re
    rw [inrCLM_apply, hx]
    exact h
  · intro x
    have h := (state_apply_star_mul_self_nonneg f hf1 hfle
      ((x : Unitization ℂ A))).2
    have hx : ((star x * x : A) : Unitization ℂ A)
        = star ((x : Unitization ℂ A)) * ((x : Unitization ℂ A)) := by
      rw [Unitization.inr_mul, Unitization.inr_star]
    show (f (inrCLM (star x * x))).im = 0
    rw [inrCLM_apply, hx]
    exact h
  · have hx : ((star a * a : A) : Unitization ℂ A)
        = star ((a : Unitization ℂ A)) * ((a : Unitization ℂ A)) := by
      rw [Unitization.inr_mul, Unitization.inr_star]
    show f (inrCLM (star a * a)) = _
    rw [inrCLM_apply, hx, hfval, Unitization.norm_inr]

end CStarState
end GroupApproximation
