import GroupApproximation.Sofic.HilbertUltraproductSpace
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# `K_ω` as an inner product space

`Sofic/UltraproductModelConstruction.lean` builds `Vec`, the manuscript's
`K_ω`, and says of it in its own docstring: "Its inner product is not
constructed, and no field of the manuscript's interface refers to one."  The
audit records that as `NEW.UF.04`: the printed proof uses inner products,
orthogonal complements and spectral projections on `K_ω`, and the Lean object
was a bare complex vector space.

The pairing itself, and every identity an inner product has to satisfy, are
proved on the *numerator* in `Sofic/HilbertUltraproductInner.lean` and
`Sofic/HilbertUltraproductSpace.lean` -- including the one that is not a
computation, that the isotropic vectors of the form are exactly the
denominator.  What was missing was the descent: that is what this file does,
and the payoff is that `K_ω` carries mathlib's `InnerProductSpace ℂ`
structure, with its norm, its orthogonal complements and everything stated for
inner product spaces.

## What is and is not proved here

Positive-definiteness is genuine, not assumed: `definite` is discharged by
`uinner_self_eq_zero_iff`, which is why the quotient is by the null families
and not by anything coarser.

**Completeness is proved, one file above.**  `K_ω` is a Hilbert space, and that
is not a naming: `Analysis/OmegaHilbertComplete.lean` registers
`kOmegaCompleteSpace` for the type introduced below, and
`Analysis/KOmegaHilbertSpaceEndpoint.lean` states the two halves together as the
closed proposition `KOmegaIsHilbertSpace`.  No `CompleteSpace` instance is
claimed *in this file*, and nothing here uses one: every statement below is
about an inner product space, so the completeness argument sits strictly above
this module and the import runs one way only.  Until 2026-08-25 this paragraph
said completeness was not proved at all, which had been false since the
instance landed.

`K_ω` is introduced as an opaque type synonym of `Vec` rather than as
instances on `Vec` itself, because `Vec` is a reducible abbreviation for a
`Submodule` quotient and instances keyed there would be found for every such
quotient.  The weight hypothesis `0 ≤ w n` is a parameter of the type for the
same reason it is a hypothesis of every lemma below: without it the pairing
need not converge, so there is no form to descend.
-/

namespace GroupApproximation
namespace KOmegaHilbert

open Filter Matrix Topology
open UltrafilterLimit UltraproductModelConstruction
open HilbertUltraproductInner HilbertUltraproductPairing
open HilbertUltraproductSpace ScaledKazhdanTransport

noncomputable section

/-! ## The identities the descent needs but the numerator did not state -/

section Bilinear

variable {Y : ℕ → FiniteModel} {w : ℕ → ℝ} {ω : Ultrafilter ℕ}

/-- Conjugate homogeneity in the first argument, from conjugate symmetry. -/
theorem uinner_smul_left (hw : ∀ n, 0 ≤ w n) (c : ℂ) (ξ η : massBounded Y w) :
    uinner (ω := ω) (c • ξ) η
      = (starRingEnd ℂ) c * uinner (ω := ω) ξ η := by
  rw [← uinner_conj_symm hw (c • ξ) η, uinner_smul_right hw c η ξ, map_mul,
    uinner_conj_symm hw ξ η]

theorem uinner_sub_left (hw : ∀ n, 0 ≤ w n) (ξ η ζ : massBounded Y w) :
    uinner (ω := ω) (ξ - η) ζ
      = uinner (ω := ω) ξ ζ - uinner (ω := ω) η ζ := by
  have hsum : (ξ - η) + η = ξ := by abel
  have h := uinner_add_left (ω := ω) hw (ξ - η) η ζ
  rw [hsum] at h
  rw [h]
  ring

theorem uinner_sub_right (hw : ∀ n, 0 ≤ w n) (ξ η ζ : massBounded Y w) :
    uinner (ω := ω) ξ (η - ζ)
      = uinner (ω := ω) ξ η - uinner (ω := ω) ξ ζ := by
  have hsum : (η - ζ) + ζ = η := by abel
  have h := uinner_add_right (ω := ω) hw ξ (η - ζ) ζ
  rw [hsum] at h
  rw [h]
  ring

end Bilinear

/-! ## The descent -/

section Descent

variable (Y : ℕ → FiniteModel) (w : ℕ → ℝ) (ω : Ultrafilter ℕ)

/-- **The inner product of `K_ω`**, on the quotient.  The form is constant on
classes because a null family pairs to zero against every mass-bounded
family, which is the one analytic step of the construction. -/
def kinner (hw : ∀ n, 0 ≤ w n) (x y : Vec Y w ω) : ℂ :=
  Quotient.liftOn₂' x y (fun ξ η ↦ uinner (ω := ω) ξ η)
    (fun ξ η ξ' η' hξ hη ↦ by
      have hx : (Submodule.Quotient.mk ξ : Vec Y w ω)
          = Submodule.Quotient.mk ξ' := Quotient.sound' hξ
      have hy : (Submodule.Quotient.mk η : Vec Y w ω)
          = Submodule.Quotient.mk η' := Quotient.sound' hη
      rw [Submodule.Quotient.eq (nullIn Y w ω)] at hx hy
      have h1 : uinner (ω := ω) (ξ - ξ') η = 0 :=
        uinner_eq_zero_of_massNull_left hw hx
      have h2 : uinner (ω := ω) ξ' (η - η') = 0 :=
        uinner_eq_zero_of_massNull_right hw hy
      rw [uinner_sub_left hw] at h1
      rw [uinner_sub_right hw] at h2
      linear_combination h1 + h2)

@[simp] theorem kinner_mk (hw : ∀ n, 0 ≤ w n) (ξ η : massBounded Y w) :
    kinner Y w ω hw (Submodule.Quotient.mk ξ) (Submodule.Quotient.mk η)
      = uinner (ω := ω) ξ η := rfl

theorem kinner_conj_symm (hw : ∀ n, 0 ≤ w n) (x y : Vec Y w ω) :
    (starRingEnd ℂ) (kinner Y w ω hw y x) = kinner Y w ω hw x y := by
  obtain ⟨ξ, rfl⟩ := Submodule.Quotient.mk_surjective (nullIn Y w ω) x
  obtain ⟨η, rfl⟩ := Submodule.Quotient.mk_surjective (nullIn Y w ω) y
  exact uinner_conj_symm hw ξ η

theorem kinner_self_nonneg (hw : ∀ n, 0 ≤ w n) (x : Vec Y w ω) :
    0 ≤ RCLike.re (kinner Y w ω hw x x) := by
  obtain ⟨ξ, rfl⟩ := Submodule.Quotient.mk_surjective (nullIn Y w ω) x
  simpa using uinner_self_nonneg hw ξ (ω := ω)

theorem kinner_add_left (hw : ∀ n, 0 ≤ w n) (x y z : Vec Y w ω) :
    kinner Y w ω hw (x + y) z
      = kinner Y w ω hw x z + kinner Y w ω hw y z := by
  obtain ⟨ξ, rfl⟩ := Submodule.Quotient.mk_surjective (nullIn Y w ω) x
  obtain ⟨η, rfl⟩ := Submodule.Quotient.mk_surjective (nullIn Y w ω) y
  obtain ⟨ζ, rfl⟩ := Submodule.Quotient.mk_surjective (nullIn Y w ω) z
  show uinner (ω := ω) (ξ + η) ζ
      = uinner (ω := ω) ξ ζ + uinner (ω := ω) η ζ
  exact uinner_add_left hw ξ η ζ

theorem kinner_smul_left (hw : ∀ n, 0 ≤ w n) (c : ℂ) (x y : Vec Y w ω) :
    kinner Y w ω hw (c • x) y
      = (starRingEnd ℂ) c * kinner Y w ω hw x y := by
  obtain ⟨ξ, rfl⟩ := Submodule.Quotient.mk_surjective (nullIn Y w ω) x
  obtain ⟨η, rfl⟩ := Submodule.Quotient.mk_surjective (nullIn Y w ω) y
  show uinner (ω := ω) (c • ξ) η
      = (starRingEnd ℂ) c * uinner (ω := ω) ξ η
  exact uinner_smul_left hw c ξ η

/-- **Positive definiteness.**  This is where the quotient is exactly right:
a class of vanishing self-pairing is null at the weight along `ω`, which is
precisely membership in the denominator. -/
theorem kinner_definite (hw : ∀ n, 0 ≤ w n) (x : Vec Y w ω)
    (h : kinner Y w ω hw x x = 0) : x = 0 := by
  obtain ⟨ξ, rfl⟩ := Submodule.Quotient.mk_surjective (nullIn Y w ω) x
  rw [Submodule.Quotient.mk_eq_zero]
  exact (uinner_self_eq_zero_iff hw ξ).1 h

/-! ## `K_ω` as an inner product space -/

/-- **KT.05, with its inner product.**  The manuscript's `K_ω`, exposed behind
an opaque boundary so that its inner-product structure is keyed to it rather
than to every `Submodule` quotient. -/
def KOmega (_hw : ∀ n, 0 ≤ w n) : Type := Vec Y w ω

noncomputable instance kOmegaAddCommGroup (hw : ∀ n, 0 ≤ w n) :
    AddCommGroup (KOmega Y w ω hw) :=
  inferInstanceAs (AddCommGroup (Vec Y w ω))

noncomputable instance kOmegaModule (hw : ∀ n, 0 ≤ w n) :
    Module ℂ (KOmega Y w ω hw) :=
  inferInstanceAs (Module ℂ (Vec Y w ω))

noncomputable instance kOmegaInner (hw : ∀ n, 0 ≤ w n) :
    Inner ℂ (KOmega Y w ω hw) :=
  ⟨kinner Y w ω hw⟩

/-- The six identities of an inner product, assembled.  Every field is a
theorem proved on the numerator and descended above; none is an assumption. -/
noncomputable instance kOmegaCore (hw : ∀ n, 0 ≤ w n) :
    InnerProductSpace.Core ℂ (KOmega Y w ω hw) where
  conj_inner_symm x y := kinner_conj_symm Y w ω hw x y
  re_inner_nonneg x := kinner_self_nonneg Y w ω hw x
  add_left x y z := kinner_add_left Y w ω hw x y z
  smul_left x y r := kinner_smul_left Y w ω hw r x y
  definite x h := kinner_definite Y w ω hw x h

noncomputable instance kOmegaNormedAddCommGroup (hw : ∀ n, 0 ≤ w n) :
    NormedAddCommGroup (KOmega Y w ω hw) :=
  (kOmegaCore Y w ω hw).toNormedAddCommGroup

/-- **NEW.UF.04.**  `K_ω` is a complex inner product space, with the
ultralimit of the renormalized Frobenius pairings as its inner product.
Completeness is not proved here and no statement in this file uses it; it is
`OmegaHilbertComplete.kOmegaCompleteSpace`, in a module that imports this
one. -/
noncomputable instance kOmegaInnerProductSpace (hw : ∀ n, 0 ≤ w n) :
    InnerProductSpace ℂ (KOmega Y w ω hw) :=
  .ofCore _

/-- The class of a mass-bounded family as a vector of `K_ω`. -/
def mkK (hw : ∀ n, 0 ≤ w n) (ξ : massBounded Y w) : KOmega Y w ω hw :=
  Submodule.Quotient.mk ξ

/-- The norm of `K_ω` is the square root of the ultralimit of the
renormalized masses, which is the manuscript's normalization. -/
theorem norm_mkK (hw : ∀ n, 0 ≤ w n) (ξ : massBounded Y w) :
    ‖mkK Y w ω hw ξ‖
      = Real.sqrt (ulim ω (fun n ↦ matMass ((ξ : MatFam Y) n) / w n)) := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ)]
  congr 1
  show RCLike.re (uinner (ω := ω) ξ ξ) = _
  rw [uinner_self hw ξ]
  simp

end Descent

end

end KOmegaHilbert
end GroupApproximation
