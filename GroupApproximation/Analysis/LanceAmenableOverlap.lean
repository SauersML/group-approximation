import GroupApproximation.Analysis.LanceFolnerCPAP
import GroupApproximation.Sofic.AmenableActionSofic

/-!
# Amenable groups supply the Følner overlaps

`Analysis/LanceFolnerCPAP` reduces the forward half of Lance's theorem to a
combinatorial statement: for every finite set of translations and every
tolerance there is an injective enumeration `e : Fin k → G` and a unit
amplitude tuple `c` whose overlaps `ω_g` are within the tolerance of `1`.
This file supplies that statement for an amenable group, from the Følner
sets the repository already produces
(`Sofic.AmenableActionSofic.exists_folner`, which is the Tarski--Hall
argument applied to the left translations).

The tuple is the obvious one: enumerate a Følner set `A`, and take every
amplitude equal to `|A|^{-1/2}`.  The overlap is then

  `ω_g = |{a ∈ A : g·a ∈ A}| / |A| = 1 - |∂_g A| / |A|`,

so the Følner estimate `|∂_g A| < δ|A|` is exactly `‖ω_g - 1‖ < δ`.  The
only work is the reindexing `Fin |A| ≃ A` and the complement count.

## Manuscript status

Completes the Lean side of the *forward* Lance implication:
`amenable → NuclearReducedCPAP`.  Together with
`Analysis/LanceNuclearity.hasInvariantMean_of_nuclearReducedCPAP` this makes
the completely positive approximation property of `C⋆_λ(G)` equivalent to
amenability of `G`.
-/

namespace GroupApproximation
namespace CStarExactness

open scoped InnerProductSpace
open Finset ReducedGroupCStarTrace Amenability AmenableActionSofic
open scoped Classical

noncomputable section

universe u

variable {Γ : Type u} [Group Γ]

/-! ## The enumeration of a finite set -/

/-- An injective enumeration of a finite subset of the group. -/
def finsetEnum (A : Finset Γ) : Fin A.card → Γ :=
  fun i ↦ ((A.equivFin.symm i : {x // x ∈ A}) : Γ)

omit [Group Γ] in
theorem finsetEnum_injective (A : Finset Γ) :
    Function.Injective (finsetEnum A) := by
  intro i j hij
  exact A.equivFin.symm.injective (Subtype.ext hij)

omit [Group Γ] in
/-- Summing a function of the enumeration is summing it over the set. -/
theorem sum_finsetEnum (A : Finset Γ) {M : Type*} [AddCommMonoid M]
    (f : Γ → M) :
    (∑ i : Fin A.card, f (finsetEnum A i)) = ∑ a ∈ A, f a := by
  classical
  rw [show (∑ i : Fin A.card, f (finsetEnum A i))
      = ∑ i : Fin A.card, (fun x : {x // x ∈ A} ↦ f (x : Γ))
          (A.equivFin.symm i) from rfl,
    Equiv.sum_comp A.equivFin.symm (fun x : {x // x ∈ A} ↦ f (x : Γ)),
    Finset.sum_coe_sort A (fun a ↦ f a)]

/-! ## The overlap of a Følner set -/

/-- The overlap of the constant-amplitude tuple on a finite set counts the
elements the translation keeps inside the set. -/
theorem folnerOverlap_const (A : Finset Γ) (g : Γ) (w : ℂ) :
    folnerOverlap (finsetEnum A) (fun _ ↦ w) g
      = ((A.filter fun b ↦ g * b ∈ A).card : ℂ) * (star w * w) := by
  classical
  rw [folnerOverlap]
  rw [show (∑ p : Fin A.card, ∑ q : Fin A.card,
        if finsetEnum A p = g * finsetEnum A q then star w * w else 0)
      = ∑ p : Fin A.card, ∑ q : Fin A.card,
        (fun a b : Γ ↦ if a = g * b then star w * w else 0)
          (finsetEnum A p) (finsetEnum A q) from rfl]
  rw [sum_finsetEnum A (fun a ↦ ∑ q : Fin A.card,
    (fun a b : Γ ↦ if a = g * b then star w * w else 0) a (finsetEnum A q))]
  have hinner : ∀ a : Γ,
      (∑ q : Fin A.card, if a = g * finsetEnum A q then star w * w else 0)
        = ∑ b ∈ A, if a = g * b then star w * w else 0 :=
    fun a ↦ sum_finsetEnum A (fun b ↦ if a = g * b then star w * w else 0)
  rw [Finset.sum_congr rfl fun a _ ↦ hinner a, Finset.sum_comm]
  have hcol : ∀ b : Γ,
      (∑ a ∈ A, if a = g * b then star w * w else 0)
        = if g * b ∈ A then star w * w else 0 := by
    intro b
    exact Finset.sum_ite_eq' A (g * b) (fun _ ↦ star w * w)
  rw [Finset.sum_congr rfl fun b _ ↦ hcol b, ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul]

/-- The elements a translation keeps inside the set are the complement of the
boundary. -/
theorem card_filter_add_card_boundary (A : Finset Γ) (g : Γ) :
    (A.filter fun b ↦ g * b ∈ A).card + (boundary A g).card = A.card := by
  classical
  have hb : boundary A g = A.filter fun b ↦ ¬ (g * b ∈ A) := by
    ext a
    simp [boundary]
  rw [hb]
  exact Finset.card_filter_add_card_filter_not _

/-! ## Amenability supplies the tuples -/

/-- **Amenable groups supply Følner overlaps.** -/
theorem exists_overlap_of_isAmenable (hΓ : IsAmenable Γ) (F : Finset Γ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (k : ℕ) (e : Fin k → Γ) (c : Fin k → ℂ),
      Function.Injective e ∧ (∑ p : Fin k, star (c p) * c p) = 1 ∧
        ∀ g ∈ F, ‖folnerOverlap e c g - 1‖ ≤ δ := by
  classical
  obtain ⟨A, hAne, hsmall⟩ := exists_folner hΓ F hδ
  have hcard : 0 < (A.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hAne
  set r : ℝ := Real.sqrt ((A.card : ℝ)⁻¹) with hr
  set w : ℂ := (r : ℂ) with hw
  have hww : star w * w = (((A.card : ℝ)⁻¹ : ℝ) : ℂ) := by
    have hnn : (0 : ℝ) ≤ ((A.card : ℝ))⁻¹ := le_of_lt (inv_pos.mpr hcard)
    rw [hw, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, hr,
      Real.mul_self_sqrt hnn]
  refine ⟨A.card, finsetEnum A, fun _ ↦ w, finsetEnum_injective A, ?_,
    fun g hg ↦ ?_⟩
  · rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin,
      hww, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
      mul_inv_cancel₀ (ne_of_gt hcard), Complex.ofReal_one]
  · rw [folnerOverlap_const, hww]
    have hsplit := card_filter_add_card_boundary A g
    have hval : (((A.filter fun b ↦ g * b ∈ A).card : ℂ)
          * (((A.card : ℝ)⁻¹ : ℝ) : ℂ)) - 1
        = -((((boundary A g).card : ℝ) / (A.card : ℝ) : ℝ) : ℂ) := by
      have hcast : (((A.filter fun b ↦ g * b ∈ A).card : ℝ))
          = (A.card : ℝ) - ((boundary A g).card : ℝ) := by
        have := congrArg (fun n : ℕ ↦ (n : ℝ)) hsplit
        push_cast at this
        linarith
      have hreal : ((A.filter fun b ↦ g * b ∈ A).card : ℝ) * ((A.card : ℝ))⁻¹ - 1
          = -(((boundary A g).card : ℝ) / (A.card : ℝ)) := by
        rw [hcast]
        field_simp
        ring
      calc (((A.filter fun b ↦ g * b ∈ A).card : ℂ)
            * (((A.card : ℝ)⁻¹ : ℝ) : ℂ)) - 1
          = ((((A.filter fun b ↦ g * b ∈ A).card : ℝ) * ((A.card : ℝ))⁻¹ - 1 : ℝ) : ℂ) := by
            push_cast
            ring
        _ = ((-(((boundary A g).card : ℝ) / (A.card : ℝ)) : ℝ) : ℂ) := by rw [hreal]
        _ = -((((boundary A g).card : ℝ) / (A.card : ℝ) : ℝ) : ℂ) := by
            push_cast
            ring
    rw [hval, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    rw [div_le_iff₀ hcard]
    exact le_of_lt (hsmall g hg)

/-- **The forward half of Lance's theorem.**  An amenable group has a
reduced C⋆-algebra with the completely positive approximation property. -/
theorem nuclearReducedCPAP_of_isAmenable {Γ : Type} [Group Γ]
    (hΓ : IsAmenable Γ) : NuclearReducedCPAP Γ :=
  nuclearReducedCPAP_of_overlap fun F _δ hδ ↦
    exists_overlap_of_isAmenable hΓ F hδ

/-- **Lance's theorem, both directions.**  The completely positive
approximation property of `C⋆_λ(G)` is equivalent to amenability of `G`. -/
theorem nuclearReducedCPAP_iff_isAmenable {Γ : Type} [Group Γ] :
    NuclearReducedCPAP Γ ↔ IsAmenable Γ :=
  ⟨fun h ↦ isAmenable_of_hasInvariantMean
      (hasInvariantMean_of_nuclearReducedCPAP Γ h),
    nuclearReducedCPAP_of_isAmenable⟩

end

end CStarExactness
end GroupApproximation
