import GroupApproximation.Analysis.PropertyALocality
import GroupApproximation.Algebra.MappingTelescope

/-!
# Property A passes to a mapping telescope

`Analysis/PropertyALocality` proves the increasing-union step of the exactness
paragraph outright.  This file spends it on the object the Lean route actually
has to handle.

The manuscript's exactness chain runs through `C(𝒢)/⟨ζ⟩` and its increasing
free products `Q_n`.  The formalized route does not: `ExactnessPermanence`
supplies property A for the lamp side from *local finiteness*, so what remains
of the group half is the vertical group, and the vertical group is

`Vertical α hα = Telescope α hα ⋊ ℤ`.

The telescope is the colimit of `Γ --α--> Γ --α--> ⋯`.  Its level copies
increase — `level (n+1) ∘ α = level n`, so the level-`n` range sits inside the
level-`(n+1)` range — and every element lies in one of them, because every
element of the telescope is a class `mk n x`.  Each level copy is isomorphic to
`Γ`, since `α` is injective.  So the increasing-union lemma applies verbatim:

`HasPropertyA Γ → HasPropertyA (Telescope α hα)`.

That is the exact analogue of the printed `Q_n` step, in the vocabulary the
formalization actually uses, and it is unconditional.

## What remains after this

Two things, and this file adds no hypothesis-carrying wrapper for either:

* the extension `Telescope ⋊ ℤ` — property A across an extension with amenable
  quotient;
* property A for `Γ` itself, which for the manuscript's base group is
  Guentner--Higson--Weinberger.

The first is permanence and is in principle of the same character as what is
proved here; the second is a genuine external theorem.
-/

namespace GroupApproximation
namespace PropertyATelescope

open ExactnessPermanence MappingTelescope PropertyALocality

universe u v

/-! ## Property A is a group-isomorphism invariant -/

/-- **Property A transports along a group isomorphism.**  The witness is
transported by relabelling: template, support, mass and the `ℓ¹` estimate are
all preserved because the relabelling is a bijective homomorphism. -/
theorem hasPropertyA_of_mulEquiv {G₁ : Type u} {G₂ : Type v} [Group G₁]
    [Group G₂] (e : G₁ ≃* G₂) (h : HasPropertyA G₁) : HasPropertyA G₂ := by
  classical
  intro R ε hε
  obtain ⟨W⟩ := h (R.image e.symm) ε hε
  refine ⟨{
    template := W.template.image e
    weight := fun g x ↦ W.weight (e.symm g) (e.symm x)
    weight_nonneg := fun g x ↦ W.weight_nonneg _ _
    weight_eq_zero := ?_
    weight_sum := ?_
    weight_close := ?_ }⟩
  · intro g x hx
    refine W.weight_eq_zero _ _ ?_
    intro hmem
    refine hx (Finset.mem_image.mpr ⟨(e.symm g)⁻¹ * e.symm x, hmem, ?_⟩)
    rw [map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  · intro g
    rw [Finset.sum_image fun a _ b _ hab ↦ e.injective hab]
    rw [← W.weight_sum (e.symm g)]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    congr 1
    rw [map_mul, MulEquiv.symm_apply_apply]
  · intro g h hgh T hTg hTh
    have hmem : (e.symm g)⁻¹ * e.symm h ∈ R.image e.symm := by
      refine Finset.mem_image.mpr ⟨g⁻¹ * h, hgh, ?_⟩
      rw [map_mul, map_inv]
    have hT'g : ∀ y, W.weight (e.symm g) y ≠ 0 → y ∈ T.image e.symm := by
      intro y hy
      refine Finset.mem_image.mpr ⟨e y, hTg (e y) ?_, ?_⟩
      · show W.weight (e.symm g) (e.symm (e y)) ≠ 0
        rwa [MulEquiv.symm_apply_apply]
      · rw [MulEquiv.symm_apply_apply]
    have hT'h : ∀ y, W.weight (e.symm h) y ≠ 0 → y ∈ T.image e.symm := by
      intro y hy
      refine Finset.mem_image.mpr ⟨e y, hTh (e y) ?_, ?_⟩
      · show W.weight (e.symm h) (e.symm (e y)) ≠ 0
        rwa [MulEquiv.symm_apply_apply]
      · rw [MulEquiv.symm_apply_apply]
    have hclose :=
      W.weight_close (e.symm g) (e.symm h) hmem (T.image e.symm) hT'g hT'h
    rwa [Finset.sum_image fun a _ b _ hab ↦ e.symm.injective hab] at hclose

/-! ## The telescope -/

variable {Γ : Type u} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

/-- The level copies of `Γ` increase: the level-`n` copy is the image of the
level-`(n+1)` copy under `α`. -/
theorem level_range_monotone :
    Monotone fun n ↦ (level α hα n).range := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  rintro t ⟨x, rfl⟩
  exact ⟨α x, level_succ_apply_hom α hα n x⟩

/-- Every element of the telescope lies in some level copy: it is a class
`mk n x`. -/
theorem exists_mem_level_range (t : Telescope α hα) :
    ∃ n, t ∈ (level α hα n).range := by
  obtain ⟨⟨n, x⟩, hx⟩ := mk_surjective α hα t
  exact ⟨n, x, hx⟩

/-- **Property A passes to a mapping telescope.**  This is the printed
increasing-union step, applied to the object the formalized route has in place
of the manuscript's `Q_n`. -/
theorem hasPropertyA_telescope (hΓ : HasPropertyA Γ) :
    HasPropertyA (Telescope α hα) := by
  refine hasPropertyA_of_monotone (K := fun n ↦ (level α hα n).range)
    (level_range_monotone α hα) (exists_mem_level_range α hα) fun n ↦ ?_
  exact hasPropertyA_of_mulEquiv
    (MonoidHom.ofInjective (level_injective α hα n)) hΓ

end PropertyATelescope
end GroupApproximation
