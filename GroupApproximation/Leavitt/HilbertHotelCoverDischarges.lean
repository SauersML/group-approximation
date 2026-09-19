import GroupApproximation.Covers.PresentedEnlargement
import GroupApproximation.Leavitt.HilbertHotelCover

/-!
# Discharging three clauses of the Hilbert-hotel cover

`HilbertHotel.Cover.CoverResiduals` (`HilbertHotelCover.lean`) collects the
residual facts about the cover group as fields.  This file discharges three
of them outright, using the generic presented-group transfer lemmas of
`GroupApproximation/Covers/PresentedEnlargement.lean`:

* `relator_vanishes` -- every imposed relator dies in the model;
* `kazhdan`, here `coverGroup_hasKazhdanPropertyT` -- the cover group has
  property `(T)`;
* `defect_ne_one`, here `coverDefect_ne_one` -- the defect survives into the
  cover group.

None of the three consumes `CoverResiduals` itself, so they are available to
build one.  All three are stated relative to `C : CoverInputs`, which is the
single mathematical residual of the cover layer; they become unconditional
the moment `Nonempty CoverInputs` lands.

## What each relator family actually costs

The compression family needs no block-layer input at all: `alphaModel` *is*
conjugation by `tauModel` by definition (`HilbertHotelCover.lean`), so the
compression relator is a formal `x * x⁻¹` once `freeToModel_liftWord` has
removed the chosen lifts.  The docstring on the `relator_vanishes` field
attributes this family to `Tunit_conj_corner`; that is not what it costs.
`Tunit_conj_corner` is still genuinely required, but for the *separate*
`tau_compresses` field, which is a real statement about `iota`.

Only the cover family (`PresentedGroup.one_of_mem` in `Δ`) and the
saturation family (`freeToModel_defectExpansion`) reach outside
`map_mul`/`map_inv` at all.

## The `(T)` clause needs no universe descent

`coverRelators ⊆ relators C`, so `Δ ↠ CoverGroup C` by
`PresentedEnlargement.enlarge`, and property `(T)` passes to quotients.  Both
presented groups sit in the universe of the generating type `Fin
generatorCount`, so the transfer is `.{0,0} → .{0,0}` directly and
`HasKazhdanPropertyT.of_max` is not involved -- unlike the `CoverData.kazhdan`
field, which is stated at `.{0,1}` and does need it.
-/

namespace GroupApproximation
namespace HilbertHotel
namespace Cover

variable (C : CoverInputs)

/-! ## The relators of `Δ` are among the imposed relators -/

/-- The transported cover relators are among the imposed relators. -/
theorem coverRelators_subset_relators :
    ((coverRelators : Finset (FreeGroup (Fin generatorCount))) :
        Set (FreeGroup (Fin generatorCount))) ⊆
      (relators C : Set (FreeGroup (Fin generatorCount))) := by
  intro r hr
  refine Finset.mem_coe.mpr ?_
  simp only [relators, Finset.mem_union]
  exact Or.inl (Or.inl (Finset.mem_coe.mp hr))

/-- A cover relator already dies in the model, being a relator of `Δ`. -/
theorem freeToModel_eq_one_of_mem_coverRelators
    {r : FreeGroup (Fin generatorCount)} (hr : r ∈ coverRelators) :
    freeToModel r = 1 := by
  have hmk : (PresentedGroup.mk
      ((coverRelators : Finset (FreeGroup (Fin generatorCount))) :
        Set (FreeGroup (Fin generatorCount))) r : Delta) = 1 :=
    PresentedGroup.one_of_mem (Finset.mem_coe.mpr hr)
  have hfree : freeToModel r =
      deltaQuotient (PresentedGroup.mk
        ((coverRelators : Finset (FreeGroup (Fin generatorCount))) :
          Set (FreeGroup (Fin generatorCount))) r) := rfl
  rw [hfree, hmk, map_one]

/-! ## The three discharges -/

/-- **`CoverResiduals.relator_vanishes`.**  Every imposed relator dies in the
model.  The three families are discharged separately: the transported cover
relators by `PresentedGroup.one_of_mem` in `Δ`, the compression family
formally (`alphaModel` is conjugation by `tauModel` by definition, so the
relator is `x * x⁻¹`), the saturation family by
`freeToModel_defectExpansion`. -/
theorem relator_vanishes :
    ∀ r ∈ (relators C : Set (FreeGroup (Fin generatorCount))),
      freeToModel r = 1 := by
  intro r hr0
  have hr : r ∈ relators C := Finset.mem_coe.mp hr0
  simp only [relators, Finset.mem_union] at hr
  rcases hr with (hr | hr) | hr
  · exact freeToModel_eq_one_of_mem_coverRelators hr
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hr
    have halpha : alphaModel (freeToModel (FreeGroup.of i)) =
        tauModel * freeToModel (FreeGroup.of i) * tauModel⁻¹ := rfl
    show freeToModel (liftWord tauModel * FreeGroup.of i * (liftWord tauModel)⁻¹ *
      (liftWord (alphaModel (freeToModel (FreeGroup.of i))))⁻¹) = 1
    simp only [map_mul, map_inv, freeToModel_liftWord, halpha]
    exact mul_inv_cancel _
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hr
    show freeToModel (FreeGroup.of i *
      (defectExpansion C (freeToModel (FreeGroup.of i)))⁻¹) = 1
    simp only [map_mul, map_inv, freeToModel_defectExpansion]
    exact mul_inv_cancel _

/-- **`CoverResiduals.kazhdan`.**  The cover group is a further quotient of
`Δ`: its relator set contains `coverRelators`, so `Δ ↠ CoverGroup C` and
property `(T)` transfers. -/
theorem coverGroup_hasKazhdanPropertyT :
    HasKazhdanPropertyT.{0, 0} (CoverGroup C) :=
  PresentedEnlargement.hasKazhdanPropertyT_of_subset
    (coverRelators_subset_relators C) delta_hasKazhdanPropertyT

/-! ## The covering map of the cover group -/

/-- The covering map factors through the cover group, by `relator_vanishes`. -/
noncomputable def coverToModel : CoverGroup C →* Model :=
  PresentedEnlargement.factor freeToModel (relator_vanishes C)

theorem coverToModel_mk (w : FreeGroup (Fin generatorCount)) :
    coverToModel C (wordInCoverGroup C w) = freeToModel w :=
  PresentedEnlargement.factor_mk freeToModel (relator_vanishes C) w

theorem coverToModel_surjective : Function.Surjective (coverToModel C) :=
  PresentedEnlargement.factor_surjective freeToModel (relator_vanishes C)
    freeToModel_surjective

/-- The cover group's defect maps to the model's defect. -/
theorem coverToModel_defect : coverToModel C (defect C) = defectModel := by
  show coverToModel C (wordInCoverGroup C (liftWord defectModel)) = defectModel
  rw [coverToModel_mk, freeToModel_liftWord]

/-- **`CoverResiduals.defect_ne_one`.**  The defect survives into the cover
group: its image under `coverToModel` is `defectModel`, which is nontrivial by
`defectModel_ne_one`.  Named `coverDefect_ne_one` rather than
`defect_ne_one`, which inside `HilbertHotel` would shadow the block layer's
`Binary.defect_ne_one`. -/
theorem coverDefect_ne_one : defect C ≠ 1 := by
  intro h
  apply defectModel_ne_one
  rw [← coverToModel_defect C, h, map_one]

end Cover
end HilbertHotel
end GroupApproximation
