import GroupApproximation.Sofic.LiteralPresentationRadius
import GroupApproximation.Sofic.MarkedGroupTopology
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The literal clopen marked-group cylinder

This module contains the unconditional topology and presentation algebra for
the exact cylinder from the companion note.  The analytic non-MF conclusion
is deliberately separated into `LiteralMarkedCylinder`.
-/

namespace GroupApproximation
namespace LiteralMarkedCylinder

open LiteralNonMFPresentation MarkedGroupSpace

noncomputable section

/-- Reindex a literal free word as a word on `Fin 8`. -/
def reindexWord : FreeGroup Generator →* FreeGroup (Fin 8) :=
  FreeGroup.map generatorEquivFin8

/-- The displayed finite relator set on the standard rank-eight alphabet. -/
def relators8 : Finset (FreeGroup (Fin 8)) :=
  relators.image reindexWord

/-- The displayed marked obstruction word on the rank-eight alphabet. -/
def markedWord8 : FreeGroup (Fin 8) := reindexWord markedWord

/-- The canonical rank-eight marked group defined by the printed relators. -/
def literalPoint : MarkedGroupSpace 8 where
  relations := Subgroup.normalClosure (relators8 : Set (FreeGroup (Fin 8)))
  normal_relations := Subgroup.normalClosure_normal

/-- The exact finite control set: every printed relation and survival of the
marked word. -/
def controlWords : Finset (FreeGroup (Fin 8)) :=
  insert markedWord8 relators8

/-- The exact neighborhood claimed in the companion note. -/
def literalCylinder : Set (MarkedGroupSpace 8) :=
  cylinder literalPoint controlWords

theorem reindexed_relator_mem_literalPoint {r : FreeGroup Generator}
    (hr : r ∈ relators) : reindexWord r ∈ literalPoint.relations := by
  apply Subgroup.subset_normalClosure
  exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨r, hr, rfl⟩)

private theorem lift_generatorEquiv_symm_reindexWord
    (q : FreeGroup Generator) :
    FreeGroup.lift
        (fun i : Fin 8 ↦ wordInMarkedGroup
          (FreeGroup.of (generatorEquivFin8.symm i)))
        (reindexWord q) = wordInMarkedGroup q := by
  change ((FreeGroup.lift _).comp reindexWord) q = wordInMarkedGroup q
  apply freeGroup_hom_eq_on_generators
  intro i
  simp [reindexWord, generatorEquivFin8]

/-- The reindexed marked word is not a relation of the canonical point. -/
theorem markedWord8_not_mem_literalPoint :
    mark ≠ 1 → markedWord8 ∉ literalPoint.relations := by
  intro hmark hw
  let assignment : Fin 8 → MarkedGroup := fun i ↦
    wordInMarkedGroup (FreeGroup.of (generatorEquivFin8.symm i))
  have hrels : ∀ q ∈ (relators8 : Set (FreeGroup (Fin 8))),
      FreeGroup.lift assignment q = 1 := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hq)
    rw [lift_generatorEquiv_symm_reindexWord]
    exact PresentedGroup.one_of_mem (Finset.mem_coe.mpr hr)
  have hkill := PresentedGroup.to_group_eq_one_of_mem_closure hrels markedWord8 hw
  rw [show markedWord8 = reindexWord markedWord from rfl,
    lift_generatorEquiv_symm_reindexWord] at hkill
  exact hmark hkill

/-- The literal point belongs to its own exact cylinder. -/
theorem literalPoint_mem_literalCylinder : literalPoint ∈ literalCylinder :=
  mem_cylinder_self literalPoint controlWords

/-- The exact literal cylinder is nonempty. -/
theorem literalCylinder_nonempty : literalCylinder.Nonempty :=
  ⟨literalPoint, literalPoint_mem_literalCylinder⟩

/-- The exact literal cylinder is simultaneously open and closed. -/
theorem literalCylinder_isClopen : IsClopen literalCylinder :=
  isClopen_cylinder literalPoint controlWords

/-- The canonical rank-eight marking of an arbitrary marked quotient,
transported back to the printed alphabet. -/
def quotientGenerator (N : MarkedGroupSpace 8) (i : Generator) : N.Quotient :=
  QuotientGroup.mk (FreeGroup.of (generatorEquivFin8 i))

private theorem lift_reindexed_quotient_mk
    (N : MarkedGroupSpace 8) (q : FreeGroup Generator) :
    FreeGroup.lift (quotientGenerator N) q =
      (QuotientGroup.mk (reindexWord q) : N.Quotient) := by
  change FreeGroup.lift (quotientGenerator N) q =
    ((QuotientGroup.mk' N.relations).comp reindexWord) q
  apply freeGroup_hom_eq_on_generators
  intro i
  simp [quotientGenerator, reindexWord]

/-- Every point of the cylinder satisfies every printed relation. -/
theorem cylinder_relator_eq_one {N : MarkedGroupSpace 8}
    (hN : N ∈ literalCylinder) {r : FreeGroup Generator}
    (hr : r ∈ relators) :
    FreeGroup.lift (quotientGenerator N) r = 1 := by
  rw [lift_reindexed_quotient_mk]
  rw [QuotientGroup.eq_one_iff]
  have hcontrol : reindexWord r ∈ controlWords := by
    exact Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨r, hr, rfl⟩)
  exact ((mem_cylinder_iff literalPoint N controlWords).mp hN
    _ hcontrol).mpr (reindexed_relator_mem_literalPoint hr)

/-- Every point of the cylinder keeps the marked word nontrivial. -/
theorem cylinder_markedWord_ne_one {N : MarkedGroupSpace 8}
    (hmark : mark ≠ 1) (hN : N ∈ literalCylinder) :
    FreeGroup.lift (quotientGenerator N) markedWord ≠ 1 := by
  rw [lift_reindexed_quotient_mk]
  intro hone
  have hmem : reindexWord markedWord ∈ N.relations := by
    rw [← QuotientGroup.eq_one_iff]
    exact hone
  have hcontrol : markedWord8 ∈ controlWords := Finset.mem_insert_self _ _
  exact markedWord8_not_mem_literalPoint hmark
    (((mem_cylinder_iff literalPoint N controlWords).mp hN
      _ hcontrol).mp hmem)

end
end LiteralMarkedCylinder
end GroupApproximation
