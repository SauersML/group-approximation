import GroupApproximation.Sofic.ChosenUniversalHorn
import GroupApproximation.Sofic.MarkedGroupTopology
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# A clopen non-MF cylinder around the chosen finitely presented witness

The chosen finite presentation and its marked residual element determine an
exact marked-group cylinder: keep every chosen relator trivial and keep the
marked word nontrivial.  The finite Horn obstruction proves that every point
of this cylinder is non-MF.  Unlike the literal radius-34 cylinder, this
result uses only the unconditional chosen Shalom-cover witness.
-/

namespace GroupApproximation
namespace ChosenMarkedCylinder

open ChosenMarkedPresentation ChosenNonMFTheorem ChosenUniversalHorn
open MarkedGroupSpace

noncomputable section

/-- Reindex the chosen finite alphabet by a standard finite type. -/
def generatorEquiv : Generator ≃ Fin (generatorCount + 2) :=
  finSumFinEquiv

/-- Reindex a chosen presentation word by the standard alphabet. -/
def reindexWord : FreeGroup Generator →* FreeGroup (Fin (generatorCount + 2)) :=
  FreeGroup.map generatorEquiv

/-- The chosen finite relator set on the standard alphabet. -/
def reindexedRelators : Finset (FreeGroup (Fin (generatorCount + 2))) :=
  relators.image reindexWord

/-- The chosen marked obstruction word on the standard alphabet. -/
def reindexedMarkedWord : FreeGroup (Fin (generatorCount + 2)) :=
  reindexWord markedWord

/-- The chosen finitely presented witness as a marked-group-space point. -/
def chosenPoint : MarkedGroupSpace (generatorCount + 2) where
  relations := Subgroup.normalClosure
    (reindexedRelators : Set (FreeGroup (Fin (generatorCount + 2))))
  normal_relations := Subgroup.normalClosure_normal

/-- The exact finite control set: all chosen relators and survival of the
marked word. -/
def controlWords : Finset (FreeGroup (Fin (generatorCount + 2))) :=
  insert reindexedMarkedWord reindexedRelators

/-- The exact marked-group neighborhood of the chosen witness. -/
def chosenCylinder : Set (MarkedGroupSpace (generatorCount + 2)) :=
  cylinder chosenPoint controlWords

private theorem lift_generatorEquiv_symm_reindexWord
    (q : FreeGroup Generator) :
    FreeGroup.lift
        (fun i : Fin (generatorCount + 2) ↦ wordInMarkedGroup
          (FreeGroup.of (generatorEquiv.symm i)))
        (reindexWord q) = wordInMarkedGroup q := by
  change ((FreeGroup.lift _).comp reindexWord) q = wordInMarkedGroup q
  apply freeGroup_hom_eq_on_generators
  intro i
  simp [reindexWord, generatorEquiv]

/-- Each reindexed chosen relator belongs to the relation subgroup of the
canonical point. -/
theorem reindexed_relator_mem_chosenPoint {r : FreeGroup Generator}
    (hr : r ∈ relators) : reindexWord r ∈ chosenPoint.relations := by
  apply Subgroup.subset_normalClosure
  exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨r, hr, rfl⟩)

/-- The reindexed marked word is not a relation of the canonical point. -/
theorem reindexedMarkedWord_not_mem_chosenPoint :
    reindexedMarkedWord ∉ chosenPoint.relations := by
  intro hw
  let assignment : Fin (generatorCount + 2) → MarkedGroup := fun i ↦
    wordInMarkedGroup (FreeGroup.of (generatorEquiv.symm i))
  have hrels : ∀ q ∈
      (reindexedRelators : Set (FreeGroup (Fin (generatorCount + 2)))),
      FreeGroup.lift assignment q = 1 := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hq)
    rw [lift_generatorEquiv_symm_reindexWord]
    exact PresentedGroup.one_of_mem (Finset.mem_coe.mpr hr)
  have hkill := PresentedGroup.to_group_eq_one_of_mem_closure
    hrels reindexedMarkedWord hw
  rw [show reindexedMarkedWord = reindexWord markedWord from rfl,
    lift_generatorEquiv_symm_reindexWord] at hkill
  exact mark_ne_one hkill

/-- The canonical point belongs to its own exact cylinder. -/
theorem chosenPoint_mem_chosenCylinder : chosenPoint ∈ chosenCylinder :=
  mem_cylinder_self chosenPoint controlWords

/-- The chosen cylinder is nonempty. -/
theorem chosenCylinder_nonempty : chosenCylinder.Nonempty :=
  ⟨chosenPoint, chosenPoint_mem_chosenCylinder⟩

/-- The chosen cylinder is simultaneously open and closed. -/
theorem chosenCylinder_isClopen : IsClopen chosenCylinder :=
  isClopen_cylinder chosenPoint controlWords

/-- The canonical assignment into an arbitrary marked quotient, transported
back to the chosen alphabet. -/
def quotientGenerator (N : MarkedGroupSpace (generatorCount + 2))
    (i : Generator) : N.Quotient :=
  QuotientGroup.mk (FreeGroup.of (generatorEquiv i))

private theorem lift_reindexed_quotient_mk
    (N : MarkedGroupSpace (generatorCount + 2))
    (q : FreeGroup Generator) :
    FreeGroup.lift (quotientGenerator N) q =
      (QuotientGroup.mk (reindexWord q) : N.Quotient) := by
  change FreeGroup.lift (quotientGenerator N) q =
    ((QuotientGroup.mk' N.relations).comp reindexWord) q
  apply freeGroup_hom_eq_on_generators
  intro i
  simp [quotientGenerator, reindexWord]

/-- Every point of the cylinder satisfies every chosen relator. -/
theorem cylinder_relator_eq_one
    {N : MarkedGroupSpace (generatorCount + 2)}
    (hN : N ∈ chosenCylinder) {r : FreeGroup Generator}
    (hr : r ∈ relators) :
    FreeGroup.lift (quotientGenerator N) r = 1 := by
  rw [lift_reindexed_quotient_mk, QuotientGroup.eq_one_iff]
  have hcontrol : reindexWord r ∈ controlWords :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨r, hr, rfl⟩)
  exact ((mem_cylinder_iff chosenPoint N controlWords).mp hN
    _ hcontrol).mpr (reindexed_relator_mem_chosenPoint hr)

/-- Every point of the cylinder keeps the chosen marked word nontrivial. -/
theorem cylinder_markedWord_ne_one
    {N : MarkedGroupSpace (generatorCount + 2)}
    (hN : N ∈ chosenCylinder) :
    FreeGroup.lift (quotientGenerator N) markedWord ≠ 1 := by
  rw [lift_reindexed_quotient_mk]
  intro hone
  have hmem : reindexedMarkedWord ∈ N.relations := by
    rw [← QuotientGroup.eq_one_iff]
    exact hone
  have hcontrol : reindexedMarkedWord ∈ controlWords :=
    Finset.mem_insert_self _ _
  exact reindexedMarkedWord_not_mem_chosenPoint
    (((mem_cylinder_iff chosenPoint N controlWords).mp hN
      _ hcontrol).mp hmem)

/-- Every group in the exact finite cylinder around the chosen witness is
non-MF. -/
theorem chosenCylinder_subset_nonMF :
    chosenCylinder ⊆
      {N : MarkedGroupSpace (generatorCount + 2) |
        ¬ IsOperatorMF N.Quotient} := by
  intro N hN hMF
  have hkill := isOperatorMF_satisfies_chosenQuasiIdentity N.Quotient hMF
  exact cylinder_markedWord_ne_one hN
    (hkill (quotientGenerator N) (fun _ hr ↦
      cylinder_relator_eq_one hN hr))

end
end ChosenMarkedCylinder
end GroupApproximation
