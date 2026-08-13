import GroupApproximation.Sofic.ChosenNonMFTheorem
import GroupApproximation.Sofic.LiteralUniversalHorn
import GroupApproximation.Sofic.NormMFCoronaRadical

/-!
# A finite universal Horn obstruction for operator-MF groups

The chosen finite presentation carries a nontrivial word in its operator-MF
residual.  Its relators therefore imply that word in every operator-MF group.
This is the unconditional semantic quasi-identity promised by the construction;
no property of the unresolved literal eight-generator presentation is used.
-/

namespace GroupApproximation
namespace ChosenUniversalHorn

open ChosenMarkedPresentation ChosenNonMFTheorem

/-- Every assignment satisfying the chosen finite relators induces the
corresponding homomorphism from the chosen presented group. -/
noncomputable def assignmentHom {H : Type*} [Group H]
    (assignment : Generator → H)
    (hrel : ∀ r ∈ relators, FreeGroup.lift assignment r = 1) :
    MarkedGroup →* H :=
  PresentedGroup.toGroup hrel

/-- Evaluation of a word through the induced homomorphism agrees with free
evaluation at the assignment. -/
theorem assignmentHom_mk {H : Type*} [Group H]
    (assignment : Generator → H)
    (hrel : ∀ r ∈ relators, FreeGroup.lift assignment r = 1)
    (word : FreeGroup Generator) :
    assignmentHom assignment hrel
        (PresentedGroup.mk (relators : Set (FreeGroup Generator)) word) =
      FreeGroup.lift assignment word := by
  simpa [assignmentHom] using presentedToGroup_mk hrel word

/-- **Finite universal Horn obstruction.**  Every operator-MF group satisfies
the quasi-identity whose premises are the chosen presentation's finite
relator set and whose conclusion is its marked word. -/
theorem isOperatorMF_satisfies_chosenQuasiIdentity
    (H : Type*) [Group H] (hMF : IsOperatorMF H) :
    SatisfiesQuasiIdentity Generator relators markedWord H := by
  intro assignment hrel
  let f : MarkedGroup →* H := assignmentHom assignment hrel
  obtain ⟨X, hX, rho, hrho⟩ := hMF
  have hmark : f mark = 1 := by
    apply hrho
    simpa only [MonoidHom.comp_apply, map_one] using
      mark_normMFInvisible.toCoronaMFInvisible X hX (rho.comp f)
  have heval := assignmentHom_mk assignment hrel markedWord
  exact heval ▸ hmark

/-- The canonical tuple in the chosen presented group satisfies every
premise of the quasi-identity. -/
theorem canonicalAssignment_satisfies_relators :
    ∀ r ∈ relators,
      FreeGroup.lift
        (fun i : Generator ↦ wordInMarkedGroup (FreeGroup.of i)) r = 1 := by
  intro r hr
  rw [freeGroup_lift_presentedGroup_generators]
  exact PresentedGroup.one_of_mem (Finset.mem_coe.mpr hr)

/-- Its marked conclusion is false. -/
theorem canonicalAssignment_markedWord_ne_one :
    FreeGroup.lift
        (fun i : Generator ↦ wordInMarkedGroup (FreeGroup.of i)) markedWord ≠
      1 := by
  rw [freeGroup_lift_presentedGroup_generators]
  exact mark_ne_one

/-- The chosen finitely presented non-MF group falsifies the same finite
quasi-identity which every operator-MF group satisfies. -/
theorem markedGroup_not_satisfies_chosenQuasiIdentity :
    ¬ SatisfiesQuasiIdentity Generator relators markedWord MarkedGroup := by
  intro h
  exact canonicalAssignment_markedWord_ne_one
    (h (fun i : Generator ↦ wordInMarkedGroup (FreeGroup.of i))
      canonicalAssignment_satisfies_relators)

end ChosenUniversalHorn
end GroupApproximation
