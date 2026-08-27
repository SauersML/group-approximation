import GroupApproximation.Sofic.LiteralNonMFEndpoint

/-!
# The finite universal Horn sentence falsified by the literal presentation

The group-theoretic content of the manuscript's quasi-identity is isolated
here without introducing a first-order syntax library.  `SatisfiesQuasiIdentity`
is the semantic universal Horn sentence associated to a finite list of free
group relators and one conclusion word.

The canonical tuple in the literal presented group violates the conclusion
unconditionally, using the exact Clifford realization of its mark.  The
premise-free literal non-MF endpoint proves that every operator-MF group
satisfies the same quasi-identity.  Thus the obstruction is one finite
universal Horn sentence, not merely a global non-embedding statement.
-/

namespace GroupApproximation

universe u v

/-- Semantic form of the finite universal Horn sentence

`forall x, (and_{r in R} r(x) = 1) -> w(x) = 1`.

The definition quantifies over assignments of the free generators and uses
the universal evaluation homomorphism of the free group. -/
def SatisfiesQuasiIdentity (X : Type u)
    (R : Finset (FreeGroup X)) (w : FreeGroup X)
    (H : Type v) [Group H] : Prop :=
  ∀ assignment : X → H,
    (∀ r ∈ R, FreeGroup.lift assignment r = 1) →
      FreeGroup.lift assignment w = 1

namespace LiteralUniversalHorn

open LiteralNonMFPresentation

/-- Every assignment satisfying the literal relators induces the canonical
homomorphism from the literal presented group. -/
noncomputable def assignmentHom {H : Type*} [Group H]
    (assignment : Generator → H)
    (hrel : ∀ r ∈ relators, FreeGroup.lift assignment r = 1) :
    MarkedGroup →* H :=
  PresentedGroup.toGroup hrel

/-- Evaluation through the induced homomorphism is free evaluation at the
chosen tuple. -/
@[simp] theorem assignmentHom_mk {H : Type*} [Group H]
    (assignment : Generator → H)
    (hrel : ∀ r ∈ relators, FreeGroup.lift assignment r = 1)
    (word : FreeGroup Generator) :
    assignmentHom assignment hrel
        (PresentedGroup.mk (relators : Set (FreeGroup Generator)) word) =
      FreeGroup.lift assignment word := by
  rfl

/-- **Literal finite universal Horn obstruction.**  In every operator-MF
group, any eight elements satisfying the forty-one printed relators also
satisfy the marked conclusion `w = 1`. -/
theorem isOperatorMF_satisfies_literalQuasiIdentity
    (H : Type*) [Group H] (hMF : IsOperatorMF H) :
    SatisfiesQuasiIdentity Generator relators markedWord H := by
  intro assignment hrel
  let f : MarkedGroup →* H := assignmentHom assignment hrel
  obtain ⟨X, hX, rho, hrho⟩ := hMF
  have hmark : f mark = 1 := by
    apply hrho
    simpa only [MonoidHom.comp_apply, map_one] using
      LiteralNonMFEndpoint.literal_mark_normMFInvisible.toCoronaMFInvisible
        X hX (rho.comp f)
  exact (assignmentHom_mk assignment hrel markedWord).symm.trans hmark

/-- The canonical generating tuple of the literal presented group satisfies
every premise of the quasi-identity. -/
theorem canonicalAssignment_satisfies_relators :
    ∀ r ∈ relators,
      FreeGroup.lift
        (fun i : Generator ↦ wordInMarkedGroup (FreeGroup.of i)) r = 1 := by
  intro r hr
  rw [freeGroup_lift_presentedGroup_generators]
  exact PresentedGroup.one_of_mem (Finset.mem_coe.mpr hr)

/-- The same canonical tuple does not satisfy the Horn conclusion. -/
theorem canonicalAssignment_markedWord_ne_one :
    FreeGroup.lift
        (fun i : Generator ↦ wordInMarkedGroup (FreeGroup.of i)) markedWord ≠
      1 := by
  rw [freeGroup_lift_presentedGroup_generators]
  exact LiteralNonMFLinearWitness.literal_mark_ne_one

/-- **Exact manuscript package for the literal finite Horn obstruction.**
Every operator-MF group satisfies the displayed quasi-identity, while the
canonical tuple in the literal group satisfies all premises and violates its
conclusion. -/
theorem manuscriptLiteralUniversalHorn :
    (∀ (H : Type*) [Group H], IsOperatorMF H →
      SatisfiesQuasiIdentity Generator relators markedWord H) ∧
      (∀ r ∈ relators,
        FreeGroup.lift
          (fun i : Generator ↦ wordInMarkedGroup (FreeGroup.of i)) r = 1) ∧
      FreeGroup.lift
          (fun i : Generator ↦ wordInMarkedGroup (FreeGroup.of i)) markedWord ≠
        1 :=
  ⟨fun H _ hMF ↦ isOperatorMF_satisfies_literalQuasiIdentity H hMF,
    canonicalAssignment_satisfies_relators,
    canonicalAssignment_markedWord_ne_one⟩

/-- The literal group itself falsifies the finite quasi-identity satisfied by
every operator-MF group. -/
theorem literalMarkedGroup_not_satisfies_literalQuasiIdentity :
    ¬ SatisfiesQuasiIdentity Generator relators markedWord MarkedGroup := by
  intro h
  exact canonicalAssignment_markedWord_ne_one
    (h (fun i : Generator ↦ wordInMarkedGroup (FreeGroup.of i))
      canonicalAssignment_satisfies_relators)

end LiteralUniversalHorn
end GroupApproximation
