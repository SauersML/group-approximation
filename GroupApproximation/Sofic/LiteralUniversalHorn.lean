import GroupApproximation.Sofic.LiteralNonMFLinearWitness

/-!
# The finite universal Horn sentence falsified by the literal presentation

The group-theoretic content of the manuscript's quasi-identity is isolated
here without introducing a first-order syntax library.  `SatisfiesQuasiIdentity`
is the semantic universal Horn sentence associated to a finite list of free
group relators and one conclusion word.

The canonical tuple in the literal presented group violates the conclusion
unconditionally, using the exact Clifford realization of its mark.  This
module deliberately makes no analytic claim that operator-MF groups satisfy
the sentence: the repository has no proof of property `(T)` for the abstract
six-generator group printed in the literal presentation.
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

/-- The literal group itself falsifies its finite quasi-identity.  This half
is unconditional and uses no property-`(T)` or MF input. -/
theorem literalMarkedGroup_not_satisfies_literalQuasiIdentity :
    ¬ SatisfiesQuasiIdentity Generator relators markedWord MarkedGroup := by
  intro h
  exact canonicalAssignment_markedWord_ne_one
    (h (fun i : Generator ↦ wordInMarkedGroup (FreeGroup.of i))
      canonicalAssignment_satisfies_relators)

end LiteralUniversalHorn
end GroupApproximation
