import GroupApproximation.Sofic.LiteralKazhdanCompression

/-!
# The finite universal Horn obstruction carried by the literal presentation

The group-theoretic content of the manuscript's quasi-identity is isolated
here without introducing a first-order syntax library.  `SatisfiesQuasiIdentity`
is the semantic universal Horn sentence associated to a finite list of free
group relators and one conclusion word.

For the literal eight-generator presentation, every operator-MF target
satisfies the sentence once property `(T)` of the literal base is supplied;
an exact rational SOS certificate supplies precisely that input.  The
canonical tuple in the literal presented group violates the conclusion
unconditionally, using the exact Clifford realization of its mark.
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

open LiteralNonMFPresentation LiteralKazhdanCompression

/-- Every map from the literal presented group to an operator-MF group kills
the marked word, provided the literal base has property `(T)`. -/
theorem map_mark_eq_one_of_hasKazhdanPropertyT
    (hT : HasKazhdanPropertyT.{0, 0} Base)
    {H : Type v} [Group H] (hH : IsOperatorMF H)
    (f : MarkedGroup →* H) : f mark = 1 := by
  obtain ⟨X, hX, j, hj⟩ := hH
  apply hj
  have hkill :=
    (mark_normMFInvisible_of_hasKazhdanPropertyT hT).toCoronaMFInvisible
      X hX (j.comp f)
  simpa only [MonoidHom.coe_comp, Function.comp_apply, map_one] using hkill

/-- **Finite quasi-identity for the literal presentation.**  Under the one
remaining property-`(T)` input, every operator-MF group satisfies all the
displayed relators only by killing the marked word. -/
theorem operatorMF_satisfies_literalQuasiIdentity_of_hasKazhdanPropertyT
    (hT : HasKazhdanPropertyT.{0, 0} Base)
    {H : Type v} [Group H] (hH : IsOperatorMF H) :
    SatisfiesQuasiIdentity Generator relators markedWord H := by
  intro assignment hrelations
  let f : MarkedGroup →* H := PresentedGroup.toGroup (by
    intro r hr
    exact hrelations r (Finset.mem_coe.mp hr))
  have hmark : f mark = 1 :=
    map_mark_eq_one_of_hasKazhdanPropertyT hT hH f
  change f (PresentedGroup.mk _ markedWord) = 1 at hmark
  rw [presentedToGroup_mk] at hmark
  exact hmark

/-- Proof-carrying form: an exact rational group-ring SOS certificate makes
the finite quasi-identity valid in every operator-MF group. -/
theorem operatorMF_satisfies_literalQuasiIdentity_of_isRationalCertificate
    {c : ℚ} (hcert : LiteralBaseSOS.IsRationalCertificate c)
    {H : Type v} [Group H] (hH : IsOperatorMF H) :
    SatisfiesQuasiIdentity Generator relators markedWord H :=
  operatorMF_satisfies_literalQuasiIdentity_of_hasKazhdanPropertyT
    (LiteralBaseSOS.base_hasKazhdanPropertyT_of_isRationalCertificate hcert)
    hH

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

/-- Exact separation package: a rational SOS certificate makes the finite
sentence true in every operator-MF group and false in the literal group. -/
theorem literalQuasiIdentity_separates_of_isRationalCertificate
    {c : ℚ} (hcert : LiteralBaseSOS.IsRationalCertificate c) :
    (∀ (H : Type) [Group H], IsOperatorMF H →
      SatisfiesQuasiIdentity Generator relators markedWord H) ∧
      ¬ SatisfiesQuasiIdentity Generator relators markedWord MarkedGroup := by
  exact ⟨fun H _ hH ↦
    operatorMF_satisfies_literalQuasiIdentity_of_isRationalCertificate
      hcert hH,
    literalMarkedGroup_not_satisfies_literalQuasiIdentity⟩

end LiteralUniversalHorn
end GroupApproximation
