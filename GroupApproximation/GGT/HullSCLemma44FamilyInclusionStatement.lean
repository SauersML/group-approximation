import GroupApproximation.GGT.HullSCLemma44FamilyStatement

/-!
# Hull Lemma 4.4 with an included preserved alphabet

Successive fillings keep the original finite relative generating set but may
enlarge Hull's ambient alphabet.  Hull's proof uses only that every original
letter is available in the ambient alphabet: the small-cancellation estimates
run in the latter, while quotient relative hyperbolicity is asserted for the
image of the former.

`HullLemma44CanonicalQuotientFamilyInclusionStatement` is this exact form.
Specializing inclusion to equality recovers the earlier family statement, so
all existing selected-family consumers remain consequences.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-- **Hull Lemma 4.4 with an arbitrary preserved family whose alphabet is
contained in the filling alphabet.** -/
def HullLemma44CanonicalQuotientFamilyInclusionStatement : Prop :=
  ∀ {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S)
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda),
      original.alphabet.carrier ⊆ A.alphabet.carrier →
      original.IsHyperbolicallyEmbedded →
      ∀ R : ℕ,
        ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
          ∀ (W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))))
            {Q : Type u} [Group Q] (q : G →* Q),
            RelWord.IsLemma44Input selected.rel W eps mu rho →
            Function.Surjective q →
            q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W) →
              Set.InjOn q (cayleyBall A.alphabet R) ∧
                Nonempty (QuotientPeripheralPreservation q selected) ∧
                Nonempty (CanonicalQuotientFamilyPreservation q original) ∧
                Nonempty (QuotientJointPeripheralPreservation q selected original)

/-- The inclusion form specializes directly to the established canonical
selected-family statement by preserving the empty original family. -/
theorem hullLemma44CanonicalQuotientStatement_of_familyInclusion
    (h44 : HullLemma44CanonicalQuotientFamilyInclusionStatement.{u, 0}) :
    HullLemma44CanonicalQuotientStatement.{u} := by
  intro G _ A N k S selected R
  obtain ⟨eps, rho, mu, hmu, hgood⟩ :=
    h44 selected (emptyPreservedRelGenSet A)
      (by rw [emptyPreservedRelGenSet_alphabet A])
      (emptyPreservedRelGenSet_embedded A) R
  refine ⟨eps, rho, mu, hmu, ?_⟩
  intro W Q _ q hinput hsurj hker
  obtain ⟨hinj, hselected, _horiginal, _hjoint⟩ :=
    hgood W q hinput hsurj hker
  exact ⟨hinj, hselected⟩

/-! ## Identity model -/

/-- The four conclusions of the inclusion interface are simultaneously
satisfied by the identity quotient whenever the source joint family is
hyperbolically embedded.  This tests the arbitrary-family output independently
of the small-cancellation threshold quantifiers. -/
theorem familyInclusionConclusion_identityModel
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S)
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda)
    (horiginal : original.IsHyperbolicallyEmbedded)
    (joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k)))
    (hbaseInv : ∀ x ∈ joint.base, x⁻¹ ∈ joint.base)
    (hjointOriginal : ∀ lam,
      joint.fam (Sum.inl lam) = original.fam lam)
    (hjointSelected : ∀ i,
      joint.fam (Sum.inr i) = selected.cores.peripheral i)
    (hjoint : joint.IsHyperbolicallyEmbedded) (R : ℕ) :
    Set.InjOn (MonoidHom.id G) (cayleyBall A.alphabet R) ∧
      Nonempty (QuotientPeripheralPreservation (MonoidHom.id G) selected) ∧
      Nonempty
        (CanonicalQuotientFamilyPreservation (MonoidHom.id G) original) ∧
      Nonempty
        (QuotientJointPeripheralPreservation (MonoidHom.id G) selected
          original) := by
  have hid : Function.Bijective (MonoidHom.id G) :=
    ⟨Function.injective_id, Function.surjective_id⟩
  exact ⟨Function.injective_id.injOn,
    quotientPeripheralPreservation_of_bijective selected (MonoidHom.id G) hid,
    canonicalQuotientFamilyPreservation_of_bijective original horiginal
      (MonoidHom.id G) hid,
    quotientJointPeripheralPreservation_of_bijective selected original joint
      hbaseInv hjointOriginal hjointSelected hjoint (MonoidHom.id G) hid⟩

end HullSC
end GroupApproximation
