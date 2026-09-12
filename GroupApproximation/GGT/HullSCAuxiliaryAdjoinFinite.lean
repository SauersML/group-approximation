import GroupApproximation.GGT.HullSCCanonicalQuotientPublished
import GroupApproximation.Meta.AxiomGuard

/-!
# Adjoining finitely many letters of the alphabet to an auxiliary family's base

An auxiliary peripheral family may have finitely many letters of its own relative alphabet adjoined
to its base without changing its cores, its peripheral subgroups or its relative alphabet
(`AuxiliaryPeripheralFamily.exists_adjoinFinite`): each letter is adjoined with its inverse by
`AuxiliaryPeripheralFamily.adjoinPair`, and both already lie in the alphabet.  Since the alphabet is
unchanged, so is the relative Cayley graph, and with it acylindricity.

This is the enlargement Osin's Theorem 2.4 needs before the joint relator family is read: the joint
collection's relative base is the original base together with finitely many letters of the selected
alphabet, and the re-spelling of the published relator asks for the joint base to lie in the
selected base.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

namespace AuxiliaryPeripheralFamily

/-- Adjoining a letter of the alphabet with its inverse leaves the alphabet unchanged. -/
theorem adjoinPair_alphabet_carrier_of_mem {G : Type u} [Group G] {A : HullGeneratingSet G}
    {N : Subgroup G} {k : ℕ} {S : Fin k → Subgroup G} (D : AuxiliaryPeripheralFamily A N S)
    {a : G} (ha : a ∈ D.rel.alphabet.carrier) :
    (D.adjoinPair a).rel.alphabet.carrier = D.rel.alphabet.carrier := by
  apply Set.Subset.antisymm
  · rintro x ((hx | hx) | hx)
    · exact Or.inl hx
    · rcases hx with rfl | rfl
      · exact ha
      · exact D.rel.alphabet.symmetricGenerating.1 _ ha
    · exact Or.inr hx
  · exact GGT.RelGenSet.alphabet_subset_adjoinPair D.rel a

/-- **Finitely many letters of the alphabet adjoined to the base.** -/
theorem exists_adjoinFinite {G : Type u} [Group G] {A : HullGeneratingSet G}
    {N : Subgroup G} {k : ℕ} {S : Fin k → Subgroup G} (D : AuxiliaryPeripheralFamily A N S)
    {T : Set G} (hT : T.Finite) (hsub : T ⊆ D.rel.alphabet.carrier) :
    ∃ E : AuxiliaryPeripheralFamily A N S,
      E.cores = D.cores ∧ D.rel.base ⊆ E.rel.base ∧ T ⊆ E.rel.base ∧
        E.rel.alphabet.carrier = D.rel.alphabet.carrier := by
  classical
  have key : ∀ s : Finset G, (s : Set G) ⊆ D.rel.alphabet.carrier →
      ∃ E : AuxiliaryPeripheralFamily A N S,
        E.cores = D.cores ∧ D.rel.base ⊆ E.rel.base ∧ (s : Set G) ⊆ E.rel.base ∧
          E.rel.alphabet.carrier = D.rel.alphabet.carrier := by
    intro s
    induction s using Finset.induction with
    | empty =>
        intro _
        exact ⟨D, rfl, subset_rfl, by simp, rfl⟩
    | @insert a s ha ih =>
        intro hs
        have hs' : (s : Set G) ⊆ D.rel.alphabet.carrier := by
          intro x hx
          exact hs (by simp [hx])
        obtain ⟨E, hcores, hbase, hsE, hcarrier⟩ := ih hs'
        have haE : a ∈ E.rel.alphabet.carrier := by
          rw [hcarrier]
          exact hs (by simp)
        refine ⟨E.adjoinPair a, hcores,
          hbase.trans (GGT.RelGenSet.base_subset_adjoinPair E.rel a), ?_, ?_⟩
        · intro x hx
          have hx' : x = a ∨ x ∈ (s : Set G) := by simpa using hx
          rcases hx' with rfl | hx'
          · exact Or.inr (Or.inl rfl)
          · exact GGT.RelGenSet.base_subset_adjoinPair E.rel a (hsE hx')
        · rw [adjoinPair_alphabet_carrier_of_mem E haE, hcarrier]
  obtain ⟨E, hcores, hbase, hTE, hcarrier⟩ := key hT.toFinset (by simpa using hsub)
  exact ⟨E, hcores, hbase, by simpa using hTE, hcarrier⟩

end AuxiliaryPeripheralFamily

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.AuxiliaryPeripheralFamily.adjoinPair_alphabet_carrier_of_mem
#audit_axioms GroupApproximation.HullSC.AuxiliaryPeripheralFamily.exists_adjoinFinite
