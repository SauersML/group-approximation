import GroupApproximation.GGT.HullSCLemma44RespellingOneRelator
import GroupApproximation.GGT.HullSCLemma44BoundedBridge
import GroupApproximation.Meta.AxiomGuard

/-!
# Hull's relator read in the joint family, with the published length bound

Osin's proof of his Theorem 2.4 (arXiv:math/0411039, §8) and Hull's proof of his Corollary 7.4
apply the small cancellation lemma to the *joint* collection: the original peripheral subgroups
together with the auxiliary elementary subgroups `E(h₁), E(h₂)`, of which the relator
`t h₁^{m₁} h₂^{m₁} ⋯` is already a word once `t` has been adjoined to the relative base.  The
original collection is then recovered by dropping the auxiliary members (Osin's Lemma 8.2), not
by re-spelling the relators over the original family alone.  So the only re-spelling the source
performs is the reading of the relator in the joint letters, which is the index relabelling of
`GGT/HullSCLemma44JointRelabel.lean`.

This module proves that reading at the published bounded input `RelWord.IsBoundedLemma44Input`
(Hull's strong boundedness, with the uniform length bound, issue #201), in the predicate
`BoundedRelatorRespellingAt` of `GGT/HullSCLemma44BoundedBridge.lean`.  The relabelling changes
no length, so the bound is carried across unchanged.

* `boundedRelatorRespellingAt_joint` is the relabelling at the structural hypotheses.
* `boundedRelatorRespellingAt_joint_of_familyBinders` derives three of those hypotheses from
  the family form's own binders.
* `boundedRelatorRespellingAt_joint_of_hullRelator` specializes to one relator `v` whose base
  letters are joint base letters.
* `boundedRelatorRespellingAt_joint_of_baseLetter` specializes to Hull's §6 relator, whose only
  base letter is `t⁻¹`.
* `exists_publishedRelator_boundedJointRespelling` reads the published relator producer
  `exists_auxiliaryRelatorOfBaseLetterPublished_exact` in the joint family.

Nothing here is assumed: every declaration is a theorem.  The uniform
`BoundedHullRelatorRespellingStatement` is not used and is not on the chain.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-! ## The relabelling keeps the length bound -/

/-- Relabelling the index changes no word length, so a uniform length bound survives. -/
theorem lengthBounded_jointRelabelWords {G : Type u} {Lambda : Type w} {k : ℕ}
    {W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k)))}
    (h : ∃ L : ℕ, ∀ word ∈ W, word.length ≤ L) :
    ∃ L : ℕ, ∀ word ∈ jointRelabelWords (Lambda := Lambda) W, word.length ≤ L := by
  obtain ⟨L, hL⟩ := h
  refine ⟨L, fun word hword => ?_⟩
  obtain ⟨v₀, hv₀, hmap⟩ := mem_jointRelabelWords_iff.mp hword
  rw [← hmap, List.length_map]
  exact hL v₀ hv₀

/-- **Hull's relator family, read in the joint peripheral family, at the bounded input.**  The
unbounded clauses are `isLemma44Input_jointRelabelWords`; the length bound is carried by
`lengthBounded_jointRelabelWords`. -/
theorem isBoundedLemma44Input_jointRelabelWords {G : Type u} [Group G]
    {A : HullGeneratingSet G} {N : Subgroup G} {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S) {Lambda : Type w}
    (joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k)))
    (hbaseSub : joint.base ⊆ selected.rel.base)
    (hfamInl : ∀ (lam : Lambda) (x : G),
      x ∈ joint.fam (Sum.inl lam) → x ∈ selected.rel.base)
    (hfamInr : ∀ i : AuxiliaryPeripheralIndex k,
      joint.fam (Sum.inr i) = selected.rel.fam i)
    (halphabet : joint.alphabet.carrier ⊆ selected.rel.alphabet.carrier)
    {W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k)))}
    {eps rho : ℕ} {mu : ℝ}
    (hWbase : ∀ v ∈ W, ∀ x : G, GGT.RelLetter.base x ∈ v → x ∈ joint.base)
    (hsc : RelWord.IsBoundedLemma44Input selected.rel W eps mu rho) :
    RelWord.IsBoundedLemma44Input joint (jointRelabelWords (Lambda := Lambda) W)
      eps mu rho :=
  ⟨isLemma44Input_jointRelabelWords selected joint hbaseSub hfamInl hfamInr
      halphabet hWbase hsc.toIsLemma44Input,
    lengthBounded_jointRelabelWords hsc.lengthBounded⟩

/-! ## The bounded joint re-spelling -/

/-- **The joint family needs no re-spelling at the bounded input either**: the index relabelling
meets any prescribed thresholds already met by the source relators, with the same length
bound. -/
theorem boundedRelatorRespellingAt_joint {G : Type u} [Group G]
    {A : HullGeneratingSet G} {N : Subgroup G} {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S) {Lambda : Type w}
    (joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k)))
    (hbaseSub : joint.base ⊆ selected.rel.base)
    (hfamInl : ∀ (lam : Lambda) (x : G),
      x ∈ joint.fam (Sum.inl lam) → x ∈ selected.rel.base)
    (hfamInr : ∀ i : AuxiliaryPeripheralIndex k,
      joint.fam (Sum.inr i) = selected.rel.fam i)
    (halphabet : joint.alphabet.carrier ⊆ selected.rel.alphabet.carrier)
    {W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k)))}
    {eps0 rho0 eps rho : ℕ} {mu : ℝ}
    (heps : eps0 ≤ eps) (hrho : rho0 ≤ rho) (h20 : 20 * (eps + 1) ≤ rho)
    (hWbase : ∀ v ∈ W, ∀ x : G, GGT.RelLetter.base x ∈ v → x ∈ joint.base)
    (hsc : RelWord.IsBoundedLemma44Input selected.rel W eps mu rho) :
    BoundedRelatorRespellingAt joint W eps0 rho0 mu :=
  ⟨jointRelabelWords (Lambda := Lambda) W, eps, rho, heps, hrho, h20,
    congrArg Subgroup.normalClosure (listVal_image_relabelWords
      (Sum.inr : AuxiliaryPeripheralIndex k →
        Sum Lambda (AuxiliaryPeripheralIndex k)) W),
    isBoundedLemma44Input_jointRelabelWords selected joint hbaseSub hfamInl hfamInr
      halphabet hWbase hsc⟩

/-- **The bounded joint re-spelling from the family form's binders.**  Three of the structural
hypotheses are theorems of the binders (`famInl_mem_selectedBase`, `famInr_eq_selectedFam`,
`jointAlphabet_subset_selectedAlphabet`); what remains is the base containment and the side
condition on the relators. -/
theorem boundedRelatorRespellingAt_joint_of_familyBinders {G : Type u} [Group G]
    {A : HullGeneratingSet G} {N : Subgroup G} {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S) {Lambda : Type w}
    (original : GGT.RelGenSet G Lambda)
    (joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k)))
    (hA : original.alphabet.carrier ⊆ A.alphabet.carrier)
    (hbaseSub : joint.base ⊆ selected.rel.base)
    (hinl : ∀ lam : Lambda, joint.fam (Sum.inl lam) = original.fam lam)
    (hinr : ∀ i : AuxiliaryPeripheralIndex k,
      joint.fam (Sum.inr i) = selected.cores.peripheral i)
    {W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k)))}
    {eps0 rho0 eps rho : ℕ} {mu : ℝ}
    (heps : eps0 ≤ eps) (hrho : rho0 ≤ rho) (h20 : 20 * (eps + 1) ≤ rho)
    (hWbase : ∀ v ∈ W, ∀ x : G, GGT.RelLetter.base x ∈ v → x ∈ joint.base)
    (hsc : RelWord.IsBoundedLemma44Input selected.rel W eps mu rho) :
    BoundedRelatorRespellingAt joint W eps0 rho0 mu :=
  boundedRelatorRespellingAt_joint selected joint hbaseSub
    (famInl_mem_selectedBase selected original joint hA hinl)
    (famInr_eq_selectedFam selected joint hinr)
    (jointAlphabet_subset_selectedAlphabet selected joint hbaseSub
      (famInl_mem_selectedBase selected original joint hA hinl)
      (famInr_eq_selectedFam selected joint hinr))
    heps hrho h20 hWbase hsc

/-- **One relator.**  The relator family is the symmetrized closure of one word whose base letters
are joint base letters; inversion-closure of the joint base lifts the side condition to the
closure (`baseLetters_symmetrized_mem_of_baseLetters`). -/
theorem boundedRelatorRespellingAt_joint_of_hullRelator {G : Type u} [Group G]
    {A : HullGeneratingSet G} {N : Subgroup G} {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S) {Lambda : Type w}
    (original : GGT.RelGenSet G Lambda)
    (joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k)))
    (hA : original.alphabet.carrier ⊆ A.alphabet.carrier)
    (hbaseSub : joint.base ⊆ selected.rel.base)
    (hjointInv : ∀ x ∈ joint.base, x⁻¹ ∈ joint.base)
    (hinl : ∀ lam : Lambda, joint.fam (Sum.inl lam) = original.fam lam)
    (hinr : ∀ i : AuxiliaryPeripheralIndex k,
      joint.fam (Sum.inr i) = selected.cores.peripheral i)
    {v : List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))}
    {eps0 rho0 eps rho : ℕ} {mu : ℝ}
    (heps : eps0 ≤ eps) (hrho : rho0 ≤ rho) (h20 : 20 * (eps + 1) ≤ rho)
    (hvbase : ∀ x : G, GGT.RelLetter.base x ∈ v → x ∈ joint.base)
    (hsc : RelWord.IsBoundedLemma44Input selected.rel (RelWord.symmetrized v)
      eps mu rho) :
    BoundedRelatorRespellingAt joint (RelWord.symmetrized v) eps0 rho0 mu :=
  boundedRelatorRespellingAt_joint_of_familyBinders selected original joint hA hbaseSub
    hinl hinr heps hrho h20
    (baseLetters_symmetrized_mem_of_baseLetters v joint.base hvbase hjointInv) hsc

/-- **Hull's §6 relator.**  Its only base letter is `t⁻¹`, so the side condition is
`t⁻¹ ∈ joint.base`: Osin adjoins `t` to the relative base before choosing the relator. -/
theorem boundedRelatorRespellingAt_joint_of_baseLetter {G : Type u} [Group G]
    {A : HullGeneratingSet G} {N : Subgroup G} {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S) {Lambda : Type w}
    (original : GGT.RelGenSet G Lambda)
    (joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k)))
    (hA : original.alphabet.carrier ⊆ A.alphabet.carrier)
    (hbaseSub : joint.base ⊆ selected.rel.base)
    (hjointInv : ∀ x ∈ joint.base, x⁻¹ ∈ joint.base)
    (hinl : ∀ lam : Lambda, joint.fam (Sum.inl lam) = original.fam lam)
    (hinr : ∀ i : AuxiliaryPeripheralIndex k,
      joint.fam (Sum.inr i) = selected.cores.peripheral i)
    {t : G} (htJoint : t⁻¹ ∈ joint.base)
    {v : List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))}
    {eps0 rho0 eps rho : ℕ} {mu : ℝ}
    (heps : eps0 ≤ eps) (hrho : rho0 ≤ rho) (h20 : 20 * (eps + 1) ≤ rho)
    (hvbase : ∀ x : G, GGT.RelLetter.base x ∈ v → x = t⁻¹)
    (hsc : RelWord.IsBoundedLemma44Input selected.rel (RelWord.symmetrized v)
      eps mu rho) :
    BoundedRelatorRespellingAt joint (RelWord.symmetrized v) eps0 rho0 mu :=
  boundedRelatorRespellingAt_joint_of_hullRelator selected original joint hA hbaseSub
    hjointInv hinl hinr heps hrho h20
    (fun x hx => by
      rw [hvbase x hx]
      exact htJoint)
    hsc

/-- **The published relator, read in the joint family.**  Hull's exact §6 relator
(`exists_auxiliaryRelatorOfBaseLetterPublished_exact`) is a Lemma 4.9 input over the selected
family, a bounded Lemma 4.4 input there (its closure is one relator's), and has a bounded
re-spelling over the joint family at any prescribed thresholds below the chosen ones. -/
theorem exists_publishedRelator_boundedJointRespelling {G : Type u} [Group G]
    {A : HullGeneratingSet G} {N : Subgroup G} {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S) (hN : Suitable A.alphabet N)
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda)
    (joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k)))
    (hA : original.alphabet.carrier ⊆ A.alphabet.carrier)
    (hbaseSub : joint.base ⊆ selected.rel.base)
    (hjointInv : ∀ x ∈ joint.base, x⁻¹ ∈ joint.base)
    (hinl : ∀ lam : Lambda, joint.fam (Sum.inl lam) = original.fam lam)
    (hinr : ∀ i : AuxiliaryPeripheralIndex k,
      joint.fam (Sum.inr i) = selected.cores.peripheral i)
    (t : G) (ht : t⁻¹ ∈ selected.rel.base) (htJoint : t⁻¹ ∈ joint.base)
    (eps0 rho0 eps rho : ℕ) (mu : ℝ) (hmu : 0 < mu)
    (heps : eps0 ≤ eps) (hrho : rho0 ≤ rho) (h20 : 20 * (eps + 1) ≤ rho) :
    ∃ u ∈ N, ∃ R : List (GGT.RelLetter G (AuxiliaryPeripheralIndex k)),
      GGT.RelLetter.listVal R = t⁻¹ * u ∧
        RelWord.IsLemma49Input selected.rel (RelWord.symmetrized R) eps mu rho ∧
        RelWord.IsBoundedLemma44Input selected.rel (RelWord.symmetrized R) eps mu rho ∧
        BoundedRelatorRespellingAt joint (RelWord.symmetrized R) eps0 rho0 mu := by
  obtain ⟨u, hu, R, hval, hsc, hbase⟩ :=
    selected.exists_auxiliaryRelatorOfBaseLetterPublished_exact hN t ht eps rho mu hmu
  have hbounded :
      RelWord.IsBoundedLemma44Input selected.rel (RelWord.symmetrized R) eps mu rho :=
    hsc.toIsLemma44Input.bounded_symmetrized
  refine ⟨u, hu, R, hval, hsc, hbounded, ?_⟩
  exact boundedRelatorRespellingAt_joint_of_baseLetter selected original joint hA hbaseSub
    hjointInv hinl hinr htJoint heps hrho h20 hbase hbounded

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.lengthBounded_jointRelabelWords
#audit_axioms GroupApproximation.HullSC.isBoundedLemma44Input_jointRelabelWords
#audit_axioms GroupApproximation.HullSC.boundedRelatorRespellingAt_joint
#audit_axioms GroupApproximation.HullSC.boundedRelatorRespellingAt_joint_of_familyBinders
#audit_axioms GroupApproximation.HullSC.boundedRelatorRespellingAt_joint_of_hullRelator
#audit_axioms GroupApproximation.HullSC.boundedRelatorRespellingAt_joint_of_baseLetter
#audit_axioms GroupApproximation.HullSC.exists_publishedRelator_boundedJointRespelling
