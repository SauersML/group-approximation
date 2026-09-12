import GroupApproximation.GGT.HullSCTheorem71General
import GroupApproximation.GGT.HullSCLemma44BoundedBridge
import GroupApproximation.Meta.AxiomGuard

/-!
# Hull's Theorem 7.1 at every acylindrically hyperbolic group, bounded Lemma 4.4

`HullSCTheorem71General` assembles the canonical quotient from the plain Lemma
4.4 statement.  The live Lemma 4.4 producers are over strongly bounded families
(`BoundedHullLemma44CanonicalQuotientStatement`), and this module is the same
assembly from that form, as `torsionFreeHullCanonicalQuotientStatement_of_boundedLemma44_of_lemma49`
is for the torsion-free one.  Clause (d) comes from
`nonempty_fillingAlphabetData_of_peripheralPreservation_general`, with no torsion
hypothesis.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-- **The canonical quotient at every ambient group, from the bounded Lemma 4.4
and Lemma 4.9.** -/
theorem hullCanonicalQuotientStatementGeneral_of_boundedLemma44_of_lemma49
    (hselect : SimultaneousAuxiliaryPeripheralSelection.{u})
    (h44 : BoundedHullLemma44CanonicalQuotientStatement.{u})
    (h49 : HullLemma49KernelPowerStatement.{u, 0}) :
    HullCanonicalQuotientStatementGeneral.{u} := by
  intro G _ A N hN k S hS t R
  obtain ⟨D₀⟩ := hselect A S hN hS
  obtain ⟨D, ht, hacy⟩ := D₀.exists_acylindricalAdjoinPair t
  obtain ⟨eps44, rho44, mu44, hmu44, hgood44⟩ := h44 D R
  obtain ⟨eps49, rho49, mu49, hmu49, hgood49⟩ :=
    h49 D.rel D.embedded hacy
  refine ⟨D, max eps44 eps49, max rho44 rho49, min mu44 mu49,
    ht, lt_min hmu44 hmu49, ?_⟩
  intro W v hv hsc
  let K : Subgroup G :=
    Subgroup.normalClosure ({GGT.RelLetter.listVal v} : Set G)
  let Q : Type u := G ⧸ K
  let q : G →* Q := QuotientGroup.mk' K
  have hscV : RelWord.IsLemma49Input D.rel (RelWord.symmetrized v)
      (max eps44 eps49) (min mu44 mu49) (max rho44 rho49) :=
    hsc.restrict_symmetrized hv
  have hsc44 : RelWord.IsBoundedLemma44Input D.rel (RelWord.symmetrized v)
      eps44 mu44 rho44 :=
    (hscV.toIsLemma44Input.mono_parameters
      (Nat.le_max_left _ _) (min_le_left _ _)
        (Nat.le_max_left _ _)).bounded_symmetrized
  have hsc49 : RelWord.IsLemma49Input D.rel W eps49 mu49 rho49 :=
    hsc.mono_parameters
      (Nat.le_max_right _ _) (min_le_right _ _) (Nat.le_max_right _ _)
  have hsurj : Function.Surjective q := QuotientGroup.mk'_surjective K
  have hker : q.ker = K := QuotientGroup.ker_mk' K
  have hkerV : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' RelWord.symmetrized v) := by
    rw [hker, RelWord.normalClosure_listVal_image_symmetrized]
  obtain ⟨hinj, ⟨P⟩⟩ := hgood44 (RelWord.symmetrized v) q hsc44 hsurj hkerV
  have hpower : KernelPowerCorrection K := hgood49 W v hv hsc49
  have hlift : ∀ y : Q, IsOfFinOrder y →
      ∃ g : G, q g = y ∧ orderOf g = orderOf y := by
    apply (kernelPowerCorrection_iff_finiteOrderLift q hsurj).mp
    rwa [hker]
  obtain ⟨F⟩ := nonempty_fillingAlphabetData_of_peripheralPreservation_general D P
  exact ⟨{ Q := Q
           group := inferInstance
           q := q
           surjective := hsurj
           ker_eq := hker
           hullSet := F.hullSet
           alphabet_image := F.alphabet_image
           injOn := hinj
           suitable_map := F.suitable_map
           suitable_map_family := F.suitable_map_family
           finiteOrder_lift := hlift }⟩

/-- **The published ball form at every acylindrically hyperbolic group, from the
bounded Lemma 4.4, Lemma 4.9 and the simultaneous peripheral selection.** -/
theorem hullBallFormStatementGeneral_of_boundedLemma44_of_lemma49
    (hselect : SimultaneousAuxiliaryPeripheralSelection.{u})
    (h44 : BoundedHullLemma44CanonicalQuotientStatement.{u})
    (h49 : HullLemma49KernelPowerStatement.{u, 0}) :
    HullBallFormStatementGeneral.{u} :=
  hullBallFormStatementGeneral_of_tower
    (hullTowerStatementGeneral_of_oneStep
      (hullOneStepStatementGeneral_of_canonicalQuotient
        (hullCanonicalQuotientStatementGeneral_of_boundedLemma44_of_lemma49
          hselect h44 h49)))

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.hullCanonicalQuotientStatementGeneral_of_boundedLemma44_of_lemma49
#audit_axioms GroupApproximation.HullSC.hullBallFormStatementGeneral_of_boundedLemma44_of_lemma49
