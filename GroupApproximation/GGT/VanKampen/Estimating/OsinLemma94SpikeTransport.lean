import GroupApproximation.GGT.VanKampen.SurgerySpikeDeletionRegions
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94DartMinimal
import GroupApproximation.Meta.AxiomGuard

/-!
# Distinguished section families across spike deletions

Osin (arXiv:math/0411039v3, §9), Lemma 9.4, Case 2 ends: "This contradicts our assumption that
`∑ l(t_i)` is minimal."  `OsinLemma94PlanarPieces` measures a family by the number of darts of
its diagram instead (`GloballyDistinguishedSectionFamily.DartMinimal`).  The descent for Case 2
inserts the connector, merges across the cutting path and deletes the rest of the cutting path as
spikes.  This file carries the optimal family across one spike deletion.

* `Surgery.SpikeDeletion.transportDistinguished`: a distinguished family across a spike deletion
  (`SurgerySpikeDeletionRegions.transportSection`) whose regions avoid the face of the spike.  The
  class the family is maximal in, the section families over diagrams O-equivalent to `Delta`,
  does not change, so maximal weight and minimal card carry over.
* The number of regions and the unbound sum are unchanged, no region contains the shrunk face,
  and two darts disappear (`transportDistinguished_card`, `transportDistinguished_unboundSum`,
  `transportDistinguished_avoid_shrunk`, `transportDistinguished_dartCount_add_two`).
* `GloballyDistinguishedSectionFamily.DartMinimal.false_of_spikeDeletion`: a dart-minimal family
  has no spike on a face that no selected region contains.
-/

namespace GroupApproximation.GGT.VanKampen

open Embedded

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

namespace Surgery.SpikeDeletion

/-- **A distinguished section family across a spike deletion of its diagram.** -/
noncomputable def transportDistinguished
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (R : SpikeDeletion S.diagram) (havoid : ∀ b ∈ S.family, R.face ∉ b.1) :
    GloballyDistinguishedSectionFamily D lambda c eps Delta cuts where
  toRealizedSectionFamily := transportSection S.toRealizedSectionFamily R havoid
  label_admissible :=
    transportSection_labelLegal S.toRealizedSectionFamily R havoid _ S.label_admissible
  weight_maximal other hother :=
    (S.weight_maximal other hother).trans_eq
      (transportSection_weight S.toRealizedSectionFamily R havoid).symm
  card_minimal other hother hweight :=
    (transportSection_card S.toRealizedSectionFamily R havoid).trans_le
      (S.card_minimal other hother
        (hweight.trans (transportSection_weight S.toRealizedSectionFamily R havoid)))

theorem transportDistinguished_diagram
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (R : SpikeDeletion S.diagram) (havoid : ∀ b ∈ S.family, R.face ∉ b.1) :
    (transportDistinguished S R havoid).diagram = R.diagram :=
  rfl

theorem transportDistinguished_family
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (R : SpikeDeletion S.diagram) (havoid : ∀ b ∈ S.family, R.face ∉ b.1) :
    (transportDistinguished S R havoid).family = R.regionFamily S.family havoid :=
  rfl

/-- The weight is unchanged. -/
theorem transportDistinguished_weight
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (R : SpikeDeletion S.diagram) (havoid : ∀ b ∈ S.family, R.face ∉ b.1) :
    (transportDistinguished S R havoid).toRealizedSectionFamily.weight =
      S.toRealizedSectionFamily.weight :=
  transportSection_weight S.toRealizedSectionFamily R havoid

/-- The number of regions is unchanged. -/
theorem transportDistinguished_card
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (R : SpikeDeletion S.diagram) (havoid : ∀ b ∈ S.family, R.face ∉ b.1) :
    (transportDistinguished S R havoid).family.card = S.family.card :=
  transportSection_card S.toRealizedSectionFamily R havoid

/-- Every transported region avoids the shrunk face. -/
theorem transportDistinguished_avoid_shrunk
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (R : SpikeDeletion S.diagram) (havoid : ∀ b ∈ S.family, R.face ∉ b.1) :
    ∀ a ∈ (transportDistinguished S R havoid).family, R.shrunk ∉ a.1 :=
  R.regionFamily_avoid_shrunk S.family havoid

/-- **The unbound sum is unchanged.** -/
theorem transportDistinguished_unboundSum
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (R : SpikeDeletion S.diagram) (havoid : ∀ b ∈ S.family, R.face ∉ b.1) :
    (transportDistinguished S R havoid).unboundSum = S.unboundSum :=
  R.sum_unboundDarts_card S.family havoid

/-- **Two darts disappear.** -/
theorem transportDistinguished_dartCount_add_two
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (R : SpikeDeletion S.diagram) (havoid : ∀ b ∈ S.family, R.face ∉ b.1) :
    (transportDistinguished S R havoid).diagram.toCombMap.dartCount + 2 =
      S.diagram.toCombMap.dartCount :=
  R.dartCount_add_two

/-- No face disappears. -/
theorem transportDistinguished_faceCount_eq
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (R : SpikeDeletion S.diagram) (havoid : ∀ b ∈ S.family, R.face ∉ b.1) :
    (transportDistinguished S R havoid).diagram.toCombMap.faceCount =
      S.diagram.toCombMap.faceCount :=
  R.faceCount_eq

end Surgery.SpikeDeletion

namespace GloballyDistinguishedSectionFamily

/-- **A dart-minimal family has no spike on a face that no selected region contains.**  Deleting
the spike keeps the unbound sum and removes two darts. -/
theorem DartMinimal.false_of_spikeDeletion
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts} (hS : S.DartMinimal)
    (R : Surgery.SpikeDeletion S.diagram) (havoid : ∀ b ∈ S.family, R.face ∉ b.1) : False := by
  refine hS.false_of_dartCount_lt
    (Surgery.SpikeDeletion.transportDistinguished_unboundSum S R havoid) ?_
  have hdart := Surgery.SpikeDeletion.transportDistinguished_dartCount_add_two S R havoid
  omega

end GloballyDistinguishedSectionFamily

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.SpikeDeletion.transportDistinguished
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.SpikeDeletion.transportDistinguished_card
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.SpikeDeletion.transportDistinguished_unboundSum
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.SpikeDeletion.transportDistinguished_avoid_shrunk
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.SpikeDeletion.transportDistinguished_dartCount_add_two
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.SpikeDeletion.transportDistinguished_faceCount_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.DartMinimal.false_of_spikeDeletion
