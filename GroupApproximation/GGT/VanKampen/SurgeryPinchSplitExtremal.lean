import GroupApproximation.GGT.VanKampen.SurgeryPinchSplitSections
import GroupApproximation.Meta.AxiomGuard

/-!
# Distinguished section families across a vertex splitting

Osin's distinguished system (Definition 9.2, arXiv:math/0411039v3, §9) is taken over every reduced
O-equivalent diagram at once (`GloballyDistinguishedSectionFamily`), so a surgery that keeps the
relator cells and the selected regions yields another optimum.  Splitting a vertex at a pinch is
such a surgery.  When the selected regions avoid both pinch faces, `transportSection` keeps the
weight, the number of regions and the legal labels, and the competitors range over the same class.
So the transported family is again distinguished (`transportDistinguished`), and no transport in the
reverse direction is needed.
-/

namespace GroupApproximation.GGT.VanKampen.PinchSplit

open GroupApproximation.GGT.VanKampen.Embedded

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **A distinguished section family across a vertex splitting of its diagram.** -/
noncomputable def transportDistinguished
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    [DecidableEq S.diagram.toCombMap.Dart] (I : Input S.diagram)
    (havoid : ∀ b ∈ S.family, I.Avoids b.1) :
    GloballyDistinguishedSectionFamily D lambda c eps Delta cuts where
  toRealizedSectionFamily := transportSection S.toRealizedSectionFamily I havoid
  label_admissible :=
    transportSection_labelLegal S.toRealizedSectionFamily I havoid _ S.label_admissible
  weight_maximal other hother :=
    (S.weight_maximal other hother).trans_eq
      (transportSection_weight S.toRealizedSectionFamily I havoid).symm
  card_minimal other hother hweight :=
    (transportSection_card S.toRealizedSectionFamily I havoid).trans_le
      (S.card_minimal other hother
        (hweight.trans (transportSection_weight S.toRealizedSectionFamily I havoid)))

theorem transportDistinguished_toRealizedSectionFamily
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    [DecidableEq S.diagram.toCombMap.Dart] (I : Input S.diagram)
    (havoid : ∀ b ∈ S.family, I.Avoids b.1) :
    (transportDistinguished S I havoid).toRealizedSectionFamily =
      transportSection S.toRealizedSectionFamily I havoid :=
  rfl

theorem transportDistinguished_diagram
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    [DecidableEq S.diagram.toCombMap.Dart] (I : Input S.diagram)
    (havoid : ∀ b ∈ S.family, I.Avoids b.1) :
    (transportDistinguished S I havoid).diagram = I.diagram :=
  rfl

theorem transportDistinguished_family
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    [DecidableEq S.diagram.toCombMap.Dart] (I : Input S.diagram)
    (havoid : ∀ b ∈ S.family, I.Avoids b.1) :
    (transportDistinguished S I havoid).family = I.regionFamily S.family havoid :=
  rfl

/-- The weight is unchanged. -/
theorem transportDistinguished_weight
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    [DecidableEq S.diagram.toCombMap.Dart] (I : Input S.diagram)
    (havoid : ∀ b ∈ S.family, I.Avoids b.1) :
    (transportDistinguished S I havoid).toRealizedSectionFamily.weight =
      S.toRealizedSectionFamily.weight :=
  transportSection_weight S.toRealizedSectionFamily I havoid

/-- The number of regions is unchanged. -/
theorem transportDistinguished_card
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    [DecidableEq S.diagram.toCombMap.Dart] (I : Input S.diagram)
    (havoid : ∀ b ∈ S.family, I.Avoids b.1) :
    (transportDistinguished S I havoid).family.card = S.family.card :=
  transportSection_card S.toRealizedSectionFamily I havoid

/-- Every transported region avoids the merged face. -/
theorem transportDistinguished_avoid_merged
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    [DecidableEq S.diagram.toCombMap.Dart] (I : Input S.diagram)
    (havoid : ∀ b ∈ S.family, I.Avoids b.1) :
    ∀ a ∈ (transportDistinguished S I havoid).family, I.merged ∉ a.1 :=
  I.regionFamily_avoid_merged S.family havoid

end GroupApproximation.GGT.VanKampen.PinchSplit

#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.transportDistinguished
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.transportDistinguished_weight
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.transportDistinguished_card
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.transportDistinguished_avoid_merged
