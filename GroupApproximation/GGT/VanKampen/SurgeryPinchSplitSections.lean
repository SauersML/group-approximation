import GroupApproximation.GGT.VanKampen.SurgeryPinchSplitRegions
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundCaseOne
import GroupApproximation.Meta.AxiomGuard

/-!
# Section families across a vertex splitting

The last layer of surgery 3 for Osin's Lemma 9.4, Case 2 (arXiv:math/0411039v3, §9).  A realized
section family whose regions avoid both pinch faces survives the split of its diagram:

* every transported region has the target profile of the region it came from
  (`regionFamily_profile`), so it still respects the sections and stays nondegenerate;
* the unbound darts of every relator cell are the same (`unboundDarts_eq`, `unboundDarts_card`,
  `sum_unboundDarts_card`);
* `transportSection`: the section family on the split diagram, with the same weight and card
  (`transportSection_weight`, `transportSection_card`), legal labels kept
  (`transportSection_labelLegal`).
-/

namespace GroupApproximation.GGT.VanKampen.PinchSplit

open GroupApproximation.GGT.VanKampen.Embedded
open scoped Classical

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

namespace Input

variable {Delta : DiscDiagram.{u, w, v} W} [DecidableEq Delta.toCombMap.Dart] (I : Input Delta)
  {D : RelGenSet G Lambda} {eps : ℕ}

/-- The exterior of the split is the kept exterior. -/
theorem outerFace_eq : I.diagram.outerFace = I.kept Delta.outerFace := rfl

/-- Legal labels stay legal. -/
theorem labelLegal (E : RelGenSet G Lambda) (h : ∀ d, E.IsLetter (Delta.label d))
    (d : I.diagram.toCombMap.Dart) : E.IsLetter (I.diagram.label d) :=
  h d

/-- **Every transported region has the target profile of the region it came from.** -/
theorem regionFamily_profile (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, I.Avoids a.1) {a : RegionCandidate D eps I.diagram}
    (ha : a ∈ I.regionFamily family havoid) :
    ∃ b ∈ family, RegionCandidate.SameTargetProfile a b := by
  obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp ha
  refine ⟨b.val, b.property, And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))⟩
  · exact Option.map_eq_none_iff
  · exact CyclicArc.mapTo_start b.val.2.targetArc id (I.targetDarts_eq b.val.2.target)
  · exact CyclicArc.mapTo_length b.val.2.targetArc id (I.targetDarts_eq b.val.2.target)
  · exact CyclicArc.mapTo_length b.val.2.sourceArc id (I.cellDarts_eq b.val.2.source)

/-! ## Unbound darts -/

theorem mem_cellArcDarts_iff {Xi : DiscDiagram.{u, w, v} W} (a : RegionCandidate D eps Xi)
    (i : Fin Xi.rCellCount) (d : Xi.toCombMap.Dart) :
    d ∈ a.cellArcDarts i ↔ (a.2.source = i ∧ d ∈ a.2.sourceArc.darts) ∨
      (a.2.target = some i ∧ d ∈ a.2.targetArc.darts) := by
  unfold RegionCandidate.cellArcDarts
  rw [Finset.mem_union]
  by_cases hs : a.2.source = i <;> by_cases ht : a.2.target = some i <;> simp [hs, ht]

theorem regionCandidate_source_eq_iff (a : { a : RegionCandidate D eps Delta // I.Avoids a.1 })
    (i : Fin Delta.rCellCount) :
    (I.regionCandidate a).2.source = I.cellMap.indexEquiv i ↔ a.val.2.source = i :=
  I.cellMap.indexEquiv.apply_eq_iff_eq

theorem regionCandidate_target_eq_some_iff
    (a : { a : RegionCandidate D eps Delta // I.Avoids a.1 }) (i : Fin Delta.rCellCount) :
    (I.regionCandidate a).2.target = some (I.cellMap.indexEquiv i) ↔ a.val.2.target = some i := by
  change Option.map I.cellMap.indexEquiv a.val.2.target = some (I.cellMap.indexEquiv i) ↔ _
  constructor
  · intro h
    exact Option.map_injective I.cellMap.indexEquiv.injective h
  · intro h
    rw [h]
    rfl

theorem regionCandidate_target_isSome (a : { a : RegionCandidate D eps Delta // I.Avoids a.1 }) :
    (I.regionCandidate a).2.target.isSome = a.val.2.target.isSome :=
  Option.isSome_map

theorem regionCandidate_sourceArc_darts
    (a : { a : RegionCandidate D eps Delta // I.Avoids a.1 }) :
    (I.regionCandidate a).2.sourceArc.darts = a.val.2.sourceArc.darts :=
  (CyclicArc.mapTo_darts a.val.2.sourceArc id (I.cellDarts_eq a.val.2.source)).trans
    (List.map_id _)

theorem regionCandidate_targetArc_darts
    (a : { a : RegionCandidate D eps Delta // I.Avoids a.1 }) :
    (I.regionCandidate a).2.targetArc.darts = a.val.2.targetArc.darts :=
  (CyclicArc.mapTo_darts a.val.2.targetArc id (I.targetDarts_eq a.val.2.target)).trans
    (List.map_id _)

theorem mem_boundDarts_iff {Xi : DiscDiagram.{u, w, v} W}
    (selected : Finset (RegionCandidate D eps Xi)) (interior : Bool) (i : Fin Xi.rCellCount)
    (d : Xi.toCombMap.Dart) :
    d ∈ RegionCandidate.boundDarts selected interior i ↔
      ∃ a ∈ selected, a.2.target.isSome = interior ∧ d ∈ a.cellArcDarts i := by
  constructor
  · intro hd
    obtain ⟨a, ha, hd⟩ := Finset.mem_biUnion.mp hd
    obtain ⟨ha, hkind⟩ := Finset.mem_filter.mp ha
    exact ⟨a, ha, hkind, hd⟩
  · rintro ⟨a, ha, hkind, hd⟩
    exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hkind⟩, hd⟩

theorem mem_unboundDarts_iff {Xi : DiscDiagram.{u, w, v} W}
    (selected : Finset (RegionCandidate D eps Xi)) (i : Fin Xi.rCellCount)
    (d : Xi.toCombMap.Dart) :
    d ∈ RegionCandidate.unboundDarts selected i ↔
      d ∈ cellDarts Xi i ∧ ¬(d ∈ RegionCandidate.boundDarts selected false i ∨
        d ∈ RegionCandidate.boundDarts selected true i) := by
  unfold RegionCandidate.unboundDarts
  simp only [Finset.mem_sdiff, Finset.mem_union, List.mem_toFinset]

/-- The split keeps every dart, but `I.diagram.toCombMap.Dart` is `Delta.toCombMap.Dart` only
after unfolding the split, so memberships across the two diagrams are compared in term mode
(`rw` and `simp` see the mixed membership as ill-typed at instance transparency). -/
theorem mem_cellArcDarts_regionCandidate_iff
    (a : { a : RegionCandidate D eps Delta // I.Avoids a.1 }) (i : Fin Delta.rCellCount)
    (d : I.diagram.toCombMap.Dart) :
    d ∈ (I.regionCandidate a).cellArcDarts (I.cellMap.indexEquiv i) ↔ d ∈ a.val.cellArcDarts i :=
  (mem_cellArcDarts_iff (I.regionCandidate a) (I.cellMap.indexEquiv i) d).trans <|
    (or_congr
      (and_congr (I.regionCandidate_source_eq_iff a i)
        (Iff.of_eq (congrArg (fun l : List I.diagram.toCombMap.Dart => d ∈ l)
          (I.regionCandidate_sourceArc_darts a))))
      (and_congr (I.regionCandidate_target_eq_some_iff a i)
        (Iff.of_eq (congrArg (fun l : List I.diagram.toCombMap.Dart => d ∈ l)
          (I.regionCandidate_targetArc_darts a))))).trans
    (mem_cellArcDarts_iff a.val i d).symm

/-- A transported region has the same darts on the image of a relator cell. -/
theorem cellArcDarts_regionCandidate
    (a : { a : RegionCandidate D eps Delta // I.Avoids a.1 }) (i : Fin Delta.rCellCount) :
    (I.regionCandidate a).cellArcDarts (I.cellMap.indexEquiv i) = a.val.cellArcDarts i :=
  Finset.ext (I.mem_cellArcDarts_regionCandidate_iff a i)

/-- The retained cell arcs of either kind at a relator cell are unchanged. -/
theorem boundDarts_regionFamily (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, I.Avoids a.1) (interior : Bool) (i : Fin Delta.rCellCount) :
    RegionCandidate.boundDarts (I.regionFamily family havoid) interior (I.cellMap.indexEquiv i) =
      RegionCandidate.boundDarts family interior i := by
  refine Finset.ext fun d =>
    (mem_boundDarts_iff (I.regionFamily family havoid) interior (I.cellMap.indexEquiv i) d).trans
      (Iff.trans ?_ (mem_boundDarts_iff family interior i d).symm)
  constructor
  · rintro ⟨a', ha', hkind, hd⟩
    obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp ha'
    exact ⟨b.val, b.property,
      (I.regionCandidate_target_isSome ⟨b.val, havoid b.val b.property⟩).symm.trans hkind,
      (I.mem_cellArcDarts_regionCandidate_iff ⟨b.val, havoid b.val b.property⟩ i d).mp hd⟩
  · rintro ⟨b, hb, hkind, hd⟩
    exact ⟨I.regionCandidate ⟨b, havoid b hb⟩,
      Finset.mem_map.mpr ⟨⟨b, hb⟩, Finset.mem_attach _ _, rfl⟩,
      (I.regionCandidate_target_isSome ⟨b, havoid b hb⟩).trans hkind,
      (I.mem_cellArcDarts_regionCandidate_iff ⟨b, havoid b hb⟩ i d).mpr hd⟩

/-- **The unbound darts of a relator cell are unchanged.** -/
theorem unboundDarts_eq (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, I.Avoids a.1) (i : Fin Delta.rCellCount) :
    RegionCandidate.unboundDarts (I.regionFamily family havoid) (I.cellMap.indexEquiv i) =
      RegionCandidate.unboundDarts family i :=
  Finset.ext fun d =>
    (mem_unboundDarts_iff (I.regionFamily family havoid) (I.cellMap.indexEquiv i) d).trans <|
      (and_congr
        (Iff.of_eq (congrArg (fun l : List I.diagram.toCombMap.Dart => d ∈ l)
          ((I.cellDarts_eq i).trans (List.map_id _))))
        (not_congr (or_congr
          (Finset.ext_iff.mp (I.boundDarts_regionFamily family havoid false i) d)
          (Finset.ext_iff.mp (I.boundDarts_regionFamily family havoid true i) d)))).trans
      (mem_unboundDarts_iff family i d).symm

theorem unboundDarts_card (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, I.Avoids a.1) (i : Fin Delta.rCellCount) :
    (RegionCandidate.unboundDarts (I.regionFamily family havoid) (I.cellMap.indexEquiv i)).card =
      (RegionCandidate.unboundDarts family i).card :=
  congrArg Finset.card (I.unboundDarts_eq family havoid i)

/-- **The total unbound length is unchanged.** -/
theorem sum_unboundDarts_card (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, I.Avoids a.1) :
    ∑ j : Fin I.diagram.rCellCount,
        (RegionCandidate.unboundDarts (I.regionFamily family havoid) j).card =
      ∑ i : Fin Delta.rCellCount, (RegionCandidate.unboundDarts family i).card := by
  rw [← Equiv.sum_comp I.cellMap.indexEquiv]
  exact Finset.sum_congr rfl fun i _ => I.unboundDarts_card family havoid i

end Input

/-! ## Section families -/

variable {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **A section family across a vertex splitting of its diagram.** -/
noncomputable def transportSection (S : RealizedSectionFamily D lambda c eps Delta cuts)
    [DecidableEq S.diagram.toCombMap.Dart] (I : Input S.diagram)
    (havoid : ∀ b ∈ S.family, I.Avoids b.1) : RealizedSectionFamily D lambda c eps Delta cuts where
  diagram := I.diagram
  equiv := S.equiv.trans I.oEquivalent
  reduced := I.reduced S.reduced
  family := I.regionFamily S.family havoid
  pairwise := I.regionFamily_pairwise S.family havoid S.pairwise
  respects := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := I.regionFamily_profile S.family havoid ha
    exact RegionCandidate.respectsSections_of_sameTargetProfile cuts hab (S.respects b hb)
  nondegenerate := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := I.regionFamily_profile S.family havoid ha
    obtain ⟨hs, ht⟩ := S.nondegenerate b hb
    exact ⟨lt_of_lt_of_eq hs hab.2.2.2.symm, lt_of_lt_of_eq ht hab.2.2.1.symm⟩

theorem transportSection_diagram (S : RealizedSectionFamily D lambda c eps Delta cuts)
    [DecidableEq S.diagram.toCombMap.Dart] (I : Input S.diagram)
    (havoid : ∀ b ∈ S.family, I.Avoids b.1) : (transportSection S I havoid).diagram = I.diagram :=
  rfl

theorem transportSection_family (S : RealizedSectionFamily D lambda c eps Delta cuts)
    [DecidableEq S.diagram.toCombMap.Dart] (I : Input S.diagram)
    (havoid : ∀ b ∈ S.family, I.Avoids b.1) :
    (transportSection S I havoid).family = I.regionFamily S.family havoid :=
  rfl

/-- **The weight is unchanged.** -/
theorem transportSection_weight (S : RealizedSectionFamily D lambda c eps Delta cuts)
    [DecidableEq S.diagram.toCombMap.Dart] (I : Input S.diagram)
    (havoid : ∀ b ∈ S.family, I.Avoids b.1) : (transportSection S I havoid).weight = S.weight :=
  I.regionFamily_weight S.family havoid

/-- The number of regions is unchanged. -/
theorem transportSection_card (S : RealizedSectionFamily D lambda c eps Delta cuts)
    [DecidableEq S.diagram.toCombMap.Dart] (I : Input S.diagram)
    (havoid : ∀ b ∈ S.family, I.Avoids b.1) :
    (transportSection S I havoid).family.card = S.family.card :=
  I.regionFamily_card S.family havoid

/-- Legal labels stay legal. -/
theorem transportSection_labelLegal (S : RealizedSectionFamily D lambda c eps Delta cuts)
    [DecidableEq S.diagram.toCombMap.Dart] (I : Input S.diagram)
    (havoid : ∀ b ∈ S.family, I.Avoids b.1) (E : RelGenSet G Lambda)
    (h : S.toRealizedRegionFamily.LabelLegal E) :
    (transportSection S I havoid).toRealizedRegionFamily.LabelLegal E :=
  fun d => h d

end GroupApproximation.GGT.VanKampen.PinchSplit

#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.regionFamily_profile
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.unboundDarts_eq
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.sum_unboundDarts_card
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.transportSection
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.transportSection_weight
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.transportSection_labelLegal
