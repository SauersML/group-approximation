import GroupApproximation.GGT.VanKampen.SurgeryGFaceMergeDarts
import GroupApproximation.GGT.VanKampen.Estimating.RegionPartition
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundCaseOne
import GroupApproximation.Meta.AxiomGuard

/-!
# Contiguity regions and section families through a G-face merge

The transport half of the G-face merge (`Surgery.GFaceMerge.diagram`) for Osin's Lemma 9.4,
Case 2 (arXiv:math/0411039v3, §9).  A face set `s` avoiding both merged faces survives the
merge as `faceSet s = s.image kept`, and each datum of a contiguity region on `s` transports
along `keep`, which is injective on the darts off the deleted edge, with left inverse `val`:

* its embedded boundary (`transportBoundary`): boundary darts, internal moves and boundary steps
  (`isBoundaryDart_keep_iff`, `internalMove_transport`, `boundaryStep_transport`);
* its shelling (`shelling`), face by face;
* the whole `ContiguityGeometry` (`contiguityGeometry`): arcs with the same start and length,
  sides mapped by `keep`, the same side words; hence the region candidate (`regionCandidate`),
  with the same weight.

A compatible family avoiding the merged faces transports to a compatible family of the merge
with the same card, weight and target profiles (`regionFamily`, `regionFamily_card`,
`regionFamily_weight`, `regionFamily_pairwise`, `regionFamily_faces`, `regionFamily_profile`,
`regionFamily_avoid_merged`).  The unbound darts of every relator cell correspond through
`keep` (`mem_unboundDarts_iff`, `unboundDarts_eq`, `unboundDarts_card`,
`sum_unboundDarts_card`).  `transportSection` is the section family on the merge, with the same
weight and card, nondegenerate, legal labels kept.
-/

namespace GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge

open scoped Classical
open GroupApproximation.GGT.VanKampen.Embedded

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}

section Transport

variable {Delta : DiscDiagram.{u, w, v} W} (R : GFaceMerge Delta)

/-! ## Darts and faces of the merge -/

theorem mem_map_keep_iff {l : List Delta.toCombMap.Dart}
    (hl : ∀ d ∈ l, d ≠ R.dart ∧ d ≠ Delta.toCombMap.alpha R.dart)
    (x : R.diagram.toCombMap.Dart) : x ∈ l.map R.keep ↔ R.val x ∈ l := by
  constructor
  · intro hx
    have h := List.mem_map_of_mem (f := R.val) hx
    rwa [R.map_keep_val hl] at h
  · intro hx
    have h := List.mem_map_of_mem (f := R.keep) hx
    rwa [R.keep_val] at h

/-- **A dart of the merge is based in the image of `s` exactly when its old dart was based
in `s`.** -/
theorem faceOf_mem_faceSet_iff {s : Finset Delta.toCombMap.Face}
    (hs : R.first ∉ s ∧ R.second ∉ s) (x : R.diagram.toCombMap.Dart) :
    R.diagram.toCombMap.faceOf x ∈ R.faceSet s ↔ Delta.toCombMap.faceOf (R.val x) ∈ s := by
  have h := R.faceOf_keep_mem_faceSet_iff hs (R.val_ne x)
  rwa [R.keep_val] at h

/-! ## Boundaries -/

theorem isBoundaryDart_keep_iff {s : Finset Delta.toCombMap.Face}
    (hs : R.first ∉ s ∧ R.second ∉ s) {d : Delta.toCombMap.Dart}
    (hd : d ≠ R.dart ∧ d ≠ Delta.toCombMap.alpha R.dart) :
    IsBoundaryDart R.diagram (R.faceSet s) (R.keep d) ↔ IsBoundaryDart Delta s d := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(R.faceOf_keep_mem_faceSet_iff hs hd).mp h1, fun h => h2 ?_⟩
    rw [R.alpha_keep hd]
    exact (R.faceOf_keep_mem_faceSet_iff hs (R.offEdge_alpha hd)).mpr h
  · rintro ⟨h1, h2⟩
    refine ⟨(R.faceOf_keep_mem_faceSet_iff hs hd).mpr h1, fun h => h2 ?_⟩
    rw [R.alpha_keep hd] at h
    exact (R.faceOf_keep_mem_faceSet_iff hs (R.offEdge_alpha hd)).mp h

theorem internalMove_transport {s : Finset Delta.toCombMap.Face}
    (hs : R.first ∉ s ∧ R.second ∉ s) {d e : Delta.toCombMap.Dart}
    (h : InternalBoundaryMove Delta s d e) :
    InternalBoundaryMove R.diagram (R.faceSet s) (R.keep d) (R.keep e) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hd := R.offEdge_of_faceOf_off (R.off_of_mem hs h1)
  refine ⟨(R.faceOf_keep_mem_faceSet_iff hs hd).mpr h1, ?_, ?_⟩
  · rw [R.alpha_keep hd]
    exact (R.faceOf_keep_mem_faceSet_iff hs (R.offEdge_alpha hd)).mpr h2
  · subst h3
    rw [R.alpha_keep hd, R.facePerm_keep (R.off_of_mem hs h2)]

theorem boundaryStep_transport {s : Finset Delta.toCombMap.Face}
    (hs : R.first ∉ s ∧ R.second ∉ s) {d e : Delta.toCombMap.Dart}
    (h : BoundaryStep Delta s d e) :
    BoundaryStep R.diagram (R.faceSet s) (R.keep d) (R.keep e) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hd := R.offEdge_of_faceOf_off (R.off_of_mem hs h1.1)
  have he := R.offEdge_of_faceOf_off (R.off_of_mem hs h2.1)
  refine ⟨(R.isBoundaryDart_keep_iff hs hd).mpr h1, (R.isBoundaryDart_keep_iff hs he).mpr h2, ?_⟩
  rw [R.facePerm_keep (R.off_of_mem hs h1.1)]
  exact h3.lift R.keep fun _ _ hm => R.internalMove_transport hs hm

/-- Every dart on the boundary of an avoiding face set is off the deleted edge. -/
theorem cycle_offEdge {s : Finset Delta.toCombMap.Face} (hs : R.first ∉ s ∧ R.second ∉ s)
    (B : FaceSetBoundary Delta s) :
    ∀ d ∈ B.cycle, d ≠ R.dart ∧ d ≠ Delta.toCombMap.alpha R.dart := fun d hd =>
  R.offEdge_of_faceOf_off (R.off_of_mem hs ((B.cycle_mem_iff d).mp hd).1)

/-- **The boundary of a face set avoiding the merged faces, after the merge.** -/
noncomputable def transportBoundary {s : Finset Delta.toCombMap.Face}
    (hs : R.first ∉ s ∧ R.second ∉ s) (B : FaceSetBoundary Delta s) :
    FaceSetBoundary R.diagram (R.faceSet s) where
  faces_nonempty := by
    obtain ⟨g, hg⟩ := B.faces_nonempty
    exact ⟨R.kept g, R.kept_mem_faceSet hg⟩
  all_gCells := by
    intro F hF
    obtain ⟨g, hg, rfl⟩ := R.mem_faceSet.mp hF
    have hoff := R.off_of_mem hs hg
    refine ⟨fun heq => (B.all_gCells g hg).1
      (R.kept_inj hoff R.outer_off (heq.trans R.outerFace_eq)), ?_⟩
    rw [R.faceWord_kept g hoff]
    exact (B.all_gCells g hg).2
  cycle := B.cycle.map R.keep
  cycle_nonempty := fun h => B.cycle_nonempty (List.map_eq_nil_iff.mp h)
  cycle_nodup := R.nodup_map_keep (R.cycle_offEdge hs B) B.cycle_nodup
  cycle_mem_iff := fun x => by
    rw [R.mem_map_keep_iff (R.cycle_offEdge hs B) x, B.cycle_mem_iff,
      ← R.isBoundaryDart_keep_iff hs (R.val_ne x), R.keep_val]
  cycle_chain :=
    List.isChain_map.mpr (B.cycle_chain.imp fun _ _ h => R.boundaryStep_transport hs h)
  cycle_closes := by
    rw [List.getLast_map, List.head_map]
    exact R.boundaryStep_transport hs B.cycle_closes

@[simp] theorem transportBoundary_cycle {s : Finset Delta.toCombMap.Face}
    (hs : R.first ∉ s ∧ R.second ∉ s) (B : FaceSetBoundary Delta s) :
    (R.transportBoundary hs B).cycle = B.cycle.map R.keep :=
  rfl

/-! ## Shellings -/

theorem shelling {s : Finset Delta.toCombMap.Face} (hs : R.first ∉ s ∧ R.second ∉ s)
    {l : List Delta.toCombMap.Face} {cycle : List Delta.toCombMap.Dart}
    (H : FaceShelling Delta s l cycle) :
    FaceShelling R.diagram (R.faceSet s) (l.map R.kept) (cycle.map R.keep) := by
  induction H with
  | empty => exact FaceShelling.empty
  | @step l before arc after exposed g hg k hrot rest ih =>
    rw [List.map_cons, List.map_append, List.map_append]
    rw [List.map_append, List.map_append] at ih
    have hoff := R.off_of_mem hs hg
    have harc : ∀ d ∈ arc, d ≠ R.dart ∧ d ≠ Delta.toCombMap.alpha R.dart := by
      intro d hd
      have h1 : Delta.toCombMap.alpha d ∈ arc.reverse.map Delta.toCombMap.alpha :=
        List.mem_map_of_mem (List.mem_reverse.mpr hd)
      have h2 : Delta.toCombMap.alpha d ∈ (Delta.faceBoundary g).darts.rotate k := by
        rw [hrot]
        exact List.mem_append.mpr (Or.inr h1)
      apply R.offEdge_of_faceOf_alpha_off
      rw [((Delta.faceBoundary g).mem_iff _).mp (List.mem_rotate.mp h2)]
      exact hoff
    refine FaceShelling.step (R.kept g) (R.kept_mem_faceSet hg) k ?_ ih
    rw [R.faceBoundary_kept_darts g hoff, ← List.map_rotate, hrot, List.map_append,
      R.invDarts_map harc]

/-! ## Contiguity geometry -/

theorem rightSide_offEdge {D : RelGenSet G Lambda} {eps : ℕ} {s : Finset Delta.toCombMap.Face}
    (hs : R.first ∉ s ∧ R.second ∉ s) (H : ContiguityGeometry D eps Delta s) :
    ∀ d ∈ H.rightSide, d ≠ R.dart ∧ d ≠ Delta.toCombMap.alpha R.dart := fun d hd =>
  R.cycle_offEdge hs H.boundary d (by
    rw [H.boundary_decomposition]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
      (List.mem_append.mpr (Or.inr hd))))))

theorem leftSide_offEdge {D : RelGenSet G Lambda} {eps : ℕ} {s : Finset Delta.toCombMap.Face}
    (hs : R.first ∉ s ∧ R.second ∉ s) (H : ContiguityGeometry D eps Delta s) :
    ∀ d ∈ H.leftSide, d ≠ R.dart ∧ d ≠ Delta.toCombMap.alpha R.dart := fun d hd =>
  R.cycle_offEdge hs H.boundary d (by
    rw [H.boundary_decomposition]
    exact List.mem_append.mpr (Or.inr hd))

/-- **A contiguity region avoiding the merged faces, after the merge.** -/
noncomputable def contiguityGeometry {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (hs : R.first ∉ s ∧ R.second ∉ s)
    (H : ContiguityGeometry D eps Delta s) :
    ContiguityGeometry D eps R.diagram (R.faceSet s) where
  boundary := R.transportBoundary hs H.boundary
  source := R.cellMap.indexEquiv H.source
  target := H.target.map R.cellMap.indexEquiv
  sourceArc := H.sourceArc.mapTo R.keep (R.cellDarts_eq H.source)
  targetArc := H.targetArc.mapTo R.keep (R.targetDarts_eq H.target)
  rightSide := H.rightSide.map R.keep
  leftSide := H.leftSide.map R.keep
  boundary_decomposition := by
    change H.boundary.cycle.map R.keep = _
    rw [R.reverseDarts_mapTo (fun d hd => R.cellDarts_offEdge H.source hd),
      R.targetBoundaryDarts_map, H.boundary_decomposition]
    simp only [List.map_append]
  rightSide_length_le := by simpa only [List.length_map] using H.rightSide_length_le
  leftSide_length_le := by simpa only [List.length_map] using H.leftSide_length_le
  rightSide_norm_le := by
    rw [R.dartWord_map (R.rightSide_offEdge hs H)]
    exact H.rightSide_norm_le
  leftSide_norm_le := by
    rw [R.dartWord_map (R.leftSide_offEdge hs H)]
    exact H.leftSide_norm_le
  pasting := by
    obtain ⟨l, hl⟩ := H.pasting
    exact ⟨l.map R.kept, R.shelling hs hl⟩

theorem contiguityGeometry_source_start {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (hs : R.first ∉ s ∧ R.second ∉ s)
    (H : ContiguityGeometry D eps Delta s) :
    (R.contiguityGeometry hs H).sourceArc.start.val = H.sourceArc.start.val :=
  H.sourceArc.mapTo_start R.keep (R.cellDarts_eq H.source)

theorem contiguityGeometry_source_length {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (hs : R.first ∉ s ∧ R.second ∉ s)
    (H : ContiguityGeometry D eps Delta s) :
    (R.contiguityGeometry hs H).sourceArc.length = H.sourceArc.length :=
  H.sourceArc.mapTo_length R.keep (R.cellDarts_eq H.source)

theorem contiguityGeometry_target_start {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (hs : R.first ∉ s ∧ R.second ∉ s)
    (H : ContiguityGeometry D eps Delta s) :
    (R.contiguityGeometry hs H).targetArc.start.val = H.targetArc.start.val :=
  H.targetArc.mapTo_start R.keep (R.targetDarts_eq H.target)

theorem contiguityGeometry_target_length {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (hs : R.first ∉ s ∧ R.second ∉ s)
    (H : ContiguityGeometry D eps Delta s) :
    (R.contiguityGeometry hs H).targetArc.length = H.targetArc.length :=
  H.targetArc.mapTo_length R.keep (R.targetDarts_eq H.target)

theorem contiguityGeometry_target_eq_none_iff {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (hs : R.first ∉ s ∧ R.second ∉ s)
    (H : ContiguityGeometry D eps Delta s) :
    (R.contiguityGeometry hs H).target = none ↔ H.target = none :=
  Option.map_eq_none_iff

theorem contiguityGeometry_injective {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (hs : R.first ∉ s ∧ R.second ∉ s) :
    Function.Injective (R.contiguityGeometry (D := D) (eps := eps) hs) := by
  intro H K h
  apply ContiguityGeometry.eq_of_data
  · exact R.map_keep_injective (R.cycle_offEdge hs H.boundary) (R.cycle_offEdge hs K.boundary)
      (congrArg (fun J => J.boundary.cycle) h)
  · exact R.cellMap.indexEquiv.injective (congrArg (fun J => J.source) h)
  · exact (Equiv.optionCongr R.cellMap.indexEquiv).injective (congrArg (fun J => J.target) h)
  · simpa only [contiguityGeometry_source_start] using
      congrArg (fun J => J.sourceArc.start.val) h
  · simpa only [contiguityGeometry_source_length] using
      congrArg (fun J => J.sourceArc.length) h
  · simpa only [contiguityGeometry_target_start] using
      congrArg (fun J => J.targetArc.start.val) h
  · simpa only [contiguityGeometry_target_length] using
      congrArg (fun J => J.targetArc.length) h
  · exact R.map_keep_injective (R.rightSide_offEdge hs H) (R.rightSide_offEdge hs K)
      (congrArg (fun J => J.rightSide) h)
  · exact R.map_keep_injective (R.leftSide_offEdge hs H) (R.leftSide_offEdge hs K)
      (congrArg (fun J => J.leftSide) h)

/-! ## Region families -/

variable {D : RelGenSet G Lambda} {eps : ℕ}

/-- A region candidate avoiding the merged faces, after the merge. -/
noncomputable def regionCandidate
    (a : { a : RegionCandidate D eps Delta // R.first ∉ a.1 ∧ R.second ∉ a.1 }) :
    RegionCandidate D eps R.diagram :=
  ⟨R.faceSet a.val.1, R.contiguityGeometry a.property a.val.2⟩

theorem regionCandidate_weight
    (a : { a : RegionCandidate D eps Delta // R.first ∉ a.1 ∧ R.second ∉ a.1 }) :
    RegionCandidate.weight (R.regionCandidate a) = RegionCandidate.weight a.val :=
  congrArg₂ Nat.add (R.contiguityGeometry_source_length a.property a.val.2)
    (R.contiguityGeometry_target_length a.property a.val.2)

theorem regionCandidate_compatible
    (a b : { a : RegionCandidate D eps Delta // R.first ∉ a.1 ∧ R.second ∉ a.1 }) :
    RegionCandidate.Compatible (R.regionCandidate a) (R.regionCandidate b) ↔
      RegionCandidate.Compatible a.val b.val :=
  R.faceSet_disjoint_iff a.property b.property

theorem regionCandidate_injective :
    Function.Injective (R.regionCandidate :
      { a : RegionCandidate D eps Delta // R.first ∉ a.1 ∧ R.second ∉ a.1 } →
        RegionCandidate D eps R.diagram) := by
  rintro ⟨⟨s, H⟩, hs⟩ ⟨⟨t, K⟩, ht⟩ h
  have hfaces : R.faceSet s = R.faceSet t := congrArg Sigma.fst h
  have hst : s = t := R.faceSet_inj hs ht hfaces
  subst hst
  have hcont : R.contiguityGeometry hs H = R.contiguityGeometry hs K :=
    eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hHK := R.contiguityGeometry_injective hs hcont
  cases hHK
  rfl

/-- The merge embedding of a family avoiding the merged faces. -/
noncomputable def regionFamilyEmbedding (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, R.first ∉ a.1 ∧ R.second ∉ a.1) :
    family ↪ RegionCandidate D eps R.diagram where
  toFun a := R.regionCandidate ⟨a.val, havoid a.val a.property⟩
  inj' a b h := by
    apply Subtype.ext
    exact congrArg
      (fun x : { a : RegionCandidate D eps Delta // R.first ∉ a.1 ∧ R.second ∉ a.1 } => x.val)
      (R.regionCandidate_injective h)

/-- **A family avoiding the merged faces, after the merge.** -/
noncomputable def regionFamily (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, R.first ∉ a.1 ∧ R.second ∉ a.1) :
    Finset (RegionCandidate D eps R.diagram) :=
  family.attach.map (R.regionFamilyEmbedding family havoid)

theorem regionFamily_faces (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, R.first ∉ a.1 ∧ R.second ∉ a.1) {a : RegionCandidate D eps R.diagram}
    (ha : a ∈ R.regionFamily family havoid) : ∃ b ∈ family, a.1 = b.1.image R.kept := by
  obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp ha
  exact ⟨b.val, b.property, rfl⟩

theorem regionFamily_card (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, R.first ∉ a.1 ∧ R.second ∉ a.1) :
    (R.regionFamily family havoid).card = family.card := by
  simp only [regionFamily, Finset.card_map, Finset.card_attach]

theorem regionFamily_weight (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, R.first ∉ a.1 ∧ R.second ∉ a.1) :
    EstimatingSelection.familyWeight RegionCandidate.weight (R.regionFamily family havoid) =
      EstimatingSelection.familyWeight RegionCandidate.weight family := by
  unfold EstimatingSelection.familyWeight regionFamily
  rw [Finset.sum_map]
  trans ∑ a ∈ family.attach, RegionCandidate.weight a.val
  · apply Finset.sum_congr rfl
    intro a _
    exact R.regionCandidate_weight ⟨a.val, havoid a.val a.property⟩
  · exact Finset.sum_attach _ _

theorem regionFamily_pairwise (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, R.first ∉ a.1 ∧ R.second ∉ a.1)
    (hcompat : EstimatingSelection.PairwiseCompatible RegionCandidate.Compatible family) :
    EstimatingSelection.PairwiseCompatible RegionCandidate.Compatible
      (R.regionFamily family havoid) := by
  intro x hx y hy hne
  obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp hy
  apply (R.regionCandidate_compatible ⟨a.val, havoid a.val a.property⟩
    ⟨b.val, havoid b.val b.property⟩).mpr
  apply hcompat a.val a.property b.val b.property
  intro hab
  exact hne (congrArg (R.regionFamilyEmbedding family havoid) (Subtype.ext hab))

/-- No region of a transported family contains the merged face. -/
theorem regionFamily_avoid_merged (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, R.first ∉ a.1 ∧ R.second ∉ a.1) :
    ∀ a ∈ R.regionFamily family havoid, R.merged ∉ a.1 := by
  intro a ha
  obtain ⟨b, hb, hab⟩ := R.regionFamily_faces family havoid ha
  rw [hab]
  exact R.merged_not_mem_faceSet (havoid b hb)

/-- **Every transported region has the target profile of the region it came from.** -/
theorem regionFamily_profile (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, R.first ∉ a.1 ∧ R.second ∉ a.1) {a : RegionCandidate D eps R.diagram}
    (ha : a ∈ R.regionFamily family havoid) :
    ∃ b ∈ family, RegionCandidate.SameTargetProfile a b := by
  obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp ha
  refine ⟨b.val, b.property, And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))⟩
  · exact Option.map_eq_none_iff
  · exact CyclicArc.mapTo_start b.val.2.targetArc R.keep (R.targetDarts_eq b.val.2.target)
  · exact CyclicArc.mapTo_length b.val.2.targetArc R.keep (R.targetDarts_eq b.val.2.target)
  · exact CyclicArc.mapTo_length b.val.2.sourceArc R.keep (R.cellDarts_eq b.val.2.source)

/-! ## Unbound darts -/

theorem mem_cellArcDarts_iff {Xi : DiscDiagram.{u, w, v} W} (a : RegionCandidate D eps Xi)
    (i : Fin Xi.rCellCount) (d : Xi.toCombMap.Dart) :
    d ∈ a.cellArcDarts i ↔ (a.2.source = i ∧ d ∈ a.2.sourceArc.darts) ∨
      (a.2.target = some i ∧ d ∈ a.2.targetArc.darts) := by
  unfold RegionCandidate.cellArcDarts
  rw [Finset.mem_union]
  by_cases hs : a.2.source = i <;> by_cases ht : a.2.target = some i <;> simp [hs, ht]

theorem regionCandidate_source_eq_iff
    (a : { a : RegionCandidate D eps Delta // R.first ∉ a.1 ∧ R.second ∉ a.1 })
    (i : Fin Delta.rCellCount) :
    (R.regionCandidate a).2.source = R.cellMap.indexEquiv i ↔ a.val.2.source = i :=
  R.cellMap.indexEquiv.apply_eq_iff_eq

theorem regionCandidate_target_eq_some_iff
    (a : { a : RegionCandidate D eps Delta // R.first ∉ a.1 ∧ R.second ∉ a.1 })
    (i : Fin Delta.rCellCount) :
    (R.regionCandidate a).2.target = some (R.cellMap.indexEquiv i) ↔ a.val.2.target = some i := by
  change Option.map R.cellMap.indexEquiv a.val.2.target = some (R.cellMap.indexEquiv i) ↔ _
  constructor
  · intro h
    exact Option.map_injective R.cellMap.indexEquiv.injective h
  · intro h
    rw [h]
    rfl

theorem regionCandidate_target_isSome
    (a : { a : RegionCandidate D eps Delta // R.first ∉ a.1 ∧ R.second ∉ a.1 }) :
    (R.regionCandidate a).2.target.isSome = a.val.2.target.isSome :=
  Option.isSome_map

theorem regionCandidate_sourceArc_darts
    (a : { a : RegionCandidate D eps Delta // R.first ∉ a.1 ∧ R.second ∉ a.1 }) :
    (R.regionCandidate a).2.sourceArc.darts = a.val.2.sourceArc.darts.map R.keep :=
  CyclicArc.mapTo_darts _ R.keep _

theorem regionCandidate_targetArc_darts
    (a : { a : RegionCandidate D eps Delta // R.first ∉ a.1 ∧ R.second ∉ a.1 }) :
    (R.regionCandidate a).2.targetArc.darts = a.val.2.targetArc.darts.map R.keep :=
  CyclicArc.mapTo_darts _ R.keep _

theorem mem_cellArcDarts_regionCandidate_iff
    (a : { a : RegionCandidate D eps Delta // R.first ∉ a.1 ∧ R.second ∉ a.1 })
    (i : Fin Delta.rCellCount) (x : R.diagram.toCombMap.Dart) :
    x ∈ (R.regionCandidate a).cellArcDarts (R.cellMap.indexEquiv i) ↔
      R.val x ∈ a.val.cellArcDarts i := by
  rw [mem_cellArcDarts_iff, mem_cellArcDarts_iff, R.regionCandidate_source_eq_iff,
    R.regionCandidate_target_eq_some_iff, R.regionCandidate_sourceArc_darts,
    R.regionCandidate_targetArc_darts,
    R.mem_map_keep_iff (fun d hd => R.cellDarts_offEdge a.val.2.source
      (a.val.2.sourceArc.mem_cycle_of_mem_darts hd)) x,
    R.mem_map_keep_iff (fun d hd => R.targetDarts_offEdge a.val.2.target
      (a.val.2.targetArc.mem_cycle_of_mem_darts hd)) x]

theorem mem_boundDarts_iff (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, R.first ∉ a.1 ∧ R.second ∉ a.1) (interior : Bool)
    (i : Fin Delta.rCellCount) (x : R.diagram.toCombMap.Dart) :
    x ∈ RegionCandidate.boundDarts (R.regionFamily family havoid) interior
        (R.cellMap.indexEquiv i) ↔
      R.val x ∈ RegionCandidate.boundDarts family interior i := by
  unfold RegionCandidate.boundDarts RegionCandidate.ofKind
  simp only [Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨a', ⟨ha', hkind⟩, hd⟩
    obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp ha'
    refine ⟨b.val, ⟨b.property, ?_⟩, ?_⟩
    · rw [← R.regionCandidate_target_isSome ⟨b.val, havoid b.val b.property⟩]
      exact hkind
    · exact (R.mem_cellArcDarts_regionCandidate_iff ⟨b.val, havoid b.val b.property⟩ i x).mp hd
  · rintro ⟨b, ⟨hb, hkind⟩, hd⟩
    refine ⟨R.regionCandidate ⟨b, havoid b hb⟩, ⟨Finset.mem_map.mpr ⟨⟨b, hb⟩,
      Finset.mem_attach _ _, rfl⟩, ?_⟩, ?_⟩
    · rw [R.regionCandidate_target_isSome ⟨b, havoid b hb⟩]
      exact hkind
    · exact (R.mem_cellArcDarts_regionCandidate_iff ⟨b, havoid b hb⟩ i x).mpr hd

/-- **A dart of a relator cell of the merge is unbound exactly when its old dart was.** -/
theorem mem_unboundDarts_iff (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, R.first ∉ a.1 ∧ R.second ∉ a.1) (i : Fin Delta.rCellCount)
    (x : R.diagram.toCombMap.Dart) :
    x ∈ RegionCandidate.unboundDarts (R.regionFamily family havoid) (R.cellMap.indexEquiv i) ↔
      R.val x ∈ RegionCandidate.unboundDarts family i := by
  unfold RegionCandidate.unboundDarts
  simp only [Finset.mem_sdiff, Finset.mem_union, List.mem_toFinset]
  rw [R.cellDarts_eq i, R.mem_map_keep_iff (fun d hd => R.cellDarts_offEdge i hd) x,
    R.mem_boundDarts_iff family havoid false i x, R.mem_boundDarts_iff family havoid true i x]

theorem unboundDarts_offEdge (family : Finset (RegionCandidate D eps Delta))
    (i : Fin Delta.rCellCount) {d : Delta.toCombMap.Dart}
    (hd : d ∈ RegionCandidate.unboundDarts family i) :
    d ≠ R.dart ∧ d ≠ Delta.toCombMap.alpha R.dart := by
  unfold RegionCandidate.unboundDarts at hd
  exact R.cellDarts_offEdge i (List.mem_toFinset.mp (Finset.mem_sdiff.mp hd).1)

/-- **The unbound darts of a relator cell are the old ones, through `keep`.** -/
theorem unboundDarts_eq (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, R.first ∉ a.1 ∧ R.second ∉ a.1) (i : Fin Delta.rCellCount) :
    RegionCandidate.unboundDarts (R.regionFamily family havoid) (R.cellMap.indexEquiv i) =
      (RegionCandidate.unboundDarts family i).image R.keep := by
  ext x
  rw [R.mem_unboundDarts_iff family havoid i x, Finset.mem_image]
  constructor
  · intro hx
    exact ⟨R.val x, hx, R.keep_val x⟩
  · rintro ⟨d, hd, rfl⟩
    rwa [R.val_keep (R.unboundDarts_offEdge family i hd)]

theorem unboundDarts_card (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, R.first ∉ a.1 ∧ R.second ∉ a.1) (i : Fin Delta.rCellCount) :
    (RegionCandidate.unboundDarts (R.regionFamily family havoid) (R.cellMap.indexEquiv i)).card =
      (RegionCandidate.unboundDarts family i).card := by
  rw [R.unboundDarts_eq family havoid i]
  exact Finset.card_image_of_injOn fun d hd e he h =>
    (R.val_keep (R.unboundDarts_offEdge family i (Finset.mem_coe.mp hd))).symm.trans
      ((congrArg R.val h).trans
        (R.val_keep (R.unboundDarts_offEdge family i (Finset.mem_coe.mp he))))

/-- **The total unbound length is unchanged.** -/
theorem sum_unboundDarts_card (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, R.first ∉ a.1 ∧ R.second ∉ a.1) :
    ∑ j : Fin R.diagram.rCellCount,
        (RegionCandidate.unboundDarts (R.regionFamily family havoid) j).card =
      ∑ i : Fin Delta.rCellCount, (RegionCandidate.unboundDarts family i).card := by
  rw [← Equiv.sum_comp R.cellMap.indexEquiv]
  exact Finset.sum_congr rfl fun i _ => R.unboundDarts_card family havoid i

end Transport

/-! ## Section families -/

section Sections

variable {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **A section family across a G-face merge of its diagram.** -/
noncomputable def transportSection (S : RealizedSectionFamily D lambda c eps Delta cuts)
    (R : GFaceMerge S.diagram) (havoid : ∀ b ∈ S.family, R.first ∉ b.1 ∧ R.second ∉ b.1) :
    RealizedSectionFamily D lambda c eps Delta cuts where
  diagram := R.diagram
  equiv := S.equiv.trans R.oEquivalent
  reduced := R.reduced S.reduced
  family := R.regionFamily S.family havoid
  pairwise := R.regionFamily_pairwise S.family havoid S.pairwise
  respects := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := R.regionFamily_profile S.family havoid ha
    exact RegionCandidate.respectsSections_of_sameTargetProfile cuts hab (S.respects b hb)
  nondegenerate := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := R.regionFamily_profile S.family havoid ha
    obtain ⟨hs, ht⟩ := S.nondegenerate b hb
    exact ⟨lt_of_lt_of_eq hs hab.2.2.2.symm, lt_of_lt_of_eq ht hab.2.2.1.symm⟩

theorem transportSection_diagram (S : RealizedSectionFamily D lambda c eps Delta cuts)
    (R : GFaceMerge S.diagram) (havoid : ∀ b ∈ S.family, R.first ∉ b.1 ∧ R.second ∉ b.1) :
    (transportSection S R havoid).diagram = R.diagram :=
  rfl

theorem transportSection_family (S : RealizedSectionFamily D lambda c eps Delta cuts)
    (R : GFaceMerge S.diagram) (havoid : ∀ b ∈ S.family, R.first ∉ b.1 ∧ R.second ∉ b.1) :
    (transportSection S R havoid).family = R.regionFamily S.family havoid :=
  rfl

/-- **The weight is unchanged.** -/
theorem transportSection_weight (S : RealizedSectionFamily D lambda c eps Delta cuts)
    (R : GFaceMerge S.diagram) (havoid : ∀ b ∈ S.family, R.first ∉ b.1 ∧ R.second ∉ b.1) :
    (transportSection S R havoid).weight = S.weight :=
  R.regionFamily_weight S.family havoid

/-- The number of regions is unchanged. -/
theorem transportSection_card (S : RealizedSectionFamily D lambda c eps Delta cuts)
    (R : GFaceMerge S.diagram) (havoid : ∀ b ∈ S.family, R.first ∉ b.1 ∧ R.second ∉ b.1) :
    (transportSection S R havoid).family.card = S.family.card :=
  R.regionFamily_card S.family havoid

/-- Legal labels stay legal. -/
theorem transportSection_labelLegal (S : RealizedSectionFamily D lambda c eps Delta cuts)
    (R : GFaceMerge S.diagram) (havoid : ∀ b ∈ S.family, R.first ∉ b.1 ∧ R.second ∉ b.1)
    (E : RelGenSet G Lambda) (h : S.toRealizedRegionFamily.LabelLegal E) :
    (transportSection S R havoid).toRealizedRegionFamily.LabelLegal E :=
  fun x => R.labelLegal E h x

end Sections

end GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.transportBoundary
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.shelling
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.contiguityGeometry
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.contiguityGeometry_injective
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.regionCandidate_injective
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.regionFamily_card
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.regionFamily_weight
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.regionFamily_pairwise
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.regionFamily_profile
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.regionFamily_avoid_merged
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.unboundDarts_eq
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.sum_unboundDarts_card
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.transportSection
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.transportSection_weight
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.transportSection_labelLegal
