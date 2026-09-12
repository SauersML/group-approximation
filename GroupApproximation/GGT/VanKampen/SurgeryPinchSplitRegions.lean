import GroupApproximation.GGT.VanKampen.SurgeryPinchSplitDiagram
import GroupApproximation.GGT.VanKampen.Estimating.RegionCandidate
import GroupApproximation.GGT.VanKampen.Estimating.CyclicArcMap
import GroupApproximation.Meta.AxiomGuard

/-!
# Contiguity regions across a vertex splitting

The transport half of surgery 3 (`PinchSplit.Input.diagram`).  A face set `s` avoiding both
pinch faces (`Avoids`) survives the split as its image `faceSet s = s.image kept`, and since the
split keeps every dart, every label, and the literal walk of every face off the pinch, each datum
of a contiguity region on `s` transports by the identity on darts:

* its embedded boundary (`transportBoundary`): boundary darts, internal moves and boundary steps
  are the same (`isBoundaryDart_iff`, `internalMove_transport`, `boundaryStep_transport`);
* its shelling (`shelling`), face by face;
* the whole `ContiguityGeometry` (`contiguityGeometry`), with the same arcs, sides and words, hence
  the region candidate (`regionCandidate`), with the same weight.

A compatible family avoiding the pinch faces transports to a compatible family of the split with
the same card and weight (`regionFamily`, `regionFamily_card`, `regionFamily_weight`,
`regionFamily_pairwise`, `regionFamily_faces`).
-/

namespace GroupApproximation.GGT.VanKampen.PinchSplit.Input

open GroupApproximation.GGT.VanKampen.Embedded
open scoped Classical

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W} [DecidableEq Delta.toCombMap.Dart] (I : Input Delta)

/-! ## Face sets -/

/-- A face set avoiding both pinch faces. -/
abbrev Avoids (s : Finset Delta.toCombMap.Face) : Prop := I.leftFace ∉ s ∧ I.rightFace ∉ s

/-- The image of an old face set. -/
noncomputable abbrev faceSet (s : Finset Delta.toCombMap.Face) : Finset I.diagram.toCombMap.Face :=
  s.image I.kept

omit [DecidableEq Delta.toCombMap.Dart] in
theorem off_of_mem {s : Finset Delta.toCombMap.Face} (hs : I.Avoids s) {g : Delta.toCombMap.Face}
    (hg : g ∈ s) : g ≠ I.leftFace ∧ g ≠ I.rightFace :=
  ⟨fun h => hs.1 (h ▸ hg), fun h => hs.2 (h ▸ hg)⟩

theorem kept_mem_faceSet {s : Finset Delta.toCombMap.Face} {g : Delta.toCombMap.Face}
    (hg : g ∈ s) : I.kept g ∈ I.faceSet s :=
  Finset.mem_image.mpr ⟨g, hg, rfl⟩

theorem kept_mem_faceSet_iff {s : Finset Delta.toCombMap.Face} (hs : I.Avoids s)
    {g : Delta.toCombMap.Face} : I.kept g ∈ I.faceSet s ↔ g ∈ s := by
  constructor
  · intro h
    obtain ⟨g', hg', heq⟩ := Finset.mem_image.mp h
    have hoff := I.off_of_mem hs hg'
    rw [← I.kept_inj hoff.1 hoff.2 heq]
    exact hg'
  · exact I.kept_mem_faceSet

theorem merged_not_mem_faceSet {s : Finset Delta.toCombMap.Face} (hs : I.Avoids s) :
    I.merged ∉ I.faceSet s := by
  intro h
  obtain ⟨g, hg, heq⟩ := Finset.mem_image.mp h
  exact I.kept_ne_merged (I.off_of_mem hs hg).1 (I.off_of_mem hs hg).2 heq

/-- **A dart is based in the image of `s` exactly when it was based in `s`.** -/
theorem faceOf_mem_faceSet_iff {s : Finset Delta.toCombMap.Face} (hs : I.Avoids s)
    (d : Delta.toCombMap.Dart) :
    I.diagram.toCombMap.faceOf d ∈ I.faceSet s ↔ Delta.toCombMap.faceOf d ∈ s := by
  rw [I.diagram_faceOf]
  exact I.kept_mem_faceSet_iff hs

theorem faceSet_disjoint_iff {s t : Finset Delta.toCombMap.Face} (_hs : I.Avoids s)
    (ht : I.Avoids t) : Disjoint (I.faceSet s) (I.faceSet t) ↔ Disjoint s t := by
  simp only [Finset.disjoint_left]
  constructor
  · intro h g hgs hgt
    exact h (I.kept_mem_faceSet hgs) (I.kept_mem_faceSet hgt)
  · intro h F hFs hFt
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hFs
    exact h hg ((I.kept_mem_faceSet_iff ht).mp hFt)

theorem faceSet_inj {s t : Finset Delta.toCombMap.Face} (hs : I.Avoids s) (ht : I.Avoids t)
    (h : I.faceSet s = I.faceSet t) : s = t := by
  ext g
  rw [← I.kept_mem_faceSet_iff hs, ← I.kept_mem_faceSet_iff ht, h]

/-! ## Boundaries -/

/-- Face rotation is unchanged at a dart based in an avoiding face set. -/
theorem facePerm_of_mem {s : Finset Delta.toCombMap.Face} (hs : I.Avoids s)
    {d : Delta.toCombMap.Dart} (hd : Delta.toCombMap.faceOf d ∈ s) :
    I.diagram.toCombMap.facePerm d = Delta.toCombMap.facePerm d := by
  have hoff := I.off_of_mem hs hd
  apply facePerm_apply_of_ne Delta.toCombMap I.x I.y
  · intro h
    apply hoff.1
    rw [h]
  · intro h
    apply hoff.2
    rw [h]

theorem isBoundaryDart_iff {s : Finset Delta.toCombMap.Face} (hs : I.Avoids s)
    (d : Delta.toCombMap.Dart) :
    IsBoundaryDart I.diagram (I.faceSet s) d ↔ IsBoundaryDart Delta s d := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(I.faceOf_mem_faceSet_iff hs d).mp h1,
      fun h => h2 ((I.faceOf_mem_faceSet_iff hs (Delta.toCombMap.alpha d)).mpr h)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(I.faceOf_mem_faceSet_iff hs d).mpr h1,
      fun h => h2 ((I.faceOf_mem_faceSet_iff hs (Delta.toCombMap.alpha d)).mp h)⟩

theorem internalMove_transport {s : Finset Delta.toCombMap.Face} (hs : I.Avoids s)
    {d e : Delta.toCombMap.Dart} (h : InternalBoundaryMove Delta s d e) :
    InternalBoundaryMove I.diagram (I.faceSet s) d e := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨(I.faceOf_mem_faceSet_iff hs d).mpr h1,
    (I.faceOf_mem_faceSet_iff hs (Delta.toCombMap.alpha d)).mpr h2, ?_⟩
  subst h3
  exact (I.facePerm_of_mem hs h2).symm

theorem boundaryStep_transport {s : Finset Delta.toCombMap.Face} (hs : I.Avoids s)
    {d e : Delta.toCombMap.Dart} (h : BoundaryStep Delta s d e) :
    BoundaryStep I.diagram (I.faceSet s) d e := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨(I.isBoundaryDart_iff hs d).mpr h1, (I.isBoundaryDart_iff hs e).mpr h2, ?_⟩
  rw [I.facePerm_of_mem hs h1.1]
  exact h3.lift id fun _ _ hm => I.internalMove_transport hs hm

/-- **The boundary of a face set avoiding the pinch, after the split.** -/
noncomputable def transportBoundary {s : Finset Delta.toCombMap.Face} (hs : I.Avoids s)
    (B : FaceSetBoundary Delta s) : FaceSetBoundary I.diagram (I.faceSet s) where
  faces_nonempty := by
    obtain ⟨g, hg⟩ := B.faces_nonempty
    exact ⟨I.kept g, I.kept_mem_faceSet hg⟩
  all_gCells := by
    intro F hF
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hF
    have hoff := I.off_of_mem hs hg
    refine ⟨fun heq => (B.all_gCells g hg).1
      (I.kept_inj hoff.1 hoff.2 (heq.trans I.diagram_outerFace)), ?_⟩
    rw [I.faceWord_kept g hoff.1 hoff.2]
    exact (B.all_gCells g hg).2
  cycle := B.cycle
  cycle_nonempty := B.cycle_nonempty
  cycle_nodup := B.cycle_nodup
  cycle_mem_iff := fun d => (B.cycle_mem_iff d).trans (I.isBoundaryDart_iff hs d).symm
  cycle_chain := B.cycle_chain.imp fun _ _ h => I.boundaryStep_transport hs h
  cycle_closes := I.boundaryStep_transport hs B.cycle_closes

@[simp] theorem transportBoundary_cycle {s : Finset Delta.toCombMap.Face} (hs : I.Avoids s)
    (B : FaceSetBoundary Delta s) : (I.transportBoundary hs B).cycle = B.cycle :=
  rfl

/-! ## Shellings -/

theorem shelling {s : Finset Delta.toCombMap.Face} (hs : I.Avoids s)
    {l : List Delta.toCombMap.Face} {cycle : List Delta.toCombMap.Dart}
    (H : FaceShelling Delta s l cycle) :
    FaceShelling I.diagram (I.faceSet s) (l.map I.kept) cycle := by
  induction H with
  | empty => exact FaceShelling.empty
  | @step l before arc after exposed g hg k hrot rest ih =>
    rw [List.map_cons]
    have hoff := I.off_of_mem hs hg
    refine FaceShelling.step (I.kept g) (I.kept_mem_faceSet hg) k ?_ ih
    change (I.faceBoundary (I.kept g)).darts.rotate k = exposed ++ invDarts Delta arc
    rw [I.faceBoundary_kept_darts g hoff.1 hoff.2]
    exact hrot

/-! ## Carriers -/

theorem cellDarts_eq (i : Fin Delta.rCellCount) :
    cellDarts I.diagram (I.cellMap.indexEquiv i) = (cellDarts Delta i).map id := by
  rw [List.map_id]
  change (I.diagram.faceBoundary (Embedded.cell I.diagram (I.cellMap.indexEquiv i)).face).darts =
    (Delta.faceBoundary (Embedded.cell Delta i).face).darts
  rw [I.cellMap.indexed_cell i]
  change (I.faceBoundary (I.kept (Embedded.cell Delta i).face)).darts = _
  rw [I.faceBoundary_kept_darts _ (I.left_not_cell _ (Embedded.cell_mem Delta i))
    (I.right_not_cell _ (Embedded.cell_mem Delta i))]

theorem outerDarts_eq : outerDarts I.diagram = (outerDarts Delta).map id := by
  rw [List.map_id]
  change (I.faceBoundary (I.kept Delta.outerFace)).darts.reverse.map Delta.toCombMap.alpha =
    (Delta.faceBoundary Delta.outerFace).darts.reverse.map Delta.toCombMap.alpha
  rw [I.faceBoundary_kept_darts _ I.outer_ne_left I.outer_ne_right]

theorem targetDarts_eq (target : Option (Fin Delta.rCellCount)) :
    targetDarts I.diagram (target.map I.cellMap.indexEquiv) = (targetDarts Delta target).map id := by
  cases target with
  | none => exact I.outerDarts_eq
  | some i => exact I.cellDarts_eq i

theorem reverseDarts_mapTo {cycle : List Delta.toCombMap.Dart} (arc : CyclicArc cycle)
    {target : List I.diagram.toCombMap.Dart} (h : target = cycle.map id) :
    CyclicArc.reverseDarts (M := I.diagram.toCombMap) (arc.mapTo id h) =
      CyclicArc.reverseDarts (M := Delta.toCombMap) arc := by
  change (arc.mapTo id h).darts.reverse.map Delta.toCombMap.alpha =
    arc.darts.reverse.map Delta.toCombMap.alpha
  rw [CyclicArc.mapTo_darts, List.map_id]

theorem targetBoundaryDarts_mapTo (target : Option (Fin Delta.rCellCount))
    (arc : CyclicArc (targetDarts Delta target)) :
    targetBoundaryDarts I.diagram (target.map I.cellMap.indexEquiv)
        (arc.mapTo id (I.targetDarts_eq target)) = targetBoundaryDarts Delta target arc := by
  cases target with
  | none => exact (arc.mapTo_darts id _).trans (List.map_id _)
  | some i => exact I.reverseDarts_mapTo arc _

/-! ## Contiguity geometry -/

/-- **A contiguity region avoiding the pinch faces, after the split.** -/
noncomputable def contiguityGeometry {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (hs : I.Avoids s) (H : ContiguityGeometry D eps Delta s) :
    ContiguityGeometry D eps I.diagram (I.faceSet s) where
  boundary := I.transportBoundary hs H.boundary
  source := I.cellMap.indexEquiv H.source
  target := H.target.map I.cellMap.indexEquiv
  sourceArc := H.sourceArc.mapTo id (I.cellDarts_eq H.source)
  targetArc := H.targetArc.mapTo id (I.targetDarts_eq H.target)
  rightSide := H.rightSide
  leftSide := H.leftSide
  boundary_decomposition := by
    change H.boundary.cycle = _
    rw [I.reverseDarts_mapTo, I.targetBoundaryDarts_mapTo]
    exact H.boundary_decomposition
  rightSide_length_le := H.rightSide_length_le
  leftSide_length_le := H.leftSide_length_le
  rightSide_norm_le := H.rightSide_norm_le
  leftSide_norm_le := H.leftSide_norm_le
  pasting := by
    obtain ⟨l, hl⟩ := H.pasting
    exact ⟨l.map I.kept, I.shelling hs hl⟩

theorem contiguityGeometry_source_length {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (hs : I.Avoids s) (H : ContiguityGeometry D eps Delta s) :
    (I.contiguityGeometry hs H).sourceArc.length = H.sourceArc.length :=
  H.sourceArc.mapTo_length id (I.cellDarts_eq H.source)

theorem contiguityGeometry_target_length {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (hs : I.Avoids s) (H : ContiguityGeometry D eps Delta s) :
    (I.contiguityGeometry hs H).targetArc.length = H.targetArc.length :=
  H.targetArc.mapTo_length id (I.targetDarts_eq H.target)

theorem contiguityGeometry_target_start {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (hs : I.Avoids s) (H : ContiguityGeometry D eps Delta s) :
    (I.contiguityGeometry hs H).targetArc.start.val = H.targetArc.start.val :=
  H.targetArc.mapTo_start id (I.targetDarts_eq H.target)

theorem contiguityGeometry_target_eq_none_iff {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (hs : I.Avoids s) (H : ContiguityGeometry D eps Delta s) :
    (I.contiguityGeometry hs H).target = none ↔ H.target = none :=
  Option.map_eq_none_iff

theorem contiguityGeometry_injective {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (hs : I.Avoids s) :
    Function.Injective (I.contiguityGeometry (D := D) (eps := eps) hs) := by
  intro H K h
  apply ContiguityGeometry.eq_of_data
  · exact congrArg (fun J => J.boundary.cycle) h
  · exact I.cellMap.indexEquiv.injective (congrArg (fun J => J.source) h)
  · exact (Equiv.optionCongr I.cellMap.indexEquiv).injective (congrArg (fun J => J.target) h)
  · simpa only [contiguityGeometry, CyclicArc.mapTo_start] using
      congrArg (fun J => J.sourceArc.start.val) h
  · simpa only [contiguityGeometry_source_length] using
      congrArg (fun J => J.sourceArc.length) h
  · simpa only [contiguityGeometry, CyclicArc.mapTo_start] using
      congrArg (fun J => J.targetArc.start.val) h
  · simpa only [contiguityGeometry_target_length] using
      congrArg (fun J => J.targetArc.length) h
  · exact congrArg (fun J => J.rightSide) h
  · exact congrArg (fun J => J.leftSide) h

/-! ## Region families -/

variable {D : RelGenSet G Lambda} {eps : ℕ}

/-- A region candidate avoiding the pinch faces, after the split. -/
noncomputable def regionCandidate (a : { a : RegionCandidate D eps Delta // I.Avoids a.1 }) :
    RegionCandidate D eps I.diagram :=
  ⟨I.faceSet a.val.1, I.contiguityGeometry a.property a.val.2⟩

theorem regionCandidate_weight (a : { a : RegionCandidate D eps Delta // I.Avoids a.1 }) :
    RegionCandidate.weight (I.regionCandidate a) = RegionCandidate.weight a.val :=
  congrArg₂ Nat.add (I.contiguityGeometry_source_length a.property a.val.2)
    (I.contiguityGeometry_target_length a.property a.val.2)

theorem regionCandidate_compatible (a b : { a : RegionCandidate D eps Delta // I.Avoids a.1 }) :
    RegionCandidate.Compatible (I.regionCandidate a) (I.regionCandidate b) ↔
      RegionCandidate.Compatible a.val b.val :=
  I.faceSet_disjoint_iff a.property b.property

theorem regionCandidate_injective :
    Function.Injective (I.regionCandidate :
      { a : RegionCandidate D eps Delta // I.Avoids a.1 } → RegionCandidate D eps I.diagram) := by
  rintro ⟨⟨s, H⟩, hs⟩ ⟨⟨t, K⟩, ht⟩ h
  have hfaces : I.faceSet s = I.faceSet t := congrArg Sigma.fst h
  have hst : s = t := I.faceSet_inj hs ht hfaces
  subst hst
  have hcont : I.contiguityGeometry hs H = I.contiguityGeometry hs K :=
    eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hHK := I.contiguityGeometry_injective hs hcont
  cases hHK
  rfl

/-- The split embedding of a family avoiding the pinch faces. -/
noncomputable def regionFamilyEmbedding (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, I.Avoids a.1) : family ↪ RegionCandidate D eps I.diagram where
  toFun a := I.regionCandidate ⟨a.val, havoid a.val a.property⟩
  inj' a b h := by
    apply Subtype.ext
    exact congrArg (fun x : { a : RegionCandidate D eps Delta // I.Avoids a.1 } => x.val)
      (I.regionCandidate_injective h)

/-- **A family avoiding the pinch faces, after the split.** -/
noncomputable def regionFamily (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, I.Avoids a.1) : Finset (RegionCandidate D eps I.diagram) :=
  family.attach.map (I.regionFamilyEmbedding family havoid)

theorem regionFamily_faces (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, I.Avoids a.1) {a : RegionCandidate D eps I.diagram}
    (ha : a ∈ I.regionFamily family havoid) : ∃ b ∈ family, a.1 = b.1.image I.kept := by
  obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp ha
  exact ⟨b.val, b.property, rfl⟩

theorem regionFamily_card (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, I.Avoids a.1) : (I.regionFamily family havoid).card = family.card := by
  simp only [regionFamily, Finset.card_map, Finset.card_attach]

theorem regionFamily_weight (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, I.Avoids a.1) :
    EstimatingSelection.familyWeight RegionCandidate.weight (I.regionFamily family havoid) =
      EstimatingSelection.familyWeight RegionCandidate.weight family := by
  unfold EstimatingSelection.familyWeight regionFamily
  rw [Finset.sum_map]
  trans ∑ a ∈ family.attach, RegionCandidate.weight a.val
  · apply Finset.sum_congr rfl
    intro a _
    exact I.regionCandidate_weight ⟨a.val, havoid a.val a.property⟩
  · exact Finset.sum_attach _ _

theorem regionFamily_pairwise (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, I.Avoids a.1)
    (hcompat : EstimatingSelection.PairwiseCompatible RegionCandidate.Compatible family) :
    EstimatingSelection.PairwiseCompatible RegionCandidate.Compatible
      (I.regionFamily family havoid) := by
  intro x hx y hy hne
  obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp hy
  apply (I.regionCandidate_compatible ⟨a.val, havoid a.val a.property⟩
    ⟨b.val, havoid b.val b.property⟩).mpr
  apply hcompat a.val a.property b.val b.property
  intro hab
  exact hne (congrArg (I.regionFamilyEmbedding family havoid) (Subtype.ext hab))

/-- No region of a transported family contains the merged face. -/
theorem regionFamily_avoid_merged (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, I.Avoids a.1) : ∀ a ∈ I.regionFamily family havoid, I.merged ∉ a.1 := by
  intro a ha
  obtain ⟨b, hb, hab⟩ := I.regionFamily_faces family havoid ha
  rw [hab]
  exact I.merged_not_mem_faceSet (havoid b hb)

end GroupApproximation.GGT.VanKampen.PinchSplit.Input

#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.transportBoundary
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.shelling
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.contiguityGeometry
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.regionCandidate_injective
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.regionFamily_card
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.regionFamily_weight
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.regionFamily_pairwise
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.regionFamily_faces
