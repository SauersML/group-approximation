import GroupApproximation.GGT.VanKampen.SurgeryInnerCollapseDarts
import GroupApproximation.GGT.VanKampen.Estimating.RegionCandidate
import GroupApproximation.GGT.VanKampen.FaceShelling
import GroupApproximation.Meta.AxiomGuard

/-!
# Contiguity regions avoiding a collapsed G-region

The second half of the transport through `InnerGRegion.diagram`.  A face set `s`
disjoint from the collapsed faces survives the collapse as `R.faceSet s`, and every
datum of a contiguity region on `s` transports with it:

* its embedded boundary (`transportBoundary`), since the boundary darts of `s` are
  retained, face rotation outside the region is unchanged, and the internal moves of
  `s` never touch the region (`boundaryStep_keep`);
* its shelling (`shelling`), face by face;
* the whole `ContiguityGeometry` (`contiguityGeometry`), with the same arc lengths and
  side words, and hence the region candidate (`regionCandidate`), with the same weight.

A compatible family of region candidates avoiding the collapsed faces transports to a
compatible family of the collapse with the same card and weight (`regionFamily`,
`regionFamily_card`, `regionFamily_weight`, `regionFamily_pairwise`).  This is what
keeps a distinguished family alive across the merge surgery of Osin's Appendix
(arXiv:math/0411039v3, Lemma 9.4 Case 1 and the merges of Lemma 9.7(a)): the family
survives, and the merged face can then carry a new region
(`Estimating/SingletonFaceRegion.lean`).
-/

namespace GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion

open MapCollapse
open GroupApproximation.GGT.VanKampen.Embedded

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}
  (R : InnerGRegion Delta)

/-! ## Face sets -/

theorem face_mem_faceSet {s : Finset Delta.toCombMap.Face} {g : Delta.toCombMap.Face}
    (hg : g ∈ s) : R.face g ∈ R.faceSet s :=
  R.mem_faceSet.mpr ⟨g, hg, rfl⟩

theorem mem_faceSet_iff {s : Finset Delta.toCombMap.Face} (hs : Disjoint s R.faces)
    {F : R.diagram.toCombMap.Face} :
    F ∈ R.faceSet s ↔ ∃ g, ∃ hg : g ∈ s, F = R.kept g (Finset.disjoint_left.mp hs hg) := by
  rw [R.mem_faceSet]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, R.face_of_not_mem _⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, R.face_of_not_mem _⟩

theorem faceSet_disjoint_iff {s t : Finset Delta.toCombMap.Face}
    (hs : Disjoint s R.faces) (ht : Disjoint t R.faces) :
    Disjoint (R.faceSet s) (R.faceSet t) ↔ Disjoint s t := by
  simp only [Finset.disjoint_left]
  constructor
  · intro h g hgs hgt
    exact h (R.face_mem_faceSet hgs) (R.face_mem_faceSet hgt)
  · intro h F hFs hFt
    obtain ⟨g, hg, rfl⟩ := (R.mem_faceSet_iff hs).mp hFs
    obtain ⟨g', hg', hgg'⟩ := (R.mem_faceSet_iff ht).mp hFt
    have hgg := R.kept_inj hgg'
    subst hgg
    exact h hg hg'

theorem faceSet_inj {s t : Finset Delta.toCombMap.Face}
    (hs : Disjoint s R.faces) (ht : Disjoint t R.faces)
    (h : R.faceSet s = R.faceSet t) : s = t := by
  ext g
  by_cases hg : g ∈ R.faces
  · exact ⟨fun hgs => (Finset.disjoint_left.mp hs hgs hg).elim,
      fun hgt => (Finset.disjoint_left.mp ht hgt hg).elim⟩
  · rw [← R.kept_mem_faceSet_iff hs hg, ← R.kept_mem_faceSet_iff ht hg, h]

theorem faceWord_kept (g : Delta.toCombMap.Face) (hg : g ∉ R.faces) :
    R.diagram.faceWord (R.kept g hg) = Delta.faceWord g :=
  R.keptFace_word g hg

theorem faceBoundary_kept_darts (g : Delta.toCombMap.Face) (hg : g ∉ R.faces) :
    (R.diagram.faceBoundary (R.kept g hg)).darts = (Delta.faceBoundary g).darts.map R.keep := by
  apply List.map_injective_iff.mpr R.val_injective
  rw [R.map_keep_val fun d hd => R.not_internal_of_faceOf_not_mem
    (by rw [((Delta.faceBoundary g).mem_iff d).mp hd]; exact hg)]
  exact R.faceBoundary_kept_map_val g hg

/-! ## Boundaries -/

theorem not_internal_of_boundaryDart {s : Finset Delta.toCombMap.Face}
    (hs : Disjoint s R.faces) {d : Delta.toCombMap.Dart}
    (h : Embedded.IsBoundaryDart Delta s d) : ¬ InternalDart Delta.toCombMap R.faces d :=
  R.not_internal_of_faceOf_not_mem (Finset.disjoint_left.mp hs h.1)

theorem isBoundaryDart_keep_iff {s : Finset Delta.toCombMap.Face} (hs : Disjoint s R.faces)
    {d : Delta.toCombMap.Dart} (hd : ¬ InternalDart Delta.toCombMap R.faces d) :
    Embedded.IsBoundaryDart R.diagram (R.faceSet s) (R.keep d) ↔
      Embedded.IsBoundaryDart Delta s d := by
  simp only [Embedded.IsBoundaryDart, R.alpha_keep hd, R.faceOf_keep_mem_faceSet_iff hs hd,
    R.faceOf_keep_mem_faceSet_iff hs (R.not_internal_alpha hd)]

theorem internalMove_keep {s : Finset Delta.toCombMap.Face} (hs : Disjoint s R.faces)
    {d e : Delta.toCombMap.Dart} (h : InternalBoundaryMove Delta s d e) :
    InternalBoundaryMove R.diagram (R.faceSet s) (R.keep d) (R.keep e) := by
  have hdR := Finset.disjoint_left.mp hs h.1
  have haR := Finset.disjoint_left.mp hs h.2.1
  have hd := R.not_internal_of_faceOf_not_mem hdR
  have ha := R.not_internal_of_faceOf_not_mem haR
  refine ⟨(R.faceOf_keep_mem_faceSet_iff hs hd).mpr h.1, ?_, ?_⟩
  · rw [R.alpha_keep hd]
    exact (R.faceOf_keep_mem_faceSet_iff hs ha).mpr h.2.1
  · rw [R.alpha_keep hd, R.facePerm_keep haR, h.2.2]

theorem boundaryStep_keep {s : Finset Delta.toCombMap.Face} (hs : Disjoint s R.faces)
    {d e : Delta.toCombMap.Dart} (h : BoundaryStep Delta s d e) :
    BoundaryStep R.diagram (R.faceSet s) (R.keep d) (R.keep e) := by
  have hd := R.not_internal_of_boundaryDart hs h.1
  have he := R.not_internal_of_boundaryDart hs h.2.1
  refine ⟨(R.isBoundaryDart_keep_iff hs hd).mpr h.1,
    (R.isBoundaryDart_keep_iff hs he).mpr h.2.1, ?_⟩
  rw [R.facePerm_keep (Finset.disjoint_left.mp hs h.1.1)]
  exact h.2.2.lift R.keep (fun _ _ hm => R.internalMove_keep hs hm)

/-- **The boundary of a face set avoiding the region, after the collapse.** -/
noncomputable def transportBoundary {s : Finset Delta.toCombMap.Face}
    (hs : Disjoint s R.faces) (B : FaceSetBoundary Delta s) :
    FaceSetBoundary R.diagram (R.faceSet s) where
  faces_nonempty := by
    obtain ⟨g, hg⟩ := B.faces_nonempty
    exact ⟨_, R.face_mem_faceSet hg⟩
  all_gCells := by
    intro F hF
    obtain ⟨g, hg, rfl⟩ := (R.mem_faceSet_iff hs).mp hF
    refine ⟨fun heq => (B.all_gCells g hg).1 (R.kept_inj (heq.trans R.outerFace_eq)), ?_⟩
    rw [R.faceWord_kept]
    exact (B.all_gCells g hg).2
  cycle := B.cycle.map R.keep
  cycle_nonempty := fun h => B.cycle_nonempty (List.map_eq_nil_iff.mp h)
  cycle_nodup := R.nodup_map_keep
    (fun d hd => R.not_internal_of_boundaryDart hs ((B.cycle_mem_iff d).mp hd)) B.cycle_nodup
  cycle_mem_iff := by
    intro x
    constructor
    · intro hx
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
      have hb := (B.cycle_mem_iff d).mp hd
      exact (R.isBoundaryDart_keep_iff hs (R.not_internal_of_boundaryDart hs hb)).mpr hb
    · intro hx
      have hkeep : R.keep (R.val x) = x := R.keep_val x
      rw [← hkeep] at hx
      have hb := (R.isBoundaryDart_keep_iff hs (R.val_not_internal x)).mp hx
      exact List.mem_map.mpr ⟨R.val x, (B.cycle_mem_iff _).mpr hb, hkeep⟩
  cycle_chain := by
    rw [List.isChain_map]
    exact B.cycle_chain.imp fun _ _ h => R.boundaryStep_keep hs h
  cycle_closes := by
    rw [List.getLast_map, List.head_map]
    exact R.boundaryStep_keep hs B.cycle_closes

@[simp] theorem transportBoundary_cycle {s : Finset Delta.toCombMap.Face}
    (hs : Disjoint s R.faces) (B : FaceSetBoundary Delta s) :
    (R.transportBoundary hs B).cycle = B.cycle.map R.keep :=
  rfl

/-! ## Shellings -/

theorem shelling {s : Finset Delta.toCombMap.Face} (hs : Disjoint s R.faces)
    {l : List Delta.toCombMap.Face} {cycle : List Delta.toCombMap.Dart}
    (H : FaceShelling Delta s l cycle) :
    FaceShelling R.diagram (R.faceSet s) (l.map R.face) (cycle.map R.keep) := by
  induction H with
  | empty => exact FaceShelling.empty
  | @step l before arc after exposed g hg k hrot rest ih =>
    simp only [List.map_cons, List.map_append] at ih ⊢
    have hgR : g ∉ R.faces := Finset.disjoint_left.mp hs hg
    have harc : ∀ d ∈ arc, ¬ InternalDart Delta.toCombMap R.faces d := by
      intro d hd
      apply R.not_internal_of_faceOf_alpha_not_mem
      have hmem : Delta.toCombMap.alpha d ∈ (Delta.faceBoundary g).darts.rotate k := by
        rw [hrot]
        exact List.mem_append_right _ (List.mem_map.mpr ⟨d, List.mem_reverse.mpr hd, rfl⟩)
      rw [((Delta.faceBoundary g).mem_iff _).mp (List.mem_rotate.mp hmem)]
      exact hgR
    refine FaceShelling.step (arc := arc.map R.keep) (R.face g) (R.face_mem_faceSet hg) k ?_ ih
    rw [R.face_of_not_mem hgR, R.faceBoundary_kept_darts g hgR, ← List.map_rotate,
      hrot, List.map_append, R.invDarts_map harc]

/-! ## Contiguity geometry -/

theorem rightSide_not_internal {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (hs : Disjoint s R.faces)
    (H : ContiguityGeometry D eps Delta s) :
    ∀ d ∈ H.rightSide, ¬ InternalDart Delta.toCombMap R.faces d := fun d hd =>
  R.not_internal_of_boundaryDart hs ((H.boundary.cycle_mem_iff d).mp (by
    rw [H.boundary_decomposition]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hd))))

theorem leftSide_not_internal {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (hs : Disjoint s R.faces)
    (H : ContiguityGeometry D eps Delta s) :
    ∀ d ∈ H.leftSide, ¬ InternalDart Delta.toCombMap R.faces d := fun d hd =>
  R.not_internal_of_boundaryDart hs ((H.boundary.cycle_mem_iff d).mp (by
    rw [H.boundary_decomposition]
    exact List.mem_append_right _ hd))

/-- **A contiguity region avoiding the collapsed faces, after the collapse.** -/
noncomputable def contiguityGeometry {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (hs : Disjoint s R.faces)
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
    rw [R.reverseDarts_mapTo (fun d hd => R.cellDarts_not_internal H.source hd),
      R.targetBoundaryDarts_map]
    exact (congrArg (List.map R.keep) H.boundary_decomposition).trans
      (by simp only [List.map_append])
  rightSide_length_le := by simpa only [List.length_map] using H.rightSide_length_le
  leftSide_length_le := by simpa only [List.length_map] using H.leftSide_length_le
  rightSide_norm_le := by
    rw [R.dartWord_map (R.rightSide_not_internal hs H)]
    exact H.rightSide_norm_le
  leftSide_norm_le := by
    rw [R.dartWord_map (R.leftSide_not_internal hs H)]
    exact H.leftSide_norm_le
  pasting := by
    obtain ⟨l, hl⟩ := H.pasting
    exact ⟨l.map R.face, R.shelling hs hl⟩

theorem contiguityGeometry_source_length {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (hs : Disjoint s R.faces)
    (H : ContiguityGeometry D eps Delta s) :
    (R.contiguityGeometry hs H).sourceArc.length = H.sourceArc.length :=
  H.sourceArc.mapTo_length R.keep (R.cellDarts_eq H.source)

theorem contiguityGeometry_target_length {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (hs : Disjoint s R.faces)
    (H : ContiguityGeometry D eps Delta s) :
    (R.contiguityGeometry hs H).targetArc.length = H.targetArc.length :=
  H.targetArc.mapTo_length R.keep (R.targetDarts_eq H.target)

theorem contiguityGeometry_injective {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (hs : Disjoint s R.faces) :
    Function.Injective (R.contiguityGeometry (D := D) (eps := eps) hs) := by
  intro H K h
  apply ContiguityGeometry.eq_of_data
  · exact R.map_keep_injective
      (fun d hd => R.not_internal_of_boundaryDart hs ((H.boundary.cycle_mem_iff d).mp hd))
      (fun d hd => R.not_internal_of_boundaryDart hs ((K.boundary.cycle_mem_iff d).mp hd))
      (congrArg (fun J => J.boundary.cycle) h)
  · exact R.cellMap.indexEquiv.injective (congrArg (fun J => J.source) h)
  · exact (Equiv.optionCongr R.cellMap.indexEquiv).injective (congrArg (fun J => J.target) h)
  · simpa only [contiguityGeometry, CyclicArc.mapTo_start] using
      congrArg (fun J => J.sourceArc.start.val) h
  · simpa only [contiguityGeometry_source_length] using
      congrArg (fun J => J.sourceArc.length) h
  · simpa only [contiguityGeometry, CyclicArc.mapTo_start] using
      congrArg (fun J => J.targetArc.start.val) h
  · simpa only [contiguityGeometry_target_length] using
      congrArg (fun J => J.targetArc.length) h
  · exact R.map_keep_injective (R.rightSide_not_internal hs H) (R.rightSide_not_internal hs K)
      (congrArg (fun J => J.rightSide) h)
  · exact R.map_keep_injective (R.leftSide_not_internal hs H) (R.leftSide_not_internal hs K)
      (congrArg (fun J => J.leftSide) h)

/-! ## Region families -/

variable {D : RelGenSet G Lambda} {eps : ℕ}

/-- A region candidate avoiding the collapsed faces, after the collapse. -/
noncomputable def regionCandidate
    (a : { a : RegionCandidate D eps Delta // Disjoint a.1 R.faces }) :
    RegionCandidate D eps R.diagram :=
  ⟨R.faceSet a.val.1, R.contiguityGeometry a.property a.val.2⟩

theorem regionCandidate_weight
    (a : { a : RegionCandidate D eps Delta // Disjoint a.1 R.faces }) :
    RegionCandidate.weight (R.regionCandidate a) = RegionCandidate.weight a.val :=
  congrArg₂ Nat.add (R.contiguityGeometry_source_length a.property a.val.2)
    (R.contiguityGeometry_target_length a.property a.val.2)

theorem regionCandidate_compatible
    (a b : { a : RegionCandidate D eps Delta // Disjoint a.1 R.faces }) :
    RegionCandidate.Compatible (R.regionCandidate a) (R.regionCandidate b) ↔
      RegionCandidate.Compatible a.val b.val :=
  R.faceSet_disjoint_iff a.property b.property

theorem regionCandidate_injective :
    Function.Injective (R.regionCandidate :
      { a : RegionCandidate D eps Delta // Disjoint a.1 R.faces } →
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

/-- The collapse embedding of a family avoiding the collapsed faces. -/
noncomputable def regionFamilyEmbedding (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, Disjoint a.1 R.faces) :
    family ↪ RegionCandidate D eps R.diagram where
  toFun a := R.regionCandidate ⟨a.val, havoid a.val a.property⟩
  inj' a b h := by
    apply Subtype.ext
    exact congrArg (fun x : { a : RegionCandidate D eps Delta // Disjoint a.1 R.faces } => x.val)
      (R.regionCandidate_injective h)

/-- **A family avoiding the collapsed faces, after the collapse.** -/
noncomputable def regionFamily (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, Disjoint a.1 R.faces) : Finset (RegionCandidate D eps R.diagram) :=
  family.attach.map (R.regionFamilyEmbedding family havoid)

theorem regionFamily_faces (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, Disjoint a.1 R.faces) {a : RegionCandidate D eps R.diagram}
    (ha : a ∈ R.regionFamily family havoid) :
    ∃ b ∈ family, a.1 = R.faceSet b.1 := by
  obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp ha
  exact ⟨b.val, b.property, rfl⟩

theorem regionFamily_card (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, Disjoint a.1 R.faces) :
    (R.regionFamily family havoid).card = family.card := by
  simp only [regionFamily, Finset.card_map, Finset.card_attach]

theorem regionFamily_weight (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, Disjoint a.1 R.faces) :
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
    (havoid : ∀ a ∈ family, Disjoint a.1 R.faces)
    (hcompat : EstimatingSelection.PairwiseCompatible RegionCandidate.Compatible family) :
    EstimatingSelection.PairwiseCompatible RegionCandidate.Compatible
      (R.regionFamily family havoid) := by
  intro x hx y hy hne
  obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp hy
  apply (R.regionCandidate_compatible
    ⟨a.val, havoid a.val a.property⟩ ⟨b.val, havoid b.val b.property⟩).mpr
  apply hcompat a.val a.property b.val b.property
  intro hab
  exact hne (congrArg (R.regionFamilyEmbedding family havoid) (Subtype.ext hab))

end GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.transportBoundary
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.shelling
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.contiguityGeometry
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.regionCandidate_injective
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.regionFamily_card
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.regionFamily_weight
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.regionFamily_pairwise
