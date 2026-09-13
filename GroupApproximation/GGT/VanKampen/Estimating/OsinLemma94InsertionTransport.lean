import GroupApproximation.GGT.VanKampen.GFaceSplitCorners
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundMerged
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PlanarPieces
import GroupApproximation.Meta.AxiomGuard

/-!
# Distinguished section families across a connector insertion

Case 2 of Osin's Lemma 9.4 (arXiv:math/0411039v3, §9) inserts a connector word across a G-face
that no selected region contains, merges across an edge next to it and deletes the rest of the
cutting path as spikes.  This file carries the optimal family across the first step.

* `DiscEmbeddingAway.unboundDarts_regionFamily`: the unbound darts of a relator cell of the new
  diagram are the old ones, through the dart embedding, so the unbound sum does not change
  (`DiscEmbeddingAway.sum_unboundDarts_regionFamily_card`).
* `GFaceWordInsertion.SplitOutput.dartCount_le_add_two_mul`: every dart of a split insertion is a
  retained old dart, a dart of the inserted path or the reverse of one, because every face is a
  retained old face or one of the two sides.  So at most `2 * word.length` darts are added.
* `GloballyDistinguishedSectionFamily.insertionTransport`: a globally distinguished section family
  across a split insertion between two corners of a G-face that no selected region contains.  The
  class the family is maximal in, the section families over diagrams O-equivalent to `Delta`, does
  not change, so maximal weight and minimal card carry over.  The number of regions and the
  unbound sum are unchanged, no region contains either side, and every region has the target
  profile of an old region.
-/

namespace GroupApproximation.GGT.VanKampen

open Embedded GFaceWordInsertion

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

namespace DiscEmbeddingAway

variable {D : RelGenSet G Lambda} {eps : ℕ}
  {Delta Xi : DiscDiagram.{u, w, v} W} {f : Delta.toCombMap.Face}
  (E : DiscEmbeddingAway Delta Xi f) (C : Surgery.OrderedRCellMap Delta Xi E.faces)
  (hcells : ∀ cell ∈ Delta.relatorCells, cell.face ≠ f) (hf : f ≠ Delta.outerFace)

theorem darts_mem_map_iff (l : List Delta.toCombMap.Dart) (d : Delta.toCombMap.Dart) :
    E.darts d ∈ l.map E.darts ↔ d ∈ l := by
  constructor
  · intro h
    obtain ⟨e, he, hed⟩ := List.mem_map.mp h
    rwa [E.darts.injective hed] at he
  · exact fun h => List.mem_map_of_mem h

theorem regionCandidate_source_eq_iff (a : { a : RegionCandidate D eps Delta // f ∉ a.1 })
    (i : Fin Delta.rCellCount) :
    (E.regionCandidate C hcells hf a).2.source = C.indexEquiv i ↔ a.val.2.source = i :=
  C.indexEquiv.apply_eq_iff_eq

theorem regionCandidate_target_eq_some_iff
    (a : { a : RegionCandidate D eps Delta // f ∉ a.1 }) (i : Fin Delta.rCellCount) :
    (E.regionCandidate C hcells hf a).2.target = some (C.indexEquiv i) ↔
      a.val.2.target = some i := by
  change Option.map C.indexEquiv a.val.2.target = some (C.indexEquiv i) ↔ _
  constructor
  · intro h
    exact Option.map_injective C.indexEquiv.injective h
  · intro h
    rw [h]
    rfl

theorem regionCandidate_target_isSome (a : { a : RegionCandidate D eps Delta // f ∉ a.1 }) :
    (E.regionCandidate C hcells hf a).2.target.isSome = a.val.2.target.isSome :=
  Option.isSome_map

theorem regionCandidate_sourceArc_darts (a : { a : RegionCandidate D eps Delta // f ∉ a.1 }) :
    (E.regionCandidate C hcells hf a).2.sourceArc.darts = a.val.2.sourceArc.darts.map E.darts :=
  CyclicArc.mapTo_darts a.val.2.sourceArc E.darts (E.cellDarts_eq C hcells a.val.2.source)

theorem regionCandidate_targetArc_darts (a : { a : RegionCandidate D eps Delta // f ∉ a.1 }) :
    (E.regionCandidate C hcells hf a).2.targetArc.darts = a.val.2.targetArc.darts.map E.darts :=
  CyclicArc.mapTo_darts a.val.2.targetArc E.darts (E.targetDarts_eq C hcells hf a.val.2.target)

/-- A retained dart lies on an arc of a transported region at a transported cell exactly when
the old dart lies on the arc of the old region at the old cell. -/
theorem darts_mem_cellArcDarts_iff (a : { a : RegionCandidate D eps Delta // f ∉ a.1 })
    (i : Fin Delta.rCellCount) (d : Delta.toCombMap.Dart) :
    E.darts d ∈ (E.regionCandidate C hcells hf a).cellArcDarts (C.indexEquiv i) ↔
      d ∈ a.val.cellArcDarts i := by
  rw [Surgery.GFaceMerge.mem_cellArcDarts_iff, Surgery.GFaceMerge.mem_cellArcDarts_iff,
    E.regionCandidate_source_eq_iff C hcells hf, E.regionCandidate_target_eq_some_iff C hcells hf,
    E.regionCandidate_sourceArc_darts C hcells hf, E.regionCandidate_targetArc_darts C hcells hf,
    E.darts_mem_map_iff, E.darts_mem_map_iff]

/-- A retained dart is used by a transported region of either kind exactly when the old dart
was used by the old region. -/
theorem darts_mem_boundDarts_regionFamily_iff (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1) (interior : Bool) (i : Fin Delta.rCellCount)
    (d : Delta.toCombMap.Dart) :
    E.darts d ∈ RegionCandidate.boundDarts (E.regionFamily C hcells hf family havoid) interior
        (C.indexEquiv i) ↔
      d ∈ RegionCandidate.boundDarts family interior i := by
  rw [Surgery.GFaceMerge.mem_boundDarts_iff, Surgery.GFaceMerge.mem_boundDarts_iff]
  constructor
  · rintro ⟨a', ha', hkind, hd⟩
    obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp ha'
    exact ⟨b.val, b.property,
      (E.regionCandidate_target_isSome C hcells hf ⟨b.val, havoid b.val b.property⟩).symm.trans
        hkind,
      (E.darts_mem_cellArcDarts_iff C hcells hf ⟨b.val, havoid b.val b.property⟩ i d).mp hd⟩
  · rintro ⟨b, hb, hkind, hd⟩
    exact ⟨E.regionCandidate C hcells hf ⟨b, havoid b hb⟩,
      Finset.mem_map.mpr ⟨⟨b, hb⟩, Finset.mem_attach _ _, rfl⟩,
      (E.regionCandidate_target_isSome C hcells hf ⟨b, havoid b hb⟩).trans hkind,
      (E.darts_mem_cellArcDarts_iff C hcells hf ⟨b, havoid b hb⟩ i d).mpr hd⟩

/-- **The unbound darts of a relator cell are the old ones, through the dart embedding.** -/
theorem unboundDarts_regionFamily (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1) (i : Fin Delta.rCellCount) :
    RegionCandidate.unboundDarts (E.regionFamily C hcells hf family havoid) (C.indexEquiv i) =
      (RegionCandidate.unboundDarts family i).map E.darts := by
  ext x
  rw [Surgery.GFaceMerge.mem_unboundDarts_iff, E.cellDarts_eq C hcells i, Finset.mem_map]
  constructor
  · rintro ⟨hx, hnot⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
    refine ⟨d, (Surgery.GFaceMerge.mem_unboundDarts_iff family i d).mpr ⟨hd, ?_⟩, rfl⟩
    rwa [E.darts_mem_boundDarts_regionFamily_iff C hcells hf family havoid false i d,
      E.darts_mem_boundDarts_regionFamily_iff C hcells hf family havoid true i d] at hnot
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨hd, hnot⟩ := (Surgery.GFaceMerge.mem_unboundDarts_iff family i d).mp hd
    refine ⟨List.mem_map_of_mem hd, ?_⟩
    rwa [E.darts_mem_boundDarts_regionFamily_iff C hcells hf family havoid false i d,
      E.darts_mem_boundDarts_regionFamily_iff C hcells hf family havoid true i d]

theorem unboundDarts_regionFamily_card (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1) (i : Fin Delta.rCellCount) :
    (RegionCandidate.unboundDarts (E.regionFamily C hcells hf family havoid)
        (C.indexEquiv i)).card =
      (RegionCandidate.unboundDarts family i).card := by
  rw [E.unboundDarts_regionFamily C hcells hf family havoid i, Finset.card_map]

/-- **The total number of unbound darts is unchanged.** -/
theorem sum_unboundDarts_regionFamily_card (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1) :
    ∑ j : Fin Xi.rCellCount,
        (RegionCandidate.unboundDarts (E.regionFamily C hcells hf family havoid) j).card =
      ∑ i : Fin Delta.rCellCount, (RegionCandidate.unboundDarts family i).card := by
  rw [← Equiv.sum_comp C.indexEquiv]
  exact Finset.sum_congr rfl fun i _ =>
    E.unboundDarts_regionFamily_card C hcells hf family havoid i

end DiscEmbeddingAway

namespace GFaceWordInsertion.SplitOutput

variable {D : RelGenSet G Lambda} {Delta : DiscDiagram.{u, w, v} W} {f : Delta.toCombMap.Face}
  {k : Fin (Delta.faceBoundary f).darts.length} {word : List (RelLetter G Lambda)}
  (R : SplitOutput D Delta f k word)

/-- Every face of a split insertion is a retained old face other than `f`, the prefix side or
the suffix side: these are `F + 1` distinct faces, and the insertion has `F + 1` faces. -/
theorem faceOf_retained_or_sides (x : R.diagram.toCombMap.Dart) :
    (∃ g, g ≠ f ∧ R.embedding.faces g = R.diagram.toCombMap.faceOf x) ∨
      R.diagram.toCombMap.faceOf x = R.prefixSide ∨
        R.diagram.toCombMap.faceOf x = R.suffixSide := by
  classical
  have hsuf : R.suffixSide ∉ (Finset.univ.erase f).map R.embedding.faces := by
    intro h
    obtain ⟨g, hg, hgeq⟩ := Finset.mem_map.mp h
    exact R.suffixSide_not_kept g (Finset.ne_of_mem_erase hg) hgeq
  have hpre : R.prefixSide ∉
      insert R.suffixSide ((Finset.univ.erase f).map R.embedding.faces) := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact R.prefixSide_ne_suffixSide h
    · obtain ⟨g, hg, hgeq⟩ := Finset.mem_map.mp h
      exact R.prefixSide_not_kept g (Finset.ne_of_mem_erase hg) hgeq
  by_contra hx
  have hnot : R.diagram.toCombMap.faceOf x ∉
      insert R.prefixSide (insert R.suffixSide ((Finset.univ.erase f).map R.embedding.faces)) := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact hx (Or.inr (Or.inl h))
    · rcases Finset.mem_insert.mp h with h | h
      · exact hx (Or.inr (Or.inr h))
      · obtain ⟨g, hg, hgeq⟩ := Finset.mem_map.mp h
        exact hx (Or.inl ⟨g, Finset.ne_of_mem_erase hg, hgeq⟩)
  have hle := Finset.card_le_univ (insert (R.diagram.toCombMap.faceOf x)
    (insert R.prefixSide (insert R.suffixSide ((Finset.univ.erase f).map R.embedding.faces))))
  rw [Finset.card_insert_of_notMem hnot, Finset.card_insert_of_notMem hpre,
    Finset.card_insert_of_notMem hsuf, Finset.card_map] at hle
  have herase := Finset.card_erase_add_one (Finset.mem_univ f)
  rw [Finset.card_univ] at herase
  have hcount : Nat.card R.diagram.toCombMap.Face = Nat.card Delta.toCombMap.Face + 1 :=
    R.faceCount_eq
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hcount
  omega

/-- Every dart of a split insertion is a retained old dart, a dart of the inserted path or the
reverse of one. -/
theorem mem_range_or_path (x : R.diagram.toCombMap.Dart) :
    x ∈ Set.range R.embedding.darts ∨ x ∈ R.darts ∨
      x ∈ Embedded.invDarts R.diagram R.darts := by
  rcases R.faceOf_retained_or_sides x with ⟨g, hg, hgx⟩ | hx | hx
  · have hmem : x ∈ (R.diagram.faceBoundary (R.embedding.faces g)).darts :=
      ((R.diagram.faceBoundary _).mem_iff x).mpr hgx.symm
    rw [R.embedding.face_boundary g hg] at hmem
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hmem
    exact Or.inl ⟨d, rfl⟩
  · have hmem : x ∈ (R.diagram.faceBoundary R.prefixSide).darts :=
      ((R.diagram.faceBoundary _).mem_iff x).mpr hx
    rw [R.prefixSide_darts, List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · exact Or.inr (Or.inr hmem)
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hmem
      exact Or.inl ⟨d, rfl⟩
  · have hmem : x ∈ (R.diagram.faceBoundary R.suffixSide).darts :=
      ((R.diagram.faceBoundary _).mem_iff x).mpr hx
    rw [R.suffixSide_darts, List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · exact Or.inr (Or.inl hmem)
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hmem
      exact Or.inl ⟨d, rfl⟩

/-- **A split insertion of `word` adds at most `2 * word.length` darts.** -/
theorem dartCount_le_add_two_mul :
    R.diagram.toCombMap.dartCount ≤ Delta.toCombMap.dartCount + 2 * word.length := by
  classical
  have hsub : (Finset.univ : Finset R.diagram.toCombMap.Dart) ⊆
      (Finset.univ.map R.embedding.darts ∪ R.darts.toFinset) ∪
        (Embedded.invDarts R.diagram R.darts).toFinset := by
    intro x _
    rw [Finset.mem_union, Finset.mem_union, List.mem_toFinset, List.mem_toFinset]
    rcases R.mem_range_or_path x with ⟨d, rfl⟩ | hx | hx
    · exact Or.inl (Or.inl (Finset.mem_map_of_mem R.embedding.darts (Finset.mem_univ d)))
    · exact Or.inl (Or.inr hx)
    · exact Or.inr hx
  have hle := Finset.card_le_card hsub
  rw [Finset.card_univ] at hle
  have hunion := Finset.card_union_le (Finset.univ.map R.embedding.darts ∪ R.darts.toFinset)
    (Embedded.invDarts R.diagram R.darts).toFinset
  have hunion' := Finset.card_union_le (Finset.univ.map R.embedding.darts) R.darts.toFinset
  rw [Finset.card_map, Finset.card_univ] at hunion'
  have hpath := List.toFinset_card_le R.darts
  have hinv := List.toFinset_card_le (Embedded.invDarts R.diagram R.darts)
  have hinvlen : (Embedded.invDarts R.diagram R.darts).length = R.darts.length := by
    rw [Embedded.invDarts, List.length_map, List.length_reverse]
  have hlen := R.length_eq
  change Nat.card R.diagram.toCombMap.Dart ≤ Nat.card Delta.toCombMap.Dart + 2 * word.length
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  omega

end GFaceWordInsertion.SplitOutput

namespace RealizedSectionFamily

variable {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  (S : RealizedSectionFamily D lambda c eps Delta cuts) {A : RelGenSet G Lambda}
  {f : S.diagram.toCombMap.Face} {hf : f ≠ S.diagram.outerFace}
  {hcells : ∀ C ∈ S.diagram.relatorCells, C.face ≠ f}
  {start finish : Fin (S.diagram.faceBoundary f).darts.length} {word : List (RelLetter G Lambda)}
  (R : SplitCornerOutput A S.diagram f hf hcells start finish word)
  (havoid : ∀ a ∈ S.family, f ∉ a.1)

/-- **A section family across a split insertion** between two corners of a G-face that no
selected region contains.  `CornerOutput.originalReplacement` already starts from the original
diagram, so the rebase to the corner needs no step of its own. -/
noncomputable def insertionSection : RealizedSectionFamily D lambda c eps Delta cuts where
  diagram := R.diagram
  equiv := S.equiv.trans (CornerOutput.originalReplacement R.toCellOutput).oEquivalent
  reduced := (CornerOutput.originalReplacement R.toCellOutput).reduced S.reduced
  family := (CornerOutput.originalEmbedding R.toCellOutput).regionFamily
    (CornerOutput.originalCellMap R.toCellOutput) hcells hf S.family havoid
  pairwise := (CornerOutput.originalEmbedding R.toCellOutput).regionFamily_pairwise
    (CornerOutput.originalCellMap R.toCellOutput) hcells hf S.family havoid S.pairwise
  respects := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := DiscEmbeddingAway.regionFamily_profile
      (CornerOutput.originalEmbedding R.toCellOutput)
      (CornerOutput.originalCellMap R.toCellOutput) hcells hf S.family havoid ha
    exact RegionCandidate.respectsSections_of_sameTargetProfile cuts hab
      (DiscEmbeddingAway.regionFamily_noLoop (CornerOutput.originalEmbedding R.toCellOutput)
        (CornerOutput.originalCellMap R.toCellOutput) hcells hf S.family havoid
        (fun x hx => (S.respects x hx).1) ha)
      (S.respects b hb)
  nondegenerate := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := DiscEmbeddingAway.regionFamily_profile
      (CornerOutput.originalEmbedding R.toCellOutput)
      (CornerOutput.originalCellMap R.toCellOutput) hcells hf S.family havoid ha
    obtain ⟨hs, ht⟩ := S.nondegenerate b hb
    exact ⟨lt_of_lt_of_eq hs hab.2.2.2.symm, lt_of_lt_of_eq ht hab.2.2.1.symm⟩

/-- The weight is unchanged. -/
theorem insertionSection_weight : (insertionSection S R havoid).weight = S.weight :=
  (CornerOutput.originalEmbedding R.toCellOutput).regionFamily_weight
    (CornerOutput.originalCellMap R.toCellOutput) hcells hf S.family havoid

/-- The number of regions is unchanged. -/
theorem insertionSection_card : (insertionSection S R havoid).family.card = S.family.card :=
  (CornerOutput.originalEmbedding R.toCellOutput).regionFamily_card
    (CornerOutput.originalCellMap R.toCellOutput) hcells hf S.family havoid

/-- The labels of the insertion are letters of its alphabet. -/
theorem insertionSection_labelLegal :
    (insertionSection S R havoid).toRealizedRegionFamily.LabelLegal A :=
  fun d => R.label_admissible d

end RealizedSectionFamily

namespace GloballyDistinguishedSectionFamily

variable {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
  {f : S.diagram.toCombMap.Face} {hf : f ≠ S.diagram.outerFace}
  {hcells : ∀ C ∈ S.diagram.relatorCells, C.face ≠ f}
  {start finish : Fin (S.diagram.faceBoundary f).darts.length} {word : List (RelLetter G Lambda)}
  (R : SplitCornerOutput (symmetricLabelAlphabet D) S.diagram f hf hcells start finish word)
  (havoid : ∀ a ∈ S.family, f ∉ a.1)

/-- **A distinguished section family across a split insertion** between two corners of a
G-face that no selected region contains. -/
noncomputable def insertionTransport : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts
    where
  toRealizedSectionFamily :=
    RealizedSectionFamily.insertionSection S.toRealizedSectionFamily R havoid
  label_admissible :=
    RealizedSectionFamily.insertionSection_labelLegal S.toRealizedSectionFamily R havoid
  weight_maximal other hother :=
    (S.weight_maximal other hother).trans_eq
      (RealizedSectionFamily.insertionSection_weight S.toRealizedSectionFamily R havoid).symm
  card_minimal other hother hweight :=
    (RealizedSectionFamily.insertionSection_card S.toRealizedSectionFamily R havoid).trans_le
      (S.card_minimal other hother (hweight.trans
        (RealizedSectionFamily.insertionSection_weight S.toRealizedSectionFamily R havoid)))

theorem insertionTransport_diagram : (insertionTransport S R havoid).diagram = R.diagram :=
  rfl

theorem insertionTransport_family :
    (insertionTransport S R havoid).family =
      (CornerOutput.originalEmbedding R.toCellOutput).regionFamily
        (CornerOutput.originalCellMap R.toCellOutput) hcells hf S.family havoid :=
  rfl

/-- The number of regions is unchanged. -/
theorem insertionTransport_card : (insertionTransport S R havoid).family.card = S.family.card :=
  RealizedSectionFamily.insertionSection_card S.toRealizedSectionFamily R havoid

/-- **The unbound sum is unchanged.** -/
theorem insertionTransport_unboundSum :
    (insertionTransport S R havoid).unboundSum = S.unboundSum :=
  (CornerOutput.originalEmbedding R.toCellOutput).sum_unboundDarts_regionFamily_card
    (CornerOutput.originalCellMap R.toCellOutput) hcells hf S.family havoid

/-- **The insertion adds at most `2 * word.length` darts.** -/
theorem insertionTransport_dartCount_le :
    (insertionTransport S R havoid).diagram.toCombMap.dartCount ≤
      S.diagram.toCombMap.dartCount + 2 * word.length :=
  SplitOutput.dartCount_le_add_two_mul R

/-- No transported region contains either side. -/
theorem insertionTransport_avoid :
    ∀ a ∈ (insertionTransport S R havoid).family, R.prefixSide ∉ a.1 ∧ R.suffixSide ∉ a.1 := by
  intro a ha
  obtain ⟨b, hb, hab⟩ := (CornerOutput.originalEmbedding R.toCellOutput).regionFamily_faces
    (CornerOutput.originalCellMap R.toCellOutput) hcells hf S.family havoid ha
  rw [hab]
  constructor
  · intro hmem
    obtain ⟨g, hg, hgeq⟩ := Finset.mem_map.mp hmem
    exact R.prefixSide_not_kept g (fun h => havoid b hb (h ▸ hg)) hgeq
  · intro hmem
    obtain ⟨g, hg, hgeq⟩ := Finset.mem_map.mp hmem
    exact R.suffixSide_not_kept g (fun h => havoid b hb (h ▸ hg)) hgeq

/-- Every transported region has the target profile of an old region. -/
theorem insertionTransport_profile :
    ∀ a ∈ (insertionTransport S R havoid).family,
      ∃ b ∈ S.family, RegionCandidate.SameTargetProfile a b :=
  fun _ ha => DiscEmbeddingAway.regionFamily_profile
    (CornerOutput.originalEmbedding R.toCellOutput)
    (CornerOutput.originalCellMap R.toCellOutput) hcells hf S.family havoid ha

end GloballyDistinguishedSectionFamily

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.DiscEmbeddingAway.darts_mem_map_iff
#audit_axioms GroupApproximation.GGT.VanKampen.DiscEmbeddingAway.darts_mem_cellArcDarts_iff
#audit_axioms GroupApproximation.GGT.VanKampen.DiscEmbeddingAway.darts_mem_boundDarts_regionFamily_iff
#audit_axioms GroupApproximation.GGT.VanKampen.DiscEmbeddingAway.unboundDarts_regionFamily
#audit_axioms GroupApproximation.GGT.VanKampen.DiscEmbeddingAway.sum_unboundDarts_regionFamily_card
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.SplitOutput.faceOf_retained_or_sides
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.SplitOutput.mem_range_or_path
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.SplitOutput.dartCount_le_add_two_mul
#audit_axioms GroupApproximation.GGT.VanKampen.RealizedSectionFamily.insertionSection
#audit_axioms GroupApproximation.GGT.VanKampen.RealizedSectionFamily.insertionSection_weight
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.insertionTransport
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.insertionTransport_card
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.insertionTransport_unboundSum
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.insertionTransport_dartCount_le
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.insertionTransport_avoid
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.insertionTransport_profile
