import GroupApproximation.GGT.VanKampen.SurgeryHairOpening
import GroupApproximation.GGT.VanKampen.SurgeryGFaceMergeRegions
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PlanarPieces
import GroupApproximation.Meta.AxiomGuard

/-!
# The unbound sum across the opening of a hair

`FaceEdgeDoubling.diagram` moves every relator cell to the image of its face, and the darts of
the cell are the old ones through `carrierImage` (`FaceEdgeDoubling.cellDarts_eq`).  Away from
`f` this map is `embed`; on `f` it puts the new dart in the place of `w_j`.  Both are injective.
The arcs of a transported region are the old arcs through the same map at the same cell, so a
dart of a relator cell is bound by a transported region exactly when its old dart was bound.
The unbound darts of every relator cell are the old ones through `carrierImage`, and the unbound
sum does not change.

* `HairOpening.carrierImage_injective`.
* `HairOpening.unboundDarts_regionFamily`, `sum_unboundDarts_regionFamily_card`.
* `HairOpening.sectionFamily_unboundSum`: the family across the doubling has the old unbound
  sum.
* `HairOpening.exists_opened_unboundSum`: `exists_opened`, with the unbound sum unchanged.

## Manuscript status

Infrastructure for Osin's Lemma 9.4 (arXiv:math/0411039v3, §9).  It certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.HairOpening

open HullSC EdgeInsertion Surgery Embedded
open scoped Classical

universe u w v

theorem mem_map_of_injective_iff {α β : Type*} {φ : α → β} (hφ : Function.Injective φ)
    (l : List α) (d : α) : φ d ∈ l.map φ ↔ d ∈ l := by
  constructor
  · intro h
    obtain ⟨e, he, hed⟩ := List.mem_map.mp h
    rwa [hφ hed] at he
  · exact fun h => List.mem_map_of_mem h

section Unbound

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face)
  (j : Fin (Delta.faceBoundary f).darts.length)
  (hlen : 1 < (Delta.faceBoundary f).darts.length) (hf : f ≠ Delta.outerFace)
  {D : RelGenSet G Lambda} {eps : ℕ}

/-- The dart map on the traversal of an old face is injective. -/
theorem carrierImage_injective (g : Delta.toCombMap.Face) :
    Function.Injective (FaceEdgeDoubling.carrierImage Delta f j hlen hf g) := by
  by_cases hg : g = f
  · rw [hg, FaceEdgeDoubling.carrierImage_self]
    intro a b h
    by_cases ha : a = FaceEdgeDoubling.dart Delta f j <;>
      by_cases hb : b = FaceEdgeDoubling.dart Delta f j
    · exact ha.trans hb.symm
    · rw [FaceEdgeDoubling.dartImage, FaceEdgeDoubling.dartImage, if_pos ha, if_neg hb] at h
      exact absurd (Option.some.inj h) (fun h' => by cases h')
    · rw [FaceEdgeDoubling.dartImage, FaceEdgeDoubling.dartImage, if_neg ha, if_pos hb] at h
      exact absurd (Option.some.inj h) (fun h' => by cases h')
    · rw [FaceEdgeDoubling.dartImage, FaceEdgeDoubling.dartImage, if_neg ha, if_neg hb] at h
      exact embed_injective Delta.toCombMap h
  · rw [FaceEdgeDoubling.carrierImage_of_ne Delta f j hlen hf hg]
    exact embed_injective Delta.toCombMap

theorem transported_source_eq_iff (a : FaceEdgeDoubling.Avoiding Delta f j D eps)
    (i : Fin Delta.rCellCount) :
    (FaceEdgeDoubling.regionCandidate Delta f j hlen hf a).2.source =
        (FaceEdgeDoubling.cellMap Delta f j hlen hf).indexEquiv i ↔ a.val.2.source = i :=
  (FaceEdgeDoubling.cellMap Delta f j hlen hf).indexEquiv.apply_eq_iff_eq

theorem transported_target_eq_some_iff (a : FaceEdgeDoubling.Avoiding Delta f j D eps)
    (i : Fin Delta.rCellCount) :
    (FaceEdgeDoubling.regionCandidate Delta f j hlen hf a).2.target =
        some ((FaceEdgeDoubling.cellMap Delta f j hlen hf).indexEquiv i) ↔
      a.val.2.target = some i := by
  change Option.map (FaceEdgeDoubling.cellMap Delta f j hlen hf).indexEquiv a.val.2.target =
    some ((FaceEdgeDoubling.cellMap Delta f j hlen hf).indexEquiv i) ↔ _
  constructor
  · intro h
    exact Option.map_injective (FaceEdgeDoubling.cellMap Delta f j hlen hf).indexEquiv.injective h
  · intro h
    rw [h]
    rfl

theorem transported_target_isSome (a : FaceEdgeDoubling.Avoiding Delta f j D eps) :
    (FaceEdgeDoubling.regionCandidate Delta f j hlen hf a).2.target.isSome =
      a.val.2.target.isSome :=
  Option.isSome_map

theorem transported_sourceArc_darts (a : FaceEdgeDoubling.Avoiding Delta f j D eps) :
    (FaceEdgeDoubling.regionCandidate Delta f j hlen hf a).2.sourceArc.darts =
      a.val.2.sourceArc.darts.map
        (FaceEdgeDoubling.carrierImage Delta f j hlen hf (Embedded.cell Delta a.val.2.source).face) :=
  CyclicArc.mapTo_darts a.val.2.sourceArc _
    (FaceEdgeDoubling.cellDarts_eq Delta f j hlen hf a.val.2.source)

theorem transported_targetArc_darts (a : FaceEdgeDoubling.Avoiding Delta f j D eps) :
    (FaceEdgeDoubling.regionCandidate Delta f j hlen hf a).2.targetArc.darts =
      a.val.2.targetArc.darts.map
        (FaceEdgeDoubling.targetImage Delta f j hlen hf a.val.2.target) :=
  CyclicArc.mapTo_darts a.val.2.targetArc _
    (FaceEdgeDoubling.targetDarts_eq Delta f j hlen hf a.val.2.target)

/-- A dart of a relator cell lies on an arc of a transported region at the transported cell
exactly when the old dart lies on the arc of the old region at the old cell. -/
theorem carrierImage_mem_cellArcDarts_iff (a : FaceEdgeDoubling.Avoiding Delta f j D eps)
    (i : Fin Delta.rCellCount) (d : Delta.toCombMap.Dart) :
    FaceEdgeDoubling.carrierImage Delta f j hlen hf (Embedded.cell Delta i).face d ∈
        (FaceEdgeDoubling.regionCandidate Delta f j hlen hf a).cellArcDarts
          ((FaceEdgeDoubling.cellMap Delta f j hlen hf).indexEquiv i) ↔
      d ∈ a.val.cellArcDarts i := by
  rw [Surgery.GFaceMerge.mem_cellArcDarts_iff, Surgery.GFaceMerge.mem_cellArcDarts_iff,
    transported_source_eq_iff Delta f j hlen hf a i,
    transported_target_eq_some_iff Delta f j hlen hf a i,
    transported_sourceArc_darts Delta f j hlen hf a,
    transported_targetArc_darts Delta f j hlen hf a]
  constructor
  · rintro (⟨hs, hd⟩ | ⟨ht, hd⟩)
    · subst hs
      exact Or.inl ⟨rfl,
        (mem_map_of_injective_iff (carrierImage_injective Delta f j hlen hf _) _ d).mp hd⟩
    · have himage : FaceEdgeDoubling.targetImage Delta f j hlen hf a.val.2.target =
          FaceEdgeDoubling.carrierImage Delta f j hlen hf (Embedded.cell Delta i).face :=
        (congrArg (FaceEdgeDoubling.targetImage Delta f j hlen hf) ht).trans rfl
      rw [himage] at hd
      exact Or.inr ⟨ht,
        (mem_map_of_injective_iff (carrierImage_injective Delta f j hlen hf _) _ d).mp hd⟩
  · rintro (⟨hs, hd⟩ | ⟨ht, hd⟩)
    · subst hs
      exact Or.inl ⟨rfl, List.mem_map_of_mem hd⟩
    · have himage : FaceEdgeDoubling.targetImage Delta f j hlen hf a.val.2.target =
          FaceEdgeDoubling.carrierImage Delta f j hlen hf (Embedded.cell Delta i).face :=
        (congrArg (FaceEdgeDoubling.targetImage Delta f j hlen hf) ht).trans rfl
      rw [himage]
      exact Or.inr ⟨ht, List.mem_map_of_mem hd⟩

/-- A dart of a relator cell is used by a transported region of either kind exactly when its old
dart was used by the old region. -/
theorem carrierImage_mem_boundDarts_iff (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1 ∧
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta f j)) ∉ a.1)
    (interior : Bool) (i : Fin Delta.rCellCount) (d : Delta.toCombMap.Dart) :
    FaceEdgeDoubling.carrierImage Delta f j hlen hf (Embedded.cell Delta i).face d ∈
        RegionCandidate.boundDarts (FaceEdgeDoubling.regionFamily Delta f j hlen hf family havoid)
          interior ((FaceEdgeDoubling.cellMap Delta f j hlen hf).indexEquiv i) ↔
      d ∈ RegionCandidate.boundDarts family interior i := by
  rw [Surgery.GFaceMerge.mem_boundDarts_iff, Surgery.GFaceMerge.mem_boundDarts_iff]
  constructor
  · rintro ⟨a', ha', hkind, hd⟩
    obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp ha'
    exact ⟨b.val, b.property,
      (transported_target_isSome Delta f j hlen hf ⟨b.val, havoid b.val b.property⟩).symm.trans
        hkind,
      (carrierImage_mem_cellArcDarts_iff Delta f j hlen hf ⟨b.val, havoid b.val b.property⟩ i
        d).mp hd⟩
  · rintro ⟨b, hb, hkind, hd⟩
    exact ⟨FaceEdgeDoubling.regionCandidate Delta f j hlen hf ⟨b, havoid b hb⟩,
      Finset.mem_map.mpr ⟨⟨b, hb⟩, Finset.mem_attach _ _, rfl⟩,
      (transported_target_isSome Delta f j hlen hf ⟨b, havoid b hb⟩).trans hkind,
      (carrierImage_mem_cellArcDarts_iff Delta f j hlen hf ⟨b, havoid b hb⟩ i d).mpr hd⟩

/-- **The unbound darts of a relator cell are the old ones, through `carrierImage`.** -/
theorem unboundDarts_regionFamily (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1 ∧
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta f j)) ∉ a.1)
    (i : Fin Delta.rCellCount) :
    RegionCandidate.unboundDarts (FaceEdgeDoubling.regionFamily Delta f j hlen hf family havoid)
        ((FaceEdgeDoubling.cellMap Delta f j hlen hf).indexEquiv i) =
      (RegionCandidate.unboundDarts family i).map
        ⟨FaceEdgeDoubling.carrierImage Delta f j hlen hf (Embedded.cell Delta i).face,
          carrierImage_injective Delta f j hlen hf _⟩ := by
  ext x
  rw [Surgery.GFaceMerge.mem_unboundDarts_iff, FaceEdgeDoubling.cellDarts_eq Delta f j hlen hf i,
    Finset.mem_map]
  constructor
  · rintro ⟨hx, hnot⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
    refine ⟨d, (Surgery.GFaceMerge.mem_unboundDarts_iff family i d).mpr ⟨hd, ?_⟩, rfl⟩
    rwa [carrierImage_mem_boundDarts_iff Delta f j hlen hf family havoid false i d,
      carrierImage_mem_boundDarts_iff Delta f j hlen hf family havoid true i d] at hnot
  · rintro ⟨d, hd, hx⟩
    have hx' : FaceEdgeDoubling.carrierImage Delta f j hlen hf (Embedded.cell Delta i).face d =
        x := hx
    subst hx'
    obtain ⟨hd, hnot⟩ := (Surgery.GFaceMerge.mem_unboundDarts_iff family i d).mp hd
    refine ⟨List.mem_map_of_mem hd, ?_⟩
    rwa [carrierImage_mem_boundDarts_iff Delta f j hlen hf family havoid false i d,
      carrierImage_mem_boundDarts_iff Delta f j hlen hf family havoid true i d]

theorem unboundDarts_regionFamily_card (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1 ∧
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta f j)) ∉ a.1)
    (i : Fin Delta.rCellCount) :
    (RegionCandidate.unboundDarts (FaceEdgeDoubling.regionFamily Delta f j hlen hf family havoid)
        ((FaceEdgeDoubling.cellMap Delta f j hlen hf).indexEquiv i)).card =
      (RegionCandidate.unboundDarts family i).card := by
  rw [unboundDarts_regionFamily Delta f j hlen hf family havoid i, Finset.card_map]

/-- **The total number of unbound darts is unchanged.** -/
theorem sum_unboundDarts_regionFamily_card (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1 ∧
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta f j)) ∉ a.1) :
    ∑ k : Fin (FaceEdgeDoubling.diagram Delta f j hlen hf).rCellCount,
        (RegionCandidate.unboundDarts
          (FaceEdgeDoubling.regionFamily Delta f j hlen hf family havoid) k).card =
      ∑ i : Fin Delta.rCellCount, (RegionCandidate.unboundDarts family i).card := by
  rw [← Equiv.sum_comp (FaceEdgeDoubling.cellMap Delta f j hlen hf).indexEquiv]
  exact Finset.sum_congr rfl fun i _ =>
    unboundDarts_regionFamily_card Delta f j hlen hf family havoid i

end Unbound

section Family

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **The unbound sum is unchanged.** -/
theorem sectionFamily_unboundSum (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (f : S.diagram.toCombMap.Face) (j : Fin (S.diagram.faceBoundary f).darts.length)
    (hlen : 1 < (S.diagram.faceBoundary f).darts.length) (hf : f ≠ S.diagram.outerFace)
    (havoid : ∀ a ∈ S.family, f ∉ a.1 ∧ S.diagram.toCombMap.faceOf
      (S.diagram.toCombMap.alpha (FaceEdgeDoubling.dart S.diagram f j)) ∉ a.1) :
    (sectionFamily S f j hlen hf havoid).unboundSum = S.unboundSum :=
  sum_unboundDarts_regionFamily_card S.diagram f j hlen hf S.family havoid

/-- **Opening a hair of an inner face, with the unbound sum.**  `exists_opened`, and the opened
family has the unbound sum of `S`. -/
theorem exists_opened_unboundSum
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {x : S.diagram.toCombMap.Dart} (hx : IsHair S.diagram x)
    (hf : S.diagram.toCombMap.faceOf x ≠ S.diagram.outerFace)
    (havoid : ∀ a ∈ S.family, S.diagram.toCombMap.faceOf x ∉ a.1) :
    ∃ (S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (e : S.family ≃ S'.family),
      Nonempty (OEquivalentDiscDiagram S.diagram S'.diagram) ∧
        S'.toRealizedSectionFamily.weight = S.toRealizedSectionFamily.weight ∧
          S'.unboundSum = S.unboundSum ∧
          (∀ a, RegionCandidate.SameTargetProfile (e a).1 a.1 ∧
            (e a).1.2.source.val = a.1.2.source.val) ∧
          ∃ g : S'.diagram.toCombMap.Face, g ≠ S'.diagram.outerFace ∧
            (S'.diagram.faceBoundary g).darts.length = 2 ∧
            RelLetter.listVal ((S'.diagram.faceBoundary g).darts.map S'.diagram.label) = 1 := by
  have hx' : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha x) =
      S.diagram.toCombMap.faceOf x := Eq.symm hx
  have hlen := one_lt_length_of_isHair hx
  obtain ⟨j, hj⟩ := exists_dart_eq x
  have havoid' : ∀ a ∈ S.family, S.diagram.toCombMap.faceOf x ∉ a.1 ∧
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha
        (FaceEdgeDoubling.dart S.diagram (S.diagram.toCombMap.faceOf x) j)) ∉ a.1 := by
    intro a ha
    refine ⟨havoid a ha, ?_⟩
    rw [hj, hx']
    exact havoid a ha
  refine ⟨sectionFamily S _ j hlen hf havoid',
    regionFamilyEquiv S.diagram _ j hlen hf S.family havoid',
    ⟨FaceEdgeDoubling.oEquivalent S.diagram _ j hlen hf⟩,
    FaceEdgeDoubling.regionFamily_weight S.diagram _ j hlen hf S.family havoid',
    sectionFamily_unboundSum S _ j hlen hf havoid',
    fun a => And.intro (regionFamilyEquiv_profile S.diagram _ j hlen hf S.family havoid' a)
      (regionFamilyEquiv_source S.diagram _ j hlen hf S.family havoid' a),
    FaceEdgeDoubling.digon S.diagram _ j hlen, ?_, ?_, ?_⟩
  · intro h
    exact FaceEdgeDoubling.keep_ne_digon S.diagram _ j hlen (Ne.symm hf) h.symm
  · change (FaceEdgeDoubling.boundary S.diagram _ j hlen
      (FaceEdgeDoubling.digon S.diagram _ j hlen)).darts.length = 2
    rw [FaceEdgeDoubling.boundary_digon]
    rfl
  · exact FaceEdgeDoubling.boundary_digon_value S.diagram _ j hlen

end Family

end GroupApproximation.GGT.VanKampen.HairOpening

#audit_axioms GroupApproximation.GGT.VanKampen.HairOpening.carrierImage_injective
#audit_axioms GroupApproximation.GGT.VanKampen.HairOpening.carrierImage_mem_boundDarts_iff
#audit_axioms GroupApproximation.GGT.VanKampen.HairOpening.unboundDarts_regionFamily
#audit_axioms GroupApproximation.GGT.VanKampen.HairOpening.sum_unboundDarts_regionFamily_card
#audit_axioms GroupApproximation.GGT.VanKampen.HairOpening.sectionFamily_unboundSum
#audit_axioms GroupApproximation.GGT.VanKampen.HairOpening.exists_opened_unboundSum
