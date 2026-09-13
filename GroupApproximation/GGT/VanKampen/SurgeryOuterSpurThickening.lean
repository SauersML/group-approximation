import GroupApproximation.GGT.VanKampen.SurgeryFaceEdgeDoublingRegions
import GroupApproximation.GGT.VanKampen.Estimating.ContiguityTransport
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundCaseOne
import GroupApproximation.Meta.AxiomGuard

/-!
# Thickening outer spurs into G-cell digons

A section word may backtrack, so the boundary of a diagram can carry a spur: an edge with
the exterior on both sides.  `FaceEdgeDoubling.diagram` doubles an edge of an inner face
only.  This file doubles an edge of the exterior.

Let `w_j` be a dart of the outer traversal `w_0 … w_{n-1}`.  Rebase the traversal at `w_j`
and insert an edge between the corners before and after `w_j` (`EdgeInsertion.splitMap`),
labelled by the label of `w_j`.  The inserted edge closes a digon `none, w_j`, a G-cell of
value one, and the exterior reads the old traversal with the new dart in the place of `w_j`
(`FaceEdgeDoubling.boundary_cellFace_darts`).  The boundary word and the relator cells are
unchanged, so the new diagram is O-equivalent over the same section cuts.  When `α w_j` is on
the exterior too, the spur `w_j, α w_j` is replaced by the new outer dart and `α w_j`, whose
reverses `none` and `w_j` lie on the digon.  No spur is created, so the number of outer spurs
drops by one (`outerSpurCount_lt`).

No selected region contains the exterior, so every region of a section family transports with
its face set, weight, target profile and source cell (`regionFamily`).  The outer arcs change
only at `α w_j`, which lies on no region boundary when its face is the exterior.  Induction on
the number of outer spurs gives `OuterSpurThickeningStatement`.
-/

namespace GroupApproximation.GGT.VanKampen.OuterSpurThickening

open HullSC EdgeInsertion Surgery Embedded
open scoped Classical

universe u w v

/-- An **outer spur**: a dart on the exterior whose reverse is also on the exterior. -/
def IsOuterSpur {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (x : Delta.toCombMap.Dart) : Prop :=
  Delta.toCombMap.faceOf x = Delta.outerFace ∧
    Delta.toCombMap.faceOf (Delta.toCombMap.alpha x) = Delta.outerFace

/-- The number of outer spur darts. -/
noncomputable def outerSpurCount {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} (Delta : DiscDiagram.{u, w, v} W) : ℕ :=
  (Finset.univ.filter (IsOuterSpur Delta)).card

/-- **Outer spur thickening.**  A distinguished section family has a distinguished section
family over the same cuts whose diagram is O-equivalent to the old one and has no outer spur.
Its regions correspond bijectively to the old ones, with the same total weight, and every
region keeps its target profile and the index of its source cell. -/
def OuterSpurThickeningStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W)
    (cuts : SectionCuts D lambda c Delta.boundaryWord)
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts),
    ∃ (S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (e : S.family ≃ S'.family),
      Nonempty (OEquivalentDiscDiagram S.diagram S'.diagram) ∧
        (∀ x, ¬ IsOuterSpur S'.diagram x) ∧
          S'.toRealizedSectionFamily.weight = S.toRealizedSectionFamily.weight ∧
            ∀ a, RegionCandidate.SameTargetProfile (e a).1 a.1 ∧
              (e a).1.2.source.val = a.1.2.source.val

section Thickening

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
variable (Delta : DiscDiagram.{u, w, v} W)
  (j : Fin (Delta.faceBoundary Delta.outerFace).darts.length)
  (hlen : 1 < (Delta.faceBoundary Delta.outerFace).darts.length)

/-- A relator cell, moved to the retained copy of its face. -/
noncomputable def spurCell (C : RelatorCell Delta.toCombMap Delta.outerFace W) :
    RelatorCell (FaceEdgeDoubling.map Delta Delta.outerFace j hlen)
      (FaceEdgeDoubling.cellFace Delta Delta.outerFace j hlen) W where
  face := FaceEdgeDoubling.faceImage Delta Delta.outerFace j hlen C.face
  face_ne_outer h := FaceEdgeDoubling.keep_ne_cellFace Delta Delta.outerFace j hlen
    C.face_ne_outer
    ((FaceEdgeDoubling.faceImage_of_ne Delta Delta.outerFace j hlen C.face_ne_outer).symm.trans h)
  word := C.word
  word_mem := C.word_mem
  conjugator := C.conjugator
  reversed := C.reversed

/-- **The thickened diagram.**  The exterior is the face of the doubled outer dart. -/
noncomputable def diagram : DiscDiagram.{u, w, v} W where
  toCombMap := FaceEdgeDoubling.map Delta Delta.outerFace j hlen
  planar := EdgeInsertion.planar Delta.toCombMap _ _ Delta.planar
    (corners_face_eq Delta.toCombMap (FaceEdgeDoubling.rebased Delta Delta.outerFace j)
      (FaceEdgeDoubling.second Delta Delta.outerFace j hlen))
  label := FaceEdgeDoubling.label Delta Delta.outerFace j hlen
  label_alpha := insertLabel_alpha Delta.toCombMap Delta.label Delta.label_alpha _ _ _
  outerFace := FaceEdgeDoubling.cellFace Delta Delta.outerFace j hlen
  faceBoundary := FaceEdgeDoubling.boundary Delta Delta.outerFace j hlen
  relatorCells := Delta.relatorCells.map (spurCell Delta j hlen)
  relatorCell_faces_nodup := by
    have heq : (Delta.relatorCells.map (spurCell Delta j hlen)).map RelatorCell.face =
        (Delta.relatorCells.map RelatorCell.face).map
          (FaceEdgeDoubling.faceImage Delta Delta.outerFace j hlen) := by
      rw [List.map_map, List.map_map]
      rfl
    rw [heq]
    exact Delta.relatorCell_faces_nodup.map
      (FaceEdgeDoubling.faceImage_injective Delta Delta.outerFace j hlen)
  relatorCell_word := by
    intro C hC
    obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC
    exact (Delta.relatorCell_word C₀ hC₀).trans
      (FaceEdgeDoubling.boundary_faceImage_word Delta Delta.outerFace j hlen C₀.face).symm
  inner_face := by
    intro F hF
    rcases face_partition Delta.toCombMap (FaceEdgeDoubling.rebased Delta Delta.outerFace j)
        (FaceEdgeDoubling.second Delta Delta.outerFace j hlen) F with
      hpre | hsuf | ⟨g, hg, hkept⟩
    · right
      rw [hpre]
      exact FaceEdgeDoubling.boundary_digon_value Delta Delta.outerFace j hlen
    · exact (hF hsuf).elim
    · rcases Delta.inner_face g hg with ⟨C, hC, hCg⟩ | hval
      · left
        refine ⟨spurCell Delta j hlen C, List.mem_map.mpr ⟨C, hC, rfl⟩, ?_⟩
        change FaceEdgeDoubling.faceImage Delta Delta.outerFace j hlen C.face = F
        rw [hCg, FaceEdgeDoubling.faceImage_of_ne Delta Delta.outerFace j hlen hg, hkept]
      · right
        rw [hkept, FaceEdgeDoubling.boundary_kept_word Delta Delta.outerFace j hlen hg]
        exact hval
  boundary_product := by
    have hvalues : (Delta.relatorCells.map (spurCell Delta j hlen)).map RelatorCell.value =
        Delta.relatorCells.map RelatorCell.value := by
      rw [List.map_map]
      rfl
    exact (congrArg List.prod hvalues).trans (Delta.boundary_product.trans
      (congrArg (fun word => RelLetter.listVal (RelWord.revInv word))
        (FaceEdgeDoubling.boundary_cellFace_word Delta Delta.outerFace j hlen).symm))

theorem boundaryWord_eq : (diagram Delta j hlen).boundaryWord = Delta.boundaryWord :=
  congrArg RelWord.revInv (FaceEdgeDoubling.boundary_cellFace_word Delta Delta.outerFace j hlen)

/-- The relator cells, literally. -/
noncomputable def cellMap :
    OrderedRCellMap Delta (diagram Delta j hlen)
      (FaceEdgeDoubling.faceImage Delta Delta.outerFace j hlen) where
  cell := spurCell Delta j hlen
  face_eq _ := rfl
  word_eq _ := rfl
  conjugator_eq _ := rfl
  reversed_eq _ := rfl
  list_eq := rfl

noncomputable def replacement : OrderedGRegionReplacement.{u, w, v, v} Delta where
  diagram := diagram Delta j hlen
  outerWord_eq := boundaryWord_eq Delta j hlen
  cells := (cellMap Delta j hlen).orderedTransport

noncomputable def oEquivalent : OEquivalentDiscDiagram Delta (diagram Delta j hlen) :=
  (replacement Delta j hlen).oEquivalent

theorem reduced (hred : Delta.Reduced) : (diagram Delta j hlen).Reduced :=
  (replacement Delta j hlen).reduced hred

theorem label_admissible (D : RelGenSet G Lambda) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (hlabel : ∀ d, D.IsLetter (Delta.label d)) (d : (diagram Delta j hlen).toCombMap.Dart) :
    D.IsLetter ((diagram Delta j hlen).label d) :=
  insertLabel_admissible Delta.toCombMap D hsymm Delta.label hlabel _ (hlabel _) d

/-- The retained old darts and faces; the old exterior goes to the new exterior. -/
noncomputable def embedding : DiscEmbeddingAway Delta (diagram Delta j hlen) Delta.outerFace where
  darts := ⟨embed Delta.toCombMap, embed_injective Delta.toCombMap⟩
  faces := ⟨FaceEdgeDoubling.faceImage Delta Delta.outerFace j hlen,
    FaceEdgeDoubling.faceImage_injective Delta Delta.outerFace j hlen⟩
  alpha _ := rfl
  label _ := rfl
  outer := (FaceEdgeDoubling.faceImage_self Delta Delta.outerFace j hlen).symm
  face_boundary g hg :=
    (congrArg (fun F => (FaceEdgeDoubling.boundary Delta Delta.outerFace j hlen F).darts)
      (FaceEdgeDoubling.faceImage_of_ne Delta Delta.outerFace j hlen hg)).trans
      (FaceEdgeDoubling.boundary_kept Delta Delta.outerFace j hlen hg)
  facePerm d hd := facePerm_embed_of_ne Delta.toCombMap _ _ d
    (corners_face_eq Delta.toCombMap (FaceEdgeDoubling.rebased Delta Delta.outerFace j)
      (FaceEdgeDoubling.second Delta Delta.outerFace j hlen))
    (by rwa [firstCorner_face Delta.toCombMap (FaceEdgeDoubling.rebased Delta Delta.outerFace j)])

/-- A region never contains the exterior. -/
theorem outer_not_mem {D : RelGenSet G Lambda} {eps : ℕ} {s : Finset Delta.toCombMap.Face}
    (H : ContiguityGeometry D eps Delta s) : Delta.outerFace ∉ s :=
  fun h => (H.boundary.all_gCells _ h).1 rfl

theorem cellDarts_eq (i : Fin Delta.rCellCount) :
    cellDarts (diagram Delta j hlen) ((cellMap Delta j hlen).indexEquiv i) =
      (cellDarts Delta i).map (embedding Delta j hlen).darts := by
  change ((diagram Delta j hlen).faceBoundary
    (Embedded.cell (diagram Delta j hlen) ((cellMap Delta j hlen).indexEquiv i)).face).darts = _
  rw [(cellMap Delta j hlen).indexed_cell, (cellMap Delta j hlen).face_eq]
  exact (embedding Delta j hlen).face_boundary _ (Embedded.cell Delta i).face_ne_outer

/-- The dart map on the exterior traversal: `α w_j` goes to the reverse of the new dart. -/
noncomputable def outerImage (y : Delta.toCombMap.Dart) :
    (FaceEdgeDoubling.map Delta Delta.outerFace j hlen).Dart :=
  if y = Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j) then none
  else embed Delta.toCombMap y

theorem outerImage_of_ne {y : Delta.toCombMap.Dart}
    (hy : y ≠ Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j)) :
    outerImage Delta j hlen y = (embedding Delta j hlen).darts y :=
  if_neg hy

theorem alpha_dartImage (d : Delta.toCombMap.Dart) :
    (diagram Delta j hlen).toCombMap.alpha
        (FaceEdgeDoubling.dartImage Delta Delta.outerFace j hlen d) =
      outerImage Delta j hlen (Delta.toCombMap.alpha d) := by
  by_cases hd : d = FaceEdgeDoubling.dart Delta Delta.outerFace j
  · rw [FaceEdgeDoubling.dartImage, if_pos hd, outerImage,
      if_pos (congrArg Delta.toCombMap.alpha hd)]
    rfl
  · rw [FaceEdgeDoubling.dartImage, if_neg hd, outerImage,
      if_neg (fun h => hd (Delta.toCombMap.alpha_involutive.injective h))]
    rfl

theorem outerDarts_eq :
    outerDarts (diagram Delta j hlen) = (outerDarts Delta).map (outerImage Delta j hlen) := by
  change invDarts (diagram Delta j hlen)
      (FaceEdgeDoubling.boundary Delta Delta.outerFace j hlen
        (FaceEdgeDoubling.cellFace Delta Delta.outerFace j hlen)).darts =
    (invDarts Delta (Delta.faceBoundary Delta.outerFace).darts).map (outerImage Delta j hlen)
  rw [FaceEdgeDoubling.boundary_cellFace_darts]
  -- The two dart types agree only after unfolding `diagram`, so no `simp` or `rw` here.
  exact (congrArg (List.map (diagram Delta j hlen).toCombMap.alpha)
      (List.map_reverse (f := FaceEdgeDoubling.dartImage Delta Delta.outerFace j hlen)
        (l := (Delta.faceBoundary Delta.outerFace).darts)).symm).trans
    ((List.map_map (g := (diagram Delta j hlen).toCombMap.alpha)
        (f := FaceEdgeDoubling.dartImage Delta Delta.outerFace j hlen)
        (l := (Delta.faceBoundary Delta.outerFace).darts.reverse)).trans
      ((List.map_congr_left fun d _ => alpha_dartImage Delta j hlen d).trans
        (List.map_map (g := outerImage Delta j hlen) (f := Delta.toCombMap.alpha)
          (l := (Delta.faceBoundary Delta.outerFace).darts.reverse)).symm))

/-- The dart map on the carrier of a target. -/
noncomputable def targetImage : Option (Fin Delta.rCellCount) →
    Delta.toCombMap.Dart → (diagram Delta j hlen).toCombMap.Dart
  | none => outerImage Delta j hlen
  | some _ => (embedding Delta j hlen).darts

theorem targetDarts_eq (t : Option (Fin Delta.rCellCount)) :
    targetDarts (diagram Delta j hlen) (t.map (cellMap Delta j hlen).indexEquiv) =
      (targetDarts Delta t).map (targetImage Delta j hlen t) := by
  cases t with
  | none => exact outerDarts_eq Delta j hlen
  | some i => exact cellDarts_eq Delta j hlen i

/-- A region does not use `α w_j` in its target arc when the face of `α w_j` is not in it. -/
theorem alpha_dart_not_mem_targetArc {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (H : ContiguityGeometry D eps Delta s)
    (hs2 : Delta.toCombMap.faceOf
      (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j)) ∉ s) :
    Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j) ∉
      H.targetArc.darts := by
  intro hmem
  have hcycle : ∀ d ∈ targetBoundaryDarts Delta H.target H.targetArc, d ∈ H.boundary.cycle := by
    intro d hd
    rw [H.boundary_decomposition]
    exact List.mem_append_left _ (List.mem_append_right _ hd)
  rcases FaceEdgeDoubling.mem_targetBoundaryDarts_of_mem Delta H.target H.targetArc hmem with
    h | h
  · exact hs2 ((H.boundary.cycle_mem_iff _).mp (hcycle _ h)).1
  · rw [Delta.toCombMap.alpha_involutive (FaceEdgeDoubling.dart Delta Delta.outerFace j)] at h
    have hin := ((H.boundary.cycle_mem_iff _).mp (hcycle _ h)).1
    rw [FaceEdgeDoubling.dart_face] at hin
    exact outer_not_mem Delta H hin

theorem targetBoundaryDarts_transport (t : Option (Fin Delta.rCellCount))
    (arc : CyclicArc (targetDarts Delta t))
    (havoid : Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j) ∉
      arc.darts) :
    targetBoundaryDarts (diagram Delta j hlen) (t.map (cellMap Delta j hlen).indexEquiv)
        (arc.mapTo (targetImage Delta j hlen t) (targetDarts_eq Delta j hlen t)) =
      (targetBoundaryDarts Delta t arc).map (embedding Delta j hlen).darts := by
  cases t with
  | none =>
      exact (CyclicArc.mapTo_darts arc (targetImage Delta j hlen none)
          (targetDarts_eq Delta j hlen none)).trans
        (List.map_congr_left fun d hd =>
          outerImage_of_ne Delta j hlen fun h => havoid (h ▸ hd))
  | some i => exact (embedding Delta j hlen).reverseDarts_mapTo arc _

/-- **Contiguity geometry through the thickening.** -/
noncomputable def contiguityGeometry {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face}
    (hs2 : Delta.toCombMap.faceOf
      (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j)) ∉ s)
    (H : ContiguityGeometry D eps Delta s) :
    ContiguityGeometry D eps (diagram Delta j hlen) ((embedding Delta j hlen).faceSet s) where
  boundary := (embedding Delta j hlen).boundary s (outer_not_mem Delta H) H.boundary
  source := (cellMap Delta j hlen).indexEquiv H.source
  target := H.target.map (cellMap Delta j hlen).indexEquiv
  sourceArc := H.sourceArc.mapTo (embedding Delta j hlen).darts
    (cellDarts_eq Delta j hlen H.source)
  targetArc := H.targetArc.mapTo (targetImage Delta j hlen H.target)
    (targetDarts_eq Delta j hlen H.target)
  rightSide := H.rightSide.map (embedding Delta j hlen).darts
  leftSide := H.leftSide.map (embedding Delta j hlen).darts
  boundary_decomposition := by
    change H.boundary.cycle.map (embedding Delta j hlen).darts = _
    rw [(embedding Delta j hlen).reverseDarts_mapTo H.sourceArc
        (cellDarts_eq Delta j hlen H.source),
      targetBoundaryDarts_transport Delta j hlen H.target H.targetArc
        (alpha_dart_not_mem_targetArc Delta j H hs2)]
    exact (congrArg (List.map (embedding Delta j hlen).darts) H.boundary_decomposition).trans
      (by simp only [List.map_append])
  rightSide_length_le := by simpa only [List.length_map] using H.rightSide_length_le
  leftSide_length_le := by simpa only [List.length_map] using H.leftSide_length_le
  rightSide_norm_le := by
    rw [(embedding Delta j hlen).dartWord_map]
    exact H.rightSide_norm_le
  leftSide_norm_le := by
    rw [(embedding Delta j hlen).dartWord_map]
    exact H.leftSide_norm_le
  pasting := by
    obtain ⟨l, hl⟩ := H.pasting
    exact ⟨l.map (embedding Delta j hlen).faces,
      (embedding Delta j hlen).shelling s (outer_not_mem Delta H) hl⟩

theorem contiguityGeometry_source_length {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face}
    (hs2 : Delta.toCombMap.faceOf
      (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j)) ∉ s)
    (H : ContiguityGeometry D eps Delta s) :
    (contiguityGeometry Delta j hlen hs2 H).sourceArc.length = H.sourceArc.length :=
  H.sourceArc.mapTo_length (embedding Delta j hlen).darts (cellDarts_eq Delta j hlen H.source)

theorem contiguityGeometry_target_length {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face}
    (hs2 : Delta.toCombMap.faceOf
      (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j)) ∉ s)
    (H : ContiguityGeometry D eps Delta s) :
    (contiguityGeometry Delta j hlen hs2 H).targetArc.length = H.targetArc.length :=
  H.targetArc.mapTo_length (targetImage Delta j hlen H.target)
    (targetDarts_eq Delta j hlen H.target)

theorem contiguityGeometry_target_start {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face}
    (hs2 : Delta.toCombMap.faceOf
      (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j)) ∉ s)
    (H : ContiguityGeometry D eps Delta s) :
    (contiguityGeometry Delta j hlen hs2 H).targetArc.start.val = H.targetArc.start.val :=
  H.targetArc.mapTo_start (targetImage Delta j hlen H.target)
    (targetDarts_eq Delta j hlen H.target)

theorem contiguityGeometry_injective {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face}
    (hs2 : Delta.toCombMap.faceOf
      (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j)) ∉ s) :
    Function.Injective (contiguityGeometry Delta j hlen hs2 :
      ContiguityGeometry D eps Delta s → ContiguityGeometry D eps (diagram Delta j hlen)
        ((embedding Delta j hlen).faceSet s)) := by
  intro H K h
  apply ContiguityGeometry.eq_of_data
  · exact (List.map_injective_iff.mpr (embedding Delta j hlen).darts.injective)
      (congrArg (fun J => J.boundary.cycle) h)
  · exact (cellMap Delta j hlen).indexEquiv.injective (congrArg (fun J => J.source) h)
  · exact (Equiv.optionCongr (cellMap Delta j hlen).indexEquiv).injective
      (congrArg (fun J => J.target) h)
  · simpa only [contiguityGeometry, CyclicArc.mapTo_start] using
      congrArg (fun J => J.sourceArc.start.val) h
  · simpa only [contiguityGeometry_source_length] using congrArg (fun J => J.sourceArc.length) h
  · simpa only [contiguityGeometry, CyclicArc.mapTo_start] using
      congrArg (fun J => J.targetArc.start.val) h
  · simpa only [contiguityGeometry_target_length] using congrArg (fun J => J.targetArc.length) h
  · exact (List.map_injective_iff.mpr (embedding Delta j hlen).darts.injective)
      (congrArg (fun J => J.rightSide) h)
  · exact (List.map_injective_iff.mpr (embedding Delta j hlen).darts.injective)
      (congrArg (fun J => J.leftSide) h)

/-- The regions a thickening retains: those avoiding the face across `w_j`. -/
abbrev Avoiding (D : RelGenSet G Lambda) (eps : ℕ) :=
  { a : RegionCandidate D eps Delta //
    Delta.toCombMap.faceOf (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j)) ∉
      a.1 }

noncomputable def regionCandidate {D : RelGenSet G Lambda} {eps : ℕ}
    (a : Avoiding Delta j D eps) : RegionCandidate D eps (diagram Delta j hlen) :=
  ⟨(embedding Delta j hlen).faceSet a.val.1, contiguityGeometry Delta j hlen a.property a.val.2⟩

theorem regionCandidate_injective {D : RelGenSet G Lambda} {eps : ℕ} :
    Function.Injective (regionCandidate Delta j hlen :
      Avoiding Delta j D eps → RegionCandidate D eps (diagram Delta j hlen)) := by
  rintro ⟨⟨s, H⟩, hs⟩ ⟨⟨t, K⟩, ht⟩ h
  have hfaces : (embedding Delta j hlen).faceSet s = (embedding Delta j hlen).faceSet t :=
    congrArg Sigma.fst h
  have hst : s = t := Finset.map_injective (embedding Delta j hlen).faces hfaces
  subst hst
  have hcont : contiguityGeometry Delta j hlen hs H = contiguityGeometry Delta j hlen ht K :=
    eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hHK := contiguityGeometry_injective Delta j hlen hs hcont
  cases hHK
  rfl

theorem regionCandidate_weight {D : RelGenSet G Lambda} {eps : ℕ} (a : Avoiding Delta j D eps) :
    RegionCandidate.weight (regionCandidate Delta j hlen a) = RegionCandidate.weight a.val :=
  congrArg₂ Nat.add (contiguityGeometry_source_length Delta j hlen a.property a.val.2)
    (contiguityGeometry_target_length Delta j hlen a.property a.val.2)

theorem regionCandidate_compatible {D : RelGenSet G Lambda} {eps : ℕ}
    (a b : Avoiding Delta j D eps) :
    RegionCandidate.Compatible (regionCandidate Delta j hlen a)
        (regionCandidate Delta j hlen b) ↔ RegionCandidate.Compatible a.val b.val :=
  (embedding Delta j hlen).faceSet_disjoint_iff a.val.1 b.val.1

theorem regionCandidate_profile {D : RelGenSet G Lambda} {eps : ℕ}
    (a : Avoiding Delta j D eps) :
    RegionCandidate.SameTargetProfile (regionCandidate Delta j hlen a) a.val :=
  And.intro Option.map_eq_none_iff
    (And.intro (contiguityGeometry_target_start Delta j hlen a.property a.val.2)
      (And.intro (contiguityGeometry_target_length Delta j hlen a.property a.val.2)
        (contiguityGeometry_source_length Delta j hlen a.property a.val.2)))

noncomputable def regionFamilyEmbedding {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, Delta.toCombMap.faceOf
      (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j)) ∉ a.1) :
    family ↪ RegionCandidate D eps (diagram Delta j hlen) where
  toFun a := regionCandidate Delta j hlen ⟨a.val, havoid a.val a.property⟩
  inj' a b h := by
    apply Subtype.ext
    exact congrArg (fun x : Avoiding Delta j D eps => x.val)
      (regionCandidate_injective Delta j hlen h)

/-- **A family avoiding the face across `w_j`, after the thickening.** -/
noncomputable def regionFamily {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, Delta.toCombMap.faceOf
      (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j)) ∉ a.1) :
    Finset (RegionCandidate D eps (diagram Delta j hlen)) :=
  family.attach.map (regionFamilyEmbedding Delta j hlen family havoid)

theorem regionFamily_profile {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, Delta.toCombMap.faceOf
      (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j)) ∉ a.1)
    {a : RegionCandidate D eps (diagram Delta j hlen)}
    (ha : a ∈ regionFamily Delta j hlen family havoid) :
    ∃ b ∈ family, RegionCandidate.SameTargetProfile a b := by
  obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp ha
  exact ⟨b.val, b.property, regionCandidate_profile Delta j hlen _⟩

theorem regionFamily_card {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, Delta.toCombMap.faceOf
      (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j)) ∉ a.1) :
    (regionFamily Delta j hlen family havoid).card = family.card := by
  simp only [regionFamily, Finset.card_map, Finset.card_attach]

theorem regionFamily_weight {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, Delta.toCombMap.faceOf
      (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j)) ∉ a.1) :
    EstimatingSelection.familyWeight RegionCandidate.weight
        (regionFamily Delta j hlen family havoid) =
      EstimatingSelection.familyWeight RegionCandidate.weight family := by
  unfold EstimatingSelection.familyWeight regionFamily
  rw [Finset.sum_map]
  trans ∑ a ∈ family.attach, RegionCandidate.weight a.val
  · apply Finset.sum_congr rfl
    intro a _
    exact regionCandidate_weight Delta j hlen ⟨a.val, havoid a.val a.property⟩
  · exact Finset.sum_attach _ _

theorem regionFamily_pairwise {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, Delta.toCombMap.faceOf
      (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j)) ∉ a.1)
    (hcompat : EstimatingSelection.PairwiseCompatible RegionCandidate.Compatible family) :
    EstimatingSelection.PairwiseCompatible RegionCandidate.Compatible
      (regionFamily Delta j hlen family havoid) := by
  intro x hx y hy hne
  obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp hy
  apply (regionCandidate_compatible Delta j hlen
    ⟨a.val, havoid a.val a.property⟩ ⟨b.val, havoid b.val b.property⟩).mpr
  apply hcompat a.val a.property b.val b.property
  intro hab
  exact hne (congrArg (regionFamilyEmbedding Delta j hlen family havoid) (Subtype.ext hab))

/-- The old regions correspond to the transported ones. -/
noncomputable def regionFamilyEquiv {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, Delta.toCombMap.faceOf
      (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j)) ∉ a.1) :
    family ≃ regionFamily Delta j hlen family havoid :=
  Equiv.ofBijective (fun a => ⟨regionFamilyEmbedding Delta j hlen family havoid a,
      Finset.mem_map_of_mem _ (Finset.mem_attach family a)⟩)
    (And.intro (fun a b h => (regionFamilyEmbedding Delta j hlen family havoid).injective
        (congrArg Subtype.val h))
      (fun x => by
        obtain ⟨a, _, ha⟩ := Finset.mem_map.mp x.property
        exact ⟨a, Subtype.ext ha⟩))

theorem regionFamilyEquiv_profile {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, Delta.toCombMap.faceOf
      (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j)) ∉ a.1)
    (a : family) :
    RegionCandidate.SameTargetProfile (regionFamilyEquiv Delta j hlen family havoid a).1 a.1 :=
  regionCandidate_profile Delta j hlen ⟨a.val, havoid a.val a.property⟩

theorem regionFamilyEquiv_source {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, Delta.toCombMap.faceOf
      (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j)) ∉ a.1)
    (a : family) :
    (regionFamilyEquiv Delta j hlen family havoid a).1.2.source.val = a.1.2.source.val :=
  rfl

/-- When `w_j` is a spur, the face across it is the exterior, which no region contains. -/
theorem spur_avoid {D : RelGenSet G Lambda} {eps : ℕ}
    (hspur : Delta.toCombMap.faceOf
      (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j)) = Delta.outerFace)
    (family : Finset (RegionCandidate D eps Delta)) :
    ∀ a ∈ family, Delta.toCombMap.faceOf
      (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j)) ∉ a.1 :=
  fun a _ => by
    rw [hspur]
    exact outer_not_mem Delta a.2

theorem dartImage_ne_none (e : Delta.toCombMap.Dart) :
    FaceEdgeDoubling.dartImage Delta Delta.outerFace j hlen e ≠ none := by
  unfold FaceEdgeDoubling.dartImage
  split_ifs <;> exact Option.some_ne_none _

/-- The new exterior consists of the images of the old exterior darts. -/
theorem faceOf_eq_outer_iff (x : (diagram Delta j hlen).toCombMap.Dart) :
    (diagram Delta j hlen).toCombMap.faceOf x = (diagram Delta j hlen).outerFace ↔
      ∃ d, Delta.toCombMap.faceOf d = Delta.outerFace ∧
        FaceEdgeDoubling.dartImage Delta Delta.outerFace j hlen d = x := by
  refine ((FaceEdgeDoubling.boundary Delta Delta.outerFace j hlen
    (FaceEdgeDoubling.cellFace Delta Delta.outerFace j hlen)).mem_iff x).symm.trans ?_
  rw [FaceEdgeDoubling.boundary_cellFace_darts, List.mem_map]
  exact exists_congr fun d => and_congr ((Delta.faceBoundary Delta.outerFace).mem_iff d) Iff.rfl

/-- **An outer spur of the thickening is an old outer spur other than `w_j`.** -/
theorem exists_of_isOuterSpur {x : (diagram Delta j hlen).toCombMap.Dart}
    (hx : IsOuterSpur (diagram Delta j hlen) x) :
    ∃ d, embed Delta.toCombMap d = x ∧ IsOuterSpur Delta d ∧
      d ≠ FaceEdgeDoubling.dart Delta Delta.outerFace j := by
  obtain ⟨d, hd, hdx⟩ := (faceOf_eq_outer_iff Delta j hlen x).mp hx.1
  obtain ⟨e, he, hex⟩ := (faceOf_eq_outer_iff Delta j hlen _).mp hx.2
  by_cases hdd : d = FaceEdgeDoubling.dart Delta Delta.outerFace j
  · rw [FaceEdgeDoubling.dartImage, if_pos hdd] at hdx
    subst hdx
    change _ = none at hex
    exact (dartImage_ne_none Delta j hlen e hex).elim
  · rw [FaceEdgeDoubling.dartImage, if_neg hdd] at hdx
    subst hdx
    by_cases hed : e = FaceEdgeDoubling.dart Delta Delta.outerFace j
    · rw [FaceEdgeDoubling.dartImage, if_pos hed] at hex
      change _ = embed Delta.toCombMap (Delta.toCombMap.alpha d) at hex
      exact (Option.some_ne_none _ (Option.some.inj hex).symm).elim
    · rw [FaceEdgeDoubling.dartImage, if_neg hed] at hex
      change _ = embed Delta.toCombMap (Delta.toCombMap.alpha d) at hex
      have hea : e = Delta.toCombMap.alpha d := embed_injective Delta.toCombMap hex
      subst hea
      exact ⟨d, rfl, And.intro hd he, hdd⟩

/-- **Thickening a spur removes it and creates none.** -/
theorem outerSpurCount_lt
    (hspur : Delta.toCombMap.faceOf
      (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j)) = Delta.outerFace) :
    outerSpurCount (diagram Delta j hlen) < outerSpurCount Delta := by
  have hmem : FaceEdgeDoubling.dart Delta Delta.outerFace j ∈
      Finset.univ.filter (IsOuterSpur Delta) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      And.intro (FaceEdgeDoubling.dart_face Delta Delta.outerFace j) hspur⟩
  unfold outerSpurCount
  refine lt_of_le_of_lt ?_ (Finset.card_erase_lt_of_mem hmem)
  refine Finset.card_le_card_of_injOn
    (fun x : (diagram Delta j hlen).toCombMap.Dart =>
      (Option.bind x id).getD (FaceEdgeDoubling.dart Delta Delta.outerFace j)) ?_ ?_
  · intro x hx
    obtain ⟨d, rfl, hd, hne⟩ :=
      exists_of_isOuterSpur Delta j hlen (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
    exact Finset.mem_coe.mpr
      (Finset.mem_erase.mpr ⟨hne, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩⟩)
  · intro x hx y hy hxy
    obtain ⟨d, rfl, -, -⟩ :=
      exists_of_isOuterSpur Delta j hlen (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
    obtain ⟨e, rfl, -, -⟩ :=
      exists_of_isOuterSpur Delta j hlen (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
    exact congrArg (embed Delta.toCombMap) hxy

/-- A spur needs two darts on the exterior. -/
theorem one_lt_length_of_isOuterSpur {x : Delta.toCombMap.Dart} (hx : IsOuterSpur Delta x) :
    1 < (Delta.faceBoundary Delta.outerFace).darts.length := by
  have h1 := ((Delta.faceBoundary Delta.outerFace).mem_iff x).mpr hx.1
  have h2 := ((Delta.faceBoundary Delta.outerFace).mem_iff _).mpr hx.2
  generalize (Delta.faceBoundary Delta.outerFace).darts = l at h1 h2 ⊢
  rcases l with _ | ⟨_, _ | ⟨_, _⟩⟩
  · exact absurd h1 List.not_mem_nil
  · rw [List.mem_singleton] at h1 h2
    exact absurd (h2.trans h1.symm) (Delta.toCombMap.alpha_fixedPointFree x)
  · exact Nat.succ_lt_succ (Nat.succ_pos _)

end Thickening

section Family

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **A distinguished section family across the thickening of an outer spur.**  The weight
and the number of regions are unchanged and the labels stay legal, so the transported family
is again optimal. -/
noncomputable def sectionFamily (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (j : Fin (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
    (hlen : 1 < (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
    (hspur : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha
      (FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)) = S.diagram.outerFace) :
    GloballyDistinguishedSectionFamily D lambda c eps Delta cuts where
  diagram := diagram S.diagram j hlen
  equiv := S.equiv.trans (oEquivalent S.diagram j hlen)
  reduced := reduced S.diagram j hlen S.reduced
  family := regionFamily S.diagram j hlen S.family (spur_avoid S.diagram j hspur S.family)
  pairwise := regionFamily_pairwise S.diagram j hlen S.family
    (spur_avoid S.diagram j hspur S.family) S.pairwise
  respects := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := regionFamily_profile S.diagram j hlen S.family
      (spur_avoid S.diagram j hspur S.family) ha
    exact RegionCandidate.respectsSections_of_sameTargetProfile cuts hab (S.respects b hb)
  nondegenerate := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := regionFamily_profile S.diagram j hlen S.family
      (spur_avoid S.diagram j hspur S.family) ha
    obtain ⟨hs, ht⟩ := S.nondegenerate b hb
    exact ⟨lt_of_lt_of_eq hs hab.2.2.2.symm, lt_of_lt_of_eq ht hab.2.2.1.symm⟩
  label_admissible := label_admissible S.diagram j hlen (symmetricLabelAlphabet D)
    (symmetricLabelAlphabet.symmetric D) S.label_admissible
  weight_maximal other hother :=
    (S.weight_maximal other hother).trans_eq
      (regionFamily_weight S.diagram j hlen S.family (spur_avoid S.diagram j hspur S.family)).symm
  card_minimal other hother hweight :=
    (regionFamily_card S.diagram j hlen S.family (spur_avoid S.diagram j hspur S.family)).trans_le
      (S.card_minimal other hother (hweight.trans
        (regionFamily_weight S.diagram j hlen S.family (spur_avoid S.diagram j hspur S.family))))

/-- **Induction on the number of outer spurs.** -/
theorem exists_spurFree (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) :
    ∃ (S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
      (e : S.family ≃ S'.family),
      Nonempty (OEquivalentDiscDiagram S.diagram S'.diagram) ∧
        (∀ x, ¬ IsOuterSpur S'.diagram x) ∧
          S'.toRealizedSectionFamily.weight = S.toRealizedSectionFamily.weight ∧
            ∀ a, RegionCandidate.SameTargetProfile (e a).1 a.1 ∧
              (e a).1.2.source.val = a.1.2.source.val := by
  generalize hn : outerSpurCount S.diagram = n
  induction n using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    by_cases hspur : ∃ x, IsOuterSpur S.diagram x
    · obtain ⟨x, hx⟩ := hspur
      have hlen := one_lt_length_of_isOuterSpur S.diagram hx
      obtain ⟨j, hj⟩ := List.get_of_mem
        (((S.diagram.faceBoundary S.diagram.outerFace).mem_iff x).mpr hx.1)
      have hspur2 : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha
          (FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)) = S.diagram.outerFace := by
        rw [FaceEdgeDoubling.dart_eq_get, hj]
        exact hx.2
      have havoid := spur_avoid S.diagram j hspur2 S.family
      obtain ⟨S', e, ⟨equiv'⟩, hfree, hweight, hprofile⟩ :=
        ih _ (lt_of_lt_of_eq (outerSpurCount_lt S.diagram j hlen hspur2) hn)
          (sectionFamily S j hlen hspur2) rfl
      refine ⟨S', (regionFamilyEquiv S.diagram j hlen S.family havoid).trans e,
        ⟨(oEquivalent S.diagram j hlen).trans equiv'⟩, hfree,
        hweight.trans (regionFamily_weight S.diagram j hlen S.family havoid), fun a => ?_⟩
      obtain ⟨hprof, hsource⟩ := hprofile (regionFamilyEquiv S.diagram j hlen S.family havoid a)
      exact And.intro (hprof.trans (regionFamilyEquiv_profile S.diagram j hlen S.family havoid a))
        (hsource.trans (regionFamilyEquiv_source S.diagram j hlen S.family havoid a))
    · exact ⟨S, Equiv.refl _, ⟨OEquivalentDiscDiagram.refl _⟩, fun x hx => hspur ⟨x, hx⟩, rfl,
        fun _ => And.intro (And.intro Iff.rfl (And.intro rfl (And.intro rfl rfl))) rfl⟩

end Family

theorem outerSpurThickening : OuterSpurThickeningStatement.{u, w, v} := by
  unfold OuterSpurThickeningStatement
  intro _ _ _ _ _ _ _ _ _ _ S
  exact exists_spurFree S

end GroupApproximation.GGT.VanKampen.OuterSpurThickening

#audit_closed_axioms GroupApproximation.GGT.VanKampen.OuterSpurThickening.outerSpurThickening
#audit_axioms GroupApproximation.GGT.VanKampen.OuterSpurThickening.diagram
#audit_axioms GroupApproximation.GGT.VanKampen.OuterSpurThickening.oEquivalent
#audit_axioms GroupApproximation.GGT.VanKampen.OuterSpurThickening.embedding
#audit_axioms GroupApproximation.GGT.VanKampen.OuterSpurThickening.outerDarts_eq
#audit_axioms GroupApproximation.GGT.VanKampen.OuterSpurThickening.contiguityGeometry
#audit_axioms GroupApproximation.GGT.VanKampen.OuterSpurThickening.regionFamily_weight
#audit_axioms GroupApproximation.GGT.VanKampen.OuterSpurThickening.regionFamilyEquiv
#audit_axioms GroupApproximation.GGT.VanKampen.OuterSpurThickening.outerSpurCount_lt
#audit_axioms GroupApproximation.GGT.VanKampen.OuterSpurThickening.sectionFamily
#audit_axioms GroupApproximation.GGT.VanKampen.OuterSpurThickening.exists_spurFree
