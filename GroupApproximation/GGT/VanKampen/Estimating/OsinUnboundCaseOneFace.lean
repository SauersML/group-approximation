import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundCaseOne
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PlanarPieces
import GroupApproximation.Meta.AxiomGuard

/-!
# Case 1 of Osin's Lemma 9.4 on an unselected face

In Case 1 of the proof of Osin's Appendix Lemma 9.4 (arXiv:math/0411039v3), two connector
words cut a quadrilateral out of a component polygon, and the quadrilateral is a new contiguity
region that contradicts the maximality of the selected system.  A polygon is an unselected
`G`-face of the optimal diagram (`OsinLemma94RealizedPolygons`), and its walk is read from the
corner where the quadrilateral starts.

`GFaceWordInsertion.exists_quadrilateral_region` reads the walk from position `0`, on a face
with no internally paired dart.  A polygon may have internally paired darts, and the
quadrilateral starts at no particular position of its walk.
`exists_quadrilateral_region_rotate` drops both requirements.  The surgery uses the absence of
internally paired darts only for the darts of the two arcs, and across such a dart lies a relator
cell or the outer face, never `f`.  The theorem also records that the new region runs from a cell
to itself exactly when the target cell is the source cell.

`RealizedSectionFamily.false_of_quadrilateral_face` is the weight contradiction on the diagram
of the family itself, with no collapse of a `G`-region first.

`OsinLemma94CaseOneSameCellStatement` is Case 1 for the connector pairs whose two sides have the
same kind, where the new region can run from a relator cell to itself.  It is a named hypothesis.
-/

namespace GroupApproximation.GGT.VanKampen.GFaceWordInsertion

open GroupApproximation.GGT.VanKampen.Embedded
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}

theorem forwardOffset_of_val_eq_mod {M : CombMap.{v}} {g : M.Face} (B : FaceBoundary M g)
    {start finish : Fin B.darts.length} {k : ℕ} (hk : k < B.darts.length)
    (hfinish : finish.val = (start.val + k) % B.darts.length) :
    B.forwardOffset start finish = k := by
  have hs := start.isLt
  unfold FaceBoundary.forwardOffset
  by_cases hlt : start.val + k < B.darts.length
  · rw [Nat.mod_eq_of_lt hlt] at hfinish
    split <;> omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hfinish
    split <;> omega

/-- Across a dart of a reversed relator-cell arc lies that relator cell. -/
theorem faceOf_alpha_ne_of_mem_reverseDarts (Delta : DiscDiagram.{u, w, v} W)
    {f : Delta.toCombMap.Face} (hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ f)
    (i : Fin Delta.rCellCount) (arc : CyclicArc (cellDarts Delta i))
    {z : Delta.toCombMap.Dart} (hz : z ∈ arc.reverseDarts) :
    Delta.toCombMap.faceOf (Delta.toCombMap.alpha z) ≠ f := by
  have hz' : z ∈ arc.darts.reverse.map Delta.toCombMap.alpha := hz
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hz'
  have hcyc : e ∈ (Delta.faceBoundary (cell Delta i).face).darts :=
    arc.mem_cycle_of_mem_darts (List.mem_reverse.mp he)
  rw [Delta.toCombMap.alpha_involutive e, ((Delta.faceBoundary _).mem_iff e).mp hcyc]
  exact hcells _ (List.get_mem _ _)

/-- Across a dart of a target arc, as a region boundary reads it, lies the target cell or the
outer face. -/
theorem faceOf_alpha_ne_of_mem_targetBoundaryDarts (Delta : DiscDiagram.{u, w, v} W)
    {f : Delta.toCombMap.Face} (hf : f ≠ Delta.outerFace)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ f)
    (target : Option (Fin Delta.rCellCount)) (arc : CyclicArc (targetDarts Delta target))
    {z : Delta.toCombMap.Dart} (hz : z ∈ targetBoundaryDarts Delta target arc) :
    Delta.toCombMap.faceOf (Delta.toCombMap.alpha z) ≠ f := by
  cases target with
  | none =>
    have hcyc : z ∈ (Delta.faceBoundary Delta.outerFace).darts.reverse.map
        Delta.toCombMap.alpha := arc.mem_cycle_of_mem_darts hz
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hcyc
    rw [Delta.toCombMap.alpha_involutive e,
      ((Delta.faceBoundary _).mem_iff e).mp (List.mem_reverse.mp he)]
    exact hf.symm
  | some j => exact faceOf_alpha_ne_of_mem_reverseDarts Delta hcells j arc hz

theorem option_map_map_equiv_eq_some_iff {α β γ : Type*} (e₁ : α ≃ β) (e₂ : β ≃ γ)
    (o : Option α) (a : α) : (o.map e₁).map e₂ = some (e₂ (e₁ a)) ↔ o = some a := by
  cases o <;> simp

/-- **The quadrilateral region of Lemma 9.4 Case 1, on a rotated walk.**  As
`exists_quadrilateral_region`, but the walk of `f` is read from any position `r`, and `f` may
have internally paired darts.  The new region runs from a cell to itself exactly when the
target cell is the source cell. -/
theorem exists_quadrilateral_region_rotate (D E : RelGenSet G Lambda) (eps : ℕ)
    (Delta : DiscDiagram.{u, w, v} W) (hlabel : ∀ d, E.IsLetter (Delta.label d))
    (f : Delta.toCombMap.Face) (hf : f ≠ Delta.outerFace)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ f)
    (source : Fin Delta.rCellCount) (target : Option (Fin Delta.rCellCount))
    (sourceArc : CyclicArc (cellDarts Delta source))
    (targetArc : CyclicArc (targetDarts Delta target))
    (X Y : List Delta.toCombMap.Dart) (r : ℕ)
    (htrav : (Delta.faceBoundary f).darts.rotate r =
      X ++ targetBoundaryDarts Delta target targetArc ++ Y ++ sourceArc.reverseDarts)
    (hsource : 0 < sourceArc.length)
    (s1 s2 : List (RelLetter G Lambda)) (hne1 : s1 ≠ []) (hne2 : s2 ≠ [])
    (hadm1 : HullSC.RelWord.IsAdmissible E s1)
    (hinv1 : ∀ l ∈ s1, E.IsLetter (HullSC.RelWord.inv l))
    (hadm2 : HullSC.RelWord.IsAdmissible E s2)
    (hinv2 : ∀ l ∈ s2, E.IsLetter (HullSC.RelWord.inv l))
    (hval1 : RelLetter.listVal s1 = RelLetter.listVal (dartWord Delta X))
    (hval2 : RelLetter.listVal s2 = RelLetter.listVal (dartWord Delta Y))
    (hlen1 : s1.length ≤ eps) (hlen2 : s2.length ≤ eps)
    (hnorm1 : WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal s1) ≤ eps)
    (hnorm2 : WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal s2) ≤ eps) :
    ∃ Xi : DiscDiagram.{u, w, v} W, Nonempty (OEquivalentDiscDiagram Delta Xi) ∧
      (Delta.Reduced → Xi.Reduced) ∧ (∀ d, E.IsLetter (Xi.label d)) ∧
      ∃ (Q : Xi.toCombMap.Face) (H : ContiguityGeometry D eps Xi {Q}),
        H.sourceArc.length = sourceArc.length ∧ H.targetArc.length = targetArc.length ∧
        (H.target = none ↔ target = none) ∧ H.targetArc.start.val = targetArc.start.val ∧
        (H.target = some H.source ↔ target = some source) ∧
        ∀ family : Finset (RegionCandidate D eps Delta), (∀ a ∈ family, f ∉ a.1) →
          EstimatingSelection.PairwiseCompatible RegionCandidate.Compatible family →
          ∃ family' : Finset (RegionCandidate D eps Xi),
            EstimatingSelection.PairwiseCompatible RegionCandidate.Compatible family' ∧
            family'.card = family.card ∧
            EstimatingSelection.familyWeight RegionCandidate.weight family' =
              EstimatingSelection.familyWeight RegionCandidate.weight family ∧
            (∀ a ∈ family', Q ∉ a.1) ∧
            ∀ a ∈ family', ∃ b ∈ family, RegionCandidate.SameTargetProfile a b := by
  have hPlen : sourceArc.reverseDarts.length = sourceArc.length := by
    simp only [CyclicArc.reverseDarts, List.length_map, List.length_reverse,
      CyclicArc.darts_length]
  have htravLen : (Delta.faceBoundary f).darts.length =
      X.length + (targetBoundaryDarts Delta target targetArc).length + Y.length +
        sourceArc.reverseDarts.length := by
    simpa only [List.length_rotate, List.length_append] using congrArg List.length htrav
  /- The first split, at the corners before and after `X`. -/
  have hn : 0 < (Delta.faceBoundary f).darts.length := by omega
  have hXlt : X.length < (Delta.faceBoundary f).darts.length := by omega
  let start1 : Fin (Delta.faceBoundary f).darts.length :=
    ⟨r % (Delta.faceBoundary f).darts.length, Nat.mod_lt _ hn⟩
  let finish1 : Fin (Delta.faceBoundary f).darts.length :=
    ⟨(start1.val + X.length) % (Delta.faceBoundary f).darts.length, Nat.mod_lt _ hn⟩
  have hoff1 : (Delta.faceBoundary f).forwardOffset start1 finish1 = X.length :=
    forwardOffset_of_val_eq_mod _ hXlt rfl
  have hvalue1 : RelLetter.listVal s1 = RelLetter.listVal
      ((((Delta.faceBoundary f).darts.rotate start1.val).take
        ((Delta.faceBoundary f).forwardOffset start1 finish1)).map Delta.label) := by
    rw [hoff1]
    change _ = RelLetter.listVal ((((Delta.faceBoundary f).darts.rotate
      (r % (Delta.faceBoundary f).darts.length)).take X.length).map Delta.label)
    rw [List.rotate_mod, htrav, List.append_assoc, List.append_assoc, List.take_left]
    exact hval1
  obtain ⟨R1⟩ := exists_split_corner_output E Delta hlabel f hf hcells start1 finish1 s1 hne1
    hadm1 hinv1 hvalue1
  let E1 := CornerOutput.originalEmbedding R1.toCellOutput
  let C1 : Surgery.OrderedRCellMap Delta R1.diagram E1.faces :=
    CornerOutput.originalCellMap R1.toCellOutput
  have hS : (R1.diagram.faceBoundary R1.suffixSide).darts =
      R1.darts ++ (targetBoundaryDarts Delta target targetArc ++
        (Y ++ sourceArc.reverseDarts)).map E1.darts := by
    have h1 := R1.suffixSide_darts_original
    have h2 : ((Delta.faceBoundary f).darts.rotate start1.val).drop
        ((Delta.faceBoundary f).forwardOffset start1 finish1) =
          targetBoundaryDarts Delta target targetArc ++ (Y ++ sourceArc.reverseDarts) := by
      rw [hoff1]
      change ((Delta.faceBoundary f).darts.rotate
        (r % (Delta.faceBoundary f).darts.length)).drop X.length = _
      rw [List.rotate_mod, htrav, List.append_assoc, List.append_assoc, List.drop_left]
    rw [h2] at h1
    exact h1
  have hf2 : R1.suffixSide ≠ R1.diagram.outerFace := fun h =>
    R1.suffixSide_not_kept Delta.outerFace hf.symm (E1.outer.symm.trans h.symm)
  have hcells2 : ∀ C ∈ R1.diagram.relatorCells, C.face ≠ R1.suffixSide := by
    intro C hC
    rw [C1.list_eq] at hC
    obtain ⟨C0, hC0, rfl⟩ := List.mem_map.mp hC
    rw [C1.face_eq]
    exact R1.suffixSide_not_kept _ (hcells C0 hC0)
  /- The second split, across the first suffix side, at the corners before and after `Y`. -/
  have hSlen : (R1.diagram.faceBoundary R1.suffixSide).darts.length =
      R1.darts.length + (targetBoundaryDarts Delta target targetArc).length + Y.length +
        sourceArc.reverseDarts.length := by
    rw [hS]
    simp only [List.length_append, List.length_map]
    omega
  have hstart2 : R1.darts.length + (targetBoundaryDarts Delta target targetArc).length <
      (R1.diagram.faceBoundary R1.suffixSide).darts.length := by omega
  have hfinish2 : R1.darts.length + (targetBoundaryDarts Delta target targetArc).length +
      Y.length < (R1.diagram.faceBoundary R1.suffixSide).darts.length := by omega
  let start2 : Fin (R1.diagram.faceBoundary R1.suffixSide).darts.length := ⟨_, hstart2⟩
  let finish2 : Fin (R1.diagram.faceBoundary R1.suffixSide).darts.length := ⟨_, hfinish2⟩
  have hoff2 : (R1.diagram.faceBoundary R1.suffixSide).forwardOffset start2 finish2 = Y.length :=
    (forwardOffset_of_le _ (Nat.le_add_right _ _)).trans (Nat.add_sub_cancel_left _ _)
  have hrot2 : (R1.diagram.faceBoundary R1.suffixSide).darts.rotate start2.val =
      Y.map E1.darts ++ (sourceArc.reverseDarts.map E1.darts ++
        (R1.darts ++ (targetBoundaryDarts Delta target targetArc).map E1.darts)) := by
    change (R1.diagram.faceBoundary R1.suffixSide).darts.rotate
      (R1.darts.length + (targetBoundaryDarts Delta target targetArc).length) = _
    have hsplit : R1.darts ++ (targetBoundaryDarts Delta target targetArc ++
        (Y ++ sourceArc.reverseDarts)).map E1.darts =
          (R1.darts ++ (targetBoundaryDarts Delta target targetArc).map E1.darts) ++
            (Y.map E1.darts ++ sourceArc.reverseDarts.map E1.darts) := by
      simp only [List.map_append, List.append_assoc]
    rw [hS, hsplit, show R1.darts.length + (targetBoundaryDarts Delta target targetArc).length =
        (R1.darts ++ (targetBoundaryDarts Delta target targetArc).map E1.darts).length by
      simp only [List.length_append, List.length_map],
      List.rotate_append_length_eq, List.append_assoc]
  have hvalue2 : RelLetter.listVal s2 = RelLetter.listVal
      ((((R1.diagram.faceBoundary R1.suffixSide).darts.rotate start2.val).take
        ((R1.diagram.faceBoundary R1.suffixSide).forwardOffset start2 finish2)).map
          R1.diagram.label) := by
    rw [hoff2, hrot2, List.take_left' (by simp only [List.length_map])]
    exact hval2.trans (congrArg RelLetter.listVal (E1.dartWord_map Y).symm)
  obtain ⟨R2⟩ := exists_split_corner_output E R1.diagram R1.label_admissible R1.suffixSide hf2
    hcells2 start2 finish2 s2 hne2 hadm2 hinv2 hvalue2
  let E2 := CornerOutput.originalEmbedding R2.toCellOutput
  let C2 : Surgery.OrderedRCellMap R1.diagram R2.diagram E2.faces :=
    CornerOutput.originalCellMap R2.toCellOutput
  have hQ : (R2.diagram.faceBoundary R2.suffixSide).darts =
      R2.darts ++ (sourceArc.reverseDarts.map E1.darts ++
        (R1.darts ++ (targetBoundaryDarts Delta target targetArc).map E1.darts)).map E2.darts := by
    have h1 := R2.suffixSide_darts_original
    have h2 : ((R1.diagram.faceBoundary R1.suffixSide).darts.rotate start2.val).drop
        ((R1.diagram.faceBoundary R1.suffixSide).forwardOffset start2 finish2) =
          sourceArc.reverseDarts.map E1.darts ++
            (R1.darts ++ (targetBoundaryDarts Delta target targetArc).map E1.darts) := by
      rw [hoff2, hrot2, List.drop_left' (by simp only [List.length_map])]
    rw [h2] at h1
    exact h1
  /- The face `Q`. -/
  have hQout : R2.suffixSide ≠ R2.diagram.outerFace := fun h =>
    R2.suffixSide_not_kept R1.diagram.outerFace hf2.symm (E2.outer.symm.trans h.symm)
  have hQval : RelLetter.listVal (R2.diagram.faceWord R2.suffixSide) = 1 := by
    rcases R2.diagram.inner_face R2.suffixSide hQout with ⟨C, hC, hface⟩ | hone
    · exfalso
      rw [C2.list_eq] at hC
      obtain ⟨C0, hC0, rfl⟩ := List.mem_map.mp hC
      rw [C2.face_eq] at hface
      exact R2.suffixSide_not_kept _ (hcells2 C0 hC0) hface
    · exact hone
  have hold_face : ∀ z, Delta.toCombMap.faceOf (Delta.toCombMap.alpha z) ≠ f →
      R1.diagram.toCombMap.faceOf (R1.diagram.toCombMap.alpha (E1.darts z)) ≠
        R1.suffixSide := by
    intro z hg
    rw [E1.alpha, E1.faceOf_darts hg]
    exact R1.suffixSide_not_kept _ hg
  have hnoQ : Surgery.MapCollapse.NoInternalFaceDart R2.diagram.toCombMap R2.suffixSide := by
    intro x hx halpha
    have hmem : x ∈ (R2.diagram.faceBoundary R2.suffixSide).darts :=
      ((R2.diagram.faceBoundary _).mem_iff x).mpr hx
    rw [hQ] at hmem
    rcases List.mem_append.mp hmem with hpath | hrest
    · have hpre : R2.diagram.toCombMap.alpha x ∈
          (R2.diagram.faceBoundary R2.prefixSide).darts := by
        rw [R2.prefixSide_darts_original]
        exact List.mem_append_left _ (List.mem_map.mpr ⟨x, List.mem_reverse.mpr hpath, rfl⟩)
      exact R2.prefixSide_ne_suffixSide
        ((((R2.diagram.faceBoundary _).mem_iff _).mp hpre).symm.trans halpha)
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hrest
      have hyS : R1.diagram.toCombMap.faceOf (R1.diagram.toCombMap.alpha y) ≠
          R1.suffixSide := by
        rcases List.mem_append.mp hy with hyP | hyrest
        · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hyP
          exact hold_face z (faceOf_alpha_ne_of_mem_reverseDarts Delta hcells source sourceArc hz)
        · rcases List.mem_append.mp hyrest with hys1 | hyT
          · have hpre1 : R1.diagram.toCombMap.alpha y ∈
                (R1.diagram.faceBoundary R1.prefixSide).darts := by
              rw [R1.prefixSide_darts_original]
              exact List.mem_append_left _
                (List.mem_map.mpr ⟨y, List.mem_reverse.mpr hys1, rfl⟩)
            rw [((R1.diagram.faceBoundary _).mem_iff _).mp hpre1]
            exact R1.prefixSide_ne_suffixSide
          · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hyT
            exact hold_face z
              (faceOf_alpha_ne_of_mem_targetBoundaryDarts Delta hf hcells target targetArc hz)
      rw [E2.alpha, E2.faceOf_darts hyS] at halpha
      exact R2.suffixSide_not_kept _ hyS halpha
  have hdecomp : (R2.diagram.faceBoundary R2.suffixSide).darts.rotate R2.darts.length =
      ((sourceArc.mapTo E1.darts (E1.cellDarts_eq C1 hcells source)).mapTo E2.darts
          (E2.cellDarts_eq C2 hcells2 (C1.indexEquiv source))).reverseDarts ++
        R1.darts.map E2.darts ++
        targetBoundaryDarts R2.diagram ((target.map C1.indexEquiv).map C2.indexEquiv)
          ((targetArc.mapTo E1.darts (E1.targetDarts_eq C1 hcells hf target)).mapTo E2.darts
            (E2.targetDarts_eq C2 hcells2 hf2 (target.map C1.indexEquiv))) ++
        R2.darts := by
    rw [hQ, List.rotate_append_length_eq, E2.reverseDarts_mapTo, E1.reverseDarts_mapTo,
      E2.targetBoundaryDarts_map C2 hcells2 hf2, E1.targetBoundaryDarts_map C1 hcells hf]
    simp only [List.map_append, List.append_assoc]
  have hright : (R1.darts.map E2.darts).length ≤ eps := by
    rw [List.length_map, R1.length_eq]
    exact hlen1
  have hleft : R2.darts.length ≤ eps := by
    rw [R2.length_eq]
    exact hlen2
  have hrightNorm : WordMetric.wordNorm D.alphabet.carrier
      (RelLetter.listVal (dartWord R2.diagram (R1.darts.map E2.darts))) ≤ eps := by
    rw [E2.dartWord_map]
    change WordMetric.wordNorm D.alphabet.carrier
      (RelLetter.listVal (R1.darts.map R1.diagram.label)) ≤ eps
    rw [R1.word_eq]
    exact hnorm1
  have hleftNorm : WordMetric.wordNorm D.alphabet.carrier
      (RelLetter.listVal (dartWord R2.diagram R2.darts)) ≤ eps := by
    change WordMetric.wordNorm D.alphabet.carrier
      (RelLetter.listVal (R2.darts.map R2.diagram.label)) ≤ eps
    rw [R2.word_eq]
    exact hnorm2
  let H : ContiguityGeometry D eps R2.diagram {R2.suffixSide} :=
    ContiguityGeometry.ofSingletonFace R2.suffixSide hQout hQval hnoQ R2.darts.length
      (C2.indexEquiv (C1.indexEquiv source)) ((target.map C1.indexEquiv).map C2.indexEquiv)
      ((sourceArc.mapTo E1.darts (E1.cellDarts_eq C1 hcells source)).mapTo E2.darts
        (E2.cellDarts_eq C2 hcells2 (C1.indexEquiv source)))
      ((targetArc.mapTo E1.darts (E1.targetDarts_eq C1 hcells hf target)).mapTo E2.darts
        (E2.targetDarts_eq C2 hcells2 hf2 (target.map C1.indexEquiv)))
      (R1.darts.map E2.darts) R2.darts hdecomp hright hleft hrightNorm hleftNorm
  have hHsource : H.sourceArc.length = sourceArc.length :=
    (CyclicArc.mapTo_length (sourceArc.mapTo E1.darts (E1.cellDarts_eq C1 hcells source))
      E2.darts (E2.cellDarts_eq C2 hcells2 (C1.indexEquiv source))).trans
      (CyclicArc.mapTo_length sourceArc E1.darts (E1.cellDarts_eq C1 hcells source))
  have hHtarget : H.targetArc.length = targetArc.length :=
    (CyclicArc.mapTo_length (targetArc.mapTo E1.darts (E1.targetDarts_eq C1 hcells hf target))
      E2.darts (E2.targetDarts_eq C2 hcells2 hf2 (target.map C1.indexEquiv))).trans
      (CyclicArc.mapTo_length targetArc E1.darts (E1.targetDarts_eq C1 hcells hf target))
  have hHstart : H.targetArc.start.val = targetArc.start.val :=
    (CyclicArc.mapTo_start (targetArc.mapTo E1.darts (E1.targetDarts_eq C1 hcells hf target))
      E2.darts (E2.targetDarts_eq C2 hcells2 hf2 (target.map C1.indexEquiv))).trans
      (CyclicArc.mapTo_start targetArc E1.darts (E1.targetDarts_eq C1 hcells hf target))
  have hHnone : H.target = none ↔ target = none := by
    change (target.map C1.indexEquiv).map C2.indexEquiv = none ↔ target = none
    simp only [Option.map_eq_none_iff]
  have hHloop : H.target = some H.source ↔ target = some source := by
    change (target.map C1.indexEquiv).map C2.indexEquiv =
      some (C2.indexEquiv (C1.indexEquiv source)) ↔ target = some source
    exact option_map_map_equiv_eq_some_iff C1.indexEquiv C2.indexEquiv target source
  refine ⟨R2.diagram,
    ⟨OEquivalentDiscDiagram.trans (CornerOutput.originalReplacement R1.toCellOutput).oEquivalent
      (CornerOutput.originalReplacement R2.toCellOutput).oEquivalent⟩,
    fun hred => (CornerOutput.originalReplacement R2.toCellOutput).reduced
      ((CornerOutput.originalReplacement R1.toCellOutput).reduced hred),
    R2.label_admissible, R2.suffixSide, H, hHsource, hHtarget, hHnone, hHstart, hHloop, ?_⟩
  intro family havoid hpairwise
  have havoid1 : ∀ a ∈ E1.regionFamily C1 hcells hf family havoid, R1.suffixSide ∉ a.1 := by
    intro a ha hmem
    obtain ⟨b, hb, hab⟩ := E1.regionFamily_faces C1 hcells hf family havoid ha
    rw [hab] at hmem
    obtain ⟨g, hg, hgeq⟩ := Finset.mem_map.mp hmem
    exact R1.suffixSide_not_kept g (fun h => havoid b hb (h ▸ hg)) hgeq
  refine ⟨E2.regionFamily C2 hcells2 hf2 (E1.regionFamily C1 hcells hf family havoid) havoid1,
    E2.regionFamily_pairwise C2 hcells2 hf2 (E1.regionFamily C1 hcells hf family havoid) havoid1
      (E1.regionFamily_pairwise C1 hcells hf family havoid hpairwise),
    (E2.regionFamily_card C2 hcells2 hf2 (E1.regionFamily C1 hcells hf family havoid)
      havoid1).trans (E1.regionFamily_card C1 hcells hf family havoid),
    (E2.regionFamily_weight C2 hcells2 hf2 (E1.regionFamily C1 hcells hf family havoid)
      havoid1).trans (E1.regionFamily_weight C1 hcells hf family havoid), ?_, ?_⟩
  · intro a ha hmem
    obtain ⟨b, hb, hab⟩ := E2.regionFamily_faces C2 hcells2 hf2
      (E1.regionFamily C1 hcells hf family havoid) havoid1 ha
    rw [hab] at hmem
    obtain ⟨g, hg, hgeq⟩ := Finset.mem_map.mp hmem
    exact R2.suffixSide_not_kept g (fun h => havoid1 b hb (h ▸ hg)) hgeq
  · intro a ha
    obtain ⟨b, hb, hab⟩ := E2.regionFamily_profile C2 hcells2 hf2
      (E1.regionFamily C1 hcells hf family havoid) havoid1 ha
    obtain ⟨c, hc, hbc⟩ := E1.regionFamily_profile C1 hcells hf family havoid hb
    exact ⟨c, hc, hab.trans hbc⟩

end GroupApproximation.GGT.VanKampen.GFaceWordInsertion

namespace GroupApproximation.GGT.VanKampen

open GroupApproximation.GGT.VanKampen.Embedded

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

namespace RealizedSectionFamily

/-- **Lemma 9.4, Case 1, on a face of the optimal diagram.**  Let `S` be a section family with
legal labels and maximal weight among legal section families, and let `f` be an inner face of
its diagram that is no relator cell and lies in no selected region.  Suppose that some rotation
of the walk of `f` reads `X ++ q ++ Y ++ p⁻¹`, where `p` is a nonempty arc of a relator cell
and `q` is a nonempty arc of a relator cell or of a boundary section, and that `s_1`, `s_2` are
legal words of length and norm at most `ε` with the values of `X` and `Y`.  Then there is a
contradiction. -/
theorem false_of_quadrilateral_face {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (S : RealizedSectionFamily D lambda c eps Delta cuts)
    (hlegal : S.toRealizedRegionFamily.LabelLegal (symmetricLabelAlphabet D))
    (hmax : ∀ other : RealizedSectionFamily D lambda c eps Delta cuts,
      other.toRealizedRegionFamily.LabelLegal (symmetricLabelAlphabet D) →
        other.weight ≤ S.weight)
    (f : S.diagram.toCombMap.Face) (hf : f ≠ S.diagram.outerFace)
    (hcells : ∀ C ∈ S.diagram.relatorCells, C.face ≠ f) (havoid : ∀ a ∈ S.family, f ∉ a.1)
    (source : Fin S.diagram.rCellCount) (target : Option (Fin S.diagram.rCellCount))
    (sourceArc : CyclicArc (cellDarts S.diagram source))
    (targetArc : CyclicArc (targetDarts S.diagram target))
    (X Y : List S.diagram.toCombMap.Dart) (r : ℕ)
    (htrav : (S.diagram.faceBoundary f).darts.rotate r =
      X ++ targetBoundaryDarts S.diagram target targetArc ++ Y ++ sourceArc.reverseDarts)
    (hsource : 0 < sourceArc.length) (htarget : 0 < targetArc.length)
    (hsection : target = none → ∃ j : Fin cuts.count,
      cuts.cut j.castSucc ≤ targetArc.start.val ∧
        targetArc.start.val + targetArc.length ≤ cuts.cut j.succ)
    (s1 s2 : List (RelLetter G Lambda)) (hne1 : s1 ≠ []) (hne2 : s2 ≠ [])
    (hadm1 : HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) s1)
    (hinv1 : ∀ l ∈ s1, (symmetricLabelAlphabet D).IsLetter (HullSC.RelWord.inv l))
    (hadm2 : HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) s2)
    (hinv2 : ∀ l ∈ s2, (symmetricLabelAlphabet D).IsLetter (HullSC.RelWord.inv l))
    (hval1 : RelLetter.listVal s1 = RelLetter.listVal (dartWord S.diagram X))
    (hval2 : RelLetter.listVal s2 = RelLetter.listVal (dartWord S.diagram Y))
    (hlen1 : s1.length ≤ eps) (hlen2 : s2.length ≤ eps)
    (hnorm1 : WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal s1) ≤ eps)
    (hnorm2 : WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal s2) ≤ eps) :
    False := by
  obtain ⟨Xi, ⟨hequiv⟩, hred, hlabelXi, Q, H, hHsource, hHtarget, hHnone, hHstart, -,
      hretain⟩ :=
    GFaceWordInsertion.exists_quadrilateral_region_rotate D (symmetricLabelAlphabet D) eps
      S.diagram (fun d => hlegal d) f hf hcells source target sourceArc targetArc X Y r htrav
      hsource s1 s2 hne1 hne2 hadm1 hinv1 hadm2 hinv2 hval1 hval2 hlen1 hlen2 hnorm1 hnorm2
  obtain ⟨family2, hpair2, -, hweight2, havoid2, hprofile2⟩ :=
    hretain S.family havoid S.pairwise
  have hpositive : 0 < H.sourceArc.length := lt_of_lt_of_eq hsource hHsource.symm
  have hlt := RegionCandidate.familyWeight_lt_cons_singleton H havoid2 hpositive
  have hrespects : ∀ a ∈ Finset.cons (⟨{Q}, H⟩ : RegionCandidate D eps Xi) family2
      (RegionCandidate.singleton_not_mem_of_avoid H havoid2),
      RegionCandidate.RespectsSections cuts a := by
    intro a ha
    rcases Finset.mem_cons.mp ha with rfl | ha2
    · intro hnoneQ
      obtain ⟨j, h1, h2⟩ := hsection (hHnone.mp hnoneQ)
      have h3 : cuts.cut j.castSucc ≤ H.targetArc.start.val := by
        rw [hHstart]
        exact h1
      have h4 : H.targetArc.start.val + H.targetArc.length ≤ cuts.cut j.succ := by
        rw [hHstart, hHtarget]
        exact h2
      exact ⟨j, hnoneQ, h3, h4⟩
    · obtain ⟨b, hb, hab⟩ := hprofile2 a ha2
      exact RegionCandidate.respectsSections_of_sameTargetProfile cuts hab (S.respects b hb)
  have hnondegenerate : ∀ a ∈ Finset.cons (⟨{Q}, H⟩ : RegionCandidate D eps Xi) family2
      (RegionCandidate.singleton_not_mem_of_avoid H havoid2),
      0 < a.2.sourceArc.length ∧ 0 < a.2.targetArc.length := by
    intro a ha
    rcases Finset.mem_cons.mp ha with rfl | ha2
    · exact ⟨hpositive, lt_of_lt_of_eq htarget hHtarget.symm⟩
    · obtain ⟨b, hb, hab⟩ := hprofile2 a ha2
      obtain ⟨hs, ht⟩ := S.nondegenerate b hb
      exact ⟨lt_of_lt_of_eq hs hab.2.2.2.symm, lt_of_lt_of_eq ht hab.2.2.1.symm⟩
  have hle : EstimatingSelection.familyWeight RegionCandidate.weight
      (Finset.cons (⟨{Q}, H⟩ : RegionCandidate D eps Xi) family2
        (RegionCandidate.singleton_not_mem_of_avoid H havoid2)) ≤
      EstimatingSelection.familyWeight RegionCandidate.weight S.family :=
    hmax
      { diagram := Xi
        equiv := S.equiv.trans hequiv
        reduced := hred S.reduced
        family := Finset.cons (⟨{Q}, H⟩ : RegionCandidate D eps Xi) family2
          (RegionCandidate.singleton_not_mem_of_avoid H havoid2)
        pairwise := RegionCandidate.cons_singleton_pairwise H havoid2 hpair2
        respects := hrespects
        nondegenerate := hnondegenerate }
      hlabelXi
  omega

end RealizedSectionFamily

open GroupApproximation.GGT.VanKampen.UnboundEstimate in
/-- **Case 1 of Lemma 9.4 for a pair with sides of one kind.**  `OsinLemma94CaseOneInput`
restricted to the backwards connector pairs whose source and target sides have the same kind.
When both sides lie across one relator cell, the quadrilateral of Case 1 is a region from that
cell to itself, and this statement is kept as a named hypothesis for those pairs. -/
def OsinLemma94CaseOneSameCellStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
            ∀ (Delta : DiscDiagram.{u, w, v} W)
              (cuts : SectionCuts D lambda c Delta.boundaryWord),
              Delta.LeastArea → 0 < Delta.rCellCount →
              ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
                S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1) → S.DartMinimal →
                  ∀ P : OsinLemma94RealizedPolygons S, P.Maximal →
                    ∀ (k : Fin P.count) (C : WordConnectorPair (symmetricLabelAlphabet D)
                      (P.corner k) (P.word k) (P.sideCount k) (P.relatorSides k)
                      (P.longSides k) eps),
                      C.b' < C.b → P.kind k C.target ≠ .cutting →
                        P.kind k C.source = P.kind k C.target → False

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.forwardOffset_of_val_eq_mod
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.faceOf_alpha_ne_of_mem_reverseDarts
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.faceOf_alpha_ne_of_mem_targetBoundaryDarts
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.option_map_map_equiv_eq_some_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.exists_quadrilateral_region_rotate
#audit_axioms GroupApproximation.GGT.VanKampen.RealizedSectionFamily.false_of_quadrilateral_face
