import GroupApproximation.GGT.VanKampen.GFaceSplitCorners
import GroupApproximation.GGT.VanKampen.Estimating.SingletonFaceRegion
import GroupApproximation.Meta.AxiomGuard

/-!
# A new contiguity region from two connector words across a G-face

Case 1 of Osin's Appendix Lemma 9.4 (arXiv:math/0411039v3): two long arcs `p` (of a
relator cell) and `q` (of a relator cell or of the boundary) face each other inside a
region of G-cells, joined by two short words `s_1`, `s_2`; "passing to an O-equivalent
diagram if necessary, there is a subdiagram `Γ` with `∂Γ = q_1 s_1 q_2^{-1} s_2` … that
does not intersect R-cells and distinguished ε-contiguity subdiagrams.  This contradicts
the maximality of M."  This file builds `Γ` as ONE face.

The input is a G-face `f` with no internally paired dart whose traversal reads
`X ++ T ++ Y ++ P`, where `P` is the reversed source arc and `T` the target arc as it
occurs on a region boundary, together with words `s_1`, `s_2` of the values of `X` and
`Y`.  The first insertion (`exists_split_corner_output`) replaces `X` by `s_1`: its
suffix side reads `s_1 ++ T ++ Y ++ P`.  The second replaces `Y` by `s_2` across that
suffix side: its suffix side `Q` reads `s_2 ++ P ++ s_1 ++ T`.  Rotated, `Q` is
`P ++ s_1 ++ T ++ s_2`, a contiguity region of the source cell to the target with short
sides `s_1`, `s_2` (`Embedded.ContiguityGeometry.ofSingletonFace`), and `Q` has no
internally paired dart: the reverse of a dart of `s_2` lies on the second prefix side,
of a dart of `s_1` on the first prefix side, and of a dart of `P` or `T` on a face that
was already different from `f`.

`exists_quadrilateral_region` returns the two-step O-equivalent diagram (reducedness and
label legality preserved), the region on `{Q}` with the arc lengths of `p` and `q`, and
the retention of every compatible family avoiding `f`, whose regions avoid `Q`.  With
`RegionCandidate.familyWeight_lt_cons_singleton` this is the weight contradiction.
-/

namespace GroupApproximation.GGT.VanKampen.DiscEmbeddingAway

open GroupApproximation.GGT.VanKampen.Embedded
universe u w v v'
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W} {Xi : DiscDiagram.{u, w, v'} W}
  {f : Delta.toCombMap.Face}

/-- A retained dart lies on the retained copy of its face. -/
theorem faceOf_darts (E : DiscEmbeddingAway Delta Xi f) {d : Delta.toCombMap.Dart}
    (hd : Delta.toCombMap.faceOf d ≠ f) :
    Xi.toCombMap.faceOf (E.darts d) = E.faces (Delta.toCombMap.faceOf d) := by
  apply ((Xi.faceBoundary (E.faces (Delta.toCombMap.faceOf d))).mem_iff (E.darts d)).mp
  rw [E.face_boundary _ hd]
  exact List.mem_map.mpr ⟨d, ((Delta.faceBoundary _).mem_iff d).mpr rfl, rfl⟩

end GroupApproximation.GGT.VanKampen.DiscEmbeddingAway

namespace GroupApproximation.GGT.VanKampen.GFaceWordInsertion

open GroupApproximation.GGT.VanKampen.Embedded
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}

/-- O-equivalence composes. -/
def oEquivTrans {Delta₁ Delta₂ Delta₃ : DiscDiagram.{u, w, v} W}
    (first : OEquivalentDiscDiagram Delta₁ Delta₂)
    (second : OEquivalentDiscDiagram Delta₂ Delta₃) : OEquivalentDiscDiagram Delta₁ Delta₃ where
  boundaryWord_eq := second.boundaryWord_eq.trans first.boundaryWord_eq
  cellIndex := first.cellIndex.trans second.cellIndex
  cellWord_eq i := (second.cellWord_eq (first.cellIndex i)).trans (first.cellWord_eq i)

theorem forwardOffset_of_le {M : CombMap.{v}} {g : M.Face} (B : FaceBoundary M g)
    {start finish : Fin B.darts.length} (h : start.val ≤ finish.val) :
    B.forwardOffset start finish = finish.val - start.val := by
  simp [FaceBoundary.forwardOffset, h]

/-- **The quadrilateral region of Lemma 9.4 Case 1.** -/
theorem exists_quadrilateral_region (D E : RelGenSet G Lambda) (eps : ℕ)
    (Delta : DiscDiagram.{u, w, v} W) (hlabel : ∀ d, E.IsLetter (Delta.label d))
    (f : Delta.toCombMap.Face) (hf : f ≠ Delta.outerFace)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ f)
    (hno : Surgery.MapCollapse.NoInternalFaceDart Delta.toCombMap f)
    (source : Fin Delta.rCellCount) (target : Option (Fin Delta.rCellCount))
    (sourceArc : CyclicArc (cellDarts Delta source))
    (targetArc : CyclicArc (targetDarts Delta target))
    (X Y : List Delta.toCombMap.Dart)
    (htrav : (Delta.faceBoundary f).darts =
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
        ∀ family : Finset (RegionCandidate D eps Delta), (∀ a ∈ family, f ∉ a.1) →
          EstimatingSelection.PairwiseCompatible RegionCandidate.Compatible family →
          ∃ family' : Finset (RegionCandidate D eps Xi),
            EstimatingSelection.PairwiseCompatible RegionCandidate.Compatible family' ∧
            family'.card = family.card ∧
            EstimatingSelection.familyWeight RegionCandidate.weight family' =
              EstimatingSelection.familyWeight RegionCandidate.weight family ∧
            ∀ a ∈ family', Q ∉ a.1 := by
  have hPlen : sourceArc.reverseDarts.length = sourceArc.length := by
    simp only [CyclicArc.reverseDarts, List.length_map, List.length_reverse,
      CyclicArc.darts_length]
  /- The first split, at the corners before and after `X`. -/
  have hXlt : X.length < (Delta.faceBoundary f).darts.length := by
    rw [htrav]
    simp only [List.length_append]
    omega
  have hn : 0 < (Delta.faceBoundary f).darts.length := by omega
  let start1 : Fin (Delta.faceBoundary f).darts.length := ⟨0, hn⟩
  let finish1 : Fin (Delta.faceBoundary f).darts.length := ⟨X.length, hXlt⟩
  have hoff1 : (Delta.faceBoundary f).forwardOffset start1 finish1 = X.length :=
    (forwardOffset_of_le _ (Nat.zero_le _)).trans (Nat.sub_zero _)
  have hvalue1 : RelLetter.listVal s1 = RelLetter.listVal
      ((((Delta.faceBoundary f).darts.rotate start1.val).take
        ((Delta.faceBoundary f).forwardOffset start1 finish1)).map Delta.label) := by
    rw [hoff1]
    change _ = RelLetter.listVal ((((Delta.faceBoundary f).darts.rotate 0).take X.length).map
      Delta.label)
    rw [List.rotate_zero, htrav, List.append_assoc, List.append_assoc, List.take_left]
    exact hval1
  obtain ⟨R1⟩ := exists_split_corner_output E Delta hlabel f hf hcells start1 finish1 s1 hne1
    hadm1 hinv1 hvalue1
  let E1 := CornerOutput.originalEmbedding R1.toCellOutput
  let C1 := CornerOutput.originalCellMap R1.toCellOutput
  have hS : (R1.diagram.faceBoundary R1.suffixSide).darts =
      R1.darts ++ (targetBoundaryDarts Delta target targetArc ++
        (Y ++ sourceArc.reverseDarts)).map E1.darts := by
    have h1 := R1.suffixSide_darts_original
    have h2 : ((Delta.faceBoundary f).darts.rotate start1.val).drop
        ((Delta.faceBoundary f).forwardOffset start1 finish1) =
          targetBoundaryDarts Delta target targetArc ++ (Y ++ sourceArc.reverseDarts) := by
      rw [hoff1]
      change ((Delta.faceBoundary f).darts.rotate 0).drop X.length = _
      rw [List.rotate_zero, htrav, List.append_assoc, List.append_assoc, List.drop_left]
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
    (forwardOffset_of_le _ (Nat.le_add_right _ _)).trans (Nat.add_sub_cancel_left)
  have hrot2 : (R1.diagram.faceBoundary R1.suffixSide).darts.rotate start2.val =
      Y.map E1.darts ++ (sourceArc.reverseDarts.map E1.darts ++
        (R1.darts ++ (targetBoundaryDarts Delta target targetArc).map E1.darts)) := by
    rw [hS]
    have hsplit : R1.darts ++ (targetBoundaryDarts Delta target targetArc ++
        (Y ++ sourceArc.reverseDarts)).map E1.darts =
          (R1.darts ++ (targetBoundaryDarts Delta target targetArc).map E1.darts) ++
            (Y.map E1.darts ++ sourceArc.reverseDarts.map E1.darts) := by
      simp only [List.map_append, List.append_assoc]
    rw [hsplit]
    change ((R1.darts ++ (targetBoundaryDarts Delta target targetArc).map E1.darts) ++
      (Y.map E1.darts ++ sourceArc.reverseDarts.map E1.darts)).rotate
        (R1.darts.length + (targetBoundaryDarts Delta target targetArc).length) = _
    rw [show R1.darts.length + (targetBoundaryDarts Delta target targetArc).length =
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
  let C2 := CornerOutput.originalCellMap R2.toCellOutput
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
  have hold_face : ∀ z ∈ (Delta.faceBoundary f).darts,
      R1.diagram.toCombMap.faceOf (R1.diagram.toCombMap.alpha (E1.darts z)) ≠
        R1.suffixSide := by
    intro z hz
    have hzf : Delta.toCombMap.faceOf z = f := ((Delta.faceBoundary f).mem_iff z).mp hz
    have hg : Delta.toCombMap.faceOf (Delta.toCombMap.alpha z) ≠ f := hno z hzf
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
          exact hold_face z (by rw [htrav]; exact List.mem_append_right _ hz)
        · rcases List.mem_append.mp hyrest with hys1 | hyT
          · have hpre1 : R1.diagram.toCombMap.alpha y ∈
                (R1.diagram.faceBoundary R1.prefixSide).darts := by
              rw [R1.prefixSide_darts_original]
              exact List.mem_append_left _
                (List.mem_map.mpr ⟨y, List.mem_reverse.mpr hys1, rfl⟩)
            rw [((R1.diagram.faceBoundary _).mem_iff _).mp hpre1]
            exact R1.prefixSide_ne_suffixSide
          · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hyT
            exact hold_face z (by
              rw [htrav]
              exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hz)))
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
  refine ⟨R2.diagram,
    ⟨oEquivTrans (CornerOutput.originalReplacement R1.toCellOutput).oEquivalent
      (CornerOutput.originalReplacement R2.toCellOutput).oEquivalent⟩,
    fun hred => (CornerOutput.originalReplacement R2.toCellOutput).reduced
      ((CornerOutput.originalReplacement R1.toCellOutput).reduced hred),
    R2.label_admissible, R2.suffixSide, H, ?_, ?_, ?_⟩
  · exact (CyclicArc.mapTo_length _ _ _).trans (CyclicArc.mapTo_length _ _ _)
  · exact (CyclicArc.mapTo_length _ _ _).trans (CyclicArc.mapTo_length _ _ _)
  · intro family havoid hpairwise
    obtain ⟨family1, hpair1, hcard1, hweight1, havoid1⟩ :=
      R1.retained_regionFamily D eps family havoid hpairwise
    obtain ⟨family2, hpair2, hcard2, hweight2, havoid2⟩ :=
      R2.retained_regionFamily D eps family1 (fun a ha => (havoid1 a ha).2) hpair1
    exact ⟨family2, hpair2, hcard2.trans hcard1, hweight2.trans hweight1,
      fun a ha => (havoid2 a ha).2⟩

end GroupApproximation.GGT.VanKampen.GFaceWordInsertion

#audit_axioms GroupApproximation.GGT.VanKampen.DiscEmbeddingAway.faceOf_darts
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.exists_quadrilateral_region
