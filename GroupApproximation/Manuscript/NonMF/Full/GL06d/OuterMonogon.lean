import GroupApproximation.Manuscript.NonMF.Full.GL06d.OuterMonogonDiagram
import GroupApproximation.Meta.AxiomGuard

/-!
# Non-rose step: the corner digon at an exterior monogon, and the corner dispatcher

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b) (`thm:hull`).

## The exterior monogon

When `σ z = α z` and `face (α z)` is the exterior, the exterior has a single dart
(`not_one_lt_length_of_monogon`, and a face traversal is nonempty).  Doubling that dart
(`outerDiagram`) inserts an edge from the corner of `σ z` to itself.

The pocket transports along the embedding, except for the target arc: the outer traversal has one
dart and the target arc is proper, so the target arc is empty (`targetArc_darts_nil`), and it
stays empty at the same start position (`zeroArc`).  The boundary cycle, both sides and the source
arc are mapped lists, the source carrier is a mapped list (`outer_cellDarts_eq`), and vertices of
old darts are kept (`outer_hvert`), so walk order, repeated visits and properness of both arcs are
kept.

The step `z → σ z` lifts to three steps with new intermediate darts, and
`α' (embed z) = embed (α z)` lies on the digon (`outer_face0`, `m = 0`), a G-face whose only old
dart is `α z` (`eq_of_outerDigon`); G-faces stay G-faces (`outer_transfer`).  This is
`cornerDigon_outerMonogon`.

## The dispatcher

`cornerDigon_of_hone`: a monogon corner is inner (`cornerDigon_innerMonogon`) or exterior
(`cornerDigon_outerMonogon`); a non-monogon corner outside the face set with (H2) is
`cornerDigon_of_nonMonogon`.

## Manuscript status

Infrastructure for `thm:hull` (`non_mf_groups_exist.tex`; Hull's small cancellation theorem,
through Osin's Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.GL06d

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.Surgery.MapCollapse
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
open GroupApproximation.GGT.VanKampen.OuterPinchIsolated
open GroupApproximation.GGT.VanKampen.OuterPinchCorners
open GroupApproximation.GGT.VanKampen.OuterPinchCornerFix
open scoped Classical

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {lo hi : ℕ}

variable (X : DiscDiagram.{u, w, v} W)

section Transport

variable (hlen : (X.faceBoundary X.outerFace).darts.length = 1)

/-- Relator cells go to the images of their faces (`thm:hull`). -/
theorem outer_hcell (k : Fin X.rCellCount) :
    (Embedded.cell (outerDiagram X hlen) ((outerCellMap X hlen).indexEquiv k)).face =
      (outerEmbedding X hlen).faces (Embedded.cell X k).face :=
  (congrArg RelatorCell.face ((outerCellMap X hlen).indexed_cell k)).trans
    ((outerCellMap X hlen).face_eq (Embedded.cell X k))

/-- The doubling keeps the vertices of old darts (`thm:hull`). -/
theorem outer_hvert (x y : X.toCombMap.Dart) :
    (outerDiagram X hlen).toCombMap.vertexOf ((outerEmbedding X hlen).darts x) =
      (outerDiagram X hlen).toCombMap.vertexOf ((outerEmbedding X hlen).darts y) ↔
      X.toCombMap.vertexOf x = X.toCombMap.vertexOf y :=
  GeodesicCollar.edgeInsertion_vertexOf_embed_iff X.toCombMap
    (EdgeInsertion.firstCorner X.toCombMap (X.faceBoundary X.outerFace))
    (EdgeInsertion.secondCorner X.toCombMap (X.faceBoundary X.outerFace)
      (MonogonDoubling.zero X X.outerFace)) x y

/-- The doubling keeps the head vertices of old darts (`thm:hull`). -/
theorem outer_hvert_alpha (x y : X.toCombMap.Dart) :
    (outerDiagram X hlen).toCombMap.vertexOf
        ((outerDiagram X hlen).toCombMap.alpha ((outerEmbedding X hlen).darts x)) =
      (outerDiagram X hlen).toCombMap.vertexOf ((outerEmbedding X hlen).darts y) ↔
      X.toCombMap.vertexOf (X.toCombMap.alpha x) = X.toCombMap.vertexOf y := by
  rw [(outerEmbedding X hlen).alpha]
  exact outer_hvert X hlen _ y

/-- The source carrier is a mapped list (`thm:hull`). -/
theorem outer_cellDarts_eq (k : Fin X.rCellCount) :
    cellDarts (outerDiagram X hlen) ((outerCellMap X hlen).indexEquiv k) =
      (cellDarts X k).map (outerEmbedding X hlen).darts := by
  change ((outerDiagram X hlen).faceBoundary
      (Embedded.cell (outerDiagram X hlen) ((outerCellMap X hlen).indexEquiv k)).face).darts =
    (X.faceBoundary (Embedded.cell X k).face).darts.map (outerEmbedding X hlen).darts
  rw [outer_hcell X hlen k]
  exact (outerEmbedding X hlen).face_boundary _ (Embedded.cell X k).face_ne_outer

include hlen in
/-- The old outer traversal has one dart (`thm:hull`). -/
theorem outerDarts_length_one : (outerDarts X).length = 1 := by
  unfold outerDarts
  rw [List.length_map, List.length_reverse]
  exact hlen

/-- The new outer traversal has one dart (`thm:hull`). -/
theorem outerDiagram_outerDarts_length_one :
    (outerDarts (outerDiagram X hlen)).length = 1 := by
  unfold outerDarts
  rw [List.length_map, List.length_reverse]
  exact congrArg List.length (MonogonDoubling.boundary_cellFace X X.outerFace)

/-- The outer traversals have the same length (`thm:hull`). -/
theorem outerDarts_length_eq :
    (outerDarts (outerDiagram X hlen)).length = (outerDarts X).length :=
  (outerDiagram_outerDarts_length_one X hlen).trans (outerDarts_length_one X hlen).symm

include hlen in
/-- A proper target arc on a one-dart exterior is empty (`thm:hull`). -/
theorem targetArc_darts_nil (K : PocketFaceSet D eps X lo hi)
    (htgt : K.targetArc.length < (outerDarts X).length) : K.targetArc.darts = [] := by
  have h0 : K.targetArc.length = 0 := by
    have h1 := outerDarts_length_one X hlen
    omega
  exact (congrArg (fun n => List.take n K.targetArc.rotated) h0).trans List.take_zero

/-- **The pocket across the doubling of a one-dart exterior** (`thm:hull`). -/
noncomputable def outerMonogonPocket (K : PocketFaceSet D eps X lo hi)
    (hta0 : K.targetArc.darts = []) : PocketFaceSet D eps (outerDiagram X hlen) lo hi where
  faces := (outerEmbedding X hlen).faceSet K.faces
  outerFace_not_mem := by
    change (outerDiagram X hlen).outerFace ∉ K.faces.map (outerEmbedding X hlen).faces
    rw [(outerEmbedding X hlen).outer, Finset.mem_map']
    exact K.outerFace_not_mem
  source := (outerCellMap X hlen).indexEquiv K.source
  source_not_mem := by
    rw [outer_hcell X hlen K.source]
    change (outerEmbedding X hlen).faces (Embedded.cell X K.source).face ∉
      K.faces.map (outerEmbedding X hlen).faces
    rw [Finset.mem_map']
    exact K.source_not_mem
  kept := (outerCellMap X hlen).indexEquiv K.kept
  kept_mem := by
    rw [outer_hcell X hlen K.kept]
    change (outerEmbedding X hlen).faces (Embedded.cell X K.kept).face ∈
      K.faces.map (outerEmbedding X hlen).faces
    rw [Finset.mem_map']
    exact K.kept_mem
  sourceArc :=
    K.sourceArc.mapTo (outerEmbedding X hlen).darts (outer_cellDarts_eq X hlen K.source)
  targetArc := zeroArc K.targetArc (outerDarts_length_eq X hlen)
  firstSide := K.firstSide.map (outerEmbedding X hlen).darts
  secondSide := K.secondSide.map (outerEmbedding X hlen).darts
  boundary := (outerEmbedding X hlen).boundaryCycle K.faces K.outerFace_not_mem K.boundary
  decomposition := by
    rw [CyclicArc.mapTo_darts K.sourceArc (outerEmbedding X hlen).darts
        (outer_cellDarts_eq X hlen K.source),
      DiscEmbeddingAway.invDarts_map, DiscEmbeddingAway.boundaryCycle_cycle, K.decomposition,
      hta0, zeroArc_darts]
    simp only [List.map_append, List.append_nil]
  firstSide_length_le := by
    rw [List.length_map]
    exact K.firstSide_length_le
  secondSide_length_le := by
    rw [List.length_map]
    exact K.secondSide_length_le
  firstSide_norm_le := by
    rw [DiscEmbeddingAway.dartWord_map]
    exact K.firstSide_norm_le
  secondSide_norm_le := by
    rw [DiscEmbeddingAway.dartWord_map]
    exact K.secondSide_norm_le
  lo_le := K.lo_le
  le_hi := by
    show K.targetArc.start.1 + 0 ≤ hi
    have hle := K.le_hi
    omega

variable (K : PocketFaceSet D eps X lo hi) (hta0 : K.targetArc.darts = [])

/-- The new boundary cycle is the mapped old one (`thm:hull`). -/
theorem outerMonogon_boundary_cycle :
    (outerMonogonPocket X hlen K hta0).boundary.cycle =
      K.boundary.cycle.map (outerEmbedding X hlen).darts :=
  rfl

/-- **The doubling keeps walk order** (`thm:hull`). -/
theorem outerMonogon_closedWalk (hK : K.ClosedWalk) :
    (outerMonogonPocket X hlen K hta0).ClosedWalk := by
  refine ⟨?_, ?_⟩
  · change (K.boundary.cycle.map (outerEmbedding X hlen).darts).IsChain
      (fun d e => (outerDiagram X hlen).toCombMap.vertexOf
        ((outerDiagram X hlen).toCombMap.alpha d) = (outerDiagram X hlen).toCombMap.vertexOf e)
    exact (List.isChain_map _).mpr (hK.1.imp fun d e h => (outer_hvert_alpha X hlen d e).mpr h)
  · change (outerDiagram X hlen).toCombMap.vertexOf
        ((outerDiagram X hlen).toCombMap.alpha
          ((K.boundary.cycle.map (outerEmbedding X hlen).darts).getLast
            (outerMonogonPocket X hlen K hta0).boundary.cycle_nonempty)) =
      (outerDiagram X hlen).toCombMap.vertexOf
        ((K.boundary.cycle.map (outerEmbedding X hlen).darts).head
          (outerMonogonPocket X hlen K hta0).boundary.cycle_nonempty)
    rw [List.getLast_map, List.head_map]
    exact (outer_hvert_alpha X hlen _ _).mpr hK.2

/-- **The doubling keeps the repeated visits** (`thm:hull`). -/
theorem outerMonogon_repeatedVisits :
    (outerMonogonPocket X hlen K hta0).repeatedVisits = K.repeatedVisits := by
  unfold PocketFaceSet.repeatedVisits
  rw [outerMonogon_boundary_cycle, List.length_map, List.map_map]
  congr 1
  exact card_toFinset_map_eq_of_iff
    ((outerDiagram X hlen).toCombMap.vertexOf ∘ (outerEmbedding X hlen).darts)
    X.toCombMap.vertexOf (fun a b => outer_hvert X hlen a b) _

/-- The source arc stays proper (`thm:hull`). -/
theorem outerMonogon_source_proper
    (hprop : K.sourceArc.length < (cellDarts X K.source).length) :
    (outerMonogonPocket X hlen K hta0).sourceArc.length <
      (cellDarts (outerDiagram X hlen) (outerMonogonPocket X hlen K hta0).source).length := by
  have h1 : (outerMonogonPocket X hlen K hta0).sourceArc.length = K.sourceArc.length :=
    CyclicArc.mapTo_length K.sourceArc _ (outer_cellDarts_eq X hlen K.source)
  have h2 :
      (cellDarts (outerDiagram X hlen) ((outerCellMap X hlen).indexEquiv K.source)).length =
        (cellDarts X K.source).length :=
    (congrArg List.length (outer_cellDarts_eq X hlen K.source)).trans (List.length_map _)
  exact lt_of_eq_of_lt h1 (lt_of_lt_of_eq hprop h2.symm)

/-- The target arc stays proper (`thm:hull`). -/
theorem outerMonogon_target_proper :
    (outerMonogonPocket X hlen K hta0).targetArc.length <
      (outerDarts (outerDiagram X hlen)).length := by
  show 0 < (outerDarts (outerDiagram X hlen)).length
  exact lt_of_lt_of_eq Nat.one_pos (outerDiagram_outerDarts_length_one X hlen).symm

end Transport

section Corner

variable (hlen : (X.faceBoundary X.outerFace).darts.length = 1)

/-- The reverse of the lifted corner dart lies on the digon (`thm:hull`). -/
theorem outer_face0 {z : X.toCombMap.Dart}
    (hfz : X.toCombMap.faceOf (X.toCombMap.alpha z) = X.outerFace) :
    (outerDiagram X hlen).toCombMap.faceOf
        ((outerDiagram X hlen).toCombMap.alpha
          (((outerDiagram X hlen).toCombMap.sigma ^ 0)
            ((RotationRefinement.sameCorner (MonogonDoubling.dart X X.outerFace)).map z))) =
      MonogonDoubling.digon X X.outerFace := by
  rw [pow_zero, Equiv.Perm.one_apply]
  change (MonogonDoubling.map X X.outerFace).faceOf
      (EdgeInsertion.embed X.toCombMap (X.toCombMap.alpha z)) =
    MonogonDoubling.digon X X.outerFace
  exact MonogonDoubling.faceOf_embed_of_face X X.outerFace hfz

/-- **The digon of the exterior doubling is a G-face** (`thm:hull`). -/
theorem outer_digon_isGFace :
    IsGFaceOf (outerDiagram X hlen) (MonogonDoubling.digon X X.outerFace) := by
  refine ⟨MonogonDoubling.digon_ne_cellFace X X.outerFace, fun C hC => ?_⟩
  change C ∈ X.relatorCells.map (outerCell X) at hC
  obtain ⟨C₀, -, rfl⟩ := List.mem_map.mp hC
  exact MonogonDoubling.faceImage_ne_digon X X.outerFace C₀.face

include hlen in
/-- The only old dart on the digon is the dart of the exterior (`thm:hull`). -/
theorem eq_of_outerDigon {z w : X.toCombMap.Dart}
    (hfz : X.toCombMap.faceOf (X.toCombMap.alpha z) = X.outerFace)
    (hw : (MonogonDoubling.map X X.outerFace).faceOf (EdgeInsertion.embed X.toCombMap w) =
      MonogonDoubling.digon X X.outerFace) : w = X.toCombMap.alpha z := by
  by_cases hwf : X.toCombMap.faceOf w = X.outerFace
  · exact (MonogonDoubling.dart_eq_of_face X X.outerFace hlen hwf).symm.trans
      (MonogonDoubling.dart_eq_of_face X X.outerFace hlen hfz)
  · exact absurd ((MonogonDoubling.faceOf_embed_of_ne X X.outerFace hwf).symm.trans hw)
      (MonogonDoubling.keep_ne_digon X X.outerFace hwf)

/-- **A G-face stays a G-face** (`thm:hull`). -/
theorem outer_transfer (w : X.toCombMap.Dart) (hG : IsGFaceOf X (X.toCombMap.faceOf w)) :
    IsGFaceOf (outerDiagram X hlen)
      ((MonogonDoubling.map X X.outerFace).faceOf (EdgeInsertion.embed X.toCombMap w)) := by
  refine isGFaceOf_congr (MonogonDoubling.faceOf_embed_of_ne X X.outerFace hG.1)
    ⟨MonogonDoubling.keep_ne_cellFace X X.outerFace hG.1, fun C hC h => ?_⟩
  change C ∈ X.relatorCells.map (outerCell X) at hC
  obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC
  have h' : MonogonDoubling.faceImage X X.outerFace C₀.face =
      MonogonDoubling.faceImage X X.outerFace (X.toCombMap.faceOf w) :=
    h.trans (MonogonDoubling.faceImage_of_ne X X.outerFace hG.1).symm
  exact hG.2 C₀ hC₀ (MonogonDoubling.faceImage_injective X X.outerFace h')

end Corner

/-- **The corner digon at an exterior monogon corner** (`thm:hull`). -/
theorem cornerDigon_outerMonogon (K : PocketFaceSet D eps X lo hi) (z : X.toCombMap.Dart)
    (hinv : PocketInvariants K)
    (hfz : X.toCombMap.faceOf (X.toCombMap.alpha z) = X.outerFace)
    (hmono : X.toCombMap.sigma z = X.toCombMap.alpha z) : CornerDigon K z := by
  obtain ⟨hlabel, hK, hsrcP, htgtP⟩ := hinv
  have hlen : (X.faceBoundary X.outerFace).darts.length = 1 := by
    have hpos : 0 < (X.faceBoundary X.outerFace).darts.length :=
      List.length_pos_iff.mpr (X.faceBoundary X.outerFace).nonempty
    have hle := not_one_lt_length_of_monogon hfz hmono
    omega
  have hσ : X.toCombMap.sigma z = MonogonDoubling.dart X X.outerFace :=
    (MonogonDoubling.dart_eq_of_face X X.outerFace hlen
      ((congrArg X.toCombMap.faceOf hmono).trans hfz)).symm
  have hta0 := targetArc_darts_nil X hlen K htgtP
  exact ⟨outerDiagram X hlen, outerMonogonPocket X hlen K hta0,
    RotationRefinement.sameCorner (MonogonDoubling.dart X X.outerFace),
    ⟨outerOEquivalent X hlen⟩,
    ⟨outerLabel_letter X hlen hlabel, outerMonogon_closedWalk X hlen K hta0 hK,
      outerMonogon_source_proper X hlen K hta0 hsrcP, outerMonogon_target_proper X hlen K hta0⟩,
    outerMonogon_repeatedVisits X hlen K hta0, outerMonogon_boundary_cycle X hlen K hta0,
    3, 0, by omega, sameCorner_sigma_three hσ, sameCorner_mid hσ,
    isGFaceOf_congr (outer_face0 X hlen hfz) (outer_digon_isGFace X hlen),
    fun w hw => Or.inl (eq_of_outerDigon X hlen hfz (hw.trans (outer_face0 X hlen hfz))),
    fun w hG _ => outer_transfer X hlen w hG⟩

/-- **The corner digon at a corner with (H2) whose face is outside the face set**
(`thm:hull`). -/
theorem cornerDigon_of_hone (hW : ∀ word ∈ W, 1 < word.length)
    (K : PocketFaceSet D eps X lo hi) (z : X.toCombMap.Dart) (hinv : PocketInvariants K)
    (hs : X.toCombMap.faceOf (X.toCombMap.alpha z) ∉ K.faces)
    (hone : ¬ ∃ h : X.toCombMap.alpha (X.toCombMap.sigma z) ∈ K.boundary.cycle,
      K.boundary.cycle.next _ h = z) : CornerDigon K z := by
  by_cases hmono : X.toCombMap.sigma z = X.toCombMap.alpha z
  · by_cases hfo : X.toCombMap.faceOf (X.toCombMap.alpha z) = X.outerFace
    · exact cornerDigon_outerMonogon X K z hinv hfo hmono
    · exact cornerDigon_innerMonogon hW K z hinv hfo hmono
  · exact cornerDigon_of_nonMonogon X K z hinv hs hone hmono

end GroupApproximation.Full.GL06d

#audit_axioms GroupApproximation.Full.GL06d.outer_hcell
#audit_axioms GroupApproximation.Full.GL06d.outer_hvert
#audit_axioms GroupApproximation.Full.GL06d.outer_hvert_alpha
#audit_axioms GroupApproximation.Full.GL06d.outer_cellDarts_eq
#audit_axioms GroupApproximation.Full.GL06d.outerDarts_length_one
#audit_axioms GroupApproximation.Full.GL06d.outerDiagram_outerDarts_length_one
#audit_axioms GroupApproximation.Full.GL06d.outerDarts_length_eq
#audit_axioms GroupApproximation.Full.GL06d.targetArc_darts_nil
#audit_axioms GroupApproximation.Full.GL06d.outerMonogonPocket
#audit_axioms GroupApproximation.Full.GL06d.outerMonogon_boundary_cycle
#audit_axioms GroupApproximation.Full.GL06d.outerMonogon_closedWalk
#audit_axioms GroupApproximation.Full.GL06d.outerMonogon_repeatedVisits
#audit_axioms GroupApproximation.Full.GL06d.outerMonogon_source_proper
#audit_axioms GroupApproximation.Full.GL06d.outerMonogon_target_proper
#audit_axioms GroupApproximation.Full.GL06d.outer_face0
#audit_axioms GroupApproximation.Full.GL06d.outer_digon_isGFace
#audit_axioms GroupApproximation.Full.GL06d.eq_of_outerDigon
#audit_axioms GroupApproximation.Full.GL06d.outer_transfer
#audit_axioms GroupApproximation.Full.GL06d.cornerDigon_outerMonogon
#audit_axioms GroupApproximation.Full.GL06d.cornerDigon_of_hone
