import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.CornerStep
import GroupApproximation.GGT.VanKampen.SurgeryMonogonDoubling
import GroupApproximation.GGT.VanKampen.SurgeryMonogonDoublingStrip
import GroupApproximation.GGT.VanKampen.SurgeryGeodesicCollarWalk
import GroupApproximation.GGT.VanKampen.SymmetricLabelAlphabet
import GroupApproximation.GGT.VanKampen.CombMapEdgeSteps
import GroupApproximation.GGT.VanKampen.DiscEmbeddingAway
import GroupApproximation.GGT.VanKampen.Estimating.CyclicArcMap
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketEdgeDoubling
import GroupApproximation.Meta.AxiomGuard

/-!
# Chord lift: the corner digon at an exterior monogon, and the corner dispatcher

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

## The same-corner refinement

An edge from the corner of a dart `a` to itself (`EdgeInsertion.toCombMap M a a`) changes the
rotation only at the predecessor `z` of `a`: `σ' (embed z) = some none`, `σ' (some none) = none`,
`σ' none = embed a`.  So an old step is one new step, or three new steps past two new darts, and
`embed` is a rotation refinement (`RotationRefinement.sameCorner`).

## The exterior monogon

When `σ z = α z` and `face (α z)` is the exterior, the exterior has a single dart
(`not_one_lt_length_of_monogon`, and a face traversal is nonempty).  Doubling that dart
(`outerDiagram`) inserts an edge from the corner of `σ z` to itself.  The new exterior is the face of
the new dart, a monogon reading the old boundary word, and the new digon has value one, so the new
diagram is O-equivalent to the old one.  Every other face keeps its traversal (`outerEmbedding`).

The pocket transports along the embedding, except for the target arc: the outer traversal has one
dart and the target arc is proper, so the target arc is empty (`targetArc_darts_nil`), and it stays
empty at the same start position (`zeroArc`).  The boundary cycle, both sides and the source arc are
mapped lists, the source carrier is a mapped list (`outer_cellDarts_eq`), and vertices of old darts
are kept (`outer_hvert`), so walk order, repeated visits and properness of both arcs are kept.

The step `z → σ z` lifts to three steps with new intermediate darts, and `α' (embed z) = embed (α z)`
lies on the digon (`outer_face0`, `m = 0`), a G-face whose only old dart is `α z`
(`eq_of_outerDigon`); G-faces stay G-faces (`outer_transfer`).  This is `cornerDigon_outerMonogon`.

## The dispatcher

`cornerDigon_of_hone`: a monogon corner is inner (`cornerDigon_innerMonogon`) or exterior
(`cornerDigon_outerMonogon`); a non-monogon corner outside the face set with (H2) is
`cornerDigon_of_nonMonogon`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift

universe u w v

open Embedded Equiv PermOrbitInsert
open scoped Classical

section SameCorner

variable {M : CombMap.{v}}

theorem sameCorner_sigma_embed_of_eq {a z : M.Dart} (ha : M.sigma z = a) :
    (EdgeInsertion.toCombMap M a a).sigma (EdgeInsertion.embed M z) = some none := by
  classical
  change insertBefore (insertBefore M.sigma a) (some a) (some (some z)) = some none
  rw [insertBefore_some, insertBefore_some, ite_cond_eq_true _ _ (eq_true ha)]
  exact ite_cond_eq_false _ _ (eq_false (Option.some_ne_none a).symm)

theorem sameCorner_sigma_embed_of_ne {a z : M.Dart} (ha : M.sigma z ≠ a) :
    (EdgeInsertion.toCombMap M a a).sigma (EdgeInsertion.embed M z) =
      EdgeInsertion.embed M (M.sigma z) := by
  classical
  change insertBefore (insertBefore M.sigma a) (some a) (some (some z)) =
    some (some (M.sigma z))
  rw [insertBefore_some, insertBefore_some, ite_cond_eq_false _ _ (eq_false ha)]
  exact ite_cond_eq_false _ _ (eq_false fun h => ha (Option.some.inj h))

theorem sameCorner_sigma_some_none (a : M.Dart) :
    (EdgeInsertion.toCombMap M a a).sigma (some none) = none := by
  classical
  change insertBefore (insertBefore M.sigma a) (some a) (some none) = none
  rw [insertBefore_some, insertBefore_none]
  exact ite_cond_eq_true _ _ (eq_true rfl)

theorem sameCorner_sigma_none (a : M.Dart) :
    (EdgeInsertion.toCombMap M a a).sigma none = EdgeInsertion.embed M a := by
  change insertBefore (insertBefore M.sigma a) (some a) none = some (some a)
  exact insertBefore_none _ _

/-- **Three new steps at the corner of `a`.** -/
theorem sameCorner_sigma_three {a z : M.Dart} (ha : M.sigma z = a) :
    ((EdgeInsertion.toCombMap M a a).sigma ^ 3) (EdgeInsertion.embed M z) =
      EdgeInsertion.embed M (M.sigma z) := by
  rw [pow_three, Perm.mul_apply, Perm.mul_apply, sameCorner_sigma_embed_of_eq ha,
    sameCorner_sigma_some_none, sameCorner_sigma_none, ha]

theorem sameCorner_sigma_two {a z : M.Dart} (ha : M.sigma z = a) :
    ((EdgeInsertion.toCombMap M a a).sigma ^ 2) (EdgeInsertion.embed M z) = none := by
  rw [pow_two, Perm.mul_apply, sameCorner_sigma_embed_of_eq ha, sameCorner_sigma_some_none]

theorem sameCorner_sigma_one {a z : M.Dart} (ha : M.sigma z = a) :
    ((EdgeInsertion.toCombMap M a a).sigma ^ 1) (EdgeInsertion.embed M z) = some none := by
  rw [pow_one, sameCorner_sigma_embed_of_eq ha]

/-- No old dart in the middle of the three new steps. -/
theorem sameCorner_mid {a z : M.Dart} (ha : M.sigma z = a) :
    ∀ t, 0 < t → t < 3 → ∀ w, ((EdgeInsertion.toCombMap M a a).sigma ^ t)
      (EdgeInsertion.embed M z) ≠ EdgeInsertion.embed M w := by
  intro t ht ht3 w hw
  rcases (by omega : t = 1 ∨ t = 2) with rfl | rfl
  · rw [sameCorner_sigma_one ha] at hw
    simp [EdgeInsertion.embed] at hw
  · rw [sameCorner_sigma_two ha] at hw
    simp [EdgeInsertion.embed] at hw

end SameCorner

namespace RotationRefinement

variable {M : CombMap.{v}}

/-- **An edge from a corner to itself refines the rotation.** -/
noncomputable def sameCorner (a : M.Dart) :
    RotationRefinement M (EdgeInsertion.toCombMap M a a) where
  map := EdgeInsertion.embed M
  injective _ _ h := Option.some.inj (Option.some.inj h)
  alpha_map _ := rfl
  step z := by
    by_cases ha : M.sigma z = a
    · exact ⟨3, by omega, sameCorner_sigma_three ha, sameCorner_mid ha⟩
    · refine ⟨1, Nat.one_pos, ?_, fun t ht ht1 => absurd ht1 (by omega)⟩
      rw [pow_one]
      exact sameCorner_sigma_embed_of_ne ha

end RotationRefinement

/-- An empty arc at the start position of a given arc, on a cycle of the same length. -/
def zeroArc {A : Type*} {c : List A} {c' : List A} (arc : CyclicArc c)
    (h : c'.length = c.length) : CyclicArc c' where
  start := ⟨arc.start.1, by have hs := arc.start.2; omega⟩
  length := 0
  length_le := Nat.zero_le _

theorem zeroArc_darts {A : Type*} {c : List A} {c' : List A} (arc : CyclicArc c)
    (h : c'.length = c.length) : (zeroArc arc h).darts = [] :=
  List.take_zero

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {lo hi : ℕ}

variable (X : DiscDiagram.{u, w, v} W)

section Diagram

/-- A relator cell, moved to the image of its face. -/
noncomputable def outerCell (C : RelatorCell X.toCombMap X.outerFace W) :
    RelatorCell (MonogonDoubling.map X X.outerFace) (MonogonDoubling.cellFace X X.outerFace) W where
  face := MonogonDoubling.faceImage X X.outerFace C.face
  face_ne_outer h := MonogonDoubling.keep_ne_cellFace X X.outerFace C.face_ne_outer
    ((MonogonDoubling.faceImage_of_ne X X.outerFace C.face_ne_outer).symm.trans h)
  word := C.word
  word_mem := C.word_mem
  conjugator := C.conjugator
  reversed := C.reversed

/-- **The doubled diagram of a one-edge exterior.** -/
noncomputable def outerDiagram (hlen : (X.faceBoundary X.outerFace).darts.length = 1) :
    DiscDiagram.{u, w, v} W where
  toCombMap := MonogonDoubling.map X X.outerFace
  planar := EdgeInsertion.planar X.toCombMap _ _ X.planar
    (EdgeInsertion.corners_face_eq X.toCombMap (X.faceBoundary X.outerFace)
      (MonogonDoubling.zero X X.outerFace))
  label := MonogonDoubling.label X X.outerFace
  label_alpha := EdgeInsertion.insertLabel_alpha X.toCombMap X.label X.label_alpha _ _ _
  outerFace := MonogonDoubling.cellFace X X.outerFace
  faceBoundary := MonogonDoubling.boundary X X.outerFace
  relatorCells := X.relatorCells.map (outerCell X)
  relatorCell_faces_nodup := by
    have heq : (X.relatorCells.map (outerCell X)).map RelatorCell.face =
        (X.relatorCells.map RelatorCell.face).map (MonogonDoubling.faceImage X X.outerFace) := by
      rw [List.map_map, List.map_map]
      rfl
    rw [heq]
    exact X.relatorCell_faces_nodup.map (MonogonDoubling.faceImage_injective X X.outerFace)
  relatorCell_word := by
    intro C hC
    obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC
    exact (X.relatorCell_word C₀ hC₀).trans
      (MonogonDoubling.boundary_faceImage_word X X.outerFace hlen C₀.face).symm
  inner_face := by
    intro F hF
    rcases EdgeInsertion.face_partition X.toCombMap (X.faceBoundary X.outerFace)
        (MonogonDoubling.zero X X.outerFace) F with hpre | hsuf | ⟨g, hg, hkept⟩
    · exact (hF hpre).elim
    · right
      rw [hsuf]
      exact MonogonDoubling.boundary_digon_value X X.outerFace hlen
    · rcases X.inner_face g hg with ⟨C, hC, hCg⟩ | hval
      · left
        refine ⟨outerCell X C, List.mem_map.mpr ⟨C, hC, rfl⟩, ?_⟩
        change MonogonDoubling.faceImage X X.outerFace C.face = F
        rw [hCg, MonogonDoubling.faceImage_of_ne X X.outerFace hg, hkept]
      · right
        rw [hkept, MonogonDoubling.boundary_kept_word X X.outerFace hg]
        exact hval
  boundary_product := by
    have hvalues : (X.relatorCells.map (outerCell X)).map RelatorCell.value =
        X.relatorCells.map RelatorCell.value := by
      rw [List.map_map]
      rfl
    exact (congrArg List.prod hvalues).trans (X.boundary_product.trans
      (congrArg (fun word => RelLetter.listVal (RelWord.revInv word))
        (MonogonDoubling.boundary_cellFace_word X X.outerFace hlen).symm))

variable (hlen : (X.faceBoundary X.outerFace).darts.length = 1)

theorem outerBoundaryWord_eq : (outerDiagram X hlen).boundaryWord = X.boundaryWord :=
  congrArg RelWord.revInv (MonogonDoubling.boundary_cellFace_word X X.outerFace hlen)

/-- The relator cells, literally. -/
noncomputable def outerCellMap :
    Surgery.OrderedRCellMap X (outerDiagram X hlen) (MonogonDoubling.faceImage X X.outerFace) where
  cell := outerCell X
  face_eq _ := rfl
  word_eq _ := rfl
  conjugator_eq _ := rfl
  reversed_eq _ := rfl
  list_eq := rfl

noncomputable def outerReplacement : Surgery.OrderedGRegionReplacement.{u, w, v, v} X where
  diagram := outerDiagram X hlen
  outerWord_eq := outerBoundaryWord_eq X hlen
  cells := (outerCellMap X hlen).orderedTransport

noncomputable def outerOEquivalent : OEquivalentDiscDiagram X (outerDiagram X hlen) :=
  (outerReplacement X hlen).oEquivalent

theorem outerLabel_letter (D : RelGenSet G Lambda)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (d : (outerDiagram X hlen).toCombMap.Dart) :
    (symmetricLabelAlphabet D).IsLetter ((outerDiagram X hlen).label d) :=
  EdgeInsertion.insertLabel_admissible X.toCombMap (symmetricLabelAlphabet D)
    (symmetricLabelAlphabet.symmetric D) X.label hlabel _
    (HullSC.isLetter_relWordInv (symmetricLabelAlphabet D) (symmetricLabelAlphabet.symmetric D)
      (hlabel _)) d

/-- **The retained old darts and faces**; the old exterior goes to the new exterior. -/
noncomputable def outerEmbedding : DiscEmbeddingAway X (outerDiagram X hlen) X.outerFace where
  darts := ⟨EdgeInsertion.embed X.toCombMap, EdgeInsertion.embed_injective X.toCombMap⟩
  faces := ⟨MonogonDoubling.faceImage X X.outerFace,
    MonogonDoubling.faceImage_injective X X.outerFace⟩
  alpha _ := rfl
  label _ := rfl
  outer := (MonogonDoubling.faceImage_self X X.outerFace).symm
  face_boundary g hg :=
    (congrArg (fun F => (MonogonDoubling.boundary X X.outerFace F).darts)
      (MonogonDoubling.faceImage_of_ne X X.outerFace hg)).trans
      (MonogonDoubling.boundary_kept X X.outerFace hg)
  facePerm d hd := EdgeInsertion.facePerm_embed_of_ne X.toCombMap _ _ d
    (EdgeInsertion.corners_face_eq X.toCombMap (X.faceBoundary X.outerFace)
      (MonogonDoubling.zero X X.outerFace))
    (by rwa [EdgeInsertion.firstCorner_face X.toCombMap (X.faceBoundary X.outerFace)])

end Diagram

section Transport

variable (hlen : (X.faceBoundary X.outerFace).darts.length = 1)

theorem outer_hcell (k : Fin X.rCellCount) :
    (Embedded.cell (outerDiagram X hlen) ((outerCellMap X hlen).indexEquiv k)).face =
      (outerEmbedding X hlen).faces (Embedded.cell X k).face :=
  (congrArg RelatorCell.face ((outerCellMap X hlen).indexed_cell k)).trans
    ((outerCellMap X hlen).face_eq (Embedded.cell X k))

theorem outer_hvert (x y : X.toCombMap.Dart) :
    (outerDiagram X hlen).toCombMap.vertexOf ((outerEmbedding X hlen).darts x) =
      (outerDiagram X hlen).toCombMap.vertexOf ((outerEmbedding X hlen).darts y) ↔
      X.toCombMap.vertexOf x = X.toCombMap.vertexOf y :=
  GeodesicCollar.edgeInsertion_vertexOf_embed_iff X.toCombMap
    (EdgeInsertion.firstCorner X.toCombMap (X.faceBoundary X.outerFace))
    (EdgeInsertion.secondCorner X.toCombMap (X.faceBoundary X.outerFace)
      (MonogonDoubling.zero X X.outerFace)) x y

theorem outer_hvert_alpha (x y : X.toCombMap.Dart) :
    (outerDiagram X hlen).toCombMap.vertexOf
        ((outerDiagram X hlen).toCombMap.alpha ((outerEmbedding X hlen).darts x)) =
      (outerDiagram X hlen).toCombMap.vertexOf ((outerEmbedding X hlen).darts y) ↔
      X.toCombMap.vertexOf (X.toCombMap.alpha x) = X.toCombMap.vertexOf y := by
  rw [(outerEmbedding X hlen).alpha]
  exact outer_hvert X hlen _ y

/-- The source carrier is a mapped list. -/
theorem outer_cellDarts_eq (k : Fin X.rCellCount) :
    cellDarts (outerDiagram X hlen) ((outerCellMap X hlen).indexEquiv k) =
      (cellDarts X k).map (outerEmbedding X hlen).darts := by
  change ((outerDiagram X hlen).faceBoundary
      (Embedded.cell (outerDiagram X hlen) ((outerCellMap X hlen).indexEquiv k)).face).darts =
    (X.faceBoundary (Embedded.cell X k).face).darts.map (outerEmbedding X hlen).darts
  rw [outer_hcell X hlen k]
  exact (outerEmbedding X hlen).face_boundary _ (Embedded.cell X k).face_ne_outer

include hlen in
theorem outerDarts_length_one : (outerDarts X).length = 1 := by
  unfold outerDarts
  rw [List.length_map, List.length_reverse]
  exact hlen

theorem outerDiagram_outerDarts_length_one : (outerDarts (outerDiagram X hlen)).length = 1 := by
  unfold outerDarts
  rw [List.length_map, List.length_reverse]
  exact congrArg List.length (MonogonDoubling.boundary_cellFace X X.outerFace)

theorem outerDarts_length_eq :
    (outerDarts (outerDiagram X hlen)).length = (outerDarts X).length :=
  (outerDiagram_outerDarts_length_one X hlen).trans (outerDarts_length_one X hlen).symm

include hlen in
/-- A proper target arc on a one-dart exterior is empty. -/
theorem targetArc_darts_nil (K : PocketFaceSet D eps X lo hi)
    (htgt : K.targetArc.length < (outerDarts X).length) : K.targetArc.darts = [] := by
  have h0 : K.targetArc.length = 0 := by
    have h1 := outerDarts_length_one X hlen
    omega
  exact (congrArg (fun n => List.take n K.targetArc.rotated) h0).trans List.take_zero

/-- **The pocket across the doubling of a one-dart exterior.** -/
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
  sourceArc := K.sourceArc.mapTo (outerEmbedding X hlen).darts (outer_cellDarts_eq X hlen K.source)
  targetArc := zeroArc K.targetArc (outerDarts_length_eq X hlen)
  firstSide := K.firstSide.map (outerEmbedding X hlen).darts
  secondSide := K.secondSide.map (outerEmbedding X hlen).darts
  boundary := (outerEmbedding X hlen).boundaryCycle K.faces K.outerFace_not_mem K.boundary
  decomposition := by
    change K.boundary.cycle.map (outerEmbedding X hlen).darts = _
    rw [CyclicArc.mapTo_darts K.sourceArc (outerEmbedding X hlen).darts
        (outer_cellDarts_eq X hlen K.source),
      DiscEmbeddingAway.invDarts_map, K.decomposition, hta0, zeroArc_darts]
    simp only [List.map_append, List.map_nil, List.append_nil]
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

theorem outerMonogon_boundary_cycle :
    (outerMonogonPocket X hlen K hta0).boundary.cycle =
      K.boundary.cycle.map (outerEmbedding X hlen).darts :=
  rfl

/-- **The doubling keeps walk order.** -/
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

/-- **The doubling keeps the repeated visits.** -/
theorem outerMonogon_repeatedVisits :
    (outerMonogonPocket X hlen K hta0).repeatedVisits = K.repeatedVisits := by
  unfold PocketFaceSet.repeatedVisits
  rw [outerMonogon_boundary_cycle, List.length_map, List.map_map]
  congr 1
  exact card_toFinset_map_eq_of_iff
    ((outerDiagram X hlen).toCombMap.vertexOf ∘ (outerEmbedding X hlen).darts)
    X.toCombMap.vertexOf (fun a b => outer_hvert X hlen a b) _

theorem outerMonogon_source_proper (hprop : K.sourceArc.length < (cellDarts X K.source).length) :
    (outerMonogonPocket X hlen K hta0).sourceArc.length <
      (cellDarts (outerDiagram X hlen) (outerMonogonPocket X hlen K hta0).source).length := by
  have h1 : (outerMonogonPocket X hlen K hta0).sourceArc.length = K.sourceArc.length :=
    CyclicArc.mapTo_length K.sourceArc _ (outer_cellDarts_eq X hlen K.source)
  have h2 : (cellDarts (outerDiagram X hlen) ((outerCellMap X hlen).indexEquiv K.source)).length =
      (cellDarts X K.source).length :=
    (congrArg List.length (outer_cellDarts_eq X hlen K.source)).trans (List.length_map _)
  exact lt_of_eq_of_lt h1 (lt_of_lt_of_eq hprop h2.symm)

theorem outerMonogon_target_proper :
    (outerMonogonPocket X hlen K hta0).targetArc.length <
      (outerDarts (outerDiagram X hlen)).length := by
  show 0 < (outerDarts (outerDiagram X hlen)).length
  exact lt_of_lt_of_eq Nat.one_pos (outerDiagram_outerDarts_length_one X hlen).symm

end Transport

section Corner

variable (hlen : (X.faceBoundary X.outerFace).darts.length = 1)

theorem outer_face0 {z : X.toCombMap.Dart}
    (hfz : X.toCombMap.faceOf (X.toCombMap.alpha z) = X.outerFace) :
    (outerDiagram X hlen).toCombMap.faceOf
        ((outerDiagram X hlen).toCombMap.alpha
          (((outerDiagram X hlen).toCombMap.sigma ^ 0)
            ((RotationRefinement.sameCorner (MonogonDoubling.dart X X.outerFace)).map z))) =
      MonogonDoubling.digon X X.outerFace := by
  rw [pow_zero, Perm.one_apply]
  change (MonogonDoubling.map X X.outerFace).faceOf
      (EdgeInsertion.embed X.toCombMap (X.toCombMap.alpha z)) =
    MonogonDoubling.digon X X.outerFace
  exact MonogonDoubling.faceOf_embed_of_face X X.outerFace hfz

/-- **The digon of the exterior doubling is a G-face.** -/
theorem outer_digon_isGFace :
    IsGFaceOf (outerDiagram X hlen) (MonogonDoubling.digon X X.outerFace) := by
  refine ⟨MonogonDoubling.digon_ne_cellFace X X.outerFace, fun C hC => ?_⟩
  change C ∈ X.relatorCells.map (outerCell X) at hC
  obtain ⟨C₀, -, rfl⟩ := List.mem_map.mp hC
  exact MonogonDoubling.faceImage_ne_digon X X.outerFace C₀.face

include hlen in
/-- The only old dart on the digon is the dart of the exterior. -/
theorem eq_of_outerDigon {z w : X.toCombMap.Dart}
    (hfz : X.toCombMap.faceOf (X.toCombMap.alpha z) = X.outerFace)
    (hw : (MonogonDoubling.map X X.outerFace).faceOf (EdgeInsertion.embed X.toCombMap w) =
      MonogonDoubling.digon X X.outerFace) : w = X.toCombMap.alpha z := by
  by_cases hwf : X.toCombMap.faceOf w = X.outerFace
  · exact (MonogonDoubling.dart_eq_of_face X X.outerFace hlen hwf).symm.trans
      (MonogonDoubling.dart_eq_of_face X X.outerFace hlen hfz)
  · exact absurd ((MonogonDoubling.faceOf_embed_of_ne X X.outerFace hwf).symm.trans hw)
      (MonogonDoubling.keep_ne_digon X X.outerFace hwf)

/-- **A G-face stays a G-face.** -/
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

/-- **The corner digon at an exterior monogon corner.** -/
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
    ⟨outerLabel_letter X hlen D hlabel, outerMonogon_closedWalk X hlen K hta0 hK,
      outerMonogon_source_proper X hlen K hta0 hsrcP, outerMonogon_target_proper X hlen K hta0⟩,
    outerMonogon_repeatedVisits X hlen K hta0, outerMonogon_boundary_cycle X hlen K hta0,
    3, 0, by omega, sameCorner_sigma_three hσ, sameCorner_mid hσ,
    isGFaceOf_congr (outer_face0 X hlen hfz) (outer_digon_isGFace X hlen),
    fun w hw => Or.inl (eq_of_outerDigon X hlen hfz (hw.trans (outer_face0 X hlen hfz))),
    fun w hG _ => outer_transfer X hlen w hG⟩

/-- **The corner digon at a corner with (H2) whose face is outside the face set.** -/
theorem cornerDigon_of_hone (hW : ∀ word ∈ W, 1 < word.length) (K : PocketFaceSet D eps X lo hi)
    (z : X.toCombMap.Dart) (hinv : PocketInvariants K)
    (hs : X.toCombMap.faceOf (X.toCombMap.alpha z) ∉ K.faces)
    (hone : ¬ ∃ h : X.toCombMap.alpha (X.toCombMap.sigma z) ∈ K.boundary.cycle,
      K.boundary.cycle.next _ h = z) : CornerDigon K z := by
  by_cases hmono : X.toCombMap.sigma z = X.toCombMap.alpha z
  · by_cases hfo : X.toCombMap.faceOf (X.toCombMap.alpha z) = X.outerFace
    · exact cornerDigon_outerMonogon X K z hinv hfo hmono
    · exact cornerDigon_innerMonogon hW K z hinv hfo hmono
  · exact cornerDigon_of_nonMonogon X K z hinv hs hone hmono

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.RotationRefinement.sameCorner
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.outerDiagram
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.outerOEquivalent
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.outerEmbedding
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.outerMonogonPocket
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.outerMonogon_closedWalk
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.outerMonogon_repeatedVisits
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.cornerDigon_outerMonogon
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ChordLift.cornerDigon_of_hone
