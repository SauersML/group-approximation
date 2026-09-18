import GroupApproximation.Manuscript.NonMF.Full.GL06d.CornerStep
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
# Non-rose step: the doubling of a one-dart exterior

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b) (`thm:hull`).

## The same-corner refinement

An edge from the corner of a dart `a` to itself (`EdgeInsertion.toCombMap M a a`) changes the
rotation only at the predecessor `z` of `a`: `σ' (embed z) = some none`, `σ' (some none) = none`,
`σ' none = embed a`.  So an old step is one new step, or three new steps past two new darts, and
`embed` is a rotation refinement (`RotationRefinement.sameCorner`).

## The exterior doubling

When the exterior has a single dart, doubling it (`outerDiagram`) inserts an edge from the corner
of that dart to itself.  The new exterior is a monogon reading the old boundary word, the new
digon has value one, and the relator cells are moved literally, so the new diagram is
O-equivalent to the old one (`outerOEquivalent`).  Every other face keeps its traversal
(`outerEmbedding`).  An empty arc can be moved to a cycle of the same length (`zeroArc`).

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

section SameCorner

variable {M : CombMap.{v}}

/-- The predecessor of `a` steps to the first new dart (`thm:hull`). -/
theorem sameCorner_sigma_embed_of_eq {a z : M.Dart} (ha : M.sigma z = a) :
    (EdgeInsertion.toCombMap M a a).sigma (EdgeInsertion.embed M z) = some none := by
  classical
  change PermOrbitInsert.insertBefore (PermOrbitInsert.insertBefore M.sigma a) (some a)
    (some (some z)) = some none
  rw [PermOrbitInsert.insertBefore_some, PermOrbitInsert.insertBefore_some,
    ite_cond_eq_true _ _ (eq_true ha)]
  exact ite_cond_eq_false _ _ (eq_false (Option.some_ne_none a).symm)

/-- Any other old dart keeps its rotation step (`thm:hull`). -/
theorem sameCorner_sigma_embed_of_ne {a z : M.Dart} (ha : M.sigma z ≠ a) :
    (EdgeInsertion.toCombMap M a a).sigma (EdgeInsertion.embed M z) =
      EdgeInsertion.embed M (M.sigma z) := by
  classical
  change PermOrbitInsert.insertBefore (PermOrbitInsert.insertBefore M.sigma a) (some a)
    (some (some z)) = some (some (M.sigma z))
  rw [PermOrbitInsert.insertBefore_some, PermOrbitInsert.insertBefore_some,
    ite_cond_eq_false _ _ (eq_false ha)]
  exact ite_cond_eq_false _ _ (eq_false fun h => ha (Option.some.inj h))

/-- The first new dart steps to the second (`thm:hull`). -/
theorem sameCorner_sigma_some_none (a : M.Dart) :
    (EdgeInsertion.toCombMap M a a).sigma (some none) = none := by
  classical
  change PermOrbitInsert.insertBefore (PermOrbitInsert.insertBefore M.sigma a) (some a)
    (some none) = none
  rw [PermOrbitInsert.insertBefore_some, PermOrbitInsert.insertBefore_none]
  exact ite_cond_eq_true _ _ (eq_true rfl)

/-- The second new dart steps to `a` (`thm:hull`). -/
theorem sameCorner_sigma_none (a : M.Dart) :
    (EdgeInsertion.toCombMap M a a).sigma none = EdgeInsertion.embed M a := by
  change PermOrbitInsert.insertBefore (PermOrbitInsert.insertBefore M.sigma a) (some a) none =
    some (some a)
  exact PermOrbitInsert.insertBefore_none _ _

/-- **Three new steps at the corner of `a`** (`thm:hull`). -/
theorem sameCorner_sigma_three {a z : M.Dart} (ha : M.sigma z = a) :
    ((EdgeInsertion.toCombMap M a a).sigma ^ 3) (EdgeInsertion.embed M z) =
      EdgeInsertion.embed M (M.sigma z) := by
  rw [pow_three, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, sameCorner_sigma_embed_of_eq ha,
    sameCorner_sigma_some_none, sameCorner_sigma_none, ha]

/-- Two new steps reach the second new dart (`thm:hull`). -/
theorem sameCorner_sigma_two {a z : M.Dart} (ha : M.sigma z = a) :
    ((EdgeInsertion.toCombMap M a a).sigma ^ 2) (EdgeInsertion.embed M z) = none := by
  rw [pow_two, Equiv.Perm.mul_apply, sameCorner_sigma_embed_of_eq ha,
    sameCorner_sigma_some_none]

/-- One new step reaches the first new dart (`thm:hull`). -/
theorem sameCorner_sigma_one {a z : M.Dart} (ha : M.sigma z = a) :
    ((EdgeInsertion.toCombMap M a a).sigma ^ 1) (EdgeInsertion.embed M z) = some none := by
  rw [pow_one, sameCorner_sigma_embed_of_eq ha]

/-- No old dart in the middle of the three new steps (`thm:hull`). -/
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

/-- **An edge from a corner to itself refines the rotation** (`thm:hull`). -/
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

/-- An empty arc at the start position of a given arc, on a cycle of the same length
(`thm:hull`). -/
def zeroArc {A : Type*} {c : List A} {c' : List A} (arc : CyclicArc c)
    (h : c'.length = c.length) : CyclicArc c' where
  start := ⟨arc.start.1, by rw [h]; exact arc.start.2⟩
  length := 0
  length_le := Nat.zero_le _

/-- The empty arc has no darts (`thm:hull`). -/
theorem zeroArc_darts {A : Type*} {c : List A} {c' : List A} (arc : CyclicArc c)
    (h : c'.length = c.length) : (zeroArc arc h).darts = [] :=
  List.take_zero

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda}

variable (X : DiscDiagram.{u, w, v} W)

section Diagram

/-- A relator cell, moved to the image of its face (`thm:hull`). -/
noncomputable def outerCell (C : RelatorCell X.toCombMap X.outerFace W) :
    RelatorCell (MonogonDoubling.map X X.outerFace)
      (MonogonDoubling.cellFace X X.outerFace) W where
  face := MonogonDoubling.faceImage X X.outerFace C.face
  face_ne_outer h := MonogonDoubling.keep_ne_cellFace X X.outerFace C.face_ne_outer
    ((MonogonDoubling.faceImage_of_ne X X.outerFace C.face_ne_outer).symm.trans h)
  word := C.word
  word_mem := C.word_mem
  conjugator := C.conjugator
  reversed := C.reversed

/-- **The doubled diagram of a one-edge exterior** (`thm:hull`). -/
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

/-- The doubling keeps the boundary word (`thm:hull`). -/
theorem outerBoundaryWord_eq : (outerDiagram X hlen).boundaryWord = X.boundaryWord :=
  congrArg RelWord.revInv (MonogonDoubling.boundary_cellFace_word X X.outerFace hlen)

/-- The relator cells, literally (`thm:hull`). -/
noncomputable def outerCellMap :
    Surgery.OrderedRCellMap X (outerDiagram X hlen)
      (MonogonDoubling.faceImage X X.outerFace) where
  cell := outerCell X
  face_eq _ := rfl
  word_eq _ := rfl
  conjugator_eq _ := rfl
  reversed_eq _ := rfl
  list_eq := rfl

/-- The doubling as an ordered replacement (`thm:hull`). -/
noncomputable def outerReplacement : Surgery.OrderedGRegionReplacement.{u, w, v, v} X where
  diagram := outerDiagram X hlen
  outerWord_eq := outerBoundaryWord_eq X hlen
  cells := (outerCellMap X hlen).orderedTransport

/-- **The doubled diagram is O-equivalent** (`thm:hull`). -/
noncomputable def outerOEquivalent : OEquivalentDiscDiagram X (outerDiagram X hlen) :=
  (outerReplacement X hlen).oEquivalent

/-- The doubling keeps labels letters of the symmetric alphabet (`thm:hull`). -/
theorem outerLabel_letter (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (d : (outerDiagram X hlen).toCombMap.Dart) :
    (symmetricLabelAlphabet D).IsLetter ((outerDiagram X hlen).label d) :=
  EdgeInsertion.insertLabel_admissible X.toCombMap (symmetricLabelAlphabet D)
    (symmetricLabelAlphabet.symmetric D) X.label hlabel _
    (HullSC.isLetter_relWordInv (symmetricLabelAlphabet D) (symmetricLabelAlphabet.symmetric D)
      (hlabel _)) d

/-- **The retained old darts and faces**; the old exterior goes to the new exterior
(`thm:hull`). -/
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

end GroupApproximation.Full.GL06d

#audit_axioms GroupApproximation.Full.GL06d.sameCorner_sigma_embed_of_eq
#audit_axioms GroupApproximation.Full.GL06d.sameCorner_sigma_embed_of_ne
#audit_axioms GroupApproximation.Full.GL06d.sameCorner_sigma_some_none
#audit_axioms GroupApproximation.Full.GL06d.sameCorner_sigma_none
#audit_axioms GroupApproximation.Full.GL06d.sameCorner_sigma_three
#audit_axioms GroupApproximation.Full.GL06d.sameCorner_sigma_two
#audit_axioms GroupApproximation.Full.GL06d.sameCorner_sigma_one
#audit_axioms GroupApproximation.Full.GL06d.sameCorner_mid
#audit_axioms GroupApproximation.Full.GL06d.RotationRefinement.sameCorner
#audit_axioms GroupApproximation.Full.GL06d.zeroArc
#audit_axioms GroupApproximation.Full.GL06d.zeroArc_darts
#audit_axioms GroupApproximation.Full.GL06d.outerCell
#audit_axioms GroupApproximation.Full.GL06d.outerDiagram
#audit_axioms GroupApproximation.Full.GL06d.outerBoundaryWord_eq
#audit_axioms GroupApproximation.Full.GL06d.outerCellMap
#audit_axioms GroupApproximation.Full.GL06d.outerReplacement
#audit_axioms GroupApproximation.Full.GL06d.outerOEquivalent
#audit_axioms GroupApproximation.Full.GL06d.outerLabel_letter
#audit_axioms GroupApproximation.Full.GL06d.outerEmbedding
