import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketColourNoncrossing
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionSimpleWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchStep
import GroupApproximation.GGT.VanKampen.SimpleClosedWalkSideFaces
import GroupApproximation.Meta.AxiomGuard

/-!
# The pocket face set between two cells

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): two distinct selected regions joining the
same two distinct cells `Π_i` and `Π_j` bound a subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`, where `s_1`, `s_2` are sides of the two regions and `t_1`, `t_2` are
arcs of `Π_i` and `Π_j`.

This module is step 6 of the binder-5 route to the copy form of `MultipleEdgePocketRegionInput`.
It is the cell-to-cell analogue of `PocketFaceSet` (`Estimating/OsinPocketPieces.lean`), of its
builders (`Estimating/OsinPocketSectionFaceSet.lean`), and of `pocketRegionOfSimple`
(`Estimating/OsinPocketRegionOfSimple.lean`).

* `CellPocketFaceSet D eps X i j`: a face set away from the exterior face and from both cells,
  holding a relator cell, whose boundary cycle is `s_1 t_1 s_2 t_2`, with `t_1` a nonempty arc of
  `Π_i` and `t_2` a nonempty arc of `Π_j`, both read backwards.  `ClosedWalk` and `Simple` are as
  for `PocketFaceSet`.
* `CellPocketFaceSet.ofBoundaryCycle`, `ofNoncrossingClosedWalk`: the builders.  Both cells lie
  across arc darts, so they are off the face set.  The exterior face is not adjacent to the walk,
  so its absence is a hypothesis (`hout`).
* `CellPocketWalk.exists_cellPocketFaceSet_closedWalk_of_orient`: the oriented pocket walk of
  steps 2–4, with a relator cell on its side and the exterior face off it, bounds a cell pocket
  face set in walk order.
* `CellPocketFaceSet.exists_pocketRegion_of_simple`: a simple cell pocket face set gives a pocket
  region with both cycles following their boundaries, the relator cell inside, both cells outside
  and the decomposition of the inverse complement cycle.  Its inner cycle is the walk, as ms-intro-2's
  `CellPocketKeptCellStatement` consumes.
* `CellPocketPinchPosStatement`: the pinch, at `0 < eps`, stated and not proved here.  At
  `eps = 0` the rose shape that refuted `PocketPinchLabelledStatement` applies.
* `CellPocketFaceSet.copyRegion_of_pinch`: from the pinch, a cell pocket face set in walk order
  gives the data of the copy form of `MultipleEdgePocketRegionInput` on an O-equivalent copy.

Residuals for the route: `CellPocketPinchPosStatement`; the exterior face off the walk's side for
the walk of `CellPocketWalk.exists_of_joinsCells` (a lake of one cell is a known obstruction to
following outer cycles, `OsinPocketMultipleEdgeLakeModel`); and a relator cell on the side of a
noncrossing walk (step 5 proves it for pocket regions).

## Manuscript status

Infrastructure for `thm:hull` (tex 2121 at origin/main 68481e4d7,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(b);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides

section FaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **The face set between two cells** (Osin's `Γ_1` for two regions joining `Π_i` and `Π_j`).  A
face set away from the exterior face and from both cells, with a relator cell `kept` inside, whose
boundary cycle is `s_1 t_1 s_2 t_2`: a side `s_1`, a nonempty arc `t_1` of `Π_i` read backwards, a
side `s_2`, and a nonempty arc `t_2` of `Π_j` read backwards.  The sides and their values are no
longer than `ε`. -/
structure CellPocketFaceSet (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    (i j : Fin X.rCellCount) where
  faces : Finset X.toCombMap.Face
  outerFace_not_mem : X.outerFace ∉ faces
  first_not_mem : (cell X i).face ∉ faces
  second_not_mem : (cell X j).face ∉ faces
  kept : Fin X.rCellCount
  kept_mem : (cell X kept).face ∈ faces
  firstArc : CyclicArc (cellDarts X i)
  secondArc : CyclicArc (cellDarts X j)
  firstSide : List X.toCombMap.Dart
  secondSide : List X.toCombMap.Dart
  boundary : Surgery.MapCollapse.BoundaryCycle X.toCombMap faces
  decomposition : boundary.cycle =
    firstSide ++ invDarts X firstArc.darts ++ secondSide ++ invDarts X secondArc.darts
  firstArc_pos : 0 < firstArc.length
  secondArc_pos : 0 < secondArc.length
  firstSide_length_le : firstSide.length ≤ eps
  secondSide_length_le : secondSide.length ≤ eps
  firstSide_norm_le :
    wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X firstSide)) ≤ eps
  secondSide_norm_le :
    wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X secondSide)) ≤ eps

namespace CellPocketFaceSet

variable {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **A cell pocket in walk order**: the boundary cycle is a closed walk. -/
def ClosedWalk (K : CellPocketFaceSet D eps X i j) : Prop :=
  K.boundary.cycle.IsChain
      (fun d e => X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e) ∧
    X.toCombMap.vertexOf
        (X.toCombMap.alpha (K.boundary.cycle.getLast K.boundary.cycle_nonempty)) =
      X.toCombMap.vertexOf (K.boundary.cycle.head K.boundary.cycle_nonempty)

/-- **A simple cell pocket**: the boundary cycle is a simple closed walk. -/
def Simple (K : CellPocketFaceSet D eps X i j) : Prop :=
  IsSimpleClosedWalk X.toCombMap K.boundary.cycle

/-- A simple cell pocket is in walk order. -/
theorem Simple.closedWalk {K : CellPocketFaceSet D eps X i j} (hK : K.Simple) : K.ClosedWalk :=
  ⟨hK.chain, hK.closes⟩

/-- **The cell pocket face set of a boundary cycle.**  When the face set has the boundary cycle
`s_1 t_1 s_2 t_2`, contains the cell `kept` and not the exterior face, both cells lie across arc
darts and so are off the face set. -/
noncomputable def ofBoundaryCycle {faces : Finset X.toCombMap.Face}
    (boundary : Surgery.MapCollapse.BoundaryCycle X.toCombMap faces) (kept : Fin X.rCellCount)
    (firstArc : CyclicArc (cellDarts X i)) (secondArc : CyclicArc (cellDarts X j))
    (firstSide secondSide : List X.toCombMap.Dart)
    (hcycle : boundary.cycle =
      firstSide ++ invDarts X firstArc.darts ++ secondSide ++ invDarts X secondArc.darts)
    (hout : X.outerFace ∉ faces) (hfirstPos : 0 < firstArc.length)
    (hsecondPos : 0 < secondArc.length) (hkept : (cell X kept).face ∈ faces)
    (hfirst : firstSide.length ≤ eps) (hsecond : secondSide.length ≤ eps)
    (hfirstNorm :
      wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X firstSide)) ≤ eps)
    (hsecondNorm :
      wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X secondSide)) ≤ eps) :
    CellPocketFaceSet D eps X i j where
  faces := faces
  outerFace_not_mem := hout
  first_not_mem := by
    obtain ⟨e, he⟩ := firstArc.exists_mem_darts hfirstPos
    have hface : X.toCombMap.faceOf e = (cell X i).face :=
      ((X.faceBoundary (cell X i).face).mem_iff e).mp (firstArc.mem_cycle_of_mem_darts he)
    have hinv : X.toCombMap.alpha e ∈ invDarts X firstArc.darts :=
      List.mem_map_of_mem (List.mem_reverse.mpr he)
    have hmem : X.toCombMap.alpha e ∈ boundary.cycle := by
      rw [hcycle]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hinv))
    have h := And.right ((boundary.cycle_mem_iff (X.toCombMap.alpha e)).mp hmem)
    rwa [X.toCombMap.alpha_involutive e, hface] at h
  second_not_mem := by
    obtain ⟨e, he⟩ := secondArc.exists_mem_darts hsecondPos
    have hface : X.toCombMap.faceOf e = (cell X j).face :=
      ((X.faceBoundary (cell X j).face).mem_iff e).mp (secondArc.mem_cycle_of_mem_darts he)
    have hinv : X.toCombMap.alpha e ∈ invDarts X secondArc.darts :=
      List.mem_map_of_mem (List.mem_reverse.mpr he)
    have hmem : X.toCombMap.alpha e ∈ boundary.cycle := by
      rw [hcycle]
      exact List.mem_append_right _ hinv
    have h := And.right ((boundary.cycle_mem_iff (X.toCombMap.alpha e)).mp hmem)
    rwa [X.toCombMap.alpha_involutive e, hface] at h
  kept := kept
  kept_mem := hkept
  firstArc := firstArc
  secondArc := secondArc
  firstSide := firstSide
  secondSide := secondSide
  boundary := boundary
  decomposition := hcycle
  firstArc_pos := hfirstPos
  secondArc_pos := hsecondPos
  firstSide_length_le := hfirst
  secondSide_length_le := hsecond
  firstSide_norm_le := hfirstNorm
  secondSide_norm_le := hsecondNorm

/-- **The region of a simple cell pocket.**  A simple cell pocket face set is on the side of its
boundary cycle, so `PocketRegion.ofSimpleClosedWalk` makes it a pocket region.  Both of its cycles
follow their boundaries, the relator cell is inside and both cells are outside, the inverse
complement cycle is the walk `s_1 t_1 s_2 t_2`, and the inner cycle is the walk. -/
theorem exists_pocketRegion_of_simple (K : CellPocketFaceSet D eps X i j) (hK : K.Simple) :
    ∃ (P : PocketRegion X) (C : RelatorCell X.toCombMap X.outerFace W),
      C ∈ X.relatorCells ∧ C.face ∈ P.faces ∧
        (cell X i).face ∉ P.faces ∧ (cell X j).face ∉ P.faces ∧
        invDarts X P.outer.cycle =
          K.firstSide ++ invDarts X K.firstArc.darts ++ K.secondSide ++
            invDarts X K.secondArc.darts ∧
        wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X K.firstSide)) ≤ eps ∧
        wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X K.secondSide)) ≤ eps ∧
        P.inner.FollowsBoundary ∧ P.outer.FollowsBoundary ∧ P.inner.cycle = K.boundary.cycle := by
  have hfaces : sideFaces X.toCombMap K.boundary.cycle = K.faces :=
    sideFaces_boundaryCycle_eq (CombMap.connected_of_planar _ X.planar) K.boundary
      K.outerFace_not_mem
  have hout : X.outerFace ∉ sideFaces X.toCombMap K.boundary.cycle := by
    rw [hfaces]
    exact K.outerFace_not_mem
  refine ⟨PocketRegion.ofSimpleClosedWalk hK hout, cell X K.kept, cell_mem X K.kept, ?_, ?_, ?_,
    ?_, K.firstSide_norm_le, K.secondSide_norm_le,
    (PocketRegion.ofSimpleClosedWalk_followsBoundary hK hout).1,
    (PocketRegion.ofSimpleClosedWalk_followsBoundary hK hout).2, rfl⟩
  · rw [PocketRegion.ofSimpleClosedWalk_faces, hfaces]
    exact K.kept_mem
  · rw [PocketRegion.ofSimpleClosedWalk_faces, hfaces]
    exact K.first_not_mem
  · rw [PocketRegion.ofSimpleClosedWalk_faces, hfaces]
    exact K.second_not_mem
  · rw [PocketRegion.ofSimpleClosedWalk_invDarts_outer]
    exact K.decomposition

end CellPocketFaceSet

namespace CellPocketWalk

variable {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **The cell pocket face set of a noncrossing pocket walk** with a relator cell on its side and
the exterior face off it: the faces on the walk's side, with the walk as boundary cycle. -/
noncomputable def toCellPocketFaceSetOfNoncrossing (K : CellPocketWalk D eps X i j)
    (kept : Fin X.rCellCount) (hw : IsNoncrossingClosedWalk X.toCombMap K.walk)
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk)
    (hkept : (cell X kept).face ∈ sideFaces X.toCombMap K.walk) :
    CellPocketFaceSet D eps X i j :=
  CellPocketFaceSet.ofBoundaryCycle (hw.innerCycle X.planar) kept K.firstArc K.secondArc
    K.firstSide K.secondSide rfl hout K.firstArc_pos K.secondArc_pos hkept
    K.firstSide_length_le K.secondSide_length_le K.firstSide_norm_le K.secondSide_norm_le

theorem toCellPocketFaceSetOfNoncrossing_cycle (K : CellPocketWalk D eps X i j)
    (kept : Fin X.rCellCount) (hw : IsNoncrossingClosedWalk X.toCombMap K.walk)
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk)
    (hkept : (cell X kept).face ∈ sideFaces X.toCombMap K.walk) :
    (K.toCellPocketFaceSetOfNoncrossing kept hw hout hkept).boundary.cycle = K.walk :=
  rfl

/-- **The oriented cell pocket walk bounds a cell pocket face set in walk order.**  Let the pocket
walk be a closed walk of distinct darts using no edge in both directions, oriented by every
two-colouring changing colour exactly across it, with a relator cell on its side and the exterior
face off it. -/
theorem exists_cellPocketFaceSet_closedWalk_of_orient (K : CellPocketWalk D eps X i j)
    (hne : K.walk ≠ []) (hnodup : K.walk.Nodup)
    (halpha : ∀ d ∈ K.walk, X.toCombMap.alpha d ∉ K.walk)
    (hchain : K.walk.IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e)
    (hcloses : X.toCombMap.vertexOf (X.toCombMap.alpha (K.walk.getLast hne)) =
      X.toCombMap.vertexOf (K.walk.head hne))
    (horient : ∀ faces : Finset X.toCombMap.Face,
      (∀ d, ¬ (X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ faces ↔
        X.toCombMap.faceOf d ∈ faces) ↔ walkKeep X.toCombMap K.walk d) →
        ∀ d ∈ K.walk, ∀ e ∈ K.walk,
          (X.toCombMap.faceOf d ∈ faces ↔ X.toCombMap.faceOf e ∈ faces))
    (hout : X.outerFace ∉ sideFaces X.toCombMap K.walk)
    (hkept : ∃ kept : Fin X.rCellCount, (cell X kept).face ∈ sideFaces X.toCombMap K.walk) :
    ∃ P : CellPocketFaceSet D eps X i j, P.boundary.cycle = K.walk ∧ P.ClosedWalk := by
  obtain ⟨kept, hkept⟩ := hkept
  have hw := ClosedWalkFaceColouring.isNoncrossingClosedWalk_of_orient X.planar hne hnodup
    halpha hchain hcloses horient
  exact ⟨K.toCellPocketFaceSetOfNoncrossing kept hw hout hkept, rfl, ⟨hw.chain, hw.closes⟩⟩

end CellPocketWalk

end FaceSet

/-- **The pinch between two cells, at a positive side bound** (binder 5, step 6).  A cell pocket
face set in walk order, of a diagram whose labels are letters of the symmetrized alphabet, with
side bound `ε > 0`, has an O-equivalent copy with letter labels and a simple cell pocket face set.
Stated here, not proved.  At `ε = 0` the relator words may all have one letter, and then no cell
pocket face set is simple: this is the shape that refuted `PocketPinchLabelledStatement`. -/
def CellPocketPinchPosStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (eps : ℕ), 0 < eps →
    ∀ (W : Set (List (RelLetter G Lambda))) (X : DiscDiagram.{u, w, v} W)
      (i j : Fin X.rCellCount),
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
      ∀ K : CellPocketFaceSet D eps X i j, K.ClosedWalk →
        ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
          (K' : CellPocketFaceSet D eps X' i' j'),
          Nonempty (OEquivalentDiscDiagram X X') ∧
            (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ K'.Simple

namespace CellPocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **The region data of the copy form of `MultipleEdgePocketRegionInput`, from the pinch.**  A
cell pocket face set in walk order, of a diagram with letter labels at `ε > 0`, gives an
O-equivalent copy with letter labels and a pocket region with a relator cell inside, two cells
outside, the inverse complement cycle `s_1 t_1 s_2 t_2`, sides of word norm at most `ε`, and both
cycles following their boundaries. -/
theorem copyRegion_of_pinch (hpinch : CellPocketPinchPosStatement.{u, w, v}) (heps : 0 < eps)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : CellPocketFaceSet D eps X i j) (hK : K.ClosedWalk) :
    ∃ X' : DiscDiagram.{u, w, v} W, Nonempty (OEquivalentDiscDiagram X X') ∧
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
      ∃ (P : PocketRegion X') (C : RelatorCell X'.toCombMap X'.outerFace W)
        (i' j' : Fin X'.rCellCount) (s₁ s₂ : List X'.toCombMap.Dart)
        (A₁ : CyclicArc (cellDarts X' i')) (A₂ : CyclicArc (cellDarts X' j')),
        C ∈ X'.relatorCells ∧ C.face ∈ P.faces ∧
          (cell X' i').face ∉ P.faces ∧ (cell X' j').face ∉ P.faces ∧
          invDarts X' P.outer.cycle = s₁ ++ invDarts X' A₁.darts ++ s₂ ++ invDarts X' A₂.darts ∧
          wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X' s₁)) ≤ eps ∧
          wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X' s₂)) ≤ eps ∧
          P.inner.FollowsBoundary ∧ P.outer.FollowsBoundary := by
  obtain ⟨X', i', j', K', hE, hlabel', hsimple⟩ := hpinch D eps heps W X i j hlabel K hK
  obtain ⟨P, C, hC, hCf, hi, hj, hdec, hn₁, hn₂, hin, hout, -⟩ :=
    K'.exists_pocketRegion_of_simple hsimple
  exact ⟨X', hE, hlabel', P, C, i', j', K'.firstSide, K'.secondSide, K'.firstArc, K'.secondArc,
    hC, hCf, hi, hj, hdec, hn₁, hn₂, hin, hout⟩

end CellPocketFaceSet

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.ofBoundaryCycle
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.Simple.closedWalk
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.exists_pocketRegion_of_simple
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWalk.toCellPocketFaceSetOfNoncrossing_cycle
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketWalk.exists_cellPocketFaceSet_closedWalk_of_orient
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketPinchPosStatement
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.copyRegion_of_pinch
