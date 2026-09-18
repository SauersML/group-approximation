import GroupApproximation.Manuscript.NonMF.Full.GL03B.Statement
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedNoncrossingSucc
import GroupApproximation.GGT.VanKampen.FaceShelling
import GroupApproximation.Meta.AxiomGuard

/-!
# The enclosed inner pocket when the complement cycle follows its boundary

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's Lemma 9.7).

If the complement cycle of the pocket walk `K.walk = s_1 Ā_1 s_2 Ā_2` follows its boundary walk,
the faces on the side of the walk already form an enclosed face set that turns to its successor
(`enclosedFaceSetSuccOfNoncrossing`).  Its outside walk is `invDarts K.walk`, whose inverse is
`K.walk` itself, and the arcs of `Π_i`, `Π_j` of `K` lie on the walk, so both cells are off the side.

* `cell_face_not_mem_sideFaces`: a cell with a nonempty arc read backwards along a noncrossing walk
  is off the side of the walk.
* `innerPocketEnclosedTwoArc_of_followsBoundary`: the conclusion of
  `InnerPocketEnclosedTwoArcLocal` when the complement cycle follows its boundary walk.
* `innerPocketEnclosedTwoArcLocal_of_pinched`: the pinched case gives the whole local statement.
-/

namespace GroupApproximation.Full.GL03B

universe u w v

open GroupApproximation.GGT GroupApproximation.GGT.VanKampen

/-- **A cell is off the side of a noncrossing walk through its arc.**  If the reversal of a
nonempty arc of `Π_k` lies on a noncrossing walk, then `Π_k` is off the side of the walk: the
reversal of an arc dart is a boundary dart of the side, so the face across it, `Π_k`, is off. -/
theorem cell_face_not_mem_sideFaces {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {X : DiscDiagram.{u, w, v} W}
    {walk : List X.toCombMap.Dart} (hw : IsNoncrossingClosedWalk X.toCombMap walk)
    {k : Fin X.rCellCount} (A : Embedded.CyclicArc (Embedded.cellDarts X k))
    (hA : 0 < A.length) (hsub : ∀ d ∈ Embedded.invDarts X A.darts, d ∈ walk) :
    (Embedded.cell X k).face ∉ SimpleClosedWalkSides.sideFaces X.toCombMap walk := by
  obtain ⟨d, hd⟩ := A.exists_mem_darts hA
  have hmem : X.toCombMap.alpha d ∈ Embedded.invDarts X A.darts := by
    show X.toCombMap.alpha d ∈ A.darts.reverse.map X.toCombMap.alpha
    exact List.mem_map_of_mem (List.mem_reverse.mpr hd)
  have hface : X.toCombMap.faceOf d = (Embedded.cell X k).face :=
    ((X.faceBoundary (Embedded.cell X k).face).mem_iff d).mp (A.mem_cycle_of_mem_darts hd)
  have h := And.right ((hw.isBoundaryDart_sideFaces_iff X.planar _).mpr (hsub _ hmem))
  rwa [X.toCombMap.alpha_involutive d, hface] at h

/-- **The enclosed inner pocket, following case.**  If the complement cycle of the pocket walk
follows its boundary walk, the faces on the side of `K.walk`, with outside walk
`invDarts K.walk`, give the conclusion of `InnerPocketEnclosedTwoArcLocal`, with arcs `K.firstArc`,
`K.secondArc` and sides `K.firstSide`, `K.secondSide` (Osin, proof of Lemma 9.7(b); `thm:hull`). -/
theorem innerPocketEnclosedTwoArc_of_followsBoundary {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {eps : ℕ}
    {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount} (K : CellPocketWalk D eps X i j)
    (hw : IsNoncrossingClosedWalk X.toCombMap K.walk)
    (hout : X.outerFace ∉ SimpleClosedWalkSides.sideFaces X.toCombMap K.walk)
    (hfollows : (hw.outerCycle X.planar).FollowsBoundary)
    {C : RelatorCell X.toCombMap X.outerFace W} (hC : C ∈ X.relatorCells)
    (hCf : C.face ∈ SimpleClosedWalkSides.sideFaces X.toCombMap K.walk) :
    ∃ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart)
      (k₁ k₂ : Fin X.rCellCount) (A₁ : Embedded.CyclicArc (Embedded.cellDarts X k₁))
      (A₂ : Embedded.CyclicArc (Embedded.cellDarts X k₂)) (s₁ s₂ : List X.toCombMap.Dart),
      EnclosedFaceSetSucc X faces outerWalk ∧
        (∃ C' ∈ X.relatorCells, C'.face ∈ faces) ∧
        (Embedded.cell X k₁).face ∉ faces ∧ (Embedded.cell X k₂).face ∉ faces ∧
        Embedded.invDarts X outerWalk =
          s₁ ++ Embedded.invDarts X A₁.darts ++ s₂ ++ Embedded.invDarts X A₂.darts ∧
        s₁.length ≤ eps ∧ s₂.length ≤ eps ∧ (A₁.length = 0 ∨ 0 < A₂.length) := by
  have hsub₁ : ∀ d ∈ Embedded.invDarts X K.firstArc.darts, d ∈ K.walk := by
    intro d hd
    show d ∈ K.firstSide ++ Embedded.invDarts X K.firstArc.darts ++ K.secondSide ++
      Embedded.invDarts X K.secondArc.darts
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
      (List.mem_append.mpr (Or.inr hd)))))
  have hsub₂ : ∀ d ∈ Embedded.invDarts X K.secondArc.darts, d ∈ K.walk := by
    intro d hd
    show d ∈ K.firstSide ++ Embedded.invDarts X K.firstArc.darts ++ K.secondSide ++
      Embedded.invDarts X K.secondArc.darts
    exact List.mem_append.mpr (Or.inr hd)
  refine ⟨SimpleClosedWalkSides.sideFaces X.toCombMap K.walk, Embedded.invDarts X K.walk, i, j,
    K.firstArc, K.secondArc, K.firstSide, K.secondSide,
    enclosedFaceSetSuccOfNoncrossing hw hout hfollows, ⟨C, hC, hCf⟩,
    cell_face_not_mem_sideFaces hw K.firstArc K.firstArc_pos hsub₁,
    cell_face_not_mem_sideFaces hw K.secondArc K.secondArc_pos hsub₂,
    (Embedded.invDarts_invDarts K.walk).trans rfl, K.firstSide_length_le,
    K.secondSide_length_le, Or.inr K.secondArc_pos⟩

/-- **The enclosed inner pocket from its pinched case.**  Split on whether the complement cycle of
the pocket walk follows its boundary walk: the following case is
`innerPocketEnclosedTwoArc_of_followsBoundary`, the other one is the pinched statement (Osin, proof
of Lemma 9.7(b); `thm:hull`). -/
theorem innerPocketEnclosedTwoArcLocal_of_pinched
    (h : InnerPocketEnclosedTwoArcPinchedLocal.{u, w, v}) :
    InnerPocketEnclosedTwoArcLocal.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hout
    hinner houter C hC hCf hCa hCb
  by_cases hfollows : (hw.outerCycle X.planar).FollowsBoundary
  · exact innerPocketEnclosedTwoArc_of_followsBoundary K hw hout hfollows hC hCf
  · exact h D eps X a b K hij hai hbi hab hlabel hW hfirst hsecond h₁ h₂ hw hout hinner houter
      hfollows C hC hCf hCa hCb

end GroupApproximation.Full.GL03B

#audit_axioms GroupApproximation.Full.GL03B.cell_face_not_mem_sideFaces
#audit_axioms GroupApproximation.Full.GL03B.innerPocketEnclosedTwoArc_of_followsBoundary
#audit_axioms GroupApproximation.Full.GL03B.innerPocketEnclosedTwoArcLocal_of_pinched
