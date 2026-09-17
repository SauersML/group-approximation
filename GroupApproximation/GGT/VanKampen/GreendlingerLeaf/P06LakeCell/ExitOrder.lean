import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.ExitStatement
import GroupApproximation.GGT.VanKampen.FaceSetBoundaryWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06, case (d): the one-arc exit from the order of the walk

Lane `gl-p06-11` of `lanes/carto-gl-p06.md`.  Osin, arXiv:math/0411039v3, §9, proof of
Lemma 9.7(b).  Certifies no printed sentence on its own.

## What this module proves

* `sideDarts_length_le`: suppose the inverse outside walk of an `EnclosedFaceSetSucc` reads `P ++ B`
  and every `α e` with `e ∈ P` lies in `K.firstSide ++ K.secondSide`.  Then `|P| ≤ 2ε`.  `P` is
  duplicate free, and `α` maps it injectively into the sides.  The pieces of the two sides may
  interleave on `P` (crossed pinches); only the count is used.
* `lakeFillOneArcExit_of_sideDarts`: with `B = Ā` an arc read backwards, split `P` at `ε`, giving
  `Piece06.LakeFillOneArcExit`.
* `caseDLakeRelatorExit_of_order`: `CaseDLakeRelatorExitStatement` from
  `CaseDLakeRelatorOrderStatement`.

## The remaining statement

`CaseDLakeRelatorOrderStatement` (OPEN) keeps every hypothesis of
`CaseDLakeRelatorExitStatement`.  Its one-arc disjunct asks for an enclosed face set turning to its
successors that holds a relator cell, with a cell `Π_k` off it, whose inverse outside walk reads
`P ++ Ā`, with `A` an arc of `Π_k` and every `α e` (`e ∈ P`) on the sides of `K`.  Its other
disjunct is unchanged.

**Why it is smaller.**  It is the order claim that the lane allows to ship as a Statement.  The
reduction proves all of the counting (duplicate freeness, injectivity of `α`, the split at `ε`).
What stays open is only the geometric fact that the walk of the filled piece is one successor
walk, with the contact with `Π_i` a single arc at its end.  It asks for no length or norm bound.

**Why it is true (paper, `ExitStatement` truth check 1–2).**  Let `H` be the piece of the second
relator cell in the complement of `K.faces ∪ {Π_i}`, with its lakes filled.  `H` holds that cell
and misses `Π_i`.  If `Π_j ∉ H`, every dart `e` of its inverse outside walk has `α e` either on
`s₁ ++ s₂` or on `Π_i`.  If `Π_j ∈ H`, the second disjunct is the target's own two-arc disjunct,
unchanged, with the truth risk of `ExitStatement` check 2.  The contact with `Π_i` is one arc:
`Π_i` and the filled `K`-side are discs meeting along `t₁`, and a region bounded alternately by two such discs meets each in a single arc.  This is
paper-level only; the walk order of absorbed boundary cycles is not in the corpus
(`Estimating/OsinPocketLakeAbsorption`).  The disjunction with the two-arc exit only weakens it.

## Manuscript status

Infrastructure for `thm:hull`; certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated

section Count

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **Side darts of a walk are at most `2ε`**: a prefix `P` of the inverse outside walk of an
enclosed face set, whose reverses lie on the sides of `K`, has length at most `ε + ε`. -/
theorem sideDarts_length_le (K : CellPocketFaceSet D eps X i j)
    {faces : Finset X.toCombMap.Face} {outerWalk P B : List X.toCombMap.Dart}
    (E : EnclosedFaceSetSucc X faces outerWalk) (hdec : invDarts X outerWalk = P ++ B)
    (hsides : ∀ e ∈ P, X.toCombMap.alpha e ∈ K.firstSide ++ K.secondSide) :
    P.length ≤ eps + eps := by
  have hinv : (invDarts X outerWalk).Nodup := Embedded.invDarts_nodup E.nodup
  rw [hdec] at hinv
  have hP : P.Nodup := List.Nodup.of_append_left hinv
  have hmap : (P.map X.toCombMap.alpha).Nodup :=
    List.Nodup.map X.toCombMap.alpha.injective hP
  have hsub : P.map X.toCombMap.alpha ⊆ K.firstSide ++ K.secondSide := by
    intro a ha
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
    exact hsides e he
  have hle := (List.Nodup.subperm hmap hsub).length_le
  rw [List.length_map, List.length_append] at hle
  have h1 := K.firstSide_length_le
  have h2 := K.secondSide_length_le
  omega

/-- **The one-arc exit from side darts**: split the side prefix at `ε`. -/
theorem lakeFillOneArcExit_of_sideDarts (K : CellPocketFaceSet D eps X i j)
    {faces : Finset X.toCombMap.Face} {outerWalk P : List X.toCombMap.Dart}
    {k : Fin X.rCellCount} (A : CyclicArc (cellDarts X k))
    (E : EnclosedFaceSetSucc X faces outerWalk)
    (hC : ∃ C ∈ X.relatorCells, C.face ∈ faces) (hk : (cell X k).face ∉ faces)
    (hdec : invDarts X outerWalk = P ++ invDarts X A.darts)
    (hsides : ∀ e ∈ P, X.toCombMap.alpha e ∈ K.firstSide ++ K.secondSide) :
    Piece06.LakeFillOneArcExit eps X := by
  have hlen := sideDarts_length_le K E hdec hsides
  refine ⟨faces, outerWalk, P.take eps, P.drop eps, k, A, E, hC, hk, ?_,
    List.length_take_le eps P, ?_⟩
  · rw [List.take_append_drop]
    exact hdec
  · rw [List.length_drop]
    omega

end Count

/-- **Case (d), the order of the walk of the filled piece** (OPEN).  Every hypothesis of
`CaseDLakeRelatorExitStatement`.  It concludes an enclosed successor face set holding a relator
cell, with a cell `Π_k` off it, whose inverse outside walk reads side darts of `K` and then an arc
of `Π_k` backwards, or the two-arc exit. -/
def CaseDLakeRelatorOrderStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∀ (eps rho : ℕ) (W : Set (List (RelLetter G Lambda))),
        OsinCCondition D W eps mu lambda c rho →
          ∀ (X : DiscDiagram.{u, w, v} W) (i j : Fin X.rCellCount), i ≠ j → X.LeastArea →
            OsinLemma97Below.{u, w, v} D lambda c mu eps W X.rCellCount →
            (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
            ∀ K : CellPocketFaceSet D eps X i j, K.ClosedWalk → ¬ K.FirstTurns →
              K.firstArc.length < (cellDarts X i).length →
              K.secondArc.length < (cellDarts X j).length →
              ¬Unpinched X.toCombMap K.faces → Piece06.AllNonFirstTurnsCrossed K →
              ¬ Piece06.CellCut K → (∀ k : Fin X.rCellCount, ¬ Piece06.SideCell K k) →
              Piece06.ShortPetalFree eps X → ¬ Piece06.CellFilterMove K →
              Assembly.AllCellsEnclosed K →
              (∃ C ∈ X.relatorCells, C.face ∈ lakeOf K i ∧ C.face ≠ (cell X i).face) →
                (∃ (faces : Finset X.toCombMap.Face) (outerWalk P : List X.toCombMap.Dart)
                  (k : Fin X.rCellCount) (A : CyclicArc (cellDarts X k)),
                  EnclosedFaceSetSucc X faces outerWalk ∧
                    (∃ C ∈ X.relatorCells, C.face ∈ faces) ∧ (cell X k).face ∉ faces ∧
                    invDarts X outerWalk = P ++ invDarts X A.darts ∧
                    ∀ e ∈ P, X.toCombMap.alpha e ∈ K.firstSide ++ K.secondSide) ∨
                  Piece06.LakeFillTwoArcExit D eps X

/-- **Case (d) exit from the order of the walk**: the side count and the split at `ε`. -/
theorem caseDLakeRelatorExit_of_order (h : CaseDLakeRelatorOrderStatement.{u, w, v}) :
    CaseDLakeRelatorExitStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16 eps rho W hcondition X i j hij
    hlea hbelow hlabel K hK hnft hfirst hsecond hpinch hrose hcut hsideCell hshort hmove hall hsec
  rcases h D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16 eps rho W hcondition X i j hij hlea
      hbelow hlabel K hK hnft hfirst hsecond hpinch hrose hcut hsideCell hshort hmove hall
      hsec with ⟨faces, outerWalk, P, k, A, E, hC, hk, hdec, hsides⟩ | htwo
  · exact Or.inl (lakeFillOneArcExit_of_sideDarts K A E hC hk hdec hsides)
  · exact Or.inr htwo

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.sideDarts_length_le
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.lakeFillOneArcExit_of_sideDarts
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.CaseDLakeRelatorOrderStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.caseDLakeRelatorExit_of_order
