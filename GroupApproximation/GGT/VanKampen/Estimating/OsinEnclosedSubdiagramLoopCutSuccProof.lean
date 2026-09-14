import GroupApproximation.GGT.VanKampen.Estimating.OsinEnclosedSubdiagramLoopCutSucc
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketLoopCut
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketGlueCellTransport
import GroupApproximation.GGT.VanKampen.SurgeryGeodesicCollarStripStep
import GroupApproximation.Meta.AxiomGuard

/-!
# The successor-form enclosed loop cut from a pocket region

`EnclosedSubdiagramLoopCutSuccStatement` (`OsinEnclosedSubdiagramLoopCutSucc`) asks for a loop cut
from an enclosed face set whose outside walk turns to its successor and whose inverse walk reads a
side and then an arc of a cell backwards.  `nonempty_osinLoopCut_of_pocketRegion` gives the loop cut
from a pocket region whose two cycles follow their boundaries.  It needs the collar insertion
(`GeodesicCollar.StripStep.geodesicCollarStatement_holds`) and the cell transport
(`pocketCellTransport`), and both are closed.  The walk can still run along a bridge or pass twice
through a vertex, and two pieces take it to such a pocket region.

* `EnclosedBridgeDoublingSideArcSuccStatement`: doubling the bridges keeps a side with the same word
  and an arc of a cell outside.
* `EnclosedLoopPocketUnpinchSuccStatement`: over relator words longer than one letter, a bridge-free
  walk has an O-equivalent copy with a pocket region whose cycles follow their boundaries, reading a
  side with the same word and then an arc of a cell outside.
* `EnclosedLoopPocketRegionSuccStatement`, `enclosedLoopPocketRegionSucc_of_pieces`: the two in turn.
* `EnclosedSubdiagramLoopCutSuccLongStatement`: the successor-form loop cut over relator words longer
  than one letter, from the pocket region (`enclosedSubdiagramLoopCutSuccLong_of_pocketRegion`) or
  from the unrestricted statement (`enclosedSubdiagramLoopCutSuccLong_of_loopCutSucc`).
* `one_lt_length_of_two_le_rho`: Osin's condition at `2 ≤ ρ` gives relator words longer than one
  letter.

The restriction is the hypothesis of the landed pinch (`PocketFaceSet.exists_simple_of_firstTurns`):
a relator face with one dart has no edge to double.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemmas 9.4 and 9.7); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded HullSC WordMetric

/-- **Doubling the bridges, keeping a side and an arc.**  Take a face set of a diagram with letter
labels, enclosed by an outside walk that turns to its successor, with a relator cell inside and a
cell `i` outside, and let the inverse walk read a side `s` and then an arc of `i` backwards.  An
O-equivalent copy with letter labels carries such a face set with a bridge-free walk, reading a side
with the word of `s` and then an arc of a cell outside. -/
def EnclosedBridgeDoublingSideArcSuccStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (X : DiscDiagram.{u, w, v} W),
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart),
      EnclosedFaceSetSucc X faces outerWalk →
      ∀ C ∈ X.relatorCells, C.face ∈ faces →
      ∀ i : Fin X.rCellCount, (cell X i).face ∉ faces →
      ∀ (A : CyclicArc (cellDarts X i)) (s : List X.toCombMap.Dart),
        invDarts X outerWalk = s ++ invDarts X A.darts →
        ∃ (X' : DiscDiagram.{u, w, v} W) (faces' : Finset X'.toCombMap.Face)
          (outerWalk' : List X'.toCombMap.Dart) (C' : RelatorCell X'.toCombMap X'.outerFace W)
          (i' : Fin X'.rCellCount) (A' : CyclicArc (cellDarts X' i'))
          (s' : List X'.toCombMap.Dart),
          Nonempty (OEquivalentDiscDiagram X X') ∧
            (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
            EnclosedFaceSetSucc X' faces' outerWalk' ∧
            (∀ d ∈ outerWalk', X'.toCombMap.alpha d ∉ outerWalk') ∧
            C' ∈ X'.relatorCells ∧ C'.face ∈ faces' ∧ (cell X' i').face ∉ faces' ∧
            invDarts X' outerWalk' = s' ++ invDarts X' A'.darts ∧
            dartWord X' s' = dartWord X s

/-- **Unpinching a bridge-free enclosed walk.**  Over relator words longer than one letter, a
bridge-free such walk has an O-equivalent copy with letter labels and a pocket region whose two
cycles follow their boundaries.  The pocket region holds a relator cell, keeps a cell `i'` outside,
and its inverse complement cycle reads a side with the word of `s` and then an arc of `i'`
backwards. -/
def EnclosedLoopPocketUnpinchSuccStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda), (∀ word ∈ W, 1 < word.length) →
    ∀ X : DiscDiagram.{u, w, v} W, (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart),
      EnclosedFaceSetSucc X faces outerWalk →
      (∀ d ∈ outerWalk, X.toCombMap.alpha d ∉ outerWalk) →
      ∀ C ∈ X.relatorCells, C.face ∈ faces →
      ∀ i : Fin X.rCellCount, (cell X i).face ∉ faces →
      ∀ (A : CyclicArc (cellDarts X i)) (s : List X.toCombMap.Dart),
        invDarts X outerWalk = s ++ invDarts X A.darts →
        ∃ (X' : DiscDiagram.{u, w, v} W) (P : PocketRegion X')
          (C' : RelatorCell X'.toCombMap X'.outerFace W) (i' : Fin X'.rCellCount)
          (A' : CyclicArc (cellDarts X' i')) (s' : List X'.toCombMap.Dart),
          Nonempty (OEquivalentDiscDiagram X X') ∧
            (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
            P.inner.FollowsBoundary ∧ P.outer.FollowsBoundary ∧
            C' ∈ X'.relatorCells ∧ C'.face ∈ P.faces ∧ (cell X' i').face ∉ P.faces ∧
            invDarts X' P.outer.cycle = s' ++ invDarts X' A'.darts ∧
            dartWord X' s' = dartWord X s

/-- **The pocket region of an enclosed walk reading a side and an arc.**  The conclusion of
`EnclosedLoopPocketUnpinchSuccStatement`, for a walk that may run along bridges. -/
def EnclosedLoopPocketRegionSuccStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda), (∀ word ∈ W, 1 < word.length) →
    ∀ X : DiscDiagram.{u, w, v} W, (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart),
      EnclosedFaceSetSucc X faces outerWalk →
      ∀ C ∈ X.relatorCells, C.face ∈ faces →
      ∀ i : Fin X.rCellCount, (cell X i).face ∉ faces →
      ∀ (A : CyclicArc (cellDarts X i)) (s : List X.toCombMap.Dart),
        invDarts X outerWalk = s ++ invDarts X A.darts →
        ∃ (X' : DiscDiagram.{u, w, v} W) (P : PocketRegion X')
          (C' : RelatorCell X'.toCombMap X'.outerFace W) (i' : Fin X'.rCellCount)
          (A' : CyclicArc (cellDarts X' i')) (s' : List X'.toCombMap.Dart),
          Nonempty (OEquivalentDiscDiagram X X') ∧
            (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
            P.inner.FollowsBoundary ∧ P.outer.FollowsBoundary ∧
            C' ∈ X'.relatorCells ∧ C'.face ∈ P.faces ∧ (cell X' i').face ∉ P.faces ∧
            invDarts X' P.outer.cycle = s' ++ invDarts X' A'.darts ∧
            dartWord X' s' = dartWord X s

/-- **The pocket region from the doubling and the unpinch.** -/
theorem enclosedLoopPocketRegionSucc_of_pieces
    (hdouble : EnclosedBridgeDoublingSideArcSuccStatement.{u, w, v})
    (hunpinch : EnclosedLoopPocketUnpinchSuccStatement.{u, w, v}) :
    EnclosedLoopPocketRegionSuccStatement.{u, w, v} := by
  intro G _ Lambda W D hW X hlabel faces outerWalk E C hC hCf i hi A s hdec
  obtain ⟨X₁, faces₁, outerWalk₁, C₁, i₁, A₁, s₁, ⟨e₁⟩, hlabel₁, E₁, hfree₁, hC₁, hCf₁, hi₁,
      hdec₁, hword₁⟩ := hdouble D X hlabel faces outerWalk E C hC hCf i hi A s hdec
  obtain ⟨X₂, P, C₂, i₂, A₂, s₂, ⟨e₂⟩, hlabel₂, hin, hout, hC₂, hCf₂, hi₂, hdec₂, hword₂⟩ :=
    hunpinch D hW X₁ hlabel₁ faces₁ outerWalk₁ E₁ hfree₁ C₁ hC₁ hCf₁ i₁ hi₁ A₁ s₁ hdec₁
  exact ⟨X₂, P, C₂, i₂, A₂, s₂, ⟨e₁.trans e₂⟩, hlabel₂, hin, hout, hC₂, hCf₂, hi₂, hdec₂,
    hword₂.trans hword₁⟩

/-- **The successor-form enclosed loop cut, over relator words longer than one letter.**  The
hypotheses of `EnclosedSubdiagramLoopCutSuccStatement`, with every relator word longer than one
letter, give a loop cut of `Δ`. -/
def EnclosedSubdiagramLoopCutSuccLongStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps rho : ℕ) (mu lambda c : ℝ),
    OsinCCondition D W eps mu lambda c rho → lambda ≤ 1 → 0 ≤ c →
    (∀ word ∈ W, 1 < word.length) →
    ∀ (Delta X : DiscDiagram.{u, w, v} W), Delta.LeastArea → OEquivalentDiscDiagram Delta X →
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
      ∀ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart),
        EnclosedFaceSetSucc X faces outerWalk →
        ∀ C ∈ X.relatorCells, C.face ∈ faces →
        ∀ i : Fin X.rCellCount, (cell X i).face ∉ faces →
        ∀ (A : CyclicArc (cellDarts X i)) (s : List X.toCombMap.Dart),
          invDarts X outerWalk = s ++ invDarts X A.darts →
          wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X s)) ≤ eps →
            Nonempty (OsinLoopCut D lambda c eps Delta)

/-- **The loop cut from the pocket region**, with the closed collar insertion and cell transport. -/
theorem enclosedSubdiagramLoopCutSuccLong_of_pocketRegion
    (h : EnclosedLoopPocketRegionSuccStatement.{u, w, v}) :
    EnclosedSubdiagramLoopCutSuccLongStatement.{u, w, v} := by
  intro G _ Lambda W D eps rho mu lambda c hcondition hlambda hc hW Delta X hlea equiv hlabel faces
    outerWalk E C hC hCf i hi A s hdec hnorm
  obtain ⟨X', P, C', i', A', s', ⟨e⟩, hlabel', hin, hout, hC', hCf', hi', hdec', hword'⟩ :=
    h D hW X hlabel faces outerWalk E C hC hCf i hi A s hdec
  refine nonempty_osinLoopCut_of_pocketRegion
    GeodesicCollar.StripStep.geodesicCollarStatement_holds pocketCellTransport hcondition hlambda hc
    hlea (equiv.trans e) hlabel' P hin hout hC' hCf' hi' A' s' hdec' ?_
  rw [hword']
  exact hnorm

/-- The unrestricted successor-form loop cut gives the restricted one. -/
theorem enclosedSubdiagramLoopCutSuccLong_of_loopCutSucc
    (h : EnclosedSubdiagramLoopCutSuccStatement.{u, w, v}) :
    EnclosedSubdiagramLoopCutSuccLongStatement.{u, w, v} := by
  intro G _ Lambda W D eps rho mu lambda c hcondition hlambda hc _hW Delta X hlea equiv hlabel faces
    outerWalk E
  exact h D eps rho mu lambda c hcondition hlambda hc Delta X hlea equiv hlabel faces outerWalk E

/-- **Osin's condition at `2 ≤ ρ` makes every relator word longer than one letter.** -/
theorem one_lt_length_of_two_le_rho {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {eps rho : ℕ}
    {mu lambda c : ℝ} (hcondition : OsinCCondition D W eps mu lambda c rho) (hrho : 2 ≤ rho) :
    ∀ word ∈ W, 1 < word.length := by
  intro word hword
  have h := hcondition.long word hword
  omega

end GroupApproximation.GGT.VanKampen

open GroupApproximation.GGT.VanKampen

#audit_axioms EnclosedBridgeDoublingSideArcSuccStatement
#audit_axioms EnclosedLoopPocketUnpinchSuccStatement
#audit_axioms EnclosedLoopPocketRegionSuccStatement
#audit_axioms enclosedLoopPocketRegionSucc_of_pieces
#audit_axioms EnclosedSubdiagramLoopCutSuccLongStatement
#audit_axioms enclosedSubdiagramLoopCutSuccLong_of_pocketRegion
#audit_axioms enclosedSubdiagramLoopCutSuccLong_of_loopCutSucc
#audit_axioms one_lt_length_of_two_le_rho
