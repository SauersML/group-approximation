import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedBridgeDoublingSideArc
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf, piece 03: the enclosed loop cut in successor form

`EnclosedSubdiagramLoopCutSuccStatement` (`Estimating/OsinEnclosedSubdiagramLoopCutSucc`) is the
`hloop` residual of `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV8Closures`
(`Estimating/OsinGreendlingerWaistV8Closures`). That producer concludes the least-area leaf
`RelativeGreendlingerQuasiGeodesicLeastAreaStatement` of Hull's Theorem 7.1 (Osin, math/0411039v3,
Lemma 9.7(b): "the subdiagram `Ξ` will be bounded by `st`, where `l(s) < ε` and `t` is a subpath of
`∂Π_1`").

## What is closed

The closed theorem `enclosedSubdiagramLoopCutSuccLong` (`ClosedWalkEnclosedBridgeDoublingSideArc`)
proves the statement when every relator word has more than one letter. Its route:

1. bridge doubling on an O-equivalent copy, keeping the side and the arc;
2. unpinching the pocket face set to a pocket region whose cycles follow their boundaries;
3. `nonempty_osinLoopCut_of_pocketRegion`, with the closed geodesic collar and the pocket cell
   transport.

This module adds three results:

* `proof_of_two_le_rho`: the residual under `C(ε, μ, λ, c, ρ)` with `2 ≤ ρ`, with no other
  hypotheses. `ρ ≤ |R|` for every relator word, so every word is longer than one letter.
* `proof_of_short`: the full residual follows from its short-relator case, where some relator word
  has at most one letter. The long case is `enclosedSubdiagramLoopCutSuccLong`.
* `proof_long`: the long case, under the lane's name.

## The open case

The short-relator case is still open. The hypothesis `∀ word ∈ W, 1 < word.length` has exactly one
use: `PocketFaceSet.one_lt_length_of_badCorner` (`Estimating/OsinPocketGoodCornersSection`) calls
`CornerCount.one_lt_length_of_relatorCell`. That is needed to double an edge of a relator face
inside the pocket at a bad corner, via `FaceEdgeDoubling.diagram`, which requires
`1 < (X.faceBoundary f).darts.length`.

A one-letter relator cell is a monogon face, and doubling an edge inside it is not built. One
possible fix:

* double the edge on the outside face `faceOf (α d)` instead;
* move the new G-digon into the pocket face set;
* show that the pocket transports, keeping its sides, its arc and `ReadsSide`.

The outside face has more than one dart, because `X` has at least two relator cells.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, through Osin's Lemmas 9.4 and 9.7); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece03

universe u w v

open Embedded HullSC WordMetric

/-- **The successor-form enclosed loop cut at `2 ≤ ρ`**: the hypotheses of
`EnclosedSubdiagramLoopCutSuccStatement`, with `2 ≤ ρ` added after `0 ≤ c`. -/
def EnclosedSubdiagramLoopCutSuccTwoLeRhoStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps rho : ℕ) (mu lambda c : ℝ),
    OsinCCondition D W eps mu lambda c rho → lambda ≤ 1 → 0 ≤ c → 2 ≤ rho →
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

/-- **The short-relator case of the successor-form enclosed loop cut**: the hypotheses of
`EnclosedSubdiagramLoopCutSuccStatement`, with a relator word of at most one letter. -/
def EnclosedSubdiagramLoopCutSuccShortStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps rho : ℕ) (mu lambda c : ℝ),
    OsinCCondition D W eps mu lambda c rho → lambda ≤ 1 → 0 ≤ c →
    (∃ word ∈ W, word.length ≤ 1) →
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

/-- **Piece 03, long relators**: `EnclosedSubdiagramLoopCutSuccLongStatement` holds, with no
hypotheses. -/
theorem proof_long : EnclosedSubdiagramLoopCutSuccLongStatement.{u, w, v} :=
  enclosedSubdiagramLoopCutSuccLong.{u, w, v}

/-- **Piece 03 at `2 ≤ ρ`**: under `C(ε, μ, λ, c, ρ)` with `2 ≤ ρ`, `λ ≤ 1` and `0 ≤ c`, the
successor-form enclosed face set gives a loop cut of `Δ`, with no other hypotheses. -/
theorem proof_of_two_le_rho : EnclosedSubdiagramLoopCutSuccTwoLeRhoStatement.{u, w, v} := by
  intro G _ Lambda W D eps rho mu lambda c hcondition hlambda hc hrho Delta X hlea equiv hlabel
    faces outerWalk E C hC hCf i hi A s hdec hnorm
  exact enclosedSubdiagramLoopCutSuccLong.{u, w, v} D eps rho mu lambda c hcondition hlambda hc
    (one_lt_length_of_two_le_rho hcondition hrho) Delta X hlea equiv hlabel faces outerWalk E C hC
    hCf i hi A s hdec hnorm

/-- **The reduction of piece 03 to its short-relator case.** If some relator word has at most one
letter, the short-relator statement applies; otherwise every word has more than one letter and
`enclosedSubdiagramLoopCutSuccLong` applies. -/
theorem proof_of_short (h : EnclosedSubdiagramLoopCutSuccShortStatement.{u, w, v}) :
    EnclosedSubdiagramLoopCutSuccStatement.{u, w, v} := by
  intro G _ Lambda W D eps rho mu lambda c hcondition hlambda hc Delta X hlea equiv hlabel
    faces outerWalk E C hC hCf i hi A s hdec hnorm
  by_cases hW : ∀ word ∈ W, 1 < word.length
  · exact enclosedSubdiagramLoopCutSuccLong.{u, w, v} D eps rho mu lambda c hcondition hlambda hc
      hW Delta X hlea equiv hlabel faces outerWalk E C hC hCf i hi A s hdec hnorm
  · have hshort : ∃ word ∈ W, word.length ≤ 1 := by
      push Not at hW
      exact hW
    exact h D eps rho mu lambda c hcondition hlambda hc hshort Delta X hlea equiv hlabel faces
      outerWalk E C hC hCf i hi A s hdec hnorm

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece03

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece03.EnclosedSubdiagramLoopCutSuccTwoLeRhoStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece03.EnclosedSubdiagramLoopCutSuccShortStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece03.proof_long
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece03.proof_of_two_le_rho
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece03.proof_of_short
