import GroupApproximation.Manuscript.NonMF.Full.GL06e.Statements
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedSucc
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06: the all-cells disjunct of the corrected enclosed inner pocket, statements

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's Lemma 9.7).

GL03BPinch showed on paper that `Full.GL03B.InnerPocketEnclosedTwoArcLocal` is false.  The
enclosed face set may absorb every relator cell.  The corrected statement
`Full.GL03BPinch.InnerPocketEnclosedTwoArcCorrected` adds one disjunct: an `EnclosedFaceSetSucc`
holding every relator cell, with outer walk of length at most `2ε`.  Its consumer, the refuted walk
binder `Full.GL06e.CellPocketWalkRefutedBelowSectionStatement`, must exclude that disjunct in its
own context.

* `EnclosedAllRelatorCellsRefutedInput`: the context of `Full.GL06e.CellPocketWalkRefutedBelowInput`
  (least-area `Δ`, clause (b) below `Δ.rCellCount`, the section family, the two regions and the
  pocket walk).  In that context no enclosed face set of the optimal copy holds every relator cell
  with outer walk of length at most `2ε`.
* `EnclosedAllRelatorCellsRefutedSectionStatement`: the same beyond thresholds.

Neither is a literature statement.  Both are combinatorial clauses of the induction step of
Lemma 9.7(b).  Warning for the prover: the enclosed subdiagram then has the same relator count as
the diagram, so `OsinLemma97Below` does not apply to it directly.

## Manuscript status

Infrastructure for `thm:hull`; certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.GL06

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides

section Input

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **No enclosed face set holds every relator cell with a short outer walk, in the refuted walk
context** (Osin, proof of Lemma 9.7(b); `thm:hull`).  The hypotheses are those of
`Full.GL06e.CellPocketWalkRefutedBelowInput`.  The conclusion excludes the extra disjunct of
`Full.GL03BPinch.InnerPocketEnclosedTwoArcCorrected` at `X = S.diagram`. -/
def EnclosedAllRelatorCellsRefutedInput (D : RelGenSet G Lambda) (lambda c mu : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) : Prop :=
  ∀ (Delta : DiscDiagram.{u, w, v} W) (cuts : SectionCuts D lambda c Delta.boundaryWord),
    Delta.LeastArea → OsinLemma97Below.{u, w, v} D lambda c mu eps W Delta.rCellCount →
      ∀ (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
        {i j : Fin S.diagram.rCellCount} {a b : RegionCandidate D eps S.diagram},
        a ∈ S.family → b ∈ S.family → a ≠ b → i ≠ j → a.JoinsCells i j → b.JoinsCells i j →
          CellPocketWalk.CopyClean a b i j →
          ∀ K : CellPocketWalk D eps S.diagram i j,
            K.firstSide = b.sideFrom j → K.secondSide = a.sideFrom i →
            (∃ G₁ : CyclicArc (cellDarts S.diagram i),
              K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i) →
            (∃ G₂ : CyclicArc (cellDarts S.diagram j),
              K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j) →
            IsNoncrossingClosedWalk S.diagram.toCombMap K.walk →
            S.diagram.outerFace ∉ sideFaces S.diagram.toCombMap K.walk →
            ∀ (faces : Finset S.diagram.toCombMap.Face)
              (outerWalk : List S.diagram.toCombMap.Dart),
              EnclosedFaceSetSucc S.diagram faces outerWalk →
              (∀ C' ∈ S.diagram.relatorCells, C'.face ∈ faces) →
              outerWalk.length ≤ eps + eps →
                False

end Input

/-- **The all-cells disjunct is refuted, beyond thresholds** (Osin, proof of Lemma 9.7(b);
`thm:hull`).  The threshold shape of `Full.GL06e.CellPocketWalkRefutedBelowSectionStatement`. -/
def EnclosedAllRelatorCellsRefutedSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, GroupApproximation.Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              EnclosedAllRelatorCellsRefutedInput.{u, w, v} D lambda c mu eps W

end GroupApproximation.Full.GL06

#audit_axioms GroupApproximation.Full.GL06.EnclosedAllRelatorCellsRefutedInput
#audit_axioms GroupApproximation.Full.GL06.EnclosedAllRelatorCellsRefutedSectionStatement
