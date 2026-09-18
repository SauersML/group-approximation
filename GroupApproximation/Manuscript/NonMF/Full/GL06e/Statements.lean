import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSections
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionInduction
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellCopyWalk
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkSides
import GroupApproximation.GGT.VanKampen.RelativeGreendlinger
import GroupApproximation.Algebra.HyperbolicGroup
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06e: the refuted cell pocket walk binder, statements

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's Lemma 9.7).

* `CellPocketWalkRefutedBelowInput`: a noncrossing cell pocket walk `K` between two distinct
  selected regions `a`, `b` joining two distinct cells of the optimal copy of a least-area `Δ`,
  with the exterior off its side and clause (b) of Lemma 9.7 below `Δ.rCellCount`, does not exist.
* `CellPocketWalkRefutedBelowSectionStatement`: the same, beyond thresholds.

Both are restated word for word from the foreign
`GGT/VanKampen/GreendlingerLeaf/P06Bypass/RefutedDef.lean`, whose latest commit is a WIP snapshot,
so that file is not imported.  The restatements are definitionally equal to
`P06Bypass.CellPocketWalkRefutedBelowInput` and `P06Bypass.CellPocketWalkRefutedBelowSectionStatement`,
with the same universe order.  The theorem proving the section statement from
`GL03B.InnerPocketEnclosedTwoArcLocal` is `GL06e.refutedBelowSection_of_innerPocketEnclosed`
(module `Full/GL06e/Refuted`).

Neither is a literature statement: they are the combinatorial clauses of the induction step of
Lemma 9.7(b), proved in this directory.
-/

namespace GroupApproximation.Full.GL06e

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides

section Input

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The cell pocket walk with the exterior off its side does not exist, below the inductive
bound** (local restatement of `P06Bypass.CellPocketWalkRefutedBelowInput`; Osin, proof of
Lemma 9.7(b); `thm:hull`). -/
def CellPocketWalkRefutedBelowInput (D : RelGenSet G Lambda) (lambda c mu : ℝ) (eps : ℕ)
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
              False

end Input

/-- **The cell pocket walk binder is refuted below the inductive bound, beyond thresholds**
(local restatement of `P06Bypass.CellPocketWalkRefutedBelowSectionStatement`; Osin, proof of
Lemma 9.7(b); `thm:hull`). -/
def CellPocketWalkRefutedBelowSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              CellPocketWalkRefutedBelowInput.{u, w, v} D lambda c mu eps W

end GroupApproximation.Full.GL06e
