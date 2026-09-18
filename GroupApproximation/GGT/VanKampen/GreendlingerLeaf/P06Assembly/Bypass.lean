import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMultipleEdgeCopyBelow
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.InnerTwoArcLong
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06 assembly: the interface of the pinch-free bypass (lanes gl-p06-01, gl-p06-02)

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p06-04, first module.

## Why a bypass

Residual 06 of the Below waist, `CellPocketOuterPinchStepSectionDistinctBelowStatement`
(`Common/CellStepBelow`), is used only inside binder 5 below the bound
(`copyRegion_of_offSideWalkSectionPinchBelow`).  There the proper-arcs residual is applied to exactly
the walk binder that P07 route 3 refutes (`P07LakeExclusion.proof_of_innerTwoArcLong` starts with
`exfalso`).  So binder 5 needs no pinch: the configuration is contradictory before any pinch is
needed.

## The interface stated here

The bypass modules `GreendlingerLeaf/P06Bypass/Refuted*` (lane gl-p06-01) and
`GreendlingerLeaf/P06Bypass/BinderFive*` (lane gl-p06-02) are not on disk at authoring time.  So
their interface is stated here, with the same bodies as the lane specification, so that the later
swap is a rename.

* `CellPocketWalkRefutedBelowInput`: the binder of `CellPocketWalkProperArcsBelowInput`
  (`Estimating/OsinPocketMultipleEdgeCopyBelow.lean:55`), concluding `False`.
* `CellPocketWalkRefutedBelowSectionStatement`: the same, beyond thresholds (as at `:107`).
* `RefutedOfInnerPocketEnclosedStatement`: lane gl-p06-01's theorem
  `refutedBelowSection_of_innerPocketEnclosed`, as an implication.
  * **True.**  Copy the body of `proof_of_innerTwoArcLong` (`InnerTwoArc.lean:86–116`) without the
    `exfalso`, and compose with `innerTwoArcLong_of_innerPocketEnclosed`.  The body ends in
    `Piece06.false_of_lakeFillTwoArcExit`, a strictly smaller count through
    `OsinMultipleEdgeCut.false_of_below`.
* `CopyBelowOfRefutedStatement`: lane gl-p06-02's theorem
  `osinMultipleEdgePocketRegionCopyBelowSection_of_refuted`, as an implication.
  * **True.**  Mirror `multipleEdgePocketRegionCopyBelowInput_of_pinchSectionOrderEuler` (`:208`)
    with the closed `cellPocketCopyCleanBothOrders` and `cellPocketWalkOuterOffSideSomeOrder`.  In
    the off-side walk, build `hw` as at `:182–191` and close with `(hrefuted … hw hoff).elim`.

Each implication is strictly smaller in proof content than the composite
`P06Assembly.proof_of_innerPocketEnclosed_of_bypass` (module `P06Assembly/Proof`), since each is one
of its two halves.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Assembly

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides

section Input

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The walk binder of the proper arcs below the bound is refuted**: the binder of
`CellPocketWalkProperArcsBelowInput`, concluding `False`.  Lane gl-p06-01 interface. -/
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

/-- **The refuted walk binder beyond thresholds**, with the thresholds of
`CellPocketWalkProperArcsBelowSectionStatement`.  Lane gl-p06-01 interface. -/
def CellPocketWalkRefutedBelowSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              CellPocketWalkRefutedBelowInput.{u, w, v} D lambda c mu eps W

/-- **Lane gl-p06-01's reduction, as a Statement**: the enclosed inner pocket refutes the walk
binder below the bound.
* **Why it is true.**  It is the Route 3 script of `P07LakeExclusion.proof_of_innerTwoArcLong`
  without `exfalso`, fed by `innerTwoArcLong_of_innerPocketEnclosed`.
* **Why it is strictly smaller.**  It is one of the two halves of
  `proof_of_innerPocketEnclosed_of_bypass`. -/
def RefutedOfInnerPocketEnclosedStatement : Prop :=
  P07LakeExclusion.InnerPocketEnclosedTwoArcStatement.{u, w, v} →
    CellPocketWalkRefutedBelowSectionStatement.{u, w, v}

/-- **Lane gl-p06-02's reduction, as a Statement**: binder 5 below the bound from the refuted walk
binder, with no Euler residual and no pinch.
* **Why it is true.**  Choose the order with the exterior off the side
  (`cellPocketWalkOuterOffSideSomeOrder`), build the noncrossing walk, and refute it.
* **Why it is strictly smaller.**  It is one of the two halves of
  `proof_of_innerPocketEnclosed_of_bypass`. -/
def CopyBelowOfRefutedStatement : Prop :=
  CellPocketWalkRefutedBelowSectionStatement.{u, w, v} →
    OsinMultipleEdgePocketRegionCopyBelowSectionStatement.{u, w, v}

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Assembly

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Assembly.CellPocketWalkRefutedBelowInput
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Assembly.CellPocketWalkRefutedBelowSectionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Assembly.RefutedOfInnerPocketEnclosedStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Assembly.CopyBelowOfRefutedStatement
