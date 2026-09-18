import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMultipleEdgeCopyBelow
import GroupApproximation.Meta.AxiomGuard

/-!
# The refuted form of the cell pocket walk binder, below the inductive bound

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), lane `gl-p06-01`.

`CellPocketWalkProperArcsBelowInput` (`Estimating/OsinPocketMultipleEdgeCopyBelow.lean:55`) asks,
for a noncrossing cell pocket walk `K = s_1 t_1⁻¹ s_2 t_2⁻¹` between two regions `a`, `b` joining the
distinct cells `Π_i`, `Π_j` of the optimal copy of a least-area `Δ`, with the exterior off its side
and clause (b) of Lemma 9.7 below `Δ.rCellCount`, that both arcs are proper.

P07 route 3 (`P07LakeExclusion.proof_of_innerTwoArcLong`, `InnerTwoArc.lean:86`) proves that
conclusion by `exfalso`: the configuration itself is contradictory.  The pocket between `a` and `b`
holds a kept relator cell, and its lake fill is a two-arc exit with fewer relator cells, refuted by
clause (b) below `Δ`.

This module states the binder with conclusion `False`:
* `CellPocketWalkRefutedBelowInput`: the exact binder of `CellPocketWalkProperArcsBelowInput`, with
  conclusion `False`;
* `CellPocketWalkRefutedBelowSectionStatement`: the same, beyond the thresholds of
  `CellPocketWalkProperArcsBelowSectionStatement`;
* `properArcsBelowInput_of_refuted`, `properArcsBelowSection_of_refuted`: the refuted form gives
  the proper-arcs form (`False.elim`).

The reductions of the refuted form to the P07 residuals are in `RefutedCore.lean`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides

section Input

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The cell pocket walk with the exterior off its side does not exist, below the inductive
bound.**  The binder of `CellPocketWalkProperArcsBelowInput`, concluding `False`. -/
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

/-- The refuted binder gives the proper-arcs binder: its hypotheses are contradictory. -/
theorem properArcsBelowInput_of_refuted {D : RelGenSet G Lambda} {lambda c mu : ℝ} {eps : ℕ}
    {W : Set (List (RelLetter G Lambda))}
    (h : CellPocketWalkRefutedBelowInput.{u, w, v} D lambda c mu eps W) :
    CellPocketWalkProperArcsBelowInput.{u, w, v} D lambda c mu eps W := by
  intro Delta cuts hlea hbelow S i j a b ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hw hoff
  exact (h Delta cuts hlea hbelow S ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hw
    hoff).elim

end Input

/-- **The cell pocket walk binder is refuted below the inductive bound, beyond thresholds.**  The
thresholds are those of `CellPocketWalkProperArcsBelowSectionStatement`. -/
def CellPocketWalkRefutedBelowSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              CellPocketWalkRefutedBelowInput.{u, w, v} D lambda c mu eps W

/-- The refuted section statement gives the proper-arcs section statement, at the same
thresholds. -/
theorem properArcsBelowSection_of_refuted
    (h : CellPocketWalkRefutedBelowSectionStatement.{u, w, v}) :
    CellPocketWalkProperArcsBelowSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨eps0, hEps⟩ := h D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hRho⟩ := hEps eps heps
  exact ⟨rho0, hrho0, fun rho hrho W hcondition =>
    properArcsBelowInput_of_refuted (hRho rho hrho W hcondition)⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.CellPocketWalkRefutedBelowInput
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.properArcsBelowInput_of_refuted
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.CellPocketWalkRefutedBelowSectionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.properArcsBelowSection_of_refuted
