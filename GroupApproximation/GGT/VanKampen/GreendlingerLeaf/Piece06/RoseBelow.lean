import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.RoseUncutOsin
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.Proof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Common.CellStepBelow
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06 below the inductive bound: short petals excluded, lakes isolated

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  `Piece06/RoseOffSideShort` explains why
a kept petal (a region of the pocket bounded by the sides only, holding a relator cell) is not
excluded by the binders of `CellRoseUncutOffSideStatement`: excluding it is Lemma 9.7(b) for a
smaller diagram, i.e. the inductive premise `OsinLemma97Below … X.rCellCount`.  The below form of
residual 06, `CellPocketOuterPinchStepSectionDistinctBelowStatement`
(`GreendlingerLeaf/Common/CellStepBelow`), carries that premise, and
`relativeGreendlingerQuasiGeodesicLeastArea_of_eightResidualsBelow` consumes it.

## What this module proves

* `ShortPetalFree eps X`: no enclosed face set of `X` turning to its successors, with some cell off
  it and inverse outside walk `s_1 s_2` read by two sides of length at most `ε`, holds a relator
  cell.
* `shortPetalFree_of_below`: at the thresholds of `P07LakeExclusion.proof_of_gaps` (`2 ≤ ρ` and
  `λ⁻¹ (3ε + c) < (μ/2) ρ`), with clause (b) below `X`, every diagram is short-petal free.  This is
  `P07LakeExclusion.false_of_enclosedSucc` at the identity O-equivalence, with the empty arc of the
  outside cell (the collar and cell transport are closed, and the multiple-edge cut it produces has
  fewer relator cells, which clause (b) below `X` refutes).
* `proof_of_below_gaps`: the below residual 06 from `CellRoseUncutLakesBelowStatement` and
  `BadCornerRefinementStatement`, by the dispatch of `proof_of_cellRoseUncutOsin`.  The `ρ₀` of the
  residual is raised to `max (max ρ₀ 2) (max ρ₁ (2ε + 1))`, which excludes side cells
  (`not_sideCell_of_osinCCondition`) and short petals (`shortPetalFree_of_below`).
* `cellRoseUncutLakesBelow_of_step`: the residual follows from the below residual 06 by forgetting
  hypotheses, so it is no stronger than `CellPocketOuterPinchStepSectionDistinctStatement` (through
  `CellPocketOuterPinchStepSectionDistinctStatement.toBelow`).

## The remaining gap

`CellRoseUncutLakesBelowStatement` (OPEN): the uncut rose step with the premise of clause (b), no
side cell and no short petal.  What it still has to handle is the planar combinatorics of the rose:
producing, from an uncut rose with a petal away from both arcs, either a closed cut or an enclosed
face set of the form excluded by `ShortPetalFree`, and the lakes (bounded components of the
complement of the pocket that the walk encloses), for which the corpus has no filling surgery on
cell pockets.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated
open scoped Classical

section Short

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **A diagram without short petals**: an enclosed face set turning to its successors, with some
relator cell off it, whose inverse outside walk is read by two sides of length at most `ε`, holds no
relator cell. -/
def ShortPetalFree (eps : ℕ) (X : DiscDiagram.{u, w, v} W) : Prop :=
  ∀ (faces : Finset X.toCombMap.Face) (outerWalk s₁ s₂ : List X.toCombMap.Dart)
    (k : Fin X.rCellCount), EnclosedFaceSetSucc X faces outerWalk → (cell X k).face ∉ faces →
    invDarts X outerWalk = s₁ ++ s₂ → s₁.length ≤ eps → s₂.length ≤ eps →
      ∀ C ∈ X.relatorCells, C.face ∉ faces

/-- **Short petals are excluded below the inductive bound.**  At the thresholds of the lake
exclusion, with clause (b) of Lemma 9.7 below the number of relator cells of a least-area `X` with
letter labels, `X` has no short petal: `P07LakeExclusion.false_of_enclosedSucc` with the identity
O-equivalence and the empty arc of the outside cell. -/
theorem shortPetalFree_of_below {D : RelGenSet G Lambda} {eps rho : ℕ} {mu lambda c : ℝ}
    (hcondition : OsinCCondition D W eps mu lambda c rho) (hlambda : 0 < lambda)
    (hlambda1 : lambda ≤ 1) (hc : 0 ≤ c) (hmu : 0 < mu) (hmu1 : mu ≤ 1 / 16) (hrho : 2 ≤ rho)
    (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ))
    {X : DiscDiagram.{u, w, v} W} (hlea : X.LeastArea)
    (hbelow : OsinLemma97Below.{u, w, v} D lambda c mu eps W X.rCellCount)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) :
    ShortPetalFree eps X := by
  intro faces outerWalk s₁ s₂ k E hk hdec hs₁ hs₂ C hC hCf
  exact P07LakeExclusion.false_of_enclosedSucc hcondition hlambda hlambda1 hc hmu hmu1 hrho hlarge
    hlea hbelow (OEquivalentDiscDiagram.refl X) hlabel E hC hCf hk
    (P07LakeExclusion.emptyArc (cellDarts X k))
    (by rw [P07LakeExclusion.invDarts_emptyArc, List.append_nil]; exact hdec) hs₁ hs₂

end Short

/-- **The uncut rose step below the inductive bound, off side cells and short petals** (OPEN; the
residual of gap 6 below the bound).  `CellRoseUncutOffSideStatement` with the premise of clause (b)
of Lemma 9.7 below the number of relator cells of `X`, and with `ShortPetalFree eps X`.  It follows
from `CellPocketOuterPinchStepSectionDistinctBelowStatement` (`cellRoseUncutLakesBelow_of_step`). -/
def CellRoseUncutLakesBelowStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              ∀ (X : DiscDiagram.{u, w, v} W) (i j : Fin X.rCellCount), i ≠ j → X.LeastArea →
                OsinLemma97Below.{u, w, v} D lambda c mu eps W X.rCellCount →
                (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
                ∀ K : CellPocketFaceSet D eps X i j, K.ClosedWalk → ¬ K.FirstTurns →
                  K.firstArc.length < (cellDarts X i).length →
                  K.secondArc.length < (cellDarts X j).length →
                  ¬Unpinched X.toCombMap K.faces → AllNonFirstTurnsCrossed K → ¬ CellCut K →
                  (∀ k : Fin X.rCellCount, ¬ SideCell K k) → ShortPetalFree eps X →
                    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
                      (K' : CellPocketFaceSet D eps X' i' j'),
                      Nonempty (OEquivalentDiscDiagram X X') ∧
                        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ i' ≠ j' ∧
                        K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
                        K'.secondArc.length < (cellDarts X' j').length ∧
                        K'.repeatedVisits < K.repeatedVisits

/-- **The residual from the below outer-pinch step**: forget the rose hypotheses.  So the residual is
no stronger than residual 06. -/
theorem cellRoseUncutLakesBelow_of_step
    (h : CellPocketOuterPinchStepSectionDistinctBelowStatement.{u, w, v}) :
    CellRoseUncutLakesBelowStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  exact ⟨rho0, hrho0, fun rho hrho' W hcond X i j hij hlea hbelow hlabel K hK hnft hfirst hsecond
    hpinch _ _ _ _ => hrho rho hrho' W hcond X i j hij hlea hbelow hlabel K hK hnft hfirst hsecond
      hpinch⟩

/-- **Piece 06 below the inductive bound from the lakes residual and the corner doubling.**  A closed
cut performs the rose step in the same diagram; an uncut rose uses `CellRoseUncutLakesBelowStatement`,
with no side cell once `2ε < ρ` and no short petal by clause (b) below `X`; an uncrossed turn uses the
good corners or `BadCornerRefinementStatement` (OPEN, gap 5). -/
theorem proof_of_below_gaps (h : CellRoseUncutLakesBelowStatement.{u, w, v})
    (hcorner : BadCornerRefinementStatement.{u, w, v}) :
    CellPocketOuterPinchStepSectionDistinctBelowStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  obtain ⟨rho1, hrho1⟩ := SameCellSimplePocket.exists_rho_large lambda c hmu eps
  refine ⟨max (max rho0 2) (max rho1 (eps + eps + 1)),
    lt_of_lt_of_le hrho0
      ((le_max_left rho0 2).trans (le_max_left (max rho0 2) (max rho1 (eps + eps + 1)))),
    fun rho hrho' W hcondition X i j hij hlea hbelow hlabel K hK hnft hfirst hsecond hpinch => ?_⟩
  have hleft : max rho0 2 ≤ rho :=
    (le_max_left (max rho0 2) (max rho1 (eps + eps + 1))).trans hrho'
  have hright : max rho1 (eps + eps + 1) ≤ rho :=
    (le_max_right (max rho0 2) (max rho1 (eps + eps + 1))).trans hrho'
  have h0 : rho0 ≤ rho := (le_max_left rho0 2).trans hleft
  have h2 : 2 ≤ rho := (le_max_right rho0 2).trans hleft
  have h1 : rho1 ≤ rho := (le_max_left rho1 (eps + eps + 1)).trans hright
  have hlt : eps + eps < rho := by
    have hmax : eps + eps + 1 ≤ rho := (le_max_right rho1 (eps + eps + 1)).trans hright
    omega
  have hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ) := hrho1 rho h1
  by_cases hrose : AllNonFirstTurnsCrossed K
  · by_cases hcut : CellCut K
    · exact exists_step_of_cellCut' hlabel K hK hij hfirst hsecond hcut
    · exact hrho rho h0 W hcondition X i j hij hlea hbelow hlabel K hK hnft hfirst hsecond hpinch
        hrose hcut (fun k => not_sideCell_of_osinCCondition hcondition hlt K k)
        (shortPetalFree_of_below hcondition hlambda hlambda1 hc hmu hmu16 h2 hlarge hlea hbelow
          hlabel)
  · obtain ⟨d₀, hd₀, hnf, hnc⟩ := exists_uncrossed_of_not_allCrossed hrose
    by_cases hgood : GoodTurnCorners X d₀ (K.boundary.cycle.next d₀ hd₀)
    · exact exists_step_of_goodCorners hlabel K hK hij hfirst hsecond hd₀ rfl hnf
        (huncross_of_not_turnCrossed hnc) hgood
    · exact exists_step_of_badCorners hcorner hlabel K hK hij hfirst hsecond hd₀ rfl hnf
        (huncross_of_not_turnCrossed hnc) hgood

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.ShortPetalFree
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.shortPetalFree_of_below
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CellRoseUncutLakesBelowStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.cellRoseUncutLakesBelow_of_step
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.proof_of_below_gaps
