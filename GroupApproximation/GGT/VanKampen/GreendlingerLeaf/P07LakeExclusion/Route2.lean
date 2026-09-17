import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.Proof
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf, sub-leaf P07, route 2: the lake exclusion without the all-cells branch

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  `Proof.lean` reduces the target
`CellPocketWalkProperArcsBelowSectionStatement` to `LakeFillSuccStatement` and
`AllCellsShortLoopStatement`.  The second is stated at the fixed thresholds `ε₀ = 0`,
`ρ₀ = max 2 ρ₁` and for an arbitrary enclosed face set of any O-equivalent copy, with no region data in scope; it is
circular (it is Greendlinger's lemma at the same cell count) and may fail at small `ε`.  This module
never meets the all-cells branch.

## The proof route

`LakeFillOutsideStatement` is step 1 of the lake exclusion (the lake filling of `Proof.lean`) with
every hypothesis of the target in scope (hyperbolicity, `ε ≥ ε₀`, `ρ ≥ ρ₀`, the C-condition, the
least-area `Δ`, clause (b) below `Δ`, the globally distinguished section family `S`, the two section
candidates `a ≠ b` joining `Π_i ≠ Π_j`, the clean copy, the side and arc shapes of `K`, the
noncrossing walk with the exterior off its side) together with a full arc, and it concludes only the
first branch: an `EnclosedFaceSetSucc` holding a relator cell, with a cell `Π_k` outside and inverse
outside walk `s_1' s_2' A⁻¹`, `|s_1'|, |s_2'| ≤ ε`.

`proof_of_gaps'` takes `ε₀` from the statement, `ρ₀' = max (max 2 ρ₁) ρ₀` with `ρ₁` from
`SameCellSimplePocket.exists_rho_large`, and refutes a full arc by `false_of_enclosedSucc` (the cut
of step 2, closed in `Proof.lean`).

## Why the remaining statement is true

`lakeFillOutside_of_target` proves `LakeFillOutsideStatement` from the target statement, with the
same thresholds: under the target the full-arc hypothesis never holds.  So the gap is true exactly when
the target is, and the target is a consequence of Osin's Lemma 9.7(b) at those thresholds (the arcs
of a cell pocket walk of an optimal copy are proper).  Non-vacuously it is the lake filling of
`Proof.lean` step 1 in the case where `Π_j` lies in the exterior component (`k = j`, `A = t_2`).

At `n = 1` relator cell the statement is vacuous, not false: it quantifies over `i ≠ j` in
`Fin S.diagram.rCellCount`, so the copy has at least two relator cells.

## Why `LakeFillSuccStatement` alone does not give it

The region hypotheses do not exclude the all-cells branch combinatorially: in a lens configuration
(`Π_i`, `Π_j` full, the side two short chords, every relator cell a lake) all data of the target is
realizable in the combinatorial map, and ruling it out needs Greendlinger's lemma at the same cell
count.  Filling every lake except the component of `Π_j` does not help either: an outer walk turning
to its successors is the boundary orbit of one complement component, so when `Π_j` lies in a lake
distinct from the exterior no such face set exists.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides

section Input

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **Lake filling with a cell outside, with the region data in scope.**  As the hypotheses of
`CellPocketWalkProperArcsBelowInput`, together with a full arc, give an enclosed face set turning to
its successors, holding a relator cell, with a relator cell `Π_k` outside, whose inverse outside
walk reads two sides of length at most `ε` and then an arc of `Π_k`. -/
def LakeFillOutsideInput (D : RelGenSet G Lambda) (lambda c mu : ℝ) (eps : ℕ)
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
            (K.firstArc.length = (cellDarts S.diagram i).length ∨
              K.secondArc.length = (cellDarts S.diagram j).length) →
            ∃ (faces : Finset S.diagram.toCombMap.Face) (outerWalk : List S.diagram.toCombMap.Dart)
              (s₁ s₂ : List S.diagram.toCombMap.Dart) (k : Fin S.diagram.rCellCount)
              (A : CyclicArc (cellDarts S.diagram k)),
              EnclosedFaceSetSucc S.diagram faces outerWalk ∧
                (∃ C ∈ S.diagram.relatorCells, C.face ∈ faces) ∧
                s₁.length ≤ eps ∧ s₂.length ≤ eps ∧
                (cell S.diagram k).face ∉ faces ∧
                invDarts S.diagram outerWalk = s₁ ++ s₂ ++ invDarts S.diagram A.darts

end Input

/-- **Lake filling with a cell outside, beyond thresholds.**  The first branch of the lake filling
(`LakeFillSuccStatement`), with all hypotheses of `CellPocketWalkProperArcsBelowSectionStatement` in
scope and its threshold shape.  True: the target statement implies it with the same thresholds
(`lakeFillOutside_of_target`), since there the full-arc hypothesis is never met; vacuous at one
relator cell since `i ≠ j`. -/
def LakeFillOutsideStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              LakeFillOutsideInput.{u, w, v} D lambda c mu eps W

/-- **The lake exclusion from the lake filling with a cell outside.**  Thresholds `ε₀` from the
statement and `ρ₀' = max (max 2 ρ₁) ρ₀`; a full arc is refuted by `false_of_enclosedSucc`. -/
theorem proof_of_gaps' (hfill : LakeFillOutsideStatement.{u, w, v}) :
    CellPocketWalkProperArcsBelowSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu1
  obtain ⟨eps0, heps0⟩ := hfill D hhyp lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0⟩ := heps0 eps heps
  obtain ⟨rho1, hrho1⟩ := SameCellSimplePocket.exists_rho_large lambda c hmu eps
  refine ⟨max (max 2 rho1) rho0, by omega, fun rho hrho W hcondition => ?_⟩
  have hmax : max 2 rho1 ≤ rho := le_of_max_le_left hrho
  have hlarge := hrho1 rho (le_of_max_le_right hmax)
  have hrho2 : 2 ≤ rho := le_of_max_le_left hmax
  have hinput : LakeFillOutsideInput.{u, w, v} D lambda c mu eps W :=
    hrho0 rho (le_of_max_le_right hrho) W hcondition
  intro Delta cuts hlea hbelow S i j _ _ ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hw hoff
  have hfalse : K.firstArc.length = (cellDarts S.diagram i).length ∨
      K.secondArc.length = (cellDarts S.diagram j).length → False := by
    intro hfull
    obtain ⟨faces, outerWalk, s₁, s₂, k, A, E, ⟨C, hC, hCf⟩, hs₁, hs₂, hk, hdec⟩ :=
      hinput Delta cuts hlea hbelow S ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hw hoff
        hfull
    exact false_of_enclosedSucc hcondition hlambda hlambda1 hc hmu hmu1 hrho2 hlarge hlea hbelow
      S.equiv S.label_admissible E hC hCf hk A hdec hs₁ hs₂
  exact ⟨lt_of_le_of_ne K.firstArc.length_le fun h => hfalse (Or.inl h),
    lt_of_le_of_ne K.secondArc.length_le fun h => hfalse (Or.inr h)⟩

/-- **The remaining statement is implied by the target.**  The target makes both arcs proper, so the
full-arc hypothesis of `LakeFillOutsideInput` is never met; the thresholds are the target's. -/
theorem lakeFillOutside_of_target
    (htarget : CellPocketWalkProperArcsBelowSectionStatement.{u, w, v}) :
    LakeFillOutsideStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu1
  obtain ⟨eps0, heps0⟩ := htarget D hhyp lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, _, hrho0⟩ := heps0 eps heps
  refine ⟨rho0, fun rho hrho W hcondition => ?_⟩
  intro Delta cuts hlea hbelow S _ _ _ _ ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hw hoff
    hfull
  obtain ⟨hlt₁, hlt₂⟩ := hrho0 rho hrho W hcondition Delta cuts hlea hbelow S ha hb hab hij hai hbi
    hclean K hfirst hsecond h₁ h₂ hw hoff
  rcases hfull with h | h
  · exact (Nat.ne_of_lt hlt₁ h).elim
  · exact (Nat.ne_of_lt hlt₂ h).elim

/-- **Route 2 is equivalent to the target.**  `proof_of_gaps'` and `lakeFillOutside_of_target`. -/
theorem lakeFillOutside_iff_target :
    LakeFillOutsideStatement.{u, w, v} ↔
      CellPocketWalkProperArcsBelowSectionStatement.{u, w, v} :=
  ⟨proof_of_gaps', lakeFillOutside_of_target⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFillOutsideInput
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFillOutsideStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.proof_of_gaps'
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.lakeFillOutside_of_target
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.lakeFillOutside_iff_target
