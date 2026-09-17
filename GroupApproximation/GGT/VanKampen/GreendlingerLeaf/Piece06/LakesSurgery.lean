import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.LakesBelow
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.Proof
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMultipleEdgeAssembly
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06 below the bound: the lakes residual with its lake-fill exits

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  The target is
`CellRoseLakesUnfilteredBelowStatement` (module `Piece06/LakesBelow`): the uncut cell rose step
below the inductive bound, with no side cell, no short petal and no in-place region-union move.

## The lake filling

Let `c = s_1 t̄_1 s_2 t̄_2` be the boundary cycle of the pocket `K`, with `t_1`, `t_2` arcs of
`Π_i ≠ Π_j` and `|s_1|, |s_2| ≤ ε`.  Let `E₀` be the class of the exterior face in the complement
of `K.faces` across edges off `c`, and `F'` every face off `E₀`.  Every boundary dart of `F'` is a
dart of `c`, so the outside walk of `F'` reads, in cyclic order, sub-walks of `s_1`, `t̄_1`, `s_2`,
`t̄_2`, and `F' ⊇ K.faces` holds the kept relator cell.
* (a) Exactly one of `Π_i`, `Π_j` lies in `F'`, say `Π_i`: the walk reads `s_1' s_2' A⁻¹`, after a
  rotation, with `A` an arc of `Π_j` outside.  This is `LakeFillOneArcExit`.
* (b) Both lie in `F'` and some relator cell `Π_k` does not: the walk reads `s_1' s_2'`, which is
  `LakeFillOneArcExit` with the empty arc of `Π_k`.
* (c) Neither lies in `F'`: after unpinching the outer walk, a pocket region of an O-equivalent
  copy whose inverse complement cycle reads `s_1' A_1⁻¹ s_2' A_2⁻¹`.  This is `LakeFillTwoArcExit`.
* (d) Every relator cell lies in `F'` (short-word case, same count): the diagram must change.

## What this module proves

* `false_of_lakeFillOneArcExit`: at `2 ≤ ρ` and `λ⁻¹ (3ε + c) < (μ/2) ρ`, clause (b) below `X`
  refutes (a) and (b), by `P07LakeExclusion.false_of_enclosedSucc` at the identity O-equivalence.
* `false_of_lakeFillTwoArcExit`: (c) is a multiple-edge cut of `X`
  (`nonempty_osinMultipleEdgeCut_of_pocketRegion`, closed collar and cell transport) with fewer
  relator cells, refuted by `OsinMultipleEdgeCut.false_of_below`.
* `proof_of_lakesSurgery`: the target from `CellRoseLakesSurgeryBelowStatement`, at
  `ρ₀' = max (max ρ₀ 2) ρ₁`; `lakesSurgery_of_target`: the converse, at the same thresholds.

## Why the remaining statement is true

`CellRoseLakesSurgeryBelowStatement` (OPEN) keeps every hypothesis of the target and weakens its
conclusion to "an exit, or the step".  It follows from the target by `Or.inr`
(`lakesSurgery_of_target`), so it is true exactly when the target is, which holds whenever
residual 06 below the bound does (`cellRoseLakesUnfilteredBelow_of_lakes`,
`cellRoseUncutLakesBelow_of_step`).  Small models (three circles of `Piece06/LakesBelow`): `Π_j`
in the exterior is (a); a relator cell in the exterior is (b); every relator cell in
`F ∪ H_i ∪ H_j` is (d), where the step is asked, as in the target.  Vacuous at one relator cell.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated

section Exits

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **A lake fill with one arc outside**: an enclosed face set turning to its successors, holding a
relator cell, with a cell `Π_k` off it, whose inverse outside walk reads two sides of length at
most `ε` and then an arc of `Π_k` backwards. -/
def LakeFillOneArcExit (eps : ℕ) (X : DiscDiagram.{u, w, v} W) : Prop :=
  ∃ (faces : Finset X.toCombMap.Face) (outerWalk s₁ s₂ : List X.toCombMap.Dart)
    (k : Fin X.rCellCount) (A : CyclicArc (cellDarts X k)),
    EnclosedFaceSetSucc X faces outerWalk ∧ (∃ C ∈ X.relatorCells, C.face ∈ faces) ∧
      (cell X k).face ∉ faces ∧ invDarts X outerWalk = s₁ ++ s₂ ++ invDarts X A.darts ∧
      s₁.length ≤ eps ∧ s₂.length ≤ eps

/-- **A lake fill with two arcs outside**: a pocket region of an O-equivalent copy with letter
labels, both cycles following the boundary, holding a relator cell, with cells `Π_i'`, `Π_j'` off
it, whose inverse complement cycle reads `s_1 A_1⁻¹ s_2 A_2⁻¹`, side values of norm at most `ε`. -/
def LakeFillTwoArcExit (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) : Prop :=
  ∃ (X' : DiscDiagram.{u, w, v} W) (P : PocketRegion X')
    (C : RelatorCell X'.toCombMap X'.outerFace W) (i' j' : Fin X'.rCellCount)
    (A₁ : CyclicArc (cellDarts X' i')) (A₂ : CyclicArc (cellDarts X' j'))
    (s₁ s₂ : List X'.toCombMap.Dart),
    Nonempty (OEquivalentDiscDiagram X X') ∧
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
      P.inner.FollowsBoundary ∧ P.outer.FollowsBoundary ∧ C ∈ X'.relatorCells ∧
      C.face ∈ P.faces ∧ (cell X' i').face ∉ P.faces ∧ (cell X' j').face ∉ P.faces ∧
      invDarts X' P.outer.cycle = s₁ ++ invDarts X' A₁.darts ++ s₂ ++ invDarts X' A₂.darts ∧
      WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X' s₁)) ≤ eps ∧
      WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X' s₂)) ≤ eps

/-- **A lake fill with one arc outside is refuted below the bound**:
`P07LakeExclusion.false_of_enclosedSucc` at the identity O-equivalence. -/
theorem false_of_lakeFillOneArcExit {D : RelGenSet G Lambda} {eps rho : ℕ} {mu lambda c : ℝ}
    (hcondition : OsinCCondition D W eps mu lambda c rho) (hlambda : 0 < lambda)
    (hlambda1 : lambda ≤ 1) (hc : 0 ≤ c) (hmu : 0 < mu) (hmu1 : mu ≤ 1 / 16) (hrho : 2 ≤ rho)
    (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ))
    {X : DiscDiagram.{u, w, v} W} (hlea : X.LeastArea)
    (hbelow : OsinLemma97Below.{u, w, v} D lambda c mu eps W X.rCellCount)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (hexit : LakeFillOneArcExit eps X) : False := by
  obtain ⟨faces, outerWalk, s₁, s₂, k, A, E, ⟨C, hC, hCf⟩, hk, hdec, hs₁, hs₂⟩ := hexit
  exact P07LakeExclusion.false_of_enclosedSucc (faces := faces) (outerWalk := outerWalk)
    hcondition hlambda hlambda1 hc hmu hmu1 hrho hlarge hlea hbelow
    (OEquivalentDiscDiagram.refl X) hlabel E hC hCf hk A hdec hs₁ hs₂

/-- **A lake fill with two arcs outside is refuted below the bound**: the multiple-edge cut of the
pocket region has fewer relator cells than `X`, and clause (b) below `X` refutes it. -/
theorem false_of_lakeFillTwoArcExit {D : RelGenSet G Lambda} {eps rho : ℕ} {mu lambda c : ℝ}
    (hcondition : OsinCCondition D W eps mu lambda c rho) (hlambda : 0 < lambda)
    (hlambda1 : lambda ≤ 1) (hc : 0 ≤ c) (hmu : 0 < mu) (hmu1 : mu ≤ 1 / 16) (hrho : 2 ≤ rho)
    (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ))
    {X : DiscDiagram.{u, w, v} W} (hlea : X.LeastArea)
    (hbelow : OsinLemma97Below.{u, w, v} D lambda c mu eps W X.rCellCount)
    (hexit : LakeFillTwoArcExit D eps X) : False := by
  obtain ⟨X', P, C, i', j', A₁, A₂, s₁, s₂, ⟨e⟩, hlabel', hin, hout, hC, hCf, hi, hj, hdec,
    hnorm₁, hnorm₂⟩ := hexit
  obtain ⟨cut⟩ := nonempty_osinMultipleEdgeCut_of_pocketRegion
    GeodesicCollar.StripStep.geodesicCollarStatement_holds pocketCellTransport hcondition hlambda1
    hc hlea e hlabel' P hin hout hC hCf hi hj A₁ A₂ s₁ s₂ hdec hnorm₁ hnorm₂
  have hrho0 : 0 < rho := by omega
  exact cut.false_of_below o52LeastArea hcondition hlambda hmu hmu1 hrho0 hlarge hlea
    (hbelow cut.enclosed cut.sections cut.leastArea cut.rCellCount_pos cut.rCellCount_lt)

end Exits

/-- **The lakes residual with its lake-fill exits** (OPEN).  Every hypothesis of
`CellRoseLakesUnfilteredBelowStatement`, concluding a lake fill with one arc outside, a lake fill
with two arcs outside, or the step.  True exactly when the target is (`lakesSurgery_of_target`). -/
def CellRoseLakesSurgeryBelowStatement : Prop :=
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
                  ¬ CellFilterMove K →
                    LakeFillOneArcExit eps X ∨ LakeFillTwoArcExit D eps X ∨
                    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
                      (K' : CellPocketFaceSet D eps X' i' j'),
                      Nonempty (OEquivalentDiscDiagram X X') ∧
                        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ i' ≠ j' ∧
                        K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
                        K'.secondArc.length < (cellDarts X' j').length ∧
                        K'.repeatedVisits < K.repeatedVisits

/-- **The lakes residual from its lake-fill form.**  Raise `ρ₀` to `max (max ρ₀ 2) ρ₁`; both exits
are then refuted below the bound. -/
theorem proof_of_lakesSurgery (h : CellRoseLakesSurgeryBelowStatement.{u, w, v}) :
    CellRoseLakesUnfilteredBelowStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  obtain ⟨rho1, hrho1⟩ := SameCellSimplePocket.exists_rho_large lambda c hmu eps
  refine ⟨max (max rho0 2) rho1,
    lt_of_lt_of_le hrho0 ((le_max_left rho0 2).trans (le_max_left (max rho0 2) rho1)),
    fun rho hrho' W hcondition X i j hij hlea hbelow hlabel K hK hnft hfirst hsecond hpinch hrose
      hcut hside hshort hmove => ?_⟩
  have hleft : max rho0 2 ≤ rho := (le_max_left (max rho0 2) rho1).trans hrho'
  have h0 : rho0 ≤ rho := (le_max_left rho0 2).trans hleft
  have h2 : 2 ≤ rho := (le_max_right rho0 2).trans hleft
  have hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ) :=
    hrho1 rho ((le_max_right (max rho0 2) rho1).trans hrho')
  rcases hrho rho h0 W hcondition X i j hij hlea hbelow hlabel K hK hnft hfirst hsecond hpinch hrose
      hcut hside hshort hmove with hone | htwo | hstep
  · exact (false_of_lakeFillOneArcExit hcondition hlambda hlambda1 hc hmu hmu16 h2 hlarge hlea
      hbelow hlabel hone).elim
  · exact (false_of_lakeFillTwoArcExit hcondition hlambda hlambda1 hc hmu hmu16 h2 hlarge hlea
      hbelow htwo).elim
  · exact hstep

/-- **The lake-fill form from the lakes residual**, by `Or.inr`, at the same thresholds.  So the
statement is no stronger than the target. -/
theorem lakesSurgery_of_target (h : CellRoseLakesUnfilteredBelowStatement.{u, w, v}) :
    CellRoseLakesSurgeryBelowStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  exact ⟨rho0, hrho0, fun rho hrho' W hcond X i j hij hlea hbelow hlabel K hK hnft hfirst hsecond
    hpinch hrose hcut hside hshort hmove => Or.inr (Or.inr (hrho rho hrho' W hcond X i j hij hlea
      hbelow hlabel K hK hnft hfirst hsecond hpinch hrose hcut hside hshort hmove))⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.LakeFillOneArcExit
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.LakeFillTwoArcExit
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.false_of_lakeFillOneArcExit
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.false_of_lakeFillTwoArcExit
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CellRoseLakesSurgeryBelowStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.proof_of_lakesSurgery
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.lakesSurgery_of_target
