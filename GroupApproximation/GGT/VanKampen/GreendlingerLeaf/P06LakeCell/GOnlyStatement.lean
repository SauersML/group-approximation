import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.LakesSurgery
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.LakeDef
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.AssemblyStatements
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06, case (d): the lakes surgery when both lakes are `G`-only

Lane `gl-p06-12` of `lanes/carto-gl-p06.md`.  Osin, arXiv:math/0411039v3, §9, proof of
Lemma 9.7(b), case (d), in the lake-filling form of `Piece06/LakesSurgery`.  Infrastructure for
`thm:hull`; certifies no printed sentence on its own.

## Objects

`K : CellPocketFaceSet D eps X i j` has boundary `c = s₁ t̄₁ s₂ t̄₂`, where `t₁` is `K.firstArc` on
`Π_i`, `t₂` is `K.secondArc` on `Π_j`, and `|s₁|, |s₂| ≤ ε`.  `E₀` is the piece of the exterior
face in the complement of `K.faces`.  `lakeOf K k` is the piece of `Π_k` (lane gl-p06-10,
`P06LakeCell/LakeDef`).  The case hypotheses:
* `hall`: no relator cell lies in `E₀` (lane gl-p06-09);
* `G`-only lakes: every relator cell in `lakeOf K i` is `Π_i`, and likewise for `j`.

## Small model (three circles at a vertex `w`)

The outer circle `∂X` meets the `K`-part at `w`.  `Π_i` and `Π_j` are glued along `t₁`, `t₂`.
The lake `H_i` is `Π_i` together with `G`-cells on the complement arc `A` of `t₁` in `∂Π_i`, and
`H_j` is similar.  So the filled face set is `F' = F ∪ H_i ∪ H_j`, and every relator cell is in `F'`.

* **Not FALSE.**  `CellRoseLakeGOnlyBelowStatement` keeps the conclusion of
  `Piece06.CellRoseLakesSurgeryBelowStatement` and only adds hypotheses, so the target implies it at
  the same thresholds (`gOnlyBelow_of_lakesSurgery`).  The target is true: by the real Lemma 9.7 at
  the same count, the hypotheses of case (d) cannot all hold, because `F'` has boundary of length
  at most `2ε` and holds every relator cell.
* **Refutable in the model (correction of the carto expectation).**  Take the face set
  `F ∪ H_j = F' ∖ H_i`.  Its successor outside walk splices at `w` into the outer-circle part
  (`s`-parts of total length `≤ 2ε`, split into two parts of length `≤ ε`) followed by `t̄₁`.  This
  is a `Piece06.LakeFillOneArcExit` with `Π_i` off the face set and fewer relator cells, so the model
  is not the obstruction.
* **The general gap (TRUE-circular).**  The splice needs two planar facts not on disk.  (1) `H_i`
  must touch `E₀` at a vertex; this fails for a chain `E₀ ~ H_j ~ H_i`.  (2) `t̄₁` must stay one
  contiguous run in successor order at the crossed pinches (`Piece06.AllNonFirstTurnsCrossed`).  If
  either fails, the only route left is short-word Greendlinger at the same count `X.rCellCount`,
  which is the statement being proved.  Route C (fill `H_i ∖ Π_i` and exit) is blocked, since
  `H_i ∖ Π_i` has no relator cell: the `∃ C ∈ X.relatorCells, C.face ∈ faces` clause of the exit
  fails.
* **FALSE-RISK for the metric shortcut.**  "The value of `A` has norm `≤ 2ε`" is not a consequence
  of the hypotheses at fixed parameters.  If `∂Π_i` is vertex-pinched and the pocket holds `K`-parts,
  `Π_j` or relator cells, then the value of `A` is a conjugate `u · value(v) · w` and need not be
  short.  So `P06LakeCell/GOnlyBound` takes the filling as an explicit value equation.

## Endpoints

* `CellRoseLakeGOnlyBelowStatement` (OPEN, TRUE-circular), with `gOnlyBelow_of_lakesSurgery`.
* `assemblyGOnly_of_gOnlyBelow`: the same statement in the local form of lane gl-p06-13
  (`P06LakeCell.Assembly.CellRoseLakeGOnlyBelowStatement`, stated through `AllCellsEnclosed` and
  `LakeGOnly`), so `Assembly.lakesSurgery_of_cases` consumes this lane's interface.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated

/-- **Case (d) with both lakes `G`-only** (OPEN, TRUE-circular; see the module docstring).  It has
every hypothesis of `Piece06.CellRoseLakesSurgeryBelowStatement`, and in addition: no relator cell
in the exterior piece, and the only relator cell in the lake of `Π_i` (resp. `Π_j`) is `Π_i` (resp.
`Π_j`).  The conclusion is the same three-way conclusion. -/
def CellRoseLakeGOnlyBelowStatement : Prop :=
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
                  ¬Unpinched X.toCombMap K.faces → Piece06.AllNonFirstTurnsCrossed K →
                  ¬ Piece06.CellCut K → (∀ k : Fin X.rCellCount, ¬ Piece06.SideCell K k) →
                  Piece06.ShortPetalFree eps X → ¬ Piece06.CellFilterMove K →
                  (∀ C ∈ X.relatorCells,
                    C.face ∉ ExteriorComponent.component X.toCombMap K.faces X.outerFace) →
                  (∀ C ∈ X.relatorCells, C.face ∈ lakeOf K i → C.face = (cell X i).face) →
                  (∀ C ∈ X.relatorCells, C.face ∈ lakeOf K j → C.face = (cell X j).face) →
                    Piece06.LakeFillOneArcExit eps X ∨ Piece06.LakeFillTwoArcExit D eps X ∨
                    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
                      (K' : CellPocketFaceSet D eps X' i' j'),
                      Nonempty (OEquivalentDiscDiagram X X') ∧
                        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ i' ≠ j' ∧
                        K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
                        K'.secondArc.length < (cellDarts X' j').length ∧
                        K'.repeatedVisits < K.repeatedVisits

/-- **The `G`-only case from the lakes surgery target.**  Same thresholds; the three extra
hypotheses are dropped.  So the statement is true whenever the target is, and it is not stronger
than the target. -/
theorem gOnlyBelow_of_lakesSurgery (h : Piece06.CellRoseLakesSurgeryBelowStatement.{u, w, v}) :
    CellRoseLakeGOnlyBelowStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  exact ⟨rho0, hrho0, fun rho hrho' W hcond X i j hij hlea hbelow hlabel K hK hnft hfirst hsecond
    hpinch hrose hcut hside hshort hmove _ _ _ => hrho rho hrho' W hcond X i j hij hlea hbelow
      hlabel K hK hnft hfirst hsecond hpinch hrose hcut hside hshort hmove⟩

/-- **Bridge to the assembly's local form.**  `Assembly.AllCellsEnclosed K` and
`Assembly.LakeGOnly K k` unfold to the raw hypotheses of `CellRoseLakeGOnlyBelowStatement`, so this
lane's statement gives the one used by `Assembly.lakesSurgery_of_cases`, at the same thresholds. -/
theorem assemblyGOnly_of_gOnlyBelow (h : CellRoseLakeGOnlyBelowStatement.{u, w, v}) :
    Assembly.CellRoseLakeGOnlyBelowStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  exact ⟨rho0, hrho0, fun rho hrho' W hcond X i j hij hlea hbelow hlabel K hK hnft hfirst hsecond
    hpinch hrose hcut hside hshort hmove hall hgi hgj => hrho rho hrho' W hcond X i j hij hlea
      hbelow hlabel K hK hnft hfirst hsecond hpinch hrose hcut hside hshort hmove hall hgi hgj⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.CellRoseLakeGOnlyBelowStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.gOnlyBelow_of_lakesSurgery
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.assemblyGOnly_of_gOnlyBelow
