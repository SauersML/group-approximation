import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.LakesSurgery
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.LakeDef
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.AssemblyDefs
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06, case (d): a lake of `Π_i` with a second relator cell gives a lake-fill exit

Lane `gl-p06-11` of `lanes/carto-gl-p06.md`.  Osin, arXiv:math/0411039v3, §9, proof of
Lemma 9.7(b), in the lake-filling form of `Piece06/LakesSurgery`.  Certifies no printed sentence
on its own.

## Objects

`K : CellPocketFaceSet D eps X i j` has boundary cycle `c = s₁ t̄₁ s₂ t̄₂`, with `t₁`, `t₂` arcs of
`Π_i ≠ Π_j` and `|s₁|, |s₂| ≤ ε`.  Case (d) is `Assembly.AllCellsEnclosed K` (no relator cell in
the exterior piece `E₀`).  `lakeOf K i` (lane gl-p06-10) is the piece of `Π_i` in the complement of
`K.faces`.  The extra hypothesis is a relator cell `C` with `Π_C ∈ lakeOf K i` and `Π_C ≠ Π_i`.

## Truth check (paper)

1. **Correction of the lane route (LOUD).**  The lane takes `H' = lakeOf K i ∖ {Π_i}` with lakes
   filled.  That set need not be edge-connected: `Π_i` may meet `K.faces` along side darts as well
   as along `t₁` (`SideCell` only forbids a whole cell on the sides), so `Π_i ∪ K.faces` can cut
   the lake into several pieces, and the outside walk of `H'` is then not one closed walk.  The
   corrected route takes `H`, the piece of `Π_C` in the complement of `K.faces ∪ {Π_i}`, with its
   lakes filled.  `Π_j` is never removed, so it never lies on the walk of `H`.  Hence the two-arc
   subcase (where `Π_j` is also in the lake), and the norm bounds it would need, do not arise on
   this route.
2. **Walk darts.**  Let `e` be a dart of the inverse outside walk of the filled `H`: its face is in
   `H` and the face of `α e` is off `H`.  An absorbed face cannot carry `e`, since it is in the same
   component of the complement of `H` as the face across `e`.  So the face across `e` is in
   `K.faces ∪ {Π_i}` (any other edge is crossed).  If it is in `K.faces`, `α e` is a boundary dart
   of `K.faces` whose far face is not `Π_i` (it is the face of `e`, in `H`), so
   `α e ∈ s₁ ++ s₂` (`lake_boundary_subset_cycle`).  Otherwise `α e` is a dart of `Π_i`.
3. **Order of the side pieces (the lane's check).**  At crossed pinches
   (`AllNonFirstTurnsCrossed`) the pieces of `s₁` and `s₂` on the walk of `H` may interleave.  This
   is **harmless** for the one-arc exit: only lengths enter.  If the walk reads `P ++ Ā` with every
   `α e` (`e ∈ P`) in `s₁ ++ s₂`, then `P` is duplicate free (the walk is), `α` is injective, so
   `|P| ≤ |s₁| + |s₂| ≤ 2ε`, and `P = P.take ε ++ P.drop ε` gives `s₁' ++ s₂' ++ Ā` with
   `|s₁'|, |s₂'| ≤ ε` (`P06LakeCell/ExitOrder`, proved).
4. **Remaining gap (not proved in the corpus).**  The contact of `H` with `Π_i` is one cyclic arc,
   and the outside walk of the filled `H` is an `EnclosedFaceSetSucc` rotated so that this arc
   comes last.  `Estimating/OsinPocketLakeAbsorption` states: "The walk order of the new boundary
   cycle is not proved here."  This is `CaseDLakeRelatorOrderStatement` (`ExitOrder`).

Small models: the three circles of `Piece06/LakesBelow` with a second cell inside the lake of
`Π_i` give the walk `s₁' Ā` (one arc of `Π_i`, nothing of `Π_j`).  Vacuous at one relator cell.

## Shape

At fixed `eps` and `rho` (no thresholds) and for the lake of `Π_i` only.  Lane 13's
`Assembly.CaseDLakeRelatorExitStatement` has the thresholds of `LakesSurgery` and either lake.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated

/-- **Case (d) with a second relator cell in the lake of `Π_i` gives a lake-fill exit** (OPEN).
Every hypothesis of `Piece06.CellRoseLakesSurgeryBelowStatement` at fixed `eps` and `rho`,
together with `Assembly.AllCellsEnclosed K` and a relator cell other than `Π_i` in `lakeOf K i`.
It concludes one of the two lake-fill exits. -/
def CaseDLakeRelatorExitStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∀ (eps rho : ℕ) (W : Set (List (RelLetter G Lambda))),
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
              Assembly.AllCellsEnclosed K →
              (∃ C ∈ X.relatorCells, C.face ∈ lakeOf K i ∧ C.face ≠ (cell X i).face) →
                Piece06.LakeFillOneArcExit eps X ∨ Piece06.LakeFillTwoArcExit D eps X

/-- **The lakes surgery in case (d) with a second relator cell in the lake of `Π_i`**: the
conclusion of `Piece06.CellRoseLakesSurgeryBelowStatement`, by its first two disjuncts. -/
theorem lakesSurgery_caseD_of_relatorExit (h : CaseDLakeRelatorExitStatement.{u, w, v})
    {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda)
    (hhyp : ∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta)
    (lambda c mu : ℝ) (hlambda : 0 < lambda) (hlambda1 : lambda ≤ 1) (hc : 0 ≤ c) (hmu : 0 < mu)
    (hmu16 : mu ≤ 1 / 16) (eps rho : ℕ) (W : Set (List (RelLetter G Lambda)))
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (X : DiscDiagram.{u, w, v} W) (i j : Fin X.rCellCount) (hij : i ≠ j) (hlea : X.LeastArea)
    (hbelow : OsinLemma97Below.{u, w, v} D lambda c mu eps W X.rCellCount)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : CellPocketFaceSet D eps X i j) (hK : K.ClosedWalk) (hnft : ¬ K.FirstTurns)
    (hfirst : K.firstArc.length < (cellDarts X i).length)
    (hsecond : K.secondArc.length < (cellDarts X j).length)
    (hpinch : ¬Unpinched X.toCombMap K.faces) (hrose : Piece06.AllNonFirstTurnsCrossed K)
    (hcut : ¬ Piece06.CellCut K) (hsideCell : ∀ k : Fin X.rCellCount, ¬ Piece06.SideCell K k)
    (hshort : Piece06.ShortPetalFree eps X) (hmove : ¬ Piece06.CellFilterMove K)
    (hall : Assembly.AllCellsEnclosed K)
    (hsec : ∃ C ∈ X.relatorCells, C.face ∈ lakeOf K i ∧ C.face ≠ (cell X i).face) :
    Piece06.LakeFillOneArcExit eps X ∨ Piece06.LakeFillTwoArcExit D eps X ∨
      ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
        (K' : CellPocketFaceSet D eps X' i' j'),
        Nonempty (OEquivalentDiscDiagram X X') ∧
          (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ i' ≠ j' ∧
          K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
          K'.secondArc.length < (cellDarts X' j').length ∧
          K'.repeatedVisits < K.repeatedVisits := by
  rcases h D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16 eps rho W hcondition X i j hij hlea
      hbelow hlabel K hK hnft hfirst hsecond hpinch hrose hcut hsideCell hshort hmove hall
      hsec with hone | htwo
  · exact Or.inl hone
  · exact Or.inr (Or.inl htwo)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.CaseDLakeRelatorExitStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.lakesSurgery_caseD_of_relatorExit
