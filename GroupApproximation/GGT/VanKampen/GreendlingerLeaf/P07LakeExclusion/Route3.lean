import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.LakesSurgery
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkEulerSectorFree
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellKeptCell
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketKeptCellSection
import GroupApproximation.Meta.AxiomGuard

/-!
# Route 3 to the lake exclusion: the inner two-arc pocket

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  The target is
`CellPocketWalkProperArcsBelowSectionStatement`, residual 07 of
`relativeGreendlingerQuasiGeodesicLeastArea_of_eightResidualsBelow`.

## The route

The pocket walk is `K = s_1 t̄_1 s_2 t̄_2`, with `s_1` the side of `b` leaving `Π_j`, `t_1 = α_a G_1 α_b`
on `Π_i` and `t_2 = β_b G_2 β_a` on `Π_j`.  The side `K.faces` holds the regions `a` and `b`.
The closed steps give the rest:
* `cellPocketWalkEuler` gives both Euler equalities;
* `PocketRegion.ofNoncrossingClosedWalkEuler` gives the pocket region;
* `exists_kept_of_cellPocketRegion_of_leastArea` gives a kept relator cell `Π` in `K.faces`.

`Π` reads a nontrivial word at least area, so it lies in neither `a` nor `b`.  So `Π` lies in the inner
pocket `K.faces \ (a ∪ b)`, which is bounded by the far sides `s_b'` of `b` and `s_a'` of `a` (each of
length `≤ ε`) and by the gaps `G_1`, `G_2`.  The residual `CellPocketInnerTwoArcStatement` turns that
cell into a two-arc exit (`Piece06.LakeFillTwoArcExit`) in the same diagram.  The exit is refuted
below the bound by the closed `Piece06.false_of_lakeFillTwoArcExit`.

## Why the residual is true

Take the edge class `F₀` of `Π` inside the inner pocket, and fill its lakes: `F` is every face that
`F₀` separates from the exterior across edges.
* The outer side `sideOutside K` is a disc (the outer Euler equality), so it is edge-connected and
  holds the exterior face, `Π_i` and `Π_j`.
* `a` and `b` are edge-adjacent to it, across their sides on `K` or across their arcs on `Π_i`, `Π_j`.
* So the filling adds no face of `a`, `b` or `sideOutside K`.  In particular `Π_i, Π_j ∉ F`.

Every boundary edge of `F` is an edge of `s_b'`, `G_1`, `s_a'` or `G_2`.  The boundary walk of `F`
reads sub-walks of these in cyclic order: `F` is a (possibly singular) disc, whose pinch vertices
are split into separate passages as in `IsNoncrossingClosedWalk`.  Consecutive pieces on the same
side or on the same gap merge.  Missing pieces are empty, and an empty gap is `emptyArc`.  So
`∂F = s_1' Ā_1 s_2' Ā_2`, with `A_1 ⊆ G_1`, `A_2 ⊆ G_2` and `|s_k'| ≤ ε`.  Each letter has norm at
most one, so `‖s_k'‖ ≤ ε`.  Both cycles of the filled region follow their boundary, because a filled
region has no lakes.

## Tests

* n = 1, 2: this route derives `False` from the kept cell and the below bound, and the Euler
  equalities are closed, so nothing about small counts is assumed.  A counterexample to the residual
  with one or two relator cells would need `Π ∉ {Π_i, Π_j}`, hence at least three cells.  With
  `n ≤ 2` the residual is vacuous.
* The lens (`t_1 = ∂Π_i` in full, the all-cells branch of `Proof.lean` and case (d) of Piece 06):
  the inner pocket is still bounded by `G_1`, `G_2` and the far sides, and `Π_i`, `Π_j` stay outside
  it.  A lens with a G-only side is refuted by the closed kept-cell step before the residual is
  used.  A lens with a relator cell in the inner pocket is a two-arc exit.

## Not equivalent to the target

The residual has no thresholds, no least area, no `OsinLemma97Below` and no hyperbolicity.  It is a
purely combinatorial statement about one diagram.  The target concludes proper arcs, which do not
give a two-arc exit, so the target does not imply the residual.

## Piece 06, case (d)

The residual needs the region pair `a`, `b` to locate a relator cell away from `Π_i`, `Π_j`.  Case (d)
of `CellRoseLakesSurgeryBelowStatement` has no such pair.  Its "cell outside both `Π`" part is
case (c), so case (d) still needs a same-count shrink.

* `CellPocketInnerTwoArcStatement`: the residual (not proved here).
* `proof_of_innerTwoArc`: the target from the residual.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

/-- **A relator cell in the side of the cell pocket walk, off the two regions, gives a two-arc exit.**
Let `K` be the pocket walk of the disjoint regions `a`, `b` joining the distinct cells `Π_i`, `Π_j`,
with arcs `α_a G_1 α_b` and `β_b G_2 β_a`.  The walk is noncrossing, both its sides keep the Euler
characteristic, and the exterior lies off its side.  Then a relator cell in the side that lies in
neither `a` nor `b` gives `Piece06.LakeFillTwoArcExit` in the same diagram: fill the lakes of its
edge class in the inner pocket, whose boundary reads sub-walks of the far sides and of `G_1`, `G_2`.
The module docstring argues why this is true and why it is not equivalent to the target. -/
def CellPocketInnerTwoArcStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W)
    {i j : Fin X.rCellCount} (a b : RegionCandidate D eps X) (K : CellPocketWalk D eps X i j),
    i ≠ j → a.JoinsCells i j → b.JoinsCells i j → Disjoint a.1 b.1 →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    K.firstSide = b.sideFrom j → K.secondSide = a.sideFrom i →
    (∃ G₁ : CyclicArc (cellDarts X i),
      K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i) →
    (∃ G₂ : CyclicArc (cellDarts X j),
      K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j) →
    ∀ hw : IsNoncrossingClosedWalk X.toCombMap K.walk,
      X.outerFace ∉ sideFaces X.toCombMap K.walk →
      (reclosedMap X.toCombMap (sideFaces X.toCombMap K.walk)
          (hw.innerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      (reclosedMap X.toCombMap (sideOutside X.toCombMap K.walk)
          (hw.outerCycle X.planar)).eulerCharacteristic = X.toCombMap.eulerCharacteristic →
      ∀ C ∈ X.relatorCells, C.face ∈ sideFaces X.toCombMap K.walk → C.face ∉ a.1 → C.face ∉ b.1 →
        Piece06.LakeFillTwoArcExit D eps X

/-- **The lake exclusion from the inner two-arc pocket.**  The kept relator cell of the pocket
region of the walk lies in neither region, so the residual gives a two-arc exit, which is refuted
below the bound. -/
theorem proof_of_innerTwoArc (h : CellPocketInnerTwoArcStatement.{u, w, v}) :
    CellPocketWalkProperArcsBelowSectionStatement.{u, w, v} := by
  intro G _ Lambda D _ lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨0, fun eps _ => ?_⟩
  obtain ⟨rho1, hrho1⟩ := SameCellSimplePocket.exists_rho_large lambda c hmu eps
  refine ⟨max 2 rho1, by omega, fun rho hrho W hcondition => ?_⟩
  have hlarge := hrho1 rho (le_of_max_le_right hrho)
  have hrho2 : 2 ≤ rho := le_of_max_le_left hrho
  intro Delta _ hlea hbelow S i j a b ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hw hoff
  exfalso
  have hlea' : S.diagram.LeastArea := OuterCellThickening.leastArea_of_oEquivalent S.equiv hlea
  obtain ⟨hinner, houter⟩ :=
    cellPocketWalkEuler hlea S ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hw
  obtain ⟨kept, hkept⟩ := S.exists_kept_of_cellPocketRegion_of_leastArea ha hb hab hij hai hbi K
    hfirst hsecond h₁ hlea' (PocketRegion.ofNoncrossingClosedWalkEuler hw hoff hinner houter) rfl
  rw [PocketRegion.ofNoncrossingClosedWalkEuler_faces] at hkept
  have hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1 :=
    fun C hC => DiscDiagram.leastArea_listVal_word_ne_one hlea' C hC
  have hcell : ∀ z : RegionCandidate D eps S.diagram, (cell S.diagram kept).face ∉ z.1 := by
    intro z hkz
    have hz := (z.2.boundary.all_gCells _ hkz).2
    rw [DiscDiagram.faceWord, ← S.diagram.relatorCell_word _ (cell_mem S.diagram kept)] at hz
    exact hvalue _ (cell_mem S.diagram kept) hz
  have hbelow' : OsinLemma97Below.{u, w, v} D lambda c mu eps W S.diagram.rCellCount := by
    rw [S.equiv.rCellCount_eq]
    exact hbelow
  exact Piece06.false_of_lakeFillTwoArcExit hcondition hlambda hlambda1 hc hmu hmu1 hrho2 hlarge
    hlea' hbelow'
    (h D eps S.diagram a b K hij hai hbi (S.pairwise a ha b hb hab) S.label_admissible hfirst
      hsecond h₁ h₂ hw hoff hinner houter _ (cell_mem S.diagram kept) hkept (hcell a) (hcell b))

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.CellPocketInnerTwoArcStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.proof_of_innerTwoArc
