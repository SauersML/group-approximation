import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94OneCellFace
import GroupApproximation.GGT.VanKampen.FaceShelling
import GroupApproximation.Meta.AxiomGuard

/-!
# The cell-free branch of the one-cell pairs of Lemma 9.4, Case 1

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, for a backwards connector pair whose source and
target sides lie across one relator cell `Π` (`OsinLemma94CaseOneSameCellStatement`).  A producer
builds a pocket region across a connector and splits on a relator cell inside it.  A pocket with a
relator cell gives a loop cut (`nonempty_osinLoopCut_of_pocketRegion`).  This file proves the other
branch, in the same spelling: the inverse outer cycle reads the connector backwards, then an arc
`A` of `Π` backwards.

* `PocketRegion.outer_isRotated_of_decomposition`: that spelling makes the outer cycle a rotation
  of the connector followed by `A`.
* `false_of_sameCell_cellFree_pocketRegion_X` and `_Y`: with `q A p` (or `p A q`) an arc of `Π`,
  the Morse kills of `OsinLemma94OneCellFace` apply.  The threshold `2κ + c ≤ λ ε` comes from
  `exists_morse_threshold_of_fourPoint`.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open GroupApproximation.GGT.OsinComponents

namespace PocketRegion

/-- **The loop-cut spelling as a rotation.**  If the inverse outer cycle of a pocket region reads
`s` backwards and then `A` backwards, the outer cycle is a rotation of `s ++ A`. -/
theorem outer_isRotated_of_decomposition {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}
    (Q : PocketRegion Delta) {s A : List Delta.toCombMap.Dart}
    (hdecomposition : invDarts Delta Q.outer.cycle = invDarts Delta s ++ invDarts Delta A) :
    Q.outer.cycle ~r s ++ A := by
  rw [← Embedded.invDarts_append] at hdecomposition
  have houter := congrArg (invDarts Delta) hdecomposition
  simp only [Embedded.invDarts_invDarts] at houter
  rw [houter]
  exact List.isRotated_append

end PocketRegion

/-- **The cell-free branch, pocket across `X`.**  `htrav`, `hsource`, `htarget` and `hY` are as in
`osinLemma94CaseOneWalk_sameCell`.  Let `Q` be a pocket region with no relator cell whose inverse
outer cycle reads `X` backwards and then an arc `A` of the cell backwards.  If `q A p` is an arc of
the cell, there is a contradiction. -/
theorem false_of_sameCell_cellFree_pocketRegion_X {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {eps rho : ℕ}
    {mu lambda c kappa : ℝ} (hW : OsinCCondition D W eps mu lambda c rho) (hlambda : 0 ≤ lambda)
    (hmorse : UnboundEstimate.IsWordMorseRadius D lambda c kappa)
    (hthreshold : 2 * kappa + c ≤ lambda * eps)
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    (P : OsinLemma94RealizedPolygons S) (k : Fin P.count)
    (C : WordConnectorPair (symmetricLabelAlphabet D) (P.corner k) (P.word k) (P.sideCount k)
      (P.relatorSides k) (P.longSides k) eps)
    {j : Fin S.diagram.rCellCount} (sourceArc targetArc : CyclicArc (cellDarts S.diagram j))
    {X Y : List S.diagram.toCombMap.Dart} {r : ℕ}
    (htrav : (S.diagram.faceBoundary (P.face k)).darts.rotate r =
      X ++ targetArc.reverseDarts ++ Y ++ sourceArc.reverseDarts)
    (hsource : vertex (P.corner k C.source) (P.word k C.source) C.a *
        RelLetter.listVal (dartWord S.diagram sourceArc.reverseDarts) =
      vertex (P.corner k C.source) (P.word k C.source) C.a')
    (htarget : vertex (P.corner k C.target) (P.word k C.target) C.b' *
        RelLetter.listVal (dartWord S.diagram targetArc.reverseDarts) =
      vertex (P.corner k C.target) (P.word k C.target) C.b)
    (hY : vertex (P.corner k C.target) (P.word k C.target) C.b *
        RelLetter.listVal (dartWord S.diagram Y) =
      vertex (P.corner k C.source) (P.word k C.source) C.a)
    (Q : PocketRegion S.diagram) (hcells : ∀ cell ∈ S.diagram.relatorCells, cell.face ∉ Q.faces)
    (A : CyclicArc (cellDarts S.diagram j))
    (hdecomposition : invDarts S.diagram Q.outer.cycle =
      invDarts S.diagram X ++ invDarts S.diagram A.darts)
    (T : CyclicArc (cellDarts S.diagram j))
    (hT : T.darts = targetArc.darts ++ A.darts ++ sourceArc.darts) : False :=
  false_of_cellFree_pocket_face_X_morse hW hlambda hmorse hthreshold P k C sourceArc targetArc
    htrav hsource htarget hY Q hcells (Q.outer_isRotated_of_decomposition hdecomposition) T hT

/-- **The cell-free branch, pocket across `Y`.**  As `false_of_sameCell_cellFree_pocketRegion_X`,
with the inverse outer cycle reading `Y` backwards and then `A` backwards, and `p A q` an arc of
the cell. -/
theorem false_of_sameCell_cellFree_pocketRegion_Y {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {eps rho : ℕ}
    {mu lambda c kappa : ℝ} (hW : OsinCCondition D W eps mu lambda c rho) (hlambda : 0 ≤ lambda)
    (hmorse : UnboundEstimate.IsWordMorseRadius D lambda c kappa)
    (hthreshold : 2 * kappa + c ≤ lambda * eps)
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
    (P : OsinLemma94RealizedPolygons S) (k : Fin P.count)
    (C : WordConnectorPair (symmetricLabelAlphabet D) (P.corner k) (P.word k) (P.sideCount k)
      (P.relatorSides k) (P.longSides k) eps)
    {j : Fin S.diagram.rCellCount} (sourceArc targetArc : CyclicArc (cellDarts S.diagram j))
    {X Y : List S.diagram.toCombMap.Dart} {r : ℕ}
    (htrav : (S.diagram.faceBoundary (P.face k)).darts.rotate r =
      X ++ targetArc.reverseDarts ++ Y ++ sourceArc.reverseDarts)
    (hsource : vertex (P.corner k C.source) (P.word k C.source) C.a *
        RelLetter.listVal (dartWord S.diagram sourceArc.reverseDarts) =
      vertex (P.corner k C.source) (P.word k C.source) C.a')
    (htarget : vertex (P.corner k C.target) (P.word k C.target) C.b' *
        RelLetter.listVal (dartWord S.diagram targetArc.reverseDarts) =
      vertex (P.corner k C.target) (P.word k C.target) C.b)
    (hX : vertex (P.corner k C.source) (P.word k C.source) C.a' *
        RelLetter.listVal (dartWord S.diagram X) =
      vertex (P.corner k C.target) (P.word k C.target) C.b')
    (Q : PocketRegion S.diagram) (hcells : ∀ cell ∈ S.diagram.relatorCells, cell.face ∉ Q.faces)
    (A : CyclicArc (cellDarts S.diagram j))
    (hdecomposition : invDarts S.diagram Q.outer.cycle =
      invDarts S.diagram Y ++ invDarts S.diagram A.darts)
    (T : CyclicArc (cellDarts S.diagram j))
    (hT : T.darts = sourceArc.darts ++ A.darts ++ targetArc.darts) : False :=
  false_of_cellFree_pocket_face_Y_morse hW hlambda hmorse hthreshold P k C sourceArc targetArc
    htrav hsource htarget hX Q hcells (Q.outer_isRotated_of_decomposition hdecomposition) T hT

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.outer_isRotated_of_decomposition
#audit_axioms GroupApproximation.GGT.VanKampen.false_of_sameCell_cellFree_pocketRegion_X
#audit_axioms GroupApproximation.GGT.VanKampen.false_of_sameCell_cellFree_pocketRegion_Y
