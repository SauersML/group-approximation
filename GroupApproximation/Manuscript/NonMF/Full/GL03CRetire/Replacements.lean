import GroupApproximation.Manuscript.NonMF.Full.GL03CRetire.Bridge
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseEndpoint.SingleRegion
import GroupApproximation.Manuscript.NonMF.Full.GL06f.Reduction
import GroupApproximation.Meta.AxiomGuard

/-!
# GL03C retirement, part 2: conditional replacements for the `GL03C/Endpoint` theorems

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull` in
`non_mf_groups_exist.tex` (around line 2121); certifies no printed sentence on its own.

`Full/GL03C/Endpoint.lean` declares four unconditional theorems, all from the FALSE
`RoseFilterWalkStatement` (`Full.GL03C.glFix01_not_roseFilterWalk`).  Each is replaced here by a
theorem CONDITIONAL on the open residual `P10Rose.RoseRegionMoveSubArcStatement`, or on its
`GL06f` spelling through the bridge of `GL03CRetire/Bridge`.

| retired `Full.GL03C.*`  | replacement                                                  |
|-------------------------|--------------------------------------------------------------|
| `roseExtremalJunction`  | none: refuted (`GreendlingerLeaf.roseJunctionRefute_not_junction`) |
| `roseRegionMoveSubArc`  | the hypothesis itself; `gl03cRetire_gl06fRegionMoveSubArc_of_p10Rose` |
| `rose`                  | `gl03cRetire_rose`, `gl03cRetire_gl06fRose`                  |
| `piece10`               | `gl03cRetire_piece10`, `gl03cRetire_piece10_of_gl06f`        |

The Piece 10 replacements go through `Piece10.proof_of_regionMoveSubArc`
(`P10RoseEndpoint/SingleRegion`).  None of them is closed: each needs a proof of the residual.
-/

namespace GroupApproximation.Full.GL03CRetire

universe u w v

open GroupApproximation.GGT GroupApproximation.GGT.VanKampen

/-- **Replacement for `Full.GL03C.piece10`** (conditional on the sub-arc region move): the
outer-pinch step of the section pinch, through `Piece10.proof_of_regionMoveSubArc`. -/
theorem gl03cRetire_piece10
    (h : GreendlingerLeaf.P10Rose.RoseRegionMoveSubArcStatement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  GreendlingerLeaf.Piece10.proof_of_regionMoveSubArc h

#audit_axioms GroupApproximation.Full.GL03CRetire.gl03cRetire_piece10

/-- **Replacement for `Full.GL03C.piece10`, `GL06f` spelling** (conditional): the outer-pinch
step from `GL06f.RoseRegionMoveSubArcStatement`, by the backward bridge and
`Piece10.proof_of_regionMoveSubArc`. -/
theorem gl03cRetire_piece10_of_gl06f (h : GL06f.RoseRegionMoveSubArcStatement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  gl03cRetire_piece10 (gl03cRetire_p10RoseRegionMoveSubArc_of_gl06f h)

#audit_axioms GroupApproximation.Full.GL03CRetire.gl03cRetire_piece10_of_gl06f

/-- **Replacement for `Full.GL03C.rose`** (conditional on the sub-arc region move): the rose
step, through `P10Rose.rose_of_regionMoveSubArc`. -/
theorem gl03cRetire_rose
    (h : GreendlingerLeaf.P10Rose.RoseRegionMoveSubArcStatement.{u, w, v}) :
    GreendlingerLeaf.P10ChordLift.RoseStepStatement.{u, w, v} :=
  GreendlingerLeaf.P10Rose.rose_of_regionMoveSubArc h

#audit_axioms GroupApproximation.Full.GL03CRetire.gl03cRetire_rose

/-- **Replacement for `Full.GL03C.rose`, `GL06f` spelling** (conditional): the rose step in the
form consumed by `Full.GL06.outerPinchStep_of_cases` (`Full/GL06/Assembly`), by the forward
bridge and `GL06f.rose_of_regionMoveSubArc`. -/
theorem gl03cRetire_gl06fRose
    (h : GreendlingerLeaf.P10Rose.RoseRegionMoveSubArcStatement.{u, w, v}) :
    GL06f.RoseStepStatement.{u, w, v} :=
  GL06f.rose_of_regionMoveSubArc (gl03cRetire_gl06fRegionMoveSubArc_of_p10Rose h)

#audit_axioms GroupApproximation.Full.GL03CRetire.gl03cRetire_gl06fRose

end GroupApproximation.Full.GL03CRetire
