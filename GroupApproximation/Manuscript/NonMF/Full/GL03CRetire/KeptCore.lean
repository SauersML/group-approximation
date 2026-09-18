import GroupApproximation.Manuscript.NonMF.Full.GL03CRetire.Replacements
import GroupApproximation.Manuscript.NonMF.Full.GL03D.Endpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# GL03C retirement, part 3: the Piece 10 replacement from the GL03D kept-walk core

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull` in
`non_mf_groups_exist.tex` (around line 2121); certifies no printed sentence on its own.

`Full/GL03D/Endpoint` reduces `GL06f.RoseRegionMoveSubArcStatement` to the single residual
`GL03DKept.gl03dKept_KeptSubwalkCoreStatement` (`gl03dKept_roseRegionMoveSubArc_of_core`).
The backward bridge of `GL03CRetire/Bridge` carries that residual to the `P10Rose` spelling.
This gives the retired `Full.GL03C.piece10` a second conditional replacement.  Its route is
`Piece10.proof_of_regionMoveSubArc`, and its hypothesis is the GL03D core in place of the sub-arc
region move.  It is still CONDITIONAL: the core statement is open.
-/

namespace GroupApproximation.Full.GL03CRetire

universe u w v

open GroupApproximation.GGT GroupApproximation.GGT.VanKampen

/-- The `P10Rose` sub-arc region move from the GL03D kept-walk core (conditional). -/
theorem gl03cRetire_p10RoseRegionMoveSubArc_of_keptSubwalkCore
    (h : GL03DKept.gl03dKept_KeptSubwalkCoreStatement.{u, w, v}) :
    GreendlingerLeaf.P10Rose.RoseRegionMoveSubArcStatement.{u, w, v} :=
  gl03cRetire_p10RoseRegionMoveSubArc_of_gl06f (GL03D.gl03dKept_roseRegionMoveSubArc_of_core h)

#audit_axioms
  GroupApproximation.Full.GL03CRetire.gl03cRetire_p10RoseRegionMoveSubArc_of_keptSubwalkCore

/-- **Replacement for `Full.GL03C.piece10` from the GL03D core** (conditional): the outer-pinch
step through `Piece10.proof_of_regionMoveSubArc`. -/
theorem gl03cRetire_piece10_of_keptSubwalkCore
    (h : GL03DKept.gl03dKept_KeptSubwalkCoreStatement.{u, w, v}) :
    PocketOuterPinchStepSectionStatement.{u, w, v} :=
  gl03cRetire_piece10 (gl03cRetire_p10RoseRegionMoveSubArc_of_keptSubwalkCore h)

#audit_axioms GroupApproximation.Full.GL03CRetire.gl03cRetire_piece10_of_keptSubwalkCore

end GroupApproximation.Full.GL03CRetire
