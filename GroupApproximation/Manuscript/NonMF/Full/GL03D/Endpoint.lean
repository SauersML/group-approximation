import GroupApproximation.Manuscript.NonMF.Full.GL03DKept.Reduction
import GroupApproximation.Meta.AxiomGuard

/-!
# The GL03D endpoint: the sub-arc region move from the kept-walk core

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull` in
`non_mf_groups_exist.tex` (around line 2121); certifies no printed sentence on its own.

**NOT THE UNCONDITIONAL ENDPOINT.**  `Full/GL06/Assembly` cites
`Full.GL03D.roseRegionMoveSubArc : Full.GL06f.RoseRegionMoveSubArcStatement`.  That name is
**not** declared here, because `Full.GL03D.KeptSubwalkStatement` is not proved.  It is a planar
(Jordan-region) statement, not list combinatorics.  This module declares only the conditional
endpoint

* `gl03dKept_roseRegionMoveSubArc_of_core`: from the single residual
  `GL03DKept.gl03dKept_KeptSubwalkCoreStatement`, the statement Assembly needs.

It goes through `GL03DKept.gl03dKept_keptSubwalk_of_core` and the existing
`roseRegionMoveSubArc_of_keptSubwalk` (module `Full/GL03D/KeptWalk`).  The residual is
equivalent to `KeptSubwalkStatement`, as `gl03dKept_core_of_keptSubwalk` shows both ways, but it
is strictly smaller in proof content.  Duplicate-freeness and one-way edges of the walk are
discharged generically.  The exterior, source-cell and relator-cell side conditions are discharged
whenever the kept darts meet `t_2`, meet `t_1⁻¹` or lie on a relator cell.  Once the residual is
proved, `roseRegionMoveSubArc := gl03dKept_roseRegionMoveSubArc_of_core <proof>` closes it.
-/

namespace GroupApproximation.Full.GL03D

universe u w v

/-- **The sub-arc region move from the kept-walk core** (Osin 9.7(b), `thm:hull`
infrastructure; conditional on `GL03DKept.gl03dKept_KeptSubwalkCoreStatement`). -/
theorem gl03dKept_roseRegionMoveSubArc_of_core
    (h : GL03DKept.gl03dKept_KeptSubwalkCoreStatement.{u, w, v}) :
    GL06f.RoseRegionMoveSubArcStatement.{u, w, v} :=
  roseRegionMoveSubArc_of_keptSubwalk (GL03DKept.gl03dKept_keptSubwalk_of_core h)

end GroupApproximation.Full.GL03D

#audit_axioms GroupApproximation.Full.GL03D.gl03dKept_roseRegionMoveSubArc_of_core
