import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.WaistFrontier
import GroupApproximation.Manuscript.NonMF.Full.GL03A.RotationTurn
-- GL03B and GL03C endpoint modules as named in fk/status/GL03B.md and fk/status/GL03C.md.
import GroupApproximation.Manuscript.NonMF.Full.GL03B.Endpoint
import GroupApproximation.Manuscript.NonMF.Full.GL03C.Endpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06: Osin's Lemma 4.4 at least-area diagrams, unconditionally

The relative Greendlinger lemma (Osin, arXiv:math/0411039v3, Lemma 4.4, proved through Lemmas 9.4
and 9.7(b)) at least-area diagrams: `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement`
(module `GGT.VanKampen.Estimating.OsinAppendixSections`). This is the Greendlinger waist of Hull's
small cancellation theorem, `thm:hull` (non_mf_groups_exist.tex, around line 2121), used by the
torsion-free results of non_mf_groups_exist.tex. It certifies no printed sentence on its own.

Route: the bypass frontier of the foreign swarm,
`GreendlingerLeaf.P06Bypass.relativeGreendlingerQuasiGeodesicLeastArea_of_bypassFrontier`
(module `P06Bypass.WaistFrontier`). Its three binders are supplied by the sibling lanes:

* `Full.GL03A.classPocketRotationTurn : Piece04.ClassPocketRotationTurnStatement` (residual 04);
* `Full.GL03B.innerPocketEnclosedTwoArc : P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`
  (residual 07, through the refuted walk binder, which retires residual 06);
* `Full.GL03C.roseRegionMoveSubArc : P10Rose.RoseRegionMoveSubArcStatement` (residual 10).

The waist supplies residual 01 (`Piece01.proof`), residuals 05, 08 and 09 (`AsmTrio.closedTrio`)
and the non-rose step (`P10ChordLift.proof`).
-/

namespace GroupApproximation.Full.GL06

universe u w v

open GroupApproximation.GGT.VanKampen

/-- **Osin's Lemma 4.4 at least-area diagrams** (relative Greendlinger lemma; `thm:hull`
infrastructure, non_mf_groups_exist.tex ~2121): for a hyperbolic relative generating set and
`0 < λ ≤ 1`, `0 ≤ c`, `0 < μ ≤ 1/16`, there are `ε`, `ρ > 0` such that every least-area disc
diagram over a `C(ε, μ, λ, c, ρ)` relator set with a `(λ, c)`-quasi-geodesic boundary has an
O-equivalent diagram with a relator cell whose external contiguity arc exceeds `(1 - 13μ)` of its
boundary length. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  GreendlingerLeaf.P06Bypass.relativeGreendlingerQuasiGeodesicLeastArea_of_bypassFrontier
    GL03A.classPocketRotationTurn.{u, w, v}
    GL03B.innerPocketEnclosedTwoArc.{u, w, v}
    GL03C.roseRegionMoveSubArc.{u, w, v}

/-- The universe-`0` instance consumed by the torsion-free endpoints. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_zero :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0} :=
  relativeGreendlingerQuasiGeodesicLeastArea.{0, 0, 0}

end GroupApproximation.Full.GL06

#audit_closed_axioms GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea
#audit_closed_axioms GroupApproximation.Full.GL06.relativeGreendlingerQuasiGeodesicLeastArea_zero
