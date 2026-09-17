import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCellPocketLoopCut
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf, piece 02: the loop cut of a same-cell pocket

`SameCellPocketLoopCutStatement` (`Estimating/OsinUnboundSameCellPocketAssembly`) is the `hcut`
residual of `relativeGreendlingerQuasiGeodesicLeastArea_of_residualsV8Closures`
(`Estimating/OsinGreendlingerWaistV8Closures`), whose conclusion is the least-area leaf
`RelativeGreendlingerQuasiGeodesicLeastAreaStatement` of Hull's Theorem 7.1 (Osin, math/0411039v3,
Lemmas 9.4 and 9.7).

Under `C(ε, μ, λ, c, ρ)`, let `Δ` be a least-area diagram and `d` a dart of relator cell `i` whose
reverse also lies on cell `i`, oriented toward the exterior.  If a relator cell other than cell `i`
has a dart joined to `α d` by moves avoiding the edge of `d`, then `Δ` has a loop cut.

Route (`sameCellPocketLoopCut`, `Estimating/OsinUnboundSameCellPocketLoopCut`, closed):

* `SameCellPocketEnclosed.exists_enclosedPocket`: the far faces are enclosed, in successor form,
  by the pocket walk of `d`, an arc of cell `i`, with the far relator cell inside and cell `i` outside.
* `EnclosedBridgeDoubling.arcDoublingOutput`: on an O-equivalent copy every bridge of the walk is
  doubled, keeping the walk an arc of the transported cell.
* `EnclosedPocketRegion.enclosedPocketRegionSucc`: the enclosed face set is a pocket region whose
  complement cycle is the arc.
* `OsinLoopCut.ofPocketRegion` with the empty side and the arc read backwards; the arc is
  `(λ, c)`-quasi-geodesic by the `C`-condition, which also gives `0 ≤ c` for the empty side.

This module exposes that closed theorem at the name the Greendlinger-leaf assembly consumes, with
the same universe parameters `.{u, w, v}` as the producer's `hcut` argument.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, through Osin's Lemmas 9.4 and 9.7); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece02

universe u w v

/-- **Piece 02 of the Greendlinger leaf: `SameCellPocketLoopCutStatement` holds**, with no
hypotheses. -/
theorem proof : SameCellPocketLoopCutStatement.{u, w, v} :=
  sameCellPocketLoopCut.{u, w, v}

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece02

#audit_closed_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece02.proof
