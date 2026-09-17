import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Assembly.Bypass
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06 assembly: binder 5 below the bound through the bypass

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p06-04, items (i) and (ii).

## What Piece 06 has to supply

The consumer of residual 06 is binder 5 below the bound,
`OsinMultipleEdgePocketRegionCopyBelowSectionStatement` (`Estimating/OsinPocketMultipleEdgeCopyBelow`).
The Below waist builds it from the cell step
`CellPocketOuterPinchStepSectionDistinctBelowStatement` and the proper arcs.  The cell step is
**circular in case (d)** of the lakes surgery (module `P06Assembly/CellStep`), so the region endpoint
of Piece 06 is binder 5 itself.  It follows from the enclosed inner pocket of P07 through the
pinch-free bypass (module `P06Assembly/Bypass`).

## Endpoints

* `proof_of_refuted`: binder 5 below the bound from the refuted walk binder and lane gl-p06-02's
  reduction.
* `proof_of_innerPocketEnclosed_of_bypass`: binder 5 below the bound from the two bypass
  reductions and the enclosed inner pocket residual
  `P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`.

## Once the upstream lanes land

* **Lanes gl-p06-01 and gl-p06-02** (`P06Bypass`).  Item (i) of the lane becomes
  ```
  theorem proof_of_innerPocketEnclosed
      (h : P07LakeExclusion.InnerPocketEnclosedTwoArcStatement.{u, w, v}) :
      OsinMultipleEdgePocketRegionCopyBelowSectionStatement.{u, w, v} :=
    P06Bypass.osinMultipleEdgePocketRegionCopyBelowSection_of_refuted
      (P06Bypass.refutedBelowSection_of_innerPocketEnclosed h)
  ```
  which is `proof_of_innerPocketEnclosed_of_bypass` with the two `P06Bypass` theorems as its
  first two arguments.
* **Lane gl-p07-15** (`P07InnerPocket.innerPocketEnclosed`, module `P07InnerPocket/Assembly`).  It
  is not on disk (a grep of `GreendlingerLeaf` for `theorem innerPocketEnclosed` finds nothing), so
  item (ii) is not authored, and no local stand-in is introduced.  The unconditional region endpoint
  is then the one line
  ```
  theorem proof : OsinMultipleEdgePocketRegionCopyBelowSectionStatement.{u, w, v} :=
    proof_of_innerPocketEnclosed P07InnerPocket.innerPocketEnclosed
  ```

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Assembly

universe u w v

/-- **Binder 5 below the bound from the refuted walk binder**, by lane gl-p06-02's reduction. -/
theorem proof_of_refuted (hcopy : CopyBelowOfRefutedStatement.{u, w, v})
    (hrefuted : CellPocketWalkRefutedBelowSectionStatement.{u, w, v}) :
    OsinMultipleEdgePocketRegionCopyBelowSectionStatement.{u, w, v} :=
  hcopy hrefuted

/-- **Piece 06 region endpoint, binder 5 below the bound, from the enclosed inner pocket.**  The
enclosed inner pocket refutes the walk binder (lane gl-p06-01), and the refuted binder gives binder 5
with no pinch (lane gl-p06-02).  Residual 06 (`hcellStep`) is not used. -/
theorem proof_of_innerPocketEnclosed_of_bypass
    (hrefuted : RefutedOfInnerPocketEnclosedStatement.{u, w, v})
    (hcopy : CopyBelowOfRefutedStatement.{u, w, v})
    (h : P07LakeExclusion.InnerPocketEnclosedTwoArcStatement.{u, w, v}) :
    OsinMultipleEdgePocketRegionCopyBelowSectionStatement.{u, w, v} :=
  proof_of_refuted hcopy (hrefuted h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Assembly

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Assembly.proof_of_refuted
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Assembly.proof_of_innerPocketEnclosed_of_bypass
