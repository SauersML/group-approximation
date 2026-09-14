import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketGlueDiagram
import GroupApproximation.GGT.VanKampen.CombMapComponents
import GroupApproximation.Meta.AxiomGuard

/-!
# Components of the glued copy of a pocket

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): regions of copies of `Γ_1` glue back into
regions of copies of `Δ`.

`PocketRegion.glueDiagram` glues an O-equivalent copy `Ξ` of the pocket diagram into the boundary
cycle of the complement, and needs that cycle to follow its boundary (`Seam.glueMap_planar`).  At a
full source arc the cycle does not follow, and the glued map can split into several components
(`OsinPocketFullArcLakeGlueModel`, `OsinPocketFullArcLobeCopyModel`).  The component route keeps the
component of the exterior face.  This module names the planarity input of that route.

* `SeamGlueComponentPlanarStatement` (not proved here): for seam data between planar maps `M` and
  `X`, if reclosing the faces off the kept set along the reversed boundary cycle gives a planar map,
  every component of the glued map is planar.
* `PocketGlueComponentPlanarStatement` (not proved here): the same for a pocket region of a disc
  diagram and an O-equivalent copy of its pocket diagram.
* `pocketGlueComponentPlanar_of_seam`: the pocket form from the seam form.

Route for the seam form.  On the `k` seam positions let `σ_C` be the corner permutation of the kept
faces, `σ_X` that of `X` off its removed face and `sh` the list order.  The glued vertices along the
seam are the cycles of `σ_X σ_C`.  Planarity of the reclosing and of `X` makes `σ_C` and `σ_X`
non-crossing with respect to `sh`; they sit on opposite sides of one circle, so every component of
the glued map is a sphere.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Surgery.MapCollapse Surgery.PocketGlue

/-- **Every component of a glued map with planar sides is planar** (not proved here).  Let `S` be
seam data between planar maps `M` and `X`, and let `B` be a boundary cycle of the faces off the kept
set, reading the reversed boundary cycle of the kept set up to rotation.  If reclosing those faces
along `B` gives a planar map, every component of the glued map is planar. -/
def SeamGlueComponentPlanarStatement : Prop :=
  ∀ (M X : CombMap.{v}) (S : Seam M X) (rest : Finset M.Face) (B : BoundaryCycle M rest),
    (∀ f, f ∈ rest ↔ f ∉ S.faces) →
      (∃ k, S.boundary.cycle.reverse.map M.alpha = B.cycle.rotate k) →
        M.IsPlanar → X.IsPlanar → (reclosedMap M rest B).IsPlanar →
          ∀ x : S.glueMap.Dart, (S.glueMap.component x).IsPlanar

/-- **Every component of the glued copy of a pocket is planar** (not proved here).  Let `P` be a
pocket region of a disc diagram `Δ`, so that both reclosings of `Δ` along its cycles are planar, and
let `Ξ` be an O-equivalent copy of the pocket diagram.  Every component of the map obtained by
gluing `Ξ` into the complement of `P` is planar. -/
def PocketGlueComponentPlanarStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (P : PocketRegion Delta) (Xi : DiscDiagram.{u, w, v} W)
    (O : OEquivalentDiscDiagram P.diagram Xi) (x : (P.glueSeam O).glueMap.Dart),
    ((P.glueSeam O).glueMap.component x).IsPlanar

/-- **The pocket form from the seam form.**  The kept faces of the seam are the complement of the
pocket, the reclosing of the pocket along its cycle is planar since the pocket is a disc region,
and the complement cycle reads the pocket cycle backwards up to rotation. -/
theorem pocketGlueComponentPlanar_of_seam (h : SeamGlueComponentPlanarStatement.{v}) :
    PocketGlueComponentPlanarStatement.{u, w, v} := by
  intro G _ Lambda W Delta P Xi O x
  exact h Delta.toCombMap Xi.toCombMap (P.glueSeam O) P.faces P.inner.toBoundaryCycle
    (fun f => ⟨fun hf hout => P.not_mem_outside hf hout, P.mem_faces_of_not_mem_outside⟩)
    P.invDarts_outer_rotate Delta.planar Xi.planar
    (replaceGRegion_planar Delta.toCombMap P.faces P.inner Delta.planar) x

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.SeamGlueComponentPlanarStatement
#audit_axioms GroupApproximation.GGT.VanKampen.PocketGlueComponentPlanarStatement
#audit_axioms GroupApproximation.GGT.VanKampen.pocketGlueComponentPlanar_of_seam
