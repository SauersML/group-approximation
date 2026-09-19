import GroupApproximation.Manuscript.NonMF.Full.GL06p.SlitCore
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06p: the windows of the slit pocket, by Osin's gluing

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), the all-cells case: "a region to `p̂` or
`p̂⁻¹` has target arc at most `ε + ε`, since `p` is minimal".  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex ~2121).  Step 4 of lane nm-gl06e's construction.

Let `Ξ` be an `O`-equivalent copy of the pocket and `a` a region of `Ξ` with a nonempty source
arc, whose target arc `[k₀, k₀ + L]` lies inside the slit side `s₁ = [lo, lo + |s₁|]`.  Glue `Ξ`
back into the complement of the pocket (`PocketRegion.glueDiagram`, which is `O`-equivalent to
the copy by `PocketRegion.glueOEquivalent`).  In the glued diagram, the `k₀ - lo` slit darts from
the foot of `s₁` followed by the reversed right side of `a` form a walk from the boundary to the
source cell of `a`.  Its value has word norm at most `(k₀ - lo) + ε`: the slit letters are
letters, and `rightSide_norm_le` bounds the rest.  Metric class-minimality of `s₁` then gives
`|s₁| ≤ (k₀ - lo) + ε`, and `k₀ + L ≤ lo + |s₁|` gives `L ≤ ε`.  For `s₂` the walk runs from the
foot of `s₂` backwards to the end of the target arc, then along the left side.

This module proves the inequalities and leaves the gluing construction as two named statements.

* `GluedSlitWalkInStatement`, `GluedSlitWalkOutStatement`: the walk in the glued diagram.  The
  ingredients are all on main:
  - `PermFirstReturn.sameCycle_iff` with `Seam.glue_sigma_firstReturn`: the glue embedding
    preserves vertices, so walks of `Ξ` transport;
  - `PocketRegion.outerWord_eq_of_oEquivalent`, `glueOuter_darts`: boundary positions of `Ξ`
    match the complement cycle;
  - the `foot_in` / `foot_out` fields of the core, carried to the glued outer face through the
    internal vertex rotations (`FollowsBoundary`);
  - `PocketRegion.glueRightCell`: the source cell of `a` as a relator cell of the glued diagram.
* `longSlitWindows_of_gluedWalk`: the window bound, from the two statements.
* `allCellsShort_of_core_of_gluedWalk`: GL06e's all-cells residual, from the core and the glued
  walks.

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121); certifies no printed sentence on
its own.  The two glued-walk statements are combinatorial clauses of Osin's proof, not
literature statements.
-/

namespace GroupApproximation.Full.GL06p

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.WordMetric

/-- **The glued walk from the foot of `s₁`** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121): a region of a copy of the pocket with a nonempty source arc and
target arc inside `s₁` gives, in a diagram `O`-equivalent to `Δ`, a walk from the boundary to a
relator cell of word norm at most `(k₀ - lo) + ε`. -/
def GluedSlitWalkInStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W)
    (C : SlitPocketCore D Delta) (Xi : DiscDiagram.{u, w, v} W),
    OEquivalentDiscDiagram C.pocket.diagram Xi →
      ∀ a : RegionCandidate D eps Xi, a.2.target = none →
        C.outerPart.length ≤ a.2.targetArc.start.1 →
        a.2.targetArc.start.1 + a.2.targetArc.length ≤ C.outerPart.length + C.slitIn.length →
        0 < a.2.sourceArc.length →
          ∃ (Y : DiscDiagram.{u, w, v} W) (_ : Nonempty (OEquivalentDiscDiagram Delta Y))
            (j : Fin Y.rCellCount) (q : List Y.toCombMap.Dart),
            IsBoundaryToCellWalk Y j q ∧
              wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord Y q)) ≤
                (a.2.targetArc.start.1 - C.outerPart.length) + eps

#audit_axioms GroupApproximation.Full.GL06p.GluedSlitWalkInStatement

/-- **The glued walk from the foot of `s₂`** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121): the same with target arc inside `s₂`, the walk running from the
end of `s₂` back to the end of the target arc and along the left side. -/
def GluedSlitWalkOutStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W)
    (C : SlitPocketCore D Delta) (Xi : DiscDiagram.{u, w, v} W),
    OEquivalentDiscDiagram C.pocket.diagram Xi →
      ∀ a : RegionCandidate D eps Xi, a.2.target = none →
        C.outerPart.length + C.slitIn.length + C.arc.length ≤ a.2.targetArc.start.1 →
        a.2.targetArc.start.1 + a.2.targetArc.length ≤
          C.outerPart.length + C.slitIn.length + C.arc.length + C.slitOut.length →
        0 < a.2.sourceArc.length →
          ∃ (Y : DiscDiagram.{u, w, v} W) (_ : Nonempty (OEquivalentDiscDiagram Delta Y))
            (j : Fin Y.rCellCount) (q : List Y.toCombMap.Dart),
            IsBoundaryToCellWalk Y j q ∧
              wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord Y q)) ≤
                (C.outerPart.length + C.slitIn.length + C.arc.length + C.slitOut.length -
                  (a.2.targetArc.start.1 + a.2.targetArc.length)) + eps

#audit_axioms GroupApproximation.Full.GL06p.GluedSlitWalkOutStatement

/-- **The windows on long slit sides, from the glued walks** (Osin, proof of Lemma 9.7(b);
`thm:hull`, non_mf_groups_exist.tex ~2121): metric class-minimality bounds each slit side by the
glued walk, and the target arc then has length at most `ε`. -/
theorem longSlitWindows_of_gluedWalk (hin : GluedSlitWalkInStatement.{u, w, v})
    (hout : GluedSlitWalkOutStatement.{u, w, v}) : longSlitWindowsStatement.{u, w, v} := by
  intro _G _ _Lambda D eps W Delta _hlea _hletters _hW _hcells _hboundary C
  refine ⟨fun _hlong => ?_, fun _hlong => ?_⟩
  · intro Xi E a hnone hlo hhi hsrc
    obtain ⟨Y, hY, j, q, hq, hnorm⟩ := hin D eps W Delta C Xi E a hnone hlo hhi hsrc
    have hmin := C.slitIn_minimal Y hY j q hq
    omega
  · intro Xi E a hnone hlo hhi hsrc
    obtain ⟨Y, hY, j, q, hq, hnorm⟩ := hout D eps W Delta C Xi E a hnone hlo hhi hsrc
    have hmin := C.slitOut_minimal Y hY j q hq
    omega

#audit_axioms GroupApproximation.Full.GL06p.longSlitWindows_of_gluedWalk

/-- **GL06e's all-cells residual from the core and the glued walks** (Osin, proof of
Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem allCellsShort_of_core_of_gluedWalk (hcore : slitPocketCoreStatement.{u, w, v})
    (hin : GluedSlitWalkInStatement.{u, w, v}) (hout : GluedSlitWalkOutStatement.{u, w, v}) :
    GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{u, w, v} :=
  allCellsShort_of_core hcore (longSlitWindows_of_gluedWalk hin hout)

#audit_axioms GroupApproximation.Full.GL06p.allCellsShort_of_core_of_gluedWalk

end GroupApproximation.Full.GL06p
