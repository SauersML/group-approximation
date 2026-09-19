import GroupApproximation.Manuscript.NonMF.Full.GL06p.SlitCore
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketKeptCellSection
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionSimpleWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06e, step 3: the slit pocket and its complement are disc regions

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), the all-cells case.  Infrastructure for
`thm:hull` (non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's
Lemma 9.7).  Step 3 of the plan on the board of lane nm-gl06e.

The slit pocket `gl06h4Nearest_Pocket` of GL06h4 has as boundary the slit walk `g s₁ t⁻¹ s₂`:
a collar `g` on `∂Δ`, a slit `s₁` to the nearest cell `Π`, the reversed arc `t` of `Π`, and
the slit `s₂` back.  Its pocket is the side of that walk that does not contain the exterior
face, and the complement is the exterior face, the ribbon and `Π`.

This module proves that both sides are disc regions, with the complement cycle following its
boundary and its inverse reading `g s₁ t⁻¹ s₂`.  It uses the existing walk-side
infrastructure, on either of two routes:

* `SlitPocket.ofSimple`: the slit walk is a simple closed walk.  Both sides are discs and both
  cycles follow, by `PocketRegion.ofSimpleClosedWalk`.
* `SlitPocket.ofNoncrossing`: the slit walk is a noncrossing closed walk whose complement cycle
  follows.  Both Euler equalities follow from `IsNoncrossingClosedWalk.eulers_of_eitherFollows`,
  and `PocketRegion.ofNoncrossingClosedWalkEuler` gives the pocket.  The walk may touch itself
  here, for instance where `∂Δ` or `∂Π` has a cut vertex.

Both routes give a `SlitPocket`, which carries the `pocket`, `follows` and `decomposition` fields
of `GL06p.SlitPocketCore` (lane ms-green-nm's interface for steps 2 and 3).  A nonempty arc also
gives `nearest_face`, by `SlitPocket.nearest_face_not_mem`: the face across a dart of `t⁻¹` is
`Π`.  So `SlitPocket.toCore` needs only the cell, geodesic, collar and slit-minimality fields.
`slitPocketCoreStatement_of_slitPocketStatement` gives `GL06p.slitPocketCoreStatement`.

## What step 2 (the ribbon) must supply

For each least-area `Δ` in the residual:
- a copy with `OEquivalentDiscDiagram Δ copy`;
- a nearest cell, and a nonempty arc of it;
- the collar and the two slits;
- the slit walk, simple, or noncrossing with a complement cycle that follows;
- the exterior face not on the walk's side.

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121); certifies no printed sentence on
its own.  Written without a build (MSI Slurm was blocked); unprobed.
-/

namespace GroupApproximation.Full.GL06eSlit

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
open GroupApproximation.GGT.VanKampen.Surgery.MapCollapse
open GroupApproximation.WordMetric

section Slit

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **The slit walk** `g s₁ t⁻¹ s₂`: collar, slit in, reversed cell arc, slit out. -/
abbrev slitWalk (X : DiscDiagram.{u, w, v} W)
    (outerPart slitIn arcDarts slitOut : List X.toCombMap.Dart) : List X.toCombMap.Dart :=
  outerPart ++ slitIn ++ invDarts X arcDarts ++ slitOut

/-- **The nearest cell is outside the pocket** (Osin, proof of Lemma 9.7(b)).  If the cell arc
is nonempty, the reverse of one of its darts lies on the slit walk, and the face across that
dart is the cell. -/
theorem nearest_face_not_mem_sideFaces {X : DiscDiagram.{u, w, v} W}
    {nearest : Fin X.rCellCount} {arc : CyclicArc (cellDarts X nearest)}
    {outerPart slitIn slitOut : List X.toCombMap.Dart}
    (hw : IsNoncrossingClosedWalk X.toCombMap (slitWalk X outerPart slitIn arc.darts slitOut))
    (harc : arc.darts ≠ []) :
    (cell X nearest).face ∉
      sideFaces X.toCombMap (slitWalk X outerPart slitIn arc.darts slitOut) := by
  obtain ⟨d, hd⟩ : ∃ d, d ∈ arc.darts := by
    cases h : arc.darts with
    | nil => exact absurd h harc
    | cons d _ => exact ⟨d, by simp⟩
  have hface : X.toCombMap.faceOf d = (cell X nearest).face :=
    ((X.faceBoundary (cell X nearest).face).mem_iff d).mp (arc.mem_cycle_of_mem_darts hd)
  have hinv : X.toCombMap.alpha d ∈ invDarts X arc.darts :=
    List.mem_map.mpr ⟨d, List.mem_reverse.mpr hd, rfl⟩
  have hmem : X.toCombMap.alpha d ∈ slitWalk X outerPart slitIn arc.darts slitOut :=
    List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hinv)))
  have hacross :=
    And.right ((hw.isBoundaryDart_sideFaces_iff X.planar (X.toCombMap.alpha d)).mpr hmem)
  have heq : X.toCombMap.faceOf (X.toCombMap.alpha (X.toCombMap.alpha d)) =
      (cell X nearest).face := by
    rw [X.toCombMap.alpha_involutive d]
    exact hface
  intro hin
  exact hacross (by rw [heq]; exact hin)

/-- **A slit pocket** (Osin, proof of Lemma 9.7(b)): a copy of `Δ` with a nearest cell and an
arc of it, a collar and two slits whose walk `g s₁ t⁻¹ s₂` is noncrossing, and a pocket region
on the walk's side whose complement cycle follows its boundary and inverts to the walk. -/
structure SlitPocket (Delta : DiscDiagram.{u, w, v} W) where
  copy : DiscDiagram.{u, w, v} W
  equiv : OEquivalentDiscDiagram Delta copy
  nearest : Fin copy.rCellCount
  arc : CyclicArc (cellDarts copy nearest)
  outerPart : List copy.toCombMap.Dart
  slitIn : List copy.toCombMap.Dart
  slitOut : List copy.toCombMap.Dart
  noncrossing : IsNoncrossingClosedWalk copy.toCombMap
    (slitWalk copy outerPart slitIn arc.darts slitOut)
  pocket : PocketRegion copy
  faces_eq : pocket.faces =
    sideFaces copy.toCombMap (slitWalk copy outerPart slitIn arc.darts slitOut)
  follows : pocket.outer.FollowsBoundary
  decomposition : invDarts copy pocket.outer.cycle =
    outerPart ++ slitIn ++ invDarts copy arc.darts ++ slitOut

namespace SlitPocket

variable {Delta : DiscDiagram.{u, w, v} W}

/-- **The slit pocket of a simple slit walk.**  Both sides of a simple closed walk are discs,
and both boundary cycles follow (`PocketRegion.ofSimpleClosedWalk`). -/
noncomputable def ofSimple (copy : DiscDiagram.{u, w, v} W)
    (equiv : OEquivalentDiscDiagram Delta copy) (nearest : Fin copy.rCellCount)
    (arc : CyclicArc (cellDarts copy nearest)) (outerPart slitIn slitOut : List copy.toCombMap.Dart)
    (hw : IsSimpleClosedWalk copy.toCombMap (slitWalk copy outerPart slitIn arc.darts slitOut))
    (hout : copy.outerFace ∉
      sideFaces copy.toCombMap (slitWalk copy outerPart slitIn arc.darts slitOut)) :
    SlitPocket Delta where
  copy := copy
  equiv := equiv
  nearest := nearest
  arc := arc
  outerPart := outerPart
  slitIn := slitIn
  slitOut := slitOut
  noncrossing := hw.isNoncrossingClosedWalk
  pocket := PocketRegion.ofSimpleClosedWalk (Delta := copy) hw hout
  faces_eq := PocketRegion.ofSimpleClosedWalk_faces (Delta := copy) hw hout
  follows := (PocketRegion.ofSimpleClosedWalk_followsBoundary (Delta := copy) hw hout).2
  decomposition := PocketRegion.ofSimpleClosedWalk_invDarts_outer (Delta := copy) hw hout

/-- **The slit pocket of a noncrossing slit walk whose complement cycle follows.**  One following
cycle gives both Euler equalities (`IsNoncrossingClosedWalk.eulers_of_eitherFollows`), and those
give the pocket region (`PocketRegion.ofNoncrossingClosedWalkEuler`). -/
noncomputable def ofNoncrossing (copy : DiscDiagram.{u, w, v} W)
    (equiv : OEquivalentDiscDiagram Delta copy) (nearest : Fin copy.rCellCount)
    (arc : CyclicArc (cellDarts copy nearest)) (outerPart slitIn slitOut : List copy.toCombMap.Dart)
    (hw : IsNoncrossingClosedWalk copy.toCombMap (slitWalk copy outerPart slitIn arc.darts slitOut))
    (hout : copy.outerFace ∉
      sideFaces copy.toCombMap (slitWalk copy outerPart slitIn arc.darts slitOut))
    (hfollow : (hw.outerCycle copy.planar).FollowsBoundary) :
    SlitPocket Delta where
  copy := copy
  equiv := equiv
  nearest := nearest
  arc := arc
  outerPart := outerPart
  slitIn := slitIn
  slitOut := slitOut
  noncrossing := hw
  pocket := PocketRegion.ofNoncrossingClosedWalkEuler (Delta := copy) hw hout
    (hw.eulers_of_eitherFollows copy.planar (Or.inl hfollow)).1
    (hw.eulers_of_eitherFollows copy.planar (Or.inl hfollow)).2
  faces_eq := rfl
  follows := hfollow
  decomposition := PocketRegion.invDarts_reverse_map_alpha (Delta := copy)
    (slitWalk copy outerPart slitIn arc.darts slitOut)

/-- The face of a dart of the slit walk is inside the pocket. -/
theorem faceOf_mem_faces (S : SlitPocket Delta) {d : S.copy.toCombMap.Dart}
    (hd : d ∈ slitWalk S.copy S.outerPart S.slitIn S.arc.darts S.slitOut) :
    S.copy.toCombMap.faceOf d ∈ S.pocket.faces := by
  rw [S.faces_eq]
  exact And.left ((S.noncrossing.isBoundaryDart_sideFaces_iff S.copy.planar d).mpr hd)

/-- The face across a dart of the slit walk is outside the pocket. -/
theorem faceOf_alpha_not_mem_faces (S : SlitPocket Delta) {d : S.copy.toCombMap.Dart}
    (hd : d ∈ slitWalk S.copy S.outerPart S.slitIn S.arc.darts S.slitOut) :
    S.copy.toCombMap.faceOf (S.copy.toCombMap.alpha d) ∉ S.pocket.faces := by
  rw [S.faces_eq]
  exact And.right ((S.noncrossing.isBoundaryDart_sideFaces_iff S.copy.planar d).mpr hd)

/-- **The nearest cell is outside the pocket** when its arc is nonempty. -/
theorem nearest_face_not_mem (S : SlitPocket Delta) (harc : S.arc.darts ≠ []) :
    (cell S.copy S.nearest).face ∉ S.pocket.faces := by
  rw [S.faces_eq]
  exact nearest_face_not_mem_sideFaces S.noncrossing harc

/-- **The slit pocket core from a slit pocket** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121).  The disc-region fields of `GL06p.SlitPocketCore` come from `S`,
and `nearest_face` from the nonempty arc.  The remaining fields are the cell inside the pocket,
the three geodesic sides, the collar bound, the metric minimality of the two slits and their two
feet on the boundary. -/
noncomputable def toCore {D : RelGenSet G Lambda} (S : SlitPocket Delta)
    (harc : S.arc.darts ≠ [])
    (inner : RelatorCell S.copy.toCombMap S.copy.outerFace W)
    (inner_mem : inner ∈ S.copy.relatorCells) (inner_face : inner.face ∈ S.pocket.faces)
    (outer_geodesic : GGT.OsinComponents.IsGeodesicWord D 1
      (RelLetter.listVal (dartWord S.copy S.outerPart)) (dartWord S.copy S.outerPart))
    (slitIn_geodesic : GGT.OsinComponents.IsGeodesicWord D 1
      (RelLetter.listVal (dartWord S.copy S.slitIn)) (dartWord S.copy S.slitIn))
    (slitOut_geodesic : GGT.OsinComponents.IsGeodesicWord D 1
      (RelLetter.listVal (dartWord S.copy S.slitOut)) (dartWord S.copy S.slitOut))
    (outer_length_le : S.outerPart.length ≤ Delta.boundaryWord.length)
    (slitIn_minimal : GL06p.MetricClassMinimal D Delta S.slitIn.length)
    (slitOut_minimal : GL06p.MetricClassMinimal D Delta S.slitOut.length)
    (foot_in : ∀ d ∈ S.slitIn.head?, ∃ b : S.copy.toCombMap.Dart,
      S.copy.toCombMap.faceOf b = S.copy.outerFace ∧
        S.copy.toCombMap.vertexOf b = S.copy.toCombMap.vertexOf d)
    (foot_out : ∀ d ∈ S.slitOut.getLast?, ∃ b : S.copy.toCombMap.Dart,
      S.copy.toCombMap.faceOf b = S.copy.outerFace ∧
        S.copy.toCombMap.vertexOf b = S.copy.toCombMap.vertexOf (S.copy.toCombMap.alpha d)) :
    GL06p.SlitPocketCore D Delta where
  copy := S.copy
  equiv := S.equiv
  pocket := S.pocket
  follows := S.follows
  inner := inner
  inner_mem := inner_mem
  inner_face := inner_face
  nearest := S.nearest
  nearest_face := S.nearest_face_not_mem harc
  arc := S.arc
  outerPart := S.outerPart
  slitIn := S.slitIn
  slitOut := S.slitOut
  decomposition := S.decomposition
  outer_geodesic := outer_geodesic
  slitIn_geodesic := slitIn_geodesic
  slitOut_geodesic := slitOut_geodesic
  outer_length_le := outer_length_le
  slitIn_minimal := slitIn_minimal
  slitOut_minimal := slitOut_minimal
  foot_in := foot_in
  foot_out := foot_out

end SlitPocket

end Slit

/-- **Slit pockets exist for every diagram with a metric nearest walk** (Osin, proof of
Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121), under the hypotheses of
`GL06p.slitPocketCoreStatement`.  It asks for a slit pocket with a nonempty arc, which is steps 2
and 3 (`SlitPocket.ofSimple`, `SlitPocket.ofNoncrossing`), and for the fields outside the disc
regions: a relator cell inside the pocket, the geodesic sides, the collar bound, slit
minimality and the two feet.  Not proved here. -/
def SlitPocketStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W),
    Delta.LeastArea → (∀ d, (symmetricLabelAlphabet D).IsLetter (Delta.label d)) →
      (∀ word ∈ W, 1 < word.length) → 2 ≤ Delta.rCellCount →
        GL06p.MetricNearestWalk D Delta →
          ∃ S : SlitPocket Delta, S.arc.darts ≠ [] ∧
            ∃ inner : RelatorCell S.copy.toCombMap S.copy.outerFace W,
              inner ∈ S.copy.relatorCells ∧ inner.face ∈ S.pocket.faces ∧
              GGT.OsinComponents.IsGeodesicWord D 1
                (RelLetter.listVal (dartWord S.copy S.outerPart)) (dartWord S.copy S.outerPart) ∧
              GGT.OsinComponents.IsGeodesicWord D 1
                (RelLetter.listVal (dartWord S.copy S.slitIn)) (dartWord S.copy S.slitIn) ∧
              GGT.OsinComponents.IsGeodesicWord D 1
                (RelLetter.listVal (dartWord S.copy S.slitOut)) (dartWord S.copy S.slitOut) ∧
              S.outerPart.length ≤ Delta.boundaryWord.length ∧
              GL06p.MetricClassMinimal D Delta S.slitIn.length ∧
              GL06p.MetricClassMinimal D Delta S.slitOut.length ∧
              (∀ d ∈ S.slitIn.head?, ∃ b : S.copy.toCombMap.Dart,
                S.copy.toCombMap.faceOf b = S.copy.outerFace ∧
                  S.copy.toCombMap.vertexOf b = S.copy.toCombMap.vertexOf d) ∧
              (∀ d ∈ S.slitOut.getLast?, ∃ b : S.copy.toCombMap.Dart,
                S.copy.toCombMap.faceOf b = S.copy.outerFace ∧
                  S.copy.toCombMap.vertexOf b =
                    S.copy.toCombMap.vertexOf (S.copy.toCombMap.alpha d))

/-- **Steps 2 and 3 of GL06p from the slit pockets** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121).  With `GL06p.longSlitWindowsStatement` (step 4),
`GL06p.allCellsShort_of_core` then closes GL06e's all-cells residual. -/
theorem slitPocketCoreStatement_of_slitPocketStatement (h : SlitPocketStatement.{u, w, v}) :
    GL06p.slitPocketCoreStatement.{u, w, v} := by
  intro _G _ _Lambda D W Delta hlea hletters hW hcells hpath
  obtain ⟨S, harc, inner, hmem, hface, hg₁, hg₂, hg₃, hlen, hmin₁, hmin₂, hfin, hfout⟩ :=
    h D W Delta hlea hletters hW hcells hpath
  exact ⟨S.toCore harc inner hmem hface hg₁ hg₂ hg₃ hlen hmin₁ hmin₂ hfin hfout⟩

end GroupApproximation.Full.GL06eSlit

#audit_axioms GroupApproximation.Full.GL06eSlit.nearest_face_not_mem_sideFaces
#audit_axioms GroupApproximation.Full.GL06eSlit.SlitPocket.ofSimple
#audit_axioms GroupApproximation.Full.GL06eSlit.SlitPocket.ofNoncrossing
#audit_axioms GroupApproximation.Full.GL06eSlit.SlitPocket.nearest_face_not_mem
#audit_axioms GroupApproximation.Full.GL06eSlit.SlitPocket.toCore
#audit_axioms GroupApproximation.Full.GL06eSlit.slitPocketCoreStatement_of_slitPocketStatement
