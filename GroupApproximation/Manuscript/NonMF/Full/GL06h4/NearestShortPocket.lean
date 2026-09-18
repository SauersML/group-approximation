import GroupApproximation.Manuscript.NonMF.Full.GL06h4.PocketAssembly
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06h4: the slit pocket for short boundaries, with short slits allowed

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), the all-cells case.  Infrastructure for
`thm:hull` (non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's
Lemma 9.7).

`NearestCellPocketStatement` (`PocketAssembly`) asks for a slit pocket at a nearest cell for
every least-area diagram `Δ` with at least two relator cells, and for both slit sides to be
near windows (`NearWindow`).  Every use goes through `nearestCellCutInput_of_pocket`, for
diagrams with `|∂Δ| ≤ ε + ε` only.  This module isolates the strictly weaker residual
`gl06h4Nearest_shortPocketStatement`:

* the hypothesis `|∂Δ| ≤ ε + ε` is added;
* each slit side need only be a near window **or** have length at most `ε + ε`
  (`gl06h4Nearest_NearOrShort`).  A window that short is a near window by arithmetic alone
  (`gl06h4Nearest_nearWindow_of_width`): a target arc inside `[lo, hi]` has length at most
  `hi - lo`.  This discharges in particular Osin's degenerate case of a nearest cell touching
  `∂Δ` (empty slit), and every slit of length at most `ε + ε`; the minimality argument is
  needed only for long slits.

Endpoints:

* `gl06h4Nearest_shortPocket_of_nearestCellPocket`: the residual is implied by
  `NearestCellPocketStatement` (it is weaker).
* `gl06h4Nearest_nearestCellCutInput_of_shortPocket`,
  `gl06h4Nearest_nearestCellCutSection_of_shortPocket`: the residual still gives
  `GL06h3.NearestCellCutSectionStatement`.
* `gl06h4Nearest_allCellsShort_of_shortPocket`: and so GL06e's
  residual `AllCellsShortEnclosedRefutedBelowSectionStatement`.
* `gl06h4Nearest_refutedBelow_of_corrected_of_shortPocket`: GL06e's
  refutation below the section count, with the corrected enclosed pocket.

## Truth of the residual

It follows from `NearestCellPocketStatement`, whose truth check (lane gl-p07-86, Python models
in the lane scratchpad) found no counterexample: the gluing argument gives, for a region to the
slit side `s₁` with target arc at offset `k` and length `L` and right side `e ≤ ε`, a walk from
`∂Δ` to another cell of length `k + e`, so `|s₁| ≤ k + e` by minimality and `L ≤ ε`.
Degenerate cases (empty slit, a nearest cell meeting `∂Δ` in a vertex or an edge, a separating
nearest cell, `ε = 0`) were modelled.  The window bound `ε + ε` really needs minimality: for a
non-nearest cell it fails in the models.

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121); certifies no printed sentence on
its own.  `gl06h4Nearest_shortPocketStatement` is a combinatorial clause of Osin's proof, not a
literature statement.
-/

namespace GroupApproximation.Full.GL06h4

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.WordMetric

section Window

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **A near or short window** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121): the window `[lo, hi]` has width at most `ε + ε`, or it is a
near window. -/
def gl06h4Nearest_NearOrShort (D : RelGenSet G Lambda) (eps : ℕ)
    {X : DiscDiagram.{u, w, v} W} (P : PocketRegion X) (lo hi : ℕ) : Prop :=
  hi ≤ lo + (eps + eps) ∨ NearWindow D eps P lo hi

/-- **A short window is near**: a target arc inside `[lo, hi]` is no longer than `hi - lo`. -/
theorem gl06h4Nearest_nearWindow_of_width (D : RelGenSet G Lambda) (eps : ℕ)
    {X : DiscDiagram.{u, w, v} W} (P : PocketRegion X) {lo hi : ℕ}
    (h : hi ≤ lo + (eps + eps)) : NearWindow D eps P lo hi := by
  unfold NearWindow
  intro _Xi _E a _hnone hlo hhi
  omega

/-- A near or short window is a near window. -/
theorem gl06h4Nearest_nearWindow_of_nearOrShort {D : RelGenSet G Lambda} {eps : ℕ}
    {X : DiscDiagram.{u, w, v} W} {P : PocketRegion X} {lo hi : ℕ}
    (h : gl06h4Nearest_NearOrShort D eps P lo hi) : NearWindow D eps P lo hi :=
  Or.elim h (gl06h4Nearest_nearWindow_of_width D eps P) id

/-- **The slit pocket with near-or-short sides** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121).  `NearestCellPocket` with each slit side a near window or at
most `ε + ε` long. -/
structure gl06h4Nearest_Pocket (D : RelGenSet G Lambda) (eps : ℕ)
    (Delta : DiscDiagram.{u, w, v} W) where
  copy : DiscDiagram.{u, w, v} W
  equiv : OEquivalentDiscDiagram Delta copy
  pocket : PocketRegion copy
  follows : pocket.outer.FollowsBoundary
  inner : RelatorCell copy.toCombMap copy.outerFace W
  inner_mem : inner ∈ copy.relatorCells
  inner_face : inner.face ∈ pocket.faces
  nearest : Fin copy.rCellCount
  nearest_face : (cell copy nearest).face ∉ pocket.faces
  arc : CyclicArc (cellDarts copy nearest)
  outerPart : List copy.toCombMap.Dart
  slitIn : List copy.toCombMap.Dart
  slitOut : List copy.toCombMap.Dart
  decomposition : invDarts copy pocket.outer.cycle =
    outerPart ++ slitIn ++ invDarts copy arc.darts ++ slitOut
  outer_geodesic : GGT.OsinComponents.IsGeodesicWord D 1
    (RelLetter.listVal (dartWord copy outerPart)) (dartWord copy outerPart)
  slitIn_geodesic : GGT.OsinComponents.IsGeodesicWord D 1
    (RelLetter.listVal (dartWord copy slitIn)) (dartWord copy slitIn)
  slitOut_geodesic : GGT.OsinComponents.IsGeodesicWord D 1
    (RelLetter.listVal (dartWord copy slitOut)) (dartWord copy slitOut)
  outer_length_le : outerPart.length ≤ Delta.boundaryWord.length
  near_in : gl06h4Nearest_NearOrShort D eps pocket outerPart.length
    (outerPart.length + slitIn.length)
  near_out : gl06h4Nearest_NearOrShort D eps pocket
    (outerPart.length + slitIn.length + arc.length)
    (outerPart.length + slitIn.length + arc.length + slitOut.length)

end Window

section Convert

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}

/-- **The near-or-short slit pocket is a slit pocket** (Osin, proof of Lemma 9.7(b);
`thm:hull`, non_mf_groups_exist.tex ~2121): a short slit side is a near window. -/
def gl06h4Nearest_toNearestCellPocket (N : gl06h4Nearest_Pocket D eps Delta) :
    NearestCellPocket D eps Delta where
  copy := N.copy
  equiv := N.equiv
  pocket := N.pocket
  follows := N.follows
  inner := N.inner
  inner_mem := N.inner_mem
  inner_face := N.inner_face
  nearest := N.nearest
  nearest_face := N.nearest_face
  arc := N.arc
  outerPart := N.outerPart
  slitIn := N.slitIn
  slitOut := N.slitOut
  decomposition := N.decomposition
  outer_geodesic := N.outer_geodesic
  slitIn_geodesic := N.slitIn_geodesic
  slitOut_geodesic := N.slitOut_geodesic
  outer_length_le := N.outer_length_le
  near_in := gl06h4Nearest_nearWindow_of_nearOrShort N.near_in
  near_out := gl06h4Nearest_nearWindow_of_nearOrShort N.near_out

/-- **A slit pocket is a near-or-short slit pocket** (Osin, proof of Lemma 9.7(b);
`thm:hull`, non_mf_groups_exist.tex ~2121). -/
def gl06h4Nearest_ofNearestCellPocket (N : NearestCellPocket D eps Delta) :
    gl06h4Nearest_Pocket D eps Delta where
  copy := N.copy
  equiv := N.equiv
  pocket := N.pocket
  follows := N.follows
  inner := N.inner
  inner_mem := N.inner_mem
  inner_face := N.inner_face
  nearest := N.nearest
  nearest_face := N.nearest_face
  arc := N.arc
  outerPart := N.outerPart
  slitIn := N.slitIn
  slitOut := N.slitOut
  decomposition := N.decomposition
  outer_geodesic := N.outer_geodesic
  slitIn_geodesic := N.slitIn_geodesic
  slitOut_geodesic := N.slitOut_geodesic
  outer_length_le := N.outer_length_le
  near_in := Or.inr N.near_in
  near_out := Or.inr N.near_out

end Convert

/-- **The near-or-short slit pocket exists for short boundaries** (Osin, proof of
Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121).  The residual of this lane.

Strictly weaker than `NearestCellPocketStatement`
(`gl06h4Nearest_shortPocket_of_nearestCellPocket`): the hypothesis `|∂Δ| ≤ ε + ε` is added,
and a slit side of length at most `ε + ε` need not be shown near (it is near by
`gl06h4Nearest_nearWindow_of_width`).  So Osin's minimality argument is needed only for slits
longer than `ε + ε`; the empty slit of a nearest cell touching `∂Δ` is free.
True by the truth check of `NearestCellPocketStatement` (module docstring). -/
def gl06h4Nearest_shortPocketStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W),
    Delta.LeastArea → (∀ d, (symmetricLabelAlphabet D).IsLetter (Delta.label d)) →
      (∀ word ∈ W, 1 < word.length) → 2 ≤ Delta.rCellCount →
        Delta.boundaryWord.length ≤ eps + eps →
          Nonempty (gl06h4Nearest_Pocket D eps Delta)

/-- **The residual is weaker than the slit pocket statement** (Osin, proof of Lemma 9.7(b);
`thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem gl06h4Nearest_shortPocket_of_nearestCellPocket
    (h : NearestCellPocketStatement.{u, w, v}) :
    gl06h4Nearest_shortPocketStatement.{u, w, v} := by
  intro _G _ _Lambda D eps W Delta hlea hletters hW hcells _hboundary
  obtain ⟨N⟩ := h D eps W Delta hlea hletters hW hcells
  exact ⟨gl06h4Nearest_ofNearestCellPocket N⟩

/-- **The nearest-cell cut at fixed parameters, from the residual** (Osin, proof of
Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121).  As `nearestCellCutInput_of_pocket`;
the cut is carried by the input diagram itself. -/
theorem gl06h4Nearest_nearestCellCutInput_of_shortPocket
    (h : gl06h4Nearest_shortPocketStatement.{u, w, v})
    {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {eps : ℕ}
    {rho : ℕ} {mu lambda c : ℝ} (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hlambda1 : lambda ≤ 1) (hc : 0 ≤ c) :
    GL06h3.NearestCellCutInput.{u, w, v} D lambda c eps W := by
  intro Xi hlea hletters hW hcells hboundary
  obtain ⟨N⟩ := h D eps W Xi hlea hletters hW hcells hboundary
  exact ⟨Xi, hlea, rfl, ⟨(gl06h4Nearest_toNearestCellPocket N).toNearestCellCut hcondition
    hlambda1 hc hlea hboundary⟩⟩

/-- **The nearest-cell cut beyond thresholds, from the residual** (Osin, proof of
Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121).  Every `ε` and `ρ ≥ 1` work. -/
theorem gl06h4Nearest_nearestCellCutSection_of_shortPocket
    (h : gl06h4Nearest_shortPocketStatement.{u, w, v}) :
    GL06h3.NearestCellCutSectionStatement.{u, w, v} := by
  intro _G _ _Lambda D _hhyp lambda c _mu _hlambda hlambda1 hc _hmu _hmu1
  refine ⟨0, fun _eps _heps => ⟨1, Nat.one_pos, fun _rho _hrho _W hcondition => ?_⟩⟩
  exact gl06h4Nearest_nearestCellCutInput_of_shortPocket h hcondition hlambda1 hc

/-- **GL06e's all-cells short enclosed residual, from the residual** (Osin, proof of
Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem gl06h4Nearest_allCellsShort_of_shortPocket
    (h : gl06h4Nearest_shortPocketStatement.{u, w, v}) :
    GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{u, w, v} :=
  GL06h3.allCellsShortEnclosedRefutedBelowSection_of_nearestCellCutSection
    (gl06h4Nearest_nearestCellCutSection_of_shortPocket h)

/-- **GL06e's refutation below the section count, from the residual** (Osin, proof of
Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121), with the corrected enclosed
pocket. -/
theorem gl06h4Nearest_refutedBelow_of_corrected_of_shortPocket
    (hencl : GL03BPinch.InnerPocketEnclosedTwoArcCorrected.{u, w, v})
    (h : gl06h4Nearest_shortPocketStatement.{u, w, v}) :
    GL06e.CellPocketWalkRefutedBelowSectionStatement.{u, w, v} :=
  GL06h3.refutedBelowSection_of_innerPocketEnclosedCorrected_of_nearestCellCut hencl
    (gl06h4Nearest_nearestCellCutSection_of_shortPocket h)

end GroupApproximation.Full.GL06h4

#audit_axioms GroupApproximation.Full.GL06h4.gl06h4Nearest_NearOrShort
#audit_axioms GroupApproximation.Full.GL06h4.gl06h4Nearest_nearWindow_of_width
#audit_axioms GroupApproximation.Full.GL06h4.gl06h4Nearest_nearWindow_of_nearOrShort
#audit_axioms GroupApproximation.Full.GL06h4.gl06h4Nearest_Pocket
#audit_axioms GroupApproximation.Full.GL06h4.gl06h4Nearest_toNearestCellPocket
#audit_axioms GroupApproximation.Full.GL06h4.gl06h4Nearest_ofNearestCellPocket
#audit_axioms GroupApproximation.Full.GL06h4.gl06h4Nearest_shortPocketStatement
#audit_axioms GroupApproximation.Full.GL06h4.gl06h4Nearest_shortPocket_of_nearestCellPocket
#audit_axioms GroupApproximation.Full.GL06h4.gl06h4Nearest_nearestCellCutInput_of_shortPocket
#audit_axioms GroupApproximation.Full.GL06h4.gl06h4Nearest_nearestCellCutSection_of_shortPocket
#audit_axioms GroupApproximation.Full.GL06h4.gl06h4Nearest_allCellsShort_of_shortPocket
#audit_axioms GroupApproximation.Full.GL06h4.gl06h4Nearest_refutedBelow_of_corrected_of_shortPocket
