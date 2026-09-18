import GroupApproximation.Manuscript.NonMF.Full.GL06h3.Threshold
import GroupApproximation.Manuscript.NonMF.Full.GL06h3.Wired
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionSections
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketGlueCellTransport
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellArcs
import GroupApproximation.GGT.VanKampen.GeodesicQuasiGeodesic
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06h4: the nearest-cell cut from a slit pocket

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), the all-cells case.  Infrastructure for
`thm:hull` (non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's
Lemma 9.7).

Let `Δ` be least area with at least two relator cells.  Osin takes a cell `Π` nearest to the
boundary and a path `p` of minimal length from `∂Δ` to `∂Π`, and cuts `Δ` along `p` and around
`Π`.  The remaining subdiagram `Ξ` has boundary `u p̂ R p̂⁻¹`.  Here this cut is a pocket region
of an O-equivalent copy of `Δ`, whose inverse complement cycle splits as `g s₁ t s₂`:

* `g` is a geodesic collar of a part of `∂Δ`, so no longer than `∂Δ`;
* `s₁` and `s₂` are the two sides of the geodesic slit `p̂`;
* `t` is an arc of the cell `Π`, which lies outside the pocket, read backwards.

The geometric input is `NearestCellPocketStatement`: such a pocket exists, with a relator cell
inside, and every region of an O-equivalent copy of the pocket to a slit side has target arc at
most `ε + ε` (`NearWindow`, from the minimality of `p`).  This module assembles from it the
four-section cut `GL06h3.NearestCellCut`:

* section `0` is `g`, short because `∂Δ` is;
* sections `1` and `3` are the slit sides, near by `NearWindow`;
* section `2` is the arc of `Π`; a region to it glues back by `pocketCellTransport`.

* `NearestCellPocket.toNearestCellCut`: the cut, at fixed parameters.
* `nearestCellCutSection_of_pocket`: `GL06h3.NearestCellCutSectionStatement` from the pocket.
* `refutedBelowSection_of_innerPocketEnclosedCorrected_of_nearestCellPocket`: GL06e's
  refutation below the section count, from the corrected enclosed pocket and the slit pocket.

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121); certifies no printed sentence on
its own.  `NearestCellPocketStatement` is a combinatorial clause of Osin's proof, not a
literature statement.
-/

namespace GroupApproximation.Full.GL06h4

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.WordMetric

/-! ## Cut values of four parts -/

private theorem partsCut_map_label {α β : Type*} (f : α → β) (parts : List (List α)) (k : ℕ) :
    CutSections.partsCut (parts.map (List.map f)) k = CutSections.partsCut parts k := by
  unfold CutSections.partsCut
  rw [← List.map_take, ← List.map_flatten, List.length_map]

private theorem partsCut_four_zero_succ {α : Type*} (a b c d : List α) :
    CutSections.partsCut [a, b, c, d] (0 + 1) = a.length := by
  simp [CutSections.partsCut]

private theorem partsCut_four_first {α : Type*} (a b c d : List α) :
    CutSections.partsCut [a, b, c, d] 1 = a.length := by
  simp [CutSections.partsCut]

private theorem partsCut_four_second {α : Type*} (a b c d : List α) :
    CutSections.partsCut [a, b, c, d] (1 + 1) = a.length + b.length := by
  simp [CutSections.partsCut]

private theorem partsCut_four_two {α : Type*} (a b c d : List α) :
    CutSections.partsCut [a, b, c, d] 2 = a.length + b.length := by
  simp [CutSections.partsCut]

private theorem partsCut_four_two_succ {α : Type*} (a b c d : List α) :
    CutSections.partsCut [a, b, c, d] (2 + 1) = a.length + b.length + c.length := by
  simp [CutSections.partsCut, Nat.add_assoc]

private theorem partsCut_four_third {α : Type*} (a b c d : List α) :
    CutSections.partsCut [a, b, c, d] 3 = a.length + b.length + c.length := by
  simp [CutSections.partsCut, Nat.add_assoc]

private theorem partsCut_four_fourth {α : Type*} (a b c d : List α) :
    CutSections.partsCut [a, b, c, d] (3 + 1) =
      a.length + b.length + c.length + d.length := by
  simp [CutSections.partsCut, Nat.add_assoc]

section Pocket

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **A near window of a pocket** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121).  Every region of an O-equivalent copy of the pocket to the
boundary positions `[lo, hi]` has target arc at most `ε + ε`.  On a side of the slit `p̂` this
follows from the minimality of `p`. -/
def NearWindow (D : RelGenSet G Lambda) (eps : ℕ) {X : DiscDiagram.{u, w, v} W}
    (P : PocketRegion X) (lo hi : ℕ) : Prop :=
  ∀ Xi : DiscDiagram.{u, w, v} W, OEquivalentDiscDiagram P.diagram Xi →
    ∀ a : RegionCandidate D eps Xi, a.2.target = none → lo ≤ a.2.targetArc.start.1 →
      a.2.targetArc.start.1 + a.2.targetArc.length ≤ hi → a.2.targetArc.length ≤ eps + eps

/-- **The slit pocket at a nearest cell** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121).  A pocket region of an O-equivalent copy of `Δ`, with a relator
cell inside and the nearest cell `Π` outside, whose inverse complement cycle is
`g s₁ t s₂`: a geodesic collar `g` of a part of `∂Δ`, the two geodesic sides `s₁`, `s₂` of
the slit, and an arc `t` of `Π` read backwards.  Both slit sides are near windows. -/
structure NearestCellPocket (D : RelGenSet G Lambda) (eps : ℕ)
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
  near_in : NearWindow D eps pocket outerPart.length (outerPart.length + slitIn.length)
  near_out : NearWindow D eps pocket (outerPart.length + slitIn.length + arc.length)
    (outerPart.length + slitIn.length + arc.length + slitOut.length)

end Pocket

/-- **The slit pocket at a nearest cell exists** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121).  Every least-area diagram with letter labels and at least two
relator cells has a slit pocket at a nearest cell.  Osin's proof: choose, over the O-equivalent
copies of `Δ`, a cell `Π` and a path `p` from `∂Δ` to `∂Π` of minimal length; collar `p` and
the boundary part to geodesics; cut along `p̂` and around `Π`.  A region to a slit side with a
long target arc would give, after gluing back, a shorter path from another cell to `∂Δ`. -/
def NearestCellPocketStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W),
    Delta.LeastArea → (∀ d, (symmetricLabelAlphabet D).IsLetter (Delta.label d)) →
      (∀ word ∈ W, 1 < word.length) → 2 ≤ Delta.rCellCount →
        Nonempty (NearestCellPocket D eps Delta)

section Assembly

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}

namespace NearestCellPocket

/-- The four parts are `(λ, c)`-quasi-geodesic: the geodesic ones for `λ ≤ 1`, `c ≥ 0`, the
cell arc under `C(ε, μ, λ, c, ρ)`. -/
theorem quasi (N : NearestCellPocket D eps Delta) {rho : ℕ} {mu lambda c : ℝ}
    (hcondition : OsinCCondition D W eps mu lambda c rho) (hlambda1 : lambda ≤ 1)
    (hc : 0 ≤ c) :
    ∀ part ∈ [N.outerPart, N.slitIn, invDarts N.copy N.arc.darts, N.slitOut],
      IsLambdaCQuasiGeodesicWord D lambda c (dartWord N.copy part) := by
  intro part hpart
  rcases List.mem_cons.mp hpart with rfl | hpart
  · exact isLambdaCQuasiGeodesicWord_of_isGeodesicWord D N.outer_geodesic hlambda1 hc
  rcases List.mem_cons.mp hpart with rfl | hpart
  · exact isLambdaCQuasiGeodesicWord_of_isGeodesicWord D N.slitIn_geodesic hlambda1 hc
  rcases List.mem_cons.mp hpart with rfl | hpart
  · exact CyclicArc.isLambdaCQuasiGeodesicWord_invDarts_darts_cellDarts hcondition N.arc
  obtain rfl := List.mem_singleton.mp hpart
  exact isLambdaCQuasiGeodesicWord_of_isGeodesicWord D N.slitOut_geodesic hlambda1 hc

/-- **The four sections `g s₁ t s₂`** of the pocket (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121). -/
noncomputable def sections (N : NearestCellPocket D eps Delta) {rho : ℕ}
    {mu lambda c : ℝ} (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hlambda1 : lambda ≤ 1) (hc : 0 ≤ c) :
    SectionCuts D lambda c N.pocket.diagram.boundaryWord :=
  N.pocket.fourSectionCuts D lambda c N.outerPart N.slitIn (invDarts N.copy N.arc.darts)
    N.slitOut N.decomposition (N.quasi hcondition hlambda1 hc)

theorem sections_count (N : NearestCellPocket D eps Delta) {rho : ℕ}
    {mu lambda c : ℝ} (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hlambda1 : lambda ≤ 1) (hc : 0 ≤ c) :
    (N.sections hcondition hlambda1 hc).count = 4 :=
  N.pocket.fourSectionCuts_count D lambda c N.outerPart N.slitIn (invDarts N.copy N.arc.darts)
    N.slitOut N.decomposition (N.quasi hcondition hlambda1 hc)

/-- The cut values of the four sections are the cumulative lengths of the four parts. -/
theorem sections_cut (N : NearestCellPocket D eps Delta) {rho : ℕ}
    {mu lambda c : ℝ} (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hlambda1 : lambda ≤ 1) (hc : 0 ≤ c)
    (k : Fin ((N.sections hcondition hlambda1 hc).count + 1)) :
    (N.sections hcondition hlambda1 hc).cut k =
      CutSections.partsCut [N.outerPart, N.slitIn, invDarts N.copy N.arc.darts, N.slitOut] k :=
  partsCut_map_label N.copy.label
    [N.outerPart, N.slitIn, invDarts N.copy N.arc.darts, N.slitOut] k

theorem invDarts_arc_length (N : NearestCellPocket D eps Delta) :
    (invDarts N.copy N.arc.darts).length = N.arc.length := by
  rw [invDarts, List.length_map, List.length_reverse, CyclicArc.darts_length]

/-- **The pocket cut is least area, with fewer cells** (Osin, proof of Lemma 9.7(b);
`thm:hull`, non_mf_groups_exist.tex ~2121): it has the inner cell and misses `Π`. -/
theorem leastAreaCut (N : NearestCellPocket D eps Delta) (hlea : Delta.LeastArea) :
    N.pocket.diagram.LeastArea ∧ 0 < N.pocket.diagram.rCellCount ∧
      N.pocket.diagram.rCellCount < Delta.rCellCount := by
  obtain ⟨hleast, hpos, hlt⟩ := N.pocket.diagram_leastAreaCut (N.equiv.leastArea hlea)
    N.inner_mem N.inner_face (cell_mem N.copy N.nearest) N.nearest_face
  have hcount := N.equiv.rCellCount_eq
  exact ⟨hleast, hpos, by omega⟩

/-- **Section `0` is short** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121): it is the collar `g`, no longer than `∂Δ`. -/
theorem side_short (N : NearestCellPocket D eps Delta) {rho : ℕ} {mu lambda c : ℝ}
    (hcondition : OsinCCondition D W eps mu lambda c rho) (hlambda1 : lambda ≤ 1)
    (hc : 0 ≤ c) (hboundary : Delta.boundaryWord.length ≤ eps + eps) :
    ∀ j : Fin (N.sections hcondition hlambda1 hc).count, (j : ℕ) = 0 →
      (N.sections hcondition hlambda1 hc).cut j.succ -
          (N.sections hcondition hlambda1 hc).cut j.castSucc ≤ eps + eps := by
  intro j hj
  rw [N.sections_cut hcondition hlambda1 hc, N.sections_cut hcondition hlambda1 hc,
    Fin.val_succ, Fin.val_castSucc, hj, partsCut_four_zero_succ, CutSections.partsCut_zero]
  have hle := N.outer_length_le
  omega

/-- **Sections `1` and `3` are near** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121): they are the slit sides, near windows by minimality. -/
theorem near (N : NearestCellPocket D eps Delta) {rho : ℕ} {mu lambda c : ℝ}
    (hcondition : OsinCCondition D W eps mu lambda c rho) (hlambda1 : lambda ≤ 1)
    (hc : 0 ≤ c) :
    ∀ j : Fin (N.sections hcondition hlambda1 hc).count, ((j : ℕ) = 1 ∨ (j : ℕ) = 3) →
      ∀ (Xi : DiscDiagram.{u, w, v} W), OEquivalentDiscDiagram N.pocket.diagram Xi →
        ∀ a : RegionCandidate D eps Xi,
          RegionCandidate.TargetsSectionIndex (N.sections hcondition hlambda1 hc) j a →
            a.2.targetArc.length ≤ eps + eps := by
  intro j hj Xi E a ha
  obtain ⟨hnone, hlo, hhi⟩ := ha
  rcases hj with hj | hj
  · rw [N.sections_cut hcondition hlambda1 hc, Fin.val_castSucc, hj,
      partsCut_four_first] at hlo
    rw [N.sections_cut hcondition hlambda1 hc, Fin.val_succ, hj, partsCut_four_second] at hhi
    exact N.near_in Xi E a hnone hlo hhi
  · rw [N.sections_cut hcondition hlambda1 hc, Fin.val_castSucc, hj, partsCut_four_third,
      N.invDarts_arc_length] at hlo
    rw [N.sections_cut hcondition hlambda1 hc, Fin.val_succ, hj, partsCut_four_fourth,
      N.invDarts_arc_length] at hhi
    exact N.near_out Xi E a hnone hlo hhi

/-- **Section `2` transports** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121): a region to the arc of `Π` glues back, by
`pocketCellTransport`, into a region between two distinct cells of an O-equivalent copy of
`Δ`, with the same degree. -/
theorem transport (N : NearestCellPocket D eps Delta) {rho : ℕ} {mu lambda c : ℝ}
    (hcondition : OsinCCondition D W eps mu lambda c rho) (hlambda1 : lambda ≤ 1)
    (hc : 0 ≤ c) :
    ∀ j : Fin (N.sections hcondition hlambda1 hc).count, (j : ℕ) = 2 →
      ∀ (Xi : DiscDiagram.{u, w, v} W), OEquivalentDiscDiagram N.pocket.diagram Xi →
        ∀ a : RegionCandidate D eps Xi,
          RegionCandidate.TargetsSectionIndex (N.sections hcondition hlambda1 hc) j a →
            ∃ (Y : DiscDiagram.{u, w, v} W) (b : RegionCandidate D eps Y)
              (t : Fin Y.rCellCount),
              Nonempty (OEquivalentDiscDiagram Delta Y) ∧
                b.2.target = some t ∧ b.2.source ≠ t ∧
                b.contiguityDegree = a.contiguityDegree := by
  intro j hj Xi E a ha
  obtain ⟨hnone, hlo, hhi⟩ := ha
  rw [N.sections_cut hcondition hlambda1 hc, Fin.val_castSucc, hj, partsCut_four_two] at hlo
  rw [N.sections_cut hcondition hlambda1 hc, Fin.val_succ, hj, partsCut_four_two_succ,
    N.invDarts_arc_length] at hhi
  obtain ⟨Y, b, t, ⟨F⟩, hb⟩ := pocketCellTransport D eps W N.copy N.pocket N.follows
    N.nearest N.nearest_face N.arc (N.outerPart ++ N.slitIn) N.slitOut N.decomposition Xi E a
    hnone (by rw [List.length_append]; exact hlo) (by rw [List.length_append]; exact hhi)
  exact ⟨Y, b, t, ⟨N.equiv.trans F⟩, hb⟩

/-- **The nearest-cell cut from the slit pocket** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121). -/
noncomputable def toNearestCellCut (N : NearestCellPocket D eps Delta) {rho : ℕ}
    {mu lambda c : ℝ} (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hlambda1 : lambda ≤ 1) (hc : 0 ≤ c) (hlea : Delta.LeastArea)
    (hboundary : Delta.boundaryWord.length ≤ eps + eps) :
    GL06h3.NearestCellCut D lambda c eps Delta where
  enclosed := N.pocket.diagram
  leastArea := (N.leastAreaCut hlea).1
  rCellCount_pos := (N.leastAreaCut hlea).2.1
  rCellCount_lt := (N.leastAreaCut hlea).2.2
  sections := N.sections hcondition hlambda1 hc
  count_eq := N.sections_count hcondition hlambda1 hc
  side_short := N.side_short hcondition hlambda1 hc hboundary
  near := N.near hcondition hlambda1 hc
  transport := N.transport hcondition hlambda1 hc

end NearestCellPocket

/-- **The nearest-cell cut at fixed parameters, from the slit pocket** (Osin, proof of
Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121).  The cut is carried by the input
diagram itself. -/
theorem nearestCellCutInput_of_pocket (h : NearestCellPocketStatement.{u, w, v})
    {rho : ℕ} {mu lambda c : ℝ} (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hlambda1 : lambda ≤ 1) (hc : 0 ≤ c) :
    GL06h3.NearestCellCutInput.{u, w, v} D lambda c eps W := by
  intro Xi hlea hletters hW hcells hboundary
  obtain ⟨N⟩ := h D eps W Xi hlea hletters hW hcells
  exact ⟨Xi, hlea, rfl, ⟨N.toNearestCellCut hcondition hlambda1 hc hlea hboundary⟩⟩

end Assembly

/-- **The nearest-cell cut beyond thresholds, from the slit pocket** (Osin, proof of
Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121).  No threshold is needed: every `ε`
and every `ρ ≥ 1` work. -/
theorem nearestCellCutSection_of_pocket (h : NearestCellPocketStatement.{u, w, v}) :
    GL06h3.NearestCellCutSectionStatement.{u, w, v} := by
  intro _G _ _Lambda D _hhyp lambda c _mu _hlambda hlambda1 hc _hmu _hmu1
  refine ⟨0, fun _eps _heps => ⟨1, Nat.one_pos, fun _rho _hrho _W hcondition => ?_⟩⟩
  exact nearestCellCutInput_of_pocket h hcondition hlambda1 hc

/-- **GL06e's refutation below the section count, from the slit pocket** (Osin, proof of
Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem refutedBelowSection_of_innerPocketEnclosedCorrected_of_nearestCellPocket
    (hencl : GL03BPinch.InnerPocketEnclosedTwoArcCorrected.{u, w, v})
    (h : NearestCellPocketStatement.{u, w, v}) :
    GL06e.CellPocketWalkRefutedBelowSectionStatement.{u, w, v} :=
  GL06h3.refutedBelowSection_of_innerPocketEnclosedCorrected_of_nearestCellCut hencl
    (nearestCellCutSection_of_pocket h)

end GroupApproximation.Full.GL06h4

#audit_axioms GroupApproximation.Full.GL06h4.nearestCellCutInput_of_pocket
#audit_axioms GroupApproximation.Full.GL06h4.nearestCellCutSection_of_pocket
#audit_axioms GroupApproximation.Full.GL06h4.refutedBelowSection_of_innerPocketEnclosedCorrected_of_nearestCellPocket
