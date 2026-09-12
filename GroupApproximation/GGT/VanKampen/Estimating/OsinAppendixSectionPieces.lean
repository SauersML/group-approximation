import GroupApproximation.GGT.VanKampen.Estimating.PieceBridge
import GroupApproximation.GGT.VanKampen.Estimating.ContiguityGeometry
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSections
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma O52 on actual contiguity regions

Osin, arXiv:math/0411039v3: "for every `ε`-contiguity subdiagram `Γ` of a cell
`Π` to another cell `Σ`", the two contiguity arcs form a published piece, so
each is shorter than `μ` times the perimeter.  On main this transfer
(`Estimating/PieceBridge.lean`) is stated for the historical
`Embedded.Contiguity`, whose non-cancellation clause comes from the stored
`o52Certificate` and `DiscDiagram.Reduced`.  The regions of Definition 9.2 are
`Embedded.ContiguityGeometry` witnesses with no such certificate
(`Estimating/OsinAppendixSections.lean` explains why).

This file ports the transfer to `ContiguityGeometry`.  Everything except the
non-cancellation clause is supplied by the region itself: its `pasting` gives
the boundary-arc equation (`arcs_value`), and the published piece and both O52
charges follow as on main.  The clause is an explicit field of
`ContiguityGeometry.PieceEquations`.  Osin obtains it from least area, "cut the
subdiagram and fill the obtained hole with a diagram without `R`-cells, reducing
the number of `R`-cells by 2", and that producer is the named statement
`O52LeastAreaStatement` below, to be proved by the G-disc surgery.
-/

namespace GroupApproximation.GGT.VanKampen.Embedded

open GroupApproximation.HullSC GroupApproximation.WordMetric

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w}
  {D : GGT.RelGenSet G Lambda}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {faces : Finset Delta.toCombMap.Face}

namespace ContiguityGeometry

/-! ## The boundary-arc equation from the region's own pasting -/

/-- Identity of the cyclic G-region boundary gives the arc equation. -/
theorem arcs_value_of_cycle_value_one
    (Gamma : ContiguityGeometry D eps Delta faces)
    (hcycle : GGT.RelLetter.listVal
      (dartWord Delta Gamma.boundary.cycle) = 1) :
    GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.darts) =
      GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide) *
        GGT.RelLetter.listVal
          (dartWord Delta
            (targetBoundaryDarts Delta Gamma.target Gamma.targetArc)) *
        GGT.RelLetter.listVal (dartWord Delta Gamma.leftSide) := by
  have hdecomposition := Gamma.boundary_decomposition
  rw [hdecomposition, dartWord_append, dartWord_append, dartWord_append,
    RelWord.listVal_append, RelWord.listVal_append,
    RelWord.listVal_append] at hcycle
  have hreverse :
      GGT.RelLetter.listVal
          (dartWord Delta Gamma.sourceArc.reverseDarts) =
        (GGT.RelLetter.listVal
          (dartWord Delta Gamma.sourceArc.darts))⁻¹ := by
    exact listVal_dartWord_reverse_alpha Delta Gamma.sourceArc.darts
  rw [hreverse] at hcycle
  calc
    GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.darts) =
        GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.darts) * 1 := by
      group
    _ = GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.darts) *
        ((GGT.RelLetter.listVal
            (dartWord Delta Gamma.sourceArc.darts))⁻¹ *
          GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide) *
          GGT.RelLetter.listVal
            (dartWord Delta
              (targetBoundaryDarts Delta Gamma.target Gamma.targetArc)) *
          GGT.RelLetter.listVal (dartWord Delta Gamma.leftSide)) := by
      rw [hcycle]
    _ = GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide) *
        GGT.RelLetter.listVal
          (dartWord Delta
            (targetBoundaryDarts Delta Gamma.target Gamma.targetArc)) *
        GGT.RelLetter.listVal (dartWord Delta Gamma.leftSide) := by
      group

/-- **The arc equation of an actual region**, from its stored shelling. -/
theorem arcs_value (Gamma : ContiguityGeometry D eps Delta faces) :
    GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.darts) =
      GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide) *
        GGT.RelLetter.listVal
          (dartWord Delta
            (targetBoundaryDarts Delta Gamma.target Gamma.targetArc)) *
        GGT.RelLetter.listVal (dartWord Delta Gamma.leftSide) := by
  obtain ⟨_l, hshell⟩ := Gamma.pasting
  exact Gamma.arcs_value_of_cycle_value_one
    (Gamma.boundary.cycle_value_eq_one_of_pasting
      (faceSetWordHomotopy_of_shelling hshell))

/-! ## The inverse target carrier -/

/-- The target arc on the syntactic carrier of its target cell. -/
noncomputable def targetArcAtSome (Gamma : ContiguityGeometry D eps Delta faces)
    (target : Fin Delta.rCellCount) (htarget : Gamma.target = some target) :
    CyclicArc (targetDarts Delta (some target)) :=
  cast (congrArg CyclicArc (congrArg (targetDarts Delta) htarget)) Gamma.targetArc

/-- The inverse relator rotation whose prefix is the oppositely oriented target
boundary arc. -/
noncomputable def targetInverseCarrier (Gamma : ContiguityGeometry D eps Delta faces)
    (target : Fin Delta.rCellCount) (htarget : Gamma.target = some target) :
    List (GGT.RelLetter G Lambda) :=
  (RelWord.revInv (dartWord Delta
      (Gamma.targetArcAtSome target htarget).rotated)).rotate
    (dartWord Delta
      ((Gamma.targetArcAtSome target htarget).rotated.drop
        (Gamma.targetArcAtSome target htarget).length)).length

/-- The inverse carrier belongs to the symmetrized family. -/
theorem targetInverseCarrier_mem (Gamma : ContiguityGeometry D eps Delta faces)
    (target : Fin Delta.rCellCount) (htarget : Gamma.target = some target)
    {rho : ℕ} {mu : ℝ} (hsc : RelWord.IsSmallCancellation D W eps mu rho) :
    Gamma.targetInverseCarrier target htarget ∈ W := by
  have hcarrier := (Gamma.targetArcAtSome target htarget).cell_rotated_mem hsc
  have hinv := hsc.inv_mem _ hcarrier
  unfold ContiguityGeometry.targetInverseCarrier
  exact hsc.rotate_mem _ hinv _

/-- The inverse carrier has the oppositely oriented target boundary as a
prefix. -/
theorem exists_targetInverseCarrier_suffix
    (Gamma : ContiguityGeometry D eps Delta faces)
    (target : Fin Delta.rCellCount) (htarget : Gamma.target = some target) :
    ∃ suffix : List (GGT.RelLetter G Lambda),
      Gamma.targetInverseCarrier target htarget =
        dartWord Delta (targetBoundaryDarts Delta Gamma.target Gamma.targetArc) ++
          suffix := by
  obtain ⟨suffix, hsuffix⟩ := CyclicArc.exists_reverseDarts_prefix_of_rotated_revInv
    Delta (Gamma.targetArcAtSome target htarget)
  refine ⟨suffix, ?_⟩
  have hboundary :
      targetBoundaryDarts Delta Gamma.target Gamma.targetArc =
        targetBoundaryDarts Delta (some target)
          (Gamma.targetArcAtSome target htarget) :=
    targetBoundaryDarts_cast htarget Gamma.targetArc
  rw [hboundary]
  simpa [ContiguityGeometry.targetInverseCarrier, targetBoundaryDarts,
    CyclicArc.reversePrefixTarget, CyclicArc.reverseDartsWord] using hsuffix

/-- The target boundary darts have the stored target arc length. -/
theorem targetBoundaryDarts_length (Gamma : ContiguityGeometry D eps Delta faces) :
    (targetBoundaryDarts Delta Gamma.target Gamma.targetArc).length =
      Gamma.targetArc.length := by
  let motive : ∀ target : Option (Fin Delta.rCellCount),
      ∀ arc : CyclicArc (targetDarts Delta target),
        (targetBoundaryDarts Delta target arc).length = arc.length := by
    intro target
    cases target with
    | none => intro arc; exact arc.darts_length
    | some i =>
        intro arc
        simp only [targetBoundaryDarts, CyclicArc.reverseDarts,
          List.length_map, List.length_reverse, CyclicArc.darts_length]
  exact motive Gamma.target Gamma.targetArc

/-! ## O52 for an actual region -/

/-- **The two O52 equations of an actual cell-to-cell region.**  The arc
equation is the region's own (`arcs_value`); the non-cancellation clause is the
one input. -/
structure PieceEquations (Gamma : ContiguityGeometry D eps Delta faces) where
  target : Fin Delta.rCellCount
  target_eq : Gamma.target = some target
  whole_ne : GGT.RelLetter.listVal (Gamma.targetInverseCarrier target target_eq) ≠
    (GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide))⁻¹ *
      GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.rotated) *
      GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide)

/-- The equation in the orientation used by the published piece. -/
theorem targetBoundary_value (Gamma : ContiguityGeometry D eps Delta faces) :
    GGT.RelLetter.listVal
        (dartWord Delta (targetBoundaryDarts Delta Gamma.target Gamma.targetArc)) =
      (GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide))⁻¹ *
        GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.darts) *
        (GGT.RelLetter.listVal (dartWord Delta Gamma.leftSide))⁻¹ := by
  have hsource := Gamma.arcs_value
  rw [hsource]
  group

/-- **The published piece of an actual region.** -/
theorem isPublishedPiece_of_equations
    (Gamma : ContiguityGeometry D eps Delta faces)
    (equations : Gamma.PieceEquations)
    {rho : ℕ} {mu : ℝ} (hsc : RelWord.IsSmallCancellation D W eps mu rho) :
    RelWord.IsPublishedPiece D W eps
      (dartWord Delta Gamma.sourceArc.darts)
      (dartWord Delta (targetBoundaryDarts Delta Gamma.target Gamma.targetArc))
      (dartWord Delta Gamma.sourceArc.rotated) := by
  obtain ⟨sourceSuffix, hsource⟩ := Gamma.sourceArc.exists_dartWord_suffix
  obtain ⟨targetSuffix, htarget⟩ :=
    Gamma.exists_targetInverseCarrier_suffix equations.target equations.target_eq
  have hsourceMem := Gamma.sourceArc.cell_rotated_mem hsc
  have htargetMem := Gamma.targetInverseCarrier_mem equations.target
    equations.target_eq hsc
  have hleft : wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal (dartWord Delta Gamma.leftSide))⁻¹ ≤ eps := by
    rw [wordNorm_inv D.alphabet.symmetricGenerating]
    exact Gamma.leftSide_norm_le
  have hright : wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide))⁻¹ ≤ eps := by
    rw [wordNorm_inv D.alphabet.symmetricGenerating]
    exact Gamma.rightSide_norm_le
  exact ⟨hsourceMem, ⟨sourceSuffix, hsource⟩,
    Gamma.targetInverseCarrier equations.target equations.target_eq,
    htargetMem, targetSuffix, htarget,
    (GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide))⁻¹,
    (GGT.RelLetter.listVal (dartWord Delta Gamma.leftSide))⁻¹,
    hright, hleft, Gamma.targetBoundary_value,
    (by simpa only [inv_inv] using equations.whole_ne)⟩

/-- The source arc's carrier word has the source perimeter as its length. -/
theorem sourceArc_rotated_length_eq (Gamma : ContiguityGeometry D eps Delta faces) :
    (dartWord Delta Gamma.sourceArc.rotated).length =
      (cell Delta Gamma.source).word.length := by
  simp only [dartWord, List.length_map, Gamma.sourceArc.rotated_length]
  have hlength := congrArg List.length (dartWord_cellDarts Delta Gamma.source)
  simpa only [dartWord, List.length_map, targetDarts] using hlength

/-- **O52 at the source cell, per arc**: `l(q_1) < μ l(∂Π)`. -/
theorem sourceArc_length_lt_mu (Gamma : ContiguityGeometry D eps Delta faces)
    (equations : Gamma.PieceEquations)
    {rho : ℕ} {mu : ℝ} (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    (hpieces : ∀ first second word,
      RelWord.IsPublishedPiece D W eps first second word →
        max (first.length : ℝ) (second.length : ℝ) < mu * word.length) :
    (Gamma.sourceArc.length : ℝ) <
      mu * ((cell Delta Gamma.source).word.length : ℝ) := by
  have hpublished := Gamma.isPublishedPiece_of_equations equations hsc
  have hbound := hpieces
    (dartWord Delta Gamma.sourceArc.darts)
    (dartWord Delta (targetBoundaryDarts Delta Gamma.target Gamma.targetArc))
    (dartWord Delta Gamma.sourceArc.rotated) hpublished
  have hsource : (Gamma.sourceArc.length : ℝ) <
      mu * (dartWord Delta Gamma.sourceArc.rotated).length := by
    simpa only [dartWord, List.length_map, Gamma.sourceArc.darts_length] using
      lt_of_le_of_lt (le_max_left _ _) hbound
  rw [Gamma.sourceArc_rotated_length_eq] at hsource
  exact hsource

/-- **O52 charge at the source cell**: both arcs of the region are charged to its
source perimeter. -/
theorem arcLengths_le_two_mu_source (Gamma : ContiguityGeometry D eps Delta faces)
    (equations : Gamma.PieceEquations)
    {rho : ℕ} {mu : ℝ} (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    (hpieces : ∀ first second word,
      RelWord.IsPublishedPiece D W eps first second word →
        max (first.length : ℝ) (second.length : ℝ) < mu * word.length) :
    (Gamma.sourceArc.length : ℝ) + (Gamma.targetArc.length : ℝ) ≤
      2 * mu * ((cell Delta Gamma.source).word.length : ℝ) := by
  have hpublished := Gamma.isPublishedPiece_of_equations equations hsc
  have hbound := hpieces
    (dartWord Delta Gamma.sourceArc.darts)
    (dartWord Delta (targetBoundaryDarts Delta Gamma.target Gamma.targetArc))
    (dartWord Delta Gamma.sourceArc.rotated) hpublished
  have hsource : (Gamma.sourceArc.length : ℝ) <
      mu * (dartWord Delta Gamma.sourceArc.rotated).length := by
    simpa only [dartWord, List.length_map, Gamma.sourceArc.darts_length] using
      lt_of_le_of_lt (le_max_left _ _) hbound
  have htarget : (Gamma.targetArc.length : ℝ) <
      mu * (dartWord Delta Gamma.sourceArc.rotated).length := by
    have htarget' := lt_of_le_of_lt (le_max_right _ _) hbound
    have hlenBoundary :
        (dartWord Delta (targetBoundaryDarts Delta Gamma.target Gamma.targetArc)).length =
          Gamma.targetArc.length := by
      simp only [dartWord, List.length_map]
      exact Gamma.targetBoundaryDarts_length
    rw [hlenBoundary] at htarget'
    exact htarget'
  rw [Gamma.sourceArc_rotated_length_eq] at hsource htarget
  linarith

/-- **O52 charge at the target cell**: invert both connectors and reverse the
arc equation and the non-cancellation clause. -/
theorem arcLengths_le_two_mu_target (Gamma : ContiguityGeometry D eps Delta faces)
    (equations : Gamma.PieceEquations)
    {rho : ℕ} {mu : ℝ} (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    (hpieces : ∀ first second word,
      RelWord.IsPublishedPiece D W eps first second word →
        max (first.length : ℝ) (second.length : ℝ) < mu * word.length) :
    (Gamma.sourceArc.length : ℝ) + (Gamma.targetArc.length : ℝ) ≤
      2 * mu * ((cell Delta equations.target).word.length : ℝ) := by
  have hpublished : RelWord.IsPublishedPiece D W eps
      (dartWord Delta (targetBoundaryDarts Delta Gamma.target Gamma.targetArc))
      (dartWord Delta Gamma.sourceArc.darts)
      (Gamma.targetInverseCarrier equations.target equations.target_eq) := by
    obtain ⟨sourceSuffix, hsource⟩ := Gamma.sourceArc.exists_dartWord_suffix
    obtain ⟨targetSuffix, htarget⟩ :=
      Gamma.exists_targetInverseCarrier_suffix equations.target equations.target_eq
    have hsourceMem := Gamma.sourceArc.cell_rotated_mem hsc
    have htargetMem := Gamma.targetInverseCarrier_mem equations.target
      equations.target_eq hsc
    have harcs : GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.darts) =
        GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide) *
          GGT.RelLetter.listVal
            (dartWord Delta (targetBoundaryDarts Delta Gamma.target Gamma.targetArc)) *
          GGT.RelLetter.listVal (dartWord Delta Gamma.leftSide) :=
      Gamma.arcs_value
    have hwhole : GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.rotated) ≠
        GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide) *
          GGT.RelLetter.listVal
            (Gamma.targetInverseCarrier equations.target equations.target_eq) *
          (GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide))⁻¹ := by
      intro hsame
      apply equations.whole_ne
      rw [hsame]
      group
    exact ⟨htargetMem, ⟨targetSuffix, htarget⟩,
      dartWord Delta Gamma.sourceArc.rotated, hsourceMem, sourceSuffix,
      hsource, GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide),
      GGT.RelLetter.listVal (dartWord Delta Gamma.leftSide),
      Gamma.rightSide_norm_le, Gamma.leftSide_norm_le, harcs, hwhole⟩
  have hbound := hpieces
    (dartWord Delta (targetBoundaryDarts Delta Gamma.target Gamma.targetArc))
    (dartWord Delta Gamma.sourceArc.darts)
    (Gamma.targetInverseCarrier equations.target equations.target_eq) hpublished
  have htarget : (Gamma.targetArc.length : ℝ) <
      mu * (Gamma.targetInverseCarrier equations.target equations.target_eq).length := by
    have htarget' := lt_of_le_of_lt (le_max_left _ _) hbound
    have hlenBoundary :
        (dartWord Delta (targetBoundaryDarts Delta Gamma.target Gamma.targetArc)).length =
          Gamma.targetArc.length := by
      simp only [dartWord, List.length_map]
      exact Gamma.targetBoundaryDarts_length
    rw [hlenBoundary] at htarget'
    exact htarget'
  have hsource : (Gamma.sourceArc.length : ℝ) <
      mu * (Gamma.targetInverseCarrier equations.target equations.target_eq).length := by
    simpa only [dartWord, List.length_map, Gamma.sourceArc.darts_length] using
      lt_of_le_of_lt (le_max_right _ _) hbound
  have hcarrier :
      (Gamma.targetInverseCarrier equations.target equations.target_eq).length =
        (cell Delta equations.target).word.length := by
    unfold ContiguityGeometry.targetInverseCarrier
    simp only [List.length_rotate, RelWord.length_revInv, dartWord,
      List.length_map, CyclicArc.rotated_length]
    have hlength := congrArg List.length
      (dartWord_cellDarts Delta equations.target)
    have htargetDarts : targetDarts Delta (some equations.target) =
        cellDarts Delta equations.target := by rfl
    rw [htargetDarts]
    simpa only [dartWord, List.length_map] using hlength
  rw [hcarrier] at hsource htarget
  linarith

end ContiguityGeometry

/-! ## The contiguity degree of a region, and the least-area producer -/

/-- **O52 as a degree bound**: a cell-to-cell region with its equations has
contiguity degree below `μ`. -/
theorem RegionCandidate.contiguityDegree_lt_mu (a : RegionCandidate D eps Delta)
    (equations : a.2.PieceEquations)
    {rho : ℕ} {mu : ℝ} (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    (hpieces : ∀ first second word,
      RelWord.IsPublishedPiece D W eps first second word →
        max (first.length : ℝ) (second.length : ℝ) < mu * word.length)
    (hlen : 0 < ((cell Delta a.2.source).word.length : ℝ)) :
    a.contiguityDegree < mu := by
  have h := a.2.sourceArc_length_lt_mu equations hsc hpieces
  unfold RegionCandidate.contiguityDegree
  rw [div_lt_iff₀ hlen]
  exact h

/-- **Osin's O52 non-cancellation at least area.**  (Owner: lane `hull-select`.)
In a least-area diagram, a contiguity region of one relator cell to ANOTHER
relator cell satisfies the non-cancellation clause.  Osin: if it fails, "we can
cut the subdiagram … and fill the obtained hole with a diagram without
`R`-cells, reducing the number of `R`-cells by 2", which contradicts least area.
The self-contiguous case is excluded, as in the source. -/
def O52LeastAreaStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} {faces : Finset Delta.toCombMap.Face}
    (Gamma : ContiguityGeometry D eps Delta faces) (target : Fin Delta.rCellCount)
    (htarget : Gamma.target = some target),
    Delta.LeastArea → Gamma.source ≠ target →
      GGT.RelLetter.listVal (Gamma.targetInverseCarrier target htarget) ≠
        (GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide))⁻¹ *
          GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.rotated) *
          GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide)

end GroupApproximation.GGT.VanKampen.Embedded

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.ContiguityGeometry.arcs_value
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.ContiguityGeometry.isPublishedPiece_of_equations
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.ContiguityGeometry.arcLengths_le_two_mu_source
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.ContiguityGeometry.arcLengths_le_two_mu_target
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.contiguityDegree_lt_mu
