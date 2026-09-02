import GroupApproximation.GGT.VanKampen.Contiguity
import GroupApproximation.GGT.VanKampen.Estimating.Embedded
import GroupApproximation.GGT.VanKampen.RelativeGreendlinger

/-!
# Piece bounds for embedded contiguity arcs

This module proves the local charge estimate in Osin's Appendix, Lemma O52.
For a cell-to-cell contiguity region, diagram reducedness supplies the
non-cancellation clause in Hull's published piece relation.  Reversing the
two short connectors gives the published piece in the opposite direction,
so both arcs are shorter than `mu` times the perimeter of either incident
cell.  Their sum is then at most the `2 * mu` local charge used by
`EstimatingData.edgeWeight_le_incident`.

The second part identifies a positioned embedded cyclic arc with a prefix of
a rotation of its carrier word.  For the outer carrier this says that an
exterior contiguity arc is a cyclic subword of the diagram boundary word; no
piece estimate is used for that arc.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

open GroupApproximation.HullSC
open GroupApproximation.WordMetric

universe u w v

namespace CellContiguity

/-- Osin O52 with the two cells interchanged.  The inverse short connectors
give the reverse value equation, and the reducedness exclusion is invariant
under that reversal. -/
theorem isPublishedPiece_reverse
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram W} {eps rho : ℕ} {mu : ℝ}
    {pre between suf : List
      (RelatorCell Delta.toCombMap Delta.outerFace W)}
    {source target : RelatorCell Delta.toCombMap Delta.outerFace W}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    (hred : Delta.Reduced)
    (Gamma : CellContiguity (D := D) (eps := eps) pre between suf source target) :
    RelWord.IsPublishedPiece D W eps Gamma.region.secondArc
      Gamma.region.firstArc (RelWord.revInv target.word) := by
  have hleftInv : wordNorm D.alphabet.carrier
      Gamma.region.leftConnector⁻¹ ≤ eps := by
    rw [wordNorm_inv D.alphabet.symmetricGenerating]
    exact Gamma.region.leftConnector_short
  have hrightInv : wordNorm D.alphabet.carrier
      Gamma.region.rightConnector⁻¹ ≤ eps := by
    rw [wordNorm_inv D.alphabet.symmetricGenerating]
    exact Gamma.region.rightConnector_short
  have harcs : GGT.RelLetter.listVal Gamma.region.firstArc =
      Gamma.region.leftConnector⁻¹ *
        GGT.RelLetter.listVal Gamma.region.secondArc *
        Gamma.region.rightConnector⁻¹ := by
    rw [Gamma.region.arcs_value]
    group
  have hwhole : GGT.RelLetter.listVal source.word ≠
      Gamma.region.leftConnector⁻¹ *
        GGT.RelLetter.listVal (RelWord.revInv target.word) *
        (Gamma.region.leftConnector⁻¹)⁻¹ := by
    intro heq
    apply Gamma.whole_relators_ne hred
    rw [heq]
    group
  exact ⟨hsc.inv_mem target.word target.word_mem,
    ⟨Gamma.targetRemainder, Gamma.target_decomposition⟩,
    source.word, source.word_mem, Gamma.sourceRemainder,
    Gamma.source_decomposition, Gamma.region.leftConnector⁻¹,
    Gamma.region.rightConnector⁻¹, hleftInv, hrightInv, harcs, hwhole⟩

/-- The published-piece output gives precisely the ordinary distinct-word
piece or the same-word published branch.  The latter retains the nontrivial
connector exclusion supplied by diagram reducedness. -/
theorem isPiece_or_sameWord
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram W} {eps rho : ℕ} {mu : ℝ}
    {pre between suf : List
      (RelatorCell Delta.toCombMap Delta.outerFace W)}
    {source target : RelatorCell Delta.toCombMap Delta.outerFace W}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    (hred : Delta.Reduced)
    (Gamma : CellContiguity (D := D) (eps := eps) pre between suf source target) :
    RelWord.IsPiece D W eps Gamma.region.firstArc source.word ∨
      RelWord.IsSameWordPublishedPiece D W eps Gamma.region.firstArc
        Gamma.region.secondArc source.word := by
  exact (Gamma.isPublishedPiece hsc hred).toIsPiece_or_sameWord

/-- The target arc satisfies O52 with the target-cell perimeter.  This is the
opposite-direction form needed when an estimating edge is incident at its
target endpoint. -/
theorem targetArc_lt_mu_mul
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram W} {eps rho : ℕ} {mu : ℝ}
    {pre between suf : List
      (RelatorCell Delta.toCombMap Delta.outerFace W)}
    {source target : RelatorCell Delta.toCombMap Delta.outerFace W}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hred : Delta.Reduced)
    (Gamma : CellContiguity (D := D) (eps := eps) pre between suf source target) :
    (Gamma.region.secondArc.length : ℝ) <
      mu * (target.word.length : ℝ) := by
  have hpublished := Gamma.isPublishedPiece_reverse
    hsc.toIsSmallCancellation hred
  have hbound := hsc.publishedPiecesSmall Gamma.region.secondArc
    Gamma.region.firstArc (RelWord.revInv target.word) hpublished
  have hsecond : (Gamma.region.secondArc.length : ℝ) ≤
      max (Gamma.region.secondArc.length : ℝ)
        (Gamma.region.firstArc.length : ℝ) := le_max_left _ _
  rw [RelWord.length_revInv] at hbound
  exact lt_of_le_of_lt hsecond hbound

/-- Both cell arcs together are strictly below the `2 * mu` charge measured
at the source endpoint. -/
theorem arcLengths_lt_two_mu_source
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram W} {eps rho : ℕ} {mu : ℝ}
    {pre between suf : List
      (RelatorCell Delta.toCombMap Delta.outerFace W)}
    {source target : RelatorCell Delta.toCombMap Delta.outerFace W}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hred : Delta.Reduced)
    (Gamma : CellContiguity (D := D) (eps := eps) pre between suf source target) :
    (Gamma.region.firstArc.length : ℝ) +
        (Gamma.region.secondArc.length : ℝ) <
      2 * mu * (source.word.length : ℝ) := by
  have hpublished := Gamma.isPublishedPiece hsc.toIsSmallCancellation hred
  have hbound := hsc.publishedPiecesSmall Gamma.region.firstArc
    Gamma.region.secondArc source.word hpublished
  have hfirst : (Gamma.region.firstArc.length : ℝ) <
      mu * (source.word.length : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) hbound
  have hsecond : (Gamma.region.secondArc.length : ℝ) <
      mu * (source.word.length : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hbound
  linarith

/-- Both cell arcs together are strictly below the `2 * mu` charge measured
at the target endpoint. -/
theorem arcLengths_lt_two_mu_target
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram W} {eps rho : ℕ} {mu : ℝ}
    {pre between suf : List
      (RelatorCell Delta.toCombMap Delta.outerFace W)}
    {source target : RelatorCell Delta.toCombMap Delta.outerFace W}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hred : Delta.Reduced)
    (Gamma : CellContiguity (D := D) (eps := eps) pre between suf source target) :
    (Gamma.region.firstArc.length : ℝ) +
        (Gamma.region.secondArc.length : ℝ) <
      2 * mu * (target.word.length : ℝ) := by
  have hpublished := Gamma.isPublishedPiece_reverse
    hsc.toIsSmallCancellation hred
  have hbound := hsc.publishedPiecesSmall Gamma.region.secondArc
    Gamma.region.firstArc (RelWord.revInv target.word) hpublished
  have hfirst : (Gamma.region.firstArc.length : ℝ) <
      mu * (target.word.length : ℝ) := by
    have hle : (Gamma.region.firstArc.length : ℝ) ≤
        max (Gamma.region.secondArc.length : ℝ)
          (Gamma.region.firstArc.length : ℝ) := le_max_right _ _
    rw [RelWord.length_revInv] at hbound
    exact lt_of_le_of_lt hle hbound
  have hsecond : (Gamma.region.secondArc.length : ℝ) <
      mu * (target.word.length : ℝ) := Gamma.targetArc_lt_mu_mul hsc hred
  linarith

/-- The non-strict source-endpoint form has the exact numerical shape of
`EstimatingData.edgeWeight_le_incident`. -/
theorem arcLengths_le_two_mu_source
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram W} {eps rho : ℕ} {mu : ℝ}
    {pre between suf : List
      (RelatorCell Delta.toCombMap Delta.outerFace W)}
    {source target : RelatorCell Delta.toCombMap Delta.outerFace W}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hred : Delta.Reduced)
    (Gamma : CellContiguity (D := D) (eps := eps) pre between suf source target) :
    (Gamma.region.firstArc.length : ℝ) +
        (Gamma.region.secondArc.length : ℝ) ≤
      2 * mu * (source.word.length : ℝ) :=
  le_of_lt (Gamma.arcLengths_lt_two_mu_source hsc hred)

/-- The non-strict target-endpoint form has the other incidence of
`EstimatingData.edgeWeight_le_incident`. -/
theorem arcLengths_le_two_mu_target
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram W} {eps rho : ℕ} {mu : ℝ}
    {pre between suf : List
      (RelatorCell Delta.toCombMap Delta.outerFace W)}
    {source target : RelatorCell Delta.toCombMap Delta.outerFace W}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hred : Delta.Reduced)
    (Gamma : CellContiguity (D := D) (eps := eps) pre between suf source target) :
    (Gamma.region.firstArc.length : ℝ) +
        (Gamma.region.secondArc.length : ℝ) ≤
      2 * mu * (target.word.length : ℝ) :=
  le_of_lt (Gamma.arcLengths_lt_two_mu_target hsc hred)

end CellContiguity

namespace Embedded
namespace CyclicArc

/-- Reading a positioned rotation of a dart cycle is the corresponding
rotation of the carrier word. -/
theorem dartWord_rotated
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {cycle : List Delta.toCombMap.Dart} (arc : CyclicArc cycle) :
    dartWord Delta arc.rotated =
      (dartWord Delta cycle).rotate arc.start.1 := by
  have hstart : arc.start.1 ≤ cycle.length := by omega
  rw [List.rotate_eq_drop_append_take (by
    simpa only [dartWord, List.length_map] using hstart)]
  simp only [dartWord, rotated, List.map_append, List.map_drop, List.map_take]

/-- The arc word is a prefix of the word read from its positioned carrier
rotation. -/
theorem exists_dartWord_suffix
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {cycle : List Delta.toCombMap.Dart} (arc : CyclicArc cycle) :
    ∃ suffix : List (GGT.RelLetter G Lambda),
      dartWord Delta arc.rotated =
        dartWord Delta arc.darts ++ suffix := by
  refine ⟨dartWord Delta (arc.rotated.drop arc.length), ?_⟩
  rw [darts]
  conv_lhs => rw [← List.take_append_drop arc.length arc.rotated]
  simp only [dartWord, List.map_append, List.map_take, List.map_drop]

/-- The word of a positioned cell carrier belongs to the relator family when
the family is closed under cyclic shifts. -/
theorem cell_rotated_mem
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    {i : Fin Delta.rCellCount} (arc : CyclicArc (cellDarts Delta i)) :
    dartWord Delta arc.rotated ∈ W := by
  rw [arc.dartWord_rotated, dartWord_cellDarts Delta i]
  exact hsc.rotate_mem (cell Delta i).word (cell Delta i).word_mem arc.start.1

/-- A positioned cell arc and its remainder expose a prefix of a cyclic shift
of the cell relator. -/
theorem cell_prefix
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {i : Fin Delta.rCellCount} (arc : CyclicArc (cellDarts Delta i)) :
    ∃ suffix : List (GGT.RelLetter G Lambda),
      dartWord Delta arc.rotated = dartWord Delta arc.darts ++ suffix :=
  arc.exists_dartWord_suffix

/-- An exterior positioned arc is a prefix of a cyclic permutation of the
diagram boundary word.  This is the boundary-subword identification used in
the exterior perimeter sum. -/
theorem exists_boundary_suffix
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    (arc : CyclicArc (outerDarts Delta)) :
    ∃ suffix : List (GGT.RelLetter G Lambda),
      Delta.boundaryWord.rotate arc.start.1 =
        dartWord Delta arc.darts ++ suffix := by
  obtain ⟨suffix, hsuffix⟩ := arc.exists_dartWord_suffix
  refine ⟨suffix, ?_⟩
  rw [← dartWord_outerDarts Delta, ← arc.dartWord_rotated]
  exact hsuffix

/-- The exterior arc length is bounded by the full boundary perimeter. -/
theorem length_le_boundary
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    (arc : CyclicArc (outerDarts Delta)) :
    arc.length ≤ Delta.boundaryWord.length := by
  have houter := congrArg List.length (dartWord_outerDarts Delta)
  have hlength : (outerDarts Delta).length = Delta.boundaryWord.length := by
    simpa only [dartWord, List.length_map] using houter
  rw [← hlength]
  exact arc.length_le

end CyclicArc

/-- Two positioned cell arcs, the two relative-short connectors, and the
reducedness exclusion are exactly the data of Hull's published piece.  The
cyclic-shift memberships and both prefix decompositions are derived here. -/
theorem isPublishedPiece_of_cyclicCellArcs
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    {source target : Fin Delta.rCellCount}
    (sourceArc : CyclicArc (cellDarts Delta source))
    (targetArc : CyclicArc (cellDarts Delta target))
    {left right : G}
    (hleft : wordNorm D.alphabet.carrier left ≤ eps)
    (hright : wordNorm D.alphabet.carrier right ≤ eps)
    (harcs : GGT.RelLetter.listVal (dartWord Delta targetArc.darts) =
      left * GGT.RelLetter.listVal (dartWord Delta sourceArc.darts) * right)
    (hwhole : GGT.RelLetter.listVal (dartWord Delta targetArc.rotated) ≠
      left * GGT.RelLetter.listVal (dartWord Delta sourceArc.rotated) * left⁻¹) :
    RelWord.IsPublishedPiece D W eps (dartWord Delta sourceArc.darts)
      (dartWord Delta targetArc.darts) (dartWord Delta sourceArc.rotated) := by
  obtain ⟨sourceSuffix, hsource⟩ := sourceArc.cell_prefix
  obtain ⟨targetSuffix, htarget⟩ := targetArc.cell_prefix
  exact ⟨sourceArc.cell_rotated_mem hsc, ⟨sourceSuffix, hsource⟩,
    dartWord Delta targetArc.rotated, targetArc.cell_rotated_mem hsc,
    targetSuffix, htarget, left, right, hleft, hright, harcs, hwhole⟩

/-- Both positioned cell arcs satisfy the local `2 * mu` charge at the
source carrier directly from the published `C₁` maximum bound. -/
theorem cyclicArcLengths_le_two_mu_cellWeight
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    {source target : Fin Delta.rCellCount}
    (sourceArc : CyclicArc (cellDarts Delta source))
    (targetArc : CyclicArc (cellDarts Delta target))
    {left right : G}
    (hleft : wordNorm D.alphabet.carrier left ≤ eps)
    (hright : wordNorm D.alphabet.carrier right ≤ eps)
    (harcs : GGT.RelLetter.listVal (dartWord Delta targetArc.darts) =
      left * GGT.RelLetter.listVal (dartWord Delta sourceArc.darts) * right)
    (hwhole : GGT.RelLetter.listVal (dartWord Delta targetArc.rotated) ≠
      left * GGT.RelLetter.listVal (dartWord Delta sourceArc.rotated) * left⁻¹) :
    (sourceArc.length : ℝ) + (targetArc.length : ℝ) ≤
      2 * mu * Delta.cellWeight source := by
  have hpublished := isPublishedPiece_of_cyclicCellArcs
    hsc.toIsSmallCancellation sourceArc targetArc hleft hright harcs hwhole
  have hbound := hsc.publishedPiecesSmall (dartWord Delta sourceArc.darts)
    (dartWord Delta targetArc.darts) (dartWord Delta sourceArc.rotated)
    hpublished
  have hsource : (sourceArc.length : ℝ) <
      mu * (dartWord Delta sourceArc.rotated).length := by
    simpa only [dartWord, List.length_map, sourceArc.darts_length] using
      lt_of_le_of_lt (le_max_left _ _) hbound
  have htarget : (targetArc.length : ℝ) <
      mu * (dartWord Delta sourceArc.rotated).length := by
    simpa only [dartWord, List.length_map, targetArc.darts_length] using
      lt_of_le_of_lt (le_max_right _ _) hbound
  have hcellLength := congrArg List.length (dartWord_cellDarts Delta source)
  have hcarrier : (dartWord Delta sourceArc.rotated).length =
      (cell Delta source).word.length := by
    simp only [dartWord, List.length_map, sourceArc.rotated_length]
    simpa only [dartWord, List.length_map] using hcellLength
  rw [hcarrier] at hsource htarget
  have hsum : (sourceArc.length : ℝ) + (targetArc.length : ℝ) <
      2 * mu * ((cell Delta source).word.length : ℝ) := by
    linarith
  exact le_of_lt hsum

namespace Contiguity

/-- When an embedded region has a relator-cell target, transport its target
arc to that cell's cyclic carrier. -/
def cellTargetArc
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps : ℕ}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces) (target : Fin Delta.rCellCount)
    (htarget : Gamma.target = some target) :
    CyclicArc (cellDarts Delta target) := by
  change CyclicArc (targetDarts Delta (some target))
  rw [← htarget]
  exact Gamma.targetArc

/-- An embedded cell-to-cell region's positioned arcs and its two
relative-short sides give exactly Hull's published piece data.  The two
remaining equations are respectively the G-cell boundary value equation and
the non-cancellation conclusion supplied by diagram reducedness. -/
theorem isPublishedPiece_of_cellTarget
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps rho : ℕ} {mu : ℝ}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces) (target : Fin Delta.rCellCount)
    (htarget : Gamma.target = some target)
    (harcs : GGT.RelLetter.listVal
        (dartWord Delta (Gamma.cellTargetArc target htarget).darts) =
      GGT.RelLetter.listVal (dartWord Delta Gamma.leftSide) *
        GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.darts) *
        GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide))
    (hwhole : GGT.RelLetter.listVal
        (dartWord Delta (Gamma.cellTargetArc target htarget).rotated) ≠
      GGT.RelLetter.listVal (dartWord Delta Gamma.leftSide) *
        GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.rotated) *
        (GGT.RelLetter.listVal (dartWord Delta Gamma.leftSide))⁻¹)
    (hsc : RelWord.IsSmallCancellation D W eps mu rho) :
    RelWord.IsPublishedPiece D W eps
      (dartWord Delta Gamma.sourceArc.darts)
      (dartWord Delta (Gamma.cellTargetArc target htarget).darts)
      (dartWord Delta Gamma.sourceArc.rotated) := by
  exact isPublishedPiece_of_cyclicCellArcs hsc Gamma.sourceArc
    (Gamma.cellTargetArc target htarget) Gamma.leftSide_norm_le
    Gamma.rightSide_norm_le harcs hwhole

/-- The distinct-cell and same-word/nontrivial-connector branches of the
embedded published piece. -/
theorem isPiece_or_sameWord_of_cellTarget
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps rho : ℕ} {mu : ℝ}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces) (target : Fin Delta.rCellCount)
    (htarget : Gamma.target = some target)
    (harcs : GGT.RelLetter.listVal
        (dartWord Delta (Gamma.cellTargetArc target htarget).darts) =
      GGT.RelLetter.listVal (dartWord Delta Gamma.leftSide) *
        GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.darts) *
        GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide))
    (hwhole : GGT.RelLetter.listVal
        (dartWord Delta (Gamma.cellTargetArc target htarget).rotated) ≠
      GGT.RelLetter.listVal (dartWord Delta Gamma.leftSide) *
        GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.rotated) *
        (GGT.RelLetter.listVal (dartWord Delta Gamma.leftSide))⁻¹)
    (hsc : RelWord.IsSmallCancellation D W eps mu rho) :
    RelWord.IsPiece D W eps (dartWord Delta Gamma.sourceArc.darts)
        (dartWord Delta Gamma.sourceArc.rotated) ∨
      RelWord.IsSameWordPublishedPiece D W eps
        (dartWord Delta Gamma.sourceArc.darts)
        (dartWord Delta (Gamma.cellTargetArc target htarget).darts)
        (dartWord Delta Gamma.sourceArc.rotated) := by
  have hpublished :=
    Gamma.isPublishedPiece_of_cellTarget target htarget harcs hwhole hsc
  exact hpublished.toIsPiece_or_sameWord

/-- The embedded cell-target interface gives the source-incidence O52 charge
in the exact `2 * mu * cellWeight` form. -/
theorem arcLengths_le_two_mu_cellWeight_of_cellTarget
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps rho : ℕ} {mu : ℝ}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces) (target : Fin Delta.rCellCount)
    (htarget : Gamma.target = some target)
    (harcs : GGT.RelLetter.listVal
        (dartWord Delta (Gamma.cellTargetArc target htarget).darts) =
      GGT.RelLetter.listVal (dartWord Delta Gamma.leftSide) *
        GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.darts) *
        GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide))
    (hwhole : GGT.RelLetter.listVal
        (dartWord Delta (Gamma.cellTargetArc target htarget).rotated) ≠
      GGT.RelLetter.listVal (dartWord Delta Gamma.leftSide) *
        GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.rotated) *
        (GGT.RelLetter.listVal (dartWord Delta Gamma.leftSide))⁻¹)
    (hsc : RelWord.IsLemma44Input D W eps mu rho) :
    (Gamma.sourceArc.length : ℝ) +
        ((Gamma.cellTargetArc target htarget).length : ℝ) ≤
      2 * mu * Delta.cellWeight Gamma.source := by
  exact cyclicArcLengths_le_two_mu_cellWeight hsc Gamma.sourceArc
    (Gamma.cellTargetArc target htarget) Gamma.leftSide_norm_le
    Gamma.rightSide_norm_le harcs hwhole

/-- When an embedded region has outer target, transport its target arc to the
oriented boundary carrier. -/
def exteriorArc
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps : ℕ}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces) (htarget : Gamma.target = none) :
    CyclicArc (outerDarts Delta) := by
  change CyclicArc (targetDarts Delta none)
  rw [← htarget]
  exact Gamma.targetArc

/-- An embedded exterior contiguity arc is a prefix of a cyclic shift of the
diagram boundary word.  This is the identification used by the exterior
perimeter sum, with no piece hypothesis. -/
theorem exists_exteriorArc_boundary_suffix
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps : ℕ}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces) (htarget : Gamma.target = none) :
    ∃ suffix : List (GGT.RelLetter G Lambda),
      Delta.boundaryWord.rotate (Gamma.exteriorArc htarget).start.1 =
        dartWord Delta (Gamma.exteriorArc htarget).darts ++ suffix :=
  (Gamma.exteriorArc htarget).exists_boundary_suffix

/-- The embedded exterior arc has length at most the outer perimeter. -/
theorem exteriorArc_length_le_boundary
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps : ℕ}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces) (htarget : Gamma.target = none) :
    (Gamma.exteriorArc htarget).length ≤ Delta.boundaryWord.length :=
  (Gamma.exteriorArc htarget).length_le_boundary

end Contiguity

namespace Contiguity

/-- Transfer the stable `CellContiguity` O52 charge to the two positioned arcs
of an embedded region at its source incidence.  The equalities are the
geometric identification supplied when the embedded face set is converted to
the relator-free four-sided region. -/
theorem arcLengths_le_two_mu_cellWeight_source_of_cellContiguity
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps rho : ℕ} {mu : ℝ}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
    {pre between suf : List
      (RelatorCell Delta.toCombMap Delta.outerFace W)}
    {sourceCell targetCell : RelatorCell Delta.toCombMap Delta.outerFace W}
    (cellGamma : CellContiguity (D := D) (eps := eps) pre between suf sourceCell targetCell)
    (hsource : sourceCell = cell Delta Gamma.source)
    (hsourceArc : Gamma.sourceArc.length = cellGamma.region.firstArc.length)
    (htargetArc : Gamma.targetArc.length = cellGamma.region.secondArc.length)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hred : Delta.Reduced) :
    (Gamma.sourceArc.length : ℝ) + (Gamma.targetArc.length : ℝ) ≤
      2 * mu * Delta.cellWeight Gamma.source := by
  calc
    (Gamma.sourceArc.length : ℝ) + (Gamma.targetArc.length : ℝ) =
        (cellGamma.region.firstArc.length : ℝ) +
          (cellGamma.region.secondArc.length : ℝ) := by
      rw [hsourceArc, htargetArc]
    _ ≤ 2 * mu * (sourceCell.word.length : ℝ) :=
      cellGamma.arcLengths_le_two_mu_source hsc hred
    _ = 2 * mu * Delta.cellWeight Gamma.source := by
      rw [hsource]
      rfl

/-- The source-incidence estimate with the arc sum cast from `Nat`, matching
the representation used by `Embedded.Candidate.weight`. -/
theorem arcWeight_le_two_mu_cellWeight_source_of_cellContiguity
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps rho : ℕ} {mu : ℝ}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
    {pre between suf : List
      (RelatorCell Delta.toCombMap Delta.outerFace W)}
    {sourceCell targetCell : RelatorCell Delta.toCombMap Delta.outerFace W}
    (cellGamma : CellContiguity (D := D) (eps := eps) pre between suf sourceCell targetCell)
    (hsource : sourceCell = cell Delta Gamma.source)
    (hsourceArc : Gamma.sourceArc.length = cellGamma.region.firstArc.length)
    (htargetArc : Gamma.targetArc.length = cellGamma.region.secondArc.length)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hred : Delta.Reduced) :
    ((Gamma.sourceArc.length + Gamma.targetArc.length : ℕ) : ℝ) ≤
      2 * mu * Delta.cellWeight Gamma.source := by
  simpa only [Nat.cast_add] using
    Gamma.arcLengths_le_two_mu_cellWeight_source_of_cellContiguity
      cellGamma hsource hsourceArc htargetArc hsc hred

/-- The corresponding transfer at the target incidence has exactly the same
`2 * mu * cellWeight` conclusion. -/
theorem arcLengths_le_two_mu_cellWeight_target_of_cellContiguity
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps rho : ℕ} {mu : ℝ}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces) (target : Fin Delta.rCellCount)
    {pre between suf : List
      (RelatorCell Delta.toCombMap Delta.outerFace W)}
    {sourceCell targetCell : RelatorCell Delta.toCombMap Delta.outerFace W}
    (cellGamma : CellContiguity (D := D) (eps := eps) pre between suf sourceCell targetCell)
    (htarget : targetCell = cell Delta target)
    (hsourceArc : Gamma.sourceArc.length = cellGamma.region.firstArc.length)
    (htargetArc : Gamma.targetArc.length = cellGamma.region.secondArc.length)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hred : Delta.Reduced) :
    (Gamma.sourceArc.length : ℝ) + (Gamma.targetArc.length : ℝ) ≤
      2 * mu * Delta.cellWeight target := by
  calc
    (Gamma.sourceArc.length : ℝ) + (Gamma.targetArc.length : ℝ) =
        (cellGamma.region.firstArc.length : ℝ) +
          (cellGamma.region.secondArc.length : ℝ) := by
      rw [hsourceArc, htargetArc]
    _ ≤ 2 * mu * (targetCell.word.length : ℝ) :=
      cellGamma.arcLengths_le_two_mu_target hsc hred
    _ = 2 * mu * Delta.cellWeight target := by
      rw [htarget]
      rfl

/-- The target-incidence estimate with the arc sum cast from `Nat`, matching
the representation used by `Embedded.Candidate.weight`. -/
theorem arcWeight_le_two_mu_cellWeight_target_of_cellContiguity
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps rho : ℕ} {mu : ℝ}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces) (target : Fin Delta.rCellCount)
    {pre between suf : List
      (RelatorCell Delta.toCombMap Delta.outerFace W)}
    {sourceCell targetCell : RelatorCell Delta.toCombMap Delta.outerFace W}
    (cellGamma : CellContiguity (D := D) (eps := eps) pre between suf sourceCell targetCell)
    (htarget : targetCell = cell Delta target)
    (hsourceArc : Gamma.sourceArc.length = cellGamma.region.firstArc.length)
    (htargetArc : Gamma.targetArc.length = cellGamma.region.secondArc.length)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hred : Delta.Reduced) :
    ((Gamma.sourceArc.length + Gamma.targetArc.length : ℕ) : ℝ) ≤
      2 * mu * Delta.cellWeight target := by
  simpa only [Nat.cast_add] using
    Gamma.arcLengths_le_two_mu_cellWeight_target_of_cellContiguity target
      cellGamma htarget hsourceArc htargetArc hsc hred

end Contiguity

namespace Candidate

/-- A certified O52 region fills the source endpoint of
`EstimatingData.edgeWeight_le_incident` with `Candidate.weight`. -/
theorem weight_le_two_mu_cellWeight_source_of_cellContiguity
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps rho : ℕ} {mu : ℝ}
    (candidate : Candidate D eps Delta)
    {pre between suf : List
      (RelatorCell Delta.toCombMap Delta.outerFace W)}
    {sourceCell targetCell : RelatorCell Delta.toCombMap Delta.outerFace W}
    (cellGamma : CellContiguity (D := D) (eps := eps) pre between suf sourceCell targetCell)
    (hsource : sourceCell = cell Delta candidate.contiguity.source)
    (hsourceArc : candidate.contiguity.sourceArc.length =
      cellGamma.region.firstArc.length)
    (htargetArc : candidate.contiguity.targetArc.length =
      cellGamma.region.secondArc.length)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hred : Delta.Reduced) :
    (candidate.weight : ℝ) ≤
      2 * mu * Delta.cellWeight candidate.contiguity.source := by
  change ((candidate.contiguity.sourceArc.length +
    candidate.contiguity.targetArc.length : ℕ) : ℝ) ≤ _
  exact candidate.contiguity.arcWeight_le_two_mu_cellWeight_source_of_cellContiguity
    cellGamma hsource hsourceArc htargetArc hsc hred

/-- A certified O52 region fills the target endpoint of
`EstimatingData.edgeWeight_le_incident` with `Candidate.weight`. -/
theorem weight_le_two_mu_cellWeight_target_of_cellContiguity
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps rho : ℕ} {mu : ℝ}
    (candidate : Candidate D eps Delta) (target : Fin Delta.rCellCount)
    {pre between suf : List
      (RelatorCell Delta.toCombMap Delta.outerFace W)}
    {sourceCell targetCell : RelatorCell Delta.toCombMap Delta.outerFace W}
    (cellGamma : CellContiguity (D := D) (eps := eps) pre between suf sourceCell targetCell)
    (htarget : targetCell = cell Delta target)
    (hsourceArc : candidate.contiguity.sourceArc.length =
      cellGamma.region.firstArc.length)
    (htargetArc : candidate.contiguity.targetArc.length =
      cellGamma.region.secondArc.length)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hred : Delta.Reduced) :
    (candidate.weight : ℝ) ≤ 2 * mu * Delta.cellWeight target := by
  change ((candidate.contiguity.sourceArc.length +
    candidate.contiguity.targetArc.length : ℕ) : ℝ) ≤ _
  exact candidate.contiguity.arcWeight_le_two_mu_cellWeight_target_of_cellContiguity
    target cellGamma htarget hsourceArc htargetArc hsc hred

end Candidate
end Embedded

end VanKampen
end GGT
end GroupApproximation
