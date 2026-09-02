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
    (Gamma : CellContiguity pre between suf source target) :
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
    (Gamma : CellContiguity pre between suf source target) :
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
    (Gamma : CellContiguity pre between suf source target) :
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
    (Gamma : CellContiguity pre between suf source target) :
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
    (Gamma : CellContiguity pre between suf source target) :
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
    (Gamma : CellContiguity pre between suf source target) :
    (Gamma.region.firstArc.length : ℝ) +
        (Gamma.region.secondArc.length : ℝ) ≤
      2 * mu * (source.word.length : ℝ) :=
  le_of_lt (Gamma.arcLengths_lt_two_mu_source hsc hred)

/-- A Lemma 4.9 input supplies the same O52 charge through its Lemma 4.4
projection. -/
theorem arcLengths_le_two_mu_source_of_lemma49
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram W} {eps rho : ℕ} {mu : ℝ}
    {pre between suf : List
      (RelatorCell Delta.toCombMap Delta.outerFace W)}
    {source target : RelatorCell Delta.toCombMap Delta.outerFace W}
    (hsc : RelWord.IsLemma49Input D W eps mu rho)
    (hred : Delta.Reduced)
    (Gamma : CellContiguity pre between suf source target) :
    (Gamma.region.firstArc.length : ℝ) +
        (Gamma.region.secondArc.length : ℝ) ≤
      2 * mu * (source.word.length : ℝ) :=
  Gamma.arcLengths_le_two_mu_source hsc.toIsLemma44Input hred

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
end Embedded

end VanKampen
end GGT
end GroupApproximation
