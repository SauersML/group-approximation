import GroupApproximation.GGT.VanKampen.RelativeGreendlinger

/-!
# O52 piece bounds for embedded contiguity arcs

This module transfers Osin Lemma O52 directly to embedded face-set regions.
A cyclic cell arc is a prefix of the corresponding rotation of the relator.
The G-cell boundary equation and diagram reducedness exclusion then give the
published piece, and the published maximum bound controls both incident arc
lengths by `2 * mu` times either cell perimeter.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

open GroupApproximation.HullSC
open GroupApproximation.WordMetric

universe u w v

namespace Embedded
namespace CyclicArc

/-- Reading a positioned rotation of a dart cycle is the corresponding
rotation of its word. -/
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

/-- A positioned arc word is a prefix of the rotated carrier word. -/
theorem exists_dartWord_suffix
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {cycle : List Delta.toCombMap.Dart} (arc : CyclicArc cycle) :
    ∃ suffix : List (GGT.RelLetter G Lambda),
      dartWord Delta arc.rotated = dartWord Delta arc.darts ++ suffix := by
  refine ⟨dartWord Delta (arc.rotated.drop arc.length), ?_⟩
  rw [darts]
  conv_lhs => rw [← List.take_append_drop arc.length arc.rotated]
  simp only [dartWord, List.map_append, List.map_take, List.map_drop]

/-- The rotated carrier of a cell arc remains in a symmetrized family. -/
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

end CyclicArc

/-- Two cyclic cell arcs with the G-cell boundary equation and reducedness
exclusion form an epsilon-published piece. -/
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
  obtain ⟨sourceSuffix, hsource⟩ := sourceArc.exists_dartWord_suffix
  obtain ⟨targetSuffix, htarget⟩ := targetArc.exists_dartWord_suffix
  exact ⟨sourceArc.cell_rotated_mem hsc, ⟨sourceSuffix, hsource⟩,
    dartWord Delta targetArc.rotated, targetArc.cell_rotated_mem hsc,
    targetSuffix, htarget, left, right, hleft, hright, harcs, hwhole⟩

/-- The exact Osin condition bounds both arc lengths at the source cell. -/
theorem cyclicArcLengths_le_two_mu_source
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps rho : ℕ}
    {mu lambda c : ℝ}
    (hcondition : OsinCCondition D W eps mu lambda c rho)
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
      2 * mu * ((cell Delta source).word.length : ℝ) := by
  have hpublished := isPublishedPiece_of_cyclicCellArcs
    hcondition.toIsSmallCancellation sourceArc targetArc hleft hright harcs hwhole
  have hbound := hcondition.publishedPiecesSmall
    (dartWord Delta sourceArc.darts) (dartWord Delta targetArc.darts)
    (dartWord Delta sourceArc.rotated) hpublished
  have hsource : (sourceArc.length : ℝ) <
      mu * (dartWord Delta sourceArc.rotated).length := by
    simpa only [dartWord, List.length_map, sourceArc.darts_length] using
      lt_of_le_of_lt (le_max_left _ _) hbound
  have htarget : (targetArc.length : ℝ) <
      mu * (dartWord Delta sourceArc.rotated).length := by
    simpa only [dartWord, List.length_map, targetArc.darts_length] using
      lt_of_le_of_lt (le_max_right _ _) hbound
  have hcarrier : (dartWord Delta sourceArc.rotated).length =
      (cell Delta source).word.length := by
    simp only [dartWord, List.length_map, sourceArc.rotated_length]
    have hlength := congrArg List.length (dartWord_cellDarts Delta source)
    simpa only [dartWord, List.length_map] using hlength
  rw [hcarrier] at hsource htarget
  linarith

/-- Transport an embedded target arc to its relator-cell cyclic carrier. -/
def Contiguity.cellTargetArc
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

/-- The two face-set equations needed to transfer O52. -/
structure CellPieceEquations
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps : ℕ}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces) where
  target : Fin Delta.rCellCount
  target_eq : Gamma.target = some target
  arcs_value : GGT.RelLetter.listVal
      (dartWord Delta (Gamma.cellTargetArc target target_eq).darts) =
    GGT.RelLetter.listVal (dartWord Delta Gamma.leftSide) *
      GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.darts) *
      GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide)
  whole_ne : GGT.RelLetter.listVal
      (dartWord Delta (Gamma.cellTargetArc target target_eq).rotated) ≠
    GGT.RelLetter.listVal (dartWord Delta Gamma.leftSide) *
      GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.rotated) *
      (GGT.RelLetter.listVal (dartWord Delta Gamma.leftSide))⁻¹

/-- O52 in the exact source-incidence charge form used by assembly. -/
theorem Contiguity.arcLengths_le_two_mu_source
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps rho : ℕ}
    {mu lambda c : ℝ}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
    (equations : CellPieceEquations Gamma)
    (hcondition : OsinCCondition D W eps mu lambda c rho) :
    (Gamma.sourceArc.length : ℝ) +
        ((Gamma.cellTargetArc equations.target equations.target_eq).length : ℝ) ≤
      2 * mu * ((cell Delta Gamma.source).word.length : ℝ) := by
  exact cyclicArcLengths_le_two_mu_source hcondition Gamma.sourceArc
    (Gamma.cellTargetArc equations.target equations.target_eq)
    Gamma.leftSide_norm_le Gamma.rightSide_norm_le
    equations.arcs_value equations.whole_ne

/-- The same charge at the target follows by supplying the reversed piece
equations, which are explicit because both short connector norms are
invariant under inversion. -/
theorem Contiguity.arcLengths_le_two_mu_target
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps rho : ℕ}
    {mu lambda c : ℝ}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
    (equations : CellPieceEquations Gamma)
    {reverseLeft reverseRight : G}
    (hleft : wordNorm D.alphabet.carrier reverseLeft ≤ eps)
    (hright : wordNorm D.alphabet.carrier reverseRight ≤ eps)
    (harcs : GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.darts) =
      reverseLeft * GGT.RelLetter.listVal
        (dartWord Delta
          (Gamma.cellTargetArc equations.target equations.target_eq).darts) *
        reverseRight)
    (hwhole : GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.rotated) ≠
      reverseLeft * GGT.RelLetter.listVal
        (dartWord Delta
          (Gamma.cellTargetArc equations.target equations.target_eq).rotated) *
        reverseLeft⁻¹)
    (hcondition : OsinCCondition D W eps mu lambda c rho) :
    (Gamma.sourceArc.length : ℝ) +
        ((Gamma.cellTargetArc equations.target equations.target_eq).length : ℝ) ≤
      2 * mu * ((cell Delta equations.target).word.length : ℝ) := by
  have hbound := cyclicArcLengths_le_two_mu_source hcondition
    (Gamma.cellTargetArc equations.target equations.target_eq) Gamma.sourceArc
    hleft hright harcs hwhole
  linarith

/-- Transporting the dependent target carrier does not change the stored arc
length.  This is the identification between O52's cell-target arc and
`Candidate.weight`. -/
theorem Contiguity.cellTargetArc_length
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps : ℕ}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces) (target : Fin Delta.rCellCount)
    (htarget : Gamma.target = some target) :
    (Gamma.cellTargetArc target htarget).length = Gamma.targetArc.length := by
  cases htarget
  rfl

/-- A candidate's natural-number weight is the real sum of the two arcs used
by the source and target O52 estimates. -/
theorem Candidate.weight_eq_cellPieceArcLengths
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps : ℕ}
    (candidate : Candidate D eps Delta)
    (equations : CellPieceEquations candidate.contiguity) :
    (candidate.weight : ℝ) =
      (candidate.contiguity.sourceArc.length : ℝ) +
        ((candidate.contiguity.cellTargetArc equations.target
          equations.target_eq).length : ℝ) := by
  rw [Candidate.weight, Nat.cast_add,
    candidate.contiguity.cellTargetArc_length equations.target
      equations.target_eq]

/-- Osin O52 fills the source incidence of
`EstimatingData.edgeWeight_le_incident` for a selected candidate. -/
theorem Candidate.weight_le_two_mu_source
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps rho : ℕ}
    {mu lambda c : ℝ}
    (candidate : Candidate D eps Delta)
    (equations : CellPieceEquations candidate.contiguity)
    (hcondition : OsinCCondition D W eps mu lambda c rho) :
    (candidate.weight : ℝ) ≤
      2 * mu *
        ((cell Delta candidate.contiguity.source).word.length : ℝ) := by
  rw [candidate.weight_eq_cellPieceArcLengths equations]
  exact candidate.contiguity.arcLengths_le_two_mu_source equations hcondition

/-- Osin O52 fills the target incidence of
`EstimatingData.edgeWeight_le_incident` for a selected candidate. -/
theorem Candidate.weight_le_two_mu_target
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps rho : ℕ}
    {mu lambda c : ℝ}
    (candidate : Candidate D eps Delta)
    (equations : CellPieceEquations candidate.contiguity)
    {reverseLeft reverseRight : G}
    (hleft : wordNorm D.alphabet.carrier reverseLeft ≤ eps)
    (hright : wordNorm D.alphabet.carrier reverseRight ≤ eps)
    (harcs : GGT.RelLetter.listVal
        (dartWord Delta candidate.contiguity.sourceArc.darts) =
      reverseLeft * GGT.RelLetter.listVal
        (dartWord Delta (candidate.contiguity.cellTargetArc equations.target
          equations.target_eq).darts) * reverseRight)
    (hwhole : GGT.RelLetter.listVal
        (dartWord Delta candidate.contiguity.sourceArc.rotated) ≠
      reverseLeft * GGT.RelLetter.listVal
        (dartWord Delta (candidate.contiguity.cellTargetArc equations.target
          equations.target_eq).rotated) * reverseLeft⁻¹)
    (hcondition : OsinCCondition D W eps mu lambda c rho) :
    (candidate.weight : ℝ) ≤
      2 * mu * ((cell Delta equations.target).word.length : ℝ) := by
  rw [candidate.weight_eq_cellPieceArcLengths equations]
  exact candidate.contiguity.arcLengths_le_two_mu_target equations
    hleft hright harcs hwhole hcondition

end Embedded

end VanKampen
end GGT
end GroupApproximation
