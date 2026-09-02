import GroupApproximation.GGT.VanKampen.Estimating.Embedded
import GroupApproximation.GGT.VanKampen.GRegionBoundaryValue
import GroupApproximation.GGT.VanKampen.Contiguity
import GroupApproximation.GGT.VanKampen.FaceSetPeelWitness
import GroupApproximation.GGT.HullSCPublishedSmallCancellation

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

noncomputable local instance faceDecidableEqPiece
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} :
    DecidableEq Delta.toCombMap.Face := Classical.decEq _

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

/-- Reverse-alpha of a positioned arc is a prefix of a suitable rotation of
the inverse carrier word.  The moved prefix is the carrier suffix, so this
is the target-carrier orientation used by the pasted boundary equation. -/
def reversePrefixTarget
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    {cycle : List Delta.toCombMap.Dart} (arc : CyclicArc cycle) :
    List (GGT.RelLetter G Lambda) :=
  (RelWord.revInv (dartWord Delta arc.rotated)).rotate
    (dartWord Delta (arc.rotated.drop arc.length)).length

def reverseDartsWord
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    {cycle : List Delta.toCombMap.Dart} (arc : CyclicArc cycle) :
    List (GGT.RelLetter G Lambda) :=
  dartWord Delta (CyclicArc.reverseDarts arc)

theorem exists_reverseDarts_prefix_of_rotated_revInv
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    {cycle : List Delta.toCombMap.Dart} (arc : CyclicArc cycle) :
    ∃ suffix : List (GGT.RelLetter G Lambda),
      reversePrefixTarget Delta arc = reverseDartsWord Delta arc ++ suffix := by
  have hsplit : arc.rotated = arc.rotated.take arc.length ++
      arc.rotated.drop arc.length := by
    exact (List.take_append_drop arc.length arc.rotated).symm
  have hword : dartWord Delta arc.rotated =
      dartWord Delta (arc.rotated.take arc.length) ++
        dartWord Delta (arc.rotated.drop arc.length) := by
    have h := congrArg (dartWord Delta) hsplit
    simpa only [dartWord_append] using h
  have hinv : RelWord.revInv (dartWord Delta arc.rotated) =
      RelWord.revInv (dartWord Delta (arc.rotated.drop arc.length)) ++
        RelWord.revInv (dartWord Delta (arc.rotated.take arc.length)) := by
    rw [hword, RelWord.revInv_append]
  have hslen :
      (RelWord.revInv (dartWord Delta (arc.rotated.drop arc.length))).length =
        (arc.rotated.drop arc.length).length := by
    rw [RelWord.length_revInv]
    simp only [dartWord, List.length_map]
  have hrotate :
      (RelWord.revInv (dartWord Delta arc.rotated)).rotate
          (arc.rotated.drop arc.length).length =
        (RelWord.revInv (dartWord Delta (arc.rotated.take arc.length))) ++
          RelWord.revInv (dartWord Delta (arc.rotated.drop arc.length)) := by
    rw [hinv, ← hslen, List.rotate_append_length_eq]
  have hreverse :
      reverseDartsWord Delta arc =
        RelWord.revInv (dartWord Delta (arc.rotated.take arc.length)) := by
    exact (dartWord_reverse_alpha Delta arc.darts).trans (by rfl)
  refine ⟨RelWord.revInv (dartWord Delta (arc.rotated.drop arc.length)), ?_⟩
  unfold reversePrefixTarget
  have hlen :
      (dartWord Delta (arc.rotated.drop arc.length)).length =
        (arc.rotated.drop arc.length).length := by
    simp only [dartWord, List.length_map]
  rw [hlen, hrotate, hreverse]

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
    {Delta : DiscDiagram.{u, w, v} W} {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    (hpieces : ∀ first second word,
      RelWord.IsPublishedPiece D W eps first second word →
        max (first.length : ℝ) (second.length : ℝ) < mu * word.length)
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
    hsc sourceArc targetArc hleft hright harcs hwhole
  have hbound := hpieces
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
  have hcycle : targetDarts Delta Gamma.target = cellDarts Delta target := by
    rw [htarget]
    rfl
  exact {
    start := Fin.cast
      (congrArg (fun cycle => cycle.length + 1) hcycle) Gamma.targetArc.start
    length := Gamma.targetArc.length
    length_le := by
      rw [← hcycle]
      exact Gamma.targetArc.length_le }

/-- The target arc transported to the syntactic `some target` carrier. -/
noncomputable def Contiguity.targetArcAtSome
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps : ℕ}
    {faces : Finset Delta.toCombMap.Face}
  (Gamma : Contiguity D eps Delta faces)
  (target : Fin Delta.rCellCount) (htarget : Gamma.target = some target) :
    CyclicArc (targetDarts Delta (some target)) := by
  have hcycle : targetDarts Delta Gamma.target =
      targetDarts Delta (some target) := by rw [htarget]
  exact cast (congrArg CyclicArc hcycle) Gamma.targetArc

theorem targetBoundaryDarts_cast
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {first second : Option (Fin Delta.rCellCount)}
    (h : first = second) (arc : CyclicArc (targetDarts Delta first)) :
    targetBoundaryDarts Delta first arc =
      targetBoundaryDarts Delta second
        (cast (congrArg CyclicArc (congrArg (targetDarts Delta) h)) arc) := by
  cases h
  rfl

/-- The exact equation obtained from a cellular face-pasting certificate in
the orientation used by `Embedded.Contiguity.boundary_decomposition`. -/
theorem Contiguity.targetBoundary_value_of_pasting
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
    (pasting : FaceSetWordHomotopy Delta faces Gamma.boundary.cycle []) :
    GGT.RelLetter.listVal
        (dartWord Delta
          (targetBoundaryDarts Delta Gamma.target Gamma.targetArc)) =
      (GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide))⁻¹ *
        GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.darts) *
        (GGT.RelLetter.listVal (dartWord Delta Gamma.leftSide))⁻¹ := by
  have hsource := Gamma.arcs_value_of_pasting pasting
  rw [hsource]
  group

/-! ## Inverse target carriers -/

/-- The transported target carrier is the inverse relator rotation whose
prefix is the oppositely oriented target boundary arc. -/
noncomputable def Contiguity.targetInverseCarrier
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
    (target : Fin Delta.rCellCount) (htarget : Gamma.target = some target) :
    List (GGT.RelLetter G Lambda) :=
  (RelWord.revInv (dartWord Delta
      (Gamma.targetArcAtSome target htarget).rotated)).rotate
    (dartWord Delta
      ((Gamma.targetArcAtSome target htarget).rotated.drop
        (Gamma.targetArcAtSome target htarget).length)).length

/-- The transported inverse carrier is a member of the relator family. -/
theorem Contiguity.targetInverseCarrier_mem
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {D : GGT.RelGenSet G Lambda} {eps rho : ℕ} {mu : ℝ}
    {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
    (target : Fin Delta.rCellCount) (htarget : Gamma.target = some target)
    (hsc : RelWord.IsSmallCancellation D W eps mu rho) :
    Gamma.targetInverseCarrier target htarget ∈ W := by
  have hcarrier := (Gamma.targetArcAtSome target htarget).cell_rotated_mem hsc
  have hinv := hsc.inv_mem _ hcarrier
  unfold Contiguity.targetInverseCarrier
  exact hsc.rotate_mem _ hinv _

/-- The inverse target carrier has the oppositely oriented target boundary as
a prefix. -/
theorem Contiguity.exists_targetInverseCarrier_suffix
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
  (target : Fin Delta.rCellCount) (htarget : Gamma.target = some target) :
    ∃ suffix : List (GGT.RelLetter G Lambda),
      Gamma.targetInverseCarrier target htarget =
        dartWord Delta (targetBoundaryDarts Delta Gamma.target Gamma.targetArc) ++ suffix := by
  obtain ⟨suffix, hsuffix⟩ := CyclicArc.exists_reverseDarts_prefix_of_rotated_revInv Delta
    (Gamma.targetArcAtSome target htarget)
  refine ⟨suffix, ?_⟩
  have hboundary :
      targetBoundaryDarts Delta Gamma.target Gamma.targetArc =
        targetBoundaryDarts Delta (some target)
          (Gamma.targetArcAtSome target htarget) := by
    change targetBoundaryDarts Delta Gamma.target Gamma.targetArc =
      targetBoundaryDarts Delta (some target)
        (cast (congrArg CyclicArc (congrArg (targetDarts Delta) htarget))
          Gamma.targetArc)
    exact targetBoundaryDarts_cast htarget Gamma.targetArc
  rw [hboundary]
  simpa [Contiguity.targetInverseCarrier, targetBoundaryDarts,
    CyclicArc.reversePrefixTarget, CyclicArc.reverseDartsWord] using hsuffix

/-- The transported inverse carrier has the target arc length. -/
theorem Contiguity.targetBoundaryDarts_length
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
    (target : Fin Delta.rCellCount) (_htarget : Gamma.target = some target) :
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
      (dartWord Delta (targetBoundaryDarts Delta Gamma.target Gamma.targetArc)) =
    (GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide))⁻¹ *
      GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.darts) *
      (GGT.RelLetter.listVal (dartWord Delta Gamma.leftSide))⁻¹
  whole_ne : GGT.RelLetter.listVal
      (Gamma.targetInverseCarrier target target_eq) ≠
    (GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide))⁻¹ *
      GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.rotated) *
      GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide)

/-- A face-set pasting and its transported reducedness exclusion produce the
single certificate consumed by both O52 endpoint estimates. -/
def CellPieceEquations.of_pasting
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps : ℕ}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
    {target : Fin Delta.rCellCount}
    (htarget : Gamma.target = some target)
    (pasting : FaceSetWordHomotopy Delta faces Gamma.boundary.cycle [])
    (hwhole : GGT.RelLetter.listVal
        (Gamma.targetInverseCarrier target htarget) ≠
      (GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide))⁻¹ *
        GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.rotated) *
        GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide)) :
    CellPieceEquations Gamma :=
  { target := target
    target_eq := htarget
    arcs_value := Gamma.targetBoundary_value_of_pasting pasting
    whole_ne := hwhole }

/-- The boundary-dart count is the only word-level part of the pasted-region
certificate.  Once the target index and the equation
`target = right⁻¹ * source * left⁻¹` have been counted directly, the same
reversed target-carrier prefix and non-cancellation clause form the complete
O52 certificate without mentioning the particular peeling homotopy used to
derive that equation. -/
def CellPieceEquations.of_boundary_equation
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps : ℕ}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
    {target : Fin Delta.rCellCount}
    (htarget : Gamma.target = some target)
    (harcs : GGT.RelLetter.listVal
        (dartWord Delta (targetBoundaryDarts Delta Gamma.target Gamma.targetArc)) =
      (GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide))⁻¹ *
        GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.darts) *
        (GGT.RelLetter.listVal (dartWord Delta Gamma.leftSide))⁻¹)
    (hwhole : GGT.RelLetter.listVal
        (Gamma.targetInverseCarrier target htarget) ≠
      (GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide))⁻¹ *
        GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.rotated) *
        GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide)) :
    CellPieceEquations Gamma :=
  { target := target
    target_eq := htarget
    arcs_value := harcs
    whole_ne := hwhole }

/-! ## Reducedness transfer for pasted embedded regions -/

/-- The data identifying an embedded source/target pair with the ordered
cell-to-cell certificate used by `CellContiguity.whole_relators_ne`. The
three value equalities are the orientation changes needed by the pasted
boundary equation. -/
structure ReducedCellPieceBridge
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps : ℕ}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces) where
  target : Fin Delta.rCellCount
  target_eq : Gamma.target = some target
  targetWord : List (GGT.RelLetter G Lambda)
  sourceWord : List (GGT.RelLetter G Lambda)
  connector : G
  whole_relators_ne : ∀ hred : Delta.Reduced, hred = hred →
      GGT.RelLetter.listVal (RelWord.revInv targetWord) ≠
        connector * GGT.RelLetter.listVal sourceWord * connector⁻¹
  targetCarrier_value_eq : GGT.RelLetter.listVal
      (Gamma.targetInverseCarrier target target_eq) =
      GGT.RelLetter.listVal (RelWord.revInv targetWord)
  sourceRotated_value_eq : GGT.RelLetter.listVal
      (dartWord Delta Gamma.sourceArc.rotated) =
      GGT.RelLetter.listVal sourceWord
  connector_value_eq : connector =
      (GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide))⁻¹

/-- A cell-to-cell contiguity witness supplies the reducedness field of the
embedded bridge after the three carrier/value identifications are checked. -/
def ReducedCellPieceBridge.of_cellContiguity
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps : ℕ}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
    {targetIndex : Fin Delta.rCellCount}
    (htarget : Gamma.target = some targetIndex)
    {pre between suf : List
      (RelatorCell Delta.toCombMap Delta.outerFace W)}
    {sourceCell targetCell : RelatorCell Delta.toCombMap Delta.outerFace W}
    (cellGamma : CellContiguity (D := D) (eps := eps)
      pre between suf sourceCell targetCell)
    (hcarrier : GGT.RelLetter.listVal
        (Gamma.targetInverseCarrier targetIndex htarget) =
      GGT.RelLetter.listVal (RelWord.revInv targetCell.word))
    (hsource : GGT.RelLetter.listVal
        (dartWord Delta Gamma.sourceArc.rotated) =
      GGT.RelLetter.listVal sourceCell.word)
    (hconnector : cellGamma.region.leftConnector =
      (GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide))⁻¹) :
    ReducedCellPieceBridge Gamma where
  target := targetIndex
  target_eq := htarget
  targetWord := targetCell.word
  sourceWord := sourceCell.word
  connector := cellGamma.region.leftConnector
  whole_relators_ne := fun hred _ => cellGamma.whole_relators_ne hred
  targetCarrier_value_eq := hcarrier
  sourceRotated_value_eq := hsource
  connector_value_eq := hconnector

/-- The complete local input for one pasted embedded region: a reducedness
bridge together with the face-set word homotopy exposing its boundary. -/
structure PastingReducedCellPieceCertificate
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps : ℕ}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces) where
  bridge : ReducedCellPieceBridge Gamma
  pasting : FaceSetWordHomotopy Delta faces Gamma.boundary.cycle []

namespace ReducedCellPieceBridge

/-- Diagram reducedness transfers through a `ReducedCellPieceBridge` to the
non-cancellation clause required by `CellPieceEquations`. -/
theorem whole_ne
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps : ℕ}
    {faces : Finset Delta.toCombMap.Face}
    {Gamma : Contiguity D eps Delta faces}
    (bridge : ReducedCellPieceBridge Gamma)
    (hred : Delta.Reduced) :
    GGT.RelLetter.listVal
        (Gamma.targetInverseCarrier bridge.target bridge.target_eq) ≠
      (GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide))⁻¹ *
        GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.rotated) *
        GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide) := by
  intro hbad
  apply bridge.whole_relators_ne hred rfl
  calc
    GGT.RelLetter.listVal (RelWord.revInv bridge.targetWord) =
        GGT.RelLetter.listVal
          (Gamma.targetInverseCarrier bridge.target bridge.target_eq) :=
      bridge.targetCarrier_value_eq.symm
    _ = (GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide))⁻¹ *
          GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.rotated) *
          GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide) := hbad
    _ = bridge.connector * GGT.RelLetter.listVal bridge.sourceWord *
          bridge.connector⁻¹ := by
      rw [bridge.connector_value_eq, bridge.sourceRotated_value_eq]
      simp only [inv_inv]

end ReducedCellPieceBridge

/-- A reduced cell bridge supplies the non-cancellation field for the direct
boundary-equation constructor. -/
def CellPieceEquations.of_boundary_equation_reduced
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps : ℕ}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
    (bridge : ReducedCellPieceBridge Gamma)
    (harcs : GGT.RelLetter.listVal
        (dartWord Delta (targetBoundaryDarts Delta Gamma.target Gamma.targetArc)) =
      (GGT.RelLetter.listVal (dartWord Delta Gamma.rightSide))⁻¹ *
        GGT.RelLetter.listVal (dartWord Delta Gamma.sourceArc.darts) *
        (GGT.RelLetter.listVal (dartWord Delta Gamma.leftSide))⁻¹)
    (hred : Delta.Reduced) :
    CellPieceEquations Gamma :=
  CellPieceEquations.of_boundary_equation Gamma bridge.target_eq harcs
    (bridge.whole_ne hred)

/-- A complete pasted certificate produces the two face-set equations. -/
def PastingReducedCellPieceCertificate.equations
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps : ℕ}
    {faces : Finset Delta.toCombMap.Face}
    {Gamma : Contiguity D eps Delta faces}
    (certificate : PastingReducedCellPieceCertificate Gamma)
    (hred : Delta.Reduced) : CellPieceEquations Gamma :=
  CellPieceEquations.of_pasting Gamma certificate.bridge.target_eq
    certificate.pasting (ReducedCellPieceBridge.whole_ne certificate.bridge hred)

/-- Every pasted embedded region equipped with the reducedness bridge yields
its exact `CellPieceEquations` certificate. -/
def cellPieceEquations_of_pasting_reduced
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps : ℕ}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
    (bridge : ReducedCellPieceBridge Gamma)
    (hred : Delta.Reduced)
    (pasting : FaceSetWordHomotopy Delta faces Gamma.boundary.cycle []) :
    CellPieceEquations Gamma := by
  exact CellPieceEquations.of_pasting Gamma bridge.target_eq pasting
    (bridge.whole_ne hred)

/-- A complete boundary peeling supplies the pasting field for a selected
region, so the reduced cell bridge immediately gives the piece equations. -/
def PastingReducedCellPieceCertificate.of_boundaryPeeling
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps : ℕ}
    {faces : Finset Delta.toCombMap.Face}
    {Gamma : Contiguity D eps Delta faces}
    (bridge : ReducedCellPieceBridge Gamma)
    (peeling : FaceSetBoundaryPeeling Gamma.boundary) :
    PastingReducedCellPieceCertificate Gamma where
  bridge := bridge
  pasting := peeling.to_homotopy

/-- Boundary dart counting through `FaceSetBoundaryPeeling` gives the source,
target, right-side, and left-side equation used by both O52 charges. -/
def CellPieceEquations.of_boundaryPeeling
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps : ℕ}
    {faces : Finset Delta.toCombMap.Face}
    {Gamma : Contiguity D eps Delta faces}
    (bridge : ReducedCellPieceBridge Gamma)
    (peeling : FaceSetBoundaryPeeling Gamma.boundary)
    (hred : Delta.Reduced) :
    CellPieceEquations Gamma :=
  (PastingReducedCellPieceCertificate.of_boundaryPeeling bridge peeling).equations hred

/-! ## One-cell and two-cell boundary models -/

/-- The one-cell disc model uses the direct face-boundary deletion schedule,
so its boundary-counting equation is available without a global peel oracle. -/
def CellPieceEquations.oneCell_model
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps : ℕ}
    {faces : Finset Delta.toCombMap.Face}
    {Gamma : Contiguity D eps Delta faces}
    {face : Delta.toCombMap.Face}
    (hfaces : faces = {face})
    (hcycle : Gamma.boundary.cycle = (Delta.faceBoundary face).darts)
    (hface : face ≠ Delta.outerFace)
    (bridge : ReducedCellPieceBridge Gamma)
    (hred : Delta.Reduced) :
    CellPieceEquations Gamma := by
  have hscheduleSingleton : FaceSetDeletionSchedule (Delta := Delta)
      ({face} : Finset Delta.toCombMap.Face)
      (Delta.faceBoundary face).darts :=
    oneFace face hface
  have hscheduleSingleton' : FaceSetDeletionSchedule (Delta := Delta)
      ({face} : Finset Delta.toCombMap.Face) Gamma.boundary.cycle := by
    rw [hcycle]
    exact hscheduleSingleton
  have hschedule : FaceSetDeletionSchedule (Delta := Delta) faces
      Gamma.boundary.cycle := by
    simpa only [hfaces] using hscheduleSingleton'
  let peeling : FaceSetBoundaryPeeling Gamma.boundary :=
    { schedule := hschedule }
  exact CellPieceEquations.of_boundaryPeeling bridge peeling hred

/-- The two-cell mirror model uses the explicit adjacent-face schedule; the
same boundary-dart equation then feeds the reduced piece bridge. -/
def CellPieceEquations.twoCell_mirror_model
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps : ℕ}
    {faces : Finset Delta.toCombMap.Face}
    {Gamma : Contiguity D eps Delta faces}
    {f₁ f₂ : Delta.toCombMap.Face}
    (hfaces : faces = {f₁, f₂})
    (hneq : f₁ ≠ f₂)
    (h₁ : f₁ ≠ Delta.outerFace) (h₂ : f₂ ≠ Delta.outerFace)
    (cycle next : List Delta.toCombMap.Dart)
    (hcycle : Gamma.boundary.cycle = cycle)
    (moves : FaceSetMoveSequence (faces := faces) cycle next)
    (hnext : next = (Delta.faceBoundary f₂).darts)
    (bridge : ReducedCellPieceBridge Gamma)
    (hred : Delta.Reduced) :
    CellPieceEquations Gamma := by
  have h₁mem : f₁ ∈ faces := by
    rw [hfaces]
    simp [hneq]
  have h₂mem : f₂ ∈ faces := by
    rw [hfaces]
    simp
  have hschedule : FaceSetDeletionSchedule (Delta := Delta) faces cycle :=
    twoFacePeeling hfaces hneq h₁ h₂ h₁mem h₂mem cycle next moves hnext
  have hschedule' : FaceSetDeletionSchedule (Delta := Delta) faces
      Gamma.boundary.cycle := by
    rw [hcycle]
    exact hschedule
  let peeling : FaceSetBoundaryPeeling Gamma.boundary :=
    { schedule := hschedule' }
  exact CellPieceEquations.of_boundaryPeeling bridge peeling hred

/-- The singleton model is inhabited as a complete piece certificate. -/
theorem cellPieceEquations_oneCell_model_nonempty
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps : ℕ}
    {faces : Finset Delta.toCombMap.Face}
    {Gamma : Contiguity D eps Delta faces}
    {face : Delta.toCombMap.Face}
    (hfaces : faces = {face})
    (hcycle : Gamma.boundary.cycle = (Delta.faceBoundary face).darts)
    (hface : face ≠ Delta.outerFace)
    (bridge : ReducedCellPieceBridge Gamma)
    (hred : Delta.Reduced) :
    Nonempty (CellPieceEquations Gamma) :=
  ⟨CellPieceEquations.oneCell_model hfaces hcycle hface bridge hred⟩

/-- The two-cell mirror model is inhabited as a complete piece certificate. -/
theorem cellPieceEquations_twoCell_mirror_model_nonempty
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps : ℕ}
    {faces : Finset Delta.toCombMap.Face}
    {Gamma : Contiguity D eps Delta faces}
    {f₁ f₂ : Delta.toCombMap.Face}
    (hfaces : faces = {f₁, f₂})
    (hneq : f₁ ≠ f₂)
    (h₁ : f₁ ≠ Delta.outerFace) (h₂ : f₂ ≠ Delta.outerFace)
    (cycle next : List Delta.toCombMap.Dart)
    (hcycle : Gamma.boundary.cycle = cycle)
    (moves : FaceSetMoveSequence (faces := faces) cycle next)
    (hnext : next = (Delta.faceBoundary f₂).darts)
    (bridge : ReducedCellPieceBridge Gamma)
    (hred : Delta.Reduced) :
    Nonempty (CellPieceEquations Gamma) :=
  ⟨CellPieceEquations.twoCell_mirror_model hfaces hneq h₁ h₂ cycle next
      hcycle moves hnext bridge hred⟩

/-- A pasted embedded region and its reducedness exclusion form the published
piece used by both endpoint estimates. -/
theorem Contiguity.isPublishedPiece_of_equations
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps rho : ℕ} {mu : ℝ}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
    (equations : CellPieceEquations Gamma)
    (hsc : RelWord.IsSmallCancellation D W eps mu rho) :
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
    hright, hleft, equations.arcs_value,
    (by simpa only [inv_inv] using equations.whole_ne)⟩

/-- O52 in the exact source-incidence charge form used by assembly. -/
theorem Contiguity.arcLengths_le_two_mu_source
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps rho : ℕ} {mu : ℝ}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
    (equations : CellPieceEquations Gamma)
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    (hpieces : ∀ first second word,
      RelWord.IsPublishedPiece D W eps first second word →
        max (first.length : ℝ) (second.length : ℝ) < mu * word.length) :
    (Gamma.sourceArc.length : ℝ) +
        ((Gamma.cellTargetArc equations.target equations.target_eq).length : ℝ) ≤
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
      exact Gamma.targetBoundaryDarts_length equations.target equations.target_eq
    rw [hlenBoundary] at htarget'
    exact htarget'
  have hcarrier : (dartWord Delta Gamma.sourceArc.rotated).length =
      (cell Delta Gamma.source).word.length := by
    simp only [dartWord, List.length_map, Gamma.sourceArc.rotated_length]
    have hlength := congrArg List.length
      (dartWord_cellDarts Delta Gamma.source)
    simpa only [dartWord, List.length_map, targetDarts] using hlength
  rw [hcarrier] at hsource htarget
  have htargetArcLength :
      (Gamma.cellTargetArc equations.target equations.target_eq).length =
        Gamma.targetArc.length := by rfl
  rw [htargetArcLength]
  linarith

/-- The same certificate gives the target charge: invert both connectors and
reverse its arc equation and non-cancellation clause. -/
theorem Contiguity.arcLengths_le_two_mu_target
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps rho : ℕ} {mu : ℝ}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Contiguity D eps Delta faces)
    (equations : CellPieceEquations Gamma)
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    (hpieces : ∀ first second word,
      RelWord.IsPublishedPiece D W eps first second word →
        max (first.length : ℝ) (second.length : ℝ) < mu * word.length) :
    (Gamma.sourceArc.length : ℝ) +
        ((Gamma.cellTargetArc equations.target equations.target_eq).length : ℝ) ≤
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
          GGT.RelLetter.listVal (dartWord Delta Gamma.leftSide) := by
      rw [equations.arcs_value]
      group
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
      exact Gamma.targetBoundaryDarts_length equations.target equations.target_eq
    rw [hlenBoundary] at htarget'
    exact htarget'
  have hsource : (Gamma.sourceArc.length : ℝ) <
      mu * (Gamma.targetInverseCarrier equations.target equations.target_eq).length := by
    simpa only [dartWord, List.length_map, Gamma.sourceArc.darts_length] using
      lt_of_le_of_lt (le_max_right _ _) hbound
  have hcarrier :
      (Gamma.targetInverseCarrier equations.target equations.target_eq).length =
        (cell Delta equations.target).word.length := by
    unfold Contiguity.targetInverseCarrier
    simp only [List.length_rotate, RelWord.length_revInv, dartWord,
      List.length_map, CyclicArc.rotated_length]
    have hlength := congrArg List.length
      (dartWord_cellDarts Delta equations.target)
    have htargetDarts : targetDarts Delta (some equations.target) =
        cellDarts Delta equations.target := by rfl
    rw [htargetDarts]
    simpa only [dartWord, List.length_map] using hlength
  rw [hcarrier] at hsource htarget
  have htargetArcLength :
      (Gamma.cellTargetArc equations.target equations.target_eq).length =
        Gamma.targetArc.length := by rfl
  rw [htargetArcLength]
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
    {Delta : DiscDiagram.{u, w, v} W} {eps rho : ℕ} {mu : ℝ}
    (candidate : Candidate D eps Delta)
    (equations : CellPieceEquations candidate.contiguity)
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    (hpieces : ∀ first second word,
      RelWord.IsPublishedPiece D W eps first second word →
        max (first.length : ℝ) (second.length : ℝ) < mu * word.length) :
    (candidate.weight : ℝ) ≤
      2 * mu *
        ((cell Delta candidate.contiguity.source).word.length : ℝ) := by
  rw [candidate.weight_eq_cellPieceArcLengths equations]
  exact candidate.contiguity.arcLengths_le_two_mu_source equations hsc hpieces

/-- Osin O52 fills the target incidence of
`EstimatingData.edgeWeight_le_incident` for a selected candidate. -/
theorem Candidate.weight_le_two_mu_target
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {eps rho : ℕ} {mu : ℝ}
    (candidate : Candidate D eps Delta)
    (equations : CellPieceEquations candidate.contiguity)
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    (hpieces : ∀ first second word,
      RelWord.IsPublishedPiece D W eps first second word →
        max (first.length : ℝ) (second.length : ℝ) < mu * word.length) :
    (candidate.weight : ℝ) ≤
      2 * mu * ((cell Delta equations.target).word.length : ℝ) := by
  rw [candidate.weight_eq_cellPieceArcLengths equations]
  exact candidate.contiguity.arcLengths_le_two_mu_target equations
    hsc hpieces

end Embedded

end VanKampen
end GGT
end GroupApproximation
