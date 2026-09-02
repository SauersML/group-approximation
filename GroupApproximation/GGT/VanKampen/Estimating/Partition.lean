import GroupApproximation.GGT.VanKampen.Estimating.Embedded
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Positioned boundary partitions for embedded contiguity systems

This file records the cell-boundary partition from Appendix Definition M.
Every bound piece points to an actual selected embedded region and remembers
whether the cell is its source or its cell target.  Every piece, including an
unbound piece, carries a cyclic base position through `Embedded.CyclicArc`.

The final section isolates the numerical conversion used after Lemma 62:
the strict `n * sqrt rho` bound on all unbound arcs becomes the `2 * mu`
uncovered budget once all `n` relator perimeters are at least `rho` and
`2 * mu * sqrt rho >= 1`.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

universe u w v

namespace Embedded

/-- Classification of one positioned arc on a relator-cell boundary. -/
inductive CellArcKind
  | exterior
  | interior
  | unbound
  deriving DecidableEq

/-- An occurrence of a selected embedded region on the boundary of the
`i`-th relator cell. -/
inductive CellIncidence
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta))
    (i : Fin Delta.rCellCount) : Type (max u w v)
  | source (candidate : Candidate D eps Delta)
      (mem_selected : candidate ∈ selected)
      (source_eq : candidate.contiguity.source = i)
  | target (candidate : Candidate D eps Delta)
      (mem_selected : candidate ∈ selected)
      (target_eq : candidate.contiguity.target = some i)

namespace CellIncidence

/-- The cyclic cell arc carried by an incidence. -/
noncomputable def arc
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    (incidence : CellIncidence selected i) : CyclicArc (cellDarts Delta i) := by
  cases incidence with
  | source candidate _ source_eq =>
      rw [← source_eq]
      exact candidate.contiguity.sourceArc
  | target candidate _ target_eq =>
      have hcarrier : targetDarts Delta candidate.contiguity.target =
          cellDarts Delta i := by
        rw [target_eq]
        rfl
      rw [← hcarrier]
      exact candidate.contiguity.targetArc

/-- A source occurrence aimed at the outer boundary is exterior; both
occurrences of a cell-to-cell region are interior. -/
noncomputable def kind
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    (incidence : CellIncidence selected i) : CellArcKind :=
  match incidence with
  | .source candidate _ _ =>
      if candidate.contiguity.target = none then
        CellArcKind.exterior
      else
        CellArcKind.interior
  | .target _ _ _ => CellArcKind.interior

end CellIncidence

/-- One part of the cyclic perimeter partition. -/
inductive CellPiece
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta))
    (i : Fin Delta.rCellCount) : Type (max u w v)
  | bound (incidence : CellIncidence selected i)
  | unbound (arc : CyclicArc (cellDarts Delta i))

namespace CellPiece

/-- The positioned cyclic arc underlying a cell piece. -/
noncomputable def arc
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    (piece : CellPiece selected i) : CyclicArc (cellDarts Delta i) :=
  match piece with
  | .bound incidence => incidence.arc
  | .unbound arc => arc

/-- Classification of a cell piece. -/
noncomputable def kind
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    (piece : CellPiece selected i) : CellArcKind :=
  match piece with
  | .bound incidence => incidence.kind
  | .unbound _ => CellArcKind.unbound

end CellPiece

/-- A complete cyclic partition of one relator-cell boundary.  The base
position names the rotation at which the displayed linear decomposition
starts; every individual piece also retains its own cyclic start position. -/
structure CellBoundaryPartition
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta))
    (i : Fin Delta.rCellCount) where
  base : Fin ((cellDarts Delta i).length + 1)
  pieces : List (CellPiece selected i)
  decomposition :
    (cellDarts Delta i).drop base.1 ++ (cellDarts Delta i).take base.1 =
      pieces.flatMap fun piece => piece.arc.darts

namespace CellBoundaryPartition

private theorem pieceLength_sum_aux
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    (pieces : List (CellPiece selected i)) :
    (pieces.map fun piece => piece.arc.length).sum =
      ((pieces.filter fun piece => piece.kind = CellArcKind.exterior).map
          fun piece => piece.arc.length).sum +
      ((pieces.filter fun piece => piece.kind = CellArcKind.interior).map
          fun piece => piece.arc.length).sum +
      ((pieces.filter fun piece => piece.kind = CellArcKind.unbound).map
          fun piece => piece.arc.length).sum := by
  induction pieces with
  | nil => simp
  | cons piece pieces ih =>
      cases hkind : piece.kind with
      | exterior => simp [hkind, ih]; omega
      | interior => simp [hkind, ih]; omega
      | unbound => simp [hkind, ih]; omega

/-- Total length of pieces of one kind. -/
noncomputable def kindLength
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    (partition : CellBoundaryPartition selected i) (kind : CellArcKind) : ℕ :=
  ((partition.pieces.filter fun piece => piece.kind = kind).map
    fun piece => piece.arc.length).sum

/-- The three classifications partition the sum of all piece lengths. -/
theorem pieceLength_sum
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    (partition : CellBoundaryPartition selected i) :
    (partition.pieces.map fun piece => piece.arc.length).sum =
      partition.kindLength CellArcKind.exterior +
      partition.kindLength CellArcKind.interior +
      partition.kindLength CellArcKind.unbound := by
  exact pieceLength_sum_aux partition.pieces

/-- The dart cycle of an indexed cell has the length of its relator word. -/
theorem cellDarts_length_eq_word_length
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (i : Fin Delta.rCellCount) :
    (cellDarts Delta i).length = (cell Delta i).word.length := by
  have hlength := congrArg List.length (dartWord_cellDarts Delta i)
  simpa only [dartWord, List.length_map] using hlength

/-- Exterior, interior, and unbound positioned arcs partition the cell
perimeter exactly. -/
theorem perimeter_eq_kindLengths
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    (partition : CellBoundaryPartition selected i) :
    (cell Delta i).word.length =
      partition.kindLength CellArcKind.exterior +
      partition.kindLength CellArcKind.interior +
      partition.kindLength CellArcKind.unbound := by
  have hlength := congrArg List.length partition.decomposition
  have hbase : partition.base.1 ≤ (cellDarts Delta i).length := by omega
  have hpieces :
      (partition.pieces.flatMap fun piece => piece.arc.darts).length =
        (partition.pieces.map fun piece => piece.arc.length).sum := by
    simp only [List.length_flatMap, CyclicArc.darts_length]
  rw [List.length_append, List.length_drop, List.length_take, Nat.min_eq_left hbase,
    hpieces, partition.pieceLength_sum] at hlength
  rw [← cellDarts_length_eq_word_length Delta i]
  omega

end CellBoundaryPartition

/-- Positioned boundary partitions for every relator cell of one selected
embedded family. -/
structure DiagramBoundaryPartition
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta)) where
  cell : ∀ i : Fin Delta.rCellCount, CellBoundaryPartition selected i

namespace DiagramBoundaryPartition

/-- Real weight of one class of positioned cell arcs. -/
noncomputable def kindWeight
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    (partition : DiagramBoundaryPartition selected)
    (kind : CellArcKind) (i : Fin Delta.rCellCount) : ℝ :=
  (partition.cell i).kindLength kind

/-- The real-valued partition used by the contiguity count. -/
theorem cellWeight_partition
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    (partition : DiagramBoundaryPartition selected)
    (i : Fin Delta.rCellCount) :
    ((Embedded.cell Delta i).word.length : ℝ) =
      partition.kindWeight CellArcKind.exterior i +
      partition.kindWeight CellArcKind.interior i +
      partition.kindWeight CellArcKind.unbound i := by
  simp only [kindWeight]
  exact_mod_cast (partition.cell i).perimeter_eq_kindLengths

/-- Total number of unbound cell-boundary darts. -/
noncomputable def unboundTotal
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    (partition : DiagramBoundaryPartition selected) : ℕ :=
  ∑ i : Fin Delta.rCellCount,
    (partition.cell i).kindLength CellArcKind.unbound

/-- Lemma 62's strict `n * sqrt rho` estimate implies the `2 * mu`
uncovered budget used by the final count. -/
theorem unbound_total_le_two_mu
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    (partition : DiagramBoundaryPartition selected)
    (mu : ℝ) (rho : ℕ)
    (hperimeter : ∀ i : Fin Delta.rCellCount,
      rho ≤ (Embedded.cell Delta i).word.length)
    (hlemma62 : (partition.unboundTotal : ℝ) <
      (Delta.rCellCount : ℝ) * Real.sqrt (rho : ℝ))
    (hthreshold : 1 ≤ 2 * mu * Real.sqrt (rho : ℝ)) :
    (∑ i : Fin Delta.rCellCount,
        partition.kindWeight CellArcKind.unbound i) ≤
      2 * mu * ∑ i : Fin Delta.rCellCount,
        ((Embedded.cell Delta i).word.length : ℝ) := by
  have hrhoPos : 0 < (rho : ℝ) := by
    by_contra hrho
    have hrhoZero : (rho : ℝ) = 0 := le_antisymm (le_of_not_gt hrho) (by positivity)
    rw [hrhoZero, Real.sqrt_zero, mul_zero] at hthreshold
    norm_num at hthreshold
  have hsqrtPos : 0 < Real.sqrt (rho : ℝ) := Real.sqrt_pos.2 hrhoPos
  have hsqrtSq : Real.sqrt (rho : ℝ) * Real.sqrt (rho : ℝ) = (rho : ℝ) :=
    Real.mul_self_sqrt (le_of_lt hrhoPos)
  have hperimeterSum :
      (Delta.rCellCount : ℝ) * (rho : ℝ) ≤
        ∑ i : Fin Delta.rCellCount, ((Embedded.cell Delta i).word.length : ℝ) := by
    calc
      (Delta.rCellCount : ℝ) * (rho : ℝ) =
          ∑ _i : Fin Delta.rCellCount, (rho : ℝ) := by simp
      _ ≤ ∑ i : Fin Delta.rCellCount, ((Embedded.cell Delta i).word.length : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        exact_mod_cast hperimeter i
  have hscale :
      (Delta.rCellCount : ℝ) * Real.sqrt (rho : ℝ) ≤
        2 * mu * ((Delta.rCellCount : ℝ) * (rho : ℝ)) := by
    have hn : 0 ≤ (Delta.rCellCount : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hthreshold
      (mul_nonneg hn (le_of_lt hsqrtPos))
    nlinarith
  have hbudget : (partition.unboundTotal : ℝ) ≤
      2 * mu * ∑ i : Fin Delta.rCellCount,
        ((Embedded.cell Delta i).word.length : ℝ) := by
    have hmuNonneg : 0 ≤ 2 * mu := by
      have : 0 ≤ mu := by nlinarith [hthreshold, hsqrtPos]
      positivity
    exact le_trans (le_of_lt hlemma62)
      (le_trans hscale (mul_le_mul_of_nonneg_left hperimeterSum hmuNonneg))
  have hunboundCast :
      (partition.unboundTotal : ℝ) =
        ∑ i : Fin Delta.rCellCount,
          partition.kindWeight CellArcKind.unbound i := by
    simp only [unboundTotal, kindWeight, Nat.cast_sum]
  rwa [hunboundCast] at hbudget

end DiagramBoundaryPartition

end Embedded

end VanKampen
end GGT
end GroupApproximation
