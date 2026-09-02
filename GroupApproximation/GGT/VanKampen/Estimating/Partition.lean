import GroupApproximation.GGT.VanKampen.Estimating.Embedded
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Positioned boundary partitions for embedded contiguity systems

This file constructs the cell-boundary partition from Appendix Definition M.
Every dart of a relator-cell boundary is indexed by its cyclic `Fin` position.
A bound dart points to an actual selected embedded region and remembers whether
the cell is its source or target.  A dart which occurs on no selected region is
unbound.  The classifier is defined by finite classical choice, so it exists
for every selected family and the exterior/interior/unbound perimeter identity
is automatic.

The final theorem isolates the numerical conversion used after Lemma 62: the
strict `n * sqrt rho` bound on unbound darts becomes the `2 * mu` uncovered
budget once every relator perimeter is at least `rho` and
`2 * mu * sqrt rho >= 1`.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

universe u w v

namespace Embedded

/-- Classification of one positioned dart on a relator-cell boundary. -/
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

/-- Positions of the fixed cell boundary occupied by one selected
incidence. -/
noncomputable def Position
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    (incidence : CellIncidence selected i) :=
  {position : Fin (cellDarts Delta i).length //
    (cellDarts Delta i).get position ∈ incidence.arc.darts}

/-- The arc of an incidence has no repeated darts. -/
theorem arc_darts_nodup
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    (incidence : CellIncidence selected i) : incidence.arc.darts.Nodup :=
  incidence.arc.darts_nodup (cellDarts_nodup Delta i)

/-- Occupied boundary positions are equivalent to the darts of the stored
cyclic arc. -/
noncomputable def positionEquivArcDarts
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    (incidence : CellIncidence selected i) :
    incidence.Position ≃
      {d : Delta.toCombMap.Dart // d ∈ incidence.arc.darts} := by
  classical
  let carrierEquiv : Fin (cellDarts Delta i).length ≃
      {d : Delta.toCombMap.Dart // d ∈ cellDarts Delta i} :=
    (cellDarts_nodup Delta i).getEquiv (cellDarts Delta i)
  let restricted : incidence.Position ≃
      {d : {d : Delta.toCombMap.Dart // d ∈ cellDarts Delta i} //
        d.1 ∈ incidence.arc.darts} :=
    carrierEquiv.subtypeEquiv fun _ => Iff.rfl
  let forgetCarrier :
      {d : {d : Delta.toCombMap.Dart // d ∈ cellDarts Delta i} //
          d.1 ∈ incidence.arc.darts} ≃
        {d : Delta.toCombMap.Dart // d ∈ incidence.arc.darts} where
    toFun d := ⟨d.1.1, d.2⟩
    invFun d :=
      ⟨⟨d.1, incidence.arc.mem_cycle_of_mem_darts d.2⟩, d.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
  exact restricted.trans forgetCarrier

/-- The number of occupied positions of an incidence is exactly its stored
arc length. -/
theorem card_position
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    (incidence : CellIncidence selected i) :
    Fintype.card incidence.Position = incidence.arc.length := by
  classical
  calc
    Fintype.card incidence.Position =
        Fintype.card {d : Delta.toCombMap.Dart // d ∈ incidence.arc.darts} :=
      Fintype.card_congr incidence.positionEquivArcDarts
    _ = Fintype.card (Fin incidence.arc.darts.length) := by
      exact Fintype.card_congr
        ((incidence.arc_darts_nodup.getEquiv incidence.arc.darts).symm)
    _ = incidence.arc.length := by
      rw [Fintype.card_fin, incidence.arc.darts_length]

end CellIncidence

/-- The singleton cyclic arc at one actual dart position. -/
def singletonArc
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    {i : Fin Delta.rCellCount}
    (position : Fin (cellDarts Delta i).length) :
    CyclicArc (cellDarts Delta i) where
  start := ⟨position.1, lt_trans position.2 (Nat.lt_succ_self _)⟩
  length := 1
  length_le := Nat.one_le_iff_ne_zero.mpr fun hzero => by
    rw [hzero] at position
    exact Fin.elim0 position

/-- Classification of the dart at one cyclic position.  A bound classifier
includes the selected incidence whose stored cyclic arc contains that dart. -/
inductive CellDartClass
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta))
    (i : Fin Delta.rCellCount)
    (position : Fin (cellDarts Delta i).length) : Type (max u w v)
  | bound (incidence : CellIncidence selected i)
      (dart_mem : (cellDarts Delta i).get position ∈ incidence.arc.darts)
  | unbound

namespace CellDartClass

/-- The cyclic base position of a classified singleton dart. -/
def arc
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    {position : Fin (cellDarts Delta i).length}
    (_classification : CellDartClass selected i position) :
    CyclicArc (cellDarts Delta i) := singletonArc position

/-- Kind of a classified positioned dart. -/
noncomputable def kind
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    {position : Fin (cellDarts Delta i).length}
    (classification : CellDartClass selected i position) : CellArcKind :=
  match classification with
  | .bound incidence _ => incidence.kind
  | .unbound => CellArcKind.unbound

end CellDartClass

/-- A complete cyclic classification of one relator-cell boundary. -/
structure CellBoundaryPartition
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta))
    (i : Fin Delta.rCellCount) where
  classify : ∀ position : Fin (cellDarts Delta i).length,
    CellDartClass selected i position

namespace CellBoundaryPartition

/-- Classify a dart as bound exactly when some selected incidence contains it.
The candidate and side are chosen from a finite type, but no ordering choice
affects any of the three resulting length totals. -/
noncomputable def canonical
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta))
    (i : Fin Delta.rCellCount) : CellBoundaryPartition selected i where
  classify := fun position => by
    by_cases hbound : ∃ incidence : CellIncidence selected i,
        (cellDarts Delta i).get position ∈ incidence.arc.darts
    · exact CellDartClass.bound (Classical.choose hbound)
        (Classical.choose_spec hbound)
    · exact CellDartClass.unbound

/-- The canonical classifier makes every cell boundary partition inhabited. -/
theorem nonempty
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta))
    (i : Fin Delta.rCellCount) :
    Nonempty (CellBoundaryPartition selected i) :=
  ⟨canonical selected i⟩

/-- Number of boundary darts of one kind. -/
noncomputable def kindLength
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    (partition : CellBoundaryPartition selected i) (kind : CellArcKind) : ℕ :=
  (Finset.univ.filter fun position => (partition.classify position).kind = kind).card

/-- The three classifications partition the number of actual dart positions. -/
theorem cellDarts_length_eq_kindLengths
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    {i : Fin Delta.rCellCount}
    (partition : CellBoundaryPartition selected i) :
    (cellDarts Delta i).length =
      partition.kindLength CellArcKind.exterior +
      partition.kindLength CellArcKind.interior +
      partition.kindLength CellArcKind.unbound := by
  classical
  rw [← Fintype.card_fin (cellDarts Delta i).length]
  simp only [kindLength, Finset.card_eq_sum_ones]
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [show Fintype.card (Fin (cellDarts Delta i).length) =
      ∑ _position : Fin (cellDarts Delta i).length, 1 by simp]
  apply Finset.sum_congr rfl
  intro position _
  cases (partition.classify position).kind <;> simp

/-- The dart cycle of an indexed cell has the length of its relator word. -/
theorem cellDarts_length_eq_word_length
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (i : Fin Delta.rCellCount) :
    (cellDarts Delta i).length = (cell Delta i).word.length := by
  have hlength := congrArg List.length (dartWord_cellDarts Delta i)
  simpa only [dartWord, List.length_map] using hlength

/-- Exterior, interior, and unbound positioned darts partition the cell
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
  rw [← cellDarts_length_eq_word_length Delta i]
  exact partition.cellDarts_length_eq_kindLengths

end CellBoundaryPartition

/-- Canonical positioned boundary partitions for all relator cells of one
selected embedded family. -/
noncomputable def DiagramBoundaryPartition
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta)) :=
  ∀ i : Fin Delta.rCellCount, CellBoundaryPartition selected i

/-- The canonical diagram partition exists for every selected family. -/
noncomputable def canonicalDiagramPartition
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Candidate D eps Delta)) :
    DiagramBoundaryPartition selected :=
  fun i => CellBoundaryPartition.canonical selected i

namespace DiagramBoundaryPartition

/-- Real weight of one class of positioned cell darts. -/
noncomputable def kindWeight
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    (partition : DiagramBoundaryPartition selected)
    (kind : CellArcKind) (i : Fin Delta.rCellCount) : ℝ :=
  (partition i).kindLength kind

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
  exact_mod_cast (partition i).perimeter_eq_kindLengths

/-- Total number of unbound cell-boundary darts. -/
noncomputable def unboundTotal
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {selected : Finset (Candidate D eps Delta)}
    (partition : DiagramBoundaryPartition selected) : ℕ :=
  ∑ i : Fin Delta.rCellCount,
    (partition i).kindLength CellArcKind.unbound

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
