import GroupApproximation.GGT.VanKampen.CombMap
import Mathlib.Tactic.Linarith

/-!
# The planar contiguity count

This file isolates the finite weighted count in Osin's Appendix, Lemma 9.7.
The geometric construction supplies a planar estimating map, one vertex for
each relator cell, one edge for each interior contiguity region, and the
partition of every cell perimeter into exterior, interior, and uncovered
weight.  The argument here is purely finite:

* orienting the estimating edges with at most five owned by one vertex and
  charging each edge at most `2 * mu` times its owner's perimeter bounds the
  total interior weight by `10 * mu` times total perimeter;
* the replacement/merging stage bounds uncovered weight by `2 * mu` times
  total perimeter;
* after summing the cellwise partitions, some cell has exterior degree
  strictly greater than `1 - 13 * mu`, hence at least `1 - 23 * mu`.

No group, path, or diagram label occurs in the proof.  The fields below are
exactly the output the contiguity-system construction has to provide.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

universe u

/-- The finite accounting data on a contracted planar contiguity map. -/
structure ContiguityAccounting (mu : ℝ) where
  /-- The contracted map of relator cells and contiguity regions. -/
  map : CombMap
  planar : map.IsPlanar
  /-- The distinguished boundary face. -/
  outerFace : map.Face
  /-- Relator cells are indexed independently of the map's quotient type. -/
  cellCount : ℕ
  cellCount_pos : 0 < cellCount
  innerFace : Fin cellCount → map.Face
  innerFace_ne_outer : ∀ i, innerFace i ≠ outerFace
  innerFace_injective : Function.Injective innerFace
  /-- The perimeter and its three parts. -/
  perimeter : Fin cellCount → ℝ
  exteriorWeight : Fin cellCount → ℝ
  interiorWeight : Fin cellCount → ℝ
  uncoveredWeight : Fin cellCount → ℝ
  perimeter_pos : ∀ i, 0 < perimeter i
  exteriorWeight_nonneg : ∀ i, 0 ≤ exteriorWeight i
  interiorWeight_nonneg : ∀ i, 0 ≤ interiorWeight i
  uncoveredWeight_nonneg : ∀ i, 0 ≤ uncoveredWeight i
  partition : ∀ i,
    perimeter i = exteriorWeight i + interiorWeight i + uncoveredWeight i
  /-- Interior contiguity edges and the five-owner orientation. -/
  ContiguityEdge : Type u
  contiguityEdgeFintype : Fintype ContiguityEdge
  owner : ContiguityEdge → Fin cellCount
  owner_fiber : ∀ i : Fin cellCount,
    ∃ edges : Finset ContiguityEdge,
      (∀ edge, edge ∈ edges ↔ owner edge = i) ∧ edges.card ≤ 5
  edgeWeight : ContiguityEdge → ℝ
  edgeWeight_nonneg : ∀ edge, 0 ≤ edgeWeight edge
  edgeWeight_le_owner : ∀ edge,
    edgeWeight edge ≤ 2 * mu * perimeter (owner edge)
  interiorWeight_sum :
    (∑ i : Fin cellCount, interiorWeight i) =
      ∑ edge : ContiguityEdge, edgeWeight edge
  /-- The Appendix replacement and merging budget. -/
  uncovered_total_le :
    (∑ i : Fin cellCount, uncoveredWeight i) ≤
      2 * mu * ∑ i : Fin cellCount, perimeter i

attribute [instance] ContiguityAccounting.contiguityEdgeFintype

namespace ContiguityAccounting

/-- The planar estimating map has the degree-five deletion vertex whenever
its face cycles have degree at least three.  The geometric construction uses
this theorem successively after deleting vertices to build `owner_fiber`. -/
theorem exists_mapVertex_degree_le_five {mu : ℝ}
    (A : ContiguityAccounting mu)
    (hface : ∀ face : A.map.Face, 3 ≤ A.map.faceDegree face) :
    ∃ vertex : A.map.Vertex, A.map.vertexDegree vertex ≤ 5 :=
  A.map.exists_vertexDegree_le_five_of_faceDegree_ge_three A.planar hface

/-- The total perimeter is positive because there is at least one cell and
every cell perimeter is positive. -/
theorem total_perimeter_pos {mu : ℝ} (A : ContiguityAccounting mu) :
    0 < ∑ i : Fin A.cellCount, A.perimeter i := by
  have hnonempty : Nonempty (Fin A.cellCount) :=
    Fin.pos_iff_nonempty.mp A.cellCount_pos
  exact Finset.sum_pos (fun i _ => A.perimeter_pos i)
    (Finset.univ_nonempty_iff.mpr hnonempty)

/-- At most five edges are charged to one cell, and every such edge costs at
most twice `mu` times that cell's perimeter. -/
theorem owner_weight_le {mu : ℝ} (A : ContiguityAccounting mu)
    (hmu : 0 ≤ mu) (i : Fin A.cellCount) :
    ∑ edge ∈ (Finset.univ.filter fun edge : A.ContiguityEdge =>
        A.owner edge = i), A.edgeWeight edge
      ≤ 10 * mu * A.perimeter i := by
  classical
  obtain ⟨edges, hedge, hcard⟩ := A.owner_fiber i
  have hfilter :
      (Finset.univ.filter fun edge : A.ContiguityEdge => A.owner edge = i) =
        edges := by
    ext edge
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hedge edge).symm
  have hcharge : 0 ≤ 2 * mu * A.perimeter i := by
    exact mul_nonneg (mul_nonneg (by positivity) hmu)
      (le_of_lt (A.perimeter_pos i))
  calc
    ∑ edge ∈ (Finset.univ.filter fun edge : A.ContiguityEdge =>
          A.owner edge = i), A.edgeWeight edge
        ≤ ∑ _edge ∈ (Finset.univ.filter fun edge : A.ContiguityEdge =>
          A.owner edge = i), 2 * mu * A.perimeter i := by
      apply Finset.sum_le_sum
      intro edge hedgeMem
      have howner : A.owner edge = i := (Finset.mem_filter.mp hedgeMem).2
      rw [← howner]
      exact A.edgeWeight_le_owner edge
    _ = ((Finset.univ.filter fun edge : A.ContiguityEdge =>
          A.owner edge = i).card : ℝ) * (2 * mu * A.perimeter i) := by
      simp
    _ ≤ 5 * (2 * mu * A.perimeter i) := by
      apply mul_le_mul_of_nonneg_right _ hcharge
      rw [hfilter]
      exact_mod_cast hcard
    _ = 10 * mu * A.perimeter i := by ring

/-- Summing owner fibres gives the `10 * mu` interior-contiguity budget. -/
theorem interior_total_le {mu : ℝ} (A : ContiguityAccounting mu)
    (hmu : 0 ≤ mu) :
    (∑ i : Fin A.cellCount, A.interiorWeight i) ≤
      10 * mu * ∑ i : Fin A.cellCount, A.perimeter i := by
  classical
  rw [A.interiorWeight_sum]
  calc
    (∑ edge : A.ContiguityEdge, A.edgeWeight edge) =
        ∑ i : Fin A.cellCount,
          ∑ edge ∈ (Finset.univ.filter fun edge : A.ContiguityEdge =>
            A.owner edge = i), A.edgeWeight edge := by
      symm
      exact Finset.sum_fiberwise Finset.univ A.owner A.edgeWeight
    _ ≤ ∑ i : Fin A.cellCount, 10 * mu * A.perimeter i := by
      apply Finset.sum_le_sum
      intro i _
      exact A.owner_weight_le hmu i
    _ = 10 * mu * ∑ i : Fin A.cellCount, A.perimeter i := by
      rw [Finset.mul_sum]

/-- Summing the cellwise partitions partitions total perimeter. -/
theorem total_partition {mu : ℝ} (A : ContiguityAccounting mu) :
    (∑ i : Fin A.cellCount, A.perimeter i) =
      (∑ i : Fin A.cellCount, A.exteriorWeight i) +
      (∑ i : Fin A.cellCount, A.interiorWeight i) +
      (∑ i : Fin A.cellCount, A.uncoveredWeight i) := by
  calc
    (∑ i : Fin A.cellCount, A.perimeter i) =
        ∑ i : Fin A.cellCount,
          (A.exteriorWeight i + A.interiorWeight i) +
            A.uncoveredWeight i := by
      apply Finset.sum_congr rfl
      intro i _
      exact A.partition i
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

/-- Osin's weighted Euler/counting conclusion: some relator cell has exterior
degree strictly greater than `1 - 13 * mu`. -/
theorem exists_exterior_gt_thirteen {mu : ℝ}
    (A : ContiguityAccounting mu) (hmu : 0 < mu) :
    ∃ i : Fin A.cellCount,
      (1 - 13 * mu) * A.perimeter i < A.exteriorWeight i := by
  have hinterior := A.interior_total_le (le_of_lt hmu)
  have huncovered := A.uncovered_total_le
  have hpartition := A.total_partition
  have htotalPos := A.total_perimeter_pos
  have htotalExterior :
      (1 - 13 * mu) * (∑ i : Fin A.cellCount, A.perimeter i) <
        ∑ i : Fin A.cellCount, A.exteriorWeight i := by
    have hslack : 0 < mu * ∑ i : Fin A.cellCount, A.perimeter i :=
      mul_pos hmu htotalPos
    linarith
  by_contra hnone
  have hall : ∀ i : Fin A.cellCount,
      A.exteriorWeight i ≤ (1 - 13 * mu) * A.perimeter i := by
    intro i
    exact le_of_not_gt (fun hi => hnone ⟨i, hi⟩)
  have hsum : (∑ i : Fin A.cellCount, A.exteriorWeight i) ≤
      ∑ i : Fin A.cellCount, (1 - 13 * mu) * A.perimeter i := by
    apply Finset.sum_le_sum
    intro i _
    exact hall i
  rw [← Finset.mul_sum] at hsum
  linarith

/-- The source's strict `1 - 13 * mu` estimate implies the common interface's
weak `1 - 23 * mu` estimate. -/
theorem exists_exterior_ge_twentyThree {mu : ℝ}
    (A : ContiguityAccounting mu) (hmu : 0 < mu) :
    ∃ i : Fin A.cellCount,
      (1 - 23 * mu) * A.perimeter i ≤ A.exteriorWeight i := by
  obtain ⟨i, hi⟩ := A.exists_exterior_gt_thirteen hmu
  refine ⟨i, ?_⟩
  have hcoeff : 1 - 23 * mu ≤ 1 - 13 * mu := by linarith
  have hscaled : (1 - 23 * mu) * A.perimeter i ≤
      (1 - 13 * mu) * A.perimeter i :=
    mul_le_mul_of_nonneg_right hcoeff (le_of_lt (A.perimeter_pos i))
  exact le_trans hscaled (le_of_lt hi)

end ContiguityAccounting

/-! ## The one-cell complement calculation -/

/-- If an exterior arc has degree at least `1 - c`, its complementary arc has
degree at most `c`.  This small calculation is shared by the diagram count and
Hull's power correction. -/
theorem complement_le_of_exterior_fraction
    {perimeter exterior complement : ℕ} {c : ℝ}
    (hsplit : perimeter = exterior + complement)
    (hlarge : (1 - c) * (perimeter : ℝ) ≤ (exterior : ℝ)) :
    (complement : ℝ) ≤ c * (perimeter : ℝ) := by
  have hcast : (perimeter : ℝ) = (exterior : ℝ) + (complement : ℝ) := by
    exact_mod_cast hsplit
  linarith

/-- The calculation is sharp in the degenerate zero-perimeter model. -/
theorem complement_zero_model (c : ℝ) :
    ((0 : ℕ) : ℝ) ≤ c * ((0 : ℕ) : ℝ) := by simp

end VanKampen
end GGT
end GroupApproximation
