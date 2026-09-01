import GroupApproximation.GGT.VanKampen.Contiguity
import GroupApproximation.GGT.VanKampen.ContiguityCount
import GroupApproximation.GGT.HullSCLemma44ExteriorArc
import GroupApproximation.GGT.HullSCRelativeGreendlingerStatement
import Mathlib.Tactic.Linarith

/-!
# The relative Greendlinger estimate

This file formalizes the counting output of Osin's Appendix Lemma 9.7
(`Gr0`).  The estimating graph is represented by a planar combinatorial map.
A five-owner certificate assigns every edge to an incident vertex so that at
most five edges are assigned to each vertex.  This is the inductive form of
the fact that every simple planar graph has a vertex of degree at most five.
If an edge has weight at most `2 * mu` times its owner's weight, fibrewise
summation proves Osin's weighted bound

`sum edgeWeight <= 10 * mu * sum vertexWeight`.

An estimating system for a relative disc diagram partitions every relator
boundary into one chosen exterior contiguity arc, interior contiguity arcs,
and uncovered arcs.  The weighted graph controls the interior total by
`10 * mu`; the Appendix replacement and merging steps control the uncovered
total by `2 * mu`.  Summing the partitions and using `mu > 0` gives a cell
whose chosen exterior arc is longer than
`(1 - 13 * mu) * |boundary Pi|`.  This proves the weaker
`1 - 23 * mu` formulation requested by the common interface as well.

The remaining geometric inputs are named explicitly.  The specialized
`EstimatingSystemStatement` constructs the distinguished maximal contiguity
system on a short-boundary diagram.  The shared downstream interface is split
more finely into `RelativeDiscRealizationStatement` (the cactus construction)
and `EstimatingSystemSelectionStatement` (Osin's hyperbolicity-dependent
choice of constants and Appendix replacement/merging construction).  The
theorem `relativeGreendlinger` proves the exact proposition declared in
`HullSCRelativeGreendlingerStatement.lean` from those two constructions; all
subsequent weighted counting and certificate transfer is proved here.  The
final section also transfers the stronger `1 - 13 * mu` output to the older
`Lemma44LargeExteriorCell` structure.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

open GroupApproximation.HullSC
open GroupApproximation.WordMetric

universe u w

/-! ## The diagram estimating system -/

/-- The `i`-th relator cell in the stored boundary order. -/
def DiscDiagram.indexedCell
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram W) (i : Fin Delta.rCellCount) :
    RelatorCell Delta.toCombMap Delta.outerFace W :=
  Delta.relatorCells.get i

/-- The perimeter of an indexed relator cell. -/
def DiscDiagram.cellWeight
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram W) (i : Fin Delta.rCellCount) : ℝ :=
  ((Delta.indexedCell i).word.length : ℝ)

/-- Osin's distinguished contiguity system after the Appendix replacement
and merging operations.  There is at most one chosen exterior contiguity
region per cell; absent regions have weight zero. -/
structure EstimatingSystem
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (eps : ℕ) (mu : ℝ) (Delta : DiscDiagram W) where
  outer : ∀ i : Fin Delta.rCellCount,
    Option (BoundaryContiguity (D := D) (eps := eps) (Delta.indexedCell i))
  interiorWeight : Fin Delta.rCellCount → ℝ
  uncoveredWeight : Fin Delta.rCellCount → ℝ
  interiorWeight_nonneg : ∀ i, 0 ≤ interiorWeight i
  uncoveredWeight_nonneg : ∀ i, 0 ≤ uncoveredWeight i
  partition : ∀ i,
    Delta.cellWeight i =
      (match outer i with
        | none => 0
        | some Gamma => (Gamma.region.secondArc.length : ℝ)) +
      interiorWeight i + uncoveredWeight i
  totalWeight_pos : 0 < ∑ i : Fin Delta.rCellCount, Delta.cellWeight i
  interior_total_le :
    (∑ i : Fin Delta.rCellCount, interiorWeight i) ≤
      10 * mu * ∑ i : Fin Delta.rCellCount, Delta.cellWeight i
  uncovered_total_le :
    (∑ i : Fin Delta.rCellCount, uncoveredWeight i) ≤
      2 * mu * ∑ i : Fin Delta.rCellCount, Delta.cellWeight i

namespace EstimatingSystem

/-- Length of the chosen exterior contiguity arc, or zero if it is absent. -/
def outerWeight
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {mu : ℝ} {Delta : DiscDiagram W}
    (S : EstimatingSystem D eps mu Delta) (i : Fin Delta.rCellCount) : ℝ :=
  match S.outer i with
  | none => 0
  | some Gamma => (Gamma.region.secondArc.length : ℝ)

/-- Summing the cellwise partitions partitions the total perimeter. -/
theorem total_partition
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {mu : ℝ} {Delta : DiscDiagram W}
    (S : EstimatingSystem D eps mu Delta) :
    (∑ i : Fin Delta.rCellCount, Delta.cellWeight i) =
      (∑ i : Fin Delta.rCellCount, S.outerWeight i) +
      (∑ i : Fin Delta.rCellCount, S.interiorWeight i) +
      (∑ i : Fin Delta.rCellCount, S.uncoveredWeight i) := by
  calc
    (∑ i : Fin Delta.rCellCount, Delta.cellWeight i) =
        ∑ i : Fin Delta.rCellCount, ((S.outerWeight i +
          S.interiorWeight i) + S.uncoveredWeight i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact S.partition i
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

/-- The global budgets leave more than `1 - 13 * mu` of the total perimeter
on chosen exterior arcs. -/
theorem total_exterior_gt
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {mu : ℝ} {Delta : DiscDiagram W}
    (hmu : 0 < mu) (S : EstimatingSystem D eps mu Delta) :
    (1 - 13 * mu) *
        (∑ i : Fin Delta.rCellCount, Delta.cellWeight i) <
      ∑ i : Fin Delta.rCellCount, S.outerWeight i := by
  have hpartition := S.total_partition
  have hmupos : 0 < mu *
      (∑ i : Fin Delta.rCellCount, Delta.cellWeight i) :=
    mul_pos hmu S.totalWeight_pos
  linarith [S.interior_total_le, S.uncovered_total_le]

/-- Some cell has one exterior contiguity arc longer than
`(1 - 13 * mu)` times its perimeter. -/
theorem exists_large_exterior
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {mu : ℝ} {Delta : DiscDiagram W}
    (hmu : 0 < mu) (hmu_upper : mu ≤ 1 / 16)
    (S : EstimatingSystem D eps mu Delta) :
    ∃ (i : Fin Delta.rCellCount)
      (Gamma : BoundaryContiguity (D := D) (eps := eps) (Delta.indexedCell i)),
      S.outer i = some Gamma ∧
      (1 - 13 * mu) * Delta.cellWeight i <
        (Gamma.region.secondArc.length : ℝ) := by
  have htotal := S.total_exterior_gt hmu
  have hindex : ∃ i : Fin Delta.rCellCount,
      (1 - 13 * mu) * Delta.cellWeight i < S.outerWeight i := by
    by_contra hnone
    have hall : ∀ i : Fin Delta.rCellCount,
        S.outerWeight i ≤ (1 - 13 * mu) * Delta.cellWeight i := by
      intro i
      exact le_of_not_gt (fun hi => hnone ⟨i, hi⟩)
    have hsum : (∑ i : Fin Delta.rCellCount, S.outerWeight i) ≤
        ∑ i : Fin Delta.rCellCount,
          (1 - 13 * mu) * Delta.cellWeight i := by
      apply Finset.sum_le_sum
      intro i _
      exact hall i
    have hfactor : (∑ i : Fin Delta.rCellCount,
        (1 - 13 * mu) * Delta.cellWeight i) =
        (1 - 13 * mu) *
          ∑ i : Fin Delta.rCellCount, Delta.cellWeight i := by
      rw [Finset.mul_sum]
    rw [hfactor] at hsum
    linarith
  obtain ⟨i, hi⟩ := hindex
  have hcoeff : 0 ≤ 1 - 13 * mu := by linarith
  cases houter : S.outer i with
  | none =>
      rw [outerWeight, houter] at hi
      have hcell : 0 ≤ Delta.cellWeight i := by positivity
      have : 0 ≤ (1 - 13 * mu) * Delta.cellWeight i :=
        mul_nonneg hcoeff hcell
      linarith
  | some Gamma =>
      refine ⟨i, Gamma, houter, ?_⟩
      rwa [outerWeight, houter] at hi

end EstimatingSystem

/-! ## The named Greendlinger statements -/

/-- The single geometric estimate left after local piece control: every
eligible reduced diagram admits the Appendix estimating system. -/
def EstimatingSystemStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    (eps rho : ℕ) (mu : ℝ) (Delta : DiscDiagram W),
    RelWord.IsLemma44Input D W eps mu rho →
    0 < mu → mu ≤ 1 / 52 → 0 < rho →
    Delta.Reduced → 0 < Delta.rCellCount →
    Delta.boundaryWord.length < rho →
    Nonempty (EstimatingSystem D eps mu Delta)

/-- Osin's relative Greendlinger conclusion in the common diagram interface.
The strict source estimate implies the stated weak degree bound. -/
def DiagramRelativeGreendlingerStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    (eps rho : ℕ) (mu : ℝ) (Delta : DiscDiagram W),
    RelWord.IsLemma44Input D W eps mu rho →
    0 < mu → mu ≤ 1 / 52 → 0 < rho →
    Delta.Reduced → 0 < Delta.rCellCount →
    Delta.boundaryWord.length < rho →
    ∃ (i : Fin Delta.rCellCount)
      (Gamma : BoundaryContiguity (D := D) (eps := eps) (Delta.indexedCell i)),
      1 - 23 * mu ≤ Gamma.degree

/-- Osin Lemma 9.7 (`Gr0`), from the distinguished estimating-system
construction. -/
theorem diagramRelativeGreendlinger
    (hestimate : EstimatingSystemStatement.{u, w}) :
    DiagramRelativeGreendlingerStatement.{u, w} := by
  intro G _ Lambda D W eps rho mu Delta hsc hmu hmuUpper hrho hred hcells hshort
  obtain ⟨S⟩ := hestimate D W eps rho mu Delta hsc hmu hmuUpper hrho
    hred hcells hshort
  have hmuSixteen : mu ≤ 1 / 16 := le_trans hmuUpper (by norm_num)
  obtain ⟨i, Gamma, _, hlarge⟩ := S.exists_large_exterior hmu hmuSixteen
  refine ⟨i, Gamma, ?_⟩
  have hlenNat : 0 < (Delta.indexedCell i).word.length :=
    lt_of_lt_of_le hrho
      (hsc.long (Delta.indexedCell i).word (Delta.indexedCell i).word_mem)
  have hlen : (0 : ℝ) < ((Delta.indexedCell i).word.length : ℝ) := by
    exact_mod_cast hlenNat
  have hcoeff : 1 - 23 * mu ≤ 1 - 13 * mu := by linarith
  have hscaled : (1 - 23 * mu) * Delta.cellWeight i ≤
      (1 - 13 * mu) * Delta.cellWeight i :=
    mul_le_mul_of_nonneg_right hcoeff (by positivity)
  have hstrict : (1 - 23 * mu) * Delta.cellWeight i <
      (Gamma.region.secondArc.length : ℝ) :=
    lt_of_le_of_lt hscaled hlarge
  rw [BoundaryContiguity.degree, le_div_iff₀ hlen]
  exact le_of_lt hstrict

/-- With an empty relator family, the estimating-system input has no positive
cell-count case.  This model test checks that the named geometric estimate is
not asserting the existence of cells. -/
theorem estimatingSystem_emptyFamilyModel
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps rho : ℕ) (mu : ℝ)
    (Delta : DiscDiagram (∅ : Set (List (GGT.RelLetter G Lambda))))
    (hcells : 0 < Delta.rCellCount) :
    Nonempty (EstimatingSystem D eps mu Delta) := by
  have hnil : Delta.relatorCells = [] := by
    cases hcellsList : Delta.relatorCells with
    | nil => exact hcellsList
    | cons C cells =>
        have hmem : C ∈ Delta.relatorCells := by rw [hcellsList]; simp
        exact (C.word_mem.elim)
  rw [DiscDiagram.rCellCount, hnil, List.length_nil] at hcells
  omega

/-! ## The common certificate interface -/

/-- A planar realization of the common reduced-diagram input used by the
Lemma 4.4 and Lemma 4.9 lanes.  The equivalence identifies every algebraic
cell with its actual planar face, including its oriented boundary word. -/
structure RelativeDiscRealization
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R) where
  diagram : DiscDiagram W
  cellIndex : Fin Z.cells.length ≃ Fin diagram.rCellCount
  boundaryWord_eq : diagram.boundaryWord =
    Z.boundaryWord.map (GGT.RelLetter.base : G → GGT.RelLetter G Lambda)
  cellWord_eq : ∀ i : Fin Z.cells.length,
    (diagram.indexedCell (cellIndex i)).word = (Z.cells.get i).relator
  reduced : diagram.Reduced

/-- The explicit cactus construction required before the estimating-graph
argument: every common algebraic reduced diagram has a planar realization. -/
def RelativeDiscRealizationStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda))) (R : ℕ)
    (Z : HullSC.RelativeReducedDiagram D W R),
    Nonempty (RelativeDiscRealization Z)

/-- The hyperbolic-geometry part of Osin's Appendix chooses `eps` and the
initial relator threshold, then constructs the maximal estimating system on
each planar realization. -/
def EstimatingSystemSelectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda),
    D.IsHyperbolicallyEmbedded →
      ∀ mu : ℝ, 0 < mu → mu ≤ 1 / 16 →
        ∃ eps rho0 : ℕ, ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (GGT.RelLetter G Lambda))) (R : ℕ),
            RelWord.IsLemma44Input D W eps mu rho →
              ∀ (Z : HullSC.RelativeReducedDiagram D W R)
                (C : RelativeDiscRealization Z),
                Nonempty (EstimatingSystem D eps mu C.diagram)

/-- Convert a genuine planar boundary-contiguity subdiagram to the finite
certificate format shared by the downstream lanes. -/
theorem relativeBoundaryContiguity_of_disc
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R eps : ℕ}
    {Z : HullSC.RelativeReducedDiagram D W R}
    (C : RelativeDiscRealization Z) (i : Fin Z.cells.length)
    (Gamma : BoundaryContiguity (D := D) (eps := eps)
      (C.diagram.indexedCell (C.cellIndex i))) :
    HullSC.RelativeBoundaryContiguity D eps Z.boundaryWord
      (Z.cells.get i).relator := by
  have hrelative :
      Z.boundaryWord.map
          (GGT.RelLetter.base : G → GGT.RelLetter G Lambda) =
        Gamma.boundaryBefore ++ Gamma.region.firstArc ++
          Gamma.boundaryAfter :=
    C.boundaryWord_eq.symm.trans Gamma.boundary_decomposition
  have hgroup : Z.boundaryWord =
      Gamma.boundaryBefore.map GGT.RelLetter.val ++
        Gamma.region.firstArc.map GGT.RelLetter.val ++
        Gamma.boundaryAfter.map GGT.RelLetter.val := by
    have hmap := congrArg (List.map GGT.RelLetter.val) hrelative
    simpa only [List.map_append, List.map_map, Function.comp_apply,
      HullSC.val_base] using hmap
  exact
    { exterior := Gamma.region.secondArc
      remainder := Gamma.sourceRemainder
      relator_decomposition :=
        (C.cellWord_eq i).symm.trans Gamma.source_decomposition
      boundaryBefore := Gamma.boundaryBefore.map GGT.RelLetter.val
      boundaryArc := Gamma.region.firstArc.map GGT.RelLetter.val
      boundaryAfter := Gamma.boundaryAfter.map GGT.RelLetter.val
      boundary_decomposition := hgroup
      leftSide := Gamma.region.leftSide
      rightSide := Gamma.region.rightSide
      leftSide_admissible := Gamma.region.leftSide_admissible
      rightSide_admissible := Gamma.region.rightSide_admissible
      leftSide_short := Gamma.region.leftSide_length_le
      rightSide_short := Gamma.region.rightSide_length_le
      exterior_value := by
        change GGT.RelLetter.listVal Gamma.region.secondArc =
          Gamma.region.leftConnector *
            (Gamma.region.firstArc.map GGT.RelLetter.val).prod *
            Gamma.region.rightConnector
        exact Gamma.region.arcs_value }

/-- The numerical estimating-system theorem packages directly into the
common finite relative Greendlinger certificate. -/
theorem relativeDiagramCertificate_of_estimatingSystem
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R eps : ℕ} {mu : ℝ}
    {Z : HullSC.RelativeReducedDiagram D W R}
    (hmu : 0 < mu) (hmuUpper : mu ≤ 1 / 16)
    (C : RelativeDiscRealization Z)
    (S : EstimatingSystem D eps mu C.diagram) :
    Nonempty (HullSC.RelativeDiagramCertificate D W eps mu Z) := by
  obtain ⟨j, Gamma, houter, hlarge⟩ :=
    S.exists_large_exterior hmu hmuUpper
  let i : Fin Z.cells.length := C.cellIndex.symm j
  have hij : C.cellIndex i = j := C.cellIndex.apply_symm_apply j
  cases hij
  let B : HullSC.RelativeBoundaryContiguity D eps Z.boundaryWord
      (Z.cells.get i).relator :=
    relativeBoundaryContiguity_of_disc C i Gamma
  refine ⟨{
      boundaryWord := Z.boundaryWord
      boundaryWord_eq := rfl
      cellLabel := fun k => (Z.cells.get k).relator
      cellLabel_eq := fun _ => rfl
      cellLabel_mem := fun k => (Z.cells.get k).relator_mem
      contiguity := fun k =>
        (S.outer (C.cellIndex k)).map
          (relativeBoundaryContiguity_of_disc C k)
      largeCell := ⟨i, B, ?_, ?_⟩ }⟩
  · dsimp [B]
    rw [houter]
    rfl
  · have hwordLength : C.diagram.cellWeight (C.cellIndex i) =
        ((Z.cells.get i).relator.length : ℝ) := by
      rw [DiscDiagram.cellWeight, C.cellWord_eq i]
    have hcoeff : 1 - 23 * mu ≤ 1 - 13 * mu := by linarith
    have hscaled :
        (1 - 23 * mu) * ((Z.cells.get i).relator.length : ℝ) ≤
          (1 - 13 * mu) * ((Z.cells.get i).relator.length : ℝ) :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)
    rw [hwordLength] at hlarge
    exact le_trans hscaled (le_of_lt hlarge)

/-- This module's public statement is definitionally the exact proposition
declared by the shared Hull interface. -/
def RelativeGreendlingerStatement : Prop :=
  HullSC.RelativeGreendlingerStatement.{u, w}

/-- Osin's relative Greendlinger lemma, reduced to the two explicit geometric
constructions and with all numerical counting completed in this file. -/
theorem relativeGreendlinger
    (hrealize : RelativeDiscRealizationStatement.{u, w})
    (hestimate : EstimatingSystemSelectionStatement.{u, w}) :
    RelativeGreendlingerStatement.{u, w} := by
  intro G _ Lambda D hemb mu hmu hmuUpper
  obtain ⟨eps, rho0, hsystem⟩ := hestimate D hemb mu hmu hmuUpper
  refine ⟨eps, rho0, ?_⟩
  intro rho hrho W R hsc Z
  obtain ⟨C⟩ := hrealize D W R Z
  obtain ⟨S⟩ := hsystem rho hrho W R hsc Z C
  exact relativeDiagramCertificate_of_estimatingSystem hmu hmuUpper C S

/-- The common realization frontier is vacuous over the empty family in
every group, matching the two-point and free-group model tests in the shared
interface. -/
theorem relativeDiscRealization_emptyFamilyModel
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (R : ℕ)
    (Z : HullSC.RelativeReducedDiagram D
      (∅ : Set (List (GGT.RelLetter G Lambda))) R) :
    Nonempty (RelativeDiscRealization Z) := by
  exact False.elim ((HullSC.no_relativeReducedDiagram_emptyFamily D R).false Z)

/-! ## Transfer to Hull's exact exterior-cell interface -/

/-- A boundary contiguity arc on a cactus realization produces the exact
`Lemma44LargeExteriorCell` consumed by Hull's Lemma 4.4. -/
theorem largeExteriorCell_of_boundaryContiguity
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {R eps : ℕ} {mu : ℝ}
    {Z : HullSC.Lemma44OrientedRelatorDiagram A W R}
    (C : CactusRealization Z)
    {i : Fin C.diagram.rCellCount}
    (Gamma : BoundaryContiguity (D := D) (eps := eps)
      (C.diagram.indexedCell i))
    (hlarge : (1 - 13 * mu) *
      ((C.diagram.indexedCell i).word.length : ℝ) <
        (Gamma.region.secondArc.length : ℝ)) :
    HullSC.Lemma44LargeExteriorCell D W eps mu
      Z.toLemma44ReducedRelatorDiagram := by
  have hrelative :
      Z.boundaryWord.map
          (GGT.RelLetter.base : G → GGT.RelLetter G Lambda) =
        Gamma.boundaryBefore ++ Gamma.region.firstArc ++
          Gamma.boundaryAfter :=
    C.boundaryWord_eq.symm.trans Gamma.boundary_decomposition
  have hgroup : Z.boundaryWord =
      Gamma.boundaryBefore.map GGT.RelLetter.val ++
        Gamma.region.firstArc.map GGT.RelLetter.val ++
        Gamma.boundaryAfter.map GGT.RelLetter.val := by
    have hmap := congrArg (List.map GGT.RelLetter.val) hrelative
    simpa only [List.map_append, List.map_map, Function.comp_apply,
      HullSC.val_base] using hmap
  let boundaryArc : HullSC.Lemma44BoundaryArc
      Z.toLemma44RelatorDiagramBoundary :=
    { before := Gamma.boundaryBefore.map GGT.RelLetter.val
      arc := Gamma.region.firstArc.map GGT.RelLetter.val
      after := Gamma.boundaryAfter.map GGT.RelLetter.val
      decomposition := hgroup }
  exact
    { relator := (C.diagram.indexedCell i).word
      relator_mem := (C.diagram.indexedCell i).word_mem
      exterior := Gamma.region.secondArc
      remainder := Gamma.sourceRemainder
      relator_decomposition := Gamma.source_decomposition
      exterior_large := hlarge
      boundaryArc := boundaryArc
      leftConnector := Gamma.region.leftConnector
      rightConnector := Gamma.region.rightConnector
      leftConnector_short := Gamma.region.leftConnector_short
      rightConnector_short := Gamma.region.rightConnector_short
      exterior_value := by
        change GGT.RelLetter.listVal Gamma.region.secondArc =
          Gamma.region.leftConnector *
            (Gamma.region.firstArc.map GGT.RelLetter.val).prod *
            Gamma.region.rightConnector
        exact Gamma.region.arcs_value }

/-- The exact theorem consumed by the Hull 4.4 lane. -/
def HullRelativeGreendlingerStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    (W : Set (List (GGT.RelLetter G Lambda)))
    (R eps rho : ℕ) (mu : ℝ),
    RelWord.IsLemma44Input D W eps mu rho →
    0 < mu → mu ≤ 1 / 52 → 0 < rho → 2 * R < rho →
    ∀ Z : HullSC.Lemma44OrientedRelatorDiagram A W R,
      Nonempty (HullSC.Lemma44LargeExteriorCell D W eps mu
        Z.toLemma44ReducedRelatorDiagram)

/-- The cactus construction and estimating-system construction prove the
exact Hull exterior-cell statement. -/
theorem hullRelativeGreendlinger
    (hcactus : CactusRealizationStatement.{u, w})
    (hestimate : EstimatingSystemStatement.{u, w}) :
    HullRelativeGreendlingerStatement.{u, w} := by
  intro G _ Lambda D A W R eps rho mu hsc hmu hmuUpper hrho hR Z
  obtain ⟨C⟩ := hcactus Z
  have hred : C.diagram.Reduced := C.reduced
  have hcells : 0 < C.diagram.rCellCount := by
    rw [C.rCellCount_eq_area]
    exact Z.area_pos
  have hboundaryLength : C.diagram.boundaryWord.length = Z.boundaryWord.length := by
    rw [C.boundaryWord_eq, List.length_map]
  have hshort : C.diagram.boundaryWord.length < rho := by
    rw [hboundaryLength, Z.boundaryWord_geodesic]
    exact lt_of_le_of_lt Z.boundary_length_le hR
  obtain ⟨S⟩ := hestimate D W eps rho mu C.diagram hsc hmu hmuUpper hrho
    hred hcells hshort
  have hmuSixteen : mu ≤ 1 / 16 := le_trans hmuUpper (by norm_num)
  obtain ⟨i, Gamma, _, hlarge⟩ := S.exists_large_exterior hmu hmuSixteen
  exact ⟨largeExteriorCell_of_boundaryContiguity C Gamma hlarge⟩

end VanKampen
end GGT
end GroupApproximation
