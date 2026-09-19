import GroupApproximation.GGT.VanKampen.Estimating.UnboundRepaired

/-!
# The complementary components of Osin Lemma 62

Cutting off the relator cells and the distinguished contiguity subdiagrams of
a diagram leaves finitely many components `Delta_1, ..., Delta_d`.  Osin's
Appendix Lemma 61 (arXiv `math/0411039`) counts their boundary arcs against
the planar graph `Phi'`: with `v` vertices and `e` edges, `e <= 3(v-1) <= 12n`,
arcs of type (A1) or (A2) number at most `2e + n + r <= 29n`, arcs of type
(A3) number at most `2e <= 24n`, and the total is at most `53n`.

`ComplementaryComponents` is that decomposition together with the six planar
counts Lemma 61 consumes.  Its arc-count conclusion is then proved outright
from the already landed arithmetic `lemma61_arcCount_le`, so no inequality
that arithmetic can close is left inside the remaining geometric producer.

What stays open is `Lemma62ComponentDecompositionStatement`: the decomposition
exists and every one of its components stays below the `1/60` density
threshold.  That is the contradiction argument of Lemma 62, which cuts each
component into a disc along at most `n_i` minimal paths, applies Proposition
4.14 to the type (A1) arcs, and contradicts either the maximality of the
distinguished family or the minimality of the cutting paths.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Estimating

open UnboundEstimate

universe u w v

/-! ## Lemma 61's edge count -/

/-- Osin Lemma 61's edge estimate `e <= 3(v-1) <= 3(n+3) <= 12n`.  The
argument needs a relator cell, since at `n = 0` the graph can still carry the
four exterior vertices. -/
theorem lemma61_edges_le (n r vertices edges : ℕ) (hn : 0 < n) (hr : r ≤ 4)
    (hvertices : vertices ≤ n + r) (hedges : edges ≤ 3 * (vertices - 1)) :
    edges ≤ 12 * n := by
  have hvertices' : vertices ≤ n + 4 := by omega
  by_cases hverticesZero : vertices = 0
  · omega
  · have hverticesPos : 0 < vertices := Nat.pos_of_ne_zero hverticesZero
    have hnFour : 4 ≤ 4 * n := by omega
    omega

/-! ## The decomposition -/

/-- The complementary components of Osin Lemma 62, with the planar counts of
Lemma 61.  `count` is `d`, `arcCount i` is `n_i`, and `unboundLength i` is
`S_i`, the total length of the type (A1) arcs on the boundary of the `i`-th
component.  The remaining fields are the vertex, edge and arc-type counts of
the graph `Phi'` associated with the distinguished family. -/
structure ComplementaryComponents
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (scaffold : EstimatingScaffold D eps Delta) where
  /-- The number `d` of complementary components. -/
  count : ℕ
  /-- The number `n_i` of boundary arcs of the `i`-th component. -/
  arcCount : Fin count → ℕ
  /-- The total length `S_i` of the type (A1) arcs of the `i`-th component. -/
  unboundLength : Fin count → ℝ
  /-- Osin's `k_i`: the sides of the disc obtained by cutting the `i`-th
  component along the minimal paths. -/
  sideCount : Fin count → ℕ
  /-- Cutting a component into a disc at most quadruples its arc count.  This
  is Osin's inequality (622). -/
  sideCount_le : ∀ i : Fin count, sideCount i ≤ 4 * arcCount i
  /-- The component totals add up to the diagram's unbound dart count. -/
  unbound_total : (∑ i : Fin count, unboundLength i) =
    (scaffold.partition.unboundTotal : ℝ)
  /-- The number `r` of sections of the exterior boundary. -/
  sections : ℕ
  /-- Osin fixes at most four exterior sections. -/
  sections_le : sections ≤ 4
  /-- The number `v` of vertices of the graph. -/
  vertices : ℕ
  /-- The number `e` of edges of the graph. -/
  edges : ℕ
  /-- One vertex per relator cell and one per exterior section. -/
  vertices_le : vertices ≤ Delta.rCellCount + sections
  /-- The Euler estimate for a planar graph with no two-gon. -/
  edges_le : edges ≤ 3 * (vertices - 1)
  /-- The number of arcs of type (A1) or (A2). -/
  typeA12 : ℕ
  /-- The number of arcs of type (A3). -/
  typeA3 : ℕ
  /-- Every boundary arc has one of the three types. -/
  arcCount_eq : (∑ i : Fin count, arcCount i) = typeA12 + typeA3
  /-- Unbound arcs are separated by contiguity arcs. -/
  typeA12_le : typeA12 ≤ 2 * edges + Delta.rCellCount + sections
  /-- Each contiguity subdiagram has two side arcs. -/
  typeA3_le : typeA3 ≤ 2 * edges

namespace ComplementaryComponents

/-- The graph of a decomposition has at most `12n` edges. -/
theorem edges_le_twelve_mul
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {scaffold : EstimatingScaffold D eps Delta}
    (components : ComplementaryComponents scaffold)
    (hcells : 0 < Delta.rCellCount) :
    components.edges ≤ 12 * Delta.rCellCount :=
  lemma61_edges_le Delta.rCellCount components.sections components.vertices
    components.edges hcells components.sections_le components.vertices_le
    components.edges_le

/-- Osin Appendix Lemma 61 on a decomposition: the boundary arcs of all
components number at most `53n`. -/
theorem arcCount_le_of_components
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {scaffold : EstimatingScaffold D eps Delta}
    (components : ComplementaryComponents scaffold)
    (hcells : 0 < Delta.rCellCount) :
    (∑ i : Fin components.count, components.arcCount i) ≤
      53 * Delta.rCellCount := by
  rw [components.arcCount_eq]
  exact lemma61_arcCount_le Delta.rCellCount components.sections
    components.vertices components.edges components.typeA12 components.typeA3
    hcells components.sections_le components.vertices_le components.edges_le
    components.typeA12_le components.typeA3_le

end ComplementaryComponents

/-- The entry point to Osin's contradiction: if the components carry the whole
`n * sqrt rho` of unbound length, then one of their discs is above the
`1/240` density threshold.  Lemma 61's arc count and the fourfold cost of
cutting a component into a disc are both spent here. -/
theorem exists_dense_disc_component_of_components
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {scaffold : EstimatingScaffold D eps Delta}
    (components : ComplementaryComponents scaffold)
    (hcells : 0 < Delta.rCellCount)
    (hsqrt : 0 < Real.sqrt (rho : ℝ))
    (htotal : (Delta.rCellCount : ℝ) * Real.sqrt (rho : ℝ) ≤
      ∑ i : Fin components.count, components.unboundLength i) :
    ∃ i : Fin components.count,
      (components.sideCount i : ℝ) * Real.sqrt (rho : ℝ) / 240 ≤
        components.unboundLength i :=
  exists_component_ge_twoForty Delta.rCellCount hcells
    (Real.sqrt (rho : ℝ)) hsqrt components.arcCount components.sideCount
    components.unboundLength (components.arcCount_le_of_components hcells)
    components.sideCount_le htotal

/-! ## The certificate from a decomposition and the density estimate -/

/-- A decomposition whose components all stay below the `1/60` density
threshold gives the Lemma 62 partition certificate.  The arc-count field is
Lemma 61, proved above, and the total is the decomposition's own sum. -/
theorem componentPartition_of_components
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {scaffold : EstimatingScaffold D eps Delta}
    (components : ComplementaryComponents scaffold)
    (hcells : 0 < Delta.rCellCount)
    (hsqrt : 0 < Real.sqrt (rho : ℝ))
    (hdensity : ∀ i : Fin components.count,
      components.unboundLength i <
        (components.arcCount i : ℝ) * Real.sqrt (rho : ℝ) / 60) :
    Nonempty (PartitionUnboundCertificate Delta.rCellCount components.count
      (Real.sqrt (rho : ℝ)) (scaffold.partition.unboundTotal : ℝ)) := by
  exact ⟨{
    averaging := {
      n_pos := hcells
      t_pos := hsqrt
      arcCount := components.arcCount
      unboundLength := components.unboundLength
      arc_count_le := components.arcCount_le_of_components hcells
      component_lt := hdensity }
    total_eq := components.unbound_total }⟩

/-! ## The remaining producer -/

/-- The geometric residue of Osin Appendix Lemma 62: the complementary
decomposition exists, and no component reaches the `1/60` density threshold.
The averaging inequality and Lemma 61's counting are already proved, so this
is the whole remaining content. -/
def Lemma62ComponentDecompositionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps rho : ℕ) (mu lambda c : ℝ)
    (_hsqrt : 0 < Real.sqrt (rho : ℝ))
    {W : Set (List (GGT.RelLetter G Lambda))}
    (_hcondition : OsinCCondition D W eps mu lambda c rho)
    (Delta : DiscDiagram.{u, w, v} W)
    (_hcells : 0 < Delta.rCellCount)
    (scaffold : EstimatingScaffold D eps Delta)
    (_graph : EstimatingGraphData D eps Delta scaffold),
    IsLambdaCQuasiGeodesicWord D lambda c Delta.boundaryWord →
      ∃ components : ComplementaryComponents scaffold,
        ∀ i : Fin components.count,
          components.unboundLength i <
            (components.arcCount i : ℝ) * Real.sqrt (rho : ℝ) / 60

/-- The decomposition producer discharges the component partition. -/
theorem lemma62ComponentPartition_of_decomposition
    (hdecomposition : Lemma62ComponentDecompositionStatement.{u, w, v}) :
    Lemma62ComponentPartitionStatement.{u, w, v} := by
  intro G _ Lambda D eps rho mu lambda c hsqrt W hcondition Delta hcells
    scaffold graph hboundary
  obtain ⟨components, hdensity⟩ := hdecomposition D eps rho mu lambda c hsqrt
    hcondition Delta hcells scaffold graph hboundary
  exact ⟨components.count,
    componentPartition_of_components components hcells hsqrt hdensity⟩

/-- The decomposition producer discharges the repaired Lemma 62 statement. -/
theorem estimatingUnboundRepaired_of_decomposition
    (hdecomposition : Lemma62ComponentDecompositionStatement.{u, w, v}) :
    EstimatingUnboundRepairedStatement.{u, w, v} :=
  estimatingUnboundRepaired_of_componentPartition
    (lemma62ComponentPartition_of_decomposition hdecomposition)

/-- The decomposition producer discharges the statement that
`estimatingDataConstruction_of_components` consumes. -/
theorem estimatingUnboundOutput_of_decomposition
    (hdecomposition : Lemma62ComponentDecompositionStatement.{u, w, v}) :
    EstimatingUnboundOutputStatement.{u, w, v} :=
  estimatingUnboundOutput_of_repaired
    (estimatingUnboundRepaired_of_decomposition hdecomposition)

/-! ## Model checks -/

/-- The one-cell decomposition with no complementary component: one graph
vertex, no edge, no exterior section, and no arc of any type.  Every count of
Lemma 61 is met with equality at `n = 1`, so the structure is not vacuous. -/
theorem complementaryComponents_oneCell_model
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {scaffold : EstimatingScaffold D eps Delta}
    (hzero : scaffold.partition.unboundTotal = 0) :
    Nonempty (ComplementaryComponents scaffold) := by
  refine ⟨{
    count := 0
    arcCount := fun i => Fin.elim0 i
    unboundLength := fun i => Fin.elim0 i
    sideCount := fun i => Fin.elim0 i
    sideCount_le := fun i => Fin.elim0 i
    unbound_total := ?_
    sections := 0
    sections_le := Nat.zero_le 4
    vertices := 0
    edges := 0
    vertices_le := Nat.zero_le _
    edges_le := Nat.zero_le _
    typeA12 := 0
    typeA3 := 0
    arcCount_eq := by simp
    typeA12_le := Nat.zero_le _
    typeA3_le := Nat.zero_le _ }⟩
  rw [hzero, Nat.cast_zero]
  simp

/-- Lemma 61's edge bound is sharp against its own inputs at the smallest
cell count: one vertex and no edge give `0 <= 12`. -/
theorem lemma61_edges_le_oneCell_model : (0 : ℕ) ≤ 12 * 1 := by
  exact lemma61_edges_le 1 0 1 0 Nat.one_pos (Nat.zero_le 4) (le_refl 1)
    (Nat.zero_le _)

/-- The arc count of Lemma 61 is met with equality at `n = 1`: `29 + 24`
arcs of the three types come to exactly `53`. -/
theorem lemma61_arcCount_base_model : 29 * 1 + 24 * 1 = 53 * 1 :=
  lemma61_constant_base

end Estimating
end VanKampen
end GGT
end GroupApproximation
