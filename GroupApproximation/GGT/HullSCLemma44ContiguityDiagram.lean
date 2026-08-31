import GroupApproximation.GGT.HullSCLemma44ExteriorArc
import GroupApproximation.Sofic.NonCrossingDegreeBound

/-!
# The explicit relative contiguity-diagram seam in Hull's Lemma 4.4

The algebraic least-area certificate is not itself a planar diagram: equality
in the ambient group does not produce a free-cancellation matching.  This file
therefore records the smallest concrete planar object the remaining relative
van Kampen argument must construct, without asserting that such an object
exists.

Vertex `0` is the exterior boundary and vertex `i+1` is oriented relator cell
`i`.  Edges are maximal contiguity runs.  Their endpoint order and noncrossing
clauses are explicit, so the outerplanar degree theorem applies directly.
`Lemma44PlanarShellCertificate` is the local output still required from that
matching: a boundary-adjacent cell of degree at most four, hence at most three
interior runs, with the relative labels and short corner connectors exposed.

The final theorem proves that constructing these two objects for every reduced
oriented certificate closes the ball-injectivity half of Hull's Lemma 4.4.
No implication from ambient-group equality to planarity is assumed here.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-- The cell vertices of a relative contiguity diagram.  Vertex `0` is
reserved for the exterior boundary. -/
def lemma44CellVertices {G : Type u} [Group G] {Λ : Type w}
    {A : Alphabet G} {W : Set (List (GGT.RelLetter G Λ))} {R : ℕ}
    (Z : Lemma44OrientedRelatorDiagram A W R) : Finset ℕ :=
  (Finset.range (Z.cells.length + 1)).erase 0

/-- The explicit outerplanar dual skeleton of a relative contiguity diagram.
An edge is one maximal run between two distinct blocks, with the exterior
boundary treated as block `0`. -/
structure Lemma44RelativeContiguityDiagram
    {G : Type u} [Group G] {Λ : Type w}
    {A : Alphabet G} {W : Set (List (GGT.RelLetter G Λ))} {R : ℕ}
    (Z : Lemma44OrientedRelatorDiagram A W R) where
  edges : Finset (ℕ × ℕ)
  ordered : ∀ p ∈ edges, p.1 < p.2
  endpoints : ∀ p ∈ edges,
    p.1 ∈ Finset.range (Z.cells.length + 1) ∧
      p.2 ∈ Finset.range (Z.cells.length + 1)
  noncrossing : ∀ p ∈ edges, ∀ q ∈ edges,
    ¬ (p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2)

namespace Lemma44RelativeContiguityDiagram

/-- A reduced oriented diagram has at least one cell. -/
theorem cells_ne_nil
    {G : Type u} [Group G] {Λ : Type w}
    {A : Alphabet G} {W : Set (List (GGT.RelLetter G Λ))} {R : ℕ}
    (Z : Lemma44OrientedRelatorDiagram A W R) : Z.cells ≠ [] := by
  intro hnil
  have hlen := congrArg List.length Z.cell_values
  rw [hnil] at hlen
  simp only [List.length_nil, List.length_map] at hlen
  have hzero : Z.area = 0 := by
    rw [← Z.factors_length]
    exact hlen.symm
  exact (Nat.ne_of_gt Z.area_pos) hzero

/-- The cell-vertex set has exactly one vertex fewer than the full vertex set:
the omitted vertex is the exterior boundary. -/
theorem cellVertices_card_add_one
    {G : Type u} [Group G] {Λ : Type w}
    {A : Alphabet G} {W : Set (List (GGT.RelLetter G Λ))} {R : ℕ}
    (Z : Lemma44OrientedRelatorDiagram A W R) :
    (lemma44CellVertices Z).card + 1 =
      (Finset.range (Z.cells.length + 1)).card := by
  rw [lemma44CellVertices, Finset.card_erase_of_mem]
  · simp
  · simp

/-- The explicit noncrossing skeleton always has a relator-cell vertex meeting
at most four maximal runs.  This is the complete planar counting step; the
separate shell certificate records why the selected cell meets vertex `0` and
turns its other (at most three) runs into published pieces. -/
theorem exists_cell_degree_le_four
    {G : Type u} [Group G] {Λ : Type w}
    {A : Alphabet G} {W : Set (List (GGT.RelLetter G Λ))} {R : ℕ}
    {Z : Lemma44OrientedRelatorDiagram A W R}
    (D : Lemma44RelativeContiguityDiagram Z) :
    ∃ v ∈ lemma44CellVertices Z,
      (SmallCancellationRouter.NonCrossing.star D.edges v).card ≤ 4 := by
  apply SmallCancellationRouter.NonCrossing.exists_degree_le_four
    D.ordered D.endpoints D.noncrossing
    (cellVertices_card_add_one Z)
  have hne : Z.cells ≠ [] := cells_ne_nil Z
  have hpos : 0 < Z.cells.length := List.length_pos_iff.mpr hne
  rw [lemma44CellVertices, Finset.card_erase_of_mem]
  · simp only [Finset.card_range]
    omega
  · simp

end Lemma44RelativeContiguityDiagram

/-- The local shell read from an explicit relative contiguity diagram.

The selected cell really is one of `Z.cells`; `boundary_incident` and
`degree_le_four` are the planar conclusions.  The remaining fields are the
relative labels on that shell: its unique exterior run, its at most three
interior published-piece runs (empty records a missing run), and the two short
corner connectors. -/
structure Lemma44PlanarShellCertificate
    {G : Type u} [Group G] {Λ : Type w}
    {A : Alphabet G} {W : Set (List (GGT.RelLetter G Λ))} {R eps : ℕ}
    {E : GGT.RelGenSet G Λ} {Z : Lemma44OrientedRelatorDiagram A W R}
    (D : Lemma44RelativeContiguityDiagram Z) where
  cellIndex : Fin Z.cells.length
  boundary_incident : (0, cellIndex.1 + 1) ∈ D.edges
  degree_le_four :
    (SmallCancellationRouter.NonCrossing.star D.edges
      (cellIndex.1 + 1)).card ≤ 4
  exterior : List (GGT.RelLetter G Λ)
  arc₁ : Lemma44InteriorContiguityArc E W eps
    Z.cells[cellIndex.1].relator.length
  arc₂ : Lemma44InteriorContiguityArc E W eps
    Z.cells[cellIndex.1].relator.length
  arc₃ : Lemma44InteriorContiguityArc E W eps
    Z.cells[cellIndex.1].relator.length
  relator_decomposition :
    Z.cells[cellIndex.1].relator = exterior ++ arc₁.word ++ arc₂.word ++ arc₃.word
  leftConnector : G
  rightConnector : G
  leftConnector_short : WordMetric.wordNorm E.base leftConnector ≤ eps
  rightConnector_short : WordMetric.wordNorm E.base rightConnector ≤ eps
  exterior_value : GGT.RelLetter.listVal exterior =
    leftConnector * Z.boundary * rightConnector

/-- A planar shell certificate has exactly the local data consumed by the
quantitative exterior-cell contradiction.  Relator membership is not repeated
in the certificate: it is inherited from the selected oriented cell. -/
def Lemma44PlanarShellCertificate.toThreePieceExteriorCell
    {G : Type u} [Group G] {Λ : Type w}
    {A : Alphabet G} {W : Set (List (GGT.RelLetter G Λ))} {R eps : ℕ}
    {E : GGT.RelGenSet G Λ} {Z : Lemma44OrientedRelatorDiagram A W R}
    {D : Lemma44RelativeContiguityDiagram Z}
    (S : Lemma44PlanarShellCertificate (E := E) (eps := eps) D) :
    Lemma44ThreePieceExteriorCell E W eps Z.boundary :=
  { relator := Z.cells[S.cellIndex.1].relator
    relator_mem := Z.cells[S.cellIndex.1].relator_mem
    exterior := S.exterior
    arc₁ := S.arc₁
    arc₂ := S.arc₂
    arc₃ := S.arc₃
    relator_decomposition := S.relator_decomposition
    leftConnector := S.leftConnector
    rightConnector := S.rightConnector
    leftConnector_short := S.leftConnector_short
    rightConnector_short := S.rightConnector_short
    exterior_value := S.exterior_value }

/-- **The ball-injectivity half of Hull Lemma 4.4, reduced to the explicit
relative contiguity construction above.**

Failure of injectivity supplies the least-area reduced diagram, inversion
closure orients all its cells, and the hypothesised relative planar
construction supplies an outerplanar skeleton and a shell certificate.  The
shell becomes `Lemma44ThreePieceExteriorCell`, whose already-proved length
estimate contradicts the short boundary. -/
theorem injOn_cayleyBall_of_relativeContiguityShell
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G} (P : AuxiliaryPeripheralFamily A N S)
    {W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k)))}
    {R eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input P.rel W eps mu rho)
    (hmu_pos : 0 < mu) (hmu : mu ≤ 1 / 16)
    (hthreshold :
      4 * ((2 * R + 2 * eps + 1 : ℕ) : ℝ) <
        (13 / 16 : ℝ) * (rho : ℝ))
    {Q : Type*} [Group Q] (q : G →* Q)
    (hker : q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hplanar : ∀ Z : Lemma44OrientedRelatorDiagram A.alphabet W R,
      ∃ D : Lemma44RelativeContiguityDiagram Z,
        Nonempty (Lemma44PlanarShellCertificate (E := P.rel) (eps := eps) D)) :
    Set.InjOn q (cayleyBall A.alphabet R) := by
  by_contra hnot
  obtain ⟨Z₀⟩ := exists_lemma44ReducedRelatorDiagram_of_not_injOn
    A.alphabet W R q hker hnot
  obtain ⟨Z⟩ := Z₀.exists_oriented hsc.toIsSmallCancellation
  obtain ⟨D, ⟨C⟩⟩ := hplanar Z
  exact false_of_lemma44ThreePieceExteriorCell P
    Z.toLemma44ReducedRelatorDiagram hsc hmu_pos hmu
    hthreshold C.toThreePieceExteriorCell

end HullSC
end GroupApproximation
