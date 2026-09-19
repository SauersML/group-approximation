import GroupApproximation.GGT.KazhdanHypGirthEight
import GroupApproximation.GGT.KazhdanHypGirthEightDiagram
import GroupApproximation.GGT.KazhdanHypQuadrangleBridge

/-!
# From a checked triangular presentation to disc-diagram curvature

This file proves the local combinatorial part of the `C(3)`-`T(8)` argument.
A periodic nonbacktracking walk in the presentation link of a positive table
passing `GirthEightChecks` has length at least eight.  The proof uses
bipartiteness to exclude odd lengths, the common-neighbour clause to exclude
length four, and the length-three-path clause to exclude length six.

For a vk `DiscDiagram`, a cover of the inner faces by literal triangle
relator cells makes every inner face triangular.  These two results assemble
the local data into `VanKampen.TriangularGirthEightDiagram`, so the curvature
theorem in `KazhdanHypGirthEightDiagram` applies.

This is the combinatorial link argument in McCammond--Wise,
*Fans and ladders in small cancellation theory*.  Definition 3.4 defines
`T(q)` by excluding internal vertices of valence strictly between two and
`q`, identifies this with exclusion of short closed immersed link paths when
there are no proper-power cells, and Corollary 3.9 transfers the condition to
reduced disc diagrams.  The curvature convention is Theorem 4.6; Theorem 4.8
uses the corresponding constant-angle count:

* https://web.math.ucsb.edu/~mccammon/papers/fanladder.pdf

The current `VanKampen.DiscDiagram.Reduced` predicate is the algebraic
no-cancelling-pair condition on the ordered list of relator values.  Its map
API has no cyclic enumeration of corners about a vertex and no assignment of
such a corner to a position in a relator cell.  Thus it cannot yet construct
the `interiorVertexWalk` field below.  The field is the smallest missing local
primitive: it gives only the periodic link labels, adjacency of consecutive
labels, and the nonbacktracking condition used by the proof.
-/

namespace GroupApproximation
namespace KazhdanHyp

open scoped BigOperators

variable {Generator TriangleIndex : Type}

/-! ## Literal triangle words for ordinary disc diagrams -/

/-- A signed generator, interpreted as a base letter in the free group. -/
def signedFreeRelLetter (u : TriangularHodgeLayer.SignedGenerator Generator) :
    GGT.RelLetter (FreeGroup Generator) PEmpty :=
  GGT.RelLetter.base (FoxBoundary.letterValue FreeGroup.of u)

/-- The three-letter relative word attached to one literal triangle. -/
def triangleRelatorWord
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (j : TriangleIndex) : List (GGT.RelLetter (FreeGroup Generator) PEmpty) :=
  (TriangularHodgeLayer.letters (T j)).map signedFreeRelLetter

/-- The ordinary relator family used by the disc-diagram interface. -/
def triangleRelatorWords
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) :
    Set (List (GGT.RelLetter (FreeGroup Generator) PEmpty)) :=
  Set.range (triangleRelatorWord T)

/-- Every literal triangle relator has length three. -/
theorem triangleRelatorWord_length
    [Fintype Generator] [DecidableEq Generator]
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (j : TriangleIndex) : (triangleRelatorWord T j).length = 3 := by
  simp only [triangleRelatorWord, List.length_map,
    TriangularHodgeLayer.letters, List.length_ofFn]

/-! ## Periodic nonbacktracking walks -/

/-- A cyclic nonbacktracking walk, written periodically on `Nat`.

This generic form model-tests the local interface independently of a
presentation.  The specialization used below takes `Adjacent u v` to mean
that the link adjacency count is positive. -/
structure PeriodicNonbacktrackingWalk
    (Vertex : Type) (Adjacent : Vertex → Vertex → Prop) (n : ℕ) where
  /-- Periodic sequence of vertices. -/
  vertex : ℕ → Vertex
  /-- The chosen period is `n`. -/
  periodic : ∀ i, vertex (i + n) = vertex i
  /-- Consecutive vertices are adjacent. -/
  adjacent : ∀ i, Adjacent (vertex i) (vertex (i + 1))
  /-- Two consecutive edges never immediately reverse. -/
  noBacktrack : ∀ i, vertex i ≠ vertex (i + 2)
  /-- Link circuits arising at an interior triangular vertex have at least
  three corners. -/
  three_le : 3 ≤ n

namespace PeriodicNonbacktrackingWalk

/-- The four-cycle on natural residues is a nonempty model of the periodic
walk interface.  Adjacency is left unrestricted in this model; periodicity
and nonbacktracking are both genuine. -/
def fourCycleModel :
    PeriodicNonbacktrackingWalk ℕ (fun _ _ ↦ True) 4 where
  vertex i := i % 4
  periodic i := by
    exact Nat.add_mod_right i 4
  adjacent _ := trivial
  noBacktrack i := by
    omega
  three_le := by norm_num

/-- The model really has four distinct consecutive positions, so the
nonbacktracking clause is not vacuous. -/
theorem fourCycleModel_vertex_zero_ne_vertex_two :
    fourCycleModel.vertex 0 ≠ fourCycleModel.vertex 2 := by
  norm_num [fourCycleModel]

end PeriodicNonbacktrackingWalk

private theorem bool_eq_of_ne_of_ne {a b c : Bool}
    (hab : a ≠ b) (hbc : b ≠ c) : a = c := by
  cases a <;> cases b <;> cases c <;> simp_all

section FiniteTable

variable [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]

/-- A periodic nonbacktracking walk in the link of a triangle table. -/
abbrev PresentationLinkWalk
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (n : ℕ) :=
  PeriodicNonbacktrackingWalk
    (TriangularHodgeLayer.SignedGenerator Generator)
    (fun u v ↦ 0 < TriangularHodgeLayer.adjacencyCount T u v) n

namespace PresentationLinkWalk

variable {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
  {d n : ℕ}

/-- A positive adjacency count is exactly one when the checked link is
simple. -/
theorem edge_eq_one (hchecks : GirthEightChecks T d)
    (W : PresentationLinkWalk T n) (i : ℕ) :
    TriangularHodgeLayer.adjacencyCount T (W.vertex i) (W.vertex (i + 1)) = 1 := by
  have hpos := W.adjacent i
  have hle := hchecks.simple (W.vertex i) (W.vertex (i + 1))
  omega

/-- Consecutive vertices of a positive presentation link are on opposite
sides of its bipartition. -/
theorem sign_ne (hchecks : GirthEightChecks T d)
    (W : PresentationLinkWalk T n) (i : ℕ) :
    (W.vertex i).2 ≠ (W.vertex (i + 1)).2 := by
  intro hsign
  have hzero : TriangularHodgeLayer.adjacencyCount T
      (W.vertex i) (W.vertex (i + 1)) = 0 :=
    adjacencyCount_eq_zero_of_same_side hchecks.1 hsign
  have hpos := W.adjacent i
  omega

/-- Two link steps return to the same side of the bipartition. -/
theorem sign_add_two (hchecks : GirthEightChecks T d)
    (W : PresentationLinkWalk T n) (i : ℕ) :
    (W.vertex i).2 = (W.vertex (i + 2)).2 := by
  have h01 := W.sign_ne hchecks i
  have h12raw := W.sign_ne hchecks (i + 1)
  have h12 : (W.vertex (i + 1)).2 ≠ (W.vertex (i + 2)).2 := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using h12raw
  exact bool_eq_of_ne_of_ne h01 h12

/-- The no-four-cycle count forbids four distinct successive sides closing
up in the link. -/
private theorem no_four_cycle
    (hchecks : GirthEightChecks T d)
    {v0 v1 v2 v3 : TriangularHodgeLayer.SignedGenerator Generator}
    (h02 : v0 ≠ v2) (h13 : v1 ≠ v3)
    (h01 : TriangularHodgeLayer.adjacencyCount T v0 v1 = 1)
    (h12 : TriangularHodgeLayer.adjacencyCount T v1 v2 = 1)
    (h23 : TriangularHodgeLayer.adjacencyCount T v2 v3 = 1)
    (h30 : TriangularHodgeLayer.adjacencyCount T v3 v0 = 1) : False := by
  let term := fun u : TriangularHodgeLayer.SignedGenerator Generator ↦
    TriangularHodgeLayer.adjacencyCount T u v0 *
      TriangularHodgeLayer.adjacencyCount T u v2
  have hterm1 : term v1 = 1 := by
    dsimp only [term]
    rw [TriangularHodgeLayer.adjacencyCount_comm T v1 v0, h01, h12]
  have hterm3 : term v3 = 1 := by
    dsimp only [term]
    rw [h30, TriangularHodgeLayer.adjacencyCount_comm T v3 v2, h23]
  have hpair : term v1 + term v3 ≤ ∑ u, term u := by
    rw [← Finset.sum_pair h13]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (by omega)
  have hupper := hchecks.2.2.2.1 v0 v2 h02
  change (∑ u, term u) ≤ 1 at hupper
  rw [hterm1, hterm3] at hpair
  omega

private theorem not_length_three (hchecks : GirthEightChecks T d)
    (W : PresentationLinkWalk T n) (hn : n = 3) : False := by
  have hpRaw := W.periodic 0
  have hp : W.vertex 3 = W.vertex 0 := by
    simpa only [zero_add, hn] using hpRaw
  have h13 := W.sign_add_two hchecks 1
  have h30 : (W.vertex 3).2 = (W.vertex 0).2 := congrArg Prod.snd hp
  have h01 := W.sign_ne hchecks 0
  have heq : (W.vertex 0).2 = (W.vertex 1).2 := by
    exact h30.symm.trans h13.symm
  exact h01 heq

private theorem not_length_four (hchecks : GirthEightChecks T d)
    (W : PresentationLinkWalk T n) (hn : n = 4) : False := by
  have hpRaw := W.periodic 0
  have hp : W.vertex 4 = W.vertex 0 := by
    simpa only [zero_add, hn] using hpRaw
  have h02 : W.vertex 0 ≠ W.vertex 2 := by
    simpa only [Nat.reduceAdd] using W.noBacktrack 0
  have h13 : W.vertex 1 ≠ W.vertex 3 := by
    simpa only [Nat.reduceAdd] using W.noBacktrack 1
  have h01 : TriangularHodgeLayer.adjacencyCount T
      (W.vertex 0) (W.vertex 1) = 1 := by
    simpa only [Nat.reduceAdd] using W.edge_eq_one hchecks 0
  have h12 : TriangularHodgeLayer.adjacencyCount T
      (W.vertex 1) (W.vertex 2) = 1 := by
    simpa only [Nat.reduceAdd] using W.edge_eq_one hchecks 1
  have h23 : TriangularHodgeLayer.adjacencyCount T
      (W.vertex 2) (W.vertex 3) = 1 := by
    simpa only [Nat.reduceAdd] using W.edge_eq_one hchecks 2
  have h34 : TriangularHodgeLayer.adjacencyCount T
      (W.vertex 3) (W.vertex 4) = 1 := by
    simpa only [Nat.reduceAdd] using W.edge_eq_one hchecks 3
  have h30 : TriangularHodgeLayer.adjacencyCount T
      (W.vertex 3) (W.vertex 0) = 1 := by
    rw [← hp]
    exact h34
  exact no_four_cycle hchecks h02 h13 h01 h12 h23 h30

private theorem not_length_five (hchecks : GirthEightChecks T d)
    (W : PresentationLinkWalk T n) (hn : n = 5) : False := by
  have hpRaw := W.periodic 0
  have hp : W.vertex 5 = W.vertex 0 := by
    simpa only [zero_add, hn] using hpRaw
  have h13 := W.sign_add_two hchecks 1
  have h35 := W.sign_add_two hchecks 3
  have h50 : (W.vertex 5).2 = (W.vertex 0).2 := congrArg Prod.snd hp
  have h01 := W.sign_ne hchecks 0
  have heq : (W.vertex 0).2 = (W.vertex 1).2 := by
    exact h50.symm.trans (h35.symm.trans h13.symm)
  exact h01 heq

private theorem not_length_six (hchecks : GirthEightChecks T d)
    (W : PresentationLinkWalk T n) (hn : n = 6) : False := by
  have hp0Raw := W.periodic 0
  have hp0 : W.vertex 6 = W.vertex 0 := by
    simpa only [zero_add, hn] using hp0Raw
  have hp1Raw := W.periodic 1
  have hp1 : W.vertex 7 = W.vertex 1 := by
    simpa only [hn, Nat.reduceAdd] using hp1Raw
  have h02 : W.vertex 0 ≠ W.vertex 2 := by
    simpa only [Nat.reduceAdd] using W.noBacktrack 0
  have h13 : W.vertex 1 ≠ W.vertex 3 := by
    simpa only [Nat.reduceAdd] using W.noBacktrack 1
  have h57 : W.vertex 5 ≠ W.vertex 7 := by
    simpa only [Nat.reduceAdd] using W.noBacktrack 5
  have h15 : W.vertex 1 ≠ W.vertex 5 := by
    intro h
    apply h57
    exact h.symm.trans hp1.symm
  have h01 : TriangularHodgeLayer.adjacencyCount T
      (W.vertex 0) (W.vertex 1) = 1 := by
    simpa only [Nat.reduceAdd] using W.edge_eq_one hchecks 0
  have h12 : TriangularHodgeLayer.adjacencyCount T
      (W.vertex 1) (W.vertex 2) = 1 := by
    simpa only [Nat.reduceAdd] using W.edge_eq_one hchecks 1
  have h23 : TriangularHodgeLayer.adjacencyCount T
      (W.vertex 2) (W.vertex 3) = 1 := by
    simpa only [Nat.reduceAdd] using W.edge_eq_one hchecks 2
  have h34 : TriangularHodgeLayer.adjacencyCount T
      (W.vertex 3) (W.vertex 4) = 1 := by
    simpa only [Nat.reduceAdd] using W.edge_eq_one hchecks 3
  have h45 : TriangularHodgeLayer.adjacencyCount T
      (W.vertex 4) (W.vertex 5) = 1 := by
    simpa only [Nat.reduceAdd] using W.edge_eq_one hchecks 4
  have h56 : TriangularHodgeLayer.adjacencyCount T
      (W.vertex 5) (W.vertex 6) = 1 := by
    simpa only [Nat.reduceAdd] using W.edge_eq_one hchecks 5
  have h50 : TriangularHodgeLayer.adjacencyCount T
      (W.vertex 5) (W.vertex 0) = 1 := by
    rw [← hp0]
    exact h56
  have h03zero : TriangularHodgeLayer.adjacencyCount T
      (W.vertex 0) (W.vertex 3) = 0 := by
    by_contra hne
    have hpos : 0 < TriangularHodgeLayer.adjacencyCount T
        (W.vertex 0) (W.vertex 3) := Nat.pos_of_ne_zero hne
    have hone : TriangularHodgeLayer.adjacencyCount T
        (W.vertex 0) (W.vertex 3) = 1 := by
      have hle := hchecks.simple (W.vertex 0) (W.vertex 3)
      omega
    have h30 : TriangularHodgeLayer.adjacencyCount T
        (W.vertex 3) (W.vertex 0) = 1 := by
      rw [TriangularHodgeLayer.adjacencyCount_comm T (W.vertex 3) (W.vertex 0)]
      exact hone
    exact no_four_cycle hchecks h02 h13 h01 h12 h23 h30
  let term := fun a b : TriangularHodgeLayer.SignedGenerator Generator ↦
    TriangularHodgeLayer.adjacencyCount T (W.vertex 0) a *
      TriangularHodgeLayer.adjacencyCount T a b *
      TriangularHodgeLayer.adjacencyCount T b (W.vertex 3)
  have hterm12 : term (W.vertex 1) (W.vertex 2) = 1 := by
    dsimp only [term]
    rw [h01, h12, h23]
  have h05 : TriangularHodgeLayer.adjacencyCount T
      (W.vertex 0) (W.vertex 5) = 1 := by
    rw [TriangularHodgeLayer.adjacencyCount_comm T (W.vertex 0) (W.vertex 5)]
    exact h50
  have h54 : TriangularHodgeLayer.adjacencyCount T
      (W.vertex 5) (W.vertex 4) = 1 := by
    rw [TriangularHodgeLayer.adjacencyCount_comm T (W.vertex 5) (W.vertex 4)]
    exact h45
  have h43 : TriangularHodgeLayer.adjacencyCount T
      (W.vertex 4) (W.vertex 3) = 1 := by
    rw [TriangularHodgeLayer.adjacencyCount_comm T (W.vertex 4) (W.vertex 3)]
    exact h34
  have hterm54 : term (W.vertex 5) (W.vertex 4) = 1 := by
    dsimp only [term]
    rw [h05, h54, h43]
  let subtotal := fun a : TriangularHodgeLayer.SignedGenerator Generator ↦
    ∑ b, term a b
  have hsub1 : 1 ≤ subtotal (W.vertex 1) := by
    calc
      1 = term (W.vertex 1) (W.vertex 2) := hterm12.symm
      _ ≤ ∑ b, term (W.vertex 1) b :=
        Finset.single_le_sum (fun b _ ↦ Nat.zero_le (term (W.vertex 1) b))
          (Finset.mem_univ (W.vertex 2))
  have hsub5 : 1 ≤ subtotal (W.vertex 5) := by
    calc
      1 = term (W.vertex 5) (W.vertex 4) := hterm54.symm
      _ ≤ ∑ b, term (W.vertex 5) b :=
        Finset.single_le_sum (fun b _ ↦ Nat.zero_le (term (W.vertex 5) b))
          (Finset.mem_univ (W.vertex 4))
  have hpair : subtotal (W.vertex 1) + subtotal (W.vertex 5) ≤
      ∑ a, subtotal a := by
    rw [← Finset.sum_pair h15]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (by omega)
  have hlower : 2 ≤ ∑ a, ∑ b, term a b := by
    change 2 ≤ ∑ a, subtotal a
    omega
  have hupper := hchecks.2.2.2.2 (W.vertex 0) (W.vertex 3) h03zero
  change (∑ a, ∑ b, term a b) ≤ 1 at hupper
  omega

private theorem not_length_seven (hchecks : GirthEightChecks T d)
    (W : PresentationLinkWalk T n) (hn : n = 7) : False := by
  have hpRaw := W.periodic 0
  have hp : W.vertex 7 = W.vertex 0 := by
    simpa only [zero_add, hn] using hpRaw
  have h13 := W.sign_add_two hchecks 1
  have h35 := W.sign_add_two hchecks 3
  have h57 := W.sign_add_two hchecks 5
  have h70 : (W.vertex 7).2 = (W.vertex 0).2 := congrArg Prod.snd hp
  have h01 := W.sign_ne hchecks 0
  have heq : (W.vertex 0).2 = (W.vertex 1).2 := by
    exact h70.symm.trans (h57.symm.trans (h35.symm.trans h13.symm))
  exact h01 heq

/-- **`T(8)` from the finite girth checks.**  Every periodic
nonbacktracking presentation-link walk has at least eight edges. -/
theorem eight_le_length (hchecks : GirthEightChecks T d)
    (W : PresentationLinkWalk T n) : 8 ≤ n := by
  by_contra hnot
  have hlt : n < 8 := by omega
  have hthree := W.three_le
  have hcases : n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by
    omega
  rcases hcases with h3 | h4 | h5 | h6 | h7
  · exact W.not_length_three hchecks h3
  · exact W.not_length_four hchecks h4
  · exact W.not_length_five hchecks h5
  · exact W.not_length_six hchecks h6
  · exact W.not_length_seven hchecks h7

end PresentationLinkWalk

/-! ## The local bridge from vk diagrams -/

open GGT.VanKampen

omit [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex] in
/-- Vertices visited by the chosen outer face traversal. -/
noncomputable def discOuterBoundaryVertices
    {W : Set (List (GGT.RelLetter (FreeGroup Generator) PEmpty))}
    (Delta : DiscDiagram W) : Finset Delta.toCombMap.Vertex := by
  classical
  exact ((Delta.faceBoundary Delta.outerFace).darts.map
    Delta.toCombMap.vertexOf).toFinset

omit [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex] in
/-- The outer traversal visits at least as many darts as distinct vertices.
This part of the boundary bookkeeping follows from the current vk API. -/
theorem discOuterBoundaryVertices_card_le
    {W : Set (List (GGT.RelLetter (FreeGroup Generator) PEmpty))}
    (Delta : DiscDiagram W) :
    (discOuterBoundaryVertices Delta).card ≤
      Delta.combinatorialBoundaryLength := by
  classical
  rw [discOuterBoundaryVertices]
  calc
    (((Delta.faceBoundary Delta.outerFace).darts.map
        Delta.toCombMap.vertexOf).toFinset).card ≤
        ((Delta.faceBoundary Delta.outerFace).darts.map
          Delta.toCombMap.vertexOf).length :=
      List.toFinset_card_le _
    _ = (Delta.faceBoundary Delta.outerFace).darts.length := by
      rw [List.length_map]
    _ = Delta.toCombMap.faceDegree Delta.outerFace :=
      (Delta.faceBoundary Delta.outerFace).length_eq_degree
    _ = Delta.combinatorialBoundaryLength := rfl

omit [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex] in
/-- An inner face whose word is nontrivial in the base free group must be one
of the stored relator cells.  This is the part of face coverage supplied by
`DiscDiagram.inner_face`; an ordinary presentation diagram must separately
exclude relative base-group cells. -/
theorem exists_relatorCell_of_inner_faceWord_ne_one
    {W : Set (List (GGT.RelLetter (FreeGroup Generator) PEmpty))}
    (Delta : DiscDiagram W) (f : Delta.toCombMap.Face)
    (hf : f ≠ Delta.outerFace)
    (hvalue : GGT.RelLetter.listVal (Delta.faceWord f) ≠ 1) :
    ∃ C ∈ Delta.relatorCells, C.face = f := by
  rcases Delta.inner_face f hf with hcell | hbase
  · exact hcell
  · exact absurd hbase hvalue

/-- The local cellular information not exposed by the current vk
`DiscDiagram` API.

`innerFaceCell` rules out relative base-group cells and assigns every inner
face to a literal triangle relator.  `interiorVertexWalk` is the cyclic list
of link labels at an interior vertex, with cellular reducedness expressed by
`noBacktrack`.  The last field is the remaining outer-boundary immersion fact;
the boundary vertex set and its cardinality bound are constructed above. -/
structure TriangularDiagramLocalData
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (Delta : DiscDiagram (triangleRelatorWords T)) where
  /-- Every inner face is represented by a stored literal relator cell. -/
  innerFaceCell : ∀ f, f ≠ Delta.outerFace →
    ∃ C ∈ Delta.relatorCells, C.face = f
  /-- The corners around each interior vertex form a reduced link circuit. -/
  interiorVertexWalk : ∀ v, v ∉ discOuterBoundaryVertices Delta →
    PresentationLinkWalk T (Delta.toCombMap.vertexDegree v)
  /-- Boundary vertices have valence at least two. -/
  boundaryVertexDegree : ∀ v, v ∈ discOuterBoundaryVertices Delta →
    2 ≤ Delta.toCombMap.vertexDegree v

namespace TriangularDiagramLocalData

variable {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
  {d : ℕ} {Delta : DiscDiagram (triangleRelatorWords T)}

omit [DecidableEq TriangleIndex] in
/-- Relator-cell coverage makes every inner face triangular. -/
theorem innerFaceDegree (L : TriangularDiagramLocalData T Delta)
    (f : Delta.toCombMap.Face) (hf : f ∈ Delta.innerFaces) :
    Delta.toCombMap.faceDegree f = 3 := by
  have hfne : f ≠ Delta.outerFace := by
    simpa only [DiscDiagram.innerFaces, Finset.mem_sdiff, Finset.mem_univ,
      true_and, Finset.mem_singleton] using hf
  obtain ⟨C, hCmem, hCface⟩ := L.innerFaceCell f hfne
  obtain ⟨j, hj⟩ := C.word_mem
  have hword : C.word = Delta.faceWord f := by
    rw [← hCface]
    exact Delta.relatorCell_word C hCmem
  have hlength : C.word.length = 3 := by
    rw [← hj]
    exact triangleRelatorWord_length T j
  have hfaceLength := Delta.faceWord_length f
  rw [← hword] at hfaceLength
  omega

/-- The checked link gives degree at least eight at every supplied interior
vertex. -/
theorem interiorVertexDegree (hchecks : GirthEightChecks T d)
    (L : TriangularDiagramLocalData T Delta)
    (v : Delta.toCombMap.Vertex)
    (hv : v ∉ discOuterBoundaryVertices Delta) :
    8 ≤ Delta.toCombMap.vertexDegree v :=
  (L.interiorVertexWalk v hv).eight_le_length hchecks

/-- The local bridge assembles the exact input of the curvature theorem. -/
noncomputable def toTriangularGirthEightDiagram
    (hchecks : GirthEightChecks T d)
    (L : TriangularDiagramLocalData T Delta) :
    TriangularGirthEightDiagram Delta where
  boundaryVertices := discOuterBoundaryVertices Delta
  innerFaceDegree := L.innerFaceDegree
  interiorVertexDegree := L.interiorVertexDegree hchecks
  boundaryVertexDegree := L.boundaryVertexDegree
  boundaryVertexCount_le := discOuterBoundaryVertices_card_le Delta

/-- The assembled local data gives the sharp triangular curvature estimate. -/
theorem innerFaceCount_add_eight_le_three_mul_boundaryLength
    (hchecks : GirthEightChecks T d)
    (L : TriangularDiagramLocalData T Delta) :
    Delta.innerFaceCount + 8 ≤ 3 * Delta.combinatorialBoundaryLength :=
  TriangularGirthEightDiagram.innerFaceCount_add_eight_le_three_mul_boundaryLength
    (L.toTriangularGirthEightDiagram hchecks)

/-- The relator-cell area is at most three times the exterior word length. -/
theorem rCellCount_le_three_mul_boundaryWord_length
    (hchecks : GirthEightChecks T d)
    (L : TriangularDiagramLocalData T Delta) :
    Delta.rCellCount ≤ 3 * Delta.boundaryWord.length :=
  TriangularGirthEightDiagram.rCellCount_le_three_mul_boundaryWord_length
    (L.toTriangularGirthEightDiagram hchecks)

end TriangularDiagramLocalData

end FiniteTable

end KazhdanHyp
end GroupApproximation
