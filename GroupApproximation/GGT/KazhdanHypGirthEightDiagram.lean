import GroupApproximation.GGT.VanKampen.DiscDiagram

/-!
# Curvature of triangular girth-eight disc diagrams

This file proves the numerical part of the `C(3)`-`T(8)` hyperbolicity
argument.  The input is a planar combinatorial disc map with a distinguished
outer face.  Every inner face has degree three, every interior vertex has
degree at least eight, every boundary vertex has degree at least two, and the
number of boundary vertices is at most the degree of the outer face.  Euler's
formula and the two degree sums then give

`innerFaceCount + 8 <= 3 * boundaryLength`.

The curvature calculation is the strict version of McCammond--Wise,
*Fans and ladders in small cancellation theory*, Section 4, especially
Theorem 4.6 (combinatorial Gauss--Bonnet) and the `pi / 3` angle assignment in
Theorem 4.8:

* https://web.math.ucsb.edu/~mccammon/papers/fanladder.pdf

For the later metric step, Bowditch's *A short proof that a subquadratic
isoperimetric inequality implies a linear one* states after Lemma 2 that a
linear area function satisfying the rectangle axiom makes the path-metric
space Gromov hyperbolic:

* https://bhbowditch.com/papers/bhb-subquadratic.pdf

The group-theoretic star-of-a-side proof is Papasoglu's Theorem 3.22 in the
following lecture notes.  It uses successive stars of a longest side of a
truncated fat geodesic triangle:

* https://www.math.ucdavis.edu/~kapovich/280-2020/hyplectures_papasoglu.pdf

The current `VanKampen.DiscDiagram` API supplies the planar map, the outer
face, and its face boundary.  The fields of `TriangularGirthEightDiagram` are
exactly the remaining local facts that a reduced-diagram theorem must derive
from a triangular presentation and its girth-eight link.  The present
algebraic `DiscDiagram.Reduced` predicate concerns cancellation among ordered
relator values; the local argument additionally needs cell adjacency in order
to map an interior vertex link cycle into the presentation link.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

open scoped BigOperators

universe u w

/-! ## The integer-free form of the curvature count -/

/-- The five counts and four relations used by the triangular curvature
argument.  `euler` is `V - E + F = 1`, written in `Nat` as
`V + F = E + 1`.  `faceIncidence` is `2E = 3F + B`.  The degree lower bound
is `8 V_i + 2 V_b <= 2E`.

This structure is independent of a particular combinatorial-map encoding, so
the arithmetic theorem can be reused by later disc-diagram implementations. -/
structure TriangularDiscCounts where
  /-- Vertices not incident to the outer face. -/
  interiorVertexCount : ℕ
  /-- Vertices incident to the outer face. -/
  boundaryVertexCount : ℕ
  /-- Edges of the closed map obtained by adjoining the outer face. -/
  edgeCount : ℕ
  /-- Inner triangular faces. -/
  faceCount : ℕ
  /-- Degree of the outer face. -/
  boundaryLength : ℕ
  /-- Euler's formula for the disc. -/
  euler : interiorVertexCount + boundaryVertexCount + faceCount = edgeCount + 1
  /-- The sum of the degrees of all faces. -/
  faceIncidence : 2 * edgeCount = 3 * faceCount + boundaryLength
  /-- The lower bound obtained by summing vertex degrees. -/
  degreeLower :
    8 * interiorVertexCount + 2 * boundaryVertexCount <= 2 * edgeCount
  /-- A boundary circuit visits at least as many darts as distinct vertices. -/
  boundaryVertexCount_le : boundaryVertexCount <= boundaryLength

namespace TriangularDiscCounts

/-- **Strict triangular curvature inequality.**  A triangular disc with
interior degree at least eight has at most `3B - 8` faces.

Algebraically, face incidence and Euler give
`F + B = 2 V_i + 2 V_b - 2`.  Substitution in the vertex-degree inequality
gives `3 V_i + 1 <= F`.  Combining this with `V_b <= B` gives
`F + 8 <= 3B`. -/
theorem faceCount_add_eight_le_three_mul_boundaryLength
    (C : TriangularDiscCounts) :
    C.faceCount + 8 <= 3 * C.boundaryLength := by
  have heuler := C.euler
  have hfaces := C.faceIncidence
  have hdegrees := C.degreeLower
  have hboundary := C.boundaryVertexCount_le
  omega

/-- The inequality implies the coarser homogeneous linear bound used by a
Dehn-function consumer. -/
theorem faceCount_le_three_mul_boundaryLength
    (C : TriangularDiscCounts) :
    C.faceCount <= 3 * C.boundaryLength := by
  have hstrict := C.faceCount_add_eight_le_three_mul_boundaryLength
  omega

/-- The one-triangle disc is the smallest nonempty model of the count
interface.  It has no interior vertices, three boundary vertices and edges,
one inner face, and boundary length three. -/
def oneTriangle : TriangularDiscCounts where
  interiorVertexCount := 0
  boundaryVertexCount := 3
  edgeCount := 3
  faceCount := 1
  boundaryLength := 3
  euler := by norm_num
  faceIncidence := by norm_num
  degreeLower := by norm_num
  boundaryVertexCount_le := by norm_num

/-- The additive constant eight is sharp on the one-triangle model. -/
theorem oneTriangle_curvature_equality :
    oneTriangle.faceCount + 8 = 3 * oneTriangle.boundaryLength := by
  norm_num [oneTriangle]

/-- The interface rules out an empty boundary for a nonempty diagram.  This
is a degeneracy check complementary to `oneTriangle`. -/
theorem boundaryLength_pos_of_faceCount_pos (C : TriangularDiscCounts)
    (hface : 0 < C.faceCount) : 0 < C.boundaryLength := by
  have hcurv := C.faceCount_add_eight_le_three_mul_boundaryLength
  omega

end TriangularDiscCounts

/-! ## Counts exposed by `DiscDiagram` -/

namespace DiscDiagram

/-- The faces other than the distinguished outer face. -/
noncomputable def innerFaces
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram W) : Finset Delta.toCombMap.Face := by
  classical
  exact Finset.univ \ {Delta.outerFace}

/-- Number of faces other than the distinguished outer face. -/
noncomputable def innerFaceCount
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram W) : ℕ :=
  Delta.innerFaces.card

/-- Combinatorial boundary length, as the degree of the outer face. -/
def combinatorialBoundaryLength
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram W) : ℕ :=
  Delta.toCombMap.faceDegree Delta.outerFace

/-- The list read around the outer face has the combinatorial boundary
length. -/
theorem boundaryWord_length_eq_combinatorialBoundaryLength
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram W) :
    Delta.boundaryWord.length = Delta.combinatorialBoundaryLength := by
  rw [boundaryWord, combinatorialBoundaryLength]
  exact Delta.faceWord_length Delta.outerFace

/-- Adding the outer face to the inner faces gives every face. -/
theorem innerFaceCount_add_one_eq_faceCount
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram W) :
    Delta.innerFaceCount + 1 = Delta.toCombMap.faceCount := by
  classical
  have hsubset : ({Delta.outerFace} : Finset Delta.toCombMap.Face) <= Finset.univ :=
    Finset.subset_univ _
  have hcard := Finset.card_sdiff_add_card_eq_card hsubset
  simpa only [innerFaceCount, innerFaces, Finset.card_singleton,
    CombMap.faceCount, Nat.card_eq_fintype_card, Finset.card_univ] using hcard

/-- Distinct relator cells occupy distinct inner faces, so algebraic relator
area is at most the number of inner faces. -/
theorem rCellCount_le_innerFaceCount
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram W) : Delta.rCellCount <= Delta.innerFaceCount := by
  classical
  have hsubset :
      (Delta.relatorCells.map RelatorCell.face).toFinset <= Delta.innerFaces := by
    intro f hf
    have hmem : f ∈ Delta.relatorCells.map RelatorCell.face := by
      simpa only [List.mem_toFinset] using hf
    obtain ⟨C, _, hface⟩ := List.mem_map.mp hmem
    subst f
    simpa only [innerFaces, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_singleton] using C.face_ne_outer
  calc
    Delta.rCellCount = (Delta.relatorCells.map RelatorCell.face).length := by
      simp only [rCellCount, List.length_map]
    _ = (Delta.relatorCells.map RelatorCell.face).toFinset.card :=
      (List.toFinset_card_of_nodup Delta.relatorCell_faces_nodup).symm
    _ <= Delta.innerFaces.card := Finset.card_le_card hsubset
    _ = Delta.innerFaceCount := rfl

end DiscDiagram

/-! ## The local curvature contract over vk's disc diagrams -/

/-- Local hypotheses on a planar vk disc diagram that are read by the
triangular girth-eight curvature count.

The future `C(3)`-`T(8)` bridge has to prove these fields for a reduced
diagram: triangular relators give `innerFaceDegree`, injectivity of each
interior diagram-link cycle into the presentation link gives
`interiorVertexDegree`, and an immersed outer boundary gives
`boundaryVertexDegree`. -/
structure TriangularGirthEightDiagram
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram W) where
  /-- The vertices assigned to the boundary part of the degree sum. -/
  boundaryVertices : Finset Delta.toCombMap.Vertex
  /-- Every inner face is triangular. -/
  innerFaceDegree : ∀ f, f ∈ Delta.innerFaces → Delta.toCombMap.faceDegree f = 3
  /-- Every vertex off the outer boundary has degree at least eight. -/
  interiorVertexDegree : ∀ v, v ∉ boundaryVertices →
    8 <= Delta.toCombMap.vertexDegree v
  /-- An immersed boundary has no valence-zero or valence-one vertex. -/
  boundaryVertexDegree : ∀ v, v ∈ boundaryVertices →
    2 <= Delta.toCombMap.vertexDegree v
  /-- A closed boundary walk has at least as many darts as vertices in its
  image. -/
  boundaryVertexCount_le :
    boundaryVertices.card <= Delta.combinatorialBoundaryLength

namespace TriangularGirthEightDiagram

/-- Vertices outside the stored boundary-vertex set. -/
noncomputable def interiorVertices
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram W} (C : TriangularGirthEightDiagram Delta) :
    Finset Delta.toCombMap.Vertex := by
  classical
  exact Finset.univ \ C.boundaryVertices

/-- Number of vertices outside the stored boundary-vertex set. -/
noncomputable def interiorVertexCount
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram W} (C : TriangularGirthEightDiagram Delta) : ℕ :=
  C.interiorVertices.card

/-- The interior and boundary vertex sets partition all vertices. -/
theorem interiorVertexCount_add_boundaryVertexCount_eq_vertexCount
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram W} (C : TriangularGirthEightDiagram Delta) :
    C.interiorVertexCount + C.boundaryVertices.card =
      Delta.toCombMap.vertexCount := by
  classical
  have hsubset : C.boundaryVertices <=
      (Finset.univ : Finset Delta.toCombMap.Vertex) := Finset.subset_univ _
  have hcard := Finset.card_sdiff_add_card_eq_card hsubset
  simpa only [interiorVertexCount, interiorVertices, CombMap.vertexCount,
    Nat.card_eq_fintype_card, Finset.card_univ] using hcard

/-- Euler's formula for the closed planar map becomes Euler's formula for the
disc after deleting the outer face. -/
theorem euler_count
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram W} (C : TriangularGirthEightDiagram Delta) :
    C.interiorVertexCount + C.boundaryVertices.card + Delta.innerFaceCount =
      Delta.toCombMap.edgeCount + 1 := by
  have heuler := Delta.toCombMap.euler_eq_two Delta.planar
  have hvertices := C.interiorVertexCount_add_boundaryVertexCount_eq_vertexCount
  have hfaces := Delta.innerFaceCount_add_one_eq_faceCount
  omega

/-- The face-degree sum is `2E = 3F + B`. -/
theorem face_incidence
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram W} (C : TriangularGirthEightDiagram Delta) :
    2 * Delta.toCombMap.edgeCount =
      3 * Delta.innerFaceCount + Delta.combinatorialBoundaryLength := by
  classical
  have hinner :
      (∑ f in Delta.innerFaces, Delta.toCombMap.faceDegree f) =
        3 * Delta.innerFaceCount := by
    calc
      (∑ f in Delta.innerFaces, Delta.toCombMap.faceDegree f) =
          ∑ _f in Delta.innerFaces, 3 := by
            apply Finset.sum_congr rfl
            intro f hf
            exact C.innerFaceDegree f hf
      _ = 3 * Delta.innerFaceCount := by
        simp only [DiscDiagram.innerFaceCount, Finset.sum_const,
          Nat.nsmul_eq_mul, Nat.mul_comm]
  have hsubset : ({Delta.outerFace} : Finset Delta.toCombMap.Face) <= Finset.univ :=
    Finset.subset_univ _
  have hsplit :
      (∑ f in Delta.innerFaces, Delta.toCombMap.faceDegree f) +
          ∑ f in ({Delta.outerFace} : Finset Delta.toCombMap.Face),
            Delta.toCombMap.faceDegree f =
        ∑ f : Delta.toCombMap.Face, Delta.toCombMap.faceDegree f := by
    simpa only [DiscDiagram.innerFaces] using
      (Finset.sum_sdiff hsubset (f := Delta.toCombMap.faceDegree))
  have htotal := Delta.toCombMap.sum_faceDegree_eq_two_mul_edgeCount
  simp only [Finset.sum_singleton] at hsplit
  unfold DiscDiagram.combinatorialBoundaryLength
  omega

/-- Summing the two vertex-degree lower bounds gives
`8 V_i + 2 V_b <= 2E`. -/
theorem vertex_degree_lower
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram W} (C : TriangularGirthEightDiagram Delta) :
    8 * C.interiorVertexCount + 2 * C.boundaryVertices.card <=
      2 * Delta.toCombMap.edgeCount := by
  classical
  have hinterior :
      8 * C.interiorVertexCount <=
        ∑ v in C.interiorVertices, Delta.toCombMap.vertexDegree v := by
    calc
      8 * C.interiorVertexCount = ∑ _v in C.interiorVertices, 8 := by
        simp only [interiorVertexCount, Finset.sum_const,
          Nat.nsmul_eq_mul, Nat.mul_comm]
      _ <= ∑ v in C.interiorVertices, Delta.toCombMap.vertexDegree v := by
        apply Finset.sum_le_sum
        intro v hv
        apply C.interiorVertexDegree v
        simpa only [interiorVertices, Finset.mem_sdiff, Finset.mem_univ,
          true_and] using hv
  have hboundary :
      2 * C.boundaryVertices.card <=
        ∑ v in C.boundaryVertices, Delta.toCombMap.vertexDegree v := by
    calc
      2 * C.boundaryVertices.card = ∑ _v in C.boundaryVertices, 2 := by
        simp only [Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_comm]
      _ <= ∑ v in C.boundaryVertices, Delta.toCombMap.vertexDegree v := by
        apply Finset.sum_le_sum
        intro v hv
        exact C.boundaryVertexDegree v hv
  have hsubset : C.boundaryVertices <=
      (Finset.univ : Finset Delta.toCombMap.Vertex) := Finset.subset_univ _
  have hsplit :
      (∑ v in C.interiorVertices, Delta.toCombMap.vertexDegree v) +
          ∑ v in C.boundaryVertices, Delta.toCombMap.vertexDegree v =
        ∑ v : Delta.toCombMap.Vertex, Delta.toCombMap.vertexDegree v := by
    simpa only [interiorVertices] using
      (Finset.sum_sdiff hsubset (f := Delta.toCombMap.vertexDegree))
  have htotal := Delta.toCombMap.sum_vertexDegree_eq_two_mul_edgeCount
  omega

/-- The local disc-diagram fields produce the reusable count package. -/
noncomputable def counts
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram W} (C : TriangularGirthEightDiagram Delta) :
    TriangularDiscCounts where
  interiorVertexCount := C.interiorVertexCount
  boundaryVertexCount := C.boundaryVertices.card
  edgeCount := Delta.toCombMap.edgeCount
  faceCount := Delta.innerFaceCount
  boundaryLength := Delta.combinatorialBoundaryLength
  euler := C.euler_count
  faceIncidence := C.face_incidence
  degreeLower := C.vertex_degree_lower
  boundaryVertexCount_le := C.boundaryVertexCount_le

/-- **Linear isoperimetric inequality for a triangular girth-eight disc.** -/
theorem innerFaceCount_add_eight_le_three_mul_boundaryLength
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram W} (C : TriangularGirthEightDiagram Delta) :
    Delta.innerFaceCount + 8 <=
      3 * Delta.combinatorialBoundaryLength :=
  C.counts.faceCount_add_eight_le_three_mul_boundaryLength

/-- Homogeneous form of the linear isoperimetric inequality. -/
theorem innerFaceCount_le_three_mul_boundaryLength
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram W} (C : TriangularGirthEightDiagram Delta) :
    Delta.innerFaceCount <= 3 * Delta.combinatorialBoundaryLength :=
  C.counts.faceCount_le_three_mul_boundaryLength

/-- Relator-cell area is linearly bounded by combinatorial boundary length. -/
theorem rCellCount_le_three_mul_boundaryLength
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram W} (C : TriangularGirthEightDiagram Delta) :
    Delta.rCellCount <= 3 * Delta.combinatorialBoundaryLength :=
  le_trans Delta.rCellCount_le_innerFaceCount
    C.innerFaceCount_le_three_mul_boundaryLength

/-- Relator-cell area is at most three times the length of the word read on
the outer face. -/
theorem rCellCount_le_three_mul_boundaryWord_length
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram W} (C : TriangularGirthEightDiagram Delta) :
    Delta.rCellCount <= 3 * Delta.boundaryWord.length := by
  rw [Delta.boundaryWord_length_eq_combinatorialBoundaryLength]
  exact C.rCellCount_le_three_mul_boundaryLength

end TriangularGirthEightDiagram

end VanKampen
end GGT
end GroupApproximation
