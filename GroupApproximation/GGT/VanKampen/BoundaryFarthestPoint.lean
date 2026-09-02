import GroupApproximation.GGT.VanKampen.CombMapStars

/-!
# Farthest points on a finite diagram boundary

The outer face of a `DiscDiagram` carries a finite, duplicate-free dart list.
Taking its image under `vertexOf` gives a finite boundary-vertex set.  This
file supplies the exact finite choice used by a far-point argument: a vertex
of maximal supplied combinatorial weight, an occurrence of that vertex on the
boundary, and the two list arcs on either side of that occurrence.

The theorem is deliberately parameterised by the vertex-weight function.  The
current `DiscDiagram` interface has no graph metric on its vertex quotient, so
the metric/geodesic theorem which instantiates this weight remains visible at
the consumer instead of being silently assumed here.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

universe u w v

open GroupApproximation.HullSC

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

noncomputable local instance boundaryVertexDecidableEq :
    DecidableEq Delta.toCombMap.Vertex := Classical.decEq _

/-! ## Boundary vertices and finite list factorisation -/

/-- The finite set of vertices visited by a stored face boundary. -/
noncomputable def faceBoundaryVertices
    {M : CombMap} {f : M.Face} (B : FaceBoundary M f) : Finset M.Vertex :=
  (B.darts.map M.vertexOf).toFinset

theorem faceBoundaryVertices_nonempty
    {M : CombMap} {f : M.Face} (B : FaceBoundary M f) :
    (faceBoundaryVertices B).Nonempty := by
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil B.nonempty
  refine ⟨M.vertexOf d, ?_⟩
  rw [faceBoundaryVertices, List.mem_toFinset]
  exact List.mem_map.mpr ⟨d, hd, rfl⟩

/-- Any occurrence in a list can be exposed as a distinguished element with
prefix and suffix.  This is the list-level boundary-cycle factorisation. -/
theorem exists_append_cons_of_mem
    {α : Type*} [DecidableEq α] (x : α) :
    ∀ {xs : List α}, x ∈ xs → ∃ before after, xs = before ++ x :: after := by
  intro xs
  induction xs with
  | nil => simp
  | cons y ys ih =>
      intro h
      by_cases hxy : x = y
      · subst x
        exact ⟨[], ys, rfl⟩
      · have hys : x ∈ ys := by simpa [hxy] using h
        obtain ⟨before, after, hsplit⟩ := ih hys
        refine ⟨y :: before, after, ?_⟩
        simp only [List.cons_append]
        rw [hsplit]

/-! ## The maximal boundary point certificate -/

/-- A boundary occurrence at a vertex of maximal supplied weight, together
with the two arcs obtained by cutting the stored cyclic list there. -/
structure BoundaryFarthestPoint
    {M : CombMap} {f : M.Face} (B : FaceBoundary M f)
    (weight : M.Vertex → ℕ) where
  /-- A dart occurrence on the boundary. -/
  dart : M.Dart
  dart_mem : dart ∈ B.darts
  /-- The vertex visited by the occurrence. -/
  vertex : M.Vertex
  vertex_eq : M.vertexOf dart = vertex
  /-- The selected vertex has maximal weight among boundary vertices. -/
  maximal : ∀ u ∈ faceBoundaryVertices B, weight u ≤ weight vertex
  /-- The boundary arc before the selected occurrence. -/
  before : List M.Dart
  /-- The boundary arc after the selected occurrence. -/
  after : List M.Dart
  /-- The cut factorization of the boundary cycle. -/
  split : B.darts = before ++ dart :: after

theorem farthestBoundaryPoint_of_faceBoundary
    {M : CombMap} {f : M.Face} (B : FaceBoundary M f)
    (weight : M.Vertex → ℕ) :
    Nonempty (BoundaryFarthestPoint B weight) := by
  classical
  let vertices := faceBoundaryVertices B
  let hvertices : vertices.Nonempty := faceBoundaryVertices_nonempty B
  let vertex := vertices.max' hvertices
  have hvertex : vertex ∈ vertices := Finset.max'_mem vertices hvertices
  rw [faceBoundaryVertices, List.mem_toFinset] at hvertex
  obtain ⟨dart, hdart, hdart_vertex⟩ := List.mem_map.mp hvertex
  obtain ⟨before, after, hsplit⟩ := exists_append_cons_of_mem dart hdart
  refine ⟨{
    dart := dart
    dart_mem := hdart
    vertex := vertex
    vertex_eq := hdart_vertex
    maximal := ?_
    before := before
    after := after
    split := hsplit }⟩
  intro u hu
  exact Finset.le_max' vertices u hu

theorem farthestBoundaryPoint_vertex_mem
    {M : CombMap} {f : M.Face} (B : FaceBoundary M f)
    (weight : M.Vertex → ℕ) (C : BoundaryFarthestPoint B weight) :
    C.vertex ∈ faceBoundaryVertices B := by
  rw [faceBoundaryVertices, List.mem_toFinset]
  exact List.mem_map.mpr ⟨C.dart, C.dart_mem, C.vertex_eq⟩

/-! ## Disc-diagram and one-triangle adapters -/

/-- The farthest-point certificate for the stored outer boundary of a disc
diagram. -/
theorem farthestBoundaryPoint_of_discDiagram
    (weight : Delta.toCombMap.Vertex → ℕ) :
    Nonempty (BoundaryFarthestPoint
      (Delta.faceBoundary Delta.outerFace) weight) :=
  farthestBoundaryPoint_of_faceBoundary
    (Delta.faceBoundary Delta.outerFace) weight

noncomputable section OneTriangleModel

local instance oneTriangleDartDecidableEq : DecidableEq OneTriangleDart :=
  Classical.decEq _

/-- The finite maximum-and-two-arcs construction is inhabited on the
one-triangle boundary for every vertex weight. -/
theorem oneTriangle_farthestBoundaryPoint_model
    (weight : oneTriangleCombMap.Vertex → ℕ) :
    Nonempty (BoundaryFarthestPoint
      (FaceBoundary.based oneTriangleCombMap (0, false)) weight) :=
  farthestBoundaryPoint_of_faceBoundary
    (FaceBoundary.based oneTriangleCombMap (0, false)) weight

end OneTriangleModel

end VanKampen
end GGT
end GroupApproximation
