import GroupApproximation.GGT.VanKampen.CombMapReduction

/-!
# Reduced links, Cayley potentials, star estimates, and power discs

This module supplies the remaining *conditional* girth-eight diagram
constructions.  Each construction is stated under the local topological
hypothesis that makes it true.  In particular, algebraic
`DiscDiagram.Reduced` is not silently identified with cellular reducedness:
the latter is the explicit no-mirror condition on consecutive relator
corners below.
-/

namespace GroupApproximation
namespace GGT
namespace GirthEightPrimitives2

open GroupApproximation.KazhdanHyp
open GirthEightVKInterface
open scoped BigOperators

section Table

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]
  {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}

/-! ## Cellular reducedness and the presentation link -/

omit [Fintype Generator] [DecidableEq TriangleIndex] in
/-- One literal triangle corner contributes a positive directed edge to the
presentation link. -/
theorem adjacencyCount_pos_of_literalCorner (j : TriangleIndex) (k : Fin 3) :
    0 < TriangularHodgeLayer.adjacencyCount T (T j k)
      (TriangularHodgeLayer.inverseSigned
        (T j (TriangularHodgeLayer.nextCorner k))) := by
  classical
  unfold TriangularHodgeLayer.adjacencyCount
    TriangularHodgeLayer.directedAdjacencyCount
  have hmem : (j, k) ∈
      ((Finset.univ : Finset (TriangleIndex × Fin 3)).filter fun p ↦
        T p.1 p.2 = T j k ∧
          TriangularHodgeLayer.inverseSigned
            (T p.1 (TriangularHodgeLayer.nextCorner p.2)) =
          TriangularHodgeLayer.inverseSigned
            (T j (TriangularHodgeLayer.nextCorner k))) := by
    simp
  have hpos := Finset.card_pos.mpr ⟨(j, k), hmem⟩
  omega

/-- Relator-position labels on the cyclic corners at one map vertex.

The witness says that every step around the vertex is the link edge supplied
by one literal position of one defining triangle.  This is precisely the
bookkeeping extracted from `TriangleFacePositions`; it contains no
nonbacktracking assumption. -/
structure VertexCornerCertificate
    {Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T)}
    {v : Delta.toCombMap.Vertex}
    (C : CyclicCornerEnumeration Delta.toCombMap v) where
  /-- Presentation-link vertex at each cyclic corner. -/
  linkVertex : ℕ → TriangularHodgeLayer.SignedGenerator Generator
  /-- Triangle supplying the corner step. -/
  triangle : ℕ → TriangleIndex
  /-- Literal position supplying the corner step. -/
  position : ℕ → Fin 3
  /-- The initial endpoint is the literal signed generator. -/
  source_eq : ∀ i, linkVertex i = T (triangle i) (position i)
  /-- The terminal endpoint is the inverse of the next literal generator. -/
  target_eq : ∀ i, linkVertex (i + 1) =
    TriangularHodgeLayer.inverseSigned
      (T (triangle i) (TriangularHodgeLayer.nextCorner (position i)))
  /-- Labels repeat when the map corner cycle repeats. -/
  periodic : ∀ i,
    linkVertex (i + Delta.toCombMap.vertexDegree v) = linkVertex i

/-- Cellular reducedness at a vertex: the two relator corners on the two
sides of any intervening edge do not carry mirror link labels.  Equivalently,
the cyclic link walk never immediately traverses an edge and its reverse. -/
abbrev CellularReducedAt
    {Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T)}
    {v : Delta.toCombMap.Vertex}
    {C : CyclicCornerEnumeration Delta.toCombMap v}
    (K : VertexCornerCertificate C) : Prop :=
  ∀ i, K.linkVertex i ≠ K.linkVertex (i + 2)

/-- A positive period and the no-mirror condition force at least three
corners. -/
theorem three_le_of_periodic_noMirror
    {A : Type} {n : ℕ} {a : ℕ → A}
    (hn : 0 < n) (hperiodic : ∀ i, a (i + n) = a i)
    (hnoMirror : ∀ i, a i ≠ a (i + 2)) : 3 ≤ n := by
  by_contra hsmall
  have hnle : n ≤ 2 := by omega
  have hcases : n = 1 ∨ n = 2 := by omega
  rcases hcases with hn1 | hn2
  · subst n
    have h0 := hperiodic 0
    have h1 := hperiodic 1
    apply hnoMirror 0
    simpa using h0.symm.trans h1.symm
  · subst n
    have h0 := hperiodic 0
    apply hnoMirror 0
    simpa using h0.symm

/-- The cellular no-mirror predicate turns the cyclic corner certificate into
the exact `PresentationLinkWalk` consumed by
`TriangularDiagramLocalData.interiorVertexWalk`. -/
noncomputable def presentationLinkWalk_of_cellularReduced
    {Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T)}
    {v : Delta.toCombMap.Vertex}
    (C : CyclicCornerEnumeration Delta.toCombMap v)
    (K : VertexCornerCertificate C) (hred : CellularReducedAt K) :
    PresentationLinkWalk T (Delta.toCombMap.vertexDegree v) where
  vertex := K.linkVertex
  periodic := K.periodic
  adjacent i := by
    rw [K.source_eq i, K.target_eq i]
    exact adjacencyCount_pos_of_literalCorner (T := T) (K.triangle i) (K.position i)
  noBacktrack := hred
  three_le := three_le_of_periodic_noMirror
    (by
      obtain ⟨i, hi, _⟩ := C.covers
        (Delta.toCombMap.vertexRepresentative v)
        (Delta.toCombMap.vertexOf_vertexRepresentative v)
      omega)
    K.periodic hred

/-- Vertexwise cellular certificates and no-mirror reducedness assemble the
interior-link field without conflating it with algebraic diagram reducedness.
Together with the already proved relator-cell cover and boundary degree this
is exactly `TriangularDiagramLocalData`. -/
noncomputable def localData_of_cellularReduced
    {Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T)}
    (R : RelatorOnly T Delta)
    (hboundary : ∀ v, v ∈ discOuterBoundaryVertices Delta →
      2 ≤ Delta.toCombMap.vertexDegree v)
    (corner : ∀ v, CyclicCornerEnumeration Delta.toCombMap v)
    (certificate : ∀ v, v ∉ discOuterBoundaryVertices Delta →
      VertexCornerCertificate (corner v))
    (cellularReduced : ∀ v (hv : v ∉ discOuterBoundaryVertices Delta),
      CellularReducedAt (certificate v hv)) :
    TriangularDiagramLocalData T Delta where
  innerFaceCell := R.cell
  interiorVertexWalk v hv :=
    presentationLinkWalk_of_cellularReduced (corner v)
      (certificate v hv) (cellularReduced v hv)
  boundaryVertexDegree := hboundary

/-! ## Cayley labels from path integration -/

/-- A directed edge path in the one-skeleton of a combinatorial map. -/
inductive DartPath (M : VanKampen.CombMap.{u}) : M.Vertex → M.Vertex → Type u
  | nil (v : M.Vertex) : DartPath M v v
  | cons (d : M.Dart) {finish : M.Vertex}
      (rest : DartPath M (M.vertexOf (M.alpha d)) finish) :
      DartPath M (M.vertexOf d) finish

namespace DartPath

variable {M : VanKampen.CombMap.{u}}

/-- Concatenate two directed dart paths. -/
def append {x y z : M.Vertex} :
    DartPath M x y → DartPath M y z → DartPath M x z
  | .nil _, q => q
  | .cons d rest, q => .cons d (rest.append q)

/-- The path consisting of one oriented dart. -/
def single (d : M.Dart) :
    DartPath M (M.vertexOf d) (M.vertexOf (M.alpha d)) :=
  .cons d (.nil _)

/-- The oriented darts traversed by a path. -/
def darts {x y : M.Vertex} : DartPath M x y → List M.Dart
  | .nil _ => []
  | .cons d rest => d :: rest.darts

@[simp]
theorem darts_append {x y z : M.Vertex}
    (p : DartPath M x y) (q : DartPath M y z) :
    (p.append q).darts = p.darts ++ q.darts := by
  induction p with
  | nil => rfl
  | cons d rest ih => simp [append, darts, ih]

@[simp]
theorem darts_single (d : M.Dart) : (single d).darts = [d] :=
  rfl

end DartPath

/-- A chosen path from one base vertex to every map vertex.  Connectivity of
the one-skeleton supplies this data; keeping it explicit avoids a second,
noncomputable graph-path implementation. -/
structure RootedPathSystem (M : VanKampen.CombMap.{u}) where
  /-- Base vertex. -/
  root : M.Vertex
  /-- Chosen path from the base to a vertex. -/
  pathTo : ∀ v, DartPath M root v

/-- Evaluate a diagram path in its triangularly presented Cayley group. -/
def cayleyPathValue
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    {x y : Delta.toCombMap.Vertex} (p : DartPath Delta.toCombMap x y) :
    TriangularHodgeLayer.Presented T :=
  (p.darts.map fun d ↦ presentedLetterValue T (Delta.label d)).prod

@[simp]
theorem cayleyPathValue_append
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    {x y z : Delta.toCombMap.Vertex}
    (p : DartPath Delta.toCombMap x y) (q : DartPath Delta.toCombMap y z) :
    cayleyPathValue Delta (p.append q) =
      cayleyPathValue Delta p * cayleyPathValue Delta q := by
  simp [cayleyPathValue, List.map_append, List.prod_append]

@[simp]
theorem cayleyPathValue_single
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (d : Delta.toCombMap.Dart) :
    cayleyPathValue Delta (DartPath.single d) =
      presentedLetterValue T (Delta.label d) := by
  simp [cayleyPathValue]

/-- Path integration is well-defined from a fixed base vertex.  For a disc
diagram this follows from the elementary face-move theorem once every inner
face word is a relator or a trivial base word; that face-homotopy theorem is
not part of the current `CombMap` API, so this is its exact, strictly local
statement. -/
abbrev PathIntegralWellDefined
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (R : RootedPathSystem Delta.toCombMap) : Prop :=
  ∀ (v : Delta.toCombMap.Vertex)
    (p q : DartPath Delta.toCombMap R.root v),
    cayleyPathValue Delta p = cayleyPathValue Delta q

/-- Path-independent integration gives the exact Cayley vertex labelling used
by `SuccessiveStarLayers.cayley`. -/
noncomputable def cayleyVertexLabelling_of_pathIntegral
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (R : RootedPathSystem Delta.toCombMap)
    (hwell : PathIntegralWellDefined Delta R) :
    CayleyVertexLabelling T Delta where
  value v := cayleyPathValue Delta (R.pathTo v)
  edge d := by
    let extended := (R.pathTo (Delta.toCombMap.vertexOf d)).append
      (DartPath.single d)
    calc
      cayleyPathValue Delta
          (R.pathTo (Delta.toCombMap.vertexOf (Delta.toCombMap.alpha d))) =
          cayleyPathValue Delta extended :=
        (hwell _ extended (R.pathTo _)).symm
      _ = cayleyPathValue Delta
            (R.pathTo (Delta.toCombMap.vertexOf d)) *
          presentedLetterValue T (Delta.label d) := by
        simp [extended]

/-- The one-triangle model has a genuine one-edge path whose dart list is the
chosen dart. -/
theorem oneTriangle_single_path_darts (d : VanKampen.OneTriangleDart) :
    (DartPath.single (M := VanKampen.oneTriangleCombMap) d).darts = [d] :=
  rfl

end Table

/-! ## One-triangle model test -/

/-- Two rotations return every dart of the one-triangle model to itself. -/
theorem oneTriangle_sigma_sq (d : VanKampen.OneTriangleDart) :
    VanKampen.oneTriangleCombMap.sigma
      (VanKampen.oneTriangleCombMap.sigma d) = d := by
  rcases d with ⟨i, b⟩
  cases b
  · change (i - 1 + 1, false) = (i, false)
    simp
  · change (i + 1 - 1, true) = (i, true)
    simp

/-- Hence the two-corner orbit at a one-triangle boundary vertex fails the
no-mirror test.  This checks that the cellular predicate is genuinely local
to interior vertices and does not silently hold on boundary corners. -/
theorem oneTriangle_cornerOrbit_not_noMirror
    (d : VanKampen.OneTriangleDart) :
    ¬ ∀ i : ℕ,
      (VanKampen.oneTriangleCombMap.sigma ^ i) d ≠
        (VanKampen.oneTriangleCombMap.sigma ^ (i + 2)) d := by
  intro h
  apply h 0
  simp only [pow_zero, Equiv.Perm.one_apply, zero_add, pow_two,
    Equiv.Perm.mul_apply]
  exact (oneTriangle_sigma_sq d).symm

end GirthEightPrimitives2
end GGT
end GroupApproximation
