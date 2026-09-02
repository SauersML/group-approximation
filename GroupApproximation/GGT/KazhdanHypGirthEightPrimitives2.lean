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

end Table

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

section Cayley

variable {Generator TriangleIndex : Type}
  [DecidableEq Generator] [Fintype TriangleIndex]
  {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}

/-- Evaluate a diagram path in its triangularly presented Cayley group. -/
def cayleyPathValue
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    {x y : Delta.toCombMap.Vertex} (p : DartPath Delta.toCombMap x y) :
    TriangularHodgeLayer.Presented T :=
  (p.darts.map fun d ↦ presentedLetterValue T (Delta.label d)).prod

theorem cayleyPathValue_append
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    {x y z : Delta.toCombMap.Vertex}
    (p : DartPath Delta.toCombMap x y) (q : DartPath Delta.toCombMap y z) :
    cayleyPathValue Delta (p.append q) =
      cayleyPathValue Delta p * cayleyPathValue Delta q := by
  simp [cayleyPathValue, List.map_append, List.prod_append]

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
        change cayleyPathValue Delta
          ((R.pathTo (Delta.toCombMap.vertexOf d)).append
            (DartPath.single d)) = _
        rw [cayleyPathValue_append, cayleyPathValue_single]

/-- The one-triangle model has a genuine one-edge path whose dart list is the
chosen dart. -/
theorem oneTriangle_single_path_darts (d : VanKampen.OneTriangleDart) :
    (DartPath.single (M := VanKampen.oneTriangleCombMap) d).darts = [d] :=
  rfl

end Cayley

/-! ## The four successive-star inequalities -/

section Table

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]
  {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}

omit [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex] in
/-- If the truncated boundary is a concatenation of six pieces of length at
most `scale`, its total combinatorial length is at most `6 * scale`.  This is
the first inequality consumed by
`GirthEightSlim.girthEight_layer_depth_bound`. -/
theorem boundaryLength_le_six_mul_of_six_pieces
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (scale : ℕ) (a b c d e f : List Delta.toCombMap.Dart)
    (hsplit : (Delta.faceBoundary Delta.outerFace).darts =
      a ++ b ++ c ++ d ++ e ++ f)
    (ha : a.length ≤ scale) (hb : b.length ≤ scale)
    (hc : c.length ≤ scale) (hd : d.length ≤ scale)
    (he : e.length ≤ scale) (hf : f.length ≤ scale) :
    Delta.combinatorialBoundaryLength ≤ 6 * scale := by
  calc
    Delta.combinatorialBoundaryLength =
        (Delta.faceBoundary Delta.outerFace).darts.length :=
      (Delta.faceBoundary Delta.outerFace).length_eq_degree.symm
    _ = (a ++ b ++ c ++ d ++ e ++ f).length := congrArg List.length hsplit
    _ ≤ 6 * scale := by
      simp only [List.length_append]
      omega

/-- Actual face-star layers are pairwise disjoint; if the selected layers are
inner faces, their total cardinality is at most `innerFaceCount`.  This proves
the second inequality consumed by `girthEight_layer_depth_bound`. -/
theorem boundaryFaceStarLayer_sum_le_innerFaceCount
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) (depth : ℕ)
    (hinner : ∀ i : Fin depth,
      GirthEightPrimitives.boundaryFaceStarLayer Delta P i ⊆
        Delta.innerFaces) :
    (∑ i : Fin depth,
      (GirthEightPrimitives.boundaryFaceStarLayer Delta P i).card) ≤
        Delta.innerFaceCount := by
  classical
  let M := Delta.toCombMap
  let seed := GirthEightPrimitives.boundaryFaceSeed Delta P
  have hballMono : ∀ {i j : ℕ}, i ≤ j →
      M.faceStarBall seed i ⊆ M.faceStarBall seed j := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact fun _ h ↦ h
    | succ j _ ih => exact ih.trans (M.faceStarBall_mono_succ seed j)
  have hlayerSubset : ∀ n : ℕ,
      M.faceStarLayer seed n ⊆ M.faceStarBall seed n := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp [VanKampen.CombMap.faceStarLayer]
    · rw [VanKampen.CombMap.faceStarLayer, if_neg hn]
      exact Finset.sdiff_subset
  have hlayerDisjoint : ∀ {i j : ℕ}, i ≠ j →
      Disjoint (M.faceStarLayer seed i) (M.faceStarLayer seed j) := by
    intro i j hij
    wlog hlt : i < j generalizing i j with H
    · exact (H hij.symm (by omega)).symm
    have hjpos : j ≠ 0 := by omega
    rw [Finset.disjoint_left]
    intro f hfi hfj
    have hfiBall : f ∈ M.faceStarBall seed i := hlayerSubset i hfi
    have hfpred : f ∈ M.faceStarBall seed (j - 1) :=
      hballMono (by omega) hfiBall
    rw [VanKampen.CombMap.faceStarLayer, if_neg hjpos] at hfj
    exact hfj.2 hfpred
  have hpairwise : ((Finset.univ : Finset (Fin depth)) : Set (Fin depth)).PairwiseDisjoint
      (fun i ↦ M.faceStarLayer seed i) := by
    intro i _hi j _hj hij
    exact hlayerDisjoint (by
      intro hval
      apply hij
      exact Fin.ext hval)
  change (∑ i : Fin depth, (M.faceStarLayer seed i).card) ≤ Delta.innerFaces.card
  rw [← Finset.card_biUnion hpairwise]
  apply Finset.card_le_card
  intro f hf
  obtain ⟨i, _hi, hfi⟩ := Finset.mem_biUnion.mp hf
  exact hinner i hfi

/-- The genuinely geometric local estimate for a star layer: after losing the
two endpoint neighborhoods, its triangular faces cover the surviving window.
It is deliberately separate from disjointness, which is proved above. -/
abbrev LayerCoversWindow
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) (depth scale loss perimeter : ℕ) : Prop :=
  ∀ i : Fin depth, scale - loss ≤ perimeter *
    (GirthEightPrimitives.boundaryFaceStarLayer Delta P i).card

omit [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex] in
/-- The third layer inequality is exactly the per-layer geometric covering
estimate, with the actual star-layer cardinality exposed. -/
theorem boundaryFaceStarLayer_covers
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) (depth scale loss perimeter : ℕ)
    (hcover : LayerCoversWindow Delta P depth scale loss perimeter) :
    ∀ i : Fin depth, scale - loss ≤ perimeter *
      (GirthEightPrimitives.boundaryFaceStarLayer Delta P i).card :=
  hcover

/-- When the surviving window has positive length, there is an arithmetic
depth strictly beyond the curvature bound.  Geometry must show that the star
construction remains disjoint and covering up to this depth.  This is the
fourth inequality in the slimness consumer. -/
theorem exists_depth_too_large
    (scale loss perimeter : ℕ) (hloss : loss < scale) :
    ∃ depth : ℕ,
      18 * perimeter * scale < depth * (scale - loss) := by
  refine ⟨18 * perimeter * scale + 1, ?_⟩
  have hpos : 1 ≤ scale - loss := by omega
  calc
    18 * perimeter * scale < 18 * perimeter * scale + 1 := by omega
    _ ≤ (18 * perimeter * scale + 1) * (scale - loss) := by
      simpa only [mul_one] using
        Nat.mul_le_mul_left (18 * perimeter * scale + 1) hpos

/-- Package the four proved/named estimates into the exact layer record used
by `GirthEightDiagramPrimitives.isHyperbolicGroup`. -/
noncomputable def successiveStarLayers_of_geometricData
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (L : TriangularDiagramLocalData T Delta)
    (cayley : CayleyVertexLabelling T Delta) (side : BoundarySubpath T Delta)
    (depth scale loss perimeter : ℕ)
    (hboundary : Delta.combinatorialBoundaryLength ≤ 6 * scale)
    (hinner : ∀ i : Fin depth,
      GirthEightPrimitives.boundaryFaceStarLayer Delta side i ⊆
        Delta.innerFaces)
    (hcover : LayerCoversWindow Delta side depth scale loss perimeter)
    (hdepth : 18 * perimeter * scale < depth * (scale - loss)) :
    SuccessiveStarLayers T where
  diagram := Delta
  localData := L
  cayley := cayley
  side := side
  depth := depth
  scale := scale
  loss := loss
  perimeter := perimeter
  layer i := (GirthEightPrimitives.boundaryFaceStarLayer Delta side i).card
  boundary_bound := hboundary
  layer_disjoint := boundaryFaceStarLayer_sum_le_innerFaceCount
    Delta side depth hinner
  layer_covers := hcover
  depth_too_large := hdepth

/-- The zero-th star layer of the one-triangle model, seeded by all faces, is
nonempty.  Thus the covering inequality has a nonvacuous finite model. -/
theorem oneTriangle_zeroLayer_nonempty :
    (VanKampen.oneTriangleCombMap.faceStarLayer
      (Finset.univ : Finset VanKampen.oneTriangleCombMap.Face) 0).Nonempty := by
  classical
  rw [VanKampen.CombMap.faceStarLayer, if_pos rfl]
  exact ⟨VanKampen.oneTriangleCombMap.faceOf (0, false), Finset.mem_univ _⟩

/-- With unit scale and perimeter, that nonempty zero-th layer satisfies the
model covering inequality. -/
theorem oneTriangle_zeroLayer_unit_cover :
    1 ≤ (VanKampen.oneTriangleCombMap.faceStarLayer
      (Finset.univ : Finset VanKampen.oneTriangleCombMap.Face) 0).card :=
  Finset.card_pos.mpr oneTriangle_zeroLayer_nonempty

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
