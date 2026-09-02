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
    {M : VanKampen.CombMap.{0}} {v : M.Vertex}
    (C : CyclicCornerEnumeration M v) where
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
    linkVertex (i + M.vertexDegree v) = linkVertex i

/-- Cellular reducedness at a vertex: the two relator corners on the two
sides of any intervening edge do not carry mirror link labels.  Equivalently,
the cyclic link walk never immediately traverses an edge and its reverse. -/
abbrev CellularReducedAt
    {M : VanKampen.CombMap.{0}} {v : M.Vertex}
    {C : CyclicCornerEnumeration M v}
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
    {M : VanKampen.CombMap.{0}} {v : M.Vertex}
    (C : CyclicCornerEnumeration M v)
    (K : VertexCornerCertificate C) (hred : CellularReducedAt K) :
    PresentationLinkWalk T (M.vertexDegree v) where
  vertex := K.linkVertex
  periodic := K.periodic
  adjacent i := by
    rw [K.source_eq i, K.target_eq i]
    exact adjacencyCount_pos_of_literalCorner (T := T) (K.triangle i) (K.position i)
  noBacktrack := hred
  three_le := three_le_of_periodic_noMirror
    (by
      obtain ⟨i, hi, _⟩ := C.covers
        (M.vertexRepresentative v)
        (M.vertexOf_vertexRepresentative v)
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

/-- The inner part of a boundary face-star layer.  Intersecting with
`innerFaces` removes the distinguished exterior face that belongs to the
zero-th boundary star. -/
noncomputable def innerBoundaryFaceStarLayer
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) (i : ℕ) : Finset Delta.toCombMap.Face :=
  GirthEightPrimitives.boundaryFaceStarLayer Delta P i ∩ Delta.innerFaces

/-- Inner face-star layers are pairwise disjoint, so their total cardinality
is at most `innerFaceCount`.  This proves the second inequality consumed by
`girthEight_layer_depth_bound`. -/
theorem innerBoundaryFaceStarLayer_sum_le_innerFaceCount
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) (depth : ℕ) :
    (∑ i : Fin depth,
      (innerBoundaryFaceStarLayer Delta P i).card) ≤
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
      (fun i ↦ M.faceStarLayer seed i ∩ Delta.innerFaces) := by
    intro i _hi j _hj hij
    exact (hlayerDisjoint (by
      intro hval
      apply hij
      exact Fin.ext hval)).mono Finset.inter_subset_left Finset.inter_subset_left
  change (∑ i : Fin depth,
    (M.faceStarLayer seed i ∩ Delta.innerFaces).card) ≤ Delta.innerFaces.card
  rw [← Finset.card_biUnion hpairwise]
  apply Finset.card_le_card
  intro f hf
  obtain ⟨i, _hi, hfi⟩ := Finset.mem_biUnion.mp hf
  exact (Finset.mem_inter.mp hfi).2

/-- A combinatorial certificate for the layer-covering estimate: every
surviving boundary position injects into a pair consisting of an inner layer
face and one of at most `perimeter` incidences on that face. -/
structure LayerIncidenceInjection
    {Face : Type} [DecidableEq Face]
    (layer : Fin depth → Finset Face) (scale loss perimeter : ℕ) where
  /-- Assign a face and an incidence slot to each surviving position. -/
  encode : ∀ i : Fin depth,
    Fin (scale - loss) → {f // f ∈ layer i} × Fin perimeter
  /-- Different positions have different face-incidence pairs. -/
  injective : ∀ i, Function.Injective (encode i)

/-- An incidence injection proves the numerical covering inequality. -/
theorem layer_covers_of_incidenceInjection
    {Face : Type} [DecidableEq Face]
    {layer : Fin depth → Finset Face} {scale loss perimeter : ℕ}
    (C : LayerIncidenceInjection layer scale loss perimeter) :
    ∀ i : Fin depth, scale - loss ≤ perimeter * (layer i).card := by
  intro i
  have hcard := Fintype.card_le_of_injective (C.encode i) (C.injective i)
  simpa only [Fintype.card_fin, Fintype.card_prod, Fintype.card_coe,
    Nat.mul_comm] using hcard

/-- The genuinely geometric local estimate for a star layer: after losing the
two endpoint neighborhoods, its triangular faces cover the surviving window.
It is deliberately separate from disjointness, which is proved above. -/
abbrev LayerCoversWindow
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) (depth scale loss perimeter : ℕ) : Prop :=
  ∀ i : Fin depth, scale - loss ≤ perimeter *
    (innerBoundaryFaceStarLayer Delta P i).card

/-- Explicit boundary-position incidences prove `LayerCoversWindow`. -/
theorem layerCoversWindow_of_incidenceInjection
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) (depth scale loss perimeter : ℕ)
    (C : LayerIncidenceInjection
      (fun i : Fin depth ↦ innerBoundaryFaceStarLayer Delta P i)
      scale loss perimeter) :
    LayerCoversWindow Delta P depth scale loss perimeter :=
  layer_covers_of_incidenceInjection C

omit [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex] in
/-- The third layer inequality is exactly the per-layer geometric covering
estimate, with the actual star-layer cardinality exposed. -/
theorem boundaryFaceStarLayer_covers
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) (depth scale loss perimeter : ℕ)
    (hcover : LayerCoversWindow Delta P depth scale loss perimeter) :
    ∀ i : Fin depth, scale - loss ≤ perimeter *
      (innerBoundaryFaceStarLayer Delta P i).card :=
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
  layer i := (innerBoundaryFaceStarLayer Delta side i).card
  boundary_bound := hboundary
  layer_disjoint := innerBoundaryFaceStarLayer_sum_le_innerFaceCount
    Delta side depth
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

/-- The one-triangle zero-th layer has an explicit unit incidence injection,
so the new covering certificate is inhabited nonvacuously. -/
noncomputable def oneTriangle_unitIncidenceInjection :
    LayerIncidenceInjection
      (fun _ : Fin 1 ↦ VanKampen.oneTriangleCombMap.faceStarLayer
        (Finset.univ : Finset VanKampen.oneTriangleCombMap.Face) 0)
      1 0 1 := by
  classical
  refine {
    encode := fun _ _ ↦
      (⟨VanKampen.oneTriangleCombMap.faceOf (0, false), ?_⟩, 0)
    injective := ?_ }
  · rw [VanKampen.CombMap.faceStarLayer, if_pos rfl]
    exact Finset.mem_univ _
  · intro i x y _hxy
    exact Subsingleton.elim x y

/-- The incidence-count theorem recovers the unit covering inequality in the
one-triangle model. -/
theorem oneTriangle_unit_cover_of_incidenceInjection :
    ∀ i : Fin 1, 1 - 0 ≤ 1 *
      (VanKampen.oneTriangleCombMap.faceStarLayer
        (Finset.univ : Finset VanKampen.oneTriangleCombMap.Face) 0).card :=
  layer_covers_of_incidenceInjection oneTriangle_unitIncidenceInjection

end Table

/-! ## Least-area power discs and cancellation surgery -/

section PowerDisc

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]
  {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
  {g : TriangularHodgeLayer.Presented T} {n : ℕ}

/-- A relator-only filling of a literal power boundary, before imposing
minimality or reducedness. -/
structure PowerDiscCandidate
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (g : TriangularHodgeLayer.Presented T) (n : ℕ) where
  /-- Literal signed word representing the group element. -/
  word : List (TriangularHodgeLayer.SignedGenerator Generator)
  /-- The chosen word represents `g`. -/
  represents : PresentedGroup.mk
      (TriangularHodgeLayer.relators T : Set (FreeGroup Generator))
      (PresentedGroupRelatorReplay.word word) = g
  /-- Filling diagram. -/
  diagram : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T)
  /-- Its exterior is the literal `n`-fold repetition. -/
  boundary_eq : diagram.boundaryWord =
    (List.replicate n (word.map signedFreeRelLetter)).flatten
  /-- Every inner face is a defining relator face. -/
  relatorOnly : RelatorOnly T diagram

/-- Every element of a triangularly presented group has a literal signed-word
representative. -/
theorem exists_signedWord_represents
    (g : TriangularHodgeLayer.Presented T) :
    ∃ word : List (TriangularHodgeLayer.SignedGenerator Generator),
      PresentedGroup.mk
        (TriangularHodgeLayer.relators T : Set (FreeGroup Generator))
        (PresentedGroupRelatorReplay.word word) = g := by
  classical
  obtain ⟨x, hx⟩ := PresentedGroup.mk_surjective
    (TriangularHodgeLayer.relators T : Set (FreeGroup Generator)) g
  refine ⟨x.toWord, ?_⟩
  rw [PresentedGroupRelatorReplay.word, FreeGroup.mk_toWord]
  exact hx

/-- The remaining van Kampen input for a literal power is only the existence
of a relator-only diagram with that exact exterior word.  Once supplied, it
gives a `PowerDiscCandidate`; word representation is proved above. -/
theorem nonempty_powerDiscCandidate_of_literalFilling
    (hn : 0 < n) (hpow : g ^ n = 1) (hne : g ≠ 1)
    (fill : ∀
      (word : List (TriangularHodgeLayer.SignedGenerator Generator)),
      PresentedGroup.mk
          (TriangularHodgeLayer.relators T : Set (FreeGroup Generator))
          (PresentedGroupRelatorReplay.word word) = g →
      0 < n → g ^ n = 1 → g ≠ 1 →
      ∃ Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T),
        Delta.boundaryWord =
          (List.replicate n (word.map signedFreeRelLetter)).flatten ∧
        RelatorOnly T Delta) :
    Nonempty (PowerDiscCandidate T g n) := by
  obtain ⟨word, hword⟩ := exists_signedWord_represents g
  obtain ⟨Delta, hboundary, hrelatorOnly⟩ :=
    fill word hword hn hpow hne
  exact ⟨{
    word := word
    represents := hword
    diagram := Delta
    boundary_eq := hboundary
    relatorOnly := hrelatorOnly }⟩

/-- A reduced candidate is the interface's `PowerDisc`. -/
def PowerDiscCandidate.toPowerDisc (D : PowerDiscCandidate T g n)
    (hred : D.diagram.Reduced) : PowerDisc T g n where
  word := D.word
  represents := D.represents
  diagram := D.diagram
  boundary_eq := D.boundary_eq
  reduced := hred
  relatorOnly := D.relatorOnly

/-- Candidate areas form a nonempty subset of the natural numbers. -/
theorem exists_powerDiscCandidate_area
    (hfill : Nonempty (PowerDiscCandidate T g n)) :
    ∃ area : ℕ, ∃ D : PowerDiscCandidate T g n,
      D.diagram.rCellCount = area := by
  obtain ⟨D⟩ := hfill
  exact ⟨D.diagram.rCellCount, D, rfl⟩

/-- Least relator area among candidates with the fixed literal power
boundary. -/
noncomputable def leastPowerDiscArea
    (hfill : Nonempty (PowerDiscCandidate T g n)) : ℕ :=
  Nat.find (exists_powerDiscCandidate_area hfill)

/-- A candidate attaining the least relator area. -/
noncomputable def leastPowerDiscCandidate
    (hfill : Nonempty (PowerDiscCandidate T g n)) :
    PowerDiscCandidate T g n :=
  Classical.choose (Nat.find_spec (exists_powerDiscCandidate_area hfill))

/-- The selected candidate has the declared least area. -/
theorem leastPowerDiscCandidate_area_eq
    (hfill : Nonempty (PowerDiscCandidate T g n)) :
    (leastPowerDiscCandidate hfill).diagram.rCellCount =
      leastPowerDiscArea hfill :=
  Classical.choose_spec (Nat.find_spec (exists_powerDiscCandidate_area hfill))

/-- No candidate with the same literal boundary has smaller relator area. -/
theorem leastPowerDiscCandidate_area_le
    (hfill : Nonempty (PowerDiscCandidate T g n))
    (D : PowerDiscCandidate T g n) :
    (leastPowerDiscCandidate hfill).diagram.rCellCount ≤
      D.diagram.rCellCount := by
  rw [leastPowerDiscCandidate_area_eq]
  exact Nat.find_min' (exists_powerDiscCandidate_area hfill) ⟨D, rfl⟩

/-- The local surgery property needed from a cellular cancellation: whenever
two stored relator cells form a cancelling pair in the sense of
`DiscDiagram.Reduced`, cutting that pair out produces a candidate with the
same literal power boundary and strictly smaller relator area. -/
abbrev CancellationReducesArea (D : PowerDiscCandidate T g n) : Prop :=
  ∀ (pre between suf : List
      (VanKampen.RelatorCell D.diagram.toCombMap D.diagram.outerFace
        (triangleRelatorWords T)))
    (C₁ C₂ : VanKampen.RelatorCell D.diagram.toCombMap D.diagram.outerFace
      (triangleRelatorWords T)),
    D.diagram.relatorCells = pre ++ C₁ :: (between ++ C₂ :: suf) →
    (between.map VanKampen.RelatorCell.value).prod⁻¹ * C₁.value *
      (between.map VanKampen.RelatorCell.value).prod * C₂.value = 1 →
    ∃ D' : PowerDiscCandidate T g n,
      D'.diagram.rCellCount < D.diagram.rCellCount

/-- Least area gives diagram reducedness exactly when cancelling pairs admit
the area-decreasing surgery above. -/
theorem leastPowerDiscCandidate_reduced
    (hfill : Nonempty (PowerDiscCandidate T g n))
    (hsurgery : CancellationReducesArea (leastPowerDiscCandidate hfill)) :
    (leastPowerDiscCandidate hfill).diagram.Reduced := by
  intro pre between suf C₁ C₂ hsplit hcancel
  obtain ⟨D', hlt⟩ := hsurgery pre between suf C₁ C₂ hsplit hcancel
  have hle := leastPowerDiscCandidate_area_le hfill D'
  omega

/-- This is the precise least-power-disc constructor used by ko's
`GirthEightDiagramPrimitives.leastPowerDisc`: van Kampen filling supplies one
candidate, and cellular cancellation surgery makes a least candidate reduced. -/
noncomputable def leastPowerDisc_of_filling
    (hn : 0 < n) (hpow : g ^ n = 1) (hne : g ≠ 1)
    (fill : 0 < n → g ^ n = 1 → g ≠ 1 →
      Nonempty (PowerDiscCandidate T g n))
    (surgery : ∀ D : PowerDiscCandidate T g n,
      CancellationReducesArea D) : PowerDisc T g n := by
  let hfill := fill hn hpow hne
  exact (leastPowerDiscCandidate hfill).toPowerDisc
    (leastPowerDiscCandidate_reduced hfill
      (surgery (leastPowerDiscCandidate hfill)))

/-- Version of the least-power constructor whose filling hypothesis mentions
only the exact diagram supplied by van Kampen's lemma, rather than a packaged
candidate. -/
noncomputable def leastPowerDisc_of_literalFilling
    (hn : 0 < n) (hpow : g ^ n = 1) (hne : g ≠ 1)
    (fill : ∀
      (word : List (TriangularHodgeLayer.SignedGenerator Generator)),
      PresentedGroup.mk
          (TriangularHodgeLayer.relators T : Set (FreeGroup Generator))
          (PresentedGroupRelatorReplay.word word) = g →
      0 < n → g ^ n = 1 → g ≠ 1 →
      ∃ Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T),
        Delta.boundaryWord =
          (List.replicate n (word.map signedFreeRelLetter)).flatten ∧
        RelatorOnly T Delta)
    (surgery : ∀ D : PowerDiscCandidate T g n,
      CancellationReducesArea D) : PowerDisc T g n := by
  let hfill : Nonempty (PowerDiscCandidate T g n) :=
    nonempty_powerDiscCandidate_of_literalFilling hn hpow hne fill
  exact (leastPowerDiscCandidate hfill).toPowerDisc
    (leastPowerDiscCandidate_reduced hfill
      (surgery (leastPowerDiscCandidate hfill)))

/-- A candidate with no stored relator cells satisfies the cancellation
surgery premise vacuously.  This is the zero-area model test for the new local
property. -/
theorem cancellationReducesArea_of_noCells
    (D : PowerDiscCandidate T g n) (hcells : D.diagram.relatorCells = []) :
    CancellationReducesArea D := by
  intro pre between suf C₁ C₂ hsplit _hcancel
  rw [hcells] at hsplit
  have hlength := congrArg List.length hsplit
  simp only [List.length_nil, List.length_append, List.length_cons] at hlength
  omega

/-! ## Rotated-copy gluing and the spherical certificate -/

/-- Combinatorial data produced by gluing rotated copies of a power disc.
Every spherical face names its copy and its source inner face, and the degree
is preserved.  The remaining fields are the local relator-corner certificates
and the no-mirror condition on the glued seams. -/
structure PowerDiscSphereGluing (D : PowerDisc T g n) where
  /-- The closed planar map after gluing. -/
  sphere : VanKampen.SphericalCombMap.{0}
  /-- Rotated copy from which a spherical face comes. -/
  sourceCopy : sphere.toCombMap.Face → Fin n
  /-- Source face in that copy of the disc. -/
  sourceFace : sphere.toCombMap.Face → D.diagram.toCombMap.Face
  /-- Exterior faces are removed by the gluing. -/
  sourceFace_ne_outer : ∀ f, sourceFace f ≠ D.diagram.outerFace
  /-- Gluing preserves the boundary degree of every source face. -/
  faceDegree_eq : ∀ f, sphere.toCombMap.faceDegree f =
    D.diagram.toCombMap.faceDegree (sourceFace f)
  /-- Cyclic corners of the glued map. -/
  cornerCycle : ∀ v, CyclicCornerEnumeration sphere.toCombMap v
  /-- Literal presentation-link labels at glued corners. -/
  cornerCertificate : ∀ v, VertexCornerCertificate (cornerCycle v)
  /-- Least-area seam reduction rules out mirror corner pairs. -/
  cellularReduced : ∀ v, CellularReducedAt (cornerCertificate v)

/-- A rotated-copy gluing certificate gives the exact labelled reduced sphere
consumed by `presented_isPowerTorsionFree_of_sphericalExtraction`. -/
noncomputable def triangularRelatorSphericalMap_of_powerDiscGluing
    (D : PowerDisc T g n) (G : PowerDiscSphereGluing D) :
    VanKampen.TriangularRelatorSphericalMap T G.sphere.toCombMap where
  planar := G.sphere.planar
  faceRelator f := by
    obtain ⟨j, _hj⟩ := D.relatorOnly.exists_faceWord_eq
      (G.sourceFace f) (G.sourceFace_ne_outer f)
    refine ⟨j, ?_⟩
    have hmem : G.sourceFace f ∈ D.diagram.innerFaces := by
      simpa only [VanKampen.DiscDiagram.innerFaces, Finset.mem_sdiff,
        Finset.mem_univ, true_and, Finset.mem_singleton] using
        G.sourceFace_ne_outer f
    calc
      G.sphere.toCombMap.faceDegree f =
          D.diagram.toCombMap.faceDegree (G.sourceFace f) := G.faceDegree_eq f
      _ = 3 := D.relatorOnly.innerFaceDegree (G.sourceFace f) hmem
      _ = (TriangularHodgeLayer.letters (T j)).length := by
        simp only [TriangularHodgeLayer.letters_eq_three, List.length_cons,
          List.length_nil, Nat.reduceAdd]
  vertexLink v := presentationLinkWalk_of_cellularReduced
    (G.cornerCycle v) (G.cornerCertificate v) (G.cellularReduced v)

/-- The gluing certificate has exactly ko's `gluePowerDisc` conclusion. -/
theorem exists_labelledSphere_of_powerDiscGluing
    (D : PowerDisc T g n) (G : PowerDiscSphereGluing D) :
    ∃ M : VanKampen.CombMap.{0},
      Nonempty (VanKampen.TriangularRelatorSphericalMap T M) :=
  ⟨G.sphere.toCombMap,
    ⟨triangularRelatorSphericalMap_of_powerDiscGluing D G⟩⟩

/-- Constructor in the exact shape of
`GirthEightDiagramPrimitives.gluePowerDisc`: the topological rotated-copy
operation supplies `PowerDiscSphereGluing`, and the local theorem above
supplies the labelled reduced sphere. -/
theorem gluePowerDisc_of_rotationGluing
    (D : PowerDisc T g n)
    (glue : (∀ j, ¬ RelatorIsProperPower
      (TriangularHodgeLayer.relator (T j))) → PowerDiscSphereGluing D)
    (hnoProper : ∀ j, ¬ RelatorIsProperPower
      (TriangularHodgeLayer.relator (T j))) :
    ∃ M : VanKampen.CombMap.{0},
      Nonempty (VanKampen.TriangularRelatorSphericalMap T M) :=
  exists_labelledSphere_of_powerDiscGluing D (glue hnoProper)

end PowerDisc

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
