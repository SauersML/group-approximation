import GroupApproximation.GGT.KazhdanHypGirthEightVKInterface
import GroupApproximation.GGT.VanKampen.DiscPathHomotopy
import GroupApproximation.GGT.KazhdanHypGirthEightPrimitives
import GroupApproximation.GGT.VanKampen.CombMapGluing
import GroupApproximation.GGT.VanKampen.CombMapReduction
import Mathlib.Data.Finset.Lattice.Basic

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

/-- The canonical cyclic corner enumeration works for every closed
combinatorial map, including a seam-glued sphere. -/
noncomputable def cornerCycleOfCombMap
    (M : VanKampen.CombMap.{0}) (v : M.Vertex) :
    CyclicCornerEnumeration M v where
  dart := M.vertexOrbitDart v
  zero_at := by
    simpa only [VanKampen.CombMap.vertexOrbitDart, pow_zero,
      Equiv.Perm.one_apply] using M.vertexOf_vertexRepresentative v
  rotates := M.vertexOrbitDart_succ v
  periodic := M.vertexOrbitDart_periodic v
  covers := M.exists_vertexOrbitDart v
  unique := M.vertexOrbitDart_injective v

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
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    {M : VanKampen.CombMap.{0}} {v : M.Vertex}
    (C : CyclicCornerEnumeration M v) where
  /-- Presentation-link label on each map dart. -/
  dartLabel : M.Dart → TriangularHodgeLayer.SignedGenerator Generator
  /-- Triangle supplying the corner step. -/
  triangle : ℕ → TriangleIndex
  /-- Literal position supplying the corner step. -/
  position : ℕ → Fin 3
  /-- The initial endpoint is the literal signed generator. -/
  source_eq : ∀ i, dartLabel (C.dart i) = T (triangle i) (position i)
  /-- The terminal endpoint is the inverse of the next literal generator. -/
  target_eq : ∀ i, dartLabel (C.dart (i + 1)) =
    TriangularHodgeLayer.inverseSigned
      (T (triangle i) (TriangularHodgeLayer.nextCorner (position i)))

namespace VertexCornerCertificate

variable {M : VanKampen.CombMap.{0}} {v : M.Vertex}
  {C : CyclicCornerEnumeration M v}

/-- Presentation-link vertex at a cyclic corner. -/
def linkVertex (K : VertexCornerCertificate T C) (i : ℕ) :
    TriangularHodgeLayer.SignedGenerator Generator :=
  K.dartLabel (C.dart i)

omit [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex] in
/-- Link labels inherit periodicity from the cyclic dart enumeration. -/
theorem periodic (K : VertexCornerCertificate T C) (i : ℕ) :
    K.linkVertex (i + M.vertexDegree v) = K.linkVertex i := by
  exact congrArg K.dartLabel (C.periodic i)

end VertexCornerCertificate

/-- Cellular reducedness at a vertex: the two relator corners on the two
sides of any intervening edge do not carry mirror link labels.  Equivalently,
the cyclic link walk never immediately traverses an edge and its reverse. -/
abbrev CellularReducedAt
    {M : VanKampen.CombMap.{0}} {v : M.Vertex}
    {C : CyclicCornerEnumeration M v}
    (K : VertexCornerCertificate T C) : Prop :=
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
    (K : VertexCornerCertificate T C) (hred : CellularReducedAt K) :
    PresentationLinkWalk T (M.vertexDegree v) where
  vertex := K.linkVertex
  periodic := K.periodic
  adjacent i := by
    change 0 < TriangularHodgeLayer.adjacencyCount T
      (K.dartLabel (C.dart i)) (K.dartLabel (C.dart (i + 1)))
    rw [K.source_eq i, K.target_eq i]
    exact adjacencyCount_pos_of_literalCorner (K.triangle i) (K.position i)
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
      VertexCornerCertificate T (corner v))
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

section Cayley

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator] [Fintype TriangleIndex]
  [DecidableEq TriangleIndex]
  {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}

omit [Fintype Generator] [DecidableEq TriangleIndex] in
/-- A literal signed relator letter evaluates to the corresponding Cayley
generator (or its inverse). -/
theorem presentedLetterValue_signedFreeRelLetter
    (u : TriangularHodgeLayer.SignedGenerator Generator) :
    presentedLetterValue T (signedFreeRelLetter u) =
      FoxBoundary.letterValue (TriangularHodgeLayer.generator T) u := by
  rcases u with ⟨generator, positive⟩
  cases positive with
  | false =>
      change PresentedGroup.mk
        (TriangularHodgeLayer.relators T : Set (FreeGroup Generator))
        ((FreeGroup.of generator)⁻¹) =
          (PresentedGroup.of generator)⁻¹
      rw [map_inv]
      rfl
  | true =>
      change PresentedGroup.mk
        (TriangularHodgeLayer.relators T : Set (FreeGroup Generator))
        (FreeGroup.of generator) = PresentedGroup.of generator
      rfl

/-- Evaluate an arbitrary list of oriented diagram darts. -/
def cayleyDartListValue
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (darts : List Delta.toCombMap.Dart) : TriangularHodgeLayer.Presented T :=
  (darts.map fun d ↦ presentedLetterValue T (Delta.label d)).prod

/-- Erasing one inner face boundary does not change presented value. -/
theorem cayleyDartListValue_erase_innerFace
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (R : RelatorOnly T Delta) (f : Delta.toCombMap.Face)
    (hf : f ≠ Delta.outerFace)
    (before after : List Delta.toCombMap.Dart) :
    cayleyDartListValue Delta
      (before ++ (Delta.faceBoundary f).darts ++ after) =
        cayleyDartListValue Delta (before ++ after) := by
  have hface : (((Delta.faceBoundary f).darts.map Delta.label).map fun d ↦
      presentedLetterValue T d).prod = 1 := by
    exact innerFace_presentedValue_eq_one Delta R f hf
  have hface' : ((Delta.faceBoundary f).darts.map
      (fun d ↦ presentedLetterValue T (Delta.label d))).prod = 1 := by
    simpa [List.map_map, Function.comp_def] using hface
  simp only [cayleyDartListValue, List.map_append, List.prod_append]
  rw [hface']
  simp

omit [Fintype Generator] [DecidableEq TriangleIndex] in
/-- Erasing an edge followed immediately by its reverse does not change
presented value. -/
theorem cayleyDartListValue_erase_backtrack
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (d : Delta.toCombMap.Dart)
    (before after : List Delta.toCombMap.Dart) :
    cayleyDartListValue Delta
      (before ++ d :: Delta.toCombMap.alpha d :: after) =
        cayleyDartListValue Delta (before ++ after) := by
  have halpha : presentedLetterValue T
      (Delta.label (Delta.toCombMap.alpha d)) =
        (presentedLetterValue T (Delta.label d))⁻¹ := by
    rw [Delta.label_alpha]
    exact presentedLetterValue_inv (T := T) (Delta.label d)
  simp only [cayleyDartListValue, List.map_append, List.map_cons,
    List.prod_append, List.prod_cons]
  rw [halpha]
  simp

/-! ## Planar path peeling -/

/-- A common-face peeling schedule.  The rank is the number of enclosed
interior faces used by the planar induction; one peel lowers that rank on both
branches. -/
structure RootedPathPeelingWitness
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T)) where
  rank : List Delta.toCombMap.Dart → ℕ
  peel : ∀ {a b : List Delta.toCombMap.Dart}, a ≠ b →
    ∃ c : List Delta.toCombMap.Dart,
      InnerFaceWordHomotopy Delta a c ∧
      InnerFaceWordHomotopy Delta b c ∧
      rank c < rank a ∧ rank c < rank b

omit [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex] in
/-- The common-face peeling induction produces the full word homotopy between
two rooted paths.  This is the planar disc induction step consumed by
`RootedPathsFaceComplete`; the two branches are recursively peeled until they
are identical. -/
theorem innerFaceWordHomotopy_of_peeling
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (W : RootedPathPeelingWitness Delta)
    (a b : List Delta.toCombMap.Dart) :
    InnerFaceWordHomotopy Delta a b := by
  generalize htotal : W.rank a + W.rank b = total
  induction total using Nat.strong_induction_on generalizing a b with
  | h total ih =>
      by_cases hab : a = b
      · subst b
        exact InnerFaceWordHomotopy.refl a
      · obtain ⟨c, hac, hbc, hca, hcb⟩ := W.peel hab
        have hac_lt : W.rank a + W.rank c < total := by
          rw [← htotal]
          omega
        have hbc_lt : W.rank b + W.rank c < total := by
          rw [← htotal]
          omega
        have hac' := ih (W.rank a + W.rank c) hac_lt a c rfl
        have hbc' := ih (W.rank b + W.rank c) hbc_lt b c rfl
        exact hac'.trans hbc'.symm

omit [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex] in
/-- The empty word is the one-face model of the peeling induction. -/
theorem innerFaceWordHomotopy_empty_model
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T)) :
    InnerFaceWordHomotopy Delta [] [] :=
  InnerFaceWordHomotopy.refl []

/-- Inner-face word homotopy preserves presented value. -/
theorem cayleyDartListValue_eq_of_innerFaceWordHomotopy
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (R : RelatorOnly T Delta) {a b : List Delta.toCombMap.Dart}
    (h : InnerFaceWordHomotopy Delta a b) :
    cayleyDartListValue Delta a = cayleyDartListValue Delta b := by
  induction h with
  | refl => rfl
  | erase f hf before after =>
      exact cayleyDartListValue_erase_innerFace Delta R f hf before after
  | eraseBacktrack d before after =>
      exact cayleyDartListValue_erase_backtrack Delta d before after
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

omit [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex] in
/-- A peeling witness gives `RootedPathsFaceComplete` for every chosen rooted
path system. -/
theorem rootedPathsFaceComplete_of_peeling
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (R : RootedPathSystem Delta.toCombMap)
    (W : RootedPathPeelingWitness Delta) :
    RootedPathsFaceComplete Delta R := by
  intro v p q
  exact innerFaceWordHomotopy_of_peeling Delta W p.darts q.darts

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

/-- Faces incident to the vertices of a boundary subpath. -/
noncomputable def boundaryFaceSeed
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) : Finset Delta.toCombMap.Face := by
  classical
  exact P.darts.toFinset.biUnion fun d ↦
    Delta.toCombMap.faceStar (Delta.toCombMap.faceOf d)

/-- The new faces in the `n`-th closed-star layer around a boundary subpath. -/
noncomputable def boundaryFaceStarLayer
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) (n : ℕ) : Finset Delta.toCombMap.Face :=
  Delta.toCombMap.faceStarLayer (boundaryFaceSeed Delta P) n

/-- The inner part of a boundary face-star layer.  Intersecting with
`innerFaces` removes the distinguished exterior face that belongs to the
zero-th boundary star. -/
noncomputable def innerBoundaryFaceStarLayer
  (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) (i : ℕ) : Finset Delta.toCombMap.Face :=
  by
    classical
    exact boundaryFaceStarLayer Delta P i ∩ Delta.innerFaces

omit [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex] in
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
  let seed := boundaryFaceSeed Delta P
  have hballMono : ∀ {i j : ℕ}, i ≤ j →
      M.faceStarBall seed i ⊆ M.faceStarBall seed j := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact fun _ h ↦ h
    | succ j _ ih => exact ih.trans (M.faceStarBall_mono_succ seed j)
  have hlayerDisjoint : ∀ {i j : ℕ}, i ≠ j →
      Disjoint (M.faceStarLayer seed i) (M.faceStarLayer seed j) := by
    intro i j hij
    wlog hlt : i < j generalizing i j with H
    · exact (H hij.symm (by omega)).symm
    have hjpos : j ≠ 0 := by omega
    rw [Finset.disjoint_left]
    intro f hfi hfj
    have hfiBall : f ∈ M.faceStarBall seed i := by
      by_cases hi0 : i = 0
      · subst i
        exact hfi
      · have hEq : M.faceStarLayer seed i =
            M.faceStarBall seed i \ M.faceStarBall seed (i - 1) := by
          rw [VanKampen.CombMap.faceStarLayer, if_neg hi0]
        rw [hEq] at hfi
        have hfi' := Finset.mem_sdiff.mp hfi
        exact hfi'.1
    have hfpred : f ∈ M.faceStarBall seed (j - 1) :=
      hballMono (by omega) hfiBall
    have hEq : M.faceStarLayer seed j =
          M.faceStarBall seed j \ M.faceStarBall seed (j - 1) := by
      rw [VanKampen.CombMap.faceStarLayer, if_neg hjpos]
    rw [hEq] at hfj
    have hfj' := Finset.mem_sdiff.mp hfj
    exact hfj'.2 hfpred
  have hpairwise : ((Finset.univ : Finset (Fin depth)) : Set (Fin depth)).PairwiseDisjoint
      (fun i ↦ M.faceStarLayer seed i ∩ Delta.innerFaces) := by
    intro i _hi j _hj hij
    exact (hlayerDisjoint (by
      intro hval
      apply hij
      exact Fin.ext hval)).mono Finset.inter_subset_left Finset.inter_subset_left
  have hsum : (∑ i : Fin depth,
    (M.faceStarLayer seed i ∩ Delta.innerFaces).card) ≤ Delta.innerFaces.card := by
    rw [← Finset.card_biUnion hpairwise]
    apply Finset.card_le_card
    intro f hf
    obtain ⟨i, _hi, hfi⟩ := Finset.mem_biUnion.mp hf
    exact (Finset.mem_inter.mp hfi).2
  simpa [VanKampen.DiscDiagram.innerFaceCount, innerBoundaryFaceStarLayer,
    boundaryFaceStarLayer, M, seed] using hsum

/-- A combinatorial certificate for the layer-covering estimate: every
surviving boundary position injects into a pair consisting of an inner layer
face and one of at most `perimeter` incidences on that face. -/
structure LayerIncidenceInjection
    {Face : Type}
    (layer : Fin depth → Finset Face) (scale loss perimeter : ℕ) where
  /-- Assign a face and an incidence slot to each surviving position. -/
  encode : ∀ i : Fin depth,
    Fin (scale - loss) → {f // f ∈ (layer i : Set Face)} × Fin perimeter
  /-- Different positions have different face-incidence pairs. -/
  injective : ∀ (i : Fin depth), Function.Injective (encode i)

/-! Geometric input for the centered-window injection.  A surviving boundary
position selects its first face in the specified star layer and an incidence
slot in that face. -/
structure CenteredWindowFirstLayerIncidence
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) (depth scale loss perimeter : ℕ) where
  /-- Occurrence of each surviving position in the centered boundary path. -/
  position : ∀ _i : Fin depth, Fin (scale - loss) → Fin P.darts.length
  /-- Different surviving positions have different path occurrences. -/
  position_injective : ∀ (i : Fin depth), Function.Injective (position i)
  /-- First inner star-layer face met by the position. -/
  face : ∀ _i : Fin depth, Fin (scale - loss) → Delta.toCombMap.Face
  /-- Incidence slot of the selected face. -/
  slot : ∀ _i : Fin depth, Fin (scale - loss) → Fin perimeter
  /-- The face-slot pair separates positions in each layer. -/
  slot_injective : ∀ (i : Fin depth), Function.Injective
    (fun q ↦ (face i q, slot i q))
  /-- The selected face belongs to the required inner layer. -/
  face_mem : ∀ (i : Fin depth) q,
    face i q ∈ innerBoundaryFaceStarLayer Delta P (i : ℕ)
  /-- The boundary dart at the position occurs on the selected face. -/
  on_face : ∀ (i : Fin depth) q, P.darts.get (position i q) ∈
    (Delta.faceBoundary (face i q)).darts
  /-- Every selected face has at most the prescribed number of incidences. -/
  faceDegree_le : ∀ (i : Fin depth) q,
    Delta.toCombMap.faceDegree (face i q) ≤ perimeter

omit [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex] in
/-- A literal boundary subpath has no repeated darts. -/
theorem boundarySubpath_nodup
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) : P.darts.Nodup := by
  have hall :
      (P.beforeDarts ++ (P.darts ++ P.afterDarts)).Nodup := by
    rw [← List.append_assoc, ← P.split]
    exact (Delta.faceBoundary Delta.outerFace).nodup
  exact hall.of_append_right.of_append_left

/-- The first-layer face assignment canonically constructs the incidence
injection used in the third successive-star inequality. -/
noncomputable def layerIncidenceInjection_of_firstLayer
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) (depth scale loss perimeter : ℕ)
    (C : CenteredWindowFirstLayerIncidence Delta P depth scale loss perimeter) :
    LayerIncidenceInjection
      (fun i : Fin depth ↦ innerBoundaryFaceStarLayer Delta P i)
      scale loss perimeter := by
  classical
  refine {
    encode := fun i q ↦
      (⟨C.face i q, C.face_mem i q⟩, C.slot i q)
    injective := ?_ }
  intro i x y hxy
  have hface : C.face i x = C.face i y :=
    congrArg (fun p ↦ (p.1.1 : Delta.toCombMap.Face)) hxy
  have hslot : C.slot i x = C.slot i y :=
    congrArg (fun p ↦ p.2) hxy
  apply C.slot_injective i
  exact Prod.ext hface hslot

/-- An incidence injection proves the numerical covering inequality. -/
theorem layer_covers_of_incidenceInjection
    {Face : Type}
    {layer : Fin depth → Finset Face} {scale loss perimeter : ℕ}
    (C : LayerIncidenceInjection layer scale loss perimeter) :
    ∀ i : Fin depth, scale - loss ≤ perimeter * (layer i).card := by
  classical
  intro i
  have hcard := Fintype.card_le_of_injective (C.encode i) (C.injective i)
  have hsetcard : Fintype.card {f // f ∈ (layer i : Set Face)} =
      (layer i).card := by
    calc
      Fintype.card {f // f ∈ (layer i : Set Face)} =
          Nat.card {f // f ∈ (layer i : Set Face)} :=
        (Nat.card_eq_fintype_card).symm
      _ = (layer i : Set Face).ncard := rfl
      _ = (layer i).card := Set.ncard_coe_finset _
  simpa only [Fintype.card_fin, Fintype.card_prod, hsetcard,
    Nat.mul_comm] using hcard

/-- The genuinely geometric local estimate for a star layer: after losing the
two endpoint neighborhoods, its triangular faces cover the surviving window.
It is deliberately separate from disjointness, which is proved above. -/
abbrev LayerCoversWindow
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) (depth scale loss perimeter : ℕ) : Prop :=
  ∀ i : Fin depth, scale - loss ≤ perimeter *
    (innerBoundaryFaceStarLayer Delta P i).card

omit [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex] in
/-- Explicit boundary-position incidences prove `LayerCoversWindow`. -/
theorem layerCoversWindow_of_incidenceInjection
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) (depth scale loss perimeter : ℕ)
    (C : LayerIncidenceInjection
      (fun i : Fin depth ↦ innerBoundaryFaceStarLayer Delta P i)
      scale loss perimeter) :
    LayerCoversWindow Delta P depth scale loss perimeter :=
  by
    classical
    exact layer_covers_of_incidenceInjection C

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
  · intro _i x y _hxy
    apply Fin.ext
    omega

/-- The incidence-count theorem recovers the unit covering inequality in the
one-triangle model. -/
theorem oneTriangle_unit_cover_of_incidenceInjection :
    ∀ _i : Fin 1, 1 - 0 ≤ 1 *
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

omit [Fintype Generator] [DecidableEq TriangleIndex] in
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

omit [Fintype Generator] [DecidableEq TriangleIndex] in
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

omit [Fintype Generator] [DecidableEq TriangleIndex] in
/-- The exact-boundary cactus retyping bridge.  Once the free-group-trivial
complementary cell has been removed, the resulting diagram has the literal
power boundary and the relator-only field required by the power-disc
candidate. -/
theorem nonempty_powerDiscCandidate_of_cactusRetyping
    (word : List (TriangularHodgeLayer.SignedGenerator Generator))
    (hword : PresentedGroup.mk
        (TriangularHodgeLayer.relators T : Set (FreeGroup Generator))
        (PresentedGroupRelatorReplay.word word) = g)
    (_hn : 0 < n) (_hpow : g ^ n = 1) (_hne : g ≠ 1)
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (C : VanKampen.CactusRelatorRetyping Delta)
    (hboundary : C.diagram.boundaryWord =
      (List.replicate n (word.map signedFreeRelLetter)).flatten) :
    Nonempty (PowerDiscCandidate T g n) := by
  have hrelatorOnly : RelatorOnly T C.diagram := by
    constructor
    intro f hf
    exact C.relatorOnly.cell f hf
  let candidate : PowerDiscCandidate T g n :=
    { word := word
      represents := hword
      diagram := C.diagram
      boundary_eq := hboundary
      relatorOnly := hrelatorOnly }
  exact ⟨candidate⟩

omit [Fintype Generator] [DecidableEq TriangleIndex] in
/-- The actual `SurgeryMap` cactus deletion supplies the literal power-disc
candidate once its replacement diagram has the prescribed boundary. -/
theorem nonempty_powerDiscCandidate_of_cactusDeletion
    (word : List (TriangularHodgeLayer.SignedGenerator Generator))
    (hword : PresentedGroup.mk
        (TriangularHodgeLayer.relators T : Set (FreeGroup Generator))
        (PresentedGroupRelatorReplay.word word) = g)
    (_hn : 0 < n) (_hpow : g ^ n = 1) (_hne : g ≠ 1)
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (C : VanKampen.CactusBaseCellDeletion Delta)
    (hplanar : Delta.toCombMap.IsPlanar)
    (hboundary : C.replacement.diagram.boundaryWord =
      (List.replicate n (word.map signedFreeRelLetter)).flatten) :
    Nonempty (PowerDiscCandidate T g n) := by
  exact nonempty_powerDiscCandidate_of_cactusRetyping word hword
    _hn _hpow _hne Delta (C.toRetyping hplanar) hboundary

omit [Fintype Generator] [DecidableEq TriangleIndex] in
/-- A finite chain of concrete cactus folds supplies the literal power-disc
candidate from its terminal relator-only diagram. -/
theorem nonempty_powerDiscCandidate_of_cactusFoldChain
    (word : List (TriangularHodgeLayer.SignedGenerator Generator))
    (hword : PresentedGroup.mk
        (TriangularHodgeLayer.relators T : Set (FreeGroup Generator))
        (PresentedGroupRelatorReplay.word word) = g)
    (_hn : 0 < n) (_hpow : g ^ n = 1) (_hne : g ≠ 1)
    (Delta Next : VanKampen.DiscDiagram.{0, 0, 0}
      (triangleRelatorWords T))
    (chain : VanKampen.CactusFoldChain Delta Next k)
    (hplanar : Delta.toCombMap.IsPlanar)
    (hred : Delta.Reduced)
    (hboundary : Next.boundaryWord =
      (List.replicate n (word.map signedFreeRelLetter)).flatten) :
    Nonempty (PowerDiscCandidate T g n) := by
  let C : VanKampen.CactusRelatorRetyping Delta :=
    chain.toRetyping hplanar hred
  have hdiagram : C.diagram = Next :=
    chain.toRetyping_diagram_eq hplanar hred
  have hboundary' : C.diagram.boundaryWord =
      (List.replicate n (word.map signedFreeRelLetter)).flatten := by
    rw [hdiagram]
    exact hboundary
  exact nonempty_powerDiscCandidate_of_cactusRetyping word hword
    _hn _hpow _hne Delta C hboundary'

/-- A reduced candidate is the interface's `PowerDisc`. -/
def PowerDiscCandidate.toPowerDisc (D : PowerDiscCandidate T g n)
    (hred : D.diagram.Reduced) : PowerDisc T g n where
  word := D.word
  represents := D.represents
  diagram := D.diagram
  boundary_eq := D.boundary_eq
  reduced := hred
  relatorOnly := D.relatorOnly

omit [Fintype Generator] [DecidableEq TriangleIndex] in
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
    (hfill : Nonempty (PowerDiscCandidate T g n)) : ℕ := by
  classical
  exact Nat.find (exists_powerDiscCandidate_area hfill)

/-- A candidate attaining the least relator area. -/
noncomputable def leastPowerDiscCandidate
    (hfill : Nonempty (PowerDiscCandidate T g n)) :
    PowerDiscCandidate T g n := by
  classical
  exact Classical.choose (Nat.find_spec (exists_powerDiscCandidate_area hfill))

omit [Fintype Generator] [DecidableEq TriangleIndex] in
/-- The selected candidate has the declared least area. -/
theorem leastPowerDiscCandidate_area_eq
    (hfill : Nonempty (PowerDiscCandidate T g n)) :
    (leastPowerDiscCandidate hfill).diagram.rCellCount =
      leastPowerDiscArea hfill := by
  classical
  exact Classical.choose_spec (Nat.find_spec (exists_powerDiscCandidate_area hfill))

omit [Fintype Generator] [DecidableEq TriangleIndex] in
/-- No candidate with the same literal boundary has smaller relator area. -/
theorem leastPowerDiscCandidate_area_le
    (hfill : Nonempty (PowerDiscCandidate T g n))
    (D : PowerDiscCandidate T g n) :
    (leastPowerDiscCandidate hfill).diagram.rCellCount ≤
      D.diagram.rCellCount := by
  classical
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

/-- A power-disc cancellation cut packages the result of deleting a mirror
pair, its unchanged literal boundary, and the two-cell area drop. -/
structure PowerDiscMirrorPairCut (D : PowerDiscCandidate T g n) where
  result : PowerDiscCandidate T g n
  boundaryWord_eq : result.diagram.boundaryWord = D.diagram.boundaryWord
  area_eq : result.diagram.rCellCount + 2 = D.diagram.rCellCount

/-- A power-disc mirror cut whose topological output is the concrete
`SurgeryMap` reclosure.  The matching equations identify its two deleted
cells with the ordered pair supplied by `CancellationReducesArea`. -/
structure PowerDiscMirrorPairDeletion
    (D : PowerDiscCandidate T g n)
    (pre between suf : List
      (VanKampen.RelatorCell D.diagram.toCombMap D.diagram.outerFace
        (triangleRelatorWords T)))
    (C₁ C₂ : VanKampen.RelatorCell D.diagram.toCombMap D.diagram.outerFace
      (triangleRelatorWords T))
    (hsplit : D.diagram.relatorCells =
      pre ++ C₁ :: (between ++ C₂ :: suf))
    (hcancel :
      (between.map VanKampen.RelatorCell.value).prod⁻¹ * C₁.value *
        (between.map VanKampen.RelatorCell.value).prod * C₂.value = 1) where
  topological : VanKampen.MirrorPairDeletion D.diagram
  pre_eq : topological.pre = pre
  between_eq : topological.between = between
  suf_eq : topological.suf = suf
  first_eq : topological.first = C₁
  second_eq : topological.second = C₂
  result : PowerDiscCandidate T g n
  result_diagram_eq : result.diagram = topological.replacement.diagram

omit [Fintype Generator] [DecidableEq TriangleIndex] in
/-- The concrete topological mirror cut drops exactly two relator cells in a
power-disc candidate. -/
theorem PowerDiscMirrorPairDeletion.area_drop
    (D : PowerDiscCandidate T g n)
    (pre between suf : List
      (VanKampen.RelatorCell D.diagram.toCombMap D.diagram.outerFace
        (triangleRelatorWords T)))
    (C₁ C₂ : VanKampen.RelatorCell D.diagram.toCombMap D.diagram.outerFace
      (triangleRelatorWords T))
    (hsplit : D.diagram.relatorCells =
      pre ++ C₁ :: (between ++ C₂ :: suf))
    (hcancel :
      (between.map VanKampen.RelatorCell.value).prod⁻¹ * C₁.value *
        (between.map VanKampen.RelatorCell.value).prod * C₂.value = 1)
    (C : PowerDiscMirrorPairDeletion D pre between suf C₁ C₂ hsplit hcancel) :
    C.result.diagram.rCellCount + 2 = D.diagram.rCellCount := by
  rw [C.result_diagram_eq]
  exact C.topological.area_drop

omit [Fintype Generator] [DecidableEq TriangleIndex] in
/-- The two-cell power-disc model leaves no relator cells after the cut. -/
theorem PowerDiscMirrorPairDeletion.area_zero_of_twoCell
    (D : PowerDiscCandidate T g n)
    (pre between suf : List
      (VanKampen.RelatorCell D.diagram.toCombMap D.diagram.outerFace
        (triangleRelatorWords T)))
    (C₁ C₂ : VanKampen.RelatorCell D.diagram.toCombMap D.diagram.outerFace
      (triangleRelatorWords T))
    (hsplit : D.diagram.relatorCells =
      pre ++ C₁ :: (between ++ C₂ :: suf))
    (hcancel :
      (between.map VanKampen.RelatorCell.value).prod⁻¹ * C₁.value *
        (between.map VanKampen.RelatorCell.value).prod * C₂.value = 1)
    (C : PowerDiscMirrorPairDeletion D pre between suf C₁ C₂ hsplit hcancel)
    (htwo : D.diagram.relatorCells.length = 2) :
    C.result.diagram.rCellCount = 0 := by
  have hdrop := C.area_drop D pre between suf C₁ C₂ hsplit hcancel
  change C.result.diagram.relatorCells.length + 2 =
    D.diagram.relatorCells.length at hdrop
  rw [htwo] at hdrop
  change C.result.diagram.relatorCells.length = 0
  omega

omit [Fintype Generator] [DecidableEq TriangleIndex] in
/-- Once the concrete `SurgeryMap` cut is supplied for each ordered mirror
pair, it proves the cancellation premise consumed by least-area reduction. -/
theorem cancellationReducesArea_of_concreteMirrorPairDeletion
    (D : PowerDiscCandidate T g n)
    (cut : ∀ (pre between suf : List
      (VanKampen.RelatorCell D.diagram.toCombMap D.diagram.outerFace
        (triangleRelatorWords T)))
      (C₁ C₂ : VanKampen.RelatorCell D.diagram.toCombMap D.diagram.outerFace
        (triangleRelatorWords T)),
      (hsplit : D.diagram.relatorCells =
        pre ++ C₁ :: (between ++ C₂ :: suf)) →
      (hcancel :
        (between.map VanKampen.RelatorCell.value).prod⁻¹ * C₁.value *
          (between.map VanKampen.RelatorCell.value).prod * C₂.value = 1) →
      PowerDiscMirrorPairDeletion D pre between suf C₁ C₂ hsplit hcancel) :
    CancellationReducesArea D := by
  intro pre between suf C₁ C₂ hsplit hcancel
  let C := cut pre between suf C₁ C₂ hsplit hcancel
  refine ⟨C.result, ?_⟩
  have harea := C.area_drop D pre between suf C₁ C₂ hsplit hcancel
  omega

omit [Fintype Generator] [DecidableEq TriangleIndex] in
/-- A concrete planar mirror reclosure produces the power-disc cut consumed by
the least-area argument.  The source reducedness and planarity fields are
exactly the hypotheses needed by the generic surgery certificate. -/
def powerDiscMirrorPairCut_of_planarDisc
    (D : PowerDiscCandidate T g n)
    (C : VanKampen.MirrorPairDeletion D.diagram)
    (hred : D.diagram.Reduced)
    (hplanar : D.diagram.toCombMap.IsPlanar) :
    PowerDiscMirrorPairCut D := by
  let R := C.toMirrorPairCut hred hplanar
  have hrelatorOnly : RelatorOnly T R.result := by
    constructor
    intro f hf
    exact R.relatorOnly.cell f hf
  let D' : PowerDiscCandidate T g n :=
    { word := D.word
      represents := D.represents
      diagram := R.result
      boundary_eq := R.boundaryWord_eq.trans D.boundary_eq
      relatorOnly := hrelatorOnly }
  refine {
    result := D'
    boundaryWord_eq := ?_
    area_eq := ?_ }
  · exact R.boundaryWord_eq
  · exact R.area_eq

omit [Fintype Generator] [DecidableEq TriangleIndex] in
/-- A supplied mirror-pair cut proves the cancellation premise by arithmetic. -/
theorem cancellationReducesArea_of_mirrorPairCut
    (D : PowerDiscCandidate T g n)
    (cut : ∀ (pre between suf : List
      (VanKampen.RelatorCell D.diagram.toCombMap D.diagram.outerFace
        (triangleRelatorWords T)))
      (C₁ C₂ : VanKampen.RelatorCell D.diagram.toCombMap D.diagram.outerFace
        (triangleRelatorWords T)),
      D.diagram.relatorCells = pre ++ C₁ :: (between ++ C₂ :: suf) →
      (between.map VanKampen.RelatorCell.value).prod⁻¹ * C₁.value *
        (between.map VanKampen.RelatorCell.value).prod * C₂.value = 1 →
      PowerDiscMirrorPairCut D) :
    CancellationReducesArea D := by
  intro pre between suf C₁ C₂ hsplit hcancel
  obtain ⟨result, _hboundary, harea⟩ :=
    cut pre between suf C₁ C₂ hsplit hcancel
  refine ⟨result, ?_⟩
  have harea' := harea
  omega

omit [Fintype Generator] [DecidableEq TriangleIndex] in
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

omit [Fintype Generator] [DecidableEq TriangleIndex] in
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
  cornerCertificate : ∀ v, VertexCornerCertificate T (cornerCycle v)
  /-- Least-area seam reduction rules out mirror corner pairs. -/
  cellularReduced : ∀ v, CellularReducedAt (cornerCertificate v)

/-- The copied-interior seam constructor supplies the map, source-copy,
source-face, and face-degree fields of the power-disc gluing certificate.
Only the literal corner labels and the no-mirror seam check remain as local
input. -/
noncomputable def powerDiscSphereGluing_of_seam
    (D : PowerDisc T g n)
    (S : VanKampen.SeamGluing.Pairing D.diagram n)
    (hS : S.Spherical)
    (certificate : ∀ v,
      VertexCornerCertificate T (cornerCycleOfCombMap S.closedMap v))
    (hcellular : ∀ v, CellularReducedAt (certificate v)) :
    PowerDiscSphereGluing D where
  sphere := S.sphericalCombMap hS
  sourceCopy := S.sourceCopy
  sourceFace := S.sourceFace
  sourceFace_ne_outer := S.sourceFace_ne_outer
  faceDegree_eq := S.faceDegree_eq_source
  cornerCycle := cornerCycleOfCombMap S.closedMap
  cornerCertificate := certificate
  cellularReduced := hcellular

/-- The explicit copied-incidence count proves the spherical hypothesis used by
the seam constructor.  This is the Euler-characteristic-two branch of the
rotated-copy gluing argument. -/
noncomputable def powerDiscSphereGluing_of_eulerCounts
    (D : PowerDisc T g n)
    (S : VanKampen.SeamGluing.Pairing D.diagram n)
    (hcounts : VanKampen.SeamGluing.Pairing.EulerTwoCountData S)
    (hdisc : D.diagram.toCombMap.IsPlanar)
    (certificate : ∀ v,
      VertexCornerCertificate T
        (cornerCycleOfCombMap S.closedMap v))
    (hcellular : ∀ v, CellularReducedAt (certificate v)) :
    PowerDiscSphereGluing D :=
  powerDiscSphereGluing_of_seam D S
    (VanKampen.SeamGluing.Pairing.spherical_of_eulerTwoCountData
      S hcounts hdisc)
    certificate hcellular

omit [Fintype Generator] [DecidableEq TriangleIndex] in
/-- A copy-index mate and the disc's Euler counts give the complete
power-disc sphere certificate.  The corner labels and cellular reducedness
remain the local triangular inputs. -/
noncomputable def powerDiscSphereGluing_of_planarDisc
    (D : PowerDisc T g n)
    (B : VanKampen.SeamGluing.ExposedPairing D.diagram n)
    (hcounts : VanKampen.SeamGluing.Pairing.EulerTwoCountData B.toPairing)
    (hplanar : D.diagram.toCombMap.IsPlanar)
    (certificate : ∀ v,
      VertexCornerCertificate T
        (cornerCycleOfCombMap B.toPairing.closedMap v))
    (hcellular : ∀ v, CellularReducedAt (certificate v)) :
    PowerDiscSphereGluing D :=
  powerDiscSphereGluing_of_seam D B.toPairing
    (VanKampen.SeamGluing.ExposedPairing.spherical_of_planarDisc
      B hcounts hplanar)
    certificate hcellular

omit [Fintype Generator] [DecidableEq TriangleIndex] in
/-- The double-copy seam constructor builds the exposed mate by swapping the
two copies, then uses the boundary-corrected Euler equations to obtain the
spherical power-disc certificate. -/
noncomputable def powerDiscSphereGluing_of_doubleCopyMate
    (D : PowerDisc T g 2)
    {I : Type}
    (index : VanKampen.SeamGluing.ExposedCopiedDart D.diagram 2 ≃
      Fin 2 × I)
    (index_copy : ∀ d, (index d).1 = d.1.1)
    (hcounts : VanKampen.SeamGluing.Pairing.DoubleEulerCountData
      (VanKampen.SeamGluing.ExposedPairing.of_doubleCopyMate
        index index_copy).toPairing)
    (certificate : ∀ v, VertexCornerCertificate T
      (cornerCycleOfCombMap
        (VanKampen.SeamGluing.ExposedPairing.of_doubleCopyMate
          index index_copy).toPairing.closedMap v))
    (hcellular : ∀ v, CellularReducedAt (certificate v))
    (hplanar : D.diagram.toCombMap.IsPlanar) :
    PowerDiscSphereGluing D := by
  let B := VanKampen.SeamGluing.ExposedPairing.of_doubleCopyMate
    index index_copy
  exact powerDiscSphereGluing_of_seam D B.toPairing
    (VanKampen.SeamGluing.Pairing.spherical_of_doubleEulerCountData
      hcounts hplanar)
    certificate hcellular

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
