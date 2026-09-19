import GroupApproximation.GGT.KazhdanHypGirthEightVKInterface
import GroupApproximation.GGT.VanKampen.CombMapStars
import Mathlib.Tactic.FinCases

/-!
# Constructible girth-eight diagram primitives

This module connects the committed permutation-map API to the local operations
in `GirthEightDiagramPrimitives`.  It constructs cyclic corner enumerations,
literal positions on triangular relator faces, boundary prefixes, face-star
layers, and the projections already supplied by `TriangularDiagramLocalData`.

The final section tests the stronger bundle on the one-edge disc.  The current
definition of `DiscDiagram.Reduced` is vacuous when there are no stored relator
cells, while the bundle's `boundaryDegree` field demands degree at least two at
every outer vertex.  The model has an outer vertex of degree one, so the full
bundle cannot be constructed from the committed definitions.  This identifies
the exact local strengthening required before the remaining global fields can
be assembled.
-/

namespace GroupApproximation
namespace GGT
namespace GirthEightPrimitives

open GroupApproximation.KazhdanHyp
open GirthEightVKInterface

universe u

section Table

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]
  {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}

/-! ## Cyclic corners -/

/-- The power enumeration of a `sigma` orbit gives the interface's cyclic
corner enumeration at every map vertex. -/
noncomputable def cornerCycle
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (v : Delta.toCombMap.Vertex) :
    CyclicCornerEnumeration Delta.toCombMap v where
  dart := Delta.toCombMap.vertexOrbitDart v
  zero_at := by
    simpa only [VanKampen.CombMap.vertexOrbitDart, pow_zero, Equiv.Perm.one_apply]
      using Delta.toCombMap.vertexOf_vertexRepresentative v
  rotates := Delta.toCombMap.vertexOrbitDart_succ v
  periodic := Delta.toCombMap.vertexOrbitDart_periodic v
  covers := Delta.toCombMap.exists_vertexOrbitDart v
  unique := Delta.toCombMap.vertexOrbitDart_injective v

/-- The constructed corner cycle exposes both incident faces at every cyclic
position. -/
noncomputable def cornerAt
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (v : Delta.toCombMap.Vertex) (i : ℕ) :
    VanKampen.Corner Delta.toCombMap v where
  dart := (cornerCycle Delta v).dart i
  atVertex := (cornerCycle Delta v).atVertex i

/-! ## Literal positions on triangular faces -/

/-- The boundary list of a literal relator face has exactly three darts. -/
theorem faceBoundary_length_eq_three
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (R : RelatorOnly T Delta) (f : Delta.toCombMap.Face)
    (hf : f ≠ Delta.outerFace) :
    (Delta.faceBoundary f).darts.length = 3 := by
  obtain ⟨j, hj⟩ := R.exists_faceWord_eq f hf
  calc
    (Delta.faceBoundary f).darts.length = Delta.toCombMap.faceDegree f :=
      (Delta.faceBoundary f).length_eq_degree
    _ = (Delta.faceWord f).length := (Delta.faceWord_length f).symm
    _ = (triangleRelatorWord T j).length := congrArg List.length hj
    _ = 3 := triangleRelatorWord_length T j

/-- Every relator-only inner face has the three literal darts and labels in the
order fixed by its stored relator word. -/
noncomputable def facePositions
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (R : RelatorOnly T Delta) (f : Delta.toCombMap.Face)
    (hf : f ≠ Delta.outerFace) : TriangleFacePositions T Delta f := by
  classical
  let witness := R.exists_faceWord_eq f hf
  let j : TriangleIndex := Classical.choose witness
  have hj : Delta.faceWord f = triangleRelatorWord T j :=
    Classical.choose_spec witness
  let b := (Delta.faceBoundary f).darts
  have hbLength : b.length = 3 := faceBoundary_length_eq_three Delta R f hf
  let position : Fin 3 → Fin b.length := Fin.cast hbLength.symm
  let dart : Fin 3 → Delta.toCombMap.Dart := fun k ↦ b.get (position k)
  have hword : b.map Delta.label =
      [signedFreeRelLetter (T j 0), signedFreeRelLetter (T j 1),
        signedFreeRelLetter (T j 2)] := by
    calc
      b.map Delta.label = Delta.faceWord f := rfl
      _ = triangleRelatorWord T j := hj
      _ = [signedFreeRelLetter (T j 0), signedFreeRelLetter (T j 1),
          signedFreeRelLetter (T j 2)] := by
        simp only [triangleRelatorWord,
          TriangularHodgeLayer.letters_eq_three, List.map_cons, List.map_nil]
  refine {
    triangle := j
    dart := dart
    onFace := ?_
    label_eq := ?_
    rotates := ?_
    covers := ?_
    injective := ?_ }
  · intro k
    exact ((Delta.faceBoundary f).mem_iff _).mp
      (List.get_mem b (position k))
  · intro k
    fin_cases k
    · have h := congrArg (fun l => l[0]?) hword
      simpa [dart, position, hbLength] using h
    · have h := congrArg (fun l => l[1]?) hword
      simpa [dart, position, hbLength] using h
    · have h := congrArg (fun l => l[2]?) hword
      simpa [dart, position, hbLength] using h
  · intro k
    have hchain := (List.isChain_iff_getElem.mp
      (Delta.faceBoundary f).chain)
    fin_cases k
    · have h := hchain 0 (by simp [b, hbLength])
      simpa [dart, position, TriangularHodgeLayer.nextCorner, hbLength] using h
    · have h := hchain 1 (by simp [b, hbLength])
      simpa [dart, position, TriangularHodgeLayer.nextCorner, hbLength] using h
    · have h := (Delta.faceBoundary f).closes
      simpa [dart, position, TriangularHodgeLayer.nextCorner, b, hbLength,
        List.getLast_eq_getElem, List.head_eq_getElem] using h
  · intro d hd
    have hdmem : d ∈ b := by
      exact ((Delta.faceBoundary f).mem_iff d).mpr hd
    obtain ⟨k, hk⟩ := List.get_of_mem hdmem
    refine ⟨Fin.cast hbLength k, ?_⟩
    simpa [dart, position] using hk
  · intro k l hkl
    apply Fin.cast_injective hbLength.symm
    apply (Delta.faceBoundary f).nodup.get_inj_iff.mp
    exact hkl

/-! ## Boundary subpaths and successive stars -/

/-- A prefix from the map-level outer traversal has exactly the interface's
boundary-subpath fields. -/
def boundaryPrefix
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (n : ℕ) : BoundarySubpath T Delta :=
  let P := VanKampen.boundaryPrefix Delta n
  { darts := P.darts
    beforeDarts := P.beforeDarts
    afterDarts := P.afterDarts
    split := P.split
    chain := P.chain }

/-- Faces incident to the vertices of a boundary subpath form the seed of the
successive face-star construction. -/
noncomputable def boundaryFaceSeed
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) : Finset Delta.toCombMap.Face := by
  classical
  exact P.darts.toFinset.biUnion fun d ↦
    Delta.toCombMap.faceStar (Delta.toCombMap.faceOf d)

/-- The `n`-th closed star around a boundary subpath. -/
noncomputable def boundaryFaceStarBall
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) (n : ℕ) : Finset Delta.toCombMap.Face :=
  Delta.toCombMap.faceStarBall (boundaryFaceSeed Delta P) n

/-- The new faces in the `n`-th star layer around a boundary subpath. -/
noncomputable def boundaryFaceStarLayer
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) (n : ℕ) : Finset Delta.toCombMap.Face :=
  Delta.toCombMap.faceStarLayer (boundaryFaceSeed Delta P) n

omit [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex] in
/-- A new star layer is disjoint from all faces in the preceding ball. -/
theorem boundaryFaceStarLayer_succ_disjoint
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (P : BoundarySubpath T Delta) (n : ℕ) :
    Disjoint (boundaryFaceStarLayer Delta P (n + 1))
      (boundaryFaceStarBall Delta P n) :=
  Delta.toCombMap.faceStarLayer_succ_disjoint_ball (boundaryFaceSeed Delta P) n

/-! ## Operations already present in local diagram data -/

/-- The local diagram input already supplies the nonbacktracking link walk. -/
def linkWalkOfLocalData
    {Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T)}
    (L : TriangularDiagramLocalData T Delta)
    (v : Delta.toCombMap.Vertex)
    (hv : v ∉ discOuterBoundaryVertices Delta) :
    PresentationLinkWalk T (Delta.toCombMap.vertexDegree v) :=
  L.interiorVertexWalk v hv

omit [Fintype Generator] [DecidableEq TriangleIndex] in
/-- The local diagram input already supplies the boundary valence estimate. -/
theorem boundaryDegreeOfLocalData
    {Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T)}
    (L : TriangularDiagramLocalData T Delta)
    (v : Delta.toCombMap.Vertex)
    (hv : v ∈ discOuterBoundaryVertices Delta) :
    2 ≤ Delta.toCombMap.vertexDegree v :=
  L.boundaryVertexDegree v hv

/-- A disc diagram gives the closed planar-map variant after forgetting which
face was designated exterior. -/
def sphericalMapOfDisc
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T)) :
    VanKampen.SphericalCombMap :=
  VanKampen.SphericalCombMap.ofDiscDiagram Delta

end Table

/-! ## The one-edge reduced-disc test for the bundled boundary field -/

/-- Edge reversal on the two darts of a single unoriented edge. -/
def oneEdgeAlpha : Equiv.Perm Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv := by intro b; cases b <;> rfl
  right_inv := by intro b; cases b <;> rfl

/-- The one-edge closed rotation system: both endpoints have singleton
`sigma` orbits, and edge reversal forms the unique face orbit. -/
def oneEdgeCombMap : VanKampen.CombMap where
  Dart := Bool
  dartFintype := inferInstance
  alpha := oneEdgeAlpha
  sigma := 1
  alpha_involutive := by intro b; cases b <;> rfl
  alpha_fixedPointFree := by intro b; cases b <;> decide

/-- The one-edge map is connected through its unique edge. -/
theorem oneEdge_isConnected : oneEdgeCombMap.IsConnected := by
  intro d e
  cases d <;> cases e
  · exact Relation.EqvGen.refl _
  · exact Relation.EqvGen.rel _ _ (Or.inl rfl)
  · exact Relation.EqvGen.rel _ _ (Or.inl rfl)
  · exact Relation.EqvGen.refl _

/-- Vertex orbits of the one-edge map are its two darts because `sigma` is the
identity. -/
noncomputable def oneEdgeVertexEquiv : oneEdgeCombMap.Vertex ≃ Bool :=
  VanKampen.OrbitClassifier.orbitEquiv oneEdgeCombMap.sigma id id
    (by intro d; rfl) (by intro d; rfl)
    (by intro d; exact Equiv.Perm.SameCycle.rfl)

/-- The edge quotient of the one-edge map is a singleton. -/
noncomputable def oneEdgeEdgeEquiv : oneEdgeCombMap.Edge ≃ PUnit.{1} where
  toFun := fun _ ↦ PUnit.unit
  invFun := fun _ ↦ Quotient.mk'' false
  left_inv q := by
    refine Quotient.inductionOn' q ?_
    intro d
    apply Quotient.sound
    cases d
    · exact Or.inl rfl
    · exact Or.inr rfl
  right_inv _ := rfl

/-- The face quotient of the one-edge map is a singleton. -/
noncomputable def oneEdgeFaceEquiv : oneEdgeCombMap.Face ≃ PUnit.{1} where
  toFun := fun _ ↦ PUnit.unit
  invFun := fun _ ↦ Quotient.mk'' false
  left_inv q := by
    refine Quotient.inductionOn' q ?_
    intro d
    apply Quotient.sound
    cases d
    · exact Equiv.Perm.SameCycle.rfl
    · refine ⟨1, ?_⟩
      rfl
  right_inv _ := rfl

theorem oneEdge_vertexCount : oneEdgeCombMap.vertexCount = 2 := by
  rw [VanKampen.CombMap.vertexCount, Nat.card_congr oneEdgeVertexEquiv]
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_bool

theorem oneEdge_edgeCount : oneEdgeCombMap.edgeCount = 1 := by
  rw [VanKampen.CombMap.edgeCount, Nat.card_congr oneEdgeEdgeEquiv]
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_punit

theorem oneEdge_faceCount : oneEdgeCombMap.faceCount = 1 := by
  rw [VanKampen.CombMap.faceCount, Nat.card_congr oneEdgeFaceEquiv]
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_punit

/-- The one-edge rotation system is a planar closed map. -/
theorem oneEdge_planar : oneEdgeCombMap.IsPlanar := by
  refine ⟨oneEdge_isConnected, ?_⟩
  simp [VanKampen.CombMap.eulerCharacteristic, oneEdge_vertexCount,
    oneEdge_edgeCount, oneEdge_faceCount]

/-- Every face of the one-edge map is its unique face. -/
theorem oneEdge_face_eq (f : oneEdgeCombMap.Face) :
    f = oneEdgeCombMap.faceOf false := by
  refine Quotient.inductionOn' f ?_
  intro d
  apply Quotient.sound
  cases d
  · exact Equiv.Perm.SameCycle.rfl
  · refine ⟨1, ?_⟩
    rfl

/-- The canonical two-dart traversal, transported to the unique face. -/
noncomputable def oneEdgeFaceBoundary (f : oneEdgeCombMap.Face) :
    VanKampen.FaceBoundary oneEdgeCombMap f := by
  have hface : oneEdgeCombMap.faceOf false = f := (oneEdge_face_eq f).symm
  exact hface ▸ VanKampen.FaceBoundary.based oneEdgeCombMap false

/-- There is no triangle index in the empty model. -/
def emptyTriangleTable : PEmpty → TriangularHodgeLayer.Triangle PEmpty :=
  PEmpty.elim

/-- All darts in the one-edge test carry the identity base letter. -/
def oneEdgeLabel (_ : oneEdgeCombMap.Dart) :
    GGT.RelLetter (FreeGroup PEmpty) PEmpty :=
  GGT.RelLetter.base 1

/-- A planar disc with one unoriented edge, one exterior face, and no relator
cells.  Its only face is the exterior face. -/
noncomputable def oneEdgeDiagram :
    VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords emptyTriangleTable) where
  toCombMap := oneEdgeCombMap
  planar := oneEdge_planar
  label := oneEdgeLabel
  label_alpha := by
    intro d
    simp [oneEdgeLabel, HullSC.RelWord.inv]
  outerFace := oneEdgeCombMap.faceOf false
  faceBoundary := oneEdgeFaceBoundary
  relatorCells := []
  relatorCell_faces_nodup := List.nodup_nil
  relatorCell_word := by intro C hC; simp at hC
  inner_face := by
    intro f hf
    exact (hf (oneEdge_face_eq f)).elim
  boundary_product := by
    simp only [List.map_nil, List.prod_nil, HullSC.RelWord.revInv,
      GGT.RelLetter.listVal, List.map_reverse, List.map_map]
    change 1 = (List.map (fun _ : Bool ↦ (1 : FreeGroup PEmpty))
      (oneEdgeFaceBoundary (oneEdgeCombMap.faceOf false)).darts).reverse.prod
    simp

/-- The one-edge disc is reduced because its stored relator-cell list is
empty. -/
theorem oneEdgeDiagram_reduced : oneEdgeDiagram.Reduced :=
  oneEdgeDiagram.reduced_of_no_rCells rfl

/-- One endpoint of the one-edge disc has degree one. -/
theorem oneEdge_vertexDegree_false :
    oneEdgeCombMap.vertexDegree (oneEdgeCombMap.vertexOf false) = 1 := by
  classical
  change VanKampen.CombMap.orbitDegree oneEdgeCombMap.sigma
    (Quotient.mk'' false) = 1
  rw [← VanKampen.closedOrbitList.length_eq_orbitDegree
    oneEdgeCombMap.sigma false]
  have hfixed : oneEdgeCombMap.sigma false = false := rfl
  rw [VanKampen.closedOrbitList, if_pos hfixed]
  rfl

/-- The same degree computation in the definitional map of the test disc. -/
theorem oneEdgeDiagram_vertexDegree_false :
    oneEdgeDiagram.toCombMap.vertexDegree
      (oneEdgeDiagram.toCombMap.vertexOf false) = 1 := by
  change oneEdgeCombMap.vertexDegree (oneEdgeCombMap.vertexOf false) = 1
  exact oneEdge_vertexDegree_false

/-- The degree-one endpoint occurs on the stored exterior traversal. -/
theorem oneEdge_false_mem_outerBoundary :
    oneEdgeDiagram.toCombMap.vertexOf false ∈
      discOuterBoundaryVertices oneEdgeDiagram := by
  classical
  rw [discOuterBoundaryVertices]
  rw [List.mem_toFinset, List.mem_map]
  refine ⟨false, ?_, rfl⟩
  exact ((oneEdgeDiagram.faceBoundary oneEdgeDiagram.outerFace).mem_iff false).mpr rfl

/-- The repaired local-data interface has no witness for the empty triangular
table on the one-edge disc: its boundary-degree field contradicts the
degree-one outer vertex. -/
theorem not_nonempty_triangularLocalData_emptyTable :
    ¬ Nonempty (TriangularDiagramLocalData emptyTriangleTable oneEdgeDiagram) := by
  rintro ⟨L⟩
  have hdegree := L.boundaryVertexDegree
    (oneEdgeDiagram.toCombMap.vertexOf false) oneEdge_false_mem_outerBoundary
  rw [oneEdgeDiagram_vertexDegree_false] at hdegree
  omega

end GirthEightPrimitives
end GGT
end GroupApproximation
