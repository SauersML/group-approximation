import GroupApproximation.GGT.KazhdanHypSymRelators
import GroupApproximation.GGT.KazhdanHypGirthEightVKInterface
import GroupApproximation.GGT.VanKampen.CombMapReduction
import GroupApproximation.Meta.AxiomGuard

set_option linter.unusedSectionVars false

/-!
# Oriented triangle faces and local data over the symmetrized family

A face of a disc diagram over `symTriangleRelatorWords T`
(`KazhdanHypSymRelators`) reads a triangle word or its formal inverse.  This
file gives the oriented readings and restates the cellular local data over the
symmetrized family.

* `orientedLetter t r k`: the `k`-th letter of `t` read forwards (`r = false`),
  or of its formal inverse `t 2⁻¹ · t 1⁻¹ · t 0⁻¹` (`r = true`);
  `orientedWord t r` is the three-letter word.
* `revInv_triangleRelatorWord`, `mem_sym_iff_orientedWord`,
  `length_of_mem_sym`: the symmetrized words are exactly the oriented words,
  and every one has length three.
* `adjacencyCount_orientedCorner_pos`: **a corner of an oriented face is an
  edge of the presentation link.**  The link is undirected
  (`TriangularHodgeLayer.adjacencyCount = directed u v + directed v u`), and a
  reversed corner is the transposed directed corner of the forward triangle.
  So `PresentationLinkWalk T` needs no orientation: walks around interior
  vertices of symmetrized diagrams are link walks of the same graph, and a
  `TriangularRelatorSphericalMap T M` (typed on a bare `CombMap`) feeds
  `false_of_girthEightChecks` unchanged.
* `SymTriangleFacePositions T Delta f`: the positive `TriangleFacePositions`
  with a `reversed` flag, `label_eq` reading `orientedLetter`.
* `SymTriangularDiagramLocalData T Delta`: the positive
  `TriangularDiagramLocalData` over the symmetrized family, with the curvature
  consequence `rCellCount_le_three_mul_boundaryWord_length`.
-/

namespace GroupApproximation
namespace GGT
namespace KazhdanHypSymLocalData

open GroupApproximation.KazhdanHyp

section Table

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]

/-! ## Oriented letters and words -/

/-- Inverting a signed generator twice does nothing. -/
theorem inverseSigned_inverseSigned (u : TriangularHodgeLayer.SignedGenerator Generator) :
    TriangularHodgeLayer.inverseSigned (TriangularHodgeLayer.inverseSigned u) = u := by
  obtain ⟨a, b⟩ := u
  cases b <;> rfl

/-- Formal inversion of a letter inverts the signed generator. -/
theorem inv_signedFreeRelLetter (u : TriangularHodgeLayer.SignedGenerator Generator) :
    HullSC.RelWord.inv (signedFreeRelLetter u) =
      signedFreeRelLetter (TriangularHodgeLayer.inverseSigned u) := by
  obtain ⟨a, b⟩ := u
  cases b
  · show GGT.RelLetter.base ((FreeGroup.of a)⁻¹)⁻¹ = GGT.RelLetter.base (FreeGroup.of a)
    rw [inv_inv]
  · rfl

/-- The `k`-th letter of a triangle read forwards (`false`), or of its formal
inverse `t 2⁻¹ · t 1⁻¹ · t 0⁻¹` (`true`). -/
def orientedLetter (t : TriangularHodgeLayer.Triangle Generator) :
    Bool → Fin 3 → TriangularHodgeLayer.SignedGenerator Generator
  | false, k => t k
  | true, k => TriangularHodgeLayer.inverseSigned (t (2 - k))

/-- The three-letter word of an oriented triangle. -/
def orientedWord (t : TriangularHodgeLayer.Triangle Generator) (r : Bool) :
    List (GGT.RelLetter (FreeGroup Generator) PEmpty.{1}) :=
  [signedFreeRelLetter (orientedLetter t r 0), signedFreeRelLetter (orientedLetter t r 1),
    signedFreeRelLetter (orientedLetter t r 2)]

theorem orientedWord_length (t : TriangularHodgeLayer.Triangle Generator) (r : Bool) :
    (orientedWord t r).length = 3 := rfl

/-- The forward oriented word is the triangle word. -/
theorem orientedWord_false (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (j : TriangleIndex) : orientedWord (T j) false = triangleRelatorWord.{0} T j := by
  rw [triangleRelatorWord, TriangularHodgeLayer.letters_eq_three]
  rfl

/-- **The formal inverse of a triangle word is the reversed oriented word.** -/
theorem revInv_triangleRelatorWord
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (j : TriangleIndex) :
    HullSC.RelWord.revInv (triangleRelatorWord.{0} T j) = orientedWord (T j) true := by
  rw [HullSC.RelWord.revInv, triangleRelatorWord, TriangularHodgeLayer.letters_eq_three]
  simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, inv_signedFreeRelLetter]
  rfl

/-- **The symmetrized words are the oriented words.** -/
theorem mem_sym_iff_orientedWord
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
    {v : List (GGT.RelLetter (FreeGroup Generator) PEmpty.{1})} :
    v ∈ symTriangleRelatorWords.{0} T ↔ ∃ j r, orientedWord (T j) r = v := by
  rw [mem_symTriangleRelatorWords]
  constructor
  · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨j, false, orientedWord_false T j⟩
    · exact ⟨j, true, (revInv_triangleRelatorWord T j).symm⟩
  · rintro ⟨j, r, rfl⟩
    cases r
    · exact Or.inl ⟨j, (orientedWord_false T j).symm⟩
    · exact Or.inr ⟨j, revInv_triangleRelatorWord T j⟩

/-- Every symmetrized word has length three. -/
theorem length_of_mem_sym {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
    {v : List (GGT.RelLetter (FreeGroup Generator) PEmpty.{1})}
    (hv : v ∈ symTriangleRelatorWords.{0} T) : v.length = 3 := by
  obtain ⟨j, r, rfl⟩ := mem_sym_iff_orientedWord.mp hv
  rfl

/-! ## Oriented corners are link edges -/

theorem nextCorner_two_sub_nextCorner (k : Fin 3) :
    TriangularHodgeLayer.nextCorner (2 - TriangularHodgeLayer.nextCorner k) = 2 - k := by
  fin_cases k <;> rfl

/-- A forward corner of a triangle is a directed corner of the table. -/
theorem directedAdjacencyCount_corner_pos
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (j : TriangleIndex)
    (k : Fin 3) :
    0 < TriangularHodgeLayer.directedAdjacencyCount T (T j k)
      (TriangularHodgeLayer.inverseSigned (T j (TriangularHodgeLayer.nextCorner k))) := by
  unfold TriangularHodgeLayer.directedAdjacencyCount
  exact Finset.card_pos.mpr ⟨(j, k), Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, rfl⟩⟩

/-- **A corner of an oriented face is an edge of the presentation link.**  The
corner from position `k` to `nextCorner k` of a face reading
`orientedWord (T j) r` joins the letter at `k` to the inverse of the letter at
`nextCorner k`.  Forwards this is the directed corner `(j, k)`; reversed it is
the transposed directed corner `(j, 2 - nextCorner k)`. -/
theorem adjacencyCount_orientedCorner_pos
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (j : TriangleIndex)
    (r : Bool) (k : Fin 3) :
    0 < TriangularHodgeLayer.adjacencyCount T (orientedLetter (T j) r k)
      (TriangularHodgeLayer.inverseSigned
        (orientedLetter (T j) r (TriangularHodgeLayer.nextCorner k))) := by
  cases r
  · show 0 < TriangularHodgeLayer.directedAdjacencyCount T (T j k)
        (TriangularHodgeLayer.inverseSigned (T j (TriangularHodgeLayer.nextCorner k))) +
      TriangularHodgeLayer.directedAdjacencyCount T
        (TriangularHodgeLayer.inverseSigned (T j (TriangularHodgeLayer.nextCorner k))) (T j k)
    exact Nat.lt_of_lt_of_le (directedAdjacencyCount_corner_pos T j k) (Nat.le_add_right _ _)
  · show 0 < TriangularHodgeLayer.directedAdjacencyCount T
        (TriangularHodgeLayer.inverseSigned (T j (2 - k)))
        (TriangularHodgeLayer.inverseSigned (TriangularHodgeLayer.inverseSigned
          (T j (2 - TriangularHodgeLayer.nextCorner k)))) +
      TriangularHodgeLayer.directedAdjacencyCount T
        (TriangularHodgeLayer.inverseSigned (TriangularHodgeLayer.inverseSigned
          (T j (2 - TriangularHodgeLayer.nextCorner k))))
        (TriangularHodgeLayer.inverseSigned (T j (2 - k)))
    have h := directedAdjacencyCount_corner_pos T j (2 - TriangularHodgeLayer.nextCorner k)
    rw [nextCorner_two_sub_nextCorner] at h
    rw [inverseSigned_inverseSigned]
    exact Nat.lt_of_lt_of_le h (Nat.le_add_left _ _)

/-! ## Oriented face positions -/

/-- Positions of one oriented triangle word on a face of a symmetrized diagram:
the positive `GirthEightVKInterface.TriangleFacePositions` with a `reversed`
flag.  `label_eq` reads `T triangle k` forwards, or `inverseSigned (T triangle (2 - k))`
on a reversed face. -/
structure SymTriangleFacePositions
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (symTriangleRelatorWords.{0} T))
    (f : Delta.toCombMap.Face) where
  /-- The defining triangle assigned to this face. -/
  triangle : TriangleIndex
  /-- Whether the face reads the formal inverse of the triangle word. -/
  reversed : Bool
  /-- The dart at each of the three positions. -/
  dart : Fin 3 → Delta.toCombMap.Dart
  /-- Each chosen dart lies on the face. -/
  onFace : ∀ k, Delta.toCombMap.faceOf (dart k) = f
  /-- The dart label is the oriented signed generator. -/
  label_eq : ∀ k, Delta.label (dart k) =
    signedFreeRelLetter (orientedLetter (T triangle) reversed k)
  /-- Face rotation advances to the next position. -/
  rotates : ∀ k, Delta.toCombMap.facePerm (dart k) =
    dart (TriangularHodgeLayer.nextCorner k)
  /-- The three positions contain every dart of the face. -/
  covers : ∀ d, Delta.toCombMap.faceOf d = f → ∃ k, dart k = d
  /-- Different positions give different darts. -/
  injective : Function.Injective dart

/-- The corner at an oriented face position is an edge of the presentation link. -/
theorem SymTriangleFacePositions.adjacencyCount_corner_pos
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
    {Delta : VanKampen.DiscDiagram.{0, 0, 0} (symTriangleRelatorWords.{0} T)}
    {f : Delta.toCombMap.Face} (P : SymTriangleFacePositions T Delta f) (k : Fin 3) :
    0 < TriangularHodgeLayer.adjacencyCount T (orientedLetter (T P.triangle) P.reversed k)
      (TriangularHodgeLayer.inverseSigned
        (orientedLetter (T P.triangle) P.reversed (TriangularHodgeLayer.nextCorner k))) :=
  adjacencyCount_orientedCorner_pos T P.triangle P.reversed k

/-! ## Local data over the symmetrized family -/

/-- The cellular local data of `TriangularDiagramLocalData`, over the
symmetrized family. -/
structure SymTriangularDiagramLocalData
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (symTriangleRelatorWords.{0} T)) where
  /-- Every inner face is represented by a stored relator cell. -/
  innerFaceCell : ∀ f, f ≠ Delta.outerFace →
    ∃ C ∈ Delta.relatorCells, C.face = f
  /-- The corners around each interior vertex form a reduced link circuit. -/
  interiorVertexWalk : ∀ v, v ∉ discOuterBoundaryVertices Delta →
    PresentationLinkWalk T (Delta.toCombMap.vertexDegree v)
  /-- Boundary vertices have valence at least two. -/
  boundaryVertexDegree : ∀ v, v ∈ discOuterBoundaryVertices Delta →
    2 ≤ Delta.toCombMap.vertexDegree v

namespace SymTriangularDiagramLocalData

variable {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator} {d : ℕ}
  {Delta : VanKampen.DiscDiagram.{0, 0, 0} (symTriangleRelatorWords.{0} T)}

/-- The local data covers the inner faces by stored cells. -/
theorem toRelatorCellCover (L : SymTriangularDiagramLocalData T Delta) :
    VanKampen.RelatorCellCover Delta :=
  ⟨L.innerFaceCell⟩

/-- Relator-cell coverage makes every inner face triangular. -/
theorem innerFaceDegree (L : SymTriangularDiagramLocalData T Delta)
    (f : Delta.toCombMap.Face) (hf : f ∈ Delta.innerFaces) :
    Delta.toCombMap.faceDegree f = 3 := by
  have hfne : f ≠ Delta.outerFace := by
    simpa only [VanKampen.DiscDiagram.innerFaces, Finset.mem_sdiff, Finset.mem_univ,
      true_and, Finset.mem_singleton] using hf
  obtain ⟨C, hCmem, hCface⟩ := L.innerFaceCell f hfne
  have hword : C.word = Delta.faceWord f := by
    rw [← hCface]
    exact Delta.relatorCell_word C hCmem
  have hlength : C.word.length = 3 := length_of_mem_sym C.word_mem
  have hfaceLength := Delta.faceWord_length f
  rw [← hword] at hfaceLength
  omega

/-- The checked link gives degree at least eight at every interior vertex. -/
theorem interiorVertexDegree (hchecks : GirthEightChecks T d)
    (L : SymTriangularDiagramLocalData T Delta)
    (v : Delta.toCombMap.Vertex) (hv : v ∉ discOuterBoundaryVertices Delta) :
    8 ≤ Delta.toCombMap.vertexDegree v :=
  (L.interiorVertexWalk v hv).eight_le_length hchecks

/-- The local data assembles the input of the curvature theorem. -/
noncomputable def toTriangularGirthEightDiagram (hchecks : GirthEightChecks T d)
    (L : SymTriangularDiagramLocalData T Delta) :
    VanKampen.TriangularGirthEightDiagram Delta where
  boundaryVertices := discOuterBoundaryVertices Delta
  innerFaceDegree := L.innerFaceDegree
  interiorVertexDegree := L.interiorVertexDegree hchecks
  boundaryVertexDegree := L.boundaryVertexDegree
  boundaryVertexCount_le := discOuterBoundaryVertices_card_le Delta

/-- **The relator-cell area is at most three times the exterior word length.** -/
theorem rCellCount_le_three_mul_boundaryWord_length (hchecks : GirthEightChecks T d)
    (L : SymTriangularDiagramLocalData T Delta) :
    Delta.rCellCount ≤ 3 * Delta.boundaryWord.length :=
  VanKampen.TriangularGirthEightDiagram.rCellCount_le_three_mul_boundaryWord_length
    (L.toTriangularGirthEightDiagram hchecks)

end SymTriangularDiagramLocalData

end Table

end KazhdanHypSymLocalData
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.KazhdanHypSymLocalData.revInv_triangleRelatorWord
#audit_axioms GroupApproximation.GGT.KazhdanHypSymLocalData.mem_sym_iff_orientedWord
#audit_axioms GroupApproximation.GGT.KazhdanHypSymLocalData.adjacencyCount_orientedCorner_pos
#audit_axioms GroupApproximation.GGT.KazhdanHypSymLocalData.SymTriangleFacePositions.adjacencyCount_corner_pos
#audit_axioms GroupApproximation.GGT.KazhdanHypSymLocalData.SymTriangularDiagramLocalData.rCellCount_le_three_mul_boundaryWord_length
