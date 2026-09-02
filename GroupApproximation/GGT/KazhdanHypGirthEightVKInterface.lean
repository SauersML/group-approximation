import GroupApproximation.GGT.KazhdanHypGirthEightLocalization
import GroupApproximation.GGT.KazhdanHypGirthEightSlim
import GroupApproximation.GGT.VanKampen.CombMapStars

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The van Kampen interface for girth-eight triangle presentations

This module isolates the combinatorial-map operations needed by the two
remaining geometric arguments for a positive triangular presentation.

For hyperbolicity, McCammond--Wise, *Fans and ladders in small cancellation
theory*, Definition 3.4 and Corollary 3.9, read the cyclic corners at an
interior vertex as a reduced path in the presentation link.  Papasoglu's
successive-star proof then uses vertex labels in the Cayley graph, boundary
subpaths, and disjoint layers of faces.  The structures below give exact types
to those operations over `VanKampen.DiscDiagram`.

For torsion, Huebschmann, *Cohomology theory of aspherical groups and of small
cancellation groups*, J. Pure Appl. Algebra 14 (1979), Theorems 3 and 4,
classifies finite-order elements in an aspherical presentation by roots of
defining relators.  The accessible account in *Homological Group Theory*,
page 272, says that this classification is obtained from Serre's theorem on
cohomology of finite subgroups.  Thus `leastPowerDisc` and `gluePowerDisc`
below specify the requested geometric replacement by a reduced diagram for
`w^n`; they are not attributed to Huebschmann's cohomological proof.

The committed `CombMap` API already proves preservation of a vertex under
`sigma`, and `DiscDiagram` already gives ordered face boundaries and literal
relator words.  This file proves the consequences of those facts.  Local link
walks and boundary valence are requested only after a
`TriangularDiagramLocalData` witness has supplied cellular reducedness and a
spur-free boundary.  Algebraic `DiscDiagram.Reduced` alone does not imply
either condition: the reduced one-edge disc in
`KazhdanHypGirthEightPrimitives` is the counterexample.
-/

namespace GroupApproximation
namespace GGT
namespace GirthEightVKInterface

open GroupApproximation.KazhdanHyp
open GroupApproximation.WordMetric
open scoped BigOperators

/-! ## Cyclic corners and literal face positions -/

/-- A cyclic enumeration of all darts based at one vertex.  The enumeration
uses `Nat` so its successor equation has no casts; `periodic`, `covers`, and
`unique` say that the first `vertexDegree` terms are exactly the orbit. -/
structure CyclicCornerEnumeration (M : VanKampen.CombMap) (v : M.Vertex) where
  /-- The dart at a natural corner position. -/
  dart : ℕ → M.Dart
  /-- The initial dart is based at the specified vertex. -/
  zero_at : M.vertexOf (dart 0) = v
  /-- Successive corners follow the vertex rotation. -/
  rotates : ∀ i, dart (i + 1) = M.sigma (dart i)
  /-- The enumeration repeats after the vertex degree. -/
  periodic : ∀ i, dart (i + M.vertexDegree v) = dart i
  /-- Every dart based at the vertex occurs in the first period. -/
  covers : ∀ d, M.vertexOf d = v →
    ∃ i, i < M.vertexDegree v ∧ dart i = d
  /-- Positions in the first period are distinct. -/
  unique : ∀ i j, i < M.vertexDegree v → j < M.vertexDegree v →
    dart i = dart j → i = j

namespace CyclicCornerEnumeration

variable {M : VanKampen.CombMap} {v : M.Vertex}

/-- Every enumerated corner is based at the stated vertex.  This follows from
`CombMap.vertexOf_sigma`; it is not an additional vk primitive. -/
theorem atVertex (C : CyclicCornerEnumeration M v) :
    ∀ i, M.vertexOf (C.dart i) = v := by
  intro i
  induction i with
  | zero => exact C.zero_at
  | succ i ih =>
      calc
        M.vertexOf (C.dart (Nat.succ i)) =
            M.vertexOf (C.dart (i + 1)) := by rw [Nat.succ_eq_add_one]
        _ = M.vertexOf (M.sigma (C.dart i)) :=
          congrArg M.vertexOf (C.rotates i)
        _ = M.vertexOf (C.dart i) := M.vertexOf_sigma (C.dart i)
        _ = v := ih

/-- The successor corner has the same vertex as the current corner. -/
theorem successor_sameVertex (C : CyclicCornerEnumeration M v) (i : ℕ) :
    M.vertexOf (C.dart (i + 1)) = M.vertexOf (C.dart i) := by
  rw [C.rotates i, M.vertexOf_sigma]

end CyclicCornerEnumeration

section Table

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]

/-- Positions of one literal triangle relator on a face.  The successor
condition uses the same `nextCorner` convention as the presentation-link
adjacency count. -/
structure TriangleFacePositions
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (f : Delta.toCombMap.Face) where
  /-- The defining triangle assigned to this face. -/
  triangle : TriangleIndex
  /-- The dart at each of the three relator positions. -/
  dart : Fin 3 → Delta.toCombMap.Dart
  /-- Each chosen dart lies on the face. -/
  onFace : ∀ k, Delta.toCombMap.faceOf (dart k) = f
  /-- The dart label is the corresponding literal signed generator. -/
  label_eq : ∀ k, Delta.label (dart k) = signedFreeRelLetter (T triangle k)
  /-- Face rotation advances to the next literal corner. -/
  rotates : ∀ k, Delta.toCombMap.facePerm (dart k) =
    dart (TriangularHodgeLayer.nextCorner k)
  /-- The three positions contain every dart of the face. -/
  covers : ∀ d, Delta.toCombMap.faceOf d = f → ∃ k, dart k = d
  /-- Different literal positions give different darts. -/
  injective : Function.Injective dart

/-- Every inner face of a relator-only diagram is a stored relator cell. -/
structure RelatorOnly
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T)) : Prop where
  cell : ∀ f, f ≠ Delta.outerFace →
    ∃ C ∈ Delta.relatorCells, C.face = f

namespace RelatorOnly

variable {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
  {Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T)}

/-- Relator-only coverage is the first field of the already checked local
disc data. -/
theorem innerFaceCell (R : RelatorOnly T Delta) :
    ∀ f, f ≠ Delta.outerFace →
      ∃ C ∈ Delta.relatorCells, C.face = f :=
  R.cell

/-- A relator-only inner face has exactly one literal triangle word.  This is
obtained solely from `DiscDiagram.relatorCell_word` and membership in
`triangleRelatorWords`. -/
theorem exists_faceWord_eq (R : RelatorOnly T Delta)
    (f : Delta.toCombMap.Face) (hf : f ≠ Delta.outerFace) :
    ∃ j, Delta.faceWord f = triangleRelatorWord T j := by
  obtain ⟨C, hCmem, hCface⟩ := R.cell f hf
  obtain ⟨j, hj⟩ := C.word_mem
  refine ⟨j, ?_⟩
  have hword : C.word = Delta.faceWord f := by
    rw [← hCface]
    exact Delta.relatorCell_word C hCmem
  exact hword.symm.trans hj.symm

/-- Relator-only coverage makes every inner face triangular. -/
theorem innerFaceDegree (R : RelatorOnly T Delta)
    (f : Delta.toCombMap.Face) (hf : f ∈ Delta.innerFaces) :
    Delta.toCombMap.faceDegree f = 3 := by
  have hfne : f ≠ Delta.outerFace := by
    simpa only [VanKampen.DiscDiagram.innerFaces, Finset.mem_sdiff,
      Finset.mem_univ, true_and, Finset.mem_singleton] using hf
  obtain ⟨j, hj⟩ := R.exists_faceWord_eq f hfne
  calc
    Delta.toCombMap.faceDegree f = (Delta.faceWord f).length :=
      (Delta.faceWord_length f).symm
    _ = (triangleRelatorWord T j).length := congrArg List.length hj
    _ = 3 := triangleRelatorWord_length T j

/-- If every non-outer face has nonidentity word in the free base group, the
existing `DiscDiagram.inner_face` alternative already supplies relator-only
coverage. -/
theorem of_innerFaceWord_ne_one
    (h : ∀ f, f ≠ Delta.outerFace →
      GGT.RelLetter.listVal (Delta.faceWord f) ≠ 1) :
    RelatorOnly T Delta where
  cell f hf := exists_relatorCell_of_inner_faceWord_ne_one Delta f hf (h f hf)

/-- Degeneracy model for `RelatorOnly`: a diagram with no face other than its
outer face satisfies the interface without a relator cell. -/
theorem noInnerFacesModel
    (h : ∀ f : Delta.toCombMap.Face, f = Delta.outerFace) :
    RelatorOnly T Delta where
  cell f hf := (hf (h f)).elim

end RelatorOnly

/-! ## Removing free-base cells -/

/-- Output of eliminating the `G`-cells allowed by the relative
`DiscDiagram` definition.  For the ordinary presentation the base group is
free.  A `G`-cell has freely trivial boundary value, but it must be removed
before the all-triangular face-degree count is applied. -/
structure RelatorOnlyReduction
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T)) where
  /-- The diagram after deleting freely trivial base cells. -/
  diagram : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T)
  /-- The exterior word is unchanged. -/
  boundaryWord_eq : diagram.boundaryWord = Delta.boundaryWord
  /-- Cell elimination does not increase relator area. -/
  rCellCount_le : diagram.rCellCount ≤ Delta.rCellCount
  /-- Reducedness is preserved. -/
  reduced : diagram.Reduced
  /-- Every remaining inner face is a literal relator cell. -/
  relatorOnly : RelatorOnly T diagram

/-! ## Cayley labels and boundary subpaths -/

/-- Evaluate an ordinary relative letter in the triangularly presented
group.  The peripheral branch is impossible because its index is `PEmpty`. -/
def presentedLetterValue
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) :
    GGT.RelLetter (FreeGroup Generator) PEmpty →
      TriangularHodgeLayer.Presented T
  | .base x => PresentedGroup.mk
      (TriangularHodgeLayer.relators T : Set (FreeGroup Generator)) x
  | .comp i _ => PEmpty.elim i

/-- A labelling of diagram vertices by the Cayley graph.  Traversing a dart
multiplies its initial vertex label by the presented value of the dart label. -/
structure CayleyVertexLabelling
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T)) where
  /-- The Cayley vertex assigned to a map vertex. -/
  value : Delta.toCombMap.Vertex → TriangularHodgeLayer.Presented T
  /-- Edge compatibility in the dart orientation. -/
  edge : ∀ d,
    value (Delta.toCombMap.vertexOf (Delta.toCombMap.alpha d)) =
      value (Delta.toCombMap.vertexOf d) * presentedLetterValue T (Delta.label d)

/-- A linearly represented subpath of the chosen outer-face traversal.  The
split field makes the occurrence literal and the chain field exposes the
successor relation used by the star construction. -/
structure BoundarySubpath
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T)) where
  /-- Darts of the subpath in traversal order. -/
  darts : List Delta.toCombMap.Dart
  /-- Darts before this occurrence. -/
  beforeDarts : List Delta.toCombMap.Dart
  /-- Darts after this occurrence. -/
  afterDarts : List Delta.toCombMap.Dart
  /-- The occurrence lies in the stored outer boundary list. -/
  split : (Delta.faceBoundary Delta.outerFace).darts =
    beforeDarts ++ darts ++ afterDarts
  /-- Consecutive darts follow the outer face rotation. -/
  chain : darts.IsChain fun d e ↦ Delta.toCombMap.facePerm d = e

/-- The endpoints of a nonempty boundary subpath, expressed as map vertices. -/
def BoundarySubpath.startVertex
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
    {Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T)}
    (P : BoundarySubpath T Delta) (h : P.darts ≠ []) :
    Delta.toCombMap.Vertex :=
  Delta.toCombMap.vertexOf (P.darts.head h)

/-- A packaged output of the successive-star construction.  Its final four
inequalities are exactly the input of
`presented_isHyperbolicGroup_of_girthEight_layer_construction`. -/
structure SuccessiveStarLayers
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) where
  /-- The reduced relator-only filling diagram. -/
  diagram : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T)
  /-- Its local corner data. -/
  localData : TriangularDiagramLocalData T diagram
  /-- Cayley labels used to identify the three geodesic boundary pieces. -/
  cayley : CayleyVertexLabelling T diagram
  /-- The centered part of the long side. -/
  side : BoundarySubpath T diagram
  /-- Number of disjoint face-star layers. -/
  depth : ℕ
  /-- Length scale of the centered window. -/
  scale : ℕ
  /-- Endpoint loss in each layer. -/
  loss : ℕ
  /-- Maximum number of boundary edges contributed by one layer face. -/
  perimeter : ℕ
  /-- Cardinality of each layer. -/
  layer : Fin depth → ℕ
  /-- The truncated triangle has controlled perimeter. -/
  boundary_bound : diagram.combinatorialBoundaryLength ≤ 6 * scale
  /-- The layers are disjoint subsets of inner faces. -/
  layer_disjoint : (∑ i, layer i) ≤ diagram.innerFaceCount
  /-- Each layer covers the surviving long-side segment. -/
  layer_covers : ∀ i, scale - loss ≤ perimeter * layer i
  /-- A far point would force more layers than the area bound permits. -/
  depth_too_large :
    18 * perimeter * scale < depth * (scale - loss)

/-! ## Power discs and the spherical output -/

/-- A reduced relator-only diagram for a literal word repeated `n` times.
This is the minimal-disc input to the requested geometric torsion argument. -/
structure PowerDisc
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (g : TriangularHodgeLayer.Presented T) (n : ℕ) where
  /-- A literal signed word representing `g`. -/
  word : List (TriangularHodgeLayer.SignedGenerator Generator)
  /-- The word maps to the chosen presented-group element. -/
  represents : PresentedGroup.mk
      (TriangularHodgeLayer.relators T : Set (FreeGroup Generator))
      (PresentedGroupRelatorReplay.word word) = g
  /-- A reduced disc for the repeated boundary word. -/
  diagram : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T)
  /-- The stored exterior traversal is the concatenation of `n` copies. -/
  boundary_eq : diagram.boundaryWord =
    (List.replicate n (word.map signedFreeRelLetter)).flatten
  /-- The chosen disc is diagram-reduced. -/
  reduced : diagram.Reduced
  /-- Free-base cells have been eliminated. -/
  relatorOnly : RelatorOnly T diagram

/-! ## The single vk construction record -/

/-- The two local projections used by triangular curvature.

The input is deliberately `TriangularDiagramLocalData`, rather than the
strictly weaker `DiscDiagram.Reduced`.  The former contains the cellular
nonbacktracking link walk and the boundary-immersion degree estimate.  This
conditioning excludes the one-edge boundary-spur countermodel without making
an assertion about unrelated reduced diagrams. -/
structure LocalDiagramProjections
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) where
  /-- Project the nonbacktracking link walk at an interior vertex. -/
  linkWalk : ∀
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (L : TriangularDiagramLocalData T Delta)
    (v : Delta.toCombMap.Vertex),
    v ∉ discOuterBoundaryVertices Delta →
    PresentationLinkWalk T (Delta.toCombMap.vertexDegree v)
  /-- Project the degree estimate at a spur-free boundary vertex. -/
  boundaryDegree : ∀
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (L : TriangularDiagramLocalData T Delta)
    (v : Delta.toCombMap.Vertex),
    v ∈ discOuterBoundaryVertices Delta →
    2 ≤ Delta.toCombMap.vertexDegree v

namespace LocalDiagramProjections

variable {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}

/-- The local diagram record itself gives both conditioned projections. -/
def canonical : LocalDiagramProjections T where
  linkWalk _ L v hv := L.interiorVertexWalk v hv
  boundaryDegree _ L v hv := L.boundaryVertexDegree v hv

/-- Rebuilding the local record through the projection interface preserves
all three inputs used by the curvature consumer. -/
def rebuild (_P : LocalDiagramProjections T)
    {Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T)}
    (L : TriangularDiagramLocalData T Delta) :
    TriangularDiagramLocalData T Delta where
  innerFaceCell := L.innerFaceCell
  interiorVertexWalk := _P.linkWalk Delta L
  boundaryVertexDegree := _P.boundaryDegree Delta L

/-- The repaired local interface is inhabited for every triangle table. -/
theorem nonemptyModel : Nonempty (LocalDiagramProjections T) :=
  ⟨canonical⟩

end LocalDiagramProjections

omit [Fintype Generator] [DecidableEq Generator]
    [Fintype TriangleIndex] [DecidableEq TriangleIndex] in
/-- Every vertex in the committed six-dart one-triangle rotation model has
degree at least two.  This is the boundary-valence model for the repaired
conditional interface; no claim is made for the unrelated one-edge spur. -/
theorem oneTriangle_vertexDegree_two_le
    (d : VanKampen.OneTriangleDart) :
    2 ≤ VanKampen.oneTriangleCombMap.vertexDegree
      (VanKampen.oneTriangleCombMap.vertexOf d) := by
  change 2 ≤ VanKampen.CombMap.orbitDegree
    VanKampen.oneTriangleCombMap.sigma (Quotient.mk'' d)
  rw [← VanKampen.closedOrbitList.length_eq_orbitDegree]
  have hne : VanKampen.oneTriangleCombMap.sigma d ≠ d := by
    rcases d with ⟨i, b⟩
    cases b <;> simp [VanKampen.oneTriangleCombMap,
      VanKampen.oneTriangleSigma]
  rw [VanKampen.closedOrbitList, if_neg hne]
  exact Equiv.Perm.two_le_length_toList_iff_mem_support.mpr
    (by simpa [Equiv.Perm.mem_support] using hne)

/-- Operations still needed from the van Kampen implementation.

`cornerCycle`, `facePositions`, and `linkWalk` form the local
`C(3)`--`T(8)` bridge.  `removeBaseCells` deals with the relative diagram's
free-group cells.  `successiveStars` is the topological input to the metric
slim-triangle theorem.  `leastPowerDisc` and `gluePowerDisc` isolate the
geometric finite-order-to-sphere construction requested as an alternative to
Huebschmann's cohomological theorem. -/
structure GirthEightDiagramPrimitives
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) where
  /-- Conditioned projections from cellular local diagram data. -/
  local : LocalDiagramProjections T
  /-- Enumerate the corners at every map vertex. -/
  cornerCycle : ∀
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (v : Delta.toCombMap.Vertex),
    CyclicCornerEnumeration Delta.toCombMap v
  /-- Assign a triangle and its three positions to every relator-only face. -/
  facePositions : ∀
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T))
    (_R : RelatorOnly T Delta) (f : Delta.toCombMap.Face),
    f ≠ Delta.outerFace → TriangleFacePositions T Delta f
  /-- Delete the freely trivial base-group cells. -/
  removeBaseCells : ∀
    (Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T)),
    Delta.Reduced → RelatorOnlyReduction T Delta
  /-- A far point in a geodesic triangle produces the Cayley-labelled
  boundary subpath and disjoint successive-star layers. -/
  successiveStars : ∀ (delta : ℕ)
    (x y z p : TriangularHodgeLayer.Presented T),
    Hyperbolic.IsBetween
      (↑(GirthEightSlim.presentedGeneratorFinset T) :
        Set (TriangularHodgeLayer.Presented T)) x p y →
    (∀ q, Hyperbolic.IsBetween
      (↑(GirthEightSlim.presentedGeneratorFinset T) :
        Set (TriangularHodgeLayer.Presented T)) x q z →
      delta < wordDist
        (↑(GirthEightSlim.presentedGeneratorFinset T) :
          Set (TriangularHodgeLayer.Presented T)) p q) →
    (∀ q, Hyperbolic.IsBetween
      (↑(GirthEightSlim.presentedGeneratorFinset T) :
        Set (TriangularHodgeLayer.Presented T)) z q y →
      delta < wordDist
        (↑(GirthEightSlim.presentedGeneratorFinset T) :
          Set (TriangularHodgeLayer.Presented T)) p q) →
    SuccessiveStarLayers T
  /-- Construct a least reduced diagram for a representative of `g^n`. -/
  leastPowerDisc : ∀ (g : TriangularHodgeLayer.Presented T) (n : ℕ),
    0 < n → g ^ n = 1 → g ≠ 1 → PowerDisc T g n
  /-- The non-cone branch of the power-disc argument gives a labelled reduced
  sphere unless a defining relator is a proper power. -/
  gluePowerDisc : ∀ (g : TriangularHodgeLayer.Presented T) (n : ℕ)
    (D : PowerDisc T g n),
    (∀ j, ¬ RelatorIsProperPower (TriangularHodgeLayer.relator (T j))) →
    ∃ M : VanKampen.CombMap.{0},
      Nonempty (VanKampen.TriangularRelatorSphericalMap T M)

namespace GirthEightDiagramPrimitives

variable {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}

/-- Re-project local data after the cellular reduction has supplied it.  The
operation cannot manufacture spur-freeness from algebraic reducedness; it
only exposes the data already proved for the diagram used by the consumer. -/
def localData (P : GirthEightDiagramPrimitives T)
    {Delta : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T)}
    (L : TriangularDiagramLocalData T Delta) :
    TriangularDiagramLocalData T Delta :=
  P.local.rebuild L

/-- The successive-star field has exactly the type consumed by the existing
slim-triangle theorem. -/
theorem isHyperbolicGroup
    (P : GirthEightDiagramPrimitives T) {d delta : ℕ}
    (hchecks : GirthEightChecks T d) :
    Hyperbolic.IsHyperbolicGroup (TriangularHodgeLayer.Presented T) := by
  apply GirthEightSlim.presented_isHyperbolicGroup_of_girthEight_layer_construction
    hchecks
  intro x y z p hp hfarXZ hfarZY
  let L := P.successiveStars delta x y z p hp hfarXZ hfarZY
  exact ⟨L.diagram, L.localData, L.depth, L.scale, L.loss, L.perimeter,
    L.layer, L.boundary_bound, L.layer_disjoint, L.layer_covers,
    L.depth_too_large⟩

/-- The two power-disc fields supply the spherical extraction input of
`presented_isPowerTorsionFree_of_sphericalExtraction`. -/
theorem sphericalExtraction
    (P : GirthEightDiagramPrimitives T) :
    ∀ (g : TriangularHodgeLayer.Presented T) (n : ℕ),
      0 < n → g ^ n = 1 → g ≠ 1 →
      (∀ j, ¬ RelatorIsProperPower
        (TriangularHodgeLayer.relator (T j))) →
      ∃ M : VanKampen.CombMap.{0},
        Nonempty (VanKampen.TriangularRelatorSphericalMap T M) := by
  intro g n hn hpow hne hnoProper
  exact P.gluePowerDisc g n (P.leastPowerDisc g n hn hpow hne) hnoProper

/-- A checked table with the vk primitives is torsion-free. -/
theorem isPowerTorsionFree
    (P : GirthEightDiagramPrimitives T) {d : ℕ}
    (hchecks : GirthEightChecks T d) :
    IsPowerTorsionFree (TriangularHodgeLayer.Presented T) :=
  presented_isPowerTorsionFree_of_sphericalExtraction hchecks
    P.sphericalExtraction

/-- End-to-end model test for the bundle: its geometric and torsion projections
can be consumed simultaneously for the same checked table. -/
theorem consumerModel
    (P : GirthEightDiagramPrimitives T) {d delta : ℕ}
    (hchecks : GirthEightChecks T d) :
    Hyperbolic.IsHyperbolicGroup (TriangularHodgeLayer.Presented T) ∧
      IsPowerTorsionFree (TriangularHodgeLayer.Presented T) :=
  ⟨P.isHyperbolicGroup (delta := delta) hchecks,
    P.isPowerTorsionFree hchecks⟩

end GirthEightDiagramPrimitives

/-! ## Assembly of the two universal geometric obligations -/

/-- A vk primitive package for every finite triangular table proves the
universal girth-eight hyperbolicity statement.  The `delta = 1` specialization
is only a witness for the existential hyperbolicity constant; the primitive
package constructs successive stars for every natural `delta`. -/
theorem girthEightHyperbolicity_of_diagramPrimitives
    (primitives : ∀ (Generator TriangleIndex : Type)
      (_ : Fintype Generator) (_ : DecidableEq Generator)
      (_ : Nonempty Generator) (_ : Fintype TriangleIndex)
      (_ : DecidableEq TriangleIndex)
      (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator),
      GirthEightDiagramPrimitives T) :
    GirthEightHyperbolicity := by
  intro Generator TriangleIndex fg dg ng ft dt T d hchecks
  let P : GirthEightDiagramPrimitives T :=
    primitives Generator TriangleIndex fg dg ng ft dt T
  exact P.isHyperbolicGroup (delta := 1) hchecks

/-- A vk primitive package for every finite triangular table proves the
universal girth-eight torsion-freeness statement.  The power-disc and gluing
fields give the reduced sphere, and `GirthEightChecks.noCube` supplies the
no-proper-power hypothesis used by spherical curvature. -/
theorem girthEightTorsionFree_of_diagramPrimitives
    (primitives : ∀ (Generator TriangleIndex : Type)
      (_ : Fintype Generator) (_ : DecidableEq Generator)
      (_ : Nonempty Generator) (_ : Fintype TriangleIndex)
      (_ : DecidableEq TriangleIndex)
      (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator),
      GirthEightDiagramPrimitives T) :
    GirthEightTorsionFree := by
  intro Generator TriangleIndex fg dg ng ft dt T d hchecks
  let P : GirthEightDiagramPrimitives T :=
    primitives Generator TriangleIndex fg dg ng ft dt T
  exact P.isPowerTorsionFree hchecks

end Table
end GirthEightVKInterface
end GGT
end GroupApproximation
