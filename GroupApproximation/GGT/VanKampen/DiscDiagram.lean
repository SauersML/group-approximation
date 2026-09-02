import GroupApproximation.GGT.VanKampen.CombMap
import GroupApproximation.GGT.HullSCLemma44OrientedCells
import Mathlib.Data.List.Chain

/-!
# Relative disc diagrams

This file defines a planar disc diagram over the relative alphabet
`X ⊔ ⨆ H_lambda`.  A face cycle is an ordered, duplicate-free enumeration of a
face orbit.  Darts carry relative letters and edge reversal applies the formal
letter inverse.  The disc boundary is the reverse-inverse of the outer-face
traversal in the closed combinatorial map.  One face is distinguished as the
exterior face.  Every other face is either listed as a relator cell or has
boundary value one in the base group, so it is a `G`-cell in Osin's
presentation convention.

Relator cells are ordered and based by conjugators.  Their conjugate-product
is required to be the exterior boundary value.  From that datum this file
proves the easy direction of van Kampen's lemma: the boundary value belongs to
the normal closure of the values of the relator family.

The last part states the precise remaining cactus realization problem for the
least-area algebraic diagrams already used by Hull's Lemma 4.4.  A realization
has the same exterior word and the same ordered factor list.  These two
equalities prove both its area equality and its diagram-level reducedness from
the existing algebraic no-cancelling-pair theorem.  Constructing the
permutations of that cactus is a geometric existence problem, not an added
hypothesis in the definition of reducedness.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

open GroupApproximation.HullSC

universe u w v

/-- An ordered traversal of one face orbit. -/
structure FaceBoundary (M : CombMap) (f : M.Face) where
  /-- Darts encountered while going around the face. -/
  darts : List M.Dart
  /-- A face has a nonempty boundary. -/
  nonempty : darts ≠ []
  /-- Every dart occurs at most once in the traversal. -/
  nodup : darts.Nodup
  /-- The list contains exactly the darts in the chosen face orbit. -/
  mem_iff : ∀ d : M.Dart, d ∈ darts ↔ M.faceOf d = f
  /-- Consecutive darts follow the face permutation. -/
  chain : darts.IsChain fun d e => M.facePerm d = e
  /-- The final dart closes back to the initial dart. -/
  closes : M.facePerm (darts.getLast nonempty) = darts.head nonempty
  /-- The enumeration has the orbit cardinality. -/
  length_eq_degree : darts.length = M.faceDegree f

/-- A relator face with a chosen base path.  `reversed = true` uses the
inverse orientation of the face word in its based value. -/
structure RelatorCell {G : Type u} [Group G] {Lambda : Type w}
    (M : CombMap) (outer : M.Face)
    (W : Set (List (GGT.RelLetter G Lambda))) where
  face : M.Face
  face_ne_outer : face ≠ outer
  word : List (GGT.RelLetter G Lambda)
  word_mem : word ∈ W
  conjugator : G
  reversed : Bool

namespace RelatorCell

/-- The signed conjugate contributed by a based relator cell. -/
def value {G : Type u} [Group G] {Lambda : Type w}
    {M : CombMap} {outer : M.Face}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (C : RelatorCell M outer W) : G :=
  if C.reversed then
    C.conjugator * (GGT.RelLetter.listVal C.word)⁻¹ * C.conjugator⁻¹
  else
    C.conjugator * GGT.RelLetter.listVal C.word * C.conjugator⁻¹

/-- Every relator-cell value belongs to the normal closure of the relator
values. -/
theorem value_mem_normalClosure {G : Type u} [Group G] {Lambda : Type w}
    {M : CombMap} {outer : M.Face}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (C : RelatorCell M outer W) :
    C.value ∈ Subgroup.normalClosure (GGT.RelLetter.listVal '' W) := by
  have hbase : GGT.RelLetter.listVal C.word ∈
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W) :=
    Subgroup.subset_normalClosure ⟨C.word, C.word_mem, rfl⟩
  cases hrev : C.reversed
  · rw [value, hrev]
    exact Subgroup.normalClosure_normal.conj_mem _ hbase C.conjugator
  · rw [value, hrev]
    have hinv : (GGT.RelLetter.listVal C.word)⁻¹ ∈
        Subgroup.normalClosure (GGT.RelLetter.listVal '' W) :=
      (Subgroup.normalClosure (GGT.RelLetter.listVal '' W)).inv_mem hbase
    exact Subgroup.normalClosure_normal.conj_mem _ hinv C.conjugator

end RelatorCell

/-- A planar relative disc diagram with an exterior face, `G`-faces, and an
ordered list of based relator faces. -/
structure DiscDiagram {G : Type u} [Group G] {Lambda : Type w}
    (W : Set (List (GGT.RelLetter G Lambda))) where
  toCombMap : CombMap.{v}
  planar : toCombMap.IsPlanar
  label : toCombMap.Dart → GGT.RelLetter G Lambda
  label_alpha : ∀ d : toCombMap.Dart,
    label (toCombMap.alpha d) = HullSC.RelWord.inv (label d)
  outerFace : toCombMap.Face
  faceBoundary : ∀ f : toCombMap.Face, FaceBoundary toCombMap f
  relatorCells : List (RelatorCell toCombMap outerFace W)
  relatorCell_faces_nodup :
    (relatorCells.map RelatorCell.face).Nodup
  relatorCell_word : ∀ C ∈ relatorCells,
    C.word = ((faceBoundary C.face).darts.map label)
  inner_face : ∀ f : toCombMap.Face, f ≠ outerFace →
    (∃ C ∈ relatorCells, C.face = f) ∨
      GGT.RelLetter.listVal ((faceBoundary f).darts.map label) = 1
  boundary_product :
    (relatorCells.map RelatorCell.value).prod =
      GGT.RelLetter.listVal
        (HullSC.RelWord.revInv ((faceBoundary outerFace).darts.map label))

namespace DiscDiagram

/-- The word read around a face. -/
def faceWord {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram W) (f : Delta.toCombMap.Face) :
    List (GGT.RelLetter G Lambda) :=
  (Delta.faceBoundary f).darts.map Delta.label

/-- A face word has the combinatorial degree of its face. -/
theorem faceWord_length {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram W) (f : Delta.toCombMap.Face) :
    (Delta.faceWord f).length = Delta.toCombMap.faceDegree f := by
  rw [faceWord, List.length_map]
  exact (Delta.faceBoundary f).length_eq_degree

/-- The exterior boundary word.  The outer face of the closed map has the
opposite orientation from the boundary of the remaining disc. -/
def boundaryWord {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram W) : List (GGT.RelLetter G Lambda) :=
  HullSC.RelWord.revInv (Delta.faceWord Delta.outerFace)

/-- Reverse-inversion preserves the length of the exterior traversal. -/
theorem boundaryWord_length {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram W) :
    Delta.boundaryWord.length = Delta.toCombMap.faceDegree Delta.outerFace := by
  rw [boundaryWord, HullSC.RelWord.revInv, List.length_reverse,
    List.length_map, Delta.faceWord_length]

/-- The group element read around the exterior boundary. -/
def boundaryValue {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram W) : G :=
  GGT.RelLetter.listVal Delta.boundaryWord

/-- The number of relator faces. -/
def rCellCount {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram W) : ℕ := Delta.relatorCells.length

/-- The stored product formula in boundary-value notation. -/
theorem relatorValues_prod_eq_boundaryValue
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram W) :
    (Delta.relatorCells.map RelatorCell.value).prod = Delta.boundaryValue :=
  Delta.boundary_product

/-- Products of relator-cell values stay in the normal closure. -/
theorem relatorValues_prod_mem_normalClosure
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram W) :
    (Delta.relatorCells.map RelatorCell.value).prod ∈
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W) := by
  induction Delta.relatorCells with
  | nil =>
      exact Subgroup.one_mem _
  | cons C cells ih =>
      rw [List.map_cons, List.prod_cons]
      exact Subgroup.mul_mem _ C.value_mem_normalClosure ih

/-- The easy direction of van Kampen's lemma: a disc boundary is in the
normal closure of the relator values. -/
theorem boundaryValue_mem_normalClosure
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram W) :
    Delta.boundaryValue ∈
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W) := by
  rw [← Delta.relatorValues_prod_eq_boundaryValue]
  exact Delta.relatorValues_prod_mem_normalClosure

/-- Diagram-level reducedness.  This is the no-cancelling-pair condition used
in Osin Lemma 4.4: two relator cells cannot cancel after transport across the
ordered cells between them. -/
def Reduced {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram W) : Prop :=
  ∀ (pre between suf : List (RelatorCell Delta.toCombMap Delta.outerFace W))
    (C₁ C₂ : RelatorCell Delta.toCombMap Delta.outerFace W),
    Delta.relatorCells = pre ++ C₁ :: (between ++ C₂ :: suf) →
      ((between.map RelatorCell.value).prod)⁻¹ * C₁.value *
        (between.map RelatorCell.value).prod * C₂.value ≠ 1

/-- The empty-relator model is reduced because it contains no pair of
relator cells. -/
theorem reduced_of_no_rCells
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram W) (h : Delta.relatorCells = []) : Delta.Reduced := by
  intro pre between suf C₁ C₂ hsplit
  rw [h] at hsplit
  have hlen := congrArg List.length hsplit
  simp only [List.length_nil, List.length_append, List.length_cons] at hlen
  omega

/-- A diagram with no relator cells has identity boundary value. -/
theorem boundaryValue_eq_one_of_no_rCells
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram W) (h : Delta.relatorCells = []) :
    Delta.boundaryValue = 1 := by
  rw [← Delta.relatorValues_prod_eq_boundaryValue, h]
  rfl

/-- A nonidentity exterior boundary forces at least one relator cell. -/
theorem rCellCount_pos_of_boundaryValue_ne_one
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram W) (h : Delta.boundaryValue ≠ 1) :
    0 < Delta.rCellCount := by
  rw [rCellCount, List.length_pos_iff]
  intro hnil
  exact h (Delta.boundaryValue_eq_one_of_no_rCells hnil)

end DiscDiagram

/-! ## The cactus realization frontier -/

/-- A planar cactus realization of an existing oriented least-area algebraic
diagram.  The outer word and the ordered cell values agree with the algebraic
data. -/
structure CactusRealization
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) where
  diagram : DiscDiagram.{u, w, 0} W
  boundaryWord_eq : diagram.boundaryWord =
    Z.boundaryWord.map (GGT.RelLetter.base : G → GGT.RelLetter G Lambda)
  cellValues_eq : diagram.relatorCells.map RelatorCell.value = Z.factors

namespace CactusRealization

/-- A cactus realization has the same boundary value as its algebraic
diagram. -/
theorem boundaryValue_eq
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    {Z : HullSC.Lemma44OrientedRelatorDiagram A W R}
    (C : CactusRealization Z) : C.diagram.boundaryValue = Z.boundary := by
  rw [← C.diagram.relatorValues_prod_eq_boundaryValue, C.cellValues_eq,
    Z.factors_prod]

/-- A cactus realization has exactly the algebraic least area. -/
theorem rCellCount_eq_area
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    {Z : HullSC.Lemma44OrientedRelatorDiagram A W R}
    (C : CactusRealization Z) : C.diagram.rCellCount = Z.area := by
  have hlen := congrArg List.length C.cellValues_eq
  simpa only [DiscDiagram.rCellCount, List.length_map, Z.factors_length] using hlen

/-- The already-proved algebraic no-cancelling-pair condition makes every
cactus realization reduced.  This is the reducedness form used by the
cell-to-cell piece argument. -/
theorem reduced
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    {Z : HullSC.Lemma44OrientedRelatorDiagram A W R}
    (C : CactusRealization Z) : C.diagram.Reduced := by
  intro pre between suf C₁ C₂ hsplit
  apply Z.no_cancelling_pair
    (pre.map RelatorCell.value)
    (between.map RelatorCell.value)
    (suf.map RelatorCell.value) C₁.value C₂.value
  rw [← C.cellValues_eq, hsplit]
  simp only [List.map_append, List.map_cons]

end CactusRealization

/-- The hard direction needed from the cactus construction: every oriented
least-area algebraic diagram has a planar labelled realization with the same
outer word and factor list. -/
def CactusRealizationStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R),
    Nonempty (CactusRealization Z)

/-- A cactus realization theorem supplies a reduced planar disc diagram with
the prescribed boundary value and relator-cell count. -/
theorem exists_reduced_discDiagram_of_cactusRealization
    (hcactus : CactusRealizationStatement.{u, w})
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    ∃ Delta : DiscDiagram W,
      Delta.boundaryValue = Z.boundary ∧
      Delta.rCellCount = Z.area ∧ Delta.Reduced := by
  obtain ⟨C⟩ := hcactus Z
  exact ⟨C.diagram, C.boundaryValue_eq, C.rCellCount_eq_area, C.reduced⟩

/-- The cactus statement has the intended trivial-group model: an oriented
Lemma 4.4 diagram would have a nonidentity boundary in a subsingleton group,
so there is no input diagram. -/
theorem cactusRealization_trivialModel
    {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet PUnit}
    {W : Set (List (GGT.RelLetter PUnit Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    Nonempty (CactusRealization Z) := by
  exact (Z.boundary_ne_one (Subsingleton.elim _ _)).elim

/-- The empty-family branch is valid in every group: positive area makes the
oriented cell list nonempty, while its first cell would have to label itself
by a member of the empty family. -/
theorem cactusRealization_emptyFamilyModel
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A
      (∅ : Set (List (GGT.RelLetter G Lambda))) R) :
    Nonempty (CactusRealization Z) := by
  have hcellsLength : Z.cells.length = Z.area := by
    calc
      Z.cells.length = Z.factors.length := by
        have h := congrArg List.length Z.cell_values
        simpa only [List.length_map] using h
      _ = Z.area := Z.factors_length
  have hcellsPos : 0 < Z.cells.length := by
    rw [hcellsLength]
    exact Z.area_pos
  let i : Fin Z.cells.length := ⟨0, hcellsPos⟩
  have hfalse : (Z.cells.get i).relator ∈
      (∅ : Set (List (GGT.RelLetter G Lambda))) :=
    (Z.cells.get i).relator_mem
  exact (Set.mem_empty_iff_false (Z.cells.get i).relator).mp hfalse

end VanKampen
end GGT
end GroupApproximation
