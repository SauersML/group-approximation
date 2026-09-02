import GroupApproximation.GGT.HullSCLemma44OrientedCells
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# The relative Greendlinger certificate used by Hull's Lemma 4.4

Osin's Lemma 4.4 supplies a relator cell whose contiguity degree to the outer
boundary is at least `1 - 23 * mu`.  The combinatorial-map diagram proving that
lemma is independent of its quotient applications.  This file specifies the
finite certificate those applications use: the outer boundary word, the
relator cells and their labels, and an optional boundary contiguity for every
cell.  A contiguity includes its relator prefix, its position in the outer
boundary, and two side words of length at most `eps`.

`RelativeGreendlingerStatement` is universe-polymorphic and has Osin's order of
choice.  The hyperbolically embedded relative generating set and `mu` are fixed
first; `eps` and a lower bound for `rho` are then chosen before the relator
family and reduced diagram.  The statement is the target of the combinatorial
relative van Kampen diagram construction.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric

universe u w

/-- The boundary contiguity data for one oriented relator cell.  The exterior
word is a prefix after orienting the cell.  `boundaryBefore` and
`boundaryAfter` give the exact position of the opposite arc in the designated
outer boundary, while `leftSide` and `rightSide` are the two short sides of the
contiguity subdiagram. -/
structure RelativeBoundaryContiguity
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps : ℕ)
    (boundaryWord : List G) (relator : List (GGT.RelLetter G Lambda)) where
  exterior : List (GGT.RelLetter G Lambda)
  remainder : List (GGT.RelLetter G Lambda)
  relator_decomposition : relator = exterior ++ remainder
  boundaryBefore : List G
  boundaryArc : List G
  boundaryAfter : List G
  boundary_decomposition :
    boundaryWord = boundaryBefore ++ boundaryArc ++ boundaryAfter
  leftSide : List (GGT.RelLetter G Lambda)
  rightSide : List (GGT.RelLetter G Lambda)
  leftSide_admissible : RelWord.IsAdmissible D leftSide
  rightSide_admissible : RelWord.IsAdmissible D rightSide
  leftSide_short : leftSide.length ≤ eps
  rightSide_short : rightSide.length ≤ eps
  exterior_value : GGT.RelLetter.listVal exterior =
    GGT.RelLetter.listVal leftSide * boundaryArc.prod *
      GGT.RelLetter.listVal rightSide

namespace RelativeBoundaryContiguity

/-- The exterior contiguity arc is no longer than its relator boundary. -/
theorem exterior_length_le_relator
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ} {boundaryWord : List G}
    {relator : List (GGT.RelLetter G Lambda)}
    (C : RelativeBoundaryContiguity D eps boundaryWord relator) :
    C.exterior.length ≤ relator.length := by
  have hlength := congrArg List.length C.relator_decomposition
  simp only [List.length_append] at hlength
  omega

/-- The opposite boundary arc is no longer than the designated outer word. -/
theorem boundaryArc_length_le_boundaryWord
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ} {boundaryWord : List G}
    {relator : List (GGT.RelLetter G Lambda)}
    (C : RelativeBoundaryContiguity D eps boundaryWord relator) :
    C.boundaryArc.length ≤ boundaryWord.length := by
  have hlength := congrArg List.length C.boundary_decomposition
  simp only [List.length_append] at hlength
  omega

end RelativeBoundaryContiguity

/-- In a reduced diagram no oriented cell reads the empty relator: such a
cell would contribute the value `1`, a trivial subproduct of the factor
list. -/
theorem Lemma44OrientedRelatorCell.relator_ne_nil_of_reduced
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {cells : List (Lemma44OrientedRelatorCell W)} {factors : List G}
    (hcells : cells.map Lemma44OrientedRelatorCell.value = factors)
    (hreduced : ∀ pre mid suf : List G,
      factors = pre ++ mid ++ suf → mid ≠ [] → mid.prod ≠ 1)
    (i : Fin cells.length) : (cells.get i).relator ≠ [] := by
  intro hnil
  subst hcells
  have hval : (cells.get i).value = 1 := by
    unfold Lemma44OrientedRelatorCell.value
    rw [hnil, GGT.RelLetter.listVal_nil, mul_one, mul_inv_cancel]
  have hi : (i : ℕ) < (cells.map Lemma44OrientedRelatorCell.value).length := by
    rw [List.length_map]
    exact i.isLt
  have hfac : (cells.map Lemma44OrientedRelatorCell.value)[(i : ℕ)] = 1 := by
    rw [List.getElem_map]
    rw [List.get_eq_getElem] at hval
    exact hval
  have hsplit : cells.map Lemma44OrientedRelatorCell.value =
      (cells.map Lemma44OrientedRelatorCell.value).take i ++ [1] ++
        (cells.map Lemma44OrientedRelatorCell.value).drop (i + 1) := by
    rw [← hfac, List.take_append_getElem hi, List.take_append_drop]
  exact hreduced _ _ _ hsplit (List.cons_ne_nil _ _) (by simp)

/-- The common reduced-diagram input to relative Greendlinger.  Both Hull
Lemma 4.4 and Hull Lemma 4.9 provide these fields: a nontrivial designated
boundary word, a positive list of oriented relator cells whose product is the
boundary value, and the cell-level reducedness condition inherited from least
area.  No geodesicity condition is imposed on the whole boundary word; each
application supplies its own boundary geometry separately. -/
structure RelativeReducedDiagram
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda))) (R : ℕ) where
  boundaryWord : List G
  boundary : G
  boundary_ne_one : boundary ≠ 1
  boundaryWord_isWord : IsWord D.alphabet.carrier boundaryWord boundary
  boundary_length_le : boundaryWord.length ≤ 2 * R
  area : ℕ
  area_pos : 0 < area
  cells : List (Lemma44OrientedRelatorCell W)
  cells_length : cells.length = area
  cell_values_prod :
    (cells.map Lemma44OrientedRelatorCell.value).prod = boundary
  no_cancelling_pair : ∀
      (pre between suf : List (Lemma44OrientedRelatorCell W))
      (C₁ C₂ : Lemma44OrientedRelatorCell W),
    cells = pre ++ C₁ :: (between ++ C₂ :: suf) →
      ((between.map Lemma44OrientedRelatorCell.value).prod)⁻¹ * C₁.value *
        (between.map Lemma44OrientedRelatorCell.value).prod * C₂.value ≠ 1
  cell_relator_ne_nil : ∀ i : Fin cells.length, (cells.get i).relator ≠ []

/-- A least-area diagram used by Hull's Lemma 4.4 supplies the common reduced
diagram interface with its stored geodesic boundary word. -/
def Lemma44OrientedRelatorDiagram.toRelativeReducedDiagram
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : Lemma44OrientedRelatorDiagram D.alphabet W R) :
    RelativeReducedDiagram D W R where
  boundaryWord := Z.boundaryWord
  boundary := Z.boundary
  boundary_ne_one := Z.boundary_ne_one
  boundaryWord_isWord := Z.boundaryWord_isWord
  boundary_length_le := by
    rw [Z.boundaryWord_geodesic]
    exact Z.boundary_length_le
  area := Z.area
  area_pos := Z.area_pos
  cells := Z.cells
  cells_length := by
    calc
      Z.cells.length = Z.factors.length := by
        have h := congrArg List.length Z.cell_values
        simpa only [List.length_map] using h
      _ = Z.area := Z.factors_length
  cell_values_prod := by rw [Z.cell_values, Z.factors_prod]
  no_cancelling_pair := Z.noCancellingCellPair
  cell_relator_ne_nil := fun i =>
    Lemma44OrientedRelatorCell.relator_ne_nil_of_reduced Z.cell_values
      Z.reduced i

/-- Lemma 4.4 diagrams coerce to the common reduced-diagram input, so its
quotient application and the power-diagram application consume the same
Greendlinger proposition. -/
instance lemma44OrientedRelatorDiagramCoeRelativeReducedDiagram
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ} :
    Coe (Lemma44OrientedRelatorDiagram D.alphabet W R)
      (RelativeReducedDiagram D W R) where
  coe Z := Z.toRelativeReducedDiagram D

/-- The finite output of Osin's relative Greendlinger lemma.  The cell index
is `Fin Z.cells.length`, so the labels cover exactly the relator cells of the
oriented reduced input.  Each cell may have a chosen boundary contiguity;
`largeCell` selects one whose exterior arc has degree at least
`1 - 23 * mu`. -/
structure RelativeDiagramCertificate
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    (eps : ℕ) (mu : ℝ) {R : ℕ}
    (Z : RelativeReducedDiagram D W R) where
  boundaryWord : List G
  boundaryWord_eq : boundaryWord = Z.boundaryWord
  cellLabel : Fin Z.cells.length → List (GGT.RelLetter G Lambda)
  /-- **The label of a cell is a cyclic permutation of its relator.**

  This used to be literal equality.  It is weakened because the planar side of
  Osin's argument produces a *cyclic* arc of the cell's dart cycle
  (`GGT.VanKampen.Embedded.Contiguity.sourceArc` is a
  `CyclicArc (cellDarts Delta source)`), while
  `RelativeBoundaryContiguity.relator_decomposition` asks the exterior to be a
  **prefix**.  Rotating the label turns a cyclic subword into a prefix, which
  is exactly Osin's own convention: `RelWord.IsSmallCancellation` requires the
  family to be closed under cyclic permutation (`rotate_mem`), and the file's
  own remark records that "every cyclic subword of a cyclic permutation is a
  prefix of a cyclic permutation".

  Nothing downstream reads this field -- consumers use `cellLabel` and
  `cellLabel_mem` only -- so the weakening costs no consumer and buys the
  planar-to-algebraic conversion its rotation. -/
  cellLabel_rotate : ∀ i, ∃ n : ℕ,
    cellLabel i = ((Z.cells.get i).relator).rotate n
  cellLabel_mem : ∀ i, cellLabel i ∈ W
  contiguity : ∀ i : Fin Z.cells.length,
    Option (RelativeBoundaryContiguity D eps boundaryWord (cellLabel i))
  largeCell : ∃ (i : Fin Z.cells.length)
      (C : RelativeBoundaryContiguity D eps boundaryWord (cellLabel i)),
    contiguity i = some C ∧
      (1 - 23 * mu) * (cellLabel i).length ≤ (C.exterior.length : ℝ)

/-- Osin's Lemma 4.4 in the certificate form consumed by Hull's Lemma 4.4.
For every `mu` in Osin's range, `eps` and the initial length threshold are
chosen from the hyperbolic relative Cayley graph.  Increasing `rho` preserves
the conclusion, so quotient applications may impose their additional boundary
length threshold after `eps` is known. -/
def RelativeGreendlingerStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda),
    D.IsHyperbolicallyEmbedded →
      ∀ mu : ℝ, 0 < mu → mu ≤ 1 / 16 →
        ∃ eps rho0 : ℕ, ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (GGT.RelLetter G Lambda))) (R : ℕ),
            RelWord.IsLemma44Input D W eps mu rho →
              ∀ Z : RelativeReducedDiagram D W R,
                Nonempty (RelativeDiagramCertificate D W eps mu Z)

/-! ## Model checks -/

/-- No reduced diagram exists over the empty relator family.  Its positive
area makes the cell list nonempty, while every oriented cell must label itself
by a member of the family. -/
theorem no_relativeReducedDiagram_emptyFamily
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (R : ℕ) :
    IsEmpty (RelativeReducedDiagram D
      (∅ : Set (List (GGT.RelLetter G Lambda))) R) := by
  refine ⟨fun Z => ?_⟩
  have hcellsPos : 0 < Z.cells.length := by
    rw [Z.cells_length]
    exact Z.area_pos
  obtain ⟨C, cells, hcells⟩ := List.exists_cons_of_length_pos hcellsPos
  have hCmem : C ∈ Z.cells := by
    rw [hcells]
    exact List.mem_cons_self
  have hfalse : C.relator ∈
      (∅ : Set (List (GGT.RelLetter G Lambda))) := by
    exact C.relator_mem
  exact (Set.mem_empty_iff_false C.relator).mp hfalse

/-- The empty family branch of the certificate conclusion is valid in every
group because its diagram hypothesis is empty. -/
theorem relativeGreendlinger_emptyFamilyModel
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) {eps : ℕ} {mu : ℝ} (R : ℕ) :
    ∀ Z : RelativeReducedDiagram D
        (∅ : Set (List (GGT.RelLetter G Lambda))) R,
      Nonempty (RelativeDiagramCertificate D ∅ eps mu Z) := by
  intro Z
  exact False.elim ((no_relativeReducedDiagram_emptyFamily D R).false Z)

/-- A positive length threshold excludes the empty relator word from every
family satisfying the published Lemma 4.4 input. -/
theorem emptyWord_not_mem_of_lemma44Input
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho) (hrho : 0 < rho) :
    [] ∉ W := by
  intro hempty
  have hlong : rho ≤ ([] : List (GGT.RelLetter G Lambda)).length :=
    hsc.long [] hempty
  simp only [List.length_nil] at hlong
  omega

/-- In the one-point group every designated boundary element equals `1`, so
the nontrivial reduced-diagram input is impossible.  This proves the complete
relative Greendlinger statement in the trivial model. -/
theorem relativeGreendlingerStatement_trivialModel
    {Lambda : Type w} (D : GGT.RelGenSet PUnit Lambda) :
    D.IsHyperbolicallyEmbedded →
      ∀ mu : ℝ, 0 < mu → mu ≤ 1 / 16 →
        ∃ eps rho0 : ℕ, ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (GGT.RelLetter PUnit Lambda))) (R : ℕ),
            RelWord.IsLemma44Input D W eps mu rho →
              ∀ Z : RelativeReducedDiagram D W R,
                Nonempty (RelativeDiagramCertificate D W eps mu Z) := by
  intro _ mu _ _
  refine ⟨0, 0, ?_⟩
  intro rho hrho W R hsc Z
  have hboundary : Z.boundary = 1 := Subsingleton.elim _ _
  exact (Z.boundary_ne_one hboundary).elim

/-- The empty-family check specializes to the two-point cyclic group. -/
theorem relativeGreendlingerStatement_twoPointEmptyModel
    {Lambda : Type w}
    (D : GGT.RelGenSet (Multiplicative (ZMod 2)) Lambda)
    {eps : ℕ} {mu : ℝ} (R : ℕ) :
    ∀ Z : RelativeReducedDiagram D
        (∅ : Set (List (GGT.RelLetter (Multiplicative (ZMod 2)) Lambda))) R,
      Nonempty (RelativeDiagramCertificate D ∅ eps mu Z) :=
  relativeGreendlinger_emptyFamilyModel D R

/-- The empty-family check specializes to the free group on one generator. -/
theorem relativeGreendlingerStatement_freeGroupOneGeneratorEmptyModel
    {Lambda : Type w} (D : GGT.RelGenSet (FreeGroup Unit) Lambda)
    {eps : ℕ} {mu : ℝ} (R : ℕ) :
    ∀ Z : RelativeReducedDiagram D
        (∅ : Set (List (GGT.RelLetter (FreeGroup Unit) Lambda))) R,
      Nonempty (RelativeDiagramCertificate D ∅ eps mu Z) :=
  relativeGreendlinger_emptyFamilyModel D R

end HullSC
end GroupApproximation
