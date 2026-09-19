import GroupApproximation.GGT.VanKampen.CactusConstruction
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.Flatten
import GroupApproximation.GGT.HullSCRelatorWord

/-!
# The complementary boundary word of the labelled cactus

The complementary cactus face is traversed from the predecessor of the
distinguished outer dart.  Its dart list first runs backward around the outer
polygon and then, in increasing geometric order, runs out each stem,
backward around its relator polygon, and back along the stem.  Geometric cells
were attached in reverse algebraic order in `CactusConstruction`, so these
segments read the inverse algebraic factors in reverse order.

This file defines that explicit list and proves its labelled value is one.
The final section identifies it with the ordered complementary face orbit.
-/

namespace GroupApproximation
namespace HullSC
namespace Lemma44OrientedRelatorDiagram

open GGT.VanKampen

universe u w

/-- Reversing finite indices reverses the list made by `List.ofFn`. -/
theorem ofFn_comp_rev {X : Type*} {n : ℕ} (f : Fin n → X) :
    List.ofFn (fun i ↦ f i.rev) = (List.ofFn f).reverse := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ', List.concat_eq_append,
        List.reverse_append,
        List.reverse_singleton]
      simp only [Fin.rev_zero, Fin.rev_succ]
      rw [ih (fun i : Fin n ↦ f i.castSucc)]
      rfl

/-- Backward outer darts, from the predecessor of zero down to zero. -/
def cactusOuterBackwardDarts
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    List (CactusDart Z.cactusShape) :=
  List.ofFn fun j : Fin Z.cactusShape.boundaryLength ↦
    CactusDart.outerBackward j.rev

/-- Backward darts of geometric relator `i`, from its predecessor of zero
down to zero. -/
def cactusRelatorBackwardDarts
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (i : Fin Z.cells.length) : List (CactusDart Z.cactusShape) :=
  List.ofFn fun j : Fin (Z.cactusShape.relatorLength i) ↦
    CactusDart.relatorBackward i j.rev

/-- One complementary-face cell segment: outgoing stem, backward relator
polygon, incoming stem. -/
def cactusCellSegment
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (i : Fin Z.cells.length) : List (CactusDart Z.cactusShape) :=
  CactusDart.stemOut i ::
    Z.cactusRelatorBackwardDarts i ++ [CactusDart.stemIn i]

/-- All complementary-face cell segments in geometric order. -/
def cactusCellSegments
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    List (CactusDart Z.cactusShape) :=
  (List.ofFn fun i : Fin Z.cells.length ↦ Z.cactusCellSegment i).flatten

/-- The explicit complementary face traversal. -/
def cactusBigDarts
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    List (CactusDart Z.cactusShape) :=
  Z.cactusOuterBackwardDarts ++ Z.cactusCellSegments

/-- Backward outer labels form the reverse-inverse of the forward outer
word. -/
theorem cactusOuterBackwardWord
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    Z.cactusOuterBackwardDarts.map Z.cactusLabel =
      RelWord.revInv Z.cactusOuterFaceWord := by
  have hforward : List.ofFn (fun j : Fin Z.cactusShape.boundaryLength ↦
      Z.cactusLabel (.outerForward j)) = Z.cactusOuterFaceWord := by
    exact ofFn_get_cast Z.cactusOuterFaceWord (by
      rw [cactusOuterFaceWord, RelWord.length_revInv, List.length_map])
  calc
    Z.cactusOuterBackwardDarts.map Z.cactusLabel =
        List.ofFn (fun j : Fin Z.cactusShape.boundaryLength ↦
          RelWord.inv (Z.cactusLabel (.outerForward j.rev))) := by
      rw [cactusOuterBackwardDarts, ← List.ofFn_comp']
      rfl
    _ = (List.ofFn (fun j : Fin Z.cactusShape.boundaryLength ↦
          RelWord.inv (Z.cactusLabel (.outerForward j)))).reverse :=
      ofFn_comp_rev (fun j : Fin Z.cactusShape.boundaryLength ↦
        RelWord.inv (Z.cactusLabel (.outerForward j)))
    _ = RelWord.revInv
        (List.ofFn (fun j : Fin Z.cactusShape.boundaryLength ↦
          Z.cactusLabel (.outerForward j))) := by
      rw [RelWord.revInv, ← List.ofFn_comp']
    _ = RelWord.revInv Z.cactusOuterFaceWord := congrArg RelWord.revInv hforward

/-- The backward labels of a geometric relator polygon form the formal
reverse-inverse of its relator word. -/
theorem cactusRelatorBackwardWord
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (i : Fin Z.cells.length) :
    (Z.cactusRelatorBackwardDarts i).map Z.cactusLabel =
      RelWord.revInv (Z.geometricCell i).relator := by
  have hforward : List.ofFn
      (fun j : Fin (Z.cactusShape.relatorLength i) ↦
        Z.cactusLabel (.relatorForward i j)) =
      (Z.geometricCell i).relator :=
    List.ofFn_get (Z.geometricCell i).relator
  calc
    (Z.cactusRelatorBackwardDarts i).map Z.cactusLabel =
        List.ofFn (fun j : Fin (Z.cactusShape.relatorLength i) ↦
          RelWord.inv (Z.cactusLabel (.relatorForward i j.rev))) := by
      rw [cactusRelatorBackwardDarts, ← List.ofFn_comp']
      rfl
    _ = (List.ofFn (fun j : Fin (Z.cactusShape.relatorLength i) ↦
          RelWord.inv (Z.cactusLabel (.relatorForward i j)))).reverse :=
      ofFn_comp_rev (fun j : Fin (Z.cactusShape.relatorLength i) ↦
        RelWord.inv (Z.cactusLabel (.relatorForward i j)))
    _ = RelWord.revInv
        (List.ofFn (fun j : Fin (Z.cactusShape.relatorLength i) ↦
          Z.cactusLabel (.relatorForward i j))) := by
      rw [RelWord.revInv, ← List.ofFn_comp']
    _ = RelWord.revInv (Z.geometricCell i).relator :=
      congrArg RelWord.revInv hforward

/-- The labelled word on one complementary cell segment. -/
theorem cactusCellSegment_word
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (i : Fin Z.cells.length) :
    (Z.cactusCellSegment i).map Z.cactusLabel =
      [GGT.RelLetter.base (Z.geometricCell i).conjugator] ++
        RelWord.revInv (Z.geometricCell i).relator ++
      [GGT.RelLetter.base (Z.geometricCell i).conjugator⁻¹] := by
  unfold cactusCellSegment
  simp only [List.map_cons, List.map_append, cactusLabel]
  rw [Z.cactusRelatorBackwardWord i]
  simp only [List.map_nil, List.singleton_append]

/-- One complementary cell segment reads the inverse of its complete
geometric cell value. -/
theorem cactusCellSegment_value
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (i : Fin Z.cells.length) :
    GGT.RelLetter.listVal ((Z.cactusCellSegment i).map Z.cactusLabel) =
      (Z.geometricCell i).value⁻¹ := by
  rw [Z.cactusCellSegment_word i, RelWord.listVal_append,
    RelWord.listVal_append, RelWord.listVal_singleton,
    RelWord.listVal_revInv, RelWord.listVal_singleton,
    HullSC.val_base, HullSC.val_base,
    HullSC.Lemma44OrientedRelatorCell.value]
  group

/-- The backward outer traversal reads the exterior boundary value. -/
theorem cactusOuterBackward_value
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    GGT.RelLetter.listVal
        (Z.cactusOuterBackwardDarts.map Z.cactusLabel) = Z.boundary := by
  rw [Z.cactusOuterBackwardWord, RelWord.listVal_revInv,
    cactusOuterFaceWord, RelWord.listVal_revInv, HullSC.listVal_map_base,
    Z.boundaryWord_isWord.prod_eq, inv_inv]

/-- `listVal` converts flattening of a list of words into the product of
their individual values. -/
theorem listVal_flatten
    {G : Type u} [Group G] {Lambda : Type w}
    (L : List (List (GGT.RelLetter G Lambda))) :
    GGT.RelLetter.listVal L.flatten =
      (L.map GGT.RelLetter.listVal).prod := by
  induction L with
  | nil => rfl
  | cons l L ih =>
      rw [List.flatten_cons, RelWord.listVal_append, List.map_cons,
        List.prod_cons, ih]

/-- The inverse geometric cell values in geometric order are the inverse of
the original algebraic cell product. -/
theorem geometricCellValues_inv_prod
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    (List.ofFn fun i : Fin Z.cells.length ↦
      (Z.geometricCell i).value⁻¹).prod =
        (Z.cells.map HullSC.Lemma44OrientedRelatorCell.value).prod⁻¹ := by
  have hcells : List.ofFn (fun i : Fin Z.cells.length ↦
      (Z.cellAt i).value⁻¹) =
      (Z.cells.map HullSC.Lemma44OrientedRelatorCell.value).map fun x ↦ x⁻¹ := by
    calc
      List.ofFn (fun i : Fin Z.cells.length ↦ (Z.cellAt i).value⁻¹) =
          (List.ofFn Z.cells.get).map
            (fun C : HullSC.Lemma44OrientedRelatorCell W ↦ C.value⁻¹) := by
        rw [← List.ofFn_comp']
        rfl
      _ = Z.cells.map
          (fun C : HullSC.Lemma44OrientedRelatorCell W ↦ C.value⁻¹) := by
        rw [List.ofFn_get]
      _ = (Z.cells.map HullSC.Lemma44OrientedRelatorCell.value).map
          fun x ↦ x⁻¹ := by
        rw [List.map_map]
        change Z.cells.map (fun C => C.value⁻¹) =
          Z.cells.map (fun C => C.value⁻¹)
        rfl
  calc
    (List.ofFn fun i : Fin Z.cells.length ↦
        (Z.geometricCell i).value⁻¹).prod =
        (List.ofFn fun i : Fin Z.cells.length ↦
          (Z.cellAt i).value⁻¹).reverse.prod := by
      exact congrArg List.prod
        (ofFn_comp_rev (fun i : Fin Z.cells.length ↦ (Z.cellAt i).value⁻¹))
    _ = ((Z.cells.map HullSC.Lemma44OrientedRelatorCell.value).map
          fun x ↦ x⁻¹).reverse.prod := by rw [hcells]
    _ = (Z.cells.map HullSC.Lemma44OrientedRelatorCell.value).prod⁻¹ :=
      (List.prod_inv_reverse _).symm

/-- All complementary cell segments read the inverse of the algebraic factor
product. -/
theorem cactusCellSegments_value
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    GGT.RelLetter.listVal (Z.cactusCellSegments.map Z.cactusLabel) =
      Z.boundary⁻¹ := by
  rw [cactusCellSegments, List.map_flatten, listVal_flatten,
    ← List.ofFn_comp']
  have hvalues : List.ofFn
      (fun i : Fin Z.cells.length ↦
        GGT.RelLetter.listVal ((Z.cactusCellSegment i).map Z.cactusLabel)) =
      List.ofFn (fun i : Fin Z.cells.length ↦
        (Z.geometricCell i).value⁻¹) := by
    apply congrArg List.ofFn
    funext i
    exact Z.cactusCellSegment_value i
  rw [← List.ofFn_comp', hvalues, Z.geometricCellValues_inv_prod,
    Z.cell_values, Z.factors_prod]

/-- The explicit complementary boundary word has value one. -/
theorem cactusBigDarts_value
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    GGT.RelLetter.listVal (Z.cactusBigDarts.map Z.cactusLabel) = 1 := by
  rw [cactusBigDarts, List.map_append, RelWord.listVal_append,
    Z.cactusOuterBackward_value, Z.cactusCellSegments_value, mul_inv_cancel]

/-! ## No repetitions in the complementary traversal -/

/-- Backward outer darts occur once. -/
theorem cactusOuterBackwardDarts_nodup
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    Z.cactusOuterBackwardDarts.Nodup := by
  rw [cactusOuterBackwardDarts]
  apply List.nodup_ofFn_ofInjective
  intro i j hij
  have hrev : i.rev = j.rev := CactusDart.outerBackward.inj hij
  exact Fin.rev_injective hrev

/-- Backward darts of one relator polygon occur once. -/
theorem cactusRelatorBackwardDarts_nodup
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (i : Fin Z.cells.length) :
    (Z.cactusRelatorBackwardDarts i).Nodup := by
  rw [cactusRelatorBackwardDarts]
  apply List.nodup_ofFn_ofInjective
  intro j k hjk
  have hrev : j.rev = k.rev := eq_of_heq (CactusDart.relatorBackward.inj hjk).2
  exact Fin.rev_injective hrev

/-- One cell segment contains no repeated dart. -/
theorem cactusCellSegment_nodup
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (i : Fin Z.cells.length) : (Z.cactusCellSegment i).Nodup := by
  have hout : CactusDart.stemOut i ∉
      Z.cactusRelatorBackwardDarts i ++ [CactusDart.stemIn i] := by
    simp [cactusRelatorBackwardDarts, List.mem_ofFn]
  have hin : CactusDart.stemIn i ∉ Z.cactusRelatorBackwardDarts i := by
    simp [cactusRelatorBackwardDarts, List.mem_ofFn]
  unfold cactusCellSegment
  exact List.Nodup.cons hout
    ((Z.cactusRelatorBackwardDarts_nodup i).append (by simp)
      (by simpa [List.disjoint_left] using hin))

/-- A dart lying in two cell segments determines the same cell index. -/
theorem eq_of_mem_cactusCellSegment
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    {i j : Fin Z.cells.length} {d : CactusDart Z.cactusShape}
    (hi : d ∈ Z.cactusCellSegment i) (hj : d ∈ Z.cactusCellSegment j) :
    i = j := by
  cases d <;>
    simp_all [cactusCellSegment, cactusRelatorBackwardDarts, List.mem_ofFn]

/-- Distinct cell segments are disjoint. -/
theorem cactusCellSegment_disjoint
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    {i j : Fin Z.cells.length} (hij : i ≠ j) :
    List.Disjoint (Z.cactusCellSegment i) (Z.cactusCellSegment j) := by
  rw [List.disjoint_left]
  intro d hi hj
  exact hij (Z.eq_of_mem_cactusCellSegment hi hj)

/-- All flattened cell segments contain no repeated dart. -/
theorem cactusCellSegments_nodup
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    Z.cactusCellSegments.Nodup := by
  rw [cactusCellSegments, List.nodup_flatten]
  constructor
  · intro l hl
    rw [List.mem_ofFn] at hl
    obtain ⟨i, rfl⟩ := hl
    exact Z.cactusCellSegment_nodup i
  · rw [List.pairwise_ofFn]
    intro i j hij
    exact Z.cactusCellSegment_disjoint hij.ne

/-- Backward outer darts do not occur in a cell segment. -/
theorem cactusOuterBackwardDarts_disjoint_cellSegment
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (i : Fin Z.cells.length) :
    List.Disjoint Z.cactusOuterBackwardDarts (Z.cactusCellSegment i) := by
  rw [List.disjoint_left]
  intro d hdouter hdcell
  rw [cactusOuterBackwardDarts, List.mem_ofFn] at hdouter
  obtain ⟨j, rfl⟩ := hdouter
  simp [cactusCellSegment, cactusRelatorBackwardDarts,
    List.mem_ofFn] at hdcell

/-- The outer part and the flattened cell part are disjoint. -/
theorem cactusOuterBackwardDarts_disjoint_cellSegments
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    List.Disjoint Z.cactusOuterBackwardDarts Z.cactusCellSegments := by
  rw [List.disjoint_left]
  intro d hdouter hdsegments
  rw [cactusCellSegments, List.mem_flatten] at hdsegments
  obtain ⟨l, hl, hdl⟩ := hdsegments
  rw [List.mem_ofFn] at hl
  obtain ⟨i, rfl⟩ := hl
  exact (List.disjoint_left.mp
    (Z.cactusOuterBackwardDarts_disjoint_cellSegment i)) hdouter hdl

/-- The full explicit complementary traversal contains every one of its
darts exactly once. -/
theorem cactusBigDarts_nodup
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    Z.cactusBigDarts.Nodup := by
  rw [cactusBigDarts]
  exact Z.cactusOuterBackwardDarts_nodup.append
    Z.cactusCellSegments_nodup
    Z.cactusOuterBackwardDarts_disjoint_cellSegments

/-! ## The complementary face orbit -/

/-- The oriented algebraic cell list is positive. -/
theorem cells_length_pos
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    0 < Z.cells.length := by
  have hcells : Z.cells.length = Z.factors.length := by
    have h := congrArg List.length Z.cell_values
    simpa only [List.length_map] using h
  rw [hcells, Z.factors_length]
  exact Z.area_pos

/-- The explicit complementary traversal is nonempty because its outer
polygon is positive. -/
theorem cactusBigDarts_ne_nil
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    Z.cactusBigDarts ≠ [] := by
  intro hnil
  have hmem : CactusDart.outerBackward Z.cactusShape.boundaryZero ∈
      Z.cactusBigDarts := by
    rw [cactusBigDarts, List.mem_append]
    left
    rw [cactusOuterBackwardDarts, List.mem_ofFn]
    exact ⟨Z.cactusShape.boundaryZero.rev, by rw [Fin.rev_rev]⟩
  rw [hnil] at hmem
  simp at hmem

/-- A dart belongs to the complementary face exactly when its explicit face
classifier is `big`. -/
theorem faceOf_eq_bigFace_iff (S : CactusShape) (d : CactusDart S) :
    S.toCombMap.faceOf d = S.bigFace ↔ S.faceClass d = .big := by
  change S.toCombMap.faceOf d =
      S.toCombMap.faceOf (S.faceRepresentative .big) ↔ _
  constructor
  · intro h
    have hcycle : S.toCombMap.facePerm.SameCycle d
        (S.faceRepresentative .big) :=
      (S.toCombMap.faceOf_eq_iff d (S.faceRepresentative .big)).mp h
    calc
      S.faceClass d = S.faceClass (S.faceRepresentative .big) :=
        OrbitClassifier.eq_of_sameCycle S.toCombMap.facePerm S.faceClass
          S.faceClass_facePerm hcycle
      _ = .big := S.faceClass_representative .big
  · intro h
    rw [S.toCombMap.faceOf_eq_iff]
    have hcycle := S.faceRepresentative_sameCycle d
    rw [h] at hcycle
    exact hcycle.symm

/-- Membership in the explicit list is exactly membership in the
complementary face. -/
theorem mem_cactusBigDarts_iff
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (d : CactusDart Z.cactusShape) :
    d ∈ Z.cactusBigDarts ↔
      Z.cactusShape.toCombMap.faceOf d = Z.cactusShape.bigFace := by
  rw [faceOf_eq_bigFace_iff Z.cactusShape d]
  have hrev : ∀ {n : ℕ} (j : Fin n), ∃ i : Fin n, i.rev = j := by
    intro n j
    exact ⟨j.rev, Fin.rev_rev j⟩
  cases d <;>
    simp [cactusBigDarts, cactusOuterBackwardDarts, cactusCellSegments,
      cactusCellSegment, cactusRelatorBackwardDarts, List.mem_ofFn,
      CactusShape.faceClass, hrev]

/-! ## Successive darts in the complementary traversal -/

/-- A reversed index with an ordinary successor remaining is not zero. -/
theorem rev_mk_ne_zero {n k : ℕ} (hk : k + 1 < n) :
    Fin.rev (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin n) ≠
      (⟨0, by omega⟩ : Fin n) := by
  intro hzero
  have hval := congrArg Fin.val hzero
  simp only [Fin.val_rev] at hval
  exact (Nat.sub_pos_iff_lt.mpr hk).ne' hval

/-- Reversed finite indices turn an ordinary successor into a cyclic
predecessor. -/
theorem prevFin_rev_succ {n k : ℕ} (hk : k + 1 < n) :
    CactusShape.prevFin n
        (Fin.rev (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin n)) =
      Fin.rev (⟨k + 1, hk⟩ : Fin n) := by
  haveI : NeZero n := ⟨by omega⟩
  have hne : Fin.rev (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin n) ≠
      (0 : Fin n) := rev_mk_ne_zero hk
  change (finRotate n).symm
      (Fin.rev (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin n)) = _
  rw [finRotate_symm_apply]
  apply Fin.ext
  rw [Fin.val_sub_one_of_ne_zero hne]
  simp only [Fin.val_rev]
  omega

/-- The cyclic predecessor of zero is the reverse of the zero index. -/
theorem prevFin_zero_eq_rev_zero {n : ℕ} (hn : 0 < n) :
    CactusShape.prevFin n (⟨0, hn⟩ : Fin n) =
      Fin.rev (⟨0, hn⟩ : Fin n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  apply (finRotate (m + 1)).injective
  change CactusShape.nextFin (m + 1)
      (CactusShape.prevFin (m + 1) ⟨0, Nat.zero_lt_succ m⟩) =
    CactusShape.nextFin (m + 1) (Fin.rev ⟨0, Nat.zero_lt_succ m⟩)
  rw [CactusShape.nextFin_prevFin]
  simp [CactusShape.nextFin]

/-- Backward outer darts follow the complementary face permutation. -/
theorem cactusOuterBackwardDarts_chain
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    Z.cactusOuterBackwardDarts.IsChain
      (fun d e : CactusDart Z.cactusShape ↦
        Z.cactusShape.toCombMap.facePerm d = e) := by
  rw [cactusOuterBackwardDarts, List.isChain_ofFn]
  intro k hk
  have hne : Fin.rev
      (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin Z.cactusShape.boundaryLength) ≠
      Z.cactusShape.boundaryZero := by
    change Fin.rev (⟨k, Nat.lt_of_succ_lt hk⟩ :
      Fin Z.cactusShape.boundaryLength) ≠
        (⟨0, Z.cactusShape.boundary_pos⟩ :
          Fin Z.cactusShape.boundaryLength)
    exact rev_mk_ne_zero hk
  rw [Z.cactusShape.facePerm_outerBackward_of_ne _ hne]
  exact congrArg
    (fun j ↦ CactusDart.outerBackward (S := Z.cactusShape) j)
    (prevFin_rev_succ hk)

/-- Backward darts around one relator polygon follow the complementary face
permutation. -/
theorem cactusRelatorBackwardDarts_chain
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (i : Fin Z.cells.length) :
    (Z.cactusRelatorBackwardDarts i).IsChain
      (fun d e : CactusDart Z.cactusShape ↦
        Z.cactusShape.toCombMap.facePerm d = e) := by
  rw [cactusRelatorBackwardDarts, List.isChain_ofFn]
  intro k hk
  have hne : Fin.rev (⟨k, Nat.lt_of_succ_lt hk⟩ :
      Fin (Z.cactusShape.relatorLength i)) ≠
      Z.cactusShape.relatorZero i := by
    change Fin.rev (⟨k, Nat.lt_of_succ_lt hk⟩ :
      Fin (Z.cactusShape.relatorLength i)) ≠
        (⟨0, Z.cactusShape.relator_pos i⟩ :
          Fin (Z.cactusShape.relatorLength i))
    exact rev_mk_ne_zero hk
  rw [Z.cactusShape.facePerm_relatorBackward_of_ne i _ hne]
  exact congrArg
    (fun j ↦ CactusDart.relatorBackward (S := Z.cactusShape) i j)
    (prevFin_rev_succ hk)

/-! ## Cell-block chains -/

/-- A backward relator-polygon list is nonempty. -/
theorem cactusRelatorBackwardDarts_ne_nil
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (i : Fin Z.cells.length) :
    Z.cactusRelatorBackwardDarts i ≠ [] := by
  change (List.ofFn (fun j : Fin (Z.cactusShape.relatorLength i) ↦
    CactusDart.relatorBackward (S := Z.cactusShape) i j.rev)) ≠ []
  intro hnil
  have hlength := congrArg List.length hnil
  simp only [List.length_ofFn, List.length_nil] at hlength
  exact (Nat.ne_of_gt (Z.cactusShape.relator_pos i)) hlength

/-- The first backward relator dart is the predecessor of its distinguished
dart. -/
theorem cactusRelatorBackwardDarts_head
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (i : Fin Z.cells.length)
    (h : Z.cactusRelatorBackwardDarts i ≠ []) :
    (Z.cactusRelatorBackwardDarts i).head h =
      CactusDart.relatorBackward i
        (CactusShape.prevFin (Z.cactusShape.relatorLength i)
          (Z.cactusShape.relatorZero i)) := by
  change (List.ofFn (fun j : Fin (Z.cactusShape.relatorLength i) ↦
    CactusDart.relatorBackward (S := Z.cactusShape) i j.rev)).head _ = _
  rw [List.head_ofFn]
  exact congrArg
    (fun j ↦ CactusDart.relatorBackward (S := Z.cactusShape) i j)
    (prevFin_zero_eq_rev_zero (Z.cactusShape.relator_pos i)).symm

/-- The final backward relator dart is its distinguished dart. -/
theorem cactusRelatorBackwardDarts_getLast
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (i : Fin Z.cells.length)
    (h : Z.cactusRelatorBackwardDarts i ≠ []) :
    (Z.cactusRelatorBackwardDarts i).getLast h =
      CactusDart.relatorBackward i (Z.cactusShape.relatorZero i) := by
  change (List.ofFn (fun j : Fin (Z.cactusShape.relatorLength i) ↦
    CactusDart.relatorBackward (S := Z.cactusShape) i j.rev)).getLast _ = _
  rw [List.getLast_ofFn]
  apply congrArg
    (fun j ↦ CactusDart.relatorBackward (S := Z.cactusShape) i j)
  apply Fin.ext
  simp only [Fin.val_rev, CactusShape.relatorZero, Fin.val_mk]
  omega

/-- One cell segment is nonempty because it begins with its outgoing stem. -/
theorem cactusCellSegment_ne_nil
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (i : Fin Z.cells.length) : Z.cactusCellSegment i ≠ [] := by
  simp [cactusCellSegment]

/-- A cell segment begins with its outgoing stem. -/
theorem cactusCellSegment_head
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (i : Fin Z.cells.length) (h : Z.cactusCellSegment i ≠ []) :
    (Z.cactusCellSegment i).head h = CactusDart.stemOut i := by
  rfl

/-- A cell segment ends with its incoming stem. -/
theorem cactusCellSegment_getLast
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (i : Fin Z.cells.length) (h : Z.cactusCellSegment i ≠ []) :
    (Z.cactusCellSegment i).getLast h = CactusDart.stemIn i := by
  change ((CactusDart.stemOut i ::
    Z.cactusRelatorBackwardDarts i) ++ [CactusDart.stemIn i]).getLast _ = _
  simp

/-- The outgoing stem, backward relator polygon, and incoming stem form one
face-permutation chain. -/
theorem cactusCellSegment_chain
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (i : Fin Z.cells.length) :
    (Z.cactusCellSegment i).IsChain
      (fun d e : CactusDart Z.cactusShape ↦
        Z.cactusShape.toCombMap.facePerm d = e) := by
  let rel := Z.cactusRelatorBackwardDarts i
  have hrel : rel ≠ [] := Z.cactusRelatorBackwardDarts_ne_nil i
  have hrelChain := Z.cactusRelatorBackwardDarts_chain i
  have htail : (rel ++ [CactusDart.stemIn i]).IsChain
      (fun d e : CactusDart Z.cactusShape ↦
        Z.cactusShape.toCombMap.facePerm d = e) := by
    apply hrelChain.append (List.IsChain.singleton _)
    intro x hx y hy
    rw [List.getLast?_eq_some_getLast hrel] at hx
    simp only [List.head?_singleton, Option.mem_some_iff] at hx hy
    subst x
    subst y
    rw [Z.cactusRelatorBackwardDarts_getLast i hrel]
    exact Z.cactusShape.facePerm_relatorBackward_zero i
  have hwhole : ([CactusDart.stemOut i] ++
      (rel ++ [CactusDart.stemIn i])).IsChain
      (fun d e : CactusDart Z.cactusShape ↦
        Z.cactusShape.toCombMap.facePerm d = e) := by
    apply (List.IsChain.singleton _).append htail
    intro x hx y hy
    simp only [List.getLast?_singleton, Option.mem_some_iff] at hx
    rw [List.head?_append_of_ne_nil rel hrel,
      List.head?_eq_some_head hrel] at hy
    simp only [Option.mem_some_iff] at hy
    subst x
    subst y
    rw [Z.cactusRelatorBackwardDarts_head i hrel]
    rfl
  simpa [rel, cactusCellSegment, List.append_assoc] using hwhole

/-- Below the wrap point, cyclic successor agrees with ordinary successor. -/
theorem nextFin_mk_succ {n k : ℕ} (hk : k + 1 < n) :
    CactusShape.nextFin n (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin n) =
      (⟨k + 1, hk⟩ : Fin n) := by
  apply Fin.ext
  simp [CactusShape.nextFin, finRotate_apply, Fin.add_def,
    Nat.mod_eq_of_lt hk]

/-- The flattened list of cell segments follows the complementary face
permutation. -/
theorem cactusCellSegments_chain
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    Z.cactusCellSegments.IsChain
      (fun d e : CactusDart Z.cactusShape ↦
        Z.cactusShape.toCombMap.facePerm d = e) := by
  rw [cactusCellSegments]
  apply (List.isChain_flatten (by
    rw [List.mem_ofFn]
    rintro ⟨i, hi⟩
    exact Z.cactusCellSegment_ne_nil i hi)).2
  constructor
  · intro l hl
    rw [List.mem_ofFn] at hl
    obtain ⟨i, rfl⟩ := hl
    exact Z.cactusCellSegment_chain i
  · rw [List.isChain_ofFn]
    intro k hk l₁ hl₁ l₂ hl₂
    let i : Fin Z.cells.length := ⟨k, Nat.lt_of_succ_lt hk⟩
    let j : Fin Z.cells.length := ⟨k + 1, hk⟩
    rw [List.getLast?_eq_some_getLast (Z.cactusCellSegment_ne_nil i)] at hl₁
    rw [List.head?_eq_some_head (Z.cactusCellSegment_ne_nil j)] at hl₂
    simp only [Option.mem_some_iff] at hl₁ hl₂
    subst l₁
    subst l₂
    rw [Z.cactusCellSegment_getLast i, Z.cactusCellSegment_head j]
    have hnext : CactusShape.nextFin Z.cells.length i = j :=
      nextFin_mk_succ hk
    have hne : CactusShape.nextFin Z.cells.length i ≠
        Z.cactusShape.cellZero (Nat.zero_lt_of_lt i.isLt) := by
      rw [hnext]
      intro hzero
      have hval := congrArg Fin.val hzero
      simp [j, CactusShape.cellZero] at hval
    rw [Z.cactusShape.facePerm_stemIn_of_ne i hne, hnext]

/-! ## The full complementary cycle -/

/-- The backward outer-polygon list is nonempty. -/
theorem cactusOuterBackwardDarts_ne_nil
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    Z.cactusOuterBackwardDarts ≠ [] := by
  change (List.ofFn (fun j : Fin Z.cactusShape.boundaryLength ↦
    CactusDart.outerBackward (S := Z.cactusShape) j.rev)) ≠ []
  intro hnil
  have hlength := congrArg List.length hnil
  simp only [List.length_ofFn, List.length_nil] at hlength
  exact (Nat.ne_of_gt Z.cactusShape.boundary_pos) hlength

/-- The backward outer-polygon list begins at the predecessor of zero. -/
theorem cactusOuterBackwardDarts_head
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (h : Z.cactusOuterBackwardDarts ≠ []) :
    Z.cactusOuterBackwardDarts.head h =
      CactusDart.outerBackward
        (CactusShape.prevFin Z.cactusShape.boundaryLength
          Z.cactusShape.boundaryZero) := by
  change (List.ofFn (fun j : Fin Z.cactusShape.boundaryLength ↦
    CactusDart.outerBackward (S := Z.cactusShape) j.rev)).head _ = _
  rw [List.head_ofFn]
  exact congrArg
    (fun j ↦ CactusDart.outerBackward (S := Z.cactusShape) j)
    (prevFin_zero_eq_rev_zero Z.cactusShape.boundary_pos).symm

/-- The backward outer-polygon list ends at zero. -/
theorem cactusOuterBackwardDarts_getLast
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (h : Z.cactusOuterBackwardDarts ≠ []) :
    Z.cactusOuterBackwardDarts.getLast h =
      CactusDart.outerBackward Z.cactusShape.boundaryZero := by
  change (List.ofFn (fun j : Fin Z.cactusShape.boundaryLength ↦
    CactusDart.outerBackward (S := Z.cactusShape) j.rev)).getLast _ = _
  rw [List.getLast_ofFn]
  apply congrArg
    (fun j ↦ CactusDart.outerBackward (S := Z.cactusShape) j)
  apply Fin.ext
  simp only [Fin.val_rev, CactusShape.boundaryZero, Fin.val_mk]
  omega

/-- The last ordinary finite index is the cyclic predecessor of zero. -/
theorem lastIndex_eq_prevFin_zero {n : ℕ} (hn : 0 < n) :
    (⟨n - 1, Nat.sub_one_lt (Nat.ne_of_gt hn)⟩ : Fin n) =
      CactusShape.prevFin n (⟨0, hn⟩ : Fin n) := by
  rw [prevFin_zero_eq_rev_zero hn]
  apply Fin.ext
  simp only [Fin.val_rev]

/-- The flattened cell-block list is nonempty. -/
theorem cactusCellSegments_ne_nil
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    Z.cactusCellSegments ≠ [] := by
  rw [cactusCellSegments, List.flatten_ne_nil_iff]
  let i := Z.cactusShape.cellZero Z.cells_length_pos
  exact ⟨Z.cactusCellSegment i, by
    constructor
    · rw [List.mem_ofFn]
      exact ⟨i, rfl⟩
    · exact Z.cactusCellSegment_ne_nil i⟩

/-- The flattened cell-block list begins with the first outgoing stem. -/
theorem cactusCellSegments_head
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (h : Z.cactusCellSegments ≠ []) :
    Z.cactusCellSegments.head h =
      CactusDart.stemOut
        (Z.cactusShape.cellZero Z.cells_length_pos) := by
  let blocks := List.ofFn fun i : Fin Z.cells.length ↦ Z.cactusCellSegment i
  have hblocks : blocks ≠ [] := by
    intro hnil
    have hlength := congrArg List.length hnil
    simp only [blocks, List.length_ofFn, List.length_nil] at hlength
    exact (Nat.ne_of_gt Z.cells_length_pos) hlength
  have hfirst : blocks.head hblocks ≠ [] := by
    simp only [blocks, List.head_ofFn]
    exact Z.cactusCellSegment_ne_nil
      (Z.cactusShape.cellZero Z.cells_length_pos)
  have hflatten : blocks.flatten ≠ [] := by
    change Z.cactusCellSegments ≠ []
    exact h
  change blocks.flatten.head hflatten = _
  rw [List.head_flatten_eq_head_head hflatten hfirst]
  simp only [blocks, List.head_ofFn]
  exact Z.cactusCellSegment_head
    (Z.cactusShape.cellZero Z.cells_length_pos) _

/-- The flattened cell-block list ends with the incoming stem of the cyclic
predecessor cell. -/
theorem cactusCellSegments_getLast
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (h : Z.cactusCellSegments ≠ []) :
    Z.cactusCellSegments.getLast h =
      CactusDart.stemIn
        (CactusShape.prevFin Z.cells.length
          (Z.cactusShape.cellZero Z.cells_length_pos)) := by
  let blocks := List.ofFn fun i : Fin Z.cells.length ↦ Z.cactusCellSegment i
  have hblocks : blocks ≠ [] := by
    intro hnil
    have hlength := congrArg List.length hnil
    simp only [blocks, List.length_ofFn, List.length_nil] at hlength
    exact (Nat.ne_of_gt Z.cells_length_pos) hlength
  have hlast : blocks.getLast hblocks ≠ [] := by
    simp only [blocks, List.getLast_ofFn]
    exact Z.cactusCellSegment_ne_nil _
  have hflatten : blocks.flatten ≠ [] := by
    change Z.cactusCellSegments ≠ []
    exact h
  change blocks.flatten.getLast hflatten = _
  rw [List.getLast_flatten_eq_getLast_getLast hflatten hlast]
  simp only [blocks, List.getLast_ofFn]
  rw [Z.cactusCellSegment_getLast]
  exact congrArg (fun i ↦ CactusDart.stemIn (S := Z.cactusShape) i)
    (lastIndex_eq_prevFin_zero Z.cells_length_pos)

/-- The full explicit complementary list follows the face permutation. -/
theorem cactusBigDarts_chain
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    Z.cactusBigDarts.IsChain
      (fun d e : CactusDart Z.cactusShape ↦
        Z.cactusShape.toCombMap.facePerm d = e) := by
  rw [cactusBigDarts]
  apply Z.cactusOuterBackwardDarts_chain.append Z.cactusCellSegments_chain
  intro x hx y hy
  rw [List.getLast?_eq_some_getLast Z.cactusOuterBackwardDarts_ne_nil] at hx
  rw [List.head?_eq_some_head Z.cactusCellSegments_ne_nil] at hy
  simp only [Option.mem_some_iff] at hx hy
  subst x
  subst y
  rw [Z.cactusOuterBackwardDarts_getLast,
    Z.cactusCellSegments_head]
  exact Z.cactusShape.facePerm_outerBackward_zero Z.cells_length_pos

/-- The full complementary list begins at the predecessor outer dart. -/
theorem cactusBigDarts_head
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (h : Z.cactusBigDarts ≠ []) :
    Z.cactusBigDarts.head h = CactusDart.outerBackward
      (CactusShape.prevFin Z.cactusShape.boundaryLength
        Z.cactusShape.boundaryZero) := by
  change (Z.cactusOuterBackwardDarts ++ Z.cactusCellSegments).head _ = _
  rw [List.head_append_of_ne_nil Z.cactusOuterBackwardDarts_ne_nil]
  exact Z.cactusOuterBackwardDarts_head _

/-- The full complementary list ends at the final incoming stem. -/
theorem cactusBigDarts_getLast
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (h : Z.cactusBigDarts ≠ []) :
    Z.cactusBigDarts.getLast h = CactusDart.stemIn
      (CactusShape.prevFin Z.cells.length
        (Z.cactusShape.cellZero Z.cells_length_pos)) := by
  change (Z.cactusOuterBackwardDarts ++ Z.cactusCellSegments).getLast _ = _
  rw [List.getLast_append_of_ne_nil _
    Z.cactusCellSegments_ne_nil]
  exact Z.cactusCellSegments_getLast _

/-- The incoming stem of the predecessor cell returns to the predecessor
outer dart. -/
theorem facePerm_stemIn_prev_zero (S : CactusShape)
    (hpos : 0 < S.cellCount) :
    S.toCombMap.facePerm
        (.stemIn (CactusShape.prevFin S.cellCount (S.cellZero hpos))) =
      .outerBackward
        (CactusShape.prevFin S.boundaryLength S.boundaryZero) := by
  change S.sigmaFun
      (.stemOut (CactusShape.prevFin S.cellCount (S.cellZero hpos))) = _
  have hnext : CactusShape.nextFin S.cellCount
      (CactusShape.prevFin S.cellCount (S.cellZero hpos)) = S.cellZero hpos :=
    CactusShape.nextFin_prevFin S.cellCount (S.cellZero hpos)
  have htest : CactusShape.nextFin S.cellCount
      (CactusShape.prevFin S.cellCount (S.cellZero hpos)) =
        S.cellZero (Nat.zero_lt_of_lt
          (CactusShape.prevFin S.cellCount (S.cellZero hpos)).isLt) := by
    rw [hnext]
  rw [CactusShape.sigmaFun, dif_pos htest]

/-- The full complementary list closes cyclically. -/
theorem cactusBigDarts_closes
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    Z.cactusShape.toCombMap.facePerm
        (Z.cactusBigDarts.getLast Z.cactusBigDarts_ne_nil) =
      Z.cactusBigDarts.head Z.cactusBigDarts_ne_nil := by
  rw [Z.cactusBigDarts_getLast, Z.cactusBigDarts_head]
  exact facePerm_stemIn_prev_zero Z.cactusShape Z.cells_length_pos

/-! ## The complementary face boundary -/

/-- The explicit complementary traversal, packaged as the based boundary of
the big cactus face. -/
noncomputable def cactusBigFaceBoundary
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    FaceBoundary Z.cactusShape.toCombMap Z.cactusShape.bigFace := by
  classical
  let l := Z.cactusBigDarts
  have hn : l.Nodup := Z.cactusBigDarts_nodup
  let e₁ : Fin l.length ≃ {x : CactusDart Z.cactusShape // x ∈ l} :=
    hn.getEquiv l
  have hpred : (fun x : CactusDart Z.cactusShape ↦ x ∈ l) =
      (fun x : CactusDart Z.cactusShape ↦
        Z.cactusShape.toCombMap.faceOf x = Z.cactusShape.bigFace) := by
    funext x
    apply propext
    exact Z.mem_cactusBigDarts_iff x
  let e₂ : {x : CactusDart Z.cactusShape // x ∈ l} ≃
      {x : CactusDart Z.cactusShape //
        Z.cactusShape.toCombMap.faceOf x = Z.cactusShape.bigFace} :=
    Equiv.subtypeEquivProp hpred
  exact
    { darts := l
      nonempty := Z.cactusBigDarts_ne_nil
      nodup := hn
      mem_iff := Z.mem_cactusBigDarts_iff
      chain := Z.cactusBigDarts_chain
      closes := Z.cactusBigDarts_closes
      length_eq_degree := by
        change l.length = Nat.card
          {x : CactusDart Z.cactusShape //
            Z.cactusShape.toCombMap.faceOf x = Z.cactusShape.bigFace}
        rw [← Nat.card_fin l.length]
        exact Nat.card_congr (e₁.trans e₂) }

/-- The chosen complementary face boundary is exactly the explicit dart
list. -/
theorem cactusBigFaceBoundary_darts
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    Z.cactusBigFaceBoundary.darts = Z.cactusBigDarts := rfl

end Lemma44OrientedRelatorDiagram
end HullSC
end GroupApproximation
