import GroupApproximation.GGT.VanKampen.CactusConstruction
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

end Lemma44OrientedRelatorDiagram
end HullSC
end GroupApproximation
