import GroupApproximation.GGT.VanKampen.CactusBigBoundary
import GroupApproximation.GGT.HullSCRelativeGreendlingerStatement

/-!
# The shared cactus for relative reduced diagrams

This module isolates the part of the polygon-cactus construction which uses
only the fields common to `HullSC.RelativeReducedDiagram`: a nontrivial base
boundary word, an ordered list of oriented relator cells, its product formula,
nonempty relator words, and the ordered no-cancellation condition.  The map is
the same finite cactus as in `CactusRealization`; the complementary face is
spelled explicitly so its value is one.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullSC
open GroupApproximation.GGT.VanKampen

universe u w

namespace RelativeReducedDiagram

abbrev cactusShape
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R) : CactusShape where
  boundaryLength := Z.boundaryWord.length
  boundary_pos := by
    apply List.length_pos_iff.mpr
    intro hnil
    apply Z.boundary_ne_one
    rw [← Z.boundaryWord_isWord.prod_eq, hnil]
    rfl
  cellCount := Z.cells.length
  relatorLength i := (Z.cells.get i.rev).relator.length
  relator_pos i := by
    apply List.length_pos_iff.mpr
    exact Z.cell_relator_ne_nil i.rev

def cellAt
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R)
    (i : Fin Z.cells.length) : Lemma44OrientedRelatorCell W := Z.cells.get i

def geometricCell
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R)
    (i : Fin Z.cells.length) : Lemma44OrientedRelatorCell W := Z.cellAt i.rev

def outerFaceWord
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R) :
    List (GGT.RelLetter G Lambda) :=
  RelWord.revInv (Z.boundaryWord.map (GGT.RelLetter.base : G → GGT.RelLetter G Lambda))

def outerIndex
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R)
    (j : Fin Z.cactusShape.boundaryLength) :
    Fin Z.outerFaceWord.length := by
  rw [outerFaceWord, RelWord.length_revInv, List.length_map]
  exact j

def label
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R) :
    CactusDart Z.cactusShape → GGT.RelLetter G Lambda
  | .outerForward j => Z.outerFaceWord.get (Z.outerIndex j)
  | .outerBackward j => RelWord.inv (Z.outerFaceWord.get (Z.outerIndex j))
  | .relatorForward i j => (Z.geometricCell i).relator.get j
  | .relatorBackward i j => RelWord.inv ((Z.geometricCell i).relator.get j)
  | .stemOut i => .base (Z.geometricCell i).conjugator
  | .stemIn i => .base (Z.geometricCell i).conjugator⁻¹

theorem label_alpha
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R) (d : CactusDart Z.cactusShape) :
    Z.label (Z.cactusShape.alpha d) = RelWord.inv (Z.label d) := by
  cases d with
  | outerForward j => rfl
  | outerBackward j =>
      change Z.outerFaceWord.get (Z.outerIndex j) =
        RelWord.inv (RelWord.inv (Z.outerFaceWord.get (Z.outerIndex j)))
      exact (RelWord.inv_inv_letter _).symm
  | relatorForward i j => rfl
  | relatorBackward i j =>
      change (Z.geometricCell i).relator.get j =
        RelWord.inv (RelWord.inv ((Z.geometricCell i).relator.get j))
      exact (RelWord.inv_inv_letter _).symm
  | stemOut i => rfl
  | stemIn i =>
      change GGT.RelLetter.base (Z.geometricCell i).conjugator =
        RelWord.inv (GGT.RelLetter.base (Z.geometricCell i).conjugator⁻¹)
      rw [RelWord.inv, inv_inv]

theorem outerForward_word
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R) :
    List.ofFn (fun j : Fin Z.cactusShape.boundaryLength ↦
      Z.label (.outerForward j)) = Z.outerFaceWord := by
  unfold label
  apply List.ext_getElem
    (by rw [List.length_ofFn, outerFaceWord, RelWord.length_revInv,
      List.length_map])
  intro k hk₁ hk₂
  simp only [List.getElem_ofFn]
  rfl

theorem relatorForward_word
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R)
    (i : Fin Z.cells.length) :
    List.ofFn (fun j : Fin (Z.cactusShape.relatorLength i) ↦
      Z.label (.relatorForward i j)) = (Z.geometricCell i).relator := by
  exact List.ofFn_get (Z.geometricCell i).relator

def outerBackwardDarts
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R) :
    List (CactusDart Z.cactusShape) :=
  List.ofFn fun j : Fin Z.cactusShape.boundaryLength ↦
    CactusDart.outerBackward j.rev

def relatorBackwardDarts
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R)
    (i : Fin Z.cells.length) : List (CactusDart Z.cactusShape) :=
  List.ofFn fun j : Fin (Z.cactusShape.relatorLength i) ↦
    CactusDart.relatorBackward i j.rev

def cellSegment
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R)
    (i : Fin Z.cells.length) : List (CactusDart Z.cactusShape) :=
  CactusDart.stemOut i :: Z.relatorBackwardDarts i ++ [CactusDart.stemIn i]

def cellSegments
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R) :
    List (CactusDart Z.cactusShape) :=
  (List.ofFn fun i : Fin Z.cells.length ↦ Z.cellSegment i).flatten

def bigDarts
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R) :
    List (CactusDart Z.cactusShape) :=
  Z.outerBackwardDarts ++ Z.cellSegments

theorem outerBackward_word
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R) :
    Z.outerBackwardDarts.map Z.label = RelWord.revInv Z.outerFaceWord := by
  have hforward := outerForward_word Z
  calc
    Z.outerBackwardDarts.map Z.label =
        List.ofFn (fun j : Fin Z.cactusShape.boundaryLength ↦
          RelWord.inv (Z.label (.outerForward j.rev))) := by
      rw [outerBackwardDarts, ← List.ofFn_comp']
      rfl
    _ = (List.ofFn (fun j : Fin Z.cactusShape.boundaryLength ↦
          RelWord.inv (Z.label (.outerForward j)))).reverse := by
      exact HullSC.Lemma44OrientedRelatorDiagram.ofFn_comp_rev
        (fun j : Fin Z.cactusShape.boundaryLength ↦
          RelWord.inv (Z.label (.outerForward j)))
    _ = RelWord.revInv
        (List.ofFn (fun j : Fin Z.cactusShape.boundaryLength ↦
          Z.label (.outerForward j))) := by
      rw [RelWord.revInv]
      congr 1
      rw [List.map_ofFn]
      rfl
    _ = RelWord.revInv Z.outerFaceWord := congrArg RelWord.revInv hforward

theorem relatorBackward_word
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R)
    (i : Fin Z.cells.length) :
    (Z.relatorBackwardDarts i).map Z.label =
      RelWord.revInv (Z.geometricCell i).relator := by
  have hforward := relatorForward_word Z i
  calc
    (Z.relatorBackwardDarts i).map Z.label =
        List.ofFn (fun j : Fin (Z.cactusShape.relatorLength i) ↦
          RelWord.inv (Z.label (.relatorForward i j.rev))) := by
      rw [relatorBackwardDarts, ← List.ofFn_comp']
      rfl
    _ = (List.ofFn (fun j : Fin (Z.cactusShape.relatorLength i) ↦
          RelWord.inv (Z.label (.relatorForward i j)))).reverse := by
      exact HullSC.Lemma44OrientedRelatorDiagram.ofFn_comp_rev
        (fun j : Fin (Z.cactusShape.relatorLength i) ↦
          RelWord.inv (Z.label (.relatorForward i j)))
    _ = RelWord.revInv (Z.geometricCell i).relator := by
      rw [RelWord.revInv]
      congr 1
      rw [List.map_ofFn]
      rfl

theorem cellSegment_word
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R)
    (i : Fin Z.cells.length) :
    (Z.cellSegment i).map Z.label =
      [.base (Z.geometricCell i).conjugator] ++
        RelWord.revInv (Z.geometricCell i).relator ++
      [.base (Z.geometricCell i).conjugator⁻¹] := by
  unfold cellSegment
  simp only [List.map_cons, List.map_append, label]
  rw [Z.relatorBackward_word i]
  simp only [List.map_nil, List.singleton_append]

theorem cellSegment_value
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R)
    (i : Fin Z.cells.length) :
    GGT.RelLetter.listVal ((Z.cellSegment i).map Z.label) =
      (Z.geometricCell i).value⁻¹ := by
  simp only [Z.cellSegment_word i, RelWord.listVal_append,
    RelWord.listVal_singleton, RelWord.listVal_revInv,
    HullSC.val_base, HullSC.Lemma44OrientedRelatorCell.value]
  group

theorem geometricCellValues_inv_prod
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R) :
    (List.ofFn fun i : Fin Z.cells.length ↦
      (Z.geometricCell i).value⁻¹).prod =
        (Z.cells.map Lemma44OrientedRelatorCell.value).prod⁻¹ := by
  have hcells : List.ofFn (fun i : Fin Z.cells.length ↦
      (Z.cellAt i).value⁻¹) =
      (Z.cells.map Lemma44OrientedRelatorCell.value).map fun x ↦ x⁻¹ := by
    calc
      List.ofFn (fun i : Fin Z.cells.length ↦ (Z.cellAt i).value⁻¹) =
          (List.ofFn Z.cells.get).map
            (fun C : Lemma44OrientedRelatorCell W ↦ C.value⁻¹) := by
        rw [← List.ofFn_comp']
        rfl
      _ = (Z.cells.map Lemma44OrientedRelatorCell.value).map
          fun x ↦ x⁻¹ := by
        rw [List.ofFn_get, List.map_map]
        rfl
  calc
    (List.ofFn fun i : Fin Z.cells.length ↦
        (Z.geometricCell i).value⁻¹).prod =
        (List.ofFn fun i : Fin Z.cells.length ↦
          (Z.cellAt i).value⁻¹).reverse.prod := by
      exact congrArg List.prod
        (HullSC.Lemma44OrientedRelatorDiagram.ofFn_comp_rev
          (fun i : Fin Z.cells.length ↦ (Z.cellAt i).value⁻¹))
    _ = ((Z.cells.map Lemma44OrientedRelatorCell.value).map
          fun x ↦ x⁻¹).reverse.prod := by rw [hcells]
    _ = (Z.cells.map Lemma44OrientedRelatorCell.value).prod⁻¹ :=
      (List.prod_inv_reverse _).symm

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

theorem cellSegments_value
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R) :
    GGT.RelLetter.listVal (Z.cellSegments.map Z.label) = Z.boundary⁻¹ := by
  rw [cellSegments, List.map_flatten, listVal_flatten, ← List.ofFn_comp']
  have hvalues : List.ofFn (fun i : Fin Z.cells.length ↦
      GGT.RelLetter.listVal ((Z.cellSegment i).map Z.label)) =
      List.ofFn (fun i : Fin Z.cells.length ↦ (Z.geometricCell i).value⁻¹) := by
    apply congrArg List.ofFn
    funext i
    exact Z.cellSegment_value i
  rw [← List.ofFn_comp', hvalues, Z.geometricCellValues_inv_prod,
    Z.cell_values_prod]

theorem bigDarts_value
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R) :
    GGT.RelLetter.listVal (Z.bigDarts.map Z.label) = 1 := by
  rw [bigDarts, List.map_append, RelWord.listVal_append,
    Z.outerBackward_word, Z.cellSegments_value,
    outerFaceWord, RelWord.revInv_revInv, HullSC.listVal_map_base,
    Z.boundaryWord_isWord.prod_eq, mul_inv_cancel]

end RelativeReducedDiagram
end HullSC
end GroupApproximation
