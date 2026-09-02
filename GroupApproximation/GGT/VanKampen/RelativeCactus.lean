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
open GroupApproximation.HullSC.Lemma44OrientedRelatorDiagram

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
    Fin Z.outerFaceWord.length :=
  ⟨j.1, by
    rw [outerFaceWord, RelWord.length_revInv, List.length_map]
    exact j.2⟩

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
  congr 1

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
      rw [← hforward]
      apply congrArg List.reverse
      simpa only [Function.comp_def] using
        (List.map_ofFn (f := fun j : Fin (Z.cactusShape.relatorLength i) ↦
          Z.label (.relatorForward i j)) (g := RelWord.inv)).symm

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

theorem cells_length_pos
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R) :
    0 < Z.cells.length := by
  rw [Z.cells_length]
  exact Z.area_pos

theorem outerBackwardDarts_nodup
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R) :
    Z.outerBackwardDarts.Nodup := by
  rw [outerBackwardDarts]
  apply List.nodup_ofFn_ofInjective
  intro i j hij
  apply Fin.rev_injective
  exact CactusDart.outerBackward.inj hij

theorem relatorBackwardDarts_nodup
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R)
    (i : Fin Z.cells.length) :
    (Z.relatorBackwardDarts i).Nodup := by
  rw [relatorBackwardDarts]
  apply List.nodup_ofFn_ofInjective
  intro j k hjk
  apply Fin.rev_injective
  exact eq_of_heq (CactusDart.relatorBackward.inj hjk).2

theorem cellSegment_nodup
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R)
    (i : Fin Z.cells.length) : (Z.cellSegment i).Nodup := by
  have hout : CactusDart.stemOut i ∉
      Z.relatorBackwardDarts i ++ [CactusDart.stemIn i] := by
    simp [relatorBackwardDarts, List.mem_ofFn]
  have hin : CactusDart.stemIn i ∉ Z.relatorBackwardDarts i := by
    simp [relatorBackwardDarts, List.mem_ofFn]
  unfold cellSegment
  exact List.Nodup.cons hout
    ((Z.relatorBackwardDarts_nodup i).append (by simp)
      (by simpa [List.disjoint_left] using hin))

theorem eq_of_mem_cellSegment
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R)
    {i j : Fin Z.cells.length} {d : CactusDart Z.cactusShape}
    (hi : d ∈ Z.cellSegment i) (hj : d ∈ Z.cellSegment j) : i = j := by
  cases d <;>
    simp_all [cellSegment, relatorBackwardDarts, List.mem_ofFn]

theorem cellSegment_disjoint
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R)
    {i j : Fin Z.cells.length} (hij : i ≠ j) :
    List.Disjoint (Z.cellSegment i) (Z.cellSegment j) := by
  rw [List.disjoint_left]
  intro d hi hj
  exact hij (Z.eq_of_mem_cellSegment hi hj)

theorem cellSegments_nodup
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R) :
    Z.cellSegments.Nodup := by
  rw [cellSegments, List.nodup_flatten]
  constructor
  · intro l hl
    rw [List.mem_ofFn] at hl
    obtain ⟨i, rfl⟩ := hl
    exact Z.cellSegment_nodup i
  · rw [List.pairwise_ofFn]
    intro i j hij
    exact Z.cellSegment_disjoint hij.ne

theorem outerBackwardDarts_disjoint_cellSegment
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R)
    (i : Fin Z.cells.length) :
    List.Disjoint Z.outerBackwardDarts (Z.cellSegment i) := by
  rw [List.disjoint_left]
  intro d hdouter hdcell
  rw [outerBackwardDarts, List.mem_ofFn] at hdouter
  obtain ⟨j, rfl⟩ := hdouter
  simp [cellSegment, relatorBackwardDarts, List.mem_ofFn] at hdcell

theorem outerBackwardDarts_disjoint_cellSegments
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R) :
    List.Disjoint Z.outerBackwardDarts Z.cellSegments := by
  rw [List.disjoint_left]
  intro d hdouter hdsegments
  rw [cellSegments, List.mem_flatten] at hdsegments
  obtain ⟨l, hl, hdl⟩ := hdsegments
  rw [List.mem_ofFn] at hl
  obtain ⟨i, rfl⟩ := hl
  exact (List.disjoint_left.mp
    (Z.outerBackwardDarts_disjoint_cellSegment i)) hdouter hdl

theorem bigDarts_nodup
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R) : Z.bigDarts.Nodup := by
  rw [bigDarts]
  exact Z.outerBackwardDarts_nodup.append Z.cellSegments_nodup
    Z.outerBackwardDarts_disjoint_cellSegments

theorem outerBackwardDarts_chain
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R) :
    Z.outerBackwardDarts.IsChain
      (fun d e : CactusDart Z.cactusShape ↦
        Z.cactusShape.toCombMap.facePerm d = e) := by
  rw [outerBackwardDarts, List.isChain_ofFn]
  intro k hk
  have hne : Fin.rev
      (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin Z.cactusShape.boundaryLength) ≠
        Z.cactusShape.boundaryZero := by
    change Fin.rev (⟨k, Nat.lt_of_succ_lt hk⟩ :
      Fin Z.cactusShape.boundaryLength) ≠
        (⟨0, Z.cactusShape.boundary_pos⟩ : Fin Z.cactusShape.boundaryLength)
    exact rev_mk_ne_zero hk
  rw [Z.cactusShape.facePerm_outerBackward_of_ne _ hne]
  exact congrArg (fun j ↦ CactusDart.outerBackward (S := Z.cactusShape) j)
    (prevFin_rev_succ hk)

theorem relatorBackwardDarts_chain
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R)
    (i : Fin Z.cells.length) :
    (Z.relatorBackwardDarts i).IsChain
      (fun d e : CactusDart Z.cactusShape ↦
        Z.cactusShape.toCombMap.facePerm d = e) := by
  rw [relatorBackwardDarts, List.isChain_ofFn]
  intro k hk
  have hne : Fin.rev
      (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin (Z.cactusShape.relatorLength i)) ≠
        Z.cactusShape.relatorZero i := by
    change Fin.rev (⟨k, Nat.lt_of_succ_lt hk⟩ :
      Fin (Z.cactusShape.relatorLength i)) ≠
        (⟨0, Z.cactusShape.relator_pos i⟩ :
          Fin (Z.cactusShape.relatorLength i))
    exact rev_mk_ne_zero hk
  rw [Z.cactusShape.facePerm_relatorBackward_of_ne i _ hne]
  exact congrArg (fun j ↦ CactusDart.relatorBackward
      (S := Z.cactusShape) i j) (prevFin_rev_succ hk)

theorem relatorBackwardDarts_ne_nil
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R)
    (i : Fin Z.cells.length) : Z.relatorBackwardDarts i ≠ [] := by
  rw [relatorBackwardDarts]
  intro hnil
  have hlength := congrArg List.length hnil
  simp only [List.length_ofFn, List.length_nil] at hlength
  exact (Nat.ne_of_gt (Z.cactusShape.relator_pos i)) hlength

theorem relatorBackwardDarts_head
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R)
    (i : Fin Z.cells.length) (h : Z.relatorBackwardDarts i ≠ []) :
    (Z.relatorBackwardDarts i).head h =
      CactusDart.relatorBackward i
        (CactusShape.prevFin (Z.cactusShape.relatorLength i)
          (Z.cactusShape.relatorZero i)) := by
  change (List.ofFn (fun j : Fin (Z.cactusShape.relatorLength i) ↦
    CactusDart.relatorBackward (S := Z.cactusShape) i j.rev)).head _ = _
  rw [List.head_ofFn]
  exact congrArg (fun j ↦ CactusDart.relatorBackward
      (S := Z.cactusShape) i j)
    (prevFin_zero_eq_rev_zero (Z.cactusShape.relator_pos i)).symm

theorem relatorBackwardDarts_getLast
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R)
    (i : Fin Z.cells.length) (h : Z.relatorBackwardDarts i ≠ []) :
    (Z.relatorBackwardDarts i).getLast h =
      CactusDart.relatorBackward i (Z.cactusShape.relatorZero i) := by
  change (List.ofFn (fun j : Fin (Z.cactusShape.relatorLength i) ↦
    CactusDart.relatorBackward (S := Z.cactusShape) i j.rev)).getLast _ = _
  rw [List.getLast_ofFn]
  apply congrArg (fun j ↦ CactusDart.relatorBackward
    (S := Z.cactusShape) i j)
  apply Fin.ext
  simp only [Fin.val_rev, CactusShape.relatorZero, Fin.val_mk]
  omega

theorem cellSegment_ne_nil
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R)
    (i : Fin Z.cells.length) : Z.cellSegment i ≠ [] := by
  simp [cellSegment]

theorem cellSegment_head
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R)
    (i : Fin Z.cells.length) (h : Z.cellSegment i ≠ []) :
    (Z.cellSegment i).head h = CactusDart.stemOut i := by
  rfl

theorem cellSegment_getLast
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R)
    (i : Fin Z.cells.length) (h : Z.cellSegment i ≠ []) :
    (Z.cellSegment i).getLast h = CactusDart.stemIn i := by
  change ((CactusDart.stemOut i :: Z.relatorBackwardDarts i) ++
    [CactusDart.stemIn i]).getLast _ = _
  simp

theorem cellSegment_chain
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R)
    (i : Fin Z.cells.length) :
    (Z.cellSegment i).IsChain
      (fun d e : CactusDart Z.cactusShape ↦
        Z.cactusShape.toCombMap.facePerm d = e) := by
  let rel := Z.relatorBackwardDarts i
  have hrel : rel ≠ [] := Z.relatorBackwardDarts_ne_nil i
  have hrelChain := Z.relatorBackwardDarts_chain i
  have htail : (rel ++ [CactusDart.stemIn i]).IsChain
      (fun d e : CactusDart Z.cactusShape ↦
        Z.cactusShape.toCombMap.facePerm d = e) := by
    apply hrelChain.append (List.IsChain.singleton _)
    intro x hx y hy
    rw [List.getLast?_eq_some_getLast hrel] at hx
    simp only [List.head?_singleton, Option.mem_some_iff] at hx hy
    subst x
    subst y
    rw [Z.relatorBackwardDarts_getLast i hrel]
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
    rw [Z.relatorBackwardDarts_head i hrel]
    rfl
  simpa [rel, cellSegment, List.append_assoc] using hwhole

theorem nextFin_mk_succ {n k : ℕ} (hk : k + 1 < n) :
    CactusShape.nextFin n (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin n) =
      (⟨k + 1, hk⟩ : Fin n) := by
  apply Fin.ext
  simp [CactusShape.nextFin, finRotate_apply, Fin.add_def,
    Nat.mod_eq_of_lt hk]

theorem cellSegments_chain
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R) :
    Z.cellSegments.IsChain
      (fun d e : CactusDart Z.cactusShape ↦
        Z.cactusShape.toCombMap.facePerm d = e) := by
  rw [cellSegments]
  apply (List.isChain_flatten (by
    rw [List.mem_ofFn]
    rintro ⟨i, hi⟩
    exact Z.cellSegment_ne_nil i hi)).2
  constructor
  · intro l hl
    rw [List.mem_ofFn] at hl
    obtain ⟨i, rfl⟩ := hl
    exact Z.cellSegment_chain i
  · rw [List.isChain_ofFn]
    intro k hk l₁ hl₁ l₂ hl₂
    let i : Fin Z.cells.length := ⟨k, Nat.lt_of_succ_lt hk⟩
    let j : Fin Z.cells.length := ⟨k + 1, hk⟩
    rw [List.getLast?_eq_some_getLast (Z.cellSegment_ne_nil i)] at hl₁
    rw [List.head?_eq_some_head (Z.cellSegment_ne_nil j)] at hl₂
    simp only [Option.mem_some_iff] at hl₁ hl₂
    subst l₁
    subst l₂
    rw [Z.cellSegment_getLast i, Z.cellSegment_head j]
    have hnext : CactusShape.nextFin Z.cells.length i = j :=
      nextFin_mk_succ hk
    have hne : CactusShape.nextFin Z.cells.length i ≠
        Z.cactusShape.cellZero (Nat.zero_lt_of_lt i.isLt) := by
      rw [hnext]
      intro hzero
      have hval := congrArg Fin.val hzero
      simp [j, CactusShape.cellZero] at hval
    rw [Z.cactusShape.facePerm_stemIn_of_ne i hne, hnext]

theorem outerBackwardDarts_ne_nil
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R) :
    Z.outerBackwardDarts ≠ [] := by
  rw [outerBackwardDarts]
  intro hnil
  have hlength := congrArg List.length hnil
  simp only [List.length_ofFn, List.length_nil] at hlength
  exact (Nat.ne_of_gt Z.cactusShape.boundary_pos) hlength

theorem outerBackwardDarts_head
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R)
    (h : Z.outerBackwardDarts ≠ []) :
    Z.outerBackwardDarts.head h = CactusDart.outerBackward
      (CactusShape.prevFin Z.cactusShape.boundaryLength
        Z.cactusShape.boundaryZero) := by
  change (List.ofFn (fun j : Fin Z.cactusShape.boundaryLength ↦
    CactusDart.outerBackward (S := Z.cactusShape) j.rev)).head _ = _
  rw [List.head_ofFn]
  exact congrArg (fun j ↦ CactusDart.outerBackward (S := Z.cactusShape) j)
    (prevFin_zero_eq_rev_zero Z.cactusShape.boundary_pos).symm

theorem outerBackwardDarts_getLast
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R)
    (h : Z.outerBackwardDarts ≠ []) :
    Z.outerBackwardDarts.getLast h =
      CactusDart.outerBackward Z.cactusShape.boundaryZero := by
  change (List.ofFn (fun j : Fin Z.cactusShape.boundaryLength ↦
    CactusDart.outerBackward (S := Z.cactusShape) j.rev)).getLast _ = _
  rw [List.getLast_ofFn]
  apply congrArg (fun j ↦ CactusDart.outerBackward (S := Z.cactusShape) j)
  apply Fin.ext
  simp only [Fin.val_rev, CactusShape.boundaryZero, Fin.val_mk]
  omega

theorem cellSegments_ne_nil
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R) : Z.cellSegments ≠ [] := by
  rw [cellSegments, List.flatten_ne_nil_iff]
  let i := Z.cactusShape.cellZero Z.cells_length_pos
  exact ⟨Z.cellSegment i, by
    constructor
    · rw [List.mem_ofFn]
      exact ⟨i, rfl⟩
    · exact Z.cellSegment_ne_nil i⟩

theorem cellSegments_head
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R)
    (h : Z.cellSegments ≠ []) :
    Z.cellSegments.head h =
      CactusDart.stemOut
        (Z.cactusShape.cellZero Z.cells_length_pos) := by
  let blocks := List.ofFn fun i : Fin Z.cells.length ↦ Z.cellSegment i
  have hblocks : blocks ≠ [] := by
    intro hnil
    have hlength := congrArg List.length hnil
    simp only [blocks, List.length_ofFn, List.length_nil] at hlength
    exact (Nat.ne_of_gt Z.cells_length_pos) hlength
  have hfirst : blocks.head hblocks ≠ [] := by
    simp only [blocks, List.head_ofFn]
    exact Z.cellSegment_ne_nil
      (Z.cactusShape.cellZero Z.cells_length_pos)
  have hflatten : blocks.flatten ≠ [] := by
    change Z.cellSegments ≠ []
    exact h
  change blocks.flatten.head hflatten = _
  rw [List.head_flatten_eq_head_head hflatten hfirst]
  simp only [blocks, List.head_ofFn]
  exact Z.cellSegment_head
    (Z.cactusShape.cellZero Z.cells_length_pos) _

theorem lastIndex_eq_prevFin_zero {n : ℕ} (hn : 0 < n) :
    (⟨n - 1, Nat.sub_one_lt (Nat.ne_of_gt hn)⟩ : Fin n) =
      CactusShape.prevFin n (⟨0, hn⟩ : Fin n) := by
  rw [prevFin_zero_eq_rev_zero hn]
  apply Fin.ext
  simp only [Fin.val_rev]

theorem cellSegments_getLast
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R)
    (h : Z.cellSegments ≠ []) :
    Z.cellSegments.getLast h =
      CactusDart.stemIn
        (CactusShape.prevFin Z.cells.length
          (Z.cactusShape.cellZero Z.cells_length_pos)) := by
  let blocks := List.ofFn fun i : Fin Z.cells.length ↦ Z.cellSegment i
  have hblocks : blocks ≠ [] := by
    intro hnil
    have hlength := congrArg List.length hnil
    simp only [blocks, List.length_ofFn, List.length_nil] at hlength
    exact (Nat.ne_of_gt Z.cells_length_pos) hlength
  have hlast : blocks.getLast hblocks ≠ [] := by
    simp only [blocks, List.getLast_ofFn]
    exact Z.cellSegment_ne_nil _
  have hflatten : blocks.flatten ≠ [] := by
    change Z.cellSegments ≠ []
    exact h
  change blocks.flatten.getLast hflatten = _
  rw [List.getLast_flatten_eq_getLast_getLast hflatten hlast]
  simp only [blocks, List.getLast_ofFn]
  rw [Z.cellSegment_getLast]
  exact congrArg (fun i ↦ CactusDart.stemIn (S := Z.cactusShape) i)
    (lastIndex_eq_prevFin_zero Z.cells_length_pos)

theorem faceOf_eq_bigFace_iff (S : CactusShape) (d : CactusDart S) :
    S.toCombMap.faceOf d = S.bigFace ↔ S.faceClass d = .big :=
  HullSC.Lemma44OrientedRelatorDiagram.faceOf_eq_bigFace_iff S d

theorem mem_bigDarts_iff
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R)
    (d : CactusDart Z.cactusShape) :
    d ∈ Z.bigDarts ↔ Z.cactusShape.toCombMap.faceOf d =
      Z.cactusShape.bigFace := by
  rw [faceOf_eq_bigFace_iff]
  cases d with
  | outerForward j => simp [bigDarts, outerBackwardDarts, cellSegments,
      cellSegment, relatorBackwardDarts, List.mem_flatten, List.mem_ofFn,
      CactusShape.faceClass]
  | outerBackward j =>
      constructor
      · intro _
        rfl
      · intro _
        rw [bigDarts, List.mem_append]
        left
        rw [outerBackwardDarts, List.mem_ofFn]
        exact ⟨j.rev, by simp⟩
  | relatorForward i j => simp [bigDarts, outerBackwardDarts, cellSegments,
      cellSegment, relatorBackwardDarts, List.mem_flatten, List.mem_ofFn,
      CactusShape.faceClass]
  | relatorBackward i j =>
      constructor
      · intro _
        rfl
      · intro _
        rw [bigDarts, List.mem_append]
        right
        rw [cellSegments, List.mem_flatten]
        refine ⟨Z.cellSegment i, ?_, ?_⟩
        · rw [List.mem_ofFn]
          exact ⟨i, rfl⟩
        · rw [cellSegment, List.mem_append]
          right
          rw [relatorBackwardDarts, List.mem_ofFn]
          exact ⟨j.rev, by simp⟩
  | stemOut i =>
      constructor
      · intro _
        rfl
      · intro _
        rw [bigDarts, List.mem_append]
        right
        rw [cellSegments, List.mem_flatten]
        refine ⟨Z.cellSegment i, ?_, ?_⟩
        · rw [List.mem_ofFn]
          exact ⟨i, rfl⟩
        · simp [cellSegment]
  | stemIn i =>
      constructor
      · intro _
        rfl
      · intro _
        rw [bigDarts, List.mem_append]
        right
        rw [cellSegments, List.mem_flatten]
        refine ⟨Z.cellSegment i, ?_, ?_⟩
        · rw [List.mem_ofFn]
          exact ⟨i, rfl⟩
        · simp [cellSegment]

theorem bigDarts_ne_nil
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R) : Z.bigDarts ≠ [] := by
  rw [bigDarts]
  intro h
  exact Z.outerBackwardDarts_ne_nil
    (List.eq_nil_of_append_eq_nil h).1

theorem facePerm_stemIn_prev_zero (S : CactusShape) (hpos : 0 < S.cellCount) :
    S.toCombMap.facePerm
        (.stemIn (CactusShape.prevFin S.cellCount (S.cellZero hpos))) =
      .outerBackward (CactusShape.prevFin S.boundaryLength S.boundaryZero) :=
  HullSC.Lemma44OrientedRelatorDiagram.facePerm_stemIn_prev_zero S hpos

theorem bigDarts_chain
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R) :
    Z.bigDarts.IsChain
      (fun d e : CactusDart Z.cactusShape ↦
        Z.cactusShape.toCombMap.facePerm d = e) := by
  rw [bigDarts]
  apply Z.outerBackwardDarts_chain.append Z.cellSegments_chain
  intro x hx y hy
  rw [List.getLast?_eq_some_getLast Z.outerBackwardDarts_ne_nil] at hx
  rw [List.head?_eq_some_head Z.cellSegments_ne_nil] at hy
  simp only [Option.mem_some_iff] at hx hy
  subst x
  subst y
  rw [Z.outerBackwardDarts_getLast, Z.cellSegments_head]
  exact Z.cactusShape.facePerm_outerBackward_zero Z.cells_length_pos

theorem bigDarts_head
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R)
    (h : Z.bigDarts ≠ []) :
    Z.bigDarts.head h = CactusDart.outerBackward
      (CactusShape.prevFin Z.cactusShape.boundaryLength
        Z.cactusShape.boundaryZero) := by
  change (Z.outerBackwardDarts ++ Z.cellSegments).head _ = _
  rw [List.head_append_of_ne_nil Z.outerBackwardDarts_ne_nil]
  exact Z.outerBackwardDarts_head _

theorem bigDarts_getLast
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R)
    (h : Z.bigDarts ≠ []) :
    Z.bigDarts.getLast h = CactusDart.stemIn
      (CactusShape.prevFin Z.cells.length
        (Z.cactusShape.cellZero Z.cells_length_pos)) := by
  change (Z.outerBackwardDarts ++ Z.cellSegments).getLast _ = _
  rw [List.getLast_append_of_ne_nil _ Z.cellSegments_ne_nil]
  exact Z.cellSegments_getLast _

theorem bigDarts_closes
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R) :
    Z.cactusShape.toCombMap.facePerm
        (Z.bigDarts.getLast Z.bigDarts_ne_nil) =
      Z.bigDarts.head Z.bigDarts_ne_nil := by
  rw [Z.bigDarts_getLast, Z.bigDarts_head]
  exact facePerm_stemIn_prev_zero Z.cactusShape Z.cells_length_pos

noncomputable def bigFaceBoundary
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R) :
    FaceBoundary Z.cactusShape.toCombMap Z.cactusShape.bigFace := by
  classical
  let l := Z.bigDarts
  have hn : l.Nodup := Z.bigDarts_nodup
  let e₁ : Fin l.length ≃ {x : CactusDart Z.cactusShape // x ∈ l} :=
    hn.getEquiv l
  have hpred : (fun x : CactusDart Z.cactusShape ↦ x ∈ l) =
      (fun x : CactusDart Z.cactusShape ↦
        Z.cactusShape.toCombMap.faceOf x = Z.cactusShape.bigFace) := by
    funext x
    apply propext
    exact Z.mem_bigDarts_iff x
  let e₂ : {x : CactusDart Z.cactusShape // x ∈ l} ≃
      {x : CactusDart Z.cactusShape //
        Z.cactusShape.toCombMap.faceOf x = Z.cactusShape.bigFace} :=
    Equiv.subtypeEquivProp hpred
  exact
    { darts := l
      nonempty := Z.bigDarts_ne_nil
      nodup := hn
      mem_iff := Z.mem_bigDarts_iff
      chain := Z.bigDarts_chain
      closes := Z.bigDarts_closes
      length_eq_degree := by
        change l.length = Nat.card
          {x : CactusDart Z.cactusShape //
            Z.cactusShape.toCombMap.faceOf x = Z.cactusShape.bigFace}
        rw [← Nat.card_fin l.length]
        exact Nat.card_congr (e₁.trans e₂) }

theorem bigFaceBoundary_darts
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.RelativeReducedDiagram D W R) :
    Z.bigFaceBoundary.darts = Z.bigDarts := rfl

end RelativeReducedDiagram
end HullSC
end GroupApproximation
