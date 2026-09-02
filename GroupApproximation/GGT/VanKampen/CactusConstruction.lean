import GroupApproximation.GGT.VanKampen.CactusFaceBoundary

/-!
# The labelled cactus realization

For an oriented least-area algebraic diagram, this file builds the explicit
polygon cactus introduced in `CactusMap`.  Least-area reducedness first rules
out an empty relator word in every cell, while the nonidentity exterior value
rules out an empty exterior word.  These facts give the positive polygon
lengths required by `CactusShape`.

The later sections label the two orientations of every polygon edge by
mutually inverse relative letters, label each stem by its algebraic
conjugator, identify the outer and relator face words, and verify that the
complementary face is a `G`-face.  The Euler computation from
`CactusTopology` then supplies planarity.
-/

namespace GroupApproximation
namespace HullSC

universe u w

namespace Lemma44OrientedRelatorDiagram

open GGT.VanKampen

/-- The cell occupying a finite position in the oriented algebraic list. -/
def cellAt
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (i : Fin Z.cells.length) : HullSC.Lemma44OrientedRelatorCell W :=
  Z.cells.get i

/-- Splitting the oriented cell list at an index isolates precisely that
cell. -/
theorem cells_eq_take_append_cellAt_drop
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (i : Fin Z.cells.length) :
    Z.cells = Z.cells.take i ++ Z.cellAt i :: Z.cells.drop (i + 1) := by
  calc
    Z.cells = Z.cells.take i ++ Z.cells.drop i :=
      (List.take_append_drop i Z.cells).symm
    _ = Z.cells.take i ++ Z.cellAt i :: Z.cells.drop (i + 1) := by
      rw [cellAt, List.cons_get_drop_succ]

/-- Least-area reducedness makes the complete value of every oriented cell
nonidentity. -/
theorem cellAt_value_ne_one
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (i : Fin Z.cells.length) : (Z.cellAt i).value ≠ 1 := by
  have hred := Z.reduced
    (Z.cells.take i |>.map HullSC.Lemma44OrientedRelatorCell.value)
    [(Z.cellAt i).value]
    (Z.cells.drop (i + 1) |>.map HullSC.Lemma44OrientedRelatorCell.value)
    (by
      have hmap := congrArg
        (List.map HullSC.Lemma44OrientedRelatorCell.value)
        (Z.cells_eq_take_append_cellAt_drop i)
      calc
        Z.factors = Z.cells.map HullSC.Lemma44OrientedRelatorCell.value :=
          Z.cell_values.symm
        _ = _ := by
          simpa only [List.map_append, List.map_cons,
            List.singleton_append, List.append_assoc] using hmap)
    (by simp)
  simpa using hred

/-- Every relator polygon has positive length.  An empty relator word has
identity value, so its conjugate would contradict reducedness of the
one-cell subproduct. -/
theorem cellAt_relator_ne_nil
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (i : Fin Z.cells.length) : (Z.cellAt i).relator ≠ [] := by
  intro hnil
  apply Z.cellAt_value_ne_one i
  rw [HullSC.Lemma44OrientedRelatorCell.value, hnil]
  simp [GGT.RelLetter.listVal_nil]

/-- The exterior polygon has positive length because its stored word spells
a nonidentity group element. -/
theorem boundaryWord_ne_nil
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    Z.boundaryWord ≠ [] := by
  intro hnil
  apply Z.boundary_ne_one
  rw [← Z.boundaryWord_isWord.prod_eq, hnil]
  rfl

/-- The positive polygon shape underlying the cactus realization. -/
def cactusShape
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) : CactusShape where
  boundaryLength := Z.boundaryWord.length
  boundary_pos := List.length_pos_iff.mpr Z.boundaryWord_ne_nil
  cellCount := Z.cells.length
  relatorLength i := (Z.cellAt i).relator.length
  relator_pos i := List.length_pos_iff.mpr (Z.cellAt_relator_ne_nil i)

@[simp] theorem cactusShape_boundaryLength
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    Z.cactusShape.boundaryLength = Z.boundaryWord.length := rfl

@[simp] theorem cactusShape_cellCount
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R) :
    Z.cactusShape.cellCount = Z.cells.length := rfl

@[simp] theorem cactusShape_relatorLength
    {G : Type u} [Group G] {Lambda : Type w}
    {A : Manuscript.NonMF.TorsionFree.Alphabet G}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : HullSC.Lemma44OrientedRelatorDiagram A W R)
    (i : Fin Z.cells.length) :
    Z.cactusShape.relatorLength i = (Z.cellAt i).relator.length := rfl

end Lemma44OrientedRelatorDiagram

end HullSC
end GroupApproximation
