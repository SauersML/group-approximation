import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.LakesSurgery
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.LakeDef
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06, case (d): the predicates of the case split

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), in the lake-filling form of
`Piece06/LakesSurgery`.  Let `K` be a cell pocket face set between `Π_i ≠ Π_j` and `E₀` the piece
of the exterior face in the complement of `K.faces` (`ExteriorComponent.component`).

* `AllCellsEnclosed K`: no relator cell lies in `E₀` (Osin's case (d), "every relator cell in `F'`").
* `P06LakeCell.lakeOf K k` (landed, lane gl-p06-10, `P06LakeCell/LakeDef`): the piece of the face
  of `Π_k` in the complement of `K.faces` (the lake holding `Π_k` when `Π_k ∉ E₀`).
* `SecondLakeCell K`: the lake of `Π_i` holds a relator cell other than `Π_i`, or the lake of `Π_j`
  holds a relator cell other than `Π_j`.
* `LakeGOnly K k`: every relator cell in the lake of `Π_k` is `Π_k` itself.

`cases_core` is the case split used by the assembly: either some relator cell lies in `E₀`, or all
are enclosed and some lake of `Π_i`, `Π_j` holds a second relator cell, or all are enclosed and both
lakes are `G`-only.  It is pure classical logic, proved here.

`AllCellsEnclosed K` unfolds to the hypothesis `hall` of lane gl-p06-09
(`P06LakeCell.cells_mem_absorbed_of_all`, `P06LakeCell/Structure`).  The other predicates are local
forms of the interfaces of lanes gl-p06-11 and gl-p06-12 (not on disk).  They sit in the
sub-namespace `P06LakeCell.Assembly` so they cannot clash with those lanes' declarations.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.Assembly

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated

section Predicates

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **Case (d)**: no relator cell lies in the piece of the exterior face in the complement of
`K.faces`. -/
def AllCellsEnclosed (K : CellPocketFaceSet D eps X i j) : Prop :=
  ∀ C ∈ X.relatorCells, C.face ∉ ExteriorComponent.component X.toCombMap K.faces X.outerFace

/-- **A second relator cell in a lake**: the lake of `Π_i` holds a relator cell other than `Π_i`,
or the lake of `Π_j` holds a relator cell other than `Π_j`. -/
def SecondLakeCell (K : CellPocketFaceSet D eps X i j) : Prop :=
  ∃ C ∈ X.relatorCells,
    (C.face ∈ lakeOf K i ∧ C.face ≠ (cell X i).face) ∨
      (C.face ∈ lakeOf K j ∧ C.face ≠ (cell X j).face)

/-- **A `G`-only lake**: every relator cell in the lake of `Π_k` is `Π_k` itself. -/
def LakeGOnly (K : CellPocketFaceSet D eps X i j) (k : Fin X.rCellCount) : Prop :=
  ∀ C ∈ X.relatorCells, C.face ∈ lakeOf K k → C.face = (cell X k).face

/-- **The case split of the lakes surgery**: a relator cell in the exterior piece, or all relator
cells enclosed with a second relator cell in a lake, or all relator cells enclosed with both lakes
`G`-only. -/
theorem cases_core (K : CellPocketFaceSet D eps X i j) {P : Prop}
    (hout : ¬ AllCellsEnclosed K → P)
    (hexit : AllCellsEnclosed K → SecondLakeCell K → P)
    (hgonly : AllCellsEnclosed K → LakeGOnly K i → LakeGOnly K j → P) : P := by
  by_cases hall : AllCellsEnclosed K
  · by_cases hsec : SecondLakeCell K
    · exact hexit hall hsec
    · refine hgonly hall ?_ ?_
      · intro C hC hmem
        by_contra hne
        exact hsec ⟨C, hC, Or.inl ⟨hmem, hne⟩⟩
      · intro C hC hmem
        by_contra hne
        exact hsec ⟨C, hC, Or.inr ⟨hmem, hne⟩⟩
  · exact hout hall

end Predicates

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.Assembly

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.Assembly.AllCellsEnclosed
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.Assembly.SecondLakeCell
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.Assembly.LakeGOnly
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.Assembly.cases_core
