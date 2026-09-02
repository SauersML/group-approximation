import GroupApproximation.GGT.VanKampen.SurgeryCutRecord

/-!
# The boundary product of a cut piece

The piece cut out by a `RegionCutData` needs the van Kampen product identity:
the ordered product of its relator-cell values is the value of its exterior
boundary word.  That identity is a theorem here rather than a supplied field,
because the producer supplies a shelling of the enclosed faces along the
enclosing walk whose recorded steps are the kept cells, rebased, and the
shelling's product formula then computes the walk's value as exactly that
ordered product.

The exterior boundary of the piece reads the enclosing walk backwards, which is
where the inversion in the product identity comes from.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Surgery
namespace MapCollapse

open GroupApproximation.HullSC

universe u w v

namespace RegionCutData

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (GGT.RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}

/-- A rebased cell's value is the conjugate of the value of the oriented
boundary of its face. -/
theorem keptCell_value (cut : RegionCutData Delta)
    (C : {C : RelatorCell Delta.toCombMap Delta.outerFace W //
      C.face ∉ cut.outside}) (hC : C ∈ cut.cells) :
    (keptRelatorCell Delta cut.outside cut.region cut.basepoint C).value =
      (cut.basepoint⁻¹ * C.1.conjugator) *
        GGT.RelLetter.listVal (Embedded.dartWord Delta
          (Embedded.orientedFaceDarts Delta C.1.face C.1.reversed)) *
        (cut.basepoint⁻¹ * C.1.conjugator)⁻¹ := by
  have hconj :
      (keptRelatorCell Delta cut.outside cut.region cut.basepoint C).conjugator =
        cut.basepoint⁻¹ * C.1.conjugator := rfl
  have hrev :
      (keptRelatorCell Delta cut.outside cut.region cut.basepoint C).reversed =
        C.1.reversed := rfl
  have hword :
      (keptRelatorCell Delta cut.outside cut.region cut.basepoint C).word =
        C.1.word := rfl
  rw [RelatorCell.value_eq_conj, hconj, hrev, hword, cut.cells_word C hC,
    Embedded.listVal_orientedFaceDarts]

/-- **The van Kampen product identity for a cut piece.**  The ordered product of
the rebased cell values is the value of the piece's exterior boundary word. -/
theorem keptCells_value_prod (cut : RegionCutData Delta) :
    ((cut.cells.map
        (keptRelatorCell Delta cut.outside cut.region cut.basepoint)).map
      RelatorCell.value).prod =
      GGT.RelLetter.listVal (RelWord.revInv
        (((replaceGRegionFaceBoundary Delta.toCombMap cut.outside cut.region
          Delta.faceBoundary
          (newFace Delta.toCombMap cut.outside cut.region)).darts).map
          (fun d => Delta.label d.1))) := by
  have hshell := Embedded.listVal_dartWord_of_cellShelling cut.shelling
  rw [List.zipWith_map, List.zipWith_self] at hshell
  have hcells : ((cut.cells.map
        (keptRelatorCell Delta cut.outside cut.region cut.basepoint)).map
      RelatorCell.value) =
      cut.cells.map (fun C => (cut.basepoint⁻¹ * C.1.conjugator) *
        GGT.RelLetter.listVal (Embedded.dartWord Delta
          (Embedded.orientedFaceDarts Delta C.1.face C.1.reversed)) *
        (cut.basepoint⁻¹ * C.1.conjugator)⁻¹) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro C hC
    exact cut.keptCell_value C hC
  have hrhs : GGT.RelLetter.listVal (RelWord.revInv
        (((replaceGRegionFaceBoundary Delta.toCombMap cut.outside cut.region
          Delta.faceBoundary
          (newFace Delta.toCombMap cut.outside cut.region)).darts).map
          (fun d => Delta.label d.1))) =
      GGT.RelLetter.listVal (Embedded.dartWord Delta
        (Embedded.invDarts Delta cut.region.toBoundaryCycle.cycle)) := by
    rw [cut.newFaceWord, RelWord.listVal_revInv,
      Embedded.listVal_dartWord_invDarts]
  rw [hcells, hrhs]
  exact hshell.symm

end RegionCutData
end MapCollapse
end Surgery
end VanKampen
end GGT
end GroupApproximation
