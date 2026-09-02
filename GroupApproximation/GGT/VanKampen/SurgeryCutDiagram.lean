import GroupApproximation.GGT.VanKampen.SurgeryCutProduct

/-!
# The subdiagram cut out by a closed walk

The piece a `RegionCutData` cuts out is the collapse of the complementary faces,
with the collapsed outside as its exterior face.  Every field of the piece comes
from the collapse: its map and planarity from `replaceGRegion`, its labels and
face boundaries from the source's, its relator cells from the kept cells rebased
at the walk's basepoint, and its boundary product from the supplied shelling.

Reducedness passes to the piece because the kept cells are an infix of the
source's ordered cells and are rebased by one fixed element, and the cell count
drops because the cut leaves at least one cell outside.  So a cut of a reduced
diagram supplies Osin's Lemma 6.5 cut data, whose remaining field is the one
that comes from the definition of the distinguished family rather than from the
surgery.

The adapter to Osin's landed cut record lives in `SurgeryCutLemma65`, so that
this file does not depend on the statement file.
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

/-- The subdiagram enclosed by the cut's walk. -/
noncomputable def diagram (cut : RegionCutData Delta) :
    DiscDiagram.{u, w, v} W where
  toCombMap := replaceGRegion Delta.toCombMap cut.outside cut.region
  planar := replaceGRegion_planar Delta.toCombMap cut.outside cut.region
    Delta.planar
  label := fun d => Delta.label d.1
  label_alpha := fun d => Delta.label_alpha d.1
  outerFace := newFace Delta.toCombMap cut.outside cut.region
  faceBoundary := replaceGRegionFaceBoundary Delta.toCombMap cut.outside
    cut.region Delta.faceBoundary
  relatorCells := cut.cells.map
    (keptRelatorCell Delta cut.outside cut.region cut.basepoint)
  relatorCell_faces_nodup := cut.keptCells_faces_nodup
  relatorCell_word := by
    intro C hC
    obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.1 hC
    exact cut.keptCells_word C₀ hC₀
  inner_face := by
    intro F hF
    obtain ⟨g, hg, rfl⟩ := exists_keptFace_of_ne_newFace Delta.toCombMap
      cut.outside cut.region F hF
    have hword := cut.keptFaceWord g hg
    have hne : g ≠ Delta.outerFace := by
      intro hgo
      apply hg
      rw [hgo]
      exact cut.outer_mem
    rcases Delta.inner_face g hne with ⟨C₀, hC₀, hface⟩ | hone
    · left
      have hmem : C₀ ∈ cut.before ++ cut.cells.map Subtype.val ++ cut.after := by
        rw [← cut.cells_infix]
        exact hC₀
      rcases List.mem_append.1 hmem with hleft | hright
      · rcases List.mem_append.1 hleft with hb | hc
        · exfalso
          apply hg
          rw [← hface]
          exact cut.cut_faces C₀ (List.mem_append.2 (Or.inl hb))
        · obtain ⟨C₁, hC₁, hval⟩ := List.mem_map.1 hc
          refine ⟨keptRelatorCell Delta cut.outside cut.region cut.basepoint C₁,
            List.mem_map.2 ⟨C₁, hC₁, rfl⟩, ?_⟩
          apply keptFace_congr
          rw [hval]
          exact hface
      · exfalso
        apply hg
        rw [← hface]
        exact cut.cut_faces C₀ (List.mem_append.2 (Or.inr hright))
    · right
      rw [hword]
      exact hone
  boundary_product := cut.keptCells_value_prod

/-- The piece keeps exactly the cut's cells. -/
theorem diagram_rCellCount (cut : RegionCutData Delta) :
    cut.diagram.rCellCount = cut.cells.length := by
  show (cut.cells.map
    (keptRelatorCell Delta cut.outside cut.region cut.basepoint)).length =
      cut.cells.length
  rw [List.length_map]

/-- The cut strictly drops the relator-cell count. -/
theorem diagram_rCellCount_lt (cut : RegionCutData Delta) :
    cut.diagram.rCellCount < Delta.rCellCount := by
  rw [cut.diagram_rCellCount]
  exact cut.rCellCount_lt

/-- Reducedness passes to the piece. -/
theorem diagram_reduced (cut : RegionCutData Delta) (hred : Delta.Reduced) :
    cut.diagram.Reduced :=
  reduced_of_infix_of_conj Delta cut.diagram cut.basepoint Subtype.val
    (keptRelatorCell Delta cut.outside cut.region cut.basepoint)
    (fun C => keptRelatorCell_value Delta cut.outside cut.region cut.basepoint C)
    cut.cells cut.before cut.after cut.cells_infix rfl hred

end RegionCutData
end MapCollapse
end Surgery
end VanKampen
end GGT
end GroupApproximation
