import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixO52Collapse
import GroupApproximation.Meta.AxiomGuard

/-!
# The cancelling surgery on a collapsed G-region

Two relator cells `Π`, `Σ` of a disc diagram meet a G-region `R` along one edge each:
the boundary cycle of `R` reads `alpha b₁ :: (us ++ alpha e :: zs)` with `b₁` on `Π` and
`e` on `Σ`.  Collapse `R` into one G-face (`Surgery.InnerGRegion.diagram`), then delete
the two shared edges (`VanKampenData.isRelatorProduct_sub_two`).  If the merged word
`zs ++ xs ++ us ++ ws` reads `1`, where `b₁ :: xs` and `e :: ws` are the face cycles of
`Π` and `Σ`, the boundary value is a relator product with two relator factors fewer
than the diagram has cells: `Surgery.InnerGRegion.isRelatorProduct_sub_two`.  This is
Osin's "cut the subdiagram … and fill the obtained hole with a diagram without
`R`-cells, reducing the number of `R`-cells by 2" (arXiv:math/0411039v3, O52).
-/

namespace GroupApproximation.GGT.VanKampen

open HullSC RelatorDefectBudget

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

namespace Surgery.InnerGRegion

variable {Delta : DiscDiagram.{u, w, v} W} (R : Surgery.InnerGRegion Delta)

/-- **The cancelling surgery on a collapsed G-region.** -/
theorem isRelatorProduct_sub_two {i j : Fin Delta.rCellCount} (hij : i ≠ j)
    {b₁ e : Delta.toCombMap.Dart} {xs ws us zs : List Delta.toCombMap.Dart}
    (hPcyc : Delta.toCombMap.IsFaceCycle (b₁ :: xs))
    (hPface : Delta.toCombMap.faceOf b₁ = (Embedded.cell Delta i).face)
    (hScyc : Delta.toCombMap.IsFaceCycle (e :: ws))
    (hSface : Delta.toCombMap.faceOf e = (Embedded.cell Delta j).face)
    (hcycle : R.boundary.cycle =
      Delta.toCombMap.alpha b₁ :: (us ++ Delta.toCombMap.alpha e :: zs))
    (hval : RelLetter.listVal (Embedded.dartWord Delta (zs ++ xs ++ us ++ ws)) = 1) :
    IsRelatorProduct (RelLetter.listVal '' W) (Delta.rCellCount - 2) Delta.boundaryValue := by
  classical
  have hiR : (Embedded.cell Delta i).face ∉ R.faces :=
    R.cells_avoid _ (Embedded.cell_mem Delta i)
  have hjR : (Embedded.cell Delta j).face ∉ R.faces :=
    R.cells_avoid _ (Embedded.cell_mem Delta j)
  obtain ⟨b₁', xs', hb₁', hPcyc', hxs'⟩ := R.exists_keptFaceCycle hiR hPcyc hPface
  obtain ⟨e', ws', he', hScyc', hws'⟩ := R.exists_keptFaceCycle hjR hScyc hSface
  obtain ⟨x₀, rest', hx₀, hγcyc, hrest'⟩ := R.exists_newFaceCycle hcycle
  obtain ⟨us', tail', hsplit, hus', htail'⟩ := List.map_eq_append_iff.mp hrest'
  obtain ⟨b₂', zs', hsplit2, hb₂', hzs'⟩ := List.map_eq_cons_iff.mp htail'
  subst hsplit hsplit2
  have hx₀α : x₀ = R.diagram.toCombMap.alpha b₁' :=
    Subtype.ext (hx₀.trans (congrArg Delta.toCombMap.alpha hb₁').symm)
  have he'α : e' = R.diagram.toCombMap.alpha b₂' :=
    Subtype.ext (he'.trans ((Delta.toCombMap.alpha_involutive e).symm.trans
      (congrArg Delta.toCombMap.alpha hb₂').symm))
  subst hx₀α he'α
  -- the two shared edges cross into the region
  have hαb₁mem : Delta.toCombMap.alpha b₁ ∈ R.boundary.cycle := by
    rw [hcycle]
    exact List.mem_cons_self
  have hαemem : Delta.toCombMap.alpha e ∈ R.boundary.cycle := by
    rw [hcycle]
    simp
  have hαb₁R : Delta.toCombMap.faceOf (Delta.toCombMap.alpha b₁) ∈ R.faces :=
    And.left ((R.boundary.cycle_mem_iff _).mp hαb₁mem)
  have hαeR : Delta.toCombMap.faceOf (Delta.toCombMap.alpha e) ∈ R.faces :=
    And.left ((R.boundary.cycle_mem_iff _).mp hαemem)
  -- faces of the collapse
  have hfP : R.diagram.toCombMap.faceOf b₁' =
      Surgery.MapCollapse.keptFace Delta.toCombMap R.faces R.region _ hiR :=
    R.faceOf_kept b₁' hiR ((congrArg Delta.toCombMap.faceOf hb₁').trans hPface)
  have hfγ : R.diagram.toCombMap.faceOf (R.diagram.toCombMap.alpha b₁') =
      Surgery.MapCollapse.newFace Delta.toCombMap R.faces R.region :=
    R.faceOf_new _ ((congrArg (fun z => Delta.toCombMap.faceOf (Delta.toCombMap.alpha z) ∈
      R.faces) hb₁').mpr hαb₁R)
  have hfS : R.diagram.toCombMap.faceOf (R.diagram.toCombMap.alpha b₂') =
      Surgery.MapCollapse.keptFace Delta.toCombMap R.faces R.region _ hjR :=
    R.faceOf_kept _ hjR ((congrArg Delta.toCombMap.faceOf he').trans hSface)
  have hfO : R.diagram.toCombMap.faceOf (R.diagram.vanKampenData.outer.head
      R.diagram.vanKampenData.outer_cycle.ne_nil) =
        Surgery.MapCollapse.keptFace Delta.toCombMap R.faces R.region Delta.outerFace
          R.outer_not_mem :=
    FaceBoundary.faceOf_head (R.diagram.faceBoundary R.diagram.outerFace)
  -- the merged word
  have hmapAll : (zs' ++ xs' ++ us' ++ ws').map Subtype.val = zs ++ xs ++ us ++ ws :=
    List.map_append.trans (congrArg₂ (· ++ ·)
      (List.map_append.trans (congrArg₂ (· ++ ·)
        (List.map_append.trans (congrArg₂ (· ++ ·) hzs' hxs')) hus')) hws')
  have hval' : RelLetter.listVal ((zs' ++ xs' ++ us' ++ ws').map R.diagram.label) = 1 := by
    have e1 : (zs' ++ xs' ++ us' ++ ws').map R.diagram.label =
        Embedded.dartWord Delta (zs ++ xs ++ us ++ ws) :=
      (List.map_map (g := Delta.label) (f := Subtype.val)
        (l := zs' ++ xs' ++ us' ++ ws')).symm.trans (congrArg (List.map Delta.label) hmapAll)
    rw [e1]
    exact hval
  have hprod := VanKampenData.isRelatorProduct_sub_two R.diagram.planar R.diagram.label_alpha
    R.diagram.vanKampenData hPcyc' hγcyc hScyc'
    ((congrArg (fun z => z ∈ R.diagram.relatorFaces) hfP).mpr (R.keptFace_mem_relatorFaces i))
    ((congrArg (fun z => z ∉ R.diagram.relatorFaces) hfγ).mpr R.newFace_not_mem_relatorFaces)
    ((congrArg (fun z => z ∈ R.diagram.relatorFaces) hfS).mpr (R.keptFace_mem_relatorFaces j))
    (fun h => (Embedded.cell Delta i).face_ne_outer
      (Surgery.MapCollapse.keptFace_inj Delta.toCombMap R.faces R.region _ _ hiR
        R.outer_not_mem (hfP.symm.trans (h.trans hfO))))
    (fun h => Surgery.MapCollapse.keptFace_ne_newFace Delta.toCombMap R.faces R.region
      Delta.outerFace R.outer_not_mem (hfO.symm.trans (h.symm.trans hfγ)))
    (fun h => (Embedded.cell Delta j).face_ne_outer
      (Surgery.MapCollapse.keptFace_inj Delta.toCombMap R.faces R.region _ _ hjR
        R.outer_not_mem (hfS.symm.trans (h.trans hfO))))
    (fun h => Surgery.MapCollapse.keptFace_ne_newFace Delta.toCombMap R.faces R.region _ hiR
      (hfP.symm.trans (h.trans hfγ)))
    (fun h => Embedded.cell_face_ne hij
      (Surgery.MapCollapse.keptFace_inj Delta.toCombMap R.faces R.region _ _ hiR hjR
        (hfP.symm.trans (h.symm.trans hfS))))
    (fun h => Surgery.MapCollapse.keptFace_ne_newFace Delta.toCombMap R.faces R.region _ hjR
      (hfS.symm.trans (h.trans hfγ)))
    hval'
  have hcard : R.diagram.vanKampenData.relFaces.card = Delta.rCellCount :=
    (DiscDiagram.relatorFaces_card R.diagram).trans R.rCellCount_eq
  have hbv : (RelLetter.listVal (R.diagram.vanKampenData.outer.map R.diagram.label))⁻¹ =
      Delta.boundaryValue := by
    have h1 : R.diagram.boundaryValue = Delta.boundaryValue :=
      congrArg RelLetter.listVal R.boundaryWord_eq
    refine Eq.trans ?_ h1
    show _ = RelLetter.listVal (RelWord.revInv (R.diagram.faceWord R.diagram.outerFace))
    rw [RelWord.listVal_revInv]
    rfl
  rw [← hcard, ← hbv]
  exact hprod.inv

end Surgery.InnerGRegion

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.InnerGRegion.isRelatorProduct_sub_two
