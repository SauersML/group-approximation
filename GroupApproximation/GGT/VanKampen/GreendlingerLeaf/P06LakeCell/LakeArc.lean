import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.LakeDef
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P06, case (d): the arcs of the pocket bound the lakes of their cells

Lane `gl-p06-10` of `lanes/carto-gl-p06.md`.  Certifies no printed sentence on its own.

For `K : CellPocketFaceSet D eps X i j` with boundary cycle `s₁ t̄₁ s₂ t̄₂`, where
`t̄₁ = invDarts X K.firstArc.darts`:

* every dart `e` of `K.firstArc.darts` is a boundary dart of `lakeOf K i`:
  `faceOf e = Π_i ∈ lakeOf K i`, and `α e ∈ t̄₁` is a boundary dart of `K.faces`, so
  `faceOf (α e) ∈ K.faces`, which is off the lake since `Π_i ∉ K.faces`;
* hence, for `d ∈ t̄₁`, `α d` is a boundary dart of `lakeOf K i` (`invArc_subset_lake_boundary`).

**Correction of the lane text (loud).**  The lane words the second item as "every dart of
`invDarts X K.firstArc.darts` is a boundary dart of `lakeOf K i`".  That is false under
`IsBoundaryDart M F d := faceOf d ∈ F ∧ faceOf (α d) ∉ F`: a dart of `t̄₁` has its face in
`K.faces`, off the lake.  The reversed darts are the boundary darts, as proved here.  The same holds
for `t̄₂` and `lakeOf K j`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell

universe u w v

open Embedded HullSC WordMetric Surgery.MapCollapse

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- A dart of the first arc reverses into the boundary cycle. -/
theorem alpha_mem_cycle_of_mem_firstArc (K : CellPocketFaceSet D eps X i j)
    {e : X.toCombMap.Dart} (he : e ∈ K.firstArc.darts) :
    X.toCombMap.alpha e ∈ K.boundary.cycle := by
  have hinv : X.toCombMap.alpha e ∈ invDarts X K.firstArc.darts :=
    List.mem_map_of_mem (List.mem_reverse.mpr he)
  rw [K.decomposition]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hinv))

/-- A dart of the second arc reverses into the boundary cycle. -/
theorem alpha_mem_cycle_of_mem_secondArc (K : CellPocketFaceSet D eps X i j)
    {e : X.toCombMap.Dart} (he : e ∈ K.secondArc.darts) :
    X.toCombMap.alpha e ∈ K.boundary.cycle := by
  have hinv : X.toCombMap.alpha e ∈ invDarts X K.secondArc.darts :=
    List.mem_map_of_mem (List.mem_reverse.mpr he)
  rw [K.decomposition]
  exact List.mem_append_right _ hinv

/-- **Every dart of the first arc is a boundary dart of the lake of `Π_i`.** -/
theorem firstArc_isBoundaryDart_lake (K : CellPocketFaceSet D eps X i j)
    {e : X.toCombMap.Dart} (he : e ∈ K.firstArc.darts) :
    Surgery.MapCollapse.IsBoundaryDart X.toCombMap (lakeOf K i) e := by
  have hface : X.toCombMap.faceOf e = (cell X i).face :=
    ((X.faceBoundary (cell X i).face).mem_iff e).mp (K.firstArc.mem_cycle_of_mem_darts he)
  have hin : X.toCombMap.faceOf e ∈ lakeOf K i := by
    rw [hface]
    exact cell_mem_lakeOf K i
  have hfar : X.toCombMap.faceOf (X.toCombMap.alpha e) ∈ K.faces :=
    And.left ((K.boundary.cycle_mem_iff (X.toCombMap.alpha e)).mp
      (alpha_mem_cycle_of_mem_firstArc K he))
  have hout : X.toCombMap.faceOf (X.toCombMap.alpha e) ∉ lakeOf K i :=
    fun hmem => not_mem_faces_of_mem_lakeOf K K.first_not_mem hmem hfar
  exact And.intro hin hout

/-- **Every dart of the second arc is a boundary dart of the lake of `Π_j`.** -/
theorem secondArc_isBoundaryDart_lake (K : CellPocketFaceSet D eps X i j)
    {e : X.toCombMap.Dart} (he : e ∈ K.secondArc.darts) :
    Surgery.MapCollapse.IsBoundaryDart X.toCombMap (lakeOf K j) e := by
  have hface : X.toCombMap.faceOf e = (cell X j).face :=
    ((X.faceBoundary (cell X j).face).mem_iff e).mp (K.secondArc.mem_cycle_of_mem_darts he)
  have hin : X.toCombMap.faceOf e ∈ lakeOf K j := by
    rw [hface]
    exact cell_mem_lakeOf K j
  have hfar : X.toCombMap.faceOf (X.toCombMap.alpha e) ∈ K.faces :=
    And.left ((K.boundary.cycle_mem_iff (X.toCombMap.alpha e)).mp
      (alpha_mem_cycle_of_mem_secondArc K he))
  have hout : X.toCombMap.faceOf (X.toCombMap.alpha e) ∉ lakeOf K j :=
    fun hmem => not_mem_faces_of_mem_lakeOf K K.second_not_mem hmem hfar
  exact And.intro hin hout

/-- **The reversed first arc bounds the lake of `Π_i`** (`invArc_subset_lake_boundary`, corrected
orientation): for every dart `d` of `t̄₁ = invDarts X K.firstArc.darts`, the reversal `α d` is a
boundary dart of `lakeOf K i`. -/
theorem invArc_subset_lake_boundary (K : CellPocketFaceSet D eps X i j)
    (d : X.toCombMap.Dart) (hd : d ∈ invDarts X K.firstArc.darts) :
    Surgery.MapCollapse.IsBoundaryDart X.toCombMap (lakeOf K i) (X.toCombMap.alpha d) := by
  have hd' : d ∈ K.firstArc.darts.reverse.map X.toCombMap.alpha := hd
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd'
  rw [X.toCombMap.alpha_involutive e]
  exact firstArc_isBoundaryDart_lake K (List.mem_reverse.mp he)

/-- **The reversed second arc bounds the lake of `Π_j`**: for every dart `d` of
`t̄₂ = invDarts X K.secondArc.darts`, the reversal `α d` is a boundary dart of `lakeOf K j`. -/
theorem invSecondArc_subset_lake_boundary (K : CellPocketFaceSet D eps X i j)
    (d : X.toCombMap.Dart) (hd : d ∈ invDarts X K.secondArc.darts) :
    Surgery.MapCollapse.IsBoundaryDart X.toCombMap (lakeOf K j) (X.toCombMap.alpha d) := by
  have hd' : d ∈ K.secondArc.darts.reverse.map X.toCombMap.alpha := hd
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd'
  rw [X.toCombMap.alpha_involutive e]
  exact secondArc_isBoundaryDart_lake K (List.mem_reverse.mp he)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.alpha_mem_cycle_of_mem_firstArc
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.alpha_mem_cycle_of_mem_secondArc
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.firstArc_isBoundaryDart_lake
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.secondArc_isBoundaryDart_lake
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.invArc_subset_lake_boundary
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeCell.invSecondArc_subset_lake_boundary
