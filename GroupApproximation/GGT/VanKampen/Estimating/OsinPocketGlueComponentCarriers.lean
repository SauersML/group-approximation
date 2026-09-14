import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketGlueComponentEmbedding
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketGlueCarriers
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketGlueOuterArc
import GroupApproximation.Meta.AxiomGuard

/-!
# Carriers of the exterior component

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): regions of copies of `Γ_1` glue back into
regions of copies of `Δ`.

Let `P` be a pocket region of a least-area diagram `Δ` and `Ξ` an O-equivalent copy of the pocket
diagram, glued into the complement of `P`.  This file computes the carriers that a region of `Ξ`
reads in the exterior component of the glued map (`PocketRegion.componentDiagram`): a relator cell
of `Δ` outside the pocket keeps its carrier, and the outer darts of `Ξ` on the part of `∂Ξ` glued to
an arc of a cell or of `∂Δ` go to that arc.

* `Embedded.reverse_map_window`: a window in the middle part of a mapped reversed concatenation.
* `PocketRegion.exists_componentLeftCell`: a relator cell of `Δ` outside the pocket is a relator
  cell of the component with the image carrier.
* `PocketRegion.glueEmbedding_cellWindow`: the outer darts of `Ξ` glued to an arc of a cell.
* `PocketRegion.componentCellArc_boundaryDarts`: they read a sub-arc of the image cell backwards.
* `PocketRegion.exists_component_outerArc_within`: an outer arc of `Ξ` glued to an arc of `∂Δ` is an
  outer arc of the component inside that arc.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, through Osin's Lemma 9.7(b)); certifies no printed
sentence on its own.
-/

noncomputable section

namespace GroupApproximation.GGT.VanKampen

open Embedded HullSC Surgery.MapCollapse Surgery.PocketGlue

universe u w v

namespace Embedded

/-- A window of a mapped reversed list is the reversed map of the mirrored window. -/
theorem reverse_map_drop_take {α β : Type*} (g : α → β) (L : List α) (k l : ℕ)
    (h : k + l ≤ L.length) :
    ((L.reverse.map g).drop k).take l = ((L.drop (L.length - k - l)).take l).reverse.map g := by
  rw [← List.map_drop, ← List.map_take, reverse_drop_take L k l h]

/-- A window in the middle part of a mapped reversed concatenation. -/
theorem reverse_map_window {α β : Type*} (g : α → β) (B3 M B1 : List α) {n : ℕ}
    (hn : B1.length = n) (m l : ℕ) (h : m + l ≤ M.length) :
    (((B3 ++ M ++ B1).reverse.map g).drop (n + m)).take l =
      ((M.drop (M.length - m - l)).take l).reverse.map g := by
  subst hn
  have h1 : m ≤ (M.reverse.map g).length := by
    rw [List.length_map, List.length_reverse]
    omega
  have h2 : l ≤ ((M.reverse.map g).drop m).length := by
    rw [List.length_drop, List.length_map, List.length_reverse]
    omega
  have hB : B1.length = (B1.reverse.map g).length := by
    rw [List.length_map, List.length_reverse]
  rw [List.reverse_append, List.reverse_append, List.map_append, List.map_append, hB,
    List.drop_length_add_append, List.drop_append_of_le_length h1,
    List.take_append_of_le_length h2, reverse_map_drop_take g M m l h]

/-- A window of a window. -/
theorem drop_take_drop_take {α : Type*} (L : List α) (a b i l : ℕ) (h : i + l ≤ b) :
    (((L.drop a).take b).drop i).take l = (L.drop (a + i)).take l := by
  rw [List.drop_take, List.drop_drop, List.take_take]
  congr 1
  omega

end Embedded

namespace PocketRegion

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W} (P : PocketRegion Delta) {Xi : DiscDiagram.{u, w, v} W}

/-- Reversing a list of darts of the exterior component, read in the glued map. -/
theorem componentDiagram_map_val_reverse (O : OEquivalentDiscDiagram P.diagram Xi)
    (hplanar : ((P.glueSeam O).glueMap.component (P.glueOuterDart O)).IsPlanar)
    (L : List (P.componentDiagram O hplanar).toCombMap.Dart) :
    (L.reverse.map (P.componentDiagram O hplanar).toCombMap.alpha).map Subtype.val =
      (L.map Subtype.val).reverse.map (P.glueSeam O).glueMap.alpha :=
  (List.map_map (f := (P.componentDiagram O hplanar).toCombMap.alpha) (g := Subtype.val)
      (l := L.reverse)).trans
    ((List.map_map (f := Subtype.val) (g := (P.glueSeam O).glueMap.alpha) (l := L.reverse)).symm.trans
      (congrArg (List.map (P.glueSeam O).glueMap.alpha)
        (List.map_reverse (f := Subtype.val) (l := L))))

open scoped Classical in
/-- A dart of `Δ` as a dart of the exterior component: its glued image when that lies on the
component, and the exterior dart otherwise. -/
def componentLeftDart (O : OEquivalentDiscDiagram P.diagram Xi)
    (hplanar : ((P.glueSeam O).glueMap.component (P.glueOuterDart O)).IsPlanar)
    (d : Delta.toCombMap.Dart) : (P.componentDiagram O hplanar).toCombMap.Dart :=
  if hd : (P.glueSeam O).glueMap.componentOf (P.glueOuterDart O)
    ((P.glueSeam O).leftIncl (P.glueOuterDart O) d)
  then (⟨(P.glueSeam O).leftIncl (P.glueOuterDart O) d, hd⟩ :
    {g // (P.glueSeam O).glueMap.componentOf (P.glueOuterDart O) g})
  else (⟨P.glueOuterDart O, (P.glueSeam O).glueMap.componentOf_self _⟩ :
    {g // (P.glueSeam O).glueMap.componentOf (P.glueOuterDart O) g})

theorem componentLeftDart_val (O : OEquivalentDiscDiagram P.diagram Xi)
    (hplanar : ((P.glueSeam O).glueMap.component (P.glueOuterDart O)).IsPlanar)
    {d : Delta.toCombMap.Dart}
    (hd : (P.glueSeam O).glueMap.componentOf (P.glueOuterDart O)
      ((P.glueSeam O).leftIncl (P.glueOuterDart O) d)) :
    Subtype.val (P.componentLeftDart O hplanar d) =
      (P.glueSeam O).leftIncl (P.glueOuterDart O) d := by
  unfold componentLeftDart
  rw [dif_pos hd]

/-- At least area, a dart of a relator face of `Δ` outside the pocket lies on the exterior
component. -/
theorem componentOf_leftIncl_of_face_mem (O : OEquivalentDiscDiagram P.diagram Xi)
    (hplanar : ((P.glueSeam O).glueMap.component (P.glueOuterDart O)).IsPlanar)
    (hlea : Delta.LeastArea) {g : Delta.toCombMap.Face}
    (hg : g ∈ Delta.relatorCells.map RelatorCell.face) (hgo : g ∈ P.outside)
    {d : Delta.toCombMap.Dart} (hd : Delta.toCombMap.faceOf d = g) :
    (P.glueSeam O).glueMap.componentOf (P.glueOuterDart O)
      ((P.glueSeam O).leftIncl (P.glueOuterDart O) d) := by
  have hdo : Delta.toCombMap.faceOf d ∈ (P.glueSeam O).faces := by
    rw [hd]
    exact hgo
  obtain ⟨y, hy, hyF⟩ := P.exists_componentOf_of_mem_glueRelFaces O hplanar hlea
    (P.glueLeft_mem_glueRelFaces O hg hgo)
  rw [(P.glueSeam O).leftIncl_of_mem _ hdo]
  refine (P.glueSeam O).glueMap.mem_of_faceOf_eq _
    ((P.glueSeam O).glueMap.componentOf_alpha _) ((P.glueSeam O).glueMap.componentOf_sigma _)
    hy ?_
  rw [hyF]
  exact ((P.glueSeam O).faceOf_inl _).trans (congrArg (P.glueSeam O).leftFace (Subtype.ext hd))

/-- A dart of the exterior face of `Δ` lies on the exterior component. -/
theorem componentOf_leftIncl_of_outer (O : OEquivalentDiscDiagram P.diagram Xi)
    {d : Delta.toCombMap.Dart} (hd : Delta.toCombMap.faceOf d = Delta.outerFace) :
    (P.glueSeam O).glueMap.componentOf (P.glueOuterDart O)
      ((P.glueSeam O).leftIncl (P.glueOuterDart O) d) := by
  have hdo : Delta.toCombMap.faceOf d ∈ (P.glueSeam O).faces := by
    rw [hd]
    exact P.outerFace_mem
  rw [(P.glueSeam O).leftIncl_of_mem _ hdo]
  refine (P.glueSeam O).glueMap.mem_of_faceOf_eq _
    ((P.glueSeam O).glueMap.componentOf_alpha _) ((P.glueSeam O).glueMap.componentOf_sigma _)
    ((P.glueSeam O).glueMap.componentOf_self (P.glueOuterDart O)) ?_
  rw [P.glueMap_faceOf_glueOuterDart O]
  exact ((P.glueSeam O).faceOf_inl _).trans (congrArg (P.glueSeam O).leftFace (Subtype.ext hd))

/-- A face of `Δ` as a face of the exterior component, through a representative dart. -/
def componentLeftFace (O : OEquivalentDiscDiagram P.diagram Xi)
    (hplanar : ((P.glueSeam O).glueMap.component (P.glueOuterDart O)).IsPlanar)
    (g : Delta.toCombMap.Face) : (P.componentDiagram O hplanar).toCombMap.Face :=
  (P.componentDiagram O hplanar).toCombMap.faceOf (P.componentLeftDart O hplanar (Quotient.out g))

theorem restrictFace_componentLeftFace (O : OEquivalentDiscDiagram P.diagram Xi)
    (hplanar : ((P.glueSeam O).glueMap.component (P.glueOuterDart O)).IsPlanar)
    {g : Delta.toCombMap.Face} (hgo : g ∈ P.outside)
    (hdom : (P.glueSeam O).glueMap.componentOf (P.glueOuterDart O)
      ((P.glueSeam O).leftIncl (P.glueOuterDart O) (Quotient.out g))) :
    (P.glueSeam O).glueMap.restrictFace ((P.glueSeam O).glueMap.componentOf (P.glueOuterDart O))
        ((P.glueSeam O).glueMap.componentOf_alpha (P.glueOuterDart O))
        ((P.glueSeam O).glueMap.componentOf_sigma (P.glueOuterDart O))
        (P.componentLeftFace O hplanar g) = (P.glueSeam O).leftFace ⟨g, hgo⟩ := by
  have hout : Delta.toCombMap.faceOf (Quotient.out g) = g := Quotient.out_eq g
  have hmem : Delta.toCombMap.faceOf (Quotient.out g) ∈ (P.glueSeam O).faces := by
    rw [hout]
    exact hgo
  change (P.glueSeam O).glueMap.faceOf
    (Subtype.val (P.componentLeftDart O hplanar (Quotient.out g))) = _
  rw [P.componentLeftDart_val O hplanar hdom, (P.glueSeam O).leftIncl_of_mem _ hmem]
  exact ((P.glueSeam O).faceOf_inl _).trans (congrArg (P.glueSeam O).leftFace (Subtype.ext hout))

theorem componentLeftFace_boundary (O : OEquivalentDiscDiagram P.diagram Xi)
    (hplanar : ((P.glueSeam O).glueMap.component (P.glueOuterDart O)).IsPlanar)
    {g : Delta.toCombMap.Face} (hgo : g ∈ P.outside)
    (hdom : ∀ d, Delta.toCombMap.faceOf d = g → (P.glueSeam O).glueMap.componentOf
      (P.glueOuterDart O) ((P.glueSeam O).leftIncl (P.glueOuterDart O) d)) :
    ((P.componentDiagram O hplanar).faceBoundary (P.componentLeftFace O hplanar g)).darts =
      (Delta.faceBoundary g).darts.map (P.componentLeftDart O hplanar) := by
  have key : ((P.componentDiagram O hplanar).faceBoundary
        (P.componentLeftFace O hplanar g)).darts.map Subtype.val =
      ((Delta.faceBoundary g).darts.map (P.componentLeftDart O hplanar)).map Subtype.val := by
    refine ((P.glueSeam O).glueMap.restrictFaceBoundary_darts _ _ _
      ((P.glueSeam O).glueFaceBoundary Delta.faceBoundary Xi.faceBoundary) _).trans ?_
    rw [P.restrictFace_componentLeftFace O hplanar hgo (hdom _ (Quotient.out_eq g)),
      (P.glueSeam O).glueFaceBoundary_leftFace_darts,
      (P.glueSeam O).leftDarts_eq_map (P.glueOuterDart O)]
    refine (List.map_congr_left fun d hd => ?_).trans
      (List.map_map (f := P.componentLeftDart O hplanar) (g := Subtype.val)
        (l := (Delta.faceBoundary g).darts)).symm
    exact (P.componentLeftDart_val O hplanar
      (hdom d (((Delta.faceBoundary g).mem_iff d).mp hd))).symm
  exact List.map_injective_iff.mpr Subtype.val_injective key

/-- **At least area, a relator cell of `Δ` outside the pocket is a relator cell of the exterior
component**, with the image carrier. -/
theorem exists_componentLeftCell (O : OEquivalentDiscDiagram P.diagram Xi)
    (hplanar : ((P.glueSeam O).glueMap.component (P.glueOuterDart O)).IsPlanar)
    (hlea : Delta.LeastArea) (t : Fin Delta.rCellCount) (ht : (cell Delta t).face ∉ P.faces) :
    ∃ j : Fin (P.componentDiagram O hplanar).rCellCount,
      cellDarts (P.componentDiagram O hplanar) j =
        (cellDarts Delta t).map (P.componentLeftDart O hplanar) := by
  have hmemX : (cell Delta t).face ∈ Delta.relatorCells.map RelatorCell.face :=
    List.mem_map_of_mem (cell_mem Delta t)
  have hgo : (cell Delta t).face ∈ P.outside := (P.mem_outside_iff _).2 ht
  have hdom : ∀ d, Delta.toCombMap.faceOf d = (cell Delta t).face →
      (P.glueSeam O).glueMap.componentOf (P.glueOuterDart O)
        ((P.glueSeam O).leftIncl (P.glueOuterDart O) d) :=
    fun d hd => P.componentOf_leftIncl_of_face_mem O hplanar hlea hmemX hgo hd
  have hmem : P.componentLeftFace O hplanar (cell Delta t).face ∈
      (P.componentDiagram O hplanar).relatorCells.map RelatorCell.face := by
    rw [P.componentDiagram_face_mem_iff O hplanar,
      P.restrictFace_componentLeftFace O hplanar hgo (hdom _ (Quotient.out_eq _))]
    exact P.glueLeft_mem_glueRelFaces O hmemX hgo
  obtain ⟨C', hC', hCF⟩ := List.mem_map.1 hmem
  obtain ⟨n, hn⟩ := List.get_of_mem hC'
  refine ⟨n, ?_⟩
  have hface : (cell (P.componentDiagram O hplanar) n).face =
      P.componentLeftFace O hplanar (cell Delta t).face :=
    (congrArg RelatorCell.face hn).trans hCF
  exact (congrArg (fun F => ((P.componentDiagram O hplanar).faceBoundary F).darts) hface).trans
    (P.componentLeftFace_boundary O hplanar hgo hdom)

/-- The outer darts of the copy, glued: the complement cycle, reversed and crossed. -/
theorem glueEmbedding_outerDarts_map (O : OEquivalentDiscDiagram P.diagram Xi) :
    (outerDarts Xi).map (P.glueSeam O).glueEmbedding =
      (P.outer.cycle.map ((P.glueSeam O).leftIncl (P.glueOuterDart O))).reverse.map
        (P.glueSeam O).glueMap.alpha := by
  have h1 := congrArg (List.map (P.glueSeam O).glueMap.alpha)
    ((P.glueSeam O).outerBoundary_map_glueEmbedding (P.glueOuterDart O))
  simp only [List.map_map] at h1
  simp only [outerDarts, List.map_reverse, List.map_map]
  exact congrArg List.reverse
    ((List.map_congr_left fun x _ => ((P.glueSeam O).glueAlpha_glueEmbedding x).symm).trans h1)

/-- **The outer darts of the copy glued to an arc of a cell**: a window of the outer darts of `Ξ`
inside the positions of `arc` is carried to the sub-arc of `arc`, read backwards. -/
theorem glueEmbedding_cellWindow (O : OEquivalentDiscDiagram P.diagram Xi)
    {t : Fin Delta.rCellCount} (arc : CyclicArc (cellDarts Delta t))
    {pre post : List Delta.toCombMap.Dart}
    (hsplit : invDarts Delta P.outer.cycle = pre ++ invDarts Delta arc.darts ++ post)
    (tarc : CyclicArc (outerDarts Xi)) (m : ℕ) (hm : tarc.start.1 = pre.length + m)
    (h : m + tarc.length ≤ arc.length) :
    tarc.darts.map (P.glueSeam O).glueEmbedding =
      ((arc.sub (arc.length - m - tarc.length) tarc.length (by omega)).darts.map
        ((P.glueSeam O).leftIncl (P.glueOuterDart O))).reverse.map
          (P.glueSeam O).glueMap.alpha := by
  have hcl : P.outer.cycle.length = pre.length + arc.length + post.length := by
    have hlen := congrArg List.length hsplit
    simp only [invDarts_length, List.length_append, CyclicArc.darts_length] at hlen
    omega
  have hol : (outerDarts Xi).length = P.outer.cycle.length := P.length_outerDarts_copy O
  rw [CyclicArc.darts_eq_drop_take tarc rfl (by omega), List.map_take, List.map_drop,
    P.glueEmbedding_outerDarts_map O, hm, cycle_eq_of_invDarts hsplit, List.map_append,
    List.map_append,
    reverse_map_window (P.glueSeam O).glueMap.alpha
      ((invDarts Delta post).map ((P.glueSeam O).leftIncl (P.glueOuterDart O)))
      (arc.darts.map ((P.glueSeam O).leftIncl (P.glueOuterDart O)))
      ((invDarts Delta pre).map ((P.glueSeam O).leftIncl (P.glueOuterDart O)))
      (by rw [List.length_map, invDarts_length]) m tarc.length
      (by rw [List.length_map, CyclicArc.darts_length]; exact h),
    CyclicArc.sub_darts, List.length_map, CyclicArc.darts_length, List.map_take, List.map_drop]

/-- The sub-arc of length `l` of the image of a cell outside the pocket, ending `m` darts before
the end of `arc`. -/
def componentCellArc (O : OEquivalentDiscDiagram P.diagram Xi)
    (hplanar : ((P.glueSeam O).glueMap.component (P.glueOuterDart O)).IsPlanar)
    {t : Fin Delta.rCellCount} {j : Fin (P.componentDiagram O hplanar).rCellCount}
    (hj : cellDarts (P.componentDiagram O hplanar) j =
      (cellDarts Delta t).map (P.componentLeftDart O hplanar))
    (arc : CyclicArc (cellDarts Delta t)) (m l : ℕ) (h : m + l ≤ arc.length) :
    CyclicArc (cellDarts (P.componentDiagram O hplanar) j) :=
  (arc.sub (arc.length - m - l) l (by omega)).mapTo (P.componentLeftDart O hplanar) hj

/-- **The image target arc reads a sub-arc of the cell backwards.** -/
theorem componentCellArc_boundaryDarts (O : OEquivalentDiscDiagram P.diagram Xi)
    (hplanar : ((P.glueSeam O).glueMap.component (P.glueOuterDart O)).IsPlanar)
    (hlea : Delta.LeastArea) {t : Fin Delta.rCellCount} (ht : (cell Delta t).face ∉ P.faces)
    {j : Fin (P.componentDiagram O hplanar).rCellCount}
    (hj : cellDarts (P.componentDiagram O hplanar) j =
      (cellDarts Delta t).map (P.componentLeftDart O hplanar))
    (arc : CyclicArc (cellDarts Delta t)) {pre post : List Delta.toCombMap.Dart}
    (hsplit : invDarts Delta P.outer.cycle = pre ++ invDarts Delta arc.darts ++ post)
    (tarc : CyclicArc (outerDarts Xi)) (m : ℕ) (hm : tarc.start.1 = pre.length + m)
    (h : m + tarc.length ≤ arc.length) :
    targetBoundaryDarts (P.componentDiagram O hplanar) (some j)
        (P.componentCellArc O hplanar hj arc m tarc.length h) =
      tarc.darts.map (P.componentDart O hplanar) := by
  have hmemX : (cell Delta t).face ∈ Delta.relatorCells.map RelatorCell.face :=
    List.mem_map_of_mem (cell_mem Delta t)
  have hgo : (cell Delta t).face ∈ P.outside := (P.mem_outside_iff _).2 ht
  have hwin := P.glueEmbedding_cellWindow O arc hsplit tarc m hm h
  have hsub : ∀ d ∈ (arc.sub (arc.length - m - tarc.length) tarc.length (by omega)).darts,
      (P.glueSeam O).glueMap.componentOf (P.glueOuterDart O)
        ((P.glueSeam O).leftIncl (P.glueOuterDart O) d) := fun d hd =>
    P.componentOf_leftIncl_of_face_mem O hplanar hlea hmemX hgo
      (((Delta.faceBoundary (cell Delta t).face).mem_iff d).mp
        (CyclicArc.mem_cycle_of_mem_darts _ hd))
  have hcomp : ∀ x ∈ tarc.darts, (P.glueSeam O).glueMap.componentOf (P.glueOuterDart O)
      ((P.glueSeam O).glueEmbedding x) := by
    intro x hx
    have hmem : (P.glueSeam O).glueEmbedding x ∈ tarc.darts.map (P.glueSeam O).glueEmbedding :=
      List.mem_map_of_mem hx
    rw [hwin, List.mem_map] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    rw [List.mem_reverse, List.mem_map] at hy
    obtain ⟨d, hd, rfl⟩ := hy
    rw [← hyx]
    exact ((P.glueSeam O).glueMap.componentOf_alpha _ _).mpr (hsub d hd)
  have e1 := P.componentDiagram_map_val_reverse O hplanar
    (P.componentCellArc O hplanar hj arc m tarc.length h).darts
  have e2 : (P.componentCellArc O hplanar hj arc m tarc.length h).darts.map Subtype.val =
      (arc.sub (arc.length - m - tarc.length) tarc.length (by omega)).darts.map
        ((P.glueSeam O).leftIncl (P.glueOuterDart O)) :=
    (congrArg (List.map Subtype.val) (CyclicArc.mapTo_darts _ _ hj)).trans
      ((List.map_map (f := P.componentLeftDart O hplanar) (g := Subtype.val)).trans
        (List.map_congr_left fun d hd => P.componentLeftDart_val O hplanar (hsub d hd)))
  have key : (targetBoundaryDarts (P.componentDiagram O hplanar) (some j)
        (P.componentCellArc O hplanar hj arc m tarc.length h)).map Subtype.val =
      (tarc.darts.map (P.componentDart O hplanar)).map Subtype.val :=
    e1.trans ((congrArg (fun L => L.reverse.map (P.glueSeam O).glueMap.alpha) e2).trans
      (hwin.symm.trans ((List.map_congr_left fun x hx =>
        (P.componentDart_val O hplanar (hcomp x hx)).symm).trans
          (List.map_map (f := P.componentDart O hplanar) (g := Subtype.val)).symm)))
  exact List.map_injective_iff.mpr Subtype.val_injective key

/-- The outer face of the exterior component carries the outer face of `Δ`. -/
theorem componentDiagram_outerBoundary_val (O : OEquivalentDiscDiagram P.diagram Xi)
    (hplanar : ((P.glueSeam O).glueMap.component (P.glueOuterDart O)).IsPlanar) :
    ((P.componentDiagram O hplanar).faceBoundary
        (P.componentDiagram O hplanar).outerFace).darts.map Subtype.val =
      (Delta.faceBoundary Delta.outerFace).darts.map
        ((P.glueSeam O).leftIncl (P.glueOuterDart O)) := by
  refine ((P.glueSeam O).glueMap.restrictFaceBoundary_darts _ _ _
    ((P.glueSeam O).glueFaceBoundary Delta.faceBoundary Xi.faceBoundary) _).trans ?_
  change ((P.glueSeam O).glueFaceBoundary Delta.faceBoundary Xi.faceBoundary
    ((P.glueSeam O).glueMap.faceOf (P.glueOuterDart O))).darts = _
  rw [P.glueMap_faceOf_glueOuterDart O, (P.glueSeam O).glueFaceBoundary_leftFace_darts]
  exact (P.glueSeam O).leftDarts_eq_map _ _ _ _

/-- The outer darts of the exterior component, read in the glued map. -/
theorem componentOuterDarts_val (O : OEquivalentDiscDiagram P.diagram Xi)
    (hplanar : ((P.glueSeam O).glueMap.component (P.glueOuterDart O)).IsPlanar) :
    (outerDarts (P.componentDiagram O hplanar)).map Subtype.val =
      ((Delta.faceBoundary Delta.outerFace).darts.map
        ((P.glueSeam O).leftIncl (P.glueOuterDart O))).reverse.map
          (P.glueSeam O).glueMap.alpha :=
  (P.componentDiagram_map_val_reverse O hplanar _).trans
    (congrArg (fun L => L.reverse.map (P.glueSeam O).glueMap.alpha)
      (P.componentDiagram_outerBoundary_val O hplanar))

/-- **An outer arc of the copy on a boundary arc of `Δ` is an outer arc of the exterior component
inside that arc.** -/
theorem exists_component_outerArc_within (O : OEquivalentDiscDiagram P.diagram Xi)
    (hplanar : ((P.glueSeam O).glueMap.component (P.glueOuterDart O)).IsPlanar)
    (arc : CyclicArc (outerDarts Delta))
    (hend : arc.start.1 + arc.length ≤ (outerDarts Delta).length)
    (pre post : List Delta.toCombMap.Dart)
    (hdec : invDarts Delta P.outer.cycle = pre ++ arc.darts ++ post)
    (A : CyclicArc (outerDarts Xi)) (hpre : pre.length ≤ A.start.1)
    (hA : A.start.1 + A.length ≤ pre.length + arc.length) :
    ∃ B : CyclicArc (outerDarts (P.componentDiagram O hplanar)),
      arc.start.1 ≤ B.start.1 ∧ B.start.1 + B.length ≤ arc.start.1 + arc.length ∧
        B.darts = A.darts.map (P.componentDart O hplanar) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hpre
  have hN : (outerDarts Delta).length = (Delta.faceBoundary Delta.outerFace).darts.length := by
    simp only [outerDarts, List.length_map, List.length_reverse]
  have hNY : (outerDarts (P.componentDiagram O hplanar)).length =
      (Delta.faceBoundary Delta.outerFace).darts.length := by
    have h := congrArg List.length (P.componentDiagram_outerBoundary_val O hplanar)
    have h2 : ((P.componentDiagram O hplanar).faceBoundary
        (P.componentDiagram O hplanar).outerFace).darts.length =
          (Delta.faceBoundary Delta.outerFace).darts.length :=
      (List.length_map (f := Subtype.val)).symm.trans (h.trans (List.length_map (f := _)))
    simp only [outerDarts, List.length_map, List.length_reverse]
    exact h2
  have hcl : P.outer.cycle.length = pre.length + arc.length + post.length := by
    have hlen := congrArg List.length hdec
    simp only [invDarts_length, List.length_append, CyclicArc.darts_length] at hlen
    omega
  have hol : (outerDarts Xi).length = P.outer.cycle.length := P.length_outerDarts_copy O
  -- The common window, read in the glued map.
  have hwinX : ((invDarts Delta arc.darts).drop (arc.length - m - A.length)).take A.length =
      ((Delta.faceBoundary Delta.outerFace).darts.drop
        ((Delta.faceBoundary Delta.outerFace).darts.length - (arc.start.1 + m) - A.length)).take
          A.length := by
    change ((arc.darts.reverse.map Delta.toCombMap.alpha).drop (arc.length - m - A.length)).take
      A.length = _
    rw [reverse_map_drop_take _ _ _ _ (by rw [CyclicArc.darts_length]; omega),
      CyclicArc.darts_length, show arc.length - (arc.length - m - A.length) - A.length = m by omega,
      CyclicArc.darts_eq_drop_take arc rfl hend, drop_take_drop_take _ _ _ _ _ (by omega)]
    change ((((Delta.faceBoundary Delta.outerFace).darts.reverse.map Delta.toCombMap.alpha).drop
      (arc.start.1 + m)).take A.length).reverse.map Delta.toCombMap.alpha = _
    rw [reverse_map_drop_take _ _ _ _ (by omega)]
    simp only [List.map_reverse, List.reverse_reverse, List.map_map,
      Delta.toCombMap.alpha_involutive.comp_self, List.map_id]
  have hGm : A.darts.map (P.glueSeam O).glueEmbedding =
      ((((Delta.faceBoundary Delta.outerFace).darts.drop
        ((Delta.faceBoundary Delta.outerFace).darts.length - (arc.start.1 + m) - A.length)).take
          A.length).map ((P.glueSeam O).leftIncl (P.glueOuterDart O))).reverse.map
            (P.glueSeam O).glueMap.alpha := by
    have hdec' : invDarts Delta P.outer.cycle =
        pre ++ invDarts Delta (invDarts Delta arc.darts) ++ post := by
      rw [invDarts_invDarts]
      exact hdec
    rw [CyclicArc.darts_eq_drop_take A rfl (by omega), List.map_take, List.map_drop,
      P.glueEmbedding_outerDarts_map O, hm, cycle_eq_of_invDarts hdec', List.map_append,
      List.map_append,
      reverse_map_window (P.glueSeam O).glueMap.alpha
        ((invDarts Delta post).map ((P.glueSeam O).leftIncl (P.glueOuterDart O)))
        ((invDarts Delta arc.darts).map ((P.glueSeam O).leftIncl (P.glueOuterDart O)))
        ((invDarts Delta pre).map ((P.glueSeam O).leftIncl (P.glueOuterDart O)))
        (by rw [List.length_map, invDarts_length]) m A.length
        (by rw [List.length_map, invDarts_length, CyclicArc.darts_length]; omega),
      List.length_map, invDarts_length, CyclicArc.darts_length, ← List.map_drop, ← List.map_take,
      hwinX]
  let B : CyclicArc (outerDarts (P.componentDiagram O hplanar)) :=
    ⟨⟨arc.start.1 + m, by omega⟩, A.length, by omega⟩
  have hBd : B.darts =
      ((outerDarts (P.componentDiagram O hplanar)).drop (arc.start.1 + m)).take A.length :=
    CyclicArc.darts_eq_drop_take B rfl (by show arc.start.1 + m + A.length ≤ _; omega)
  have hcomp : ∀ x ∈ A.darts, (P.glueSeam O).glueMap.componentOf (P.glueOuterDart O)
      ((P.glueSeam O).glueEmbedding x) := by
    intro x hx
    have hmem : (P.glueSeam O).glueEmbedding x ∈ A.darts.map (P.glueSeam O).glueEmbedding :=
      List.mem_map_of_mem hx
    rw [hGm, List.mem_map] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    rw [List.mem_reverse, List.mem_map] at hy
    obtain ⟨d, hd, rfl⟩ := hy
    rw [← hyx]
    exact ((P.glueSeam O).glueMap.componentOf_alpha _ _).mpr
      (P.componentOf_leftIncl_of_outer O (((Delta.faceBoundary Delta.outerFace).mem_iff d).mp
        (List.mem_of_mem_drop (List.mem_of_mem_take hd))))
  refine ⟨B, Nat.le_add_right _ _, by show arc.start.1 + m + A.length ≤ _; omega, ?_⟩
  have hstep : (((((Delta.faceBoundary Delta.outerFace).darts.map
        ((P.glueSeam O).leftIncl (P.glueOuterDart O))).drop
          (((Delta.faceBoundary Delta.outerFace).darts.map
            ((P.glueSeam O).leftIncl (P.glueOuterDart O))).length - (arc.start.1 + m) -
              A.length)).take A.length).reverse.map (P.glueSeam O).glueMap.alpha) =
      ((((Delta.faceBoundary Delta.outerFace).darts.drop
        ((Delta.faceBoundary Delta.outerFace).darts.length - (arc.start.1 + m) - A.length)).take
          A.length).map ((P.glueSeam O).leftIncl (P.glueOuterDart O))).reverse.map
            (P.glueSeam O).glueMap.alpha := by
    rw [List.length_map, List.map_take, List.map_drop]
  have key : B.darts.map Subtype.val = (A.darts.map (P.componentDart O hplanar)).map Subtype.val :=
    (congrArg (List.map Subtype.val) hBd).trans
      ((List.map_take (f := Subtype.val)).trans ((congrArg (List.take A.length)
        (List.map_drop (f := Subtype.val))).trans
        ((congrArg (fun L => (L.drop (arc.start.1 + m)).take A.length)
          (P.componentOuterDarts_val O hplanar)).trans
          ((reverse_map_drop_take _ _ _ _ (by rw [List.length_map]; omega)).trans
            (hstep.trans (hGm.symm.trans ((List.map_congr_left fun x hx =>
                (P.componentDart_val O hplanar (hcomp x hx)).symm).trans
                  (List.map_map (f := P.componentDart O hplanar) (g := Subtype.val)).symm)))))))
  exact List.map_injective_iff.mpr Subtype.val_injective key

end PocketRegion

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.reverse_map_window
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.exists_componentLeftCell
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.componentCellArc_boundaryDarts
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.exists_component_outerArc_within
