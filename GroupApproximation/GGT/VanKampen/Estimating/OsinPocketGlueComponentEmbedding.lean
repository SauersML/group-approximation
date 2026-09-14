import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketGlueComponentDiagram
import GroupApproximation.GGT.VanKampen.Estimating.DiscEmbeddingOn
import GroupApproximation.Meta.AxiomGuard

/-!
# Regions of the copy on the exterior component

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): regions of copies of `Γ_1` glue back into
regions of copies of `Δ`.

Let `P` be a pocket region of a least-area diagram `Δ` and `Ξ` an O-equivalent copy of the pocket
diagram, glued into the complement of `P`.  The exterior component of the glued map is a disc
diagram O-equivalent to `Δ` (`PocketRegion.componentOEquivalent`).  A region of `Ξ` whose source arc
is nonempty lies on that component: its source cell is a relator face, and the region is joined to
it along the boundary cycle.  So the region embeds into the component.

* `Embedded.FaceSetBoundary.forall_of_mem_cycle`: a predicate carried by edges and face rotations
  that holds at one dart of the boundary cycle of a face set holds on the whole face set.
* `PocketRegion.componentDart`, `PocketRegion.componentFace`: darts and faces of the copy in the
  exterior component.
* `PocketRegion.componentEmbedding`: a face set of the copy on the component embeds into it.
* `PocketRegion.componentOf_of_region`: a region with a nonempty source arc lies on the component.
* `PocketRegion.exists_componentCell`: a relator cell of the copy is a relator cell of the
  component with the image carrier.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, through Osin's Lemma 9.7(b)); certifies no printed
sentence on its own.
-/

noncomputable section

namespace GroupApproximation.GGT.VanKampen

open Embedded HullSC Surgery.MapCollapse Surgery.PocketGlue

universe u w v

/-- The component of a dart is closed under the face rotation. -/
theorem CombMap.componentOf_facePerm (M : CombMap.{v}) (x y : M.Dart) :
    M.componentOf x (M.facePerm y) ↔ M.componentOf x y :=
  (M.componentOf_sigma x (M.alpha y)).trans (M.componentOf_alpha x y)

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

namespace Embedded.FaceSetBoundary

variable {Delta : DiscDiagram.{u, w, v} W} {s : Finset Delta.toCombMap.Face}

/-- **A predicate carried by edges and face rotations holds on a face set from one boundary
dart.**  Let `Q` be invariant under `alpha` and under the face rotation off the outer face.  If `Q`
holds at a dart of the boundary cycle of `s`, it holds at every dart of `s`. -/
theorem forall_of_mem_cycle (B : FaceSetBoundary Delta s) (Q : Delta.toCombMap.Dart → Prop)
    (hα : ∀ d, Q (Delta.toCombMap.alpha d) ↔ Q d)
    (hf : ∀ d, Delta.toCombMap.faceOf d ≠ Delta.outerFace →
      (Q (Delta.toCombMap.facePerm d) ↔ Q d))
    (hanchor : ∃ a ∈ B.cycle, Q a) : ∀ d, Delta.toCombMap.faceOf d ∈ s → Q d := by
  have hne : ∀ d, Delta.toCombMap.faceOf d ∈ s → Delta.toCombMap.faceOf d ≠ Delta.outerFace :=
    fun d hd => (B.all_gCells _ hd).1
  -- `Q` is constant along the boundary cycle.
  have hstep : ∀ d e, BoundaryStep Delta s d e → (Q d ↔ Q e) := by
    intro d e hde
    obtain ⟨hdb, -, hrt⟩ := hde
    refine (hf d (hne d hdb.1)).symm.trans ?_
    induction hrt with
    | refl => exact Iff.rfl
    | tail _ hm ih =>
      obtain ⟨-, hm2, rfl⟩ := hm
      exact ih.trans ((hα _).symm.trans (hf _ (hne _ hm2)).symm)
  have hcycle : ∀ d ∈ B.cycle, Q d ↔ Q (B.cycle.head B.cycle_nonempty) :=
    List.IsChain.induction (fun d => Q d ↔ Q (B.cycle.head B.cycle_nonempty)) B.cycle
      B.cycle_chain (fun _ _ hxy hx => (hstep _ _ hxy).symm.trans hx) (fun _ => Iff.rfl)
  obtain ⟨a, ha, hQa⟩ := hanchor
  have hQcycle : ∀ d ∈ B.cycle, Q d := fun d hd => (hcycle d hd).mpr ((hcycle a ha).mp hQa)
  intro d hd
  by_contra hQ
  have hNα : ∀ x, (Delta.toCombMap.faceOf x ∈ s ∧ ¬ Q x) →
      (Delta.toCombMap.faceOf (Delta.toCombMap.alpha x) ∈ s ∧ ¬ Q (Delta.toCombMap.alpha x)) := by
    intro x hx
    refine ⟨?_, fun h => hx.2 ((hα x).mp h)⟩
    by_contra hax
    exact hx.2 (hQcycle x ((B.cycle_mem_iff x).mpr ⟨hx.1, hax⟩))
  have hNalpha : ∀ x, (Delta.toCombMap.faceOf (Delta.toCombMap.alpha x) ∈ s ∧
      ¬ Q (Delta.toCombMap.alpha x)) ↔ (Delta.toCombMap.faceOf x ∈ s ∧ ¬ Q x) := by
    intro x
    refine ⟨fun h => ?_, hNα x⟩
    have h2 := hNα _ h
    rwa [Delta.toCombMap.alpha_involutive x] at h2
  have hNface : ∀ x, (Delta.toCombMap.faceOf (Delta.toCombMap.facePerm x) ∈ s ∧
      ¬ Q (Delta.toCombMap.facePerm x)) ↔ (Delta.toCombMap.faceOf x ∈ s ∧ ¬ Q x) := by
    intro x
    rw [Delta.toCombMap.faceOf_facePerm]
    constructor
    · rintro ⟨hx, hq⟩
      exact ⟨hx, fun h => hq ((hf x (hne x hx)).mpr h)⟩
    · rintro ⟨hx, hq⟩
      exact ⟨hx, fun h => hq ((hf x (hne x hx)).mp h)⟩
  have hNsigma : ∀ x, (Delta.toCombMap.faceOf (Delta.toCombMap.sigma x) ∈ s ∧
      ¬ Q (Delta.toCombMap.sigma x)) ↔ (Delta.toCombMap.faceOf x ∈ s ∧ ¬ Q x) := by
    intro x
    have hσ : Delta.toCombMap.sigma x =
        Delta.toCombMap.facePerm (Delta.toCombMap.alpha x) := by
      change _ = Delta.toCombMap.sigma (Delta.toCombMap.alpha (Delta.toCombMap.alpha x))
      rw [Delta.toCombMap.alpha_involutive x]
    rw [hσ]
    exact (hNface _).trans (hNalpha x)
  have hinv : ∀ a b, Relation.EqvGen Delta.toCombMap.Adjacent a b →
      ((Delta.toCombMap.faceOf a ∈ s ∧ ¬ Q a) ↔ (Delta.toCombMap.faceOf b ∈ s ∧ ¬ Q b)) := by
    intro a b hab
    induction hab with
    | rel a b hr =>
      rcases hr with rfl | rfl
      · exact (hNalpha a).symm
      · exact (hNsigma a).symm
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ (Delta.faceBoundary Delta.outerFace).nonempty
  have hNy := (hinv d y (Delta.planar.1 d y)).mp ⟨hd, hQ⟩
  exact (B.all_gCells _ hNy.1).1 (((Delta.faceBoundary Delta.outerFace).mem_iff y).mp hy)

end Embedded.FaceSetBoundary

namespace PocketRegion

variable {Delta : DiscDiagram.{u, w, v} W} (P : PocketRegion Delta) {Xi : DiscDiagram.{u, w, v} W}

open scoped Classical in
/-- A dart of the copy as a dart of the exterior component: its glued image when that lies on the
component, and the exterior dart otherwise. -/
def componentDart (O : OEquivalentDiscDiagram P.diagram Xi)
    (hplanar : ((P.glueSeam O).glueMap.component (P.glueOuterDart O)).IsPlanar)
    (x : Xi.toCombMap.Dart) : (P.componentDiagram O hplanar).toCombMap.Dart :=
  if hx : (P.glueSeam O).glueMap.componentOf (P.glueOuterDart O) ((P.glueSeam O).glueEmbedding x)
  then (⟨(P.glueSeam O).glueEmbedding x, hx⟩ :
    {g // (P.glueSeam O).glueMap.componentOf (P.glueOuterDart O) g})
  else (⟨P.glueOuterDart O, (P.glueSeam O).glueMap.componentOf_self _⟩ :
    {g // (P.glueSeam O).glueMap.componentOf (P.glueOuterDart O) g})

theorem componentDart_val (O : OEquivalentDiscDiagram P.diagram Xi)
    (hplanar : ((P.glueSeam O).glueMap.component (P.glueOuterDart O)).IsPlanar)
    {x : Xi.toCombMap.Dart}
    (hx : (P.glueSeam O).glueMap.componentOf (P.glueOuterDart O)
      ((P.glueSeam O).glueEmbedding x)) :
    Subtype.val (P.componentDart O hplanar x) = (P.glueSeam O).glueEmbedding x := by
  unfold componentDart
  rw [dif_pos hx]

/-- A face of the copy as a face of the exterior component, through a representative dart. -/
def componentFace (O : OEquivalentDiscDiagram P.diagram Xi)
    (hplanar : ((P.glueSeam O).glueMap.component (P.glueOuterDart O)).IsPlanar)
    (h : Xi.toCombMap.Face) : (P.componentDiagram O hplanar).toCombMap.Face :=
  (P.componentDiagram O hplanar).toCombMap.faceOf (P.componentDart O hplanar (Quotient.out h))

theorem restrictFace_componentFace (O : OEquivalentDiscDiagram P.diagram Xi)
    (hplanar : ((P.glueSeam O).glueMap.component (P.glueOuterDart O)).IsPlanar)
    {h : Xi.toCombMap.Face} (hh : h ≠ Xi.outerFace)
    (hdom : (P.glueSeam O).glueMap.componentOf (P.glueOuterDart O)
      ((P.glueSeam O).glueEmbedding (Quotient.out h))) :
    (P.glueSeam O).glueMap.restrictFace ((P.glueSeam O).glueMap.componentOf (P.glueOuterDart O))
        ((P.glueSeam O).glueMap.componentOf_alpha (P.glueOuterDart O))
        ((P.glueSeam O).glueMap.componentOf_sigma (P.glueOuterDart O))
        (P.componentFace O hplanar h) = (P.glueSeam O).rightFace ⟨h, hh⟩ := by
  have hout : Xi.toCombMap.faceOf (Quotient.out h) = h := Quotient.out_eq h
  have hne : Xi.toCombMap.faceOf (Quotient.out h) ≠ (P.glueSeam O).outer :=
    fun heq => hh (hout.symm.trans heq)
  change (P.glueSeam O).glueMap.faceOf
    (Subtype.val (P.componentDart O hplanar (Quotient.out h))) = _
  rw [P.componentDart_val O hplanar hdom, (P.glueSeam O).glueEmbedding_of_ne _ hne,
    (P.glueSeam O).faceOf_inr]
  exact congrArg (P.glueSeam O).rightFace (Subtype.ext hout)

theorem componentFace_boundary (O : OEquivalentDiscDiagram P.diagram Xi)
    (hplanar : ((P.glueSeam O).glueMap.component (P.glueOuterDart O)).IsPlanar)
    {h : Xi.toCombMap.Face} (hh : h ≠ Xi.outerFace)
    (hdom : ∀ x, Xi.toCombMap.faceOf x = h → (P.glueSeam O).glueMap.componentOf
      (P.glueOuterDart O) ((P.glueSeam O).glueEmbedding x)) :
    ((P.componentDiagram O hplanar).faceBoundary (P.componentFace O hplanar h)).darts =
      (Xi.faceBoundary h).darts.map (P.componentDart O hplanar) := by
  have key : ((P.componentDiagram O hplanar).faceBoundary
        (P.componentFace O hplanar h)).darts.map Subtype.val =
      ((Xi.faceBoundary h).darts.map (P.componentDart O hplanar)).map Subtype.val := by
    refine ((P.glueSeam O).glueMap.restrictFaceBoundary_darts _ _ _
      ((P.glueSeam O).glueFaceBoundary Delta.faceBoundary Xi.faceBoundary) _).trans ?_
    rw [P.restrictFace_componentFace O hplanar hh (hdom _ (Quotient.out_eq h)),
      (P.glueSeam O).glueFaceBoundary_rightFace_darts]
    refine (List.map_congr_left fun x hx => ?_).trans
      (List.map_map (f := P.componentDart O hplanar) (g := Subtype.val)
        (l := (Xi.faceBoundary h).darts)).symm
    exact (P.componentDart_val O hplanar (hdom x (((Xi.faceBoundary h).mem_iff x).mp hx))).symm
  exact List.map_injective_iff.mpr Subtype.val_injective key

/-- **A face set of the copy on the exterior component embeds into it.** -/
def componentEmbedding (O : OEquivalentDiscDiagram P.diagram Xi)
    (hplanar : ((P.glueSeam O).glueMap.component (P.glueOuterDart O)).IsPlanar)
    {s : Finset Xi.toCombMap.Face} (hout : Xi.outerFace ∉ s)
    (hs : ∀ x, Xi.toCombMap.faceOf x ∈ s →
      (P.glueSeam O).glueMap.componentOf (P.glueOuterDart O) ((P.glueSeam O).glueEmbedding x)) :
    DiscEmbeddingOn Xi (P.componentDiagram O hplanar) s where
  darts := P.componentDart O hplanar
  faces := P.componentFace O hplanar
  domain x :=
    (P.glueSeam O).glueMap.componentOf (P.glueOuterDart O) ((P.glueSeam O).glueEmbedding x)
  domain_of_mem := hs
  domain_alpha x hx := by
    rw [← (P.glueSeam O).glueAlpha_glueEmbedding]
    exact ((P.glueSeam O).glueMap.componentOf_alpha _ _).mpr hx
  injective x y hx hy hxy := (P.glueSeam O).glueEmbedding.injective
    ((P.componentDart_val O hplanar hx).symm.trans
      ((congrArg Subtype.val hxy).trans (P.componentDart_val O hplanar hy)))
  alpha x hx := by
    have hαx : (P.glueSeam O).glueMap.componentOf (P.glueOuterDart O)
        ((P.glueSeam O).glueEmbedding (Xi.toCombMap.alpha x)) := by
      rw [← (P.glueSeam O).glueAlpha_glueEmbedding]
      exact ((P.glueSeam O).glueMap.componentOf_alpha _ _).mpr hx
    exact Subtype.ext (((congrArg (P.glueSeam O).glueAlpha (P.componentDart_val O hplanar hx)).trans
      ((P.glueSeam O).glueAlpha_glueEmbedding x)).trans (P.componentDart_val O hplanar hαx).symm)
  label x hx :=
    (congrArg ((P.glueSeam O).glueLabel Delta.label Xi.label) (P.componentDart_val O hplanar hx)).trans
      ((P.glueSeam O).glueLabel_glueEmbedding Delta.label Xi.label (P.glueSeam_label O) x)
  facePerm x hx := by
    have hne : Xi.toCombMap.faceOf x ≠ (P.glueSeam O).outer := by
      intro heq
      have h2 := hx
      rw [heq] at h2
      exact hout h2
    have hfx : (P.glueSeam O).glueMap.componentOf (P.glueOuterDart O)
        ((P.glueSeam O).glueEmbedding (Xi.toCombMap.facePerm x)) :=
      hs _ (by rw [Xi.toCombMap.faceOf_facePerm]; exact hx)
    exact Subtype.ext (((congrArg (P.glueSeam O).glueMap.facePerm
      (P.componentDart_val O hplanar (hs x hx))).trans
        ((P.glueSeam O).glueMap_facePerm_glueEmbedding x hne)).trans
      (P.componentDart_val O hplanar hfx).symm)
  faces_ne_outer h hh := by
    have hne : h ≠ Xi.outerFace := fun heq => hout (heq ▸ hh)
    have hdom : (P.glueSeam O).glueMap.componentOf (P.glueOuterDart O)
        ((P.glueSeam O).glueEmbedding (Quotient.out h)) :=
      hs _ (by rw [show Xi.toCombMap.faceOf (Quotient.out h) = h from Quotient.out_eq h]; exact hh)
    intro heq
    have h1 := congrArg ((P.glueSeam O).glueMap.restrictFace
      ((P.glueSeam O).glueMap.componentOf (P.glueOuterDart O))
      ((P.glueSeam O).glueMap.componentOf_alpha (P.glueOuterDart O))
      ((P.glueSeam O).glueMap.componentOf_sigma (P.glueOuterDart O))) heq
    rw [P.restrictFace_componentFace O hplanar hne hdom] at h1
    change _ = (P.glueSeam O).glueMap.faceOf (P.glueOuterDart O) at h1
    rw [P.glueMap_faceOf_glueOuterDart O] at h1
    exact (P.glueSeam O).leftFace_ne_rightFace _ _ h1.symm
  face_boundary h hh :=
    P.componentFace_boundary O hplanar (fun heq => hout (heq ▸ hh)) (fun x hx => hs x (hx ▸ hh))

/-- At least area, a dart of a relator face of the copy lies on the exterior component. -/
theorem componentOf_glueEmbedding_of_face_mem (O : OEquivalentDiscDiagram P.diagram Xi)
    (hplanar : ((P.glueSeam O).glueMap.component (P.glueOuterDart O)).IsPlanar)
    (hlea : Delta.LeastArea) {h : Xi.toCombMap.Face}
    (hh : h ∈ Xi.relatorCells.map RelatorCell.face) {x : Xi.toCombMap.Dart}
    (hx : Xi.toCombMap.faceOf x = h) :
    (P.glueSeam O).glueMap.componentOf (P.glueOuterDart O) ((P.glueSeam O).glueEmbedding x) := by
  obtain ⟨y, hy, hyF⟩ := P.exists_componentOf_of_mem_glueRelFaces O hplanar hlea
    (P.glueRight_mem_glueRelFaces O hh)
  have hne : Xi.toCombMap.faceOf x ≠ (P.glueSeam O).outer :=
    fun heq => DiscDiagram.relFace_ne_outerFace hh (hx.symm.trans heq)
  refine (P.glueSeam O).glueMap.mem_of_faceOf_eq _
    ((P.glueSeam O).glueMap.componentOf_alpha _) ((P.glueSeam O).glueMap.componentOf_sigma _)
    hy ?_
  rw [hyF, (P.glueSeam O).glueEmbedding_of_ne x hne, (P.glueSeam O).faceOf_inr]
  exact congrArg (P.glueSeam O).rightFace (Subtype.ext hx)

/-- **At least area, a region of the copy with a nonempty source arc lies on the exterior
component.** -/
theorem componentOf_of_region (O : OEquivalentDiscDiagram P.diagram Xi)
    (hplanar : ((P.glueSeam O).glueMap.component (P.glueOuterDart O)).IsPlanar)
    (hlea : Delta.LeastArea) {D : RelGenSet G Lambda} {eps : ℕ} {s : Finset Xi.toCombMap.Face}
    (H : ContiguityGeometry D eps Xi s) (hsrc : H.sourceArc.length ≠ 0) :
    ∀ x, Xi.toCombMap.faceOf x ∈ s →
      (P.glueSeam O).glueMap.componentOf (P.glueOuterDart O) ((P.glueSeam O).glueEmbedding x) := by
  refine H.boundary.forall_of_mem_cycle _ (fun d => ?_) (fun d hd => ?_) ?_
  · rw [← (P.glueSeam O).glueAlpha_glueEmbedding]
    exact (P.glueSeam O).glueMap.componentOf_alpha _ _
  · rw [← (P.glueSeam O).glueMap_facePerm_glueEmbedding d hd]
    exact (P.glueSeam O).glueMap.componentOf_facePerm _ _
  · have hne : H.sourceArc.darts ≠ [] :=
      List.ne_nil_of_length_pos (by rw [H.sourceArc.darts_length]; omega)
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hne
    have hcmem : c ∈ cellDarts Xi H.source := H.sourceArc.mem_cycle_of_mem_darts hc
    have hcface : Xi.toCombMap.faceOf c = (cell Xi H.source).face :=
      ((Xi.faceBoundary (cell Xi H.source).face).mem_iff c).mp hcmem
    refine ⟨Xi.toCombMap.alpha c, ?_, ?_⟩
    · rw [H.boundary_decomposition]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map_of_mem (List.mem_reverse.mpr hc))))
    · rw [← (P.glueSeam O).glueAlpha_glueEmbedding]
      exact ((P.glueSeam O).glueMap.componentOf_alpha _ _).mpr
        (P.componentOf_glueEmbedding_of_face_mem O hplanar hlea
          (List.mem_map_of_mem (cell_mem Xi H.source)) hcface)

/-- **At least area, a relator cell of the copy is a relator cell of the exterior component**, with
the image carrier. -/
theorem exists_componentCell (O : OEquivalentDiscDiagram P.diagram Xi)
    (hplanar : ((P.glueSeam O).glueMap.component (P.glueOuterDart O)).IsPlanar)
    (hlea : Delta.LeastArea) (i : Fin Xi.rCellCount) :
    ∃ j : Fin (P.componentDiagram O hplanar).rCellCount,
      cellDarts (P.componentDiagram O hplanar) j =
        (cellDarts Xi i).map (P.componentDart O hplanar) := by
  have hmemX : (cell Xi i).face ∈ Xi.relatorCells.map RelatorCell.face :=
    List.mem_map_of_mem (cell_mem Xi i)
  have hne := DiscDiagram.relFace_ne_outerFace hmemX
  have hdom : ∀ x, Xi.toCombMap.faceOf x = (cell Xi i).face →
      (P.glueSeam O).glueMap.componentOf (P.glueOuterDart O) ((P.glueSeam O).glueEmbedding x) :=
    fun x hx => P.componentOf_glueEmbedding_of_face_mem O hplanar hlea hmemX hx
  have hmem : P.componentFace O hplanar (cell Xi i).face ∈
      (P.componentDiagram O hplanar).relatorCells.map RelatorCell.face := by
    rw [P.componentDiagram_face_mem_iff O hplanar,
      P.restrictFace_componentFace O hplanar hne (hdom _ (Quotient.out_eq _))]
    exact P.glueRight_mem_glueRelFaces O hmemX
  obtain ⟨C', hC', hCF⟩ := List.mem_map.1 hmem
  obtain ⟨n, hn⟩ := List.get_of_mem hC'
  refine ⟨n, ?_⟩
  have hface : (cell (P.componentDiagram O hplanar) n).face =
      P.componentFace O hplanar (cell Xi i).face :=
    (congrArg RelatorCell.face hn).trans hCF
  exact (congrArg (fun F => ((P.componentDiagram O hplanar).faceBoundary F).darts) hface).trans
    (P.componentFace_boundary O hplanar hne hdom)

end PocketRegion

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.FaceSetBoundary.forall_of_mem_cycle
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.componentEmbedding
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.componentOf_of_region
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.exists_componentCell
