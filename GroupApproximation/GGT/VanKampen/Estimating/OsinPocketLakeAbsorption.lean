import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPieces
import GroupApproximation.Meta.AxiomGuard

/-!
# Filling the lakes of a pocket face set

Osin, arXiv:math/0411039v3, proof of Lemma 9.7(b):

> "Let us consider the subdiagram `Γ_1` of `Δ` such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2`, where
> `s_1, s_2` are side arcs of some of `Γ_{i,1}`'s and `t_1, t_2` are subpaths of `∂Π` and the
> section `q_1` of `∂Δ`, respectively; (ii) `Γ_1` contains all `Γ_{i,1}`'s."

The faces outside a face set fall into pieces.  Two faces lie in one piece when a chain of moves
around a face, and of crossings of edges off the boundary of the face set, joins them.  The piece
of the exterior face is the exterior piece, and the other pieces are lakes, enclosed by the face
set.  Filling the lakes gives the face set of all faces outside the exterior piece.  Its boundary
darts are the old boundary darts whose reversal faces the exterior piece.  When the source cell
`Π` faces the exterior piece, a pocket face set keeps its cells, arcs and positions after the
filling, and its sides become subsets `s_1' ⊆ s_1` and `s_2' ⊆ s_2`.  With letters for labels the
norm of a side is at most its length, so the new sides keep their bounds.

* `ExteriorComponent.component`, `ExteriorComponent.absorbed`: the piece of a face, and the face
  set with every face outside that piece.
* `ExteriorComponent.faceOf_mem_iff_of_eqvGen`: a move inside a piece stays inside or outside
  the face set.
* `ExteriorComponent.isBoundaryDart_absorbed_iff`: the boundary darts after filling are the old
  boundary darts facing the piece of the exterior face.
* `PocketFaceSet.wordNorm_dartWord_le_length`: with letters for labels, the norm of a list of
  darts is at most its length.
* `PocketFaceSet.absorb`: the pocket face set with its lakes filled.

The walk order of the new boundary cycle is not proved here.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded HullSC WordMetric
open scoped Classical

namespace Surgery.MapCollapse.ExteriorComponent

variable (M : CombMap.{v}) (faces : Finset M.Face)

/-- The darts on an edge of the boundary of a face set. -/
def BoundaryEdge (x : M.Dart) : Prop :=
  IsBoundaryDart M faces x ∨ IsBoundaryDart M faces (M.alpha x)

/-- The darts reached from the face `o` by moving around faces and crossing edges off the
boundary of the face set. -/
def Reach (o : M.Face) (y : M.Dart) : Prop :=
  ∃ x, M.faceOf x = o ∧ Relation.EqvGen (CombMap.FaceClassStep M (BoundaryEdge M faces)) x y

/-- **The piece of a face**: the faces reached from `o` without crossing the boundary of the face
set. -/
noncomputable def component (o : M.Face) : Finset M.Face :=
  Finset.univ.filter fun f => ∃ y, M.faceOf y = f ∧ Reach M faces o y

/-- **The face set with its lakes filled**: every face outside the piece of `o`. -/
noncomputable def absorbed (o : M.Face) : Finset M.Face :=
  Finset.univ.filter fun f => f ∉ component M faces o

variable {M faces}

theorem mem_component_iff {o f : M.Face} :
    f ∈ component M faces o ↔ ∃ y, M.faceOf y = f ∧ Reach M faces o y := by
  unfold component
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ f)

theorem mem_absorbed_iff {o f : M.Face} :
    f ∈ absorbed M faces o ↔ f ∉ component M faces o := by
  unfold absorbed
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ f)

/-- **A move inside a piece stays inside or outside the face set.**  Moving around a face keeps
the face, and an edge off the boundary has both of its faces inside or both outside. -/
theorem faceOf_mem_iff_of_eqvGen {x y : M.Dart}
    (h : Relation.EqvGen (CombMap.FaceClassStep M (BoundaryEdge M faces)) x y) :
    M.faceOf x ∈ faces ↔ M.faceOf y ∈ faces := by
  induction h with
  | rel x₁ x₂ hx =>
      rcases hx with rfl | ⟨hoff, rfl⟩
      · rw [M.faceOf_facePerm]
      · constructor
        · intro hin
          by_contra hout
          exact hoff (show IsBoundaryDart M faces x₁ ∨ IsBoundaryDart M faces (M.alpha x₁) from
            Or.inl (show M.faceOf x₁ ∈ faces ∧ M.faceOf (M.alpha x₁) ∉ faces from ⟨hin, hout⟩))
        · intro hin
          by_contra hout
          have hout' : M.faceOf (M.alpha (M.alpha x₁)) ∉ faces := by
            rw [M.alpha_involutive x₁]
            exact hout
          exact hoff (show IsBoundaryDart M faces x₁ ∨ IsBoundaryDart M faces (M.alpha x₁) from
            Or.inr (show M.faceOf (M.alpha x₁) ∈ faces ∧
              M.faceOf (M.alpha (M.alpha x₁)) ∉ faces from ⟨hin, hout'⟩))
  | refl _ => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The reach of a face passes to every dart of a reached face. -/
theorem Reach.of_faceOf_eq {o : M.Face} {y y' : M.Dart} (hy : Reach M faces o y)
    (hyy' : M.faceOf y = M.faceOf y') : Reach M faces o y' := by
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨x, hx, Relation.EqvGen.trans _ _ _ hxy
    (SimpleClosedWalkSides.eqvGen_faceClass_of_sameCycle M _ ((M.faceOf_eq_iff y y').mp hyy'))⟩

/-- The reach of a face crosses every edge off the boundary. -/
theorem Reach.alpha {o : M.Face} {y : M.Dart} (hy : Reach M faces o y)
    (hoff : ¬ BoundaryEdge M faces y) : Reach M faces o (M.alpha y) := by
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨x, hx, Relation.EqvGen.trans _ _ _ hxy (Relation.EqvGen.rel _ _ (Or.inr ⟨hoff, rfl⟩))⟩

/-- A face lies in its own piece. -/
theorem self_mem_component (o : M.Face) : o ∈ component M faces o := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep o
  exact mem_component_iff.mpr ⟨x, rfl, x, rfl, Relation.EqvGen.refl x⟩

/-- **The piece of a face outside the face set lies outside the face set.** -/
theorem not_mem_of_mem_component {o f : M.Face} (ho : o ∉ faces)
    (hf : f ∈ component M faces o) : f ∉ faces := by
  obtain ⟨y, rfl, x, hx, hxy⟩ := mem_component_iff.mp hf
  rw [← faceOf_mem_iff_of_eqvGen hxy, hx]
  exact ho

/-- Filling the lakes keeps the face set. -/
theorem subset_absorbed {o : M.Face} (ho : o ∉ faces) : faces ⊆ absorbed M faces o :=
  fun _ hf => mem_absorbed_iff.mpr fun hc => not_mem_of_mem_component ho hc hf

/-- **The boundary darts after filling the lakes** are the old boundary darts whose reversal
faces the piece of `o`. -/
theorem isBoundaryDart_absorbed_iff {o : M.Face} (ho : o ∉ faces) (d : M.Dart) :
    IsBoundaryDart M (absorbed M faces o) d ↔
      IsBoundaryDart M faces d ∧ M.faceOf (M.alpha d) ∈ component M faces o := by
  have hunfold : IsBoundaryDart M (absorbed M faces o) d ↔
      M.faceOf d ∉ component M faces o ∧ M.faceOf (M.alpha d) ∈ component M faces o := by
    unfold IsBoundaryDart
    rw [mem_absorbed_iff, mem_absorbed_iff, not_not]
  rw [hunfold]
  constructor
  · rintro ⟨hd, hα⟩
    refine ⟨show M.faceOf d ∈ faces ∧ M.faceOf (M.alpha d) ∉ faces from
      ⟨?_, not_mem_of_mem_component ho hα⟩, hα⟩
    by_contra hout
    apply hd
    obtain ⟨y, hy, hreach⟩ := mem_component_iff.mp hα
    have hoff : ¬ BoundaryEdge M faces (M.alpha d) := by
      intro hb
      rcases hb with hb | hb
      · have hb' : M.faceOf (M.alpha d) ∈ faces ∧ M.faceOf (M.alpha (M.alpha d)) ∉ faces := hb
        exact not_mem_of_mem_component ho hα hb'.1
      · have hb' : M.faceOf (M.alpha (M.alpha d)) ∈ faces ∧
            M.faceOf (M.alpha (M.alpha (M.alpha d))) ∉ faces := hb
        rw [M.alpha_involutive d] at hb'
        exact hout hb'.1
    have hd' := (hreach.of_faceOf_eq hy).alpha hoff
    rw [M.alpha_involutive d] at hd'
    exact mem_component_iff.mpr ⟨d, rfl, hd'⟩
  · rintro ⟨hb, hα⟩
    have hb' : M.faceOf d ∈ faces ∧ M.faceOf (M.alpha d) ∉ faces := hb
    exact ⟨fun hc => not_mem_of_mem_component ho hc hb'.1, hα⟩

end Surgery.MapCollapse.ExteriorComponent

open Surgery.MapCollapse Surgery.MapCollapse.ExteriorComponent

namespace PocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **With letters for labels, the norm of a list of darts is at most its length.** -/
theorem wordNorm_dartWord_le_length
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) (s : List X.toCombMap.Dart) :
    wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X s)) ≤ s.length := by
  rw [← symmetricLabelAlphabet.wordNorm_eq D]
  have hval : ∀ a : RelLetter G Lambda, (symmetricLabelAlphabet D).IsLetter a →
      a.val ∈ (symmetricLabelAlphabet D).alphabet.carrier := by
    intro a ha
    cases a with
    | base x => exact Set.mem_union_left _ ha
    | comp lam y => exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨lam, ha⟩)
  have hword : IsWord (symmetricLabelAlphabet D).alphabet.carrier
      ((dartWord X s).map RelLetter.val) (RelLetter.listVal (dartWord X s)) := by
    refine ⟨?_, rfl⟩
    intro g hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp ha
    exact hval (X.label d) (hlabel d)
  calc wordNorm (symmetricLabelAlphabet D).alphabet.carrier (RelLetter.listVal (dartWord X s))
      ≤ ((dartWord X s).map RelLetter.val).length := wordNorm_le_length hword
    _ = s.length := by simp only [dartWord, List.length_map]

theorem nodup_first {α : Type*} {s₁ a s₂ b : List α} (h : (s₁ ++ a ++ s₂ ++ b).Nodup) :
    s₁.Nodup :=
  List.Nodup.sublist ((List.sublist_append_left s₁ a).trans
    ((List.sublist_append_left _ s₂).trans (List.sublist_append_left _ b))) h

theorem nodup_second {α : Type*} {s₁ a s₂ b : List α} (h : (s₁ ++ a ++ s₂ ++ b).Nodup) :
    s₂.Nodup :=
  List.Nodup.sublist ((List.sublist_append_right (s₁ ++ a) s₂).trans
    (List.sublist_append_left _ b)) h

/-- **The pocket face set with its lakes filled.**  When the source cell faces the piece of the
exterior face, filling the lakes keeps the cells, the arcs and the positions.  The boundary cycle
lists the old boundary darts facing the exterior piece, as sides `s₁ ⊆ s_1` and `s₂ ⊆ s_2` around
the same arcs.  With letters for labels the sides keep their bounds. -/
noncomputable def absorb (K : PocketFaceSet D eps X lo hi)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (hsource : (cell X K.source).face ∈ component X.toCombMap K.faces X.outerFace)
    (s₁ s₂ : List X.toCombMap.Dart) (hs₁ : s₁ ⊆ K.firstSide) (hs₂ : s₂ ⊆ K.secondSide)
    (hne : s₁ ++ invDarts X K.sourceArc.darts ++ s₂ ++ K.targetArc.darts ≠ [])
    (hnodup : (s₁ ++ invDarts X K.sourceArc.darts ++ s₂ ++ K.targetArc.darts).Nodup)
    (hmem : ∀ d, d ∈ s₁ ++ invDarts X K.sourceArc.darts ++ s₂ ++ K.targetArc.darts ↔
      IsBoundaryDart X.toCombMap K.faces d ∧
        X.toCombMap.faceOf (X.toCombMap.alpha d) ∈
          component X.toCombMap K.faces X.outerFace) :
    PocketFaceSet D eps X lo hi where
  faces := absorbed X.toCombMap K.faces X.outerFace
  outerFace_not_mem := fun h => mem_absorbed_iff.mp h (self_mem_component _)
  source := K.source
  source_not_mem := fun h => mem_absorbed_iff.mp h hsource
  kept := K.kept
  kept_mem := subset_absorbed K.outerFace_not_mem K.kept_mem
  sourceArc := K.sourceArc
  targetArc := K.targetArc
  firstSide := s₁
  secondSide := s₂
  boundary :=
    { cycle := s₁ ++ invDarts X K.sourceArc.darts ++ s₂ ++ K.targetArc.darts
      cycle_nonempty := hne
      cycle_nodup := hnodup
      cycle_mem_iff := fun d =>
        (hmem d).trans (isBoundaryDart_absorbed_iff K.outerFace_not_mem d).symm }
  decomposition := rfl
  firstSide_length_le :=
    (List.subperm_of_subset (nodup_first hnodup) hs₁).length_le.trans K.firstSide_length_le
  secondSide_length_le :=
    (List.subperm_of_subset (nodup_second hnodup) hs₂).length_le.trans K.secondSide_length_le
  firstSide_norm_le := (wordNorm_dartWord_le_length hlabel s₁).trans
    ((List.subperm_of_subset (nodup_first hnodup) hs₁).length_le.trans K.firstSide_length_le)
  secondSide_norm_le := (wordNorm_dartWord_le_length hlabel s₂).trans
    ((List.subperm_of_subset (nodup_second hnodup) hs₂).length_le.trans K.secondSide_length_le)
  lo_le := K.lo_le
  le_hi := K.le_hi

section Absorb

variable (K : PocketFaceSet D eps X lo hi)
  (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
  (hsource : (cell X K.source).face ∈ component X.toCombMap K.faces X.outerFace)
  (s₁ s₂ : List X.toCombMap.Dart) (hs₁ : s₁ ⊆ K.firstSide) (hs₂ : s₂ ⊆ K.secondSide)
  (hne : s₁ ++ invDarts X K.sourceArc.darts ++ s₂ ++ K.targetArc.darts ≠ [])
  (hnodup : (s₁ ++ invDarts X K.sourceArc.darts ++ s₂ ++ K.targetArc.darts).Nodup)
  (hmem : ∀ d, d ∈ s₁ ++ invDarts X K.sourceArc.darts ++ s₂ ++ K.targetArc.darts ↔
    IsBoundaryDart X.toCombMap K.faces d ∧
      X.toCombMap.faceOf (X.toCombMap.alpha d) ∈ component X.toCombMap K.faces X.outerFace)

theorem absorb_faces :
    (K.absorb hlabel hsource s₁ s₂ hs₁ hs₂ hne hnodup hmem).faces =
      absorbed X.toCombMap K.faces X.outerFace :=
  rfl

theorem faces_subset_absorb_faces :
    K.faces ⊆ (K.absorb hlabel hsource s₁ s₂ hs₁ hs₂ hne hnodup hmem).faces :=
  subset_absorbed K.outerFace_not_mem

theorem absorb_source :
    (K.absorb hlabel hsource s₁ s₂ hs₁ hs₂ hne hnodup hmem).source = K.source :=
  rfl

theorem absorb_kept :
    (K.absorb hlabel hsource s₁ s₂ hs₁ hs₂ hne hnodup hmem).kept = K.kept :=
  rfl

/-- The boundary cycle after filling the lakes. -/
theorem absorb_boundary_cycle :
    (K.absorb hlabel hsource s₁ s₂ hs₁ hs₂ hne hnodup hmem).boundary.cycle =
      s₁ ++ invDarts X K.sourceArc.darts ++ s₂ ++ K.targetArc.darts :=
  rfl

theorem absorb_firstSide :
    (K.absorb hlabel hsource s₁ s₂ hs₁ hs₂ hne hnodup hmem).firstSide = s₁ :=
  rfl

theorem absorb_secondSide :
    (K.absorb hlabel hsource s₁ s₂ hs₁ hs₂ hne hnodup hmem).secondSide = s₂ :=
  rfl

theorem absorb_sourceArc :
    (K.absorb hlabel hsource s₁ s₂ hs₁ hs₂ hne hnodup hmem).sourceArc = K.sourceArc :=
  rfl

theorem absorb_targetArc :
    (K.absorb hlabel hsource s₁ s₂ hs₁ hs₂ hne hnodup hmem).targetArc = K.targetArc :=
  rfl

end Absorb

end PocketFaceSet

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.ExteriorComponent.component
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.ExteriorComponent.absorbed
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.ExteriorComponent.mem_component_iff
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.ExteriorComponent.mem_absorbed_iff
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.ExteriorComponent.faceOf_mem_iff_of_eqvGen
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.ExteriorComponent.Reach.of_faceOf_eq
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.ExteriorComponent.Reach.alpha
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.ExteriorComponent.self_mem_component
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.ExteriorComponent.not_mem_of_mem_component
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.ExteriorComponent.subset_absorbed
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.ExteriorComponent.isBoundaryDart_absorbed_iff
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.wordNorm_dartWord_le_length
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.nodup_first
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.nodup_second
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.absorb
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.absorb_faces
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.faces_subset_absorb_faces
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.absorb_boundary_cycle
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.absorb_firstSide
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.absorb_secondSide
