import GroupApproximation.GGT.VanKampen.SurgeryPocketGlueVertices
import GroupApproximation.GGT.VanKampen.SurgeryReclosedPlanarity
import GroupApproximation.Meta.AxiomGuard

/-!
# Planarity of the glued map

The glued map is connected when `M` and `X` are.  A dart of `X` reaches the base seam dart
through `X`.  A dart of `M` on `faces` reaches a dart of `X` because reachability is invariant
along the edges and vertex rotation of `M`, and it holds at the boundary darts of `faces`, which
are darts of `outer`.  The counts of `SurgeryPocketGlueCount` and `SurgeryPocketGlueVertices`
give `χ(glueMap) = χ(M) + χ(X) - χ(piece)`, and the reclosed piece is planar along the
boundary walk (`reclosedMap_planar`).  So the glued map is planar (`Seam.glueMap_planar`).
-/

noncomputable section

namespace GroupApproximation.GGT.VanKampen.Surgery.PocketGlue

open Equiv MapCollapse

universe v

theorem eqvGen_sigma_pow (N : CombMap.{v}) (n : ℕ) (z : N.Dart) :
    Relation.EqvGen N.Adjacent z ((N.sigma ^ n) z) := by
  induction n with
  | zero =>
    rewrite [pow_zero, Perm.one_apply]
    exact Relation.EqvGen.refl _
  | succ n ih =>
    rewrite [pow_succ', Perm.mul_apply]
    exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ (Or.inr rfl))

theorem eqvGen_facePerm_self (N : CombMap.{v}) (z : N.Dart) :
    Relation.EqvGen N.Adjacent z (N.facePerm z) :=
  Relation.EqvGen.trans _ (N.alpha z) _ (Relation.EqvGen.rel _ _ (Or.inl rfl))
    (Relation.EqvGen.rel _ _ (Or.inr rfl))

namespace Seam

variable {M X : CombMap.{v}} (S : Seam M X)

theorem glueFacePerm_inl (d : {d : M.Dart // M.faceOf d ∈ S.faces}) :
    (S.glueFacePerm (Sum.inl d) : S.GlueDart) =
      Sum.inl ⟨M.facePerm d.1, by rw [CombMap.faceOf_facePerm]; exact d.2⟩ := rfl

/-- Paths of `X` are paths of the glued map. -/
theorem eqvGen_glueEmbedding (hwalk : S.boundary.FollowsBoundary) {x x' : X.Dart}
    (h : Relation.EqvGen X.Adjacent x x') :
    Relation.EqvGen S.glueMap.Adjacent (S.glueEmbedding x) (S.glueEmbedding x') := by
  induction h with
  | rel x y hxy =>
    rcases hxy with hxy | hxy
    · exact Relation.EqvGen.rel _ _ (Or.inl
        ((S.glueAlpha_glueEmbedding x).trans (congrArg (fun z => S.glueEmbedding z) hxy)))
    · subst hxy
      obtain ⟨m, -, hm, -⟩ := S.glue_sigma_firstReturn hwalk x
      have hs := eqvGen_sigma_pow S.glueMap m (S.glueEmbedding x)
      rewrite [hm] at hs
      exact hs
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- A dart of `M` reaches the image of `X` whenever it is a glued dart. -/
def Reach (d : M.Dart) : Prop :=
  ∀ hd : M.faceOf d ∈ S.faces, ∃ x : X.Dart,
    Relation.EqvGen S.glueMap.Adjacent (Sum.inl ⟨d, hd⟩ : S.GlueDart) (S.glueEmbedding x)

theorem reach_of_boundary (d : M.Dart) (hd : M.faceOf d ∈ S.faces)
    (hn : M.faceOf (M.alpha d) ∉ S.faces) : S.Reach d := by
  intro _
  refine ⟨(S.seamEquiv ⟨d, hd, hn⟩).1, ?_⟩
  rewrite [S.glueEmbedding_seam ⟨d, hd, hn⟩]
  exact Relation.EqvGen.refl _

theorem reach_alpha (d : M.Dart) : S.Reach d ↔ S.Reach (M.alpha d) := by
  by_cases hd : M.faceOf d ∈ S.faces
  · by_cases ha : M.faceOf (M.alpha d) ∈ S.faces
    · have hadj : Relation.EqvGen S.glueMap.Adjacent (Sum.inl ⟨d, hd⟩ : S.GlueDart)
          (Sum.inl ⟨M.alpha d, ha⟩ : S.GlueDart) :=
        Relation.EqvGen.rel _ _ (Or.inl (S.glueAlpha_inl_of_mem ⟨d, hd⟩ ha))
      constructor
      · intro h _
        obtain ⟨x, hx⟩ := h hd
        exact ⟨x, Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hadj) hx⟩
      · intro h _
        obtain ⟨x, hx⟩ := h ha
        exact ⟨x, Relation.EqvGen.trans _ _ _ hadj hx⟩
    · exact ⟨fun _ h => absurd h ha, fun _ => S.reach_of_boundary d hd ha⟩
  · have hr : S.Reach d := fun h => absurd h hd
    by_cases ha : M.faceOf (M.alpha d) ∈ S.faces
    · have hn : M.faceOf (M.alpha (M.alpha d)) ∉ S.faces := by
        rw [M.alpha_involutive d]
        exact hd
      exact ⟨fun _ => S.reach_of_boundary (M.alpha d) ha hn, fun _ => hr⟩
    · exact ⟨fun _ h => absurd h ha, fun _ => hr⟩

theorem reach_sigma (d : M.Dart) : S.Reach d ↔ S.Reach (M.sigma d) := by
  by_cases ha : M.faceOf (M.alpha d) ∈ S.faces
  · have hs : M.faceOf (M.sigma d) ∈ S.faces := by
      rw [faceOf_sigma_eq M d]
      exact ha
    by_cases hd : M.faceOf d ∈ S.faces
    · have hadj : Relation.EqvGen S.glueMap.Adjacent (Sum.inl ⟨d, hd⟩ : S.GlueDart)
          (Sum.inl ⟨M.sigma d, hs⟩ : S.GlueDart) :=
        Relation.EqvGen.rel _ _ (Or.inr (S.glueSigma_inl_of_mem ⟨d, hd⟩ ha))
      constructor
      · intro h _
        obtain ⟨x, hx⟩ := h hd
        exact ⟨x, Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hadj) hx⟩
      · intro h _
        obtain ⟨x, hx⟩ := h hs
        exact ⟨x, Relation.EqvGen.trans _ _ _ hadj hx⟩
    · have hn : M.faceOf (M.alpha (M.alpha d)) ∉ S.faces := by
        rw [M.alpha_involutive d]
        exact hd
      have hfp : (S.glueMap.facePerm (Sum.inl ⟨M.alpha d, ha⟩ : S.GlueDart) : S.GlueDart) =
          Sum.inl ⟨M.sigma d, hs⟩ := by
        have h := congrArg (fun p : Perm S.GlueDart => p (Sum.inl ⟨M.alpha d, ha⟩))
          S.glueMap_facePerm
        exact h.trans ((S.glueFacePerm_inl ⟨M.alpha d, ha⟩).trans
          (congrArg Sum.inl (Subtype.ext (facePerm_alpha_eq M d))))
      refine ⟨fun _ _ => ?_, fun _ h => absurd h hd⟩
      obtain ⟨x, hx⟩ := S.reach_of_boundary (M.alpha d) ha hn ha
      have hstep := eqvGen_facePerm_self S.glueMap (Sum.inl ⟨M.alpha d, ha⟩ : S.GlueDart)
      rewrite [hfp] at hstep
      exact ⟨x, Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hstep) hx⟩
  · have hs : M.faceOf (M.sigma d) ∉ S.faces := by
      rw [faceOf_sigma_eq M d]
      exact ha
    exact ⟨fun _ h => absurd h hs, fun _ hd => S.reach_of_boundary d hd ha hd⟩

theorem reach_iff_of_eqvGen {d e : M.Dart} (h : Relation.EqvGen M.Adjacent d e) :
    S.Reach d ↔ S.Reach e := by
  induction h with
  | rel d e hde =>
    rcases hde with hde | hde
    · subst hde
      exact S.reach_alpha d
    · subst hde
      exact S.reach_sigma d
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem glueMap_connected (hwalk : S.boundary.FollowsBoundary) (hM : M.IsConnected)
    (hX : X.IsConnected) : S.glueMap.IsConnected := by
  obtain ⟨b⟩ := nonempty_boundaryDart M S.faces S.boundary
  have hbase : ∀ g : S.glueMap.Dart,
      Relation.EqvGen S.glueMap.Adjacent g (S.glueEmbedding (S.seamEquiv b).1) := by
    intro g
    rcases g with d | x
    · obtain ⟨x, hx⟩ := (S.reach_iff_of_eqvGen (hM b.1 d.1)).1
        (S.reach_of_boundary b.1 b.2.1 b.2.2) d.2
      exact Relation.EqvGen.trans _ _ _ hx
        (S.eqvGen_glueEmbedding hwalk (hX x (S.seamEquiv b).1))
    · have hx := S.eqvGen_glueEmbedding hwalk (hX x.1 (S.seamEquiv b).1)
      rewrite [S.glueEmbedding_of_ne x.1 x.2] at hx
      exact hx
  intro g g'
  exact Relation.EqvGen.trans _ _ _ (hbase g) (Relation.EqvGen.symm _ _ (hbase g'))

/-- Gluing a planar map into a face-set region of a planar map along the boundary walk gives
a planar map. -/
theorem glueMap_planar (hwalk : S.boundary.FollowsBoundary) (hM : M.IsPlanar)
    (hX : X.IsPlanar) : S.glueMap.IsPlanar := by
  have hP : S.piece.IsPlanar := reclosedMap_planar M S.faces S.boundary hwalk hM
  refine ⟨S.glueMap_connected hwalk hM.1 hX.1, ?_⟩
  have hM2 : (M.vertexCount : ℤ) - (M.edgeCount : ℤ) + (M.faceCount : ℤ) = 2 := hM.2
  have hX2 : (X.vertexCount : ℤ) - (X.edgeCount : ℤ) + (X.faceCount : ℤ) = 2 := hX.2
  have hP2 : (S.piece.vertexCount : ℤ) - (S.piece.edgeCount : ℤ) +
      (S.piece.faceCount : ℤ) = 2 := hP.2
  have hv := S.glue_vertexCount hwalk
  have he := S.glue_edgeCount
  have hf := S.glue_faceCount
  show (S.glueMap.vertexCount : ℤ) - (S.glueMap.edgeCount : ℤ) +
    (S.glueMap.faceCount : ℤ) = 2
  omega

end Seam

end GroupApproximation.GGT.VanKampen.Surgery.PocketGlue

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.PocketGlue.Seam.glueMap_connected
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.PocketGlue.Seam.glueMap_planar
