import GroupApproximation.GGT.VanKampen.CombMapRestriction
import GroupApproximation.GGT.VanKampen.DiscDiagram
import GroupApproximation.GGT.VanKampen.SurgeryReclosedVertices
import GroupApproximation.Meta.AxiomGuard

/-!
# Gluing a disc into the boundary of a face set

Let `faces` be a set of faces of a combinatorial map `M` with a cyclic boundary enumeration, and
let `X` be a map with a chosen face `outer` whose boundary traversal has the same length.  The
glued map keeps the darts of `M` on `faces` and the darts of `X` off `outer`.  An edge internal
to `faces` keeps its reversal in `M`; a boundary dart of `faces` is identified with the dart of
`outer` at the same position, and takes the reversal of that dart in `X`.

The main result, `Seam.glue_isRestriction`, says that `X` is the restriction of the glued map to
the darts of `X`, provided the boundary enumeration follows the actual boundary of `faces`.
Together with `CombMap.reclosed_isRestriction`, this is the Euler bookkeeping of replacing the
region cut off by a pocket with an O-equivalent disc.
-/

noncomputable section

namespace GroupApproximation.GGT.VanKampen.Surgery.PocketGlue

open Equiv MapCollapse

universe v

/-- The face rotation after a reversal is the vertex rotation. -/
theorem facePerm_alpha_eq (M : CombMap.{v}) (d : M.Dart) :
    M.facePerm (M.alpha d) = M.sigma d := by
  change M.sigma (M.alpha (M.alpha d)) = M.sigma d
  rw [M.alpha_involutive d]

/-- A dart and its reversal rotated at the vertex lie on the same face. -/
theorem faceOf_sigma_eq (M : CombMap.{v}) (d : M.Dart) :
    M.faceOf (M.sigma d) = M.faceOf (M.alpha d) := by
  rw [← facePerm_alpha_eq M d, CombMap.faceOf_facePerm]

/-- Seam data: a face set of `M` with a cyclic boundary enumeration, and a face of `X` with a
boundary traversal of the same length. -/
structure Seam (M X : CombMap.{v}) where
  /-- The faces of `M` that are kept. -/
  faces : Finset M.Face
  /-- A cyclic enumeration of the oriented boundary darts of `faces`. -/
  boundary : BoundaryCycle M faces
  /-- The face of `X` that is removed. -/
  outer : X.Face
  /-- A traversal of the removed face. -/
  outerBoundary : FaceBoundary X outer
  /-- The two boundaries have the same length. -/
  length_eq : boundary.cycle.length = outerBoundary.darts.length

namespace Seam

variable {M X : CombMap.{v}} (S : Seam M X)

/-- Positions on the traversal of the removed face. -/
def outerPosition :
    Fin S.outerBoundary.darts.length ≃ {x : X.Dart // X.faceOf x = S.outer} := by
  classical
  exact (S.outerBoundary.nodup.getEquiv S.outerBoundary.darts).trans
    (Equiv.subtypeEquivRight S.outerBoundary.mem_iff)

theorem outerPosition_val (i : Fin S.outerBoundary.darts.length) :
    (S.outerPosition i).1 = S.outerBoundary.darts.get i := rfl

/-- The identification of the two position types. -/
def positionCast : Fin S.boundary.cycle.length ≃ Fin S.outerBoundary.darts.length where
  toFun i := Fin.cast S.length_eq i
  invFun i := Fin.cast S.length_eq.symm i
  left_inv _ := Fin.ext rfl
  right_inv _ := Fin.ext rfl

theorem positionCast_val (i : Fin S.boundary.cycle.length) :
    (S.positionCast i).val = i.val := rfl

/-- A boundary dart of `faces` corresponds to the dart of `outer` at the same position. -/
def seamEquiv : BoundaryDart M S.faces ≃ {x : X.Dart // X.faceOf x = S.outer} :=
  S.boundary.positionEquiv.symm.trans (S.positionCast.trans S.outerPosition)

theorem seamEquiv_positionEquiv (i : Fin S.boundary.cycle.length) :
    S.seamEquiv (S.boundary.positionEquiv i) = S.outerPosition (S.positionCast i) := by
  show S.outerPosition (S.positionCast
    (S.boundary.positionEquiv.symm (S.boundary.positionEquiv i))) = _
  rw [Equiv.symm_apply_apply]

/-- The seam carries the boundary rotation of `faces` to the face rotation of `outer`. -/
theorem seamEquiv_boundaryPerm (b : BoundaryDart M S.faces) :
    (S.seamEquiv (S.boundary.boundaryPerm b)).1 = X.facePerm (S.seamEquiv b).1 := by
  obtain ⟨i, rfl⟩ := S.boundary.positionEquiv.surjective b
  rw [boundaryPerm_positionEquiv, seamEquiv_positionEquiv, seamEquiv_positionEquiv,
    outerPosition_val, outerPosition_val,
    FaceBoundary.cyclic_get_rotate X.facePerm S.outerBoundary.darts S.outerBoundary.nonempty
      S.outerBoundary.chain S.outerBoundary.closes]
  have hi : S.positionCast (finRotate S.boundary.cycle.length i) =
      finRotate S.outerBoundary.darts.length (S.positionCast i) := by
    apply Fin.ext
    have hlen := S.length_eq
    simp only [positionCast_val, FiniteCycleSplit.rotate_val]
    split_ifs <;> omega
  rw [hi]

/-- Darts of the glued map: darts of `M` on `faces` and darts of `X` off `outer`. -/
abbrev GlueDart :=
  {d : M.Dart // M.faceOf d ∈ S.faces} ⊕ {x : X.Dart // X.faceOf x ≠ S.outer}

instance glueDartFintype : Fintype S.GlueDart := by
  classical
  exact inferInstance

/-- Darts of `M` on an edge internal to `faces`. -/
abbrev InteriorDart := {d : M.Dart // InternalDart M S.faces d}

open Classical in
/-- Split a glued dart into an internal dart of `faces` or a dart of `X`. -/
def glueSplit : S.GlueDart → S.InteriorDart ⊕ X.Dart
  | .inl d =>
    if h : M.faceOf (M.alpha d.1) ∈ S.faces then .inl ⟨d.1, d.2, h⟩
    else .inr (S.seamEquiv ⟨d.1, d.2, h⟩).1
  | .inr x => .inr x.1

open Classical in
/-- The inverse of `glueSplit`. -/
def glueUnsplit : S.InteriorDart ⊕ X.Dart → S.GlueDart
  | .inl w => .inl ⟨w.1, w.2.1⟩
  | .inr x =>
    if h : X.faceOf x = S.outer then
      .inl ⟨(S.seamEquiv.symm ⟨x, h⟩).1, (S.seamEquiv.symm ⟨x, h⟩).2.1⟩
    else .inr ⟨x, h⟩

theorem glueSplit_inl_of_mem (d : {d : M.Dart // M.faceOf d ∈ S.faces})
    (h : M.faceOf (M.alpha d.1) ∈ S.faces) :
    S.glueSplit (Sum.inl d) = Sum.inl ⟨d.1, d.2, h⟩ := by
  simp only [glueSplit, dif_pos h]

theorem glueSplit_inl_of_notMem (d : {d : M.Dart // M.faceOf d ∈ S.faces})
    (h : M.faceOf (M.alpha d.1) ∉ S.faces) :
    S.glueSplit (Sum.inl d) = Sum.inr (S.seamEquiv ⟨d.1, d.2, h⟩).1 := by
  simp only [glueSplit, dif_neg h]

theorem glueSplit_inr (x : {x : X.Dart // X.faceOf x ≠ S.outer}) :
    S.glueSplit (Sum.inr x) = Sum.inr x.1 := rfl

theorem glueUnsplit_inl (w : S.InteriorDart) :
    S.glueUnsplit (Sum.inl w) = Sum.inl ⟨w.1, w.2.1⟩ := rfl

theorem glueUnsplit_inr_of_eq (x : X.Dart) (h : X.faceOf x = S.outer) :
    S.glueUnsplit (Sum.inr x) =
      Sum.inl ⟨(S.seamEquiv.symm ⟨x, h⟩).1, (S.seamEquiv.symm ⟨x, h⟩).2.1⟩ := by
  simp only [glueUnsplit, dif_pos h]

theorem glueUnsplit_inr_of_ne (x : X.Dart) (h : X.faceOf x ≠ S.outer) :
    S.glueUnsplit (Sum.inr x) = Sum.inr ⟨x, h⟩ := by
  simp only [glueUnsplit, dif_neg h]

theorem glueUnsplit_glueSplit (g : S.GlueDart) : S.glueUnsplit (S.glueSplit g) = g := by
  rcases g with d | x
  · by_cases h : M.faceOf (M.alpha d.1) ∈ S.faces
    · exact (congrArg S.glueUnsplit (S.glueSplit_inl_of_mem d h)).trans rfl
    · have hx : X.faceOf (S.seamEquiv ⟨d.1, d.2, h⟩).1 = S.outer :=
        (S.seamEquiv ⟨d.1, d.2, h⟩).2
      rw [S.glueSplit_inl_of_notMem d h, S.glueUnsplit_inr_of_eq _ hx]
      exact congrArg Sum.inl (Subtype.ext
        (congrArg Subtype.val (S.seamEquiv.symm_apply_apply ⟨d.1, d.2, h⟩) :))
  · exact S.glueUnsplit_inr_of_ne x.1 x.2

theorem glueSplit_glueUnsplit (z : S.InteriorDart ⊕ X.Dart) :
    S.glueSplit (S.glueUnsplit z) = z := by
  rcases z with w | x
  · exact (congrArg S.glueSplit (S.glueUnsplit_inl w)).trans
      (S.glueSplit_inl_of_mem ⟨w.1, w.2.1⟩ w.2.2)
  · by_cases h : X.faceOf x = S.outer
    · have hb := (S.seamEquiv.symm ⟨x, h⟩).2
      rw [S.glueUnsplit_inr_of_eq x h,
        S.glueSplit_inl_of_notMem ⟨(S.seamEquiv.symm ⟨x, h⟩).1, hb.1⟩ hb.2]
      exact congrArg Sum.inr (congrArg Subtype.val (S.seamEquiv.apply_symm_apply ⟨x, h⟩))
    · exact (congrArg S.glueSplit (S.glueUnsplit_inr_of_ne x h)).trans
        (S.glueSplit_inr ⟨x, h⟩)

/-- Glued darts split into internal darts of `faces` and darts of `X`. -/
def splitEquiv : S.GlueDart ≃ S.InteriorDart ⊕ X.Dart where
  toFun := S.glueSplit
  invFun := S.glueUnsplit
  left_inv := S.glueUnsplit_glueSplit
  right_inv := S.glueSplit_glueUnsplit

theorem splitEquiv_apply (g : S.GlueDart) : S.splitEquiv g = S.glueSplit g := rfl

theorem splitEquiv_symm_apply (z : S.InteriorDart ⊕ X.Dart) :
    S.splitEquiv.symm z = S.glueUnsplit z := rfl

/-- Reversal on internal darts of `faces`. -/
def interiorAlpha : Perm S.InteriorDart :=
  M.alpha.subtypePerm (p := InternalDart M S.faces) (internalDart_alpha_iff M S.faces)

/-- Edge reversal on glued darts. -/
def glueAlpha : Perm S.GlueDart :=
  S.splitEquiv.trans ((Equiv.sumCongr S.interiorAlpha X.alpha).trans S.splitEquiv.symm)

theorem glueAlpha_apply (g : S.GlueDart) :
    S.glueAlpha g =
      S.splitEquiv.symm (Equiv.sumCongr S.interiorAlpha X.alpha (S.splitEquiv g)) := rfl

theorem glueAlpha_involutive : Function.Involutive S.glueAlpha := by
  intro g
  have hz : ∀ z : S.InteriorDart ⊕ X.Dart,
      Equiv.sumCongr S.interiorAlpha X.alpha (Equiv.sumCongr S.interiorAlpha X.alpha z) = z := by
    rintro (w | x)
    · exact congrArg Sum.inl (Subtype.ext (M.alpha_involutive w.1))
    · exact congrArg Sum.inr (X.alpha_involutive x)
  rw [glueAlpha_apply, glueAlpha_apply, Equiv.apply_symm_apply, hz, Equiv.symm_apply_apply]

theorem glueAlpha_fixedPointFree (g : S.GlueDart) : S.glueAlpha g ≠ g := by
  intro h
  have h' := congrArg S.splitEquiv h
  rw [glueAlpha_apply, Equiv.apply_symm_apply] at h'
  have key : ∀ z : S.InteriorDart ⊕ X.Dart,
      Equiv.sumCongr S.interiorAlpha X.alpha z ≠ z := by
    rintro (w | x) hw
    · exact M.alpha_fixedPointFree w.1 (congrArg Subtype.val (Sum.inl_injective hw))
    · exact X.alpha_fixedPointFree x (Sum.inr_injective hw)
  exact key _ h'

/-- Face rotation on glued darts: the faces of `faces` and the faces of `X` other than
`outer`. -/
def glueFacePerm : Perm S.GlueDart :=
  Equiv.Perm.sumCongr
    (M.facePerm.subtypePerm (p := fun d => M.faceOf d ∈ S.faces)
      (fun d => iff_of_eq (congrArg (· ∈ S.faces) (M.faceOf_facePerm d))))
    (X.facePerm.subtypePerm (p := fun x => X.faceOf x ≠ S.outer)
      (fun x => iff_of_eq (congrArg (· ≠ S.outer) (X.faceOf_facePerm x))))

/-- The glued map. -/
def glueMap : CombMap.{v} :=
  ofAlphaFacePerm S.glueAlpha S.glueFacePerm S.glueAlpha_involutive S.glueAlpha_fixedPointFree

theorem glueMap_facePerm : S.glueMap.facePerm = S.glueFacePerm :=
  ofAlphaFacePerm_facePerm _ _ _ _

/-- The darts of `X` inside the glued map. -/
def glueEmbedding : X.Dart ↪ S.glueMap.Dart where
  toFun x := S.splitEquiv.symm (Sum.inr x)
  inj' _ _ h := Sum.inr_injective (S.splitEquiv.symm.injective h)

theorem glueEmbedding_apply (x : X.Dart) :
    (S.glueEmbedding x : S.GlueDart) = S.glueUnsplit (Sum.inr x) := rfl

theorem splitEquiv_glueEmbedding (x : X.Dart) :
    S.splitEquiv (S.glueEmbedding x) = Sum.inr x :=
  S.splitEquiv.apply_symm_apply (Sum.inr x)

theorem glueEmbedding_of_ne (x : X.Dart) (h : X.faceOf x ≠ S.outer) :
    (S.glueEmbedding x : S.GlueDart) = Sum.inr ⟨x, h⟩ :=
  S.glueUnsplit_inr_of_ne x h

/-- A dart of `outer` is glued to the boundary dart of `faces` at the same position. -/
theorem glueEmbedding_seam (b : BoundaryDart M S.faces) :
    (S.glueEmbedding (S.seamEquiv b).1 : S.GlueDart) = Sum.inl ⟨b.1, b.2.1⟩ := by
  rewrite [glueEmbedding_apply, S.glueUnsplit_inr_of_eq _ (S.seamEquiv b).2]
  exact congrArg Sum.inl (Subtype.ext
    (congrArg Subtype.val (S.seamEquiv.symm_apply_apply b) :))

theorem glueAlpha_glueEmbedding (x : X.Dart) :
    S.glueAlpha (S.glueEmbedding x) = S.glueEmbedding (X.alpha x) :=
  congrArg (fun z => S.splitEquiv.symm (Equiv.sumCongr S.interiorAlpha X.alpha z))
    (S.splitEquiv_glueEmbedding x)

theorem glueAlpha_inl_of_mem (d : {d : M.Dart // M.faceOf d ∈ S.faces})
    (h : M.faceOf (M.alpha d.1) ∈ S.faces) :
    S.glueAlpha (Sum.inl d) = Sum.inl ⟨M.alpha d.1, h⟩ :=
  congrArg (fun z => S.splitEquiv.symm (Equiv.sumCongr S.interiorAlpha X.alpha z))
    (S.glueSplit_inl_of_mem d h)

theorem mem_sigma (d : M.Dart) (h : M.faceOf (M.alpha d) ∈ S.faces) :
    M.faceOf (M.sigma d) ∈ S.faces := by
  rw [faceOf_sigma_eq]
  exact h

/-- On an internal dart the glued vertex rotation is the vertex rotation of `M`. -/
theorem glueSigma_inl_of_mem (d : {d : M.Dart // M.faceOf d ∈ S.faces})
    (h : M.faceOf (M.alpha d.1) ∈ S.faces) :
    (S.glueMap.sigma (Sum.inl d : S.GlueDart) : S.GlueDart) =
      Sum.inl ⟨M.sigma d.1, S.mem_sigma d.1 h⟩ := by
  change S.glueFacePerm (S.glueAlpha (Sum.inl d)) = _
  rewrite [S.glueAlpha_inl_of_mem d h]
  exact congrArg Sum.inl (Subtype.ext (facePerm_alpha_eq M d.1))

theorem glueSigma_pow_inl (d : {d : M.Dart // M.faceOf d ∈ S.faces}) (n : ℕ) :
    (∀ k, k < n → InternalDart M S.faces ((M.sigma ^ k) d.1)) →
      ∃ e : {d : M.Dart // M.faceOf d ∈ S.faces}, e.1 = (M.sigma ^ n) d.1 ∧
        (S.glueMap.sigma ^ n) (Sum.inl d : S.GlueDart) = Sum.inl e := by
  induction n with
  | zero =>
    intro _
    refine ⟨d, ?_, ?_⟩
    · rw [pow_zero, Perm.one_apply]
    · rw [pow_zero, Perm.one_apply]
  | succ n ih =>
    intro hint
    obtain ⟨e, he, hpow⟩ := ih (fun k hk => hint k (by omega))
    have hin : InternalDart M S.faces e.1 := by
      rw [he]
      exact hint n (by omega)
    refine ⟨⟨M.sigma e.1, S.mem_sigma e.1 hin.2⟩, ?_, ?_⟩
    · show M.sigma e.1 = (M.sigma ^ (n + 1)) d.1
      rw [pow_succ', Perm.mul_apply, he]
    · rewrite [pow_succ', Perm.mul_apply, hpow]
      exact S.glueSigma_inl_of_mem e hin.2

theorem inl_notMem_range (d : {d : M.Dart // M.faceOf d ∈ S.faces})
    (h : M.faceOf (M.alpha d.1) ∈ S.faces) :
    (Sum.inl d : S.GlueDart) ∉ Set.range S.glueEmbedding := by
  rintro ⟨x, hx⟩
  have h1 := S.splitEquiv_glueEmbedding x
  rw [hx, splitEquiv_apply, S.glueSplit_inl_of_mem d h] at h1
  exact Sum.inl_ne_inr h1

/-- The vertex rotation of `X` is the first return of the glued vertex rotation. -/
theorem glue_sigma_firstReturn (hwalk : S.boundary.FollowsBoundary) :
    PermFirstReturn.IsFirstReturn S.glueMap.sigma X.sigma S.glueEmbedding := by
  intro x
  by_cases hy : X.faceOf (X.alpha x) = S.outer
  · obtain ⟨b, hb⟩ : ∃ b : BoundaryDart M S.faces, (S.seamEquiv b).1 = X.alpha x :=
      ⟨S.seamEquiv.symm ⟨X.alpha x, hy⟩,
        congrArg Subtype.val (S.seamEquiv.apply_symm_apply ⟨X.alpha x, hy⟩)⟩
    have hfp : M.faceOf (M.facePerm b.1) ∈ S.faces := by
      rw [CombMap.faceOf_facePerm]
      exact b.2.1
    have hstep : (S.glueMap.sigma (S.glueEmbedding x) : S.GlueDart) =
        Sum.inl ⟨M.facePerm b.1, hfp⟩ := by
      change S.glueFacePerm (S.glueAlpha (S.glueEmbedding x)) = _
      rewrite [S.glueAlpha_glueEmbedding, ← hb, S.glueEmbedding_seam]
      rfl
    have hpath : Relation.ReflTransGen (fun y z => InternalDart M S.faces y ∧ M.sigma y = z)
        (M.facePerm b.1) (S.boundary.boundaryPerm b).1 := hwalk b
    obtain ⟨n, hn, hskip⟩ :=
      PermFirstReturn.exists_pow_of_skip_walk M.sigma (InternalDart M S.faces) hpath
    obtain ⟨e, he, hpow⟩ := S.glueSigma_pow_inl ⟨M.facePerm b.1, hfp⟩ n hskip
    refine ⟨n + 1, by omega, ?_, ?_⟩
    · rewrite [pow_succ, Perm.mul_apply, hstep, hpow]
      have hsig : (S.seamEquiv (S.boundary.boundaryPerm b)).1 = X.sigma x := by
        rw [S.seamEquiv_boundaryPerm, hb]
        exact facePerm_alpha_eq X x
      rewrite [← hsig, S.glueEmbedding_seam]
      exact congrArg Sum.inl (Subtype.ext (he.trans hn))
    · intro k hk hkn hmem
      obtain ⟨e', he', hpow'⟩ := S.glueSigma_pow_inl ⟨M.facePerm b.1, hfp⟩ (k - 1)
        (fun j hj => hskip j (by omega))
      have hin : InternalDart M S.faces e'.1 := by
        rw [he']
        exact hskip (k - 1) (by omega)
      have hk' : (S.glueMap.sigma ^ k) (S.glueEmbedding x) = Sum.inl e' := by
        have hk1 : k = k - 1 + 1 := by omega
        rw [hk1, pow_succ, Perm.mul_apply, hstep, hpow']
      rw [hk'] at hmem
      exact S.inl_notMem_range e' hin.2 hmem
  · have hy' : X.faceOf (X.sigma x) ≠ S.outer := by
      rw [faceOf_sigma_eq]
      exact hy
    refine ⟨1, by omega, ?_, by intro k hk hkn; omega⟩
    rewrite [pow_one, S.glueEmbedding_of_ne _ hy']
    change S.glueFacePerm (S.glueAlpha (S.glueEmbedding x)) = _
    rewrite [S.glueAlpha_glueEmbedding, S.glueEmbedding_of_ne _ hy]
    exact congrArg Sum.inr (Subtype.ext (facePerm_alpha_eq X x))

/-- `X` is the restriction of the glued map to the darts of `X`. -/
theorem glue_isRestriction (hwalk : S.boundary.FollowsBoundary) :
    CombMap.IsRestriction S.glueMap X S.glueEmbedding :=
  ⟨fun x => (S.glueAlpha_glueEmbedding x).symm, S.glue_sigma_firstReturn hwalk⟩

end Seam

end GroupApproximation.GGT.VanKampen.Surgery.PocketGlue

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.PocketGlue.Seam.seamEquiv_boundaryPerm
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.PocketGlue.Seam.glueMap_facePerm
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.PocketGlue.Seam.glue_sigma_firstReturn
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.PocketGlue.Seam.glue_isRestriction
