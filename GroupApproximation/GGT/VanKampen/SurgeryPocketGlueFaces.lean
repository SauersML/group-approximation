import GroupApproximation.GGT.VanKampen.SurgeryPocketGluePlanar
import GroupApproximation.GGT.VanKampen.SurgeryFaceDiagram
import GroupApproximation.Meta.AxiomGuard

/-!
# Face boundaries and labels of the glued map

`SurgeryPocketGlueCount` identifies the faces of the glued map with the faces in `faces` and the
faces of `X` other than `outer`.  This file transports ordered face boundaries across that
identification.  A face in `faces` keeps its dart list, read as glued darts, and a face of `X`
other than `outer` keeps its dart list through `glueEmbedding`.

Labels of the darts of `M` and of `X` that agree along the seam label the glued darts.  The
glued labelling is compatible with edge reversal when both labellings are, and every glued face
reads the old face word.
-/

noncomputable section

namespace GroupApproximation.GGT.VanKampen.Surgery.PocketGlue

open Equiv MapCollapse

universe v

namespace Seam

variable {M X : CombMap.{v}} (S : Seam M X)

/-! ## The faces, named -/

/-- The glued face carrying a face in `faces`. -/
def leftFace (g : {f : M.Face // f ∈ S.faces}) : S.glueMap.Face :=
  S.glueFaceEquiv.symm (Sum.inl g)

/-- The glued face carrying a face of `X` other than `outer`. -/
def rightFace (h : {f : X.Face // f ≠ S.outer}) : S.glueMap.Face :=
  S.glueFaceEquiv.symm (Sum.inr h)

theorem leftFace_injective : Function.Injective S.leftFace :=
  S.glueFaceEquiv.symm.injective.comp Sum.inl_injective

theorem rightFace_injective : Function.Injective S.rightFace :=
  S.glueFaceEquiv.symm.injective.comp Sum.inr_injective

theorem leftFace_ne_rightFace (g : {f : M.Face // f ∈ S.faces})
    (h : {f : X.Face // f ≠ S.outer}) : S.leftFace g ≠ S.rightFace h :=
  fun hgh => Sum.inl_ne_inr (S.glueFaceEquiv.symm.injective hgh)

theorem glueFaceEquiv_faceOf_inl (d : {d : M.Dart // M.faceOf d ∈ S.faces}) :
    S.glueFaceEquiv (S.glueMap.faceOf (Sum.inl d : S.GlueDart)) =
      Sum.inl ⟨M.faceOf d.1, d.2⟩ := rfl

theorem glueFaceEquiv_faceOf_inr (x : {x : X.Dart // X.faceOf x ≠ S.outer}) :
    S.glueFaceEquiv (S.glueMap.faceOf (Sum.inr x : S.GlueDart)) =
      Sum.inr ⟨X.faceOf x.1, x.2⟩ := rfl

theorem faceOf_inl (d : {d : M.Dart // M.faceOf d ∈ S.faces}) :
    S.glueMap.faceOf (Sum.inl d : S.GlueDart) = S.leftFace ⟨M.faceOf d.1, d.2⟩ :=
  S.glueFaceEquiv.eq_symm_apply.2 (S.glueFaceEquiv_faceOf_inl d)

theorem faceOf_inr (x : {x : X.Dart // X.faceOf x ≠ S.outer}) :
    S.glueMap.faceOf (Sum.inr x : S.GlueDart) = S.rightFace ⟨X.faceOf x.1, x.2⟩ :=
  S.glueFaceEquiv.eq_symm_apply.2 (S.glueFaceEquiv_faceOf_inr x)

/-! ## Face rotation on glued darts -/

theorem glueFacePerm_inr (x : {x : X.Dart // X.faceOf x ≠ S.outer}) :
    (S.glueFacePerm (Sum.inr x) : S.GlueDart) =
      Sum.inr ⟨X.facePerm x.1, by rw [CombMap.faceOf_facePerm]; exact x.2⟩ := rfl

theorem glueMap_facePerm_inl (d : {d : M.Dart // M.faceOf d ∈ S.faces}) :
    (S.glueMap.facePerm (Sum.inl d : S.GlueDart) : S.GlueDart) =
      Sum.inl ⟨M.facePerm d.1, by rw [CombMap.faceOf_facePerm]; exact d.2⟩ :=
  (congrArg (fun p : Perm S.GlueDart => p (Sum.inl d)) S.glueMap_facePerm).trans
    (S.glueFacePerm_inl d)

theorem glueMap_facePerm_inr (x : {x : X.Dart // X.faceOf x ≠ S.outer}) :
    (S.glueMap.facePerm (Sum.inr x : S.GlueDart) : S.GlueDart) =
      Sum.inr ⟨X.facePerm x.1, by rw [CombMap.faceOf_facePerm]; exact x.2⟩ :=
  (congrArg (fun p : Perm S.GlueDart => p (Sum.inr x)) S.glueMap_facePerm).trans
    (S.glueFacePerm_inr x)

theorem glueMap_facePerm_glueEmbedding (x : X.Dart) (hx : X.faceOf x ≠ S.outer) :
    S.glueMap.facePerm (S.glueEmbedding x) = S.glueEmbedding (X.facePerm x) := by
  have hx' : X.faceOf (X.facePerm x) ≠ S.outer := by
    rw [CombMap.faceOf_facePerm]
    exact hx
  calc S.glueMap.facePerm (S.glueEmbedding x)
      = S.glueMap.facePerm (Sum.inr ⟨x, hx⟩ : S.GlueDart) :=
        congrArg (fun z => S.glueMap.facePerm z) (S.glueEmbedding_of_ne x hx)
    _ = (Sum.inr ⟨X.facePerm x, hx'⟩ : S.GlueDart) := S.glueMap_facePerm_inr ⟨x, hx⟩
    _ = S.glueEmbedding (X.facePerm x) := (S.glueEmbedding_of_ne (X.facePerm x) hx').symm

/-! ## Boundaries of the faces in `faces` -/

theorem faceOf_mem_of_mem_darts (g : M.Face) (hg : g ∈ S.faces) (B : FaceBoundary M g) :
    ∀ d ∈ B.darts, M.faceOf d ∈ S.faces :=
  fun d hd => (congrArg (· ∈ S.faces) ((B.mem_iff d).1 hd)).mpr hg

/-- A dart of `M` on `faces`, as a glued dart. -/
def leftDart (d : M.Dart) (hd : M.faceOf d ∈ S.faces) : S.glueMap.Dart :=
  (Sum.inl ⟨d, hd⟩ : S.GlueDart)

/-- The darts of an ordered boundary of a face in `faces`, as glued darts. -/
def leftDarts (g : M.Face) (hg : g ∈ S.faces) (B : FaceBoundary M g) :
    List S.glueMap.Dart :=
  B.darts.pmap S.leftDart (S.faceOf_mem_of_mem_darts g hg B)

theorem leftDarts_ne_nil (g : M.Face) (hg : g ∈ S.faces) (B : FaceBoundary M g) :
    S.leftDarts g hg B ≠ [] :=
  (List.pmap_ne_nil_iff S.leftDart (S.faceOf_mem_of_mem_darts g hg B)).2 B.nonempty

theorem leftDarts_nodup (g : M.Face) (hg : g ∈ S.faces) (B : FaceBoundary M g) :
    (S.leftDarts g hg B).Nodup := by
  refine List.Nodup.pmap ?_ B.nodup
  intro a ha b hb hab
  have h' : (Sum.inl ⟨a, ha⟩ : S.GlueDart) = Sum.inl ⟨b, hb⟩ := hab
  exact congrArg Subtype.val (Sum.inl_injective h')

theorem mem_leftDarts_iff (g : M.Face) (hg : g ∈ S.faces) (B : FaceBoundary M g)
    (e : S.GlueDart) :
    e ∈ S.leftDarts g hg B ↔ S.glueMap.faceOf e = S.leftFace ⟨g, hg⟩ := by
  rewrite [leftFace, Equiv.eq_symm_apply, leftDarts, List.mem_pmap]
  rcases e with d | x
  · rewrite [S.glueFaceEquiv_faceOf_inl d]
    constructor
    · rintro ⟨a, ha, hmem⟩
      have h' : (Sum.inl ⟨a, S.faceOf_mem_of_mem_darts g hg B a ha⟩ : S.GlueDart) =
          Sum.inl d := hmem
      have had : a = d.1 := congrArg Subtype.val (Sum.inl_injective h')
      exact congrArg Sum.inl (Subtype.ext
        ((congrArg M.faceOf had).symm.trans ((B.mem_iff a).1 ha)))
    · intro hface
      have hf : M.faceOf d.1 = g := congrArg Subtype.val (Sum.inl_injective hface)
      exact ⟨d.1, (B.mem_iff d.1).2 hf, rfl⟩
  · rewrite [S.glueFaceEquiv_faceOf_inr x]
    constructor
    · rintro ⟨a, ha, hmem⟩
      have h' : (Sum.inl ⟨a, S.faceOf_mem_of_mem_darts g hg B a ha⟩ : S.GlueDart) =
          Sum.inr x := hmem
      exact absurd h' Sum.inl_ne_inr
    · intro hface
      exact absurd hface Sum.inr_ne_inl

theorem leftDarts_chain (g : M.Face) (hg : g ∈ S.faces) (B : FaceBoundary M g) :
    (S.leftDarts g hg B).IsChain fun d e => S.glueMap.facePerm d = e := by
  refine List.isChain_pmap_of_isChain ?_ B.chain _
  intro a b ha hb hab
  exact (S.glueMap_facePerm_inl ⟨a, ha⟩).trans
    (congrArg (fun z => (Sum.inl z : S.GlueDart)) (Subtype.ext hab))

theorem leftDarts_closes (g : M.Face) (hg : g ∈ S.faces) (B : FaceBoundary M g) :
    S.glueMap.facePerm ((S.leftDarts g hg B).getLast (S.leftDarts_ne_nil g hg B)) =
      (S.leftDarts g hg B).head (S.leftDarts_ne_nil g hg B) := by
  have hlast : (S.leftDarts g hg B).getLast (S.leftDarts_ne_nil g hg B) =
      S.leftDart (B.darts.getLast B.nonempty)
        (S.faceOf_mem_of_mem_darts g hg B _ (List.getLast_mem B.nonempty)) :=
    List.getLast_pmap _ _
  have hhead : (S.leftDarts g hg B).head (S.leftDarts_ne_nil g hg B) =
      S.leftDart (B.darts.head B.nonempty)
        (S.faceOf_mem_of_mem_darts g hg B _ (List.head_mem B.nonempty)) :=
    List.head_pmap _ _
  rewrite [hlast, hhead]
  exact (S.glueMap_facePerm_inl ⟨B.darts.getLast B.nonempty,
      S.faceOf_mem_of_mem_darts g hg B _ (List.getLast_mem B.nonempty)⟩).trans
    (congrArg (fun z => (Sum.inl z : S.GlueDart)) (Subtype.ext B.closes))

/-- The ordered boundary of the glued face carrying a face in `faces`. -/
def leftFaceBoundary (g : M.Face) (hg : g ∈ S.faces) (B : FaceBoundary M g) :
    FaceBoundary S.glueMap (S.leftFace ⟨g, hg⟩) where
  darts := S.leftDarts g hg B
  nonempty := S.leftDarts_ne_nil g hg B
  nodup := S.leftDarts_nodup g hg B
  mem_iff := S.mem_leftDarts_iff g hg B
  chain := S.leftDarts_chain g hg B
  closes := S.leftDarts_closes g hg B
  length_eq_degree := length_eq_faceDegree_of_nodup S.glueMap _ _
    (S.leftDarts_nodup g hg B) (S.mem_leftDarts_iff g hg B)

/-! ## Boundaries of the faces of `X` other than `outer` -/

theorem faceOf_ne_of_mem_darts (h : X.Face) (hh : h ≠ S.outer) (B : FaceBoundary X h) :
    ∀ x ∈ B.darts, X.faceOf x ≠ S.outer :=
  fun x hx => (congrArg (· ≠ S.outer) ((B.mem_iff x).1 hx)).mpr hh

/-- The darts of an ordered boundary of a face of `X`, as glued darts. -/
def rightDarts (h : X.Face) (B : FaceBoundary X h) : List S.glueMap.Dart :=
  B.darts.map S.glueEmbedding

theorem rightDarts_ne_nil (h : X.Face) (B : FaceBoundary X h) : S.rightDarts h B ≠ [] :=
  fun hnil => B.nonempty (List.map_eq_nil_iff.1 hnil)

theorem rightDarts_nodup (h : X.Face) (B : FaceBoundary X h) : (S.rightDarts h B).Nodup :=
  B.nodup.map S.glueEmbedding.injective

theorem mem_rightDarts_iff (h : X.Face) (hh : h ≠ S.outer) (B : FaceBoundary X h)
    (e : S.GlueDart) :
    e ∈ S.rightDarts h B ↔ S.glueMap.faceOf e = S.rightFace ⟨h, hh⟩ := by
  rewrite [rightFace, Equiv.eq_symm_apply, rightDarts, List.mem_map]
  rcases e with d | x
  · rewrite [S.glueFaceEquiv_faceOf_inl d]
    constructor
    · rintro ⟨a, ha, hmem⟩
      have h' : (Sum.inr ⟨a, S.faceOf_ne_of_mem_darts h hh B a ha⟩ : S.GlueDart) =
          Sum.inl d :=
        (S.glueEmbedding_of_ne a (S.faceOf_ne_of_mem_darts h hh B a ha)).symm.trans hmem
      exact absurd h' Sum.inr_ne_inl
    · intro hface
      exact absurd hface Sum.inl_ne_inr
  · rewrite [S.glueFaceEquiv_faceOf_inr x]
    constructor
    · rintro ⟨a, ha, hmem⟩
      have h' : (Sum.inr ⟨a, S.faceOf_ne_of_mem_darts h hh B a ha⟩ : S.GlueDart) =
          Sum.inr x :=
        (S.glueEmbedding_of_ne a (S.faceOf_ne_of_mem_darts h hh B a ha)).symm.trans hmem
      have hax : a = x.1 := congrArg Subtype.val (Sum.inr_injective h')
      exact congrArg Sum.inr (Subtype.ext
        ((congrArg X.faceOf hax).symm.trans ((B.mem_iff a).1 ha)))
    · intro hface
      have hf : X.faceOf x.1 = h := congrArg Subtype.val (Sum.inr_injective hface)
      exact ⟨x.1, (B.mem_iff x.1).2 hf, S.glueEmbedding_of_ne x.1 x.2⟩

theorem rightDarts_chain (h : X.Face) (hh : h ≠ S.outer) (B : FaceBoundary X h) :
    (S.rightDarts h B).IsChain fun d e => S.glueMap.facePerm d = e := by
  refine (List.isChain_map _).2 (List.IsChain.imp_of_mem_imp ?_ B.chain)
  intro a b ha _ hab
  exact (S.glueMap_facePerm_glueEmbedding a (S.faceOf_ne_of_mem_darts h hh B a ha)).trans
    (congrArg (fun z => S.glueEmbedding z) hab)

theorem rightDarts_closes (h : X.Face) (hh : h ≠ S.outer) (B : FaceBoundary X h) :
    S.glueMap.facePerm ((S.rightDarts h B).getLast (S.rightDarts_ne_nil h B)) =
      (S.rightDarts h B).head (S.rightDarts_ne_nil h B) := by
  have hlast : (S.rightDarts h B).getLast (S.rightDarts_ne_nil h B) =
      S.glueEmbedding (B.darts.getLast B.nonempty) := List.getLast_map _
  have hhead : (S.rightDarts h B).head (S.rightDarts_ne_nil h B) =
      S.glueEmbedding (B.darts.head B.nonempty) := List.head_map _
  rewrite [hlast, hhead]
  exact (S.glueMap_facePerm_glueEmbedding (B.darts.getLast B.nonempty)
      (S.faceOf_ne_of_mem_darts h hh B _ (List.getLast_mem B.nonempty))).trans
    (congrArg (fun z => S.glueEmbedding z) B.closes)

/-- The ordered boundary of the glued face carrying a face of `X` other than `outer`. -/
def rightFaceBoundary (h : X.Face) (hh : h ≠ S.outer) (B : FaceBoundary X h) :
    FaceBoundary S.glueMap (S.rightFace ⟨h, hh⟩) where
  darts := S.rightDarts h B
  nonempty := S.rightDarts_ne_nil h B
  nodup := S.rightDarts_nodup h B
  mem_iff := S.mem_rightDarts_iff h hh B
  chain := S.rightDarts_chain h hh B
  closes := S.rightDarts_closes h hh B
  length_eq_degree := length_eq_faceDegree_of_nodup S.glueMap _ _
    (S.rightDarts_nodup h B) (S.mem_rightDarts_iff h hh B)

/-! ## An ordered boundary for every glued face -/

variable (FBM : ∀ g : M.Face, FaceBoundary M g) (FBX : ∀ h : X.Face, FaceBoundary X h)

/-- The ordered boundary attached to a glued face, named by the face partition. -/
def glueSumBoundary :
    ∀ s : {f : M.Face // f ∈ S.faces} ⊕ {f : X.Face // f ≠ S.outer},
      FaceBoundary S.glueMap (S.glueFaceEquiv.symm s)
  | Sum.inl g => S.leftFaceBoundary g.1 g.2 (FBM g.1)
  | Sum.inr h => S.rightFaceBoundary h.1 h.2 (FBX h.1)

/-- An ordered boundary for every face of the glued map. -/
def glueFaceBoundary (F : S.glueMap.Face) : FaceBoundary S.glueMap F :=
  S.glueFaceEquiv.symm_apply_apply F ▸ S.glueSumBoundary FBM FBX (S.glueFaceEquiv F)

theorem glueFaceBoundary_darts (F : S.glueMap.Face) :
    (S.glueFaceBoundary FBM FBX F).darts =
      (S.glueSumBoundary FBM FBX (S.glueFaceEquiv F)).darts :=
  faceBoundary_darts_cast _ _

theorem glueFaceBoundary_leftFace_darts (g : M.Face) (hg : g ∈ S.faces) :
    (S.glueFaceBoundary FBM FBX (S.leftFace ⟨g, hg⟩)).darts = S.leftDarts g hg (FBM g) := by
  have hval : S.glueFaceEquiv (S.leftFace ⟨g, hg⟩) = Sum.inl ⟨g, hg⟩ :=
    S.glueFaceEquiv.apply_symm_apply _
  exact (S.glueFaceBoundary_darts FBM FBX _).trans
    (congrArg (fun s => (S.glueSumBoundary FBM FBX s).darts) hval)

theorem glueFaceBoundary_rightFace_darts (h : X.Face) (hh : h ≠ S.outer) :
    (S.glueFaceBoundary FBM FBX (S.rightFace ⟨h, hh⟩)).darts = S.rightDarts h (FBX h) := by
  have hval : S.glueFaceEquiv (S.rightFace ⟨h, hh⟩) = Sum.inr ⟨h, hh⟩ :=
    S.glueFaceEquiv.apply_symm_apply _
  exact (S.glueFaceBoundary_darts FBM FBX _).trans
    (congrArg (fun s => (S.glueSumBoundary FBM FBX s).darts) hval)

/-! ## Labels -/

section Label

variable {L : Type*} (labM : M.Dart → L) (labX : X.Dart → L)

/-- A glued dart takes the label of the dart of `M` or of `X` it comes from. -/
def glueLabel (g : S.GlueDart) : L :=
  Sum.elim (fun d : {d : M.Dart // M.faceOf d ∈ S.faces} => labM d.1)
    (fun x : {x : X.Dart // X.faceOf x ≠ S.outer} => labX x.1) g

theorem glueLabel_glueEmbedding
    (hseam : ∀ b : BoundaryDart M S.faces, labX (S.seamEquiv b).1 = labM b.1) (x : X.Dart) :
    S.glueLabel labM labX (S.glueEmbedding x) = labX x := by
  by_cases hx : X.faceOf x = S.outer
  · obtain ⟨b, hb⟩ := S.seamEquiv.surjective ⟨x, hx⟩
    have hxb : (S.seamEquiv b).1 = x := congrArg Subtype.val hb
    calc S.glueLabel labM labX (S.glueEmbedding x)
        = S.glueLabel labM labX (S.glueEmbedding (S.seamEquiv b).1) := by rw [hxb]
      _ = labM b.1 := congrArg (S.glueLabel labM labX) (S.glueEmbedding_seam b)
      _ = labX (S.seamEquiv b).1 := (hseam b).symm
      _ = labX x := by rw [hxb]
  · exact congrArg (S.glueLabel labM labX) (S.glueEmbedding_of_ne x hx)

theorem glueLabel_alpha (inv : L → L) (hM : ∀ d, labM (M.alpha d) = inv (labM d))
    (hX : ∀ x, labX (X.alpha x) = inv (labX x))
    (hseam : ∀ b : BoundaryDart M S.faces, labX (S.seamEquiv b).1 = labM b.1)
    (g : S.GlueDart) :
    S.glueLabel labM labX (S.glueMap.alpha g) = inv (S.glueLabel labM labX g) := by
  have hemb : ∀ x : X.Dart, S.glueLabel labM labX (S.glueAlpha (S.glueEmbedding x)) =
      inv (S.glueLabel labM labX (S.glueEmbedding x)) := fun x => by
    rewrite [S.glueAlpha_glueEmbedding x, S.glueLabel_glueEmbedding labM labX hseam,
      S.glueLabel_glueEmbedding labM labX hseam]
    exact hX x
  change S.glueLabel labM labX (S.glueAlpha g) = inv (S.glueLabel labM labX g)
  rcases g with d | x
  · by_cases h : M.faceOf (M.alpha d.1) ∈ S.faces
    · rewrite [S.glueAlpha_inl_of_mem d h]
      exact hM d.1
    · have hd : (Sum.inl d : S.GlueDart) = S.glueEmbedding (S.seamEquiv ⟨d.1, d.2, h⟩).1 :=
        (S.glueEmbedding_seam ⟨d.1, d.2, h⟩).symm
      rewrite [hd]
      exact hemb _
  · have hx : (Sum.inr x : S.GlueDart) = S.glueEmbedding x.1 :=
      (S.glueEmbedding_of_ne x.1 x.2).symm
    rewrite [hx]
    exact hemb _

theorem leftDarts_map_glueLabel (g : M.Face) (hg : g ∈ S.faces) (B : FaceBoundary M g) :
    (S.leftDarts g hg B).map (S.glueLabel labM labX) = B.darts.map labM :=
  (List.map_pmap (g := S.glueLabel labM labX) (S.faceOf_mem_of_mem_darts g hg B)).trans
    (List.pmap_eq_map (f := labM) (S.faceOf_mem_of_mem_darts g hg B))

theorem rightDarts_map_glueLabel (h : X.Face) (hh : h ≠ S.outer) (B : FaceBoundary X h) :
    (S.rightDarts h B).map (S.glueLabel labM labX) = B.darts.map labX :=
  (List.map_map).trans (List.map_congr_left fun a ha =>
    congrArg (S.glueLabel labM labX)
      (S.glueEmbedding_of_ne a (S.faceOf_ne_of_mem_darts h hh B a ha)))

theorem glueFaceBoundary_leftFace_word (g : M.Face) (hg : g ∈ S.faces) :
    (S.glueFaceBoundary FBM FBX (S.leftFace ⟨g, hg⟩)).darts.map (S.glueLabel labM labX) =
      (FBM g).darts.map labM := by
  rewrite [S.glueFaceBoundary_leftFace_darts FBM FBX g hg]
  exact S.leftDarts_map_glueLabel labM labX g hg (FBM g)

theorem glueFaceBoundary_rightFace_word (h : X.Face) (hh : h ≠ S.outer) :
    (S.glueFaceBoundary FBM FBX (S.rightFace ⟨h, hh⟩)).darts.map (S.glueLabel labM labX) =
      (FBX h).darts.map labX := by
  rewrite [S.glueFaceBoundary_rightFace_darts FBM FBX h hh]
  exact S.rightDarts_map_glueLabel labM labX h hh (FBX h)

end Label

end Seam

end GroupApproximation.GGT.VanKampen.Surgery.PocketGlue

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.PocketGlue.Seam.leftFaceBoundary
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.PocketGlue.Seam.rightFaceBoundary
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.PocketGlue.Seam.glueFaceBoundary_leftFace_darts
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.PocketGlue.Seam.glueFaceBoundary_rightFace_darts
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.PocketGlue.Seam.glueLabel_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.PocketGlue.Seam.glueFaceBoundary_leftFace_word
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.PocketGlue.Seam.glueFaceBoundary_rightFace_word
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.PocketGlue.Seam.leftFace_ne_rightFace
