import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindElevenList
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'`: an inside dart and the repeated or closed inside stretches

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-70.

Setting of `gfaceWindEleven_Statement`: `W` is a lobe of `c`, and `W ++ T` is a rotation of `c`.
Call a stretch `Q` of `T` *inside* when each of its darts has its face on the side of `W`.
* `gfaceWindEleven_inside`: if `W` is not clean, some dart of the rest has its face on the side
  of `W`. A face class from `W` that meets `alpha y` for a rest dart `y` crosses the edge of `y`
  to reach it, since `y` is off `W`, and `alpha y` is off `W` by `not_faceClass_alpha`.
* `gfaceWindEleven_e1`: an inside stretch that repeats a vertex contains a lobe
  (`gfaceWindFive_lobe`), and this lobe is inner to `W`.
* `gfaceWindEleven_e2`: an inside stretch that repeats no vertex and closes up is itself an
  inner lobe.

## Truth check

Scratchpad `gl-p10-70/elevencheck.py` (counts in `GFaceWindEleven`): `INFAIL` = 0, i.e. every
non-clean lobe at a residual state has an inside dart in its rest.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10ExtremalWrap GFaceChoose
open scoped Classical

/-- **A dart of a walk has its face on the side of the walk.** -/
theorem gfaceWindEleven_face_self {M : CombMap.{v}} {W : List M.Dart} {d : M.Dart}
    (hd : d ∈ W) : M.faceOf d ∈ sideFaces M W :=
  (mem_sideFaces_iff M W d).mpr ⟨d, hd, .refl _⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindEleven_face_self

/-- **A non-clean lobe has a rest dart with its face on its side.** -/
theorem gfaceWindEleven_inside {M : CombMap.{v}} (hM : M.IsPlanar) {W R : List M.Dart}
    (hW : IsSimpleClosedWalk M W) (hWR : ∀ x ∈ W, M.alpha x ∉ R)
    (hnc : ¬ gfaceWindEight_Clean M W R) :
    ∃ r ∈ R, M.faceOf r ∈ sideFaces M W := by
  by_contra hno
  apply hnc
  intro d hd y hy
  have hyf : M.faceOf y ∈ sideFaces M W := (mem_sideFaces_iff M W y).mpr ⟨d, hd, hy⟩
  refine ⟨fun hyR => hno ⟨y, hyR, hyf⟩, fun hayR => ?_⟩
  have hk : ¬ walkKeep M W y := by
    rintro (hyW | hayW)
    · exact hWR y hyW hayR
    · exact hW.not_faceClass_alpha hM hd hayW (by rw [M.alpha_involutive y]; exact hy)
  exact hno ⟨M.alpha y, hayR, (mem_sideFaces_iff M W _).mpr
    ⟨d, hd, .trans _ _ _ hy (.rel _ _ (Or.inr ⟨hk, rfl⟩))⟩⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindEleven_inside

/-- **An inside stretch with a repeated vertex yields an inner lobe.** -/
theorem gfaceWindEleven_e1 {M : CombMap.{v}} {c W T : List M.Dart}
    (hZ : (W ++ T).IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    (hal : ∀ x ∈ W ++ T, M.alpha x ∉ W ++ T) (hdis : ∀ x ∈ T, x ∉ W)
    (hlobe : ∀ P L S : List M.Dart, W ++ T = P ++ L ++ S → IsSimpleClosedWalk M L →
      ∃ R : List M.Dart, gfaceWindEight_Lobe M c L R)
    {X Q Y : List M.Dart} (hT : T = X ++ Q ++ Y)
    (hQ : ∀ x ∈ Q, M.faceOf x ∈ sideFaces M W) (hrep : ¬ (Q.map M.vertexOf).Nodup) :
    ∃ W' R' : List M.Dart, gfaceWindEight_Lobe M c W' R' ∧
      (∀ x ∈ W', M.faceOf x ∈ sideFaces M W) ∧ ∃ x ∈ W', x ∉ W := by
  subst hT
  have hchQ : Q.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e :=
    hZ.infix ⟨W ++ X, Y, by simp only [List.append_assoc]⟩
  have hsubQ : ∀ x ∈ Q, x ∈ W ++ (X ++ Q ++ Y) := fun x hx =>
    List.mem_append_right W (List.mem_append_left Y (List.mem_append_right X hx))
  obtain ⟨p, A, q, hseg, hA⟩ := gfaceWindFive_lobe hchQ
    (fun x hx hax => hal x (hsubQ x hx) (hsubQ _ hax)) hrep
  subst hseg
  obtain ⟨R, hR⟩ := hlobe (W ++ X ++ p) A (q ++ Y) (by simp only [List.append_assoc]) hA
  have hAQ : ∀ x ∈ A, x ∈ p ++ A ++ q := fun x hx =>
    List.mem_append_left q (List.mem_append_right p hx)
  refine ⟨A, R, hR, fun x hx => hQ x (hAQ x hx), A.head hA.ne_nil, List.head_mem _, ?_⟩
  exact hdis _ (List.mem_append_left Y (List.mem_append_right X (hAQ _ (List.head_mem _))))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindEleven_e1

/-- **A closed inside stretch without repeated vertex is an inner lobe.** -/
theorem gfaceWindEleven_e2 {M : CombMap.{v}} {c W T : List M.Dart}
    (hZ : (W ++ T).IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    (hal : ∀ x ∈ W ++ T, M.alpha x ∉ W ++ T) (hdis : ∀ x ∈ T, x ∉ W)
    (hlobe : ∀ P L S : List M.Dart, W ++ T = P ++ L ++ S → IsSimpleClosedWalk M L →
      ∃ R : List M.Dart, gfaceWindEight_Lobe M c L R)
    {X Q Y : List M.Dart} (hT : T = X ++ Q ++ Y) (hQ0 : Q ≠ [])
    (hQ : ∀ x ∈ Q, M.faceOf x ∈ sideFaces M W) (hnd : (Q.map M.vertexOf).Nodup)
    (hcl : M.vertexOf (M.alpha (Q.getLast hQ0)) = M.vertexOf (Q.head hQ0)) :
    ∃ W' R' : List M.Dart, gfaceWindEight_Lobe M c W' R' ∧
      (∀ x ∈ W', M.faceOf x ∈ sideFaces M W) ∧ ∃ x ∈ W', x ∉ W := by
  subst hT
  have hchQ : Q.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e :=
    hZ.infix ⟨W ++ X, Y, by simp only [List.append_assoc]⟩
  have hsubQ : ∀ x ∈ Q, x ∈ W ++ (X ++ Q ++ Y) := fun x hx =>
    List.mem_append_right W (List.mem_append_left Y (List.mem_append_right X hx))
  have hQs : IsSimpleClosedWalk M Q :=
    ⟨hQ0, hchQ, hcl, hnd, fun x hx hax => hal x (hsubQ x hx) (hsubQ _ hax)⟩
  obtain ⟨R, hR⟩ := hlobe (W ++ X) Q Y (by simp only [List.append_assoc]) hQs
  refine ⟨Q, R, hR, hQ, Q.head hQ0, List.head_mem _, ?_⟩
  exact hdis _ (List.mem_append_left Y (List.mem_append_right X (List.head_mem _)))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindEleven_e2

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind
