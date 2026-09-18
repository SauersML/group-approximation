import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindElevenCase
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'`: an inside chord at the start of the rest

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-70.

Setting of `gfaceWindEleven_Statement`: `W ++ T` is a rotation of `c`. Let `Q` be an inside
prefix of `T` (every dart's face on the side of `W`) that
* repeats no vertex and is not closed,
* has its inner vertices (those of `Q.tail`) off `W`, and
* ends at a vertex `vertexOf w` of `W`, with `W = s ++ w :: t`.

`Q` starts where `W` closes, at the head vertex of `W`. So `w` is not the head of `W`, and
`(w :: t) ++ Q` is a simple closed stretch of `W ++ T`, hence an inner lobe with the dart
`Q.head` off `W` (`gfaceWindEleven_adjStart`).

## Truth check

Scratchpad `gl-p10-70/elevencheck.py`: `EASYFAIL` = 0 over all residual states checked (counts in
`GFaceWindEleven`).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10ExtremalWrap GFaceChoose
open scoped Classical

/-- **An inside chord at the start of the rest yields an inner lobe.** -/
theorem gfaceWindEleven_adjStart {M : CombMap.{v}} {c W T : List M.Dart}
    (hW : IsSimpleClosedWalk M W)
    (hZ : (W ++ T).IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    (hal : ∀ x ∈ W ++ T, M.alpha x ∉ W ++ T) (hdis : ∀ x ∈ T, x ∉ W)
    (hlobe : ∀ P L S : List M.Dart, W ++ T = P ++ L ++ S → IsSimpleClosedWalk M L →
      ∃ R : List M.Dart, gfaceWindEight_Lobe M c L R)
    {Q Y : List M.Dart} (hT : T = Q ++ Y) (hQ0 : Q ≠ [])
    (hQ : ∀ x ∈ Q, M.faceOf x ∈ sideFaces M W) (hnd : (Q.map M.vertexOf).Nodup)
    (hcl : M.vertexOf (M.alpha (Q.getLast hQ0)) ≠ M.vertexOf (Q.head hQ0))
    (hint : ∀ x ∈ Q.tail, M.vertexOf x ∉ W.map M.vertexOf)
    (hend : M.vertexOf (M.alpha (Q.getLast hQ0)) ∈ W.map M.vertexOf) :
    ∃ W' R' : List M.Dart, gfaceWindEight_Lobe M c W' R' ∧
      (∀ x ∈ W', M.faceOf x ∈ sideFaces M W) ∧ ∃ x ∈ W', x ∉ W := by
  subst hT
  obtain ⟨q₀, Q', rfl⟩ := List.exists_cons_of_ne_nil hQ0
  have hWQ : (W ++ (q₀ :: Q')).IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e :=
    hZ.infix ⟨[], Y, by simp only [List.nil_append, List.append_assoc]⟩
  have hj : M.vertexOf (M.alpha (W.getLast hW.ne_nil)) = M.vertexOf q₀ :=
    hWQ.rel_getLast_head_of_append hW.ne_nil (List.cons_ne_nil _ _)
  have hstart : M.vertexOf q₀ = M.vertexOf (W.head hW.ne_nil) := hj.symm.trans hW.closes
  obtain ⟨w, hwW, hwv⟩ := List.mem_map.mp hend
  obtain ⟨s, t, hWs⟩ := List.append_of_mem hwW
  have hs : s ≠ [] := by
    rintro rfl
    have hh : W.head hW.ne_nil = w :=
      gfaceWindEleven_head_eq hW.ne_nil (by rw [hWs, List.nil_append])
    exact hcl (hwv.symm.trans ((congrArg M.vertexOf hh).symm.trans hstart.symm))
  have hWn : (s.map M.vertexOf ++ (w :: t).map M.vertexOf).Nodup := by
    have h0 := hW.vertex_nodup
    rw [hWs, List.map_append] at h0
    exact h0
  have hsh : W.head hW.ne_nil ∈ s := gfaceWindEleven_head_mem hW.ne_nil hWs hs
  have hwtW : ∀ x ∈ w :: t, x ∈ W := fun x hx => by
    rw [hWs]
    exact List.mem_append_right s hx
  have hLsub : ∀ x ∈ (w :: t) ++ (q₀ :: Q'), x ∈ W ++ ((q₀ :: Q') ++ Y) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (hwtW x hx)
    · exact List.mem_append_right W (List.mem_append_left Y hx)
  have hL : IsSimpleClosedWalk M ((w :: t) ++ (q₀ :: Q')) := by
    refine ⟨List.append_ne_nil_of_left_ne_nil (List.cons_ne_nil _ _) _,
      hZ.infix ⟨s, Y, ?_⟩, ?_, ?_, fun x hx hax => hal x (hLsub x hx) (hLsub _ hax)⟩
    · rw [hWs]
      simp only [List.append_assoc]
    · rw [List.getLast_append_of_ne_nil _ hQ0, List.head_append_of_ne_nil (List.cons_ne_nil w t),
        List.head_cons]
      exact hwv.symm
    · rw [List.map_append, List.nodup_append]
      refine ⟨(List.nodup_append.mp hWn).2.1, hnd, ?_⟩
      intro a ha b hb hab
      obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
      obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
      rcases List.mem_cons.mp hb' with hb0 | hb1
      · rw [hb0] at hab
        exact (List.nodup_append.mp hWn).2.2 _ (List.mem_map_of_mem hsh) _
          (List.mem_map_of_mem ha') (hab.trans hstart).symm
      · refine hint b' hb1 ?_
        rw [← hab]
        exact List.mem_map_of_mem (hwtW a' ha')
  obtain ⟨R, hR⟩ := hlobe s ((w :: t) ++ (q₀ :: Q')) Y
    (by rw [hWs]; simp only [List.append_assoc]) hL
  refine ⟨_, R, hR, ?_, q₀, List.mem_append_right _ List.mem_cons_self,
    hdis q₀ (List.mem_append_left Y List.mem_cons_self)⟩
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact gfaceWindEleven_face_self (hwtW x hx)
  · exact hQ x hx

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindEleven_adjStart

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind
