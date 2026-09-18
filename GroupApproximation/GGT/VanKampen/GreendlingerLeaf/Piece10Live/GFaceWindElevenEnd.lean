import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindElevenStart
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'`: an inside chord at the end of the rest

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-70.

Setting of `gfaceWindEleven_Statement`: `W ++ T` and `T ++ W` are rotations of `c`. Let `Q` be
an inside suffix of `T` (every dart's face on the side of `W`) that
* repeats no vertex and is not closed,
* has its inner vertices (those of `Q.tail`) off `W`, and
* starts at a vertex `vertexOf w` of `W`, with `W = s ++ w :: t`.

`Q` ends where `W` starts, at the head vertex of `W`. So `w` is not the head of `W`, and
`Q ++ s` is a simple closed stretch of `T ++ W`, hence an inner lobe with the dart `Q.head` off
`W` (`gfaceWindEleven_adjEnd`). This mirrors `gfaceWindEleven_adjStart`.

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

/-- **An inside chord at the end of the rest yields an inner lobe.** -/
theorem gfaceWindEleven_adjEnd {M : CombMap.{v}} {c W T : List M.Dart}
    (hW : IsSimpleClosedWalk M W)
    (hZ : (T ++ W).IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    (hal : ∀ x ∈ W ++ T, M.alpha x ∉ W ++ T) (hdis : ∀ x ∈ T, x ∉ W)
    (hlobe : ∀ P L S : List M.Dart, T ++ W = P ++ L ++ S → IsSimpleClosedWalk M L →
      ∃ R : List M.Dart, gfaceWindEight_Lobe M c L R)
    {X Q : List M.Dart} (hT : T = X ++ Q) (hQ0 : Q ≠ [])
    (hQ : ∀ x ∈ Q, M.faceOf x ∈ sideFaces M W) (hnd : (Q.map M.vertexOf).Nodup)
    (hcl : M.vertexOf (M.alpha (Q.getLast hQ0)) ≠ M.vertexOf (Q.head hQ0))
    (hint : ∀ x ∈ Q.tail, M.vertexOf x ∉ W.map M.vertexOf)
    (hst : M.vertexOf (Q.head hQ0) ∈ W.map M.vertexOf) :
    ∃ W' R' : List M.Dart, gfaceWindEight_Lobe M c W' R' ∧
      (∀ x ∈ W', M.faceOf x ∈ sideFaces M W) ∧ ∃ x ∈ W', x ∉ W := by
  subst hT
  obtain ⟨q₀, Q', rfl⟩ := List.exists_cons_of_ne_nil hQ0
  have hQW : ((q₀ :: Q') ++ W).IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e :=
    hZ.infix ⟨X, [], by simp only [List.append_nil, List.append_assoc]⟩
  have hj : M.vertexOf (M.alpha ((q₀ :: Q').getLast hQ0)) = M.vertexOf (W.head hW.ne_nil) :=
    hQW.rel_getLast_head_of_append hQ0 hW.ne_nil
  obtain ⟨w, hwW, hwv⟩ := List.mem_map.mp hst
  have hwq : M.vertexOf w = M.vertexOf q₀ := hwv
  obtain ⟨s, t, hWs⟩ := List.append_of_mem hwW
  have hs : s ≠ [] := by
    rintro rfl
    have hh : W.head hW.ne_nil = w :=
      gfaceWindEleven_head_eq hW.ne_nil (by rw [hWs, List.nil_append])
    exact hcl (hj.trans ((congrArg M.vertexOf hh).trans hwq))
  have hsw : (s ++ w :: t).IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e := by
    rw [← hWs]
    exact hW.chain
  have hjs : M.vertexOf (M.alpha (s.getLast hs)) = M.vertexOf w :=
    hsw.rel_getLast_head_of_append hs (List.cons_ne_nil _ _)
  have hWn : (s.map M.vertexOf ++ (w :: t).map M.vertexOf).Nodup := by
    have h0 := hW.vertex_nodup
    rw [hWs, List.map_append] at h0
    exact h0
  have hsW : ∀ x ∈ s, x ∈ W := fun x hx => by
    rw [hWs]
    exact List.mem_append_left _ hx
  have hLsub : ∀ x ∈ (q₀ :: Q') ++ s, x ∈ W ++ (X ++ (q₀ :: Q')) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_right W (List.mem_append_right X hx)
    · exact List.mem_append_left _ (hsW x hx)
  have hL : IsSimpleClosedWalk M ((q₀ :: Q') ++ s) := by
    refine ⟨List.append_ne_nil_of_left_ne_nil (List.cons_ne_nil _ _) _,
      hZ.infix ⟨X, w :: t, ?_⟩, ?_, ?_, fun x hx hax => hal x (hLsub x hx) (hLsub _ hax)⟩
    · rw [hWs]
      simp only [List.append_assoc]
    · rw [List.getLast_append_of_ne_nil _ hs, List.head_append_of_ne_nil (List.cons_ne_nil q₀ Q'),
        List.head_cons]
      exact hjs.trans hwq
    · rw [List.map_append, List.nodup_append]
      refine ⟨hnd, (List.nodup_append.mp hWn).1, ?_⟩
      intro a ha b hb hab
      obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
      obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
      rcases List.mem_cons.mp ha' with ha0 | ha1
      · rw [ha0] at hab
        exact (List.nodup_append.mp hWn).2.2 _ (List.mem_map_of_mem hb') _
          (List.mem_map_of_mem (List.mem_cons_self (a := w) (l := t))) (hab.symm.trans hwq.symm)
      · refine hint a' ha1 ?_
        rw [hab]
        exact List.mem_map_of_mem (hsW b' hb')
  obtain ⟨R, hR⟩ := hlobe X ((q₀ :: Q') ++ s) (w :: t)
    (by rw [hWs]; simp only [List.append_assoc]) hL
  refine ⟨_, R, hR, ?_, q₀, List.mem_append_left _ List.mem_cons_self,
    hdis q₀ (List.mem_append_right X List.mem_cons_self)⟩
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hQ x hx
  · exact gfaceWindEleven_face_self (hsW x hx)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindEleven_adjEnd

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind
