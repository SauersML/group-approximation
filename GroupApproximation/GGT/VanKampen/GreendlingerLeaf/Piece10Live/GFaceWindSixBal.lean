import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindStep
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'`: closure of the walks along excision sequences

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-61.

Route.  Closure of a walk `c` is recorded as a balance condition: the end vertices of the darts
of `c` are a permutation of their start vertices (`gfaceWindSix_Bal`).  For a nonempty chain
walk this is exactly closure (`gfaceWindSix_bal_iff`), and it is additive: excising a balanced
stretch (a simple closed walk) from a balanced walk leaves a balanced walk
(`gfaceWindSix_bal_cancel`).  So every walk reached by excision steps from a closed walk is
closed (`gfaceWindSix_bal_reach`), and a reached walk that repeats no vertex, is nonempty and
reverses no dart is a simple closed walk (`gfaceWindSix_simple`).

* `gfaceWindSix_Bal` (definition), `gfaceWindSix_map_chain`, `gfaceWindSix_bal_iff` (proved).
* `gfaceWindSix_bal_of_simple`, `gfaceWindSix_bal_cancel` (proved).
* `gfaceWindSix_bal_step`, `gfaceWindSix_bal_reach`, `gfaceWindSix_simple` (proved).

## Truth check

All statements here are proved (no hypothesis Props); list combinatorics only.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe v

open scoped Classical

/-- **A balanced walk**: the end vertices of its darts are a permutation of their start
vertices. -/
def gfaceWindSix_Bal (M : CombMap.{v}) (c : List M.Dart) : Prop :=
  List.Perm (c.map fun d => M.vertexOf (M.alpha d)) (c.map M.vertexOf)

/-- **End vertices along a chain**: shifted start vertices, followed by the last end vertex. -/
theorem gfaceWindSix_map_chain {M : CombMap.{v}} :
    ∀ (d : M.Dart) (l : List M.Dart),
      (d :: l).IsChain (fun a b => M.vertexOf (M.alpha a) = M.vertexOf b) →
      (d :: l).map (fun a => M.vertexOf (M.alpha a)) =
        l.map M.vertexOf ++ [M.vertexOf (M.alpha ((d :: l).getLast (List.cons_ne_nil d l)))]
  | d, [], _ => by simp
  | d, e :: l, h => by
    rw [List.isChain_cons_cons] at h
    have ih := gfaceWindSix_map_chain e l h.2
    calc (d :: e :: l).map (fun a => M.vertexOf (M.alpha a))
        = M.vertexOf (M.alpha d) :: (e :: l).map (fun a => M.vertexOf (M.alpha a)) := rfl
      _ = M.vertexOf e :: (l.map M.vertexOf ++
            [M.vertexOf (M.alpha ((e :: l).getLast (List.cons_ne_nil e l)))]) := by
          rw [ih, h.1]
      _ = (e :: l).map M.vertexOf ++
            [M.vertexOf (M.alpha ((d :: e :: l).getLast (List.cons_ne_nil d (e :: l))))] := rfl

/-- **Balance is closure** for a nonempty chain walk. -/
theorem gfaceWindSix_bal_iff {M : CombMap.{v}} {w : List M.Dart} (hne : w ≠ [])
    (hch : w.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) :
    gfaceWindSix_Bal M w ↔
      M.vertexOf (M.alpha (w.getLast hne)) = M.vertexOf (w.head hne) := by
  obtain ⟨d, l, rfl⟩ := List.exists_cons_of_ne_nil hne
  unfold gfaceWindSix_Bal
  rw [gfaceWindSix_map_chain d l hch]
  show List.Perm (l.map M.vertexOf ++ [M.vertexOf (M.alpha ((d :: l).getLast hne))])
      (M.vertexOf d :: l.map M.vertexOf) ↔
    M.vertexOf (M.alpha ((d :: l).getLast hne)) = M.vertexOf d
  generalize M.vertexOf (M.alpha ((d :: l).getLast hne)) = x
  generalize l.map M.vertexOf = L
  generalize M.vertexOf d = y
  constructor
  · intro h
    have h1 : List.Perm (x :: L) (y :: L) := (List.perm_append_singleton x L).symm.trans h
    exact List.singleton_perm_singleton.mp
      ((List.perm_append_right_iff (l₁ := [x]) (l₂ := [y]) L).mp h1)
  · intro h
    subst h
    exact List.perm_append_singleton _ _

/-- **Simple closed walks are balanced.** -/
theorem gfaceWindSix_bal_of_simple {M : CombMap.{v}} {w : List M.Dart}
    (hw : IsSimpleClosedWalk M w) : gfaceWindSix_Bal M w :=
  (gfaceWindSix_bal_iff hw.ne_nil hw.chain).mpr hw.closes

/-- **Cancelling a balanced stretch**: if `s` is a permutation of `W ++ t` with `s` and `W`
balanced, then `t` is balanced. -/
theorem gfaceWindSix_bal_cancel {M : CombMap.{v}} {s W t : List M.Dart}
    (hp : List.Perm s (W ++ t)) (hs : gfaceWindSix_Bal M s) (hW : gfaceWindSix_Bal M W) :
    gfaceWindSix_Bal M t := by
  unfold gfaceWindSix_Bal at hs hW ⊢
  have h1 := hp.map (fun d => M.vertexOf (M.alpha d))
  have h2 := hp.map M.vertexOf
  rw [List.map_append] at h1 h2
  have h3 : List.Perm (W.map M.vertexOf ++ t.map fun d => M.vertexOf (M.alpha d))
      (W.map M.vertexOf ++ t.map M.vertexOf) :=
    List.Perm.trans (hW.symm.append_right _) (List.Perm.trans h1.symm (List.Perm.trans hs h2))
  exact (List.perm_append_left_iff (W.map M.vertexOf)).mp h3

/-- **One excision step keeps balance.** -/
theorem gfaceWindSix_bal_step {M : CombMap.{v}} {o : M.Face}
    {s t : List M.Dart × (M.Face → ℤ)} (h : gfaceWind_Step M o s t)
    (hs : gfaceWindSix_Bal M s.1) : gfaceWindSix_Bal M t.1 := by
  obtain ⟨p, A, q, hseg, hstep⟩ := h
  rcases hstep with ⟨hw, ht1, -⟩ | ⟨hw, ht1, -⟩
  · rw [ht1]
    refine gfaceWindSix_bal_cancel ?_ hs (gfaceWindSix_bal_of_simple hw)
    rw [hseg, ← List.append_assoc]
    exact List.perm_append_comm.append_right q
  · rw [ht1]
    refine gfaceWindSix_bal_cancel ?_ hs (gfaceWindSix_bal_of_simple hw)
    rw [hseg, List.append_assoc q p A]
    exact List.perm_append_comm

/-- **Excision sequences keep balance.** -/
theorem gfaceWindSix_bal_reach {M : CombMap.{v}} {o : M.Face}
    {s t : List M.Dart × (M.Face → ℤ)} (h : Relation.ReflTransGen (gfaceWind_Step M o) s t)
    (hs : gfaceWindSix_Bal M s.1) : gfaceWindSix_Bal M t.1 := by
  induction h with
  | refl => exact hs
  | tail _ hst ih => exact gfaceWindSix_bal_step hst ih

/-- **A simple closed walk from a balanced one**: a nonempty balanced chain walk that repeats no
vertex and reverses no dart. -/
theorem gfaceWindSix_simple {M : CombMap.{v}} {c : List M.Dart} (hne : c ≠ [])
    (hch : c.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    (hbal : gfaceWindSix_Bal M c) (hnd : (c.map M.vertexOf).Nodup)
    (hal : ∀ x ∈ c, M.alpha x ∉ c) : IsSimpleClosedWalk M c :=
  ⟨hne, hch, (gfaceWindSix_bal_iff hne hch).mp hbal, hnd, hal⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSix_Bal
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSix_map_chain
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSix_bal_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSix_bal_of_simple
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSix_bal_cancel
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSix_bal_step
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSix_bal_reach
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindSix_simple
