import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindCell
import GroupApproximation.Meta.AxiomGuard

/-!
# Cutting stretches out of a walk: the list layer of the `0`-cell excision

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-83.

The excision choice of `F'` (`Piece10Live/GFaceWindCollapse`) removes from the walk of `K` the
darts that stop being boundary darts.  This module holds the list facts, over a Boolean test `b`
(true on the darts kept).

* `gfaceWindCollapse_CutStep M b l l'` (definition): `l = p ++ A ++ q`, `l' = p ++ q`, `b` false
  on `A`, and `A` closes up or sits at one end of `l` (`p = []` or `q = []`).
* `gfaceWindCollapse_chain_step`, `gfaceWindCollapse_filter_step` (proved): a cut keeps a walk a
  walk (`GFaceChoose.gfaceChoose_chain_cut` for a closed stretch, `left_of_append` and
  `right_of_append` at the ends) and does not change the filter by `b`.
* `gfaceWindCollapse_rt` (proved): the same along any finite sequence of cuts.
* `gfaceWindCollapse_block` (proved): a list on which a test is constant is one block for it.

## Truth check

Map-level identities; the check of the assembled construction is in
`Piece10Live/GFaceWindCollapse` (scratchpad `gl-p10-83/cut.py`).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe v

/-- **One cut**: a consecutive stretch `A` of `l`, on which the test `b` is false, is removed;
`A` closes up (its last dart ends where its first starts) or sits at one end of `l`. -/
def gfaceWindCollapse_CutStep (M : CombMap.{v}) (b : M.Dart → Bool) (l l' : List M.Dart) :
    Prop :=
  ∃ p A q : List M.Dart, l = p ++ A ++ q ∧ l' = p ++ q ∧ (∀ x ∈ A, b x = false) ∧
    (p = [] ∨ q = [] ∨
      ∃ hA : A ≠ [], M.vertexOf (M.alpha (A.getLast hA)) = M.vertexOf (A.head hA))

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindCollapse_CutStep

/-- **A cut keeps a walk a walk.** -/
theorem gfaceWindCollapse_chain_step {M : CombMap.{v}} {b : M.Dart → Bool}
    {l l' : List M.Dart} (h : gfaceWindCollapse_CutStep M b l l')
    (hl : l.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) :
    l'.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e := by
  obtain ⟨p, A, q, rfl, rfl, -, hp | hq | ⟨hA, hcl⟩⟩ := h
  · subst hp
    rw [List.nil_append]
    exact hl.right_of_append
  · subst hq
    rw [List.append_nil]
    exact hl.left_of_append.left_of_append
  · exact GFaceChoose.gfaceChoose_chain_cut hA hcl hl

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindCollapse_chain_step

/-- **A cut does not change the filter by the test.** -/
theorem gfaceWindCollapse_filter_step {M : CombMap.{v}} {b : M.Dart → Bool}
    {l l' : List M.Dart} (h : gfaceWindCollapse_CutStep M b l l') :
    l.filter b = l'.filter b := by
  obtain ⟨p, A, q, rfl, rfl, hA, -⟩ := h
  have h0 : A.filter b = [] := List.filter_eq_nil_iff.mpr fun x hx => by
    rw [hA x hx]
    exact Bool.false_ne_true
  simp only [List.filter_append, h0, List.append_nil]

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindCollapse_filter_step

/-- **A sequence of cuts**: it keeps a walk a walk and does not change the filter. -/
theorem gfaceWindCollapse_rt {M : CombMap.{v}} {b : M.Dart → Bool} {l l' : List M.Dart}
    (h : Relation.ReflTransGen (gfaceWindCollapse_CutStep M b) l l')
    (hl : l.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) :
    l.filter b = l'.filter b ∧
      l'.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e := by
  induction h with
  | refl => exact ⟨rfl, hl⟩
  | tail _ hst ih =>
    exact ⟨ih.1.trans (gfaceWindCollapse_filter_step hst),
      gfaceWindCollapse_chain_step hst ih.2⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindCollapse_rt

/-- **A constant test gives one block**: if `b` is true on all of `l` or false on all of `l`,
then the filter of `l` by `b` is a consecutive stretch of `l`. -/
theorem gfaceWindCollapse_block {α : Type*} (l : List α) (b : α → Bool)
    (h : (∀ x ∈ l, b x = true) ∨ ∀ x ∈ l, b x = false) :
    ∃ pre mid post : List α, l = pre ++ mid ++ post ∧ l.filter b = mid := by
  rcases h with h | h
  · exact ⟨[], l, [], by simp, List.filter_eq_self.mpr h⟩
  · refine ⟨l, [], [], by simp, List.filter_eq_nil_iff.mpr fun x hx => ?_⟩
    rw [h x hx]
    exact Bool.false_ne_true

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindCollapse_block

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind
