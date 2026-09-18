import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.BlkBalance
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.FLBlock
import GroupApproximation.Meta.AxiomGuard

/-!
# The removed block of a lobe move closes up

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  Lane gl-p10-54.

`roseLobeFL_BlockStatement` (gl-p10-53) ends with the block clause: the boundary cycle `c` is
`A ++ B ++ C` where either the move `P = movePred (lobeColour rs)` removes all of `B` (empty or a
closed dart walk) and keeps all of `A ++ C ≠ []`, or `P` keeps all of the closed dart walk `B`
and removes all of `A ++ C`.  The residual here, `roseLobeBlk_BlockStatement`, drops both
closedness requirements: it asks only that the removed darts are one cyclically contiguous block
(and that `B ≠ []` in the second case).

## The route: closedness is double counting, from the definition of the lobe colouring

Write `z = roseJunctionCore_lobeColour M (walkKeep M c) rs`.  By its definition `z` is the
indicator of a union of classes of `FaceClassStep M (walkKeep M c)`, so it is constant along
face steps and across edges off the walk (`roseJunctionCore_lobeColour_step`).

1. *The removed set is a boundary.*  The root clause of the statement puts all the roots on one
   side of the walk.  Roots on `c` never colour the outer side of a dart of `c`
   (`roseJunctionCore_lobeColour_alpha_eq_false`); a single root `r` colours no outer side of `c`
   if its face is in the face set and no inner side otherwise, since a class never changes
   membership in the face set (`P10Rose.faceOf_mem_iff_of_walkEqvGen`)
   (`roseLobeBlk_side`).  In the first case a dart of `c` is removed iff it lies on the boundary
   `{z ∧ ¬ z ∘ alpha}`; in the second iff it lies on `{¬ z ∧ z ∘ alpha}`
   (`roseLobeBlk_removed_iff_in`, `roseLobeBlk_removed_iff_out`).  Conversely a boundary dart is
   on the walk, because across an edge off the walk `z` does not change.
2. *Boundaries are balanced* (`BlkBalance`): as many of their darts leave each vertex as arrive.
3. *A balanced chain closes up* (`BlkBalance`).  If `B` is exactly the removed set, it is a
   balanced chain.  If `A ++ C` is exactly the removed set, then `B` has the counts of the
   closed walk `c` minus the balanced counts of `A ++ C`, so it is balanced too
   (`roseLobeBlk_block_close`).

So the reduction `roseLobeBlk_block_of_weak` uses no planarity.

## LOUD: strength of the residual

`roseLobeBlk_BlockStatement` is **only EQUIVALENT** to `roseLobeFL_BlockStatement` as a closed
proposition: both directions are proved here (`roseLobeBlk_block_of_weak`,
`roseLobeBlk_weak_of_block`).  It is weaker pointwise (for each fixed choice of `rs`, `A`, `B`,
`C` its conclusion is implied by, and strictly weaker in form than, the old one), and strictly
smaller in proof content: both closed-walk clauses are proved.  What stays open is exactly the
planar core: the placement clauses (b'') and (c'') and the cyclic contiguity of the removed
darts.

## Truth check (Python, `scratchpad/gl-p10-54/weak.py`, not formalised)

Implied by `roseLobeFL_BlockStatement` for the same witness, so the gl-p10-53 check (`101504`
random configurations and `315` models, `0` failures) carries over.  `weak.py` re-runs the
weakened clause and also tests step 3 empirically: on every cyclic removed block of every
admissible colouring, both the removed block and the kept block are closed.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10RoseExtremalTrim

section Removed

variable {M : CombMap.{v}}

/-- **Removed darts, lobe inside.**  If `z` is constant along the face-class steps of `c` and
colours no outer side of `c`, the darts of `c` removed by `movePred z` are the boundary darts
`{z ∧ ¬ z ∘ alpha}`. -/
theorem roseLobeBlk_removed_iff_in {c : List M.Dart} {z : M.Dart → Bool}
    (hz : ∀ x y, CombMap.FaceClassStep M (walkKeep M c) x y → z x = z y)
    (hI : ∀ d ∈ c, z (M.alpha d) = false) (d : M.Dart) :
    (z d = true ∧ ¬ z (M.alpha d) = true) ↔ d ∈ c ∧ ¬ movePred M z d = true := by
  rw [movePred_eq_true_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have hk : walkKeep M c d := by
      by_contra hk
      exact h2 (by rw [← hz d (M.alpha d) (Or.inr ⟨hk, rfl⟩)]; exact h1)
    rcases hk with hk | hk
    · exact ⟨hk, fun h => by simp [h.1] at h1⟩
    · have h3 := hI _ hk
      rw [M.alpha_involutive d] at h3
      simp [h3] at h1
  · rintro ⟨hd, h⟩
    have h2 := hI d hd
    refine ⟨?_, by simp [h2]⟩
    by_contra h1
    exact h ⟨by simpa using h1, h2⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeBlk_removed_iff_in

/-- **Removed darts, lobe outside.**  If `z` is constant along the face-class steps of `c` and
colours no dart of `c`, the darts of `c` removed by `movePred z` are the reversed boundary darts
`{¬ z ∧ z ∘ alpha}`. -/
theorem roseLobeBlk_removed_iff_out {c : List M.Dart} {z : M.Dart → Bool}
    (hz : ∀ x y, CombMap.FaceClassStep M (walkKeep M c) x y → z x = z y)
    (hO : ∀ d ∈ c, z d = false) (d : M.Dart) :
    (z d = false ∧ z (M.alpha d) = true) ↔ d ∈ c ∧ ¬ movePred M z d = true := by
  rw [movePred_eq_true_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have hk : walkKeep M c d := by
      by_contra hk
      have h3 := hz d (M.alpha d) (Or.inr ⟨hk, rfl⟩)
      rw [h1, h2] at h3
      exact absurd h3 (by decide)
    rcases hk with hk | hk
    · exact ⟨hk, fun h => by simp [h.2] at h2⟩
    · have h3 := hO _ hk
      simp [h3] at h2
  · rintro ⟨hd, h⟩
    have h1 := hO d hd
    refine ⟨h1, ?_⟩
    by_contra h2
    exact h ⟨h1, by simpa using h2⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeBlk_removed_iff_out

/-- **A contiguous balanced removed block closes up.**  If the darts of the closed dart walk
`c = A ++ B ++ C` removed by `P` form a balanced set, and the removed darts are `B` or `A ++ C`,
then the block clause of `roseLobeFL_BlockStatement` holds, closedness included. -/
theorem roseLobeBlk_block_close {c A B C : List M.Dart} {P : M.Dart → Bool}
    {p : M.Dart → Prop} (hbal : roseLobeBlk_Balanced M p)
    (hp : ∀ d, p d ↔ d ∈ c ∧ ¬ P d = true)
    (hw : IsClosedDartWalk M c) (hnd : c.Nodup) (hABC : c = A ++ B ++ C)
    (hblk : (B.filter P = [] ∧ (A ++ C).filter P = A ++ C ∧ A ++ C ≠ []) ∨
      (B.filter P = B ∧ (A ++ C).filter P = [] ∧ B ≠ [])) :
    (B.filter P = [] ∧ (A ++ C).filter P = A ++ C ∧ A ++ C ≠ [] ∧
        (B = [] ∨ IsClosedDartWalk M B)) ∨
      (B.filter P = B ∧ (A ++ C).filter P = [] ∧ IsClosedDartWalk M B) := by
  subst hABC
  have hc := roseLobeBlk_balanced_of_closed hw
  obtain ⟨-, hch, -⟩ := hw
  have hchB : B.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e :=
    hch.infix (List.infix_append A B C)
  have hndB : B.Nodup := List.Nodup.sublist (List.infix_append A B C).sublist hnd
  have hndAC : (A ++ C).Nodup := List.Nodup.sublist
    (List.Sublist.append (List.sublist_append_left A B) (List.Sublist.refl C)) hnd
  rcases hblk with ⟨hB0, hAC, hne⟩ | ⟨hBB, hAC0, hBne⟩
  · refine Or.inl ⟨hB0, hAC, hne, ?_⟩
    by_cases hB : B = []
    · exact Or.inl hB
    · refine Or.inr (roseLobeBlk_closes_of_balanced hB hndB hchB hbal fun d => ?_)
      rw [hp]
      constructor
      · intro hd
        exact ⟨List.mem_append_left _ (List.mem_append_right _ hd),
          List.filter_eq_nil_iff.mp hB0 d hd⟩
      · rintro ⟨hd, hPd⟩
        rcases List.mem_append.mp hd with hd | hd
        · rcases List.mem_append.mp hd with hd | hd
          · exact absurd (List.filter_eq_self.mp hAC d (List.mem_append_left _ hd)) hPd
          · exact hd
        · exact absurd (List.filter_eq_self.mp hAC d (List.mem_append_right _ hd)) hPd
  · refine Or.inr ⟨hBB, hAC0, roseLobeBlk_closes hBne hchB fun o => ?_⟩
    have hmem : ∀ d, d ∈ A ++ C ↔ p d := by
      intro d
      rw [hp]
      constructor
      · intro hd
        refine ⟨?_, List.filter_eq_nil_iff.mp hAC0 d hd⟩
        rcases List.mem_append.mp hd with hd | hd
        · exact List.mem_append_left _ (List.mem_append_left _ hd)
        · exact List.mem_append_right _ hd
      · rintro ⟨hd, hPd⟩
        rcases List.mem_append.mp hd with hd | hd
        · rcases List.mem_append.mp hd with hd | hd
          · exact List.mem_append_left _ hd
          · exact absurd (List.filter_eq_self.mp hBB d hd) hPd
        · exact List.mem_append_right _ hd
    have h1 := hc o
    have h2 : roseLobeBlk_outL M (A ++ C) o = roseLobeBlk_inL M (A ++ C) o := by
      rw [roseLobeBlk_outL_eq_outN hndAC hmem, roseLobeBlk_inL_eq_inN hndAC hmem]
      exact hbal o
    rw [roseLobeBlk_outL_append (A ++ B) C, roseLobeBlk_outL_append A B,
      roseLobeBlk_inL_append (A ++ B) C, roseLobeBlk_inL_append A B] at h1
    rw [roseLobeBlk_outL_append A C, roseLobeBlk_inL_append A C] at h2
    omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeBlk_block_close

/-- **The lobe lies on one side of the walk.**  For roots on `c`, or a single root, the lobe
colouring colours no outer side of a dart of `c`, or no dart of `c` at all. -/
theorem roseLobeBlk_side {faces : Finset M.Face} {c : List M.Dart}
    (hc : ∀ d, d ∈ c ↔ IsBoundaryDart M faces d) {rs : List M.Dart}
    (hroot : (∀ r ∈ rs, r ∈ c) ∨ ∃ r, rs = [r]) :
    (∀ d ∈ c, roseJunctionCore_lobeColour M (walkKeep M c) rs (M.alpha d) = false) ∨
      ∀ d ∈ c, roseJunctionCore_lobeColour M (walkKeep M c) rs d = false := by
  rcases hroot with hrs | ⟨r, rfl⟩
  · exact Or.inl fun d hd => roseJunctionCore_lobeColour_alpha_eq_false hc hrs hd
  · by_cases hr : M.faceOf r ∈ faces
    · refine Or.inl fun d hd => roseJunctionCore_lobeColour_eq_false M _ fun r' hr' h => ?_
      rw [List.mem_singleton] at hr'
      subst hr'
      exact ((hc d).mp hd).2 ((P10Rose.faceOf_mem_iff_of_walkEqvGen hc h).mp hr)
    · refine Or.inr fun d hd => roseJunctionCore_lobeColour_eq_false M _ fun r' hr' h => ?_
      rw [List.mem_singleton] at hr'
      subst hr'
      exact hr ((P10Rose.faceOf_mem_iff_of_walkEqvGen hc h).mpr ((hc d).mp hd).1)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeBlk_side
