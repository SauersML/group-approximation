import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkSplit
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkSides
import GroupApproximation.Meta.AxiomGuard

/-!
# A tight closed walk is noncrossing

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, across one relator cell: the touch-only X-pocket.
A tight closed walk (`WalkSplit.IsTightClosedWalk`) carries every turn `d → e` by vertex rotation
from `e` to `alpha d` with no dart of the walk, and no reverse of one, strictly in between.  This
module shows that such a walk with no repeated dart is noncrossing (`IsNoncrossingClosedWalk`), so
the side lemmas of the pocket walks (`SameCellWalkSimple.face_not_mem_sideFaces_sublist`) apply to
it.

The turning condition asks that the first kept dart after `alpha d`, in vertex rotation, be a dart of
the walk.  If it were the reverse `t = alpha d'` of a walk dart, the tight turn from `d'` ends at `t`
with no kept dart strictly inside.  The stretch from `alpha d` to `t` has no kept dart strictly inside
either, and one of the two stretches is a final part of the other.  So either the two start darts
agree, which puts `alpha d` on the walk together with `d`, or one start dart is kept strictly inside
the other stretch.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, Hull's small cancellation theorem, through Osin's
Lemma 9.4, Case 1).  It certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe v

open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides

namespace WalkSplit

variable {M : CombMap.{v}} {walk : List M.Dart}

/-- **Every dart of a tight closed walk turns tightly into a dart of the walk.** -/
theorem IsTightClosedWalk.exists_successor (hw : IsTightClosedWalk M walk) {d : M.Dart}
    (hd : d ∈ walk) : ∃ e ∈ walk, TightTurn M walk d e := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
  by_cases hlast : i + 1 < walk.length
  · exact ⟨walk[i + 1], List.getElem_mem _, List.isChain_iff_getElem.mp hw.chain i hlast⟩
  · have hi' : i = walk.length - 1 := by omega
    subst hi'
    refine ⟨walk.head hw.ne_nil, List.head_mem _, ?_⟩
    have h := hw.closes
    rwa [List.getLast_eq_getElem] at h

/-- Powers of one permutation meeting at a dart: the later start is carried to the earlier one. -/
theorem sigma_pow_eq_of_pow_eq {x y : M.Dart} {a b : ℕ} (hab : a ≤ b)
    (h : (M.sigma ^ a) x = (M.sigma ^ b) y) : x = (M.sigma ^ (b - a)) y := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add, Equiv.Perm.mul_apply] at h
  rw [Nat.add_sub_cancel_left]
  exact (M.sigma ^ a).injective h

/-- **The first kept dart after the reverse of a walk dart.** -/
theorem exists_first_keep {d : M.Dart} (hd : d ∈ walk) :
    ∃ m, 0 < m ∧ walkKeep M walk ((M.sigma ^ m) (M.alpha d)) ∧
      ∀ k, 0 < k → k < m → ¬ walkKeep M walk ((M.sigma ^ k) (M.alpha d)) := by
  classical
  have hex : ∃ m, 0 < m ∧ walkKeep M walk ((M.sigma ^ m) (M.alpha d)) := by
    refine ⟨orderOf M.sigma, orderOf_pos _, ?_⟩
    rw [pow_orderOf_eq_one, Equiv.Perm.one_apply]
    exact Or.inr (by rw [M.alpha_involutive]; exact hd)
  exact ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
    fun k hk hkm hkeep => Nat.find_min hex hkm ⟨hk, hkeep⟩⟩

/-- **A tight closed walk with no repeated dart is noncrossing.** -/
theorem IsTightClosedWalk.isNoncrossingClosedWalk (hw : IsTightClosedWalk M walk)
    (hnodup : walk.Nodup) : IsNoncrossingClosedWalk M walk where
  ne_nil := hw.ne_nil
  nodup := hnodup
  chain := hw.chain.imp fun _ _ h => h.vertexOf_eq
  closes := hw.closes.vertexOf_eq
  alpha_not_mem := hw.alpha_not_mem
  turn_mem := by
    intro d hd
    obtain ⟨k₀, hk₀, hkeep₀, hfirst⟩ := exists_first_keep hd
    refine NoncrossingClosedWalkSides.turn_mem_of_first hk₀ ?_ hfirst
    rcases hkeep₀ with hmem | halpha
    · exact hmem
    · exfalso
      obtain ⟨e', he', n', hn', hnk'⟩ := hw.exists_successor halpha
      rw [M.alpha_involutive] at hn'
      rcases Nat.eq_zero_or_pos n' with hn0 | hnpos
      · rw [hn0, pow_zero, Equiv.Perm.one_apply] at hn'
        exact hw.alpha_not_mem _ (by rw [← hn']; exact he') halpha
      rcases le_or_gt n' k₀ with hle | hlt
      · have heq := sigma_pow_eq_of_pow_eq hle hn'
        rcases Nat.eq_zero_or_pos (k₀ - n') with h0 | hpos
        · rw [h0, pow_zero, Equiv.Perm.one_apply] at heq
          exact hw.alpha_not_mem d hd (by rw [← heq]; exact he')
        · exact hfirst (k₀ - n') hpos (by omega) (by rw [← heq]; exact Or.inl he')
      · have heq := sigma_pow_eq_of_pow_eq hlt.le hn'.symm
        exact hnk' (n' - k₀) (by omega) (by omega)
          (by rw [← heq]; exact Or.inr (by rw [M.alpha_involutive]; exact hd))

end WalkSplit

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.WalkSplit.IsTightClosedWalk.exists_successor
#audit_axioms GroupApproximation.GGT.VanKampen.WalkSplit.IsTightClosedWalk.isNoncrossingClosedWalk
