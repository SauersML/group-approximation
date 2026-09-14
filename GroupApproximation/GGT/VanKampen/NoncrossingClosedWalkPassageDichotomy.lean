import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkPassageKinds
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkRotationSides
import GroupApproximation.Meta.AxiomGuard

/-!
# Along a free stretch the darts stay outside, and an adjacent passage is alone

Osin, arXiv:math/0411039v3, proof of Lemma 9.7(b): "Let us consider the subdiagram `Γ_1` of `Δ`
such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2` ... (ii) `Γ_1` contains all `Γ_{i,1}`'s."

For a noncrossing closed walk `w` whose passages have free sectors, the passage at position `i` is
adjacent when the stretch from `w[i+1]` back to `alpha w[i]` is free.  Rotating from a walk dart, the
darts stay outside the side of the walk until the reversal of a walk dart
(`faceOf_sigma_pow_not_mem_of_free`).  If the stretch from `w[i+1]` to `alpha w[j]` is free and the
passage at `j` is adjacent, the two stretches end at one dart, so `w[i+1] = w[j+1]` and `i = j`
(`eq_of_adjacent_of_free`).  Rotation around a vertex therefore never passes from a passage that is not
adjacent to an adjacent one.

* `IsNoncrossingClosedWalk.faceOf_sigma_pow_not_mem_of_free`: outside persists along a free stretch.
* `SectorNoninterleaving.eq_of_adjacent_of_free`: an adjacent passage is the only passage whose free
  stretch ends at its reversal.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(b);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv SimpleClosedWalkSides SectorNoninterleaving

universe u

namespace IsNoncrossingClosedWalk

variable {M : CombMap.{u}} {w : List M.Dart}

/-- **Outside persists along a free stretch.**  If `y` is based outside the side of the walk, its
reversal is not a walk dart, and no dart strictly between `y` and `sigma^m y` lies on an edge of the
walk, then `sigma^k y` is based outside the side for every `k ≤ m`. -/
theorem faceOf_sigma_pow_not_mem_of_free (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    {y : M.Dart} {m : ℕ} (hy : M.faceOf y ∉ sideFaces M w) (hya : M.alpha y ∉ w)
    (hfree : ∀ k, 0 < k → k < m → ¬ walkKeep M w ((M.sigma ^ k) y)) :
    ∀ k, k ≤ m → M.faceOf ((M.sigma ^ k) y) ∉ sideFaces M w := by
  intro k
  induction k with
  | zero => intro _; rw [pow_zero, Perm.one_apply]; exact hy
  | succ k ih =>
    intro hk
    have hprev := ih (by omega)
    have hpa : M.alpha ((M.sigma ^ k) y) ∉ w := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0, pow_zero, Perm.one_apply]; exact hya
      · exact fun h => hfree k h0 (by omega) (Or.inr h)
    intro hmem
    rw [pow_succ', Perm.mul_apply] at hmem
    exact hpa (hw.alpha_mem_of_faceOf_sigma_mem hM hprev hmem)

end IsNoncrossingClosedWalk

namespace SectorNoninterleaving

variable {M : CombMap.{u}} {w : List M.Dart}

/-- **An adjacent passage is the only passage whose free stretch ends at its reversal.**  If the
stretch from `w[j+1]` back to `alpha w[j]` is free, and the stretch from `w[i+1]` to `alpha w[j]` is
free, then `i = j`. -/
theorem eq_of_adjacent_of_free (hnodup : w.Nodup) (halpha : ∀ d ∈ w, M.alpha d ∉ w)
    {i j : Fin w.length}
    (hadj : SectorFree M w (w.get (finRotate w.length j)) (M.alpha (w.get j)))
    (hfree : SectorFree M w (w.get (finRotate w.length i)) (M.alpha (w.get j))) : i = j := by
  have hmem : ∀ k : Fin w.length, w.get k ∈ w := fun k => List.get_mem w k
  have hx : ∀ k : Fin w.length, w.get (finRotate w.length k) ≠ M.alpha (w.get j) := fun k h =>
    halpha _ (hmem j) (by rw [← h]; exact hmem _)
  have heq := eq_of_sectorFree_rev_both hfree hadj (Or.inl (hmem _)) (Or.inl (hmem _)) (hx i) (hx j)
  exact (finRotate w.length).injective (hnodup.get_inj_iff.mp heq)

end SectorNoninterleaving

end GroupApproximation.GGT.VanKampen

#audit_axioms
  GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.faceOf_sigma_pow_not_mem_of_free
#audit_axioms GroupApproximation.GGT.VanKampen.SectorNoninterleaving.eq_of_adjacent_of_free
