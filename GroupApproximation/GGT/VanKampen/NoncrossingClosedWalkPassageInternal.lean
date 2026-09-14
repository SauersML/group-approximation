import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkVertexKind
import GroupApproximation.Meta.AxiomGuard

/-!
# The darts strictly inside a free passage are internal to one side

Osin, arXiv:math/0411039v3, proof of Lemma 9.7(b): "Let us consider the subdiagram `Γ_1` of `Δ`
such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2` ... (ii) `Γ_1` contains all `Γ_{i,1}`'s."

For a noncrossing closed walk `w`, rotating from the reversal `alpha w[l]` of a walk dart, the next
dart lies on the side of the walk; along a free sector the darts stay there, so every dart strictly
before `w[l+1]` is internal to the side (`IsNoncrossingClosedWalk.internal_sideFaces_of_short`).
Rotating from a walk dart `w[l+1]`, the next dart lies outside; along a free stretch every dart
strictly before `alpha w[l]` is internal to the other side
(`IsNoncrossingClosedWalk.internal_sideOutside_of_free`, `NoncrossingClosedWalkPassageInternalOuter`).
So the inner reclosing jumps over the first stretch in one first return, and the outer reclosing over
the second.

* `IsNoncrossingClosedWalk.faceOf_sigma_pow_mem_of_free`: on the side persists along a free stretch.
* `IsNoncrossingClosedWalk.internal_sideFaces_of_short`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(b);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv Surgery.MapCollapse SimpleClosedWalkSides

universe u

namespace IsNoncrossingClosedWalk

variable {M : CombMap.{u}} {w : List M.Dart}

/-- **On the side persists along a free stretch.**  If `y` is based on the side of the walk, is not a
walk dart, and no dart strictly between `y` and `sigma^m y` lies on an edge of the walk, then
`sigma^k y` is based on the side for every `k ≤ m`. -/
theorem faceOf_sigma_pow_mem_of_free (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    {y : M.Dart} {m : ℕ} (hy : M.faceOf y ∈ sideFaces M w) (hyw : y ∉ w)
    (hfree : ∀ k, 0 < k → k < m → ¬ walkKeep M w ((M.sigma ^ k) y)) :
    ∀ k, k ≤ m → M.faceOf ((M.sigma ^ k) y) ∈ sideFaces M w := by
  intro k
  induction k with
  | zero => intro _; rw [pow_zero, Perm.one_apply]; exact hy
  | succ k ih =>
    intro hk
    have hprev := ih (by omega)
    have hpw : (M.sigma ^ k) y ∉ w := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0, pow_zero, Perm.one_apply]; exact hyw
      · exact fun h => hfree k h0 (by omega) (Or.inl h)
    by_contra hnot
    rw [pow_succ', Perm.mul_apply] at hnot
    exact hpw (hw.mem_of_faceOf_sigma_not_mem hM hprev hnot)

/-- **Inside a free sector from the reversal of a walk dart, the darts are internal to the side.** -/
theorem internal_sideFaces_of_short (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    {d : M.Dart} (hd : d ∈ w) {a : ℕ}
    (hfree : ∀ k, 0 < k → k < a → ¬ walkKeep M w ((M.sigma ^ k) (M.alpha d)))
    {k : ℕ} (hk0 : 0 < k) (hka : k < a) :
    InternalDart M (sideFaces M w) ((M.sigma ^ k) (M.alpha d)) := by
  have hy : M.faceOf (M.sigma (M.alpha d)) ∈ sideFaces M w := by
    rw [faceOf_sigma M (M.alpha d), M.alpha_involutive d]
    exact hw.faceOf_mem_of_mem hM hd
  have hyw : M.sigma (M.alpha d) ∉ w := fun h =>
    hfree 1 Nat.one_pos (by omega) (Or.inl (by rw [pow_one]; exact h))
  have hpers := hw.faceOf_sigma_pow_mem_of_free hM (m := a - 1) hy hyw (fun t ht hta => by
    have h' := hfree (t + 1) (by omega) (by omega)
    rwa [pow_succ, Perm.mul_apply] at h')
  have hshift : ∀ t, (M.sigma ^ t) (M.sigma (M.alpha d)) = (M.sigma ^ (t + 1)) (M.alpha d) :=
    fun t => by rw [pow_succ, Perm.mul_apply]
  have hk : M.faceOf ((M.sigma ^ k) (M.alpha d)) ∈ sideFaces M w := by
    have h' := hpers (k - 1) (by omega)
    rwa [hshift, Nat.sub_add_cancel (by omega : 1 ≤ k)] at h'
  refine ⟨hk, ?_⟩
  rcases Nat.lt_or_ge (k + 1) a with hka' | hka'
  · have h' := hpers k (by omega)
    rw [hshift, pow_succ', Perm.mul_apply, faceOf_sigma M] at h'
    exact h'
  · -- `k + 1 = a`: the next dart is not on an edge of the walk only if it is `w`-free; use membership
    by_contra hnot
    have hkw : (M.sigma ^ k) (M.alpha d) ∉ w := fun h => hfree k hk0 hka (Or.inl h)
    exact hkw (hw.mem_of_faceOf_sigma_not_mem hM hk (by rwa [faceOf_sigma M]))

end IsNoncrossingClosedWalk

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.faceOf_sigma_pow_mem_of_free
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.internal_sideFaces_of_short
