import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkPassageInternal
import GroupApproximation.Meta.AxiomGuard

/-!
# The darts strictly inside an adjacent passage are internal to the other side

Osin, arXiv:math/0411039v3, proof of Lemma 9.7(b): "Let us consider the subdiagram `Γ_1` of `Δ`
such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2` ... (ii) `Γ_1` contains all `Γ_{i,1}`'s."

For a noncrossing closed walk `w`, rotating from a walk dart `e`, the next dart lies outside the side
of the walk, and along a free stretch the darts stay outside.  So every dart strictly between `e` and
the end of a free stretch from `e` is internal to the other side
(`IsNoncrossingClosedWalk.internal_sideOutside_of_free`).  For an adjacent passage the stretch from
`w[l+1]` back to `alpha w[l]` is free, and the outer reclosing jumps over it in one first return.

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

/-- **Inside a free stretch from a walk dart, the darts are internal to the other side.** -/
theorem internal_sideOutside_of_free (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    {e : M.Dart} (he : e ∈ w) {b : ℕ}
    (hfree : ∀ k, 0 < k → k < b → ¬ walkKeep M w ((M.sigma ^ k) e))
    {k : ℕ} (hk0 : 0 < k) (hkb : k < b) :
    InternalDart M (sideOutside M w) ((M.sigma ^ k) e) := by
  have hy : M.faceOf (M.sigma e) ∉ sideFaces M w := by
    rw [faceOf_sigma M e]
    exact hw.faceOf_alpha_not_mem_of_mem hM he
  have hya : M.alpha (M.sigma e) ∉ w := fun h =>
    hfree 1 Nat.one_pos (by omega) (Or.inr (by rw [pow_one]; exact h))
  have hpers := hw.faceOf_sigma_pow_not_mem_of_free hM (m := b - 1) hy hya (fun t ht htb => by
    have h' := hfree (t + 1) (by omega) (by omega)
    rwa [pow_succ, Perm.mul_apply] at h')
  have hshift : ∀ t, (M.sigma ^ t) (M.sigma e) = (M.sigma ^ (t + 1)) e :=
    fun t => by rw [pow_succ, Perm.mul_apply]
  have hk : M.faceOf ((M.sigma ^ k) e) ∉ sideFaces M w := by
    have h' := hpers (k - 1) (by omega)
    rwa [hshift, Nat.sub_add_cancel (by omega : 1 ≤ k)] at h'
  have hk1 : M.faceOf (M.alpha ((M.sigma ^ k) e)) ∉ sideFaces M w := by
    have h' := hpers k (by omega)
    rwa [hshift, pow_succ', Perm.mul_apply, faceOf_sigma M] at h'
  exact ⟨(mem_sideOutside_iff M w _).mpr hk, (mem_sideOutside_iff M w _).mpr hk1⟩

end IsNoncrossingClosedWalk

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.internal_sideOutside_of_free
