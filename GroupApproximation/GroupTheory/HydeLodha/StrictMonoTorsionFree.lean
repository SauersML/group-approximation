import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import GroupApproximation.Algebra.GroupTorsionFree
import GroupApproximation.Meta.AxiomGuard

/-!
# Order-preserving permutations have no torsion

Hyde–Lodha groups are groups of orientation-preserving homeomorphisms of the line, hence
torsion-free; this is what lets Fournier-Facio embed them in a torsion-free universal group.
Here the groups are realised on `ℚ`, and the same one-line argument applies: if a strictly
increasing permutation moves a point up, every positive power moves it up.

* `eq_one_of_pow_eq_one`: a strictly increasing permutation `f` with `f ^ n = 1`, `n > 0`,
  is the identity.
* `isPowerTorsionFree_of_strictMono`: a subgroup of `Equiv.Perm ℚ` all of whose elements
  are strictly increasing is torsion-free.
-/

namespace GroupApproximation
namespace HydeLodha

theorem lt_pow_apply_of_lt {f : Equiv.Perm ℚ} (hf : StrictMono f) {t : ℚ} (ht : t < f t) :
    ∀ k : ℕ, 0 < k → t < (f ^ k) t := by
  intro k hk
  induction k with
  | zero => exact absurd hk (lt_irrefl 0)
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      simpa using ht
    · have h1 := ih hpos
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact lt_trans ht (hf h1)

theorem pow_apply_lt_of_lt {f : Equiv.Perm ℚ} (hf : StrictMono f) {t : ℚ} (ht : f t < t) :
    ∀ k : ℕ, 0 < k → (f ^ k) t < t := by
  intro k hk
  induction k with
  | zero => exact absurd hk (lt_irrefl 0)
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      simpa using ht
    · have h1 := ih hpos
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact lt_trans (hf h1) ht

/-- **A strictly increasing permutation of finite order is the identity.** -/
theorem eq_one_of_pow_eq_one {f : Equiv.Perm ℚ} (hf : StrictMono f) {n : ℕ} (hn : 0 < n)
    (hpow : f ^ n = 1) : f = 1 := by
  ext t
  rw [Equiv.Perm.one_apply]
  rcases lt_trichotomy t (f t) with h | h | h
  · have h' := lt_pow_apply_of_lt hf h n hn
    rw [hpow, Equiv.Perm.one_apply] at h'
    exact absurd h' (lt_irrefl t)
  · exact h.symm
  · have h' := pow_apply_lt_of_lt hf h n hn
    rw [hpow, Equiv.Perm.one_apply] at h'
    exact absurd h' (lt_irrefl t)

/-- **A group of strictly increasing permutations of `ℚ` is torsion-free.** -/
theorem isPowerTorsionFree_of_strictMono (G : Subgroup (Equiv.Perm ℚ))
    (hG : ∀ f ∈ G, StrictMono f) : IsPowerTorsionFree G := by
  intro g n hn hpow
  have h1 : (g : Equiv.Perm ℚ) ^ n = 1 := by
    have h2 := congrArg (fun x : G => (x : Equiv.Perm ℚ)) hpow
    simpa using h2
  exact Subtype.ext (eq_one_of_pow_eq_one (hG g g.2) hn h1)

#audit_axioms GroupApproximation.HydeLodha.eq_one_of_pow_eq_one
#audit_axioms GroupApproximation.HydeLodha.isPowerTorsionFree_of_strictMono

end HydeLodha
end GroupApproximation
