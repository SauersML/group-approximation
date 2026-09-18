import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalJordanPickCount
import GroupApproximation.Meta.AxiomGuard

/-!
# The parity clause: the sign argument

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-43.

`ExtremalJordanPickCountParity K` (lane gl-p10-41) says `excess = 2 → #O ≠ 2`.  This file proves
it from one comparison of a class count with an orbit count.

**The sign argument.**  Let `c` be the walk and `m` its length.  Let `f` be a permutation of the
darts that fixes every dart off `c` and satisfies

  `f (next d) = d  ↔  d is a first passage`  for `d ∈ c`.

Put `h = f * formPerm c`.  Then `h d ≠ d` exactly for the non-first passages
(`extremalJordanPickCountParity_support_eq`).
* With `excess = 2` there are exactly three non-first passages
  (`extremalJordanPickCountParity_card_nonFirst`).  The proved local lemma
  `ExtremalJordanPickEulerThreeAtVertex` gives `n_x = 0 ∨ n_x ≥ 3` at every vertex.  So
  `2 Σ n_x ≤ 3 Σ (n_x - 1) = 6`, and some `n_x ≥ 3`.
* So `h` has support of size three.  It is a 3-cycle, with sign `1`.
* `formPerm c` is an `m`-cycle, with sign `-(-1)^m`.  So `sign f = -(-1)^m`.
* The number of orbits of `f` on `c` is `(m - #supp f) + #cycleType f`.  Its sign is
  `(-1)^(#supp f + #cycleType f) = sign f`.  So this number is odd
  (`extremalJordanPickCountParity_perm_odd`).

So if `#O` has the parity of the orbit count of `f` on `c`, then `#O` is odd and `#O ≠ 2`
(`extremalJordanPickCountParity_of_perm`).  The concrete `f` is `α ∘ σ_P` on the walk map
(`ExtremalJordanPickCountParityPerm.lean`).  The remaining class count is isolated in
`ExtremalJordanPickCountParityCycles.lean`.

## Mathematical infrastructure

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
no manuscript citation of its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open scoped Classical

section ParityAbstract

/-- **Parity from signs**: equal powers of `-1` in `ℤˣ` have exponents of equal parity. -/
theorem extremalJordanPickCountParity_mod_two_eq {a b : ℕ}
    (h : (-1 : ℤˣ) ^ a = (-1) ^ b) : a % 2 = b % 2 := by
  rw [Int.units_pow_eq_pow_mod_two (-1) a, Int.units_pow_eq_pow_mod_two (-1) b] at h
  have hne : (1 : ℤˣ) ≠ -1 := units_ne_neg_self 1
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
    rw [ha, hb] at h
  · omega
  · rw [pow_zero, pow_one] at h
    exact absurd h hne
  · rw [pow_zero, pow_one] at h
    exact absurd h.symm hne
  · omega

/-- **The sign argument.**  Let `f` fix every point off a duplicate-free list `l`.  If
`f * formPerm l` moves exactly three points, then the number of orbits of `f` on `l`, namely
`#l - #supp f + #cycleType f`, is odd. -/
theorem extremalJordanPickCountParity_perm_odd {α : Type*} [Fintype α] [DecidableEq α]
    (l : List α) (hl : l.Nodup) (f : Equiv.Perm α) (hf : ∀ x, x ∉ l → f x = x)
    (h3 : (f * l.formPerm).support.card = 3) :
    (l.length - f.support.card + f.cycleType.card) % 2 = 1 := by
  have hcard : l.toFinset.card = l.length := by
    rw [List.card_toFinset, List.dedup_eq_self.mpr hl]
  have hsubf : f.support ⊆ l.toFinset := by
    intro x hx
    rw [Equiv.Perm.mem_support] at hx
    rw [List.mem_toFinset]
    by_contra h
    exact hx (hf x h)
  have hsubh : (f * l.formPerm).support ⊆ l.toFinset := by
    intro x hx
    rw [Equiv.Perm.mem_support, Equiv.Perm.mul_apply] at hx
    rw [List.mem_toFinset]
    by_contra h
    exact hx (by rw [List.formPerm_apply_of_notMem h, hf x h])
  have hsf_le : f.support.card ≤ l.length := by
    have := Finset.card_le_card hsubf
    omega
  have h3le : 3 ≤ l.length := by
    have := Finset.card_le_card hsubh
    omega
  have hne : ∀ x, l ≠ [x] := by
    intro x hx
    rw [hx] at h3le
    simp at h3le
  have hform : Equiv.Perm.sign l.formPerm = -(-1) ^ l.length := by
    rw [(List.isCycle_formPerm hl (by omega)).sign, List.support_formPerm_of_nodup l hl hne,
      hcard]
  have hsh : Equiv.Perm.sign (f * l.formPerm) = 1 := (card_support_eq_three_iff.mp h3).sign
  rw [Equiv.Perm.sign_mul] at hsh
  have hsf : Equiv.Perm.sign f = Equiv.Perm.sign l.formPerm := by
    rw [eq_inv_of_mul_eq_one_left hsh, Int.units_inv_eq_self]
  have hpow : (-1 : ℤˣ) ^ (f.support.card + f.cycleType.card) = (-1) ^ (l.length + 1) := by
    rw [pow_succ (-1 : ℤˣ) l.length, mul_neg_one, ← hform, ← hsf,
      Equiv.Perm.sign_of_cycleType, Equiv.Perm.sum_cycleType]
  have := extremalJordanPickCountParity_mod_two_eq hpow
  omega

end ParityAbstract
