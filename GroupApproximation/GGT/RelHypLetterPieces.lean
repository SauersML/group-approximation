import GroupApproximation.Sofic.OsinWeightedMetric
import GroupApproximation.Algebra.FreeProductConjugacy

/-!
# Pieces vanish when distinct relators have distinct heads, and a tie relator is
never a proper power

Two of the six design certificates of
`OsinWeightedMetric.WeightedRouterDesign` — the metric small-cancellation
condition and the no-proper-power condition — discharged here, for the shape of
relator family Fournier-Facio's Proposition 2.3 supplies.

## The exponent blocks are unnecessary

The plan this module replaces was: relators `u_k · w_k⁻¹` with
`w_k = a b^{n_1} a b^{n_2} ⋯` over a free pair `a, b`, and a count showing that a
common prefix of two distinct members spans at most one separator, hence has at
most `2·maxblock + 1` letters, hence clears `C'(1/8)` once there are enough
blocks.  That count is real, and it is a few hundred lines of list induction over
`List.rotate` with the positive/inverse cross cases.

**None of it is needed**, because `LetterIsPiece` asks for a common *prefix*, and
a nonempty common prefix forces the two members to have the same head.  So if
distinct members of the symmetrized family have distinct heads, every piece is
empty and `LetterMetricSmallCancellation R lam` holds for every positive `lam`
with no count at all.  That is `letterMetricSmallCancellation_of_head_injective`
below, and it is fifteen lines.

The design obligation this trades for is "all letters of the whole symmetrized
family are pairwise distinct", which is arranged rather than proved, and the
peripheral factor is what makes it arrangeable: `len_source_le_one` says *every*
element of `G false` is a letter, so an infinite peripheral factor supplies
infinitely many distinct letters, and the partner side can supply as many more as
needed by putting `c_i = a b^i a` into the generating set for `i` in a range —
these are pairwise distinct as soon as `⟨a, b⟩` is free, which is exactly the
`PingPong.FreeRankTwo` input.  A relator is then

    [of u_k, of c_{i₁}, of c_{i₂}, …, of c_{i_L}]

with every index used once in the whole family.  Its product is
`u_k · (c_{i₁} ⋯ c_{i_L})`, a peripheral letter times a partner element, so the
tie is met; adjacent letters are peripheral·partner or partner·partner, neither
of which is a letter, so it is reduced.

Note which way the trade runs.  It costs a *larger generating set* for the
partner factor — Osin's alphabet is allowed to be any finite generating set, and
nothing downstream cares how big it is — and it buys the deletion of the entire
combinatorial argument.  The block design was spending relator *length* to make
pieces short; this one spends alphabet *size* to make them empty.

## What is proved

* `head?_eq_of_prefix` — a nonempty prefix has the head of its host.
* `letterMetricSmallCancellation_of_head_injective` — **the metric certificate**,
  from distinct heads alone, at every positive constant.
* `not_properPower_of_neWord` — a cyclically reduced word of exactly two
  syllables is not a proper power.  The three cases of
  `FreeProductCyclic.exists_cyclicReduction`: the identity is excluded because a
  cyclically reduced word has infinite order, a conjugate of a syllable by
  `not_conj_of_le_one`, and a conjugate of a cyclically reduced `v` because
  syllable length is a conjugacy invariant, so `2 = (m+1)·|v|` with both factors
  at least two.
* `letterNoProperPower_of_tie` — **the no-proper-power certificate**, free for a
  family of tie relators.  `u · y⁻¹` with `u` peripheral and `y` a nonidentity
  partner element is exactly a two-syllable cyclically reduced word, so the
  previous theorem applies and no design parameter is spent.

`GreendlingerRelativeTransfer.noProperPower_of_prime_wlen` proves the same thing
one metric down, for `Set (Word G)` and a prime syllable count; the argument here
is its specialisation to the count `2`, rewritten for `Set (List (CoprodI G))`
because the two lanes carry relators in different types and neither predicate
mentions the other.

## Names without precedent in this repository

`inv_ne_one` and `NeWord.append_prod` are used here on the strength of Mathlib
and of `Algebra/CoprodITorsionFree.lean` respectively; every other name is
exercised elsewhere in this tree.  `DecidableEq` for the index and the factors is
supplied by `classical` inside the proof and kept out of every statement, as
`OsinWeightedMetric.isPowerTorsionFree_coprodI` does for the same reason.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open Monoid Monoid.CoprodI
open OsinWeightedMetric

/-! ## 1.  A nonempty prefix carries the head -/

/-- A nonempty prefix has the same head as the list it is a prefix of. -/
theorem head?_eq_of_prefix {α : Type*} {p l : List α} (h : p <+: l) (hp : p ≠ []) :
    l.head? = p.head? := by
  obtain ⟨t, rfl⟩ := h
  cases p with
  | nil => exact absurd rfl hp
  | cons c p' => rfl

/-! ## 2.  The metric certificate, from distinct heads -/

/-- **Pieces vanish when distinct relators have distinct heads.**

`LetterIsPiece` asks for a common *prefix* of two distinct members, and a
nonempty common prefix forces equal heads.  So a family in which the head
determines the member has only the empty piece, and the metric condition is the
statement that `0 < lam · |r|`, which holds at every positive `lam` and every
nonempty relator.

No count, no rotation arithmetic, and no hypothesis on the relator lengths beyond
their being nonempty. -/
theorem letterMetricSmallCancellation_of_head_injective
    {G : Bool → Type} [∀ b, Group (G b)] {R : Set (List (CoprodI G))} {lam : ℚ}
    (hlam : 0 < lam) (hpos : ∀ r ∈ R, 0 < r.length)
    (hhead : ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁.head? = r₂.head? → r₁ = r₂) :
    LetterMetricSmallCancellation R lam := by
  intro p hp r hr _
  obtain ⟨r₁, hr₁, r₂, hr₂, hne, hp₁, hp₂⟩ := hp
  have hpnil : p = [] := by
    by_contra hpne
    exact hne (hhead r₁ hr₁ r₂ hr₂
      ((head?_eq_of_prefix hp₁ hpne).trans (head?_eq_of_prefix hp₂ hpne).symm))
  have hrpos : (0 : ℚ) < (r.length : ℚ) := by exact_mod_cast hpos r hr
  rw [hpnil, List.length_nil, Nat.cast_zero]
  exact mul_pos hlam hrpos

/-! ## 3.  A two-syllable relator is not a proper power -/

/-- **A cyclically reduced word of exactly two syllables is not a proper
power.**

Cyclic reduction sorts the putative root into three kinds and each is excluded:
the identity, because a cyclically reduced word has infinite order; a conjugate
of a single syllable, by `FreeProductCyclic.not_conj_of_le_one`; and a conjugate
of a cyclically reduced `v`, because syllable length of a cyclically reduced form
is a conjugacy invariant, so `2 = (m+1)·|v|` with `m + 1 ≥ 2` and `|v| ≥ 2`.

This is `GreendlingerRelativeTransfer.noProperPower_of_prime_wlen` at the count
`2`, stated for a `NeWord` rather than for a member of a `Set (Word G)` so that
the letter lane can use it. -/
theorem not_properPower_of_neWord {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]
    {i j : ι} (hij : i ≠ j) (u : NeWord G i j) (hlen : u.toList.length = 2)
    (s : CoprodI G) (k : ℕ) (hk : 2 ≤ k) : u.prod ≠ s ^ k := by
  classical
  intro heq
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hm1 : 1 ≤ m := by omega
  rcases FreeProductCyclic.exists_cyclicReduction s with
    h1 | ⟨p, x, c, hs⟩ | ⟨p, q, v, c, hpq, hs⟩
  · exact FreeProductCyclic.pow_ne_one_of_ne hij u 0
      (by rw [zero_add, pow_one, heq, h1, one_pow])
  · exact FreeProductCyclic.not_conj_of_le_one hij u (x ^ (m + 1)) c
      (by rw [heq, hs, FreeProductCyclic.conj_pow_eq, map_pow])
  · have hpow : u.prod = c * (FreeProductCyclic.npow hpq v m).prod * c⁻¹ := by
      rw [FreeProductCyclic.npow_prod, heq, hs, FreeProductCyclic.conj_pow_eq]
    have hlen' := FreeProductCyclic.length_eq_of_conj hpq hij
      (FreeProductCyclic.npow hpq v m) u c hpow
    rw [FreeProductCyclic.npow_toList_length, hlen] at hlen'
    have h2 : 2 ≤ v.toList.length := FreeProductCyclic.two_le_length_of_ne hpq v
    have hmul : 2 * 2 ≤ (m + 1) * v.toList.length :=
      Nat.mul_le_mul (by omega) h2
    omega

/-- **The no-proper-power certificate is free for tie relators.**

A relator whose product is `u · y⁻¹`, one nonidentity peripheral element times
the inverse of one nonidentity partner element, spells a two-syllable cyclically
reduced word, so the previous theorem applies.  No design parameter is spent:
this clause costs the relator family nothing at all. -/
theorem letterNoProperPower_of_tie {G : Bool → Type} [∀ b, Group (G b)]
    {R : Set (List (CoprodI G))}
    (htie : ∀ r ∈ R, ∃ (x : G false) (y : G true), x ≠ 1 ∧ y ≠ 1 ∧
      r.prod = CoprodI.of x * (CoprodI.of y)⁻¹) :
    LetterNoProperPower R := by
  intro r hr s k hk
  obtain ⟨x, y, hx, hy, hprod⟩ := htie r hr
  have hfalse : (false : Bool) ≠ true := by decide
  have hyinv : y⁻¹ ≠ 1 := inv_ne_one.mpr hy
  have hu : ((NeWord.singleton x hx).append hfalse
      (NeWord.singleton y⁻¹ hyinv)).prod = CoprodI.of x * (CoprodI.of y)⁻¹ := by
    rw [NeWord.append_prod, NeWord.prod_singleton, NeWord.prod_singleton,
      map_inv]
  rw [hprod, ← hu]
  exact not_properPower_of_neWord hfalse _ rfl s k hk

end RelHyp
end GGT
end GroupApproximation
