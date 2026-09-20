---
rg: 2
id: fpbs-free-burnside-groups-lie-in-kesten-half-proof
kind: route
title: Retraction and divisor quotients, with finite normal subgroups ruled out by finite centralizers
target: fpbs-free-burnside-groups-lie-in-kesten-half
requires:
  - fpbs-burnside-normal-closure-split
  - fpbs-burnside-embedding-input
  - fpbs-burnside-nonamenable-two-generator-input
  - fpbs-monster-groups-have-only-finite-amenable-subgroups
  - fpbs-relative-gap-along-any-subgroup-separates
---

**Lemma 1.** Let `F ⊴ Gamma` be finite and nontrivial, and pick `f in F \ {e}`.
`Gamma` acts on `F` by conjugation, with kernel `C_Gamma(F)`. The permutation
group of `F` is finite, so `C_Gamma(F)` has finite index in `Gamma`, and so it is
infinite because `Gamma` is. But `C_Gamma(F) <= C_Gamma(f)`, which is finite.
This is a contradiction. The "iff" follows: (α) gives such a `K = N`, and
conversely a nontrivial `K` with nonamenable `Gamma/K` is infinite, so `K` is a
witness for (α). ∎

**Nonamenability of `B(k,n)` for `k >= 2`, odd `n >= 1003`.** Sending the
first two free generators to the free generators of `B(2,n)`, and the rest to
`e`, is a surjection `B(k,n) -> B(2,n)`, by relative freeness. `B(2,n)` is
nonamenable (`fpbs-burnside-nonamenable-two-generator-input`), and quotients of
amenable groups are amenable. This is also item 2 of
`fpbs-monster-groups-have-only-finite-amenable-subgroups`.

**(a)** By `fpbs-burnside-normal-closure-split`, for `m >= 3` and odd `n >= 665`,
`N = <<x_1>>` is infinite and `B(m,n)/N ≅ B(m-1,n)`. Here `m-1 >= 2` and
`n >= 1003`, so the quotient is nonamenable by the previous paragraph. ∎

**(b)** Let `d | n` with `1003 <= d < n`.

- `B(m,d)` has exponent `d`, which divides `n`. So relative freeness gives a
  surjection `pi : B(m,n) -> B(m,d)` sending `x_i -> x_i`. Write `K = ker pi`.
- `K` is nontrivial. The map `B(m,n) -> Z/n` sending `x_1 -> 1` and the other
  generators to `0` shows that `x_1` has order exactly `n`. So `x_1^d != e`,
  while `pi(x_1^d) = e`.
- `B(m,n)` is infinite and, by `fpbs-burnside-embedding-input`, every
  nontrivial element has cyclic centralizer of order `n`, in particular finite.
  Lemma 1 gives `K` infinite.
- `B(m,d)` is nonamenable, by the previous paragraph with `n` replaced by `d`
  (`d` is odd since `n` is). ∎

**Divisor count.** If `n` is odd and composite, write `n = ab` with
`1 < a <= b`. Then `b >= n^(1/2)` is a proper divisor, and `b >= 1003` once
`n >= 1003^2`.

**Corollary 3.** Apply `fpbs-bs-via-percolation-kesten-split`, case (α), to the
witness `N` (resp. `K`). `fpbs-percolation-kesten-normal-gap` gives
`p_c(G) < p_c(N;G)`, and `fpbs-relative-gap-along-any-subgroup-separates`
(statement 1 implies `p_c < p_u`) finishes. This is conditional on the first
node, as stated.

**Corollary 4.** The monster facts are elementary. They are recorded in the
claim.

**What was checked.** Every step above uses only relative freeness, the
abelianization map to `Z/n`, the conjugation-action index bound, and the four
required nodes. There was no computation.
