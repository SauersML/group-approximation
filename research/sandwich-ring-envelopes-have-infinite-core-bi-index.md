---
rg: 2
id: sandwich-ring-envelopes-have-infinite-core-bi-index
kind: claim
title: Every group mapping onto an elementary group over a ring with an infinite ideal chain has infinite core bi-index, so every universal-sandwich marking fails
distinct_from:
  ck-quotient-corner-has-infinite-bi-index: that fixes the canonical corner core and separates its double cosets with root subgroups; this holds for EVERY subgroup S meeting proper normal subgroups trivially, whatever its position, and uses no root combinatorics.
  direct-ck-corner-core-has-infinite-bi-index: that treats the direct corner embedding only; this is independent of the embedding and of which core is chosen.
  ck-cover-quotient-kernel-dichotomy: that constrains quotients of the marked cover which do not descend to matrix quotients; this kills every group that still surjects onto EL_4(U), including the marked cover itself for any marking and any core.
  ck-envelope-simple-core-has-finite-bi-index: that is the open hole; this removes the whole universal-sandwich class of envelopes from it without refuting the existential claim.
  finite-bi-index-kazhdan-stabilizer-is-nonseparable: that obstructs finite-index overgroups of a Kazhdan stabilizer; this obstructs ambient groups with infinite normal height, via congruence kernels.
  normally-generating-core-bi-index-bounds-normal-height: that is the abstract normal-height bound; this supplies the infinite chains (congruence kernels over prime multiples) that violate it for sandwich-ring envelopes.
---

**(B) Ring obstruction.** Let `R` be a unital ring with an infinite strictly
monotone chain of two-sided ideals, `n >= 2`, and let `Gamma` be a group with
a surjection `pi : Gamma ->> EL_n(R)`. Then

    |S \ Gamma / S| = infinity

for every subgroup `S <= Gamma` such that `N ∩ S = 1` for all proper normal
`N` of `Gamma`.

**(U) Universal sandwich rings qualify.** Let `T` be any group, `1 != g in T`,
and `U = Z[T]<p,q>/(p(1-g)q - 1)`. Then `U/lU != 0` for every prime `l`. So
with `m_k = l_1 l_2 ... l_k` the product of the first `k` primes,

    U  ⊋  m_1 U  ⊋  m_2 U  ⊋  ...

is an infinite strictly descending chain of two-sided ideals.

**Consequence.** Take any marking `H <= [T,T]`, `1 != g in H` and any
envelope `Gamma` from `ck-steinberg-marked-cover`, which maps onto
`EL_4(U)`. Then **no** subgroup `S` of `Gamma` meeting every proper normal
subgroup trivially has finite bi-index. This covers the simple core, any
simple or non-simple enlargement of it with that property, any core embedded
through a different corner, and `EL_4(U)` itself if it serves as ambient
group. It also covers every group between the Steinberg group and `EL_4(U)`,
and every other group that surjects onto `EL_4(U)` or onto `EL_n(U)` with
`n >= 2`.

So the universal-sandwich route to
`ck-envelope-simple-core-has-finite-bi-index` is dead as a class. The obstruction
invariant is normal height, and the step where every member dies is the
congruence kernels `C(m_k U)`. A surviving envelope must have normal height at
most its bi-index, finite center if nonabelian, and no surjection onto
`EL_n(R)` for any ring `R` of infinite two-sided ideal length. For example the
coefficients might be a simple ring such as a Leavitt algebra, or the envelope
might be simple itself.

## What is not covered

- Quotients `Gamma/N` of the marked cover in which the covering kernel
  `K = ker(Gamma -> EL_4(U))` satisfies `KN = Gamma`. These no longer map onto
  a matrix group over a quotient of `U`, which is the case isolated by
  `ck-cover-quotient-kernel-dichotomy`.
- The original Chatterji--Kassabov subring `L ⊆ End(W)`, a quotient of `U`.
  Whether `L` has an infinite chain of two-sided ideals is not checked here.
- Quotients `Gamma/N` that surject onto `EL_4(U/J)` are covered exactly when
  `U/J` has an infinite ideal chain, for example when `U/J` is nonzero mod
  infinitely many primes.
