---
rg: 2
id: almost-commuting-permutations-are-near-commuting
kind: claim
title: Almost commuting permutations are near commuting permutations (Arzhantseva--Paunescu)
distinct_from:
  sofic-stable-implies-residually-finite: that is the general principle that a sofic stable group is residually finite; this is the stability of one specific relator system, the commutator, for every tuple size.
---

**ESTABLISHED by citation.** For every `k >= 2`, the system of commutator words
`{[x_i, x_j] : i < j <= k}` is stable in permutations with the normalized Hamming distance. For every
`epsilon > 0` there is `delta > 0` such that, for all `n`, any `p_1, ..., p_k in Sym(n)` with
`d(p_i p_j, p_j p_i) < delta` lie within `epsilon` of pairwise commuting permutations. Equivalently,
`Z^k` is stable in permutations.

Consumer: `thompson-f-sofic-iff-relator-system-unstable`, which uses `k = 2` to correct the
abelianization part of almost-actions of Thompson's `F`.
