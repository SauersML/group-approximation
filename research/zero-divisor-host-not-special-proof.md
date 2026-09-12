---
rg: 2
id: zero-divisor-host-not-special-proof
kind: route
title: A domain has domain subrings, and property (T) with the Haagerup property forces finiteness
target: zero-divisor-host-is-not-virtually-compact-special
requires:
  - fisher-sanchez-peralta-special-and-3-manifold-domains
---

(1) and (2). Suppose `H <= G'`, where `G'` is torsion-free and is either
virtually compact special or a compact 3-manifold group. The coefficients of
`alpha` and `beta` lie in `k`, and `alpha beta = 0` already holds in
`k[H] <= k[G']`. By `fisher-sanchez-peralta-special-and-3-manifold-domains`,
`k[G']` embeds in a division ring. A division ring has no zero divisors, so
`alpha = 0` or `beta = 0`, which is a contradiction.

**Infinite Kazhdan groups are not virtually compact special.** Suppose `G'` has
property (T) and a finite-index subgroup `G_0` is the fundamental group of a
compact special cube complex.
- By Haglund--Wise, *Special cube complexes*, GAFA 17 (2008), `G_0` embeds in
  a right-angled Artin group.
- A right-angled Artin group acts properly on a CAT(0) cube complex (the
  universal cover of its Salvetti complex), so it has the Haagerup property,
  and so does its subgroup `G_0`.
- The Haagerup property passes to finite-index overgroups, so `G'` has it.
- A group with both property (T) and the Haagerup property is finite.
So an infinite Kazhdan group is not virtually compact special.

`E_3(3) = <e_ij(3) : i != j>` is a finite-index subgroup of `SL_3(Z)`, so it is
infinite with property (T). It is torsion-free, as recorded in
`e33-balls-have-no-small-zero-divisors`. Parts (1) and (2) therefore do not
exclude it.

Agol's theorem that cubulated hyperbolic groups are virtually compact special
is used only in the list of consequences on the claim node, not in (1) or (2).

QED
