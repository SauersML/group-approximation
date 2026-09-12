---
rg: 2
id: regular-tree-torsion-orders-have-primes-at-most-degree
kind: claim
title: Every finite-order automorphism of the d-regular rooted tree has an order whose prime factors are at most d
distinct_from:
  self-similar-hosts-contain-only-residually-finite-groups: that shows every subgroup of Aut(T_d) is residually finite, which excludes inputs that are not residually finite; this bounds the primes dividing torsion orders by the degree d, which also excludes some residually finite inputs.
artifacts:
  - research/artifacts/regular-tree-torsion-obstruction-2026-09-12.md
---

**ESTABLISHED.** Let `d >= 2`, and let `g in Aut(T_d)` have finite order `m`.
Then every prime divisor of `m` is at most `d`.

**Consequences:**
- If a group `G` contains an element of prime order `p > d`, then `G` has no
  faithful action on `T_d`. It is therefore a subgroup of no self-similar group
  `H <= Aut(T_d)`.
- If `G` contains elements of prime order for infinitely many primes, then `G`
  embeds in `Aut(T_d)` for no `d`.

This is the torsion form of condition (N1) of
`every-fp-rf-group-embeds-in-fp-self-similar-group`. It needs no computation of
quotients: one element of large prime order is a certificate.

DERIVATION
regular-tree-torsion-primes-proof
