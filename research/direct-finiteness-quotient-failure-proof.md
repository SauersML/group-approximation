---
rg: 2
id: direct-finiteness-quotient-failure-proof
kind: route
title: A free algebra is a domain; kill one relation and get the unilateral shift
target: direct-finiteness-not-inherited-by-quotients
requires: []
artifacts:
  - research/artifacts/kaplansky-direct-finiteness-audit-2026-08-17.md
---

## Direct proof

**The free algebra is directly finite.**  `k<X,Y>` is a domain: order words
by length then lexicographically, and the leading word of a product of two
nonzero polynomials is the concatenation of their leading words, which cannot
cancel against anything shorter.  Every domain is directly finite — from
`ab = 1`,

    (ba - 1) b = b(ab) - b = 0,

and `b != 0` (else `ab = 0 != 1`), so `ba = 1`.

**The quotient is not.**  Let `V` have basis `v_0, v_1, v_2, ...` and define

    Y v_n = v_(n+1),     X v_0 = 0,     X v_(n+1) = v_n.

This is a representation of `k<X,Y>` in which `XY` acts as the identity, so it
factors through `B = k<X,Y>/(XY-1)`; and `YX v_0 = 0 != v_0`, so `YX != 1`
already in `B`.  Hence `B` is a unital quotient of a directly finite ring and
is not directly finite.

**The permitted direction.**  If `S` is directly finite and `I` is an ideal
with `I subseteq J(S)`, then `S/I` is directly finite.  Suppose `ab = 1` in
`S/I`.  Then `ab` lies in `1 + I subseteq 1 + J(S)`, so `ab` is a unit of `S`.
Put `c = b(ab)^-1`; then `ac = 1`, so `ca = 1` by direct finiteness of `S`.
Finally `(ab)^-1 - 1 = (ab)^-1(1 - ab)` lies in `I`, so `c = b` mod `I` and
`ba = 1` in `S/I`.

The contrast is the content: the radical hypothesis is exactly what the free
algebra example lacks, since `J(k<X,Y>) = 0` while `(XY-1)` is large.
