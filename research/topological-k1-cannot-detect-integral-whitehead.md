---
rg: 2
id: topological-k1-cannot-detect-integral-whitehead
kind: claim
title: Corona topological K-one is a zero detector for integral Whitehead classes
distinct_from:
  matrix-corona-k1-vanishes: that is the computation that the corona's topological K_1 is zero, a fact about the C-star algebra; this is the methodological consequence for algebraic K_1 of ZG, namely that a zero target can neither detect nor exclude an integral class. The computation is the input; this is the no-go it forces.
  matrix-corona-k0-index-survives: that says a relative index in K_0 does survive the corona quotient; this says the K_1 side cannot see algebraic classes at all. They point in opposite directions and are both true.
artifacts:
  - research/artifacts/whitehead-vanishing-audit-2026-08-17.md
---

Vanishing of `K_1^top` of a matrix corona `Q` implies **nothing** about
`K_1^alg(ZG)` or `Wh(G)` for a group represented in `Q`.

A representation `G -> U(Q)` induces `ZG -> Q` and hence

    K_1^alg(ZG) -> K_1^alg(Q) -> K_1^top(Q) = 0.

The composite annihilates every class, zero or not, so it can establish
neither injectivity nor vanishing at the source.  A zero-valued invariant is
not a detector.

## The categorical boundary, and why it is not a technicality

Whitehead groups are algebraic `K_1` of the *discrete integral* group ring;
corona winding and Bott arguments are topological `K`-theory of a
`C*`-algebra.  There is no general comparison isomorphism here, in either
direction.  The warning example is `G = Z^2`: `C*(Z^2) = C(T^2)` carries a
nontrivial reduced topological `K_0` class, the Bott class, while
Bass--Heller--Swan over the regular ring `Z` gives
`K~_0^alg(Z[Z^2]) = 0` and `Wh(Z^2) = 0`.  Analytic classes need not come
from algebraic ones, and analytic vanishing need not reflect algebraic
vanishing.

## Scope

This kills the operator-algebraic lane as a source of Whitehead information
in **both** directions -- it cannot prove `whitehead-vanishing-torsion-free`
and it cannot refute it -- and it is a statement about the shape of the
argument, not about any particular group.  It is separate from, and does not
weaken, the non-MF program's use of the same corona: there the object of
study *is* the operator algebra, and `matrix-corona-k1-vanishes` /
`matrix-corona-k0-index-survives` remain the correct delimitation of which
index arguments live there.
