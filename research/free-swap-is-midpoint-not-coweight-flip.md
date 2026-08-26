---
rg: 2
id: free-swap-is-midpoint-not-coweight-flip
kind: claim
title: A free swap projection is a coweight midpoint, not a common sheet flip
invalidates:
  - outlier-exclusion-from-coweight-flip
distinct_from:
  coweight-triangle-charges-every-common-sheet-flip: that gives a sharp obstruction when all three denominator directions approximately carry one projection to its complement; this computes the actual amalgamated-free swap overlaps and shows that they are a fixed distance one over square root two from that hypothesis.
  swap-involution-enemy-is-never-abelian-carried: that uses a four-letter moment to prove maximal noncommutation of a swap and one twist; this uses the two-letter overlap moment simultaneously in the three coweight directions and evaluates the newly established triangle inequality on the enemy itself.
---

Use the arithmetic pair `C=SL_3(Z)<A=SL_3(Z[1/p])` and the three
coweight directions `d_12,d_23,d_31` of
`coweight-triangle-charges-every-common-sheet-flip`.  Let `B=L(C)`, let
`pi:L(A)->M` be trace preserving for the regular character, and suppose a
self-adjoint unitary `s in pi(B)'` is centered and
`W^*(pi(B),s)` is free from `pi(L(A))` with amalgamation over `pi(B)`.
Put

```text
P=(1+s)/2,              P_r=pi(d_r)Ppi(d_r)^*.
```

Then, for every `r in {12,23,31}`,

```text
tau(PP_r)=1/4,
||P_r-(1-P)||_2^2=1/2.                                 (CFM1)
```

Thus the common-complement errors in `(CTA6)` are all exactly
`1/sqrt(2)`.  The coweight-triangle bound

```text
epsilon_12+epsilon_23+epsilon_31>=1
```

is satisfied with strict slack `3/sqrt(2)-1`; it gives no contradiction
to the free involution enemy.  Canonical matrix microstates, if they exist,
inherit the same limits.

This sharply separates the new triangle obstruction from the open outlier
leaf.  The triangle kills a literal common Boolean sheet flip.  The
double-swap enemy instead asks for trace independence of `P` and its
translates, which lies at the midpoint of the two endpoint transports.
Extracting a common complement projection from freeness would therefore
change a fixed `L^2` distance, not round a vanishing defect.

DERIVATION
free-swap-coweight-midpoint-proof
