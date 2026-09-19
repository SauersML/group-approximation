---
rg: 2
id: atlas-a8-carrier-reaches-third-large-core-edge
kind: claim
title: An exact A8 carrier reaches three of four large-component core edges
artifacts:
  - experiments/atlas_a4_three_large_core_a8_certificate.g
  - experiments/atlas_a4_low_index_next_core_screen.g
  - research/artifacts/atlas-a4-three-large-core-a8-certificate.json
distinct_from:
  atlas-s288-carrier-extends-through-first-core-cycle: that structurally constructs a 576-point carrier through two edges; this gives an independent eight-point carrier through a third distinct edge.
  atlas-a10-first-core-cycle-collapses: that proves one marked A10 carrier cannot pass the second edge; this changes carrier type and exhibits an exact positive completion.
  atlas-a4-rank-three-core-commutant-collapse: that false claim concerned all fourteen core occurrences and arbitrary complex matrices; this finite carrier covers only one K2,2 component and explicitly fails its fourth edge.
---

There are six explicit even permutations of eight points, labeled
`r,z,c,t,s,u`, which generate `A8` and satisfy exactly:

```text
the minimal forward-collision presentation,
<r,z,s t> ~= C2^4 : C3^2                 (order 144),
<r,z,c> ~= C3 x S3                       (order 18),
<t,s> ~= S3                              (order 6),
<r,z,c,u> ~= S3 x S3                     (order 36),
```

together with the first three distinct pair-cubes of the large rank-three
`K2,2` component.  Put `b=s t` and `y=t^-1`.  The exact mask is

```text
(r^-1 b)^3=1,
(u y)^3=1,
((u r)y^-1)^3=1,
(r b y)^3 != 1.                            (A4-A8-3EDGE)
```

Each of the first three order-two/order-three pairs generates an injected
`A4` of order twelve.  The generated ambient image has order `20160`, and all
six generators are even, hence it is exactly `A8`.

The regular representation is already at atlas multiplicity one: its
restrictions are `1120 Reg(F)`, `140 Reg(C)`, `3360 Reg(K)`, and
`560 Reg(S3 x S3)`.  Thus collision, the forward fan, and three quarters of
the large `K2,2` have an exact finite regular-margin carrier with no
amplification.

The bounded low-index classification explains where it sits.  Among all 375
subgroups of index at most twelve of the minimal presentation, 232 finite
coset images preserve the three vertex orders `144,18,6`; 56 admit `u` and
the second edge.  Their full large-component masks are

```text
0x3: 53,       0x7: 2,       0xb: 1,
```

and none is `0xf`.  This last fact is only a degree-at-most-twelve finite
screen.  In the displayed `A8` carrier the missing word `r b y=r s` has order
seven.  Imposing its cube kills that element, and its normal closure is all of
the simple group `A8`; hence this particular carrier cannot be quotiented
through the fourth edge at all.  The universal four-edge completion remains
unclassified.
