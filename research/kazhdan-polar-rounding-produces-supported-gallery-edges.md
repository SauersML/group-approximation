---
rg: 2
id: kazhdan-polar-rounding-produces-supported-gallery-edges
kind: claim
title: Kazhdan averaging and polar rounding produce supported gallery intertwiners with trace-controlled leakage
distinct_from:
  lambda-exact-face-of-the-collapse-closes: that combines the Kazhdan distance with a representation-specific upper bound on the exact intertwiner space; this extracts the physical partial isometry and its source/target leakage without assuming regular isotypic weights.
  mixed-intertwiner-energy-transport-localization: that decomposes the energy of one unitary into a fractional transportation plan among reducing blocks; this rounds the whole almost intertwiner to one exact partial intertwiner and records its physical support loss.
  six-edge-holonomy-energy-ledger-is-scale-free: that charges a closed product after supported edges are given; this constructs each supported edge from exact conductor-band representations.
---

Let `(G,S,kappa)` be a group with the following Kazhdan-pair convention:
for every unitary representation `rho` and every vector `xi`,

```text
dist(xi,Fix(rho))
 <= kappa^(-1) max_(s in S)||rho(s)xi-xi||.             (KPR1)
```

Let

```text
pi_-,pi_+:G->U(d)                                      (KPR2)
```

be exact representations and let `A in U(d)` satisfy

```text
eta=max_(s in S)||pi_+(s)A-A pi_-(s)||_2.               (KPR3)
```

Then there is an exact intertwining partial isometry `B` such that, writing

```text
r_-=B^*B,                 r_+=BB^*,                     (KPR4)
```

one has

```text
pi_+(g)B=B pi_-(g)                         (g in G),     (KPR5)
[r_-,pi_-(g)]=[r_+,pi_+(g)]=0,                          (KPR6)
tr(1-r_-),tr(1-r_+) <= (eta/kappa)^2,                   (KPR7)
||A-B||_2 <= 2 eta/kappa.                               (KPR8)
```

The constants do not depend on `d`, on the irreducible degrees, or on the
isotypic multiplicities.

## Carrier transport

Let `P_- in pi_-(G)'` and `P_+ in pi_+(G)'` be projections.  If the raw
transition transports them with defect

```text
zeta=||A P_- A^*-P_+||_2,                               (KPR9)
```

then the rounded edge obeys

```text
||B P_- - P_+ B||_2 <= zeta+4 eta/kappa.                (KPR10)
```

The same estimate applies simultaneously to the four joint atoms of two
commuting lamp projections.  Compressing `B` between any chosen source and
target atoms therefore produces a supported contraction whose transition
error is bounded by `(KPR10)` plus the support losses `(KPR7)`.

For a six-edge gallery, apply the theorem to every edge.  The total missing
physical carrier trace is at most

```text
2 sum_(i=1)^6 (eta_i/kappa)^2,                           (KPR11)
```

before any additional intersections, and the sum of the edge rounding
errors is at most

```text
2 kappa^(-1) sum_i eta_i.                               (KPR12)
```

Thus, **after genuine conductor-band representations have been decoded**,
property `(T)` supplies exactly the supported-transition input of
`six-edge-holonomy-energy-ledger-is-scale-free` with a dimension-independent
constant.

This theorem does not exactify an approximate representation of `G`.
Applying `(KPR1)` requires the left-right action

```text
T |-> pi_+(g) T pi_-(g)^*
```

to be an actual unitary representation.  For the `G_cc` problem this leaves
the load-bearing step unchanged: extract genuine compatible conductor-band
representations of `SL_3(Z)` from the raw normalized-HS microstate, and make
the same positive four-atom mass occur in the six bands.  Property `(T)`
then rounds the edges; it does not manufacture those bands.
