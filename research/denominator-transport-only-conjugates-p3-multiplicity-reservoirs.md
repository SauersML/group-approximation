---
rg: 2
id: denominator-transport-only-conjugates-p3-multiplicity-reservoirs
kind: claim
title: Denominator transport only conjugates adjacent p-three multiplicity reservoirs
distinct_from:
  regular-p3-parahoric-bands-have-twisted-gauge-surplus: that computes the inverse gauge available inside each regular depth band; this proves an adjacent denominator transition transports its multiplicity algebra with an arbitrary spatial gauge rather than identifying its elements.
  common-corner-mutual-bicommutant-extraction: that asks to recover two transverse algebras as mutual commutants on one positive carrier; this shows why a single packet normalizer supplies only conjugate commutants and cannot perform that recovery.
  folner-multiplicity-atlases-have-vanishing-first-exit: that builds coherent rectangular Schur matches for arbitrary finite depth stencils; this adds the full-matrix normalizer calculation and shows that inverse projective gauges can be transported through the same Folner architecture.
---

Suppose an adjacent-depth denominator word has been decoded on a supported
carrier and exactly intertwines two isomorphic irreducible packet factors.
After fixed identifications write the endpoint spaces as

```text
K tensor M_a,              K tensor M_(a+1),            (DTR1)
```

with packet algebra `B(K) tensor I`.  If the supported transition `U_a`
implements the prescribed packet isomorphism `Ad(W_a)`, then

```text
U_a = W_a tensor V_a                                      (DTR2)
```

for an arbitrary unitary `V_a:M_a->M_(a+1)`.  Indeed
`(W_a^* tensor I)U_a` commutes with `B(K) tensor I`, whose commutant is
`I tensor B(M_a)`.  Consequently

```text
U_a (I tensor B(M_a)) U_a^*
 = I tensor B(M_(a+1)),                                  (DTR3)
```

but the induced identification is `Ad(V_a)`, not the identity map on a
previously named reservoir.

On a depth interval the transition graph is a tree.  Changing the
multiplicity coordinates recursively gauges every `V_a` to the identity.
Thus adjacent denominator transport creates no holonomy and does not make
the inverse cocycle requirements at different depths act simultaneously on
one fixed multiplicity representation.  Weyl conjugates enlarge the depth
graph to a finite-stencil piece of the `A_2` coweight lattice; every fixed
native loop there is still canceled by
`finite-native-p3-atlas-has-a-global-inverse-groupoid-gauge`.

There is a quantitative Følner recycling escape.  On an `N`-wide depth box,
amplify the regular packet blocks to a common multiple of their finite gauge
dimensions, use `(DTR2)` and the inverse groupoid gauge on every interior
edge, and complete the boundary partial shifts arbitrarily to unitaries.  A
fixed word of propagation radius `R` is exact off the `R`-boundary, so

```text
||word-1||_2^2 <= 4 |partial_R box|/|box| = O_R(1/N).   (DTR4)
```

Triangular conductor weights give the same conclusion with the
first-exit estimate already recorded in
`folner-multiplicity-atlases-have-vanishing-first-exit`.  On every interior
block, the p-three oscillator flux is canceled by the regular inverse gauge
from `regular-p3-parahoric-bands-have-twisted-gauge-surplus`.  Positive odd
depth mass therefore survives with zero bulk flux defect.

This does not construct a microstate for every raw relation of
`SL_3(Z[1/3])`: a mixed-root word may fail to respect the decoded block
transport.  It proves the precise no-go requested here.  A fixed
denominator/Weyl normalizer, adjacent-depth isotypic matching, regular
induction, and all native finite projective loops do **not** authenticate one
stationary multiplicity algebra.  The surviving arithmetic input must couple
the raw mixed-root coordinates to that algebra in a way that cannot be
gauged along the amenable depth graph.

The first raw mixed-root candidate does not provide that coupling.
`p3-denominator-steinberg-word-is-multiplicity-blind` evaluates
`[h x_12(1)h^(-1),x_23(1)]=x_13(3)` on the oscillator block: the
multiplicity unitary cancels inside the conjugated root, so the relation is
the packet Chevalley identity tensored with the identity.  A successful raw
coordinate must name a same-object multiplicity selector or a global
building PVM, not merely another root identity.
