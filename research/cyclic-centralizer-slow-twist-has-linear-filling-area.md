---
rg: 2
id: cyclic-centralizer-slow-twist-has-linear-filling-area
kind: claim
title: A slow order-three holonomy forces linear cyclic-centralizer filling area
artifacts:
  - research/artifacts/thompson-centralizer-slow-twist-area-firewall-2026-08-21.md
distinct_from:
  literal-one-cell-carmichael-cliques-are-uniformly-finite: that bounds one-cell Carmichael templates by free-group axis geometry; this gives an explicit linear lower bound for arbitrarily many interacting commutation cells in a cyclic centralizer presentation.
  houghton-carmichael-sections-have-unbounded-edge-area: that deduces presentation-independent divergence from hyperlinearity of an amenable Houghton group; this is a direct quantitative matrix certificate requiring no approximation property of the presented group.
  thompson-v-r5-uniform-common-pivot-centralizers: that asks whether the full Bleak--Quick R1--R5 presentation admits ambient R2/R3 shortcuts; this theorem applies only to the isolated cyclic centralizer presentation and identifies exactly what such a shortcut must defeat.
---

Let

```text
P=<b,c | b^3=1, [b,c]=1>
```

and, for `j>=1`, put

```text
q_j=[b,c^(-j)b c^j].
```

There is an absolute constant `kappa>0` such that

```text
Area_P(q_j) >= kappa j.                                  (CST1)
```

More precisely, with normalized Hilbert--Schmidt norm and with area counting
both defining relators,

```text
Area_P(q_j)
 >= (3/2)/(sqrt(3) sin(pi/(4j))).                         (CST2)
```

The proof uses `8j` two-dimensional blocks.  The image of `b` has order
three exactly, the defining commutator has defect

```text
sqrt(3) sin(pi/(4j)),
```

but `q_j` has defect exactly `3/2`.  Telescoping any van Kampen product gives
`(CST2)`.

Consequently one shallow almost-centralizer relation cannot be transported
through arbitrarily long powers with a bounded relator-cell budget.  A
uniform Thompson common-pivot proof cannot consist only of cyclically
iterating an R4/R5 commutation seed.  It must use a genuinely ambient
Bleak--Quick shortcut, necessarily involving the transport/split structure
R2/R3 or a nonlocal cancellation among several contextual charts.
