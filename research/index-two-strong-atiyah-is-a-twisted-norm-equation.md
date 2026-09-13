---
rg: 2
id: index-two-strong-atiyah-is-a-twisted-norm-equation
kind: claim
title: Strong Atiyah passes from an index-2 subgroup exactly when a twisted norm equation has no solution in its Linnell division ring
distinct_from:
  atiyah-passes-to-torsion-free-elementary-amenable-extensions: that is Schick's permanence for torsion-free elementary amenable quotients; finite quotients are not torsion-free, and this is the exact criterion for a quotient of order 2.
  strong-atiyah-passes-to-locally-indicable-extensions: that covers locally indicable quotients; this is the index-2 case, where no locally indicable quotient exists.
---

**ESTABLISHED** by [[index-two-twisted-norm-crossed-product-proof]]. Not
independently reviewed. This is standard crossed-product algebra and no novelty
is claimed.

Let `K <= C` be a subfield, `G` a torsion-free group, and `N <= G` a subgroup of
index 2 satisfying the Strong Atiyah conjecture over `K`. Fix `h` in `G` minus `N`, and let
`sigma(x) = h x h^-1` on the division closure `D_K(N)` of `K[N]` in `U(N)`. Then:

1. `D_K(G) = D_K(N) + D_K(N) h`, a direct sum of left `D_K(N)`-modules;
2. `G` satisfies Strong Atiyah over `K` if and only if there is no `a` in `D_K(N)` with

       sigma(a) a = h^2.

**Model test.** A group element `a = g` in `N` solves the equation iff
`h g h^-1 g = h^2`, iff `(g h^-1)^2 = 1`. That is excluded by torsion-freeness, as it
must be.
