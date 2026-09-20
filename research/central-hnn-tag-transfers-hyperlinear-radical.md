---
rg: 2
id: central-hnn-tag-transfers-hyperlinear-radical
kind: claim
title: A central HNN tag converts any killed nontrivial word into a central killed involution with a controlled modulus
distinct_from:
  marked-approximate-radical-survives-solution-group-embedding: That transfers an existing central involution through Slofstra's embedding; this constructs the central involution from an arbitrary nontrivial killed word before that embedding.
artifacts:
  - research/artifacts/liu-to-linear-games-and-marked-gap-2026-09-20.md
---

Let G=<S|R> be finitely presented and w a word representing a nonidentity
element killed by every homomorphism to a tracial matrix ultraproduct.
There is an effective finitely presented group K and a distinguished
nonidentity central involution J killed by every such homomorphism.

Use two copies G_1,G_2, put v=w_1 w_2 in G_1*G_2, and set

```
K = < S_1,S_2,J,t |
      R_1,R_2,J^2,[J,s] (s in S_1 union S_2),[t,J],
      t v t^-1 (v J)^-1 >.
```

For unitary assignments in arbitrary finite dimensions define
kappa_G(delta)=sup ||w(U)-I||_2 over max relator defect at most delta.
For the displayed presentation,

```
kappa_K,J(delta) <= 4 kappa_G(delta) + delta.
```

In particular kappa_K,J(delta) tends to zero. The relation [t,J] is
included explicitly: centrality in the HNN base alone is not centrality in
the HNN extension. No numerical rate for kappa_G is asserted.

If w is already a nontrivial involution, the two source copies are
unnecessary. Use G times C2 and the automorphism of <w,J> isomorphic to
C2 times C2 given by w -> wJ, J -> J. The resulting presentation has
generators S,J,t and relators R,J^2,[J,s],[t,J],twt^-1(wJ)^-1, with the
sharper estimate kappa_K,J(delta) <= 2 kappa_G(delta)+delta.
