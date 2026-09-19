---
rg: 2
id: amenable-edge-hnn-hyperlinear-permanence-proof
kind: route
title: Realize the von Neumann HNN extension as a corner of an amenable amalgam
target: amenable-edge-hnn-preserves-hyperlinearity
requires: []
---

Put `M=L(G)` and `N=L(A)`, with the two trace-preserving embeddings

```text
i_0:N->M,                 lambda_a |-> lambda_a,
i_1:N->M,                 lambda_a |-> lambda_(theta(a)). (AEH2)
```

Because `G` is hyperlinear, `M` is Connes embeddable.  Because `A` is
amenable, `N` is hyperfinite.  Matrix amplification preserves Connes
embeddability.

Ueda's reduced-HNN/AFP identification realizes the reduced von Neumann HNN
extension of `(M,N,i_0,i_1)` as the `e_11` corner of

```text
(M_2(C) tensor M)
  *_(N direct-sum N)
(M_2(C) tensor N),                                      (AEH3)
```

where the first embedding of `N direct-sum N` uses `i_0` and `i_1`, and the
second is the diagonal matrix embedding.  The amalgam in `(AEH3)` is
hyperfinite.  Brown--Dykema--Jung, Corollary 4.5, says that a tracial
amalgamated free product of Connes-embeddable finite von Neumann algebras over
a hyperfinite von Neumann algebra is Connes embeddable.  Hence `(AEH3)` is
Connes embeddable, and so is its `e_11` corner.

For subgroup embeddings `(AEH2)`, the reduced von Neumann HNN extension is
canonically `L(H)`, where `H` is the group HNN extension `(AEH1)`: the group
stable letter supplies the HNN unitary, and Britton normal form gives the
matching reduced-word trace.  Therefore `L(H)` is Connes embeddable.  For a
countable discrete group this is equivalent to hyperlinearity, proving the
claim.

Primary sources:

- Yoshimichi Ueda, *A relationship between HNN extensions and amalgamated
  free products in operator algebras*, arXiv:math/0601706 (2006), especially
  the corner realization of the reduced HNN extension.
- Nathanial P. Brown, Kenneth J. Dykema and Kenley Jung, *Free entropy
  dimension in amalgamated free products*, Proc. London Math. Soc. 97 (2008),
  arXiv:math/0609080, Corollary 4.5.

No finite-dimensional trace inequality is asserted here.  The proof is a
permanence theorem for Connes embeddability and therefore is compatible with
properly infinite exact witnesses; its force is precisely that amenability of
the edge still makes all of those witnesses approximable after the HNN step.
