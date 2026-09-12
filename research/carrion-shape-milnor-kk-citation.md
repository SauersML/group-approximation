---
rg: 2
id: carrion-shape-milnor-kk-citation
kind: route
title: Import Carrion's Milnor sequence and Hausdorffness criterion
target: carrion-shape-milnor-detects-kk-hausdorffness
requires: []
artifacts:
  - research/artifacts/stw-operator-literature-exact-imports-2026-08-30.md
---

Apply Jose R. Carrion, *A Milnor exact sequence for E-theory*,
arXiv:2608.06496v1 (2026-08-06), Theorem 1.1 and Corollary 4.3, to the
separable algebras `A` and `B` and the specified shape system for
`SA tensor K`.  Theorem 1.1 identifies

```text
closure({0}) in E(A,B) = lim^1 [C_n,S^2 B tensor K]
```

inside the displayed natural Milnor exact sequence.  Corollary 4.3 gives the
Hausdorffness equivalence and the Mittag--Leffler sufficient condition.

Since `A` is nuclear, `E(A,B)=KK(A,B)`.  Proposition 4.5 states that this is
an isomorphism of topological groups, carries the closure of zero onto the
closure of zero in `KK(A,B)`, and identifies the Hausdorff quotients.  These
are exactly the hypotheses and conclusions in the target claim; no UCT or
`Q`-stability assertion is added.
