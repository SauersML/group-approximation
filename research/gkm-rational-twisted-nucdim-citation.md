---
rg: 2
id: gkm-rational-twisted-nucdim-citation
kind: route
title: Import the exact rational-twist nuclear-dimension computation
target: gkm-rational-twists-have-hirsch-nuclear-dimension
requires: []
artifacts:
  - research/artifacts/stw-operator-literature-exact-imports-2026-08-30.md
---

Apply Forrest Glebe, Pradyut Karmakar, and Iason Moutzouris,
*Nuclear Dimension of Twisted C-star Algebras of Virtually Abelian Groups*,
arXiv:2605.27936v1 (2026-05-27), Theorem 4.12 (Theorem A).

Theorem 4.12 assumes exactly that `G` is finitely generated and virtually
abelian and that `[sigma]` is a rational class in `H^2(G,T)`, and concludes

```text
dim_nuc C*(G,sigma) = h(G).
```

The paper's Theorem 3.9 identifies rationality, in this setting, with the
existence of a root-of-unity-valued representative (and with the twisted
algebra being subhomogeneous).  This justifies the equivalent formulation in
the claim.  Nothing from the paper's separate irrational-torus upper bound
is promoted to an equality here.
