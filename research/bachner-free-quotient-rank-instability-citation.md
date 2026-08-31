---
rg: 2
id: bachner-free-quotient-rank-instability-citation
kind: route
title: Pull Bachner's uniform rank-instability models back from F_2
target: free-quotient-obstructs-flexible-uniform-rank-stability
requires: []
---

Source: Benjamin Bachner, *Uniform rank-metric stability of Lie algebras and
groups*, [arXiv:2408.15614v2](https://arxiv.org/abs/2408.15614), Theorem 1.3
and Proposition 4.1.

Proposition 4.1 constructs, over every field `K`, a uniform
`3/n`-representation `phi_n:F_2 -> GL_n(K)` with an element represented
at full normalized-rank distance from the identity, while

```text
d_flex(phi_n, psi) >= 1/6 - 1/(6n)
```

for every genuine representation `psi:F_2 -> GL_N(K)`. Given a surjection
`pi:Gamma -> F_2`, Theorem 1.3 pulls these maps back along `pi`; lifts in
`Gamma` of the two free generators give the identical gap against every
genuine representation of `Gamma`.

This is **uniform** defect and distance: the defect is the supremum over all
pairs of group elements and the distance is the supremum over all group
elements. It is not pointwise rank stability or weak stability of the group
algebra. Flexible comparison uses the paper's infinite-corner convention for
different matrix sizes, normalized by the smaller size. The theorem assumes
a quotient onto `F_2`, not merely a nonabelian free subgroup.

Status: arXiv preprint v2, revised 2026-04-15. The primary HTML statement,
definitions, quantitative bound, and pullback proof were checked 2026-08-31.
