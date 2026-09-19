---
rg: 2
id: universal-hyperbolic-vtf-iff-rf-proof
kind: route
title: Turn an invisible infinite-order element into invisible torsion
target: universal-hyperbolic-vtf-iff-rf
requires: []
---

`(1) -> (2)` is immediate: residual finiteness says `R_f(G)=1`.

`(2) -> (1)`. Suppose instead that a word-hyperbolic group `G` is not
residually finite, and choose `1 != g in R_f(G)`. If `g` has finite order,
then `R_f(G)` already contains nontrivial torsion. If `g` has infinite
order, Wise's quoted Theorem 9.3 gives `n>1` such that

```text
G_bar = G / <<g^n>>
```

is word-hyperbolic and `g_bar != 1`. The relation `g_bar^n=1` makes
`g_bar` torsion. For every homomorphism `psi:G_bar->F` to a finite group,
`psi` composed with `G->G_bar` is a finite quotient of `G`, so it kills `g`;
hence `psi(g_bar)=1`. Thus `1 != g_bar in R_f(G_bar)`, contradicting (2).

`(1) -> (3)`. A word-hyperbolic group has only finitely many conjugacy
classes of torsion elements. Under residual finiteness choose one finite
quotient separating a representative of each nonidentity class; the kernel
is finite-index and torsion-free.

`(3) -> (1)` is Wise's Proposition 9.2. Its proof is exactly the same
contrapositive construction above, together with Lemma 9.1: nontrivial
finite-residual torsion lies in every finite-index subgroup, so no
finite-index subgroup can be torsion-free. `QED`

Primary source: Daniel T. Wise, *Complete square complexes*, Comment. Math.
Helv. **82** (2007), 683--724, DOI `10.4171/CMH/107`, pp. 713--714,
Proposition 9.2 and Theorem 9.3.
