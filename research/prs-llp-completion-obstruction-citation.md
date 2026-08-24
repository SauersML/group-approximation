---
rg: 2
id: prs-llp-completion-obstruction-citation
kind: route
title: Import Paulsen--Rahaman--Samei Theorems 4.6 and 4.9
target: llp-regular-dominating-completion-forces-nonhyperlinear
requires: []
artifacts:
  - research/artifacts/paulsen-harris-lalonde-tang-macmahon-source-audit-2026-08-23.md
---

## Source theorem

Paulsen--Rahaman--Samei, arXiv:2606.18369v1, Theorem 4.6 states that if
`G` is hyperlinear, `pi` is a nonamenable unitary representation of `G`,
and the left regular representation `lambda_G` is weakly contained in
`pi`, then `C^*_pi(G)` does not have LLP.  Taking the contrapositive gives
exactly the claim:

```text
lambda_G prec pi + pi nonamenable + LLP(C^*_pi(G))
  => G is not hyperlinear.
```

The same source's Theorem 4.9 gives the advertised Brown--Guentner
specialization: for nonamenable `G` and an algebraic ideal `D` containing
`c_00(G)` with `C^*(G) != C^*_D(G)` canonically, `C^*_D(G)` has no
amenable trace, and hyperlinearity of `G` forces `C^*_D(G)` to fail LLP.
No property-(T), residual-finiteness, or full-group-algebra hypothesis is
present in either implication.
