---
rg: 2
id: nonhyperlinear-from-centralizer-product-classicalization
kind: route
title: Thirty centralizer products, classicalized, contradict the 19243 distance floor
target: non-hyperlinear-group
requires:
  - atlas-thirty-centralizer-products-classicalize
  - atlas-a4-packet-centralizer-product-compiler
  - atlas-a4-19243-classical-collapse
  - atlas-19243-centrality-forces-s3-distance
  - leavitt-regular-atlas-separating-refinement
---

Assume the prerequisites and suppose `Q = L_(F_2)(1,2)^x` is hyperlinear.
`leavitt-regular-atlas-separating-refinement` produces canonical regular-`A_8`
relative-unitary models `U_k in U(20160k)` whose packet defect tends to zero
while the compiled collision word `19243` stays nontrivial.

`atlas-a4-packet-centralizer-product-compiler` converts the thirty shortest
`A_4` relations into thirty centralizer-product constraints, so

```text
max_(1<=j<=30) dist_2(U_k, C(rho_k(a_j)) C(rho_k(b_j))) -> 0.
```

`atlas-thirty-centralizer-products-classicalize` then gives
`dist_2(U_k, B_k) -> 0` with `B_k` the finite classical alignment branch set,
uniformly in `k`.

`atlas-a4-19243-classical-collapse` says no member of `B_k` satisfies the
collision condition, and `atlas-19243-centrality-forces-s3-distance` makes
that quantitative on the same sequence: every atlas microstate keeps
`liminf_k dist_2(U_k, C(rho_k(K))) >= sqrt(2)/16` for the fixed `S_3` slice
`K` of `19243`.  Approaching `B_k` drives that distance to the value it takes
on the branches, which is zero, contradicting the floor.

Hence no such `U_k` exists and `Q` is not hyperlinear -- an explicit
non-hyperlinear group.

**Where the difficulty sits.**  Entirely in the first prerequisite; the other
four are established.  The route is recorded so that the frontier shows one
hole rather than a program.
