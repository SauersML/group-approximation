---
rg: 2
id: perfect-lcs-gap-implies-weak-non-mf
kind: claim
title: A perfect commuting LCS gap makes its solution group weak non-MF
distinct_from:
  perfect-lcs-gap-implies-nonhyperlinear: That conclusion only excludes faithful Hilbert--Schmidt models; this one excludes even weak operator-norm matrix-corona embeddings by renormalizing the finite central sign sector.
  mf-hyperlinear-of-finite-normal-quotient: That theorem also assumes the quotient is hyperlinear and concludes that the whole MF group is hyperlinear; this uses only visibility of the finite central sign and makes no assumption on the quotient.
  hs-collapse-sign-twist-non-mf: That construction adjoins an HNN sign-twist to an arbitrary involutive HS-collapse mark; here the original solution group is already non-MF and no wrapper is added.
  central-extension-twisted-sector-criterion: That is an equivalence conditional on MF of the central quotient; this is a one-way obstruction which needs no approximation hypothesis on the quotient.
artifacts:
  - research/perfect-lcs-gap-implies-weak-non-mf-proof.md
  - research/artifacts/property-t-free-non-mf-literature-audit-2026-08-30.md
---

Let `G(A,b)` be a finite binary linear-constraint-system game and let
`Gamma(A,b)` be its finitely presented solution group, with distinguished
central involution `J`.  If

```text
omega^co(G(A,b))=1,
omega^q(G(A,b))<1,
```

then `Gamma(A,b)` is not MF even in the weak Carrión--Dadarlat--Eckhardt
operator-norm sense

```text
Gamma(A,b) -> U(product_n M_(d_n) / directSum_(||.||) M_(d_n)).
```

Indeed, perfect commuting play makes `J` algebraically nontrivial, whereas
the strict finite-dimensional value gap prevents `J` from being visible in
normalized-Hilbert--Schmidt approximate representations.  If the solution
group were weak MF, the finite normal subgroup `<J>` would instead make `J`
tracially visible after passing to a nonzero invariant isotypic corona
corner and normalizing that corner by its own rank.  This contradiction
does not use Property `(T)`, a Kazhdan pair or projection, spectral gap,
stability, expansion, or any hypothesis on `Gamma(A,b)/<J>`.

This is a conditional endgame, not an existence theorem: no finite LCS with
the displayed perfect gap is currently known.  Producing one is the
`epsilon=0` threshold which Taller--Vidick identify with the
nonhyperlinear-group problem.
