---
rg: 2
id: nonsingular-adjunction-preserves-approximation-radicals
kind: claim
title: Nonsingular relative presentations preserve both approximation radicals on coefficients
distinct_from:
  universal-mf-quotient: that constructs a universal MF quotient for one group; this proves that a nonsingular coefficient map induces an injection between the two universal quotients and also treats the hyperlinear radical.
  nonsingular-equations-preserve-matrix-certificates: that is a fixed-size matrix and quantitative certificate theorem; this extends every homomorphism into a unitary product quotient and identifies exact radical pullbacks.
artifacts:
  - research/artifacts/nonsingular-equations-and-approximation-radicals.md
---

Let `G` be countable, `w in G*<t>` have nonzero `t`-exponent, and
`q:G -> H=(G*<t>)/<<w>>` be the coefficient map. Every homomorphism from
`G` into any algebraic quotient `(prod_n U(d_n))/N`, with `N` normal,
extends to `H` with the same target. In particular,

```text
q^(-1)(Rad_MF(H)) = Rad_MF(G),
q^(-1)(Rad_hyp(H)) = Rad_hyp(G),
ker(q) <= Rad_MF(G) intersect Rad_hyp(G).
```

Here MF uses norm matrix coronas and the hyperlinear radical uses tracial
metric ultraproducts; neither approximation notion is substituted for the
other. The result also holds for countable successive triangular adjunctions
whose new equation is nonsingular in its newly added variable.

This proves injectivity on both radical quotients. It does not show that
`q` is injective for every group or classify new-variable radical elements.
