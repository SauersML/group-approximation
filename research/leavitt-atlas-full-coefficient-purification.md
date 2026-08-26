---
rg: 2
id: leavitt-atlas-full-coefficient-purification
kind: claim
title: Every positive Leavitt atlas certificate purifies to one growing full-coefficient matrix block
distinct_from:
  leavitt-regular-atlas-hyperlinearity-criterion: that permits arbitrary relative unitaries at arbitrary multiplicities; this proves convex mixtures and internal centers can be removed and gives an equivalent irreducible target.
  leavitt-regular-atlas-block-monomial-gap: that forces mass to escape bounded internal sizes; this selects one full matrix summand carrying no more average relator energy than the original model.
  atlas-packet-collision-m2-has-full-coefficient-algebra: that verifies full coefficients in one fixed multiplicity-two countermodel which fails another atlas word; this is an asymptotic purification principle for a hypothetical complete certificate.
artifacts:
  - notes/EXPLICIT_LEAVITT_ATLAS.md
---

Let `bar S` be the fixed finite relator set and put

```text
E(U)=|bar S|^(-1) sum_(s in bar S) ||pi_U(s)-1||_2^2.
```

The binary Leavitt group is hyperlinear if and only if there are integers
`r_i->infinity` and relative unitaries

```text
U_i in U(20160 r_i)
```

such that:

1. the `20160 by 20160` block coefficients of `U_i` generate the full matrix
   algebra `M_(r_i)(C)`;
2. `max_(s in bar S)||pi_(U_i)(s)-1||_2 -> 0`.

In particular, direct sums of rational transports, convex mixtures of finite
quantum absorbers, and growing centers add no feasibility. Any successful
construction may be required from the start to be internally irreducible,
with dimension diverging and, by
`leavitt-regular-atlas-block-monomial-gap`, order-one noncommutativity among
its block coefficients.
