---
rg: 2
id: atlas-edge-folner-natural-type-proof
kind: route
title: Compare the transvection rank on natural and free modular A8 modules
target: atlas-edge-folner-modules-miss-natural-type
requires:
  - atlas-augmented-relations-have-unbounded-chart-width
  - atlas-repeated-h6-gauge-is-one-gl2m-coordinate
---

A transvection on the four-dimensional natural module has the form
`I+e_(ij)`, so `t-I` has rank one.  This proves `(EFM1)` and gives the same
ratio on every direct sum `V^m`.

In the left regular module, the order-two permutation of the basis `A` by
`t` consists of `|A|/2` disjoint two-cycles.  In characteristic two, on each
two-cycle the operator `t-I` has matrix

```text
[1 1]
[1 1]
```

and rank one.  This proves `(EFM2)`.  A linear bundle over a free transitive
`A`-set is equivariantly trivial after choosing one fiber: transporting that
fiber along the unique group element identifies the decorated orbit module
with `F2[A] tensor W`, so the same half-rank calculation applies.

Let `R_n` be the free summand and `C_n` its invariant complement.  Rank on
direct sums and the trivial bounds on `C_n` give

```text
rank_(E_n)(t-I)/dim(E_n)=1/2-o(1).                    (EFM4)
```

For any two matrices `X,Y`,

```text
|rank(X-I)-rank(Y-I)|<=rank(X-Y).
```

Compare `(EFM4)` with the exact value `1/4` on the conjugated repeated
natural module to obtain `(EFM3)`.

Finally, edges of the Bass--Serre tree and of every genuine chart-coset
edge model have free left `A` and `B` actions.  A finite-subgraph/Folner
compression changes those free actions only on boundary cells.  If the
boundary density tends to zero, the preceding estimate applies separately
to both charts and yields the claimed obstruction.

