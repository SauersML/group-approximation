---
rg: 2
id: iwahori-low-gap-cluster-integralization-proof
kind: route
title: Apply spectral transport localization then stabilized cluster polar rounding
target: iwahori-low-gap-cluster-integralization
requires:
  - mixed-intertwiner-energy-transport-localization
  - block-transport-cluster-unitarization
---

Use the exact transportation plan

```text
m_(n,i,j)=||P_(n,i) Q_(n,j)||_2^2
```

for the identity identification.  By
`mixed-intertwiner-energy-transport-localization`, for the threshold `a_n`,

```text
beta_n := sum_(lambda_(n,i,j) >= a_n) m_(n,i,j)
        <= E_n/a_n -> 0.                               (1)
```

Let `G_n` be the bipartite graph of pairs with `lambda_(n,i,j)<a_n`.
If two vertices belong to different connected components of `G_n`, their
pair is certainly not an edge of `G_n`.  Therefore the off-component mass
`gamma_n` appearing in `block-transport-cluster-unitarization` satisfies

```text
gamma_n <= beta_n -> 0.                               (2)
```

Apply that theorem to the reducing isotypic projections of the two exact
Iwahori representations and to `U=I`.  It adds at most
`gamma_n d_n=o(d_n)` dimensions on each side, balances every connected
component, and produces componentwise unitaries whose direct sum obeys

```text
||W_n-I||_2 <= (1+sqrt(2)) sqrt(gamma_n) -> 0.         (3)
```

For the fixed Iwahori generator packet `S_B`, the same theorem gives

```text
sqrt(E(W_n))
 <= sqrt(E_n)+2 sqrt(2 |S_B| gamma_n) -> 0.            (4)
```

The stabilizing coordinates may carry the trivial `B` representation, which
is exact.  By construction `W_n` has no matrix block between distinct
connected components of `G_n`.  Thus `(1)--(4)` give exactly the claimed
component-scale integralization.