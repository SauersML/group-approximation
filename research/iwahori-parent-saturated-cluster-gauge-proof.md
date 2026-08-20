---
rg: 2
id: iwahori-parent-saturated-cluster-gauge-proof
kind: route
title: Merge by modular parents, then apply low-gap cluster polar rounding
target: iwahori-parent-saturated-cluster-gauge
requires:
  - mixed-intertwiner-energy-transport-localization
  - block-transport-cluster-unitarization
---

Let `G_n^0` be the bipartite graph of low-gap cross pairs
`lambda_(n,i,j)<a_n`.  Transport localization gives

```text
beta_n=sum_((i,j) notin G_n^0)||P_(n,i)Q_(n,j)||_2^2
      <= E_n/a_n -> 0.                                (1)
```

Now add all source-parent and target-parent edges from the claim, obtaining
`G_n`.  Adding edges can only merge connected components.  Hence if a source
vertex `i` and target vertex `j` lie in distinct components of `G_n`, then in
particular `(i,j)` was not a low-gap edge of `G_n^0`.  Therefore the total
overlap mass between distinct `G_n` components is at most `beta_n`.

Apply `block-transport-cluster-unitarization` with `U=I` to the projections
obtained by summing Iwahori blocks over components of `G_n`.  It adds
`o(d_n)` trivial coordinates, balances source and target dimension component
by component, and supplies a direct-sum unitary `V_n` with

```text
||V_n-I||_2 -> 0                                      (2)
```

and vanishing aggregate Iwahori intertwining energy after conjugating the
target representation.

It remains only to check the stronger reduction statement.  Fix an
irreducible `K`-summand `pi` of `alpha_n`.  Every irreducible Iwahori
constituent of `pi|B` is joined to every other such constituent by the
source-parent edges, so they lie in one component `C`.  The entire carrier of
`pi` is the orthogonal sum of those Iwahori isotypic carriers and is therefore
contained in `P_(n,C)`.  Summing over the irreducible `K`-summands shows that
every `P_(n,C)` is a sum of full `K`-summands and hence commutes with
`alpha_n(K)`.  The same argument shows that every `Q_(n,C)` commutes with
`beta_n(K)`.

The component unitary satisfies `V_n Q_(n,C)V_n^*=P~_(n,C)` on the stabilized
spaces.  Consequently `P~_(n,C)` reduces

```text
beta'_n=V_n beta_n V_n^*
```

as well as the stabilized source representation.  Taking
`R_(n,C)=P~_(n,C)` gives one common full-vertex reducing decomposition.  The
Iwahori discrepancy estimate is exactly the energy estimate already supplied
by the cluster-unitarization theorem.  This proves all clauses.