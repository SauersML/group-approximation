---
rg: 2
id: iwahori-low-gap-common-cluster-gauge
kind: claim
title: Low-gap Iwahori clusters admit one common reducing gauge after negligible stabilization
---

In the central-sector Iwahori setup, choose thresholds `a_n->0` with
`E_n/a_n->0` and form the bipartite low-gap graph on the source and target
Iwahori isotypic blocks.  Then, after adding `o(d_n)` trivial coordinates,
there are orthogonal projections `(R_(n,C))_C` summing to the stabilized
identity and a unitary `V_n` with

```text
||V_n-I||_(2,d_n) -> 0
```

such that:

1. every `R_(n,C)` reduces the source representation `rho_n`;
2. every `R_(n,C)` reduces the conjugated target representation
   `sigma'_n=V_n sigma_n V_n^*`;
3. the source and target cluster dimensions agree exactly on every `C`; and
4. the aggregate generator discrepancy still tends to zero:

```text
sum_(s in S_B)||rho_n(s)-sigma'_n(s)||_(2,d_n)^2 -> 0.
```

Thus the Iwahori basin problem decomposes, after a negligible gauge change,
into independent **same-carrier** problems indexed by connected low-gap
clusters.  No cross-cluster matching, rank balancing, or relative-position
problem remains.