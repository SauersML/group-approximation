---
rg: 2
id: mf-residual-topology-is-hausdorffized-by-reflection
kind: claim
title: MF reflection is the Hausdorffization of the intrinsic MF residual topology
artifacts:
  - research/mf-residual-topology-is-hausdorffized-by-reflection-proof.md
---

Give a countable group `G` the **MF residual topology** whose identity
neighborhood basis consists of kernels of homomorphisms from `G` to countable
MF groups, each target being discrete.  Then:

```text
closure_G({1})=Rad_MF(G).                              (MT1)
```

The quotient map

```text
G -> R_MF(G)
```

is the Hausdorffization of this topological group.  Hence the MF residual
topology is Hausdorff exactly when `G` is MF.

For every normal subgroup `N`, equip `G/N` with its intrinsic MF residual
topology.  The preimage in `G` of the closure of its identity is exactly

```text
mfroot_G(N).                                           (MT2)
```

Thus MF-semantic closure is literal topological indistinguishability after
imposing the relations `N`.  A quotient `G/N` is MF exactly when its intrinsic
MF residual topology is Hausdorff.
