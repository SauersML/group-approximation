---
rg: 2
id: graph-witness-product-supplies-tensor-sync
kind: claim
title: Product with a finite-CEP graph witness supplies tensor synchronization without changing the kernel
artifacts:
  - research/artifacts/regular-mf-tensor-synchronized-rope-2026-08-25.md
  - research/artifacts/three-bridge-finite-cep-rope-route-2026-08-25.md
distinct_from:
  positive-benign-compiler-specializes-to-kernel-witness: that asks the ordinary witness itself to specialize to the graph witness; this takes their product, lets the graph factor supply finite edge models, and lets the ordinary regular-MF factor supply faithfulness.
  quotient-benign-witness-forces-finite-presentation: that obstruction uses one global quotient map killing the cutting subgroup; here each finite quotient uses a different map which may ignore the ordinary witness factor.
---

Let `N_e<=N_+` be normal subgroups of a finite-rank free group `F`.  Suppose
`w_e=(K_e,e_e,L_e)` is a uniformly constructed benign witness for `N_e` and
that `K_e` is regularly operator-MF realized on the positive specialization
`N_e=N_+`.  Suppose also that `Q_+=F/N_+` has an effective finite-CEP
embedding `j:Q_+->P` into a finitely presented residually finite group.

Take the product/intersection of `w_e` with the fixed graph witness

```text
K^graph=F times P,       L^graph=graph(F->Q_+->P).              (GWP1)
```

The resulting witness cuts out

```text
N_e intersect N_+ = N_e,                                      (GWP2)
```

so it is uniformly correct on both branches.  On the positive branch its
ambient group is regularly operator-MF, and so is its first central rope HNN.
For every finite quotient of `Q_+`, the graph factor supplies a finite map
`lambda_n` satisfying `(RTS1)`; this map is allowed to kill the entire
`K_e` factor.  Therefore the final twisted rope is regularly operator-MF by
`regular-mf-tensor-sync-proves-twisted-rope-mf`.

On the negative branch no approximation assertion is used: `(GWP2)` and the
ordinary rope normal form still embed `F/N_e`.
