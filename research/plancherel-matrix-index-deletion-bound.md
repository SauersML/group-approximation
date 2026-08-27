---
rg: 2
id: plancherel-matrix-index-deletion-bound
kind: claim
title: Hall deficit after Fourier-edge deletion is bounded by deleted Plancherel branching mass
---

Let `H<=G` be finite groups and let

```text
m_(sigma,theta)=dim Hom_H(theta, Res^G_H sigma).
```

Refine each `sigma in Irr(G)` into matrix-index vertices `(sigma,a)`,
`1<=a<=d_sigma`, each of weight `d_sigma/|G|`, and each
`theta in Irr(H)` into `(theta,b)`, `1<=b<=d_theta`, each of weight
`d_theta/|H|`.  On the full restriction-support graph put the edge transport

```text
Pi((sigma,a),(theta,b))=m_(sigma,theta)/|G|.          (PMD1)
```

Then `Pi` has exactly the stated source and target marginals.

Now delete any set `F` of branching edges and let `E` be the remaining graph.
For a source set `S`, let `N_E(S)` be its remaining target neighborhood and
write

```text
Delta_E(S)=w(S)-w(N_E(S)).                            (PMD2)
```

Then

```text
Delta_E(S)
 <= Pi({(v,u) in F : v in S, u notin N_E(S)})
 <= Pi(F).                                             (PMD3)
```

Consequently the maximum weighted Hall deficit of the pruned graph satisfies

```text
max_S Delta_E(S) <= Pi(F)
 = (1/|G|) sum_((sigma,a),(theta,b) in F)
             m_(sigma,theta).                         (PMD4)
```

Thus a relation-sensitive Fourier search cannot obtain a fixed Hall gap by
certifying only a negligible collection of low-Plancherel-mass coefficient
zeros.  Before expensive noncommutative ideal elimination, candidate zero
patterns can be rejected solely from their deleted branching-mass budget.
