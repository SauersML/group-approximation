---
rg: 2
id: mikhailova-left-right-lef-rf-proof
kind: route
title: Use finite generation to collapse almost-finite-index models to separability
target: mikhailova-left-right-lef-iff-quotient-rf
requires: []
---

## The fiber product is finitely generated

Let `N=ker(q)`.  The relators `r_1,...,r_k` normally generate `N`
in `F_m`.  The diagonal elements `(x_i,x_i)` generate every
`(w,w)`, and

```text
(w,w)(r_j,1)(w,w)^(-1)=(w r_j w^(-1),1).
```

Thus the elements displayed in `(MLA2)` generate `N x {1}`.  If
`(u,v) in M_H`, then `uv^(-1) in N` and

```text
(u,v)=(uv^(-1),1)(v,v).
```

This proves `(MLA2)`.

## LEF action implies separability

The action is transitive with stabilizer `M_H`.  Proposition 4.5 of
Alekseev--Bradford, *Sofic actions, halo products, and metric
approximations of groups* (arXiv:2601.18742), says that a transitive action
`G` on `G/M_H` is LEF exactly when `M_H` is almost of finite index.

Assume the action is LEF.  In the definition of almost finite index take

```text
tilde G=G=F_m x F_m,       rho=id_G.
```

The group `G` is finitely presented, so there are finite-index subgroups
`J_n<G` with

```text
J_n -> M_H in Sub(G).                                    (MLP1)
```

Let `T` be the finite generating set in `(MLA2)`.  Chabauty convergence
means `J_n cap T=M_H cap T=T` eventually.  Hence `M_H<=J_n` eventually.
For any fixed `g notin M_H`, equation `(MLP1)` also gives `g notin J_n`
eventually.  Therefore every element outside `M_H` is excluded by a
finite-index subgroup containing `M_H`; this is separability of `M_H`
in `G`.

This step is where finite presentation of `H` is load-bearing.  Without
finite generation of the stabilizer, a sequence converging to `M_H` need
not eventually consist of overgroups of `M_H`.

## Separability is equivalent to residual finiteness of H

If `H` is residually finite and `(u,v) notin M_H`, choose a finite
quotient `p:H->C` with `p(q(u)) != p(q(v))`.  The finite quotient

```text
(pq) x (pq):G->C x C
```

sends `M_H` into `Delta C` and sends `(u,v)` outside `Delta C`.
Thus `M_H` is separable.

Conversely, suppose `M_H` is separable and let `q(w) != 1`.  Since
`(w,1) notin M_H`, there is a finite quotient `theta:G->K` with

```text
theta(w,1) notin theta(M_H).                            (MLP2)
```

Put

```text
A=theta(F_m x {1}),       D=theta(N x {1}).
```

Then `D normal A`, and `(MLP2)` implies
`theta(w,1) notin D`.  The map `F_m->A/D` kills `N` but not `w`,
so it factors through a finite quotient of `H` separating `q(w)`.
Hence `H` is residually finite.

## Residual finiteness supplies LEF models

If `H` is residually finite, then `M_H` is separable by the preceding
argument, and the transitive `G`-set is residually finite.  More directly,
for a prescribed finite packet in `H`, choose a finite quotient
`p:H->C` injective on that packet and use the exact finite left-right
action

```text
C x C acts on C,        (a,b).c=a c b^(-1).
```

Pulling the actor labels back through `q x q` gives an exact LEF action
chart.  This proves the converse and completes all three equivalences.
