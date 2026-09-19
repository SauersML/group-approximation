---
rg: 2
id: corona-quotients-program-countable-graph-completions
kind: claim
title: Quotients of one matrix corona program every completion of a countable commutation graph
artifacts:
  - research/corona-quotients-program-countable-graph-completions-proof.md
---

Let `Gamma=(V,E)` be a countable graph and let `NED` be its set of nonedges.
There are nonidentity involutions `(u_v)_(v in V)` in

```text
Q_2=(prod_n M_2(C))/(directSum_n M_2(C))
```

and pairwise disjoint infinite coordinate sets `(C_e)_(e in NED)` such that

```text
Supp([u_v,u_w])=J_(C_{v,w})       for {v,w} in NED,
[u_v,u_w]=1                       for {v,w} in E.       (GC1)
```

For every subset `F subset NED`, let `I_F` be the principal ideal supported
on `union_(e in F) C_e`.  In the quotient `Q_2/I_F`, the images of the same
involutions have exact commutation graph

```text
Gamma_F=(V,E union F).                                 (GC2)
```

The assignment `F |-> I_F` is injective and order-preserving.  Therefore, if
`NED` is infinite, the quotient lattice of `Q_2` contains a copy of the full
power-set lattice `P(NED)` on which one fixed family of involutions realizes
all graph completions simultaneously.  Private support coordinates ensure
that no vertex involution disappears in any of these quotients.
