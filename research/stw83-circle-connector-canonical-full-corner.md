---
rg: 2
id: stw83-circle-connector-canonical-full-corner
kind: claim
title: Every finite acyclic connector between two circles collapses to a canonical full corner
artifacts:
  - research/artifacts/stw83-lxxxiii-graph-nuclear-dimension-audit-2026-08-30.md
---

Let `F` satisfy the four graph hypotheses of
`stw83-circle-circle-boundary-index`, and let `N>=1` be its weighted connector
path count.  Let `E_N` be the graph with two vertices `v,w`, one loop at each
vertex, and exactly `N` parallel edges from `v` to `w`.

Choose vertices `v_0` and `w_0` on the upstream and downstream cycles of `F`
and set `P=p_(v_0)+p_(w_0)`.  Then `P` is full in `C*(F)` and

```text
P C*(F) P = C*(E_N).                                   (1)
```

Here (1) denotes a canonical isomorphism: the edges of `E_N` correspond to
paths in `F` which start and end in `{v_0,w_0}` and have no intermediate
vertex in that set.  Consequently

```text
C*(F) tensor K = C*(E_N) tensor K,
dim_nuc(C*(F)) = dim_nuc(C*(E_N)).                     (2)
```

The canonical algebra also has an explicit Toeplitz-module model.  If `S` is
the unilateral shift, `A=C(T)`, and both act on the standard Hilbert
`A`-module, then

```text
C*(E_N) = C*(S^N tensor 1, K tensor A)
          subset M(K tensor A).                        (3)
```

Thus the nuclear-dimension-one question for every finite circle-by-circle
graph with an acyclic connector reduces, without using classification or only
`K`-theory, to the concrete family in (3).  The value for this canonical
family remains open.
