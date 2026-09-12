---
rg: 2
id: native-sl3-group-is-hecke-graph-wreath-product
kind: claim
title: The native two-coordinate group is the graph wreath product of the arithmetic Hecke orbital graph
distinct_from:
  native-sl3-commuting-involution-group: that proves finite presentation, mark nontriviality, and exact finite-dimensional invisibility; this identifies the whole group structurally.
  sl3-codense-coset-lamp-recursive-host: that has the abelian direct-sum lamp base, equivalently the graph product over the complete graph on A/C; this uses only one Hecke edge orbital and has a right-angled Coxeter base.
---

Let `X=A/C` and let `Theta_h` be the `A`-invariant simple graph on `X` whose
edge set is the orbit of the unordered pair

```text
{C,hC}.
```

Let

```text
B_Theta = graph_product_(x in X) C_2
```

be the right-angled Coxeter group with one involution `c_x` per vertex and
commutation exactly on the edges of `Theta_h`.  Then

```text
G_cc isomorphic to B_Theta rtimes A,                    (HGW1)
```

where `A` permutes the vertex groups through its action on `A/C`.

Thus the native candidate is precisely a **graph wreath product**.  Its mark
`[c,h]=c_C c_(hC)` is the product of the two commuting generators on the
distinguished edge.
