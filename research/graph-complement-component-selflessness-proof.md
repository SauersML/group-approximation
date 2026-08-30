---
rg: 2
id: graph-complement-component-selflessness-proof
kind: route
title: Decompose the complement into complete-selfless factors and classify the two-vertex obstruction
target: graph-products-no-universal-vertex-selfless-criterion
requires:
  - complete-selflessness-is-tensor-stable
  - graph-products-connected-complement-are-selfless
  - non-dihedral-free-products-are-completely-selfless
  - robert-directed-unions-preserve-selflessness
  - robert-tracial-selfless-regularity
artifacts:
  - research/artifacts/stw91-graph-component-selflessness-audit-2026-08-30.md
---

Let `(C_i)_(i in I)` be the connected components of `Gamma^c`, and let

```text
P_i=graph_product_(Gamma[C_i]) G_v.
```

Because distinct complement components have no complement edge between them,
every vertex of `C_i` is adjacent in `Gamma` to every vertex of `C_j` for
`i!=j`.  The graph-product presentation therefore gives

```text
P=direct_sum_(i in I) P_i,
```

where this means the restricted direct product if `I` is infinite.

There are no singleton `C_i`, since `Gamma` has no universal vertex.

If `|C_i|>=3`, the complement of `Gamma[C_i]` is the connected graph `C_i`.
Thus `graph-products-connected-complement-are-selfless` shows that
`C*_r(P_i)` is completely selfless.

If `C_i={v,w}`, connectedness means that `v,w` are not adjacent in `Gamma`,
so

```text
P_i=G_v * G_w.
```

By `non-dihedral-free-products-are-completely-selfless`, its reduced algebra
is completely selfless exactly when `G_v,G_w` are not both `C_2`.

Assume condition 3.  Every component factor is therefore completely selfless.
For every finite `F subset I`,

```text
P_F=product_(i in F) P_i
```

has completely selfless reduced algebra by
`complete-selflessness-is-tensor-stable`.  If `I` is finite, this already
proves complete selflessness of `C*_r(P)`.

If `I` is infinite, the canonical copies of `C*_r(P_F)` form an upward
directed family with norm-dense union in `C*_r(P)`: every group-ring element
uses only finitely many complement components.  Hence
`robert-directed-unions-preserve-selflessness` proves ordinary selflessness
of `C*_r(P)`.  This proves `3=>2`, and
`robert-tracial-selfless-regularity` gives `2=>1`.

For `1=>3`, suppose `{v,w}` is a complement component labelled by two copies
of `C_2`.  Then

```text
P=D_infinity x Q
```

for the graph product `Q` over all remaining complement components.  Since
`D_infinity` is amenable, its trivial representation gives a noninjective
character `epsilon:C*_r(D_infinity)->C`.  Consequently

```text
epsilon tensor id:
C*_r(D_infinity) tensor_min C*_r(Q)->C*_r(Q)
```

has a nonzero proper kernel.  Thus `C*_r(P)` is not simple, contradicting
condition 1.

Finally suppose every `G_v` is nontrivial and C-star-simple.  Such a group is
infinite: for a nontrivial finite group, the averaging projection

```text
|G_v|^(-1) sum_(g in G_v) lambda(g)
```

is a nontrivial central projection.  Hence every `C*_r(G_v)` is simple,
separable, unital, and non-elementary, with faithful canonical trace.
There are no isolated vertices of `Gamma^c`.  Flores--Klisse--O
Cobhthaigh--Pagliero, arXiv:2510.24675v3, Corollary E, now applies directly
and gives complete selflessness, even when `I` is infinite.

There is no remaining gap.