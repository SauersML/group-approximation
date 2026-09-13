---
rg: 2
id: leavitt-algebras-l-k-1-n-are-simple
kind: claim
title: For every field K and every n >= 2 the Leavitt algebra L_K(1,n) is a simple ring
distinct_from:
  leavitt-center-is-coefficient-field: that computes the center of the binary Leavitt algebra; this is simplicity of every Leavitt algebra L_K(1,n), imported from the Abrams--Aranda Pino theorem.
  binary-leavitt-elementary-group-is-simple: that is simplicity of large elementary groups over the binary Leavitt algebra; this is simplicity of the algebras themselves, which makes every nonzero homomorphism out of them injective.
---

**ESTABLISHED** by `leavitt-algebras-l-k-1-n-are-simple-citation`.

Let `K` be a field and `n >= 2`. Then

```text
L_K(1,n) = K<x_1..x_n, y_1..y_n | y_i x_j = delta_ij, sum_i x_i y_i = 1>
```

has no two-sided ideals other than `0` and itself.

`L_K(1,n)` is the Leavitt path algebra `L_K(R_n)` of the rose `R_n`: one vertex
and `n` loops. `R_n` has only the trivial hereditary saturated subsets. Every
cycle of `R_n` has an exit when `n >= 2`, since a loop exits through any other loop.
So the Abrams--Aranda Pino simplicity theorem applies.

**Use.** A nonzero ring homomorphism out of `L_K(1,n)` is injective. This is
used by `leavitt-unit-groups-over-finite-fields-mutually-embed-proof`.
