---
rg: 2
id: haettel-flag-poset-contractibility-criterion
kind: claim
title: "Haettel: a simply connected typed simplicial complex whose vertex order is a partial order with bowtie-free flag upper and lower sets is contractible"
distinct_from:
  artin-k-pi-1-from-contractible-artin-complex: that turns contractibility of an Artin complex into the K(π,1) conjecture; this is a combinatorial criterion for contractibility of a typed simplicial complex.
---

Let `S = {s_1, …, s_n}` be totally ordered, and let `X` be a simplicial complex of type `S`:
each vertex has a type in `S`, and the vertices of a simplex have distinct types. For
vertices `x, x'` write `x < x'` when `x, x'` are neighbours and `type(x) < type(x')`.

A poset is *bowtie free* when for any distinct `x_1, x_2, y_1, y_2` with `x_i < y_j` for all
`i, j` there is `z` with `x_i ≤ z ≤ y_j` for all `i, j`. It is *upward flag* (resp. *downward
flag*) when any three pairwise upper-bounded (resp. lower-bounded) elements have a common
upper (resp. lower) bound.

**Criterion.** Suppose:

1. `X` is simply connected;
2. the relation `<` on `X^0` is a partial order;
3. for each `x ∈ X^0`, the set of vertices `≥ x` is bowtie free and upward flag;
4. for each `x ∈ X^0`, the set of vertices `≤ x` is bowtie free and downward flag.

Then `X` is contractible.

Literature import through `haettel-flag-poset-contractibility-criterion-citation`.
