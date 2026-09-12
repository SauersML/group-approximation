---
rg: 2
id: kazhdan-two-complex-b2-is-euler-characteristic-minus-one
kind: claim
title: A Kazhdan group with a finite nonpositively curved 2-complex model has b_2 equal to its Euler characteristic minus one
distinct_from:
  kazhdan-hyperbolic-b2-group-flexibly-hs-stable: that is the open stability premise; this is the elementary computation that certifies its b_2 >= 1 clause at explicit 2-complex candidates, with no stability content
---

**ESTABLISHED.** Let `K` be a finite connected 2-dimensional polygonal complex
whose universal cover `X`, in a piecewise Euclidean or hyperbolic metric with
finitely many shapes, is CAT(0). Put `Γ = π_1(K)`.

1. `K` is a `K(Γ,1)`, so `χ(Γ) = χ(K)`.
2. If `Γ` has property (T), then `b_2(Γ;Q) = χ(K) - 1`.
3. If every face is a `p`-gon and every vertex link is a graph with `v_L` vertices
   and `e_L` edges, then `χ(K) = |V|(1 - v_L/2 + e_L/p)`.
4. If `X` is CAT(−1), then `Γ` is word-hyperbolic.

**Worked instance.** Take hyperbolic squares with corner angles `π/3`, and let every
link be the incidence graph of the projective plane `PG(2,q)` (girth 6). Then the
link condition holds, `X` is CAT(−1), and

```text
χ(K) = |V| (1 + (q^2+q+1)(q-3)/4).
```

For `q = 3` this is `|V|`. The formal conditional gives `b_2 = |V| - 1`
under (T), but no Kazhdan instance with at least two vertices exists:
`square-pg23-groups-cannot-be-kazhdan` proves the obstruction by assigning
Euclidean squares and applying the CAT(0) cubical fixed-point theorem.
The general Euler formula above remains valid; the former suggested
application of Żuk's simplicial criterion to square links was invalid.

DERIVATION
kazhdan-two-complex-b2-euler-characteristic-proof
