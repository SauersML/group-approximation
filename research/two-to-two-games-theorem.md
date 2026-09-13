---
rg: 2
id: two-to-two-games-theorem
kind: claim
title: 2-to-2 Games Theorem -- for every eps there is l with Gap 2-to-2 over F_2^l at (1-eps, eps) NP-hard (Khot--Minzer--Safra 2018)
distinct_from:
  unique-games-conjecture: that asks the same near-1 versus near-0 gap for permutation constraints; this is the proved gap for constraints accepting two values, with completeness 1-eps.
  rich-2to1-games-conjecture: that is the open 2-to-1 hardness with the richness condition on pairings; this is the proved 2-to-2 hardness with linear constraints and no richness.
  k-uniform-hypergraph-vertex-cover-hardness-without-ugc: that is a downstream Karthik--Minzer consequence through multilayered 2-to-2 label cover; this is the base 2-to-2 theorem.
---

**ESTABLISHED, BY CITATION.** An instance of `2-to-2 Game[F_2^l]` has variables
`x_1, ..., x_n` over `F_2^l` and constraints

```text
T_ij x_i + T'_ij x_j in { b_ij, b'_ij },     T_ij, T'_ij invertible l x l,  b_ij, b'_ij in F_2^l.
```

**Theorem.** For every constant `eps > 0` there is `l = l(eps)` such that
`Gap 2-to-2[F_2^l](1-eps, eps)` is NP-hard.

This combines Khot--Minzer--Safra (STOC 2017), Dinur--Khot--Kindler--Minzer--Safra
(STOC 2018, two papers) and Barak--Kothari--Steurer, with the final
combinatorial hypothesis on pseudorandom sets of the Grassmann graph proved by
Khot--Minzer--Safra (FOCS 2018). Completeness is **imperfect** (`1-eps`). The
original conjecture asked for perfect completeness, and that version remains
open. As the source's footnote 2 records, the linear constraints reinterpret as
2-to-1 constraints, so this also proves the 2-to-1 Games Conjecture with
imperfect completeness.

Consequence in this graph: `unique-games-hard-at-completeness-one-half`, the
best unconditional unique games gap. Its completeness is `1/2`, where
`unique-games-conjecture` needs `1-eps`.

DERIVATION two-to-two-games-theorem-citation
