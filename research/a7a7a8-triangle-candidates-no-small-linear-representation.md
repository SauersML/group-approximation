---
rg: 2
id: a7a7a8-triangle-candidates-no-small-linear-representation
kind: claim
title: The four (A_7, A_7, A_8) triangle candidates have no nontrivial linear representation of dimension at most 7 in characteristic 0 or 3, 5, 11, 13, 29, 43
distinct_from:
  a7a7a8-triangle-candidates-no-4dim-char2-representation: that is dimension 4 in characteristic 2, where A_7 and A_8 act on 4 or 4*; this is dimension 7 in characteristic 0 and in six odd characteristics, with modules 1+6 and 7
---

Let `G_1, …, G_4` be the four `(A_7, A_7, A_8)` hyperbolic triangles of groups with `Z/7`
edge groups. The data are in `experiments/hyperbolic-triangle-search/cands.g`.

For each `i`, every homomorphism `G_i -> GL_d(K)` is trivial whenever `d <= 7` and
`char K ∈ {0, 3, 5, 11, 13, 29, 43}`.
- For `d <= 6` this holds because `A_8` has no faithful representation of that dimension in
  these characteristics.
- For `d = 7` the only faithful modules are `1 ⊕ 6` for `A_7` and `7` for `A_8`, and the
  trace ideal of the torus parametrisation has Gröbner basis `[1]`.

So no `G_i` has a nontrivial finite quotient with a faithful linear representation of dimension
at most 7 in these characteristics. That covers every such subgroup of `GL_7(p^m)`, for example of
`SL_7(p^m)` or `Ω_7(p^m)`, for `p ∈ {3, 5, 11, 13, 29, 43}`.

The claim does not cover projective representations `G_i -> PGL_7(K)` in which the lifts of an edge
generator from its two vertex groups differ by a 7th root of unity. So it does not cover
quotients inside `PSL_7(p^m)` when `7 | p^m − 1`.

The result is computer-assisted (Sage 10.7 / Singular) and unreviewed.
