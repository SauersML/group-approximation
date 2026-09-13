---
rg: 2
id: a7a7a8-triangle-candidates-no-small-linear-representation
kind: claim
title: The four (A_7, A_7, A_8) triangle candidates have no nontrivial linear representation of dimension at most 7 in any characteristic other than 2 and 7
distinct_from:
  a7a7a8-triangle-candidates-no-4dim-char2-representation: that is dimension 4 in characteristic 2, where A_7 and A_8 act on 4 or 4*; this is dimension at most 7 away from characteristics 2 and 7, with modules 1+6 and 7
---

Let `G_1, …, G_4` be the four `(A_7, A_7, A_8)` hyperbolic triangles of groups with `Z/7`
edge groups. Their data are in `experiments/hyperbolic-triangle-search/cands.g`.

**Claim.** For each `i` and every field `K` with `char K ∉ {2, 7}`, including characteristic 0,
every homomorphism `G_i -> GL_d(K)` with `d <= 7` is trivial.
- **Dimension at most 6.** `A_8` has no faithful representation of dimension below 7 in these
  characteristics, so the homomorphism is trivial.
- **Dimension 7.** The only faithful modules are `1 ⊕ 6` for `A_7` and `7` for `A_8`. With the circulant
  parametrisation of the `B`-conjugator and the trace equations of the `A_8`-heart, the
  resulting ideal over `Z` has strong Gröbner basis `[1]`. So there are no solutions over any field.
- **Partial results in characteristics 2 and 7.**
  - `p = 2`: no representation of module type `(6 ⊕ 1, 6 ⊕ 1, factors {6,1})`.
  - `p = 7`: none where `A` and `B` act by the permutation module.
- **Consequence.** No `G_i` has a nontrivial finite quotient with a faithful 7-dimensional linear
  representation in characteristic `≠ 2, 7`, for example inside `SL_7(p^m)` or `Ω_7(p^m)`.

**Projective representations `G_i -> PGL_7(K)` are recorded separately.** These are the ones where the lifts of an edge
generator differ by a 7th root of unity.
- For `char K ∈ {29, 43}`, all 343 twists give trace ideal `(1)`.
- In characteristic 0, all 58 Galois orbits of twists give `(1)` for `G_1` and `G_3`; `G_2` and `G_4` are running.
- The integral version is running.
- Status: `research/artifacts/hyperbolic-triangle-linear-search-2026-09-13.md` §5.

The claim is computer-assisted (Sage 10.7 / Singular) and unreviewed. For `p = 3, 5` the list of small
Brauer characters of `A_8` is recalled, not re-derived.
