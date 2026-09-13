---
rg: 2
id: a7a7a8-triangle-candidates-no-small-linear-representation
kind: claim
title: The four (A_7, A_7, A_8) triangle candidates have no nontrivial linear representation of dimension at most 7 over any field
distinct_from:
  a7a7a8-triangle-candidates-no-4dim-char2-representation: that is the single case of dimension 4 in characteristic 2; this is every dimension up to 7 in every characteristic, and uses that case
---

Let `G_1, …, G_4` be the four `(A_7, A_7, A_8)` hyperbolic triangles of groups with `Z/7`
edge groups. The data are in `experiments/hyperbolic-triangle-search/cands.g`.

**Claim.** For each `i`, every field `K` and every `d <= 7`, every homomorphism
`G_i -> GL_d(K)` is trivial. So no `G_i` has a nontrivial finite quotient with a faithful linear
representation of dimension at most 7 in any characteristic.

**Cases, by the faithful vertex modules.**
- **`char K ∉ {2, 7}`.** `A_8` needs dimension 7. The modules are `1 ⊕ 6` and `7`, and the integral
  trace-ideal certificate is `N = 1`.
- **`char K = 7`.**
  - On the `A_8`-module `7`, a 7-element is a single Jordan block. So by edge consistency the `A` and `B`
    modules are free over a Sylow 7-subgroup.
  - Hence they are projective with factors `{5,1,1}`, which forces the permutation module.
  - The same certificate `N = 1` covers this case.
- **`char K = 2`.**
  - **The type is uniform.** The composition type `{6, 1^k}` or `{4 or 4*, 1^k}` is the same at every
    vertex, because the eigenvalue multisets of the edge generators must match.
  - **Type 6.** `{6}` has trace ideal `(1)`; `{6, 1}` is covered by `N = 1`.
  - **Type 4, setup.** The modules are semisimple, and `W_X = [V, X]` is 4-dimensional.
  - **Type 4, all `W_X` equal.** Then everything happens in dimension 4, which is
    `a7a7a8-triangle-candidates-no-4dim-char2-representation`.
  - **Type 4, otherwise.** `W_A + W_B + W_C` is a 5-dimensional invariant subspace with modules `4 ⊕ 1`,
    and that case has trace ideal `(1)`.

**Projective representations** `G_i -> PGL_7(K)`, whose edge lifts may differ by `μ_7`, are recorded in
`research/artifacts/hyperbolic-triangle-linear-search-2026-09-13.md` §§5–6:
- excluded in characteristics 0, 7, 29 and 43;
- excluded in all but finitely many characteristics, by case (b) of
  `linear-quotient-exclusion-lifts-from-char-zero`;
- the effective integer `N` is not computed. The integral twisted Gröbner runs with `a ≠ 0` were stopped
  after 50 minutes and about 11 GB each without finishing.

The claim is computer-assisted (Sage 10.7 / Singular) and unreviewed. The small Brauer characters of
`A_7` and `A_8` for `p = 2, 3, 5, 7` are recalled rather than re-derived, and so is `H^1(L_4(2), F_2^4) = 0`.
