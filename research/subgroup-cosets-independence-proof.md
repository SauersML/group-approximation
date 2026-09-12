---
rg: 2
id: subgroup-cosets-independence-proof
kind: route
title: Clear denominators in the affiliated algebra of the subgroup, then use orthogonality of the coset decomposition
target: subgroup-cosets-are-independent-over-division-closure
requires: []
artifacts:
  - research/artifacts/atiyah-coproduct-inner-rank-2026-09-12.md
---

Let `a_1 x_1 + ... + a_n x_n = 0` with `a_i in U(H)` and the right cosets
`H x_i` pairwise distinct.

1. **Common denominator.** `N(H)` is a finite von Neumann algebra, so it
   satisfies the left Ore condition with respect to its non-zero-divisors and
   `U(H)` is the corresponding Ore localization. A finite family of elements of
   an Ore localization admits a common left denominator: there are `b in N(H)`
   injective with dense range and `c_1, ..., c_n in N(H)` with
   `a_i = b^(-1) c_i`.

2. **Clear it.** Applying `b` on the left to the relation gives
   `c_1 x_1 + ... + c_n x_n = 0` inside `N(H) . G <= N(G)`, an identity of
   bounded operators.

3. **Coset supports.** Realize `N(G)` on `l^2(G)` by left convolution. For
   `c in N(H)` the vector `c delta_e` lies in `l^2(H)`, and
   `c lambda(x) delta_e = (c delta_e) * delta_x` is supported in `H x`. The
   subspaces `l^2(H x_i)` are pairwise orthogonal because the cosets are
   distinct.

4. **Conclusion.** Evaluating the identity of step 2 at `delta_e` gives a sum of
   vectors in pairwise orthogonal subspaces that vanishes, so each
   `c_i delta_{x_i} = 0`. Since `lambda(x_i)` is unitary, `c_i delta_e = 0`, and
   `delta_e` is separating for `N(H)`, so `c_i = 0`. Hence
   `a_i = b^(-1) c_i = 0`. QED

The free-module statement follows by applying this to `a_i in D_H <= U(H)` and
one representative per coset.

Step 1 is what makes the argument work for unbounded affiliated coefficients:
an element of `U(H)` need not have `delta_e` in its domain, so step 3 cannot be
applied to `a_i` directly. Every input is a standard property of `N(H)`,
`U(H)` and the regular representation.
