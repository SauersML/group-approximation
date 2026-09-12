---
rg: 2
id: odd-measure-space-has-no-honest-thompson-compression
kind: claim
title: The space of odd two-valued measures carries an invariant Haar measure, so Thompson translates cannot honestly compress it into a proper clopen set
invalidates: [ternary-lift-by-honest-odd-measure-compression]
artifacts:
  - research/artifacts/ternary-lift-signed-thompson-crossed-product-2026-09-12.md
---

Let `M_-` be the space of finitely additive `F_2`-valued measures on the clopens of Cantor space
with `mu(X) = 1`, with Thompson's group `V` acting by pushforward, as in
`signed-thompson-algebra-is-odd-measure-crossed-product`.

1. The normalized Haar measure `lambda` on `M_-` is `V`-invariant, has full support, and satisfies
   `lambda({mu(C) = 1}) = 1/2` for every proper nonempty clopen `C`.
2. **No honest compression.** Let `A_1, ..., A_n` be a clopen partition of `M_-`, and let `g_i in V` be
   such that the translates `g_i A_i` are pairwise disjoint and contained in a clopen `U`. Then
   `U = M_-`.
3. **Consequence.** No partial isometry `v = sum [g_i] 1_(A_i)` of this shape in
   `C(M_-, F_3) ⋊ V` has `v* v = 1` and `v v*` below a proper clopen idempotent. In particular the
   naive lift `[g_1] q_[0] + [g_2] q_[1]` of the Hilbert-hotel isometry `s0` fails:
   * its images overlap on `{mu(00) = mu(01) = 1}`;
   * `q_[00] + q_[01] - q_[0] = 2 q_[00] q_[01] != 0`.

Not excluded: covers with multiplicities `1 mod 3` whose cross terms cancel mod 3, and witnesses using
units outside the signed Thompson group. Proposition 4 of the artifact.
