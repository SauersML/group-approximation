---
rg: 2
id: burau-power-projective-ping-pong-needs-cubes
kind: claim
title: Closed projective ping-pong for powers of the 4-strand Burau generators exists exactly from cubes on
distinct_from:
  four-strand-burau-representation-is-faithful: that claim is injectivity of Burau on B_4, equivalently freeness of <A, B>; this claim is about one proof method, closed ping-pong sets on the projective plane, for the pair of powers (A^m, B^n), and shows it works exactly when min(m, n) >= 3
  burau-kernel-avoids-short-point-pushing-braids: that claim is a finite computational exclusion of kernel words; this claim is a structural threshold for ping-pong configurations
artifacts:
  - research/artifacts/burau-power-projective-ping-pong-2026-09-16.md
  - experiments/zaremsky-3-05-burau-squares-2026-09-16/threshold_verify.py
  - experiments/zaremsky-3-05-burau-squares-2026-09-16/bbt_sets_test.py
---

**Setup.** Work in the reduced Burau image of `B_4` in `GL_3(Z[t, t^{-1}])`.

- Witzel–Zaremsky generators: `f = diag(t, 1, t^{-1})` and `k = s f s^{-1}`.
- Beridze–Bigelow–Traczyk generators: `A`, `B`.
- After `t -> -t`, the pair `(A, B)` is conjugate to `(f, k)` by an integral
  matrix `P` with `det P = -t^2 (t-1)^2 (t^2+1)`.
- The explicit matrices are in the artifact.

**4-set ping-pong.** For `g, h` acting on a set `Z`, a *4-set ping-pong* is a
choice of nonempty, pairwise disjoint sets `X_{g+}, X_{g-}, X_{h+}, X_{h-}` in
`Z` such that

- `g^{±1}` maps `X_{g±} ∪ X_{h+} ∪ X_{h-}` into `X_{g±}`, and
- `h^{±1}` maps `X_{h±} ∪ X_{g+} ∪ X_{g-}` into `X_{h±}`.

It forces `<g, h>` to be free on `g, h`. Let `m, n >= 1`.

1. **Obstruction.**
   - **Setting.** Let `K` be any field with an absolute value, of any
     characteristic, archimedean or not. Specialize `t` to some `t_0 ∈ K`
     with `|t_0| != 1`.
   - **If `n <= 2`.** No 4-set ping-pong for `(f^m, k^n)` on `P^2(K)` has
     `X_{f+}` and `X_{f-}` closed.
   - **If `m <= 2`.** No such configuration has `X_{k+}` and `X_{k-}`
     closed.
   - **Consequence.** If `min(m, n) <= 2`, there is no configuration with all
     four sets closed.
   - **Dual plane.** The same holds on the dual plane `P^2(K)^*`.
2. **Existence.** Let `F` be any field and `K = F((t))` with the `t`-adic
   absolute value. If `m, n >= 3`, there is a 4-set ping-pong for
   `(f^m, k^n)`, and also one for `(A^m, B^n)`, on `P^2(K)` with all four
   sets clopen.

So closed ping-pong on the projective plane proves freeness of `<f^m, k^n>`
exactly when `min(m, n) >= 3`. This explains why the exponent 3 recurs in
Moran, in Witzel–Zaremsky (arXiv:1304.7923) and in Beridze–Bigelow–Traczyk
(arXiv:1904.11730).

- **Closedness is essential.** Over an uncountable `K`, a 4-set ping-pong
  with arbitrary sets exists iff `<f^m, k^n>` is free on `f^m, k^n`. Without
  closedness the method is therefore tautological.
- **Out of scope.** The claim says nothing about:
  - ping-pong on buildings or flag varieties, including the rays of
    Witzel–Zaremsky Remark 3.5;
  - the 2-set form;
  - ping-pong arguments on other spaces.

Proof: route `burau-power-projective-ping-pong-needs-cubes-proof` and the
artifact.
