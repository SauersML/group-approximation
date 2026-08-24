---
rg: 2
id: pakhunov-critical-face-structural-laws
kind: claim
title: The critical-tilt tangent framework has a kernel law, a homogeneous pin space, and a two-row germ step
artifacts:
  - research/artifacts/npa-critical-face-dimension-law-audit-2026-08-23.md
---

At the symmetric critical doubly-tilted CHSH point of the `(2,2,2)` scenario,
write `Gamma_k(y)` for the level-`k` moment matrix, `N_k` for the matrix of
`T/D` relation columns, and

```text
Phi_k(y) := N_k^T Gamma_k(y) N_k,
V_k      := { (y, lambda) : Phi_k(y) = lambda u_k u_k^T,  y_[identity] = 0 }.
```

The following are imported from the source, not proved here.

1. **Counting law.**  `|W_k| = 2k^2 + 2k + 1`, the number of moment classes at
   level `k` is `C_k = (5k+2)(k+1)/2`, and the `2k^2` columns of `N_k` are
   linearly independent.
2. **Kernel law.**  At `delta* = (1/2, 1/4, 1/2, ..., 1/2)` truncated to length
   `k`, `ker Gamma_k(y_0(delta*)) = span N_k` exactly, of dimension `2k^2`, and
   `rank Gamma_k = 2k+1` splitting as `(k+1, k)` into party-symmetric and
   antisymmetric parts.  Positive definiteness verified for `k <= 8`.
3. **Homogeneous pins.**  All pins of the tangent program are homogeneous, so
   `V_k` is a linear space.
4. **Germ step.**  The old-class rows of the level-`(k+1)` system reduce, modulo
   the level-`k` system, to exactly two residual conditions supported on the
   level-`k` unseen classes `m_k = 1(01)^(k-1)` of length `2k-1`:

   ```text
   y[(empty,m_k)] - y[((0),m_k)]                                = -1/2
   y[(empty,m_k)] - y[((1),m_k)] - y[((0),0m')] + y[((1),0m')]  = (4k-3)/2
   ```

   This was obtained by an exact induction-step analysis of the transitions
   `2->3`, `3->4`, `4->5` only.  The accompanying assertion that unseen
   coordinates are free at level `k` rests on the same computation and is
   **not** imported here; it is carried as the separate open claim
   `npa-unseen-classes-are-free-at-level-k`.

Source: Anton Pakhunov, *No finite level of the NPA hierarchy is exact for the
doubly-tilted CHSH functional near the critical tilt*, arXiv:2607.13762,
Proposition 2.1, Theorem 3.7, Lemma 5.3(1), Section 4.1, Remark 4.10.
