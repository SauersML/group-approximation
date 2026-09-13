---
rg: 2
id: p-cycle-tree-invariance-cannot-force-order-char-law-proof
kind: route
title: Truncated-exponential models on elementary abelian p-groups are coherent rank functions with every Frobenius-allowed profile
target: p-cycle-tree-invariance-cannot-force-order-char-law
requires: []
artifacts:
  - research/artifacts/p-cycle-tree-rank-models-and-ternary-gate-2026-09-12.md
  - research/artifacts/w3-vf-linear-verification-2026-09-12.md
---

This is Section 2 of the artifact (w7-v-cycle-c3). `w3-vf-linear` re-derived it in §33.3, and checked the scope fix
a886f33f26 in §34.6. It is a complete direct proof. Its scope is elementary abelian `p`-subgroups of `V` and injective
homomorphisms between them.

**Proof.**
- **Rank functions.** For `s < m <= p`, the coefficient of `u^s` in `exp_m(au) exp_m(bu)` is `(a + b)^s/s!`. So
  `rho_m` is a ring map `F[E] -> L[u]/(u^m)`, and `rk_m` is the pullback of the normalized rank on `M_m(L)`.
- **Coherence** (Lemma 2.1). An injective homomorphism sends the basis to `F_p`-independent vectors, which stay
  independent over `F`. Completing the substitution of variables to an invertible one gives a field embedding over
  `F`, and rank is invariant under it and under field extension.
- **Profiles** (Lemma 2.2). `1 − exp_m(lambda u)` is `u` times a unit, so `(1 − [g])^j` has rank `max(m − j, 0)` for
  `g != 1`. The column `col(1 − [tau_i])` kills exactly `u^(m−1) L`, so the joint fixed rank is `1/m`.
- **Every allowed profile** (Proposition 2.3(1)). With `d_p = 0`, the weights `w_m = m(d_(m−1) − d_m)` are nonnegative
  and sum to `1`, and `sum_m w_m rk_m` has drops `d_i`.
- **The law fails.**
  - At `j = m < p`, `0 = (1 − phi)(p − m)/p` forces `phi = 1`. Then `j = 1` gives `(m − 1)/m != 0`.
  - `1/m = phi + (1 − phi) p^(-r)` for all `r` forces `phi = 1/m`, and then `m = 1`.
- **Finite models** (Proposition 2.3(3)). Specialization never raises rank. Schwartz–Zippel and a union bound over the
  first `k` matrices give failure probability at most `k(k + 1)/p^k`.

*Verification by `w3-vf-linear` (2026-09-12), §33.3 and §34.6 of `research/artifacts/w3-vf-linear-verification-2026-09-12.md`: PASS. Claims 1–6 re-derived; the scope is elementary abelian p-subgroups, as corrected in a886f33f26.*
