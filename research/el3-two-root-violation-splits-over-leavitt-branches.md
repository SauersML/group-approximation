---
rg: 2
id: el3-two-root-violation-splits-over-leavitt-branches
kind: claim
title: The unit two-root product of a characteristic-two model of the Leavitt unit group splits over the two Leavitt branches
distinct_from:
  leavitt-isometry-commutators-constrain-el3-rank-models: that records the commutator identities forced by the isometry coefficients t_i, s_j; this is the exact decomposition of the coefficient-one product N_23 N_12 over the orthogonal idempotents s_i t_i, with the branch swap and the defect factorization of any commutator.
artifacts:
  - research/artifacts/el3-two-root-self-similarity-2026-09-12.md
---

**ESTABLISHED** (proof route `el3-two-root-branch-split-proof`; artifact Sections 2–3). Let
`R = L_K(1,2)` with `char K = 2`, `sigma : EL_3(R) -> M^x` a homomorphism into a ring with
`2 = 0`, and `n_ab(c) = sigma(x_ab(c)) - 1`.

**Defect factorization.** For distinct `i, j, k` and `a, b` in `R`, with `X = n_ij(a)` and
`Y = n_jk(b)`,

```text
n_ik(ab) = XY + (1 + X)(YX)(1 + Y).
```

In a rank ultraproduct, `rk(n_ik(ab) - XY) = rk(YX)`, and this defect is invariant under Weyl
relabeling and two-sided unit changes of the coefficients.

**Branch split.** Put `e_i = s_i t_i`, `a_i = n_12(e_i)`, `b_i = n_23(e_i)`, `P_i = b_i a_i`. Then
`a_0, b_0` commute with `a_1, b_1`, and

```text
N_23 N_12 = P_0 (1 + a_1 + b_1 + P_1) + P_1 (1 + a_0 + b_0) + (b_0 a_1 + b_1 a_0).
```

Conjugation by `sigma(diag(w,w,w))`, `w = s_0 t_1 + s_1 t_0`, fixes `N_12` and `N_23` and swaps
the branches, so `rk P_0 = rk P_1`. `P_0` is the unit two-root product of the branch model
`sigma o iota_0`, `iota_0(g) = s_0 g t_0 + (1 - e_0)`. So

```text
rk(N_23 N_12) <= 2 rk(two-root product of sigma o iota_0) + rk(b_0 a_1 + b_1 a_0).
```

This is an upper bound only. Tensor-type models have no matching lower bound (artifact
Section 6).
