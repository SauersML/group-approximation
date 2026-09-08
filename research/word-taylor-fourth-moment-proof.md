---
rg: 2
id: word-taylor-fourth-moment-proof
kind: route
title: Differentiate the word twice, count the terms, and apply normalized Schatten Hoelder
target: word-taylor-remainder-has-a-fourth-moment-bound
requires: []
artifacts:
  - research/artifacts/pde-transfer-quadratic-repair-2026-09-08.md
---

## Proof

Write `f(t) = w(U(t)) = V_1(t) ... V_ell(t)`, each `V_j(t)` being either
`U_s exp(i t X_s)` or `exp(-i t X_s) U_s^*`.  In the first case
`V_j'' = - V_j X_s^2`, in the second `V_j'' = - X_s^2 V_j`; in both cases the
second derivative is a unitary with one factor `X_s^2` attached on one side,
and the first derivative is a unitary with one factor `X_s` attached on one
side.

By the product rule,

```text
f''(t) = sum_j V_1 ... V_j'' ... V_ell
         + sum_(j != m) V_1 ... V_j' ... V_m' ... V_ell,
```

which is `ell + ell(ell - 1) = ell^2` terms.  Every term is a product of
unitaries carrying either one factor `X_s^2` or two factors `X_i`, `X_j`.
Normalized Schatten norms are unitarily invariant and satisfy Hoelder, so

```text
|| P X_i Q X_j R ||_(2,d) <= ||X_i||_(4,d) ||X_j||_(4,d),
|| P X_s^2 Q ||_(2,d)     = ||X_s^2||_(2,d) = ||X_s||_(4,d)^2,
```

for unitary `P, Q, R` (the two-factor case uses `1/4 + 1/4 = 1/2`).  Hence
`||f''(t)||_(2,d) <= ell^2 (max_s ||X_s||_(4,d))^2` for every `t`, uniformly,
since `exp(i t X_s)` is unitary and does not change any of these norms.

Taylor's theorem with integral remainder gives

```text
f(1) - f(0) - f'(0) = int_0^1 (1 - t) f''(t) dt,
```

whose norm is at most `(1/2) sup_t ||f''(t)||_(2,d)`.  That is `(WT1)`.

For `(WT2)`: `tr_d |X|^4 <= ||X||_op^2 tr_d |X|^2`, so
`||X||_(4,d)^4 <= ||X||_op^2 ||X||_(2,d)^2`.  For `theta_eff <= 1`: by
Cauchy-Schwarz `tr_d |X|^2 <= (tr_d |X|^4)^(1/2)`, i.e.
`||X||_(2,d)^2 <= ||X||_(4,d)^2`.  For `X = a P`,
`||X||_(2,d)^2 = a^2 mu` and `||X||_(4,d)^2 = a^2 sqrt(mu)`, so
`theta_eff = mu`.
