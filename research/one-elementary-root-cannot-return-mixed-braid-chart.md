---
rg: 2
id: one-elementary-root-cannot-return-mixed-braid-chart
kind: claim
title: One elementary root cannot return the mixed-braid channel-nine chart
invalidates:
  - one-root-returns-mixed-braid-channel-nine-chart
artifacts:
  - research/one-root-mixed-braid-return-proof.md
distinct_from:
  first-cross-whitehead-has-no-alternative-low-depth-return: that classifies a root or same-pair partial inverse appended to the coarse cross Whitehead `K_0`; this treats an arbitrary-coefficient elementary root after the asymmetric channel-nine involution produced by the mixed braid.
  one-nonnormal-dressing-cannot-preserve-moving-full-gram: that uses the transporter torsor for one already correct native target; this proves directly that the present residual chart cannot return even to the signed source.
---

**ESTABLISHED ONE-ROOT CHANNEL-NINE FENCE.**  Put

```text
P=[[q_0,1],[q_1,q_0]]_(7,9)
 =x_79(q_1)x_97(q_1)x_79(1),                          (ORB1)
```

and let `n=x_79(1)` be the positive signed generator of `L_0`.  Then

```text
PnP^(-1)=x_79(q_0)x_97(q_1)=:1+N,
N=q_0E_79+q_1E_97.                                   (ORB2)
```

For every actor pair `a!=b` and every binary-Leavitt coefficient `c`, set

```text
R=x_ab(c).
```

In the conjugate `R(1+N)R^(-1)`, at least one of the two displayed entries
is unchanged:

```text
coefficient at (7,9) remains q_0,  unless (a,b)=(7,9),
coefficient at (9,7) remains q_1,  unless (a,b)=(9,7). (ORB3)
```

When `(a,b)=(7,9)`, the `(9,7)` coefficient is still exactly `q_1`;
when `(a,b)=(9,7)`, the `(7,9)` coefficient is still exactly `q_0`.
Thus in every case one original entry is the nonconstant proper idempotent
`q_0` or `q_1`.

Every element of `L_0` is a constant binary matrix.  Consequently

```text
R P n P^(-1) R^(-1) notin L_0,
R P notin Norm(L_0,lambda_0),                         (ORB4)
```

and uniqueness of finite group-algebra support gives

```text
(RP)Q(RP)^(-1) != Q.                                 (ORB5)
```

This closes one arbitrary elementary continuation, with no restriction on
the coefficient depth or root position.  It does not exclude two further
nonnormal occurrences or a genuine three-coordinate return, and it does
not classify the separate native-target equation
`J_1^(-1)RP in Norm(L_0,lambda_0)`.

No Property `(T)`, trace hypothesis, stability theorem, enumeration, or
local computation is used.

DERIVATION
one-root-mixed-braid-return-proof

## Attempts

- **Use a root away from `(7,9)`.**  Such a conjugation can add a new row
  or column but cannot alter either original opposite entry.
- **Use one of the two opposite roots on `(7,9)`.**  It may alter the
  coefficient in its own orientation through the quadratic conjugation
  term, but the coefficient in the reverse orientation is untouched.

