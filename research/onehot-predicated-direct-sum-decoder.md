---
rg: 2
id: onehot-predicated-direct-sum-decoder
kind: claim
title: One-hot selector sectors decode predicated branch copies by direct sum with no gate-link relations
artifacts:
  - research/artifacts/selector-overlap-rounding-2026-08-18.md
distinct_from:
  controlled-linear-predication-normal-form: that constructs gated copies from a known controlled strategy; this is the converse decoding step once one-hot selector sectors have been recovered.
  zpc-selector-robust-lcs-compiler: that still needs an LCS mechanism making selector overlap pay for output loss; this theorem says no additional relation linking branch copies to one common unreadable operator is needed.
---

Let `Q_a` be pairwise orthogonal projections in a finite tracial algebra,
`Q=sum_a Q_a`, and assume `q=tau(Q)>0`.  For every branch `a` and unreadable
variable `i`, let `G_(a,i)` be a self-adjoint involution commuting with every
`Q_b`.  Define in the normalized corner `(QMQ,tau_Q)`

```text
U_i = sum_a Q_a G_(a,i),
tau_Q(x)=tau(x)/q.
```

Then every `U_i` is a self-adjoint involution.  Suppose branch `a` selects an
affine equation

```text
sum_(i in I) x_i = b mod 2
```

and the compiled predicated relation uses a selector involution `Z_a` with
`Q_a Z_a=-Q_a`:

```text
H_(a,I)=product_(i in I) G_(a,i) ~= Z_a^b.
```

Whenever the variables participating in the equation commute on the branch,

```text
||Q_a(product_(i in I) U_i-(-1)^b)||_2
 <= ||H_(a,I)-Z_a^b||_2.                         (DS1)
```

Consequently, for any nonnegative weights `lambda_e` on the finite source
check set, the decoded controlled-linear strategy on the good corner has total
weighted squared equation defect at most

```text
(1/q) sum_(a,e) lambda_e
      ||H_(a,e)-Z_a^(b_(a,e))||_2^2.              (DS2)
```

The readable answer is simply the classical direct-sum label `a` of the sector
`Q_a`.  No relation `product_a G_(a,i)=U_i`, and no requirement that inactive
gated copies equal one, is needed for sound decoding.
