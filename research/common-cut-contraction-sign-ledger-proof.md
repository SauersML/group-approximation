---
rg: 2
id: common-cut-contraction-sign-ledger-proof
kind: route
title: Expand through one common two-block grading and sign only at the end
target: common-cut-contraction-sign-has-complete-balanced-energy-ledger
requires:
  - aggregate-cut-compression-stores-boundary-as-involution-defect
  - one-anchor-grading-makes-parity-damage-quadratic
  - involution-augmented-code-jacobian-adds-no-cb-loss
  - quadratic-overlay-has-uniform-linearized-synchronization-gap
  - tangent-commutator-covariance-bypasses-code-riesz-endpoint
---

Relative to `p+q`, `X_i` and `O_i` are respectively block diagonal and
block off-diagonal.  The diagonal and off-diagonal corners of `B_i^2=I`
give `X_i^2+O_i^2=I` and `X_iO_i+O_iX_i=0`.  Taking the normalized trace
gives `(CCL1)--(CCL2)`; the last inequality uses `0<=O_i^2<=I`.

The conditional expectation `Phi` retains exactly the words containing an
even number of off-diagonal factors.  Separating the empty subset gives
`(CCL3)`.  Linearity and contractivity of `Phi` give `(CCL4)`.  Taking the
even part of the commutator expansion gives

```text
 Phi([B_i,B_j])=[X_i,X_j]+[O_i,O_j],
```

which is `(CCL5)`.  Telescoping through contractions gives
`||prod X-prod B||_2<=sum_a d_(i_a)`; the scalar inequalities
`(u+v)^2<=2u^2+2v^2` and
`(sum_a d_(i_a))^2<=m sum_a d_(i_a)^2` prove `(CCL6)`.
Furthermore

```text
 ||[O_i,O_j]||_2
 <=||O_iO_j||_2+||O_jO_i||_2
 <=2 min(d_i,d_j),
```

because every `O_i` is a contraction.  This proves `(CCL8)`.

For `lambda in [-1,1]`, with either choice of sign at zero,

```text
 |sgn(lambda)-lambda|=1-|lambda|<=1-lambda^2.
```

Squaring and integrating proves `(CCL9)`.  Telescope a fixed word from
`X` to `S` and use Cauchy--Schwarz to obtain `(CCL10)`.  The triangle
inequality followed by `(u+v+w)^2<=3(u^2+v^2+w^2)` gives `(CCL11)`.
Finally

```text
 ||[S_i,S_j]-[X_i,X_j]||_2<=2a_i+2a_j,
```

and the same three-term inequality gives `(CCL12)`.

After averaging, bounded face width and bounded normalized occurrence turn
the coordinate sums in `(CCL6)`, `(CCL10)`, and `(CCL11)` into constant
multiples of the average coordinate energy.  For the dense layer use
`min(d_i^2,d_j^2)<=d_i^2`; the final sign terms in `(CCL12)` average to
`24L^(-1)sum_i r_i^2`.

The last paragraph of the claim combines the exact kernel description of
the complete-pair Jacobian with the involution normal/tangent splitting.
The finite-time covariant-divergence/Green step gives a completely bounded
strict contraction on this quotient.  Its character decomposition is still
an exact-base input, which is why the global nonlinear basin remains open.
