---
rg: 2
id: binary-jacobson-second-balanced-t-root-is-half-supported
kind: claim
title: The second balanced Jacobson T-root is also at most half-supported on the raw range
artifacts:
  - research/binary-jacobson-second-balanced-t-root-support-proof.md
distinct_from:
  binary-jacobson-first-alternating-polar-is-half-supported: that computes the support of e x_21(T)e in the positive x_23(1),x_23(Q) sector; this treats the other T-labelled generator x_41(T) in the balanced target redesign.
  binary-jacobson-balanced-center-fold-authenticates-two-rows: that reduces the redesigned packet to two T-root leakage rows; this computes the raw compression support of the second of those rows.
  binary-jacobson-native-v4-polar-orbit-leaves-one-residual: that completes the first T-root support under source-row conjugations; this proves the second T-root is not by itself a full complementary return.
---

**ESTABLISHED.**  On the positive raw range `e=F_+`, put

```text
l=x_41(T),                  B=e l e.                     (JST1)
```

Then `e` commutes with `lel`, so `B` is a partial isometry with equal source
and range support

```text
B^*B=BB^*=p_l
 =e(1+x_43(Q))(1+x_43(ST))/4.                           (JST2)
```

In particular `p_l` lies in the positive `x_43(Q)` cut.  The native root
`x_14(Q)` preserves `e` and exchanges the two `x_43(Q)` signs on it, because
their commutator is the head root `x_13(Q)=-1` on `e`.  Hence

```text
rank(p_l)<=rank(e)/2                                     (JST3)
```

in every finite-dimensional exact model.

Thus the second T-labelled generator in the balanced target is not a full
raw return either.  The center fold authenticates the carrier and both
Q-rows, but its two remaining T-roots each have a proper raw compression
support.  Any covariance completion must combine their leakage ranges (or
add another authenticated conjugate).  Even after that, the separate
source-degree fence in
`binary-jacobson-balanced-center-fold-authenticates-two-rows` remains.

DERIVATION
binary-jacobson-second-balanced-t-root-support-proof
