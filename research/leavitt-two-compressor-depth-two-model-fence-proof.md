---
rg: 2
id: leavitt-two-compressor-depth-two-model-fence-proof
kind: route
title: Evaluate the two sides of the child split at the identity pair
target: leavitt-two-compressor-depth-two-relation-breaks-hxh-model
requires:
  - leavitt-two-compressor-covariance-triangle-has-marked-models
---

In the model of the prerequisite write `A=T_0`, `B=T_1`, `d=D_h`, and
`L=A d A^(-1)`, where `h` is a nontrivial involution of `H`.  The two
depth-two factors are

```text
F_0=A L A^(-1),                 F_1=B L B^(-1).
```

Direct evaluation gives

```text
L(1,1)=(h,1),
F_0(1,1)=(h,h),
F_1(1,1)=(h,1),
F_0F_1(1,1)=F_1F_0(1,1)=(1,h).
```

Hence `L!=F_0F_1`, exactly contradicting `(DTS1)`.  For
`H_k=G^(2^k)`, every operation is the coordinatewise `2^k`-fold power of
the base model.  The fixed fraction of the discrepancy word is therefore
the corresponding base fixed fraction raised to `2^k`; the defect cannot
tend to zero and in normalized Hamming distance tends to one.
