---
rg: 2
id: common-physical-reflection-pays-two-exit-gram-seam
kind: claim
title: Two individual exit errors against one physical reflection pay the mixed Gram seam
distinct_from:
  two-exit-gram-swap-builds-low-rank-involution-surgery: that gives the exact Gram criterion and low-rank completion; this gives the quantitative inequality which forces its only mixed block from one common approximate reflection.
  two-source-gram-alignment-pays-frequency-not-mode-purity: that aligns the source isometries; this controls the cross-row exit Gram after a common source has been chosen.
  bs14-residual-polars-pay-mixed-minus-three-six-moment: that asks for a bound directly from the original residual polar extraction; this identifies the exact intermediate exit-transport estimates sufficient for it.
---

**ESTABLISHED.**  Let `F_1,F_2,H_1,H_2:E -> K` be contractions and let
`X` be unitary on `K`.  Put

```text
a_i=||XF_i-H_i||_F,
iota=||X^2-1||_F=||X-X^*||_F.                        (CPR1)
```

Then

```text
||F_1^*H_2-H_1^*F_2||_F <= a_1+a_2+iota.            (CPR2)
```

More locally, the last term may be replaced by

```text
||F_1^*(X-X^*)F_2||_F.                               (CPR3)
```

If `X` is already a selfadjoint involution, only the two individual exit
errors remain.

In the BS specialization `(GS8)--(GS12)` of
`two-exit-gram-swap-builds-low-rank-involution-surgery`, this is exactly

```text
||V^*S^(-3)V-V^*S^6V||_F <= a_1+a_2+iota.            (CPR4)
```

Consequently the mixed minus-three/six moment is not a new independent
energy carrier.  It is automatically paid once both polar rows retain
their forward/backward exit equations against the **same physical**
involution.

The proof is the one-line expansion

```text
F_1^*H_2-H_1^*F_2
 =F_1^*(H_2-XF_2)
  +F_1^*(X-X^*)F_2
  +(XF_1-H_1)^*F_2.                                  (CPR5)
```

Contractivity and the Frobenius ideal inequality give `(CPR2)`.  Finally,
right multiplication by the unitary `X` gives

```text
||(X-X^*)X||_F=||X^2-1||_F,
```

proving the equality in `(CPR1)`.
