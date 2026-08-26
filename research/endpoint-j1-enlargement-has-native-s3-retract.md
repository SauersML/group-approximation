---
rg: 2
id: endpoint-j1-enlargement-has-native-s3-retract
kind: claim
title: Adding the first prefix Whitehead still leaves a split native S3 retract
artifacts:
  - experiments/endpoint_j1_external_s3_retract_audit.py
  - experiments/endpoint_j1_external_subgroup_relator_audit.py
  - research/endpoint-j1-native-s3-retract-proof.md
distinct_from:
  endpoint-external-subgroup-has-native-s3-retract: that cuts by the full complement of the endpoint support and retracts the three-generator subgroup; this passes to the smaller q corner and proves that the literal first prefix Whitehead can be added without disturbing the retract.
  endpoint-whitehead-star-braid-synchronizes-native-gauges: that proves the endpoint-prefix braid synchronizes the two Whitehead gauges once both occurrences are typed on one common homogeneous packet; this proves that their actual four-generator elementary subgroup still has a quotient killing both Whiteheads while retaining the native external S3.
  endpoint-external-order-four-is-conditional-s3-breaker: that supplies an incompatible order after identifying the endpoint gauge with the constant Weyl gauge; this shows the first literal prefix Whitehead and its braid with the endpoint do not provide that missing occurrence identification.
---

**ESTABLISHED ENLARGED ALL-WORD FENCE.**  Put

```text
P=What_(8,2;2),          J_1=What_(7,8;1),
n=x_78(1),               m=x_87(1),
G_1=<P,J_1,n,m>,         N=<n,m>~=S_3.                 (EJR1)
```

There is a split retraction

```text
rho_1:G_1 -> N,
rho_1(P)=rho_1(J_1)=1,       rho_1(n)=n,  rho_1(m)=m. (EJR2)
```

The retraction is an actual invariant corner of the literal elementary
matrices.  Let

```text
q=s_1t_1.                                                (EJR3)
```

Both Whiteheads in `(EJR1)` are supported on zero-prefix cylinder
summands, all contained in `p=s_0t_0`.  Since `pq=qp=0`, the scalar
projection `qI` commutes with all four generators and

```text
(qI)P(qI)=qI,             (qI)J_1(qI)=qI.             (EJR4)
```

The constant roots restrict instead to

```text
n_q=qI+qE_78,             m_q=qI+qE_87.               (EJR5)
```

The two matrices in `(EJR5)` generate the standard
`GL_2(F_2)=S_3` over the nonzero corner with identity `q`; corner
restriction is injective on `N` and proves `(EJR2)`.

Hence **no ordinary word relation in `<P,J_1,n,m>` can kill the surviving
native `S_3` gauge**.  In particular, the genuine endpoint-prefix braid

```text
(PJ_1)^3=1                                               (EJR6)
```

does not identify either Whitehead occurrence with the constant Weyl
occurrence `w=nmn`: the exact quotient `(EJR2)` sends the two former
occurrences to one and keeps `n,m,w` nontrivial.

As a bounded calibration, an MSI-only faithful Leavitt-normal-form search
through freely reduced length nine finds exactly the cyclic classes

```text
(PJ_1)^3,             (Pn)^4,             (Pm)^4,
(nm)^3.                                                   (EJR7)
```

All reduce correctly under `(EJR2)`.  The enumeration is not used for the
all-word conclusion; the literal `qI` corner proves that conclusion at
once.

Thus the smallest outside-data enlargement by `J_1` is fenced.  A genuine
breaker must add an occurrence that acts nontrivially on, or destroys, this
`q`-corner quotient, or it must independently authenticate `P` against the
constant Weyl occurrence on the paid carrier.  No Property `(T)`, Kazhdan
input, trace profile, stability theorem, or numerical approximation is
used.

DERIVATION
endpoint-j1-native-s3-retract-proof

