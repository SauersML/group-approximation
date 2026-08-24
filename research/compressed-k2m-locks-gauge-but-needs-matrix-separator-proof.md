---
rg: 2
id: compressed-k2m-locks-gauge-but-needs-matrix-separator-proof
kind: route
title: Synchronize the rectangles and compare orthogonal source capacity
target: compressed-k2m-locks-gauge-but-needs-matrix-separator
requires:
  - unitary-k2m-rectangle-synchronization
---

Apply `unitary-k2m-rectangle-synchronization` to the edge unitaries.  Choose
unitaries `A_0,A_1,B_j` with

```text
M_(0,j)=A_0B_j,
M_(1,0)=A_1B_0,
sum_j ||M_(1,j)-A_1B_j||_2^2=h.                       (CKP1)
```

Put `S_j=B_jG_jB_j^*`.  Since the row-zero ranges
`M_(0,j)G_jM_(0,j)^*=A_0S_jA_0^*` are pairwise orthogonal, so are the `S_j`.
Thus `S=sum_j S_j` is a projection and
`tau(S)=sum_j tau(G_j)`.

Capacity of `C` gives

```text
sum_j ||(I-C)A_1B_jG_j||_2^2
 = tau(S)-tau(CA_1SA_1^*)
 >= tau(S)-tau(C)
 = sum_j tau(G_j)-tau(C).                              (CKP2)
```

View the `m` compressed matrices as one vector in the Hilbert direct sum of
`m` copies of `L^2(M_d)`.  By the triangle inequality,

```text
( sum_j ||(I-C)A_1B_jG_j||_2^2 )^(1/2)
 <= ( sum_j ||(I-C)M_(1,j)G_j||_2^2 )^(1/2)
    +( sum_j ||(M_(1,j)-A_1B_j)G_j||_2^2 )^(1/2)
 <= sqrt(ell)+sqrt(h),                                 (CKP3)
```

because right multiplication by a projection is contractive in Hilbert--
Schmidt norm.  Squaring `(CKP3)` and combining with `(CKP2)` yields

```text
sum_j tau(G_j)-tau(C) <= (sqrt(ell)+sqrt(h))^2
                       <= 2(ell+h),
```

which is `(CKR6)`.  The eight-slice specialization is the stated substitution
of its already computed source-capacity deficit.