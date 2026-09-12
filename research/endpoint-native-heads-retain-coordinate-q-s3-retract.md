---
rg: 2
id: endpoint-native-heads-retain-coordinate-q-s3-retract
kind: claim
title: Both native Hecke heads and B2 leave a two-coordinate q-corner S3 retract
artifacts:
  - research/endpoint-native-heads-coordinate-q-s3-retract-proof.md
distinct_from:
  endpoint-b2-enlargement-has-native-s3-retract: that kills the B2 enlargement on the quotient module R/pR; this uses a smaller reducing q-corner and shows that even A1, A2, B3, and both complete native Hecke heads act trivially there.
  proper-support-returns-retain-constant-s3-retract: that uses the scalar qI corner and therefore stops at B2; this uses q only in coordinates 7 and 8, so B2 has neither an active source nor a surviving active range.
  native-whitehead-hecke-head-has-order-seven-anchor: that gives odd order-seven occurrence anchors on their native three-summand packets; this proves that both heads can simultaneously be killed in an exact all-word quotient retaining the separate constant opposite-root pair.
---

**ESTABLISHED COORDINATE-CORNER FENCE.**  In the binary Leavitt elementary
group write

```text
p=s_0t_0,                         q=s_1t_1,
a_1=s_1t_0,                       a_2=s_1t_00,
b_2=s_00t_1,                      b_3=s_000t_1,

P=What_(8,2;2),                   J_1=What_(7,8;1),
J_2=What_(8,9;2),                 A_1=x_47(a_1),
A_2=x_58(a_2),                    B_2=x_84(b_2),
B_3=x_95(b_3),

n=x_78(1),                        m=x_87(1).
```

Put

```text
E=qE_77+qE_88.
```

Then `E` commutes with every displayed generator.  Their restrictions to
`ER^20` are

```text
EP E=EJ_1E=EJ_2E=EA_1E=EA_2E=EB_2E=EB_3E=E,
EnE=E+qE_78,                     EmE=E+qE_87.        (NHR1)
```

Consequently, for

```text
G=<P,J_1,J_2,A_1,A_2,B_2,B_3,n,m>,
N=<n,m>~=GL_2(F_2)=S_3,
```

corner restriction gives a split retraction

```text
G -> N
```

killing the seven nonconstant generators and fixing `n,m`.  In particular
the same conclusion holds after replacing the listed generators by either
or both complete native heads

```text
J_1B_2A_1,                         J_2B_3A_2,
```

and hence after adjoining the endpoint Singer word `M=J_2B_3A_2`.

Thus neither the first paid sign-pairing root `B_2` nor the two native odd
order-seven occurrence anchors authenticate the endpoint gauge against the
constant Weyl gauge.  Every ordinary word relation among this literal
subgroup is compatible with a nontrivial native `S_3` image.

For an arbitrary elementary root `x_ij(a)`, the exact boundary of this
particular corner argument is

```text
q_i a = a q_j,
q_7=q_8=q,                         q_k=0 (k!=7,8).    (NHR2)
```

For example `x_84(1)` violates `(NHR2)` because `q*1!=0`.  By contrast
`A_2=x_58(s_1t_00)` still satisfies `(NHR2)`, since
`(s_1t_00)q=0`; its coefficient escaping the left ideal `pR` does not make
it a breaker of this sharper coordinate corner.

No Property `(T)`, Kazhdan input, trace profile, stability theorem,
finite-word enumeration, literature input, or numerical approximation is
used.

DERIVATION
endpoint-native-heads-coordinate-q-s3-retract-proof

